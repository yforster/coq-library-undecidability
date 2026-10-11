(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The three paper inputs that stay hypotheses (PLAN.md Phase 2F, task
   P17; ASSEMBLY.md Sec. 1; FEASIBILITY.md Sec. 6).

   The final theorem is meant to have the shape
     HeightThm -> PrimePattern -> PP1_L0 -> undecidable H10Q.
   The three premises are closed [Prop]s, defined here. They mention
   ORDINARY objects only: rat, int, nat, Z, the finite index types i3, i4,
   mem13 of Signature.v, the bit height [htb], the explicit curve
   constants (through [aEmod]/[countF] of ExplicitData.v) and the explicit
   Phi lists [PhiL0]. No [FixedData], [Ambient] or [AmbientS] occurs in
   them. They are Definitions, never Axioms: they appear as premises.

   1. [HeightThm]     Thm hei:height (02-reduction.tex);
   2. [PrimePattern]  Lemma pri:pattern (06-primes.tex), uniform in C;
   3. [PP1_L0]        Prop par:pole-parity part 1, for the lists PhiL0.

   Conversion lemmas into the record forms for
   [D := mkData C S Hb c Kset Nh Ch]:
   - [MSC_mkData], [LintC_mkData], [memC_mkData]: the C-parametric copies
     of the contact radical and of the members agree definitionally with
     the [FixedData] versions;
   - [HeightThm_O_height], [HeightThm_hei_enlarge]: the field O_height of
     [OrdHyps] and [hei_enlarge_ord] (via [OrdHeights.hei_enlarge_thm]);
   - [PrimePattern_Kset]: the multiplier set with positivity and the
     pattern, in the form [PatternSpec] consumed by HCov (task P15);
     [pattern_prime_*] extract all unary facts about r needed by
     [RepSpec]; [RepSpec_of_pattern] reduces [RepSpec] to the per-branch
     conditions (the job of P15);
   - [PP1_mkData]: the field PP1 of [StdHyps];
   - [mkData_WF_from_inputs]: [FixedWF].
   Finally, Section [assembly] shows how the final theorem destructs the
   hypotheses ([inputs_to_data]).

   No axioms. *)

From Stdlib Require Import ZArith Lia List.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData ExplicitData
                 RatVal OrdHeights.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

(** * 1. C-parametric copies of the contact-radical definitions

    Verbatim copies of [FixedData.fd_Lint], [odd_contact],
    [contact_support], [MS], with [fd_C D] replaced by a parameter [C].
    The four finite points of the five-point set are [C B1 .. C B4]; the
    fifth point is oo, with form L_oo(U,V) = V (the [denq] clause). *)

(* the primitive integral form L_b(U,V) = den(b) U - num(b) V of b = C i *)
Definition LintC (C : i4 -> rat) (i : i4) (u v : int) : int :=
  denq (C i) * u - numq (C i) * v.

(* odd contact order at q, in the primitive coordinates (numq s : denq s) *)
Definition odd_contactC (C : i4 -> rat) (q : nat) (s : rat) : bool :=
     odd (logn q (absz (denq s)))
  || has (fun i => odd (logn q (absz (LintC C i (numq s) (denq s))))) all_i4.

Definition contact_supportC (C : i4 -> rat) (s : rat) : nat :=
  (absz (denq s) * \prod_(i <- all_i4) absz (LintC C i (numq s) (denq s)))%N.

(* the contact radical M_S(s) of hei:radical *)
Definition MSC (C : i4 -> rat) (S : seq nat) (s : rat) : nat :=
  \prod_(q <- primes (contact_supportC C s) | (q \notin S) && odd_contactC C q s) q.

(** * 2. Hypothesis 1: Thm hei:height (02-reduction.tex, l.232-249)

    Paper: there are five distinct points C of P^1(Q) including oo, a
    finite set S of primes and constants H, c > 0 with
    h(s) <= H M_S(s)^c for all s notin C.

    Dependency: the paper's Section 4 proof relies on the companion
    preprint OddRegularFontaineMazurAtTwo ("Fontaine-Mazur modularity at
    the prime 2", Oct 6 2026, Thm 1.1 and Sec. 2.1) and on published deep
    results (Shimura canonical models, Faltings heights, Gaudron-Remond,
    Carayol, Scholze). Infeasible to formalize at present.

    Why this form: the real height bound is replaced by the bit height
    [htb s = log2_up max(|num s|, den s)] (htb <= 1 + h / ln 2 and
    M_S >= 1, so Hb := ceil(1 + H / ln 2) and c := ceil(c_paper) work);
    this is weaker than the paper's statement. oo in C is implicit since
    s : rat. Restricting the product to the primes of the contact support
    loses nothing (other primes have contact order 0). The points C are
    existential, since the paper does not make them explicit (branch
    values of a Shimura map). *)

Definition HeightBound (C : i4 -> rat) (S : seq nat) (Hb c : nat) : Prop :=
  forall s : rat, (forall i, s != C i) -> (htb s <= Hb * (MSC C S s) ^ c)%N.

Definition HeightThm : Prop :=
  exists (C : i4 -> rat) (S : seq nat) (Hb c : nat),
       (forall i j, C i = C j -> i = j)     (* the five points C B1..C B4, oo are distinct *)
    /\ all prime S
    /\ (0 < Hb)%N /\ (0 < c)%N
    /\ HeightBound C S Hb c.

(** * 3. Hypothesis 2: Lemma pri:pattern (06-primes.tex, l.21-43)

    Paper: there is a finite K in Z_{>0} such that for all A in Z and real
    B > 0 there are integers u1, u2, v with v <> 0 such that, with
    u3 = A v - u1 - u2, each of the 13 numbers v, L_b(u_j, v) is eps k r
    with eps = +-1, k in K and r > B a positive prime; r splits in F, has
    good reduction for E and E^sigma, and at either place above r the
    orders d1, d2 of E(F_r), E^sigma(F_r) satisfy gcd(d1,d2) | 4 and
    r notdvd d1 d2.

    Dependency: no companion preprint; the proof uses Green-Tao-Ziegler
    (GreenTao2010, GreenTao2012, GreenTaoZiegler2012,
    GreenTaoZiegler2024Erratum), the Selberg sieve, Dirichlet's theorem
    and Mertens' theorem. Infeasible to formalize at present.

    Why this form:
    - UNIFORM IN C (coordinator decision, PLAN "Phase 2 design
      decisions"): the paper proves it for the C of Thm hei:height, but the
      proof only uses that the forms L_b are primitive with alpha_b <> 0
      and pairwise nonzero determinants, which holds for every injective
      C. This keeps the three inputs independent.
    - The real bound B becomes Y : nat.
    - [7 < r] is stated explicitly. It is implied by the paper's
      conclusions (splitting excludes 2, 3, 5; good reduction excludes 7,
      the norm of d), and it makes [exists s, s^2 = 2 mod r] really mean
      "splits" (this is trivial at r = 2). Good reduction for E and
      E^sigma then follows from r notin {2, 7} = S_E and is not stated.
    - The place sqrt2 |-> s above r: E reduces to y^2 = x^3 + aEmod r s x
      and E^sigma (coefficient the conjugate of aE) to
      y^2 = x^3 + aEmod r (-s) x. The group orders are point counts
      [countF] (brute force over F_r^2, plus O).
    - The congruences r = 1 mod 8, r = 3 mod 7 used in the paper's proof
      (pri:prime-residues) are not part of the lemma and are omitted.
    Everything inside the quantifiers over A, Y is decidable, so for fixed
    C and Kset the body is a Pi_2 sentence. *)

(* u_3 := A v - u_1 - u_2 *)
Definition uC (A u1 u2 v : int) (i : i3) : int :=
  match i with I1 => u1 | I2 => u2 | I3 => A * v - u1 - u2 end.

(* the 13 members of pri:forms-list *)
Definition memC (C : i4 -> rat) (A u1 u2 v : int) (j : mem13) : int :=
  match j with
  | mem_v => v
  | mem_L i b => LintC C b (uC A u1 u2 v i) v
  end.

(* #E(F_r) at the place sqrt2 |-> s; #E^sigma(F_r) at that place is
   [cntE r (- s)] *)
Definition cntE (r s : Z) : nat := countF r (aEmod r s).

(* r is a prime as required by pri:pattern, above the threshold Y *)
Definition pattern_prime (Y r : nat) : Prop :=
     prime r /\ (Y < r)%N /\ (7 < r)%N
  /\ (exists s : Z, Z.modulo (s * s - 2) (Z.of_nat r) = 0%ZZ)            (* r splits in F *)
  /\ forall s : Z, Z.modulo (s * s - 2) (Z.of_nat r) = 0%ZZ ->           (* either place *)
       (gcdn (cntE (Z.of_nat r) s) (cntE (Z.of_nat r) (- s)) %| 4)%N
    /\ ~~ (r %| cntE (Z.of_nat r) s * cntE (Z.of_nat r) (- s))%N.

(* the body of pri:pattern for fixed C and K *)
Definition PatternBody (C : i4 -> rat) (Kset : seq nat) : Prop :=
  forall (A : int) (Y : nat), exists u1 u2 v : int, v != 0 /\
    forall j : mem13, exists (eps : int) (k r : nat),
         memC C A u1 u2 v j = eps * k%:Z * r%:Z
      /\ (eps = 1 \/ eps = -1)
      /\ k \in Kset
      /\ pattern_prime Y r.

Definition PrimePattern : Prop :=
  forall C : i4 -> rat, (forall i j, C i = C j -> i = j) ->
  exists Kset : seq nat, all (fun k => 0 < k)%N Kset /\ PatternBody C Kset.

(** * 4. Hypothesis 3: Prop par:pole-parity, part 1, for PhiL0

    Paper (03-parity.tex, Prop par:pole-parity (1)): Q |= Phi(b) for every
    integer b, for any lists M, D_m with the covering properties
    par:b-prime-choices and par:d-choices.

    Dependency: the paper's Section 3 proof relies on the companion
    preprint PointwiseTwoConverse ("A pointwise 2-converse for elliptic
    curves with rational two-torsion", Oct 7 2026, Thm 1.1; alternatively
    UnrestrictedTwoConverse) and on the Cassels-Tate pairing (Cassels1962,
    PoonenStoll1999); deriving it from Lemma par:global-point would also
    need weak approximation, local square classes and Dirichlet's theorem.

    Why this form (coordinator decision): it is word for word claim (1)
    for one admissible choice of lists, the explicit [PhiL0] of
    ExplicitData.v, stated by the mathematical condition [Phi_math] (not
    the formula). It is an instance of the paper's statement because
    [PhiL0] has the covering properties par:b-prime-choices and
    par:d-choices: PhiCovering.v proves [PhiL0_CoversM], [PhiL0_CoversD]
    and [PP1_paper_L0 : PP1_paper -> PP1_L0], where [PP1_paper] is the
    paper's claim (1) for all lists with these properties. *)

Definition PP1_L0 : Prop := forall b : int, Phi_math PhiL0 (b%:~R : rat).

(** * 5. Conversion: Thm hei:height *)

(* the field O_height of [OrdHyps] (= premise of [hei_enlarge_thm]) *)
Definition O_height_stmt (D : FixedData) : Prop :=
  forall s : rat, (forall i, s != fd_C D i) ->
    (htb s <= fd_Hb D * (MS D (fd_S D) s) ^ fd_c D)%N.

Section mkData_conv.

  Variables (C : i4 -> rat) (S : seq nat) (Hb c : nat) (Kset : seq nat) (Nh Ch : nat).
  Let D := mkData C S Hb c Kset Nh Ch.

  Lemma LintC_mkData i u v : fd_Lint D i u v = LintC C i u v.
  Proof. by []. Qed.

  Lemma odd_contactC_mkData q s : odd_contact D q s = odd_contactC C q s.
  Proof. by []. Qed.

  Lemma contact_supportC_mkData s : contact_support D s = contact_supportC C s.
  Proof. by []. Qed.

  Lemma MSC_mkData S' s : MS D S' s = MSC C S' s.
  Proof. by []. Qed.

  Lemma HeightBound_O_height : HeightBound C S Hb c -> O_height_stmt D.
  Proof. by move=> H s Hs; rewrite MSC_mkData; exact: H. Qed.

  Lemma HeightBound_hei_enlarge : FixedWF D -> HeightBound C S Hb c -> hei_enlarge_ord D.
  Proof. by move=> HWF H; apply: (hei_enlarge_thm HWF); exact: HeightBound_O_height. Qed.

End mkData_conv.

(* the HeightThm body for given witnesses, as in the task statement *)
Lemma HeightThm_O_height (C : i4 -> rat) (S : seq nat) (Hb c : nat) :
  HeightBound C S Hb c ->
  forall Kset Nh Ch, O_height_stmt (mkData C S Hb c Kset Nh Ch).
Proof. by move=> H Kset Nh Ch; exact: HeightBound_O_height. Qed.

Lemma HeightThm_hei_enlarge (C : i4 -> rat) (S : seq nat) (Hb c : nat) :
  HeightBound C S Hb c ->
  forall Kset Nh Ch, FixedWF (mkData C S Hb c Kset Nh Ch) ->
    hei_enlarge_ord (mkData C S Hb c Kset Nh Ch).
Proof. by move=> H Kset Nh Ch HWF; exact: HeightBound_hei_enlarge. Qed.

(** * 6. Conversion: FixedWF *)

Lemma mkData_WF_from_inputs (C : i4 -> rat) (S : seq nat) (Hb c : nat) (Kset : seq nat)
  (Nh Ch : nat) :
  (forall i j, C i = C j -> i = j) -> all prime S -> (0 < Hb)%N -> (0 < c)%N ->
  all (fun k => 0 < k)%N Kset -> (0 < Nh)%N ->
  FixedWF (mkData C S Hb c Kset Nh Ch).
Proof.
  move=> HC HS HHb Hc HK HNh.
  by apply: mkData_WF => // k hk; exact: (allP HK).
Qed.

(** * 7. Conversion: PP1 *)

Lemma PP1_mkData : PP1_L0 ->
  forall C S Hb c Kset Nh Ch (b : int),
    Phi_holdsR (fd_PhiL (mkData C S Hb c Kset Nh Ch)) (b%:~R : rat).
Proof. by move=> H C S Hb c Kset Nh Ch b; apply/Phi_holds_iff; exact: H. Qed.

(** * 8. Conversion: Lemma pri:pattern *)

(** ** 8.1 Bridges between Z and int *)

Definition Z_to_int (z : Z) : int :=
  match z with
  | Z0 => 0
  | Zpos p => Posz (Pos.to_nat p)
  | Zneg p => - Posz (Pos.to_nat p)
  end.

Lemma iz_Z_to_int (z : Z) : int_to_Z (Z_to_int z) = z.
Proof.
  case: z => [ // | p | p ] /=; first exact: positive_nat_Z.
  by rewrite iz_opp /= positive_nat_Z.
Qed.

Lemma iz_sqr_sub2 (B : int) : int_to_Z (B ^+ 2 - 2) = (int_to_Z B * int_to_Z B - 2)%ZZ.
Proof. by rewrite iz_add iz_opp expr2 iz_mul. Qed.

(* r | B^2 - 2 over int iff (B^2 - 2) mod r = 0 over Z, for r > 0 *)
Lemma split_int_Z (r : nat) (B : int) : (0 < r)%N ->
  (exists wB : int, B ^+ 2 - 2 = r%:Z * wB) <->
  Z.modulo (int_to_Z B * int_to_Z B - 2) (Z.of_nat r) = 0%ZZ.
Proof.
  move=> Hr; have Hr' : Z.of_nat r <> 0%ZZ by move/ssrnat.ltP: Hr; lia.
  split.
  - move=> [wB HwB]; move: (f_equal int_to_Z HwB).
    rewrite iz_sqr_sub2 iz_mul iz_nat => ->.
    by rewrite Z.mul_comm Z_mod_mult.
  - move=> /(Z.mod_divide _ _ Hr') [q Hq].
    exists (Z_to_int q); apply: iz_inj.
    by rewrite iz_sqr_sub2 iz_mul iz_nat iz_Z_to_int Hq Z.mul_comm.
Qed.

(** ** 8.2 What [pattern_prime] gives about r (the unary part of RepSpec) *)

Section pattern_prime_facts.

  Variables (Y r : nat).
  Hypothesis Hr : pattern_prime Y r.

  Lemma pattern_prime_prime : prime r.
  Proof using Hr. by case: Hr. Qed.

  Lemma pattern_prime_gtY : (Y < r)%N.
  Proof using Hr. by case: Hr => _ []. Qed.

  Lemma pattern_prime_gt7 : (7 < r)%N.
  Proof using Hr. by case: Hr => _ [_ []]. Qed.

  Lemma pattern_prime_pos : 0 < r%:Z.
  Proof using Hr. by rewrite ltz_nat (prime_gt0 pattern_prime_prime). Qed.

  Lemma pattern_prime_absz : prime (absz r%:Z).
  Proof using Hr. exact: pattern_prime_prime. Qed.

  (* good reduction for E and E^sigma: r is not in S_E = {2, 7} *)
  Lemma pattern_prime_SE0 : r \notin SE0.
  Proof using Hr.
    have H7 := pattern_prime_gt7.
    rewrite /SE0 !inE; apply/negP => /orP [] /eqP E; by rewrite E in H7.
  Qed.

  Lemma pattern_prime_odd : odd r.
  Proof using Hr.
    have H7 := pattern_prime_gt7.
    have [ | -> // ] := even_prime pattern_prime_prime.
    by move=> E; rewrite E in H7.
  Qed.

  (* r splits: an integer B with r | B^2 - 2, as in RepSpec *)
  Lemma pattern_prime_split : exists B wB : int, B ^+ 2 - 2 = r%:Z * wB.
  Proof using Hr.
    case: Hr => Hp [_ [_ [[s Hs] _]]].
    exists (Z_to_int s); apply/split_int_Z; first exact: prime_gt0.
    by rewrite iz_Z_to_int.
  Qed.

  (* the reduction-order conditions at the place sqrt2 |-> B above r *)
  Lemma pattern_prime_orders (B wB : int) : B ^+ 2 - 2 = r%:Z * wB ->
       (gcdn (cntE (Z.of_nat r) (int_to_Z B)) (cntE (Z.of_nat r) (- int_to_Z B)) %| 4)%N
    /\ ~~ (r %| cntE (Z.of_nat r) (int_to_Z B) * cntE (Z.of_nat r) (- int_to_Z B))%N.
  Proof using Hr.
    move=> HB; case: Hr => Hp [_ [_ [_ Hord]]]; apply: Hord.
    by apply/split_int_Z; [ exact: prime_gt0 | exists wB ].
  Qed.

  (* at the place sqrt2 |-> sgnz s * B, for either sign s *)
  Lemma pattern_prime_orders_sgn (B wB : int) (s : sgn) : B ^+ 2 - 2 = r%:Z * wB ->
       (gcdn (cntE (Z.of_nat r) (int_to_Z (sgnz s * B)))
             (cntE (Z.of_nat r) (- int_to_Z (sgnz s * B))) %| 4)%N
    /\ ~~ (r %| cntE (Z.of_nat r) (int_to_Z (sgnz s * B))
               * cntE (Z.of_nat r) (- int_to_Z (sgnz s * B)))%N.
  Proof using Hr.
    move=> HB; apply: (@pattern_prime_orders _ wB).
    by case: s; rewrite /sgnz ?mul1r ?mulN1r ?sqrrN.
  Qed.

End pattern_prime_facts.

(** ** 8.3 Choice over the finite index type mem13 (no axiom) *)

Lemma mem13_choice (X : Type) (P : mem13 -> X -> Prop) :
  (forall j, exists x, P j x) -> exists f : mem13 -> X, forall j, P j (f j).
Proof.
  move=> H.
  have [x0 H0] := H mem_v.
  have [x11 H11] := H (mem_L I1 B1). have [x12 H12] := H (mem_L I1 B2).
  have [x13 H13] := H (mem_L I1 B3). have [x14 H14] := H (mem_L I1 B4).
  have [x21 H21] := H (mem_L I2 B1). have [x22 H22] := H (mem_L I2 B2).
  have [x23 H23] := H (mem_L I2 B3). have [x24 H24] := H (mem_L I2 B4).
  have [x31 H31] := H (mem_L I3 B1). have [x32 H32] := H (mem_L I3 B2).
  have [x33 H33] := H (mem_L I3 B3). have [x34 H34] := H (mem_L I3 B4).
  exists (fun j => match j with
                   | mem_v => x0
                   | mem_L I1 B1 => x11 | mem_L I1 B2 => x12 | mem_L I1 B3 => x13 | mem_L I1 B4 => x14
                   | mem_L I2 B1 => x21 | mem_L I2 B2 => x22 | mem_L I2 B3 => x23 | mem_L I2 B4 => x24
                   | mem_L I3 B1 => x31 | mem_L I3 B2 => x32 | mem_L I3 B3 => x33 | mem_L I3 B4 => x34
                   end).
  by case => [ | [] [] ].
Qed.

(** ** 8.4 [PatternSpec]: the conclusions of pri:pattern for a [FixedData] *)

(* the witnesses of pri:pattern: u1, u2, v and per member eps, k, r *)
Record PatWit : Type := {
  pw_u1 : int;
  pw_u2 : int;
  pw_v : int;
  pw_eps : mem13 -> int;
  pw_k : mem13 -> nat;
  pw_r : mem13 -> nat
}.

Section pattern_spec.

  Variable D : FixedData.

  (* the 13 members v, L_b(u_i, v) of pri:forms-list, in terms of D *)
  Definition pw_mem (W : PatWit) (A : int) (j : mem13) : int :=
    match j with
    | mem_v => pw_v W
    | mem_L i b => fd_Lint D b (uC A (pw_u1 W) (pw_u2 W) (pw_v W) i) (pw_v W)
    end.

  Record PatternSpec (A : int) (Y : nat) (W : PatWit) : Prop := {
    ps_v : pw_v W != 0;
    ps_mem : forall j, pw_mem W A j = pw_eps W j * (pw_k W j)%:Z * (pw_r W j)%:Z;
    ps_eps : forall j, pw_eps W j = 1 \/ pw_eps W j = -1;
    ps_k : forall j, pw_k W j \in fd_Kset D;
    ps_prime : forall j, pattern_prime Y (pw_r W j)
  }.

  (* extend the pattern witness by the per-member/per-branch data of HCov *)
  Definition pw_ext (W : PatWit) (B : mem13 -> int) (h j0 : mem13 -> sgn -> int) : RepWit1 :=
    {| rw_u1 := pw_u1 W; rw_u2 := pw_u2 W; rw_v := pw_v W;
       rw_eps := pw_eps W; rw_k := pw_k W; rw_r := fun j => (pw_r W j)%:Z;
       rw_B := B; rw_h := h; rw_j0 := j0 |}.

  Lemma rw_mem_pw_ext W B h j0 A j : rw_mem D (pw_ext W B h j0) A j = pw_mem W A j.
  Proof. by case: j => [ | [] b ]. Qed.

  (* the square roots of 2 modulo the r's, one per member *)
  Lemma pattern_B (A : int) (Y : nat) (W : PatWit) : PatternSpec A Y W ->
    exists B : mem13 -> int, forall j, exists wB : int, B j ^+ 2 - 2 = (pw_r W j)%:Z * wB.
  Proof.
    move=> HW; apply: (@mem13_choice _ (fun j B => exists wB : int, B ^+ 2 - 2 = (pw_r W j)%:Z * wB)).
    by move=> j; exact: pattern_prime_split (ps_prime HW j).
  Qed.

  (* RepSpec from the pattern, given the per-branch data (the job of P15):
     everything in RepSpec except the per-branch conditions comes from
     PatternSpec, provided the threshold Y is at least K + 1 *)
  Lemma RepSpec_of_pattern (K : nat) (A : int) (Y : nat) (W : PatWit) :
    PatternSpec A Y W -> (K.+1 <= Y)%N ->
    forall (B : mem13 -> int), (forall j, exists wB : int, B j ^+ 2 - 2 = (pw_r W j)%:Z * wB) ->
    forall (h j0 : mem13 -> sgn -> int),
      (forall j s, h j s != 0 /\ j0 j s != 0 /\
                   forall a : int, RepConds D K (pw_r W j)%:Z (B j) s (h j s) (j0 j s) a) ->
    RepSpec D K A (pw_ext W B h j0).
  Proof.
    move=> HW HKY B HB h j0 Hhj; split; first exact: ps_v HW.
    move=> j; rewrite rw_mem_pw_ext /=.
    have Hp := ps_prime HW j.
    split; first exact: ps_mem HW j.
    split; first exact: ps_eps HW j.
    split; first exact: ps_k HW j.
    split; first exact: pattern_prime_pos Hp.
    split; first exact: pattern_prime_absz Hp.
    split; first exact: leq_ltn_trans HKY (pattern_prime_gtY Hp).
    split; first exact: HB j.
    exact: Hhj j.
  Qed.

End pattern_spec.

(* the members of pri:pattern for C are the members of mkData C ... *)
Lemma memC_mkData C S Hb c Kset Nh Ch (W : PatWit) A j :
  memC C A (pw_u1 W) (pw_u2 W) (pw_v W) j = pw_mem (mkData C S Hb c Kset Nh Ch) W A j.
Proof. by case: j. Qed.

Lemma PatternBody_spec (C : i4 -> rat) (Kset : seq nat) :
  PatternBody C Kset ->
  forall S Hb c Nh Ch (A : int) (Y : nat),
    exists W : PatWit, PatternSpec (mkData C S Hb c Kset Nh Ch) A Y W.
Proof.
  move=> HP S Hb c Nh Ch A Y.
  have [u1 [u2 [v [Hv Hj]]]] := HP A Y.
  have [f Hf] := @mem13_choice (int * nat * nat)
    (fun j x => memC C A u1 u2 v j = x.1.1 * x.1.2%:Z * x.2%:Z
             /\ (x.1.1 = 1 \/ x.1.1 = -1) /\ x.1.2 \in Kset /\ pattern_prime Y x.2)
    (fun j => let: ex_intro eps (ex_intro k (ex_intro r H)) := Hj j in
              ex_intro _ (eps, k, r) H).
  exists {| pw_u1 := u1; pw_u2 := u2; pw_v := v;
            pw_eps := fun j => (f j).1.1; pw_k := fun j => (f j).1.2; pw_r := fun j => (f j).2 |}.
  split => //= j; have [H1 [H2 [H3 H4]]] := Hf j; rewrite // -H1.
Qed.

(* the form consumed by HCov (P15) *)
Lemma PrimePattern_Kset : PrimePattern ->
  forall C : i4 -> rat, (forall i j, C i = C j -> i = j) ->
  exists Kset : seq nat, all (fun k => 0 < k)%N Kset /\
    forall S Hb c Nh Ch (A : int) (Y : nat),
      exists W : PatWit, PatternSpec (mkData C S Hb c Kset Nh Ch) A Y W.
Proof.
  move=> HP C HC; have [Kset [HK HB]] := HP C HC.
  by exists Kset; split => //; exact: PatternBody_spec.
Qed.

(** * 9. Sketch of the final assembly: destructing the hypotheses

    [Nh0], [Ch0] are the canonical-height constants of red:elliptic-lower,
    to be delivered by P13; here they are Section variables. *)

Section assembly.

  Variables (Nh0 Ch0 : nat).
  Hypothesis HNh0 : (0 < Nh0)%N.

  Lemma inputs_to_data : HeightThm -> PrimePattern ->
    exists C S Hb c Kset,
      let D := mkData C S Hb c Kset Nh0 Ch0 in
         FixedWF D
      /\ O_height_stmt D
      /\ hei_enlarge_ord D
      /\ forall (A : int) (Y : nat), exists W : PatWit, PatternSpec D A Y W.
  Proof using HNh0.
    move=> [C [S [Hb [c [HC [HS [HHb [Hc Hh]]]]]]]] HP.
    have [Kset [HK HPat]] := PrimePattern_Kset HP HC.
    have HWF := mkData_WF_from_inputs Ch0 HC HS HHb Hc HK HNh0.
    exists C, S, Hb, c, Kset; split => //; split; first exact: HeightThm_O_height.
    by split; [ exact: HeightThm_hei_enlarge | exact: HPat ].
  Qed.

  (* with the third input: also the field PP1 of StdHyps *)
  Lemma inputs_to_data_PP1 : HeightThm -> PrimePattern -> PP1_L0 ->
    exists C S Hb c Kset,
      let D := mkData C S Hb c Kset Nh0 Ch0 in
         FixedWF D
      /\ O_height_stmt D
      /\ hei_enlarge_ord D
      /\ (forall (A : int) (Y : nat), exists W : PatWit, PatternSpec D A Y W)
      /\ (forall b : int, Phi_holdsR (fd_PhiL D) (b%:~R : rat)).
  Proof using HNh0.
    move=> HH HP HPP; have [C [S [Hb [c [Kset [H1 [H2 [H3 H4]]]]]]]] := inputs_to_data HH HP.
    by exists C, S, Hb, c, Kset; do 4 (split => //); exact: PP1_mkData.
  Qed.

End assembly.

