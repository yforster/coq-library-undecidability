(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The explicit part of the fixed data (PLAN.md, Phase 2D, task P10).

   EXPLICIT AND PROVED here:
   - the point [Q0 = (799 - 565 sqrt2, -31800 + 22486 sqrt2)] of
     05-elliptic.tex (Q = (-d w, 2 sqrt2 d^2), w = -5 + 4 sqrt2): the
     identities [w0 = d (1 + sqrt2)^3], [w0^3 - w0 = -8 d], [Q0_spec] and
     [on_curve_Q0];
   - [SE0 = [:: 2; 7]] (S_E: 2, the bad primes of E and E^sigma, which
     lie above 7, and the ramified prime 2);
   - [m0 = 2] (CONJECTURAL, see below);
   - explicit Phi lists [PhiL0] (03-parity.tex Sec. 3.2), with a
     computed check that they hit every tuple of local square-class
     signatures;
   - [mkData] and [mkData_WF]: the explicit FixedWF conjuncts are proved,
     the others are hypotheses on the parameters.
   - an exact binary-integer mirror of the chord-tangent law on
     Q(sqrt2) and a proof that it computes [mulQn] for [Q0]; from it, by
     [vm_compute], the multiples 1..10 of Q0, their reductions at the
     place sqrt2 |-> 6 above 17, and the fact that the reduction of Q0
     has order exactly 10 in E(F_17) (FEASIBILITY.md, Sec. 2.4).

   CONJECTURAL: [m0 = 2] and [P0 = Q0] are correct for O_rank only if
   Q0 generates E(F) modulo torsion and E(F)_tors = E[2]. Neither fact is
   proved (FEASIBILITY.md Sec. 2.2); the paper never claims that Q
   generates. Nothing in this file depends on it: the definitions are
   just data, and every statement proved here is unconditional.

   NOT EXPLICIT (parameters of [mkData]): the five points C, the
   exceptional set S, the height constants Hb and c (Thm hei:height),
   the multiplier set K (Lemma pri:pattern), and the canonical-height
   constants Nh, Ch.

   Implementation note: MathComp naturals are unary, so rationals with
   large numerators must not be computed by [vm_compute], and large
   [rat] numerals are not even elaborated. All explicit constants are
   therefore given as images of binary integers [Z] under the ring
   morphism [Z_to_rat] (RatUtil.v), and all computations are done on
   [Z]. *)

From Stdlib Require Import ZArith Lia List.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData.

From HB Require Import structures.
From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** * 1. Binary integers in Q and in Q(sqrt2) *)

(* locked, so that neither [simpl] nor the unifier ever unfolds it into
   unary naturals *)
HB.lock Definition zr (z : Z) : rat := Z_to_rat z.

Lemma zr_add (a b : Z) : zr (a + b)%ZZ = zr a + zr b. Proof. rewrite unlock; exact: Z_to_rat_add. Qed.
Lemma zr_mul (a b : Z) : zr (a * b)%ZZ = zr a * zr b. Proof. rewrite unlock; exact: Z_to_rat_mul. Qed.
Lemma zr_opp (a : Z) : zr (- a)%ZZ = - zr a. Proof. rewrite unlock; exact: Z_to_rat_opp. Qed.
Lemma zr_sub (a b : Z) : zr (a - b)%ZZ = zr a - zr b. Proof. rewrite unlock; exact: Z_to_rat_sub. Qed.
Lemma zr0 : zr 0 = 0. Proof. rewrite unlock; exact: Z_to_rat_0. Qed.
Lemma zr1 : zr 1 = 1. Proof. rewrite unlock; exact: Z_to_rat_1. Qed.
Lemma zr_nat n : zr (Z.of_nat n) = n%:R. Proof. rewrite unlock; exact: Z_to_rat_of_nat. Qed.
Lemma zr2 : zr 2 = 2%:R. Proof. exact: (zr_nat 2). Qed.
Lemma zr3 : zr 3 = 3%:R. Proof. exact: (zr_nat 3). Qed.

Lemma zr_inj (a b : Z) : zr a = zr b -> a = b. Proof. rewrite unlock; exact: Z_to_rat_inj. Qed.

Lemma zr_eq0 (a : Z) : (zr a == 0) = (a =? 0)%ZZ.
Proof.
  apply/eqP/idP => [ H | /Z.eqb_eq -> ]; last exact: zr0.
  apply/Z.eqb_eq/zr_inj; by rewrite H zr0.
Qed.

Lemma zr_neq0 (a : Z) : a <> 0%ZZ -> zr a != 0.
Proof. by move=> H; rewrite zr_eq0; apply/negP => /Z.eqb_eq. Qed.

(* the element  a + b sqrt2  of F *)
HB.lock Definition zq (a b : Z) : qe rat := QE (zr a) (zr b).

Lemma zq_add (a b c d : Z) : zq a b + zq c d = zq (a + c)%ZZ (b + d)%ZZ.
Proof. by rewrite zq.unlock qe_addE !zr_add. Qed.

Lemma zq_opp (a b : Z) : - zq a b = zq (- a)%ZZ (- b)%ZZ.
Proof. by rewrite zq.unlock qe_oppE !zr_opp. Qed.

Lemma zq_mul (a b c d : Z) : zq a b * zq c d = zq (a * c + 2 * (b * d))%ZZ (a * d + b * c)%ZZ.
Proof. by rewrite zq.unlock qe_mulE !zr_add !zr_mul zr2. Qed.

Lemma zq_nat (n : nat) : n%:R = zq (Z.of_nat n) 0.
Proof. by rewrite qe_natE zq.unlock zr_nat zr0. Qed.

(* positive literals: [zr (Zpos p)] is the unary literal *)
Lemma zr_pos (p : positive) : zr (Zpos p) = (Pos.to_nat p)%:R.
Proof. by rewrite -zr_nat positive_nat_Z. Qed.

Lemma zr_neg (p : positive) : zr (Zneg p) = - (Pos.to_nat p)%:R.
Proof. by rewrite -zr_pos -zr_opp. Qed.

(** * 2. The point Q of 05-elliptic.tex *)

Lemma dF_zq : dF = zq 75 (-53).
Proof. by rewrite /dF zq.unlock zr_neg zr_pos. Qed.

Lemma aE_zq : aE = zq (-11243) 7950.
Proof. by rewrite /aE zq.unlock zr_neg zr_pos. Qed.

Definition sqrt2F : qe rat := qe_sqrt2.

Lemma sqrt2F_zq : sqrt2F = zq 0 1.
Proof. by rewrite /sqrt2F /qe_sqrt2 zq.unlock zr0 zr1. Qed.

(* w = -5 + 4 sqrt2 *)
Definition w0 : qe rat := zq (-5) 4.

(* Q0 = (799 - 565 sqrt2, -31800 + 22486 sqrt2), i.e.
   (QE 799 (-565), QE (-31800) 22486) with binary literals *)
Definition Q0 : qe rat * qe rat := (zq 799 (-565), zq (-31800) 22486).

Lemma zq_eq (a b c d : Z) : a = c -> b = d -> zq a b = zq c d.
Proof. by move=> -> ->. Qed.

Lemma qexp2 (x : qe rat) : x ^+ 2 = x * x. Proof. exact: expr2. Qed.
Lemma qexp3 (x : qe rat) : x ^+ 3 = x * (x * x). Proof. by rewrite !exprS expr0 mulr1. Qed.

(* rewrite everything into [zq] form; never let [simpl] or the unifier
   see the unary naturals behind [zr] *)
Ltac zq_norm :=
  rewrite ?dF_zq ?aE_zq ?sqrt2F_zq /w0 /Q0 /=;
  rewrite ?qexp3 ?qexp2 ?(zq_nat 2) ?(zq_nat 8);
  rewrite ?zq_mul ?zq_opp ?zq_add ?zq_mul ?zq_opp ?zq_add.

Ltac zq_close := try congr (_, _); apply: zq_eq; vm_compute; reflexivity.

(* w = d (1 + sqrt2)^3 *)
Lemma w0_spec : w0 = dF * (1 + sqrt2F) ^+ 3.
Proof.
  have -> : 1 + sqrt2F = zq 1 1 by rewrite sqrt2F_zq zq.unlock zr0 zr1 [1]qe1E qe_addE add0r addr0.
  zq_norm; zq_close.
Qed.

(* w^3 - w = -8 d *)
Lemma w0_cubic : w0 ^+ 3 - w0 = - (8%:R * dF).
Proof. zq_norm; zq_close. Qed.

(* Q = (-d w, 2 sqrt2 d^2) *)
Lemma Q0_spec : Q0 = (- (dF * w0), 2%:R * sqrt2F * dF ^+ 2).
Proof. zq_norm; zq_close. Qed.

(* Q0 lies on E: y^2 = x^3 - d^2 x. First symbolically, as in the paper:
   x^3 - d^2 x = - d^3 (w^3 - w) = 8 d^4 = y^2. *)
Lemma on_curve_symbolic_aux (R : comNzRingType) (d w r : R) :
  r * r = 2%:R -> w ^+ 3 - w = - (8%:R * d) ->
  (2%:R * r * d ^+ 2) * (2%:R * r * d ^+ 2) = (- (d * w)) ^+ 3 + - (d * d) * - (d * w).
Proof.
  move=> Hr Hw.
  have -> : (- (d * w)) ^+ 3 + - (d * d) * - (d * w) = - d ^+ 3 * (w ^+ 3 - w) by ring.
  rewrite Hw.
  have -> : (2%:R * r * d ^+ 2) * (2%:R * r * d ^+ 2) = 4%:R * (r * r) * d ^+ 4 by ring.
  rewrite Hr; ring.
Qed.

Lemma on_curve_Q0_symbolic : on_curve Q0.
Proof.
  rewrite /on_curve Q0_spec aE_spec /=.
  apply: on_curve_symbolic_aux; [ exact: qe_sqrt2_sqr | exact: w0_cubic ].
Qed.

(* ... and by direct computation on binary integers *)
Lemma on_curve_Q0 : on_curve Q0.
Proof. rewrite /on_curve; zq_norm; zq_close. Qed.

(** * 3. S_E and the index m *)

(* S_E = {2, 7}: Delta(E) = 64 d^6, N(d) = 7, the bad places of E and
   E^sigma lie above 7, and 2 is the only ramified prime (05-elliptic.tex,
   "Include 2, the primes of bad reduction of either equation, and the
   ramified primes of F/Q in S_E"). *)
Definition SE0 : seq nat := [:: 2%N; 7%N].

Lemma SE0_prime : all prime SE0.
Proof. by []. Qed.

(* m = 2. CONJECTURAL for O_rank: correct iff Q0 generates E(F) modulo
   torsion and E(F)_tors = E[2] (exponent 2), FEASIBILITY.md Sec. 2.2.
   The paper only says "choose m divisible by the exponent of the finite
   torsion subgroup" (05-elliptic.tex, proof of Prop ell:rank). *)
Definition m0 : nat := 2.

Lemma m0_pos : (0 < m0)%N. Proof. by []. Qed.

(** * 4. The Phi lists (03-parity.tex, Sec. 3.2)

    The paper requires (par:b-prime-choices) a finite list M such that
    for every b in Q^x some m in M gives b' = m b > 0, b' in Q_2^{x2},
    and b' in the unit nonsquare class of Q_3^x; and, for every m in M,
    with S(m) = {2,3} u Supp(m), (par:d-choices) a finite list D_m such
    that for every b <> 0 some m_d in D_m gives d = m_d b > 0 and
    d in Q_q^{x2} for q in S(m). The paper obtains them by weak
    approximation; any lists with these properties do. Since square
    classes have order two, both properties say exactly: M is a full set
    of representatives of R^x/R^{x2} x Q_2^x/Q_2^{x2} x Q_3^x/Q_3^{x2}
    (2 * 8 * 4 = 64 classes), and D_m is a full set of representatives of
    R^x/R^{x2} x prod_{q in S(m)} Q_q^x/Q_q^{x2}.

    OUR CHOICE (definite, documented):
    - M = { sigma 2^e 3^f k : sigma = +-1, e, f in {0,1},
            k in {1,5,7,11,13,17,19,23} }  (64 entries). As k runs over
      (Z/24)^x, (k mod 8, k mod 3) runs over (Z/8)^x x (Z/3)^x, so the
      64 entries represent the 64 classes.
    - S(m) = {2,3} if k = 1, and {2,3,k} otherwise (each such k is prime).
    - D_m depends only on k:
        D_m = { sigma 2^e 3^f k^g j : sigma = +-1, e, f, g in {0,1}, j in J_k }
      with g = 0 only if k = 1, and J_k the list of the smallest positive
      integers coprime to 6k, one for each class of
      (j mod 8, j mod 3, Legendre symbol (j/k)) (for k = 1: of
      (j mod 8, j mod 3)). Hence |D_m| = 64 for k = 1 (then D_m = M) and
      |D_m| = 256 otherwise. For fixed (sigma, e, f, g) the map from the
      class of j to the class of sigma 2^e 3^f k^g j is a bijection, so
      D_m is a full set of representatives.
    The lists are integers. [PhiL0_classes] below checks by computation
    that the entries have pairwise distinct (hence all) signatures
    (sign; parity of v_q and unit class mod 8 resp. quadratic character,
    for q in S(m)).

    WHAT PP1 NEEDS (not proved here; PP1 is class C): exactly the two
    covering properties (par:b-prime-choices) and (par:d-choices) above
    for these lists. They follow from the signature check together with
    the textbook description of local square classes (for odd q,
    u in Q_q^x is a square iff v_q(u) is even and its unit part is a
    square mod q; u in Q_2^x is a square iff v_2(u) is even and its unit
    part is 1 mod 8), which is not formalized here. *)

Definition Klist : list (Z * list Z) :=
  [:: (1, [:: 1; 5; 7; 11; 13; 17; 19; 23]);
    (5, [:: 1; 7; 11; 13; 17; 19; 23; 29; 31; 41; 43; 53; 61; 71; 73; 83]);
    (7, [:: 1; 5; 11; 13; 17; 19; 23; 29; 31; 37; 43; 47; 59; 65; 73; 79]);
    (11, [:: 1; 5; 7; 13; 17; 19; 23; 29; 31; 35; 37; 59; 67; 73; 89; 95]);
    (13, [:: 1; 5; 7; 11; 17; 19; 23; 29; 35; 37; 41; 43; 47; 55; 61; 73]);
    (17, [:: 1; 5; 7; 11; 13; 19; 23; 35; 37; 41; 47; 53; 55; 73; 89; 91]);
    (19, [:: 1; 5; 7; 11; 13; 17; 23; 29; 31; 41; 43; 59; 61; 67; 71; 97]);
    (23, [:: 1; 5; 7; 11; 13; 17; 19; 29; 31; 35; 37; 41; 47; 97; 139; 143]) ]%ZZ.

(* sigma 2^e 3^f, all eight choices *)
Definition unit23 : list Z :=
  flat_map (fun s => flat_map (fun e => map (fun f => (s * e * f)%ZZ) [:: 1; 3]%ZZ) [:: 1; 2]%ZZ) [:: 1; -1]%ZZ.

Definition DZ (kJ : Z * list Z) : list Z :=
  let '(k, J) := kJ in
  let gs := if (k =? 1)%ZZ then [:: 1%ZZ] else [:: 1; k]%ZZ in
  flat_map (fun u => flat_map (fun g => map (fun j => (u * g * j)%ZZ) J) gs) unit23.

Definition MZ : list Z := flat_map (fun kJ => map (fun u => (u * kJ.1)%ZZ) unit23) Klist.

Definition PhiL0Z : list (Z * list Z) :=
  flat_map (fun kJ => map (fun u => (u * kJ.1, DZ kJ)%ZZ) unit23) Klist.

Definition PhiL0 : seq (rat * seq rat) := map (fun mD => (zr mD.1, map zr mD.2)) PhiL0Z.

Lemma PhiL0Z_M : map fst PhiL0Z = MZ.
Proof. by vm_compute. Qed.

Lemma PhiL0_sizes :
  length PhiL0Z = 64%N /\ map (fun mD => length mD.2) PhiL0Z
  = (nseq 8 64 ++ nseq 56 256)%N.
Proof. by vm_compute. Qed.

(* checked by computation: all entries nonzero, every D_m nonempty *)
Definition PhiL0Z_ok : bool :=
  forallb (fun mD => negb (mD.1 =? 0)%ZZ && (if mD.2 is [::] then false else true) &&
                     forallb (fun z => negb (z =? 0)%ZZ) mD.2) PhiL0Z.

Lemma PhiL0Z_ok_true : PhiL0Z_ok = true. Proof. by vm_compute. Qed.

Lemma PhiL0_nonempty : PhiL0 <> [::]. Proof. by []. Qed.

Lemma PhiL0_wf mm Dm : List.In (mm, Dm) PhiL0 ->
  mm != 0 /\ Dm <> [::] /\ forall md, List.In md Dm -> md != 0.
Proof.
  rewrite /PhiL0 => H; apply in_map_iff in H.
  destruct H as [[m D] [Heq HIn]]; case: Heq => <- <-.
  have := proj1 (forallb_forall _ _) PhiL0Z_ok_true _ HIn => /=.
  move=> /andP [/andP [Hm HD] HDz]; split; [ | split ].
  - by apply: zr_neq0 => /Z.eqb_eq H; rewrite H in Hm.
  - by case: D HIn HD HDz.
  - move=> md Hmd; apply in_map_iff in Hmd; destruct Hmd as [z [<- Hz]].
    apply: zr_neq0 => H0.
    by have := proj1 (forallb_forall _ _) HDz _ Hz; rewrite H0.
Qed.

(** Local square-class signatures, on binary integers. *)

Fixpoint vZ_aux (fuel : nat) (q z : Z) : nat :=
  match fuel with
  | O => O
  | S f => if negb (z =? 0)%ZZ && (Z.modulo z q =? 0)%ZZ then S (vZ_aux f q (Z.div z q)) else O
  end.

(* the q-adic valuation of a nonzero integer of absolute value < 2^64 *)
Definition vZ (q z : Z) : nat := vZ_aux 64 q z.

Definition unitZ (q z : Z) : Z := Z.div z (q ^ Z.of_nat (vZ q z)).

(* modular exponentiation, for the Euler criterion *)
Fixpoint powmod_pos (a : Z) (e : positive) (r : Z) : Z :=
  match e with
  | xH => Z.modulo a r
  | xO e' => let h := powmod_pos a e' r in Z.modulo (h * h) r
  | xI e' => let h := powmod_pos a e' r in Z.modulo (h * h * a) r
  end.

Definition powmod (a e r : Z) : Z :=
  match e with Zpos p => powmod_pos (Z.modulo a r) p r | _ => Z.modulo 1 r end.

(* the class of z in Q_q^x / Q_q^{x2}: parity of v_q and unit class *)
Definition sigq (q z : Z) : list Z :=
  let v := Z.of_nat (vZ q z) in
  let u := unitZ q z in
  [:: Z.modulo v 2; if (q =? 2)%ZZ then Z.modulo u 8 else powmod u ((q - 1) / 2) q]%ZZ.

(* the class in R^x/R^{x2} x prod_{q in Sm} Q_q^x/Q_q^{x2} *)
Definition sig (Sm : list Z) (z : Z) : list Z :=
  (if (0 <? z)%ZZ then 1 else -1)%ZZ :: flat_map (fun q => sigq q z) Sm.

Definition Sm_of (k : Z) : list Z := if (k =? 1)%ZZ then [:: 2; 3]%ZZ else [:: 2; 3; k]%ZZ.

Definition n_classes (l : list Z) (Sm : list Z) : nat :=
  length (nodup (list_eq_dec Z.eq_dec) (map (sig Sm) l)).

(* M hits all 64 classes of R^x/2 x Q_2^x/2 x Q_3^x/2 *)
Lemma MZ_classes : n_classes MZ [:: 2; 3]%ZZ = 64%N /\ length MZ = 64%N.
Proof. by vm_compute. Qed.

(* each D_m hits all 2 * 8 * 4 * 4^{|Supp m|} classes over S(m) *)
Lemma PhiL0_classes :
  forallb (fun kJ => let n := n_classes (DZ kJ) (Sm_of kJ.1) in
                     (n =? length (DZ kJ))%nat &&
                     (n =? if (kJ.1 =? 1)%ZZ then 64 else 256)%nat) Klist = true.
Proof. by vm_compute. Qed.

(** * 5. The fixed data with the explicit components filled in

    Parameters (not explicit in the paper): the four finite points [C]
    of the five-point set, the exceptional primes [S], the bit-height
    constant [Hb] and exponent [c] (Thm hei:height), the multiplier set
    [Kset] (Lemma pri:pattern), the canonical-height constants [Nh], [Ch]
    (red:elliptic-lower). *)

Definition mkData (C : i4 -> rat) (S : seq nat) (Hb c : nat) (Kset : seq nat)
  (Nh Ch : nat) : FixedData :=
  {| fd_m := m0; fd_P0 := Q0; fd_C := C; fd_S := S; fd_Hb := Hb; fd_c := c;
     fd_Kset := Kset; fd_SE := SE0; fd_PhiL := PhiL0; fd_Nh := Nh; fd_Ch := Ch |}.

Section mkData_wf.

  Variables (C : i4 -> rat) (S : seq nat) (Hb c : nat) (Kset : seq nat) (Nh Ch : nat).
  Let D := mkData C S Hb c Kset Nh Ch.

  (* the explicit conjuncts of FixedWF *)
  Lemma mkData_wf_m : (0 < fd_m D)%N. Proof. exact: m0_pos. Qed.
  Lemma mkData_wf_PhiL_nonempty : fd_PhiL D <> [::]. Proof. exact: PhiL0_nonempty. Qed.
  Lemma mkData_wf_PhiL mm Dm : List.In (mm, Dm) (fd_PhiL D) ->
    mm != 0 /\ Dm <> [::] /\ forall md, List.In md Dm -> md != 0.
  Proof. exact: PhiL0_wf. Qed.
  Lemma mkData_wf_SE : all prime (fd_SE D). Proof. exact: SE0_prime. Qed.
  Lemma mkData_P0_on_curve : on_curve (fd_P0 D). Proof. exact: on_curve_Q0. Qed.

  (* the remaining conjuncts are exactly hypotheses on the parameters *)
  Lemma mkData_WF :
    (forall i j, C i = C j -> i = j) ->
    (forall k, k \in Kset -> (0 < k)%N) ->
    (0 < c)%N -> (0 < Hb)%N -> (0 < Nh)%N -> all prime S ->
    FixedWF D.
  Proof.
    move=> HC HK Hc HHb HNh HS; constructor;
      first [ exact: mkData_wf_m | exact: mkData_wf_PhiL_nonempty
            | exact: mkData_wf_PhiL | exact: mkData_wf_SE | assumption ].
  Qed.

End mkData_wf.

(** * 6. An exact mirror of the chord-tangent law on binary integers

    A triple (a, b, c) of binary integers with c <> 0 represents
    (a + b sqrt2) / c in F. The operations below mirror the field
    operations of [qe rat] (including the junk value of [qe_inv] at 0)
    and keep triples reduced (gcd 1, c > 0). [ec_addZ_ok] shows that the
    mirror of [ec_add] computes [ec_add], so [mulQn_mirror] computes the
    multiples of Q0 exactly by [vm_compute]. *)

Definition zt : Type := (Z * Z * Z)%type.

Definition tq (t : zt) : qe rat := let '(a, b, c) := t in QE (zr a / zr c) (zr b / zr c).
Definition wfz (t : zt) : Prop := snd t <> 0%ZZ.

Definition znorm (t : zt) : zt :=
  let '(a, b, c) := t in
  if (c =? 0)%ZZ then (0, 0, 1)%ZZ else
  let g0 := Z.gcd (Z.gcd a b) c in
  let g := if (c <? 0)%ZZ then (- g0)%ZZ else g0 in
  (a / g, b / g, c / g)%ZZ.

Arguments znorm : simpl never.

Lemma znorm_aux (a b c : Z) : c <> 0%ZZ ->
  let g0 := Z.gcd (Z.gcd a b) c in
  let g := if (c <? 0)%ZZ then (- g0)%ZZ else g0 in
  g <> 0%ZZ /\ (g | a)%ZZ /\ (g | b)%ZZ /\ (g | c)%ZZ.
Proof.
  move=> Hc g0 g.
  have Hg0 : g0 <> 0%ZZ by move=> /Z.gcd_eq_0 [_ ?].
  have Ha : (g0 | a)%ZZ := Z.divide_trans _ _ _ (Z.gcd_divide_l _ c) (Z.gcd_divide_l a b).
  have Hb : (g0 | b)%ZZ := Z.divide_trans _ _ _ (Z.gcd_divide_l _ c) (Z.gcd_divide_r a b).
  have Hc' : (g0 | c)%ZZ := Z.gcd_divide_r _ c.
  rewrite /g; case: (c <? 0)%ZZ.
  - split; first lia.
    by split; [ | split ]; apply/Z.divide_opp_l.
  - by [].
Qed.

Lemma znorm_wf t : wfz (znorm t).
Proof.
  case: t => [[a b] c]; rewrite /wfz /znorm.
  case: (Z.eqb_spec c 0) => Hc /=; first by [].
  move: (znorm_aux a b Hc) => /= [Hg [_ [_ [k Hk]]]].
  set g := (if (c <? 0)%ZZ then _ else _) in Hg Hk *.
  rewrite {1}Hk Z.div_mul //; move=> Hk0; apply: Hc; by rewrite Hk Hk0.
Qed.

Lemma div_cancel (x y g : rat) : g != 0 -> (x * g) / (y * g) = x / y.
Proof. by move=> Hg; rewrite -mulf_div divff // mulr1. Qed.

Lemma znorm_ok t : wfz t -> tq (znorm t) = tq t.
Proof.
  case: t => [[a b] c]; rewrite /wfz /= => Hc; rewrite /znorm.
  have -> : (c =? 0)%ZZ = false by apply/Z.eqb_neq.
  move: (znorm_aux a b Hc) => /= [Hg [[ka Hka] [[kb Hkb] [kc Hkc]]]].
  set g := (if (c <? 0)%ZZ then _ else _) in Hg Hka Hkb Hkc *.
  rewrite Hka Hkb Hkc !Z.div_mul // !zr_mul.
  by rewrite !div_cancel //; apply: zr_neq0.
Qed.

Definition zc (n : Z) : zt := (n, 0, 1)%ZZ.

Definition zadd (u v : zt) : zt :=
  let '(a1, b1, c1) := u in let '(a2, b2, c2) := v in
  znorm (a1 * c2 + a2 * c1, b1 * c2 + b2 * c1, c1 * c2)%ZZ.

Definition zmul (u v : zt) : zt :=
  let '(a1, b1, c1) := u in let '(a2, b2, c2) := v in
  znorm (a1 * a2 + 2 * (b1 * b2), a1 * b2 + b1 * a2, c1 * c2)%ZZ.

Definition zopp (u : zt) : zt := let '(a, b, c) := u in znorm (- a, - b, c)%ZZ.

Definition zsub (u v : zt) : zt := zadd u (zopp v).

Definition zinv (u : zt) : zt :=
  let '(a, b, c) := u in
  let N := (a * a - 2 * (b * b))%ZZ in
  if (N =? 0)%ZZ then znorm u else znorm (a * c, - (b * c), N)%ZZ.

Definition zdiv (u v : zt) : zt := zmul u (zinv v).

Definition zeqb (u v : zt) : bool :=
  let '(a1, b1, c1) := u in let '(a2, b2, c2) := v in
  (a1 * c2 =? a2 * c1)%ZZ && (b1 * c2 =? b2 * c1)%ZZ.

Arguments zadd : simpl never.
Arguments zmul : simpl never.
Arguments zopp : simpl never.
Arguments zsub : simpl never.
Arguments zinv : simpl never.
Arguments zdiv : simpl never.
Arguments zeqb : simpl never.
Arguments zc : simpl never.

Lemma wf_zadd u v : wfz (zadd u v). Proof. by case: u => [[? ?] ?]; case: v => [[? ?] ?]; apply: znorm_wf. Qed.
Lemma wf_zmul u v : wfz (zmul u v). Proof. by case: u => [[? ?] ?]; case: v => [[? ?] ?]; apply: znorm_wf. Qed.
Lemma wf_zopp u : wfz (zopp u). Proof. by case: u => [[? ?] ?]; apply: znorm_wf. Qed.
Lemma wf_zsub u v : wfz (zsub u v). Proof. exact: wf_zadd. Qed.
Lemma wf_zinv u : wfz (zinv u).
Proof. case: u => [[a b] c]; rewrite /zinv; case: ifP => _; exact: znorm_wf. Qed.
Lemma wf_zdiv u v : wfz (zdiv u v). Proof. exact: wf_zmul. Qed.
Lemma wf_zc n : wfz (zc n). Proof. by []. Qed.

Create HintDb zwf.
#[local] Hint Resolve wf_zadd wf_zmul wf_zopp wf_zsub wf_zinv wf_zdiv wf_zc : zwf.

Lemma Zmul_neq0 (x y : Z) : x <> 0%ZZ -> y <> 0%ZZ -> (x * y)%ZZ <> 0%ZZ.
Proof. lia. Qed.

Lemma tq_add u v : wfz u -> wfz v -> tq (zadd u v) = tq u + tq v.
Proof.
  case: u => [[a1 b1] c1]; case: v => [[a2 b2] c2] H1 H2; rewrite /wfz /= in H1 H2.
  rewrite /zadd znorm_ok; first by rewrite /wfz /=; lia.
  rewrite /tq qe_addE !zr_add !zr_mul; congr QE; rewrite addf_div ?zr_neq0 //.
Qed.

Lemma tq_mul u v : wfz u -> wfz v -> tq (zmul u v) = tq u * tq v.
Proof.
  case: u => [[a1 b1] c1]; case: v => [[a2 b2] c2] H1 H2; rewrite /wfz /= in H1 H2.
  rewrite /zmul znorm_ok; first by rewrite /wfz /=; lia.
  rewrite /tq.
  have Hc1 := zr_neq0 H1; have Hc2 := zr_neq0 H2.
  rewrite qe_mulE !zr_add !zr_mul zr2; congr QE; field; by rewrite Hc1 Hc2.
Qed.

Lemma tq_opp u : wfz u -> tq (zopp u) = - tq u.
Proof.
  case: u => [[a b] c] H; rewrite /wfz /= in H; rewrite /zopp znorm_ok // /tq qe_oppE !zr_opp.
  by rewrite !mulNr.
Qed.

Lemma tq_sub u v : wfz u -> wfz v -> tq (zsub u v) = tq u - tq v.
Proof. by move=> Hu Hv; rewrite /zsub tq_add ?tq_opp //; apply: wf_zopp. Qed.

Lemma tq_inv u : wfz u -> tq (zinv u) = (tq u)^-1.
Proof.
  case: u => [[a b] c] H; rewrite /wfz /= in H.
  have Hc := zr_neq0 H.
  set N := (a * a - 2 * (b * b))%ZZ.
  have HN : qe_norm (tq (a, b, c)) = zr N / (zr c * zr c).
  { rewrite /qe_norm /tq /= /N zr_sub !zr_mul zr2; field; by rewrite Hc. }
  have Hcond : (qe_norm (tq (a, b, c)) != 0) = ~~ (N =? 0)%ZZ.
  { by rewrite HN mulf_eq0 invr_eq0 mulf_eq0 (negbTE Hc) !orbF zr_eq0. }
  rewrite qe_invE /qe_inv Hcond /zinv -/N.
  case: (Z.eqb_spec N 0) => HN0 /=.
  - by rewrite znorm_ok.
  - have Hw : wfz ((a * c)%ZZ, (- (b * c))%ZZ, N) by [].
    rewrite (znorm_ok Hw) HN /tq /=.
    have HNz := zr_neq0 HN0.
    rewrite !zr_mul zr_opp zr_mul; congr QE; field; by rewrite HNz Hc.
Qed.

Lemma tq_div u v : wfz u -> wfz v -> tq (zdiv u v) = tq u / tq v.
Proof. by move=> Hu Hv; rewrite /zdiv tq_mul ?tq_inv //; apply: wf_zinv. Qed.

Lemma zr_div_eq (x y z t : Z) : y <> 0%ZZ -> t <> 0%ZZ ->
  (zr x / zr y == zr z / zr t) = (x * t =? z * y)%ZZ.
Proof.
  move=> Hy Ht; rewrite eqr_div ?zr_neq0 // -!zr_mul.
  by apply/eqP/Z.eqb_spec => [ /zr_inj | -> ].
Qed.

Lemma qe_eqE (p q r s : rat) : (QE p q == QE r s) = (p == r) && (q == s).
Proof. by []. Qed.

Lemma tq_eqb u v : wfz u -> wfz v -> (tq u == tq v) = zeqb u v.
Proof.
  case: u => [[a1 b1] c1]; case: v => [[a2 b2] c2] H1 H2; rewrite /wfz /= in H1 H2.
  by rewrite /tq /zeqb qe_eqE !zr_div_eq.
Qed.

Lemma tq_zc (n : nat) : tq (zc (Z.of_nat n)) = n%:R.
Proof. by rewrite /tq /zc zr1 !divr1 zr_nat zr0 qe_natE. Qed.

Definition aZ : zt := (-11243, 7950, 1)%ZZ.

Lemma tq_aZ : tq aZ = aE.
Proof. by rewrite aE_zq /tq /aZ zr1 !divr1 zq.unlock. Qed.

(* points *)
Definition ptq (p : option (zt * zt)) : pt rat :=
  match p with None => None | Some (x, y) => Some (tq x, tq y) end.

Definition wfp (p : option (zt * zt)) : Prop :=
  match p with None => True | Some (x, y) => wfz x /\ wfz y end.

Definition ec_addZ (p1 p2 : option (zt * zt)) : option (zt * zt) :=
  match p1, p2 with
  | None, _ => p2
  | _, None => p1
  | Some (x1, y1), Some (x2, y2) =>
      if zeqb x1 x2 then
        if zeqb y1 (zopp y2) then None
        else let l := zdiv (zadd (zmul (zc 3) (zmul x1 x1)) aZ) (zmul (zc 2) y1) in
             let x3 := zsub (zmul l l) (zmul (zc 2) x1) in
             Some (x3, zsub (zmul l (zsub x1 x3)) y1)
      else let l := zdiv (zsub y2 y1) (zsub x2 x1) in
           let x3 := zsub (zsub (zmul l l) x1) x2 in
           Some (x3, zsub (zmul l (zsub x1 x3)) y1)
  end.

Lemma wfp_ec_addZ p1 p2 : wfp p1 -> wfp p2 -> wfp (ec_addZ p1 p2).
Proof.
  case: p1 => [[x1 y1] | ]; case: p2 => [[x2 y2] | ] //= H1 H2.
  case: zeqb; [ case: zeqb | ]; rewrite /=; try split; auto with zwf.
Qed.

Ltac tq_push :=
  repeat first
    [ rewrite tq_sub; try by auto with zwf
    | rewrite tq_add; try by auto with zwf
    | rewrite tq_mul; try by auto with zwf
    | rewrite tq_div; try by auto with zwf
    | rewrite tq_inv; try by auto with zwf
    | rewrite tq_aZ
    | rewrite (tq_zc 3)
    | rewrite (tq_zc 2) ].

Lemma ec_addZ_ok p1 p2 : wfp p1 -> wfp p2 -> ec_add (ptq p1) (ptq p2) = ptq (ec_addZ p1 p2).
Proof.
  case: p1 => [[x1 y1] | ]; case: p2 => [[x2 y2] | ] //= [H1 H1'] [H2 H2'].
  rewrite tq_eqb //; case: zeqb.
  - rewrite -tq_opp // tq_eqb //; first exact: wf_zopp.
    case: zeqb => //=.
    tq_push; by rewrite !expr2.
  - rewrite /=; tq_push; by rewrite !expr2.
Qed.

(* the multiples of Q0, computed on binary integers *)
Definition Q0Z : zt * zt := ((799, -565, 1), (-31800, 22486, 1))%ZZ.

Lemma Q0_ptq : Some Q0 = ptq (Some Q0Z).
Proof. by rewrite /Q0 /= /tq zr1 !divr1 !zq.unlock. Qed.

Definition mulZn (k : nat) : option (zt * zt) := iter k (ec_addZ (Some Q0Z)) None.

Lemma mulQn_mirror (D : FixedData) : fd_P0 D = Q0 ->
  forall k, mulQn D k = ptq (mulZn k) /\ wfp (mulZn k).
Proof.
  move=> HP; elim=> [ | k [IH IHw] ]; first by [].
  have HQ : wfp (Some Q0Z) by [].
  rewrite /mulQn /mulZn !iterS -/(mulQn D k) -/(mulZn k) IH HP Q0_ptq.
  split; [ exact: (ec_addZ_ok HQ IHw) | exact: (wfp_ec_addZ HQ IHw) ].
Qed.

Lemma mkData_mulQn C S Hb c Kset Nh Ch k :
  mulQn (mkData C S Hb c Kset Nh Ch) k = ptq (mulZn k).
Proof. by case: (mulQn_mirror (D := mkData C S Hb c Kset Nh Ch) erefl k). Qed.

(** * 7. Computational facts about Q0 (stepping stones for E2, O_F1)

    The place v of F above 17 with sqrt2 |-> 6 (6^2 = 36 = 2 mod 17).
    Reduction of a reduced triple (a, b, c) with 17 not dividing c is
    (a + 6 b) / c mod 17. *)

Definition invmod (r x : Z) : Z := powmod x (r - 2) r.

(* the chord-tangent law on y^2 = x^3 + a x over F_r, coordinates in [0, r) *)
Definition ecF_add (r a : Z) (p1 p2 : option (Z * Z)) : option (Z * Z) :=
  match p1, p2 with
  | None, _ => p2
  | _, None => p1
  | Some (x1, y1), Some (x2, y2) =>
      if (x1 =? x2)%ZZ then
        if (Z.modulo (y1 + y2) r =? 0)%ZZ then None
        else let l := Z.modulo ((3 * x1 * x1 + a) * invmod r (2 * y1)) r in
             let x3 := Z.modulo (l * l - 2 * x1) r in
             Some (x3, Z.modulo (l * (x1 - x3) - y1) r)
      else let l := Z.modulo ((y2 - y1) * invmod r (x2 - x1)) r in
           let x3 := Z.modulo (l * l - x1 - x2) r in
           Some (x3, Z.modulo (l * (x1 - x3) - y1) r)
  end%ZZ.

(* Hensel lift of s (s^2 = 2 mod r, r odd prime not dividing s) to a
   square root of 2 modulo R = r^n *)
Definition hensel (r s : Z) (n : nat) : Z :=
  let R := (r ^ Z.of_nat n)%ZZ in
  let phi := (r ^ (Z.of_nat n - 1) * (r - 1))%ZZ in
  iter n (fun t => Z.modulo (t - (t * t - 2) * powmod (2 * t) (phi - 1) R) R)%ZZ s.

(* reduction at the place sqrt2 |-> s of (a + b sqrt2)/c: with e = v_r(c),
   compute a + s' b modulo r^(e+1) for the lift s' of s; the element is
   integral iff r^e divides it, and then its residue is
   ((a + s' b)/r^e) (c/r^e)^{-1} mod r. None: a pole. *)
Definition red_elt (r s : Z) (t : zt) : option Z :=
  let '(a, b, c) := t in
  let e := vZ r c in
  let R := (r ^ Z.of_nat e.+1)%ZZ in
  let n := Z.modulo (a + hensel r s e.+1 * b) R in
  let re := (r ^ Z.of_nat e)%ZZ in
  if (Z.modulo n re =? 0)%ZZ
  then Some (Z.modulo ((n / re) * invmod r (c / re)) r)%ZZ
  else None.

(* x = (a + b sqrt2)/c has a pole at the place: r | c, r does not divide a + s b *)
Definition pole_at (r s : Z) (t : zt) : bool :=
  let '(a, b, c) := t in (Z.modulo c r =? 0)%ZZ && negb (Z.modulo (a + s * b) r =? 0)%ZZ.

Definition red_pt (r s : Z) (p : option (zt * zt)) : option (option (Z * Z)) :=
  match p with
  | None => Some None
  | Some (x, y) =>
      match red_elt r s x, red_elt r s y with
      | Some u, Some v => Some (Some (u, v))
      | _, _ => None
      end
  end.

Definition aEmod (r s : Z) : Z := Z.modulo (-11243 + 7950 * s) r.

Definition Q0mod (r s : Z) : option (Z * Z) :=
  if red_pt r s (Some Q0Z) is Some p then p else None.

Definition mulF (r s : Z) (k : nat) : option (Z * Z) :=
  iter k (ecF_add r (aEmod r s) (Q0mod r s)) None.

(* number of points of y^2 = x^3 + a x over F_r, including O *)
Definition countF (r a : Z) : nat :=
  S (length (filter (fun xy : Z * Z => Z.modulo (xy.2 * xy.2 - (xy.1 * xy.1 * xy.1 + a * xy.1)) r =? 0)%ZZ
     (flat_map (fun x => map (fun y => (x, y)) (map Z.of_nat (iota 0 (Z.to_nat r))))
               (map Z.of_nat (iota 0 (Z.to_nat r)))))).

Definition order_is (r s : Z) (n : nat) : bool :=
  (if mulF r s n is None then true else false) &&
  forallb (fun k => if mulF r s k is None then false else true) (iota 1 n.-1).

(* sqrt2 |-> 6 and sqrt2 |-> 11 are the two places above 17 *)
Lemma sqrt2_mod17 : (Z.modulo (6 * 6) 17 = 2 /\ Z.modulo (11 * 11) 17 = 2)%ZZ.
Proof. by vm_compute. Qed.

(* the reductions of Q0 and of E at the two places above 17 *)
Lemma Q0mod17 : Q0mod 17 6 = Some (10, 11)%ZZ /\ aEmod 17 6 = 9%ZZ /\
                Q0mod 17 11 = Some (7, 3)%ZZ /\ aEmod 17 11 = 13%ZZ.
Proof. by vm_compute. Qed.

(* #E(k_v) = 20 at sqrt2 |-> 6 and 16 at sqrt2 |-> 11 *)
Lemma countF17 : countF 17 (aEmod 17 6) = 20%N /\ countF 17 (aEmod 17 11) = 16%N.
Proof. by vm_compute. Qed.

(* the reduction of Q0 has order exactly 10 at sqrt2 |-> 6 (and 4 at 11) *)
Lemma Q0mod17_order : order_is 17 6 10 = true /\ order_is 17 11 4 = true.
Proof. by vm_compute. Qed.

(* the exact multiples kQ0, k = 1..10, are affine points *)
(* 2 Q0 = (1641/8 - 145 sqrt2, -15465/4 + (87483/32) sqrt2) *)
Lemma mulZn2 : mulZn 2 = Some ((1641, -1160, 8), (-123720, 87483, 32))%ZZ.
Proof. by vm_compute. Qed.

Lemma mkData_mulQ2 C S Hb c Kset Nh Ch :
  mulQn (mkData C S Hb c Kset Nh Ch) 2 = Some (tq (1641, -1160, 8)%ZZ, tq (-123720, 87483, 32)%ZZ).
Proof. by rewrite mkData_mulQn mulZn2. Qed.

Lemma mulZn_affine : forallb (fun k => if mulZn k is Some _ then true else false) (iota 1 10) = true.
Proof. by vm_compute. Qed.

(* for k = 1..9, kQ0 is integral at the place sqrt2 |-> 6 above 17 and its
   reduction (computed by [red_elt]) is k times the reduction of Q0
   (computed in E(F_17)): on these instances, reduction commutes with the
   group law. (The denominators of 4Q0 and 8Q0 are divisible by 17, since
   these points reduce to O at the other place sqrt2 |-> 11; at
   sqrt2 |-> 6 they are integral, which [red_elt] detects with a Hensel
   lift of the square root of 2.) [red_elt] is a computational device; its
   agreement with the residue map of the place is part of TODO (b). *)
Lemma mulZn_red17 :
  forallb (fun k => if red_pt 17 6 (mulZn k) is Some p then
                      if p is Some (u, v) then
                        if mulF 17 6 k is Some (u', v') then (u =? u')%ZZ && (v =? v')%ZZ else false
                      else false
                    else false) (iota 1 9) = true.
Proof. by vm_compute. Qed.

(* 10 Q0 has a pole at the place sqrt2 |-> 6: in reduced form
   x(10 Q0) = (a + b sqrt2)/c and y(10 Q0) = (a' + b' sqrt2)/c' with
   17 | c, 17 | c', and 17 dividing neither a + 6 b nor a' + 6 b'. *)
Lemma mulZn10_pole :
  (if mulZn 10 is Some (x, y) then pole_at 17 6 x && pole_at 17 6 y else false) = true.
Proof. by vm_compute. Qed.

(* the transferred statement for any data built by [mkData] *)
Lemma mkData_mulQ10 C S Hb c Kset Nh Ch :
  exists x y : zt, mulQn (mkData C S Hb c Kset Nh Ch) 10 = Some (tq x, tq y) /\
    wfz x /\ wfz y /\ pole_at 17 6 x /\ pole_at 17 6 y.
Proof.
  have [H Hw] := mulQn_mirror (D := mkData C S Hb c Kset Nh Ch) erefl 10.
  move: H Hw mulZn10_pole; case: (mulZn 10) => [[x y] | ] //= H [Hx Hy] /andP [Px Py].
  by exists x, y.
Qed.

(** BRIDGING TODOs (for task P11; no Admitted here):
    (a) Valuation at the place. For [v] with [is_place_above v 17] and
        v(sqrt2F - 6) > 0, and a reduced triple t with [pole_at 17 6 t]:
        v (tq t) < 0. (v >= 0 on Z by ultrametricity and v(1) = 0;
        v(c) >= v(17) = 1; a + b sqrt2 = (a + 6b) + b (sqrt2 - 6) with
        v(a + 6b) = 0 by Bezout with 17.) With [mkData_mulQ10] this gives
        [red_ord false v (mulQ D 10)]: 10 Q0 lies in the kernel of
        reduction at v, the input of the kernel-of-reduction argument for
        E2 (FEASIBILITY.md Sec. 2.4).
    (b) Reduction homomorphism. For integral points at v, reduction
        commutes with [ec_add] (when the sum is integral too). Only
        instances of it are checked above ([mulZn_red17]); the general
        lemma is not needed for (a) and E2, but it is needed for the torsion
        bound E(F)_tors -> E(k_v) and for HCov's integer tests. *)
