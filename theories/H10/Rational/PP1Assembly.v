(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Prop par:pole-parity (1) (integer completeness of Phi) modulo Lemma
   par:global-point (PLAN.md, Phase 3, task Q4 = milestone L1 of
   PP1_DESIGN.md; 03-parity.tex, Sec. 3.2 and 3.4).

   MAIN RESULTS (all PROVED; Print Assumptions: [Classical_Prop.classic] only,
   from [PrimePatterns.new_prime_nodir]; everything else is closed):
   - [cross_squares]: Lemma par:cross-squares, for the local choices
     m, m_d, t of Sec. 3.2 (Section CrossSquares, Sec. 10 below), with
     beta = [sqk b'], theta = [sqk H'], B = [sqkB b'], J = [sqkB H'];
     [cross_squares_nat] restates its consequences as congruences and
     Legendre symbols;
   - [sim_matrices] (Sec. 6, for abstract B, J with the properties
     (par:fixed-symbol-sums), (par:cross-symbol-sums)) and
     [simultaneous_matrices] (Sec. 14, for the B, J of par:cross-squares):
     Lemma par:simultaneous-matrices (primes with prescribed Legendre
     symbols from [PrimePatterns.new_prime_nodir], Dirichlet's theorem
     for quadratic characters, proved in Phase 4);
   - [choose_t_gen] (Sec. 11): the choice of t by weak approximation
     ([Hensel.weak_approx_inf], explicit precisions);
   - [PP1_int] (Sec. 15): the completion of the proof of
     Prop par:pole-parity (1): Phi_math L b for every integer b and all
     lists L with [CoversM L], [CoversD L];
   - [PP1_paper_of_global_point : global_point_El -> PP1_paper]
     and [PP1_L0_of_global_point : global_point_El -> PP1_L0].
     The paper's argument uses the lists only through (par:b-prime-choices)
     and (par:d-choices), so it is proved for all lists ([PP1_paper]); the
     nonemptiness/nonzero side conditions of [PP1_paper] are not needed.

   HYPOTHESES (premises of the final theorems, no Axiom):
   - [global_point_El] (Sec. 12), "TO-MERGE from SelDescent.v /
     TwoConverse.v": Lemma par:descent + Lemma par:global-point in the
     elementary form of the conclusion of [TwoConverseSel2_El] for the
     class gamma = (beta, 1). For admissible l (l > 0 squarefree,
     l = 3 mod 4, l = 2 mod 3, hence prime to 6) whose support
     Q = primes |l| contains B (beta = prod B, beta = 1 mod 8 i.e. a
     square in Q_2, beta = 2 mod 3 i.e. the unit nonsquare class at 3,
     so B is nonempty) and a prime outside B, and with
     ker K = <1, 1_B> ([ker_target]) and lambda not in im K
     ([lam_notin_im]), the curve E_l has a rational point (x, y) with
     x <> 0, x in beta Q^x2, x - l in Q^x2. Coordinates: TwoConverse.v uses
     the Kummer coordinates (x, x - l); the paper's (x + 3l, x - l) give the
     same class (beta, 1) since x = (x + 3l)(x - l) mod squares. To be
     discharged (task Q5b) by [TwoConverse_El_point] (from
     [TwoConverseSel2_El]) and Lemma par:descent (SelDescent.v):
     in_Sel2 l (beta, 1), every Selmer class in the span of tau_l, tau_3,
     (beta, 1), and (beta, 1) not in the span of tau_l, tau_3.
   (Until Phase 4 there was a second hypothesis, Dirichlet's theorem on
   primes in arithmetic progressions, used only in [new_prime] (Sec. 5).
   It is now discharged: [new_prime] is [PrimePatterns.new_prime_nodir],
   Dirichlet's theorem for quadratic characters, proved in RSeq.v, RLog.v,
   DChar.v, DirichletL.v, DirichletQuad.v, PrimePatterns.v.)

   TRANSLATION OF THE PAPER'S OBJECTS.
   - Local squares: "x in Q_q^{x2}" is [PhiCovering.locsq q x] (equivalent
     to the "for all k" form [Hensel.is_locsq], [Hensel.locsq_is_locsq]);
     "unit nonsquare class of Q_3" is [PhiCovering.unit_nonsq3].
   - "the unique positive squarefree integer representing the square class"
     of x > 0 is [sqk x] = prod_{p in sqkB x} p, sqkB x = the primes with
     odd valuation ([sqk_sq], [sqkB_mem]).
   - The nonsquare bit [a/q] in F_2 = 'F_2 is [nsq_bit a q] (= 1 iff the
     Legendre symbol (a/q) is -1); s_i = [-1/q_i], lambda_i = [3/q_i];
     (K u)_i = sum_{j <> i} [q_j/q_i] (u_j + u_i) is [Kmat Q u i]
     (par:matrices), vectors are functions nat -> F_2 restricted to Q.

   PROOF OF par:simultaneous-matrices: as in the paper (K^# = K + lambda a^t,
   T = Id - 1_B a^t, K = K^# T, the deleted matrix M, the block M_0 =
   [[A, C], [C^t, 0]]), with these choices made explicit:
   - C has the columns e_{b*} + e_b (b in B \ {b*}) (a "star"); the auxiliary
     prime i_b of I paired with b has [i_b/b*] = [i_b/b] = 1, all other
     symbols incident with I zero; q0 = 7 mod 8, q0 = 1 mod 3, I = 1 mod 8,
     I = 1 mod 3 (types (1,1), (0,0));
   - instead of the determinant / multilinear-polynomial argument, the
     J-diagonal toggles are chosen one at a time: if the principal block on
     Q \ {j} is nonsingular, then the matrix or its j-th diagonal toggle is
     nonsingular ([toggle], [toggles]); nonsingularity (injectivity on F_2^Q)
     is decided by enumerating F_2^Q ([injbF2]), so no classical axiom is used;
   - the primes are realized successively: first I (all symbols fixed),
     then the toggle bits from the actual symbols of B, J, I, then q0.

   CHOICE OF t (Sec. 3.2, "Weak approximation satisfies all these
   conditions"): at q in S(m) a rational t_q with v_q(1 - d t_q^2) >= K_q,
   K_q = |v_q(b')| + |v_q(b)| + 3 ([local_target]), at
   q in Supp(m_d) \ S(m) the target 0 with precision |v_q(d)| + 1, at the
   real place an integer square root ([real_target]); then H' is a local
   square at S(m) ([H'_locsq]), positive ([real_H'_pos]), and
   v_q(d t^2) > 0 at Supp(m_d) \ S(m). *)

From Stdlib Require Import ZArith Lia Ring Field List.
From mathcomp Require Import boot order algebra finite_group cyclic finfield.
From Undecidability.H10.Rational
  Require Import RatUtil PosExistential FixedData ExplicitData PaperInputs PhiCovering RatVal OrdinaryFacts
                 Hensel QuadRec TwoConverse.
From Undecidability.H10.Rational Require PrimePatterns.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.



(** * 1. Linear algebra over F_2 on finite index lists *)

Abbreviation F2 := 'F_2.

Lemma F2_cases (x : F2) : x = 0 \/ x = 1.
Proof. case: x => [[|[|n]] Hn] /=; [left|right|]; try (by apply/val_inj). by []. Qed.

Lemma F2_xx (x : F2) : x + x = 0.
Proof. by case: (F2_cases x) => ->; apply/val_inj. Qed.

Lemma F2_opp (x : F2) : - x = x.
Proof. by apply/eqP; rewrite eq_sym -subr_eq0 opprK F2_xx. Qed.

Lemma F2_10 : (1 : F2) != 0.
Proof. by []. Qed.

Lemma F2_11 : (1 + 1 : F2) = 0.
Proof. exact: F2_xx. Qed.

Lemma F2_rt : ring_theory (0 : F2) 1 +%R *%R (fun x y => x - y) -%R (@eq F2).
Proof.
  split; [ exact: add0r | exact: addrC | exact: addrA | exact: mul1r | exact: mulrC
         | exact: mulrA | exact: mulrDl | done | exact: subrr ].
Qed.

Add Ring F2_ring : F2_rt.

(* x = y iff x + y = 0 *)
Lemma F2_eq (x y : F2) : (x + y = 0) <-> x = y.
Proof.
  split => [H | ->]; last exact: F2_xx.
  by have := congr1 (fun z => z + y) H; rewrite add0r -addrA F2_xx addr0.
Qed.

Lemma F2_sub (x y : F2) : x - y = x + y.
Proof. by rewrite F2_opp. Qed.

(* indicator *)
Definition bitF2 (b : bool) : F2 := b%:R.

Lemma ind_true : bitF2 true = 1. Proof. by []. Qed.
Lemma ind_false : bitF2 false = 0. Proof. by []. Qed.

Lemma ind_mul (a b : bool) : bitF2 (a && b) = bitF2 a * bitF2 b.
Proof. by case: a; case: b; rewrite /bitF2 /= ?mulr1 ?mulr0 ?mul0r. Qed.

Section Sums.

  Implicit Types (Q : seq nat) (g : nat -> F2).

  Lemma sum_ind_eq Q a g : uniq Q ->
    \sum_(c <- Q) bitF2 (c == a) * g c = bitF2 (a \in Q) * g a.
  Proof.
    elim: Q => [ | q Q IH ] /=; first by rewrite big_nil /bitF2 /= mul0r.
    move=> /andP [ Hq HQ ]; rewrite big_cons IH // in_cons.
    case: (eqVneq q a) => [ <- | Hne ] /=.
    - by rewrite (negbTE Hq) /bitF2 /= mul1r mul0r addr0.
    - by rewrite /bitF2 /= mul0r add0r.
  Qed.

  Lemma sum_ind_eq' Q a g : uniq Q -> a \in Q ->
    \sum_(c <- Q) bitF2 (c == a) * g c = g a.
  Proof. by move=> HQ Ha; rewrite sum_ind_eq // Ha mul1r. Qed.

  Lemma sum_ind2 Q a b g : uniq Q -> a \in Q -> b \in Q -> a != b ->
    \sum_(c <- Q) bitF2 ((c == a) || (c == b)) * g c = g a + g b.
  Proof.
    move=> HQ Ha Hb Hab.
    rewrite -(sum_ind_eq' g HQ Ha) -(sum_ind_eq' g HQ Hb) -big_split /=.
    apply: eq_bigr => c _; case: (eqVneq c a) => [ -> | Hca ] /=.
    - by rewrite (negbTE Hab) /bitF2 /= mul1r mul0r addr0.
    - by rewrite /bitF2 /= mul0r add0r.
  Qed.

  Lemma sum_ind2c Q a b : uniq Q -> a \in Q -> b \in Q -> a != b ->
    \sum_(c <- Q) bitF2 ((c == a) || (c == b)) = 0.
  Proof.
    move=> HQ Ha Hb Hab; rewrite -[RHS](F2_xx 1).
    rewrite -(sum_ind2 (fun _ => 1) HQ Ha Hb Hab); apply: eq_bigr => c _; by rewrite mulr1.
  Qed.

  Lemma sum_F2_ext Q g h : (forall c, c \in Q -> g c = h c) ->
    \sum_(c <- Q) g c = \sum_(c <- Q) h c.
  Proof. move=> H; rewrite big_seq [RHS]big_seq; apply: eq_bigr => c; exact: H. Qed.

End Sums.

(** matrices and vectors indexed by nat, restricted to a finite list Q *)

Definition mvF2 (Q : seq nat) (M : nat -> nat -> F2) (x : nat -> F2) (i : nat) : F2 :=
  \sum_(j <- Q) M i j * x j.

Definition injF2 (Q : seq nat) (M : nat -> nat -> F2) : Prop :=
  forall x : nat -> F2, (forall i, i \in Q -> mvF2 Q M x i = 0) -> forall i, i \in Q -> x i = 0.

Lemma mv_ext Q M N x y i : (forall j, j \in Q -> M i j = N i j) -> (forall j, j \in Q -> x j = y j) ->
  mvF2 Q M x i = mvF2 Q N y i.
Proof. move=> HM Hx; apply: sum_F2_ext => j Hj; by rewrite HM ?Hx. Qed.

Lemma mv_cons q Q M x i : mvF2 (q :: Q) M x i = M i q * x q + mvF2 Q M x i.
Proof. by rewrite /mvF2 big_cons. Qed.

Lemma mv_add Q M x y i : mvF2 Q M (fun j => x j + y j) i = mvF2 Q M x i + mvF2 Q M y i.
Proof. rewrite /mvF2 -big_split /=; apply: eq_bigr => j _; ring. Qed.

Lemma inj_ext Q M N : (forall p c, p \in Q -> c \in Q -> M p c = N p c) -> injF2 Q M -> injF2 Q N.
Proof.
  move=> H HM x Hx; apply: HM => i Hi; rewrite -(Hx i Hi); apply: mv_ext => // j Hj; exact: H.
Qed.

Lemma inj_perm Q Q' M : perm_eq Q Q' -> injF2 Q M -> injF2 Q' M.
Proof.
  move=> Hp HM x Hx i Hi.
  apply: HM; last by rewrite (perm_mem Hp).
  move=> j Hj; rewrite /mvF2 (perm_big _ Hp); apply: Hx; by rewrite -(perm_mem Hp).
Qed.

(** decidability of [injF2] by enumeration of the vectors on Q *)

Definition updF2 (f : nat -> F2) (q : nat) (c : F2) : nat -> F2 := fun i => if i == q then c else f i.

Fixpoint vecsF2 (Q : seq nat) : seq (nat -> F2) :=
  if Q is q :: Q' then flatten (map (fun f => [:: updF2 f q 0; updF2 f q 1]) (vecsF2 Q')) else [:: fun _ => 0].

Lemma In_flatten_map (A B : Type) (F : A -> seq B) (s : seq A) (y : B) :
  List.In y (flatten (map F s)) <-> exists x, List.In x s /\ List.In y (F x).
Proof.
  elim: s => [ | a s IH ] /=; first by split => // [ [ ? [ [] ] ] ].
  rewrite -/(flatten (map F s)).
  have E : forall (l1 l2 : seq B), List.In y (l1 ++ l2) <-> List.In y l1 \/ List.In y l2.
  { move=> l1 l2; rewrite -List.in_app_iff; done. }
  rewrite E IH; split.
  - case=> [ H | [ x [ Hx Hy ] ] ]; [ by exists a; split; [ left | ] | by exists x; split; [ right | ] ].
  - case=> x [ [ -> | Hx ] Hy ]; [ by left | by right; exists x ].
Qed.

Lemma vecs_complete Q (x : nat -> F2) : exists y, List.In y (vecsF2 Q) /\ forall i, i \in Q -> y i = x i.
Proof.
  elim: Q => [ | q Q [ y [ Hy Hyx ] ] ] /=; first by exists (fun _ => 0); split; [ left | ].
  exists (updF2 y q (x q)); split.
  - apply/In_flatten_map; exists y; split => //.
    by case: (F2_cases (x q)) => ->; [ left | right; left ].
  - move=> i; rewrite in_cons /updF2; case: eqP => [ -> // | _ ] /= Hi; exact: Hyx.
Qed.

Definition allLF2 (A : Type) (P : A -> bool) (s : seq A) : bool := all P s.

Lemma allL_In (A : Type) (P : A -> bool) (s : seq A) : all P s -> forall y, List.In y s -> P y.
Proof. elim: s => [ | a s IH ] //= /andP [ Ha Hs ] y [ <- // | Hy ]; exact: IH. Qed.

Lemma allL_notIn (A : Type) (P : A -> bool) (s : seq A) : ~~ all P s -> exists y, List.In y s /\ ~~ P y.
Proof.
  elim: s => [ | a s IH ] //=; rewrite negb_and; case: (boolP (P a)) => /= Ha H.
  - have [ y [ Hy Hy' ] ] := IH H; exists y; split => //; by right.
  - by exists a; split; [ left | ].
Qed.

Definition injbF2 (Q : seq nat) (M : nat -> nat -> F2) : bool :=
  all (fun y => ~~ all (fun i => mvF2 Q M y i == 0) Q || all (fun i => y i == 0) Q) (vecsF2 Q).

Lemma injbP Q M : injbF2 Q M -> injF2 Q M.
Proof.
  move=> H x Hx i Hi.
  have [ y [ Hy Hyx ] ] := vecs_complete Q x.
  have := allL_In H Hy => /orP [ /negP [] | /allP Hy0 ].
  - apply/allP => j Hj; apply/eqP; rewrite -(Hx j Hj); apply: mv_ext => // k Hk; exact: Hyx.
  - by rewrite -(Hyx i Hi); apply/eqP; exact: Hy0.
Qed.

Lemma injbN Q M : ~~ injbF2 Q M -> exists x, (forall i, i \in Q -> mvF2 Q M x i = 0) /\ exists i, i \in Q /\ x i = 1.
Proof.
  move=> /allL_notIn [ y [ _ ] ]; rewrite negb_or negbK => /andP [ /allP H1 /allPn [ i Hi Hyi ] ].
  exists y; split; first by move=> j Hj; apply/eqP; exact: H1.
  exists i; split => //; case: (F2_cases (y i)) => // E; by rewrite E eqxx in Hyi.
Qed.

(** toggling one diagonal entry *)

Definition togF2 (j : nat) (M : nat -> nat -> F2) : nat -> nat -> F2 :=
  fun p c => M p c + bitF2 ((p == j) && (c == j)).

Lemma toggle Q j M : uniq (j :: Q) -> injF2 Q M -> injF2 (j :: Q) M \/ injF2 (j :: Q) (togF2 j M).
Proof.
  move=> /= /andP [ HjQ HQ ] HM.
  case Hb : (injbF2 (j :: Q) M); first by left; exact: injbP.
  right; have [ x [ Hx [ i0 [ Hi0 Hxi0 ] ] ] ] := injbN (negbT Hb).
  (* rows of Q are unchanged by the toggle *)
  have Hrow : forall z i, i \in Q -> mvF2 (j :: Q) (togF2 j M) z i = mvF2 (j :: Q) M z i.
  { move=> z i Hi; apply: mv_ext => // k _; rewrite /togF2.
    have -> : (i == j) = false by apply/negbTE; apply: contraNneq HjQ => <-.
    by rewrite /bitF2 /= addr0. }
  (* x j = 1 *)
  have Hxj : x j = 1.
  { case: (F2_cases (x j)) => // Hxj0; exfalso.
    have Hx0 : forall i, i \in Q -> x i = 0.
    { apply: HM => i Hi; have := Hx i; rewrite in_cons Hi orbT mv_cons Hxj0 mulr0 add0r; by apply. }
    move: Hi0 Hxi0; rewrite in_cons => /orP [ /eqP -> | Hi0 ]; first by rewrite Hxj0.
    by rewrite Hx0. }
  move=> y Hy.
  case: (F2_cases (y j)) => Hyj.
  - (* y j = 0 *)
    have Hy0 : forall i, i \in Q -> y i = 0.
    { apply: HM => i Hi; have := Hy i; rewrite in_cons Hi orbT Hrow // mv_cons Hyj mulr0 add0r; by apply. }
    move=> i; rewrite in_cons => /orP [ /eqP -> // | Hi ]; exact: Hy0.
  - (* y j = 1: z = x + y vanishes *)
    exfalso.
    set z := fun i => x i + y i.
    have Hz0 : forall i, i \in Q -> z i = 0.
    { apply: HM => i Hi.
      have E := mv_add (j :: Q) M x y i; rewrite mv_cons in E.
      move: E; rewrite /z Hxj Hyj F2_xx mulr0 add0r => E.
      rewrite E.
      have := Hx i; rewrite in_cons Hi orbT => /(_ isT) ->.
      have := Hy i; rewrite in_cons Hi orbT Hrow // => /(_ isT) ->.
      by rewrite addr0. }
    have Exy : forall i, i \in j :: Q -> x i = y i.
    { move=> i; rewrite in_cons => /orP [ /eqP -> | Hi ]; first by rewrite Hxj Hyj.
      by apply/F2_eq; exact: Hz0. }
    have := Hy j; rewrite in_cons eqxx /= => /(_ isT).
    have -> : mvF2 (j :: Q) (togF2 j M) y j = mvF2 (j :: Q) M y j + y j.
    { rewrite /mvF2 /togF2.
      have -> : \sum_(k <- j :: Q) (M j k + bitF2 ((j == j) && (k == j))) * y k
              = \sum_(k <- j :: Q) M j k * y k + \sum_(k <- j :: Q) bitF2 (k == j) * y k.
      { rewrite -big_split /=; apply: eq_bigr => k _; rewrite eqxx /=; ring. }
      by rewrite sum_ind_eq' //= ?HQ ?HjQ // mem_head. }
    have -> : mvF2 (j :: Q) M y j = mvF2 (j :: Q) M x j by apply: mv_ext => // k Hk; rewrite Exy.
    by rewrite (Hx j (mem_head _ _)) add0r Hyj.
Qed.

(** toggling the diagonal entries on a list J *)

Definition dgF2 (J : seq nat) (t : nat -> F2) (M : nat -> nat -> F2) : nat -> nat -> F2 :=
  fun p c => M p c + bitF2 ((p == c) && (p \in J)) * t p.

Lemma toggles (J R : seq nat) (M : nat -> nat -> F2) : uniq (J ++ R) -> injF2 R M ->
  exists t : nat -> F2, injF2 (J ++ R) (dgF2 J t M).
Proof.
  elim: J => [ | j J IH ] /=.
  - move=> _ HM; exists (fun _ => 0); apply: inj_ext HM => p c _ _; by rewrite /dgF2 mulr0 addr0.
  - move=> /andP [ Hj HJ ] HM.
    have [ t' Ht' ] := IH HJ HM.
    have HjJ : j \notin J by apply: contra Hj; rewrite mem_cat => ->.
    have Hu : uniq (j :: J ++ R) by rewrite /= Hj HJ.
    case: (toggle Hu Ht') => [ H | H ].
    + exists (updF2 t' j 0); apply: inj_ext H => p c _ _.
      rewrite /dgF2 /updF2 in_cons; case: (eqVneq p j) => [ -> | Hpj ] /=.
      * by rewrite (negbTE HjJ) andbF /bitF2 /= !mulr0 !mul0r.
      * by [].
    + exists (updF2 t' j 1); apply: inj_ext H => p c _ _.
      rewrite /dgF2 /togF2 /updF2 in_cons; case: (eqVneq p j) => [ -> | Hpj ] /=.
      * by rewrite (negbTE HjJ) andbF andbT /bitF2 /= mul0r addr0 mulr1 eq_sym.
      * by rewrite /bitF2 /= ?andbF ?addr0.
Qed.

(** * 2. The matrix K of par:matrices and the reduction to a deleted matrix *)

Section KMatrix.

  (* A p c : the bit [q_c / q_p] (row p, column c); lam p : the bit [3 / q_p] *)
  Variable A : nat -> nat -> F2.

  (* (K u)_i = sum_{j <> i} [q_j/q_i] (u_j + u_i)   (par:matrices) *)
  Definition KmatA (Q : seq nat) (u : nat -> F2) (i : nat) : F2 :=
    \sum_(j <- Q | j != i) A i j * (u j + u i).

  Definition indB (B : seq nat) : nat -> F2 := fun i => bitF2 (i \in B).

  (* ker K = <1, 1_B> *)
  Definition ker_targetA (Q B : seq nat) : Prop :=
    forall u : nat -> F2, (forall i, i \in Q -> KmatA Q u i = 0) <->
      exists c c' : F2, forall i, i \in Q -> u i = c + c' * indB B i.

  (* lambda not in im K *)
  Definition lam_notinA (lam : nat -> F2) (Q : seq nat) : Prop :=
    ~ exists u : nat -> F2, forall i, i \in Q -> KmatA Q u i = lam i.

  Lemma KmatA_ext Q u v i : i \in Q -> (forall j, j \in Q -> u j = v j) -> KmatA Q u i = KmatA Q v i.
  Proof.
    move=> Hi H; rewrite /KmatA big_seq_cond [RHS]big_seq_cond; apply: eq_bigr => j /andP [ Hj _ ]; by rewrite !H.
  Qed.

  Lemma KmatA_add Q u v i : KmatA Q (fun j => u j + v j) i = KmatA Q u i + KmatA Q v i.
  Proof. rewrite /KmatA -big_split /=; apply: eq_bigr => j _; ring. Qed.

  Lemma KmatA_scale Q (c : F2) u i : KmatA Q (fun j => c * u j) i = c * KmatA Q u i.
  Proof. rewrite /KmatA big_distrr /=; apply: eq_bigr => j _; ring. Qed.

  Lemma KmatA_const Q (c : F2) i : KmatA Q (fun _ => c) i = 0.
  Proof. rewrite /KmatA big1 // => j _; by rewrite F2_xx mulr0. Qed.

  Lemma KmatA_addc Q u (c : F2) i : KmatA Q (fun j => u j + c) i = KmatA Q u i.
  Proof. by rewrite KmatA_add KmatA_const addr0. Qed.

  Lemma KmatA_cons q Q u i : q != i -> KmatA (q :: Q) u i = A i q * (u q + u i) + KmatA Q u i.
  Proof. move=> Hq; by rewrite /KmatA big_cons Hq. Qed.

  (* the matrix with diagonal sum_{k <> p} A p k *)
  Definition Kd (Q : seq nat) (p c : nat) : F2 :=
    if p == c then \sum_(k <- Q | k != p) A p k else A p c.

  (* the deleted matrix of the proof of par:simultaneous-matrices:
     K^# = K + lambda a^t with a = e_{q0} + e_{bs}, row and column q0 deleted;
     w p = A p q0 is the contribution of q0 to the diagonal *)
  Definition Mdel (Q : seq nat) (w lam : nat -> F2) (bs : nat) (p c : nat) : F2 :=
    Kd Q p c + bitF2 (p == c) * w p + lam p * bitF2 (c == bs).

  Lemma mv_Kd Q x p : uniq Q -> p \in Q -> mvF2 Q (Kd Q) x p = KmatA Q x p.
  Proof.
    move=> HQ Hp; rewrite /mvF2 (bigD1_seq p Hp HQ) /= /Kd eqxx /KmatA big_distrl /=.
    rewrite -big_split /=; apply: eq_bigr => j Hj; rewrite eq_sym (negbTE Hj); ring.
  Qed.

  Lemma mv_Mdel Q w lam bs x p : uniq Q -> p \in Q -> bs \in Q ->
    mvF2 Q (Mdel Q w lam bs) x p = KmatA Q x p + w p * x p + lam p * x bs.
  Proof.
    move=> HQ Hp Hbs; rewrite /mvF2 /Mdel.
    have -> : \sum_(j <- Q) (Kd Q p j + bitF2 (p == j) * w p + lam p * bitF2 (j == bs)) * x j
            = \sum_(j <- Q) Kd Q p j * x j + \sum_(j <- Q) bitF2 (j == p) * (w p * x j)
              + lam p * \sum_(j <- Q) bitF2 (j == bs) * x j.
    { rewrite big_distrr -!big_split /=; apply: eq_bigr => j _; rewrite eq_sym; ring. }
    rewrite -/(mvF2 Q (Kd Q) x p) mv_Kd // !sum_ind_eq' //.
  Qed.

  Section Reduction.

    Variables (lam : nat -> F2) (Q' B : seq nat) (q0 bs : nat).
    Hypothesis HQ : uniq (q0 :: Q').
    Hypothesis Hbs : bs \in B.
    Hypothesis HB : {subset B <= Q'}.
    Hypothesis HK1B : forall p, p \in q0 :: Q' -> KmatA (q0 :: Q') (indB B) p = 0.
    Hypothesis HM : injF2 Q' (Mdel Q' (fun p => A p q0) lam bs).

    Local Abbreviation Q := (q0 :: Q').

    Lemma red_q0 : q0 \notin Q'. Proof using HQ. by move: HQ => /= /andP [ ]. Qed.
    Lemma red_uQ' : uniq Q'. Proof using HQ. by move: HQ => /= /andP [ ]. Qed.
    Lemma red_bsQ' : bs \in Q'. Proof using HB Hbs. exact: HB. Qed.
    Lemma red_q0B : q0 \notin B.
    Proof using HB HQ. apply: contra red_q0; exact: HB. Qed.

    Definition Ksharp (x : nat -> F2) (p : nat) : F2 := KmatA Q x p + lam p * (x q0 + x bs).

    Lemma Ksh_mv x p : p \in Q' -> Ksharp x p = (A p q0 + lam p) * x q0 + mvF2 Q' (Mdel Q' (fun p => A p q0) lam bs) x p.
    Proof using HB HQ Hbs.
      move=> Hp; have Hpq : q0 != p by apply: contraNneq red_q0 => ->.
      rewrite /Ksharp KmatA_cons // (@mv_Mdel Q' _ _ bs x p red_uQ' Hp red_bsQ'); ring.
    Qed.

    Lemma Ksh_ker x : (forall p, p \in Q -> Ksharp x p = 0) -> forall p, p \in Q -> x p = x q0.
    Proof using HB HM HQ Hbs.
      move=> Hx.
      set x' := fun i => x i + x q0.
      have Hx' : forall p, p \in Q' -> x' p = 0.
      { apply: HM => p Hp.
        have := Hx p; rewrite in_cons Hp orbT => /(_ isT).
        rewrite /Ksharp -(KmatA_addc Q x (x q0)) -/x'.
        have -> : x q0 + x bs = x' q0 + x' bs by rewrite /x' F2_xx add0r addrC.
        rewrite -/(Ksharp x' p) Ksh_mv // /x' F2_xx mulr0 add0r; by []. }
      move=> p; rewrite in_cons => /orP [ /eqP -> // | Hp ].
      by apply/F2_eq; exact: Hx'.
    Qed.

    (* K = K^# T *)
    Definition TxK (x : nat -> F2) : nat -> F2 := fun i => x i + (x q0 + x bs) * indB B i.

    Lemma Tx_a x : TxK x q0 + TxK x bs = 0.
    Proof using HB HQ Hbs.
      rewrite /TxK /indB (negbTE red_q0B) Hbs /bitF2 /=; rewrite mulr0 mulr1 addr0.
      have E := F2_xx (x q0 + x bs). rewrite -E; ring.
    Qed.

    Lemma K_KshT x p : p \in Q -> KmatA Q x p = Ksharp (TxK x) p.
    Proof using HB HK1B HQ Hbs.
      move=> Hp; rewrite /Ksharp Tx_a mulr0 addr0 /TxK KmatA_add KmatA_scale HK1B //; ring.
    Qed.

    Theorem red_ker : ker_targetA Q B.
    Proof using HB HK1B HM HQ Hbs.
      move=> u; split.
      - move=> Hu; exists (TxK u q0), (u q0 + u bs) => i Hi.
        have Hk : forall p, p \in Q -> Ksharp (TxK u) p = 0 by move=> p Hp; rewrite -K_KshT // Hu.
        have E := Ksh_ker Hk Hi.
        apply/F2_eq; rewrite -E /TxK.
        have -> : forall a b : F2, a + (a + b + b) = (a + a) + (b + b) by move=> a b; ring.
        by rewrite !F2_xx ?addr0.
      - move=> [ c [ c' Hc ] ] i Hi.
        rewrite (KmatA_ext (v := fun j => c' * indB B j + c) Hi).
        { move=> j Hj; rewrite Hc //; ring. }
        by rewrite KmatA_addc KmatA_scale HK1B // mulr0.
    Qed.

    Theorem red_lam : lam_notinA lam Q.
    Proof using HB HK1B HM HQ Hbs.
      move=> [ x Hx ].
      set y := TxK x.
      have Hy : forall p, p \in Q -> Ksharp y p = lam p by move=> p Hp; rewrite -K_KshT // Hx.
      have HKB : forall p, p \in Q -> Ksharp (indB B) p = lam p.
      { move=> p Hp; rewrite /Ksharp HK1B // /indB (negbTE red_q0B) Hbs /bitF2 /=; ring. }
      have Hk : forall p, p \in Q -> Ksharp (fun i => y i + indB B i) p = 0.
      { move=> p Hp; rewrite /Ksharp KmatA_add.
        have := Hy p Hp; have := HKB p Hp; rewrite /Ksharp => E1 E2.
        have -> : lam p * (y q0 + indB B q0 + (y bs + indB B bs)) = lam p * (y q0 + y bs) + lam p * (indB B q0 + indB B bs) by ring.
        have -> : KmatA Q y p + KmatA Q (indB B) p + (lam p * (y q0 + y bs) + lam p * (indB B q0 + indB B bs))
                = (KmatA Q y p + lam p * (y q0 + y bs)) + (KmatA Q (indB B) p + lam p * (indB B q0 + indB B bs)) by ring.
        by rewrite E1 E2 F2_xx. }
      have Hbs' : bs \in Q by rewrite in_cons red_bsQ' orbT.
      have := Ksh_ker Hk Hbs'.
      rewrite /indB (negbTE red_q0B) Hbs /bitF2 /= addr0 => E.
      have := Tx_a x; rewrite -/y.
      move=> E'; move: E; move/(congr1 (fun z => z + y q0)).
      rewrite F2_xx; have -> : y bs + 1 + y q0 = (y q0 + y bs) + 1 by ring.
      by rewrite E' add0r => /eqP; rewrite (negbTE F2_10).
    Qed.

  End Reduction.

End KMatrix.




(** * 3. The block matrix M_0 and the toggles (proof of par:simultaneous-matrices) *)

Lemma perm_filter_sub (Q R : seq nat) : uniq Q -> uniq R -> {subset R <= Q} ->
  perm_eq [seq k <- Q | k \in R] R.
Proof.
  move=> HQ HR HRQ; apply: uniq_perm; [ exact: filter_uniq | exact: HR | ].
  move=> k; rewrite mem_filter; apply/andP/idP => [ [ -> _ ] // | Hk ]; split => //; exact: HRQ.
Qed.

Lemma uniq_map_inj (f : nat -> nat) (s : seq nat) x y : uniq (map f s) -> x \in s -> y \in s -> f x = f y -> x = y.
Proof.
  elim: s => // a s IH /= /andP [ Ha Hs ]; rewrite !in_cons => /orP [ /eqP -> | Hx ] /orP [ /eqP -> | Hy ] E //.
  - by move: Ha; rewrite E (map_f f Hy).
  - by move: Ha; rewrite -E (map_f f Hx).
  - exact: IH.
Qed.

Section M0.

  Variables (A : nat -> nat -> F2) (lam w : nat -> F2) (bs : nat) (Bt : seq nat) (f : nat -> nat).

  Local Abbreviation B := (bs :: Bt).
  Local Abbreviation I := (map f Bt).
  Local Abbreviation R := (B ++ I).

  Hypothesis HR : uniq R.
  Hypothesis HBI : forall b i', b \in B -> i' \in Bt -> A b (f i') = bitF2 ((b == bs) || (b == i')).
  Hypothesis HIB : forall i' b, i' \in Bt -> b \in B -> A (f i') b = bitF2 ((b == bs) || (b == i')).
  Hypothesis HII : forall i' i'', i' \in Bt -> i'' \in Bt -> i' != i'' -> A (f i') (f i'') = 0.
  Hypothesis HwB : forall b, b \in B -> w b = \sum_(i <- I) A b i.
  Hypothesis HwI : forall i, i \in I -> w i = 0.
  Hypothesis HlamI : forall i, i \in I -> lam i = 0.
  Hypothesis HlamB : \sum_(b <- B) lam b = 1.

  Lemma M0_uB : uniq B. Proof using HR. by move: HR; rewrite cat_uniq => /and3P [ ]. Qed.
  Lemma M0_uI : uniq I. Proof using HR. by move: HR; rewrite cat_uniq => /and3P [ ]. Qed.
  Lemma M0_disj p : p \in I -> p \notin B.
  Proof using HR. move: HR; rewrite cat_uniq => /and3P [ _ /hasPn H _ ] Hp; exact: H. Qed.
  Lemma M0_bsBt : bs \notin Bt. Proof using HR. by have := M0_uB => /= /andP [ ]. Qed.
  Lemma M0_uBt : uniq Bt. Proof using HR. by have := M0_uB => /= /andP [ ]. Qed.
  Lemma M0_finj i' i'' : i' \in Bt -> i'' \in Bt -> f i' = f i'' -> i' = i''.
  Proof using HR. move=> H1 H2 E; exact: (uniq_map_inj M0_uI H1 H2 E). Qed.

  (* the B-part and I-part of K_R x at a row p *)
  Lemma KmatA_R x p : KmatA A R x p = KmatA A B x p + KmatA A I x p.
  Proof. by rewrite /KmatA big_cat. Qed.

  Lemma KmatA_out Q x p : p \notin Q -> KmatA A Q x p = \sum_(c <- Q) A p c * (x c + x p).
  Proof.
    move=> Hp; rewrite /KmatA [RHS]big_seq_cond [LHS]big_seq_cond; apply: eq_bigl => c.
    case: (boolP (c \in Q)) => // Hc /=; apply/eqP => E; by move: Hp; rewrite -E Hc.
  Qed.

  Theorem M0_inj : injF2 R (Mdel A R w lam bs).
  Proof using HBI HII HIB HR HlamB HlamI HwB HwI.
    move=> x Hx.
    have HuR : uniq R := HR.
    have HbsR : bs \in R by rewrite mem_cat mem_head.
    have Hrow : forall p, p \in R -> KmatA A R x p + w p * x p + lam p * x bs = 0.
    { move=> p Hp; rewrite -mv_Mdel //; exact: Hx. }
    (* rows of I: x i' = x bs *)
    have HxB : forall i', i' \in Bt -> x i' = x bs.
    { move=> i' Hi'.
      have HfI : f i' \in I by exact: map_f.
      have := Hrow (f i'); rewrite mem_cat HfI orbT => /(_ isT).
      rewrite HwI // HlamI // !mul0r !addr0 KmatA_R.
      rewrite (KmatA_out _ (M0_disj HfI)).
      have -> : KmatA A I x (f i') = 0.
      { rewrite /KmatA big_map big_seq_cond big1 // => i'' /andP [ Hi'' Hne ].
        rewrite HII // ?mul0r //; apply: contraNneq Hne => ->; by []. }
      rewrite addr0.
      have Hi'B : i' \in B by rewrite in_cons Hi' orbT.
      have Hne : bs != i' by apply: contraNneq M0_bsBt => ->.
      have E2 : \sum_(c <- B) A (f i') c * (x c + x (f i')) = \sum_(c <- B) bitF2 ((c == bs) || (c == i')) * (x c + x (f i')).
      { rewrite big_seq [RHS]big_seq; apply: eq_bigr => c Hc; by rewrite HIB. }
      rewrite E2 (sum_ind2 _ M0_uB (mem_head _ _) Hi'B Hne).
      move=> E; apply/esym/F2_eq.
      have -> : x bs + x i' = (x bs + x (f i')) + (x i' + x (f i')).
      { have -> : x bs + x (f i') + (x i' + x (f i')) = (x bs + x i') + (x (f i') + x (f i')) by ring.
        by rewrite F2_xx addr0. }
      exact: E. }
    have HxB' : forall b, b \in B -> x b = x bs.
    { move=> b; rewrite in_cons => /orP [ /eqP -> // | Hb ]; exact: HxB. }
    (* rows of B *)
    have Hsum : forall b g, b \in B ->
        \sum_(i'' <- Bt) A b (f i'') * g i'' = \sum_(i'' <- Bt) bitF2 ((b == bs) || (b == i'')) * g i''.
    { move=> b g Hb; rewrite big_seq [RHS]big_seq; apply: eq_bigr => i'' Hi''; by rewrite HBI. }
    have HrowB : forall b, b \in B ->
        \sum_(i'' <- Bt) bitF2 ((b == bs) || (b == i'')) * x (f i'') + lam b * x bs = 0.
    { move=> b Hb.
      have := Hrow b; rewrite mem_cat Hb => /(_ isT).
      rewrite KmatA_R.
      have -> : KmatA A B x b = 0.
      { rewrite /KmatA big_seq_cond big1 // => c /andP [ Hc _ ]; by rewrite HxB' // HxB' // F2_xx mulr0. }
      have HbI : b \notin I by apply: contraTN Hb; exact: M0_disj.
      rewrite add0r (KmatA_out _ HbI) HwB // !big_map (Hsum b (fun i'' => x (f i'' ) + x b)) //.
      have E3 : \sum_(i'' <- Bt) A b (f i'') = \sum_(i'' <- Bt) bitF2 ((b == bs) || (b == i'')).
      { rewrite big_seq [RHS]big_seq; apply: eq_bigr => i'' Hi''; by rewrite HBI. }
      rewrite E3 big_distrl /= -big_split /= HxB' //.
      move=> E; rewrite -[RHS]E; congr (_ + _); apply: eq_bigr => i'' _.
      have -> : forall a c d : F2, a * (c + d) + a * d = a * c + a * (d + d) by move=> *; ring.
      by rewrite F2_xx mulr0 addr0. }
    (* summing the rows of B: x bs = 0 *)
    have Hbs0 : x bs = 0.
    { have : \sum_(b <- B) (\sum_(i'' <- Bt) bitF2 ((b == bs) || (b == i'')) * x (f i'') + lam b * x bs) = 0.
      { rewrite big_seq big1 // => b Hb; exact: HrowB. }
      rewrite big_split /= exchange_big /= -big_distrl /= HlamB mul1r.
      rewrite big_seq big1 ?add0r // => i'' Hi''.
      rewrite -big_distrl /= sum_ind2c ?mul0r //; [ exact: M0_uB | exact: mem_head | by rewrite in_cons Hi'' orbT | ].
      by apply: contraNneq M0_bsBt => ->. }
    (* rows i' of Bt (as elements of B): x (f i') = 0 *)
    have HxI : forall i', i' \in Bt -> x (f i') = 0.
    { move=> i' Hi'.
      have := HrowB i'; rewrite in_cons Hi' orbT => /(_ isT).
      have -> : (i' == bs) = false by apply/negbTE; apply: contraNneq M0_bsBt => <-.
      rewrite Hbs0 mulr0 addr0 /=.
      have E4 : \sum_(i'' <- Bt) bitF2 (i' == i'') * x (f i'') = \sum_(i'' <- Bt) bitF2 (i'' == i') * x (f i'').
      { by apply: eq_bigr => i'' _; rewrite eq_sym. }
      by rewrite E4 sum_ind_eq' //; exact: M0_uBt. }
    move=> p; rewrite mem_cat => /orP [ Hp | /mapP [ i' Hi' -> ] ].
    - by rewrite HxB' // Hbs0.
    - exact: HxI.
  Qed.

  (** the larger support J ++ R: the R-block is unchanged *)
  Lemma Mdel_JR (J : seq nat) (w' : nat -> F2) p c :
    uniq (J ++ R) -> p \in R -> c \in R -> w' p = w p ->
    (forall p, p \in R -> \sum_(k <- J) A p k = 0) ->
    Mdel A (J ++ R) w' lam bs p c = Mdel A R w lam bs p c.
  Proof.
    move=> HJR Hp Hc Hw HJ.
    have HpJ : p \notin J.
    { move: HJR; rewrite cat_uniq => /and3P [ _ /hasPn H _ ]; exact: H. }
    rewrite /Mdel /Kd Hw; case: (eqVneq p c) => // _.
    rewrite big_cat /=.
    have -> : \sum_(k <- J | k != p) A p k = \sum_(k <- J) A p k.
    { rewrite big_seq_cond [RHS]big_seq; apply: eq_bigl => k.
      case: (boolP (k \in J)) => //= Hk; apply/eqP => E; by move: HpJ; rewrite -E Hk. }
    by rewrite HJ // add0r.
  Qed.

  Theorem M_choose (J : seq nat) : uniq (J ++ R) ->
    (forall p, p \in R -> \sum_(k <- J) A p k = 0) ->
    exists w' : nat -> F2, (forall p, p \notin J -> w' p = w p) /\
      injF2 (J ++ R) (Mdel A (J ++ R) w' lam bs).
  Proof using HBI HII HIB HR HlamB HlamI HwB HwI.
    move=> HJR HJ.
    have H0 : injF2 R (Mdel A (J ++ R) w lam bs).
    { apply: inj_ext M0_inj => p c Hp Hc; by rewrite Mdel_JR. }
    have [ t Ht ] := toggles HJR H0.
    exists (fun p => w p + bitF2 (p \in J) * t p); split.
    - move=> p Hp; by rewrite (negbTE Hp) /bitF2 /= mul0r addr0.
    - apply: inj_ext Ht => p c _ _; rewrite /dgF2 /Mdel ind_mul; ring.
  Qed.

  (** K 1_B = 0 *)
  Lemma KmatA_notB (Q : seq nat) p : uniq Q -> {subset B <= Q} -> p \notin B ->
    KmatA A Q (indB B) p = \sum_(c <- B) A p c.
  Proof using HR.
    move=> HQ HBQ Hp.
    rewrite /KmatA big_mkcond /=.
    have -> : \sum_(c <- Q) (if c != p then A p c * (indB B c + indB B p) else 0)
            = \sum_(c <- Q) (if c \in B then A p c else 0).
    { apply: eq_bigr => c _; rewrite /indB (negbTE Hp) /bitF2 addr0.
      case: (eqVneq c p) => [ -> | _ ]; first by rewrite (negbTE Hp).
      by case: (c \in B); rewrite /= ?mulr1 ?mulr0. }
    rewrite -big_mkcond -big_filter; apply: perm_big; apply: perm_filter_sub => //; exact: M0_uB.
  Qed.

  Lemma KmatA_inB (Q : seq nat) p : p \in B ->
    KmatA A Q (indB B) p = \sum_(c <- Q) bitF2 (c \notin B) * A p c.
  Proof.
    move=> Hp; rewrite /KmatA big_mkcond /=; apply: eq_bigr => c _.
    rewrite /indB Hp; case: (eqVneq c p) => [ -> | _ ]; first by rewrite Hp /bitF2 /= mul0r.
    by case: (c \in B); rewrite /bitF2 /= ?mul1r ?mul0r ?F2_xx ?mulr0 ?add0r ?mulr1.
  Qed.

  Theorem K1B (J : seq nat) (q0 : nat) :
    uniq (q0 :: J ++ R) ->
    (forall b, b \in B -> A b q0 = \sum_(i <- I) A b i) ->
    (forall p, p \in R -> \sum_(k <- J) A p k = 0) ->
    \sum_(b <- B) A q0 b = 0 ->
    (forall j, j \in J -> \sum_(b <- B) A j b = 0) ->
    forall p, p \in q0 :: J ++ R -> KmatA A (q0 :: J ++ R) (indB B) p = 0.
  Proof using HIB HR.
    move=> HQ HBq0 HJ Hq0B HJB p Hp.
    have HBQ : {subset B <= q0 :: J ++ R}.
    { move=> b Hb; by rewrite in_cons mem_cat mem_cat Hb !orbT. }
    have Hdisj : forall c, c \in q0 :: J ++ R -> c \notin R -> c \notin B.
    { move=> c _ HcR; apply: contra HcR => Hc; by rewrite mem_cat Hc. }
    have HQ' := HQ; move: HQ' => /= /andP [ Hq0 HJR ].
    have HJdisj : forall c, c \in J -> c \notin R.
    { move: HJR; rewrite cat_uniq => /and3P [ _ /hasPn H _ ] c Hc; apply/negP => HcR.
      by have := H c HcR; rewrite Hc. }
    have Hq0R : q0 \notin R by apply: contra Hq0 => H; rewrite mem_cat H orbT.
    case: (boolP (p \in B)) => HpB.
    - rewrite KmatA_inB //.
      have E : \sum_(c <- q0 :: J ++ R) bitF2 (c \notin B) * A p c =
               bitF2 (q0 \notin B) * A p q0 + (\sum_(c <- J) bitF2 (c \notin B) * A p c +
               (\sum_(c <- B) bitF2 (c \notin B) * A p c + \sum_(c <- I) bitF2 (c \notin B) * A p c)).
      { by rewrite big_cons !big_cat. }
      rewrite E.
      have -> : bitF2 (q0 \notin B) = 1.
      { by rewrite (Hdisj q0 (mem_head _ _) Hq0R). }
      have -> : \sum_(c <- J) bitF2 (c \notin B) * A p c = \sum_(c <- J) A p c.
      { rewrite big_seq [RHS]big_seq; apply: eq_bigr => c Hc.
        by rewrite (Hdisj c _ (HJdisj c Hc)) ?mul1r // in_cons mem_cat Hc orbT. }
      have HpR : p \in R by rewrite mem_cat HpB.
      rewrite (HJ p HpR).
      have -> : \sum_(c <- B) bitF2 (c \notin B) * A p c = 0.
      { rewrite big_seq big1 // => c Hc; by rewrite Hc /bitF2 /= mul0r. }
      have -> : \sum_(c <- I) bitF2 (c \notin B) * A p c = \sum_(c <- I) A p c.
      { rewrite big_seq [RHS]big_seq; apply: eq_bigr => c Hc; by rewrite M0_disj // mul1r. }
      by rewrite !add0r mul1r HBq0 // F2_xx.
    - rewrite KmatA_notB //.
      move: Hp; rewrite in_cons mem_cat mem_cat (negbTE HpB) /= => /orP [ /eqP -> // | /orP [ HpJ | HpI ] ].
      + exact: HJB.
      + move: HpI => /mapP [ i' Hi' -> ].
        have E5 : \sum_(c <- B) A (f i') c = \sum_(c <- B) bitF2 ((c == bs) || (c == i')).
        { rewrite big_seq [RHS]big_seq; apply: eq_bigr => c Hc; exact: HIB. }
        rewrite E5 sum_ind2c //; [ exact: M0_uB | exact: mem_head | by rewrite in_cons Hi' orbT | ].
        by apply: contraNneq M0_bsBt => ->.
  Qed.

End M0.




(** * 4. Legendre bits *)

(* the nonsquare bit [a/p] *)
Definition nsq_bit (a : int) (p : nat) : F2 := bitF2 (legendre a p == -1).

(* A p c = [q_c / q_p] *)
Definition Lsym (p c : nat) : F2 := nsq_bit c%:Z p.

Definition pm1_int (x : int) : bool := (x == 1) || (x == -1).

Definition sgn_bool (e : bool) : int := if e then 1 else -1.

Lemma pm1_sgnb e : pm1_int (sgn_bool e). Proof. by case: e. Qed.

Lemma ind_pm1M (x y : int) : pm1_int x -> pm1_int y ->
  pm1_int (x * y) /\ bitF2 (x * y == -1) = bitF2 (x == -1) + bitF2 (y == -1).
Proof.
  by move=> /orP [ /eqP -> | /eqP -> ] /orP [ /eqP -> | /eqP -> ];
    rewrite /pm1_int /bitF2 /= ?mulr1 ?mul1r ?mulrNN ?mulr1; split => //; apply/val_inj.
Qed.

Lemma legendre_pm1 (a : int) (p : nat) : prime p -> ~~ (p %| a)%Z -> pm1_int (legendre a p).
Proof.
  move=> Hp Ha; have := legendre_sgn3 p a; rewrite /sgn3 /pm1_int.
  have -> : (legendre a p == 0) = false by rewrite legendre_eq0 // (negbTE Ha).
  by [].
Qed.

Lemma lbM (a b : int) (p : nat) : prime p -> odd p -> ~~ (p %| a)%Z -> ~~ (p %| b)%Z ->
  nsq_bit (a * b) p = nsq_bit a p + nsq_bit b p.
Proof.
  move=> Hp Ho Ha Hb; rewrite /nsq_bit legendreM //.
  exact: (ind_pm1M (legendre_pm1 Hp Ha) (legendre_pm1 Hp Hb)).2.
Qed.

Lemma lb_sgnb (a : int) (p : nat) (e : bool) : legendre a p = sgn_bool e -> nsq_bit a p = bitF2 (~~ e).
Proof. by rewrite /nsq_bit => ->; case: e. Qed.

Lemma lb1 (a : int) (p : nat) : legendre a p = 1 -> nsq_bit a p = 0.
Proof. by rewrite /nsq_bit => ->. Qed.

Lemma ind_F2 (x : F2) : bitF2 (~~ (x == 0)) = x.
Proof. by case: (F2_cases x) => ->. Qed.

Lemma ind_F2' (x : F2) : bitF2 (x != 0) = x.
Proof. exact: ind_F2. Qed.

(* products of lists of naturals *)
Lemma ndvd_prod (p : nat) (L : seq nat) : prime p -> (forall c, c \in L -> ~~ (p %| c)%N) ->
  ~~ (p %| \prod_(c <- L) c)%N.
Proof.
  move=> Hp HL; rewrite Euclid_dvd_prod // big_has; apply/hasPn => c Hc; exact: HL.
Qed.

Lemma dvdz_nat_ndvd (p c : nat) : ~~ (p %| c)%N -> ~~ (p %| c%:Z)%Z.
Proof. by []. Qed.

Lemma lb_prod (L : seq nat) (p : nat) : prime p -> odd p -> (forall c, c \in L -> ~~ (p %| c)%N) ->
  \sum_(c <- L) nsq_bit c%:Z p = nsq_bit (\prod_(c <- L) c)%N%:Z p.
Proof.
  move=> Hp Ho; elim: L => [ | c L IH ] HL.
  - by rewrite !big_nil /nsq_bit legendre1.
  - have HL' : forall d, d \in L -> ~~ (p %| d)%N by move=> d Hd; apply: HL; rewrite in_cons Hd orbT.
    rewrite big_cons (IH HL') big_cons PoszM lbM //; first exact: HL (mem_head _ _).
    exact: ndvd_prod.
Qed.

Lemma prod_gt0 (L : seq nat) : all prime L -> (0 < \prod_(c <- L) c)%N.
Proof.
  elim: L => [ | c L IH ] /=; first by rewrite big_nil.
  by move=> /andP [ Hc HL ]; rewrite big_cons muln_gt0 prime_gt0 // IH.
Qed.

Lemma jacobi_prod (a : int) (L : seq nat) : all prime L -> all odd L ->
  (forall b, b \in L -> ~~ (b %| a)%Z) ->
  pm1_int (jacobi a (\prod_(b <- L) b)) /\ bitF2 (jacobi a (\prod_(b <- L) b) == -1) = \sum_(b <- L) nsq_bit a b.
Proof.
  elim: L => [ | c L IH ] /=.
  - by move=> _ _ _; rewrite !big_nil jacobi1.
  - move=> /andP [ Hc HL ] /andP [ Hco HLo ] Ha.
    have [ H1 H2 ] := IH HL HLo (fun b Hb => Ha b (@mem_behead _ (c :: L) b Hb)).
    rewrite !big_cons (jacobiMr a (prime_gt0 Hc) (prod_gt0 HL)) (jacobi_prime a Hc).
    have Hc1 := legendre_pm1 Hc (Ha c (mem_head _ _)).
    have [ K1 K2 ] := ind_pm1M Hc1 H1.
    by split => //; rewrite K2 H2.
Qed.

(* parities of (n-1)/2 *)
Lemma half_pred_mod4 (n : nat) : (n %% 4 = 1)%N -> ~~ odd (n.-1)./2.
Proof.
  move=> H; rewrite (divn_eq n 4) H addn1 /=; set k := (n %/ 4)%N.
  have -> : (k * 4 = (k * 2).*2)%N by rewrite -muln2 -mulnA.
  by rewrite half_double oddM andbF.
Qed.

Lemma half_pred_mod4' (n : nat) : (n %% 4 = 3)%N -> odd (n.-1)./2.
Proof.
  move=> H; rewrite (divn_eq n 4) H; set k := (n %/ 4)%N.
  have -> : (k * 4 + 3).-1 = (k * 2 + 1).*2 by rewrite addnS /= -muln2 mulnDl -mulnA.
  by rewrite half_double oddD oddM andbF.
Qed.

Lemma mod8_mod4 (n : nat) : (n %% 4 = (n %% 8) %% 4)%N.
Proof. by rewrite modn_dvdm. Qed.

(* the symbol mod 3 *)
Lemma legendre_3 (a : int) : legendre a 3 = if (a %% 3)%Z == 0 then 0 else if (a %% 3)%Z == 1 then 1 else -1.
Proof.
  have -> : legendre a 3 = legendre (a %% 3)%Z 3 by apply: (legendre_mod (isT : prime 3)); rewrite modz_mod.
  have : (0 <= a %% 3 < 3)%Z by rewrite modz_ge0 // ltz_pmod.
  case: (a %% 3)%Z => [ [ | [ | [ | n ] ] ] | n ] //=.
Qed.

Lemma legendre3_nat (q : nat) : legendre q%:Z 3 = 1 -> (q %% 3 = 1)%N.
Proof.
  rewrite legendre_3 modz_nat.
  have : (q %% 3 < 3)%N by rewrite ltn_mod.
  by case: (q %% 3)%N => [ | [ | [ | n ] ] ].
Qed.

Lemma legendre3_2 (q : nat) : (q %% 3 = 2)%N -> legendre q%:Z 3 = -1.
Proof. by rewrite legendre_3 modz_nat => ->. Qed.

(** the matrices of par:matrices on a support Q, with Legendre symbols *)

(* (K u)_i = sum_{j <> i} [q_j/q_i] (u_j + u_i) *)
Definition Kmat (Q : seq nat) (u : nat -> F2) (i : nat) : F2 :=
  \sum_(j <- Q | j != i) nsq_bit j%:Z i * (u j + u i).

(* ker K = <1, 1_B> *)
Definition ker_target (Q B : seq nat) : Prop :=
  forall u : nat -> F2, (forall i, i \in Q -> Kmat Q u i = 0) <->
    exists c c' : F2, forall i, i \in Q -> u i = c + c' * bitF2 (i \in B).

(* lambda = ([3/q_i])_i is not in im K *)
Definition lam_notin_im (Q : seq nat) : Prop :=
  ~ exists u : nat -> F2, forall i, i \in Q -> Kmat Q u i = nsq_bit 3 i.

Lemma ker_target_of_A (Q B : seq nat) : ker_targetA Lsym Q B -> ker_target Q B.
Proof. by []. Qed.

Lemma lam_notin_of_A (Q : seq nat) : lam_notinA Lsym (fun p => nsq_bit 3 p) Q -> lam_notin_im Q.
Proof. by []. Qed.

Lemma Kmat_perm (Q Q' : seq nat) u i : perm_eq Q Q' -> Kmat Q u i = Kmat Q' u i.
Proof. move=> Hp; exact: perm_big. Qed.

Lemma ker_target_perm (Q Q' B : seq nat) : perm_eq Q Q' -> ker_target Q B -> ker_target Q' B.
Proof.
  move=> Hp H u; split.
  - move=> Hu.
    have [ c [ c' Hc ] ] : exists c c' : F2, forall i, i \in Q -> u i = c + c' * bitF2 (i \in B).
    { apply/(H u) => i Hi; rewrite (Kmat_perm _ _ Hp); apply: Hu; by rewrite -(perm_mem Hp). }
    exists c, c' => i Hi; apply: Hc; by rewrite (perm_mem Hp).
  - move=> [ c [ c' Hc ] ] i Hi.
    have H0 : forall i, i \in Q -> Kmat Q u i = 0.
    { apply/(H u); exists c, c' => j Hj; apply: Hc; by rewrite -(perm_mem Hp). }
    rewrite -(Kmat_perm _ _ Hp); apply: H0; by rewrite (perm_mem Hp).
Qed.

Lemma lam_notin_perm (Q Q' : seq nat) : perm_eq Q Q' -> lam_notin_im Q -> lam_notin_im Q'.
Proof.
  move=> Hp H [ u Hu ]; apply: H; exists u => i Hi.
  rewrite (Kmat_perm _ _ Hp); apply: Hu; by rewrite -(perm_mem Hp).
Qed.

(** products of distinct primes *)

Lemma dvd_prod_primes (L : seq nat) (p : nat) : prime p -> all prime L ->
  (p %| \prod_(c <- L) c)%N = (p \in L).
Proof.
  move=> Hp HL; rewrite Euclid_dvd_prod // big_has; apply/hasP/idP.
  - move=> [ c Hc Hpc ]; have Hcp := allP HL c Hc.
    by move: Hpc; rewrite dvdn_prime2 // => /eqP ->.
  - by move=> Hin; exists p.
Qed.

Lemma mem_primes_prod (L : seq nat) (p : nat) : all prime L -> (p \in primes (\prod_(c <- L) c)) = (p \in L).
Proof.
  move=> HL; rewrite mem_primes prod_gt0 //=.
  case: (boolP (prime p)) => Hp /=; first exact: dvd_prod_primes.
  by apply/esym/negP => Hin; move: Hp; rewrite (allP HL p Hin).
Qed.

Lemma perm_primes_prod (L : seq nat) : uniq L -> all prime L -> perm_eq (primes (\prod_(c <- L) c)) L.
Proof.
  move=> Hu HL; apply: uniq_perm => //; first exact: primes_uniq.
  move=> p; exact: mem_primes_prod.
Qed.

Lemma sqfree_prod (L : seq nat) : uniq L -> all prime L -> sqfree_int (\prod_(c <- L) c)%N%:Z.
Proof.
  move=> Hu HL n Hn; apply/negP => Hdvd.
  have Hp := pdiv_prime Hn; set p := pdiv n in Hp.
  have Hpn : (p %| n)%N by exact: pdiv_dvd.
  have Hpp : (p * p %| \prod_(c <- L) c)%N.
  { apply: dvdn_trans Hdvd; exact: dvdn_mul. }
  have HpL : p \in L.
  { rewrite -dvd_prod_primes //; apply: dvdn_trans Hpp; exact: dvdn_mulr. }
  move: Hpp; rewrite (big_rem p HpL) /= dvdn_pmul2l ?prime_gt0 //.
  have HL' : all prime (rem p L) by apply/allP => x Hx; apply: (allP HL); exact: mem_rem Hx.
  by rewrite (dvd_prod_primes Hp HL') (mem_rem_uniq p Hu) !inE eqxx.
Qed.

Lemma prod_mod1 (L : seq nat) (m : nat) : (forall x, x \in L -> (x %% m = 1 %% m)%N) ->
  ((\prod_(c <- L) c) %% m = 1 %% m)%N.
Proof.
  elim: L => [ | c L IH ] H; first by rewrite big_nil.
  have HL' : forall x, x \in L -> (x %% m = 1 %% m)%N by move=> x Hx; apply: H; rewrite in_cons Hx orbT.
  by rewrite big_cons -modnMm (H c (mem_head _ _)) (IH HL') modnMm mul1n.
Qed.




(** * 5. Realizing prescribed symbols by primes

    Dirichlet's theorem for quadratic characters, proved in
    PrimePatterns.v (Phase 4). *)

Lemma new_prime (eps : nat -> bool) (r : nat) (ps : seq nat) :
  odd r -> uniq ps -> all prime ps -> all odd ps ->
  exists q : nat, [/\ prime q, q \notin ps, (q %% 8 = r %% 8)%N &
    forall p, p \in ps -> legendre q%:Z p = sgn_bool (eps p) /\
      legendre p%:Z q = sgn_bool (eps p) * (-1) ^+ ((p.-1)./2 * (r.-1)./2)].
Proof. exact: PrimePatterns.new_prime_nodir. Qed.

(** * 6. Lemma par:simultaneous-matrices

    03-parity.tex, Sec. 3.4: "Lemma (par:simultaneous-matrices). For
    beta, theta, B, J as in Lemma par:cross-squares, there is a positive
    squarefree integer n, prime to 6 theta, whose support P contains B and
    at least one auxiliary prime outside B, such that the following
    statements hold for both l = n and l = n theta. The number l satisfies
    l = 3 (mod 4) and l = 2 (mod 3). On its prime support Q = P or
    Q = P u J, the matrices (par:matrices) satisfy (par:matrix-target)",
    where (par:matrix-target) is "ker K = <1, 1_B>, lambda not in im K".

    In this section B = bs :: Bt and J are abstract lists of primes > 3 with
    the properties that the proof uses: beta = 1 mod 8, theta = 1 mod 8
    (squares in Q_2), beta = 2 mod 3, theta = 1 mod 3 (the classes at 3),
    (theta/b) = 1 for b in B and (beta/j) = 1 for j in J
    (par:mutual-squares); [simultaneous_matrices] (Sec. 14) derives them
    from Lemma par:cross-squares. *)

Section SimMat.

  Local Set Default Proof Using "All".

  Variables (bs : nat) (Bt J : seq nat).

  Local Abbreviation B := (bs :: Bt).
  Local Abbreviation beta := (\prod_(b <- bs :: Bt) b)%N.
  Local Abbreviation theta := (\prod_(j <- J) j)%N.

  Hypotheses (HBu : uniq B) (HJu : uniq J) (HBp : all prime B) (HJp : all prime J).
  Hypotheses (HB3 : forall b, b \in B -> (3 < b)%N) (HJ3 : forall j, j \in J -> (3 < j)%N).
  Hypothesis HBJ : forall b, b \in B -> b \notin J.
  Hypotheses (Hb8 : (beta %% 8 = 1)%N) (Ht8 : (theta %% 8 = 1)%N).
  Hypotheses (Hb3 : (beta %% 3 = 2)%N) (Ht3 : (theta %% 3 = 1)%N).
  Hypothesis HthB : forall b, b \in B -> legendre theta%:Z b = 1.
  Hypothesis HbeJ : forall j, j \in J -> legendre beta%:Z j = 1.

  Lemma prime_odd3 (p : nat) : prime p -> (3 < p)%N -> odd p.
  Proof.
    move=> Hp H3; case: (even_prime Hp) => // E; by rewrite E in H3.
  Qed.

  Lemma B_prime b : b \in B -> prime b. Proof. by move=> Hb; exact: (allP HBp). Qed.
  Lemma J_prime j : j \in J -> prime j. Proof. by move=> Hj; exact: (allP HJp). Qed.
  Lemma B_odd b : b \in B -> odd b. Proof. move=> Hb; apply: prime_odd3; [ exact: B_prime | exact: HB3 ]. Qed.
  Lemma J_odd j : j \in J -> odd j. Proof. move=> Hj; apply: prime_odd3; [ exact: J_prime | exact: HJ3 ]. Qed.
  Lemma B_ne3 b : b \in B -> b != 3%N. Proof. by move=> /HB3; case: b => [ | [ | [ | [ | ] ] ] ]. Qed.
  Lemma J_ne3 j : j \in J -> j != 3%N. Proof. by move=> /HJ3; case: j => [ | [ | [ | [ | ] ] ] ]. Qed.

  (** the auxiliary primes I = f(Bt), of type (0,0): f i' = 1 mod 8, = 1 mod 3;
      [f i' / b] = [b / f i'] = 1 iff b in {bs, i'} (the matrix C, a star),
      all other symbols incident with I are squares *)
  Definition auxI (f : nat -> nat) (L : seq nat) : Prop :=
    forall i', i' \in L ->
      [/\ prime (f i') /\ (f i' %% 8 = 1)%N,
          legendre (f i') 3 = 1 /\ legendre 3 (f i') = 1,
          f i' \notin B /\ f i' \notin J /\ f i' != 3%N,
          forall b, b \in B -> legendre (f i') b = sgn_bool (~~ ((b == bs) || (b == i'))) /\
                               legendre b (f i') = sgn_bool (~~ ((b == bs) || (b == i'))) &
          (forall j, j \in J -> legendre (f i') j = 1 /\ legendre j (f i') = 1) /\
          (forall i'', i'' \in L -> i'' != i' -> f i'' != f i' /\ legendre (f i'') (f i') = 1)].

  Lemma auxI_inj f L : auxI f L -> {in L &, injective f}.
  Proof.
    move=> H x y Hx Hy E; apply/eqP; apply/negP => /negP Hne.
    have [ _ _ _ _ [ _ H6 ] ] := H y Hy.
    by have [ /eqP ] := H6 x Hx Hne.
  Qed.

  Lemma ps_props f L : auxI f L -> uniq L ->
    [/\ uniq (3%N :: B ++ J ++ map f L), all prime (3%N :: B ++ J ++ map f L) &
        all odd (3%N :: B ++ J ++ map f L)].
  Proof.
    move=> Hf HL.
    have Hfm : forall x, x \in map f L -> [/\ prime x, odd x, x \notin B, x \notin J & x != 3%N].
    { move=> x /mapP [ i' Hi' -> ]; have [ [ Hp H8 ] _ [ HnB [ HnJ Hn3 ] ] _ _ ] := Hf i' Hi'.
      split => //; rewrite -(@odd_mod _ 8) // H8 //. }
    split.
    - rewrite cons_uniq; apply/andP; split.
      + apply/negP; rewrite !mem_cat => /orP [ H | /orP [ H | H ] ].
        * by have := B_ne3 H; rewrite eqxx.
        * by have := J_ne3 H; rewrite eqxx.
        * by have [ _ _ _ _ ] := Hfm _ H; rewrite eqxx.
      + rewrite cat_uniq; apply/and3P; split => //.
        * rewrite has_cat negb_or; apply/andP; split; apply/hasPn => x Hx.
          -- apply/negP => HxB; by move: (HBJ HxB); rewrite Hx.
          -- by have [ _ _ ] := Hfm x Hx.
        * rewrite cat_uniq HJu (map_inj_in_uniq (auxI_inj Hf)) HL andbT /=.
          by apply/hasPn => x Hx; have [ _ _ _ ] := Hfm x Hx.
    - have HA : all prime (B ++ J ++ map f L).
      { rewrite !all_cat HBp HJp /=; apply/allP => x /Hfm; by case. }
      apply/andP; split; [ done | exact: HA ].
    - have HA : all odd (B ++ J ++ map f L).
      { rewrite !all_cat; apply/and3P; split.
        + by apply/allP => x; exact: B_odd.
        + by apply/allP => x; exact: J_odd.
        + by apply/allP => x /Hfm; case. }
      apply/andP; split; [ done | exact: HA ].
  Qed.

  Lemma choose_I (L : seq nat) : uniq L -> {subset L <= Bt} -> exists f, auxI f L.
  Proof.
    elim: L => [ | a L IH ]; first by move=> _ _; exists id => i'.
    move=> /= /andP [ HaL HL ] Hsub.
    have [ f' Hf' ] := IH HL (fun x Hx => Hsub x (mem_behead (s := a :: L) Hx)).
    have [ Hu Hp Ho ] := ps_props Hf' HL.
    set eps := fun p => if p \in B then ~~ ((p == bs) || (p == a)) else true.
    have [ q [ Hq Hqps Hq8 Hqs ] ] := new_prime eps (isT : odd 1) Hu Hp Ho.
    have Hqs' : forall p, p \in 3%N :: B ++ J ++ map f' L ->
                  legendre q p = sgn_bool (eps p) /\ legendre p q = sgn_bool (eps p).
    { move=> p Hpp; have [ E1 E2 ] := Hqs p Hpp; split => //; by rewrite E2 muln0 expr0 mulr1. }
    have Hin3 : 3%N \in 3%N :: B ++ J ++ map f' L by rewrite mem_head.
    have HinB : forall b, b \in B -> b \in 3%N :: B ++ J ++ map f' L by move=> b Hb; rewrite in_cons mem_cat Hb orbT.
    have HinJ : forall j, j \in J -> j \in 3%N :: B ++ J ++ map f' L by move=> j Hj; rewrite in_cons !mem_cat Hj !orbT.
    have HinL : forall i', i' \in L -> f' i' \in 3%N :: B ++ J ++ map f' L.
    { move=> i' Hi'; by rewrite in_cons !mem_cat (map_f f' Hi') !orbT. }
    have Heps3 : eps 3%N = true by rewrite /eps; case: ifP => // H; have := B_ne3 H; rewrite eqxx.
    have HepsJ : forall j, j \in J -> eps j = true.
    { move=> j Hj; rewrite /eps; case: ifP => // H; have := HBJ H; by rewrite Hj. }
    have HepsL : forall i', i' \in L -> eps (f' i') = true.
    { move=> i' Hi'; rewrite /eps; case: ifP => // HB; have [ _ _ [ HnB _ ] _ _ ] := Hf' i' Hi'; by rewrite HB in HnB. }
    have HqnB : q \notin B by apply: contra Hqps => H; exact: HinB.
    have HqnJ : q \notin J by apply: contra Hqps => H; exact: HinJ.
    have Hqn3 : q != 3%N by apply: contraNneq Hqps => ->; exact: Hin3.
    have HqnL : forall i', i' \in L -> f' i' != q.
    { move=> i' Hi'; apply: contraNneq Hqps => <-; exact: HinL. }
    exists (fun x => if x == a then q else f' x) => i'; rewrite in_cons.
    case: (eqVneq i' a) => [ -> _ | Hne /= Hi' ].
    - rewrite ?eqxx; split.
      + by [].
      + by have [ -> -> ] := Hqs' _ Hin3; rewrite Heps3.
      + by [].
      + move=> b Hb; have [ -> -> ] := Hqs' _ (HinB b Hb); by rewrite /eps Hb.
      + split.
        * move=> j Hj; have [ -> -> ] := Hqs' _ (HinJ j Hj); by rewrite HepsJ.
        * move=> i''; rewrite in_cons => /orP [ /eqP -> | Hi'' ]; first by rewrite eqxx.
          move=> Hne; rewrite (negbTE Hne); split; first exact: HqnL.
          by have [ _ -> ] := Hqs' _ (HinL i'' Hi''); rewrite HepsL.
    - rewrite ?(negbTE Hne).
      have [ H1 H2 H3 H4 [ H5 H6 ] ] := Hf' i' Hi'.
      split => //; split => //.
      move=> i''; rewrite in_cons => /orP [ /eqP -> | Hi'' ].
      + move=> _; rewrite eqxx; split; first by rewrite eq_sym; exact: HqnL.
        by have [ -> _ ] := Hqs' _ (HinL i' Hi'); rewrite HepsL.
      + move=> Hne'; have Hia : i'' != a by apply: contraNneq HaL => <-.
        rewrite (negbTE Hia); exact: H6.
  Qed.

  (** fixed symbol sums (par:fixed-symbol-sums), (par:cross-symbol-sums) *)

  Lemma beta_mod4 : (beta %% 4 = 1)%N.
  Proof. by rewrite mod8_mod4 Hb8. Qed.

  Lemma theta_mod4 : (theta %% 4 = 1)%N.
  Proof. by rewrite mod8_mod4 Ht8. Qed.

  Lemma B_ndvd3 b : b \in B -> ~~ (b %| 3%:R)%Z.
  Proof.
    move=> Hb; rewrite natz /dvdz /=; apply/negP => H.
    have := dvdn_leq (isT : (0 < 3)%N) H; have := HB3 Hb; by case: b {H Hb} => [ | [ | [ | [ | ] ] ] ].
  Qed.

  Lemma B_ndvdN1 b : b \in B -> ~~ (b %| -1)%Z.
  Proof.
    move=> Hb; apply/negP; rewrite dvdzE /= dvdn1 => /eqP Hb1; have := HB3 Hb; by rewrite Hb1.
  Qed.

  Lemma sum_lam_B : \sum_(b <- B) nsq_bit 3 b = 1.
  Proof.
    have Ho : all odd B by apply/allP => b; exact: B_odd.
    have [ _ E ] := jacobi_prod HBp Ho B_ndvd3.
    rewrite -E natz.
    have Hbo : odd beta by rewrite -(@odd_mod _ 4) // beta_mod4.
    have Hco : coprime 3 beta.
    { by rewrite prime_coprime // /dvdn Hb3. }
    have R := jacobi_reciprocity (isT : odd 3) Hbo Hco.
    move: R; rewrite (jacobi_prime _ (isT : prime 3)) legendre3_2 // -signr_odd mul1n.
    rewrite (negbTE (half_pred_mod4 beta_mod4)) expr0 => /eqP.
    rewrite mulrN1 eqr_oppLR => /eqP ->; by [].
  Qed.

  Lemma sum_s_B : \sum_(b <- B) nsq_bit (-1) b = 0.
  Proof.
    have Ho : all odd B by apply/allP => b; exact: B_odd.
    have [ _ E ] := jacobi_prod HBp Ho B_ndvdN1.
    have Hbo : odd beta by rewrite -(@odd_mod _ 4) // beta_mod4.
    rewrite -E jacobi_minus_one // -signr_odd (negbTE (half_pred_mod4 beta_mod4)) expr0; by [].
  Qed.

  Lemma sum_J_row b : b \in B -> \sum_(j <- J) nsq_bit j%:Z b = 0.
  Proof.
    move=> Hb.
    have Hc : forall j, j \in J -> ~~ (b %| j)%N.
    { move=> j Hj; rewrite (dvdn_prime2 (B_prime Hb) (J_prime Hj)).
      by apply: contraNneq (HBJ Hb) => ->. }
    rewrite (lb_prod (B_prime Hb) (B_odd Hb) Hc); apply: lb1; exact: HthB.
  Qed.

  Lemma sum_B_row j : j \in J -> \sum_(b <- B) nsq_bit b%:Z j = 0.
  Proof.
    move=> Hj.
    have Hc : forall b, b \in B -> ~~ (j %| b)%N.
    { move=> b Hb; rewrite (dvdn_prime2 (J_prime Hj) (B_prime Hb)).
      by apply: contraNneq (HBJ Hb) => <-. }
    rewrite (lb_prod (J_prime Hj) (J_odd Hj) Hc); apply: lb1; exact: HbeJ.
  Qed.

  Lemma mulmod (a b m x y : nat) : (a %% m = x)%N -> (b %% m = y)%N -> ((a * b) %% m = (x * y) %% m)%N.
  Proof. by move=> Ha Hb; rewrite -modnMm Ha Hb. Qed.

  (** the lemma *)
  Theorem sim_matrices : exists n : nat,
    [/\ (0 < n)%N, coprime n (6 * theta), {subset B <= primes n},
        (exists p, p \in primes n /\ p \notin B) &
        forall l : nat, l = n \/ l = (n * theta)%N ->
          [/\ (l %% 4 = 3)%N, (l %% 3 = 2)%N, sqfree_int l%:Z,
              {subset B <= primes l} /\ (exists p, p \in primes l /\ p \notin B) &
              ker_target (primes l) B /\ lam_notin_im (primes l)]].
  Proof.
    have HBtu : uniq Bt by move: HBu => /= /andP [ ].
    have HBtbs : (bs \in Bt) = false by move: HBu => /= /andP [ /negbTE ].
    have [ f Hf ] := choose_I HBtu (fun x Hx => Hx).
    set I := map f Bt.
    have [ Hu0 Hp0 Ho0 ] := ps_props Hf HBtu.
    (* the auxiliary primes *)
    have HfI : forall i, i \in I -> exists2 i', i' \in Bt & i = f i' by move=> i /mapP.
    have Hu1 : uniq (B ++ J ++ I) by move: Hu0; rewrite cons_uniq => /andP [ _ ].
    have HuR : uniq (B ++ I).
    { apply: subseq_uniq Hu1; apply: cat_subseq; [ exact: subseq_refl | exact: suffix_subseq ]. }
    have HuJR : uniq (J ++ (B ++ I)).
    { have Hp : perm_eq (B ++ J ++ I) (J ++ B ++ I) by rewrite perm_catCA.
      by rewrite -(perm_uniq Hp). }
    have Hall1 : all prime (B ++ J ++ I) by move: Hp0 => /andP [ _ ].
    (* bit facts *)
    set lam := fun p : nat => nsq_bit 3 p.
    set w := fun p : nat => if p \in B then \sum_(i <- I) Lsym p i else 0.
    have HBI : forall b i', b \in B -> i' \in Bt -> Lsym b (f i') = bitF2 ((b == bs) || (b == i')).
    { move=> b i' Hb Hi'; have [ _ _ _ H4 _ ] := Hf i' Hi'.
      have [ E _ ] := H4 b Hb; by rewrite /Lsym (lb_sgnb E) negbK. }
    have HIB : forall i' b, i' \in Bt -> b \in B -> Lsym (f i') b = bitF2 ((b == bs) || (b == i')).
    { move=> i' b Hi' Hb; have [ _ _ _ H4 _ ] := Hf i' Hi'.
      have [ _ E ] := H4 b Hb; by rewrite /Lsym (lb_sgnb E) negbK. }
    have HII : forall i' i'', i' \in Bt -> i'' \in Bt -> i' != i'' -> Lsym (f i') (f i'') = 0.
    { move=> i' i'' Hi' Hi'' Hne; have [ _ _ _ _ [ _ H6 ] ] := Hf i' Hi'.
      have Hne' : i'' != i' by rewrite eq_sym.
      have [ _ E ] := H6 i'' Hi'' Hne'; by rewrite /Lsym lb1. }
    have HfIx : forall i, i \in I -> exists2 i', i' \in Bt & i = f i' by move=> i /mapP.
    have HIdisj : forall i, i \in I -> [/\ i \notin B, i \notin J, i != 3%N & legendre 3 i = 1].
    { move=> i /HfIx [ i' Hi' -> ]; have [ _ [ _ E ] [ H1 [ H2 H3 ] ] _ _ ] := Hf i' Hi'; by split. }
    have HwB : forall b, b \in B -> w b = \sum_(i <- I) Lsym b i by move=> b Hb; rewrite /w Hb.
    have HwI : forall i, i \in I -> w i = 0.
    { move=> i Hi; have [ H _ _ _ ] := HIdisj i Hi; by rewrite /w (negbTE H). }
    have HlamI : forall i, i \in I -> lam i = 0.
    { move=> i Hi; have [ _ _ _ E ] := HIdisj i Hi; exact: lb1. }
    have HlamB : \sum_(b <- B) lam b = 1 := sum_lam_B.
    have Hext : forall p, p \in B ++ I -> \sum_(k <- J) Lsym p k = 0.
    { move=> p; rewrite mem_cat => /orP [ Hp | /HfIx [ i' Hi' -> ] ]; first exact: sum_J_row.
      rewrite big_seq big1 // => j Hj; have [ _ _ _ _ [ H5 _ ] ] := Hf i' Hi'.
      have [ _ E ] := H5 j Hj; exact: lb1. }
    have [ w' [ Hw'1 Hw'2 ] ] := @M_choose Lsym lam w bs Bt f HuR HBI HIB HII HwB HwI HlamI HlamB J HuJR Hext.
    have HM0 := @M0_inj Lsym lam w bs Bt f HuR HBI HIB HII HwB HwI HlamI HlamB.
    (* the prime q0 of type (1,1): q0 = 7 mod 8, = 1 mod 3 *)
    set eps := fun p : nat => if p \in B then (w p == 0) else if p \in J then (w' p == 0) else true.
    have [ q0 [ Hq0 Hq0ps Hq08 Hq0s ] ] := new_prime eps (isT : odd 7) Hu0 Hp0 Ho0.
    have Hin : forall p, p \in J ++ (B ++ I) -> p \in 3%N :: B ++ J ++ I.
    { move=> p; rewrite in_cons !mem_cat => /orP [ H | /orP [ H | H ] ]; by rewrite H !orbT. }
    have HinB : forall b, b \in B -> b \in J ++ (B ++ I) by move=> b Hb; rewrite !mem_cat Hb orbT.
    have Hq0nR : q0 \notin J ++ (B ++ I) by apply: contra Hq0ps; exact: Hin.
    have HLq0 : forall p, p \in J ++ (B ++ I) -> Lsym p q0 = w' p.
    { move=> p Hp; have [ E _ ] := Hq0s p (Hin p Hp); rewrite /Lsym (lb_sgnb E) /eps.
      case: (boolP (p \in B)) => HpB.
      - have HpJ : p \notin J by apply: HBJ.
        by rewrite ind_F2 Hw'1.
      - case: (boolP (p \in J)) => HpJ; first by rewrite ind_F2.
        move: Hp; rewrite !mem_cat (negbTE HpB) (negbTE HpJ) /= => HpI.
        by rewrite Hw'1 // HwI. }
    have HLq0R : forall p, p \in B ++ I -> Lsym p q0 = w p.
    { move=> p Hp; have HpJ : p \notin J.
      { move: Hp; rewrite mem_cat => /orP [ /HBJ // | /HIdisj [ ] // ]. }
      have HpQ : p \in J ++ (B ++ I) by rewrite mem_cat Hp orbT.
      by rewrite (HLq0 p HpQ) (Hw'1 p HpJ). }
    have HBq0 : forall b, b \in B -> Lsym b q0 = \sum_(i <- I) Lsym b i.
    { move=> b Hb; have HbR : b \in B ++ I by rewrite mem_cat Hb.
      by rewrite (HLq0R b HbR) HwB. }
    have Hq0B : \sum_(b <- B) Lsym q0 b = 0.
    { have E1 : forall b, b \in B -> Lsym q0 b = w b + nsq_bit (-1) b.
      { move=> b Hb; have [ E E' ] := Hq0s b (Hin b (HinB b Hb)).
        have Hm1 : (-1) ^+ ((b.-1)./2 * (7.-1)./2) = legendre (-1) b :> int.
        { rewrite (_ : (7.-1)./2 = 3)%N // (legendre_minus_one (B_prime Hb) (B_odd Hb)).
          by rewrite -signr_odd oddM andbT signr_odd. }
        rewrite /Lsym /nsq_bit E' Hm1 -E.
        have Hbq : ~~ (b %| q0%:Z)%Z.
        { rewrite dvdzE /= (dvdn_prime2 (B_prime Hb) Hq0).
          by apply: contraNneq Hq0ps => <-; rewrite in_cons mem_cat Hb orbT. }
        have [ _ -> ] := ind_pm1M (legendre_pm1 (B_prime Hb) Hbq) (legendre_pm1 (B_prime Hb) (B_ndvdN1 Hb)).
        by rewrite -/(nsq_bit q0%:Z b) (lb_sgnb E) /eps Hb ind_F2. }
      have Esum : \sum_(b <- B) Lsym q0 b = \sum_(b <- B) (w b + nsq_bit (-1) b).
      { rewrite big_seq [RHS]big_seq; apply: eq_bigr => b Hb; exact: E1. }
      rewrite Esum big_split /= sum_s_B addr0.
      have Ew : \sum_(b <- B) w b = \sum_(b <- B) \sum_(i' <- Bt) bitF2 ((b == bs) || (b == i')).
      { rewrite big_seq [RHS]big_seq; apply: eq_bigr => b Hb; rewrite HwB // big_map.
        rewrite big_seq [RHS]big_seq; apply: eq_bigr => i' Hi'; exact: HBI. }
      rewrite Ew exchange_big /= big_seq big1 // => i' Hi'.
      apply: sum_ind2c => //; first exact: mem_head.
      - by rewrite in_cons Hi' orbT.
      - by apply: contraNneq (negbT (HBtbs)) => ->. }
    have HJB : forall j, j \in J -> \sum_(b <- B) Lsym j b = 0 by move=> j Hj; exact: sum_B_row.
    (* K 1_B = 0 on both supports *)
    have HuQ1 : uniq (q0 :: J ++ (B ++ I)) by rewrite cons_uniq Hq0nR HuJR.
    have Hq0nR0 : q0 \notin [::] ++ (B ++ I).
    { apply: contra Hq0nR => H; rewrite mem_cat H orbT; by []. }
    have HuQ0 : uniq (q0 :: [::] ++ (B ++ I)) by rewrite cons_uniq Hq0nR0 HuR.
    have HK1 := @K1B Lsym bs Bt f HuR HIB J q0 HuQ1 HBq0 Hext Hq0B HJB.
    have HK0 := @K1B Lsym bs Bt f HuR HIB [::] q0 HuQ0 HBq0 (fun p _ => big_nil _ _ _ _) Hq0B
                  (fun j (Hj : j \in [::]) => False_ind _ (notF Hj)).
    (* the deleted matrices are nonsingular on both supports *)
    have HM1 : injF2 (J ++ (B ++ I)) (Mdel Lsym (J ++ (B ++ I)) (fun p => Lsym p q0) lam bs).
    { apply: inj_ext Hw'2 => p c Hp _; by rewrite /Mdel (HLq0 p Hp). }
    have HM0' : injF2 ([::] ++ (B ++ I)) (Mdel Lsym ([::] ++ (B ++ I)) (fun p => Lsym p q0) lam bs).
    { apply: inj_ext HM0 => p c Hp _; by rewrite /Mdel (HLq0R p Hp). }
    have Hbs : bs \in B by exact: mem_head.
    have HBs1 : {subset B <= J ++ (B ++ I)} by move=> b Hb; rewrite !mem_cat Hb orbT.
    have HBs0 : {subset B <= [::] ++ (B ++ I)} by move=> b Hb; rewrite !mem_cat Hb.
    have Hk1 := red_ker HuQ1 Hbs HBs1 HK1 HM1.
    have Hl1 := red_lam HuQ1 Hbs HBs1 HK1 HM1.
    have Hk0 := red_ker HuQ0 Hbs HBs0 HK0 HM0'.
    have Hl0 := red_lam HuQ0 Hbs HBs0 HK0 HM0'.
    (* the parameter n *)
    set R := B ++ I.
    have HallR : all prime R.
    { apply/allP => x; rewrite mem_cat => /orP [ H | H ]; apply: (allP Hall1); by rewrite !mem_cat H ?orbT. }
    have HallJ : all prime J := HJp.
    have HallQ0 : all prime (q0 :: R) by apply/andP; split; [ exact: Hq0 | exact: HallR ].
    have HallJR : all prime (J ++ R) by rewrite all_cat HallJ HallR.
    have HallQ1 : all prime (q0 :: J ++ R) by apply/andP; split; [ exact: Hq0 | exact: HallJR ].
    set n := (\prod_(p <- q0 :: R) p)%N.
    have Hn : n = (q0 * (beta * \prod_(i <- I) i))%N by rewrite /n big_cons big_cat.
    have Hnt : (n * theta)%N = (\prod_(p <- q0 :: J ++ R) p)%N.
    { have E1 : (\prod_(p <- q0 :: R) p = q0 * \prod_(p <- R) p)%N by rewrite big_cons.
      have E2 : (\prod_(p <- q0 :: J ++ R) p = q0 * (theta * \prod_(p <- R) p))%N by rewrite big_cons big_cat.
      by rewrite /n E1 E2 -mulnA [(\prod_(p <- R) p * theta)%N]mulnC. }
    have Hn0 : (0 < n)%N by rewrite /n prod_gt0.
    have Ht0 : (0 < theta)%N by rewrite prod_gt0.
    (* congruences *)
    have HI4 : ((\prod_(i <- I) i) %% 4 = 1 %% 4)%N.
    { apply: prod_mod1 => i /HfIx [ i' Hi' -> ]; have [ [ _ H8 ] _ _ _ _ ] := Hf i' Hi'.
      by rewrite mod8_mod4 H8. }
    have HI3 : ((\prod_(i <- I) i) %% 3 = 1 %% 3)%N.
    { apply: prod_mod1 => i /HfIx [ i' Hi' -> ]; have [ _ [ E _ ] _ _ _ ] := Hf i' Hi'.
      exact: legendre3_nat. }
    have Hq04 : (q0 %% 4 = 3)%N by rewrite mod8_mod4 Hq08.
    have Heps3 : eps 3%N = true.
    { rewrite /eps; case: ifP => [ H | _ ]; first by have := B_ne3 H; rewrite eqxx.
      case: ifP => // H; by have := J_ne3 H; rewrite eqxx. }
    have Hq03 : (q0 %% 3 = 1)%N.
    { have [ E _ ] := Hq0s 3%N (mem_head _ _); apply: legendre3_nat; by rewrite E Heps3. }
    have HbI4 : ((beta * \prod_(i <- I) i) %% 4 = 1)%N by rewrite -modnMm beta_mod4 HI4.
    have HbI3 : ((beta * \prod_(i <- I) i) %% 3 = 2)%N by rewrite -modnMm Hb3 HI3.
    have Hn4 : (n %% 4 = 3)%N by rewrite Hn -modnMm Hq04 HbI4.
    have Hn3 : (n %% 3 = 2)%N by rewrite Hn -modnMm Hq03 HbI3.
    have Hnt4 : ((n * theta) %% 4 = 3)%N by rewrite -modnMm Hn4 theta_mod4.
    have Hnt3 : ((n * theta) %% 3 = 2)%N by rewrite -modnMm Hn3 Ht3.
    (* supports *)
    have HuQ0' : uniq (q0 :: R) := HuQ0.
    have Hpn : perm_eq (primes n) (q0 :: R) := perm_primes_prod HuQ0' HallQ0.
    have Hpnt : perm_eq (primes (n * theta)) (q0 :: J ++ R) by rewrite Hnt; exact: perm_primes_prod.
    have Hpn' : perm_eq (q0 :: R) (primes n) by rewrite perm_sym.
    have Hpnt' : perm_eq (q0 :: J ++ R) (primes (n * theta)) by rewrite perm_sym.
    have Hq0B' : q0 \notin B by apply: contra Hq0nR => H; rewrite !mem_cat H orbT.
    have HsubB : forall l, perm_eq (primes l) (q0 :: J ++ R) \/ perm_eq (primes l) (q0 :: R) ->
      {subset B <= primes l} /\ exists p, p \in primes l /\ p \notin B.
    { move=> l [ Hp | Hp ]; (split; [ move=> b Hb; rewrite (perm_mem Hp) in_cons !mem_cat Hb ?orbT // | ]);
        exists q0; by rewrite (perm_mem Hp) mem_head. }
    exists n; split => //.
    - rewrite coprimeMr; apply/andP; split.
      + rewrite (_ : 6 = 2 * 3)%N // coprimeMr coprimen2 -(@odd_mod _ 4) // Hn4 /=.
        by rewrite coprime_sym prime_coprime // /dvdn Hn3.
      + rewrite coprime_has_primes //; apply/hasPn => p.
        rewrite mem_primes_prod // (perm_mem Hpn) => HpJ; apply/negP; rewrite in_cons => /orP [ /eqP Hq | HpR ].
        * by move: Hq0nR; rewrite -Hq mem_cat HpJ.
        * move: HuQ1; rewrite cons_uniq cat_uniq => /andP [ _ /and3P [ _ /hasPn H _ ] ].
          by have := H p HpR; rewrite HpJ.
    - by have [ ] := HsubB n (or_intror Hpn).
    - by have [ ] := HsubB n (or_intror Hpn).
    - move=> l [ -> | -> ]; split => //.
      + by rewrite /n; apply: sqfree_prod.
      + exact: HsubB n (or_intror Hpn).
      + split; [ apply: (ker_target_perm Hpn'); exact: ker_target_of_A Hk0
               | apply: (lam_notin_perm Hpn'); exact: lam_notin_of_A Hl0 ].
      + by rewrite Hnt; apply: sqfree_prod.
      + exact: HsubB _ (or_introl Hpnt).
      + split; [ apply: (ker_target_perm Hpnt'); exact: ker_target_of_A Hk1
               | apply: (lam_notin_perm Hpnt'); exact: lam_notin_of_A Hl1 ].
  Qed.

End SimMat.



(** * 7. Valuation bookkeeping *)

(* x = 0 or v_q(x) >= k *)
Definition vge (q : nat) (k : int) (x : rat) : Prop := x = 0 \/ k <= vqr q x.

Section Vge.

  Variable q : nat.
  Hypothesis q_prime : prime q.
  Local Abbreviation v := (vqr q).

  Lemma vge0 k : vge q k 0. Proof. by left. Qed.

  Lemma vge_le k k' x : k' <= k -> vge q k x -> vge q k' x.
  Proof. move=> H [ -> | Hx ]; [ by left | right; exact: le_trans Hx ]. Qed.

  Lemma vge_opp k x : vge q k x -> vge q k (- x).
  Proof. move=> [ -> | Hx ]; [ left; exact: oppr0 | right; by rewrite vqrN ]. Qed.

  Lemma vge_add k x y : vge q k x -> vge q k y -> vge q k (x + y).
  Proof using q_prime.
    move=> [ -> | Hx ]; first by rewrite add0r.
    move=> [ -> | Hy ]; first by rewrite addr0; right.
    case: (eqVneq x 0) => [ -> | Hx0 ]; first by rewrite add0r; right.
    case: (eqVneq y 0) => [ -> | Hy0 ]; first by rewrite addr0; right.
    case: (eqVneq (x + y) 0) => [ -> | Hxy ]; first by left.
    right; exact: vqr_add_ge.
  Qed.

  Lemma vge_sub k x y : vge q k x -> vge q k y -> vge q k (x - y).
  Proof using q_prime. move=> Hx Hy; apply: vge_add Hx _; exact: vge_opp. Qed.

  Lemma vge_mul k l x y : vge q k x -> vge q l y -> vge q (k + l) (x * y).
  Proof.
    move=> [ -> | Hx ]; first by rewrite mul0r; left.
    move=> [ -> | Hy ]; first by rewrite mulr0; left.
    case: (eqVneq x 0) => [ -> | Hx0 ]; first by rewrite mul0r; left.
    case: (eqVneq y 0) => [ -> | Hy0 ]; first by rewrite mulr0; left.
    right; rewrite vqrM //; exact: lerD.
  Qed.

  Lemma vge_div k x y : y != 0 -> vge q k x -> vge q (k - v y) (x / y).
  Proof.
    move=> Hy [ -> | Hx ]; first by rewrite mul0r; left.
    case: (eqVneq x 0) => [ -> | Hx0 ]; first by rewrite mul0r; left.
    right; rewrite vqr_div // lerD2r; exact: Hx.
  Qed.

  Lemma vge_int k (z : int) : k <= 0 -> vge q k z%:~R.
  Proof.
    move=> Hk; case: (eqVneq z 0) => [ -> | Hz ]; first by left.
    right; apply: le_trans Hk _; exact: vqr_int_ge0.
  Qed.

  Lemma vge_self x : vge q (v x) x.
  Proof. by right. Qed.

  Lemma vge_neq0 k x : x != 0 -> vge q k x -> k <= v x.
  Proof. by move=> Hx [ E | // ]; move: Hx; rewrite E eqxx. Qed.

End Vge.

Lemma close_vge (x xt : rat) (q k : nat) : close_at x (q, k, xt) -> vge q k%:Z (x - xt).
Proof. by move=> [ -> | H ]; [ left; rewrite subrr | right ]. Qed.

(** * 8. Square-free kernels of positive rationals *)

Definition sqk_N (x : rat) : nat := ((absz (numq x)) * (absz (denq x)))%N.
Definition sqkB (x : rat) : seq nat := [seq p <- primes (sqk_N x) | odd (logn p (sqk_N x))].
Definition sqk (x : rat) : nat := (\prod_(p <- sqkB x) p)%N.

Lemma sqkB_uniq x : uniq (sqkB x). Proof. exact/filter_uniq/primes_uniq. Qed.

Lemma sqkB_prime x : all prime (sqkB x).
Proof. by apply/allP => p; rewrite mem_filter mem_primes => /andP [ _ /andP [ ] ]. Qed.

Lemma sqk_gt0 x : (0 < sqk x)%N. Proof. exact/prod_gt0/sqkB_prime. Qed.

Lemma prodn_sq (L : seq nat) (F : nat -> nat) : ((\prod_(p <- L) F p) ^ 2 = \prod_(p <- L) (F p ^ 2))%N.
Proof.
  elim: L => [ | a L IH ]; first by rewrite !big_nil.
  by rewrite !big_cons expnMn IH.
Qed.

Lemma nat_sq_dec (N : nat) : (0 < N)%N ->
  N = (\prod_(p <- primes N | odd (logn p N)) p * (\prod_(p <- primes N) p ^ (logn p N)./2) ^ 2)%N.
Proof.
  move=> HN; rewrite {1}(prod_prime_decomp HN) prime_decompE big_map /=.
  have E1 : (\prod_(p <- primes N | odd (logn p N)) p = \prod_(p <- primes N) (if odd (logn p N) then p else 1))%N.
  { by rewrite big_mkcond. }
  have E2 : (\prod_(p <- primes N) (if odd (logn p N) then p else 1) * \prod_(p <- primes N) (p ^ (logn p N)./2) ^ 2
           = \prod_(p <- primes N) ((if odd (logn p N) then p else 1) * (p ^ (logn p N)./2) ^ 2))%N.
  { by rewrite -big_split. }
  rewrite prodn_sq E1 E2; apply: eq_bigr => p _.
  rewrite -expnM -{1}(odd_double_half (logn p N)) expnD -muln2.
  by case: (odd (logn p N)); rewrite /= ?expn1 ?expn0 ?mul1n.
Qed.

Lemma sqk_sq (x : rat) : 0 < x -> exists s : rat, s != 0 /\ x = (sqk x)%:R * s ^+ 2.
Proof.
  move=> Hx.
  set n := (absz (numq x)); set d := (absz (denq x)).
  have Hn : (0 < n)%N by rewrite /n absz_gt0 numq_eq0 gt_eqF.
  have Hd : (0 < d)%N by rewrite /d absz_gt0 denq_neq0.
  have HN : (0 < sqk_N x)%N by rewrite /sqk_N muln_gt0 Hn Hd.
  set m := (\prod_(p <- primes (sqk_N x)) p ^ (logn p (sqk_N x))./2)%N.
  set S := (\prod_(p <- primes (sqk_N x) | odd (logn p (sqk_N x))) p)%N.
  have E : sqk_N x = (S * m ^ 2)%N := nat_sq_dec HN.
  have Esqk : sqk x = S by rewrite /sqk /sqkB big_filter.
  have Hm : (0 < m)%N.
  { move: HN; rewrite E muln_gt0 expn_gt0 => /andP [ _ /orP [ // | // ] ]. }
  have Hd0 : (d%:R : rat) != 0 by rewrite pnatr_eq0 -lt0n.
  have Hm0 : (m%:R : rat) != 0 by rewrite pnatr_eq0 -lt0n.
  exists (m%:R / d%:R); split; first by rewrite mulf_neq0 ?invr_eq0.
  have Ex : x = n%:R / d%:R.
  { rewrite /n /d -[x in LHS]divq_num_den.
    have Ez : numq x = (absz (numq x))%:Z by rewrite gez0_abs // ltW // numq_gt0.
    have Ez' : denq x = (absz (denq x))%:Z by rewrite gez0_abs // denq_ge0.
    by rewrite {1}Ez {1}Ez'. }
  have Hnd : (n%:R : rat) * d%:R = S%:R * m%:R ^+ 2.
  { by rewrite -natrM -natrX -natrM -E. }
  rewrite Esqk Ex.
  have -> : (n%:R / d%:R : rat) = (n%:R * d%:R) / d%:R ^+ 2.
  { rewrite expr2 invfM mulrA mulfK //. }
  by rewrite Hnd expr_div_n mulrA.
Qed.

Lemma sqkB_mem (x : rat) (p : nat) : x != 0 -> (p \in sqkB x) = odd (absz (vqr p x)).
Proof.
  move=> Hx; rewrite mem_filter.
  have Hn : (0 < absz (numq x))%N by rewrite absz_gt0 numq_eq0.
  have Hd : (0 < absz (denq x))%N by rewrite absz_gt0 denq_neq0.
  have Eodd : odd (logn p (sqk_N x)) = odd (absz (vqr p x)).
  { rewrite /sqk_N lognM // oddD /vqr.
    by rewrite odd_add abszN. }
  rewrite Eodd; case: (boolP (odd (absz (vqr p x)))) => Ho; rewrite ?andbF ?andbT //.
  by rewrite -logn_gt0; move: Ho; rewrite -Eodd; case: (logn p (sqk_N x)).
Qed.

Lemma sqkB_ndvd (x : rat) (p : nat) : prime p -> p \notin sqkB x -> ~~ (p %| sqk x)%N.
Proof. by move=> Hp Hn; rewrite /sqk dvd_prod_primes // sqkB_prime. Qed.

Lemma sqkB_dvd (x : rat) (p : nat) : p \in sqkB x -> (p %| sqk x)%N.
Proof.
  move=> Hp; have Hpp := allP (sqkB_prime x) p Hp.
  by rewrite /sqk dvd_prod_primes // sqkB_prime.
Qed.

(** * 9. Local squares of integers: Legendre symbols and congruences *)

Lemma qunit_nat (q m : nat) : ~~ (q %| m)%N -> qunit q (Z.of_nat m).
Proof.
  move=> H [ k Hk ]; move/negP: H; apply.
  have Hq0 : (0 <= Z.of_nat q)%ZZ by lia.
  case: (Z.eq_dec (Z.of_nat q) 0) => [ Eq | Hq ].
  - have Em : Z.of_nat m = 0%ZZ by rewrite Hk Eq; lia.
    by have -> : m = 0%N by lia.
  - have Hk0 : (0 <= k)%ZZ by nia.
    apply/dvdnP; exists (Z.to_nat k); rewrite -multE; lia.
Qed.

Lemma zdvd_nat (m a r : nat) : (r < m)%N ->
  (Z.of_nat m | Z.of_nat a - Z.of_nat r)%ZZ <-> (a %% m = r)%N.
Proof.
  move=> Hrm; have Hrm' : (r < m)%coq_nat by apply/ssrnat.ltP.
  split.
  - move=> [ k Hk ].
    have Hk0 : (0 <= k)%ZZ by nia.
    have Ea : a = (Z.to_nat k * m + r)%N by rewrite -multE -plusE; lia.
    by rewrite Ea modnMDl modn_small.
  - move=> H; exists (Z.of_nat (a %/ m)).
    have Ea := divn_eq a m; rewrite H in Ea.
    rewrite {1}Ea -multE -plusE; lia.
Qed.

Lemma Zsq_int (q a : nat) :
  (exists w : Z, (Z.of_nat q | Z.of_nat a * 1 - w * w)%ZZ) <->
  (exists z : int, (z ^+ 2 == a%:Z %[mod q])%Z).
Proof.
  split.
  - move=> [ w [ k Hk ] ]; exists (Z_to_int w); rewrite eqz_mod_dvd; apply/dvdzP.
    exists (- Z_to_int k); apply: iz_inj.
    rewrite iz_add iz_opp expr2 !iz_mul iz_opp !iz_Z_to_int !iz_nat; lia.
  - move=> [ z ]; rewrite eqz_mod_dvd => /dvdzP [ k Hk ].
    exists (int_to_Z z); exists (- int_to_Z k)%ZZ.
    have := congr1 int_to_Z Hk; rewrite iz_add iz_opp expr2 !iz_mul !iz_nat; lia.
Qed.

Lemma locsq_nat_iff (q a : nat) : prime q -> odd q -> ~~ (q %| a)%N ->
  (locsq q a%:R <-> legendre a%:Z q = 1).
Proof.
  move=> Hq Ho Ha.
  have Hq2 : q != 2%N by apply: contraTneq Ho => ->.
  have Hua := qunit_nat Ha.
  have Hu1 : qunit q 1 := qunit1 Hq.
  have Ea : (a%:R : rat) = 1 ^+ 2 * (zr (Z.of_nat a) / zr 1) by rewrite expr1n mul1r zr_nat zr1 divr1.
  rewrite (locsq_iff_rep Hq (oner_neq0 _) Hua Hu1 Ea).
  rewrite (sqmod_odd_prod Hq Hq2 Hua Hu1) Zsq_int (legendre_eq1 Hq Ho).
  by split => [ H | [ _ H ] ]; [ split | ].
Qed.

Lemma locsq2_nat (a : nat) : odd a -> (locsq 2 a%:R <-> (a %% 8 = 1)%N).
Proof.
  move=> Ha.
  have H2a : ~~ (2 %| a)%N by rewrite dvdn2 Ha.
  have Hua := qunit_nat H2a.
  have Hu1 : qunit 2 1 := qunit1 (isT : prime 2).
  have Ea : (a%:R : rat) = 1 ^+ 2 * (zr (Z.of_nat a) / zr 1) by rewrite expr1n mul1r zr_nat zr1 divr1.
  rewrite (locsq_iff_rep (isT : prime 2) (oner_neq0 _) Hua Hu1 Ea).
  rewrite (sqmod_two_prod (erefl 2%N) Hua Hu1) -(@zdvd_nat 8 a 1 isT).
  by rewrite Z.mul_1_r.
Qed.

Lemma unit_nonsq3_nlocsq (x : rat) : unit_nonsq3 x -> ~ locsq 3 x.
Proof.
  move=> [ y [ a [ c [ Hy [ Ha [ Hc [ Ex Hn ] ] ] ] ] ] ] Hl.
  have := locsq_rep (isT : prime 3) Hl Hy Ha Hc Ex; rewrite /sqmod /= => [ [ z Hz ] ].
  exact: (Hn z Hz).
Qed.

Lemma locsq_scale (q : nat) (x y s : rat) : prime q -> s != 0 -> x = y * s ^+ 2 -> locsq q x -> locsq q y.
Proof.
  move=> Hq Hs E Hx.
  have -> : y = x / s ^+ 2 by rewrite E mulfK // expf_neq0.
  apply: locsq_div => //; exact: locsq_sq.
Qed.

Lemma unit_nonsq3_scale (x y s : rat) : s != 0 -> x = y * s ^+ 2 -> unit_nonsq3 x -> unit_nonsq3 y.
Proof.
  move=> Hs E [ y0 [ a [ c [ Hy0 [ Ha [ Hc [ Ex Hn ] ] ] ] ] ] ].
  exists (y0 / s), a, c; split; first by rewrite mulf_neq0 ?invr_eq0.
  do 2 (split => //); split => //.
  have -> : y = x / s ^+ 2 by rewrite E mulfK // expf_neq0.
  by rewrite Ex expr_div_n mulrAC.
Qed.



(** * 10. Lemma par:cross-squares

    03-parity.tex, Sec. 3.2: "Let beta, theta be the unique positive
    squarefree integers representing the square classes of b', H', and let
    B = Supp(beta), J = Supp(theta).

    Lemma (par:cross-squares). The sets B, J are disjoint and avoid 2, 3.
    Moreover,
       theta in Q_q^{x2} (q in B),     beta in Q_q^{x2} (q in J).
    Both beta and theta are squares in Q_2^x; at 3, theta is a square and
    beta is a unit nonsquare. In particular B <> {}."

    The hypotheses of Section CrossSquares are the local choices preceding
    the lemma: (par:b-prime-choices) for b' = m b, (par:d-choices) for
    d = m_d b, and the three properties of t: H' > 0, H' in Q_q^{x2} for
    q in S(m), and v_q(d t^2) > 0 (or t = 0) for q in Supp(m_d) \ S(m). *)

Lemma even_vqr_not_odd (q : nat) (x : rat) : (exists m : int, vqr q x = m + m) -> ~~ odd (absz (vqr q x)).
Proof. by move=> [ m -> ]; rewrite odd_dbl. Qed.

Lemma locsq_not_odd (q : nat) (x : rat) : locsq q x -> ~~ odd (absz (vqr q x)).
Proof. by move=> /locsq_val H; apply: even_vqr_not_odd. Qed.

Lemma unit_nonsq3_not_odd (x : rat) : unit_nonsq3 x -> ~~ odd (absz (vqr 3 x)).
Proof.
  move=> [ y [ a [ c [ Hy [ Ha [ Hc [ -> _ ] ] ] ] ] ] ].
  by apply: even_vqr_not_odd; exists (vqr 3 y); rewrite vqr_rep.
Qed.

(* (1 - X) / (1 + X) is a unit if v(X) <> 0 *)
Lemma unit_quot (q : nat) (X : rat) : prime q -> X != 0 -> vqr q X != 0 ->
  [/\ 1 - X != 0, 1 + X != 0 & vqr q ((1 - X) / (1 + X)) = 0].
Proof.
  move=> Hq HX Hv.
  have HnX : - X != 0 by rewrite oppr_eq0.
  case: (ltrgtP (vqr q X) 0) => Hc; last by move: Hv; rewrite Hc eqxx.
  - (* v X < 0 *)
    have [ H1 E1 ] := vqr_add_lt Hq HnX (oner_neq0 _) ltac:(by rewrite vqrN vqr1).
    have [ H2 E2 ] := vqr_add_lt Hq HX (oner_neq0 _) ltac:(by rewrite vqr1).
    rewrite addrC in H1 E1; rewrite addrC in H2 E2.
    split => //; by rewrite vqr_div // E1 E2 vqrN subrr.
  - (* v X > 0 *)
    have [ H1 E1 ] := vqr_add_lt Hq (oner_neq0 _) HnX ltac:(by rewrite vqrN vqr1).
    have [ H2 E2 ] := vqr_add_lt Hq (oner_neq0 _) HX ltac:(by rewrite vqr1).
    split => //; by rewrite vqr_div // E1 E2 subrr.
Qed.

Lemma S_of_prime (m : rat) (q : nat) : q \in S_of m -> prime q.
Proof.
  rewrite /S_of !in_cons => /orP [ /eqP -> // | /orP [ /eqP -> // | ] ].
  by rewrite mem_cat !mem_primes => /orP [ /andP [ ] | /andP [ ] ].
Qed.

Lemma locsq1 (q : nat) : prime q -> locsq q 1.
Proof. move=> Hq; have := locsq_sq Hq (oner_neq0 rat); by rewrite expr1n. Qed.

Lemma H_eq_gen (x u : rat) : x != 0 -> x * (x - u) = x ^+ 2 * (1 - u / x).
Proof.
  move=> Hx; rewrite expr2; field; exact/eqP.
Qed.

Section CrossSquares.

  Local Set Default Proof Using "All".

  Variables (b : int) (mm md t : rat).

  Local Abbreviation br := (b%:~R : rat).
  Local Abbreviation d := (md * br).
  Local Abbreviation b' := (mm * br).
  Local Abbreviation U := (Phi_U d br t).
  Local Abbreviation H' := (b' * (b' - U ^+ 2)).

  Hypothesis Hb0 : b != 0.
  (* (par:b-prime-choices) *)
  Hypotheses (Hb'pos : 0 < b') (Hb'2 : locsq 2 b') (Hb'3 : unit_nonsq3 b').
  (* (par:d-choices) *)
  Hypothesis Hdpos : 0 < d.
  (* the choice of t: H' > 0, H' a local square at S(m), smallness at Supp(m_d) \ S(m) *)
  Hypothesis HT1 : 0 < H'.
  Hypothesis HT2 : forall q, q \in S_of mm -> locsq q H'.
  Hypothesis HT3 : forall q, prime q -> q \in rat_support md -> q \notin S_of mm ->
                     t = 0 \/ 0 < vqr q (d * t ^+ 2).

  Local Abbreviation beta := (sqk b').
  Local Abbreviation B := (sqkB b').
  Local Abbreviation theta := (sqk H').
  Local Abbreviation J := (sqkB H').

  Lemma cs_b'0 : b' != 0. Proof. exact: lt0r_neq0. Qed.
  Lemma cs_H'0 : H' != 0. Proof. exact: lt0r_neq0. Qed.
  Lemma cs_br0 : br != 0. Proof. by rewrite intr_eq0. Qed.
  Lemma cs_mm0 : mm != 0. Proof. by apply: contraTneq Hb'pos => ->; rewrite mul0r ltxx. Qed.
  Lemma cs_md0 : md != 0. Proof. by apply: contraTneq Hdpos => ->; rewrite mul0r ltxx. Qed.

  Lemma cs_S2 : 2%N \in S_of mm. Proof. by rewrite /S_of mem_head. Qed.
  Lemma cs_S3 : 3%N \in S_of mm. Proof. by rewrite /S_of !in_cons eqxx orbT. Qed.

  Lemma cs_B q : (q \in B) = odd (absz (vqr q b')). Proof. exact: sqkB_mem cs_b'0. Qed.
  Lemma cs_J q : (q \in J) = odd (absz (vqr q H')). Proof. exact: sqkB_mem cs_H'0. Qed.

  Lemma cs_Bprime q : q \in B -> prime q. Proof. by move=> Hq; exact: (allP (sqkB_prime _) q Hq). Qed.
  Lemma cs_Jprime q : q \in J -> prime q. Proof. by move=> Hq; exact: (allP (sqkB_prime _) q Hq). Qed.

  Lemma cs_H'_eq : H' = b' ^+ 2 * (1 - U ^+ 2 / b').
  Proof. exact: H_eq_gen cs_b'0. Qed.

  (* the core: H' is a local square at every q in B *)
  Lemma cs_core q : q \in B -> locsq q H'.
  Proof.
    move=> HqB; have Hq := cs_Bprime HqB.
    case: (boolP (q \in S_of mm)) => HqS; first exact: HT2.
    have Hq2 : q != 2%N by apply: contraNneq HqS => ->; exact: cs_S2.
    have Hq3 : q != 3%N by apply: contraNneq HqS => ->; exact: cs_S3.
    have Hvmm : vqr q mm = 0.
    { apply: vqr_unit; apply: contra HqS => H; by rewrite /S_of !in_cons H !orbT. }
    have Hvb : vqr q br = vqr q b' by rewrite vqrM ?cs_mm0 ?cs_br0 // Hvmm add0r.
    have Hodd : odd (absz (vqr q br)) by rewrite Hvb -cs_B.
    have Hvb1 : 1 <= vqr q br.
    { have H0 := vqr_int_ge0 q b.
      by move: Hodd H0; case: (vqr q br) => [ [ | n ] | n ] //. }
    (* the quotient Psi = (1 - d t^2)/(1 + d t^2) is a unit *)
    set X := d * t ^+ 2.
    have [ HPsi HvPsi ] : (1 - X) / (1 + X) != 0 /\ vqr q ((1 - X) / (1 + X)) = 0.
    { case: (eqVneq t 0) => [ Ht0 | Ht ].
      - rewrite /X Ht0 expr2 !mulr0 subr0; by rewrite divr1 oner_neq0 vqr1.
      - have Hd0 : d != 0 := mulf_neq0 cs_md0 cs_br0.
        have HX : X != 0 := mulf_neq0 Hd0 (expf_neq0 _ Ht).
        have HvX : vqr q X != 0.
        { case: (boolP (q \in rat_support md)) => Hsupp.
          - case: (HT3 Hq Hsupp HqS) => [ E | H ]; first by move: Ht; rewrite E eqxx.
            by rewrite gt_eqF.
          - have Hvmd : vqr q md = 0 by exact: vqr_unit.
            rewrite /X (vqrM q Hd0 (expf_neq0 _ Ht)) (vqrM q cs_md0 cs_br0) Hvmd add0r (vqrX2 q Ht).
            apply/negP => /eqP H0.
            by move: (congr1 (fun z : int => odd (absz z)) H0); rewrite odd_add_dbl Hodd. }
        have [ H1 H2 H3 ] := unit_quot Hq HX HvX.
        by split => //; rewrite mulf_neq0 ?invr_eq0. }
    have EU : U = br * ((1 - X) / (1 + X)) by rewrite /Phi_U mulrA.
    have HU0 : U != 0 by rewrite EU mulf_neq0 ?cs_br0.
    have HvU : vqr q U = vqr q br by rewrite EU vqrM ?cs_br0 // HvPsi addr0.
    set Y := U ^+ 2 / b'.
    have HY0 : Y != 0 by rewrite /Y mulf_neq0 ?invr_eq0 ?expf_neq0 ?cs_b'0.
    have HvY : vqr q Y = vqr q br by rewrite /Y vqr_div ?expf_neq0 ?cs_b'0 // vqrX2 // HvU -Hvb addrK.
    have H1Y : 1 - Y != 0.
    { apply: contra_neq cs_H'0 => E; by rewrite cs_H'_eq -/Y E mulr0. }
    have Hloc : locsq q (1 - Y).
    { apply: (@locsq_close q Hq 1 (1 - Y) (locsq1 Hq) H1Y).
      right; rewrite vqr1 add0r /cq (negbTE Hq2).
      have -> : 1 - Y - 1 = - Y by rewrite addrC addKr.
      rewrite vqrN HvY; exact: Hvb1. }
    rewrite cs_H'_eq; exact: (locsq_mul Hq (locsq_sq Hq cs_b'0) Hloc).
  Qed.

  Lemma cs_BJ q : q \in B -> q \notin J.
  Proof. move=> HqB; rewrite cs_J; exact: locsq_not_odd (cs_core HqB). Qed.

  Lemma cs_theta_sq : exists s : rat, s != 0 /\ H' = theta%:R * s ^+ 2.
  Proof. exact: sqk_sq HT1. Qed.

  Lemma cs_beta_sq : exists s : rat, s != 0 /\ b' = beta%:R * s ^+ 2.
  Proof. exact: sqk_sq Hb'pos. Qed.

  Lemma cs_B_theta q : q \in B -> locsq q theta%:R.
  Proof.
    move=> HqB; have [ s [ Hs E ] ] := cs_theta_sq.
    exact: locsq_scale (cs_Bprime HqB) Hs E (cs_core HqB).
  Qed.

  Lemma cs_J_beta q : q \in J -> locsq q beta%:R.
  Proof.
    move=> HqJ; have Hq := cs_Jprime HqJ.
    have HoH : odd (absz (vqr q H')) by rewrite -cs_J.
    have HqS : q \notin S_of mm.
    { apply/negP => HS; by move: (locsq_not_odd (HT2 HS)); rewrite HoH. }
    have Hq2 : q != 2%N by apply: contraNneq HqS => ->; exact: cs_S2.
    have HqB : q \notin B by apply: contraL HqJ; exact: cs_BJ.
    have Hob : ~~ odd (absz (vqr q b')) by rewrite -cs_B.
    have HU0 : U != 0.
    { apply/negP => /eqP HU; move: HoH.
      by rewrite HU expr0n subr0 -expr2 vqrX2 ?cs_b'0 // odd_dbl. }
    set D := b' - U ^+ 2.
    have HD0 : D != 0 by apply: contra_neq cs_H'0 => E; rewrite -/D E mulr0.
    have HU2 : U ^+ 2 != 0 by rewrite expf_neq0.
    have HnU2 : - U ^+ 2 != 0 by rewrite oppr_eq0.
    have HvH : vqr q H' = vqr q b' + vqr q D by rewrite vqrM ?cs_b'0.
    have HvU2 : vqr q (U ^+ 2) = vqr q U + vqr q U by rewrite vqrX2.
    (* the two valuations agree *)
    have Hag : vqr q b' = vqr q (U ^+ 2).
    { case: (ltrgtP (vqr q b') (vqr q (U ^+ 2))) => // Hc; exfalso.
      - have [ _ E ] := vqr_add_lt Hq cs_b'0 HnU2 ltac:(by rewrite vqrN).
        move: HoH; rewrite HvH -/D /D E.
        by rewrite odd_add (negbTE Hob).
      - have [ _ E ] := vqr_add_lt Hq HnU2 cs_b'0 ltac:(by rewrite vqrN).
        have ED : vqr q D = vqr q U + vqr q U by rewrite /D addrC E vqrN HvU2.
        by move: HoH; rewrite HvH ED odd_add (negbTE Hob) odd_dbl. }
    have HvD : vqr q b' + 1 <= vqr q D.
    { have Hge : vqr q b' <= vqr q D.
      { have Hk : vqr q b' <= vqr q (- U ^+ 2) by rewrite vqrN -Hag.
        exact: (vqr_add_ge Hq cs_b'0 HnU2 HD0 (lexx _) Hk). }
      rewrite lezD1 lt_neqAle Hge andbT; apply/negP => /eqP E.
      move: HoH; by rewrite HvH -E odd_dbl. }
    have Hloc : locsq q (b' / U ^+ 2).
    { have Hne : b' / U ^+ 2 != 0 by rewrite mulf_neq0 ?invr_eq0 ?cs_b'0.
      apply: (@locsq_close q Hq 1 (b' / U ^+ 2) (locsq1 Hq) Hne).
      - right; rewrite vqr1 add0r /cq (negbTE Hq2).
        have -> : b' / U ^+ 2 - 1 = D / U ^+ 2 by rewrite /D mulrBl divff.
        rewrite vqr_div // -Hag.
        by rewrite -(lerD2r (vqr q b')) addrNK addrC. }
    have Hb'loc : locsq q b'.
    { have -> : b' = b' / U ^+ 2 * U ^+ 2 by rewrite mulfVK.
      exact: (locsq_mul Hq Hloc (locsq_sq Hq HU0)). }
    have [ s [ Hs E ] ] := cs_beta_sq.
    exact: locsq_scale Hq Hs E Hb'loc.
  Qed.

  Lemma cs_23 : [/\ 2%N \notin B, 3%N \notin B, 2%N \notin J & 3%N \notin J].
  Proof.
    split.
    - by rewrite cs_B; exact: locsq_not_odd Hb'2.
    - by rewrite cs_B; exact: unit_nonsq3_not_odd Hb'3.
    - by rewrite cs_J; exact: locsq_not_odd (HT2 cs_S2).
    - by rewrite cs_J; exact: locsq_not_odd (HT2 cs_S3).
  Qed.

  Lemma cs_local : [/\ locsq 2 beta%:R, locsq 2 theta%:R, locsq 3 theta%:R & unit_nonsq3 beta%:R].
  Proof.
    have [ s [ Hs E ] ] := cs_beta_sq; have [ s' [ Hs' E' ] ] := cs_theta_sq.
    split.
    - exact: locsq_scale (isT : prime 2) Hs E Hb'2.
    - exact: locsq_scale (isT : prime 2) Hs' E' (HT2 cs_S2).
    - exact: locsq_scale (isT : prime 3) Hs' E' (HT2 cs_S3).
    - exact: unit_nonsq3_scale Hs E Hb'3.
  Qed.

  Lemma cs_Bne : B != [::].
  Proof.
    apply/negP => /eqP HB.
    have [ _ _ _ H ] := cs_local.
    have H1 : beta = 1%N by rewrite /sqk HB big_nil.
    move: H; rewrite H1 => /unit_nonsq3_nlocsq; apply.
    exact: locsq1.
  Qed.

  (** Lemma par:cross-squares *)
  Theorem cross_squares :
    [/\ (forall q, q \in B -> q \notin J),
        [/\ 2%N \notin B, 3%N \notin B, 2%N \notin J & 3%N \notin J],
        (forall q, q \in B -> locsq q theta%:R) /\ (forall q, q \in J -> locsq q beta%:R),
        [/\ locsq 2 beta%:R, locsq 2 theta%:R, locsq 3 theta%:R & unit_nonsq3 beta%:R] &
        B != [::]].
  Proof.
    split; [ exact: cs_BJ | exact: cs_23 | split; [ exact: cs_B_theta | exact: cs_J_beta ] | exact: cs_local | exact: cs_Bne ].
  Qed.

End CrossSquares.



(** * 11. The choice of t (weak approximation) *)

(* a q-adic approximate solution of x t^2 = 1 *)
Lemma local_target (q : nat) (x : rat) (K : nat) : prime q -> locsq q x ->
  exists tq : rat, tq != 0 /\ vge q K%:Z (1 - x * tq ^+ 2).
Proof.
  move=> Hq /(locsq_is_locsq Hq) [ y [ a [ c [ Hy [ Ha [ Hc [ Ex Hu ] ] ] ] ] ] ].
  have [ z Hw ] := Hu K.+1.
  have Hq0 : (0 < Z.of_nat q)%ZZ by have := Z.prime_ge_2 _ (primeZ Hq); lia.
  have Hdq : (Z.of_nat q | a - z * z * c)%ZZ.
  { apply: Z.divide_trans Hw; rewrite -{1}(Z.pow_1_r (Z.of_nat q)).
    apply: pz_dvd; lia. }
  have Hz : qunit q z.
  { move=> Hqz; apply: Ha.
    have Hzzc : (Z.of_nat q | z * z * c)%ZZ by do 2 apply: Z.divide_mul_l.
    have := Z.divide_add_r _ _ _ Hdq Hzzc; by rewrite Z.sub_add. }
  have Hz0 := qunit_neq0 Hz; have Hc0 := qunit_neq0 Hc.
  have Hzr : zr z != 0 by exact: zr_neq0.
  have Hcr : zr c != 0 by exact: zr_neq0.
  exists (y * zr z)^-1; split; first by rewrite invr_eq0 mulf_neq0.
  have HD : (c * z * z <> 0)%ZZ by apply/Z.neq_mul_0; split => //; apply/Z.neq_mul_0.
  have HDu : qunit q (c * z * z) := qunit_mul Hq (qunit_mul Hq Hc Hz) Hz.
  have E : 1 - x * (y * zr z)^-1 ^+ 2 = zr (c * z * z - a) / zr (c * z * z).
  { rewrite Ex zr_sub !zr_mul; field. }
  rewrite E.
  apply: (vge_le (k := (K.+1)%:Z - vqr q (zr (c * z * z)))).
  { by rewrite (vqr_zr_unit HDu) subr0 lez_nat. }
  apply: vge_div; first exact: zr_neq0.
  case: (Z.eq_dec (c * z * z - a)%ZZ 0%ZZ) => [ E0 | HN ]; first by rewrite E0 zr0; left.
  right; apply: vqr_zr_ge Hq HN _.
  have -> : (c * z * z - a = - (a - z * z * c))%ZZ by lia.
  exact/Z.divide_opp_r.
Qed.

(* finite choice over a list *)
Lemma list_choice (A : Type) (P : nat -> A -> Prop) (s : seq nat) (a0 : A) :
  (forall q, q \in s -> exists x, P q x) -> exists f : nat -> A, forall q, q \in s -> P q (f q).
Proof.
  elim: s => [ | q s IH ] H; first by exists (fun _ => a0).
  have [ f Hf ] := IH (fun q' Hq' => H q' (mem_behead (s := q :: s) Hq')).
  have [ x Hx ] := H q (mem_head _ _).
  exists (fun q' => if q' == q then x else f q') => q'; rewrite in_cons.
  case: (eqVneq q' q) => [ -> // | _ /= Hq' ]; exact: Hf.
Qed.

Lemma In_mem_nat (x : nat) (s : seq nat) : List.In x s -> x \in s.
Proof.
  elim: s => [ // | y s IH ] /= [ -> | /IH H ]; rewrite inE ?eqxx //.
  by rewrite H orbT.
Qed.

Lemma mem_In_nat (x : nat) (s : seq nat) : x \in s -> List.In x s.
Proof.
  elim: s => [ // | y s IH ]; rewrite inE => /orP [ /eqP -> | H ]; [ by left | right; exact: IH ].
Qed.

Lemma mem_In_eq (T : eqType) (x : T) (s : seq T) : x \in s -> List.In x s.
Proof.
  elim: s => [ // | y s IH ]; rewrite inE => /orP [ /eqP -> | H ]; [ by left | right; exact: IH ].
Qed.

Lemma uniq_NoDup (s : seq nat) : uniq s -> NoDup s.
Proof.
  elim: s => [ | x s IH ] /=; first by constructor.
  move=> /andP [ Hx Hs ]; constructor; last exact: IH.
  by move=> /In_mem_nat H; move: Hx; rewrite H.
Qed.

Lemma absz_bounds (x : int) : - (absz x)%:Z <= x /\ x <= (absz x)%:Z.
Proof.
  rewrite abszE; split; [ rewrite lerNl -normrN; exact: ler_norm | exact: ler_norm ].
Qed.

Lemma zr_le (a b : Z) : (a <= b)%ZZ -> zr a <= zr b.
Proof. move=> H; rewrite !zr_Z ler_int; apply/iz_le; by rewrite !iz_Z_to_int. Qed.

(* a rational approximate square root of 1/d *)
Lemma real_target (d eta : rat) : 0 < d -> 0 < eta -> exists r : rat, `|1 - d * r ^+ 2| < eta.
Proof.
  move=> Hd He.
  set P := int_to_Z (numq d); set Qd := int_to_Z (denq d).
  have HP : (0 < P)%ZZ by have := proj1 (iz_lt 0 (numq d)); apply; rewrite numq_gt0.
  have HQ : (0 < Qd)%ZZ by have := proj1 (iz_lt 0 (denq d)); apply; rewrite denq_gt0.
  have Ed : d = zr P / zr Qd by rewrite /P /Qd !zr_iz divq_num_den.
  set N := (int_to_Z (Num.floor (2 / eta)) + 1)%ZZ.
  have HNe : 2 / eta < zr N.
  { by rewrite /N zr_add zr_iz zr1 -intrD1 floorD1_gt. }
  have HN0 : (0 <= int_to_Z (Num.floor (2 / eta)))%ZZ.
  { apply/iz_ge0; rewrite floor_ge0 divr_ge0 // ltW //. }
  have HN : (1 <= N)%ZZ by rewrite /N; lia.
  set M := (N * N * P * Qd)%ZZ.
  have HM : (0 < M)%ZZ by rewrite /M; nia.
  set k := Z.sqrt M.
  have [ Hk1 Hk2 ] := Z.sqrt_spec M (Z.lt_le_incl _ _ HM).
  rewrite -/k in Hk1 Hk2.
  have Hk0 : (0 <= k)%ZZ := Z.sqrt_nonneg M.
  have HNNM : (N * N <= M)%ZZ.
  { rewrite /M; have HPQ : (1 <= P * Qd)%ZZ by nia.
    have := Z.mul_le_mono_nonneg_l _ _ (N * N) ltac:(nia) HPQ; lia. }
  have HNk : (N <= k)%ZZ.
  { case: (Z.le_gt_cases N k) => // H.
    have H' : (Z.succ k <= N)%ZZ by lia.
    have : (Z.succ k * Z.succ k <= N * N)%ZZ by apply: Z.mul_le_mono_nonneg; lia.
    lia. }
  have HMk : (0 <= M - k * k)%ZZ by lia.
  have HMk3 : (M - k * k <= 2 * k)%ZZ by rewrite /Z.succ in Hk2; nia.
  have HMk2 : ((M - k * k) * N <= 2 * M)%ZZ.
  { have E1 : ((M - k * k) * N <= 2 * k * N)%ZZ by apply: Z.mul_le_mono_nonneg_r; lia.
    have E2 : (2 * k * N <= 2 * k * k)%ZZ by apply: Z.mul_le_mono_nonneg_l; lia.
    lia. }
  exists (zr k / (zr N * zr P)).
  have HNr : zr N != 0 by apply: zr_neq0; lia.
  have HPr : zr P != 0 by apply: zr_neq0; lia.
  have HQr : zr Qd != 0 by apply: zr_neq0; lia.
  have HMr : 0 < zr M by apply/zr_pos.
  have E : 1 - d * (zr k / (zr N * zr P)) ^+ 2 = zr (M - k * k) / zr M.
  { rewrite Ed /M zr_sub !zr_mul; field. }
  have HMk' : 0 <= zr (M - k * k) by have := zr_le HMk; rewrite zr0.
  rewrite E (ger0_norm (divr_ge0 HMk' (ltW HMr))).
  have H1 : zr (M - k * k) * zr N <= 2 * zr M.
  { have Z2 : zr 2 = 2 by rewrite (_ : 2%ZZ = Z.of_nat 2) // zr_nat.
    have := zr_le HMk2; by rewrite !zr_mul Z2. }
  have HNpos : 0 < zr N by apply/zr_pos; lia.
  have H2 : 2 < eta * zr N.
  { have := HNe; rewrite ltr_pdivrMr //. by rewrite mulrC. }
  rewrite ltr_pdivrMr //.
  nra.
Qed.

(* continuity of t |-> d t^2 at r *)
Lemma real_close (d r eta : rat) : 0 < d -> 0 < eta ->
  exists eps : rat, 0 < eps /\ forall t, `|t - r| < eps -> `|d * t ^+ 2 - d * r ^+ 2| < eta.
Proof.
  move=> Hd He.
  set X := d * (2 * `|r| + 1).
  have HX : 0 < X by rewrite /X mulr_gt0 // ltr_wpDl // mulr_ge0.
  exists (eta / (X + eta)); split; first by rewrite divr_gt0 // addr_gt0.
  move=> t Ht.
  set s := t - r.
  have Et : t = r + s by rewrite /s addrC subrK.
  have E : d * t ^+ 2 - d * r ^+ 2 = d * (s * (2 * r + s)) by rewrite Et !expr2; ring.
  have Heps1 : eta / (X + eta) < 1 by rewrite ltr_pdivrMr ?addr_gt0 // mul1r ltrDr.
  have Hs1 : `|s| < 1 := lt_trans Ht Heps1.
  have Hn : `|2 * r + s| <= 2 * `|r| + 1.
  { apply: le_trans (ler_normD _ _) _; rewrite normrM ger0_norm //; apply: lerD => //; exact: ltW. }
  rewrite E normrM (gtr0_norm Hd) normrM.
  have Hss : `|s| * `|2 * r + s| <= `|s| * (2 * `|r| + 1) by apply: ler_wpM2l.
  have Hs2 : `|s| * (2 * `|r| + 1) < eta / (X + eta) * (2 * `|r| + 1).
  { have Hpos : 0 < 2 * `|r| + 1 by rewrite ltr_wpDl // mulr_ge0.
    by rewrite (ltr_pM2r Hpos). }
  have Hfin : d * (eta / (X + eta) * (2 * `|r| + 1)) < eta.
  { rewrite mulrCA -/X mulrAC.
    have HXe : 0 < X + eta by rewrite addr_gt0.
    rewrite (ltr_pdivrMr _ _ HXe) (ltr_pM2l He); by rewrite ltrDl. }
  apply: le_lt_trans Hfin; rewrite (ler_pM2l Hd).
  exact: le_trans Hss (ltW Hs2).
Qed.

Lemma vqr2_le1 (q : nat) : prime q -> vqr q 2 <= 1.
Proof.
  move=> Hq; have -> : vqr q 2 = (logn q 2)%:Z by exact: (vqr_int q 2).
  by rewrite (logn_prime _ (isT : prime 2)); case: (q == 2%N).
Qed.

(* if d t^2 is q-adically close to 1, then H' is a local square at q *)
Lemma H'_locsq (q : nat) (b' br d t : rat) (K : nat) : prime q -> br != 0 -> b' != 0 ->
  (absz (vqr q b'))%:Z + (absz (vqr q br))%:Z + 3 <= K%:Z ->
  vge q K%:Z (1 - d * t ^+ 2) -> b' * (b' - Phi_U d br t ^+ 2) != 0 ->
  locsq q (b' * (b' - Phi_U d br t ^+ 2)).
Proof.
  move=> Hq Hbr Hb' HK Hw HH.
  have [ w Ew ] : exists w, w = 1 - d * t ^+ 2 by eexists.
  rewrite -Ew in Hw.
  have E2 : 1 + d * t ^+ 2 = 2 - w by rewrite Ew; ring.
  have EU : Phi_U d br t = br * w / (2 - w) by rewrite /Phi_U E2 -Ew.
  case: Hw => [ Hw0 | Hvw ].
  - have -> : Phi_U d br t = 0 by rewrite EU Hw0 mulr0 mul0r.
    rewrite expr0n /= subr0 -expr2; exact: locsq_sq.
  - have Hw0 : w != 0.
    { apply/eqP => E; move: Hvw HK; rewrite E vqr0.
      rewrite !iz_le !iz_add !iz_nat /=; lia. }
    have Hv2 := vqr2_le1 Hq.
    have H20 : (2 : rat) != 0 by [].
    have Hnw : - w != 0 by rewrite oppr_eq0.
    have Hlt : vqr q 2 < vqr q (- w).
    { rewrite vqrN; move: Hv2 Hvw HK; move: (vqr q 2) (vqr q w) => T W.
      rewrite !iz_le !iz_lt !iz_add !iz_nat; lia. }
    have [ H2w Hv2w ] := vqr_add_lt Hq H20 Hnw Hlt.
    have HU0 : Phi_U d br t != 0 by rewrite EU mulf_neq0 ?invr_eq0 ?mulf_neq0.
    have HvU : vqr q (Phi_U d br t) = vqr q br + vqr q w - vqr q 2.
    { by rewrite EU (vqr_div q (mulf_neq0 Hbr Hw0) H2w) (vqrM q Hbr Hw0) Hv2w. }
    have HU2 : Phi_U d br t ^+ 2 != 0 by rewrite expf_neq0.
    have HY0 : Phi_U d br t ^+ 2 / b' != 0 by rewrite mulf_neq0 ?invr_eq0.
    have HvY : vqr q (Phi_U d br t ^+ 2 / b') = vqr q (Phi_U d br t) + vqr q (Phi_U d br t) - vqr q b'.
    { by rewrite (vqr_div q HU2 Hb') (vqrX2 q HU0). }
    have HY3 : 3 <= vqr q (Phi_U d br t ^+ 2 / b').
    { have [ Ha1 Ha2 ] := absz_bounds (vqr q br); have [ Hb1 Hb2 ] := absz_bounds (vqr q b').
      rewrite HvY HvU; move: Ha1 Ha2 Hb1 Hb2 Hvw Hv2 HK.
      move: (vqr q br) (vqr q b') (vqr q w) (vqr q 2) => a bb W T.
      rewrite !iz_le !iz_add !iz_opp !iz_nat; lia. }
    have HnY : - (Phi_U d br t ^+ 2 / b') != 0 by rewrite oppr_eq0.
    have HltY : vqr q 1 < vqr q (- (Phi_U d br t ^+ 2 / b')).
    { rewrite vqr1 vqrN; apply: lt_le_trans HY3; by []. }
    have [ H1Y _ ] := vqr_add_lt Hq (oner_neq0 _) HnY HltY.
    have Hloc : locsq q (1 - Phi_U d br t ^+ 2 / b').
    { apply: (@locsq_close q Hq 1 _ (locsq1 Hq) H1Y); right.
      rewrite vqr1 add0r.
      have -> : 1 - Phi_U d br t ^+ 2 / b' - 1 = - (Phi_U d br t ^+ 2 / b') by rewrite addrC addKr.
      rewrite vqrN; apply: le_trans HY3; rewrite /cq; by case: (q == 2%N). }
    rewrite (H_eq_gen _ Hb'); exact: (locsq_mul Hq (locsq_sq Hq Hb') Hloc).
Qed.

(* closeness of t to the local solution tq transfers to 1 - d t^2 *)
Lemma close_one (q : nat) (d tq t : rat) (K : nat) : prime q -> tq != 0 ->
  vge q K%:Z (1 - d * tq ^+ 2) -> vge q (K + absz (vqr q tq))%N%:Z (t - tq) ->
  vge q K%:Z (1 - d * t ^+ 2).
Proof.
  move=> Hq Htq Hw0 Hc.
  set w0 := 1 - d * tq ^+ 2.
  set u := (t - tq) / tq.
  have E : 1 - d * t ^+ 2 = w0 - (1 - w0) * (2 * u + u ^+ 2).
  { rewrite /w0 /u; field; exact/eqP. }
  rewrite E.
  have Hv1 : vge q 0 1 := @vge_int q 0 1 (lexx _).
  have Hv2 : vge q 0 2 := @vge_int q 0 2 (lexx _).
  have HK0 : 0 <= K%:Z by [].
  have Hu : vge q K%:Z u.
  { apply: vge_le (vge_div Htq Hc).
    have [ H1 H2 ] := absz_bounds (vqr q tq).
    move: H1 H2; rewrite PoszD; move: (vqr q tq) => v.
    rewrite !iz_le !iz_add !iz_opp !iz_nat; lia. }
  have Hw0' : vge q 0 w0 := vge_le HK0 Hw0.
  have H1w : vge q 0 (1 - w0) := vge_sub Hq Hv1 Hw0'.
  have H2u : vge q K%:Z (2 * u) by rewrite -[K%:Z]add0r; exact: vge_mul Hv2 Hu.
  have Hu2 : vge q K%:Z (u ^+ 2).
  { rewrite expr2; apply: vge_le (vge_mul Hu Hu); by rewrite lerDr. }
  have Hs : vge q K%:Z (2 * u + u ^+ 2) := vge_add Hq H2u Hu2.
  have Hp : vge q K%:Z ((1 - w0) * (2 * u + u ^+ 2)) by rewrite -[K%:Z]add0r; exact: vge_mul H1w Hs.
  have := @vge_sub q Hq K%:Z w0 ((1 - w0) * (2 * u + u ^+ 2)) Hw0 Hp. by [].
Qed.

(* the real place: H' > 0 if d t^2 is close to 1 *)
Lemma real_H'_pos (br b' w : rat) : 0 < b' ->
  `|w| < b' / (2 * (b' + br ^+ 2 + 1)) -> 0 < b' * (b' - (br * w / (2 - w)) ^+ 2).
Proof.
  move=> Hb Hw.
  set eta := b' / (2 * (b' + br ^+ 2 + 1)).
  have Hbr2 : 0 <= br ^+ 2 := sqr_ge0 br.
  have HD : 0 < 2 * (b' + br ^+ 2 + 1) by rewrite mulr_gt0 // addr_gt0 // ltr_wpDr.
  have He : 0 < eta by rewrite divr_gt0.
  have He2 : eta * (2 * (b' + br ^+ 2 + 1)) = b' by rewrite /eta mulfVK // gt_eqF.
  have Hw1 : -eta < w < eta by rewrite -ltr_norml.
  move/andP: Hw1 => [ Hwl Hwr ].
  have Heta : eta < 1 / 2 by nra.
  have H2w : 1 < 2 - w by nra.
  have Hw2 : w ^+ 2 < eta * eta by rewrite expr2; nra.
  have HU : (br * w / (2 - w)) ^+ 2 <= br ^+ 2 * w ^+ 2.
  { rewrite expr_div_n exprMn ler_pdivrMr ?exprn_gt0 ?(lt_trans ltr01 H2w) //.
    have : 1 <= (2 - w) ^+ 2 by rewrite expr2; nra.
    have : 0 <= br ^+ 2 * w ^+ 2 by rewrite mulr_ge0 // sqr_ge0.
    nra. }
  have Hfin : br ^+ 2 * w ^+ 2 < b'.
  { have : br ^+ 2 * w ^+ 2 <= br ^+ 2 * (eta * eta) by rewrite ler_wpM2l // ltW.
    nra. }
  apply: mulr_gt0 => //; rewrite subr_gt0; exact: le_lt_trans HU Hfin.
Qed.

Lemma choose_t_gen (br b' d : rat) (S T : seq nat) :
  br != 0 -> 0 < b' -> 0 < d -> uniq S -> uniq T -> all prime S -> all prime T ->
  (forall q, q \in S -> q \notin T) -> (forall q, q \in S -> locsq q d) ->
  exists t : rat, [/\ 0 < b' * (b' - Phi_U d br t ^+ 2),
      forall q, q \in S -> locsq q (b' * (b' - Phi_U d br t ^+ 2)) &
      forall q, q \in T -> t = 0 \/ 0 < vqr q (d * t ^+ 2)].
Proof.
  move=> Hbr Hb' Hd HuS HuT HpS HpT HST HS.
  have Hb'0 : b' != 0 by rewrite gt_eqF.
  set K := fun q : nat => (absz (vqr q b') + absz (vqr q br) + 3)%N.
  have [ f Hf ] := @list_choice rat (fun q tq => tq != 0 /\ vge q (K q)%:Z (1 - d * tq ^+ 2)) S 0
                     (fun q Hq => local_target (K q) (allP HpS q Hq) (HS q Hq)).
  set k := fun q : nat => (K q + absz (vqr q (f q)))%N.
  set kz := fun q : nat => (absz (vqr q d)).+1.
  set L := [seq (q, k q, f q) | q <- S] ++ [seq (q, kz q, 0) | q <- T].
  set eta := b' / (2 * (b' + br ^+ 2 + 1)).
  have HD : 0 < 2 * (b' + br ^+ 2 + 1) by rewrite mulr_gt0 // addr_gt0 // ltr_wpDr // sqr_ge0.
  have He : 0 < eta by rewrite divr_gt0.
  have He2 : 0 < eta / 2 by rewrite divr_gt0.
  have [ r Hr ] := real_target Hd He2.
  have [ eps [ Heps Hclose ] ] := real_close r Hd He2.
  have HmapL : map tq L = S ++ T.
  { by rewrite map_cat -!map_comp !map_id_in. }
  have HND : NoDup (map tq L).
  { rewrite HmapL; apply: uniq_NoDup; rewrite cat_uniq HuS HuT andbT /=.
    by apply/hasPn => x Hx; apply/negP => HxS; move: (HST x HxS); rewrite Hx. }
  have HPr : List.Forall (fun t => prime (tq t)) L.
  { apply/List.Forall_forall => x Hx.
    have : tq x \in map tq L by apply: In_mem_nat; apply: List.in_map.
    by rewrite HmapL mem_cat => /orP [ H | H ]; [ exact: (allP HpS) | exact: (allP HpT) ]. }
  have [ t [ Htr Ht ] ] := weak_approx_inf r HND HPr Heps.
  have HtL : forall x, x \in L -> close_at t x.
  { move=> x Hx; move: Ht => /List.Forall_forall; apply; exact: mem_In_eq. }
  (* the real place *)
  have Hw : `|1 - d * t ^+ 2| < eta.
  { have E : 1 - d * t ^+ 2 = (1 - d * r ^+ 2) - (d * t ^+ 2 - d * r ^+ 2) by ring.
    rewrite E; apply: le_lt_trans (ler_normB _ _) _.
    have -> : eta = eta / 2 + eta / 2 by rewrite -mulr2n -mulr_natr mulfVK.
    exact: ltrD Hr (Hclose t Htr). }
  have E2 : 1 + d * t ^+ 2 = 2 - (1 - d * t ^+ 2) by ring.
  have EU : Phi_U d br t = br * (1 - d * t ^+ 2) / (2 - (1 - d * t ^+ 2)) by rewrite /Phi_U E2.
  have Hpos : 0 < b' * (b' - Phi_U d br t ^+ 2) by rewrite EU; exact: real_H'_pos.
  exists t; split => //.
  - move=> q Hq.
    have Hqp : prime q := allP HpS q Hq.
    have [ Hfq Hfw ] := Hf q Hq.
    have Hcl : close_at t (q, k q, f q) by apply: HtL; rewrite mem_cat; apply/orP; left; apply/mapP; exists q.
    have Hw' := close_one Hqp Hfq Hfw (close_vge Hcl).
    apply: (H'_locsq (K := K q)) => //; last by rewrite gt_eqF.
  - move=> q Hq.
    have Hqp : prime q := allP HpT q Hq.
    have Hcl : close_at t (q, kz q, 0) by apply: HtL; rewrite mem_cat; apply/orP; right; apply/mapP; exists q.
    case: Hcl => [ Ht0 | Hvt ]; first by left.
    case: (eqVneq t 0) => [ Ht0 | Ht0 ]; first by left.
    right; rewrite subr0 in Hvt.
    rewrite (vqrM q (negbT (gt_eqF Hd)) (expf_neq0 _ Ht0)) (vqrX2 q Ht0).
    have [ H1 _ ] := absz_bounds (vqr q d).
    move: H1 Hvt; rewrite /kz; move: (vqr q d) (vqr q t) => a v.
    rewrite !iz_le !iz_lt !iz_add !iz_opp !iz_nat; lia.
Qed.



(** * 12. The hypothesis: Lemma par:descent + Lemma par:global-point

    03-parity.tex: "Lemma (par:descent). Let l > 0 be squarefree, prime to 6,
    with l = 3 (mod 4) and l = 2 (mod 3). Suppose that its support Q contains
    the nonempty set B of Lemma par:cross-squares and a prime outside B, and
    suppose that ker K = <1, 1_B>, lambda not in im K. Then
    dim Sel_2(E_l/Q) = 3, and (beta, 1) is a Selmer class outside the
    subgroup of rational two-torsion classes, in Kummer coordinates
    (x + 3l, x - l)."
    "Lemma (par:global-point). Under the hypotheses of Lemma par:descent,
    the curve E_l has a rational point with nonzero x-coordinate in
    beta Q^{x2}."
    Of beta and B, Lemma par:descent uses: beta = prod B > 0, beta a square
    in Q_2 (beta = 1 mod 8) and a unit nonsquare at 3 (beta = 2 mod 3). *)

(* TO-MERGE from SelDescent.v / TwoConverse.v *)
Definition global_point_El : Prop :=
  forall (l : int) (B : seq nat),
    admissible_l l -> uniq B -> all prime B ->
    ((\prod_(p <- B) p) %% 8 = 1)%N -> ((\prod_(p <- B) p) %% 3 = 2)%N ->
    {subset B <= primes (absz l)} -> (exists p, p \in primes (absz l) /\ p \notin B) ->
    ker_target (primes (absz l)) B -> lam_notin_im (primes (absz l)) ->
    exists x y : rat, y ^+ 2 = x * (x - l%:~R) * (x + 3 * l%:~R) /\ x != 0 /\
      sqc x (\prod_(p <- B) p)%N%:Z /\ sqc (x - l%:~R) 1.

(** * 13. The twist isomorphism (par:twist-scaling) *)

Lemma El_point_twist (l c b' : rat) : c != 0 -> El_point l b' -> El_point (l * c ^+ 2) b'.
Proof.
  move=> Hc [ x [ y [ z [ Hz [ Ex Hy ] ] ] ] ].
  exists (c ^+ 2 * x), (c ^+ 3 * y), (c * z); split; first by rewrite mulf_neq0.
  split; first by rewrite Ex; ring.
  have -> : (c ^+ 3 * y) ^+ 2 = c ^+ 6 * y ^+ 2 by ring.
  rewrite Hy; ring.
Qed.

(** * 14. Lemma par:simultaneous-matrices for the lists of par:cross-squares *)

Lemma prime_gt3 (p : nat) : prime p -> p != 2%N -> p != 3%N -> (3 < p)%N.
Proof.
  move=> Hp H2 H3; have := prime_gt1 Hp.
  by move: H2 H3; case: p {Hp} => [ | [ | [ | [ | ] ] ] ].
Qed.

Lemma odd_prime_ne2 (p : nat) : prime p -> p != 2%N -> odd p.
Proof. by move=> Hp H2; case: (even_prime Hp) => // E; move: H2; rewrite E eqxx. Qed.

Section SimultaneousMatrices.

  Local Set Default Proof Using "All".

  Variables (b : int) (mm md t : rat).

  Local Abbreviation br := (b%:~R : rat).
  Local Abbreviation d := (md * br).
  Local Abbreviation b' := (mm * br).
  Local Abbreviation U := (Phi_U d br t).
  Local Abbreviation H' := (b' * (b' - U ^+ 2)).

  Hypothesis Hb0 : b != 0.
  Hypotheses (Hb'pos : 0 < b') (Hb'2 : locsq 2 b') (Hb'3 : unit_nonsq3 b').
  Hypothesis Hdpos : 0 < d.
  Hypothesis HT1 : 0 < H'.
  Hypothesis HT2 : forall q, q \in S_of mm -> locsq q H'.
  Hypothesis HT3 : forall q, prime q -> q \in rat_support md -> q \notin S_of mm ->
                     t = 0 \/ 0 < vqr q (d * t ^+ 2).

  Local Abbreviation B := (sqkB b').
  Local Abbreviation J := (sqkB H').
  Local Abbreviation beta := (\prod_(p <- sqkB b') p)%N.
  Local Abbreviation theta := (\prod_(p <- sqkB H') p)%N.

  (* the consequences of par:cross-squares in the form of Legendre symbols
     and congruences (the hypotheses of [sim_matrices]) *)
  Lemma cross_squares_nat :
    [/\ (forall q, q \in B -> (3 < q)%N) /\ (forall q, q \in J -> (3 < q)%N),
        (beta %% 8 = 1)%N /\ (theta %% 8 = 1)%N,
        (beta %% 3 = 2)%N /\ (theta %% 3 = 1)%N,
        (forall q, q \in B -> legendre theta%:Z q = 1) /\ (forall q, q \in J -> legendre beta%:Z q = 1) &
        (forall q, q \in B -> q \notin J) /\ B != [::]].
  Proof.
    have [ HBJ [ H2B H3B H2J H3J ] [ HBth HJbe ] [ Hl2b Hl2t Hl3t Hu3b ] HBne ] :=
      cross_squares Hb0 Hb'pos Hb'2 Hb'3 Hdpos HT1 HT2 HT3.
    rewrite /sqk in Hl2b Hl2t Hl3t Hu3b HBth HJbe.
    have HBp : all prime B := sqkB_prime _.
    have HJp : all prime J := sqkB_prime _.
    have HB3 : forall q, q \in B -> (3 < q)%N.
    { move=> q Hq; apply: prime_gt3; first exact: (allP HBp).
      - by apply: contraNneq H2B => E; rewrite E in Hq.
      - by apply: contraNneq H3B => E; rewrite E in Hq. }
    have HJ3 : forall q, q \in J -> (3 < q)%N.
    { move=> q Hq; apply: prime_gt3; first exact: (allP HJp).
      - by apply: contraNneq H2J => E; rewrite E in Hq.
      - by apply: contraNneq H3J => E; rewrite E in Hq. }
    have Hbodd : odd beta.
    { by rewrite -[odd _]negbK -dvdn2 (dvd_prod_primes (isT : prime 2) HBp) H2B. }
    have Htodd : odd theta.
    { by rewrite -[odd _]negbK -dvdn2 (dvd_prod_primes (isT : prime 2) HJp) H2J. }
    have Hb8 : (beta %% 8 = 1)%N := (locsq2_nat Hbodd).1 Hl2b.
    have Ht8 : (theta %% 8 = 1)%N := (locsq2_nat Htodd).1 Hl2t.
    have H3b : ~~ (3 %| beta)%N by rewrite (dvd_prod_primes (isT : prime 3) HBp).
    have H3t : ~~ (3 %| theta)%N by rewrite (dvd_prod_primes (isT : prime 3) HJp).
    have Hb3 : (beta %% 3 = 2)%N.
    { have : (beta %% 3 < 3)%N by rewrite ltn_mod.
      case E : (beta %% 3)%N => [ | [ | [ | n ] ] ] // _.
      - by move: H3b; rewrite /dvdn E.
      - exfalso; apply: (unit_nonsq3_nlocsq Hu3b).
        apply/(locsq_nat_iff (isT : prime 3) (isT : odd 3) H3b).
        by rewrite legendre_3 modz_nat E. }
    have Ht3 : (theta %% 3 = 1)%N.
    { apply: legendre3_nat; exact/(locsq_nat_iff (isT : prime 3) (isT : odd 3) H3t). }
    have HthB : forall q, q \in B -> legendre theta%:Z q = 1.
    { move=> q Hq; have Hqp := allP HBp q Hq.
      have Hq2 : q != 2%N by apply: contraNneq H2B => E; rewrite E in Hq.
      apply/(locsq_nat_iff Hqp (odd_prime_ne2 Hqp Hq2)); last exact: HBth.
      by rewrite (dvd_prod_primes Hqp HJp) (HBJ q Hq). }
    have HbeJ : forall q, q \in J -> legendre beta%:Z q = 1.
    { move=> q Hq; have Hqp := allP HJp q Hq.
      have Hq2 : q != 2%N by apply: contraNneq H2J => E; rewrite E in Hq.
      apply/(locsq_nat_iff Hqp (odd_prime_ne2 Hqp Hq2)); last exact: HJbe.
      rewrite (dvd_prod_primes Hqp HBp); apply/negP => HqB.
      by move: (HBJ q HqB); rewrite Hq. }
    by split.
  Qed.

  (** Lemma par:simultaneous-matrices *)
  Theorem simultaneous_matrices : exists n : nat,
    [/\ (0 < n)%N, coprime n (6 * theta), {subset B <= primes n},
        (exists p, p \in primes n /\ p \notin B) &
        forall l : nat, l = n \/ l = (n * theta)%N ->
          [/\ (l %% 4 = 3)%N, (l %% 3 = 2)%N, sqfree_int l%:Z,
              {subset B <= primes l} /\ (exists p, p \in primes l /\ p \notin B) &
              ker_target (primes l) B /\ lam_notin_im (primes l)]].
  Proof.
    have [ [ HB3 HJ3 ] [ Hb8 Ht8 ] [ Hb3 Ht3 ] [ HthB HbeJ ] [ HBJ HBne ] ] := cross_squares_nat.
    have HBu : uniq B := sqkB_uniq _.
    have HJu : uniq J := sqkB_uniq _.
    have HBp : all prime B := sqkB_prime _.
    have HJp : all prime J := sqkB_prime _.
    move: HBu HBp HB3 HBJ Hb8 Hb3 HthB HbeJ HBne.
    case: (sqkB b') => [ | bs Bt ] HBu HBp HB3 HBJ Hb8 Hb3 HthB HbeJ HBne //.
    exact: (sim_matrices HBu HJu HBp HJp HB3 HJ3 HBJ Hb8 Ht8 Hb3 Ht3 HthB HbeJ).
  Qed.

End SimultaneousMatrices.

(** * 15. Assembly of Prop par:pole-parity (1) *)

Section Assembly.

  Local Set Default Proof Using "All".

  Hypothesis HGP : global_point_El.

  (* the integer witnesses for one integer b *)
  Theorem PP1_int (L : seq (rat * seq rat)) : CoversM L -> CoversD L ->
    forall b : int, Phi_math L (b%:~R : rat).
  Proof.
    move=> HM HD b.
    case: (eqVneq b 0) => [ -> | Hb0 ]; first by left.
    right; split; first by rewrite intr_eq0.
    have Hbr : (b%:~R : rat) != 0 by rewrite intr_eq0.
    (* the entries m, m_d of the lists (par:b-prime-choices), (par:d-choices) *)
    have [ mm [ Dm [ HIn [ Hb'pos [ Hb'2 Hb'3 ] ] ] ] ] := HM _ Hbr.
    have [ md [ HInd [ Hdpos HdS ] ] ] := HD _ _ HIn _ Hbr.
    (* the choice of t (weak approximation) *)
    set S := undup (S_of mm).
    set T := [seq q <- undup (rat_support md) | q \notin S_of mm].
    have HuS : uniq S := undup_uniq _.
    have HuT : uniq T := filter_uniq _ (undup_uniq _).
    have HpS : all prime S by apply/allP => q; rewrite mem_undup; exact: S_of_prime.
    have HpT : all prime T.
    { apply/allP => q; rewrite mem_filter mem_undup => /andP [ _ ].
      by rewrite /rat_support mem_cat !mem_primes => /orP [ /andP [ ? _ ] | /andP [ ? _ ] ]. }
    have HST : forall q, q \in S -> q \notin T by move=> q; rewrite mem_undup mem_filter => ->.
    have HSd : forall q, q \in S -> locsq q (md * b%:~R) by move=> q; rewrite mem_undup; exact: HdS.
    have [ t [ HT1 HT2' HT3' ] ] := choose_t_gen Hbr Hb'pos Hdpos HuS HuT HpS HpT HST HSd.
    have HT2 : forall q, q \in S_of mm ->
        locsq q (mm * b%:~R * (mm * b%:~R - Phi_U (md * b%:~R) b%:~R t ^+ 2)).
    { move=> q Hq; apply: HT2'; by rewrite mem_undup. }
    have HT3 : forall q, prime q -> q \in rat_support md -> q \notin S_of mm ->
        t = 0 \/ 0 < vqr q (md * b%:~R * t ^+ 2).
    { move=> q _ H1 H2; apply: HT3'; by rewrite mem_filter H2 mem_undup H1. }
    (* Lemmas par:cross-squares and par:simultaneous-matrices *)
    have [ [ _ _ ] [ Hb8 _ ] [ Hb3 _ ] _ _ ] := cross_squares_nat Hb0 Hb'pos Hb'2 Hb'3 Hdpos HT1 HT2 HT3.
    have [ n [ Hn0 Hcop HBn _ Hl ] ] := simultaneous_matrices Hb0 Hb'pos Hb'2 Hb'3 Hdpos HT1 HT2 HT3.
    set b' := mm * b%:~R in Hb'pos HT1 Hb8 Hb3 Hl *.
    set H' := b' * (b' - Phi_U (md * b%:~R) b%:~R t ^+ 2) in HT1 Hl Hcop *.
    have [ s1 [ Hs1 Eb' ] ] := sqk_sq Hb'pos.
    have [ s2 [ Hs2 EH' ] ] := sqk_sq HT1.
    rewrite /sqk in Eb' EH'.
    have HBu : uniq (sqkB b') := sqkB_uniq _.
    have HBp : all prime (sqkB b') := sqkB_prime _.
    set theta := (\prod_(p <- sqkB H') p)%N in Hcop Hl EH' *.
    have Ht0 : (0 < theta)%N by rewrite prod_gt0 // sqkB_prime.
    (* Lemma par:global-point for l = n and l = n theta *)
    have Hsb' : sqc b' (\prod_(p <- sqkB b') p)%N%:Z by exists s1; split.
    have Hpt : forall l : nat, l = n \/ l = (n * theta)%N -> El_point (l%:R : rat) b'.
    { move=> l Hl'; have [ H4 H3 Hsq [ HsubB HexB ] [ Hker Hlam ] ] := Hl l Hl'.
      have Hl0 : (0 < l)%N by case: Hl' => ->; rewrite ?muln_gt0 ?Hn0 ?Ht0.
      have Hadm : admissible_l l%:Z.
      { split; first by rewrite ltz_nat.
        split; first exact: Hsq.
        by rewrite !modz_nat H4 H3. }
      have Hpt := HGP Hadm HBu HBp Hb8 Hb3 HsubB HexB Hker Hlam.
      exact: (sqc_El_point Hpt Hsb'). }
    have Hn : (n%:R : rat) != 0 by rewrite pnatr_eq0 -lt0n.
    have HH'0 : H' != 0 by rewrite gt_eqF.
    (* the twist E_{n theta} -> E_{n H'} (par:twist-scaling), e = n *)
    have Hpt2 : El_point (n%:R * H') b'.
    { have E : (n%:R * H' : rat) = ((n * theta)%N%:R) * s2 ^+ 2 by rewrite EH' natrM mulrA.
      rewrite E; apply: El_point_twist => //; apply: Hpt; by right. }
    exists mm, Dm, md, t, n%:R; split => //; split => //.
    rewrite /= !ratr_id; split; [ | split; [ | split ] ].
    - by rewrite gt_eqF // ltr_wpDr // mulr_ge0 // ?sqr_ge0 // ltW.
    - by rewrite mulf_neq0.
    - by apply: Hpt; left.
    - exact: Hpt2.
  Qed.

End Assembly.

(** * 16. The final theorem *)

Theorem PP1_paper_of_global_point : global_point_El -> PP1_paper.
Proof. move=> HGP L _ _ HM HD b; exact: (PP1_int HGP HM HD). Qed.

Corollary PP1_L0_of_global_point : global_point_El -> PP1_L0.
Proof. move=> H1; exact: PP1_paper_L0 (PP1_paper_of_global_point H1). Qed.
