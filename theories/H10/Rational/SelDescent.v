(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Lemma par:descent of the paper (03-parity.tex, Sec. 3.3) in the
   elementary Selmer language of TwoConverse.v (PLAN.md, Phase 3, task Q5;
   design PP1_DESIGN.md, Sec. 2.3).

   MAIN RESULT ([descent_main]). Let l be admissible ([admissible_l]: l > 0
   squarefree, l = 3 mod 4, l = 2 mod 3; hence prime to 6) and let beta
   (the positive squarefree integer of Lemma par:cross-squares, with support
   B) satisfy
     0 < beta,  beta | l,  beta <> l    (B inside Q = supp l, a prime of Q
                                          outside B),
     beta = 1 mod 8                     (beta is a 2-adic square),
     beta = 2 mod 3                     (beta is a 3-adic unit nonsquare;
                                          in particular B is nonempty),
   and the matrix condition (par:matrix-target)
     ker K = <1, 1_B>   as   [Kmx l *m oneB l beta = 0] and
                             [forall u, Kmx l *m u = 0 ->
                                u = 0 \/ u = 1 \/ u = 1_B \/ u = 1 + 1_B]
                             (K 1 = 0 always holds, [HK1_l]),
     lambda \notin im K  as  [forall u, Kmx l *m u != lamv l].
   Then
     in_Sel2 l (beta, 1)                                    [gamma_sel],
     forall d, in_Sel2 l d ->
        in_span3 (tors_Tl l) (tors_T3 l) (beta, 1) d        [upper_bound],
     ~ in_span2 (tors_Tl l) (tors_T3 l) (beta, 1)           [gamma_not_tors],
   i.e. exactly the premises of [TwoConverseSel2_El] with (g1, g2) =
   (beta, 1); [descent_El_point] chains this with [TwoConverse_El_point].

   THE MATRIX K, exactly as in the paper (eq. par:matrices). Q is the list
   [qs l = primes |l|] (increasing), indexed by i < [nq l] = |Q|, q_i =
   [qi i]. For an odd prime q and a q-adic unit a, [nbit a q] in F_2 is the
   nonsquare bit [a/q] (1 iff legendre a q = -1). Vectors are column
   vectors 'cV['F_2]_(nq l):
     (K u)_i = sum_(j <> i) [q_j/q_i] (u_j + u_i), i.e.
       K_ij = [q_j/q_i] (j <> i),  K_ii = sum_(j <> i) [q_j/q_i]   [Kmx],
     s_i = [-1/q_i] [sv],  lambda_i = [3/q_i] [lamv],
     (1_B)_i = 1 iff q_i | beta  [oneB].

   COORDINATES. TwoConverse.v uses the Kummer coordinates (x, x - l); the
   paper uses (x + 3l, x - l). Since x = (x + 3l)(x - l) mod squares, the
   paper's class (beta, 1) is (beta, 1) in both, tau_1 = (l, 1) is
   [tors_Tl], tau_2 = (3, -l) is (-3l, -l) = [tors_T3].

   ROUTE (no formal groups, no Q_p, no Hasse bound).
   A. Necessary local conditions, from primitive solutions of C_d modulo
      p^k (k = v_p(d1) + v_p(d2) + 4), by a case analysis on the valuations
      of Y1 = d1 z1^2, Y2 = d2 z2^2, Y3 = d1 d2 z3^2, W = z0^2
      (Y1 - Y2 = l W + p^k(..), Y1 - Y3 = -3l W + p^k(..), Y1 Y2 Y3 a
      square), replacing the paper's "local image of order four":
      - good odd p (p not dividing 6l): v_p(d1), v_p(d2) even [good_even];
      - p = 2: v_2(d1), v_2(d2) even [two_even] (the configuration
        v(Y1) = v(W), v(Y2) = v(Y3) = v(W) + 1 contradicts l = 3 mod 4 by
        the paper's mod-8 computation, [two_core]);
      - p = 3: d2 is a 3-adic square [three_sq];
      - q | l: the class of d at q is one of the four torsion classes
        [l_tors]; at infinity d1 d2 > 0 [inf_pos].
   B/C. With u, v, delta, sigma the parities of v_q(d1), v_q(d2) (q in Q),
      v_3(d1) and the sign, d ~ (sigma 3^delta prod_u q, sigma prod_v q);
      the local conditions give the F_2 equations (par:selmer-matrix-
      equations, par:selmer-three-equation) [row_eqs], [S3_eq]; quadratic
      reciprocity gives K + K^T = s s^T + D_s [HQR_l], s^T 1 = 1 [Hs1_l],
      lambda^T 1 = 0 [Hl1_l]; the kernel argument (ker K^T has dimension 2,
      im K = (ker K^T)^perp via ranks, [key]) gives v = sigma 1,
      delta = sigma, K u = 0 [linalg], [sel_classes]; Hker then leaves the
      eight classes [upper_bound].
   D. gamma is not a torsion class: second coordinate sign, and the
      valuations at a prime of B, resp. of Q outside B [gamma_not_tors].
   E-H. gamma in Sel2. At infinity, 2 (beta = 1 mod 8), 3 (beta = l mod 3)
      and q | l (the rows of K 1_B = 0) gamma is locally a torsion class:
      exact solutions of the torsion coverings transported by p-adic square
      roots of unit quotients (Hensel.v) [locsol_transfer], [gamma_two],
      [gamma_three], [gamma_q]. At primes of good reduction: E(F_p) is a
      finite abelian group ([EPT3], GroupLaw.v), its Kummer map is a
      homomorphism [kv_hom], [lb_hom] with kernel 2E(F_p) (halving formula
      [half_xy], [halve]), and |E/2E| = |E[2]| = 4 by counting fibres
      [card_fib], [card_G2], so it is onto [kap_surj]; an F_p-point of class
      (beta, 1) lifts by Hensel ([cov_lift_odd], [locsol_of_mod]) or, if it
      is 2-torsion, gives a transported torsion solution [gamma_good].

   No axioms: [Print Assumptions descent_main] is closed. *)

From Stdlib Require Import ZArith Lia.
From HB Require Import structures.
From Undecidability.H10.Rational
  Require Import RatUtil PosExistential FixedData ExplicitData PaperInputs PhiCovering RatVal OrdinaryFacts
                 Hensel QuadRec TwoConverse GroupLaw.
From mathcomp Require Import boot order algebra finite_group.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

(** * Part A. Local necessary conditions: valuations of a primitive solution *)
Ltac nlia := repeat match goal with
  | H : is_true (leq _ _) |- _ => move/ssrnat.leP: H => H
  | H : is_true (~~ leq _ _) |- _ => rewrite -ltnNge in H
  | |- is_true (leq _ _) => apply/ssrnat.leP
  | H : is_true (_ || _) |- _ => case/orP: H => H
  | H : is_true (_ && _) |- _ => case/andP: H => H
  end;
  change addn with Nat.add in *; change muln with Nat.mul in *; change subn with Nat.sub in *;
  lia.

Lemma evenE (n : nat) : ~~ odd n -> exists h, n = (h + h)%N.
Proof. move=> H; exists n./2; by rewrite -{1}(odd_double_half n) (negbTE H) add0n -addnn. Qed.

Lemma oddE (n : nat) : odd n -> exists h, n = (h + h + 1)%N.
Proof. move=> H; exists n./2; by rewrite -{1}(odd_double_half n) H -addnn addnC. Qed.

Lemma evenI (n h : nat) : n = (h + h)%N -> ~~ odd n.
Proof. by move=> ->; rewrite addnn odd_double. Qed.

(** * 1. Valuations of integers *)

Definition vz (p : nat) (a : int) : nat := logn p `|a|.

Definition vge (p k : nat) (e : int) : Prop := e = 0 \/ (k <= vz p e)%N.

Section vz.

  Variable p : nat.
  Hypothesis pP : prime p.

  Lemma vz_rat (a : int) : vqr p a%:~R = (vz p a)%:Z.
  Proof. exact: vqr_int. Qed.

  Lemma vzM (a b : int) : a != 0 -> b != 0 -> vz p (a * b) = (vz p a + vz p b)%N.
  Proof. by move=> Ha Hb; rewrite /vz abszM lognM ?absz_gt0. Qed.

  Lemma vzN (a : int) : vz p (- a) = vz p a.
  Proof. by rewrite /vz abszN. Qed.

  Lemma vz_ndvd (a : int) : ~~ (p%:Z %| a)%Z -> vz p a = 0%N.
  Proof. by move=> H; rewrite /vz logn_ndvd //; move: H; rewrite dvdzE. Qed.

  Lemma vz_nat (n : nat) : vz p n%:Z = logn p n.
  Proof. by []. Qed.

  Lemma vz_sq (a : int) : a != 0 -> vz p (a ^+ 2) = (vz p a + vz p a)%N.
  Proof. by move=> Ha; rewrite expr2 vzM. Qed.

  Lemma vz_dvd (k : nat) (a : int) : a != 0 -> ((p ^ k)%:Z %| a)%Z = (k <= vz p a)%N.
  Proof. by move=> Ha; rewrite dvdzE absz_nat /vz pfactor_dvdn ?absz_gt0. Qed.

  Lemma vge_dvd (k : nat) (e : int) : ((p ^ k)%:Z %| e)%Z -> vge p k e.
  Proof.
    move=> H; case: (eqVneq e 0) => [ -> | He ]; [ by left | right ].
    by rewrite -vz_dvd.
  Qed.

  Lemma vge0 k : vge p k 0.
  Proof. by left. Qed.

  Lemma vgeN k e : vge p k e -> vge p k (- e).
  Proof. by case=> [ -> | H ]; [ left; rewrite oppr0 | right; rewrite vzN ]. Qed.

  Lemma vge_le j k e : (j <= k)%N -> vge p k e -> vge p j e.
  Proof. by move=> Hjk [ -> | H ]; [ left | right; exact: leq_trans H ]. Qed.

  Lemma vge_self e : vge p (vz p e) e.
  Proof. by right. Qed.

  Lemma vz_add_lt (a b : int) : a != 0 -> b != 0 -> (vz p a < vz p b)%N ->
    a + b != 0 /\ vz p (a + b) = vz p a.
  Proof.
    move=> Ha Hb Hlt.
    have Ha' : (a%:~R : rat) != 0 by rewrite intr_eq0.
    have Hb' : (b%:~R : rat) != 0 by rewrite intr_eq0.
    have := @vqr_add_lt p pP _ _ Ha' Hb'; rewrite !vz_rat ltz_nat => /(_ Hlt) [].
    rewrite -intrD intr_eq0 vz_rat => -> [] ->; done.
  Qed.

  Lemma vz_add_ge (a b : int) (k : nat) : a + b != 0 -> vge p k a -> vge p k b -> (k <= vz p (a + b))%N.
  Proof.
    move=> Hab Ha Hb.
    case: (eqVneq a 0) => [ Ea | Ha0 ].
    { move: Hab; rewrite Ea add0r => Hab; case: Hb => [ Eb | // ]; by move: Hab; rewrite Eb eqxx. }
    case: (eqVneq b 0) => [ Eb | Hb0 ].
    { move: Hab; rewrite Eb addr0 => Hab; case: Ha => [ Ea | // ]; by move: Ha0; rewrite Ea eqxx. }
    case: Ha => [ Ea | Ha ]; first by move: Ha0; rewrite Ea eqxx.
    case: Hb => [ Eb | Hb ]; first by move: Hb0; rewrite Eb eqxx.
    have Ha' : (a%:~R : rat) != 0 by rewrite intr_eq0.
    have Hb' : (b%:~R : rat) != 0 by rewrite intr_eq0.
    have Hab' : (a%:~R + b%:~R : rat) != 0 by rewrite -intrD intr_eq0.
    have := @vqr_add_ge p pP _ _ k%:Z Ha' Hb' Hab'; rewrite !vz_rat !lez_nat -intrD vz_rat lez_nat.
    by apply.
  Qed.

  Lemma vgeD k e f : vge p k e -> vge p k f -> vge p k (e + f).
  Proof.
    move=> He Hf; case: (eqVneq (e + f) 0) => [ -> | H ]; first by left.
    by right; apply: vz_add_ge.
  Qed.

  Lemma vgeB k e f : vge p k e -> vge p k f -> vge p k (e - f).
  Proof. by move=> He Hf; apply: vgeD => //; apply: vgeN. Qed.

  Lemma vgeMr k e c : vge p k e -> vge p k (e * c).
  Proof.
    move=> [ -> | H ]; first by left; rewrite mul0r.
    case: (eqVneq c 0) => [ -> | Hc ]; first by left; rewrite mulr0.
    case: (eqVneq e 0) => [ -> | He ]; first by left; rewrite mul0r.
    by right; rewrite vzM // (leq_trans H) ?leq_addr.
  Qed.

  Lemma vz_small (a e : int) (k : nat) : a != 0 -> vge p k e -> (vz p a < k)%N ->
    a + e != 0 /\ vz p (a + e) = vz p a.
  Proof.
    move=> Ha [ -> | He ] Hk; first by rewrite addr0.
    have He0 : e != 0 by apply/eqP => E; move: He; rewrite E /vz /= logn0 leqn0 => /eqP E'; move: Hk; rewrite E' ltn0.
    apply: vz_add_lt => //; exact: leq_trans Hk He.
  Qed.

  (* Z = X + c + e with v(X) < v(c), v(X) < k *)
  Lemma vprop (X c e : int) (k : nat) : X != 0 -> c != 0 -> vge p k e ->
    (vz p X < vz p c)%N -> (vz p X < k)%N -> X + c + e != 0 /\ vz p (X + c + e) = vz p X.
  Proof.
    move=> HX Hc He H1 H2; rewrite -addrA.
    case: (eqVneq (c + e) 0) => [ -> | Hf ]; first by rewrite addr0.
    apply: vz_add_lt => //.
    have := @vz_add_ge c e (minn (vz p c) k) Hf.
    have Hc' : vge p (minn (vz p c) k) c by apply: vge_le (vge_self c); rewrite geq_minl.
    have He' : vge p (minn (vz p c) k) e by apply: vge_le He; rewrite geq_minr.
    move=> /(_ Hc' He'); apply: leq_trans; by rewrite leq_min H1 H2.
  Qed.

  (* X - Z = c + e with v(c) < k: one of X, Z has valuation <= v(c) *)
  Lemma vpair (X Z c e : int) (k : nat) : X != 0 -> Z != 0 -> c != 0 -> vge p k e ->
    (vz p c < k)%N -> X - Z = c + e -> (vz p X <= vz p c)%N || (vz p Z <= vz p c)%N.
  Proof.
    move=> HX HZ Hc He Hck E.
    apply/negPn/negP; rewrite negb_or -!ltnNge => /andP [ H1 H2 ].
    have [ Hf Hv ] := vz_small Hc He Hck.
    have HXZ : X + - Z != 0 by rewrite E.
    have HX' : vge p (vz p c).+1 X by right.
    have HZ' : vge p (vz p c).+1 (- Z) by right; rewrite vzN.
    have := @vz_add_ge X (- Z) (vz p c).+1 HXZ HX' HZ'.
    by rewrite E Hv ltnn.
  Qed.

  (* closeness: a = b + f with f = 0 or v(f) > v(b) gives a / b in Q_p^x2 (p odd) *)
  Lemma lsq_close (a b f : int) : p != 2%N -> a != 0 -> b != 0 -> a = b + f ->
    vge p (vz p b).+1 f -> locsq p (a%:~R / b%:~R).
  Proof.
    move=> Hp2 Ha Hb E Hf.
    have Hb' : (b%:~R : rat) != 0 by rewrite intr_eq0.
    have Ha' : (a%:~R : rat) != 0 by rewrite intr_eq0.
    apply: (@locsq_close p pP 1); first by have := @locsq_sq p pP 1 (oner_neq0 _); rewrite expr1n.
    - by rewrite mulf_neq0 ?invr_eq0.
    case: Hf => [ Hf | Hf ]; first by left; rewrite E Hf addr0 divff.
    right.
    have Hf0 : f != 0 by apply/eqP => E'; move: Hf; rewrite E' /vz /= logn0.
    have -> : a%:~R / b%:~R - 1 = f%:~R / b%:~R :> rat.
    { by rewrite E intrD mulrDl divff // addrC addKr. }
    rewrite vqr_div ?intr_eq0 // !vz_rat vqr1 /cq (negbTE Hp2) add0r.
    by rewrite lerBrDr -PoszD lez_nat add1n.
  Qed.

End vz.

Section close.

  Variable p : nat.
  Hypothesis pP : prime p.
  Hypothesis p2 : p != 2%N.

  (* X = c + (Y + e), v(c) < v(Y), v(c) < k: X / c is a local square *)
  Lemma close_t (X c Y e : int) (k : nat) : X != 0 -> c != 0 -> Y != 0 -> vge p k e ->
    (vz p c < vz p Y)%N -> (vz p c < k)%N -> X = c + (Y + e) -> locsq p (X%:~R / c%:~R).
  Proof.
    move=> HX Hc HY He H1 H2 E; apply: (lsq_close pP p2 HX Hc E).
    apply: (vgeD pP); first by right.
    exact: vge_le He.
  Qed.

  (* Z = X + (c + e), v(X) < v(c), v(X) < k: Z / X is a local square *)
  Lemma close_r (Z X c e : int) (k : nat) : Z != 0 -> X != 0 -> c != 0 -> vge p k e ->
    (vz p X < vz p c)%N -> (vz p X < k)%N -> Z = X + (c + e) -> locsq p (Z%:~R / X%:~R).
  Proof.
    move=> HZ HX Hc He H1 H2 E; apply: (lsq_close pP p2 HZ HX E).
    apply: (vgeD pP); first by right.
    exact: vge_le He.
  Qed.

End close.

(** * 2. The local analysis of a primitive solution of C_d modulo p^k

    Y1 = d1 z1^2, Y2 = d2 z2^2, Y3 = d1 d2 z3^2, W = z0^2 (all nonzero):
    Y1 - Y2 = l W + E1, Y1 - Y3 = -3 l W + E2 with E1, E2 divisible by
    p^k, Y1 Y2 Y3 a square, and one of the four valuations at most M. *)

Section Local.

  Variables (p : nat) (l Y1 Y2 Y3 W : int) (k M : nat).
  Hypothesis pP : prime p.
  Hypotheses (Y1n : Y1 != 0) (Y2n : Y2 != 0) (Y3n : Y3 != 0) (Wn : W != 0) (ln : l != 0).
  Hypothesis HE1 : vge p k (Y1 - Y2 - l * W).
  Hypothesis HE2 : vge p k (Y1 - Y3 + 3 * l * W).
  Hypothesis Hprod : exists s : int, Y1 * Y2 * Y3 = s ^+ 2.
  Hypothesis HWsq : exists z : int, W = z ^+ 2.
  Hypothesis Hmin : [|| vz p Y1 <= M, vz p Y2 <= M, vz p Y3 <= M | vz p W <= M]%N.
  Hypothesis Hk : (M + 3 < k)%N.

  Local Abbreviation E1 := (Y1 - Y2 - l * W).
  Local Abbreviation E2 := (Y1 - Y3 + 3 * l * W).
  Local Abbreviation c12 := (l * W).
  Local Abbreviation c13 := (3 * l * W).
  Local Abbreviation c23 := (4 * l * W).

  Let c12n : c12 != 0. Proof. by rewrite mulf_neq0. Qed.
  Let c13n : c13 != 0. Proof. by rewrite !mulf_neq0. Qed.
  Let c23n : c23 != 0. Proof. by rewrite !mulf_neq0. Qed.
  Let HE3 : vge p k (E2 - E1). Proof. exact: vgeB. Qed.

  Let R12 : Y2 = Y1 + (- c12) + (- E1). Proof. ring. Qed.
  Let R21 : Y1 = Y2 + c12 + E1. Proof. ring. Qed.
  Let R13 : Y3 = Y1 + c13 + (- E2). Proof. ring. Qed.
  Let R31 : Y1 = Y3 + (- c13) + E2. Proof. ring. Qed.
  Let R23 : Y3 = Y2 + c23 + (E1 - E2). Proof. ring. Qed.
  Let R32 : Y2 = Y3 + (- c23) + (E2 - E1). Proof. ring. Qed.

  Local Abbreviation a1 := (vz p Y1).
  Local Abbreviation a2 := (vz p Y2).
  Local Abbreviation a3 := (vz p Y3).
  Local Abbreviation w := (vz p W).
  Local Abbreviation v12 := (vz p c12).
  Local Abbreviation v13 := (vz p c13).
  Local Abbreviation v23 := (vz p c23).

  Ltac prop_tac R := move=> H1 H2; rewrite [in LHS]R; apply: (vprop pP) => //; rewrite ?oppr_eq0 ?vzN //;
    by apply: vgeN || apply: vgeB || done.

  Lemma P12 : (a1 < v12)%N -> (a1 < k)%N -> a2 = a1.
  Proof.
    move=> H1 H2; have [ _ E ] := vprop pP Y1n (c := - c12) (e := - E1) (k := k) ltac:(by rewrite oppr_eq0)
      (vgeN HE1) ltac:(by rewrite vzN) H2.
    by rewrite -E -R12.
  Qed.

  Lemma P21 : (a2 < v12)%N -> (a2 < k)%N -> a1 = a2.
  Proof.
    move=> H1 H2; have [ _ E ] := vprop pP Y2n (c := c12) (e := E1) (k := k) c12n HE1 H1 H2.
    by rewrite -E -R21.
  Qed.

  Lemma P13 : (a1 < v13)%N -> (a1 < k)%N -> a3 = a1.
  Proof.
    move=> H1 H2; have [ _ E ] := vprop pP Y1n (c := c13) (e := - E2) (k := k) c13n (vgeN HE2) H1 H2.
    by rewrite -E -R13.
  Qed.

  Lemma P31 : (a3 < v13)%N -> (a3 < k)%N -> a1 = a3.
  Proof.
    move=> H1 H2; have [ _ E ] := vprop pP Y3n (c := - c13) (e := E2) (k := k) ltac:(by rewrite oppr_eq0)
      HE2 ltac:(by rewrite vzN) H2.
    by rewrite -E -R31.
  Qed.

  Lemma P23 : (a2 < v23)%N -> (a2 < k)%N -> a3 = a2.
  Proof.
    move=> H1 H2; have [ _ E ] := vprop pP Y2n (c := c23) (e := E1 - E2) (k := k) c23n
      (vgeB pP HE1 HE2) H1 H2.
    by rewrite -E -R23.
  Qed.

  Lemma P32 : (a3 < v23)%N -> (a3 < k)%N -> a2 = a3.
  Proof.
    move=> H1 H2; have [ _ E ] := vprop pP Y3n (c := - c23) (e := E2 - E1) (k := k) ltac:(by rewrite oppr_eq0)
      HE3 ltac:(by rewrite vzN) H2.
    by rewrite -E -R32.
  Qed.

  Lemma D12 : (v12 < k)%N -> (a1 <= v12)%N \/ (a2 <= v12)%N.
  Proof.
    move=> Hv; have E : Y1 - Y2 = c12 + E1 by ring.
    by have /orP := vpair pP Y1n Y2n c12n HE1 Hv E.
  Qed.

  Lemma D13 : (v13 < k)%N -> (a1 <= v13)%N \/ (a3 <= v13)%N.
  Proof.
    move=> Hv; have E : Y1 - Y3 = - c13 + E2 by ring.
    have Hc : - c13 != 0 by rewrite oppr_eq0.
    have Hv' : (vz p (- c13) < k)%N by rewrite vzN.
    by have /orP := vpair pP Y1n Y3n Hc HE2 Hv' E; rewrite vzN.
  Qed.

  Lemma D23 : (v23 < k)%N -> (a2 <= v23)%N \/ (a3 <= v23)%N.
  Proof.
    move=> Hv; have E : Y2 - Y3 = - c23 + (E2 - E1) by ring.
    have Hc : - c23 != 0 by rewrite oppr_eq0.
    have Hv' : (vz p (- c23) < k)%N by rewrite vzN.
    by have /orP := vpair pP Y2n Y3n Hc HE3 Hv' E; rewrite vzN.
  Qed.

  Lemma Hmin' : (a1 <= M \/ a2 <= M \/ a3 <= M \/ w <= M)%N.
  Proof. by move: Hmin => /or4P [] H; [ left | right; left | right; right; left | right; right; right ]. Qed.

  Lemma Hsq' : exists s, (a1 + a2 + a3 = s + s)%N.
  Proof.
    have [ s Hs ] := Hprod; exists (vz p s).
    have Hs0 : s != 0 by apply/eqP => E; move: Hs; rewrite E expr0n /= => /eqP; rewrite !mulf_eq0 (negbTE Y1n) (negbTE Y2n) (negbTE Y3n).
    by rewrite -!vzM ?mulf_neq0 // Hs vz_sq.
  Qed.

  Lemma HW' : exists s, (w = s + s)%N.
  Proof.
    have [ z Hz ] := HWsq; exists (vz p z).
    have Hz0 : z != 0 by apply/eqP => E; move: Wn; rewrite Hz E expr0n.
    by rewrite Hz vz_sq.
  Qed.

  (* Prop forms for lia *)
  Lemma p12 : (a1 < v12)%coq_nat -> (a1 < k)%coq_nat -> a2 = a1.
  Proof. by move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: P12. Qed.
  Lemma p21 : (a2 < v12)%coq_nat -> (a2 < k)%coq_nat -> a1 = a2.
  Proof. by move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: P21. Qed.
  Lemma p13 : (a1 < v13)%coq_nat -> (a1 < k)%coq_nat -> a3 = a1.
  Proof. by move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: P13. Qed.
  Lemma p31 : (a3 < v13)%coq_nat -> (a3 < k)%coq_nat -> a1 = a3.
  Proof. by move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: P31. Qed.
  Lemma p23 : (a2 < v23)%coq_nat -> (a2 < k)%coq_nat -> a3 = a2.
  Proof. by move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: P23. Qed.
  Lemma p32 : (a3 < v23)%coq_nat -> (a3 < k)%coq_nat -> a2 = a3.
  Proof. by move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: P32. Qed.
  Lemma d12 : (v12 < k)%coq_nat -> (a1 <= v12)%coq_nat \/ (a2 <= v12)%coq_nat.
  Proof. by move=> /ssrnat.ltP H; case: (D12 H) => /ssrnat.leP; tauto. Qed.
  Lemma d13 : (v13 < k)%coq_nat -> (a1 <= v13)%coq_nat \/ (a3 <= v13)%coq_nat.
  Proof. by move=> /ssrnat.ltP H; case: (D13 H) => /ssrnat.leP; tauto. Qed.
  Lemma d23 : (v23 < k)%coq_nat -> (a2 <= v23)%coq_nat \/ (a3 <= v23)%coq_nat.
  Proof. by move=> /ssrnat.ltP H; case: (D23 H) => /ssrnat.leP; tauto. Qed.
  Lemma hmin : (a1 <= M \/ a2 <= M \/ a3 <= M \/ w <= M)%coq_nat.
  Proof. by case: Hmin' => [ /ssrnat.leP | [ /ssrnat.leP | [ /ssrnat.leP | /ssrnat.leP ] ] ]; tauto. Qed.
  Lemma hk : (M + 3 < k)%coq_nat.
  Proof. by apply/ssrnat.ltP. Qed.

  Lemma vW (n : nat) (c : int) : c != 0 -> vz p c = n -> vz p (c * W) = (n + w)%N.
  Proof. by move=> Hc Hn; rewrite vzM // Hn. Qed.

  Lemma split_min :
    (a1 < w /\ a1 <= a2 /\ a1 <= a3 /\ a1 + 3 < k)%coq_nat \/
    (a2 < w /\ a2 <= a1 /\ a2 <= a3 /\ a2 + 3 < k)%coq_nat \/
    (a3 < w /\ a3 <= a1 /\ a3 <= a2 /\ a3 + 3 < k)%coq_nat \/
    (w <= a1 /\ w <= a2 /\ w <= a3 /\ w + 3 < k)%coq_nat.
  Proof. have := hmin; have := hk; nlia. Qed.

  (** good odd primes: both valuations even *)
  Lemma loc_good : vz p l = 0%N -> vz p 3 = 0%N -> vz p 4 = 0%N -> ~~ odd a1 /\ ~~ odd a2.
  Proof.
    move=> Hl H3 H4.
    have V12 : v12 = w by rewrite (vW ln Hl).
    have V13 : v13 = w by rewrite (@vW 0 (3 * l)) ?mulf_neq0 // vzM // H3 Hl.
    have V23 : v23 = w by rewrite (@vW 0 (4 * l)) ?mulf_neq0 // vzM // H4 Hl.
    have [ s Hs ] := Hsq'; have [ s0 Hs0 ] := HW'.
    suff : (a1 = a2 /\ a2 = a3) \/ (a1 = w /\ a2 = w) \/ (a1 = w /\ a3 = w) \/ (a2 = w /\ a3 = w).
    { by move=> H; split; apply/negP => /oddE [ h Hh ]; nlia. }
    case: split_min => [ [ H1 [ H2 [ H3' H4' ] ] ] | [ [ H1 [ H2 [ H3' H4' ] ] ] |
                         [ [ H1 [ H2 [ H3' H4' ] ] ] | [ H1 [ H2 [ H3' H4' ] ] ] ] ] ].
    - have := p12; have := p13; rewrite V12 V13 => A B.
      left; have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia); nlia.
    - have := p21; have := p23; rewrite V12 V23 => A B.
      left; have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia); nlia.
    - have := p31; have := p32; rewrite V13 V23 => A B.
      left; have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia); nlia.
    - have := d12; have := d13; have := d23; rewrite V12 V13 V23 => A B C.
      have := A ltac:(nlia); have := B ltac:(nlia); have := C ltac:(nlia); nlia.
  Qed.

  (** threshold split: the minimal valuation is below c, or all are >= c *)
  Lemma split_c (c : nat) : (w <= c)%coq_nat -> (c <= w + 1)%coq_nat ->
    (a1 < c /\ a1 <= a2 /\ a1 <= a3 /\ a1 + 3 < k)%coq_nat \/
    (a2 < c /\ a2 <= a1 /\ a2 <= a3 /\ a2 + 3 < k)%coq_nat \/
    (a3 < c /\ a3 <= a1 /\ a3 <= a2 /\ a3 + 3 < k)%coq_nat \/
    (c <= a1 /\ c <= a2 /\ c <= a3 /\ w + 3 < k)%coq_nat.
  Proof. move=> Hc Hc'; have := hmin; have := hk; nlia. Qed.

  (** the rational side *)
  Local Abbreviation y1 := (Y1%:~R : rat).
  Local Abbreviation y2 := (Y2%:~R : rat).
  Local Abbreviation y3 := (Y3%:~R : rat).
  Local Abbreviation lr := (l%:~R : rat).
  Local Abbreviation wr := (W%:~R : rat).

  Let y1n : y1 != 0. Proof. by rewrite intr_eq0. Qed.
  Let y2n : y2 != 0. Proof. by rewrite intr_eq0. Qed.
  Let y3n : y3 != 0. Proof. by rewrite intr_eq0. Qed.
  Let lrn : lr != 0. Proof. by rewrite intr_eq0. Qed.
  Let wrn : wr != 0. Proof. by rewrite intr_eq0. Qed.

  Lemma Pq : locsq p (y1 * y2 * y3).
  Proof.
    have [ s Hs ] := Hprod.
    have Hs0 : (s%:~R : rat) != 0.
    { rewrite intr_eq0; apply/eqP => E; move: Hs; rewrite E expr0n /= => /eqP.
      by rewrite !mulf_eq0 (negbTE Y1n) (negbTE Y2n) (negbTE Y3n). }
    have -> : y1 * y2 * y3 = (s%:~R) ^+ 2 by rewrite -!intrM Hs rmorphXn.
    exact: locsq_sq.
  Qed.

  Lemma Wq : locsq p wr.
  Proof.
    have [ z Hz ] := HWsq.
    have Hz0 : (z%:~R : rat) != 0 by rewrite intr_eq0; apply/eqP => E; move: Wn; rewrite Hz E expr0n.
    by rewrite Hz rmorphXn; apply: locsq_sq.
  Qed.

  Lemma sqq (x : rat) : x != 0 -> locsq p (x ^+ 2).
  Proof. exact: locsq_sq. Qed.

  Section odd.

    Hypothesis p2 : p != 2%N.

    Lemma C12 : (a1 < v12)%coq_nat -> (a1 < k)%coq_nat -> locsq p (y2 / y1).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: (close_r pP p2 (k := k) (c := - c12) (e := - E1)) => //.
      - by rewrite oppr_eq0.
      - exact: vgeN.
      - by rewrite vzN.
      - ring.
    Qed.

    Lemma C21 : (a2 < v12)%coq_nat -> (a2 < k)%coq_nat -> locsq p (y1 / y2).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: (close_r pP p2 (k := k) (c := c12) (e := E1)) => //.
      ring.
    Qed.

    Lemma C13 : (a1 < v13)%coq_nat -> (a1 < k)%coq_nat -> locsq p (y3 / y1).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: (close_r pP p2 (k := k) (c := c13) (e := - E2)) => //.
      - exact: vgeN.
      - ring.
    Qed.

    Lemma C31 : (a3 < v13)%coq_nat -> (a3 < k)%coq_nat -> locsq p (y1 / y3).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: (close_r pP p2 (k := k) (c := - c13) (e := E2)) => //.
      - by rewrite oppr_eq0.
      - by rewrite vzN.
      - ring.
    Qed.

    Lemma C23 : (a2 < v23)%coq_nat -> (a2 < k)%coq_nat -> locsq p (y3 / y2).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: (close_r pP p2 (k := k) (c := c23) (e := E1 - E2)) => //.
      - exact: vgeB.
      - ring.
    Qed.

    Lemma C32 : (a3 < v23)%coq_nat -> (a3 < k)%coq_nat -> locsq p (y2 / y3).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2; apply: (close_r pP p2 (k := k) (c := - c23) (e := E2 - E1)) => //.
      - by rewrite oppr_eq0.
      - by rewrite vzN.
      - ring.
    Qed.

    Lemma T21 : (v12 < a2)%coq_nat -> (v12 < k)%coq_nat -> locsq p (y1 / (lr * wr)).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2; rewrite -intrM.
      apply: (close_t pP p2 (k := k) (Y := Y2) (e := E1)) => //.
      ring.
    Qed.

    Lemma T12 : (v12 < a1)%coq_nat -> (v12 < k)%coq_nat -> locsq p (y2 / (- (lr * wr))).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2; rewrite -intrM -intrN.
      apply: (close_t pP p2 (k := k) (Y := Y1) (e := - E1)) => //.
      - by rewrite oppr_eq0.
      - exact: vgeN.
      - by rewrite vzN.
      - by rewrite vzN.
      - ring.
    Qed.

    Lemma T31 : (v13 < a3)%coq_nat -> (v13 < k)%coq_nat -> locsq p (y1 / (- (3 * lr * wr))).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2.
      rewrite (_ : 3 * lr * wr = (3 * l * W)%:~R); first by rewrite !intrM rmorphMn rmorph1.
      rewrite -intrN; apply: (close_t pP p2 (k := k) (Y := Y3) (e := E2)) => //.
      - by rewrite oppr_eq0.
      - by rewrite vzN.
      - by rewrite vzN.
      - ring.
    Qed.

    Lemma T13 : (v13 < a1)%coq_nat -> (v13 < k)%coq_nat -> locsq p (y3 / (3 * lr * wr)).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2.
      rewrite (_ : 3 * lr * wr = (3 * l * W)%:~R); first by rewrite !intrM rmorphMn rmorph1.
      apply: (close_t pP p2 (k := k) (Y := Y1) (e := - E2)) => //.
      - exact: vgeN.
      - ring.
    Qed.

    Lemma T32 : (v23 < a3)%coq_nat -> (v23 < k)%coq_nat -> locsq p (y2 / (- (4 * lr * wr))).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2.
      rewrite (_ : 4 * lr * wr = (4 * l * W)%:~R); first by rewrite !intrM rmorphMn rmorph1.
      rewrite -intrN; apply: (close_t pP p2 (k := k) (Y := Y3) (e := E2 - E1)) => //.
      - by rewrite oppr_eq0.
      - by rewrite vzN.
      - by rewrite vzN.
      - ring.
    Qed.

    Lemma T23 : (v23 < a2)%coq_nat -> (v23 < k)%coq_nat -> locsq p (y3 / (4 * lr * wr)).
    Proof.
      move=> /ssrnat.ltP H1 /ssrnat.ltP H2.
      rewrite (_ : 4 * lr * wr = (4 * l * W)%:~R); first by rewrite !intrM rmorphMn rmorph1.
      apply: (close_t pP p2 (k := k) (Y := Y2) (e := E1 - E2)) => //.
      - exact: vgeB.
      - ring.
    Qed.

  End odd.

  Ltac lsq_tac := repeat first [ exact: Pq | exact: Wq | eassumption
    | (apply: sqq; by rewrite ?mulf_neq0 ?oppr_eq0)
    | apply: (locsq_inv pP) | apply: (locsq_mul pP) | apply: (locsq_div pP) ].

  (** the support primes q | l: the class of (Y1, Y2) is one of the
      four classes of the 2-torsion points *)
  Lemma loc_l : p != 2%N -> vz p 3 = 0%N -> vz p 4 = 0%N -> vz p l = 1%N ->
    (locsq p y1 /\ locsq p y2) \/
    (locsq p (y1 / lr) /\ locsq p y2) \/
    (locsq p (y1 / (- (3 * lr))) /\ locsq p (y2 / (- lr))) \/
    (locsq p (y1 / (- 3)) /\ locsq p (y2 / (- lr))).
  Proof.
    move=> p2 H3 H4 Hl.
    have V12 : v12 = (1 + w)%N by rewrite (vW ln Hl).
    have V13 : v13 = (1 + w)%N by rewrite (@vW 1 (3 * l)) ?mulf_neq0 // vzM // H3 Hl.
    have V23 : v23 = (1 + w)%N by rewrite (@vW 1 (4 * l)) ?mulf_neq0 // vzM // H4 Hl.
    have [ s Hs ] := Hsq'; have [ s0 Hs0 ] := HW'.
    have H3r : (3 : rat) != 0 by [].
    have H4r : (4 : rat) != 0 by [].
    have H2r : (2 : rat) != 0 by [].
    have := @split_c (w + 1) ltac:(nlia) ltac:(nlia).
    case=> [ [ H1 [ H2 [ H3' H4' ] ] ] | [ [ H1 [ H2 [ H3' H4' ] ] ] |
             [ [ H1 [ H2 [ H3' H4' ] ] ] | [ H1 [ H2 [ H3' H4' ] ] ] ] ] ].
    - have := C12 p2; have := C13 p2; rewrite V12 V13 => A B.
      have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia) => Hb Ha.
      have Hy1 : locsq p y1.
      { have -> : y1 = (y1 * y2 * y3) / ((y2 / y1) * (y3 / y1) * y1 ^+ 2) by field.
        lsq_tac. }
      left; split => //; have -> : y2 = (y2 / y1) * y1 by field.
      lsq_tac.
    - have := C21 p2; have := C23 p2; rewrite V12 V23 => A B.
      have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia) => Hb Ha.
      have Hy2 : locsq p y2.
      { have -> : y2 = (y1 * y2 * y3) / ((y1 / y2) * (y3 / y2) * y2 ^+ 2) by field.
        lsq_tac. }
      left; split => //; have -> : y1 = (y1 / y2) * y2 by field.
      lsq_tac.
    - have := C31 p2; have := C32 p2; rewrite V13 V23 => A B.
      have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia) => Hb Ha.
      have Hy3 : locsq p y3.
      { have -> : y3 = (y1 * y2 * y3) / ((y1 / y3) * (y2 / y3) * y3 ^+ 2) by field.
        lsq_tac. }
      left; split.
      + have -> : y1 = (y1 / y3) * y3 by field. lsq_tac.
      + have -> : y2 = (y2 / y3) * y3 by field. lsq_tac.
    - have := d12; have := d13; have := d23; rewrite V12 V13 V23 => A B C.
      have := A ltac:(nlia); have := B ltac:(nlia); have := C ltac:(nlia) => Hc Hb Ha.
      have : (1 + w < a3 \/ 1 + w < a2 \/ 1 + w < a1)%coq_nat by nlia.
      case=> [ Ha3 | [ Ha2 | Ha1 ] ].
      + have := T31 p2; have := T32 p2; rewrite V13 V23 => A' B'.
        have := A' ltac:(nlia) ltac:(nlia); have := B' ltac:(nlia) ltac:(nlia) => Hy2 Hy1.
        right; right; left; split.
        * have -> : y1 / (- (3 * lr)) = (y1 / (- (3 * lr * wr))) * wr by field.
          lsq_tac.
        * have -> : y2 / (- lr) = (y2 / (- (4 * lr * wr))) * (wr * 2 ^+ 2) by field.
          lsq_tac.
      + have := T21 p2; have := T23 p2; rewrite V12 V23 => A' B'.
        have := A' ltac:(nlia) ltac:(nlia); have := B' ltac:(nlia) ltac:(nlia) => Hy3 Hy1.
        right; left; split.
        * have -> : y1 / lr = (y1 / (lr * wr)) * wr by field.
          lsq_tac.
        * have -> : y2 = (y1 * y2 * y3) / ((y1 / (lr * wr)) * (y3 / (4 * lr * wr)) * (2 * lr * wr) ^+ 2) by field.
          lsq_tac.
      + have := T12 p2; have := T13 p2; rewrite V12 V13 => A' B'.
        have := A' ltac:(nlia) ltac:(nlia); have := B' ltac:(nlia) ltac:(nlia) => Hy3 Hy2.
        right; right; right; split.
        * have -> : y1 / (- 3) = (y1 * y2 * y3) / ((y2 / (- (lr * wr))) * (y3 / (3 * lr * wr)) * (3 * lr * wr) ^+ 2) by field.
          lsq_tac.
        * have -> : y2 / (- lr) = (y2 / (- (lr * wr))) * wr by field.
          lsq_tac.
  Qed.

  (** the prime 3 (3 does not divide l, -l a 3-adic square):
      the second coordinate is a local square *)
  Lemma loc_three : p = 3%N -> vz p l = 0%N -> locsq p (- lr) -> locsq p y2.
  Proof.
    move=> Hp3 Hl Hml.
    have p2 : p != 2%N by rewrite Hp3.
    have H3 : vz p 3 = 1%N by rewrite Hp3 /vz /= (@logn_prime 3 3).
    have H4 : vz p 4 = 0%N by rewrite Hp3.
    have V12 : v12 = w by rewrite (vW ln Hl).
    have V13 : v13 = (1 + w)%N by rewrite (@vW 1 (3 * l)) ?mulf_neq0 // vzM // H3 Hl.
    have V23 : v23 = w by rewrite (@vW 0 (4 * l)) ?mulf_neq0 // vzM // H4 Hl.
    have [ s Hs ] := Hsq'; have [ s0 Hs0 ] := HW'.
    have H4r : (4 : rat) != 0 by [].
    have H2r : (2 : rat) != 0 by [].
    have := @split_c w ltac:(nlia) ltac:(nlia).
    case=> [ [ H1 [ H2 [ H3' H4' ] ] ] | [ [ H1 [ H2 [ H3' H4' ] ] ] |
             [ [ H1 [ H2 [ H3' H4' ] ] ] | [ H1 [ H2 [ H3' H4' ] ] ] ] ] ].
    - have := C12 p2; have := C13 p2; rewrite V12 V13 => A B.
      have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia) => Hb Ha.
      have Hy1 : locsq p y1.
      { have -> : y1 = (y1 * y2 * y3) / ((y2 / y1) * (y3 / y1) * y1 ^+ 2) by field.
        lsq_tac. }
      have -> : y2 = (y2 / y1) * y1 by field.
      lsq_tac.
    - have := C21 p2; have := C23 p2; rewrite V12 V23 => A B.
      have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia) => Hb Ha.
      have -> : y2 = (y1 * y2 * y3) / ((y1 / y2) * (y3 / y2) * y2 ^+ 2) by field.
      lsq_tac.
    - have := C31 p2; have := C32 p2; rewrite V13 V23 => A B.
      have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia) => Hb Ha.
      have Hy3 : locsq p y3.
      { have -> : y3 = (y1 * y2 * y3) / ((y1 / y3) * (y2 / y3) * y3 ^+ 2) by field.
        lsq_tac. }
      have -> : y2 = (y2 / y3) * y3 by field.
      lsq_tac.
    - have := d12; have := d23; rewrite V12 V23 => A C.
      have := A ltac:(nlia); have := C ltac:(nlia) => Hc Ha.
      have : (w < a2 \/ (a2 = w /\ w < a1) \/ (a2 = w /\ w < a3) \/ (a1 = w /\ a2 = w /\ a3 = w))%coq_nat
        by nlia.
      case=> [ Ha2 | [ [ Ha2 Ha1 ] | [ [ Ha2 Ha3 ] | [ Ha1 [ Ha2 Ha3 ] ] ] ] ].
      + have := T21 p2; have := T23 p2; rewrite V12 V23 => A' B'.
        have := A' ltac:(nlia) ltac:(nlia); have := B' ltac:(nlia) ltac:(nlia) => Hy3 Hy1.
        have -> : y2 = (y1 * y2 * y3) / ((y1 / (lr * wr)) * (y3 / (4 * lr * wr)) * (2 * lr * wr) ^+ 2) by field.
        lsq_tac.
      + have := T12 p2; rewrite V12 => A'.
        have := A' ltac:(nlia) ltac:(nlia) => Hy2.
        have -> : y2 = (y2 / (- (lr * wr))) * (- lr) * wr by field.
        lsq_tac.
      + have := T32 p2; rewrite V23 => A'.
        have := A' ltac:(nlia) ltac:(nlia) => Hy2.
        have -> : y2 = (y2 / (- (4 * lr * wr))) * (- lr) * wr * 2 ^+ 2 by field.
        lsq_tac.
      + have := C13 p2; rewrite V13 => A'.
        have := A' ltac:(nlia) ltac:(nlia) => Hy3.
        have -> : y2 = (y1 * y2 * y3) / (y1 ^+ 2 * (y3 / y1)) by field.
        lsq_tac.
  Qed.

  (** the prime 2: both valuations even, except in one exceptional
      configuration excluded separately (Lemma [two_bad]) *)
  Lemma loc_two : p = 2%N -> vz p l = 0%N ->
    (~~ odd a1 /\ ~~ odd a2) \/ (a1 = w /\ a2 = (w + 1)%N /\ a3 = (w + 1)%N /\ (w + 3 < k)%coq_nat).
  Proof.
    move=> Hp2 Hl.
    have H3 : vz p 3 = 0%N by rewrite Hp2.
    have H4 : vz p 4 = 2%N by rewrite Hp2 /vz /= (@lognX 2 2 2) (@logn_prime 2 2).
    have V12 : v12 = w by rewrite (vW ln Hl).
    have V13 : v13 = w by rewrite (@vW 0 (3 * l)) ?mulf_neq0 // vzM // H3 Hl.
    have V23 : v23 = (2 + w)%N by rewrite (@vW 2 (4 * l)) ?mulf_neq0 // vzM // H4 Hl.
    have [ s Hs ] := Hsq'; have [ s0 Hs0 ] := HW'.
    suff : (a1 = a2 /\ a2 = a3) \/ (a2 = w /\ a3 = w) \/ (a1 = w /\ a2 = w /\ a3 = w) \/
           (a1 = w /\ (a2 = 2 + w \/ a3 = 2 + w))%N \/
           (a1 = w /\ a2 = (w + 1)%N /\ a3 = (w + 1)%N /\ (w + 3 < k)%coq_nat).
    { move=> H; case: H => [ H | [ H | [ H | [ H | H ] ] ] ]; try (right; exact: H);
        left; split; apply/negP => /oddE [ h Hh ]; nlia. }
    have := @split_c w ltac:(nlia) ltac:(nlia).
    case=> [ [ H1 [ H2 [ H3' H4' ] ] ] | [ [ H1 [ H2 [ H3' H4' ] ] ] |
             [ [ H1 [ H2 [ H3' H4' ] ] ] | [ H1 [ H2 [ H3' H4' ] ] ] ] ] ].
    - have := p12; have := p13; rewrite V12 V13 => A B.
      left; have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia); nlia.
    - have := p21; have := p23; rewrite V12 V23 => A B.
      left; have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia); nlia.
    - have := p31; have := p32; rewrite V13 V23 => A B.
      left; have := A ltac:(nlia) ltac:(nlia); have := B ltac:(nlia) ltac:(nlia); nlia.
    - have := d12; have := d13; have := d23; have := p23; have := p32; rewrite V12 V13 V23 => P P' A B C.
      have := A ltac:(nlia); have := B ltac:(nlia); have := C ltac:(nlia) => Hc Hb Ha.
      have Hk3 : (a3 < k)%coq_nat \/ (2 + w <= a3)%coq_nat by nlia.
      have Hk2 : (a2 < k)%coq_nat \/ (2 + w <= a2)%coq_nat by nlia.
      nlia.
  Qed.

End Local.


(** ** The exceptional configuration at 2 (excluded by l = 3 mod 4) *)
Lemma oddz_of (x : int) : ~~ (2 %| x)%Z -> exists a, x = 2 * a + 1.
Proof.
  move=> H; exists (x %/ 2)%Z.
  have E := divz_eq x 2.
  have H0 : 0 <= (x %% 2)%Z by apply: modz_ge0.
  have H2 : (x %% 2)%Z < 2 by apply: ltz_pmod.
  have Hr : (x %% 2)%Z != 0 by apply: contra H => /eqP /dvdz_mod0P.
  move: H0 H2 Hr E; case: (x %% 2)%Z => [ [ | [ | n ] ] | n ] //= _ _ _ E. rewrite {1}E; congr (_ + _); exact: mulrC.
Qed.

Lemma int_2_4 (X : int) : 2 + 4 * X <> 0.
Proof.
  move=> /(congr1 int_to_Z); rewrite iz_add iz_mul => H.
  have E2 : int_to_Z 2 = 2%ZZ by []. have E4 : int_to_Z 4 = 4%ZZ by []. have E0 : int_to_Z 0 = 0%ZZ by [].
  rewrite E2 E4 E0 in H; lia.
Qed.

(* the exceptional 2-adic configuration contradicts l = 3 mod 4 *)
Lemma two_core (y1 y2 y3 l z s e e' : int) : ~~ (2 %| y2)%Z -> (l %% 4)%Z = 3 ->
  ~~ (2 %| z)%Z -> ~~ (2 %| s)%Z ->
  y1 - 2 * y2 - l * z ^+ 2 = e * 8 -> y1 - 2 * y3 + 3 * l * z ^+ 2 = e' * 8 ->
  y1 * y2 * y3 = s ^+ 2 -> False.
Proof.
  move=> /oddz_of [ a Ha ] Hl /oddz_of [ c Hc ] /oddz_of [ f Hf ] E1 E2 Hp.
  have Hb := divz_eq l 4; rewrite Hl in Hb; set b := (l %/ 4)%Z in Hb.
  have Hy1 : y1 = 2 * y2 + l * z ^+ 2 + e * 8.
  { by rewrite -E1; ring. }
  have Hy3 : y3 = y2 + 2 * l * z ^+ 2 + 4 * e - 4 * e'.
  { have : 2 * (y3 - (y2 + 2 * l * z ^+ 2 + 4 * e - 4 * e')) = 0.
    { have -> : 2 * (y3 - (y2 + 2 * l * z ^+ 2 + 4 * e - 4 * e')) =
                - (y1 - 2 * y3 + 3 * l * z ^+ 2) + (y1 - 2 * y2 - l * z ^+ 2) - e * 8 + 8 * e' by ring.
      rewrite E1 E2; ring. }
    move/eqP; rewrite mulf_eq0 /= subr_eq0 => /eqP; done. }
  set r2 := b * (4 * c ^+ 2 + 4 * c + 1) + 3 * c ^+ 2 + 3 * c.
  set u := a + 1 + r2 + 2 * e.
  set r3 := 1 + 2 * r2 + e - e'.
  set v := a ^+ 2 + 2 * a + r3 * (2 * a + 1).
  apply: (@int_2_4 (v + 3 * u + 4 * u * v - f ^+ 2 - f)).
  have -> : 2 + 4 * (v + 3 * u + 4 * u * v - f ^+ 2 - f) = y1 * y2 * y3 - s ^+ 2.
  { rewrite Hy3 Hy1 Ha Hc Hf Hb /v /r3 /u /r2; ring. }
  by rewrite Hp subrr.
Qed.

Section dec.

  Variable p : nat.
  Hypothesis pP : prime p.

  Lemma vz_dec (Y : int) : Y != 0 -> exists y, Y = (p ^ vz p Y)%:Z * y /\ ~~ (p%:Z %| y)%Z.
  Proof.
    move=> HY; have Hn : (0 < `|Y|)%N by rewrite absz_gt0.
    have [ m Hm E ] := pfactor_coprime pP Hn.
    rewrite /vz; set v := logn p `|Y| in E *.
    exists (sgz Y * m%:Z); split.
    - rewrite {1}(intEsg Y) E PoszM; ring.
    - rewrite dvdzE abszM.
      have -> : `|sgz Y|%N = 1%N by move: HY; case: (sgzP Y).
      by rewrite mul1n /= -prime_coprime.
  Qed.

  Lemma pz_neq0 (n : nat) : (p ^ n)%:Z != 0.
  Proof. by rewrite eqz_nat expn_eq0 negb_and -lt0n prime_gt0. Qed.

  Lemma vz_pmul (n : nat) (X : int) : X != 0 -> vz p ((p ^ n)%:Z * X) = (n + vz p X)%N.
  Proof. by move=> HX; rewrite vzM ?pz_neq0 // vz_nat pfactorK. Qed.

  Lemma vge_cancel (k w : nat) (X : int) : vge p k ((p ^ w)%:Z * X) -> (w + 3 <= k)%N ->
    ((p ^ 3)%:Z %| X)%Z.
  Proof.
    case: (eqVneq X 0) => [ -> | HX ]; first by rewrite dvdz0.
    case=> [ E | H ] Hk.
    - by move: E => /eqP; rewrite mulf_eq0 (negbTE HX) orbF (negbTE (pz_neq0 _)).
    - rewrite vz_dvd //; move: H; rewrite vz_pmul //; move=> H; nlia.
  Qed.

  Lemma odd_mul (a b : int) : ~~ (p%:Z %| a)%Z -> ~~ (p%:Z %| b)%Z -> ~~ (p%:Z %| a * b)%Z.
  Proof. by rewrite !dvdzE abszM Euclid_dvdM // negb_or => -> ->. Qed.

End dec.

Lemma two_bad (l Y1 Y2 Y3 W : int) (k w : nat) :
  Y1 != 0 -> Y2 != 0 -> Y3 != 0 -> W != 0 ->
  vge 2 k (Y1 - Y2 - l * W) -> vge 2 k (Y1 - Y3 + 3 * l * W) ->
  (exists s, Y1 * Y2 * Y3 = s ^+ 2) -> (exists z, W = z ^+ 2) ->
  vz 2 W = w -> vz 2 Y1 = w -> vz 2 Y2 = (w + 1)%N -> vz 2 Y3 = (w + 1)%N -> (w + 3 < k)%N ->
  (l %% 4)%Z = 3 -> False.
Proof.
  move=> H1 H2 H3 HW E1 E2 [ s Hs ] [ z Hz ] VW V1 V2 V3 Hk Hl.
  have p2 : prime 2 by [].
  have [ y1 [ Ey1 Oy1 ] ] := vz_dec p2 H1; rewrite V1 in Ey1.
  have [ y2 [ Ey2 Oy2 ] ] := vz_dec p2 H2; rewrite V2 in Ey2.
  have [ y3 [ Ey3 Oy3 ] ] := vz_dec p2 H3; rewrite V3 in Ey3.
  have Hz0 : z != 0 by apply/eqP => E; move: HW; rewrite Hz E expr0n.
  have [ z' [ Ez Oz ] ] := vz_dec p2 Hz0.
  have Hw : w = (vz 2 z + vz 2 z)%N by rewrite -VW Hz vz_sq.
  have EW : W = (2 ^ w)%:Z * z' ^+ 2 by rewrite Hz Ez Hw expnD PoszM; ring.
  have Hs0 : s != 0.
  { apply/eqP => E; move: Hs; rewrite E expr0n /= => /eqP.
    by rewrite !mulf_eq0 (negbTE H1) (negbTE H2) (negbTE H3). }
  have [ s' [ Es Os ] ] := vz_dec p2 Hs0.
  set t := vz 2 s in Es.
  have HP : ~~ (2%:Z %| y1 * y2 * y3)%Z by apply: odd_mul => //; apply: odd_mul.
  have HS : ~~ (2%:Z %| s' ^+ 2)%Z by rewrite expr2; apply: odd_mul.
  have HP0 : y1 * y2 * y3 != 0 by apply: contra HP => /eqP ->; rewrite dvdz0.
  have HS0 : s' ^+ 2 != 0 by apply: contra HS => /eqP ->; rewrite dvdz0.
  have EP : Y1 * Y2 * Y3 = (2 ^ (3 * w + 2))%:Z * (y1 * y2 * y3).
  { rewrite Ey1 Ey2 Ey3 (_ : (3 * w + 2 = w + (w + 1) + (w + 1))%N); first by nlia.
    rewrite !expnD !PoszM; ring. }
  have ES : s ^+ 2 = (2 ^ (t + t))%:Z * s' ^+ 2.
  { by rewrite {1}Es expnD PoszM; ring. }
  have Ev : (3 * w + 2 = t + t)%N.
  { have := congr1 (vz 2) Hs; rewrite EP ES !vz_pmul // !vz_ndvd //; nlia. }
  have Hsq : y1 * y2 * y3 = s' ^+ 2.
  { apply: (mulfI (pz_neq0 p2 (3 * w + 2))); by rewrite -EP Hs ES Ev. }
  have [ e He ] : exists e, y1 - 2 * y2 - l * z' ^+ 2 = e * 8.
  { apply/dvdzP; apply: (@vge_cancel 2 p2 k w); last by nlia.
    have -> : (2 ^ w)%:Z * (y1 - 2 * y2 - l * z' ^+ 2) = Y1 - Y2 - l * W
      by rewrite Ey1 Ey2 EW expnD PoszM; ring.
    done. }
  have [ e' He' ] : exists e, y1 - 2 * y3 + 3 * l * z' ^+ 2 = e * 8.
  { apply/dvdzP; apply: (@vge_cancel 2 p2 k w); last by nlia.
    have -> : (2 ^ w)%:Z * (y1 - 2 * y3 + 3 * l * z' ^+ 2) = Y1 - Y3 + 3 * l * W
      by rewrite Ey1 Ey3 EW expnD PoszM; ring.
    done. }
  exact: (two_core Oy2 Hl Oz Os He He' Hsq).
Qed.


(** ** From [locsol l p d] to local conditions on d *)
Definition pad (P z : int) : int := if z == 0 then P else z.

Lemma pad_neq0 P z : P != 0 -> pad P z != 0.
Proof. by move=> HP; rewrite /pad; case: (eqVneq z 0). Qed.

Lemma pad_dvd P z : (P %| pad P z - z)%Z.
Proof. by rewrite /pad; case: (eqVneq z 0) => [ -> | _ ]; rewrite ?eqxx ?subr0 ?subrr ?dvdz0 ?dvdzz. Qed.

Lemma pad_sq P z : (P %| pad P z ^+ 2 - z ^+ 2)%Z.
Proof.
  have -> : pad P z ^+ 2 - z ^+ 2 = (pad P z - z) * (pad P z + z) by ring.
  exact: dvdz_mulr (pad_dvd P z).
Qed.

Lemma pad_ndvd (p : nat) P z : ~~ (p%:Z %| z)%Z -> pad P z = z.
Proof. by rewrite /pad; case: (eqVneq z 0) => // ->; rewrite dvdz0. Qed.

Lemma locsol_data (l : int) (p : nat) (d1 d2 : int) : prime p -> locsol l p (d1, d2) ->
  forall k : nat, (0 < k)%N ->
  exists z0 z1 z2 z3 : int, (z0 != 0 /\ z1 != 0 /\ z2 != 0 /\ z3 != 0) /\
    vge p k (d1 * z1 ^+ 2 - d2 * z2 ^+ 2 - l * z0 ^+ 2) /\
    vge p k (d1 * z1 ^+ 2 - d1 * d2 * z3 ^+ 2 + 3 * l * z0 ^+ 2) /\
    (~~ (p%:Z %| z0)%Z \/ ~~ (p%:Z %| z1)%Z \/ ~~ (p%:Z %| z2)%Z \/ ~~ (p%:Z %| z3)%Z).
Proof.
  move=> pP Hl k Hk.
  have [ z0 [ z1 [ z2 [ z3 [ Hpr [ H1 H2 ] ] ] ] ] ] := Hl k.
  set P := (p ^ k)%:Z.
  have P0 : P != 0 by apply: pz_neq0.
  exists (pad P z0), (pad P z1), (pad P z2), (pad P z3).
  split; first by rewrite !pad_neq0.
  split; [ | split ].
  - apply: (vge_dvd pP).
    have -> : d1 * pad P z1 ^+ 2 - d2 * pad P z2 ^+ 2 - l * pad P z0 ^+ 2 =
      eqn1 l (d1, d2) z0 z1 z2 z3 + (d1 * (pad P z1 ^+ 2 - z1 ^+ 2) - d2 * (pad P z2 ^+ 2 - z2 ^+ 2)
        - l * (pad P z0 ^+ 2 - z0 ^+ 2)).
    { rewrite /eqn1 /qform /=; ring. }
    apply: rpredD; first exact: H1.
    by apply: rpredB; first apply: rpredB; apply: dvdz_mull; apply: pad_sq.
  - apply: (vge_dvd pP).
    have -> : d1 * pad P z1 ^+ 2 - d1 * d2 * pad P z3 ^+ 2 + 3 * l * pad P z0 ^+ 2 =
      eqn2 l (d1, d2) z0 z1 z2 z3 + (d1 * (pad P z1 ^+ 2 - z1 ^+ 2) - d1 * d2 * (pad P z3 ^+ 2 - z3 ^+ 2)
        + 3 * l * (pad P z0 ^+ 2 - z0 ^+ 2)).
    { rewrite /eqn2 /qform /=; ring. }
    apply: rpredD; first exact: H2.
    by apply: rpredD; first apply: rpredB; apply: dvdz_mull; apply: pad_sq.
  - move: Hpr; rewrite /primitive !negb_and => /or4P [] H.
    + by left; rewrite (pad_ndvd _ H).
    + by right; left; rewrite (pad_ndvd _ H).
    + by right; right; left; rewrite (pad_ndvd _ H).
    + by right; right; right; rewrite (pad_ndvd _ H).
Qed.

Lemma local_facts (l : int) (p : nat) (d1 d2 : int) : prime p -> d1 != 0 -> d2 != 0 ->
  locsol l p (d1, d2) ->
  exists z0 z1 z2 z3 : int, (z0 != 0 /\ z1 != 0 /\ z2 != 0 /\ z3 != 0) /\
   vge p (vz p d1 + vz p d2 + 4) (d1 * z1 ^+ 2 - d2 * z2 ^+ 2 - l * z0 ^+ 2) /\
   vge p (vz p d1 + vz p d2 + 4) (d1 * z1 ^+ 2 - d1 * d2 * z3 ^+ 2 + 3 * l * z0 ^+ 2) /\
   [|| vz p (d1 * z1 ^+ 2) <= vz p d1 + vz p d2, vz p (d2 * z2 ^+ 2) <= vz p d1 + vz p d2,
       vz p (d1 * d2 * z3 ^+ 2) <= vz p d1 + vz p d2 | vz p (z0 ^+ 2) <= vz p d1 + vz p d2]%N.
Proof.
  move=> pP H1 H2 Hl.
  have [ z0 [ z1 [ z2 [ z3 [ [ n0 [ n1 [ n2 n3 ] ] ] [ E1 [ E2 Hpr ] ] ] ] ] ] ] :=
    locsol_data pP Hl (k := (vz p d1 + vz p d2 + 4)%N) ltac:(by rewrite addn4).
  exists z0, z1, z2, z3; do 3 (split => //).
  apply/or4P; case: Hpr => [ H | [ H | [ H | H ] ] ].
  - by constructor 4; rewrite vz_sq // (vz_ndvd H).
  - by constructor 1; rewrite vzM ?expf_neq0 // vz_sq // (vz_ndvd H) !addn0 leq_addr.
  - by constructor 2; rewrite vzM ?expf_neq0 // vz_sq // (vz_ndvd H) !addn0 leq_addl.
  - by constructor 3; rewrite vzM ?mulf_neq0 ?expf_neq0 // vz_sq // (vz_ndvd H) !addn0 vzM.
Qed.

Lemma par_sq (p : nat) (d z : int) : prime p -> d != 0 -> z != 0 ->
  ~~ odd (vz p (d * z ^+ 2)) -> ~~ odd (vz p d).
Proof. by move=> pP Hd Hz; rewrite vzM ?expf_neq0 // vz_sq // oddD addnn odd_double addbF. Qed.

Lemma lsq_sq (p : nat) (d z : int) (t : rat) : prime p -> z != 0 ->
  locsq p ((d * z ^+ 2)%:~R * t) -> locsq p (d%:~R * t).
Proof.
  move=> pP Hz H.
  have Hz' : (z%:~R : rat) != 0 by rewrite intr_eq0.
  have -> : d%:~R * t = ((d * z ^+ 2)%:~R * t) / (z%:~R ^+ 2).
  { by rewrite intrM rmorphXn /=; field. }
  by apply: (locsq_div pP) => //; apply: locsq_sq.
Qed.

Lemma lsq_sq1 (p : nat) (d z : int) : prime p -> z != 0 ->
  locsq p ((d * z ^+ 2)%:~R) -> locsq p (d%:~R).
Proof. move=> pP Hz H; rewrite -[_%:~R]mulr1; apply: (lsq_sq pP Hz); by rewrite mulr1. Qed.

Lemma prod_sq (d1 d2 z1 z2 z3 : int) :
  exists s : int, d1 * z1 ^+ 2 * (d2 * z2 ^+ 2) * (d1 * d2 * z3 ^+ 2) = s ^+ 2.
Proof. by exists (d1 * d2 * z1 * z2 * z3); ring. Qed.

Lemma vz3 (p : nat) : prime p -> p != 3%N -> vz p 3 = 0%N.
Proof.
  move=> pP H3; rewrite (_ : (3 : int) = (3%N)%:Z) // vz_nat logn_ndvd //.
  by rewrite dvdn_prime2.
Qed.

Lemma vz4 (p : nat) : prime p -> p != 2%N -> vz p 4 = 0%N.
Proof.
  move=> pP H2; rewrite (_ : (4 : int) = (4%N)%:Z) // vz_nat logn_ndvd //.
  rewrite (_ : 4%N = 2 * 2)%N // Euclid_dvdM // dvdn_prime2 //; by rewrite (negbTE H2).
Qed.

(** good odd primes *)
Lemma good_even (l : int) (p : nat) (d1 d2 : int) : prime p -> p != 2%N -> p != 3%N ->
  ~~ (p%:Z %| l)%Z -> l != 0 -> d1 != 0 -> d2 != 0 -> locsol l p (d1, d2) ->
  ~~ odd (vz p d1) /\ ~~ odd (vz p d2).
Proof.
  move=> pP p2 p3 Hpl Hl H1 H2 Hloc.
  have [ z0 [ z1 [ z2 [ z3 [ [ n0 [ n1 [ n2 n3 ] ] ] [ E1 [ E2 Hm ] ] ] ] ] ] ] := local_facts pP H1 H2 Hloc.
  have [ ] := @loc_good p l (d1 * z1 ^+ 2) (d2 * z2 ^+ 2) (d1 * d2 * z3 ^+ 2) (z0 ^+ 2)
    (vz p d1 + vz p d2 + 4) (vz p d1 + vz p d2) pP ltac:(by rewrite mulf_neq0 ?expf_neq0)
    ltac:(by rewrite mulf_neq0 ?expf_neq0) ltac:(by rewrite !mulf_neq0 ?expf_neq0)
    ltac:(by rewrite expf_neq0) Hl E1 E2 (prod_sq _ _ _ _ _) (ex_intro _ z0 erefl) Hm
    ltac:(by rewrite ltn_add2l) (vz_ndvd Hpl) (vz3 pP p3) (vz4 pP p2).
  by move=> A B; split; [ exact: par_sq A | exact: par_sq B ].
Qed.

Ltac inst_local lem p l d1 d2 z0 z1 z2 z3 pP Hl E1 E2 Hm :=
  have := @lem p l (d1 * z1 ^+ 2) (d2 * z2 ^+ 2) (d1 * d2 * z3 ^+ 2) (z0 ^+ 2)
    (vz p d1 + vz p d2 + 4) (vz p d1 + vz p d2) pP ltac:(by rewrite mulf_neq0 ?expf_neq0)
    ltac:(by rewrite mulf_neq0 ?expf_neq0) ltac:(by rewrite !mulf_neq0 ?expf_neq0)
    ltac:(by rewrite expf_neq0) Hl E1 E2 (prod_sq _ _ _ _ _) (ex_intro _ z0 erefl) Hm
    ltac:(by rewrite ltn_add2l).

Lemma ndvd_lin (d m q r l : int) : l = q * m + r -> (d %| m)%Z -> ~~ (d %| r)%Z -> ~~ (d %| l)%Z.
Proof.
  move=> -> Hm Hr; apply: contra Hr => H.
  have -> : r = q * m + r - q * m by ring.
  by apply: rpredB => //; apply: dvdz_mull.
Qed.

Lemma ndvd_mod (d m r l : int) : (l %% m)%Z = r -> (d %| m)%Z -> ~~ (d %| r)%Z -> ~~ (d %| l)%Z.
Proof. by move=> Hl; apply: ndvd_lin; rewrite {1}(divz_eq l m) Hl. Qed.

(** the prime 2 *)
Lemma two_even (l : int) (d1 d2 : int) : (l %% 4)%Z = 3 -> d1 != 0 -> d2 != 0 ->
  locsol l 2 (d1, d2) -> ~~ odd (vz 2 d1) /\ ~~ odd (vz 2 d2).
Proof.
  move=> Hl4 H1 H2 Hloc.
  have pP : prime 2 by [].
  have Hl2 : ~~ ((2%N)%:Z %| l)%Z by apply: (ndvd_mod Hl4).
  have Hl : l != 0 by apply: contra Hl2 => /eqP ->; rewrite dvdz0.
  have [ z0 [ z1 [ z2 [ z3 [ [ n0 [ n1 [ n2 n3 ] ] ] [ E1 [ E2 Hm ] ] ] ] ] ] ] := local_facts pP H1 H2 Hloc.
  inst_local loc_two 2%N l d1 d2 z0 z1 z2 z3 pP Hl E1 E2 Hm.
  case/(_ erefl (vz_ndvd Hl2)) => [ [ A B ] | [ V1 [ V2 [ V3 Hk ] ] ] ].
  - by split; [ exact: par_sq A | exact: par_sq B ].
  - exfalso; apply: (@two_bad l (d1 * z1 ^+ 2) (d2 * z2 ^+ 2) (d1 * d2 * z3 ^+ 2) (z0 ^+ 2)
      (vz 2 d1 + vz 2 d2 + 4) (vz 2 (z0 ^+ 2)) ltac:(by rewrite mulf_neq0 ?expf_neq0)
      ltac:(by rewrite mulf_neq0 ?expf_neq0) ltac:(by rewrite !mulf_neq0 ?expf_neq0)
      ltac:(by rewrite expf_neq0) E1 E2 (prod_sq _ _ _ _ _) (ex_intro _ z0 erefl) erefl V1 V2 V3 _ Hl4).
    by apply/ssrnat.ltP.
Qed.

(** the prime 3 *)
Lemma three_sq (l : int) (d1 d2 : int) : (l %% 3)%Z = 2 -> d1 != 0 -> d2 != 0 ->
  locsol l 3 (d1, d2) -> locsq 3 d2%:~R.
Proof.
  move=> Hl3 H1 H2 Hloc.
  have pP : prime 3 by [].
  have Hl3' : ~~ ((3%N)%:Z %| l)%Z by apply: (ndvd_mod Hl3).
  have Hl : l != 0 by apply: contra Hl3' => /eqP ->; rewrite dvdz0.
  have Hml : locsq 3 (- l%:~R).
  { have H : locsq 3 ((- l)%:~R / (1 : int)%:~R).
    { apply: (@lsq_close 3 pP (- l) 1 (- l - 1)) => //; first by rewrite oppr_eq0.
      - by rewrite addrC subrK.
      - apply: (vge_dvd pP); rewrite expn1; apply/dvdzP; exists (- (l %/ 3)%Z - 1).
        by rewrite {1}(divz_eq l 3) Hl3; ring. }
    by move: H; rewrite rmorph1 divr1 intrN. }
  have [ z0 [ z1 [ z2 [ z3 [ [ n0 [ n1 [ n2 n3 ] ] ] [ E1 [ E2 Hm ] ] ] ] ] ] ] := local_facts pP H1 H2 Hloc.
  inst_local loc_three 3%N l d1 d2 z0 z1 z2 z3 pP Hl E1 E2 Hm.
  move=> /(_ erefl (vz_ndvd Hl3') Hml); exact: lsq_sq1.
Qed.

(** the support primes *)
Lemma l_tors (l : int) (q : nat) (d1 d2 : int) : prime q -> q != 2%N -> q != 3%N ->
  vz q l = 1%N -> d1 != 0 -> d2 != 0 -> locsol l q (d1, d2) ->
  let x1 := (d1%:~R : rat) in let x2 := (d2%:~R : rat) in let lr := (l%:~R : rat) in
    (locsq q x1 /\ locsq q x2) \/
    (locsq q (x1 / lr) /\ locsq q x2) \/
    (locsq q (x1 / (- (3 * lr))) /\ locsq q (x2 / (- lr))) \/
    (locsq q (x1 / (- 3)) /\ locsq q (x2 / (- lr))).
Proof.
  move=> pP q2 q3 Hl1 H1 H2 Hloc x1 x2 lr.
  have Hl : l != 0 by apply/eqP => E; move: Hl1; rewrite E /vz /= logn0.
  have [ z0 [ z1 [ z2 [ z3 [ [ n0 [ n1 [ n2 n3 ] ] ] [ E1 [ E2 Hm ] ] ] ] ] ] ] := local_facts pP H1 H2 Hloc.
  inst_local loc_l q l d1 d2 z0 z1 z2 z3 pP Hl E1 E2 Hm.
  move=> /(_ q2 (vz3 pP q3) (vz4 pP q2) Hl1).
  case=> [ [ A B ] | [ [ A B ] | [ [ A B ] | [ A B ] ] ] ].
  - by left; split; apply: lsq_sq1 A || apply: lsq_sq1 B.
  - by right; left; split; [ apply: lsq_sq A | apply: lsq_sq1 B ].
  - by right; right; left; split; [ apply: lsq_sq A | apply: lsq_sq B ].
  - by right; right; right; split; [ apply: lsq_sq A | apply: lsq_sq B ].
Qed.

(** the real place: d1 d2 > 0 *)
Lemma inf_pos (l d1 d2 : int) : 0 < l -> locsol_inf l (d1, d2) -> 0 < d1 * d2.
Proof.
  move=> Hl [ x [ C1 [ C2 C3 ] ] ] /=; rewrite /= in C1 C2 C3.
  have Hl' : (0 : rat) < l%:~R by rewrite ltr0z.
  rewrite -(ltr0z rat) intrM.
  have neg_d (y : rat) (d : int) : y < 0 -> (y = 0 \/ 0 < y * d%:~R) -> (d%:~R : rat) < 0.
  { move=> Hy [ E | H ]; first by move: Hy; rewrite E ltxx.
    by move: H; rewrite nmulr_rgt0. }
  have Hneg : x < 0 -> (d1%:~R : rat) * d2%:~R > 0.
  { move=> Hx; have Hxl : x - l%:~R < 0 by rewrite subr_lt0 (lt_trans Hx).
    by rewrite nmulr_rgt0 ?(neg_d _ _ Hx C1) // (neg_d _ _ Hxl C2). }
  case: C3 => [ E | H ].
  - apply: Hneg; have -> : x = - (3 * l%:~R) by apply/eqP; rewrite -addr_eq0 E.
    by rewrite oppr_lt0 mulr_gt0.
  - case: (ltrgtP (x + 3 * l%:~R) 0) => [ Hn | Hp | E ].
    + rewrite intrM nmulr_rgt0 // in H.
      have Hx : x < 0 by apply: lt_trans Hn; rewrite ltrDl mulr_gt0.
      by move: (Hneg Hx); rewrite ltNge (ltW H).
    + by move: H; rewrite intrM pmulr_rgt0.
    + by move: H; rewrite E mul0r ltxx.
Qed.


(** * Part B. Linear algebra over F_2 (the kernel argument of par:descent) *)
Lemma F2_cases (c : 'F_2) : c = 0 \/ c = 1.
Proof. case: c => [ [ | [ | m ] ] Hm ] //=. all: try (by left; apply: val_inj). all: try (by right; apply: val_inj). Qed.

Lemma F2_add_eq0 (c : 'F_2) : c + c = 0.
Proof. by case: (F2_cases c) => ->; [ rewrite addr0 | apply/eqP ]. Qed.

Lemma mx1_neq0 : (1%:M : 'M['F_2]_1) != 0.
Proof. by apply/eqP => /matrixP /(_ 0 0); rewrite !mxE /= => /eqP; rewrite oner_eq0. Qed.

Lemma mx2 (a b : nat) (A : 'M['F_2]_(a, b)) : A + A = 0.
Proof. by apply/matrixP => i j; rewrite !mxE F2_add_eq0. Qed.

Lemma mxN (a b : nat) (A : 'M['F_2]_(a, b)) : - A = A.
Proof. by apply/eqP; rewrite eq_sym -subr_eq0 opprK mx2. Qed.

Lemma mx_eqD (a b : nat) (A B : 'M['F_2]_(a, b)) : A + B = 0 -> A = B.
Proof. by move=> H; apply/eqP; rewrite -subr_eq0 mxN H. Qed.

Section F2.

  Variable n : nat.
  Local Abbreviation F := 'F_2.

  Lemma rank2 (a b : 'rV[F]_n) : a != 0 -> b != 0 -> a != b -> \rank (a + b)%MS = 2%N.
  Proof.
    move=> Ha Hb Hab.
    have Hra : \rank a = 1%N by rewrite rank_rV Ha.
    have Hrb : \rank b = 1%N by rewrite rank_rV Hb.
    apply/eqP; rewrite eqn_leq; apply/andP; split.
    - by have [ H _ ] := mxrank_adds_leqif a b; rewrite Hra Hrb in H.
    - rewrite ltnNge; apply/negP => Hle.
      have Hs : (a + b <= a)%MS by rewrite -(geq_leqif (mxrank_leqif_sup (addsmxSl a b))) Hra.
      have /sub_rVP [ c Hc ] : (b <= a)%MS by apply: submx_trans (addsmxSr a b) Hs.
      case: (F2_cases c) => Ec; move: Hc; rewrite Ec ?scale0r ?scale1r => Hc.
      + by move: Hb; rewrite Hc eqxx.
      + by move: Hab; rewrite Hc eqxx.
  Qed.

  Variables (K : 'M[F]_n) (s lam oneB : 'cV[F]_n).
  Local Abbreviation one := (const_mx 1 : 'cV[F]_n).

  Hypothesis Hker : forall u : 'cV[F]_n, K *m u = 0 -> u = 0 \/ u = one \/ u = oneB \/ u = one + oneB.
  Hypothesis Hlam : forall u : 'cV[F]_n, K *m u != lam.
  Hypothesis Hs1 : s^T *m one = 1%:M.
  Hypothesis Hl1 : lam^T *m one = 0.
  Hypothesis HKt1 : K^T *m one = 0.

  Lemma rank_kerKt : (\rank (kermx K^T) <= 2)%N.
  Proof.
    have Hsub : (kermx K^T <= one^T + oneB^T)%MS.
    { apply/row_subP => i; set r := row i (kermx K^T).
      have Hr : r *m K^T = 0 by rewrite /r -row_mul mulmx_ker row0.
      have : K *m r^T = 0 by rewrite -[K]trmxK -trmx_mul Hr trmx0.
      move/Hker => Hr'; rewrite -(trmxK r); case: Hr' => [ -> | [ -> | [ -> | -> ] ] ]; rewrite ?trmxK ?trmx0 ?sub0mx ?addsmxSl ?addsmxSr //.
      by rewrite linearD /= addmx_sub_adds. }
    apply: leq_trans (mxrankS Hsub) _.
    have [ H _ ] := mxrank_adds_leqif one^T oneB^T.
    by apply: leq_trans H _; rewrite -[2%N]/(1 + 1)%N; apply: leq_add; apply: rank_leq_row.
  Qed.

  Lemma key (w : 'cV[F]_n) : K^T *m w = 0 -> s^T *m w = 0 -> lam^T *m w = 0 -> w = 0.
  Proof.
    move=> H1 H2 H3; apply/eqP; apply/negPn/negP => Hw.
    have Hone : one != 0.
    { apply/negP => /eqP E; move: Hs1; rewrite E mulmx0 => E'.
      by move: mx1_neq0; rewrite -E' eqxx. }
    have Hw1 : w != one.
    { apply/negP => /eqP E; move: H2; rewrite E Hs1 => E'.
      by move: mx1_neq0; rewrite E' eqxx. }
    set W := kermx K.
    have HwW : (w^T <= W)%MS by apply/sub_kermxP; rewrite -[K]trmxK -trmx_mul H1 trmx0.
    have H1W : (one^T <= W)%MS by apply/sub_kermxP; rewrite -[K]trmxK -trmx_mul HKt1 trmx0.
    have HrW : (\rank W <= 2)%N.
    { rewrite /W mxrank_ker -(mxrank_tr K) -mxrank_ker; exact: rank_kerKt. }
    have HS : (w^T + one^T <= W)%MS by rewrite addsmx_sub HwW H1W.
    have HrS : \rank (w^T + one^T)%MS = 2%N.
    { apply: rank2.
      - by apply: contra Hw => /eqP E; rewrite -[w]trmxK E trmx0.
      - by apply: contra Hone => /eqP E; rewrite -[one]trmxK E trmx0.
      - by apply: contra Hw1 => /eqP E; rewrite -[w]trmxK E trmxK. }
    have HWS : (W <= w^T + one^T)%MS.
    { by rewrite -(geq_leqif (mxrank_leqif_sup HS)) HrS. }
    have HSl : (w^T + one^T <= kermx lam)%MS.
    { rewrite addsmx_sub; apply/andP; split; apply/sub_kermxP.
      - by rewrite -[lam]trmxK -trmx_mul H3 trmx0.
      - by rewrite -[lam]trmxK -trmx_mul Hl1 trmx0. }
    have HWl : W *m lam = 0 by apply/sub_kermxP; apply: submx_trans HWS HSl.
    have Hlk : (lam^T <= kermx W^T)%MS by apply/sub_kermxP; rewrite -trmx_mul HWl trmx0.
    have HKk : (K^T <= kermx W^T)%MS by apply/sub_kermxP; rewrite -trmx_mul mulmx_ker trmx0.
    have HKr : (\rank (kermx W^T) <= \rank K^T)%N.
    { rewrite mxrank_ker mxrank_tr /W mxrank_ker mxrank_tr subKn //; exact: rank_leq_row. }
    have HkK : (kermx W^T <= K^T)%MS by rewrite -(geq_leqif (mxrank_leqif_sup HKk)).
    have /submxP [ x Hx ] : (lam^T <= K^T)%MS by apply: submx_trans Hlk HkK.
    by move: (Hlam x^T); rewrite -[lam]trmxK Hx trmx_mul trmxK eqxx.
  Qed.

  Hypothesis HQR : K + K^T = s *m s^T + diag_mx s^T.
  Hypothesis HK1 : K *m one = 0.

  Lemma diag_one (x : 'cV[F]_n) : diag_mx x^T *m one = x.
  Proof. by apply/matrixP => i j; rewrite mul_diag_mx !mxE (ord1 j) mulr1. Qed.

  Lemma diag_add (x y v : 'cV[F]_n) : diag_mx (x + y)^T *m v = diag_mx x^T *m v + diag_mx y^T *m v.
  Proof. by apply/matrixP => i j; rewrite !mul_diag_mx !mxE mulrDl. Qed.

  Lemma diag_scale (x : 'cV[F]_n) (c : F) : diag_mx x^T *m (c *: one) = c *: x.
  Proof. by rewrite -scalemxAr diag_one. Qed.

  Lemma Kt_eq : K^T = K + s *m s^T + diag_mx s^T.
  Proof. by rewrite -addrA -HQR addrA mx2 add0r. Qed.

  Lemma HKt1' : K^T *m one = 0.
  Proof.
    rewrite Kt_eq !mulmxDl HK1 add0r -mulmxA Hs1 mul_mx_scalar scale1r diag_one; exact: mx2.
  Qed.

  Theorem linalg (u1 v : 'cV[F]_n) (dl sg : F) :
    K *m u1 + dl *: lam + diag_mx (s + lam)^T *m v + sg *: s = 0 ->
    K *m v + diag_mx s^T *m v + sg *: s = 0 ->
    (lam + s)^T *m v + sg%:M = 0 ->
    v = sg *: one /\ dl = sg /\ K *m u1 = 0.
  Proof.
    move=> S1 S2 S3.
    have Hst : (s^T *m one)^T = one^T *m s by rewrite trmx_mul trmxK.
    have H1s : one^T *m s = 1%:M by rewrite -Hst Hs1 tr_scalar_mx.
    have HKv : K^T *m v = sg *: s + s *m (s^T *m v).
    { rewrite Kt_eq !mulmxDl -mulmxA.
      have -> : K *m v = diag_mx s^T *m v + sg *: s.
      { apply: mx_eqD; by rewrite addrA. }
      by rewrite addrC !addrA mx2 add0r. }
    have Hsv : s^T *m v = sg%:M.
    { have : one^T *m (K^T *m v) = 0 by rewrite mulmxA -trmx_mul HK1 trmx0 mul0mx.
      rewrite HKv mulmxDr -scalemxAr H1s mulmxA H1s mul1mx scalemx1.
      by move/mx_eqD. }
    have HKv0 : K^T *m v = 0 by rewrite HKv Hsv mul_mx_scalar mx2.
    have Hlv : lam^T *m v = 0.
    { move: S3; rewrite linearD /= mulmxDl Hsv -addrA mx2 addr0; done. }
    set w := v + sg *: one.
    have Hw : w = 0.
    { apply: key.
      - by rewrite /w mulmxDr HKv0 -scalemxAr HKt1' scaler0 addr0.
      - by rewrite /w mulmxDr Hsv -scalemxAr Hs1 scalemx1 mx2.
      - by rewrite /w mulmxDr Hlv -scalemxAr Hl1 scaler0 addr0. }
    have Hv : v = sg *: one by apply: mx_eqD.
    split => //.
    move: S1; rewrite Hv diag_scale scalerDr.
    have -> : K *m u1 + dl *: lam + (sg *: s + sg *: lam) + sg *: s = K *m u1 + (dl + sg) *: lam.
    { move: (K *m u1) => A; apply/matrixP => i j; rewrite !mxE.
      move: (A i j) (lam i j) (s i j) => x y z.
      by case: (F2_cases x) => ->; case: (F2_cases y) => ->; case: (F2_cases z) => ->;
        case: (F2_cases dl) => ->; case: (F2_cases sg) => ->; apply/eqP. }
    case: (F2_cases (dl + sg)) => E.
    - rewrite E scale0r addr0 => H; split => //.
      by move: E; case: (F2_cases dl) => ->; case: (F2_cases sg) => -> //; move/eqP.
    - by rewrite E scale1r => /mx_eqD H; move: (Hlam u1); rewrite H eqxx.
  Qed.


End F2.

Lemma f2_rows (s lam KL G1 G2 sg dl u v : 'F_2) :
  (sg * s + dl * lam + G1) + (v * (s + lam) + u * KL) == 0 ->
  (sg * s + G2) + v * (s + KL) == 0 ->
  ((u * KL + G1) + dl * lam + (s + lam) * v + sg * s == 0) && ((v * KL + G2) + s * v + sg * s == 0).
Proof.
  case: (F2_cases s) => ->; case: (F2_cases lam) => ->; case: (F2_cases KL) => ->;
  case: (F2_cases G1) => ->; case: (F2_cases G2) => ->; case: (F2_cases sg) => ->;
  case: (F2_cases dl) => ->; case: (F2_cases u) => ->; case: (F2_cases v) => ->; vm_compute; done.
Qed.

Lemma F2_of_eq (x : 'F_2) (b : bool) : (x == 1) = b -> x = b%:R.
Proof. by case: (F2_cases x) => -> <-. Qed.


(** * Part C. The matrix K and the Selmer equations of a Selmer pair *)
(** * Bits of signs and Legendre symbols *)

Definition bitv (x : int) : 'F_2 := (x != 1)%:R.
Definition pm1 (x : int) : bool := (x == 1) || (x == -1).

Lemma pm1M x y : pm1 x -> pm1 y -> pm1 (x * y).
Proof. by case/orP => /eqP -> /orP [] /eqP ->. Qed.

Lemma bitvM x y : pm1 x -> pm1 y -> bitv (x * y) = bitv x + bitv y.
Proof. by case/orP => /eqP -> /orP [] /eqP ->; apply/eqP. Qed.

Lemma bitv_prod (I : Type) (r : seq I) (P : pred I) (F : I -> int) :
  (forall i, P i -> pm1 (F i)) ->
  bitv (\prod_(i <- r | P i) F i) = \sum_(i <- r | P i) bitv (F i).
Proof.
  move=> H.
  suff : pm1 (\prod_(i <- r | P i) F i) && (bitv (\prod_(i <- r | P i) F i) == \sum_(i <- r | P i) bitv (F i)).
  { by case/andP => _ /eqP. }
  apply: (big_ind2 (fun x y => pm1 x && (bitv x == y))).
  - by rewrite /pm1 /bitv eqxx.
  - move=> x1 x2 y1 y2 /andP [ Hx /eqP <- ] /andP [ Hy /eqP <- ].
    by rewrite (pm1M Hx Hy) (bitvM Hx Hy) eqxx.
  - by move=> i Hi; rewrite H ?eqxx.
Qed.

Lemma bitv_sign (k : nat) : bitv ((-1) ^+ k) = (odd k)%:R.
Proof. by rewrite -signr_odd; case: (odd k); apply/eqP. Qed.

Definition nbit (a : int) (p : nat) : 'F_2 := bitv (legendre a p).

Section nbit.

  Variable p : nat.
  Hypotheses (pP : prime p) (po : odd p).

  Lemma legendre_pm1 a : ~~ (p%:Z %| a)%Z -> pm1 (legendre a p).
  Proof.
    move=> H; have := legendre_sgn3 p a; rewrite /sgn3 -orbA => /orP [ E | // ].
    by move: H; rewrite -(legendre_eq0 pP) E.
  Qed.

  Lemma nbitM a b : ~~ (p%:Z %| a)%Z -> ~~ (p%:Z %| b)%Z -> nbit (a * b) p = nbit a p + nbit b p.
  Proof. by move=> Ha Hb; rewrite /nbit (legendreM pP po) bitvM ?legendre_pm1. Qed.

  Lemma legendre_prod (I : Type) (r : seq I) (P : pred I) (F : I -> int) :
    legendre (\prod_(i <- r | P i) F i) p = \prod_(i <- r | P i) legendre (F i) p.
  Proof. by apply: (big_morph (fun a => legendre a p) (legendreM pP po) (legendre1 p)). Qed.

  Lemma nbit_prod (I : Type) (r : seq I) (P : pred I) (F : I -> int) :
    (forall i, P i -> ~~ (p%:Z %| F i)%Z) ->
    nbit (\prod_(i <- r | P i) F i) p = \sum_(i <- r | P i) nbit (F i) p.
  Proof. by move=> H; rewrite /nbit legendre_prod bitv_prod // => i /H; apply: legendre_pm1. Qed.

  Lemma nbit_eq0 a : ~~ (p%:Z %| a)%Z -> (nbit a p == 0) = (legendre a p == 1).
  Proof.
    move=> H; rewrite /nbit /bitv; case: (legendre a p == 1) => //=.
  Qed.

  Lemma nbitN1 : nbit (-1) p = (odd (p.-1)./2)%:R.
  Proof. by rewrite /nbit (legendre_minus_one pP po) bitv_sign. Qed.

End nbit.

Lemma prime_ndvd (p q : nat) : prime p -> prime q -> p != q -> ~~ (p%:Z %| q%:Z)%Z.
Proof. by move=> pP qP Hpq; rewrite dvdzE /= dvdn_prime2. Qed.

(* reciprocity in bits *)
Lemma qr_bits (p q : nat) : prime p -> prime q -> odd p -> odd q -> p != q ->
  nbit p q + nbit q p = nbit (-1) p * nbit (-1) q.
Proof.
  move=> pP qP po qo Hpq.
  have H1 : pm1 (legendre p q) by apply: (legendre_pm1 qP); apply: prime_ndvd; rewrite // eq_sym.
  have H2 : pm1 (legendre q p) by apply: (legendre_pm1 pP); apply: prime_ndvd.
  rewrite /nbit -(bitvM H1 H2).
  rewrite (quadratic_reciprocity pP qP po qo Hpq) bitv_sign.
  rewrite -/(nbit (-1) p) -/(nbit (-1) q) (nbitN1 pP po) (nbitN1 qP qo) oddM.
  by case: (odd _); case: (odd _); rewrite ?mulr0 ?mulr1.
Qed.

(** * The matrix K of the paper (03-parity.tex, eq. par:matrices)

    Q = supp(l) = [primes |l|], indexed by i < size Q, q_i = nth 0 Q i;
    [a/q] is the nonsquare bit [nbit a q];
    (K u)_i = sum_(j <> i) [q_j/q_i] (u_j + u_i), so K_ij = [q_j/q_i]
    off the diagonal and K_ii = sum_(j <> i) [q_j/q_i];
    s_i = [-1/q_i], lambda_i = [3/q_i]; 1_B the indicator of the primes
    of Q dividing beta. *)

Definition qs (l : int) : seq nat := primes `|l|.
Definition nq (l : int) : nat := size (qs l).
Definition qi (l : int) (i : 'I_(nq l)) : nat := nth 0%N (qs l) i.

Definition Kmx (l : int) : 'M['F_2]_(nq l) :=
  \matrix_(i, j) (if i == j then \sum_(k < nq l | k != i) nbit (qi k) (qi i)
                  else nbit (qi j) (qi i)).
Definition lamv (l : int) : 'cV['F_2]_(nq l) := \col_i nbit 3 (qi i).
Definition sv (l : int) : 'cV['F_2]_(nq l) := \col_i nbit (-1) (qi i).
Definition oneB (l b : int) : 'cV['F_2]_(nq l) := \col_i (((qi i)%:Z %| b)%Z)%:R.

Section Kfacts.

  Variable l : int.
  Hypothesis Hl : admissible_l l.

  Local Abbreviation n := (nq l).
  Local Abbreviation q := (@qi l).

  Lemma l_pos : 0 < l. Proof. by case: Hl. Qed.
  Lemma l_neq0 : l != 0. Proof. by rewrite gt_eqF ?l_pos. Qed.
  Lemma l_mod4 : (l %% 4)%Z = 3. Proof. by case: Hl => _ [ _ [ ] ]. Qed.
  Lemma l_mod3 : (l %% 3)%Z = 2. Proof. by case: Hl => _ [ _ [ ] ]. Qed.
  Lemma l_sqf : sqfree_int l. Proof. by case: Hl => _ [ ]. Qed.
  Lemma l_ndvd2 : ~~ ((2%N)%:Z %| l)%Z. Proof. exact: (ndvd_mod l_mod4). Qed.
  Lemma l_ndvd3 : ~~ ((3%N)%:Z %| l)%Z. Proof. exact: (ndvd_mod l_mod3). Qed.
  Lemma absl_gt0 : (0 < `|l|)%N. Proof. by rewrite absz_gt0 l_neq0. Qed.

  Lemma qi_mem (i : 'I_n) : q i \in primes `|l|.
  Proof. by apply: mem_nth. Qed.

  Lemma qi_prime i : prime (q i).
  Proof. by have := qi_mem i; rewrite mem_primes => /and3P []. Qed.

  Lemma qi_dvd i : (q i %| `|l|)%N.
  Proof. by have := qi_mem i; rewrite mem_primes => /and3P []. Qed.

  Lemma qi_dvdz i : ((q i)%:Z %| l)%Z.
  Proof. by rewrite dvdzE /= qi_dvd. Qed.

  Lemma qi_ne2 i : q i != 2%N.
  Proof. by apply: contra l_ndvd2 => /eqP <-; apply: qi_dvdz. Qed.

  Lemma qi_ne3 i : q i != 3%N.
  Proof. by apply: contra l_ndvd3 => /eqP <-; apply: qi_dvdz. Qed.

  Lemma qi_odd i : odd (q i).
  Proof. by apply/negPn/negP => /(prime_oddPn (qi_prime i)) E; move: (qi_ne2 i); rewrite E. Qed.

  Lemma qi_inj : injective q.
  Proof.
    move=> i j E; apply: val_inj; apply/eqP.
    by rewrite -(nth_uniq 0%N (ltn_ord i) (ltn_ord j) (primes_uniq `|l|)); apply/eqP.
  Qed.

  Lemma logn_l (p : nat) : p \in primes `|l| -> logn p `|l| = 1%N.
  Proof.
    move=> Hp; apply/eqP; rewrite eqn_leq; apply/andP; split; last by rewrite logn_gt0.
    rewrite leqNgt; apply/negP => H.
    have pP : prime p by move: Hp; rewrite mem_primes => /and3P [].
    have := l_sqf (prime_gt1 pP).
    have E : (p * p = p ^ 2)%N by rewrite expnS expn1.
    by rewrite E pfactor_dvdn ?absl_gt0 // H.
  Qed.

  Lemma prod_qi : (\prod_(i < n) q i)%N = absz l.
  Proof.
    rewrite [RHS](prod_prime_decomp absl_gt0) prime_decompE big_map /=.
    rewrite (eq_big_seq (fun p => p)); first by move=> p Hp; rewrite logn_l // expn1.
    by rewrite (big_nth 0%N) big_mkord.
  Qed.

  Lemma prod_qiz : \prod_(i < n) (q i)%:Z = l.
  Proof.
    rewrite -(big_morph Posz PoszM (erefl 1%:Z)) prod_qi gtz0_abs //; exact: l_pos.
  Qed.

  Local Abbreviation one := (const_mx 1 : 'cV['F_2]_n).

  Lemma qi_ndvd (i j : 'I_n) : i != j -> ~~ ((q i)%:Z %| (q j)%:Z)%Z.
  Proof.
    move=> Hij; apply: prime_ndvd; try exact: qi_prime.
    by apply: contra Hij => /eqP /qi_inj ->.
  Qed.

  Lemma HQR_l : Kmx l + (Kmx l)^T = sv l *m (sv l)^T + diag_mx (sv l)^T.
  Proof.
    apply/matrixP => i j; rewrite !mxE big_ord1 !mxE.
    case: (eqVneq i j) => [ <- | Hij ].
      rewrite F2_add_eq0 mulr1n.
      by case: (F2_cases (nbit (-1) (q i))) => ->; apply/eqP.
    - rewrite mulr0n addr0.
      rewrite qr_bits ?qi_prime ?qi_odd //; first by apply/eqP => /qi_inj E; move: Hij; rewrite E eqxx.
      by rewrite mulrC.
  Qed.

  Lemma HK1_l : Kmx l *m one = 0.
  Proof.
    apply/matrixP => i j; rewrite !mxE (bigD1 i) //= !mxE eqxx mulr1.
    rewrite (eq_bigr (fun k => nbit (q k) (q i))).
    { by move=> k Hk; rewrite !mxE eq_sym (negbTE Hk) mulr1. }
    exact: F2_add_eq0.
  Qed.

  Lemma sign_prod : \prod_(i < n) (-1) ^+ ((q i).-1)./2 = (-1) ^+ ((absz l).-1)./2 :> int.
  Proof.
    rewrite -prod_qi.
    suff : odd (\prod_(i < n) q i)%N && (\prod_(i < n) (-1) ^+ ((q i).-1)./2 ==
                                          (-1) ^+ ((\prod_(i < n) q i)%N.-1)./2 :> int).
    { by case/andP => _ /eqP. }
    apply: (big_ind2 (fun (x : int) y => odd y && (x == (-1) ^+ (y.-1)./2))).
    - by [].
    - move=> x1 x2 y1 y2 /andP [ o1 /eqP -> ] /andP [ o2 /eqP -> ].
      by rewrite oddM o1 o2 sign4M ?eqxx.
    - by move=> i _; rewrite qi_odd eqxx.
  Qed.

  Lemma absl_mod4 : (absz l %% 4)%N = 3%N.
  Proof.
    have E : (absz l)%:Z = l by rewrite gtz0_abs // l_pos.
    have : ((absz l)%:Z %% (4%N)%:Z)%Z = (3%N)%:Z by rewrite E; exact: l_mod4.
    by rewrite modz_nat => /eqP; rewrite eqz_nat => /eqP.
  Qed.

  Lemma Hs1_l : (sv l)^T *m one = 1%:M.
  Proof.
    apply/matrixP => i j; rewrite (ord1 i) (ord1 j) !mxE /=.
    rewrite (eq_bigr (fun k => nbit (-1) (q k))); first by move=> k _; rewrite !mxE mulr1.
    rewrite /nbit -bitv_prod.
    { by move=> k _; apply: (legendre_pm1 (qi_prime k)); rewrite dvdzE /= dvdn1; apply/negP => /eqP E; move: (qi_prime k); rewrite E. }
    rewrite (eq_bigr (fun k => (-1) ^+ ((q k).-1)./2)).
    { by move=> k _; rewrite legendre_minus_one ?qi_prime ?qi_odd. }
    rewrite sign_prod bitv_sign.
    have E := divn_eq (absz l) 4; rewrite absl_mod4 in E.
    rewrite E (_ : ((absz l %/ 4) * 4 + 3).-1 = ((absz l %/ 4) * 2 + 1).*2)%N.
    - by rewrite -muln2 mulnDl -mulnA addnS.
    - by rewrite doubleK oddD oddM andbF.
  Qed.

  Lemma n3 : nbit (-1) 3 = 1.
  Proof. by rewrite nbitN1. Qed.

  Lemma nbit_l3 : nbit l 3 = 1.
  Proof.
    have H : (l %% (3%N)%:Z)%Z = 2 := l_mod3.
    rewrite /nbit (@legendre_mod 3 _ l 2) //; last by apply/eqP; rewrite H.
  Qed.

  Lemma sum_s : \sum_(k < n) nbit (-1) (q k) = 1.
  Proof.
    transitivity (((sv l)^T *m one) 0 0).
    { by rewrite !mxE; apply: eq_bigr => k _; rewrite !mxE mulr1. }
    by rewrite Hs1_l mxE.
  Qed.

  Lemma nbit3_q (k : 'I_n) : nbit 3 (q k) = nbit (-1) (q k) + nbit (q k) 3.
  Proof.
    have := @qr_bits 3 (q k) isT (qi_prime k) isT (qi_odd k) ltac:(by rewrite eq_sym qi_ne3).
    rewrite n3 mul1r => <-; rewrite -addrA F2_add_eq0 addr0. done.
  Qed.

  Lemma Hl1_l : (lamv l)^T *m one = 0.
  Proof.
    apply/matrixP => i j; rewrite (ord1 i) (ord1 j) !mxE /=.
    rewrite (eq_bigr (fun k => nbit (-1) (q k) + nbit (q k) 3)).
    { by move=> k _; rewrite !mxE mulr1 nbit3_q. }
    rewrite big_split /= sum_s -(nbit_prod (isT : prime 3) isT).
    - by move=> k _; apply: prime_ndvd; rewrite ?qi_prime // eq_sym qi_ne3.
    - by rewrite prod_qiz nbit_l3; apply/eqP.
  Qed.

End Kfacts.

(** * From local squares to bits *)

Lemma dvd_iz (q : nat) (a : int) : (Z.of_nat q | int_to_Z a)%ZZ <-> ((q%:Z) %| a)%Z.
Proof.
  split.
  - move=> [ k Hk ]; apply/dvdzP; exists (Z_to_int k); apply: iz_inj.
    by rewrite iz_mul iz_Z_to_int iz_nat.
  - move=> /dvdzP [ k -> ]; exists (int_to_Z k); by rewrite iz_mul iz_nat.
Qed.

Lemma qunit_iz (q : nat) (a : int) : ~~ ((q%:Z) %| a)%Z -> qunit q (int_to_Z a).
Proof. by move=> H /dvd_iz H'; move: H; rewrite H'. Qed.

Lemma locsq_legendre (q : nat) (A B : int) : prime q -> odd q -> ~~ (q%:Z %| A)%Z -> ~~ (q%:Z %| B)%Z ->
  locsq q (A%:~R / B%:~R) -> nbit A q + nbit B q = 0.
Proof.
  move=> qP qo HA HB H.
  have q2 : q != 2%N by apply: contraTneq qo => ->.
  have := locsq_rep qP (y := 1) (a := int_to_Z A) (c := int_to_Z B) H (oner_neq0 _) (qunit_iz HA) (qunit_iz HB).
  rewrite !zr_iz expr1n mul1r => /(_ erefl).
  move/(sqmod_odd_prod qP q2 (qunit_iz HA) (qunit_iz HB)) => [ w Hw ].
  have HAB : ~~ (q%:Z %| A * B)%Z by apply: odd_mul.
  have : legendre (A * B) q = 1.
  { apply/(legendre_eq1 qP qo); split => //; exists (Z_to_int w).
    rewrite eqz_mod_dvd -rpredN opprB; apply/dvd_iz.
    rewrite expr2 iz_add iz_opp !iz_mul !iz_Z_to_int; done. }
  by move=> E; rewrite -(nbitM qP qo HA HB) /nbit E.
Qed.

Lemma lsq_bits (q : nat) (A B : int) (e f : bool) : prime q -> odd q ->
  ~~ (q%:Z %| A)%Z -> ~~ (q%:Z %| B)%Z ->
  locsq q (((q ^ e)%:Z * A)%:~R / ((q ^ f)%:Z * B)%:~R) -> e = f /\ nbit A q + nbit B q = 0.
Proof.
  move=> qP qo HA HB H.
  have A0 : A != 0 by apply: contra HA => /eqP ->; rewrite dvdz0.
  have B0 : B != 0 by apply: contra HB => /eqP ->; rewrite dvdz0.
  have Hef : e = f.
  { have [ m Hm ] := locsq_val H.
    move: Hm; rewrite vqr_div ?intr_eq0 ?mulf_neq0 ?pz_neq0 // !vz_rat !vz_pmul // !vz_ndvd // !addn0.
    move/(congr1 int_to_Z); rewrite iz_add iz_opp !iz_add !iz_nat.
    by clear H; case: e; case: f => //= H'; exfalso; lia. }
  split => //; apply: locsq_legendre => //.
  move: H; rewrite Hef !intrM.
  have Hq : (((q ^ f)%:Z)%:~R : rat) != 0 by rewrite intr_eq0 pz_neq0.
  by rewrite -mulf_div divff // mul1r.
Qed.

(** * Integers with even valuations are squares *)

Lemma logn_prodseq (s : seq nat) (e : nat -> nat) (p : nat) : prime p -> all prime s -> uniq s ->
  logn p (\prod_(r <- s) r ^ e r) = if p \in s then e p else 0%N.
Proof.
  move=> pP; elim: s => [ | r s IH ] /=; first by rewrite big_nil logn1.
  move=> /andP [ rP Hs ] /andP [ Hr Hu ].
  have Hpos : (0 < \prod_(x <- s) x ^ e x)%N.
  { rewrite big_seq; apply: prodn_cond_gt0 => x Hx.
    by rewrite expn_gt0 (prime_gt0 (allP Hs x Hx)). }
  have Hr0 : (0 < r ^ e r)%N by rewrite expn_gt0 prime_gt0.
  rewrite big_cons (lognM p Hr0 Hpos) IH // lognX logn_prime // inE.
  case: (eqVneq p r) => [ E | Hpr ] /=.
  - by rewrite -E in Hr; rewrite (negbTE Hr) muln1 addn0 E.
  - by rewrite muln0 add0n.
Qed.

Lemma prodX2 (s : seq nat) (f : nat -> nat) : ((\prod_(x <- s) f x) ^ 2 = \prod_(x <- s) (f x) ^ 2)%N.
Proof. by elim: s => [ | x s IH ]; rewrite ?big_nil ?big_cons // expnMn IH. Qed.

Lemma nat_sq (N : nat) : (0 < N)%N -> (forall p, prime p -> ~~ odd (logn p N)) -> exists m, N = (m ^ 2)%N.
Proof.
  move=> HN Hev.
  exists (\prod_(p <- primes N) p ^ (logn p N)./2)%N.
  rewrite prodX2 {1}(prod_prime_decomp HN) prime_decompE big_map /= big_seq [RHS]big_seq.
  apply: eq_bigr => p; rewrite mem_primes => /and3P [ pP _ _ ].
  by rewrite -expnM -{1}(odd_double_half (logn p N)) (negbTE (Hev p pP)) add0n -muln2.
Qed.



Lemma sqc_of_val (a b : int) : a != 0 -> b != 0 -> 0 < a * b ->
  (forall p, prime p -> ~~ odd (vz p a + vz p b)) -> sqc a%:~R b.
Proof.
  move=> Ha Hb Hab Hv.
  set N := absz (a * b).
  have HN : (0 < N)%N by rewrite absz_gt0 mulf_neq0.
  have HvN : forall p, prime p -> ~~ odd (logn p N) by move=> p pP; rewrite /N -/(vz p _) vzM //; apply: Hv.
  have [ m Hm ] := nat_sq HN HvN.
  have E : a * b = (m%:Z) ^+ 2 by rewrite -(gtz0_abs Hab) -/N Hm expnS expn1 PoszM expr2.
  have Hb' : (b%:~R : rat) != 0 by rewrite intr_eq0.
  have Hm0 : m != 0%N by apply/eqP => E0; move: HN; rewrite Hm E0.
  exists (m%:R / b%:~R); split.
  - by rewrite mulf_neq0 ?invr_eq0 // pnatr_eq0.
  - have : ((a * b)%:~R : rat) = ((m%:Z) ^+ 2)%:~R by rewrite E.
    rewrite intrM rmorphXn /= => Hr.
    have -> : (a%:~R : rat) = (a%:~R * b%:~R) / b%:~R by field.
    rewrite Hr; rewrite (_ : ((m%:Z)%:~R : rat) = m%:R) //; field.
Qed.


(** * Products of the support primes *)

Definition parv (l : int) (d : int) : 'cV['F_2]_(nq l) := \col_i (odd (vz (qi i) d))%:R.
Definition gu (l : int) (u : 'cV['F_2]_(nq l)) : int := \prod_(i < nq l | u i 0 == 1) (qi i)%:Z.
Definition gi (l : int) (i : 'I_(nq l)) (u : 'cV['F_2]_(nq l)) : int :=
  \prod_(j < nq l | (j != i) && (u j 0 == 1)) (qi j)%:Z.

Section Prods.

  Variable l : int.
  Hypothesis Hl : admissible_l l.

  Local Abbreviation n := (nq l).
  Local Abbreviation q := (@qi l).
  Local Abbreviation one := (const_mx 1 : 'cV['F_2]_n).

  Lemma prod_ndvd (p : nat) (P : pred 'I_n) : prime p -> (forall j, P j -> q j != p) ->
    ~~ (p%:Z %| \prod_(j < n | P j) (q j)%:Z)%Z.
  Proof.
    move=> pP H; apply: (big_ind (fun x => ~~ (p%:Z %| x)%Z)).
    - by rewrite dvdz1 /=; apply/negP => /eqP E; move: pP; rewrite E.
    - by move=> x y Hx Hy; apply: odd_mul.
    - by move=> j Hj; apply: prime_ndvd => //; [ exact: qi_prime | rewrite eq_sym; exact: H ].
  Qed.

  Lemma gi_ndvd (i : 'I_n) (u : 'cV['F_2]_n) : ~~ ((q i)%:Z %| gi i u)%Z.
  Proof.
    apply: prod_ndvd; first exact: qi_prime.
    by move=> j /andP [ Hj _ ]; apply/eqP => /qi_inj E; move: Hj; rewrite E eqxx.
  Qed.

  Lemma gu_split (u : 'cV['F_2]_n) (i : 'I_n) : gu u = (expn (q i) (u i 0 == 1))%:Z * gi i u.
  Proof.
    rewrite /gu /gi; case: (eqVneq (u i 0) 1) => Hu.
    - rewrite (bigD1 i) ?Hu //= expn1; congr (_ * _); apply: eq_bigl => j; exact: andbC.
    - rewrite expn0 mul1r; apply: eq_bigl => j; case: (eqVneq j i) => [ -> | // ].
      by rewrite (negbTE Hu).
  Qed.

  Lemma gu_one : gu one = l.
  Proof. by rewrite /gu (eq_bigl xpredT) ?(prod_qiz Hl) // => j; rewrite mxE eqxx. Qed.

  Lemma l_split (i : 'I_n) : l = (q i)%:Z * gi i one.
  Proof. by rewrite -{1}gu_one (gu_split one i) mxE eqxx expn1. Qed.

  Lemma vz_gu_q (u : 'cV['F_2]_n) (i : 'I_n) : vz (q i) (gu u) = (u i 0 == 1).
  Proof.
    have H := gi_ndvd i u.
    have H0 : gi i u != 0 by apply: contra H => /eqP ->; rewrite dvdz0.
    by rewrite (gu_split u i) (vz_pmul (qi_prime i)) // (vz_ndvd H) addn0.
  Qed.

  Lemma vz_gu_out (u : 'cV['F_2]_n) (p : nat) : prime p -> (forall i, q i != p) -> vz p (gu u) = 0%N.
  Proof. by move=> pP H; apply: vz_ndvd; apply: prod_ndvd. Qed.

  Lemma gu_pos (u : 'cV['F_2]_n) : 0 < gu u.
  Proof.
    rewrite /gu big_seq_cond; apply: (big_ind (fun x : int => 0 < x)) => //.
    - by move=> x y; apply: mulr_gt0.
    - by move=> j _; rewrite ltz_nat prime_gt0 ?qi_prime.
  Qed.

  Lemma gi_pos (i : 'I_n) (u : 'cV['F_2]_n) : 0 < gi i u.
  Proof.
    rewrite /gi; apply: (big_ind (fun x : int => 0 < x)) => //.
    - by move=> x y; apply: mulr_gt0.
    - by move=> j _; rewrite ltz_nat prime_gt0 ?qi_prime.
  Qed.

  Lemma nbit_gi (i : 'I_n) (u : 'cV['F_2]_n) :
    nbit (gi i u) (q i) = \sum_(j < n | j != i) u j 0 * nbit (q j) (q i).
  Proof.
    rewrite /gi (nbit_prod (qi_prime i) (qi_odd Hl i)).
    - move=> j /andP [ Hj _ ]; apply: prime_ndvd; try exact: qi_prime.
      by apply/eqP => /qi_inj E; move: Hj; rewrite E eqxx.
    - rewrite big_mkcondr /=; apply: eq_bigr => j _.
      by case: (F2_cases (u j 0)) => ->; rewrite ?mul0r ?mul1r.
  Qed.

  Lemma Kii (i : 'I_n) : Kmx l i i = nbit (gi i one) (q i).
  Proof. by rewrite mxE eqxx nbit_gi; apply: eq_bigr => j _; rewrite mxE mul1r. Qed.

  Lemma K_mul (u : 'cV['F_2]_n) (i : 'I_n) :
    (Kmx l *m u) i 0 = u i 0 * nbit (gi i one) (q i) + nbit (gi i u) (q i).
  Proof.
    rewrite !mxE (bigD1 i) //= -Kii mulrC nbit_gi; congr (_ + _).
    by apply: eq_bigr => j Hj; rewrite mxE eq_sym (negbTE Hj) mulrC.
  Qed.

End Prods.

(** * The Selmer equations of a pair satisfying the local conditions *)

Definition ltors (q : nat) (l d1 d2 : int) : Prop :=
  let x1 := (d1%:~R : rat) in let x2 := (d2%:~R : rat) in let lr := (l%:~R : rat) in
    (locsq q x1 /\ locsq q x2) \/
    (locsq q (x1 / lr) /\ locsq q x2) \/
    (locsq q (x1 / (- (3 * lr))) /\ locsq q (x2 / (- lr))) \/
    (locsq q (x1 / (- 3)) /\ locsq q (x2 / (- lr))).

Lemma lsq_sqc (q : nat) (x : rat) (g : int) (t : rat) : prime q -> sqc x g ->
  locsq q (x / t) -> locsq q (g%:~R / t).
Proof.
  move=> qP [ s [ Hs -> ] ] H.
  have Hs2 : s ^+ 2 != 0 by rewrite expf_neq0.
  have E : g%:~R * s ^+ 2 / t = (g%:~R / t) * s ^+ 2 by rewrite mulrAC.
  rewrite -(mulfK Hs2 (g%:~R / t)) -E.
  by apply: (locsq_div qP) => //; apply: locsq_sq.
Qed.

Section SelBits.

  Variable l : int.
  Hypothesis Hl : admissible_l l.
  Local Abbreviation n := (nq l).
  Local Abbreviation q := (@qi l).
  Local Abbreviation one := (const_mx 1 : 'cV['F_2]_n).

  Variables d1 d2 : int.
  Hypotheses (Hd1 : d1 != 0) (Hd2 : d2 != 0) (Hpos : 0 < d1 * d2).
  Hypothesis Hq : forall i : 'I_n, ltors (q i) l d1 d2.
  Hypothesis H3 : locsq 3 d2%:~R.
  Hypothesis Hev : forall p, prime p -> (forall i, q i != p) -> p != 3%N ->
    ~~ odd (vz p d1) /\ ~~ odd (vz p d2).

  Local Abbreviation u1 := (parv l d1).
  Local Abbreviation v := (parv l d2).
  Definition dl : 'F_2 := (odd (vz 3 d1))%:R.
  Definition sg : 'F_2 := if d1 < 0 then 1 else 0.
  Definition sgd : int := sgz d1.
  Definition rep1 : int := sgd * 3 ^+ (odd (vz 3 d1)) * gu u1.
  Definition rep2 : int := sgd * gu v.

  Lemma sgz_d2 : sgz d2 = sgd.
  Proof.
    rewrite /sgd; move: Hpos; rewrite -sgz_gt0 sgzM.
    by case: (sgzP d1); case: (sgzP d2).
  Qed.

  Lemma sgd_pm : (sgd == 1) || (sgd == -1).
  Proof. by rewrite /sgd; move: Hd1; case: (sgzP d1). Qed.

  Lemma sgd_ndvd (p : nat) : prime p -> ~~ (p%:Z %| sgd)%Z.
  Proof.
    move=> pP; case/orP: sgd_pm => /eqP ->; rewrite ?rpredN dvdz1 /=;
      apply/negP => /eqP E; by move: pP; rewrite E.
  Qed.

  Lemma vz_sgd (p : nat) : prime p -> vz p sgd = 0%N.
  Proof. by move=> pP; apply: vz_ndvd; apply: sgd_ndvd. Qed.

  Lemma F2b (b : bool) : ((b%:R : 'F_2) == 1) = b.
  Proof. by case: b => //=; rewrite eq_sym oner_eq0. Qed.

  Lemma parvE (d : int) (i : 'I_n) : (parv l d i 0 == 1) = odd (vz (q i) d).
  Proof. by rewrite mxE F2b. Qed.

  Lemma vz_3pow (p : nat) (b : bool) : vz p (3 ^+ b) = if b then vz p 3 else 0%N.
  Proof. by case: b => /=; rewrite ?expr1 ?expr0 // /vz /= logn1. Qed.

  Lemma sgd_neq0 : sgd != 0.
  Proof. by rewrite /sgd sgz_eq0. Qed.

  Lemma rep1_neq0 : rep1 != 0.
  Proof. by rewrite /rep1 !mulf_neq0 ?sgd_neq0 ?expf_neq0 ?(lt0r_neq0 (gu_pos _)). Qed.

  Lemma rep2_neq0 : rep2 != 0.
  Proof. by rewrite /rep2 !mulf_neq0 ?sgd_neq0 ?(lt0r_neq0 (gu_pos _)). Qed.

  Lemma d1_sgd : 0 < d1 * sgd.
  Proof. by rewrite /sgd; move: Hd1; case: (sgzP d1) => // H _; rewrite ?mulr1 ?mulrN1 ?oppr_gt0. Qed.

  Lemma rep_sqc1 : sqc d1%:~R rep1.
  Proof.
    apply: sqc_of_val => //; first exact: rep1_neq0.
    - rewrite /rep1 !mulrA; apply: mulr_gt0; last exact: gu_pos.
      by apply: mulr_gt0; [ exact: d1_sgd | exact: exprn_gt0 ].
    - move=> p pP; rewrite /rep1 !vzM ?mulf_neq0 ?sgd_neq0 ?expf_neq0 ?(lt0r_neq0 (gu_pos _)) // vz_sgd // add0n vz_3pow.
      case: (pickP (fun i => q i == p)) => [ i /eqP Hi | Hn ].
      + rewrite -Hi vz_gu_q // parvE vz3 ?qi_prime ?(qi_ne3 Hl) // if_same add0n.
        by rewrite oddD oddb addbb.
      + have Hn' : forall i, q i != p by move=> i; rewrite Hn.
        rewrite vz_gu_out // addn0.
        case: (eqVneq p 3%N) => [ -> | H3p ].
        * have E33 : vz 3 3 = 1%N by []. rewrite E33.
          by case E: (odd (vz 3 d1)); rewrite oddD E.
        * have [ E _ ] := Hev pP Hn' H3p.
          by rewrite vz3 // if_same addn0.
  Qed.

  Lemma vz3_d2 : ~~ odd (vz 3 d2).
  Proof.
    have [ m Hm ] := locsq_val H3; move: Hm; rewrite vz_rat => /(congr1 int_to_Z).
    rewrite iz_add iz_nat; move=> E; apply/negP => /oddE [ h Hh ]; move: E; rewrite Hh.
    rewrite !Nat2Z.inj_add; lia.
  Qed.

  Lemma rep_sqc2 : sqc d2%:~R rep2.
  Proof.
    apply: sqc_of_val => //; first exact: rep2_neq0.
    - rewrite /rep2 mulrA; apply: mulr_gt0; last exact: gu_pos.
      by rewrite -sgz_d2 /sgd; move: Hd2; case: (sgzP d2) => // H _; rewrite ?mulr1 ?mulrN1 ?oppr_gt0.
    - move=> p pP; rewrite /rep2 !vzM ?sgd_neq0 ?(lt0r_neq0 (gu_pos _)) // vz_sgd // add0n.
      case: (pickP (fun i => q i == p)) => [ i /eqP Hi | Hn ].
      + by rewrite -Hi vz_gu_q // parvE oddD oddb addbb.
      + have Hn' : forall i, q i != p by move=> i; rewrite Hn.
        rewrite vz_gu_out // addn0.
        case: (eqVneq p 3%N) => [ -> | H3p ]; first exact: vz3_d2.
        by have [ _ E ] := Hev pP Hn' H3p.
  Qed.

  Section row.

    Variable i : 'I_n.
    Local Abbreviation Q := (q i).
    Let QP : prime Q. Proof. exact: qi_prime. Qed.
    Let QO : odd Q. Proof. exact: qi_odd. Qed.
    Let Q3 : Q != 3%N. Proof. exact: qi_ne3. Qed.
    Let L := gi i one.
    Let A1 := sgd * 3 ^+ (odd (vz 3 d1)) * gi i u1.
    Let A2 := sgd * gi i v.

    Let ndQ3 : ~~ (Q%:Z %| 3)%Z.
    Proof. by apply: (prime_ndvd QP (isT : prime 3)). Qed.
    Let ndQm1 : ~~ (Q%:Z %| -1)%Z.
    Proof. by rewrite dvdzE /= dvdn1; apply/negP => /eqP E; move: QP; rewrite E. Qed.
    Let ndQ3p : ~~ (Q%:Z %| 3 ^+ (odd (vz 3 d1)))%Z.
    Proof. by case: (odd _); rewrite ?expr1 ?expr0 //; rewrite dvdz1 /=; apply/negP => /eqP E; move: QP; rewrite E. Qed.
    Let ndL : ~~ (Q%:Z %| L)%Z. Proof. exact: gi_ndvd. Qed.
    Let ndA1 : ~~ (Q%:Z %| A1)%Z.
    Proof. exact: (odd_mul QP (odd_mul QP (sgd_ndvd QP) ndQ3p) (gi_ndvd _ _)). Qed.
    Let ndA2 : ~~ (Q%:Z %| A2)%Z.
    Proof. exact: (odd_mul QP (sgd_ndvd QP) (gi_ndvd _ _)). Qed.

    Lemma nbit_sgd : nbit sgd Q = sg * sv l i 0.
    Proof.
      rewrite mxE /sg /sgd; move: Hd1; case: (sgzP d1) => // H _.
      - by rewrite ?(lt_gtF H) mul0r /nbit legendre1 /bitv eqxx.
      - by rewrite ?H mul1r.
    Qed.

    Lemma nbit_A1 : nbit A1 Q = sg * sv l i 0 + dl * lamv l i 0 + nbit (gi i u1) Q.
    Proof.
      rewrite /A1 (nbitM QP QO (odd_mul QP (sgd_ndvd QP) ndQ3p) (gi_ndvd _ _)).
      rewrite (nbitM QP QO (sgd_ndvd QP) ndQ3p) nbit_sgd /dl mxE; congr (_ + _ + _).
      by case: (odd _) => /=; rewrite mxE ?expr1 ?expr0 ?mul1r ?mul0r // /nbit legendre1 /bitv eqxx.
    Qed.

    Lemma nbit_A2 : nbit A2 Q = sg * sv l i 0 + nbit (gi i v) Q.
    Proof. by rewrite /A2 (nbitM QP QO (sgd_ndvd QP) (gi_ndvd _ _)) nbit_sgd. Qed.

    Lemma nbitN (x : int) : ~~ (Q%:Z %| x)%Z -> nbit (- x) Q = sv l i 0 + nbit x Q.
    Proof. by move=> Hx; rewrite -mulN1r (nbitM QP QO) // mxE. Qed.

    Let ndQ3L : ~~ (Q%:Z %| 3 * L)%Z. Proof. exact: odd_mul. Qed.

    Lemma row_eqs :
      (Kmx l *m u1) i 0 + dl * lamv l i 0 + (sv l i 0 + lamv l i 0) * v i 0 + sg * sv l i 0 = 0 /\
      (Kmx l *m v) i 0 + sv l i 0 * v i 0 + sg * sv l i 0 = 0.
    Proof.
      have Er1 : rep1 = (expn Q (u1 i 0 == 1))%:Z * A1.
      { rewrite /rep1 (gu_split u1 i) /A1.
        move: (expn _ _)%:Z (gi i u1) (3 ^+ _) => X Y Z; by rewrite mulrCA mulrA. }
      have Er2 : rep2 = (expn Q (v i 0 == 1))%:Z * A2.
      { rewrite /rep2 (gu_split v i) /A2; by rewrite mulrCA. }
      have El : l = (expn Q true)%:Z * L by rewrite expn1 /L -(l_split Hl i).
      have T1 : (1 : rat) = ((expn Q false)%:Z * 1)%:~R by rewrite expn0 mul1r.
      have Tl : (l%:~R : rat) = ((expn Q true)%:Z * L)%:~R by rewrite -El.
      have T3l : (- (3 * l%:~R) : rat) = ((expn Q true)%:Z * (- (3 * L)))%:~R.
      { by rewrite [in LHS]El !rmorphM /= rmorphN /= rmorphM /= rmorphMn rmorph1 mulrN mulrCA. }
      have T3 : (- 3 : rat) = ((expn Q false)%:Z * (- 3))%:~R.
      { by rewrite expn0 mul1r rmorphN rmorphMn rmorph1. }
      have Tml : (- l%:~R : rat) = ((expn Q true)%:Z * (- L))%:~R.
      { by rewrite [in LHS]El !rmorphM /= rmorphN /= mulrN. }
      have Hr1 := lsq_sqc QP rep_sqc1; have Hr2 := lsq_sqc QP rep_sqc2.
      rewrite Er1 in Hr1; rewrite Er2 in Hr2.
      have nL : nbit L Q = nbit (gi i one) Q by [].
      have n3L : nbit (- (3 * L)) Q = sv l i 0 + lamv l i 0 + nbit L Q.
      { by rewrite nbitN // (nbitM QP QO) // [lamv _ _ _]mxE addrA. }
      have n3 : nbit (- 3) Q = sv l i 0 + lamv l i 0 by rewrite nbitN // [lamv _ _ _]mxE.
      have nmL : nbit (- L) Q = sv l i 0 + nbit L Q by rewrite nbitN.
      have n1 : nbit 1 Q = 0 by rewrite /nbit legendre1 /bitv eqxx.
      rewrite !(K_mul Hl) -/L.
      suff [ H1 H2 ] : nbit A1 Q + (v i 0 * (sv l i 0 + lamv l i 0) + u1 i 0 * nbit L Q) == 0 /\
                       nbit A2 Q + v i 0 * (sv l i 0 + nbit L Q) == 0.
      { move: H1 H2; rewrite nbit_A1 nbit_A2 => H1 H2.
        by case/andP: (f2_rows H1 H2) => A B; split; apply/eqP; [ exact: A | exact: B ]. }
      have get1 : forall (f : bool) (B : int) (t : rat), ~~ (Q%:Z %| B)%Z ->
          t = ((expn Q f)%:Z * B)%:~R -> locsq Q (d1%:~R / t) -> u1 i 0 = f%:R /\ nbit A1 Q + nbit B Q = 0.
      { move=> f B t HB Et H; have := Hr1 _ H; rewrite Et => /(lsq_bits QP QO ndA1 HB) [ E H' ].
        by split => //; apply: F2_of_eq. }
      have get2 : forall (f : bool) (B : int) (t : rat), ~~ (Q%:Z %| B)%Z ->
          t = ((expn Q f)%:Z * B)%:~R -> locsq Q (d2%:~R / t) -> v i 0 = f%:R /\ nbit A2 Q + nbit B Q = 0.
      { move=> f B t HB Et H; have := Hr2 _ H; rewrite Et => /(lsq_bits QP QO ndA2 HB) [ E H' ].
        by split => //; apply: F2_of_eq. }
      have nd1 : ~~ (Q%:Z %| 1)%Z by rewrite dvdz1 /=; apply/negP => /eqP E; move: QP; rewrite E.
      have ndm3L : ~~ (Q%:Z %| - (3 * L))%Z by rewrite rpredN.
      have ndm3 : ~~ (Q%:Z %| - 3)%Z by move: ndQ3; rewrite !dvdzE ?abszN.
      have ndmL : ~~ (Q%:Z %| - L)%Z by rewrite rpredN.
      have Hq' := Hq i; rewrite /ltors in Hq'.
      case: Hq' => [ [ A B ] | [ [ A B ] | [ [ A B ] | [ A B ] ] ] ].
      - move: A B; rewrite -[d1%:~R]divr1 -[d2%:~R]divr1 => A B.
        have [ Eu Hu ] := get1 false 1 1 nd1 T1 A; have [ Ev Hv ] := get2 false 1 1 nd1 T1 B.
        rewrite Eu Ev /= !mul0r !addr0; rewrite n1 !addr0 in Hu Hv.
        by rewrite Hu Hv.
      - move: B; rewrite -[d2%:~R]divr1 => B.
        have [ Eu Hu ] := get1 true L _ ndL Tl A; have [ Ev Hv ] := get2 false 1 1 nd1 T1 B.
        rewrite Eu Ev /= !mul0r mul1r add0r !addr0 Hu; rewrite n1 addr0 in Hv; by rewrite Hv.
      - have [ Eu Hu ] := get1 true _ _ ndm3L T3l A; have [ Ev Hv ] := get2 true _ _ ndmL Tml B.
        rewrite Eu Ev /= !mul1r; rewrite n3L in Hu; rewrite nmL in Hv.
        by rewrite Hu Hv.
      - have [ Eu Hu ] := get1 false _ _ ndm3 T3 A; have [ Ev Hv ] := get2 true _ _ ndmL Tml B.
        rewrite Eu Ev /= !mul1r mul0r addr0; rewrite n3 in Hu; rewrite nmL in Hv.
        by rewrite Hu Hv.
    Qed.


  End row.
  Lemma nbitq3 (j : 'I_n) : nbit (q j) 3 = lamv l j 0 + sv l j 0.
  Proof.
    have := nbit3_q Hl j; rewrite !mxE.
    move: (nbit 3 (q j)) (nbit (-1) (q j)) (nbit (q j) 3) => a b c ->.
    by apply/eqP; case: (F2_cases b) => ->; case: (F2_cases c) => ->.
  Qed.

  Lemma S3_eq : \sum_(j < n) (lamv l j 0 + sv l j 0) * v j 0 + sg = 0.
  Proof.
    have Hr := lsq_sqc (isT : prime 3) rep_sqc2 (t := 1); rewrite !divr1 in Hr.
    have nd : ~~ ((3%N)%:Z %| gu v)%Z.
    { apply: prod_ndvd => // j _; exact: qi_ne3. }
    have ndr : ~~ ((3%N)%:Z %| rep2)%Z by apply: odd_mul => //; apply: sgd_ndvd.
    have := @locsq_legendre 3 rep2 1 isT isT ndr ltac:(by []) ltac:(by rewrite divr1; apply: Hr).
    have n13 : nbit 1 3 = 0 by rewrite /nbit legendre1 /bitv eqxx.
    rewrite n13 addr0 /rep2 (nbitM (isT : prime 3) isT) ?sgd_ndvd //.
    rewrite /gu (nbit_prod (isT : prime 3) isT); first by move=> j _; apply: prime_ndvd => //; [ exact: qi_prime | rewrite eq_sym; exact: qi_ne3 ].
    have -> : nbit sgd 3 = sg.
    { by rewrite /sg /sgd; move: Hd1; case: (sgzP d1). }
    rewrite big_mkcond /= => E; rewrite -[RHS]E addrC; congr (_ + _).
    apply: eq_bigr => j _; rewrite nbitq3.
    by case: (F2_cases (v j 0)) => ->; rewrite ?mulr0 ?mulr1.
  Qed.

  Variable beta : int.
  Hypothesis Hker : forall u : 'cV['F_2]_n, Kmx l *m u = 0 ->
    u = 0 \/ u = one \/ u = oneB l beta \/ u = one + oneB l beta.
  Hypothesis Hlam : forall u : 'cV['F_2]_n, Kmx l *m u != lamv l.

  Theorem sel_classes : v = sg *: one /\ dl = sg /\ Kmx l *m u1 = 0.
  Proof.
    have Hs1 := Hs1_l Hl; have Hl1 := Hl1_l Hl; have HQR := HQR_l Hl; have HK1 := HK1_l l.
    apply: (linalg Hker Hlam Hs1 Hl1 (HKt1' Hs1 HQR HK1) HQR HK1).
    - apply/matrixP => i j; rewrite (ord1 j) mul_diag_mx.
      have [ E _ ] := row_eqs i; move: E; rewrite !mxE; by move=> ->.
    - apply/matrixP => i j; rewrite (ord1 j) mul_diag_mx.
      have [ _ E ] := row_eqs i; move: E; rewrite !mxE; by move=> ->.
    - apply/matrixP => i j; rewrite (ord1 i) (ord1 j) !mxE /= mulr1n -[RHS]S3_eq.
      by congr (_ + _); apply: eq_bigr => k _; rewrite !mxE.
  Qed.

End SelBits.


(** * Part D. The upper bound, and gamma outside the span of the torsion classes *)
Lemma sqc_trans (x : rat) (g h : int) : sqc x g -> sqc g%:~R h -> sqc x h.
Proof.
  move=> [ s [ Hs -> ] ] [ r [ Hr -> ] ]; exists (r * s); split; first by rewrite mulf_neq0.
  by rewrite exprMn mulrA.
Qed.

Lemma sqc_refl (g : int) : sqc g%:~R g.
Proof. by exists 1; rewrite expr1n mulr1 oner_eq0. Qed.

Section Upper.

  Variable l : int.
  Hypothesis Hl : admissible_l l.
  Local Abbreviation n := (nq l).
  Local Abbreviation q := (@qi l).
  Local Abbreviation one := (const_mx 1 : 'cV['F_2]_n).

  Variable beta : int.
  Hypotheses (Hb0 : 0 < beta) (Hbl : (beta %| l)%Z).

  Lemma notin_qs (p : nat) : prime p -> (forall j, q j != p) -> ~~ (p %| absz l)%N.
  Proof.
    move=> pP H; apply/negP => Hd.
    have Hm : p \in primes (absz l) by rewrite mem_primes pP absl_gt0 // Hd.
    have := Hm; rewrite -index_mem => Hi.
    by move: (H (Ordinal Hi)); rewrite /qi /= nth_index // eqxx.
  Qed.

  Lemma vz_l_q (j : 'I_n) : vz (q j) l = 1%N.
  Proof. exact: (logn_l Hl (qi_mem j)). Qed.

  Lemma vz_l_out (p : nat) : prime p -> (forall j, q j != p) -> vz p l = 0%N.
  Proof. by move=> pP H; rewrite /vz logn_ndvd // notin_qs. Qed.

  Lemma b_neq0 : beta != 0. Proof. by rewrite gt_eqF. Qed.

  Lemma vz_b_q (j : 'I_n) : vz (q j) beta = (oneB l beta j 0 == 1).
  Proof.
    rewrite mxE F2b.
    have Hle : (vz (q j) beta <= 1)%N.
    { rewrite -(vz_l_q j) /vz; apply: dvdn_leq_log; first exact: absl_gt0.
      by move: Hbl; rewrite dvdzE. }
    case Hd : ((q j)%:Z %| beta)%Z.
    - apply/eqP; rewrite eqn_leq Hle /= /vz logn_gt0 mem_primes qi_prime absz_gt0 b_neq0 /=.
      by move: Hd; rewrite dvdzE.
    - by rewrite vz_ndvd ?Hd.
  Qed.

  Lemma vz_b_out (p : nat) : prime p -> (forall j, q j != p) -> vz p beta = 0%N.
  Proof.
    move=> pP H; apply: vz_ndvd; apply/negP => Hd.
    by move: (dvdz_trans Hd Hbl); rewrite dvdzE /=; apply/negP; exact: notin_qs pP H.
  Qed.

  Lemma sqc_gu (c : int) (u : 'cV['F_2]_n) (g : int) : c != 0 -> 0 < g ->
    (forall j, odd (vz (q j) g) = (u j 0 == 1)) ->
    (forall p, prime p -> (forall j, q j != p) -> ~~ odd (vz p g)) ->
    sqc (c * gu u)%:~R (c * g).
  Proof.
    move=> Hc Hg Hq Hp.
    have Hgu := gu_pos u.
    apply: sqc_of_val; rewrite ?mulf_neq0 ?(lt0r_neq0 Hgu) ?(lt0r_neq0 Hg) //.
    - rewrite mulrACA; apply: mulr_gt0; last exact: mulr_gt0.
      by rewrite -expr2 exprn_even_gt0 // Hc orbT.
    - move=> p pP; rewrite !vzM ?(lt0r_neq0 Hgu) ?(lt0r_neq0 Hg) //.
      rewrite !oddD; have -> : forall a b e : bool, (a (+) b) (+) (a (+) e) = b (+) e by do 3 case.
      case: (pickP (fun j => q j == p)) => [ j /eqP <- | Hn ].
      + by rewrite vz_gu_q Hq oddb addbb.
      + have Hn' : forall j, q j != p by move=> j; rewrite Hn.
        by rewrite vz_gu_out // /= (negbTE (Hp p pP Hn')).
  Qed.

  Lemma odd_l j : odd (vz (q j) l) = true.
  Proof. by rewrite vz_l_q. Qed.

  Lemma vz_lb (j : 'I_n) : vz (q j) (l * beta) = addn 1 (oneB l beta j 0 == 1).
  Proof. by rewrite (vzM _ (l_neq0 Hl) b_neq0) vz_l_q vz_b_q. Qed.

  Lemma vz_ll (j : 'I_n) : vz (q j) (l * l) = 2%N.
  Proof. by rewrite (vzM _ (l_neq0 Hl) (l_neq0 Hl)) vz_l_q. Qed.

  Lemma vz_llb (j : 'I_n) : vz (q j) (l * l * beta) = addn 2 (oneB l beta j 0 == 1).
  Proof. by rewrite (vzM _ (mulf_neq0 (l_neq0 Hl) (l_neq0 Hl)) b_neq0) vz_ll vz_b_q. Qed.

  Lemma out_l p : prime p -> (forall j, q j != p) -> ~~ odd (vz p l).
  Proof. by move=> pP H; rewrite vz_l_out. Qed.

  Lemma out_b p : prime p -> (forall j, q j != p) -> ~~ odd (vz p beta).
  Proof. by move=> pP H; rewrite vz_b_out. Qed.

  Lemma out_lb p : prime p -> (forall j, q j != p) -> ~~ odd (vz p (l * beta)).
  Proof. by move=> pP H; rewrite (vzM _ (l_neq0 Hl) b_neq0) vz_l_out ?vz_b_out. Qed.

  Lemma out_ll p : prime p -> (forall j, q j != p) -> ~~ odd (vz p (l * l)).
  Proof. by move=> pP H; rewrite (vzM _ (l_neq0 Hl) (l_neq0 Hl)) vz_l_out. Qed.

  Lemma out_llb p : prime p -> (forall j, q j != p) -> ~~ odd (vz p (l * l * beta)).
  Proof.
    by move=> pP H; rewrite (vzM _ (mulf_neq0 (l_neq0 Hl) (l_neq0 Hl)) b_neq0)
      (vzM _ (l_neq0 Hl) (l_neq0 Hl)) vz_l_out ?vz_b_out.
  Qed.

  Lemma out_1 p : prime p -> (forall j, q j != p) -> ~~ odd (vz p 1).
  Proof. by move=> pP H; rewrite /vz logn1. Qed.

  Lemma oneE (j : 'I_n) : (one j 0 == 1) = true. Proof. by rewrite mxE. Qed.
  Lemma zeroE (j : 'I_n) : ((0 : 'cV['F_2]_n) j 0 == 1) = false. Proof. by rewrite mxE. Qed.
  Lemma oneBE (j : 'I_n) : ((one + oneB l beta) j 0 == 1) = ~~ (oneB l beta j 0 == 1).
  Proof. by rewrite [X in X == _]mxE [X in X + _]mxE; case: (F2_cases (oneB l beta j 0)) => ->. Qed.

  Lemma gu0 : gu (0 : 'cV['F_2]_n) = 1.
  Proof. by rewrite /gu big_pred0 // => j; rewrite mxE. Qed.

  Lemma l_pos' : 0 < l. Proof. exact: l_pos Hl. Qed.

  Lemma good_hyp (d1 d2 : int) : d1 != 0 -> d2 != 0 -> (forall p, prime p -> locsol l p (d1, d2)) ->
    forall p, prime p -> (forall i, q i != p) -> p != 3%N -> ~~ odd (vz p d1) /\ ~~ odd (vz p d2).
  Proof.
    move=> H1 H2 Hloc p pP Hn H3.
    case: (eqVneq p 2%N) => [ -> | H2p ].
    - exact: two_even (l_mod4 Hl) H1 H2 (Hloc 2%N isT).
    - apply: (good_even pP H2p H3 _ (l_neq0 Hl) H1 H2 (Hloc p pP)).
      by rewrite dvdzE /=; apply: notin_qs.
  Qed.

  Hypothesis Hker : forall u : 'cV['F_2]_n, Kmx l *m u = 0 ->
    u = 0 \/ u = one \/ u = oneB l beta \/ u = one + oneB l beta.
  Hypothesis Hlam : forall u : 'cV['F_2]_n, Kmx l *m u != lamv l.

  Theorem upper_bound (d : int * int) : in_Sel2 l d ->
    in_span3 (tors_Tl l) (tors_T3 l) (beta, 1) d.
  Proof.
    case: d => d1 d2 [ H1 [ H2 [ Hinf Hloc ] ] ] /=; rewrite /= in H1 H2.
    have Hpos := inf_pos l_pos' Hinf.
    have Hq : forall i, ltors (q i) l d1 d2.
    { move=> i; exact: (l_tors (qi_prime i) (qi_ne2 Hl i) (qi_ne3 Hl i) (vz_l_q i) H1 H2 (Hloc _ (qi_prime i))). }
    have H3 := three_sq (l_mod3 Hl) H1 H2 (Hloc 3%N isT).
    have Hev := good_hyp H1 H2 Hloc.
    have [ Hv [ Hdl HKu ] ] := sel_classes Hl H1 H2 Hpos Hq H3 Hev Hker Hlam.
    have R1 := rep_sqc1 Hl H1 Hev; have R2 := rep_sqc2 H1 H2 Hpos H3 Hev.
    move: Hv Hdl R1 R2; rewrite /rep1 /rep2 /dl /sg /sgd.
    have Hl0 := l_neq0 Hl.
    have Hll : 0 < l * l by rewrite mulr_gt0 ?l_pos'.
    have Hlb : 0 < l * beta by rewrite mulr_gt0 ?l_pos'.
    have Hllb : 0 < l * l * beta by rewrite !mulr_gt0 ?l_pos'.
    have m3 : (- 3 : int) != 0 by [].
    case Hneg : (d1 < 0).
    - rewrite (ltr0_sgz Hneg) scale1r => -> /eqP; rewrite F2b => -> R1 R2.
      rewrite (gu_one Hl) in R2.
      have R1' : sqc d1%:~R ((- 3) * gu (parv l d1)).
      { move: R1; rewrite expr1 (_ : -1 * 3 = - 3) //; by rewrite mulN1r. }
      have R2' : sqc d2%:~R (- l) by move: R2; rewrite mulN1r.
      case: (Hker HKu) => [ E | [ E | [ E | E ] ] ]; rewrite E in R1'.
      + exists true, true, false; rewrite /psq /pmul /ppow /tors_Tl /tors_T3 /=; split.
        * apply: (sqc_trans R1'); have -> : l * (- (3 * l) * 1) = (- 3) * (l * l) by ring.
          apply: sqc_gu => // j; first by rewrite vz_ll zeroE.
          exact: out_ll.
        * by rewrite mul1r mulr1.
      + exists false, true, false; rewrite /psq /pmul /ppow /tors_Tl /tors_T3 /=; split.
        * apply: (sqc_trans R1'); have -> : 1 * (- (3 * l) * 1) = (- 3) * l by ring.
          apply: sqc_gu => //; [ exact: l_pos' | move=> j; by rewrite odd_l oneE | exact: out_l ].
        * by rewrite mul1r mulr1.
      + exists true, true, true; rewrite /psq /pmul /ppow /tors_Tl /tors_T3 /=; split.
        * apply: (sqc_trans R1'); have -> : l * (- (3 * l) * beta) = (- 3) * (l * l * beta) by ring.
          apply: sqc_gu => // j; first by rewrite vz_llb oddD oddb.
          exact: out_llb.
        * by rewrite mul1r mulr1.
      + exists false, true, true; rewrite /psq /pmul /ppow /tors_Tl /tors_T3 /=; split.
        * apply: (sqc_trans R1'); have -> : 1 * (- (3 * l) * beta) = (- 3) * (l * beta) by ring.
          apply: sqc_gu => // j; first by rewrite vz_lb oneBE oddD oddb.
          exact: out_lb.
        * by rewrite mul1r mulr1.
    - have Hp : 0 < d1 by rewrite lt_neqAle eq_sym H1 /= leNgt Hneg.
      have F2b0 : forall b : bool, ((b%:R : 'F_2) == 0) = ~~ b by case => //=; rewrite oner_eq0.
      rewrite (gtr0_sgz Hp) scale0r => -> /eqP; rewrite F2b0 => /negbTE -> R1 R2.
      rewrite gu0 in R2.
      have R1' : sqc d1%:~R (1 * gu (parv l d1)) by move: R1; rewrite expr0 mulr1.
      have R2' : sqc d2%:~R 1 by move: R2; rewrite mulr1.
      case: (Hker HKu) => [ E | [ E | [ E | E ] ] ]; rewrite E in R1'.
      + exists false, false, false; rewrite /psq /pmul /ppow /tors_Tl /tors_T3 /=; split.
        * apply: (sqc_trans R1'); have -> : 1 * (1 * 1) = 1 * (1 : int) by [].
          apply: sqc_gu => // j; first by rewrite /vz logn1 zeroE.
          exact: out_1.
        * by rewrite !mulr1.
      + exists true, false, false; rewrite /psq /pmul /ppow /tors_Tl /tors_T3 /=; split.
        * apply: (sqc_trans R1'); have -> : l * (1 * 1) = 1 * l by rewrite !mulr1 mul1r.
          apply: sqc_gu => //; [ exact: l_pos' | move=> j; by rewrite odd_l oneE | exact: out_l ].
        * by rewrite !mulr1.
      + exists false, false, true; rewrite /psq /pmul /ppow /tors_Tl /tors_T3 /=; split.
        * apply: (sqc_trans R1'); have -> : 1 * (1 * beta) = 1 * beta by rewrite mul1r.
          apply: sqc_gu => // j; first by rewrite vz_b_q oddb.
          exact: out_b.
        * by rewrite !mulr1.
      + exists true, false, true; rewrite /psq /pmul /ppow /tors_Tl /tors_T3 /=; split.
        * apply: (sqc_trans R1'); have -> : l * (1 * beta) = 1 * (l * beta) by rewrite !mul1r.
          apply: sqc_gu => // j; first by rewrite vz_lb oneBE oddD oddb.
          exact: out_lb.
        * by rewrite !mulr1.
  Qed.

  Lemma sqc_val (a b : int) : a != 0 -> b != 0 -> sqc a%:~R b -> forall p, prime p -> ~~ odd (vz p a + vz p b).
  Proof.
    move=> Ha Hb [ t [ Ht E ] ] p pP.
    have := congr1 (vqr p) E; rewrite vqrM ?intr_eq0 ?expf_neq0 // vqrX2 // !vz_rat.
    move/(congr1 int_to_Z); rewrite !iz_add !iz_nat => H.
    apply/negP => /oddE [ h Hh ]; move: H; nlia.
  Qed.

  Lemma vz_b_pdiv : beta != 1 -> exists p, prime p /\ vz p beta = 1%N.
  Proof.
    move=> Hb1.
    have Hb1' : (1 < absz beta)%N.
    { rewrite ltn_neqAle absz_gt0 b_neq0 andbT eq_sym; apply: contra Hb1 => /eqP E.
      by rewrite -[beta]gtz0_abs // E. }
    exists (pdiv (absz beta)); split; first exact: pdiv_prime.
    have Hd : (pdiv (absz beta) %| absz l)%N.
    { apply: dvdn_trans (pdiv_dvd _) _; by move: Hbl; rewrite dvdzE. }
    have Hm : pdiv (absz beta) \in primes (absz l) by rewrite mem_primes pdiv_prime // absl_gt0.
    apply/eqP; rewrite eqn_leq; apply/andP; split.
    - rewrite -(logn_l Hl Hm) /vz; apply: dvdn_leq_log; first exact: absl_gt0.
      by move: Hbl; rewrite dvdzE.
    - by rewrite /vz logn_gt0 mem_primes pdiv_prime // absz_gt0 b_neq0 pdiv_dvd.
  Qed.

  Lemma vz_l_notb : beta != l -> exists p, prime p /\ vz p l = 1%N /\ vz p beta = 0%N.
  Proof.
    move=> Hbl'.
    have [ c Hc ] := dvdzP Hbl.
    have Hc0 : 0 < c by move: (l_pos'); rewrite Hc pmulr_lgt0.
    have Hc1 : (1 < absz c)%N.
    { have Hc' : c != 0 by rewrite gt_eqF.
      rewrite ltn_neqAle absz_gt0 Hc' andbT eq_sym; apply: contra Hbl' => /eqP E.
      by rewrite Hc -[c]gtz0_abs // E mul1r. }
    set p := pdiv (absz c).
    have pP : prime p by apply: pdiv_prime.
    have Hpl : (p %| absz l)%N by rewrite Hc abszM dvdn_mulr // pdiv_dvd.
    have Hm : p \in primes (absz l) by rewrite mem_primes pP absl_gt0.
    exists p; split => //; split; first exact: (logn_l Hl Hm).
    apply: vz_ndvd; rewrite dvdzE /=; apply/negP => Hpb.
    have := l_sqf Hl (prime_gt1 pP); rewrite Hc abszM mulnC.
    by rewrite dvdn_mul // pdiv_dvd.
  Qed.

  Theorem gamma_not_tors : beta != 1 -> beta != l -> ~ in_span2 (tors_Tl l) (tors_T3 l) (beta, 1).
  Proof.
    move=> Hb1 Hbl' [ i [ j ] ]; rewrite /psq /pmul /ppow /tors_Tl /tors_T3 /=.
    case: j => /= [ [ _ [ t [ Ht E ] ] ] | [ E _ ] ].
    - move: E; rewrite (_ : (if i then (l, 1) else (1, 1)).2 = 1); first by case: i.
      rewrite mul1r.
      move=> E; have : (0 : rat) < (1 : int)%:~R by rewrite rmorph1.
      rewrite E rmorphN /= mulNr oppr_gt0 => H.
      by move: H; rewrite ltNge mulr_ge0 // ?sqr_ge0 // ler0z ltW // l_pos'.
    - case: i E => /= E.
      + have [ p [ pP [ H1 H2 ] ] ] := vz_l_notb Hbl'.
        have := sqc_val b_neq0 (mulf_neq0 (l_neq0 Hl) (oner_neq0 _)) E pP.
        by rewrite mulr1 H1 H2.
      + have [ p [ pP H1 ] ] := vz_b_pdiv Hb1.
        have := sqc_val b_neq0 (mulf_neq0 (oner_neq0 _) (oner_neq0 _)) E pP.
        by rewrite mulr1 H1 /vz logn1.
  Qed.

End Upper.


(** * Part E. The Kummer map over a field: multiplicativity and halving *)
(** * The Kummer map for a root e of the cubic is multiplicative modulo squares *)

Section Kummer.

  Variable K : fieldType.
  Variables A2 A4 A6 : K.
  Hypothesis two0 : 2%:R != 0 :> K.
  Hypothesis nons : forall x, fc A2 A4 A6 x = 0 -> fd A2 A4 x != 0.
  Variable e : K.
  Hypothesis He : fc A2 A4 A6 e = 0.

  Local Abbreviation f := (fc A2 A4 A6).
  Local Abbreviation f' := (fd A2 A4).

  Definition kv (P : option (K * K)) : K :=
    if P is Some (x, y) then (if x == e then f' e else x - e) else 1.

  Lemma kv_neq0 P : kv P != 0.
  Proof.
    case: P => [ [ x y ] | ] /=; last exact: oner_neq0.
    by case: (eqVneq x e) => [ _ | ]; [ exact: nons He | rewrite subr_eq0 ].
  Qed.

  Lemma kv_neg P : kv (wneg P) = kv P.
  Proof. by case: P => [ [ x y ] | ]. Qed.

  Definition x3of (m x1 x2 : K) : K := m ^+ 2 - A2 - x1 - x2.
  Definition Pl (m x1 y1 x2 x : K) : K :=
    f x - (m * (x - x1) + y1) ^+ 2 - (x - x1) * (x - x2) * (x - x3of m x1 x2).
  Definition Dl (m x1 y1 x2 x : K) : K :=
    f' x - 2%:R * m * (m * (x - x1) + y1)
    - ((x - x2) * (x - x3of m x1 x2) + (x - x1) * (x - x3of m x1 x2) + (x - x1) * (x - x2)).

  Lemma Pl_lin m x1 y1 x2 a b c : Pl m x1 y1 x2 a - Pl m x1 y1 x2 b = (a - b) * Dl m x1 y1 x2 c.
  Proof. rewrite /Pl /Dl /x3of /fc /fd; ring. Qed.

  Lemma Dl_const m x1 y1 x2 c c' : Dl m x1 y1 x2 c = Dl m x1 y1 x2 c'.
  Proof. rewrite /Dl /x3of /fd; ring. Qed.

  Lemma Pl_x1 m x1 y1 x2 : won A2 A4 A6 (x1, y1) -> Pl m x1 y1 x2 x1 = 0.
  Proof. rewrite /won /= /Pl => h; rewrite -h; ring. Qed.

  Lemma Pl_x2 m x1 y1 x2 y2 : won A2 A4 A6 (x2, y2) -> m * (x2 - x1) + y1 = y2 -> Pl m x1 y1 x2 x2 = 0.
  Proof. rewrite /won /= /Pl => h hm; rewrite hm -h; ring. Qed.

  Lemma Pl_e m x1 y1 x2 : Pl m x1 y1 x2 e = 0 ->
    (x1 - e) * (x2 - e) * (x3of m x1 x2 - e) = (m * (e - x1) + y1) ^+ 2.
  Proof.
    rewrite /Pl He => /eqP; rewrite -subr_eq0 => /eqP H.
    apply/eqP; rewrite -subr_eq0; apply/eqP; rewrite -[RHS]H; ring.
  Qed.

  Lemma Dl0 m x1 y1 x2 : Dl m x1 y1 x2 e = 0 -> m * (e - x1) + y1 = 0 ->
    f' e = (e - x2) * (e - x3of m x1 x2) + (e - x1) * (e - x3of m x1 x2) + (e - x1) * (e - x2).
  Proof.
    move=> H HL; apply/eqP; rewrite -subr_eq0; apply/eqP; rewrite -[RHS]H /Dl HL; ring.
  Qed.

  Lemma sq0 (a : K) : a ^+ 2 = 0 -> a = 0.
  Proof. by move/eqP; rewrite expf_eq0 /= => /eqP. Qed.

  Lemma y0_of (x y : K) : won A2 A4 A6 (x, y) -> x = e -> y = 0.
  Proof. by rewrite /won /= => h E; apply: sq0; rewrite h E He. Qed.

  Lemma sq_ex (a b : K) : a = b ^+ 2 -> exists s, a = s ^+ 2.
  Proof. by move=> ->; exists b. Qed.

  Theorem kv_hom (P Q : option (K * K)) : won_pt A2 A4 A6 P -> won_pt A2 A4 A6 Q ->
    exists s, kv P * kv Q * kv (wadd A2 A4 P Q) = s ^+ 2.
  Proof.
    case: P => [ [ x1 y1 ] | ]; last by move=> _ _; exists (kv Q); rewrite wadd0P /= mul1r expr2.
    case: Q => [ [ x2 y2 ] | ] h1 h2; last by exists (kv (Some (x1, y1))); rewrite waddP0 /= mulr1 expr2.
    rewrite /= in h1 h2.
    case: (wcases h1 h2) => [ [ ex ey ] | [ [ ex [ ey ny ] ] | ne ] ].
    - subst x2; rewrite wadd_op //= mulr1; by exists (if x1 == e then f' e else x1 - e); rewrite expr2.
    - (* tangent *)
      subst x2 y2; rewrite (wadd_tg A2 A4 two0 x1 ny) /=.
      set m := f' x1 / (2%:R * y1).
      have Hm : 2%:R * m * y1 = f' x1 by rewrite /m; field; rewrite ny two0.
      have Hx1 : x1 != e by apply: contra ny => /eqP E; rewrite (y0_of h1 E).
      have D0 : Dl m x1 y1 x1 x1 = 0 by rewrite /Dl -Hm; ring.
      have Pe : Pl m x1 y1 x1 e = 0.
      { have := Pl_lin m x1 y1 x1 e x1 x1; rewrite D0 mulr0 (Pl_x1 m x1 h1) subr0; done. }
      have HL := Pl_e Pe.
      rewrite (negbTE Hx1).
      case: (eqVneq (x3of m x1 x1) e) => Ex3.
      + have HL0 : m * (e - x1) + y1 = 0 by apply: sq0; rewrite -HL Ex3 subrr mulr0.
        have Hd : Dl m x1 y1 x1 e = 0 by rewrite (Dl_const _ _ _ _ e x1).
        have Hf := Dl0 Hd HL0; rewrite Ex3 in Hf.
        rewrite Hf; exists ((x1 - e) * (e - x1)); ring.
      + by exists (m * (e - x1) + y1); rewrite -HL.
    - (* chord *)
      rewrite (wadd_ch A2 A4 y1 y2 ne) /=.
      set m := (y2 - y1) / (x2 - x1).
      have ne' : x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
      have Hm : m * (x2 - x1) + y1 = y2 by rewrite /m mulfVK // subrK.
      have P1 := Pl_x1 m x2 h1; have P2 := Pl_x2 h2 Hm.
      have Dz : forall c, Dl m x1 y1 x2 c = 0.
      { move=> c; have := Pl_lin m x1 y1 x2 x2 x1 c; rewrite P1 P2 subr0 => /esym /eqP.
        by rewrite mulf_eq0 (negbTE ne') /= => /eqP. }
      have Pe : Pl m x1 y1 x2 e = 0.
      { by have := Pl_lin m x1 y1 x2 e x1 x1; rewrite Dz mulr0 P1 subr0. }
      have HL := Pl_e Pe.
      have Hf := fun H => Dl0 (Dz e) H.
      case: (eqVneq x1 e) => E1.
      + (* P is the 2-torsion point (e, 0) *)
        subst x1; have Hy1 := y0_of h1 erefl.
        have HL0 : m * (e - e) + y1 = 0 by rewrite Hy1 subrr mulr0 addr0.
        have := Hf HL0; rewrite !subrr !mul0r !addr0 => Hf'.
        rewrite eq_sym (negbTE ne).
        case: (eqVneq (x3of m e x2) e) => E3.
        * have F0 : f' e = 0 by rewrite Hf' E3; ring.
             by move: (nons He); rewrite F0 eqxx.
        * by exists (f' e); rewrite Hf' /x3of; ring.
      +
        case: (eqVneq x2 e) => E2.
        * subst x2; have Hy2 := y0_of h2 erefl.
          have HL0 : m * (e - x1) + y1 = 0 by rewrite Hm Hy2.
          have := Hf HL0; rewrite subrr !mul0r ?add0r ?addr0 => Hf'.
          case: (eqVneq (x3of m x1 e) e) => E3.
          -- have F0 : f' e = 0 by rewrite Hf' E3; ring.
             by move: (nons He); rewrite F0 eqxx.
          -- by exists (f' e); rewrite Hf' /x3of; ring.
        *
          case: (eqVneq (x3of m x1 x2) e) => E3.
          -- have HL0 : m * (e - x1) + y1 = 0 by apply: sq0; rewrite -HL E3 subrr mulr0.
             have := Hf HL0; rewrite E3 subrr !mulr0 !add0r => Hf'.
             by exists (f' e); rewrite Hf' /x3of; ring.
          -- by exists (m * (e - x1) + y1); rewrite -HL.
  Qed.

End Kummer.



(** * Halving: a point whose Kummer values are all squares is a double *)

Section Halving.

  Variable K : fieldType.
  Hypothesis two0 : 2%:R != 0 :> K.

  Definition cA2 (e1 e2 e3 : K) : K := - (e1 + e2 + e3).
  Definition cA4 (e1 e2 e3 : K) : K := e1 * e2 + e1 * e3 + e2 * e3.
  Definition cA6 (e1 e2 e3 : K) : K := - (e1 * e2 * e3).

  Lemma fcE (e1 e2 e3 x : K) : fc (cA2 e1 e2 e3) (cA4 e1 e2 e3) (cA6 e1 e2 e3) x = (x - e1) * (x - e2) * (x - e3).
  Proof. rewrite /fc /cA2 /cA4 /cA6; ring. Qed.

  Lemma fdE (e1 e2 e3 x : K) : fd (cA2 e1 e2 e3) (cA4 e1 e2 e3) x =
    (x - e2) * (x - e3) + (x - e1) * (x - e3) + (x - e1) * (x - e2).
  Proof. rewrite /fd /cA2 /cA4; ring. Qed.

  Lemma half_xy (x0 r1 r2 r3 : K) :
    let e1 := x0 - r1 ^+ 2 in let e2 := x0 - r2 ^+ 2 in let e3 := x0 - r3 ^+ 2 in
    let xq := x0 + r1 * r2 + r1 * r3 + r2 * r3 in let yq := (r1 + r2) * (r1 + r3) * (r2 + r3) in
    yq != 0 ->
    wsum (cA2 e1 e2 e3) (fd (cA2 e1 e2 e3) (cA4 e1 e2 e3) xq / (2%:R * yq)) xq yq xq = (x0, r1 * r2 * r3).
  Proof.
    move=> e1 e2 e3 xq yq Hy.
    have H12 : r1 + r2 != 0 by apply: contra Hy => /eqP E; rewrite /yq E !mul0r.
    have H13 : r1 + r3 != 0 by apply: contra Hy => /eqP E; rewrite /yq E mulr0 mul0r.
    have H23 : r2 + r3 != 0 by apply: contra Hy => /eqP E; rewrite /yq E mulr0.
    rewrite /wsum /e1 /e2 /e3 /xq /yq /cA2 /fd /cA4; congr pair; field; by rewrite ?two0 ?H12 ?H13 ?H23.
  Qed.

End Halving.


(** * Part F. E(F_p) as a finite group; the F_p-Kummer map is onto *)
Local Open Scope group_scope.
(** * Counting in a finite group: fibres of a map constant on cosets *)

Lemma card_fib (G : finGroupType) (T : finType) (f : G -> T) (H : {set G}) :
  (forall x y, (f x == f y) = (x * y^-1 \in H)) ->
  #|[set: G]| = (#|f @: [set: G]| * #|H|)%N.
Proof.
  move=> Hf.
  rewrite -sum1_card (partition_big_imset f) /=.
  rewrite -sum_nat_const; apply: eq_bigr => t /imsetP [ x0 _ -> ].
  rewrite -[RHS](card_rcoset H x0) -sum1_card; apply: eq_bigl => y.
  rewrite in_setT /= Hf mem_rcoset.
  done.
Qed.

(** * E(F_p) as a finite group, for the split cubic (x - a1)(x - a2)(x - a3) *)

Local Close Scope group_scope.

Definition goodE (p : nat) (a1 a2 a3 : 'F_p) : bool :=
  [&& (2%:R != 0 :> 'F_p), a1 != a2, a1 != a3 & a2 != a3].

Section curve.

  Variables (p : nat) (a1 a2 a3 : 'F_p).
  Local Abbreviation A2 := (cA2 a1 a2 a3).
  Local Abbreviation A4 := (cA4 a1 a2 a3).
  Local Abbreviation A6 := (cA6 a1 a2 a3).

  Definition onb3 (P : option ('F_p * 'F_p)) : bool :=
    if P is Some (x, y) then y ^+ 2 == fc A2 A4 A6 x else true.

  Lemma onb3P P : reflect (won_pt A2 A4 A6 P) (onb3 P).
  Proof. case: P => [ [ x y ] | ] /=; [ exact: eqP | exact: ReflectT ]. Qed.

  Hypothesis h : goodE a1 a2 a3.

  Lemma two0E : 2%:R != 0 :> 'F_p. Proof. by case/and4P: h. Qed.
  Lemma dE12 : a1 != a2. Proof. by case/and4P: h. Qed.
  Lemma dE13 : a1 != a3. Proof. by case/and4P: h. Qed.
  Lemma dE23 : a2 != a3. Proof. by case/and4P: h. Qed.

  Lemma roots x : fc A2 A4 A6 x = 0 -> [\/ x = a1, x = a2 | x = a3].
  Proof.
    rewrite fcE => /eqP; rewrite !mulf_eq0 !subr_eq0 => /orP [ /orP [] | ] /eqP ->;
      by [ constructor 1 | constructor 2 | constructor 3 ].
  Qed.

  Lemma nonsE : forall x, fc A2 A4 A6 x = 0 -> fd A2 A4 x != 0.
  Proof.
    move=> x /roots [] ->; rewrite fdE !subrr ?mulr0 ?mul0r ?addr0 ?add0r.
    - by rewrite mulf_neq0 // subr_eq0 ?dE12 ?dE13.
    - by rewrite mulf_neq0 // subr_eq0 ?dE23 // eq_sym ?dE12.
    - by rewrite mulf_neq0 // subr_eq0 eq_sym ?dE13 ?dE23.
  Qed.

End curve.

Definition EPT3 (p : nat) (a1 a2 a3 : 'F_p) (h : goodE a1 a2 a3) : Type :=
  {P : option ('F_p * 'F_p) | onb3 a1 a2 a3 P}.

#[warning="-redundant-canonical-projection"]
HB.instance Definition _ (p : nat) (a1 a2 a3 : 'F_p) (h : goodE a1 a2 a3) := Finite.on (@EPT3 p a1 a2 a3 h).

Section ept3.

  Variables (p : nat) (a1 a2 a3 : 'F_p) (h : goodE a1 a2 a3).
  Local Abbreviation A2 := (cA2 a1 a2 a3).
  Local Abbreviation A4 := (cA4 a1 a2 a3).
  Local Abbreviation A6 := (cA6 a1 a2 a3).
  Local Abbreviation T := (@EPT3 p a1 a2 a3 h).

  Lemma onb3_add P Q : onb3 a1 a2 a3 P -> onb3 a1 a2 a3 Q -> onb3 a1 a2 a3 (wadd A2 A4 P Q).
  Proof. move=> /onb3P hP /onb3P hQ; apply/onb3P; exact: (wadd_on (two0E h)). Qed.

  Lemma onb3_neg P : onb3 a1 a2 a3 P -> onb3 a1 a2 a3 (wneg P).
  Proof. move=> /onb3P hP; apply/onb3P; exact: wneg_on. Qed.

  Definition emul3 (P Q : T) : T := exist _ (wadd A2 A4 (val P) (val Q)) (onb3_add (valP P) (valP Q)).
  Definition eone3 : T := exist _ None isT.
  Definition einv3 (P : T) : T := exist _ (wneg (val P)) (onb3_neg (valP P)).

  Lemma emul3A : associative emul3.
  Proof.
    move=> P Q R; apply: val_inj => /=; symmetry.
    by apply: (wadd_assoc (two0E h) (nonsE h)); apply/onb3P; apply: valP.
  Qed.

  Lemma emul31 : left_id eone3 emul3.
  Proof. by move=> P; apply: val_inj. Qed.

  Lemma emul3V : left_inverse eone3 einv3 emul3.
  Proof. by move=> P; apply: val_inj => /=; rewrite waddNl. Qed.

End ept3.

#[warning="-redundant-canonical-projection"]
HB.instance Definition _ (p : nat) (a1 a2 a3 : 'F_p) (h : goodE a1 a2 a3) :=
  Finite_isGroup.Build (@EPT3 p a1 a2 a3 h) (@emul3A p a1 a2 a3 h) (@emul31 p a1 a2 a3 h) (@emul3V p a1 a2 a3 h).

(** * The Kummer map on E(F_p) is onto *)

Section surj.

  Variable p : nat.
  Hypotheses (pP : prime p) (po : odd p).
  Variables (a1 a2 a3 : 'F_p).
  Hypothesis h : goodE a1 a2 a3.
  Local Abbreviation A2 := (cA2 a1 a2 a3).
  Local Abbreviation A4 := (cA4 a1 a2 a3).
  Local Abbreviation A6 := (cA6 a1 a2 a3).
  Local Abbreviation G := (@EPT3 p a1 a2 a3 h).

  Definition lb (x : 'F_p) : bool := lchi p x == -1.

  Lemma lchi_pm (x : 'F_p) : x != 0 -> (lchi p x = 1) \/ (lchi p x = -1).
  Proof. by rewrite /lchi => /negbTE ->; case: ifP; [ left | right ]. Qed.

  Lemma lchi_sq (s : 'F_p) : s != 0 -> lchi p (s ^+ 2) = 1.
  Proof. by move=> Hs; apply/(lchi_eq1 pP po); split; [ rewrite expf_neq0 | exists s ]. Qed.

  Lemma He1 : fc A2 A4 A6 a1 = 0. Proof. by rewrite fcE subrr !mul0r. Qed.
  Lemma He2 : fc A2 A4 A6 a2 = 0. Proof. by rewrite fcE subrr mulr0 mul0r. Qed.
  Lemma He3 : fc A2 A4 A6 a3 = 0. Proof. by rewrite fcE subrr mulr0. Qed.

  Lemma lb_hom (e : 'F_p) (He : fc A2 A4 A6 e = 0) (P Q : G) :
    lb (kv A2 A4 e (val (P * Q)%g)) = lb (kv A2 A4 e (val P)) (+) lb (kv A2 A4 e (val Q)).
  Proof.
    have := @kv_hom _ A2 A4 A6 (two0E h) (nonsE h) e He (val P) (val Q) (elimT (onb3P _ _ _ _) (valP P))
      (elimT (onb3P _ _ _ _) (valP Q)).
    move=> [ s Hs ]; rewrite /= in Hs |- *.
    set u := kv A2 A4 e (val P) in Hs *; set w := kv A2 A4 e (val Q) in Hs *.
    set r := kv A2 A4 e (wadd A2 A4 (val P) (val Q)) in Hs *.
    have Hu : u != 0 by exact: (@kv_neq0 _ A2 A4 A6 (nonsE h) e He _).
    have Hw : w != 0 by exact: (@kv_neq0 _ A2 A4 A6 (nonsE h) e He _).
    have Hr : r != 0 by exact: (@kv_neq0 _ A2 A4 A6 (nonsE h) e He _).
    have Hs0 : s != 0 by apply/eqP => E; move: Hs; rewrite E expr0n /= => /eqP; rewrite !mulf_eq0 (negbTE Hu) (negbTE Hw) (negbTE Hr).
    have := congr1 (lchi p) Hs; rewrite (lchi_sq Hs0) !(lchiM pP po) /lb.
    by case: (lchi_pm Hu) => ->; case: (lchi_pm Hw) => ->; case: (lchi_pm Hr) => ->.
  Qed.

  Lemma kv_pm1 (e : 'F_p) (He : fc A2 A4 A6 e = 0) (P : option ('F_p * 'F_p)) :
    lb (kv A2 A4 e P) = false -> lchi p (kv A2 A4 e P) = 1.
  Proof.
    move=> Hb; case: (lchi_pm (@kv_neq0 _ A2 A4 A6 (nonsE h) e He P)) => // E.
    by move: Hb; rewrite /lb E eqxx.
  Qed.

  Lemma sqrt_kv (e : 'F_p) (He : fc A2 A4 A6 e = 0) (x0 y0 : 'F_p) :
    lb (kv A2 A4 e (Some (x0, y0))) = false -> exists r, r ^+ 2 = x0 - e.
  Proof.
    move=> Hb; case: (eqVneq x0 e) => [ -> | Hx ]; first by exists 0; rewrite expr0n subrr.
    have := kv_pm1 He Hb; rewrite /= (negbTE Hx) => /(lchi_eq1 pP po) [ _ [ y Hy ] ].
    by exists y.
  Qed.

  Lemma prod3 (x0 y0 : 'F_p) : y0 ^+ 2 = fc A2 A4 A6 x0 ->
    exists s, kv A2 A4 a1 (Some (x0, y0)) * kv A2 A4 a2 (Some (x0, y0)) * kv A2 A4 a3 (Some (x0, y0)) = s ^+ 2.
  Proof.
    move=> Hy; rewrite /kv.
    case: (eqVneq x0 a1) => [ -> | H1 ].
    - rewrite (negbTE (dE12 h)) (negbTE (dE13 h)) fdE; exists ((a1 - a2) * (a1 - a3)); ring.
    - case: (eqVneq x0 a2) => [ -> | H2 ].
      + rewrite (negbTE (dE23 h)) fdE; exists ((a2 - a1) * (a2 - a3)); ring.
      + case: (eqVneq x0 a3) => [ -> | H3 ].
        * rewrite fdE; exists ((a3 - a1) * (a3 - a2)); ring.
        * by exists y0; rewrite Hy fcE.
  Qed.

  Lemma lb3 (x0 y0 : 'F_p) : y0 ^+ 2 = fc A2 A4 A6 x0 ->
    lb (kv A2 A4 a1 (Some (x0, y0))) = false -> lb (kv A2 A4 a2 (Some (x0, y0))) = false ->
    lb (kv A2 A4 a3 (Some (x0, y0))) = false.
  Proof.
    move=> Hy H1 H2; have [ s Hs ] := prod3 Hy.
    have N1 := @kv_neq0 _ A2 A4 A6 (nonsE h) a1 He1 (Some (x0, y0)).
    have N2 := @kv_neq0 _ A2 A4 A6 (nonsE h) a2 He2 (Some (x0, y0)).
    have N3 := @kv_neq0 _ A2 A4 A6 (nonsE h) a3 He3 (Some (x0, y0)).
    have Hs0 : s != 0 by apply/eqP => E; move: Hs; rewrite E expr0n /= => /eqP; rewrite !mulf_eq0 (negbTE N1) (negbTE N2) (negbTE N3).
    have := congr1 (lchi p) Hs; rewrite (lchi_sq Hs0) !(lchiM pP po) (kv_pm1 He1 H1) (kv_pm1 He2 H2) !mul1r => E.
    by rewrite /lb E.
  Qed.

  Lemma halve (P : G) : lb (kv A2 A4 a1 (val P)) = false -> lb (kv A2 A4 a2 (val P)) = false ->
    exists Q : G, (Q * Q)%g = P.
  Proof.
    case: P => x Hon; case: x Hon => [ [ x0 y0 ] | ] Hon /=; last by move=> _ _; exists 1%g; apply: val_inj.
    move=> L1 L2; have Hy : y0 ^+ 2 = fc A2 A4 A6 x0 by apply/eqP.
    have L3 := lb3 Hy L1 L2.
    have [ r1 E1 ] := @sqrt_kv a1 He1 x0 y0 L1.
    have [ r2 E2 ] := @sqrt_kv a2 He2 x0 y0 L2.
    have [ r3' E3' ] := @sqrt_kv a3 He3 x0 y0 L3.
    have Hsq : (r1 * r2 * r3') ^+ 2 = y0 ^+ 2 by rewrite Hy fcE !exprMn E1 E2 E3'.
    have [ r3 [ E3 Hr ] ] : exists r3, r3 ^+ 2 = x0 - a3 /\ r1 * r2 * r3 = y0.
    { move/eqP: Hsq; rewrite eqf_sqr => /orP [ /eqP H | /eqP H ].
      - by exists r3'.
      - by exists (- r3'); rewrite sqrrN mulrN H opprK. }
    have ea1 : a1 = x0 - r1 ^+ 2 by rewrite E1 opprB addrC subrK.
    have ea2 : a2 = x0 - r2 ^+ 2 by rewrite E2 opprB addrC subrK.
    have ea3 : a3 = x0 - r3 ^+ 2 by rewrite E3 opprB addrC subrK.
    have ne : forall (ri rj ai aj : 'F_p), ai != aj -> ai = x0 - ri ^+ 2 -> aj = x0 - rj ^+ 2 -> ri + rj != 0.
    { move=> ri rj ai aj Hij Hi Hj; apply: contra Hij => /eqP E; rewrite Hi Hj.
      have -> : ri = - rj by apply/eqP; rewrite -addr_eq0 E.
      by rewrite sqrrN. }
    have n12 := ne _ _ _ _ (dE12 h) ea1 ea2.
    have n13 := ne _ _ _ _ (dE13 h) ea1 ea3.
    have n23 := ne _ _ _ _ (dE23 h) ea2 ea3.
    set xq := x0 + r1 * r2 + r1 * r3 + r2 * r3.
    set yq := (r1 + r2) * (r1 + r3) * (r2 + r3).
    have Hyq : yq != 0 by rewrite /yq !mulf_neq0.
    have Hq : onb3 a1 a2 a3 (Some (xq, yq)).
    { by rewrite /= fcE ea1 ea2 ea3 /xq /yq; apply/eqP; ring. }
    exists (exist _ (Some (xq, yq)) Hq); apply: val_inj.
    change (wadd A2 A4 (Some (xq, yq)) (Some (xq, yq)) = Some (x0, y0)).
    rewrite (wadd_tg A2 A4 (two0E h) xq Hyq); congr Some.
    have := half_xy (two0E h) x0 Hyq; rewrite -ea1 -ea2 -ea3 Hr; exact.
  Qed.


  Lemma mulC3 (x y : G) : (x * y = y * x)%g.
  Proof.
    apply: val_inj => /=; apply: wadd_comm; apply/onb3P; exact: valP.
  Qed.

  Definition kap (x : G) : bool * bool := (lb (kv A2 A4 a1 (val x)), lb (kv A2 A4 a2 (val x))).

  Lemma kapM (x y : G) : (kap (x * y)%g).1 = (kap x).1 (+) (kap y).1 /\ (kap (x * y)%g).2 = (kap x).2 (+) (kap y).2.
  Proof. by rewrite /kap /= (lb_hom He1) (lb_hom He2). Qed.

  Lemma kapV (x : G) : kap (x^-1)%g = kap x.
  Proof. by rewrite /kap /= !kv_neg. Qed.

  Local Abbreviation H2 := [set (z * z)%g | z in [set: G]].
  Local Abbreviation G2 := [set z : G | (z * z == 1)%g].

  Lemma kap_fib (x y : G) : (kap x == kap y) = ((x * y^-1)%g \in H2).
  Proof.
    have [ E1 E2 ] := kapM x (y^-1)%g; rewrite kapV in E1 E2.
    apply/idP/idP.
    - move=> /eqP Exy.
      have [ z Hz ] := @halve (x * y^-1)%g ltac:(by rewrite -[lb _]/((kap _).1) E1 Exy addbb)
                                            ltac:(by rewrite -[lb _]/((kap _).2) E2 Exy addbb).
      by apply/imsetP; exists z; rewrite ?in_setT // Hz.
    - move=> /imsetP [ z _ Hz ].
      have [ F1 F2 ] := kapM z z; rewrite !addbb -Hz E1 E2 in F1 F2.
      by move: F1 F2; case: (kap x) => b1 b2; case: (kap y) => c1 c2 /=; case: b1; case: c1; case: b2; case: c2.
  Qed.

  Lemma sq_fib (x y : G) : ((x * x)%g == (y * y)%g) = ((x * y^-1)%g \in G2).
  Proof.
    rewrite inE eq_mulgV1; congr (_ == _).
    by rewrite invMg -!mulgA; congr (_ * _)%g; rewrite [RHS]mulgA [(y^-1 * x)%g]mulC3 -mulgA.
  Qed.

  Definition L2 : seq (option ('F_p * 'F_p)) := [:: None; Some (a1, 0); Some (a2, 0); Some (a3, 0)].

  Lemma y_opp (y : 'F_p) : (y == - y) = (y == 0).
  Proof.
    apply/eqP/eqP => [ E | -> ]; last by rewrite oppr0.
    exact: (y_opp0 (two0E h) E).
  Qed.

  Lemma G2_mem (z : G) : ((z * z)%g == 1%g) = (val z \in L2).
  Proof.
    case: z => x Hon; rewrite -val_eqE /=; case: x Hon => [ [ x y ] | ] Hon /=; last by [].
    rewrite eqxx y_opp; case: (eqVneq y 0) => [ Ey | Hy ] /=.
    - subst y; move: Hon; rewrite /= expr0n eq_sym => /eqP Hf.
      rewrite !inE /=; case: (roots Hf) => ->; by rewrite !eqxx ?orbT.
    - rewrite !inE /=; apply/idP/idP => // /or3P [] /eqP [] _ E; by move: Hy; rewrite E eqxx.
  Qed.

  Lemma L2_uniq : uniq L2.
  Proof.
    by rewrite /L2 /= !inE !negb_or /= (dE12 h) (dE13 h) (dE23 h).
  Qed.

  Lemma L2_on x : x \in L2 -> onb3 a1 a2 a3 x.
  Proof.
    rewrite !inE => /or4P [] /eqP -> //=; rewrite expr0n eq_sym; apply/eqP;
      [ exact: He1 | exact: He2 | exact: He3 ].
  Qed.

  Lemma card_G2 : #|G2| = 4%N.
  Proof.
    rewrite -(card_imset _ val_inj).
    have -> : val @: G2 = [set x | x \in L2].
    { apply/setP => x; rewrite inE; apply/imsetP/idP.
      - by move=> [ z ]; rewrite inE G2_mem => H ->.
      - move=> Hx; exists (exist _ x (L2_on Hx)) => //; by rewrite inE G2_mem. }
    by rewrite cardsE (card_uniqP L2_uniq).
  Qed.

  Theorem kap_surj (c : bool * bool) : exists x : G, kap x = c.
  Proof.
    have F1 := @card_fib _ _ kap H2 kap_fib.
    have F2 := @card_fib _ _ (fun z => (z * z)%g) G2 sq_fib.
    have HH : (0 < #|H2|)%N by apply/card_gt0P; exists 1%g; apply/imsetP; exists 1%g; rewrite ?in_setT ?mulg1.
    have E : #|kap @: [set: G]| = 4%N.
    { apply/eqP; rewrite -(eqn_pmul2r HH) -F1 F2 card_G2 mulnC. done. }
    have Hall : kap @: [set: G] = [set: bool * bool].
    { apply/eqP; rewrite eqEcard subsetT /= E cardsT card_prod card_bool. done. }
    have : c \in kap @: [set: G] by rewrite Hall in_setT.
    by move=> /imsetP [ x _ -> ]; exists x.
  Qed.

End surj.


(** * Part G. Sufficient conditions for local solvability of C_gamma *)
(** * Sufficient conditions for local solvability *)

(* transfer of an exact primitive solution of C_d' to C_d when d / d' is a
   p-adic unit square in both coordinates *)
Lemma locsol_transfer (l : int) (p : nat) (d d' : int * int) (w0 w1 w2 w3 : int) : prime p ->
  primitive p w0 w1 w2 w3 -> eqn1 l d' w0 w1 w2 w3 = 0 -> eqn2 l d' w0 w1 w2 w3 = 0 ->
  (forall k : nat, exists a b : int, ~~ (p%:Z %| a)%Z /\ ~~ (p%:Z %| b)%Z /\
     ((p ^ k)%:Z %| d.1 - d'.1 * a ^+ 2)%Z /\ ((p ^ k)%:Z %| d.2 - d'.2 * b ^+ 2)%Z) ->
  locsol l p d.
Proof.
  move=> pP Hw E1 E2 H k; have [ a [ b [ Ha [ Hb [ Da Db ] ] ] ] ] := H k.
  clear H; case: d Da Db => d1 d2; case: d' E1 E2 => e1 e2 /= E1 E2 /dvdzP [ X HX ] /dvdzP [ Y HY ].
  have Hd1 : d1 = e1 * a ^+ 2 + X * (p ^ k)%:Z by rewrite -HX; ring.
  have Hd2 : d2 = e2 * b ^+ 2 + Y * (p ^ k)%:Z by rewrite -HY; ring.
  exists (a * b * w0), (b * w1), (a * w2), w3; split; [ | split ].
  - move: Hw; rewrite /primitive; apply: contra => /and4P [ H0 H1 H2 H3 ].
    apply/and4P; split => //.
    + by move: H0; rewrite !dvdzE !abszM !Euclid_dvdM // -!dvdzE (negbTE Ha) (negbTE Hb).
    + by move: H1; rewrite !dvdzE !abszM !Euclid_dvdM // -!dvdzE (negbTE Hb).
    + by move: H2; rewrite !dvdzE !abszM !Euclid_dvdM // -!dvdzE (negbTE Ha).
  - apply/dvdzP; exists (X * b ^+ 2 * w1 ^+ 2 - Y * a ^+ 2 * w2 ^+ 2).
    move: E1; rewrite /eqn1 /qform /= Hd1 Hd2 => E1.
    have -> : (e1 * a ^+ 2 + X * (p ^ k)%:Z) * (b * w1) ^+ 2 - (e2 * b ^+ 2 + Y * (p ^ k)%:Z) * (a * w2) ^+ 2 -
              l * (a * b * w0) ^+ 2 = a ^+ 2 * b ^+ 2 * (e1 * w1 ^+ 2 - e2 * w2 ^+ 2 - l * w0 ^+ 2) +
              (X * b ^+ 2 * w1 ^+ 2 - Y * a ^+ 2 * w2 ^+ 2) * (p ^ k)%:Z by ring.
    by rewrite E1 mulr0 add0r.
  - apply/dvdzP; exists (X * b ^+ 2 * w1 ^+ 2 - (X * e2 * b ^+ 2 + Y * e1 * a ^+ 2 + X * Y * (p ^ k)%:Z) * w3 ^+ 2).
    move: E2; rewrite /eqn2 /qform /= Hd1 Hd2 => E2.
    have -> : (e1 * a ^+ 2 + X * (p ^ k)%:Z) * (b * w1) ^+ 2 -
              (e1 * a ^+ 2 + X * (p ^ k)%:Z) * (e2 * b ^+ 2 + Y * (p ^ k)%:Z) * w3 ^+ 2 -
              - (3 * l) * (a * b * w0) ^+ 2 =
              a ^+ 2 * b ^+ 2 * (e1 * w1 ^+ 2 - e1 * e2 * w3 ^+ 2 - - (3 * l) * w0 ^+ 2) +
              (X * b ^+ 2 * w1 ^+ 2 - (X * e2 * b ^+ 2 + Y * e1 * a ^+ 2 + X * Y * (p ^ k)%:Z) * w3 ^+ 2) * (p ^ k)%:Z
      by ring.
    by rewrite E2 mulr0 add0r.
Qed.

Lemma iz_pow (p k : nat) : Z.of_nat (p ^ k) = (Z.of_nat p ^ Z.of_nat k)%ZZ.
Proof.
  elim: k => [ | k IH ]; first by rewrite expn0.
  by rewrite expnS Nat2Z.inj_mul IH Nat2Z.inj_succ Z.pow_succ_r //; lia.
Qed.

Lemma lift_sq (p : nat) (a c : int) : prime p -> ~~ (p%:Z %| a)%Z ->
  usq (Z.of_nat p) (int_to_Z a) (int_to_Z c) ->
  forall k : nat, exists z : int, ~~ (p%:Z %| z)%Z /\ ((p ^ k)%:Z %| a - c * z ^+ 2)%Z.
Proof.
  move=> pP Ha H k; have [ z Hz ] := H k.+1.
  have Hz' : ((p ^ k.+1)%:Z %| a - c * (Z_to_int z) ^+ 2)%Z.
  { apply/dvd_iz; rewrite iz_pow; move: Hz.
    by rewrite iz_add iz_opp !iz_mul !iz_Z_to_int => -[ t Ht ]; exists t; lia. }
  exists (Z_to_int z); split.
  - apply: contra Ha => Hp.
    have -> : a = (a - c * (Z_to_int z) ^+ 2) + c * (Z_to_int z) ^+ 2 by rewrite subrK.
    apply: rpredD; first by apply: dvdz_trans Hz'; rewrite dvdzE /= expnS dvdn_mulr.
    by apply: dvdz_mull; rewrite expr2; apply: dvdz_mull.
  - by apply: dvdz_trans Hz'; rewrite dvdzE /= dvdn_exp2l.
Qed.

Lemma usq_leg (p : nat) (a c : int) : prime p -> odd p -> ~~ (p%:Z %| a)%Z -> ~~ (p%:Z %| c)%Z ->
  legendre (a * c) p = 1 -> usq (Z.of_nat p) (int_to_Z a) (int_to_Z c).
Proof.
  move=> pP po Ha Hc /(legendre_eq1 pP po) [ _ [ z Hz ] ].
  have p2 : p != 2%N by apply: contraTneq po => ->.
  apply/(usq_sqmod pP (qunit_iz Ha) (qunit_iz Hc)).
  apply/(sqmod_odd_prod pP p2 (qunit_iz Ha) (qunit_iz Hc)).
  exists (int_to_Z z).
  have E : (int_to_Z a * int_to_Z c - int_to_Z z * int_to_Z z = int_to_Z (a * c - z ^+ 2))%ZZ.
  { by rewrite iz_add iz_opp !iz_mul. }
  by rewrite E; apply/dvd_iz; move: Hz; rewrite eqz_mod_dvd -rpredN opprB.
Qed.

Lemma cov1_iz (l d1 d2 z0 z1 z2 z3 : int) :
  cov1 (int_to_Z d1) (int_to_Z d2) (int_to_Z l) (int_to_Z z0) (int_to_Z z1) (int_to_Z z2) =
  int_to_Z (eqn1 l (d1, d2) z0 z1 z2 z3).
Proof. by rewrite /cov1 /eqn1 /qform /= !iz_add !iz_opp !iz_mul; lia. Qed.

Lemma cov2_iz (l d1 d2 z0 z1 z2 z3 : int) :
  cov2 (int_to_Z d1) (int_to_Z d2) (int_to_Z (- (3 * l))) (int_to_Z z0) (int_to_Z z1) (int_to_Z z3) =
  int_to_Z (eqn2 l (d1, d2) z0 z1 z2 z3).
Proof.
  have E : int_to_Z (- (3 * l)) = (- (int_to_Z 3 * int_to_Z l))%ZZ by rewrite iz_opp iz_mul.
  rewrite /cov2 /eqn2 /qform /= !iz_add !iz_opp !iz_mul; lia.
Qed.

Lemma dvd_izk (p k : nat) (a : int) : (Z.of_nat p ^ Z.of_nat k | int_to_Z a)%ZZ <-> (((p ^ k)%N)%:Z %| a)%Z.
Proof. by rewrite -iz_pow; apply: dvd_iz. Qed.

Lemma locsol_of_mod (l : int) (p : nat) (d1 d2 z0 z1 z2 z3 : int) : prime p -> p != 2%N ->
  (p%:Z %| eqn1 l (d1, d2) z0 z1 z2 z3)%Z -> (p%:Z %| eqn2 l (d1, d2) z0 z1 z2 z3)%Z ->
  ~~ (p%:Z %| d2 * z2)%Z -> ~~ (p%:Z %| d1 * d2 * z3)%Z -> locsol l p (d1, d2).
Proof.
  move=> pP p2 H1 H2 H3 H4 k.
  have pZ := primeZ pP.
  have p2Z : ~ (Z.of_nat p | 2)%ZZ.
  { move/(dvd_iz p (2%:Z)); rewrite dvdzE /= dvdn_prime2 //; by rewrite (negbTE p2). }
  have C1 : (Z.of_nat p | cov1 (int_to_Z d1) (int_to_Z d2) (int_to_Z l) (int_to_Z z0) (int_to_Z z1) (int_to_Z z2))%ZZ.
  { by rewrite (cov1_iz _ _ _ _ _ _ z3); apply/dvd_iz. }
  have C2 : (Z.of_nat p | cov2 (int_to_Z d1) (int_to_Z d2) (int_to_Z (- (3 * l))) (int_to_Z z0) (int_to_Z z1) (int_to_Z z3))%ZZ.
  { by rewrite (cov2_iz _ _ _ _ _ z2); apply/dvd_iz. }
  have N3 : ~ (Z.of_nat p | int_to_Z d2 * int_to_Z z2)%ZZ by rewrite -iz_mul => /dvd_iz; apply/negP.
  have N4 : ~ (Z.of_nat p | int_to_Z d1 * int_to_Z d2 * int_to_Z z3)%ZZ by rewrite -!iz_mul => /dvd_iz; apply/negP.
  have [ y2 [ y3 [ _ [ _ [ U2 [ _ [ K1 K2 ] ] ] ] ] ] ] := cov_lift_odd pZ p2Z C1 C2 N3 N4 k.
  exists z0, z1, (Z_to_int y2), (Z_to_int y3); split; [ | split ].
  - rewrite /primitive; apply/negP => /and4P [ _ _ D2 _ ]; apply: U2.
    by rewrite -(iz_Z_to_int y2); apply/dvd_iz.
  - apply/dvd_izk; rewrite -(cov1_iz _ _ _ _ _ _ (Z_to_int y3)) iz_Z_to_int; exact: K1.
  - apply/dvd_izk; rewrite -(cov2_iz _ _ _ _ _ (Z_to_int y2)) iz_Z_to_int; exact: K2.
Qed.

(** ** exact primitive solutions of the four torsion coverings *)

Lemma prim1 (p : nat) (a b c d : int) : prime p -> [|| a == 1, b == 1, c == 1 | d == 1] -> primitive p a b c d.
Proof.
  move=> pP H; rewrite /primitive; apply/negP => /and4P [ A B C D ].
  have Hp1 : ~~ (p%:Z %| 1)%Z by rewrite dvdz1 /=; apply/negP => /eqP E; move: pP; rewrite E.
  by case/or4P: H => /eqP E; [ move: A | move: B | move: C | move: D ]; rewrite E (negbTE Hp1).
Qed.

Lemma sol_O (l : int) : eqn1 l (1, 1) 0 1 1 1 = 0 /\ eqn2 l (1, 1) 0 1 1 1 = 0.
Proof. by rewrite /eqn1 /eqn2 /qform /=; split; ring. Qed.

Lemma sol_Tl (l : int) : eqn1 l (l, 1) 1 1 0 2 = 0 /\ eqn2 l (l, 1) 1 1 0 2 = 0.
Proof. by rewrite /eqn1 /eqn2 /qform /=; split; ring. Qed.

Lemma sol_T0 (l : int) : eqn1 l (- 3, - l) 1 0 1 1 = 0 /\ eqn2 l (- 3, - l) 1 0 1 1 = 0.
Proof. by rewrite /eqn1 /eqn2 /qform /=; split; ring. Qed.

Lemma sol_T3 (l : int) : eqn1 l (- (3 * l), - l) 1 1 2 0 = 0 /\ eqn2 l (- (3 * l), - l) 1 1 2 0 = 0.
Proof. by rewrite /eqn1 /eqn2 /qform /=; split; ring. Qed.

(* transfer to (b1, b2) from a torsion covering with an exact solution *)
Lemma transfer_usq (l : int) (p : nat) (b1 b2 : int) (d' : int * int) (w0 w1 w2 w3 : int) : prime p ->
  primitive p w0 w1 w2 w3 -> eqn1 l d' w0 w1 w2 w3 = 0 -> eqn2 l d' w0 w1 w2 w3 = 0 ->
  ~~ (p%:Z %| b1)%Z -> ~~ (p%:Z %| b2)%Z ->
  usq (Z.of_nat p) (int_to_Z b1) (int_to_Z d'.1) -> usq (Z.of_nat p) (int_to_Z b2) (int_to_Z d'.2) ->
  locsol l p (b1, b2).
Proof.
  move=> pP Hw E1 E2 H1 H2 U1 U2; apply: (locsol_transfer pP Hw E1 E2) => k.
  have [ a [ Ha Da ] ] := lift_sq pP H1 U1 k; have [ b [ Hb Db ] ] := lift_sq pP H2 U2 k.
  by exists a, b.
Qed.

(** * gamma at the primes of good reduction, via E(F_p) *)

Section goodp.

  Variables (l beta : int) (p : nat).
  Hypotheses (pP : prime p) (p2 : p != 2%N) (p3 : p != 3%N).
  Hypotheses (Hpl : ~~ (p%:Z %| l)%Z) (Hpb : ~~ (p%:Z %| beta)%Z).

  Let po : odd p. Proof. by apply/negPn/negP => /(prime_oddPn pP) E; move: p2; rewrite E. Qed.
  Let pF := pchar_Fp pP.
  Local Abbreviation r n := ((n : int)%:~R : 'F_p).

  Lemma r0 (n : int) : (r n == 0) = (p%:Z %| n)%Z.
  Proof. exact: (intr_pchar_eq0 pF). Qed.

  Lemma r0' (n : int) : ~~ (p%:Z %| n)%Z -> r n != 0.
  Proof. by rewrite r0. Qed.

  Lemma nd_mul (a b : int) : ~~ (p%:Z %| a)%Z -> ~~ (p%:Z %| b)%Z -> ~~ (p%:Z %| a * b)%Z.
  Proof. exact: odd_mul. Qed.

  Let nd2 : ~~ (p%:Z %| 2)%Z. Proof. by rewrite dvdzE /= dvdn_prime2 // (negbTE p2). Qed.
  Let nd3 : ~~ (p%:Z %| 3)%Z. Proof. by rewrite dvdzE /= dvdn_prime2 // (negbTE p3). Qed.
  Let nd4 : ~~ (p%:Z %| 4)%Z.
  Proof. by rewrite dvdzE /= (_ : 4%N = (2 * 2)%N) // Euclid_dvdM // dvdn_prime2 // (negbTE p2). Qed.
  Let ndm1 : ~~ (p%:Z %| -1)%Z.
  Proof. by rewrite dvdzE /= dvdn1; apply/negP => /eqP E; move: pP; rewrite E. Qed.
  Let nd1 : ~~ (p%:Z %| 1)%Z.
  Proof. by rewrite dvdz1 /=; apply/negP => /eqP E; move: pP; rewrite E. Qed.
  Let ndm3 : ~~ (p%:Z %| - 3)%Z. Proof. by move: nd3; rewrite !dvdzE ?abszN. Qed.
  Let ndml : ~~ (p%:Z %| - l)%Z. Proof. by rewrite rpredN. Qed.
  Let ndm3l : ~~ (p%:Z %| - (3 * l))%Z. Proof. by rewrite rpredN; apply: nd_mul. Qed.

  Local Abbreviation a1 := (0 : 'F_p).
  Local Abbreviation a2 := (r l).
  Local Abbreviation a3 := (r (- (3 * l))).

  Lemma good_h : goodE a1 a2 a3.
  Proof.
    apply/and4P; split.
    - have E2 : (2%:R : 'F_p) = r 2 by rewrite /= rmorphMn rmorph1.
      by rewrite E2 r0.
    - by rewrite eq_sym r0.
    - by rewrite eq_sym r0.
    - rewrite -subr_eq0 -rmorphB /= r0 (_ : l - - (3 * l) = 4 * l); first by ring.
      by apply: nd_mul.
  Qed.

  Lemma lchi_r (n : int) : lchi p (r n) = legendre n p.
  Proof. by []. Qed.

  Lemma lbeq (u w : 'F_p) : u != 0 -> w != 0 -> lb u = lb w -> lchi p u = lchi p w.
  Proof. by move=> Hu Hw; rewrite /lb; case: (lchi_pm Hu) => ->; case: (lchi_pm Hw) => ->. Qed.

  Lemma lb_false (u : 'F_p) : u != 0 -> lb u = false -> lchi p u = 1.
  Proof. by move=> Hu; rewrite /lb; case: (lchi_pm Hu) => ->. Qed.

  Lemma Fr_rep (t : 'F_p) : exists n : int, t = r n.
  Proof. by exists (val t)%:Z; rewrite /= -pmulrn natr_Zp. Qed.

  Lemma lchi_sqr' (u : 'F_p) : u != 0 -> lchi p u * lchi p u = 1.
  Proof. exact: lchi_sqr. Qed.

  Theorem gamma_good : locsol l p (beta, 1).
  Proof.
    have h := good_h.
    have rb0 : r beta != 0 by rewrite r0.
    have rl0 : r l != 0 by rewrite r0.
    have [ x Hx ] := kap_surj pP po h (lb (r beta), false).
    move: Hx; rewrite /kap; case: x => P HP /= [ E1 E2 ].
    case: P HP E1 E2 => [ [ x0 y0 ] | ] HP E1 E2; last first.
    - (* the identity: beta is a square mod p *)
      rewrite /kv in E1; move: E1; rewrite /lb lchi1 => /esym E1.
      have Hb : legendre (beta * 1) p = 1 by rewrite mulr1 -lchi_r; apply: lb_false.
      have [ U1 U2 ] := sol_O l.
      apply: (transfer_usq (d' := (1, 1)) pP (@prim1 p 0 1 1 1 pP isT) U1 U2 Hpb nd1).
      + exact: (usq_leg pP po Hpb nd1 Hb).
      + exact: usq_refl.
    - rewrite /= in HP; have Hy : y0 ^+ 2 = fc (cA2 a1 a2 a3) (cA4 a1 a2 a3) (cA6 a1 a2 a3) x0 by apply/eqP.
      rewrite fcE in Hy; rewrite /kv in E1 E2.
      have leq1 : forall a b : int, ~~ (p%:Z %| a)%Z -> ~~ (p%:Z %| b)%Z ->
          legendre a p = legendre b p -> legendre (a * b) p = 1.
      { move=> a b Ha Hb E; rewrite (legendreM pP po) E legendre_sqr //. }
      have [ U0 V0 ] := sol_T0 l; have [ Ul Vl ] := sol_Tl l; have [ U3 V3 ] := sol_T3 l.
      move: E1 E2; case: (eqVneq x0 a1) => [ -> | n1 ].
      + (* x = 0 *)
        rewrite (negbTE (dE12 h)) => E1 E2.
        have F0 : fd (cA2 a1 a2 a3) (cA4 a1 a2 a3) a1 = r (- 3 * l * l).
        { by rewrite fdE /= !rmorphM !rmorphN /= !rmorphM /=; ring. }
        rewrite F0 in E1.
        have nd33 : ~~ (p%:Z %| - 3 * l * l)%Z by apply: nd_mul => //; apply: nd_mul.
        have L1 := lbeq (r0' nd33) rb0 E1; rewrite !lchi_r in L1.
        have Hb : legendre (beta * (- 3)) p = 1.
        { by apply: leq1 => //; rewrite -L1 !(legendreM pP po) -mulrA legendre_sqr // mulr1. }
        have Hl : legendre (1 * (- l)) p = 1.
        { rewrite mul1r -lchi_r; apply: lb_false; first by rewrite r0.
          by rewrite -E2 rmorphN /= sub0r. }
        apply: (transfer_usq (d' := (- 3, - l)) pP (@prim1 p 1 0 1 1 pP isT) U0 V0 Hpb nd1).
        * exact: (usq_leg pP po Hpb ndm3 Hb).
        * exact: (usq_leg pP po nd1 ndml Hl).
      + case: (eqVneq x0 a2) => [ -> | n2 ].
        * (* x = l *)
          rewrite subr0 => E1 _.
          have L1 := lbeq rl0 rb0 E1; rewrite !lchi_r in L1.
          have Hb : legendre (beta * l) p = 1 by apply: leq1.
          apply: (transfer_usq (d' := (l, 1)) pP (@prim1 p 1 1 0 2 pP isT) Ul Vl Hpb nd1).
          -- exact: (usq_leg pP po Hpb Hpl Hb).
          -- exact: usq_refl.
        * case: (eqVneq x0 a3) => [ -> | n3 ].
          -- (* x = -3l *)
             rewrite subr0 => E1 E2.
             have L1 := lbeq (r0' ndm3l) rb0 E1; rewrite !lchi_r in L1.
             have Hb : legendre (beta * (- (3 * l))) p = 1 by apply: leq1.
             have E4 : a3 - a2 = r (4 * (- l)) by rewrite /= !rmorphM !rmorphN /= !rmorphM /=; ring.
             rewrite E4 in E2.
             have Hl : legendre (1 * (- l)) p = 1.
             { have := lb_false (r0' (nd_mul nd4 ndml)) E2; rewrite lchi_r (legendreM pP po) mul1r.
               have -> : legendre 4 p = 1 by rewrite (_ : (4 : int) = 2 * 2) // (legendreM pP po) legendre_sqr.
               by rewrite mul1r. }
             apply: (transfer_usq (d' := (- (3 * l), - l)) pP (@prim1 p 1 1 2 0 pP isT) U3 V3 Hpb nd1).
             ++ exact: (usq_leg pP po Hpb ndm3l Hb).
             ++ exact: (usq_leg pP po nd1 ndml Hl).
          -- (* a point of order > 2 *)
             move=> E1 E2.
             have N1 : x0 - a1 != 0 by rewrite subr_eq0.
             have N2 : x0 - a2 != 0 by rewrite subr_eq0.
             have N3 : x0 - a3 != 0 by rewrite subr_eq0.
             have L1 := lbeq N1 rb0 E1; have L2 := lb_false N2 E2.
             have Hy0 : y0 != 0.
             { apply/eqP => E; move: Hy; rewrite E expr0n /= => /esym /eqP.
               by rewrite !mulf_eq0 (negbTE N1) (negbTE N2) (negbTE N3). }
             have L3 : lchi p (x0 - a3) = lchi p (r beta).
             { have := congr1 (lchi p) Hy; rewrite (lchi_sq pP po Hy0) !(lchiM pP po) L1 L2 mulr1 => E.
               move: E; case: (lchi_pm N3) => ->; case: (lchi_pm rb0) => -> //= /eqP //. }
             have sq_of : forall u : 'F_p, lchi p u = lchi p (r beta) -> u != 0 ->
                 exists s, s ^+ 2 * r beta = u.
             { move=> u Hu Hu0.
               have : lchi p (u * r beta) = 1 by rewrite (lchiM pP po) Hu lchi_sqr'.
               move/(lchi_eq1 pP po) => [ _ [ t Ht ] ]; exists (t / r beta).
               by rewrite expr_div_n Ht; field. }
             have [ s1 Es1 ] := sq_of _ L1 N1; have [ s3 Es3 ] := sq_of _ L3 N3.
             have [ _ [ s2 Es2 ] ] := (lchi_eq1 pP po _).1 L2.
             have [ z1 Ez1 ] := Fr_rep s1; have [ z2 Ez2 ] := Fr_rep s2; have [ z3 Ez3 ] := Fr_rep s3.
             apply: (@locsol_of_mod l p beta 1 1 z1 z2 z3 pP p2).
             ++ rewrite -r0 /eqn1 /qform /= !rmorphB !rmorphM /= -Ez1 -Ez2 rmorph1 !mul1r !mulr1 -!expr2.
                by apply/eqP; rewrite [r beta * _]mulrC Es1 Es2 subr0; ring.
             ++ rewrite -r0 /eqn2 /qform /= !rmorphB !rmorphM /= -Ez1 -Ez3 rmorph1 !mul1r !mulr1 -!expr2.
                by apply/eqP; rewrite [r beta * s1 ^+ 2]mulrC [r beta * s3 ^+ 2]mulrC Es1 Es3 subr0; ring.
             ++ apply: nd_mul => //; rewrite -r0 -Ez2; apply/negP => /eqP E; by move: N2; rewrite -Es2 E expr0n eqxx.
             ++ apply: nd_mul; first exact: nd_mul.
                by rewrite -r0 -Ez3; apply/negP => /eqP E; move: N3; rewrite -Es3 E expr0n mul0r eqxx.
  Qed.

End goodp.



(** * Part H. gamma is a Selmer class; Lemma par:descent *)
Lemma eq_logn (a b : nat) : (0 < a)%N -> (0 < b)%N -> (forall p, prime p -> logn p a = logn p b) -> a = b.
Proof.
  move=> Ha Hb H.
  have Hpr : primes a = primes b.
  { apply: (irr_sorted_eq ltn_trans ltnn (sorted_primes a) (sorted_primes b)) => p.
    case: (boolP (prime p)) => pP; last by rewrite !mem_primes (negbTE pP).
    by rewrite -!logn_gt0 H. }
  have Ea := prod_prime_decomp Ha; have Eb := prod_prime_decomp Hb.
  rewrite prime_decompE big_map /= in Ea; rewrite prime_decompE big_map /= in Eb.
  rewrite Ea Eb Hpr big_seq [RHS]big_seq; apply: eq_bigr => p; rewrite mem_primes => /and3P [ pP _ _ ].
  by rewrite H.
Qed.

Section Gamma.

  Variable l : int.
  Hypothesis Hl : admissible_l l.
  Local Abbreviation n := (nq l).
  Local Abbreviation q := (@qi l).
  Local Abbreviation one := (const_mx 1 : 'cV['F_2]_n).

  Variable beta : int.
  Hypotheses (Hb0 : 0 < beta) (Hbl : (beta %| l)%Z).
  Hypotheses (Hb8 : (beta %% 8)%Z = 1) (Hb3 : (beta %% 3)%Z = 2).
  Hypothesis HK0 : Kmx l *m oneB l beta = 0.

  Let b0 : beta != 0. Proof. by rewrite gt_eqF. Qed.

  Lemma gu_oneB : gu (oneB l beta) = beta.
  Proof.
    have Hg := gu_pos (oneB l beta).
    rewrite -(gtz0_abs Hg) -(gtz0_abs Hb0); congr Posz.
    apply: eq_logn; rewrite ?absz_gt0 ?(lt0r_neq0 Hg) ?b0 // => p pP.
    rewrite -!/(vz p _).
    case: (pickP (fun j => q j == p)) => [ j /eqP <- | Hn ].
    - by rewrite vz_gu_q (vz_b_q Hl Hb0 Hbl).
    - have Hn' : forall j, q j != p by move=> j; rewrite Hn.
      by rewrite vz_gu_out // (vz_b_out Hl Hbl).
  Qed.

  Lemma gamma_inf : locsol_inf l (beta, 1).
  Proof.
    have Hl0 := l_pos' Hl.
    exists (l%:~R); rewrite /= subrr; split; [ right | split; [ by left | right ] ].
    - by apply: mulr_gt0; rewrite ltr0z.
    - apply: mulr_gt0; last by rewrite ltr0z mulr1.
      by apply: addr_gt0; rewrite ?mulr_gt0 ?ltr0z.
  Qed.

  Let nd1 (p : nat) : prime p -> ~~ (p%:Z %| 1)%Z.
  Proof. by move=> pP; rewrite dvdz1 /=; apply/negP => /eqP E; move: pP; rewrite E. Qed.

  Lemma gamma_two : locsol l 2 (beta, 1).
  Proof.
    have pP : prime 2 by [].
    have Hb2 : ~~ ((2%N)%:Z %| beta)%Z by apply: (ndvd_mod Hb8).
    have [ U1 U2 ] := sol_O l.
    apply: (transfer_usq (d' := (1, 1)) pP (@prim1 2 0 1 1 1 pP isT) U1 U2 Hb2 (nd1 pP)).
    - apply/usq_two; [ exact: (qunit_iz Hb2) | exact: (qunit_iz (nd1 pP)) | ].
      have : ((8%N)%:Z %| beta - 1)%Z.
      { apply/dvdzP; exists (beta %/ 8)%Z; rewrite {1}(divz_eq beta 8) Hb8; ring. }
      by move/(dvd_iz 8); rewrite iz_add iz_opp.
    - exact: usq_refl.
  Qed.

  Lemma gamma_three : locsol l 3 (beta, 1).
  Proof.
    have pP : prime 3 by [].
    have Hb3' : ~~ ((3%N)%:Z %| beta)%Z by apply: (ndvd_mod Hb3).
    have [ U1 U2 ] := sol_Tl l.
    apply: (transfer_usq (d' := (l, 1)) pP (@prim1 3 1 1 0 2 pP isT) U1 U2 Hb3' (nd1 pP)).
    - apply/(usq_odd (primeZ pP)); [ by move=> [ t Ht ]; simpl in Ht; lia | exact: (qunit_iz Hb3') | exact: (qunit_iz (l_ndvd3 Hl)) | ].
      exists 1%ZZ.
      have : ((3%N)%:Z %| beta - l)%Z.
      { apply/dvdzP; exists ((beta %/ 3)%Z - (l %/ 3)%Z).
        rewrite {1}(divz_eq beta 3) {1}(divz_eq l 3) Hb3 (l_mod3 Hl); ring. }
      move/(dvd_iz 3); rewrite iz_add iz_opp => [ [ t Ht ] ]; exists t; cbn [fst]; lia.
    - exact: usq_refl.
  Qed.

  Lemma gamma_q (i : 'I_n) : locsol l (q i) (beta, 1).
  Proof.
    have qP := qi_prime i; have qo := qi_odd Hl i.
    have Hrow : oneB l beta i 0 * nbit (gi i one) (q i) + nbit (gi i (oneB l beta)) (q i) = 0.
    { by rewrite -(K_mul Hl) HK0 mxE. }
    have Hsplit := gu_split (oneB l beta) i; rewrite gu_oneB in Hsplit.
    have ndL : ~~ ((q i)%:Z %| gi i one)%Z by apply: gi_ndvd.
    have ndB : ~~ ((q i)%:Z %| gi i (oneB l beta))%Z by apply: gi_ndvd.
    case: (F2_cases (oneB l beta i 0)) => Eb; rewrite Eb in Hrow Hsplit.
    - rewrite mul0r add0r in Hrow; rewrite /= expn0 mul1r in Hsplit.
      rewrite -Hsplit in Hrow.
      have nb : ~~ ((q i)%:Z %| beta)%Z by rewrite Hsplit.
      have Hleg : legendre (beta * 1) (q i) = 1.
      { by rewrite mulr1; apply/eqP; rewrite -(nbit_eq0 nb) Hrow. }
      have [ U1 U2 ] := sol_O l.
      apply: (transfer_usq (d' := (1, 1)) qP (@prim1 _ 0 1 1 1 qP isT) U1 U2 nb (nd1 qP)).
      + exact: (usq_leg qP qo nb (nd1 qP) Hleg).
      + exact: usq_refl.
    - rewrite mul1r in Hrow; rewrite /= expn1 in Hsplit.
      have Hleg : legendre (gi i (oneB l beta) * gi i one) (q i) = 1.
      { apply/eqP; rewrite -(nbit_eq0 (odd_mul qP ndB ndL)) (nbitM qP qo ndB ndL) addrC Hrow. done. }
      have Us := usq_leg qP qo ndB ndL Hleg.
      have [ U1 U2 ] := sol_Tl l.
      apply: (locsol_transfer qP (@prim1 _ 1 1 0 2 qP isT) U1 U2) => k.
      have [ a [ Ha Da ] ] := lift_sq qP ndB Us k.
      exists a, 1; split => //; split; first exact: nd1.
      split; last by rewrite /= expr1n mulr1 subrr dvdz0.
      have E : beta - l * a ^+ 2 = (q i)%:Z * (gi i (oneB l beta) - gi i one * a ^+ 2).
      { by rewrite mulrBr -Hsplit mulrA -(l_split Hl i). }
      by rewrite /= E; apply: dvdz_mull.
  Qed.

  Theorem gamma_sel : in_Sel2 l (beta, 1).
  Proof.
    split; first exact: b0; split; first by []; split; first exact: gamma_inf.
    move=> p pP.
    case: (eqVneq p 2%N) => [ -> | p2 ]; first exact: gamma_two.
    case: (eqVneq p 3%N) => [ -> | p3 ]; first exact: gamma_three.
    case: (pickP (fun j => q j == p)) => [ j /eqP <- | Hn ]; first exact: gamma_q.
    have Hn' : forall j, q j != p by move=> j; rewrite Hn.
    have Hpl : ~~ (p%:Z %| l)%Z by rewrite dvdzE /=; apply: (notin_qs Hl pP Hn').
    have Hpb : ~~ (p%:Z %| beta)%Z by apply: contra Hpl => H; apply: dvdz_trans H Hbl.
    exact: (gamma_good pP p2 p3 Hpl Hpb).
  Qed.

End Gamma.

(** * Lemma par:descent *)

Theorem descent_main (l beta : int) :
  admissible_l l -> 0 < beta -> (beta %| l)%Z -> beta != l ->
  (beta %% 8)%Z = 1 -> (beta %% 3)%Z = 2 ->
  Kmx l *m oneB l beta = 0 ->
  (forall u : 'cV['F_2]_(nq l), Kmx l *m u = 0 ->
     u = 0 \/ u = const_mx 1 \/ u = oneB l beta \/ u = const_mx 1 + oneB l beta) ->
  (forall u : 'cV['F_2]_(nq l), Kmx l *m u != lamv l) ->
  in_Sel2 l (beta, 1) /\
  (forall d, in_Sel2 l d -> in_span3 (tors_Tl l) (tors_T3 l) (beta, 1) d) /\
  ~ in_span2 (tors_Tl l) (tors_T3 l) (beta, 1).
Proof.
  move=> Hl Hb0 Hbl Hbl' Hb8 Hb3 HK0 Hker Hlam.
  have Hb1 : beta != 1 by apply/eqP => E; move: Hb3; rewrite E.
  split; first exact: (gamma_sel Hl Hb0 Hbl Hb8 Hb3 HK0).
  split; first by move=> d; apply: (upper_bound Hl Hb0 Hbl Hker Hlam).
  exact: (gamma_not_tors Hl Hb0 Hbl Hb1 Hbl').
Qed.



(** The conclusion in the form consumed by [TwoConverse_El_point]: under the
    elementary 2-converse, E_l has a rational point with x in beta Q^x2. *)
Corollary descent_El_point : TwoConverseSel2_El ->
  forall l beta : int, admissible_l l -> 0 < beta -> (beta %| l)%Z -> beta != l ->
  (beta %% 8)%Z = 1 -> (beta %% 3)%Z = 2 ->
  Kmx l *m oneB l beta = 0 ->
  (forall u : 'cV['F_2]_(nq l), Kmx l *m u = 0 ->
     u = 0 \/ u = const_mx 1 \/ u = oneB l beta \/ u = const_mx 1 + oneB l beta) ->
  (forall u : 'cV['F_2]_(nq l), Kmx l *m u != lamv l) ->
  forall b' : rat, sqc b' beta -> El_point (l%:~R : rat) b'.
Proof.
  move=> H2c l beta Hl Hb0 Hbl Hbl' Hb8 Hb3 HK0 Hker Hlam.
  have [ H1 [ H2 H3 ] ] := descent_main Hl Hb0 Hbl Hbl' Hb8 Hb3 HK0 Hker Hlam.
  exact: (TwoConverse_El_point H2c Hl H1 H2 H3).
Qed.
