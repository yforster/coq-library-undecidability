(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The truncated formal logarithm on the kernel of reduction: the field
   O_F2 of OrdHyps (05-elliptic.tex, Prop ell:formal, eq. ell:truncation)
   from E2 (PLAN.md, Phase 2D, task P12b; F2_DESIGN.md, steps V1 to V6).

   ROUTE (F2_DESIGN.md, route (b)). The recipe [ct] is the series of the
   lemniscatic integral  int dt / sqrt(1 - 4 aE t^4)  (TruncSeries.v). On
   the curve y^2 = x^3 + aE x with z = -x/y the square root is the
   rational function  s = (x^2 - aE)/(x^2 + aE), and Euler's addition
   theorem holds exactly:
       z(P1 + P2) (1 + 4 aE z1^2 z2^2) = z1 s2 + z2 s1
   ([euler_chord], [euler_tangent]: field identities with explicit
   polynomial certificates computed by sympy; [euler_pts] for points).
   1. [s_approx]: on the kernel (v(z) >= k >= 1), s = S_K(z) mod p^((K+1)k)
      (Hensel: s^2 = 1 - 4 aE z^4 exactly, S_K^2 = 1 - 4 aE z^4 mod z^(K+1)).
   2. [ellK_add]: v(L_K(z3) - L_K(z1) - L_K(z2)) >= (K+1) k for kernel points,
      by evaluating the formal addition theorem [log_add_formal] (TruncSeries.v)
      at lambda = pi = p^k with u_i = z_i / pi; integrality needs only
      v(aE) >= 0, p odd and K < p.
   3. [ellK_mul]: L_K(z(jR)) = j L_K(z(R)) mod p^((K+1)k).
   4. [Lk_val]: v(L_K(z)) = v(z) for v(z) >= 1.
   5. [O_F2_core]: W = gcd(n, n') P is in the kernel (Bezout, [add_kern]);
      with n = d m, n' = d m', v_p(m') = 0, v(z(n'P)) = v(z(W)) = k
      ([kernel_mul]) and the ratio error has valuation >= K k >= K.
   6. [O_F2_of_E2]: both curves (sg = true via the conjugate place,
      [conj_place]); [O_F2_mkData] for the explicit data.
   Good reduction is not used: p \notin S_E is a dummy hypothesis. *)

From Stdlib Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData RatVal ExplicitData
                 KernelReduction GroupLaw OrdPlaces TruncSeries.
Import Order.TTheory GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.
Local Open Scope ring_scope.

(** * Euler's addition formula on y^2 = x^3 + a x (exact identities) *)

(* discharging the nonzero side conditions of [field] *)
Ltac nzt := rewrite ?oppr_eq0 ?mulf_eq0 ?expf_eq0 /= ?negb_or;
            repeat (apply/andP; split); by [].

Section euler_curve.

  Variable K0 : fieldType.
  Variables (a x1 y1 x2 y2 : K0).

  Definition sf (x : K0) : K0 := (x ^+ 2 - a) / (x ^+ 2 + a).
  Definition zf (x y : K0) : K0 := - x / y.

  Lemma euler_chord_cert :
    x2 - x1 != 0 -> x1 - x2 != 0 -> y1 != 0 -> y2 != 0 -> x1 ^+ 2 + a != 0 -> x2 ^+ 2 + a != 0 ->
    a + x1 ^+ 2 != 0 -> a + x2 ^+ 2 != 0 ->
    let l := (y2 - y1) / (x2 - x1) in
    let x3 := l ^+ 2 - x1 - x2 in
    let y3 := l * (x1 - x3) - y1 in
    - x3 * (1 + 4%:R * a * zf x1 y1 ^+ 2 * zf x2 y2 ^+ 2)
      - y3 * (zf x1 y1 * sf x2 + zf x2 y2 * sf x1)
    = ((4%:R * x1 ^+ 5 * x2 ^+ 4 * a + 4%:R * x1 ^+ 5 * x2 ^+ 2 * a ^+ 2 - 4%:R * x1 ^+ 4 * x2 ^+ 5 * a - 4%:R * x1 ^+ 4 * x2 ^+ 3 * a ^+ 2 - 4%:R * x1 ^+ 4 * x2 ^+ 2 * y2 ^+ 2 * a + 2%:R * x1 ^+ 3 * y1 ^+ 2 * x2 ^+ 2 * y2 ^+ 2 + 3%:R * x1 ^+ 3 * y1 * x2 ^+ 5 * y2 + 4%:R * x1 ^+ 3 * y1 * x2 ^+ 3 * y2 * a - 5%:R * x1 ^+ 3 * y1 * x2 ^+ 2 * y2 ^+ 3 + x1 ^+ 3 * y1 * x2 * y2 * a ^+ 2 + x1 ^+ 3 * y1 * y2 ^+ 3 * a - 4%:R * x1 ^+ 3 * x2 ^+ 5 * y2 ^+ 2 + 4%:R * x1 ^+ 3 * x2 ^+ 4 * a ^+ 2 - 2%:R * x1 ^+ 3 * x2 ^+ 3 * y2 ^+ 2 * a + 4%:R * x1 ^+ 3 * x2 ^+ 2 * y2 ^+ 4 + 4%:R * x1 ^+ 3 * x2 ^+ 2 * a ^+ 3 - 2%:R * x1 ^+ 3 * x2 * y2 ^+ 2 * a ^+ 2 - 2%:R * x1 ^+ 3 * y2 ^+ 4 * a + x1 ^+ 2 * y1 ^+ 3 * x2 ^+ 3 * y2 + x1 ^+ 2 * y1 ^+ 3 * x2 * y2 * a - 4%:R * x1 ^+ 2 * y1 ^+ 2 * x2 ^+ 3 * y2 ^+ 2 - 4%:R * x1 ^+ 2 * y1 ^+ 2 * x2 * y2 ^+ 2 * a - 2%:R * x1 ^+ 2 * y1 * x2 ^+ 6 * y2 - 2%:R * x1 ^+ 2 * y1 * x2 ^+ 4 * y2 * a + 5%:R * x1 ^+ 2 * y1 * x2 ^+ 3 * y2 ^+ 3 + 5%:R * x1 ^+ 2 * y1 * x2 * y2 ^+ 3 * a + 2%:R * x1 ^+ 2 * x2 ^+ 6 * y2 ^+ 2 - 4%:R * x1 ^+ 2 * x2 ^+ 5 * a ^+ 2 + 8%:R * x1 ^+ 2 * x2 ^+ 4 * y2 ^+ 2 * a - 2%:R * x1 ^+ 2 * x2 ^+ 3 * y2 ^+ 4 - 4%:R * x1 ^+ 2 * x2 ^+ 3 * a ^+ 3 + 2%:R * x1 ^+ 2 * x2 ^+ 2 * y2 ^+ 2 * a ^+ 2 - 2%:R * x1 ^+ 2 * x2 * y2 ^+ 4 * a + 2%:R * x1 * y1 ^+ 2 * x2 ^+ 2 * y2 ^+ 2 * a - 3%:R * x1 * y1 * x2 ^+ 5 * y2 * a - 4%:R * x1 * y1 * x2 ^+ 3 * y2 * a ^+ 2 - 5%:R * x1 * y1 * x2 ^+ 2 * y2 ^+ 3 * a - x1 * y1 * x2 * y2 * a ^+ 3 + x1 * y1 * y2 ^+ 3 * a ^+ 2 - 4%:R * x1 * x2 ^+ 5 * y2 ^+ 2 * a + 2%:R * x1 * x2 ^+ 3 * y2 ^+ 2 * a ^+ 2 + 4%:R * x1 * x2 ^+ 2 * y2 ^+ 4 * a + 2%:R * x1 * x2 * y2 ^+ 2 * a ^+ 3 - 2%:R * x1 * y2 ^+ 4 * a ^+ 2 - y1 ^+ 3 * x2 ^+ 3 * y2 * a - y1 ^+ 3 * x2 * y2 * a ^+ 2 + 2%:R * y1 ^+ 2 * x2 ^+ 3 * y2 ^+ 2 * a + 2%:R * y1 ^+ 2 * x2 * y2 ^+ 2 * a ^+ 2 + 2%:R * y1 * x2 ^+ 6 * y2 * a + 2%:R * y1 * x2 ^+ 4 * y2 * a ^+ 2 - y1 * x2 ^+ 3 * y2 ^+ 3 * a - y1 * x2 * y2 ^+ 3 * a ^+ 2) * (y1 ^+ 2 - x1 ^+ 3 - a * x1) + (- 4%:R * x1 ^+ 7 * x2 ^+ 2 * a - 3%:R * x1 ^+ 6 * y1 * x2 ^+ 2 * y2 - x1 ^+ 6 * y1 * y2 * a + 4%:R * x1 ^+ 6 * x2 ^+ 2 * y2 ^+ 2 - 4%:R * x1 ^+ 6 * x2 * a ^+ 2 - 2%:R * x1 ^+ 6 * y2 ^+ 2 * a + 2%:R * x1 ^+ 5 * y1 * x2 ^+ 3 * y2 + 8%:R * x1 ^+ 5 * y1 * x2 * y2 * a + 8%:R * x1 ^+ 5 * x2 ^+ 4 * a - 2%:R * x1 ^+ 5 * x2 ^+ 3 * y2 ^+ 2 - 2%:R * x1 ^+ 5 * x2 * y2 ^+ 2 * a - 8%:R * x1 ^+ 4 * y1 * x2 ^+ 2 * y2 * a - 4%:R * x1 ^+ 4 * x2 ^+ 5 * a + 8%:R * x1 ^+ 4 * x2 ^+ 2 * y2 ^+ 2 * a - 4%:R * x1 ^+ 4 * x2 * a ^+ 3 - 4%:R * x1 ^+ 4 * y2 ^+ 2 * a ^+ 2 - x1 ^+ 3 * y1 * x2 ^+ 2 * y2 ^+ 3 + 8%:R * x1 ^+ 3 * y1 * x2 * y2 * a ^+ 2 + x1 ^+ 3 * y1 * y2 ^+ 3 * a + 8%:R * x1 ^+ 3 * x2 ^+ 4 * a ^+ 2 - 2%:R * x1 ^+ 3 * x2 ^+ 3 * y2 ^+ 2 * a + 4%:R * x1 ^+ 3 * x2 ^+ 2 * a ^+ 3 - 2%:R * x1 ^+ 3 * x2 * y2 ^+ 2 * a ^+ 2 - 5%:R * x1 ^+ 2 * y1 * x2 ^+ 2 * y2 * a ^+ 2 + x1 ^+ 2 * y1 * y2 * a ^+ 3 - 4%:R * x1 ^+ 2 * x2 ^+ 5 * a ^+ 2 + 4%:R * x1 ^+ 2 * x2 ^+ 2 * y2 ^+ 2 * a ^+ 2 - 2%:R * x1 ^+ 2 * y2 ^+ 2 * a ^+ 3 - 2%:R * x1 * y1 * x2 ^+ 3 * y2 * a ^+ 2 - x1 * y1 * x2 ^+ 2 * y2 ^+ 3 * a + x1 * y1 * y2 ^+ 3 * a ^+ 2) * (y2 ^+ 2 - x2 ^+ 3 - a * x2))
      / (- (y1 ^+ 2 * y2 ^+ 2 * (a + x1 ^+ 2) * (a + x2 ^+ 2) * (x1 - x2) ^+ 3)).
  Proof. move=> H1 H2 H3 H4 H5 H6 H7 H8 l x3 y3; rewrite /y3 /x3 /l /zf /sf; field by nzt. Qed.

  Lemma euler_chord :
    y1 * y1 = x1 ^+ 3 + a * x1 -> y2 * y2 = x2 ^+ 3 + a * x2 ->
    x2 - x1 != 0 -> y1 != 0 -> y2 != 0 -> x1 ^+ 2 + a != 0 -> x2 ^+ 2 + a != 0 ->
    let l := (y2 - y1) / (x2 - x1) in
    let x3 := l ^+ 2 - x1 - x2 in
    let y3 := l * (x1 - x3) - y1 in
    - x3 * (1 + 4%:R * a * zf x1 y1 ^+ 2 * zf x2 y2 ^+ 2)
    = y3 * (zf x1 y1 * sf x2 + zf x2 y2 * sf x1).
  Proof.
    move=> C1 C2 H1 H3 H4 H5 H6 l x3 y3.
    have H2 : x1 - x2 != 0 by rewrite -oppr_eq0 opprB.
    have H7 : a + x1 ^+ 2 != 0 by rewrite addrC.
    have H8 : a + x2 ^+ 2 != 0 by rewrite addrC.
    have E := euler_chord_cert H1 H2 H3 H4 H5 H6 H7 H8.
    have h1 : y1 ^+ 2 - x1 ^+ 3 - a * x1 = 0 by rewrite expr2 C1; ring.
    have h2 : y2 ^+ 2 - x2 ^+ 3 - a * x2 = 0 by rewrite expr2 C2; ring.
    rewrite h1 h2 !mulr0 addr0 mul0r in E.
    by apply/eqP; rewrite -subr_eq0; apply/eqP.
  Qed.

  Lemma euler_tangent_cert :
    2%:R != 0 :> K0 -> 4%:R != 0 :> K0 -> y1 != 0 -> x1 ^+ 2 + a != 0 -> a + x1 ^+ 2 != 0 ->
    let l := (3%:R * x1 ^+ 2 + a) / (2%:R * y1) in
    let x3 := l ^+ 2 - 2%:R * x1 in
    let y3 := l * (x1 - x3) - y1 in
    - x3 * (1 + 4%:R * a * zf x1 y1 ^+ 2 * zf x1 y1 ^+ 2)
      - y3 * (zf x1 y1 * sf x1 + zf x1 y1 * sf x1)
    = ((36%:R * x1 ^+ 7 * a + 27%:R * x1 ^+ 6 * y1 ^+ 2 + 24%:R * x1 ^+ 5 * a ^+ 2 - 23%:R * x1 ^+ 4 * y1 ^+ 2 * a + 4%:R * x1 ^+ 3 * a ^+ 3 - 3%:R * x1 ^+ 2 * y1 ^+ 2 * a ^+ 2 + 16%:R * x1 * y1 ^+ 4 * a - y1 ^+ 2 * a ^+ 3) * (y1 ^+ 2 - x1 ^+ 3 - a * x1)) / (4%:R * y1 ^+ 6 * (a + x1 ^+ 2)).
  Proof. move=> H1 H2 H3 H4 H5 l x3 y3; rewrite /y3 /x3 /l /zf /sf; field by nzt. Qed.

  Lemma euler_tangent :
    2%:R != 0 :> K0 -> 4%:R != 0 :> K0 ->
    y1 * y1 = x1 ^+ 3 + a * x1 -> y1 != 0 -> x1 ^+ 2 + a != 0 ->
    let l := (3%:R * x1 ^+ 2 + a) / (2%:R * y1) in
    let x3 := l ^+ 2 - 2%:R * x1 in
    let y3 := l * (x1 - x3) - y1 in
    - x3 * (1 + 4%:R * a * zf x1 y1 ^+ 2 * zf x1 y1 ^+ 2)
    = y3 * (zf x1 y1 * sf x1 + zf x1 y1 * sf x1).
  Proof.
    move=> H1 H2 C1 H3 H4 l x3 y3.
    have H5 : a + x1 ^+ 2 != 0 by rewrite addrC.
    have E := euler_tangent_cert H1 H2 H3 H4 H5.
    have h1 : y1 ^+ 2 - x1 ^+ 3 - a * x1 = 0 by rewrite expr2 C1; ring.
    rewrite h1 !mulr0 mul0r in E.
    by apply/eqP; rewrite -subr_eq0; apply/eqP.
  Qed.

  (* the square root of 1 - 4 a z^4 *)
  Lemma sf_sq : y1 * y1 = x1 ^+ 3 + a * x1 -> x1 != 0 -> y1 != 0 -> x1 ^+ 2 + a != 0 ->
    sf x1 ^+ 2 = 1 - 4%:R * a * zf x1 y1 ^+ 4.
  Proof.
    move=> C1 H1 H2 H3.
    have E : y1 ^+ 4 = x1 ^+ 2 * (x1 ^+ 2 + a) ^+ 2.
    { have -> : y1 ^+ 4 = (y1 * y1) ^+ 2 by ring.
      rewrite C1; ring. }
    rewrite /sf /zf; apply/eqP; rewrite -subr_eq0; apply/eqP.
    have -> : ((x1 ^+ 2 - a) / (x1 ^+ 2 + a)) ^+ 2 - (1 - 4%:R * a * (- x1 / y1) ^+ 4)
            = ((x1 ^+ 2 - a) ^+ 2 * y1 ^+ 4 - ((x1 ^+ 2 + a) ^+ 2 * y1 ^+ 4 - 4%:R * a * x1 ^+ 4 * (x1 ^+ 2 + a) ^+ 2))
              / ((x1 ^+ 2 + a) ^+ 2 * y1 ^+ 4) by field by nzt.
    by rewrite E; apply/eqP; rewrite mulf_eq0; apply/orP; left; apply/eqP; ring.
  Qed.

End euler_curve.

Lemma two_KRF : 2%:R != 0 :> KRF. Proof. exact: KRF_nat_neq0. Qed.
Lemma four_KRF : 4%:R != 0 :> KRF. Proof. exact: KRF_nat_neq0. Qed.

Lemma aEK : (aE : KRF) = aK. Proof. by rewrite aK.unlock. Qed.

Lemma int_dbl_neg (a : int) : a < 0 -> a + a < 0. Proof. move=> H; ilia. Qed.
Lemma int_le3 (k : int) : 1 <= k -> k <= 3 * k. Proof. move=> H; ilia. Qed.
Lemma int_le0 (k : int) : 1 <= k -> 0 <= k. Proof. move=> H; ilia. Qed.

Lemma horner_sq_sub (S : {poly KRF}) (z c : KRF) :
  (S ^+ 2 - (1 - c%:P * 'X^4)).[z] = S.[z] ^+ 2 - (1 - c * z ^+ 4).
Proof. by rewrite -horner_evalE !(rmorphB, rmorphM, rmorphXn, rmorph1) /= !horner_evalE hornerC hornerX. Qed.

Lemma horner_sub1 (S : {poly KRF}) (z : KRF) : (S - 1).[z] = S.[z] - 1.
Proof. by rewrite -horner_evalE !(rmorphB, rmorph1) /= !horner_evalE. Qed.

Lemma horner_Qe (c a b x : KRF) :
  (1 + c%:P * (a%:P * 'X) ^+ 2 * (b%:P * 'X) ^+ 2).[x] = 1 + c * (a * x) ^+ 2 * (b * x) ^+ 2.
Proof. by rewrite -horner_evalE !(rmorphD, rmorphM, rmorphXn, rmorph1) /= !horner_evalE !hornerC hornerX. Qed.

Lemma kern_neg (v : qe rat -> int) (P : pt rat) : kern v P -> kern v (pt_neg P).
Proof. by case: P => [ [ x y ] | ]. Qed.

(** * The logarithm polynomials over F *)

Definition Lk (K : nat) : {poly KRF} := LK aK K.
Definition Sk (K : nat) : {poly KRF} := SP aK K.
Definition Wk (K : nat) : {poly KRF} := wP aK K.

(* the square root  s = (x^2 - aE)/(x^2 + aE)  of 1 - 4 aE z^4 *)
Definition sk (P : pt rat) : KRF := if P is Some (x, _) then sf aK (x : KRF) else 1.

Lemma ct_K (t : nat) : (ct t : KRF) = ct_gen aK t.
Proof. by rewrite aK.unlock. Qed.

Lemma ellK_horner (K : nat) (Z : qe rat) : ellK false K Z = (Lk K).[Z : KRF].
Proof.
  rewrite /ellK (@horner_coef_wide _ K.+1) ?size_poly //.
  rewrite -(big_mkord xpredT (fun i => (Lk K)`_i * (Z : KRF) ^+ i)).
  rewrite [in RHS]big_ltn // /Lk LK_0 mul0r add0r.
  apply: eq_big_nat => i /andP [_ Hi].
  by rewrite coef_poly Hi qe_rat_id /= ct_K.
Qed.

(** * Valuations: the kernel of reduction and the logarithm *)

Section kernel_log.

  Variable v : qe rat -> int.
  Variable p : nat.
  Hypothesis Hp : prime p.
  Hypothesis Hv : is_place_above v p.
  Hypothesis Hp2 : (2 < p)%N.

  Definition Ov (x : KRF) : Prop := vge v 0 x.

  Lemma HOv : sring Ov.
  Proof.
    split.
    - exact: vge0.
    - exact: vge_1 Hv.
    - move=> x y Hx Hy; exact (vge_add Hv Hx Hy).
    - move=> x Hx; exact (vge_opp Hv Hx).
    - move=> x y Hx Hy; have H := vge_mul Hv Hx Hy; rewrite addr0 in H; exact H.
  Qed.

  Lemma Ov_aK : Ov aK. Proof. exact: vge_aE Hv. Qed.

  Lemma v_unit_nat (t : nat) : (0 < t < p)%N -> (t%:R : KRF) != 0 /\ v (t%:R : KRF) = 0.
  Proof.
    move=> /andP [H0 Ht]; split; first exact: KRF_nat_neq0.
    refine (v_coprime Hv H0 _).
    rewrite coprime_sym prime_coprime //; apply/negP => /(dvdn_leq H0).
    by rewrite leqNgt Ht.
  Qed.

  Lemma Ov_inv_nat (t : nat) : (0 < t < p)%N -> Ov (t%:R^-1).
  Proof.
    move=> Ht; have [H0 H1] := v_unit_nat Ht.
    by right; rewrite (vV Hv H0) H1 oppr0.
  Qed.

  Lemma v2 : (2%:R : KRF) != 0 /\ v (2%:R : KRF) = 0.
  Proof. by apply: v_unit_nat; rewrite /= Hp2. Qed.

  Lemma vge_exp (k : int) (x : KRF) (n : nat) : vge v k x -> vge v (n%:Z * k) (x ^+ n).
  Proof.
    move=> Hx; elim: n => [ | n IH ]; first by rewrite mul0r expr0; exact: vge_1 Hv.
    rewrite exprS -addn1 PoszD mulrDl mul1r addrC; exact (vge_mul Hv Hx IH).
  Qed.

  Lemma vge_eval (d : {poly KRF}) (n : nat) (k : int) (x : KRF) :
    pint Ov d -> tc n d 0 -> vge v k x -> 0 <= k -> vge v (n%:Z * k) d.[x].
  Proof.
    move=> Hd H Hx Hk.
    have Ox : Ov x by apply: vge_le Hk Hx.
    have [r [Hr ->]] := eval_tc0 HOv Hd H Ox.
    by have := vge_mul Hv (vge_exp n Hx) Hr; rewrite addr0.
  Qed.

  Lemma vge_div (k : int) (x y : KRF) : vge v k x -> y != 0 -> vge v (k - v y) (x / y).
  Proof.
    move=> [ -> | Hx ] Hy; first by rewrite mul0r; left.
    case: (eqVneq x 0) => [ -> | nx ]; first by rewrite mul0r; left.
    by right; rewrite (vdiv Hv) // lerD2r.
  Qed.

  Lemma xa_neq0 (x : KRF) : x != 0 -> v x < 0 -> x ^+ 2 + aK != 0 /\ v (x ^+ 2 + aK) = v x + v x.
  Proof.
    move=> Hx Hvx.
    have H2 : x ^+ 2 != 0 by rewrite expf_neq0.
    have Hv2 : v (x ^+ 2) = v x + v x by rewrite expr2 (vM Hv).
    have Hlt : v (x ^+ 2) < 0 by rewrite Hv2; exact: int_dbl_neg.
    have [H1 H3] := vge_strict Hv H2 Ov_aK Hlt.
    by rewrite H3 Hv2.
  Qed.

  (** Euler's formula for points of the kernel *)
  Lemma zmul_eq (x y D R : KRF) : y != 0 -> - x * D = y * R -> (- x / y) * D = R.
  Proof. move=> Hy E; rewrite mulrAC E; field. Qed.

  Lemma euler_pts (P1 P2 : pt rat) (k : int) : 1 <= k ->
    onp P1 -> onp P2 -> onp (ec_add P1 P2) -> kern v P1 -> kern v P2 ->
    vge v k (zk P1) -> vge v k (zk P2) ->
    zk (ec_add P1 P2) * (1 + 4%:R * aK * zk P1 ^+ 2 * zk P2 ^+ 2) = zk P1 * sk P2 + zk P2 * sk P1.
  Proof.
    move=> Hk Hc1 Hc2 Hc3 Hk1 Hk2 hz1 hz2.
    have [Hk3 _] := add_kern Hv Hk Hc1 Hc2 Hc3 Hk1 Hk2 hz1 hz2.
    move: Hc1 Hc2 Hc3 Hk1 Hk2 Hk3; clear hz1 hz2.
    case: P1 => [ [ x1 y1 ] | ]; last by move=> *; rewrite /=; ring.
    case: P2 => [ [ x2 y2 ] | ]; last by move=> *; rewrite /=; ring.
    move=> Hc1 Hc2 Hc3 [Hx1 Hvx1] [Hx2 Hvx2] Hk3.
    have C1 := on_curveK Hc1; have C2 := on_curveK Hc2.
    have [Hy1 _] := kv Hv C1 Hx1 Hvx1; have [Hy2 _] := kv Hv C2 Hx2 Hvx2.
    have [Hxa1 _] := xa_neq0 Hx1 Hvx1; have [Hxa2 _] := xa_neq0 Hx2 Hvx2.
    case: (eqVneq x1 x2) => [ Ex | Nx ].
    - case: (eqVneq y1 (- y2)) => [ Ey | Ny ].
      + rewrite (ec_add_opp Ex Ey) /=; subst x2 y1.
        by rewrite /zk /sk invrN; ring.
      + have Ey : y2 = y1.
        { move: C1 C2; rewrite -Ex => H1 H2.
          have : ((y2 : KRF) - y1) * (y2 + y1) = 0.
          { rewrite mulrDr !mulrBl H1 H2 (mulrC (y1 : KRF) y2); ring. }
          move/eqP; rewrite mulf_eq0 => /orP [ /eqP H | /eqP H ].
          - by apply/eqP; rewrite -subr_eq0 H.
          - exfalso; move: Ny; rewrite (_ : y1 = - y2) ?eqxx //.
            by apply/eqP; rewrite -addr_eq0 addrC H. }
        subst x2 y2.
        move: Hc3 Hk3; rewrite (ec_add_tan erefl Ny) => Hc3 [Hx3 Hvx3].
        have [Hy3 _] := kv Hv (on_curveK Hc3) Hx3 Hvx3.
        move: Hy3; rewrite /slope_tan aEK => Hy3.
        have E := euler_tangent two_KRF four_KRF C1 Hy1 Hxa1.
        rewrite /=; apply: zmul_eq Hy3 _; exact: E.
    - move: Hc3 Hk3; rewrite (ec_add_ch y1 y2 Nx) => Hc3 [Hx3 Hvx3].
      have [Hy3 _] := kv Hv (on_curveK Hc3) Hx3 Hvx3.
      move: Hy3; rewrite /slope_ch => Hy3.
      have Hx : (x2 : KRF) - x1 != 0 by rewrite subr_eq0 eq_sym.
      have E := euler_chord C1 C2 Hx Hy1 Hy2 Hxa1 Hxa2.
      rewrite /=; apply: zmul_eq Hy3 _; exact: E.
  Qed.

  (** The truncated logarithm at level K < p *)
  Variable K : nat.
  Hypothesis HKp : (K < p)%N.

  Lemma pint_Lk : pint Ov (Lk K).
  Proof.
    apply: (pint_LK HOv KRF_nat_neq0 Ov_aK) => t /andP [Ht0 HtK].
    apply: Ov_inv_nat; rewrite Ht0; exact: leq_ltn_trans HtK HKp.
  Qed.

  Lemma pint_Sk : pint Ov (Sk K). Proof. exact: (pint_SP HOv Ov_aK K). Qed.

  Lemma pint_scl (u : KRF) : Ov u -> pint Ov (scl u).
  Proof. by move=> Hu; apply: (pint_mul HOv (pint_C HOv Hu) (pint_X HOv)). Qed.

  Lemma Ov4a : Ov (4%:R * aK).
  Proof. exact: (srmul HOv (O_nat HOv 4) Ov_aK). Qed.

  (* Hensel at the points: s = S_K(z) mod p^((K+1)k) *)
  Lemma s_approx (P : pt rat) (k : int) : 1 <= k -> onp P -> kern v P -> vge v k (zk P) ->
    vge v ((K.+1)%:Z * k) (sk P - (Sk K).[zk P]).
  Proof.
    have Hk0 : forall k : int, 1 <= k -> 0 <= k := int_le0.
    case: P => [ [ x y ] | ] Hk; last first.
    { move=> _ _ _; rewrite /= horner_coef0 /Sk SP0 subrr; exact: vge0. }
    move=> Hc [Hx Hvx] hz.
    have Hc' := on_curveK Hc.
    have [Hy _] := kv Hv Hc' Hx Hvx.
    have [Hxa Hvxa] := xa_neq0 Hx Hvx.
    set z := zk (Some (x, y)) in hz *.
    have Ss : sk (Some (x, y)) ^+ 2 = 1 - 4%:R * aK * z ^+ 4 := sf_sq Hc' Hx Hy Hxa.
    set s := sk (Some (x, y)) in Ss *; set t := (Sk K).[z].
    have Ht : vge v ((K.+1)%:Z * k) (t ^+ 2 - (1 - 4%:R * aK * z ^+ 4)).
    { have E : (Sk K ^+ 2 - (1 - (4%:R * aK)%:P * 'X^4)).[z] = t ^+ 2 - (1 - 4%:R * aK * z ^+ 4).
      { exact: horner_sq_sub. }
      rewrite -E; apply: vge_eval (Hk0 _ Hk).
      - apply: (pint_sub HOv (pint_exp HOv 2 pint_Sk)).
        apply: (pint_sub HOv (pint_1 HOv)); apply: (pint_mul HOv (pint_C HOv Ov4a) (pint_Xn HOv 4)).
      - exact: tc_sub0 (S_sq aK K).
      - exact: hz. }
    have hs1 : vge v 1 (s - 1).
    { have E : s - 1 = (- (2%:R * aK)) / (x ^+ 2 + aK) by rewrite /s /= /sf; field.
      rewrite E.
      have h := vge_div (vge_opp Hv (srmul HOv (O_nat HOv 2) Ov_aK)) Hxa.
      apply: vge_le h; rewrite Hvxa; move: Hvx; clear; move=> H; ilia. }
    have ht1 : vge v 1 (t - 1).
    { have E : t - 1 = (Sk K - 1).[z] := esym (horner_sub1 (Sk K) z).
      rewrite E; have h := vge_eval (pint_sub HOv pint_Sk (pint_1 HOv)) _ hz (Hk0 _ Hk).
      have T1 : tc 1 (Sk K - 1) 0.
      { constructor=> i; rewrite ltnS leqn0 => /eqP ->; by rewrite coefB coef1 /Sk SP0 subrr coef0. }
      have := h 1%N T1; apply: vge_le; rewrite mul1r; exact: Hk. }
    have [Hst Hvst] : s + t != 0 /\ v (s + t) = 0.
    { have E : s + t = 2%:R + ((s - 1) + (t - 1)) by ring.
      have [H20 Hv20] := v2.
      have Hlt : v (2%:R : KRF) < 1 by rewrite Hv20.
      have [H1 H2] := vge_strict Hv H20 (vge_add Hv hs1 ht1) Hlt.
      by rewrite E; split; [ exact H1 | rewrite H2 Hv20 ]. }
    have E : s - t = (- (t ^+ 2 - (1 - 4%:R * aK * z ^+ 4))) / (s + t).
    { rewrite -Ss; field. }
    rewrite E; exact (vge_div_unit Hv (vge_opp Hv Ht) Hst Hvst).
  Qed.

  Lemma vpow (n : nat) : (p%:R : KRF) ^+ n != 0 /\ v ((p%:R : KRF) ^+ n) = n%:Z.
  Proof.
    have Hp0 : (p%:R : KRF) != 0 by apply: KRF_nat_neq0; exact: prime_gt0.
    elim: n => [ | n [IH1 IH2] ].
    { by rewrite expr0 (v1 Hv); split; [ exact: oner_neq0 | ]. }
    rewrite exprS; split; first by rewrite mulf_neq0.
    by rewrite (vM Hv Hp0 IH1) IH2 (vP Hv) -addn1 PoszD addrC.
  Qed.

  Lemma vge_mulO (M : int) (x y : KRF) : Ov x -> vge v M y -> vge v M (x * y).
  Proof. by move=> Hx Hy; have H := vge_mul Hv Hx Hy; rewrite add0r in H; exact H. Qed.

  Lemma vge_mulOr (M : int) (x y : KRF) : vge v M x -> Ov y -> vge v M (x * y).
  Proof. by move=> Hx Hy; have H := vge_mul Hv Hx Hy; rewrite addr0 in H; exact H. Qed.

  (* additivity of the truncated logarithm on the kernel, precision (K+1) k *)
  Theorem ellK_add (P1 P2 : pt rat) (k : int) : 1 <= k ->
    onp P1 -> onp P2 -> onp (ec_add P1 P2) -> kern v P1 -> kern v P2 ->
    vge v k (zk P1) -> vge v k (zk P2) ->
    vge v ((K.+1)%:Z * k) ((Lk K).[zk (ec_add P1 P2)] - (Lk K).[zk P1] - (Lk K).[zk P2]).
  Proof.
    move=> Hk Hc1 Hc2 Hc3 Hk1 Hk2 hz1 hz2.
    have Hk0 := int_le0 Hk.
    have [Hk3 hz3'] := add_kern Hv Hk Hc1 Hc2 Hc3 Hk1 Hk2 hz1 hz2.
    have Euler := euler_pts Hk Hc1 Hc2 Hc3 Hk1 Hk2 hz1 hz2.
    have hs1 := s_approx Hk Hc1 Hk1 hz1.
    have hs2 := s_approx Hk Hc2 Hk2 hz2.
    move: Euler hs1 hs2 hz3' hz1 hz2.
    set z1 := zk P1; set z2 := zk P2; set z3 := zk (ec_add P1 P2).
    set s1 := sk P1; set s2 := sk P2.
    move=> Euler hs1 hs2 hz3' hz1 hz2.
    have hz3 : vge v k z3.
    { have -> : z3 = (z3 - z1 - z2) + z1 + z2 by ring.
      exact (vge_add Hv (vge_add Hv (vge_le (int_le3 Hk) hz3') hz1) hz2). }
    have Oz1 : Ov z1 := vge_le Hk0 hz1.
    have Oz2 : Ov z2 := vge_le Hk0 hz2.
    have Oz3 : Ov z3 := vge_le Hk0 hz3.
    (* the scale pi = p^k *)
    set n := `|k|%N.
    have Hn : n%:Z = k by rewrite /n gez0_abs.
    set pi := (p%:R : KRF) ^+ n.
    have [Hpi0 Hvpi] := vpow n.
    have hpi : vge v k pi by right; rewrite Hvpi Hn.
    have Opi : Ov pi := vge_le Hk0 hpi.
    set u1 := z1 / pi; set u2 := z2 / pi.
    have Ou1 : Ov u1 by have := vge_div hz1 Hpi0; rewrite Hvpi Hn subrr.
    have Ou2 : Ov u2 by have := vge_div hz2 Hpi0; rewrite Hvpi Hn subrr.
    have Ez1 : z1 = u1 * pi by rewrite /u1 divfK.
    have Ez2 : z2 = u2 * pi by rewrite /u2 divfK.
    (* the formal side *)
    have F0 := log_add_formal KRF_nat_neq0 u1 u2 (SP0 aK K) (S_sq aK K)
                 (tc_le (leqnSn K) (omega_S KRF_nat_neq0 aK K)) (LK_deriv KRF_nat_neq0 aK K) (LK_0 aK K).
    set g := ge aK u1 u2 K (SP aK K) in F0.
    have pQ : pint Ov (Qe aK u1 u2).
    { apply: (pint_add HOv (pint_1 HOv)).
      apply: (pint_mul HOv (pint_mul HOv (pint_C HOv Ov4a) (pint_exp HOv 2 (pint_scl Ou1)))).
      exact: (pint_exp HOv 2 (pint_scl Ou2)). }
    have pI : pint Ov (Ie aK u1 u2 K) := pint_ginv HOv K.+1 pQ.
    have pg : pint Ov g.
    { apply: (pint_mul HOv) pI; apply: (pint_add HOv).
      - exact: (pint_mul HOv (pint_scl Ou1) (pint_comp HOv pint_Sk (pint_scl Ou2))).
      - exact: (pint_mul HOv (pint_scl Ou2) (pint_comp HOv pint_Sk (pint_scl Ou1))). }
    set Dp := (LK aK K \Po g) - ((LK aK K \Po scl u1) + (LK aK K \Po scl u2)).
    have hD : vge v ((K.+1)%:Z * k) Dp.[pi].
    { apply: vge_eval _ (tc_sub0 F0) hpi Hk0.
      apply: (pint_sub HOv (pint_comp HOv pint_Lk pg)).
      exact: (pint_add HOv (pint_comp HOv pint_Lk (pint_scl Ou1)) (pint_comp HOv pint_Lk (pint_scl Ou2))). }
    have Escl : forall (f : {poly KRF}) u, (f \Po scl u).[pi] = f.[u * pi].
    { by move=> f u; rewrite horner_comp /scl hornerCM hornerX. }
    have ED : Dp.[pi] = (LK aK K).[g.[pi]] - ((LK aK K).[z1] + (LK aK K).[z2]).
    { by rewrite /Dp hornerD hornerN hornerD !Escl horner_comp -Ez1 -Ez2. }
    (* the exact side *)
    set t1 := (Sk K).[z1]; set t2 := (Sk K).[z2].
    have Ot1 : Ov t1 := horner_O HOv pint_Sk Oz1.
    have Ot2 : Ov t2 := horner_O HOv pint_Sk Oz2.
    set Ip := (Ie aK u1 u2 K).[pi].
    have Eg : g.[pi] = (z1 * t2 + z2 * t1) * Ip.
    { rewrite /g /ge hornerM /N0 hornerD !hornerM !Escl !hornerC hornerX -Ez1 -Ez2.
      by []. }
    set qq := 1 + 4%:R * aK * z1 ^+ 2 * z2 ^+ 2.
    have EQ : (Qe aK u1 u2).[pi] = qq.
    { by rewrite /Qe /scl horner_Qe -Ez1 -Ez2. }
    have hqq : vge v 1 (4%:R * aK * z1 ^+ 2 * z2 ^+ 2).
    { have h := vge_mul Hv (vge_mulO Ov4a (vge_exp 2 hz1)) (vge_exp 2 hz2).
      apply: vge_le h; move: Hk; clear; move=> H; ilia. }
    have [Hqq0 Hvqq] := one_plus Hv hqq.
    have Heps : vge v ((K.+1)%:Z * k) (Ip * qq - 1).
    { have E : Ip * qq - 1 = (Ie aK u1 u2 K * Qe aK u1 u2 - 1).[pi] by rewrite horner_sub1 hornerM EQ.
      rewrite E; apply: vge_eval _ (tc_sub0 (IQ aK u1 u2 K)) hpi Hk0.
      exact: (pint_sub HOv (pint_mul HOv pI pQ) (pint_1 HOv)). }
    have Ez3 : z3 = (z1 * s2 + z2 * s1) / qq by rewrite -Euler mulfK.
    have E : z3 - g.[pi] = (z1 * (s2 - t2) + z2 * (s1 - t1) - (z1 * t2 + z2 * t1) * (Ip * qq - 1)) / qq.
    { rewrite Ez3 Eg; field. }
    have hzg : vge v ((K.+1)%:Z * k) (z3 - g.[pi]).
    { rewrite E; refine (vge_div_unit Hv _ Hqq0 Hvqq).
      refine (vge_sub Hv (vge_add Hv (vge_mulO Oz1 hs2) (vge_mulO Oz2 hs1)) _).
      refine (vge_mulO _ Heps).
      exact: (sradd HOv (srmul HOv Oz1 Ot2) (srmul HOv Oz2 Ot1)). }
    have [c [Oc Ec]] := lipschitz HOv pint_Lk Oz3 (horner_O HOv pg Opi).
    rewrite /Lk.
    have -> : (LK aK K).[z3] - (LK aK K).[z1] - (LK aK K).[z2]
            = ((LK aK K).[z3] - (LK aK K).[g.[pi]]) + Dp.[pi] by rewrite ED; ring.
    rewrite Ec; exact (vge_add Hv (vge_mulOr hzg Oc) hD).
  Qed.

  (* v(L_K(z)) = v(z) on the kernel *)
  Lemma Lk_val (z : KRF) : (0 < K)%N -> z != 0 -> 1 <= v z ->
    (Lk K).[z] != 0 /\ v ((Lk K).[z]) = v z.
  Proof.
    move=> HK Hz Hvz.
    have Ht : tc 2 (Lk K - 'X) 0.
    { constructor=> -[ | [ | i ] ] Hi //; rewrite coefB coefX coef0 /Lk.
      - by rewrite LK_0 subr0.
      - by rewrite (LK_1 KRF_nat_neq0 aK HK) subrr. }
    have hz : vge v (v z) z by right.
    have H := vge_eval (pint_sub HOv pint_Lk (pint_X HOv)) Ht hz (int_le0 Hvz).
    have E : (Lk K).[z] = z + (Lk K - 'X).[z] by rewrite hornerD hornerN hornerX; ring.
    have Hlt : v z < 2%:Z * v z by move: Hvz; clear; move=> H; ilia.
    rewrite E; exact (vge_strict Hv Hz H Hlt).
  Qed.

  (** Multiples *)
  Section mult.

    Variable Pn : int -> pt rat.
    Hypothesis Pn_on : forall n, onp (Pn n).
    Hypothesis Pn_add : forall n n', Pn (n + n') = ec_add (Pn n) (Pn n').
    Hypothesis Pn_0 : Pn 0 = None.
    Hypothesis Pn_neg : forall n, Pn (- n) = pt_neg (Pn n).

    Local Abbreviation lz P := ((Lk K).[zk P]).

    Lemma lz0 : lz None = 0.
    Proof. by rewrite /= horner_coef0 /Lk LK_0. Qed.

    Lemma ellK_mul_nat (b k : int) : 1 <= k -> kern v (Pn b) -> vge v k (zk (Pn b)) ->
      forall n : nat, vge v ((K.+1)%:Z * k) (lz (Pn (b * n%:Z)) - n%:R * lz (Pn b)).
    Proof.
      move=> Hk Hb hb; elim=> [ | n IH ].
      { rewrite mulr0 Pn_0 lz0 mul0r subr0; exact: vge0. }
      have E : b * (n.+1)%:Z = b * n%:Z + b by rewrite -addn1 PoszD mulrDr mulr1.
      have [H1 [_ H3]] := mul_kern Hv Pn_on Pn_add Pn_0 Hk Hb hb n.
      have Hon3 : onp (ec_add (Pn (b * n%:Z)) (Pn b)) by rewrite -Pn_add; exact: Pn_on.
      have H := ellK_add Hk (Pn_on _) (Pn_on _) Hon3 H1 Hb H3 hb.
      rewrite E Pn_add.
      have -> : lz (ec_add (Pn (b * n%:Z)) (Pn b)) - (n.+1)%:R * lz (Pn b)
              = (lz (ec_add (Pn (b * n%:Z)) (Pn b)) - lz (Pn (b * n%:Z)) - lz (Pn b))
                + (lz (Pn (b * n%:Z)) - n%:R * lz (Pn b)) by rewrite -addn1 natrD; ring.
      exact (vge_add Hv H IH).
    Qed.

    Lemma ec_addN' (P : pt rat) : ec_add P (pt_neg P) = None.
    Proof. case: P => [ [ x y ] | ] //; exact: ec_add_opp erefl (esym (opprK y)). Qed.

    Lemma ellK_neg (j k : int) : 1 <= k -> kern v (Pn j) -> vge v k (zk (Pn j)) ->
      vge v ((K.+1)%:Z * k) (lz (pt_neg (Pn j)) + lz (Pn j)).
    Proof.
      move=> Hk HP hz.
      have Hc := Pn_on j.
      have Hc' : onp (pt_neg (Pn j)) by rewrite -Pn_neg; exact: Pn_on.
      move: HP hz Hc Hc'; set P := Pn j => HP hz Hc Hc'.
      have Hc3 : onp (ec_add P (pt_neg P)) by rewrite ec_addN'.
      have HP' : kern v (pt_neg P) by exact: kern_neg.
      have hz' : vge v k (zk (pt_neg P)) by rewrite zk_neg; exact (vge_opp Hv hz).
      have H := ellK_add Hk Hc Hc' Hc3 HP HP' hz hz'.
      rewrite ec_addN' lz0 in H.
      have -> : lz (pt_neg P) + lz P = - (0 - lz P - lz (pt_neg P)) by ring.
      exact (vge_opp Hv H).
    Qed.

    (* L_K(z(j R)) = j L_K(z(R)) mod p^((K+1)k) *)
    Theorem ellK_mul (b k : int) : 1 <= k -> kern v (Pn b) -> vge v k (zk (Pn b)) ->
      forall j : int, vge v ((K.+1)%:Z * k) (lz (Pn (b * j)) - j%:~R * lz (Pn b)).
    Proof.
      move=> Hk Hb hb [ n | n ]; first exact: ellK_mul_nat.
      have E : b * Negz n = - (b * (n.+1)%:Z) by rewrite NegzE mulrN.
      rewrite E Pn_neg.
      have [H1 [_ H3]] := mul_kern Hv Pn_on Pn_add Pn_0 Hk Hb hb n.+1.
      have HN := ellK_neg Hk H1 H3.
      have HM := ellK_mul_nat Hk Hb hb n.+1.
      have -> : lz (pt_neg (Pn (b * (n.+1)%:Z))) - (Negz n)%:~R * lz (Pn b)
              = (lz (pt_neg (Pn (b * (n.+1)%:Z))) + lz (Pn (b * (n.+1)%:Z)))
                - (lz (Pn (b * (n.+1)%:Z)) - (n.+1)%:R * lz (Pn b)).
      { by rewrite NegzE mulrNz -pmulrn; ring. }
      exact (vge_sub Hv HN HM).
    Qed.

  End mult.

  (** The assembly for a homomorphism Pn with nonzero values at nonzero
      arguments (E2), on the curve E (sg = false) *)

  Lemma v_int (z : int) : v (z%:~R : KRF) = v (`|z|%:R : KRF).
  Proof. by case: z => n //; rewrite NegzE mulrNz (vN Hv) -pmulrn. Qed.

  Lemma Ov_int (z : int) : Ov (z%:~R).
  Proof.
    case: z => n; first exact: (vge_nat Hv n).
    rewrite NegzE mulrNz -pmulrn; exact (vge_opp Hv (vge_nat Hv n.+1)).
  Qed.

  Lemma int_unit (z : int) : z != 0 -> logn p `|z| = 0%N -> (z%:~R : KRF) != 0 /\ v (z%:~R : KRF) = 0.
  Proof.
    move=> Hz Hl; have Hz0 : (0 < `|z|)%N by rewrite absz_gt0.
    split.
    - by apply/eqP => E; move: Hz; rewrite -(intr_eq0 rat) => /eqP; apply; move: E; rewrite qe_intE => -[].
    - rewrite v_int; refine (v_coprime Hv Hz0 _).
      rewrite coprime_sym prime_coprime //; apply/negP => Hd.
      have : (0 < logn p `|z|)%N by rewrite logn_gt0 mem_primes Hp Hz0 Hd.
      by rewrite Hl.
  Qed.

  Lemma qe_of_div (a b : rat) : b != 0 -> (qe_of (a / b) : KRF) = qe_of a / qe_of b.
  Proof.
    move=> Hb; have Hb' : (qe_of b : KRF) != 0 by apply/eqP => -[] /eqP; rewrite (negbTE Hb).
    apply: (mulIf Hb'); rewrite divfK // -[_ * _]/(qe_of (a / b) * qe_of b : qe rat) -qe_of_mul.
    by rewrite divfK.
  Qed.

  Lemma qe_of_int (z : int) : (qe_of (z%:~R : rat) : KRF) = z%:~R.
  Proof. by rewrite /qe_of qe_intE. Qed.

  Lemma int_Kk (K' : nat) (k : int) : 1 <= k -> K'%:Z <= (K'.+1)%:Z * k - k.
  Proof.
    move=> Hk; have -> : (K'.+1)%:Z * k - k = K'%:Z * k by rewrite -addn1 PoszD mulrDl mul1r addrK.
    by apply: ler_peMr.
  Qed.

  Lemma vqr_m_unit (n n' d m m' : int) : n != 0 -> n' != 0 -> d != 0 ->
    n = m * d -> n' = m' * d -> gcdn `|m| `|m'| = 1%N ->
    vqr p n'%:~R <= vqr p n%:~R -> logn p `|m'| = 0%N.
  Proof.
    move=> Hn Hn' Hd En En' Hg Hle.
    have Hm : m != 0 by apply/eqP => E0; move: Hn; rewrite En E0 mul0r eqxx.
    have Hm' : m' != 0 by apply/eqP => E0; move: Hn'; rewrite En' E0 mul0r eqxx.
    move: Hle; rewrite !vqr_int En En' !abszM !lognM ?absz_gt0 // lez_nat leq_add2r => Hle.
    apply/eqP; rewrite -leqn0 leqNgt; apply/negP => H.
    have H' : (0 < logn p `|m|)%N := leq_trans H Hle.
    move: H H'; rewrite !logn_gt0 !mem_primes => /and3P [_ _ D1] /and3P [_ _ D2].
    have : (p %| gcdn `|m| `|m'|)%N by rewrite dvdn_gcd D1 D2.
    by rewrite Hg dvdn1 => /eqP Hp1; move: Hp; rewrite Hp1.
  Qed.

  Section core.

    Variable Pn : int -> pt rat.
    Hypothesis Pn_on : forall n, onp (Pn n).
    Hypothesis Pn_add : forall n n', Pn (n + n') = ec_add (Pn n) (Pn n').
    Hypothesis Pn_0 : Pn 0 = None.
    Hypothesis Pn_neg : forall n, Pn (- n) = pt_neg (Pn n).
    Hypothesis Pn_E2 : forall n, n != 0 -> exists x y, Pn n = Some (x, y) /\ (x : KRF) != 0.
    Hypothesis HK : (1 <= K)%N.

    Local Abbreviation lz P := ((Lk K).[zk P]).

    Definition redv (P : pt rat) : Prop := if P is Some (x, _) then v x < 0 else True.

    Lemma kern_of (n : int) : n != 0 -> redv (Pn n) ->
      exists x y, Pn n = Some (x, y) /\ kern v (Pn n) /\ zk (Pn n) != 0 /\ 1 <= v (zk (Pn n)).
    Proof.
      move=> Hn; have [x [y [E Hx]]] := Pn_E2 Hn; rewrite E /= => Hvx.
      have Hc : on_curve (x, y) by have := Pn_on n; rewrite E.
      have [_ [Hz [_ [H1 _]]]] := kv Hv (on_curveK Hc) Hx Hvx.
      exists x, y; split; first by [].
      split; first by split.
      by split.
    Qed.

    Lemma kern_int (b : int) (k : int) : 1 <= k -> kern v (Pn b) -> vge v k (zk (Pn b)) ->
      forall j : int, kern v (Pn (b * j)) /\ vge v k (zk (Pn (b * j))).
    Proof.
      move=> Hk Hb hb [ j | j ].
      - by have [H1 [_ H3]] := mul_kern Hv Pn_on Pn_add Pn_0 Hk Hb hb j.
      - have E : b * Negz j = - (b * (j.+1)%:Z) by rewrite NegzE mulrN.
        rewrite E Pn_neg zk_neg.
        have [H1 [_ H3]] := mul_kern Hv Pn_on Pn_add Pn_0 Hk Hb hb j.+1.
        split; [ exact: kern_neg | exact (vge_opp Hv H3) ].
    Qed.

    Theorem O_F2_hom (n n' : int) : n' != 0 -> redv (Pn n) -> redv (Pn n') ->
      (n = 0 \/ vqr p n'%:~R <= vqr p n%:~R) ->
      lz (Pn n') != 0 /\
      (let x := lz (Pn n) / lz (Pn n') - qe_of (n%:~R / n'%:~R) in x = 0 \/ K%:Z <= v x).
    Proof.
      move=> Hn' Hr Hr' Hle.
      have [x' [y' [EV [HkV [HzV HvV]]]]] := kern_of Hn' Hr'.
      have [HLV HvLV] := Lk_val HK HzV HvV.
      split; first exact: HLV.
      case: (eqVneq n 0) => [ En | Hn ].
      { left; rewrite En Pn_0 lz0 mul0r /= mul0r subr0; by []. }
      case: Hle => [ En | Hle ]; first by move: Hn; rewrite En eqxx.
      have [x [y [EU [HkU [HzU HvU]]]]] := kern_of Hn Hr.
      (* the base point W = gcd(n, n') P *)
      set d := gcdz n n'.
      have Hd : d != 0 by rewrite /d gcdz_eq0 negb_and Hn.
      have [a [b Eab]] := Bezoutz n n'.
      set k0 := Num.min (v (zk (Pn n))) (v (zk (Pn n'))).
      have Hk0 : 1 <= k0 by rewrite le_min HvU HvV.
      have hU : vge v k0 (zk (Pn n)) by right; rewrite ge_min lexx.
      have hV : vge v k0 (zk (Pn n')) by right; rewrite ge_min lexx orbT.
      have [Ha1 Ha2] := kern_int Hk0 HkU hU a.
      have [Hb1 Hb2] := kern_int Hk0 HkV hV b.
      have EW : Pn d = ec_add (Pn (n * a)) (Pn (n' * b)) by rewrite -Pn_add /d -Eab mulrC (mulrC n').
      have HonW : onp (ec_add (Pn (n * a)) (Pn (n' * b))) by rewrite -EW; exact: Pn_on.
      have [HkW _] := add_kern Hv Hk0 (Pn_on _) (Pn_on _) HonW Ha1 Hb1 Ha2 Hb2.
      rewrite -EW in HkW.
      have [xw [yw [EW' Hxw]]] := Pn_E2 Hd.
      have HrW : redv (Pn d) by move: HkW; rewrite EW' /= => -[].
      have [xw2 [yw2 [_ [_ [HzW HvW]]]]] := kern_of Hd HrW.
      set kW := v (zk (Pn d)) in HvW.
      have hW : vge v kW (zk (Pn d)) by right.
      (* n = m d, n' = m' d *)
      set m := (n %/ d)%Z; set m' := (n' %/ d)%Z.
      have En : n = m * d by rewrite /m divzK // dvdz_gcdl.
      have En' : n' = m' * d by rewrite /m' divzK // dvdz_gcdr.
      have Hm' : m' != 0 by apply/eqP => E0; move: Hn'; rewrite En' E0 mul0r eqxx.
      have Hg : gcdn `|m| `|m'| = 1%N.
      { have E := mulz_gcdl m m' d; rewrite -En -En' -/d in E.
        have Ed : `|d|%:Z = d by [].
        rewrite Ed -[X in _ = X]mul1r in E.
        have E1 := mulIf Hd E.
        by move: E1; rewrite /gcdz => -[]. }
      have Hlm := vqr_m_unit Hn Hn' Hd En En' Hg Hle.
      have [Hm'0 Hvm'] := int_unit Hm' Hlm.
      have FU : Pn n = Pn (d * m) by rewrite {1}En mulrC.
      have FV : Pn n' = Pn (d * m') by rewrite {1}En' mulrC.
      have HmU := ellK_mul Pn_on Pn_add Pn_0 Pn_neg HvW HkW hW m.
      have HmV := ellK_mul Pn_on Pn_add Pn_0 Pn_neg HvW HkW hW m'.
      rewrite -FU in HmU; rewrite -FV in HmV.
      have Hvxw : v xw < 0 by move: HrW; rewrite EW'.
      have [x3 [y3 [_ [_ [_ Hvz]]]]] := kernel_mul Hp Hv Pn_on Pn_add Pn_0 Pn_neg EW' Hxw Hvxw Hm'.
      rewrite -FV vqr_int Hlm addr0 -/kW in Hvz.
      rewrite Hvz in HvLV.
      have Eq : (n%:~R / n'%:~R : rat) = m%:~R / m'%:~R.
      { have Hd' : (d%:~R : rat) != 0 by rewrite intr_eq0.
        have Hm'' : (m'%:~R : rat) != 0 by rewrite intr_eq0.
        rewrite En En' !intrM; field. }
      rewrite Eq qe_of_div ?intr_eq0 // !qe_of_int.
      set LU := lz (Pn n); set LV := lz (Pn n'); set LW := lz (Pn d).
      have E : LU / LV - m%:~R / m'%:~R
             = (m'%:~R * (LU - m%:~R * LW) - m%:~R * (LV - m'%:~R * LW)) / (m'%:~R * LV).
      { field. }
      rewrite E; apply: (@vge_le _ ((K.+1)%:Z * kW - kW)); first exact: int_Kk.
      have Hden : m'%:~R * LV != 0 by rewrite mulf_neq0.
      have Hvden : v (m'%:~R * LV) = kW by rewrite (vM Hv Hm'0 HLV) Hvm' HvLV add0r.
      rewrite -[X in vge _ (_ - X)]Hvden; apply: vge_div Hden.
      exact (vge_sub Hv (vge_mulO (Ov_int m') HmU) (vge_mulO (Ov_int m) HmV)).
    Qed.

  End core.

End kernel_log.

(** * The conjugate curve *)

Lemma qe_conj_exp (x : qe rat) (n : nat) : qe_conj (x ^+ n) = qe_conj x ^+ n.
Proof.
  elim: n => [ | n IH ]; first by rewrite !expr0 qe_conj1.
  by rewrite !exprS qe_conj_mul IH.
Qed.

Lemma qe_conj_sum (I : Type) (r : seq I) (P : pred I) (F : I -> qe rat) :
  qe_conj (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) qe_conj (F i).
Proof. exact: (big_morph _ (@qe_conj_add rat) qe_conj0). Qed.

Lemma zpar_conj (P : pt rat) : zpar true P = qe_conj (zk P).
Proof. by case: P => [ [ x y ] | ]; [ exact: qe_conj_zk | rewrite /= qe_conj0 ]. Qed.

Lemma ellK_conj (K : nat) (P : pt rat) : ellK true K (zpar true P) = qe_conj ((Lk K).[zk P]).
Proof.
  rewrite -[(Lk K).[zk P]]/((Lk K).[(zk P : qe rat) : KRF]) -ellK_horner zpar_conj /ellK qe_conj_sum.
  apply: eq_bigr => t _; rewrite /= !qe_rat_id qe_conj_mul qe_conj_exp; by [].
Qed.

Lemma qe_conj_invq (b : qe rat) : qe_conj (b^-1) = (qe_conj b)^-1.
Proof. exact (qe_conj_inv b). Qed.

Lemma conj_ratio (a b c : qe rat) : qe_conj a / qe_conj b - qe_conj c = qe_conj (a / b - c).
Proof.
  have E1 := qe_conj_add (a / b) (- c); have E2 := qe_conj_opp c.
  have E3 := qe_conj_mul a (b^-1); have E4 := qe_conj_invq b.
  rewrite E1 E2 E3 E4; reflexivity.
Qed.

Lemma qe_conj_of (r : rat) : qe_conj (qe_of r) = qe_of r.
Proof. by rewrite /qe_conj /qe_of /= oppr0. Qed.

Lemma qe_conj_eq0 (x : qe rat) : (qe_conj x == 0) = (x == 0).
Proof.
  apply/eqP/eqP => [ H | -> ]; last exact: qe_conj0.
  by rewrite -[x]qe_conjK H qe_conj0.
Qed.

(** * O_F2 *)

Section group.

  Variable D : FixedData.
  Hypothesis HP0 : on_curve (fd_P0 D).

  Let mulQ_on_h : forall D : FixedData, on_curve (fd_P0 D) -> forall n : int, onp (mulQ D n) :=
    fun D0 H n => @mulQ_on D0 H n.
  Let mulQ_add_h : forall D : FixedData, on_curve (fd_P0 D) ->
      forall n n' : int, mulQ D (n + n') = ec_add (mulQ D n) (mulQ D n') :=
    fun D0 H => @mulQ_add D0 H.

  Theorem O_F2_of_E2 : (0 < fd_m D)%N ->
    (forall n : int, n != 0 ->
       exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y)) ->
    forall (sg : bool) (K p : nat), (1 <= K)%N -> prime p -> p \notin fd_SE D -> (K.+1 < p)%N ->
      forall v, is_place_above v p ->
      forall n n' : int, n' != 0 ->
      red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
      (n = 0 \/ vqr p n'%:~R <= vqr p n%:~R) ->
      ellK sg K (zpar sg (mulP D n')) != 0 /\
      (let x := ellK sg K (zpar sg (mulP D n)) / ellK sg K (zpar sg (mulP D n'))
                - qe_of (n%:~R / n'%:~R) in x = 0 \/ K%:Z <= v x).
  Proof.
    move=> Hm0 HE2 sg K p HK Hp _ HKp v Hv n n' Hn' Hr Hr' Hle.
    have Hm : (fd_m D)%:Z != 0 by rewrite -lt0n.
    have Pn_on := mulPn_on mulQ_on_h HP0 (fd_m D).
    have Pn_add := mulPn_add mulQ_add_h HP0 (fd_m D).
    have Pn_0 := mulPn_0 D (fd_m D).
    have Pn_neg := mulPn_neg D (fd_m D).
    have Pn_E2 : forall j : int, j != 0 ->
        exists x y, mulQ D (j * (fd_m D)%:Z) = Some (x, y) /\ (x : KRF) != 0.
    { move=> j Hj; have [x [y [E [Hx _]]]] := HE2 _ (mulf_neq0 Hj Hm).
      by exists x, y. }
    have Hp2 : (2 < p)%N by apply: leq_ltn_trans HKp; rewrite ltnS.
    have HKp' : (K < p)%N := ltnW HKp.
    case: sg Hr Hr' => Hr Hr'.
    - have Hw := conj_place Hv.
      have [H1 H2] := O_F2_hom Hp Hw Hp2 HKp' Pn_on Pn_add Pn_0 Pn_neg Pn_E2 HK Hn' Hr Hr' Hle.
      rewrite /mulP !ellK_conj; split; first by rewrite qe_conj_eq0.
      rewrite -(qe_conj_of (n%:~R / n'%:~R)).
      rewrite conj_ratio.
      case: H2 => [ H | H ]; [ left; rewrite H; exact: qe_conj0 | right; exact: H ].
    - have [H1 H2] := O_F2_hom Hp Hv Hp2 HKp' Pn_on Pn_add Pn_0 Pn_neg Pn_E2 HK Hn' Hr Hr' Hle.
      rewrite /mulP !zk_zpar !ellK_horner; split; [ exact: H1 | exact: H2 ].
  Qed.

End group.

(** * The explicit data *)

Section explicit_F2.

  Variables (C : i4 -> rat) (S : seq nat) (Hb c : nat) (Kset : seq nat) (Nh Ch : nat).
  Local Abbreviation D := (mkData C S Hb c Kset Nh Ch).

  (* the field O_F2 of OrdHyps for the explicit data *)
  Theorem O_F2_mkData :
    forall (sg : bool) (K p : nat), (1 <= K)%N -> prime p -> p \notin fd_SE D -> (K.+1 < p)%N ->
      forall v, is_place_above v p ->
      forall n n' : int, n' != 0 ->
      red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
      (n = 0 \/ vqr p n'%:~R <= vqr p n%:~R) ->
      ellK sg K (zpar sg (mulP D n')) != 0 /\
      (let x := ellK sg K (zpar sg (mulP D n)) / ellK sg K (zpar sg (mulP D n'))
                - qe_of (n%:~R / n'%:~R) in x = 0 \/ K%:Z <= v x).
  Proof.
    apply: (O_F2_of_E2 (mkData_P0_on_curve C S Hb c Kset Nh Ch) (mkData_wf_m C S Hb c Kset Nh Ch)).
    exact: (E2_mkData (fun D0 H n => @mulQ_on D0 H n) (fun D0 H => @mulQ_add D0 H)
              (ord_place_family (q := 17) isT isT) C S Hb c Kset Nh Ch).
  Qed.

End explicit_F2.
