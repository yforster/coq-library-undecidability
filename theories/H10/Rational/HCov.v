(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2D, task P15: the field HCov of StdHyps (Cor pri:integer-coverage,
   02-reduction.tex) from Lemma pri:pattern (in the form [PatternSpec] of
   PaperInputs.v) and Prop ell:formal (the fields O_F1, O_F2 of OrdHyps,
   taken as hypotheses [O_F1_stmt], [O_F2_stmt]), following the proof of
   Cor pri:integer-tests (06-primes.tex).

   Main results:
   - [rp_add]          the REDUCTION HOMOMORPHISM: for an odd prime r <> 7 and
                       any place v above r with v(sqrt2 - c) >= 1 (c^2 = 2 mod r),
                       reduction [rp] of points of E(F) to y^2 = x^3 + abar x
                       over 'F_r commutes with the chord-tangent laws:
                       rp P Pb -> rp Q Qb -> rp (P + Q) (Pb + Qb);
   - [wmuln_card]      LAGRANGE in the finite group E(F_r) (a [finGroupType]
                       built from GroupLaw.v over 'F_r): #E(F_r) . P = O;
   - [card_countF]     #E(F_r) = [countF r (aEmod r c)] (ExplicitData.v);
   - [kernel_countF]   #E(F_r) | n  ->  n P0 reduces to O at v;
   - [crt_h]           the CRT choice h = 0 (d1), h = 4 (d2 r^K), h <> 0;
   - [integer_tests]   Cor pri:integer-tests at one place (RepConds);
   - [HCov_thm]        the HCov field for [mkData]; [HCov_of_OrdHyps].

   ROUTE for the homomorphism (the most economical one found):
   - the valuation ring and its residue map to 'F_r are RELATIONS: [vge v k x]
     is "v(x) >= k" (v(0) = +oo), [rs x t] says x - n is in the maximal ideal
     for an integer n with t = n mod r. [rs] is functional, total on the
     valuation ring ([rs_ex], via OrdBridges.val_LocZ at i = 0) and a ring
     morphism (sums, products, inverses of units);
   - a point reduces to an affine point if x is integral (then so is y), and
     to O if v(x) < 0 ([rp]);
   - homomorphism, by cases:
     (ii) both points integral ([rp_add_ii]): chord or tangent with a unit
          denominator, or a pole of the slope (reduced sum O); the slope is
          rewritten as (x1^2 + x1 x2 + x2^2 + a)/(y1 + y2) when y1, y2 are
          close to 0 ([chord_alt]), nonsingularity mod r gives the unit
          numerator;
     (ik) integral + kernel point ([rp_add_ik]): with z = x2/y2, m = y2/x2^2
          (both in the maximal ideal) the exact identities [kernel_chord]
          x3 - x1 = m M / U^2, y3 - y1 = - T / U^3 (U = 1 - x1 z m a unit,
          M integral, T in the maximal ideal) give P + Q = P mod v;
     (kk) two kernel points: if the sum were integral, P = (P + Q) - Q would
          be integral by (ik) and the cancellation law of GroupLaw.v;
     (ki) by commutativity.
   - the reduced curve is nonsingular since r <> 2, 7 ([abar_neq0]:
     N(aE) = 49).

   PITFALL (performance): the constant aE contains unary numerals (11243);
   any unification that compares aE with another term (e.g. [apply/] with
   GroupLaw.on_curve_w, rewriting a pattern [v (_)] in a goal containing
   [v aE], or [//] with a hypothesis mentioning aE) can unfold it and hang.
   Hence the explicit proof terms and the generalization of aE in places.

   Assumptions: none (Print Assumptions HCov_thm: closed under the global
   context). *)

From Stdlib Require Import ZArith Lia List.

From HB Require Import structures.
From mathcomp Require Import boot order algebra fingroup cyclic.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData ExplicitData PaperInputs
                 RatVal OrdinaryFacts OrdPlaces OrdBridges GroupLaw.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

(** * 1. Generic identities of the chord-tangent law (any field) *)

Section identities.

  Variable K : fieldType.
  Variable a : K.

  (* the chord slope through two points with y1 + y2 <> 0 *)
  Lemma chord_alt (x1 y1 x2 y2 : K) :
    y1 ^+ 2 = x1 ^+ 3 + a * x1 -> y2 ^+ 2 = x2 ^+ 3 + a * x2 ->
    x1 != x2 -> y1 + y2 != 0 ->
    (y2 - y1) / (x2 - x1) = (x1 ^+ 2 + x1 * x2 + x2 ^+ 2 + a) / (y1 + y2).
  Proof.
    move=> h1 h2 nx ny.
    have d : x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
    apply/eqP; rewrite eqr_div //; apply/eqP.
    have -> : (y2 - y1) * (y1 + y2) = y2 ^+ 2 - y1 ^+ 2 by ring.
    rewrite h1 h2; ring.
  Qed.

  (* two points with x1 <> x2 and y1 = - y2 *)
  Lemma opp_y_sum (x1 y1 x2 y2 : K) :
    y1 ^+ 2 = x1 ^+ 3 + a * x1 -> y2 ^+ 2 = x2 ^+ 3 + a * x2 ->
    x1 != x2 -> y1 = - y2 -> x1 ^+ 2 + x1 * x2 + x2 ^+ 2 + a = 0.
  Proof.
    move=> h1 h2 nx ey.
    have d : x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
    apply: (mulfI d); rewrite mulr0.
    have -> : (x2 - x1) * (x1 ^+ 2 + x1 * x2 + x2 ^+ 2 + a) =
              (x2 ^+ 3 + a * x2) - (x1 ^+ 3 + a * x1) by ring.
    by rewrite -h1 -h2 ey sqrrN subrr.
  Qed.

  (* the chord through (x1, y1) and a point (x2, y2) written in the
     formal coordinates z = x2/y2, m = y2/x2^2 (so x2 = 1/(z m)) *)
  Definition kM (x1 y1 z m : K) : K :=
    (a + 3%:R * x1 ^+ 2) * z - 2%:R * y1 + (y1 ^+ 2 - 2%:R * x1 ^+ 3) * z ^+ 2 * m.

  Definition kT (x1 y1 z m : K) : K :=
    m * (a + 3%:R * x1 ^+ 2) - 2%:R * y1 * a * z ^+ 2 * m ^+ 2
    + (y1 ^+ 2 - 2%:R * x1 ^+ 3) * z * m ^+ 2 - y1 * z * m ^+ 2 * kM x1 y1 z m
    + 2%:R * y1 * ((1 - x1 * z * m) ^+ 3 - 1).

  Lemma kernel_chord (x1 y1 x2 y2 : K) :
    y2 ^+ 2 = x2 ^+ 3 + a * x2 -> x2 != 0 -> y2 != 0 -> x1 != x2 ->
    let z := x2 / y2 in let m := y2 / x2 ^+ 2 in
    let U := 1 - x1 * z * m in
    let l := (y2 - y1) / (x2 - x1) in
    let x3 := l ^+ 2 - 0 - x1 - x2 in
    let y3 := l * (x1 - x3) - y1 in
    U != 0 /\ x3 - x1 = m * kM x1 y1 z m / U ^+ 2 /\ y3 - y1 = - kT x1 y1 z m / U ^+ 3.
  Proof.
    move=> h2 nx2 ny2 nx; cbv zeta.
    have d : x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
    have EU : 1 - x1 * (x2 / y2) * (y2 / x2 ^+ 2) = (x2 - x1) / x2 by field.
    have nU : (x2 - x1) / x2 != 0 by rewrite mulf_neq0 ?invr_eq0.
    have Ea : a = (y2 ^+ 2 - x2 ^+ 3) / x2 by rewrite h2; field.
    rewrite EU /kT /kM !EU; split => //.
    rewrite Ea; split; field; by rewrite nx2 ny2 d.
  Qed.

End identities.

(** * 2. The valuation ring at a split place and its residue map to F_r

    [v] is any place above the odd prime r ([is_place_above]) with
    v(sqrt2 - c) >= 1, where c^2 = 2 mod r (the hypotheses of
    OrdBridges.split_bridge). [vge k x] is "v(x) >= k" with v(0) = +oo.
    The residue map is a RELATION [rs x t] (t in 'F_r): x - n is in the
    maximal ideal for an integer n with t = n mod r. It is functional,
    total on the valuation ring and a ring morphism. *)

Definition vge (v : qe rat -> int) (k : int) (x : qe rat) : Prop := x = 0 \/ k <= v x.

Lemma qe_unit_neq0 (x : qe rat) : x != 0 -> x \is a GRing.unit.
Proof. exact: (qe_neq0_unit rat_sq2). Qed.

Lemma Fr_nat0 (r : nat) (k : nat) : prime r -> ((k%:R : 'F_r) == 0) = (r %| k)%N.
Proof. by move=> Hr; rewrite -val_eqE /= val_Fp_nat. Qed.

Lemma Fr_int0 (r : nat) (n : int) : prime r ->
  ((n%:~R : 'F_r) == 0) = (r%:Z %| n)%Z.
Proof.
  move=> Hr; case: n => k.
  - by rewrite /= -pmulrn dvdzE /= Fr_nat0.
  - by rewrite NegzE mulrNz oppr_eq0 dvdzE abszN /= -pmulrn Fr_nat0.
Qed.

(* divisibility in int and in Z *)
Lemma dvdz_Z (r : nat) (m : int) : (r%:Z %| m)%Z -> Z.divide (Z.of_nat r) (int_to_Z m).
Proof. move=> /dvdz_ex [ t -> ]; exists (int_to_Z t); rewrite iz_mul iz_nat; lia. Qed.

Lemma Z_dvdz (r : nat) (m : int) : Z.divide (Z.of_nat r) (int_to_Z m) -> (r%:Z %| m)%Z.
Proof.
  move=> [ k Hk ]; apply: (@ex_dvdz _ _ (Z_to_int k)); apply: iz_inj.
  rewrite iz_mul iz_nat iz_Z_to_int Hk; lia.
Qed.

Lemma Fr_two0 (r : nat) : prime r -> r != 2%N -> (2%:R : 'F_r) != 0.
Proof.
  move=> Hr H2; rewrite Fr_nat0 //; apply/negP => H.
  by move: H; rewrite (dvdn_prime2 Hr (isT : prime 2)) (negbTE H2).
Qed.

Lemma Fr_int (r : nat) (t : 'F_r) : exists n : int, t = n%:~R.
Proof. by exists (val t)%:Z; rewrite -pmulrn natr_Zp. Qed.

Section residue.

  Variable r : nat.
  Hypothesis r_prime : prime r.
  Hypothesis r_odd : r != 2%N.
  Variable v : qe rat -> int.
  Hypothesis Hv : is_place_above v r.
  Variable c : int.
  Hypothesis c_root : (r%:Z %| c ^+ 2 - 2)%Z.
  Hypothesis c_place : 1 <= v (tcq c).

  Let vM : forall x y, x != 0 -> y != 0 -> v (x * y) = v x + v y.
  Proof. by case: Hv. Qed.
  Let vU : forall x y, x != 0 -> y != 0 -> x + y != 0 -> Num.min (v x) (v y) <= v (x + y).
  Proof. by case: Hv => _ []. Qed.

  Local Abbreviation vg := (vge v).

  Lemma vge0 k : vg k 0. Proof. by left. Qed.

  Lemma vge_add k x y : vg k x -> vg k y -> vg k (x + y).
  Proof using Hv.
    move=> [ -> | Hx ]; first by rewrite add0r.
    move=> [ -> | Hy ]; first by rewrite addr0; right.
    case: (eqVneq x 0) => [ -> | nx ]; first by rewrite add0r; right.
    case: (eqVneq y 0) => [ -> | ny ]; first by rewrite addr0; right.
    case: (eqVneq (x + y) 0) => [ -> | nxy ]; first by left.
    right; apply: le_trans (vU nx ny nxy); by rewrite le_min Hx Hy.
  Qed.

  Lemma vge_opp k x : vg k x -> vg k (- x).
  Proof using Hv.
    move=> [ -> | Hx ]; first by rewrite oppr0; left.
    case: (eqVneq x 0) => [ -> | nx ]; first by rewrite oppr0; left.
    by right; rewrite (vbN Hv).
  Qed.

  Lemma vge_sub k x y : vg k x -> vg k y -> vg k (x - y).
  Proof using Hv. by move=> Hx Hy; apply: vge_add => //; apply: vge_opp. Qed.

  Lemma vge_mul k l x y : vg k x -> vg l y -> vg (k + l) (x * y).
  Proof using Hv.
    move=> [ -> | Hx ]; first by rewrite mul0r; left.
    move=> [ -> | Hy ]; first by rewrite mulr0; left.
    case: (eqVneq x 0) => [ -> | nx ]; first by rewrite mul0r; left.
    case: (eqVneq y 0) => [ -> | ny ]; first by rewrite mulr0; left.
    by right; rewrite vM // lerD.
  Qed.

  Lemma vge_le k l x : k <= l -> vg l x -> vg k x.
  Proof. by move=> Hkl [ -> | H ]; [ left | right; exact: le_trans H ]. Qed.

  Lemma vge_mul0 k x y : vg 0 x -> vg k y -> vg k (x * y).
  Proof using Hv. by move=> Hx Hy; rewrite -[k]add0r; apply: vge_mul. Qed.

  Lemma vge_mul0r k x y : vg k x -> vg 0 y -> vg k (x * y).
  Proof using Hv. by move=> Hx Hy; rewrite -[k]addr0; apply: vge_mul. Qed.

  Lemma vge_exp x n : vg 0 x -> vg 0 (x ^+ n).
  Proof using Hv.
    move=> Hx; elim: n => [ | n IH ]; last by rewrite exprS; apply: vge_mul0.
    by rewrite expr0; right; rewrite (vb1 Hv).
  Qed.

  Lemma vge_int (n : int) : vg 0 (n%:~R).
  Proof using Hv r_prime.
    case: (eqVneq n 0) => [ -> | nn ]; first by left.
    by right; rewrite qe_intE -/(qe_of _) (vb_int r_prime Hv nn).
  Qed.

  Lemma vge_nat (n : nat) : vg 0 (n%:R).
  Proof using Hv r_prime. by rewrite pmulrn; apply: vge_int. Qed.

  Lemma vge_QE (a b : int) : vg 0 (QE a%:~R b%:~R).
  Proof using Hv r_prime r_odd.
    case: (eqVneq (QE (a%:~R : rat) b%:~R) 0) => [ -> | nz ]; first by left.
    by right; apply: (v_Zsqrt2_ge0 r_prime r_odd Hv).
  Qed.

  Lemma vge_int_dvd (n : int) : (r%:Z %| n)%Z -> vg 1 (n%:~R).
  Proof using Hv r_prime.
    move=> /dvdz_ex [ t -> ].
    case: (eqVneq t 0) => [ -> | nt ]; first by rewrite mulr0; left.
    have nr : r%:Z != 0 by rewrite eqz_nat -lt0n prime_gt0.
    right; rewrite qe_intE -/(qe_of _) (vb_int r_prime Hv) ?mulf_neq0 //.
    rewrite abszM lognM ?absz_gt0 //= logn_prime // eqxx.
    by rewrite PoszD lerDl.
  Qed.

  Lemma vge_int_ndvd (n : int) : vg 1 (n%:~R) -> (r%:Z %| n)%Z.
  Proof using Hv r_prime.
    case: (eqVneq n 0) => [ -> _ | nn ]; first exact: dvdz0.
    move=> [ E | H ]; first by move: E; rewrite qe_intE => -[] /eqP; rewrite intr_eq0 (negbTE nn).
    apply/negPn/negP => Hn.
    move: H; rewrite qe_intE -/(qe_of _) (vb_int r_prime Hv nn) logn_ndvd //.
  Qed.

  Lemma vge_tcq : vg 1 (tcq c).
  Proof using c_place. by right. Qed.

  Lemma vge_unit x : vg 0 x -> ~ vg 1 x -> x != 0 /\ v x = 0.
  Proof.
    move=> [ -> | H0 ] H1; first by case: H1; left.
    have nx : x != 0 by apply/eqP => E; apply: H1; left.
    split => //; apply/eqP; rewrite eq_le H0 andbT.
    case: (lerP (v x) 0) => // H; exfalso; apply: H1; right; by [].
  Qed.

  Lemma vge_div k x y : y != 0 -> vg k x -> vg (k - v y) (x / y).
  Proof using Hv.
    move=> ny Hx; have [ ny' Ey ] := vb_inv Hv ny.
    apply: vge_mul => //; right; by rewrite Ey.
  Qed.

  (** ** Residues *)

  Definition rs (x : qe rat) (t : 'F_r) : Prop :=
    exists n : int, t = n%:~R /\ vg 1 (x - n%:~R).

  Lemma rs_int (n : int) : rs n%:~R n%:~R.
  Proof. by exists n; rewrite subrr; split => //; left. Qed.

  Lemma rs_nat (n : nat) : rs n%:R n%:R.
  Proof. by rewrite !pmulrn; apply: rs_int. Qed.

  Lemma rs_0 : rs 0 0. Proof. exact: (rs_int 0). Qed.
  Lemma rs_1 : rs 1 1. Proof. exact: (rs_int 1). Qed.

  Lemma rs_congr x y t : rs x t -> vg 1 (y - x) -> rs y t.
  Proof using Hv.
    move=> [ n [ -> H ] ] Hyx; exists n; split => //.
    have -> : y - n%:~R = (y - x) + (x - n%:~R) by rewrite addrA subrK.
    exact: vge_add.
  Qed.

  Lemma rs_O x t : rs x t -> vg 0 x.
  Proof using Hv r_prime.
    move=> [ n [ _ H ] ]; rewrite -(subrK n%:~R x); apply: vge_add; last exact: vge_int.
    exact: vge_le H.
  Qed.

  Lemma rs_fun x t t' : rs x t -> rs x t' -> t = t'.
  Proof using Hv r_prime.
    move=> [ n [ -> H ] ] [ n' [ -> H' ] ].
    have : vg 1 ((n' - n)%:~R).
    { rewrite intrB; have -> : (n'%:~R - n%:~R : qe rat) = (x - n%:~R) - (x - n'%:~R) by ring.
      exact: vge_sub. }
    move=> /vge_int_ndvd; rewrite -(Fr_int0 _ r_prime) intrB subr_eq0 => /eqP ->. by [].
  Qed.

  Lemma rs_add x y t u : rs x t -> rs y u -> rs (x + y) (t + u).
  Proof using Hv.
    move=> [ n [ -> H ] ] [ m [ -> H' ] ]; exists (n + m); rewrite !intrD; split => //.
    have -> : x + y - (n%:~R + m%:~R) = (x - n%:~R) + (y - m%:~R) by ring.
    exact: vge_add.
  Qed.

  Lemma rs_opp x t : rs x t -> rs (- x) (- t).
  Proof using Hv.
    move=> [ n [ -> H ] ]; exists (- n); rewrite !intrN; split => //.
    have -> : - x - - n%:~R = - (x - n%:~R) by ring.
    exact: vge_opp.
  Qed.

  Lemma rs_sub x y t u : rs x t -> rs y u -> rs (x - y) (t - u).
  Proof using Hv. by move=> Hx Hy; apply: rs_add => //; apply: rs_opp. Qed.

  Lemma rs_mul x y t u : rs x t -> rs y u -> rs (x * y) (t * u).
  Proof using Hv r_prime.
    move=> Hx Hy; have Oy := rs_O Hy.
    move: Hx Hy => [ n [ -> H ] ] [ m [ -> H' ] ]; exists (n * m); rewrite !intrM; split => //.
    have -> : x * y - n%:~R * m%:~R = (x - n%:~R) * y + n%:~R * (y - m%:~R) by ring.
    by apply: vge_add; [ apply: vge_mul0r | apply: vge_mul0 => //; apply: vge_int ].
  Qed.

  Lemma rs_exp x t n : rs x t -> rs (x ^+ n) (t ^+ n).
  Proof using Hv r_prime.
    move=> H; elim: n => [ | n IH ]; first by rewrite !expr0; exact: rs_1.
    by rewrite !exprS; apply: rs_mul.
  Qed.

  Lemma rs0 x : rs x 0 <-> vg 1 x.
  Proof using Hv r_prime.
    split.
    - move=> [ n [ E H ] ]; have Hn : vg 1 n%:~R.
      { apply: vge_int_dvd; rewrite -(Fr_int0 _ r_prime); by rewrite -E. }
      by rewrite -(subrK n%:~R x); apply: vge_add.
    - by move=> H; exists 0; rewrite subr0.
  Qed.

  Lemma rs_unit x t : rs x t -> t != 0 -> x != 0 /\ v x = 0.
  Proof using Hv r_prime.
    move=> H nt; apply: vge_unit; first exact: rs_O H.
    by move=> /rs0 H0; move: nt; rewrite (rs_fun H H0) eqxx.
  Qed.

  Lemma rs_inv x t : rs x t -> t != 0 -> rs x^-1 t^-1.
  Proof using Hv r_prime.
    move=> H nt; have [ nx vx ] := rs_unit H nt.
    have [ m Em ] := Fr_int t^-1.
    have Hu := qe_unit_neq0 nx.
    exists m; split => //.
    have -> : x^-1 - m%:~R = x^-1 * (1 - x * m%:~R).
    { by rewrite mulrBr mulr1 mulrA mulVr // mul1r. }
    apply: vge_mul0.
    - right; have [ _ -> ] := vb_inv Hv nx; by rewrite vx oppr0.
    - apply/rs0; have := rs_sub rs_1 (rs_mul H (rs_int m)).
      by rewrite -Em mulfV // subrr.
  Qed.

  Lemma rs_div x y t u : rs x t -> rs y u -> u != 0 -> rs (x / y) (t / u).
  Proof using Hv r_prime. by move=> Hx Hy nu; apply: rs_mul => //; apply: rs_inv. Qed.

  Lemma rs_QE (a b : int) : rs (QE a%:~R b%:~R) (a + c * b)%:~R.
  Proof using Hv r_prime c_place.
    exists (a + c * b); split => //.
    rewrite (decomp_tc c a b) /qe_of -!qe_intE addrAC subrr add0r.
    apply: vge_mul0; [ exact: vge_int | exact: vge_tcq ].
  Qed.

  Lemma rs_ex x : vg 0 x -> exists t, rs x t.
  Proof using Hv r_prime r_odd c_root c_place.
    move=> Hx; case: (eqVneq x 0) => [ -> | nx ]; first by exists 0; exact: rs_0.
    have Hx' : (0 : nat)%:Z <= v x by case: Hx => // /eqP; rewrite (negbTE nx).
    have [ X0 [ X1 [ Y0 [ Y1 [ io [ ka [ E Hu ] ] ] ] ] ] ] :=
      val_LocZ r_prime r_odd Hv c_root c_place (B := c) (s := sg_p) (esym (mul1r c)) nx Hx'.
    rewrite expr0 mul1r in E; rewrite /sgnz mul1r in Hu.
    have nd : ((Y0 + c * Y1)%:~R : 'F_r) != 0.
    { rewrite (Fr_int0 _ r_prime); apply: (not_dvd_unit r_prime Hu). }
    have HY := rs_QE Y0 Y1.
    have [ nY _ ] := rs_unit HY nd.
    exists ((X0 + c * X1)%:~R / (Y0 + c * Y1)%:~R).
    have -> : x = QE X0%:~R X1%:~R / QE Y0%:~R Y1%:~R.
    { by rewrite -E mulrK // qe_unit_neq0. }
    by apply: rs_div => //; apply: rs_QE.
  Qed.


  Hypothesis r_7 : r != 7%N.

  Local Abbreviation KQ := (@QF rat rat_sq2).

  (** ** The reduced curve  y^2 = x^3 + abar x  at the place *)

  Definition aEint : int := - 11243%:Z + c * 7950%:Z.
  Definition abar : 'F_r := aEint%:~R.

  Lemma aE_QE : (aE : qe rat) = QE (- 11243%:Z)%:~R (7950%:Z)%:~R.
  Proof. by rewrite /aE intrN -!pmulrn. Qed.

  Local Opaque aE.

  Lemma rs_aE : rs aE abar.
  Proof using Hv r_prime c_place. rewrite aE_QE; exact: rs_QE. Qed.

  Lemma abar_neq0 : abar != 0.
  Proof using r_prime r_7 c_root.
    rewrite /abar (Fr_int0 _ r_prime); apply/negP => H.
    have HZ := dvdz_Z H; have HZc := dvdz_Z c_root.
    have Ea : int_to_Z aEint = (-11243 + int_to_Z c * 7950)%ZZ.
    { by rewrite /aEint iz_add iz_opp iz_mul !iz_nat. }
    have Ec : int_to_Z (c ^+ 2 - 2) = (int_to_Z c * int_to_Z c - 2)%ZZ.
    { by rewrite iz_add iz_opp expr2 iz_mul. }
    rewrite Ea in HZ; rewrite Ec in HZc.
    have H49 : Z.divide (Z.of_nat r) (Z.of_nat 49).
    { have -> : Z.of_nat 49 = ((-11243 + int_to_Z c * 7950) * (-11243 - int_to_Z c * 7950)
                              + 63202500 * (int_to_Z c * int_to_Z c - 2))%ZZ by change (Z.of_nat 49) with 49%ZZ; lia.
      apply: Z.divide_add_r; [ exact: Z.divide_mul_l | exact: Z.divide_mul_r ]. }
    have := Z_dvdz (m := 49%:Z) H49; rewrite dvdzE /= => H49'.
    have : (r %| 7 * 7)%N by [].
    rewrite Euclid_dvdM // orbb (dvdn_prime2 r_prime (isT : prime 7)) => /eqP E.
    by move: r_7; rewrite E.
  Qed.

  Lemma abar_aEmod : abar = (Z_to_int (aEmod (Z.of_nat r) (int_to_Z c)))%:~R.
  Proof using r_prime.
    apply/eqP; rewrite -subr_eq0 -intrB (Fr_int0 _ r_prime); apply: Z_dvdz.
    rewrite /aEmod iz_add iz_opp iz_Z_to_int /aEint iz_add iz_opp iz_mul !iz_nat.
    have Hr : Z.of_nat r <> 0%ZZ by move: (prime_gt0 r_prime) => /ssrnat.ltP; lia.
    have := Z.div_mod (-11243 + 7950 * int_to_Z c)%ZZ (Z.of_nat r) Hr.
    move: (Z.modulo _ _) (Z.div _ _) => m q E.
    exists q; change (Z.of_nat 11243) with 11243%ZZ; change (Z.of_nat 7950) with 7950%ZZ; lia.
  Qed.

  Local Opaque abar.

  Lemma two0F : (2%:R : 'F_r) != 0.
  Proof using r_prime r_odd. exact: Fr_two0. Qed.

  Lemma nonsingF (t : 'F_r) : fc 0 abar 0 t = 0 -> fd 0 abar t != 0.
  Proof using r_prime r_odd r_7 c_root. exact: (nonsing0 two0F abar_neq0). Qed.

  (** ** Reduction of points *)

  Definition rp (P : pt rat) (Pb : option ('F_r * 'F_r)) : Prop :=
    match P, Pb with
    | None, None => True
    | None, Some _ => False
    | Some (x, _), None => x != 0 /\ v x < 0
    | Some (x, y), Some (t, u) => rs x t /\ rs y u
    end.

  Lemma vge_aE : vg 0 (aE : qe rat).
  Proof using Hv r_prime c_place. exact: rs_O rs_aE. Qed.

  Lemma aE_unit : (aE : qe rat) != 0 /\ v aE = 0.
  Proof using Hv r_prime r_7 c_root c_place. exact: rs_unit rs_aE abar_neq0. Qed.

  (* integral x gives integral y *)
  Lemma curve_y_O (x y : qe rat) : on_curve (x, y) -> vg 0 x -> vg 0 y.
  Proof using Hv r_prime c_place.
    rewrite /on_curve /= => E Hx.
    have Hyy : vg 0 (y * y).
    { rewrite E; apply: vge_add; [ exact: vge_exp | exact: vge_mul0 vge_aE Hx ]. }
    case: (eqVneq y 0) => [ -> | ny ]; first by left.
    right; case: Hyy => [ /eqP | H ]; first by rewrite (negbTE (qe_mul_neq0 ny ny)).
    move: H; rewrite vM //; move: (v y) => k Hk; ilia.
  Qed.

  (* a pole of x: y is a pole too, with 2 v(y) = 3 v(x) *)
  Lemma curve_pole (x y : qe rat) : on_curve (x, y) -> x != 0 -> v x < 0 ->
    y != 0 /\ v y + v y = v x + v x + v x.
  Proof using Hv r_prime r_7 c_root c_place.
    rewrite /on_curve /= => E nx vx.
    have [ na va ] := aE_unit.
    move: (aE : qe rat) na va E => A na va E.
    have nx2 : x ^+ 2 != 0 by rewrite expr2; apply: qe_mul_neq0.
    have vx2 : v (x ^+ 2) = v x + v x by rewrite expr2 (vM nx nx).
    have hlt : v (x ^+ 2) < v A.
    { rewrite vx2 va; move: (v x) vx => k Hk; ilia. }
    have [ ns vs ] := vb_strict Hv nx2 na hlt.
    have Eyy : y * y = x * (x ^+ 2 + A) by rewrite E; ring.
    have nyy : y * y != 0 by rewrite Eyy; apply: qe_mul_neq0.
    have ny : y != 0 by apply: contraNneq nyy => ->; rewrite mulr0.
    split => //; have := congr1 v Eyy; rewrite vM // vM // vs vx2 => ->.
    by rewrite addrA.
  Qed.

  Lemma rp_ex (P : pt rat) : on_curve_pt P -> exists Pb, rp P Pb.
  Proof using Hv r_prime r_odd c_root c_place.
    case: P => [ [ x y ] | ] /= ; last by exists None.
    move=> h; case: (eqVneq x 0) => [ Ex | nx ].
    - have Hx : vg 0 x by left.
      have [ t Ht ] := rs_ex Hx; have [ u Hu ] := rs_ex (curve_y_O h Hx).
      by exists (Some (t, u)).
    - case: (ltrP (v x) 0) => vx; first by exists None.
      have Hx : vg 0 x by right.
      have [ t Ht ] := rs_ex Hx; have [ u Hu ] := rs_ex (curve_y_O h Hx).
      by exists (Some (t, u)).
  Qed.

  Lemma rp_fun (P : pt rat) Pb Pb' : rp P Pb -> rp P Pb' -> Pb = Pb'.
  Proof using Hv r_prime.
    case: P => [ [ x y ] | ]; case: Pb => [ [ t u ] | ]; case: Pb' => [ [ t' u' ] | ] //=.
    - by move=> [ H1 H2 ] [ H1' H2' ]; rewrite (rs_fun H1 H1') (rs_fun H2 H2').
    - move=> [ H1 _ ] [ nx vx ]; exfalso; case: (rs_O H1) => [ /eqP | H ].
      + by rewrite (negbTE nx).
      + by move: H; rewrite leNgt vx.
    - move=> [ nx vx ] [ H1 _ ]; exfalso; case: (rs_O H1) => [ /eqP | H ].
      + by rewrite (negbTE nx).
      + by move: H; rewrite leNgt vx.
  Qed.

  Lemma rp_on (P : pt rat) Pb : on_curve_pt P -> rp P Pb -> won_pt 0 abar 0 Pb.
  Proof using Hv r_prime c_place.
    case: P => [ [ x y ] | ]; case: Pb => [ [ t u ] | ] //= h [ Hx Hy ].
    rewrite /won /fc /=.
    have E1 := rs_mul Hy Hy; rewrite h in E1.
    have E2 : rs (x ^+ 3 + aE * x) (t ^+ 3 + abar * t).
    { apply: rs_add; [ exact: rs_exp | exact: rs_mul rs_aE Hx ]. }
    rewrite expr2 (rs_fun E1 E2); ring.
  Qed.

  Lemma rp_neg (P : pt rat) Pb : rp P Pb -> rp (pt_neg P) (wneg Pb).
  Proof using Hv.
    case: P => [ [ x y ] | ]; case: Pb => [ [ t u ] | ] //= [ Hx Hy ]; split => //.
    exact: rs_opp.
  Qed.

  Lemma vge1 : vg 0 1.
  Proof. by right; rewrite (vb1 Hv). Qed.

  Ltac vg0 := repeat match goal with
    | |- vge _ _ (_ + _) => apply: vge_add
    | |- vge _ _ (- _) => apply: vge_opp
    | |- vge _ _ (_ * _) => apply: vge_mul0
    | |- vge _ _ (_ ^+ _) => apply: vge_exp
    | |- vge _ _ (_%:R) => apply: vge_nat
    | |- vge _ _ (_%:~R) => apply: vge_int
    | |- vge _ _ 0 => apply: vge0
    | |- vge _ _ 1 => apply: vge1
    | _ => assumption
    end.

  Lemma vge_kM A x1 y1 z m : vg 0 A -> vg 0 x1 -> vg 0 y1 -> vg 0 z -> vg 0 m ->
    vg 0 (kM (K := KQ) A x1 y1 z m).
  Proof. move=> *; rewrite /kM; vg0. Qed.

  Lemma vge_sq1 x : vg 1 x -> vg 1 (x ^+ 2).
  Proof. by move=> H; rewrite expr2; apply: vge_mul0r => //; apply: vge_le H. Qed.

  Lemma vge_kT A x1 y1 z m : vg 0 A -> vg 0 x1 -> vg 0 y1 -> vg 1 z -> vg 1 m ->
    vg 1 (kT (K := KQ) A x1 y1 z m).
  Proof.
    move=> HA H1 H2 Pz Pm.
    have Oz : vg 0 z by apply: vge_le Pz. have Om : vg 0 m by apply: vge_le Pm.
    have Pm2 := vge_sq1 Pm.
    have Pw : vg 1 (x1 * z * m) by apply: vge_mul0 => //; vg0.
    have Ec : (1 - x1 * z * m) ^+ 3 - 1
              = (x1 * z * m) * (- 3%:R + 3%:R * (x1 * z * m) - (x1 * z * m) ^+ 2) by ring.
    rewrite /kT Ec.
    apply: vge_add; [ apply: vge_add; [ apply: vge_add; [ apply: vge_add | ] | ] | ].
    - apply: vge_mul0r => //; vg0.
    - apply: vge_opp; apply: vge_mul0 => //; vg0.
    - apply: vge_mul0 => //; vg0.
    - apply: vge_opp; apply: vge_mul0r; last by apply: vge_kM.
      apply: vge_mul0 => //; vg0.
    - apply: vge_mul0; first by vg0.
      apply: vge_mul0r => //; vg0.
  Qed.

  (** ** The homomorphism property of the reduction *)

  Local Abbreviation wF := (wadd (K := 'F_r) 0 abar).
  Local Abbreviation wQ := (wadd (K := KQ) 0 aE).

  Lemma rs_wsum (l x1 y1 x2 : qe rat) lb t1 u1 t2 :
    rs l lb -> rs x1 t1 -> rs y1 u1 -> rs x2 t2 ->
    rp (Some (wsum (K := KQ) 0 l x1 y1 x2)) (Some (wsum (K := 'F_r) 0 lb t1 u1 t2)).
  Proof.
    move=> Hl H1 H1' H2; rewrite /wsum /=.
    have Hx3 : rs (l ^+ 2 - 0 - x1 - x2) (lb ^+ 2 - 0 - t1 - t2).
    { by apply: rs_sub => //; apply: rs_sub => //; apply: rs_sub; [ exact: rs_exp | exact: rs_0 ]. }
    split => //; apply: rs_sub => //; apply: rs_mul => //; exact: rs_sub.
  Qed.

  Lemma pole_wsum (N Dn x1 y1 x2 : qe rat) nb :
    vg 0 x1 -> vg 0 x2 -> rs N nb -> nb != 0 -> Dn != 0 -> vg 1 Dn ->
    rp (Some (wsum (K := KQ) 0 (N / Dn) x1 y1 x2)) None.
  Proof.
    move=> H1 H2 HN nb0 nD HD; rewrite /wsum /=.
    have [ nN vN ] := rs_unit HN nb0.
    have [ nD' vD' ] := vb_inv Hv nD.
    have nl : N / Dn != 0 by apply: qe_mul_neq0.
    have vl : v (N / Dn) <= -1.
    { rewrite vM // vN vD' add0r; case: HD => [ E | ]; first by move: nD; rewrite E eqxx.
      move: (v Dn) => k Hk; ilia. }
    have nl2 : (N / Dn) ^+ 2 != 0 by rewrite expr2; apply: qe_mul_neq0.
    have vl2 : v ((N / Dn) ^+ 2) = v (N / Dn) + v (N / Dn) by rewrite expr2 vM.
    have -> : (N / Dn) ^+ 2 - 0 - x1 - x2 = (N / Dn) ^+ 2 + - (x1 + x2) by ring.
    case: (eqVneq (x1 + x2) 0) => [ -> | ns ].
    - rewrite oppr0 addr0; split => //; rewrite vl2; move: (v (N / Dn)) vl => k Hk; ilia.
    - have Os : vg 0 (- (x1 + x2)) by vg0.
      have ns' : - (x1 + x2) != 0 by rewrite oppr_eq0.
      have vs : 0 <= v (- (x1 + x2)) by case: Os => [ E | // ]; move: ns'; rewrite E eqxx.
      have [ nt vt ] := vb_strict Hv nl2 ns' ltac:(rewrite vl2; move: (v (N / Dn)) (v (- (x1 + x2))) vl vs => k l Hk Hl; ilia).
      split => //; rewrite vt vl2; move: (v (N / Dn)) vl => k Hk; ilia.
  Qed.

  Lemma oncQ (x y : qe rat) : on_curve (x, y) -> won (K := KQ) 0 aE 0 (x, y).
  Proof. by move=> h; exact: (proj1 (on_curve_w rat_sq2 (x, y)) h). Qed.

  Lemma oncQ2 (x y : qe rat) : on_curve (x, y) -> y ^+ 2 = x ^+ 3 + aE * x.
  Proof. by rewrite /on_curve /= expr2. Qed.

  Lemma two_neq0Q : (2%:R : qe rat) != 0.
  Proof. exact: (two0_QF rat_sq2). Qed.

  Lemma rs_fd x t : rs x t -> rs (fd (K := KQ) 0 aE x) (fd 0 abar t).
  Proof.
    move=> H; rewrite /fd; apply: rs_add; last exact: rs_aE.
    apply: rs_add; first by apply: rs_mul; [ exact: rs_nat | exact: rs_exp ].
    apply: rs_mul => //; apply: rs_mul; [ exact: rs_nat | exact: rs_0 ].
  Qed.

  Lemma fd_alt (t : 'F_r) : t ^+ 2 + t * t + t ^+ 2 + abar = fd 0 abar t.
  Proof. by rewrite /fd; ring. Qed.

  Lemma y_opp0F (u : 'F_r) : u = - u -> u = 0.
  Proof. exact: (y_opp0 two0F). Qed.

  Lemma y_opp0Q (y : qe rat) : y = - y -> y = 0.
  Proof. exact: (y_opp0 (two0_QF rat_sq2)). Qed.

  (* both points integral *)
  Lemma rp_add_ii x1 y1 x2 y2 t1 u1 t2 u2 :
    on_curve (x1, y1) -> on_curve (x2, y2) -> rs x1 t1 -> rs y1 u1 -> rs x2 t2 -> rs y2 u2 ->
    rp (wQ (Some (x1, y1)) (Some (x2, y2))) (wF (Some (t1, u1)) (Some (t2, u2))).
  Proof.
    move=> h1 h2 r1 s1 r2 s2.
    have w1 := oncQ h1; have w2 := oncQ h2.
    have wb1 : won (K := 'F_r) 0 abar 0 (t1, u1) := @rp_on (Some (x1, y1)) (Some (t1, u1)) h1 (conj r1 s1).
    have wb2 : won (K := 'F_r) 0 abar 0 (t2, u2) := @rp_on (Some (x2, y2)) (Some (t2, u2)) h2 (conj r2 s2).
    have O1 := rs_O r1; have O2 := rs_O r2.
    have c1 := oncQ2 h1; have c2 := oncQ2 h2.
    have hfd : forall t u : 'F_r, won 0 abar 0 (t, u) -> u = 0 -> fd 0 abar t != 0.
    { move=> t u w e; apply: nonsingF; move: w; rewrite /won /= e expr2 mulr0 => <-. by []. }
    case: (eqVneq t1 t2) => [ Et | nt ].
    - subst t2.
      case: (eqVneq u1 (- u2)) => [ Eu | nu ].
      + rewrite (wadd_op _ _ erefl Eu).
        have Eu2 : u2 = - u1 by rewrite Eu opprK.
        case: (eqVneq x1 x2) => [ Ex | nx ].
        * subst x2; case: (eqVneq y1 (- y2)) => [ Ey | ny ]; first by rewrite (wadd_op (K := KQ) _ _ erefl Ey).
          have Ey : y1 = y2 by case: (won_x w1 w2) => // E; move: ny; rewrite E eqxx.
          subst y2.
          have u0 : u1 = 0 by apply: y_opp0F; rewrite {2}(rs_fun s1 s2); exact: Eu.
          have ny1 : y1 != 0 by apply: contraNneq ny => ->; rewrite oppr0.
          rewrite (wadd_tg _ _ (two0_QF rat_sq2) _ ny1).
          have HD : vg 1 (2%:R * y1) by apply: vge_mul0; [ vg0 | apply/rs0; rewrite -u0 ].
          exact: (@pole_wsum _ _ _ _ _ _ O1 O1 (rs_fd r1) (hfd _ _ wb1 u0) (qe_mul_neq0 two_neq0Q ny1) HD).
        * rewrite (wadd_ch (K := KQ) _ _ _ _ nx).
          have rd : rs (x2 - x1) 0 by rewrite -(subrr t1); apply: rs_sub.
          have nd : x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
          case: (eqVneq u1 0) => [ u10 | nu1 ].
          -- have u20 : u2 = 0 by rewrite Eu2 u10 oppr0.
             have nys : y1 + y2 != 0.
             { apply/eqP => E.
               have Ey : y1 = - y2 by apply/eqP; rewrite -addr_eq0 E.
               have E0 := opp_y_sum (K := KQ) c1 c2 nx Ey.
               have R0 : rs (x1 ^+ 2 + x1 * x2 + x2 ^+ 2 + aE) (fd 0 abar t1).
               { rewrite -fd_alt; apply: rs_add; last exact: rs_aE.
                 apply: rs_add; [ apply: rs_add; [ exact: rs_exp | exact: rs_mul ] | exact: rs_exp ]. }
               rewrite E0 in R0; move: (hfd _ _ wb1 u10); by rewrite -(rs_fun rs_0 R0) eqxx. }
             rewrite (chord_alt (K := KQ) c1 c2 nx nys).
             have HN : rs (x1 ^+ 2 + x1 * x2 + x2 ^+ 2 + aE) (t1 ^+ 2 + t1 * t1 + t1 ^+ 2 + abar).
             { apply: rs_add; last exact: rs_aE.
               apply: rs_add; [ apply: rs_add; [ exact: rs_exp | exact: rs_mul ] | exact: rs_exp ]. }
             have Hnb : t1 ^+ 2 + t1 * t1 + t1 ^+ 2 + abar != 0 by rewrite fd_alt; apply: hfd wb1 u10.
             have HD : vg 1 (y1 + y2) by apply/rs0; have := rs_add s1 s2; rewrite u10 u20 addr0.
             exact: (@pole_wsum _ _ _ _ _ _ O1 O2 HN Hnb nys HD).
          -- have Hnb : u2 - u1 != 0.
             { rewrite Eu2 -opprD oppr_eq0 -mulr2n -mulr_natl; apply: mulf_neq0 => //; exact: two0F. }
             exact: (@pole_wsum _ _ _ _ _ _ O1 O2 (rs_sub s2 s1) Hnb nd (proj1 (rs0 _) rd)).
      + have Eu : u1 = u2 by case: (won_x wb1 wb2) => // E; move: nu; rewrite E eqxx.
        subst u2.
        have nu1 : u1 != 0 by apply: contraNneq nu => ->; rewrite oppr0.
        rewrite (wadd_tg _ _ two0F _ nu1).
        have r2u : rs (2%:R * y1) (2%:R * u1) by apply: rs_mul => //; exact: rs_nat.
        have n2u : 2%:R * u1 != 0 by rewrite mulf_neq0 // two0F.
        case: (eqVneq x1 x2) => [ Ex | nx ].
        * subst x2.
          have Ey : y1 = y2.
          { case: (won_x w1 w2) => [ // | E ]; exfalso; have := rs_opp s2; rewrite -E => H.
            by move: nu; rewrite {1}(rs_fun s1 H) eqxx. }
          subst y2.
          have ny1 : y1 != 0 by apply: contraNneq nu1 => E; apply/eqP; rewrite E in s1; exact: rs_fun s1 rs_0.
          rewrite (wadd_tg _ _ (two0_QF rat_sq2) _ ny1).
          exact: (@rs_wsum _ _ _ _ _ _ _ _ (rs_div (rs_fd r1) r2u n2u) r1 s1 r1).
        * rewrite (wadd_ch (K := KQ) _ _ _ _ nx).
          have r12 : rs (y1 + y2) (u1 + u1) by exact: rs_add.
          have n12 : u1 + u1 != 0 by rewrite -mulr2n -mulr_natl.
          have nys : y1 + y2 != 0 by have [ H _ ] := rs_unit r12 n12.
          rewrite (chord_alt (K := KQ) c1 c2 nx nys).
          have -> : fd 0 abar t1 / (2%:R * u1) = (t1 ^+ 2 + t1 * t1 + t1 ^+ 2 + abar) / (u1 + u1).
          { by rewrite fd_alt mulr_natl mulr2n. }
          have HN : rs (x1 ^+ 2 + x1 * x2 + x2 ^+ 2 + aE) (t1 ^+ 2 + t1 * t1 + t1 ^+ 2 + abar).
          { apply: rs_add; last exact: rs_aE.
            apply: rs_add; [ apply: rs_add; [ exact: rs_exp | exact: rs_mul ] | exact: rs_exp ]. }
          exact: (@rs_wsum _ _ _ _ _ _ _ _ (rs_div HN r12 n12) r1 s1 r2).
    - have nx : x1 != x2 by apply: contraNneq nt => E; subst x2; apply/eqP; exact: rs_fun r1 r2.
      rewrite (wadd_ch (K := KQ) _ _ _ _ nx) (wadd_ch _ _ _ _ nt).
      have nt' : t2 - t1 != 0 by rewrite subr_eq0 eq_sym.
      exact: (@rs_wsum _ _ _ _ _ _ _ _ (rs_div (rs_sub s2 s1) (rs_sub r2 r1) nt') r1 s1 r2).
  Qed.

  (* an integral point plus a point of the kernel of reduction *)
  Lemma rp_add_ik x1 y1 x2 y2 t1 u1 :
    on_curve (x1, y1) -> on_curve (x2, y2) -> rs x1 t1 -> rs y1 u1 -> x2 != 0 -> v x2 < 0 ->
    rp (wQ (Some (x1, y1)) (Some (x2, y2))) (Some (t1, u1)).
  Proof.
    move=> h1 h2 r1 s1 nx2 vx2.
    have O1 := rs_O r1; have O1' := rs_O s1.
    have nx : x1 != x2.
    { apply/eqP => E; rewrite E in O1; case: O1 => [ E0 | H ]; first by move: nx2; rewrite E0 eqxx.
      by move: H; rewrite leNgt vx2. }
    have [ ny2 vy2 ] := curve_pole h2 nx2 vx2.
    have c2 := oncQ2 h2.
    have [ nU [ E3 E4 ] ] := @kernel_chord KQ _ x1 y1 x2 y2 c2 nx2 ny2 nx.
    rewrite (wadd_ch (K := KQ) _ _ _ _ nx) /wsum /=.
    move: nU E3 E4; set z := x2 / y2; set m := y2 / x2 ^+ 2 => nU E3 E4.
    have [ ny2' vy2' ] := vb_inv Hv ny2.
    have nz : z != 0 by apply: qe_mul_neq0.
    have vz : 1 <= v z.
    { rewrite /z vM // vy2'; move: (v x2) (v y2) vx2 vy2 => p q Hp Hq; clear -Hp Hq; ilia. }
    have nx22 : x2 ^+ 2 != 0 by rewrite expr2; apply: qe_mul_neq0.
    have [ nx22' vx22' ] := vb_inv Hv nx22.
    have nm : m != 0 by apply: qe_mul_neq0.
    have vm : 1 <= v m.
    { rewrite /m vM // vx22' expr2 (vM nx2 nx2).
      move: (v x2) (v y2) vx2 vy2 => p q Hp Hq; clear -Hp Hq; ilia. }
    have Pz : vg 1 z by right.
    have Pm : vg 1 m by right.
    have Oz : vg 0 z := vge_le ler01 Pz.
    have Om : vg 0 m := vge_le ler01 Pm.
    have Pw : vg 1 (x1 * z * m) by apply: vge_mul0 => //; vg0.
    have rU : rs (1 - x1 * z * m) 1.
    { apply: (rs_congr rs_1); have -> : 1 - x1 * z * m - 1 = - (x1 * z * m) by ring.
      exact: vge_opp. }
    have [ nU' vUU ] := rs_unit rU (oner_neq0 _).
    have nU2 : (1 - x1 * z * m) ^+ 2 != 0 by rewrite expr2; apply: qe_mul_neq0.
    have nU3 : (1 - x1 * z * m) ^+ 3 != 0 by rewrite exprS; apply: qe_mul_neq0.
    have vU2 : v ((1 - x1 * z * m) ^+ 2) = 0 by rewrite expr2 vM // vUU.
    have vU3 : v ((1 - x1 * z * m) ^+ 3) = 0 by rewrite exprS vM // vU2 vUU.
    have HA := vge_aE.
    split.
    - apply: (rs_congr r1); rewrite E3.
      have := vge_div nU2 (vge_mul0r Pm (vge_kM HA O1 O1' Oz Om)); by rewrite vU2 subr0.
    - apply: (rs_congr s1); rewrite E4.
      have := vge_div nU3 (vge_opp (vge_kT HA O1 O1' Pz Pm)); by rewrite vU3 subr0.
  Qed.

  Definition onc_ptQ (P : pt rat) (h : on_curve_pt P) := proj1 (on_curve_pt_w rat_sq2 P) h.

  Lemma wQ_cancel (P Q : pt rat) : on_curve_pt P -> on_curve_pt Q -> wQ (wQ P Q) (wneg (K := KQ) Q) = P.
  Proof.
    move=> hP hQ.
    exact: (wadd_cancel (two0_QF rat_sq2) (@nonsing_QF _ rat_sq2) (onc_ptQ hP) (onc_ptQ hQ)).
  Qed.

  Theorem rp_addQ (P Q : pt rat) Pb Qb : on_curve_pt P -> on_curve_pt Q -> rp P Pb -> rp Q Qb ->
    rp (wQ P Q) (wF Pb Qb).
  Proof.
    case: P => [ [ x1 y1 ] | ]; last by case: Pb => [ [] | ].
    case: Q => [ [ x2 y2 ] | ]; last by case: Qb => [ [] | ] // h1 _ H1 _; case: Pb H1 => [ [] | ].
    move=> h1 h2.
    case: Pb => [ [ t1 u1 ] | ]; case: Qb => [ [ t2 u2 ] | ].
    - move=> [ r1 s1 ] [ r2 s2 ]; exact: (rp_add_ii h1 h2 r1 s1 r2 s2).
    - move=> [ r1 s1 ] [ nx2 vx2 ]; exact: (rp_add_ik h1 h2 r1 s1 nx2 vx2).
    - move=> [ nx1 vx1 ] [ r2 s2 ].
      rewrite (wadd_comm (onc_ptQ (P := Some (x1, y1)) h1) (onc_ptQ (P := Some (x2, y2)) h2)).
      exact: (rp_add_ik h2 h1 r2 s2 nx1 vx1).
    - move=> [ nx1 vx1 ] [ nx2 vx2 ].
      have hS : on_curve_pt (wQ (Some (x1, y1)) (Some (x2, y2))).
      { apply/(on_curve_pt_w rat_sq2).
        exact: (wadd_on (two0_QF rat_sq2) (onc_ptQ (P := Some (x1, y1)) h1)
                                           (onc_ptQ (P := Some (x2, y2)) h2)). }
      have [ Sb HS ] := rp_ex hS.
      case: Sb HS => [ [ t u ] | ] HS; last exact: HS.
      exfalso.
      move: hS HS; case ES : (wQ (Some (x1, y1)) (Some (x2, y2))) => [ [ xs ys ] | ] hS HS; last by [].
      have hN : on_curve (x2, - y2) := pt_neg_on rat_sq2 (P := Some (x2, y2)) h2.
      have := rp_add_ik hS hN (proj1 HS) (proj2 HS) nx2 vx2.
      have -> : Some (x2, - y2) = wneg (K := KQ) (Some (x2, y2)) by [].
      rewrite -ES (wQ_cancel (P := Some (x1, y1)) (Q := Some (x2, y2)) h1 h2) => H.
      by have := rp_fun H (conj nx1 vx1 : rp (Some (x1, y1)) None).
  Qed.

  Theorem rp_add (P Q : pt rat) Pb Qb : on_curve_pt P -> on_curve_pt Q -> rp P Pb -> rp Q Qb ->
    rp (ec_add P Q) (wF Pb Qb).
  Proof. rewrite (ec_add_w rat_sq2); exact: rp_addQ. Qed.

  (** ** Multiples of P0: the kernel of reduction contains [N P0] for N = #E(F_r) *)

  Section multiples.

    Variable D : FixedData.
    Hypothesis hP0 : on_curve (fd_P0 D).

    Lemma rp_mulQn g : rp (Some (fd_P0 D)) g -> forall k, rp (mulQn D k) (wmuln (K := 'F_r) 0 abar g k).
    Proof.
      move=> Hg; elim => [ | k IH ]; first by [].
      rewrite /mulQn /wmuln !iterS -/(mulQn D k) -/(wmuln _ _ g k).
      exact: (rp_add (P := Some (fd_P0 D)) hP0 (mulQ_on hP0 k) Hg IH).
    Qed.

    Theorem kernel_mult (N : nat) :
      (forall g, won_pt 0 abar 0 g -> wmuln (K := 'F_r) 0 abar g N = None) ->
      forall n : int, (N %| `|n|)%N -> rp (mulQ D n) None.
    Proof.
      move=> HN.
      have [ g Hg ] := rp_ex (P := Some (fd_P0 D)) hP0.
      have wg : won_pt 0 abar 0 g := rp_on (P := Some (fd_P0 D)) hP0 Hg.
      have Hm : forall t, wmuln (K := 'F_r) 0 abar g (t * N) = None.
      { elim => [ | t IH ]; first by [].
        by rewrite mulSn (wmuln_add two0F nonsingF wg) HN // IH. }
      have Hk : forall k, (N %| k)%N -> rp (mulQn D k) None.
      { move=> k /dvdnP [ t -> ]; rewrite -(Hm t); exact: rp_mulQn. }
      case=> k Hd; first exact: Hk.
      have -> : mulQ D (Negz k) = pt_neg (mulQn D k.+1) by [].
      have := Hk _ Hd; case: (mulQn D k.+1) => [ [ x y ] | ] //.
    Qed.

  End multiples.

End residue.

(** * 4. The finite group of points of  y^2 = x^3 + a x  over F_r, and Lagrange

    For 2 <> 0 and a <> 0 in 'F_r, the points (O = None and the affine
    solutions) with the chord-tangent law [wadd] of GroupLaw.v form a
    [finGroupType] (associativity: GroupLaw.wadd_assoc, generic over any
    field with 2 <> 0 and a nonsingular cubic). Lagrange's theorem
    (MathComp [expg_cardG]) gives  #E(F_r) . P = O, and the order of the
    group is the point count [countF] of ExplicitData.v. *)

Definition onb (r : nat) (a : 'F_r) (P : option ('F_r * 'F_r)) : bool :=
  if P is Some (x, y) then y ^+ 2 == fc 0 a 0 x else true.

Lemma onbP (r : nat) (a : 'F_r) P : reflect (won_pt 0 a 0 P) (onb a P).
Proof. case: P => [ [ x y ] | ] /=; [ exact: eqP | exact: ReflectT ]. Qed.

Definition goodF (r : nat) (a : 'F_r) : bool := (2%:R != 0 :> 'F_r) && (a != 0).

Definition EPT (r : nat) (a : 'F_r) (h : goodF a) : Type := {P : option ('F_r * 'F_r) | onb a P}.

#[warning="-redundant-canonical-projection"]
HB.instance Definition _ (r : nat) (a : 'F_r) (h : goodF a) := Finite.on (@EPT r a h).

Section ept.

  Variables (r : nat) (a : 'F_r) (h : goodF a).

  Let two0 : 2%:R != 0 :> 'F_r. Proof. by case/andP: h. Qed.
  Let a0 : a != 0. Proof. by case/andP: h. Qed.
  Let nons := nonsing0 two0 a0.

  Lemma onb_add P Q : onb a P -> onb a Q -> onb a (wadd 0 a P Q).
  Proof. move=> /onbP hP /onbP hQ; apply/onbP; exact: wadd_on. Qed.

  Lemma onb_neg P : onb a P -> onb a (wneg P).
  Proof. move=> /onbP hP; apply/onbP; exact: wneg_on. Qed.

  Local Abbreviation T := (@EPT r a h).

  Definition emul (P Q : T) : T := exist _ (wadd 0 a (val P) (val Q)) (onb_add (valP P) (valP Q)).
  Definition eone : T := exist _ None isT.
  Definition einv (P : T) : T := exist _ (wneg (val P)) (onb_neg (valP P)).

  Lemma emulA : associative emul.
  Proof.
    move=> P Q R; apply: val_inj => /=; symmetry.
    by apply: (wadd_assoc two0 nons); apply/onbP; apply: valP.
  Qed.

  Lemma emul1 : left_id eone emul.
  Proof. by move=> P; apply: val_inj. Qed.

  Lemma emulV : left_inverse eone einv emul.
  Proof. by move=> P; apply: val_inj => /=; rewrite waddNl. Qed.

End ept.

HB.instance Definition _ (r : nat) (a : 'F_r) (h : goodF a) :=
  Finite_isGroup.Build (@EPT r a h) (@emulA r a h) (@emul1 r a h) (@emulV r a h).

Section lagrange.

  Variables (r : nat) (a : 'F_r) (h : goodF a).
  Local Abbreviation T := (@EPT r a h).

  Lemma ept_expg (P : T) n : val (P ^+ n)%g = wmuln 0 a (val P) n.
  Proof. elim: n => [ | n IH ]; first by []. by rewrite expgS /= -IH. Qed.

  (* Lagrange: #E(F_r) kills every point *)
  Theorem wmuln_card P : won_pt 0 a 0 P -> wmuln 0 a P #|{: T}| = None.
  Proof.
    move=> /onbP hP; pose X : T := exist _ P hP.
    have := expg_cardG (G := [set: T]%G) (in_setT X); rewrite cardsT => /(congr1 val).
    by rewrite ept_expg.
  Qed.

End lagrange.

(** ** The group order is the point count [countF] *)

Lemma card_count (T : finType) (A : pred T) (l : seq T) :
  uniq l -> (forall x, x \in l) -> #|A| = count A l.
Proof.
  move=> ul al; rewrite -size_filter; have /card_uniqP <- := filter_uniq A ul.
  by apply: eq_card => x; rewrite mem_filter al andbT.
Qed.

Definition grid (r : nat) : seq (nat * nat) := [seq (i, j) | i <- iota 0 r, j <- iota 0 r].

Lemma grid_uniq r : uniq (grid r).
Proof.
  rewrite /grid. apply: allpairs_uniq; [ exact: iota_uniq | exact: iota_uniq | ].
  by move=> [ ? ? ] [ ? ? ] _ _ [] -> ->.
Qed.

Lemma Fr_nat_inj (r i i' : nat) : prime r -> (i < r)%N -> (i' < r)%N ->
  (i%:R : 'F_r) = i'%:R -> i = i'.
Proof. by move=> Hr Hi Hi' /(congr1 (@nat_of_ord _)); rewrite !val_Fp_nat // !modn_small. Qed.

Lemma card_EPT (r : nat) (a : 'F_r) (h : goodF a) : prime r ->
  #|{: EPT h}| = (count (fun p : nat * nat => onb a (Some (p.1%:R, p.2%:R))) (grid r)).+1.
Proof.
  move=> Hr; rewrite card_sig.
  pose l := None :: [seq Some ((p.1%:R : 'F_r), (p.2%:R : 'F_r)) | p <- grid r].
  have ul : uniq l.
  { rewrite /l /=; apply/andP; split.
    - by apply/negP => /mapP [ p _ ].
    - have Hinj : {in grid r &, injective (fun p : nat * nat => Some ((p.1%:R : 'F_r), (p.2%:R : 'F_r)))}.
      { move=> [ i j ] [ i' j' ] /allpairsP [ [ i1 j1 ] [ Hi1 Hj1 E1 ] ] /allpairsP [ [ i2 j2 ] [ Hi2 Hj2 E2 ] ].
        move: E1 E2 Hi1 Hj1 Hi2 Hj2 => /= [ -> -> ] [ -> -> ]; rewrite !mem_iota !add0n => Hi1 Hj1 Hi2 Hj2.
        move=> [] E1 E2.
        by rewrite (Fr_nat_inj Hr Hi1 Hi2 E1) (Fr_nat_inj Hr Hj1 Hj2 E2). }
      rewrite (map_inj_in_uniq Hinj); exact: grid_uniq. }
  have al : forall P, P \in l.
  { case=> [ [ t u ] | ]; last by rewrite inE eqxx.
    rewrite inE /=; apply/mapP; exists (val t, val u).
    - have Ht : (val t < r)%N by apply: (leq_trans (ltn_ord t)); rewrite (Fp_cast Hr).
      have Hu : (val u < r)%N by apply: (leq_trans (ltn_ord u)); rewrite (Fp_cast Hr).
      by apply: allpairs_f; rewrite mem_iota add0n.
    - by rewrite /= !natr_Zp. }
  rewrite (card_count _ ul al) /l /= count_map.
  by [].
Qed.

Lemma length_filter (T : Type) (p : pred T) (l : seq T) : List.length (filter p l) = count p l.
Proof. by elim: l => //= x l IH; case: (p x) => /=; rewrite IH. Qed.

Lemma countF_grid (r : nat) (A : Z) :
  countF (Z.of_nat r) A =
  (count (fun p : nat * nat =>
     (Z.modulo (Z.of_nat p.2 * Z.of_nat p.2 - (Z.of_nat p.1 * Z.of_nat p.1 * Z.of_nat p.1 + A * Z.of_nat p.1))
               (Z.of_nat r) =? 0)%ZZ) (grid r)).+1.
Proof.
  rewrite /countF Nat2Z.id length_filter; congr S.
  have E : forall I J : seq nat,
      flat_map (fun x => map (fun y => (x, y)) (map Z.of_nat J)) (map Z.of_nat I)
      = map (fun p : nat * nat => (Z.of_nat p.1, Z.of_nat p.2)) [seq (i, j) | i <- I, j <- J].
  { move=> I J; elim: I => [ | i I IH ] //=.
    by rewrite IH map_cat -!map_comp. }
  rewrite E /grid.
  by rewrite count_map.
Qed.

Lemma onb_Z (r : nat) (A : Z) (i j : nat) : prime r ->
  onb ((Z_to_int A)%:~R : 'F_r) (Some (i%:R, j%:R)) =
  (Z.modulo (Z.of_nat j * Z.of_nat j - (Z.of_nat i * Z.of_nat i * Z.of_nat i + A * Z.of_nat i))
            (Z.of_nat r) =? 0)%ZZ.
Proof.
  move=> Hr; rewrite /onb /fc.
  set n : int := j%:Z * j%:Z - (i%:Z * i%:Z * i%:Z + Z_to_int A * i%:Z).
  have E : (j%:R ^+ 2 : 'F_r) - (i%:R ^+ 3 + 0 * i%:R ^+ 2 + (Z_to_int A)%:~R * i%:R + 0) = n%:~R.
  { rewrite /n intrB intrD !intrM -!pmulrn; ring. }
  rewrite -subr_eq0 E (Fr_int0 _ Hr).
  have En : int_to_Z n = (Z.of_nat j * Z.of_nat j - (Z.of_nat i * Z.of_nat i * Z.of_nat i + A * Z.of_nat i))%ZZ.
  { by rewrite /n iz_add iz_opp iz_add !iz_mul !iz_nat iz_Z_to_int. }
  have Hr0 : Z.of_nat r <> 0%ZZ by move: (prime_gt0 Hr) => /ssrnat.ltP; lia.
  apply/idP/idP => H.
  - apply/Z.eqb_eq/Z.mod_divide => //; rewrite -En; exact: dvdz_Z.
  - apply: Z_dvdz; rewrite En; apply/Z.mod_divide => //; exact/Z.eqb_eq.
Qed.

Theorem card_countF (r : nat) (A : Z) (h : goodF ((Z_to_int A)%:~R : 'F_r)) : prime r ->
  #|{: EPT h}| = countF (Z.of_nat r) A.
Proof.
  move=> Hr; rewrite card_EPT // countF_grid; congr S; apply: eq_count => -[ i j ] /=.
  exact: onb_Z.
Qed.

(** * 5. The kernel of reduction contains the multiples of #E(F_r) . P0 *)

(* reduction to O at v, with a nonzero x-coordinate: O, or 0 <> x with v(x) < 0 *)
Definition kern (v : qe rat -> int) (P : pt rat) : Prop :=
  if P is Some (x, _) then x != 0 /\ v x < 0 else True.

Lemma rp_kern (r : nat) (v : qe rat -> int) P : @rp r v P None -> kern v P.
Proof. by case: P => [ [] | ]. Qed.

Theorem kernel_countF (D : FixedData) (r : nat) (v : qe rat -> int) (c : int) :
  prime r -> r != 2%N -> r != 7%N -> is_place_above v r ->
  (r%:Z %| c ^+ 2 - 2)%Z -> 1 <= v (tcq c) -> on_curve (fd_P0 D) ->
  forall n : int, (countF (Z.of_nat r) (aEmod (Z.of_nat r) (int_to_Z c)) %| `|n|)%N ->
  kern v (mulQ D n).
Proof.
  move=> Hr r2 r7 Hv c_root c_place hP0 n Hn.
  set A := aEmod (Z.of_nat r) (int_to_Z c) in Hn.
  have Ea : abar r c = (Z_to_int A)%:~R := abar_aEmod Hr c.
  have h : goodF ((Z_to_int A)%:~R : 'F_r).
  { rewrite /goodF -Ea; apply/andP; split; [ exact: two0F | exact: abar_neq0 ]. }
  rewrite -(card_countF h Hr) in Hn.
  apply: (@rp_kern r v); apply: (kernel_mult Hr r2 Hv c_root c_place r7 hP0 _ Hn).
  move=> g; rewrite Ea; exact: wmuln_card.
Qed.

(** * 6. The Chinese remainder choice of h (proof of Cor pri:integer-tests) *)

Lemma crt_h (d1 d2 r K : nat) : prime r -> (0 < d1)%N -> (0 < d2)%N ->
  (gcdn d1 d2 %| 4)%N -> ~~ (r %| d1)%N ->
  exists h : int, h != 0 /\ (d1%:Z %| h)%Z /\ ((d2 * r ^ K)%N%:Z %| h - 4)%Z.
Proof.
  move=> Hr H1 H2 Hg Hd.
  set M := (d2 * r ^ K)%N.
  have HM : (0 < M)%N by rewrite muln_gt0 H2 expn_gt0 prime_gt0.
  have Hc : coprime d1 (r ^ K) by apply: coprimeXr; rewrite coprime_sym prime_coprime.
  have EG : gcdn d1 M = gcdn d1 d2 by rewrite /M mulnC Gauss_gcdr.
  have [ q Hq ] : exists q : nat, 4%N = (gcdn d1 M * q)%N.
  { move: Hg; rewrite -EG => /dvdnP [ q Hq ]; exists q; by rewrite mulnC. }
  have [ u [ w Huw ] ] := Bezoutz d1%:Z M%:Z.
  rewrite /gcdz /= in Huw.
  set h0 : int := u * d1%:Z * q%:Z.
  have D1 : (d1%:Z %| h0)%Z by rewrite /h0; apply: dvdz_mulr; apply: dvdz_mull; exact: dvdzz.
  have D2 : (M%:Z %| h0 - 4)%Z.
  { have -> : h0 - 4 = - (w * q%:Z) * M%:Z.
    { have E4 : (4 : int) = (gcdn d1 M)%:Z * q%:Z by rewrite -PoszM -Hq.
      rewrite /h0 E4 -Huw; ring. }
    apply: dvdz_mull; exact: dvdzz. }
  case: (eqVneq h0 0) => [ E0 | nh0 ]; last by exists h0.
  exists (d1%:Z * M%:Z); split; first by rewrite mulf_neq0 // eqz_nat -lt0n.
  split; first by apply: dvdz_mulr; exact: dvdzz.
  have -> : d1%:Z * M%:Z - 4 = (h0 - 4) + d1%:Z * M%:Z by rewrite E0 add0r addrC.
  by apply: rpredD => //; apply: dvdz_mull; exact: dvdzz.
Qed.

(** * 7. Cor pri:integer-tests and Cor pri:integer-coverage (HCov) *)

(* the fields O_F1 and O_F2 of OrdHyps (FixedData.v), verbatim *)
Definition O_F1_stmt (D : FixedData) : Prop :=
  forall (sg : bool) (p : nat), prime p -> p \notin fd_SE D ->
    forall v, is_place_above v p ->
    forall n n' : int, n' != 0 ->
    red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
    n = 0 \/ v (zpar sg (mulP D n)) - v (zpar sg (mulP D n')) = vqr p n%:~R - vqr p n'%:~R.

Definition O_F2_stmt (D : FixedData) : Prop :=
  forall (sg : bool) (K p : nat), (1 <= K)%N -> prime p -> p \notin fd_SE D -> (K.+1 < p)%N ->
    forall v, is_place_above v p ->
    forall n n' : int, n' != 0 ->
    red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
    (n = 0 \/ vqr p n'%:~R <= vqr p n%:~R) ->
    ellK sg K (zpar sg (mulP D n')) != 0 /\
    (let x := ellK sg K (zpar sg (mulP D n)) / ellK sg K (zpar sg (mulP D n'))
              - qe_of (n%:~R / n'%:~R) in x = 0 \/ K%:Z <= v x).

Lemma O_F1_of (D : FixedData) : OrdHyps D -> O_F1_stmt D.
Proof. by case. Qed.

Lemma O_F2_of (D : FixedData) : OrdHyps D -> O_F2_stmt D.
Proof. by case. Qed.

Lemma LocZ0 (i : nat) (r B : int) (s : sgn) : LocZ i r B s 0.
Proof.
  exists 0, 0, 1, 0, 1, 0; split; first by rewrite mul0r !mulr0z qe0E -qe0E mulr0.
  by rewrite !mulr0 addr0 mulr1 subrr.
Qed.

Lemma kern_red (v : qe rat -> int) (P : pt rat) : kern v P -> red_ord false v P.
Proof. by case: P => [ [ x y ] [] | ]. Qed.

Lemma kern_red_conj (v : qe rat -> int) (P : pt rat) :
  kern (fun x => v (qe_conj x)) P -> red_ord true v P.
Proof. by case: P => [ [ x y ] [] | ]. Qed.

Section bridge.

  Variables (r : nat) (B : int) (s : sgn).
  Hypothesis r_prime : prime r.
  Hypothesis r_odd : r != 2%N.
  Hypothesis B_root : exists wB : int, B ^+ 2 - 2 = r%:Z * wB.

  Local Abbreviation w := (wsplit r B s).

  Lemma kern_FormalZ (P : pt rat) : kern (ovP w) P -> FormalZ false r%:Z B s P.
  Proof.
    case: P => [ [ x y ] | ] //= [ nx vx ].
    have [ ni Ei ] := vb_inv (wsplit_place r_prime r_odd B_root s) nx.
    apply/(LocZ_ovP r_prime r_odd B_root s 1 ni); rewrite Ei.
    by move: (ovP w x) vx => k Hk; clear -Hk; ilia.
  Qed.

  Lemma kern_FormalZ_conj (P : pt rat) : kern (fun x => ovP w (qe_conj x)) P -> FormalZ true r%:Z B s P.
  Proof.
    case: P => [ [ x y ] | ] //= [ nx vx ].
    have nx' := qe_conj_neq0 nx.
    have [ ni Ei ] := vb_inv (wsplit_place r_prime r_odd B_root s) nx'.
    apply/(LocZ_ovP r_prime r_odd B_root s 1 ni); rewrite Ei.
    by move: (ovP w (qe_conj x)) vx => k Hk; clear -Hk; ilia.
  Qed.

  Lemma val_LocZw (i : nat) (alpha : qe rat) : (alpha = 0 \/ i%:Z <= ovP w alpha) -> LocZ i r%:Z B s alpha.
  Proof.
    case: (eqVneq alpha 0) => [ -> _ | na [ E | H ] ]; first exact: LocZ0.
    - by move: na; rewrite E eqxx.
    - exact/(LocZ_ovP r_prime r_odd B_root s i na).
  Qed.

End bridge.

Section integer_tests.

  Variables (C : i4 -> rat) (S : seq nat) (Hb c : nat) (Kset : seq nat) (Nh Ch : nat).
  Local Abbreviation D := (mkData C S Hb c Kset Nh Ch).

  Hypothesis HF1 : O_F1_stmt D.
  Hypothesis HF2 : O_F2_stmt D.

  Lemma mulP_mk (n : int) : mulP D n = mulQ D (n * (2%N)%:Z).
  Proof. by []. Qed.

  Lemma zpar_mulP0 (sg : bool) : zpar sg (mulP D 0) = 0.
  Proof. by rewrite mulP_mk mul0r. Qed.

  (* Cor pri:integer-tests at one place sqrt2 |-> s B above r *)
  Theorem integer_tests (K r : nat) (B : int) (s : sgn) :
    (1 <= K)%N -> prime r -> (K.+1 < r)%N -> (7 < r)%N ->
    (exists wB : int, B ^+ 2 - 2 = r%:Z * wB) ->
    (gcdn (cntE (Z.of_nat r) (int_to_Z (sgnz s * B))) (cntE (Z.of_nat r) (- int_to_Z (sgnz s * B))) %| 4)%N ->
    ~~ (r %| cntE (Z.of_nat r) (int_to_Z (sgnz s * B)) * cntE (Z.of_nat r) (- int_to_Z (sgnz s * B)))%N ->
    exists h j0 : int, h != 0 /\ j0 != 0 /\ forall a : int, RepConds D K r%:Z B s h j0 a.
  Proof.
    move=> HK Hr Hrk Hr7 HB Hg Hnd.
    have r2 : r != 2%N by apply/eqP => E; move: Hr7; rewrite E.
    have r7 : r != 7%N by apply/eqP => E; move: Hr7; rewrite E.
    set cc := sgnz s * B.
    set v := ovP (wsplit r B s).
    have Hv : is_place_above v r := wsplit_place Hr r2 HB s.
    have cpl : 1 <= v (tcq cc) := wsplit_root Hr r2 HB s.
    have crt : (r%:Z %| cc ^+ 2 - 2)%Z := c_root_of HB s.
    set v' := fun x => v (qe_conj x).
    have Hv' : is_place_above v' r := conj_place Hv.
    have cpl' : 1 <= v' (tcq (- cc)) by rewrite /v' conj_tcq (vbN Hv) ?tcq_neq0.
    have crt' : (r%:Z %| (- cc) ^+ 2 - 2)%Z by rewrite sqrrN.
    have hP0 : on_curve (fd_P0 D) := mkData_P0_on_curve C S Hb c Kset Nh Ch.
    set d1 := cntE (Z.of_nat r) (int_to_Z cc) in Hg Hnd.
    set d2 := cntE (Z.of_nat r) (- int_to_Z cc) in Hg Hnd.
    have K1 : forall n : int, (d1 %| `|n|)%N -> kern v (mulQ D n).
    { exact: (kernel_countF Hr r2 r7 Hv crt cpl hP0). }
    have K2 : forall n : int, (d2 %| `|n|)%N -> kern v' (mulQ D n).
    { move=> n Hn; apply: (kernel_countF Hr r2 r7 Hv' crt' cpl' hP0); by rewrite iz_opp. }
    have d1p : (0 < d1)%N by [].
    have d2p : (0 < d2)%N by [].
    have nd1 : ~~ (r %| d1)%N by apply: contra Hnd => H; apply: dvdn_mulr.
    have nd2 : ~~ (r %| d2)%N by apply: contra Hnd => H; apply: dvdn_mull.
    have [ h [ nh [ Dh Dh4 ] ] ] := crt_h K Hr d1p d2p Hg nd1.
    have D2h4 : (d2%:Z %| h - 4)%Z.
    { apply: dvdz_trans Dh4; rewrite PoszM; apply: dvdz_mulr; exact: dvdzz. }
    have RKh4 : (r%:Z ^+ K %| h - 4)%Z.
    { have E : (r ^ K)%N%:Z = r%:Z ^+ K by rewrite -!natz natrX.
      apply: dvdz_trans Dh4; rewrite PoszM E; apply: dvdz_mull; exact: dvdzz. }
    have Kv : forall n : int, (d1%:Z %| n)%Z -> kern v (mulP D n).
    { move=> n Hn; rewrite mulP_mk; apply: K1; rewrite abszM; apply: dvdn_mulr; by move: Hn; rewrite dvdzE. }
    have Kv' : forall n : int, (d2%:Z %| n)%Z -> kern v' (mulP D n).
    { move=> n Hn; rewrite mulP_mk; apply: K2; rewrite abszM; apply: dvdn_mulr; by move: Hn; rewrite dvdzE. }
    have r_SE : r \notin fd_SE D by rewrite /= !inE negb_or r2 r7.
    exists h, d2%:Z; split => //; split; first by rewrite eqz_nat -lt0n.
    move=> a.
    have Dha : (d1%:Z %| h * a)%Z by apply: dvdz_mulr.
    have Dh4a : (d2%:Z %| (h - 4) * a)%Z by apply: dvdz_mulr.
    (* the truncated logarithm test (F2 with indices h a, h) *)
    have Hcond : h * a = 0 \/ vqr r h%:~R <= vqr r (h * a)%:~R.
    { case: (eqVneq a 0) => [ -> | na ]; first by left; rewrite mulr0.
      right; rewrite !vqr_int abszM lognM ?absz_gt0 //= lez_nat; exact: leq_addr. }
    have [ Hell Hlog ] := HF2 HK Hr r_SE Hrk Hv nh (kern_red (Kv _ Dha)) (kern_red (Kv _ Dh)) Hcond.
    have Eq : qe_of ((h * a)%:~R / h%:~R) = a%:~R :> qe rat.
    { have nh' : (h%:~R : rat) != 0 by rewrite intr_eq0.
      by rewrite intrM mulrAC divff // mul1r qe_intE. }
    move: Hlog; cbv zeta; rewrite Eq => Hlog.
    (* the conjugate ratio test (F1 on E^sigma with indices (h - 4) a, j0 = d2) *)
    have nd2' : d2%:Z != 0 by rewrite eqz_nat -lt0n.
    have L7 : LocZ K r%:Z B s (zpar true (mulP D ((h - 4) * a)) / zpar true (mulP D d2%:Z)).
    { set z1 := zpar true (mulP D ((h - 4) * a)); set z2 := zpar true (mulP D d2%:Z).
      apply: (@val_LocZw r B s Hr r2 HB); case: (eqVneq (z1 / z2) 0) => [ -> | nal ]; first by left.
      right.
      have nz1 : z1 != 0 by apply: contraNneq nal => ->; rewrite mul0r.
      have nz2 : z2 != 0 by apply: contraNneq nal => ->; rewrite invr0 mulr0.
      have [ E0 | E1 ] := HF1 Hr r_SE Hv nd2' (kern_red_conj (Kv' _ Dh4a))
                                 (kern_red_conj (Kv' _ (dvdzz _))).
      - by move: nz1; rewrite /z1 E0 zpar_mulP0 eqxx.
      - have nn : (h - 4) * a != 0 by apply: contraNneq nz1 => E; rewrite /z1 E zpar_mulP0.
        have [ ni Ei ] := vb_inv Hv nz2.
        rewrite -/v (proj1 Hv _ _ nz1 ni) Ei.
        have -> : v z1 - v z2 = vqr r ((h - 4) * a)%:~R - vqr r (d2%:Z)%:~R by exact: E1.
        rewrite !vqr_int /= (logn_ndvd nd2) subr0 lez_nat.
        have n4 : h - 4 != 0 by apply: contraNneq nn => ->; rewrite mul0r.
        have na : a != 0 by apply: contraNneq nn => ->; rewrite mulr0.
        rewrite abszM lognM ?absz_gt0 //; apply: leq_trans (leq_addr _ _).
        rewrite -pfactor_dvdn ?absz_gt0 //.
        by move: RKh4; rewrite dvdzE abszX. }
    split; first exact: (@kern_FormalZ r B s Hr r2 HB _ (Kv _ Dh)).
    split; first exact: (@kern_FormalZ r B s Hr r2 HB _ (Kv _ Dha)).
    split; first exact: Hell.
    split; first exact: (@val_LocZw r B s Hr r2 HB K _ Hlog).
    split; first exact: (@kern_FormalZ_conj r B s Hr r2 HB _ (Kv' _ (dvdzz _))).
    split; first exact: (@kern_FormalZ_conj r B s Hr r2 HB _ (Kv' _ Dh4a)).
    exact: L7.
  Qed.

End integer_tests.

(** The field HCov of StdHyps (FixedData.v), Cor pri:integer-coverage, for
    the data [mkData], from the prime-pattern lemma (in the form
    [PatternSpec] of PaperInputs.v) and the formal-group facts O_F1, O_F2. *)
Theorem HCov_thm (C : i4 -> rat) (S : seq nat) (Hb c : nat) (Kset : seq nat) (Nh Ch : nat) :
  let D := mkData C S Hb c Kset Nh Ch in
  FixedWF D -> O_F1_stmt D -> O_F2_stmt D ->
  (forall (A : int) (Y : nat), exists W : PatWit, PatternSpec D A Y W) ->
  forall (K : nat) (A : int), (1 <= K)%N -> exists W : RepWit1, RepSpec D K A W.
Proof.
  move=> D _ HF1 HF2 HP K A HK.
  have [ W HW ] := HP A K.+1.
  have [ B HB ] := pattern_B HW.
  have Hj : forall j, exists hj : (int * int) * (int * int),
      (hj.1.1 != 0 /\ hj.1.2 != 0 /\ forall a, RepConds D K (pw_r W j)%:Z (B j) sg_p hj.1.1 hj.1.2 a) /\
      (hj.2.1 != 0 /\ hj.2.2 != 0 /\ forall a, RepConds D K (pw_r W j)%:Z (B j) sg_m hj.2.1 hj.2.2 a).
  { move=> j.
    have Hr := ps_prime HW j.
    have [ wB HwB ] := HB j.
    have T : forall s : sgn, exists h j0 : int,
        h != 0 /\ j0 != 0 /\ forall a : int, RepConds D K (pw_r W j)%:Z (B j) s h j0 a.
    { move=> s; have [ Hg Hnd ] := pattern_prime_orders_sgn Hr s HwB.
      exact: (integer_tests HF1 HF2 HK (pattern_prime_prime Hr) (pattern_prime_gtY Hr)
                            (pattern_prime_gt7 Hr) (HB j) Hg Hnd). }
    have [ hp [ jp Hp ] ] := T sg_p; have [ hm [ jm Hm ] ] := T sg_m.
    by exists ((hp, jp), (hm, jm)). }
  have [ f Hf ] := mem13_choice Hj.
  exists (pw_ext W B (fun j s => if s is sg_p then (f j).1.1 else (f j).2.1)
                     (fun j s => if s is sg_p then (f j).1.2 else (f j).2.2)).
  apply: (RepSpec_of_pattern HW (leqnn _) HB).
  move=> j [] /=; [ exact: (proj1 (Hf j)) | exact: (proj2 (Hf j)) ].
Qed.

(* the same with the record OrdHyps as the source of O_F1, O_F2 *)
Corollary HCov_of_OrdHyps (C : i4 -> rat) (S : seq nat) (Hb c : nat) (Kset : seq nat) (Nh Ch : nat) :
  let D := mkData C S Hb c Kset Nh Ch in
  FixedWF D -> OrdHyps D ->
  (forall (A : int) (Y : nat), exists W : PatWit, PatternSpec D A Y W) ->
  forall (K : nat) (A : int), (1 <= K)%N -> exists W : RepWit1, RepSpec D K A W.
Proof. move=> D HWF HO; exact: (HCov_thm HWF (O_F1_of HO) (O_F2_of HO)). Qed.

