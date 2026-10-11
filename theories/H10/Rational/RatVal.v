(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The q-adic valuation [vqr q] on MathComp's rat (defined in
   FixedData.v as logn of the numerator minus logn of the denominator,
   junk value 0 at 0), for a prime q:
   - [vqr_frac]: the valuation of a fraction a/c of nonzero integers,
     computed from any (not necessarily reduced) representation;
   - multiplicativity [vqrM], [vqrV], [vqr_div], [vqrX2], [vqrN];
   - values on integers [vqr_int], [vqr1], [vqr_prime];
   - units [vqr_unit] (q outside the support of x);
   - the ultrametric inequality [vqr_add_min], [vqr_add_ge] and
     its strict form [vqr_add_lt];
   - a bridge [int_to_Z] from int to Z (parity, order) so that
     integer side conditions can be closed by lia.
   No result of the paper is formalized here. *)

From Stdlib Require Import ZArith Lia List.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential FixedData.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

(** * The bridge int -> Z *)

Section int_Z.

  Local Abbreviation iz := int_to_Z.

  Lemma iz_inj (a b : int) : iz a = iz b -> a = b.
  Proof.
    move=> H; apply: (@intr_inj rat).
    by rewrite -!Z_to_rat_int H.
  Qed.

  Lemma iz_add (a b : int) : iz (a + b) = (iz a + iz b)%ZZ.
  Proof.
    apply Z_to_rat_inj.
    by rewrite Z_to_rat_add !Z_to_rat_int rmorphD.
  Qed.

  Lemma iz_opp (a : int) : iz (- a) = (- iz a)%ZZ.
  Proof.
    apply Z_to_rat_inj.
    by rewrite Z_to_rat_opp !Z_to_rat_int rmorphN.
  Qed.

  Lemma iz_mul (a b : int) : iz (a * b) = (iz a * iz b)%ZZ.
  Proof.
    apply Z_to_rat_inj.
    by rewrite Z_to_rat_mul !Z_to_rat_int rmorphM.
  Qed.

  Lemma iz_nat (n : nat) : iz n%:Z = Z.of_nat n.
  Proof. by []. Qed.

  Lemma iz_ge0 (a : int) : (0 <= a) <-> (0 <= iz a)%ZZ.
  Proof. case: a => n /=; split => //; lia. Qed.

  Lemma iz_le (a b : int) : (a <= b) <-> (iz a <= iz b)%ZZ.
  Proof.
    rewrite -subr_ge0 iz_ge0 iz_add iz_opp; lia.
  Qed.

  Lemma iz_lt (a b : int) : (a < b) <-> (iz a < iz b)%ZZ.
  Proof.
    rewrite ltNge; split.
    - move=> /negP H; apply Z.nle_gt => H'; apply: H; exact/iz_le.
    - move=> H; apply/negP => /iz_le; lia.
  Qed.

  Lemma ssr_odd_Z (n : nat) : odd n = Z.odd (Z.of_nat n).
  Proof.
    elim: n => [ // | n IH ].
    by rewrite Nat2Z.inj_succ Z.odd_succ -Z.negb_odd -IH.
  Qed.

  Lemma iz_odd (a : int) : odd `|a| = Z.odd (iz a).
  Proof.
    case: a => n; rewrite /int_to_Z.
    - by rewrite ssr_odd_Z.
    - by rewrite Z.odd_opp -ssr_odd_Z.
  Qed.

  (* parity lemmas used for valuations *)

  Lemma odd_dbl (a : int) : odd `|a + a| = false.
  Proof.
    rewrite iz_odd iz_add Z.odd_add.
    by case: (Z.odd (iz a)).
  Qed.

  Lemma odd_add_dbl (k j : int) : odd `|k + (j + j)| = odd `|k|.
  Proof.
    rewrite !iz_odd !iz_add !Z.odd_add.
    by case: (Z.odd (iz k)); case: (Z.odd (iz j)).
  Qed.

  Lemma odd_add (a b : int) : odd `|a + b| = odd `|a| (+) odd `|b|.
  Proof.
    rewrite !iz_odd !iz_add !Z.odd_add.
    by case: (Z.odd (iz a)); case: (Z.odd (iz b)).
  Qed.

End int_Z.

(** * The q-adic valuation *)

Section RatVal.

  Variable q : nat.
  Hypothesis q_prime : prime q.

  Local Abbreviation v := (vqr q).

  Lemma logn_ndvd (n : nat) : ~~ (q %| n)%N -> logn q n = 0%N.
  Proof.
    move=> H; apply/eqP; rewrite -leqn0 leqNgt logn_gt0 mem_primes.
    by rewrite (negbTE H) !andbF.
  Qed.

  Lemma rat_int_neq0 (a : int) : a != 0 -> a%:~R != 0 :> rat.
  Proof. by rewrite intr_eq0. Qed.

  (* the valuation of a fraction of nonzero integers *)
  Lemma vqr_frac (a c : int) : a != 0 -> c != 0 ->
    v (a%:~R / c%:~R) = (logn q `|a|)%:Z - (logn q `|c|)%:Z.
  Proof.
    move=> Ha Hc.
    set x := a%:~R / c%:~R.
    have Hd := denq_neq0 x.
    have Hx : x != 0 by rewrite /x mulf_neq0 ?invr_eq0 ?rat_int_neq0.
    have Hn : numq x != 0 by rewrite numq_eq0.
    have E : numq x * c = a * denq x.
    { apply: (@intr_inj rat); rewrite !intrM.
      have := divq_num_den x; rewrite /x => /eqP.
      rewrite eqr_div ?rat_int_neq0 // => /eqP ->; by rewrite mulrC. }
    have E' : (logn q `|numq x| + logn q `|c|)%N = (logn q `|a| + logn q `|denq x|)%N.
    { rewrite -!lognM ?absz_gt0 // -!abszM; by rewrite E. }
    rewrite /vqr.
    have : (logn q `|numq x|)%:Z + (logn q `|c|)%:Z = (logn q `|a|)%:Z + (logn q `|denq x|)%:Z.
    { by rewrite -!PoszD E'. }
    move=> /(congr1 int_to_Z); rewrite !iz_add !iz_nat => H.
    apply: iz_inj; rewrite !iz_add !iz_opp !iz_nat; lia.
  Qed.

  Lemma vqr_numden (x : rat) :
    v x = (logn q `|numq x|)%:Z - (logn q `|denq x|)%:Z.
  Proof. by []. Qed.

  Lemma vqr_int (a : int) : v a%:~R = (logn q `|a|)%:Z.
  Proof. by rewrite /vqr numq_int denq_int logn1 subr0. Qed.

  Lemma vqr1 : v 1 = 0.
  Proof. by rewrite /vqr /= logn1. Qed.

  Lemma vqr_prime : v q%:R = 1.
  Proof using q_prime.
    have -> : q%:R = (q%:Z)%:~R :> rat by rewrite -pmulrn.
    rewrite vqr_int /=.
    by rewrite (@logn_prime q q q_prime) eqxx.
  Qed.

  Lemma vqrN (x : rat) : v (- x) = v x.
  Proof. by rewrite /vqr numqN denqN abszN. Qed.

  Lemma vqrM (x y : rat) : x != 0 -> y != 0 -> v (x * y) = v x + v y.
  Proof.
    move=> Hx Hy.
    have Hnx : numq x != 0 by rewrite numq_eq0.
    have Hny : numq y != 0 by rewrite numq_eq0.
    have Hdx := denq_neq0 x; have Hdy := denq_neq0 y.
    have -> : x * y = (numq x * numq y)%:~R / (denq x * denq y)%:~R.
    { by rewrite !intrM -mulf_div !divq_num_den. }
    rewrite vqr_frac ?mulf_neq0 // !abszM !lognM ?absz_gt0 // /vqr.
    apply: iz_inj; rewrite !iz_add !iz_opp !iz_nat !Nat2Z.inj_add; lia.
  Qed.

  Lemma vqrV (x : rat) : v x^-1 = - v x.
  Proof.
    case: (eqVneq x 0) => [ -> | Hx ]; first by rewrite invr0 /vqr /= !logn1 !logn0.
    have Hnx : numq x != 0 by rewrite numq_eq0.
    have Hdx := denq_neq0 x.
    have -> : x^-1 = (denq x)%:~R / (numq x)%:~R.
    { by rewrite -[x in LHS]divq_num_den invf_div. }
    by rewrite vqr_frac // /vqr opprB.
  Qed.

  Lemma vqr_div (x y : rat) : x != 0 -> y != 0 -> v (x / y) = v x - v y.
  Proof. move=> Hx Hy; by rewrite vqrM ?invr_eq0 // vqrV. Qed.

  Lemma vqrX2 (x : rat) : x != 0 -> v (x ^+ 2) = v x + v x.
  Proof. move=> Hx; by rewrite expr2 vqrM. Qed.

  (* units: q outside the support of x *)
  Lemma vqr_unit (x : rat) : q \notin rat_support x -> v x = 0.
  Proof.
    rewrite /rat_support mem_cat negb_or => /andP [H1 H2].
    rewrite /vqr.
    have -> : logn q `|numq x| = 0%N by apply/eqP; rewrite -leqn0 leqNgt logn_gt0.
    have -> : logn q `|denq x| = 0%N by apply/eqP; rewrite -leqn0 leqNgt logn_gt0.
    by [].
  Qed.

  Lemma vqr_nat_ndvd (n : nat) : ~~ (q %| n)%N -> v n%:R = 0.
  Proof.
    move=> H; have -> : n%:R = (n%:Z)%:~R :> rat by rewrite -pmulrn.
    rewrite vqr_int /=.
    by rewrite logn_ndvd.
  Qed.

  (* nonnegative valuation means q does not divide the denominator *)
  Lemma vqr_ge0_den (x : rat) : 0 <= v x -> ~~ (q %| `|denq x|)%N.
  Proof using q_prime.
    move=> H; apply/negP => Hq.
    have Hcop := coprime_num_den x.
    have Hnq : ~~ (q %| `|numq x|)%N.
    { apply/negP => Hq'.
      have : (q %| gcdn `|numq x| `|denq x|)%N by rewrite dvdn_gcd Hq Hq'.
      move: Hcop; rewrite /coprime => /eqP ->; rewrite dvdn1.
      move=> /eqP Hq1; move: q_prime; by rewrite Hq1. }
    have Hd : (0 < logn q `|denq x|)%N.
    { rewrite logn_gt0 mem_primes q_prime Hq absz_gt0 denq_neq0. done. }
    move: H; rewrite /vqr logn_ndvd // sub0r oppr_ge0 lez_nat leqn0.
    by move=> /eqP Hd0; move: Hd; rewrite Hd0.
  Qed.

  Lemma vqr_add_ge0 (x y : rat) : x != 0 -> y != 0 -> x + y != 0 ->
    0 <= v x -> 0 <= v y -> 0 <= v (x + y).
  Proof using q_prime.
    move=> Hx Hy Hxy /vqr_ge0_den Hdx /vqr_ge0_den Hdy.
    have Hdx0 := denq_neq0 x; have Hdy0 := denq_neq0 y.
    have E : x + y = (numq x * denq y + numq y * denq x)%:~R / (denq x * denq y)%:~R.
    { by rewrite intrD !intrM -addf_div ?rat_int_neq0 // !divq_num_den. }
    have HN : numq x * denq y + numq y * denq x != 0.
    { apply/eqP => H0; move: Hxy; rewrite E H0 mul0r. by rewrite eqxx. }
    rewrite E vqr_frac ?mulf_neq0 //.
    have -> : logn q `|denq x * denq y| = 0%N.
    { by rewrite logn_ndvd // abszM Euclid_dvdM // negb_or Hdx Hdy. }
    by rewrite subr0.
  Qed.

  (* the ultrametric inequality *)
  Lemma vqr_add_min (x y : rat) : x != 0 -> y != 0 -> x + y != 0 ->
    v x <= v y -> v x <= v (x + y).
  Proof using q_prime.
    move=> Hx Hy Hxy Hle.
    have -> : x + y = x * (1 + y / x) by field.
    have H1 : 1 + y / x != 0.
    { apply/eqP => H0; move: Hxy; have -> : x + y = x * (1 + y / x) by field.
      by rewrite H0 mulr0 eqxx. }
    rewrite vqrM // lerDl.
    apply: vqr_add_ge0 => //.
    - by rewrite mulf_neq0 ?invr_eq0.
    - by rewrite vqr1.
    - by rewrite vqr_div // subr_ge0.
  Qed.

  Lemma vqr_add_ge (x y : rat) (k : int) : x != 0 -> y != 0 -> x + y != 0 ->
    k <= v x -> k <= v y -> k <= v (x + y).
  Proof using q_prime.
    move=> Hx Hy Hxy Hkx Hky.
    case: (lerP (v x) (v y)) => H.
    - exact: le_trans Hkx (vqr_add_min Hx Hy Hxy H).
    - rewrite addrC; apply: le_trans Hky (vqr_add_min _ _ _ _) => //.
      + by rewrite addrC.
      + exact: ltW.
  Qed.

  (* the strict form: v (x + y) = v x if v x < v y *)
  Lemma vqr_add_lt (x y : rat) : x != 0 -> y != 0 -> v x < v y ->
    x + y != 0 /\ v (x + y) = v x.
  Proof using q_prime.
    move=> Hx Hy Hlt.
    have Hxy : x + y != 0.
    { apply/eqP => H0; move: Hlt.
      have -> : y = - x by apply/eqP; rewrite -addr_eq0 addrC H0.
      by rewrite vqrN ltxx. }
    split => //.
    apply/eqP; rewrite eq_le vqr_add_min ?(ltW Hlt) // andbT.
    have Hny : - y != 0 by rewrite oppr_eq0.
    case: (lerP (v (x + y)) (v (- y))) => H.
    - have Hs : x + y + - y != 0 by rewrite addrK.
      have := vqr_add_min Hxy Hny Hs H; by rewrite addrK.
    - have E : - y + (x + y) = x by rewrite addrC addrK.
      have Hs : - y + (x + y) != 0 by rewrite E.
      have := vqr_add_min Hny Hxy Hs (ltW H); rewrite E vqrN => Hyx.
      by move: Hlt; rewrite ltNge Hyx.
  Qed.

End RatVal.
