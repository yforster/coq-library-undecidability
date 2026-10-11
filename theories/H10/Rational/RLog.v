(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The real logarithm of natural numbers, the von Mangoldt function,
   Chebyshev's bound and a Mertens-type lower bound (PLAN.md Phase 4,
   task D2; DIRICHLET_DESIGN.md, Sec. 5). Built on the choice-free reals
   of RSeq.v. No axioms: [Print Assumptions] of the main results
   ([rlog_lrs], [vmangoldt_divisors], [psi_le], [sum_rlog_primes_lower],
   [sum_rlog_primes_unbounded]) is closed under the global context.

   Contents.
   1. Rational helpers: [ev_small] ([c / (k+1) < e] eventually),
      [sum_if_eq], [sum_if_le] (counting), [big_blocks] (splitting an
      index range into blocks of [m] consecutive indices).
   2. Riemann sums of [1/t] on [[1, n]] with step [1/k]:
      [lsum k n := sum_(k < i <= k n) 1/i] (lower), [usum k n] (upper);
      [usum_lsum], [lsum_refine], [usum_refine], [lsum_close]
      ([|lsum k n - lsum k' n| <= 1/k + 1/k']); the Riemann representative
      [lrs n := fun k => lsum k.+1 n] is Cauchy ([lrs_cauchy]); the
      additivity error [lsum_mul_err] (block comparison) and [lrs_mul].
   3. The logarithm, exactly additive by definition:
      [rlog n k := sum_(p | n) logn p n * lsum k.+1 p]; [rlog_mul]
      (pointwise), [rlog_pow], [rlog_prime], [rlog_lrs]
      ([req (rlog n) (lrs n)], via [|lsum k.+1 n - rlog n k| <= n/(k+1)]),
      [rlog_cauchy].
   4. The von Mangoldt function [vmangoldt]; the expansion lemma
      [pp_expand] (a function of prime powers as a double sum over
      [p ^ j]); [vmangoldt_divisors] ([sum_(d | n) vmangoldt d = rlog n],
      pointwise).
   5. Analytic facts, pointwise on [lrs] and transferred to [rlog]:
      [rlog_mono], [rlog_dvd], [rlog_succ_ge]/[rlog_succ_le]
      ([1/(n+1) <= log(n+1) - log n <= 1/n]), [rlog_ge_harm],
      [rlog_le_harm], [rlog2_le1], [rlog2_ge_half], [rlog_ge1],
      [rlog_pos], [rlog_le_sqrt], [rlog_le_nat], [rlog_unbounded];
      the pointwise facts [lrs_mono_pt], [lrs_div_decr]
      ([lrs n k / n] decreasing for [n >= 4]), [lrs_ge1], [lrs_le_harm_pt].
   6. Chebyshev: [theta x] and [psi x] (sums over [1 <= n <= x]);
      [prod_primes_dvd_bin], [bin_le_4pow], [theta_double], [theta_le]
      ([theta x <= 4x]), [psi_theta], [psi_le] ([psi x <= 6x]).
   7. Mertens-type bounds: [sum_rlog_lower] ([x log x - (x-1) <=
      sum_(n<=x) log n]), [sum_rlog_floor] ([sum_(n<=x) log n =
      sum_(d<=x) vmangoldt d * (x %/ d)]), [vmangoldt_div_lower]
      ([log x - 1 <= sum_(d<=x) vmangoldt d / d]), [prime_pow_tail]
      ([sum over proper prime powers <= 8]), [sum_rlog_primes_lower]
      ([log x - 9 <= sum_(p<=x) log p / p]), [sum_rlog_primes_unbounded].

   Convention: a sum over the primes [p <= x] is always written
   [rsum F [seq p <- iota 1 x | prime p]] (as in [theta]); sums over
   [1 <= n <= x] are [rsum F (iota 1 x)].

   Arguments of lemmas are implicit exactly when they occur in a
   hypothesis. *)

From Stdlib Require Import PeanoNat Setoid Morphisms Classical_Prop.
From mathcomp Require Import boot order algebra.
Import Order.TTheory GRing.Theory Num.Theory.
From Undecidability.H10.Rational Require Import RSeq.

Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(** * 1. Rational helpers *)

Lemma inv_le {a b : nat} : (0 < a)%N -> (a <= b)%N -> 1 / b%:R <= 1 / a%:R :> rat.
Proof.
move=> ha hab; have hb : (0 < b)%N := leq_trans ha hab.
by rewrite !div1r lef_pV2 ?posrE ?ltr0n ?ler_nat.
Qed.

Lemma inv_ge0 (a : nat) : 0 <= 1 / a%:R :> rat.
Proof. by rewrite div1r invr_ge0 ler0n. Qed.

Lemma inv_gt0 {a : nat} : (0 < a)%N -> 0 < 1 / a%:R :> rat.
Proof. by move=> ha; rewrite div1r invr_gt0 ltr0n. Qed.

Lemma ev_small (c : rat) {e : rat} : 0 < e -> ev (fun k => c / k.+1%:R < e).
Proof.
move=> he; have hb := archi_boundP (normr_ge0 (c / e)).
exists (Num.bound `|c / e|) => k hk.
have hk1 : 0 < k.+1%:R :> rat by rewrite ltr0n.
rewrite ltr_pdivrMr //.
have h : c / e < k.+1%:R.
  apply: le_lt_trans (ler_norm _) _; apply: lt_le_trans hb _.
  by rewrite ler_nat; apply: leq_trans hk _.
have : c / e * e < k.+1%:R * e by rewrite ltr_pM2r.
rewrite divfK ?gt_eqF //; lra.
Qed.

Lemma sumr_const_blk (m j : nat) (c : rat) :
  \sum_(m * j <= i < m * j.+1) c = c * m%:R.
Proof. by rewrite sumr_const_nat mulnS addnK mulr_natr. Qed.

(** Sums of indicator-weighted constants. *)
Lemma sum_if_eq {r : seq nat} (x : nat) (c : rat) : uniq r ->
  \sum_(i <- r) (if i == x then c else 0) = if x \in r then c else 0.
Proof.
elim: r => [|a r IH] /=; first by rewrite big_nil.
case/andP => har hu; rewrite big_cons IH // in_cons.
case: (eqVneq a x) => [<-|hax] /=; last by rewrite add0r.
by rewrite (negbTE har) addr0.
Qed.

Lemma sum_if_le {r : seq nat} (s : nat) {c : rat} : uniq r -> all (fun p => 0 < p)%N r ->
  0 <= c -> \sum_(p <- r) (if (p <= s)%N then c else 0) <= s%:R * c.
Proof.
move=> hu hpos hc.
have -> : \sum_(p <- r) (if (p <= s)%N then c else 0) = c *+ count (fun p => p <= s)%N r.
  elim: r {hu hpos} => [|a r IH]; first by rewrite big_nil.
  by rewrite big_cons IH /=; case: (a <= s)%N; rewrite ?add1n ?mulrS ?add0n ?add0r.
rewrite -mulr_natl ler_wpM2r // ler_nat -size_filter.
apply: leq_trans (uniq_leq_size (s2 := iota 1 s) _ _) _.
- exact: filter_uniq.
- move=> p; rewrite mem_filter mem_iota add1n ltnS => /andP [hps hp].
  by rewrite hps andbT; move/allP: hpos => /(_ p hp).
- by rewrite size_iota.
Qed.

(** Splitting a range into blocks of [m] consecutive indices. *)
Lemma big_blocks (F : nat -> rat) (m : nat) {a b : nat} : (a <= b)%N ->
  \sum_(m * a <= i < m * b) F i = \sum_(a <= j < b) \sum_(m * j <= i < m * j.+1) F i.
Proof.
elim: b => [|b IH] hab.
  by move: hab; rewrite leqn0 => /eqP ->; rewrite !big_geq.
move: hab; rewrite leq_eqVlt => /orP [/eqP <-|hab]; first by rewrite !big_geq.
rewrite big_nat_recr //= -IH // (big_cat_nat (n := m * b)) //.
- by rewrite leq_mul2l -ltnS hab orbT.
- by rewrite leq_mul2l leqnSn orbT.
Qed.

(* ------------------------------------------------------------------ *)
(** * 2. Riemann sums of [1/t] *)

Definition lsum (k n : nat) : rat := \sum_(k.+1 <= i < (k * n).+1) 1 / i%:R.
Definition usum (k n : nat) : rat := \sum_(k <= i < k * n) 1 / i%:R.
Definition harm (n : nat) : rat := \sum_(1 <= i < n.+1) 1 / i%:R.

Lemma lsum_shift (k n : nat) : lsum k n = \sum_(k <= j < k * n) 1 / j.+1%:R.
Proof. by rewrite /lsum big_add1. Qed.

Lemma lsum0 (k : nat) : lsum k 0 = 0.
Proof. by rewrite lsum_shift muln0 big_geq. Qed.

Lemma lsum1 (k : nat) : lsum k 1 = 0.
Proof. by rewrite lsum_shift muln1 big_geq. Qed.

Lemma lsum_ge0 (k n : nat) : 0 <= lsum k n.
Proof. by apply: sumr_ge0 => i _; apply: inv_ge0. Qed.

Lemma usum_lsum {k n : nat} : (0 < k)%N -> (0 < n)%N ->
  usum k n - lsum k n = 1 / k%:R - 1 / (k * n)%:R.
Proof.
move=> hk hn; have hkn : (k <= k * n)%N by rewrite leq_pmulr.
have h1 : \sum_(k <= i < (k * n).+1) 1 / i%:R = usum k n + 1 / (k * n)%:R :> rat.
  by rewrite big_nat_recr.
have h2 : \sum_(k <= i < (k * n).+1) 1 / i%:R = 1 / k%:R + lsum k n :> rat.
  by rewrite big_ltn // ltnS.
lra.
Qed.

Lemma lsum_le_usum {k n : nat} : (0 < k)%N -> (0 < n)%N -> lsum k n <= usum k n.
Proof.
move=> hk hn; have := usum_lsum hk hn.
have := inv_le hk (leq_pmulr k hn); lra.
Qed.

Lemma usum_le {k n : nat} : (0 < k)%N -> (0 < n)%N -> usum k n <= lsum k n + 1 / k%:R.
Proof.
move=> hk hn; have := usum_lsum hk hn.
have := inv_ge0 (k * n); lra.
Qed.

(** The two block shapes. *)
Definition blkL (m j : nat) : rat := \sum_(m * j <= i < m * j.+1) 1 / i.+1%:R.
Definition blkU (m j : nat) : rat := \sum_(m * j <= i < m * j.+1) 1 / i%:R.

Lemma blkL_ge {m : nat} (j : nat) : (0 < m)%N -> 1 / j.+1%:R <= blkL m j.
Proof.
move=> hm.
have -> : 1 / j.+1%:R = \sum_(m * j <= i < m * j.+1) 1 / (m * j.+1)%:R :> rat.
  rewrite sumr_const_blk natrM.
  have hm0 : m%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n.
  have hJ : 1 + j%:R != 0 :> rat by rewrite addrC natr1 pnatr_eq0.
  by field.
apply: ler_sum_nat => i /andP [_ hi]; apply: inv_le => //.
Qed.

Lemma blkU_le {m j : nat} : (0 < m)%N -> (0 < j)%N -> blkU m j <= 1 / j%:R.
Proof.
move=> hm hj.
have -> : 1 / j%:R = \sum_(m * j <= i < m * j.+1) 1 / (m * j)%:R :> rat.
  rewrite sumr_const_blk natrM.
  have hm0 : m%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n.
  have hj0 : j%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n.
  by field.
apply: ler_sum_nat => i /andP [hi _]; apply: inv_le => //.
by rewrite muln_gt0 hm.
Qed.

Lemma blkL_le {m j : nat} : (0 < m)%N -> (0 < j)%N -> blkL m j <= 1 / j%:R.
Proof.
move=> hm hj; apply: le_trans (blkU_le hm hj); apply: ler_sum_nat => i /andP [hi _].
apply: inv_le => //; apply: leq_trans hi; by rewrite muln_gt0 hm.
Qed.

Lemma lsum_blocks (k m : nat) {n : nat} : (0 < n)%N ->
  lsum (k * m) n = \sum_(k <= j < k * n) blkL m j.
Proof.
move=> hn; rewrite lsum_shift [(k * m)%N]mulnC -mulnA big_blocks //.
by rewrite leq_pmulr.
Qed.

Lemma usum_blocks (k m : nat) {n : nat} : (0 < n)%N ->
  usum (k * m) n = \sum_(k <= j < k * n) blkU m j.
Proof.
move=> hn; rewrite /usum [(k * m)%N]mulnC -mulnA big_blocks //.
by rewrite leq_pmulr.
Qed.

Lemma blocks_bounds {k m : nat} (n : nat) : (0 < k)%N -> (0 < m)%N ->
  lsum k n <= \sum_(k <= j < k * n) blkL m j <= usum k n.
Proof.
move=> hk hm; apply/andP; split.
- rewrite lsum_shift; apply: ler_sum_nat => j _; exact: blkL_ge.
- apply: ler_sum_nat => j /andP [hj _]; apply: blkL_le => //.
  exact: leq_trans hk hj.
Qed.

Lemma lsum_refine {k m : nat} (n : nat) : (0 < k)%N -> (0 < m)%N -> lsum k n <= lsum (k * m) n.
Proof.
move=> hk hm; case: n => [|n]; first by rewrite !lsum0.
by rewrite lsum_blocks //; case/andP: (blocks_bounds n.+1 hk hm).
Qed.

Lemma lsum_refine_le {k m : nat} (n : nat) : (0 < k)%N -> (0 < m)%N -> lsum (k * m) n <= usum k n.
Proof.
move=> hk hm; case: n => [|n]; first by rewrite lsum0 /usum muln0 big_geq.
by rewrite lsum_blocks //; case/andP: (blocks_bounds n.+1 hk hm).
Qed.

Lemma usum_refine {k m : nat} (n : nat) : (0 < k)%N -> (0 < m)%N -> usum (k * m) n <= usum k n.
Proof.
move=> hk hm; case: n => [|n]; first by rewrite /usum !muln0 !big_geq.
rewrite usum_blocks //; apply: ler_sum_nat => j /andP [hj _]; apply: blkU_le => //.
exact: leq_trans hk hj.
Qed.

Lemma lsum_close {k k' : nat} (n : nat) : (0 < k)%N -> (0 < k')%N ->
  `|lsum k n - lsum k' n| <= 1 / k%:R + 1 / k'%:R.
Proof.
move=> hk hk'; case: n => [|n]; first by rewrite !lsum0 subrr normr0 addr_ge0 ?inv_ge0.
have h1 := lsum_refine n.+1 hk hk'; have h2 := lsum_refine_le n.+1 hk hk'.
have h3 := lsum_refine n.+1 hk' hk; have h4 := lsum_refine_le n.+1 hk' hk.
have h5 := usum_le hk (ltn0Sn n); have h6 := usum_le hk' (ltn0Sn n).
have h7 := inv_ge0 k; have h8 := inv_ge0 k'.
rewrite mulnC in h3 h4; nlra.
Qed.

Definition lrs (n : nat) : rseq := fun k => lsum k.+1 n.

Lemma lrs_cauchy (n : nat) : cauchy (lrs n).
Proof.
move=> e he; have he2 : 0 < e / 2 by lra.
have [N hN] := ev_small 1 he2; exists N => i j hi hj.
apply: le_lt_trans (lsum_close n (ltn0Sn i) (ltn0Sn j)) _.
have h1 : 1 / i.+1%:R < e / 2 := hN i hi.
have h2 : 1 / j.+1%:R < e / 2 := hN j hj.
move: h1 h2; set a := 1 / i.+1%:R; set b := 1 / j.+1%:R; lra.
Qed.

Lemma lrs_ge0 (n : nat) : forall k, 0 <= lrs n k.
Proof. by move=> k; apply: lsum_ge0. Qed.

(** Additivity error (block comparison). *)
Lemma lsum_mul_err {k p q : nat} : (0 < k)%N -> (0 < p)%N -> (0 < q)%N ->
  lsum k p + lsum k q <= lsum k (p * q) <= lsum k p + lsum k q + 1 / k%:R.
Proof.
move=> hk hp hq.
have hsplit : lsum k (p * q) = lsum k p + \sum_(k <= j < k * q) blkL p j.
  have h1 : (k <= k * p)%N by rewrite leq_pmulr.
  have h2 : (k * p <= k * (p * q))%N by rewrite leq_pmul2l // leq_pmulr.
  rewrite !lsum_shift (big_cat_nat h1 h2) /=; congr (_ + _).
  by rewrite [(k * p)%N]mulnC mulnCA big_blocks // leq_pmulr.
have := blocks_bounds q hk hp; have := usum_le hk hq.
rewrite hsplit => h1 /andP [h2 h3]; apply/andP; split; lra.
Qed.

(* ------------------------------------------------------------------ *)
(** * 3. The real logarithm, exactly additive *)

Definition rlog (n : nat) : rseq :=
  fun k => \sum_(p <- primes n) (logn p n)%:R * lsum k.+1 p.

Lemma rlog_range (n : nat) {N : nat} : (n < N)%N -> forall k,
  rlog n k = \sum_(0 <= p < N) (logn p n)%:R * lsum k.+1 p.
Proof.
move=> hN k.
have -> : \sum_(0 <= p < N) (logn p n)%:R * lsum k.+1 p =
          \sum_(0 <= p < N | p \in primes n) (logn p n)%:R * lsum k.+1 p.
  rewrite [in RHS]big_mkcond; apply: eq_bigr => p _; case: ifP => // hp.
  by move/negbT: hp; rewrite -logn_gt0 lt0n negbK => /eqP ->; rewrite mul0r.
rewrite -big_filter /rlog; apply: perm_big; apply: uniq_perm.
- exact: primes_uniq.
- by apply: filter_uniq; apply: iota_uniq.
- move=> p; rewrite mem_filter mem_index_iota /=.
  case hp: (p \in primes n) => //=; symmetry; move: hp; rewrite mem_primes => /and3P [_ hn hpn].
  by apply: leq_ltn_trans hN; apply: dvdn_leq.
Qed.

Lemma rlog_mul {m n : nat} : (0 < m)%N -> (0 < n)%N -> forall k,
  rlog (m * n) k = rlog m k + rlog n k.
Proof.
move=> hm hn k; have hN : forall a, (a <= m * n)%N -> (a < (m * n).+1)%N by [].
rewrite !(rlog_range _ (N := (m * n).+1)) ?hN ?leq_pmulr ?leq_pmull //.
by rewrite -big_split; apply: eq_bigr => p _; rewrite lognM // natrD mulrDl.
Qed.

Lemma rlog_pow (m j : nat) : forall k, rlog (m ^ j) k = j%:R * rlog m k.
Proof.
move=> k; rewrite !(rlog_range _ (N := (m ^ j + m).+1)) ?ltnS ?leq_addr ?leq_addl //.
by rewrite mulr_sumr; apply: eq_bigr => p _; rewrite lognX natrM mulrA.
Qed.

Lemma rlog1 : forall k, rlog 1 k = 0.
Proof. by move=> k; have := rlog_pow 2 0 k; rewrite expn0 mul0r. Qed.

Lemma rlog0 : forall k, rlog 0 k = 0.
Proof. by move=> k; rewrite (rlog_range _ (N := 1)) // big_nat1 logn0 mul0r. Qed.

Lemma rlog_prime_pow {p : nat} (j : nat) : prime p -> forall k, rlog (p ^ j) k = j%:R * rlog p k.
Proof. by move=> _; apply: rlog_pow. Qed.

Lemma rlog_pow2 (j : nat) : forall k, rlog (2 ^ j) k = j%:R * rlog 2 k.
Proof. exact: rlog_pow. Qed.

Lemma rlog_prime {p : nat} : prime p -> forall k, rlog p k = lsum k.+1 p.
Proof. by move=> hp k; rewrite /rlog primes_prime // big_seq1 logn_prime // eqxx mul1r. Qed.

Lemma rlog_ge0_pt (n : nat) : forall k, 0 <= rlog n k.
Proof. by move=> k; apply: sumr_ge0 => p _; apply: mulr_ge0; [apply: ler0n | apply: lsum_ge0]. Qed.

Lemma rlog_ge0 (n : nat) : rle (cst 0) (rlog n).
Proof. exact: rle_of_ptwise (rlog_ge0_pt n). Qed.

Lemma rlog_lrs_err {n : nat} : (0 < n)%N -> forall k,
  `|lsum k.+1 n - rlog n k| <= n%:R / k.+1%:R.
Proof.
elim/ltn_ind: n => n IH hn k.
have hK : 0 < k.+1%:R :> rat by rewrite ltr0n.
case: n IH hn => [//|[|n]] IH hn.
  by rewrite lsum1 rlog1 subrr normr0 divr_ge0 // ler0n.
set n' := n.+2; set p := pdiv n'; set m := (n' %/ p)%N.
have hp : prime p by apply: pdiv_prime.
have hnm : n' = (p * m)%N by rewrite mulnC divnK // pdiv_dvd.
have hm0 : (0 < m)%N by rewrite divn_gt0 ?prime_gt0 // dvdn_leq // pdiv_dvd.
have hmn : (m < n')%N by apply: ltn_Pdiv; [apply: prime_gt1 | ].
have hIH := IH m hmn hm0 k.
have hr : rlog n' k = lsum k.+1 p + rlog m k by rewrite hnm (rlog_mul (prime_gt0 hp) hm0) (rlog_prime hp).
have := lsum_mul_err (k := k.+1) (ltn0Sn k) (prime_gt0 hp) hm0.
rewrite -hnm => /andP [h1 h2].
have hm1 : (m + 1 <= n')%N by rewrite addn1.
have h3 : (m%:R + 1) / k.+1%:R <= n'%:R / k.+1%:R :> rat.
  by apply: ler_wpM2r; [rewrite invr_ge0 ler0n | rewrite natr1 ler_nat].
have h4 : (m%:R + 1) / k.+1%:R = m%:R / k.+1%:R + 1 / k.+1%:R :> rat by rewrite mulrDl.
rewrite hr; move: hIH h1 h2 h3 h4.
set a := lsum k.+1 n'; set b := lsum k.+1 p; set c := lsum k.+1 m; set r := rlog m k.
set u := m%:R / k.+1%:R; set v := 1 / k.+1%:R; set w := n'%:R / k.+1%:R.
set z := (m%:R + 1) / k.+1%:R.
move=> *; nlra.
Qed.

Lemma rlog_lrs {n : nat} : (0 < n)%N -> req (rlog n) (lrs n).
Proof.
move=> hn e he; apply: ev_mono (ev_small n%:R he) => k hk.
rewrite distrC; exact: le_lt_trans (rlog_lrs_err hn k) hk.
Qed.

Lemma lrs_mul {m n : nat} : (0 < m)%N -> (0 < n)%N -> req (lrs (m * n)) (radd (lrs m) (lrs n)).
Proof.
move=> hm hn e he; apply: ev_mono (ev_small 1 he) => k hk.
have := lsum_mul_err (k := k.+1) (ltn0Sn k) hm hn; rewrite /lrs /radd.
move: hk; set v := 1 / k.+1%:R; move=> hk /andP [h1 h2]; nlra.
Qed.

Lemma rlog_cauchy (n : nat) : cauchy (rlog n).
Proof.
case: n => [|n]; first by apply: cauchy_ext (cauchy_cst 0) => k; rewrite rlog0.
exact: req_cauchy (req_sym (rlog_lrs (ltn0Sn n))) (lrs_cauchy _).
Qed.

(* ------------------------------------------------------------------ *)
(** * 4. The von Mangoldt function *)

Definition vmangoldt (n : nat) : rseq :=
  if (1 < n)%N && (n == pdiv n ^ logn (pdiv n) n)%N then rlog (pdiv n) else cst 0.

Lemma vmangoldtE (n : nat) : forall k, vmangoldt n k =
  if (1 < n)%N && (n == pdiv n ^ logn (pdiv n) n)%N then rlog (pdiv n) k else 0.
Proof. by move=> k; rewrite /vmangoldt; case: ifP. Qed.

Lemma prime_pow_gt1 {p j : nat} : prime p -> (0 < j)%N -> (1 < p ^ j)%N.
Proof.
move=> hp hj; apply: leq_trans (prime_gt1 hp) _.
by rewrite -{1}(expn1 p) leq_pexp2l // prime_gt0.
Qed.

Lemma prime_pow_ge {p j : nat} : prime p -> (0 < j)%N -> (p <= p ^ j)%N.
Proof. by move=> hp hj; rewrite -{1}(expn1 p) leq_pexp2l // prime_gt0. Qed.

(** Expansion of a function of prime powers as a double sum over [p ^ j]. *)
Lemma pp_expand (n : nat) (c : nat -> nat -> rat) {P : seq nat} {J : nat -> seq nat} :
  uniq P -> all prime P -> (forall p, uniq (J p)) -> (forall p j, j \in J p -> (0 < j)%N) ->
  (forall p j, prime p -> (0 < j)%N -> n = (p ^ j)%N -> p \in P /\ j \in J p) ->
  (if (1 < n)%N && (n == pdiv n ^ logn (pdiv n) n)%N then c (pdiv n) (logn (pdiv n) n) else 0)
  = \sum_(p <- P) \sum_(j <- J p) (if n == (p ^ j)%N then c p j else 0).
Proof.
move=> hP hPp hJ hJ0 hcov.
case: ifP => [/andP [hn1 /eqP hn] | hnot].
- set q := pdiv n in hn *; set i := logn q n in hn *.
  have hq : prime q by apply: pdiv_prime.
  have hi : (0 < i)%N by rewrite logn_gt0 mem_primes hq (ltnW hn1) pdiv_dvd.
  have [hqP hiJ] := hcov q i hq hi hn.
  have hrest : \sum_(p <- P | p != q) \sum_(j <- J p) (if n == (p ^ j)%N then c p j else 0) = 0.
    apply: big1_seq => p /andP [hpq hpP]; apply: big1_seq => j /andP [_ hj].
    case: eqP => // hnp; exfalso; move/negP: hpq; apply.
    have hpp : prime p by move/allP: hPp => /(_ p hpP).
    have hj0 := hJ0 _ _ hj.
    by rewrite /q hnp -(prednK hj0) pdiv_pfactor.
  rewrite (bigD1_seq q) //= hrest addr0.
  rewrite (bigD1_seq i) //= -hn eqxx big1_seq ?addr0 //.
  move=> j /andP [hji hj]; case: eqP => // hnj; exfalso; move/negP: hji; apply.
  by rewrite -(eqn_exp2l _ _ (prime_gt1 hq)) -hnj -hn.
- symmetry; apply: big1_seq => p /andP [_ hp]; apply: big1_seq => j /andP [_ hj].
  case: eqP => // hnp; exfalso; move: hnot.
  have hpp : prime p by move/allP: hPp => /(_ p hp).
  have hj0 := hJ0 _ _ hj.
  rewrite hnp prime_pow_gt1 //= -(prednK hj0) pdiv_pfactor // pfactorK //.
  by rewrite eqxx.
Qed.

Lemma vmangoldt_ge0 (n : nat) : forall k, 0 <= vmangoldt n k.
Proof. by move=> k; rewrite vmangoldtE; case: ifP => _ //; apply: rlog_ge0_pt. Qed.

Lemma vmangoldt_cauchy (n : nat) : cauchy (vmangoldt n).
Proof. by rewrite /vmangoldt; case: ifP => _; [apply: rlog_cauchy | apply: cauchy_cst]. Qed.

Lemma vmangoldt_prime_pow {p j : nat} : prime p -> (0 < j)%N -> forall k,
  vmangoldt (p ^ j) k = rlog p k.
Proof.
move=> hp hj k; rewrite vmangoldtE prime_pow_gt1 //= -(prednK hj) pdiv_pfactor //.
by rewrite pfactorK // eqxx.
Qed.

Lemma vmangoldt_prime {p : nat} : prime p -> forall k, vmangoldt p k = rlog p k.
Proof. by move=> hp k; have := vmangoldt_prime_pow hp (ltn0Sn 0) k; rewrite expn1. Qed.

Lemma vmangoldt_not_pp {n : nat} : (forall p j, prime p -> n != (p ^ j)%N) ->
  forall k, vmangoldt n k = 0.
Proof.
move=> h k; rewrite vmangoldtE; case: ifP => // /andP [hn1 /eqP hn].
by move: (h _ (logn (pdiv n) n) (pdiv_prime hn1)); rewrite -hn eqxx.
Qed.

Lemma vmangoldt_le1 {n : nat} : (n <= 1)%N -> forall k, vmangoldt n k = 0.
Proof. by move=> hn k; rewrite vmangoldtE ltnNge hn. Qed.

Lemma vmangoldt_divisors {n : nat} : (0 < n)%N -> forall k,
  \sum_(d <- divisors n) vmangoldt d k = rlog n k.
Proof.
move=> hn k.
have hexp : forall d, d \in divisors n -> vmangoldt d k =
    \sum_(p <- primes n) \sum_(j <- index_iota 1 (logn p n).+1)
       (if d == (p ^ j)%N then rlog p k else 0).
  move=> d hd; rewrite vmangoldtE; apply: (pp_expand d (fun p _ => rlog p k)
    (P := primes n) (J := fun p => index_iota 1 (logn p n).+1)).
  + exact: primes_uniq.
  + by apply/allP => p; rewrite mem_primes => /andP [].
  + by move=> p; apply: iota_uniq.
  + by move=> p j; rewrite mem_index_iota => /andP [].
  + move=> p j hp hj hdp; rewrite -dvdn_divisors // in hd.
    rewrite mem_primes hp hn mem_index_iota hj ltnS -pfactor_dvdn //=.
    by split; apply: dvdn_trans hd; rewrite hdp // dvdn_exp.
rewrite (eq_big_seq _ hexp) exchange_big /=.
rewrite /rlog; apply: eq_big_seq => p hp.
have hpp : prime p by move: hp; rewrite mem_primes => /andP [].
rewrite exchange_big /=.
have hin : forall j, j \in index_iota 1 (logn p n).+1 ->
    \sum_(d <- divisors n) (if d == (p ^ j)%N then rlog p k else 0) = rlog p k.
  move=> j; rewrite mem_index_iota ltnS => /andP [hj1 hj2].
  by rewrite sum_if_eq ?divisors_uniq // -dvdn_divisors // pfactor_dvdn // hj2.
rewrite (eq_big_seq _ hin) sumr_const_nat subn1 /= rlog_prime //.
by rewrite mulr_natl.
Qed.

(* ------------------------------------------------------------------ *)
(** * 5. Analytic facts *)

Lemma harm0 : harm 0 = 0.
Proof. by rewrite /harm big_geq. Qed.

Lemma harm_succ (n : nat) : harm n.+1 = harm n + 1 / n.+1%:R.
Proof. by rewrite /harm big_nat_recr. Qed.

Lemma harm1 : harm 1 = 1.
Proof. by rewrite harm_succ harm0 add0r divr1. Qed.

Lemma harm2 : harm 2 = 3 / 2.
Proof. by rewrite harm_succ harm1; apply/eqP; rewrite -subr_eq0; apply/eqP; field. Qed.

Lemma harm4 : harm 4 = 25 / 12.
Proof.
rewrite !harm_succ harm0 add0r divr1.
have h3 : (3%:R : rat) = 3 by []. have h4 : (4%:R : rat) = 4 by [].
have h2 : (2%:R : rat) = 2 by [].
by rewrite h2 h3 h4; field.
Qed.

Lemma harm_ge0 (n : nat) : 0 <= harm n.
Proof. by apply: sumr_ge0 => i _; apply: inv_ge0. Qed.

Lemma harm_le_nat (n : nat) : harm n <= n%:R.
Proof.
elim: n => [|n IH]; first by rewrite harm0.
have h : 1 / n.+1%:R <= (1 : rat) by rewrite ler_pdivrMr ?ltr0n // mul1r ler1n.
rewrite harm_succ; move: h; set u := 1 / n.+1%:R => h; rewrite -natr1; lra.
Qed.

Lemma lsum_mono_pt (k : nat) {m n : nat} : (m <= n)%N -> lsum k m <= lsum k n.
Proof.
case: m => [|m] hmn; first by rewrite lsum0 lsum_ge0.
case: k => [|k]; first by rewrite /lsum !mul0n !big_geq.
have h1 : (k.+1 <= k.+1 * m.+1)%N by rewrite leq_pmulr.
have h2 : (k.+1 * m.+1 <= k.+1 * n)%N by rewrite leq_pmul2l.
rewrite [X in _ <= X]lsum_shift (big_cat_nat h1 h2) /= -lsum_shift.
by rewrite lerDl; apply: sumr_ge0 => i _; apply: inv_ge0.
Qed.

Lemma lsum_succ {k n : nat} : (0 < k)%N -> (0 < n)%N -> lsum k n.+1 = lsum k n + blkL k n.
Proof.
move=> hk hn.
have h1 : (k <= k * n)%N by rewrite leq_pmulr.
have h2 : (k * n <= k * n.+1)%N by rewrite leq_pmul2l.
by rewrite [LHS]lsum_shift (big_cat_nat h1 h2) /= -lsum_shift.
Qed.

Lemma lsum_succ_bounds {k n : nat} : (0 < k)%N -> (0 < n)%N ->
  1 / n.+1%:R <= lsum k n.+1 - lsum k n <= 1 / n%:R.
Proof.
move=> hk hn; rewrite lsum_succ // [lsum k n + _]addrC addrK.
by rewrite blkL_ge // blkL_le.
Qed.

Lemma lsum_harm {k n : nat} : (0 < k)%N -> (0 < n)%N ->
  harm n - 1 <= lsum k n <= harm n - 1 / n%:R.
Proof.
move=> hk; elim: n => [//|n IH] _.
case: n IH => [|n] IH; first by rewrite lsum1 harm1 divr1 subrr lexx.
have /andP [h1 h2] := IH (ltn0Sn n).
have /andP [h3 h4] := lsum_succ_bounds hk (ltn0Sn n).
rewrite harm_succ; move: h1 h2 h3 h4.
set a := lsum k n.+2; set b := lsum k n.+1; set u := 1 / n.+2%:R; set v := 1 / n.+1%:R.
move=> h1 h2 h3 h4; apply/andP; split; lra.
Qed.

Lemma lrs_mono_pt {m n : nat} : (0 < m)%N -> (m <= n)%N -> forall k, lrs m k <= lrs n k.
Proof. by move=> _ hmn k; apply: lsum_mono_pt. Qed.

Lemma lrs_le_harm_pt (n : nat) : forall k, lrs n k <= harm n.
Proof.
move=> k; case: n => [|n]; first by rewrite /lrs lsum0 harm0.
have /andP [_ h] := lsum_harm (ltn0Sn k) (ltn0Sn n).
by apply: le_trans h _; rewrite lerBlDr lerDl inv_ge0.
Qed.

Lemma lrs_ge1 {n : nat} : (4 <= n)%N -> forall k, 1 <= lrs n k.
Proof.
move=> hn k; apply: le_trans (lsum_mono_pt k.+1 hn).
have /andP [h _] := lsum_harm (k := k.+1) (n := 4) (ltn0Sn k) isT.
by apply: le_trans h; rewrite harm4 lerBrDr; lra.
Qed.

Lemma lrs_ge_half {n : nat} : (2 <= n)%N -> forall k, 1 / 2 <= lrs n k.
Proof.
move=> hn k; apply: le_trans (lsum_mono_pt k.+1 hn).
have /andP [h _] := lsum_harm (k := k.+1) (n := 2) (ltn0Sn k) isT.
by apply: le_trans h; rewrite harm2; lra.
Qed.

Lemma lrs_div_decr {n : nat} : (4 <= n)%N -> forall k, lrs n.+1 k / n.+1%:R <= lrs n k / n%:R.
Proof.
move=> hn k; have hn0 : (0 < n)%N by apply: leq_trans hn.
have hN : 0 < n%:R :> rat by rewrite ltr0n.
have hN1 : 0 < n.+1%:R :> rat by rewrite ltr0n.
have /andP [_ h2] := lsum_succ_bounds (ltn0Sn k) hn0.
have h1 := lrs_ge1 hn k; rewrite /lrs in h1 *.
rewrite ler_pdivrMr // mulrAC ler_pdivlMr //.
have : n%:R * (lsum k.+1 n.+1 - lsum k.+1 n) <= n%:R * (1 / n%:R).
  by rewrite ler_wpM2l // ltW.
rewrite mulrA mulr1 divff ?gt_eqF // -natr1.
move: h1; set a := lsum k.+1 n.+1; set b := lsum k.+1 n; set N := n%:R => h1.
move=> h; have : N * a <= N * b + 1 by lra.
move=> h'; rewrite mulrDr mulr1 [a * N]mulrC [b * N]mulrC; lra.
Qed.

(** Transfer of pointwise facts on the Riemann representative. *)
Lemma rlog_lrs_rle {n : nat} {f : rseq} : (0 < n)%N -> (forall k, f k <= lrs n k) -> rle f (rlog n).
Proof. by move=> hn h; apply: rle_req_trans (rle_of_ptwise h) (req_sym (rlog_lrs hn)). Qed.

Lemma rlog_lrs_rle' {n : nat} {f : rseq} : (0 < n)%N -> (forall k, lrs n k <= f k) -> rle (rlog n) f.
Proof. by move=> hn h; apply: req_rle_trans (rlog_lrs hn) (rle_of_ptwise h). Qed.

Lemma rlog_mono {m n : nat} : (0 < m)%N -> (m <= n)%N -> rle (rlog m) (rlog n).
Proof.
move=> hm hmn; have hn := leq_trans hm hmn.
apply: req_rle_trans (rlog_lrs hm) _; apply: rlog_lrs_rle hn _ => k.
exact: lrs_mono_pt.
Qed.

Lemma rlog_dvd_pt {m n : nat} : (0 < n)%N -> (m %| n)%N -> forall k, rlog m k <= rlog n k.
Proof.
move=> hn hmn k; have hm := dvdn_gt0 hn hmn.
have hq : (0 < n %/ m)%N by rewrite divn_gt0 // dvdn_leq.
by rewrite -(divnK hmn) mulnC rlog_mul // lerDl rlog_ge0_pt.
Qed.

Lemma rlog_dvd {m n : nat} : (0 < n)%N -> (m %| n)%N -> rle (rlog m) (rlog n).
Proof. by move=> hn hmn; apply: rle_of_ptwise; apply: rlog_dvd_pt. Qed.

Lemma rlog_succ_ge {n : nat} : (0 < n)%N -> rle (cst (1 / n.+1%:R)) (rsub (rlog n.+1) (rlog n)).
Proof.
move=> hn; apply: rle_req_trans _ (req_sym (req_rsub (rlog_lrs (ltn0Sn n)) (rlog_lrs hn))).
by apply: rle_of_ptwise => k; case/andP: (lsum_succ_bounds (ltn0Sn k) hn).
Qed.

Lemma rlog_succ_le {n : nat} : (0 < n)%N -> rle (rsub (rlog n.+1) (rlog n)) (cst (1 / n%:R)).
Proof.
move=> hn; apply: req_rle_trans (req_rsub (rlog_lrs (ltn0Sn n)) (rlog_lrs hn)) _.
by apply: rle_of_ptwise => k; case/andP: (lsum_succ_bounds (ltn0Sn k) hn).
Qed.

Lemma rlog_ge_harm {n : nat} : (0 < n)%N -> rle (cst (harm n - 1)) (rlog n).
Proof. by move=> hn; apply: (rlog_lrs_rle hn) => k; case/andP: (lsum_harm (ltn0Sn k) hn). Qed.

Lemma rlog_le_harm {n : nat} : (0 < n)%N -> rle (rlog n) (cst (harm n - 1 / n%:R)).
Proof. by move=> hn; apply: (rlog_lrs_rle' hn) => k; case/andP: (lsum_harm (ltn0Sn k) hn). Qed.

Lemma rlog2_le1_pt : forall k, rlog 2 k <= 1.
Proof.
move=> k; rewrite rlog_prime //; case/andP: (lsum_harm (k := k.+1) (n := 2) (ltn0Sn k) isT) => _.
by rewrite harm2 => h; apply: le_trans h _; lra.
Qed.

Lemma rlog2_ge_half_pt : forall k, 1 / 2 <= rlog 2 k.
Proof. by move=> k; rewrite rlog_prime //; apply: lrs_ge_half. Qed.

Lemma rlog2_le1 : rle (rlog 2) (cst 1).
Proof. exact: rle_of_ptwise rlog2_le1_pt. Qed.

Lemma rlog2_ge_half : rle (cst (1 / 2)) (rlog 2).
Proof. exact: rle_of_ptwise rlog2_ge_half_pt. Qed.

Lemma rlog_ge1 {n : nat} : (4 <= n)%N -> rle (cst 1) (rlog n).
Proof.
move=> hn; have hn0 : (0 < n)%N by apply: leq_trans hn.
by apply: (rlog_lrs_rle hn0) => k; apply: lrs_ge1.
Qed.

Lemma rlog_ge_half {n : nat} : (1 < n)%N -> rle (cst (1 / 2)) (rlog n).
Proof. by move=> hn; apply: (rlog_lrs_rle (ltnW hn)) => k; apply: lrs_ge_half. Qed.

Lemma rlog_pos {n : nat} : (1 < n)%N -> rlt (cst 0) (rlog n).
Proof.
move=> hn; apply: rlt_rle_trans (rlog_ge_half hn).
by apply/rlt_cst; lra.
Qed.

Lemma rlog_le_harmn (n : nat) : rle (rlog n) (cst (harm n)).
Proof.
case: n => [|n]; first by apply: rle_of_ptwise => k; rewrite rlog0 harm0.
by apply: (rlog_lrs_rle' (ltn0Sn n)) => k; apply: lrs_le_harm_pt.
Qed.

Lemma rlog_le_sqrt (n : nat) : rle (rlog n) (rmul (cst 2) (rsqrt n)).
Proof. exact: rle_trans (rlog_le_harmn n) (harm_le_sqrt n). Qed.

Lemma rlog_le_nat (n : nat) : rle (rlog n) (cst n%:R).
Proof. by apply: rle_trans (rlog_le_harmn n) _; apply/rle_cst; apply: harm_le_nat. Qed.

Lemma rlog_unbounded (C : rat) : exists n, rlt (cst C) (rlog n).
Proof.
have hb := archi_boundP (normr_ge0 C); set B := Num.bound `|C| in hb.
exists (2 ^ (2 * B.+1))%N; apply: (rlt_of_eventually (e := 1)) => //.
exists 0%N => k _; rewrite /cst rlog_pow2.
have h := rlog2_ge_half_pt k.
have hC : C <= B%:R by apply: le_trans (ler_norm C) (ltW hb).
have : (2 * B.+1)%:R * (1 / 2) <= (2 * B.+1)%:R * rlog 2 k by rewrite ler_wpM2l.
have e1 : ((2 * B.+1)%:R : rat) * (1 / 2) = B%:R + 1.
  by rewrite natrM -[B.+1]addn1 natrD mulr1n; field.
rewrite e1; move: hC; set R := rlog 2 k; set b := B%:R; set t := (2 * B.+1)%:R.
lra.
Qed.

(* ------------------------------------------------------------------ *)
(** * 6. Chebyshev's bound *)

(** Sums over primes [p <= x] are always written [rsum F [seq p <- iota 1 x | prime p]]. *)
Definition theta (x : nat) : rseq := rsum rlog [seq p <- iota 1 x | prime p].
Definition psi (x : nat) : rseq := rsum vmangoldt (iota 1 x).

Lemma prod_gt0_in (s : seq nat) (F : nat -> nat) :
  (forall i, i \in s -> (0 < F i)%N) -> (0 < \prod_(i <- s) F i)%N.
Proof.
elim: s => [|a s IH] h; first by rewrite big_nil.
rewrite big_cons muln_gt0 h ?mem_head //=; apply: IH => i hi.
by apply: h; rewrite in_cons hi orbT.
Qed.

Lemma rlog_prod (s : seq nat) (F : nat -> nat) :
  (forall i, i \in s -> (0 < F i)%N) -> forall k,
  rlog (\prod_(i <- s) F i) k = \sum_(i <- s) rlog (F i) k.
Proof.
elim: s => [|a s IH] h k; first by rewrite !big_nil rlog1.
have hs : forall i, i \in s -> (0 < F i)%N by move=> i hi; apply: h; rewrite in_cons hi orbT.
rewrite !big_cons rlog_mul ?IH // ?h ?mem_head //; exact: prod_gt0_in.
Qed.

Lemma prime_dvd_fact_le {p : nat} (n : nat) : prime p -> (p %| n`!)%N -> (p <= n)%N.
Proof.
move=> hp; elim: n => [|n IH]; first by rewrite fact0 Euclid_dvd1.
rewrite factS Euclid_dvdM // => /orP [h|h].
- exact: dvdn_leq h.
- exact: leq_trans (IH h) (leqnSn n).
Qed.

Lemma prod_primes_dvd_bin (n : nat) :
  (\prod_(n.+1 <= p < (2 * n).+1 | prime p) p %| 'C(2 * n, n))%N.
Proof.
set P := (\prod_(n.+1 <= p < (2 * n).+1 | prime p) p)%N.
set R := (\prod_(n.+1 <= i < (2 * n).+1) i)%N.
have h2n : (2 * n - n = n)%N by rewrite mul2n -addnn addnK.
have hle : (n.+1 <= (2 * n).+1)%N by rewrite ltnS mul2n -addnn leq_addr.
have hfact : ((2 * n)`! = n`! * R)%N.
  by rewrite !fact_prod (big_cat_nat (n := n.+1)).
have hbin : ('C(2 * n, n) * n`! = R)%N.
  have hn2 : (n <= 2 * n)%N by rewrite mul2n -addnn leq_addr.
  have := bin_fact hn2; rewrite h2n hfact mulnA => /eqP.
  by rewrite [(_ * _`!)%N]mulnC eqn_pmul2l ?fact_gt0 // => /eqP.
have hPR : (P %| R)%N by rewrite /R (bigID prime) /= dvdn_mulr.
have hcop : coprime P n`!.
  rewrite /P big_seq_cond; apply: (big_ind (fun a => coprime a n`!)).
  - exact: coprime1n.
  - by move=> a b ha hb; rewrite coprimeMl ha hb.
  - move=> p /andP [hp hpr]; rewrite prime_coprime //; apply/negP => hd.
    move: hp; rewrite mem_index_iota => /andP [hp _].
    by have := prime_dvd_fact_le n hpr hd; rewrite leqNgt hp.
by rewrite -(Gauss_dvdl _ hcop) hbin.
Qed.

Lemma bin_le_4pow (n : nat) : ('C(2 * n, n) <= 4 ^ n)%N.
Proof.
have hs : (\sum_(i < (2 * n).+1) 'C(2 * n, i) * (1 ^ (2 * n - i) * 1 ^ i) =
           \sum_(i < (2 * n).+1) 'C(2 * n, i))%N.
  by apply: eq_bigr => i _; rewrite !exp1n !muln1.
have hn : (n < (2 * n).+1)%N by rewrite ltnS mul2n -addnn leq_addr.
have h4 : (4 ^ n = (1 + 1) ^ (2 * n))%N by rewrite expnM.
by rewrite h4 expnDn hs (bigD1 (Ordinal hn)) //= leq_addr.
Qed.

Lemma theta_succ (x : nat) : forall k,
  theta x.+1 k = theta x k + (if prime x.+1 then rlog x.+1 k else 0).
Proof.
move=> k; rewrite /theta /rsum !big_filter.
have -> : iota 1 x.+1 = iota 1 x ++ [:: x.+1] by rewrite -[in LHS](addn1 x) iotaD add1n.
rewrite big_cat /= big_cons big_nil.
by case: ifP => _; rewrite ?addr0.
Qed.

Lemma theta_succ_le (x : nat) : forall k, theta x.+1 k <= theta x k + rlog x.+1 k.
Proof.
move=> k; rewrite theta_succ lerD2l; case: ifP => _ //; exact: rlog_ge0_pt.
Qed.

Lemma theta0 : forall k, theta 0 k = 0.
Proof. by move=> k; rewrite /theta /rsum big_nil. Qed.

Lemma theta_ge0 (x : nat) : forall k, 0 <= theta x k.
Proof. by move=> k; apply: sumr_ge0 => p _; apply: rlog_ge0_pt. Qed.

Lemma theta_cauchy (x : nat) : cauchy (theta x).
Proof. by apply: cauchy_rsum => p _; apply: rlog_cauchy. Qed.

Lemma theta_diff (n : nat) : forall k,
  theta (2 * n) k - theta n k = rlog (\prod_(n.+1 <= p < (2 * n).+1 | prime p) p)%N k.
Proof.
move=> k; rewrite /theta /rsum !big_filter mul2n -addnn iotaD big_cat /= addrC addKr.
rewrite -[in RHS]big_filter rlog_prod; first by move=> i; rewrite mem_filter => /andP [/prime_gt0].
by rewrite big_filter /index_iota subSS addnK add1n.
Qed.

Lemma theta_double (n : nat) : rle (rsub (theta (2 * n)) (theta n)) (cst (2 * n%:R)).
Proof.
have hC : (0 < 'C(2 * n, n))%N by rewrite bin_gt0 mul2n -addnn leq_addr.
have h4 : (0 < 4 ^ n)%N by rewrite expn_gt0.
apply: rle_trans (_ : rle _ (rlog 'C(2 * n, n))) _.
  apply: rle_of_ptwise => k; rewrite /rsub theta_diff.
  exact: rlog_dvd_pt hC (prod_primes_dvd_bin n) k.
apply: rle_trans (rlog_mono hC (bin_le_4pow n)) _.
apply: rle_of_ptwise => k; rewrite /cst.
have -> : (4 ^ n = 2 ^ (2 * n))%N by rewrite expnM.
rewrite rlog_pow2 natrM.
have h := rlog2_le1_pt k; have h0 : 0 <= (2%:R : rat) * n%:R by rewrite mulr_ge0 ?ler0n.
have := ler_wpM2l h0 h; rewrite mulr1 => h'; exact: h'.
Qed.

Lemma theta_double' (n : nat) : rle (theta (2 * n)) (radd (theta n) (cst (2 * n%:R))).
Proof.
move=> e he; apply: ev_mono (theta_double n e he) => k.
rewrite /rsub /radd /cst; lra.
Qed.

Lemma nat_parity (x : nat) : exists n, x = (2 * n)%N \/ x = (2 * n).+1.
Proof.
exists x./2; rewrite mul2n; have := odd_double_half x.
by case: (odd x) => h; [right | left]; rewrite -{1}h ?add1n ?add0n.
Qed.

Lemma theta_le (x : nat) : rle (theta x) (cst (4 * x%:R)).
Proof.
elim/ltn_ind: x => x IH.
have [n [hx|hx]] := nat_parity x.
- case: n hx => [|n] hx.
    by rewrite hx; apply: rle_of_ptwise => k; rewrite theta0 /cst mulr0.
  have hlt : (n.+1 < x)%N by rewrite hx mul2n -addnn -addn1 leq_add2l.
  apply: rle_trans (_ : rle _ (radd (theta n.+1) (cst (2 * n.+1%:R)))) _.
    by rewrite hx; apply: theta_double'.
  apply: rle_trans (rle_add (IH _ hlt) (rle_refl _)) _.
  apply: rle_of_ptwise => k; rewrite /radd /cst hx natrM.
  have := ler0n rat n.+1; set N := n.+1%:R; lra.
- have hlt : (n < x)%N by rewrite hx ltnS mul2n -addnn leq_addr.
  apply: rle_trans (_ : rle _ (radd (theta (2 * n)) (rlog x))) _.
    by rewrite hx; apply: rle_of_ptwise => k; apply: theta_succ_le.
  apply: rle_trans (rle_add (theta_double' n) (rlog_le_nat x)) _.
  apply: rle_trans (rle_add (rle_add (IH _ hlt) (rle_refl _)) (rle_refl _)) _.
  apply: rle_of_ptwise => k; rewrite /radd /cst hx -!(natr1 (2 * n)%N) natrM.
  have := ler0n rat n; set N := n%:R; lra.
Qed.

(** [psi] as a double sum over prime powers. *)
Lemma psi_expand (x : nat) : forall k, psi x k =
  \sum_(p <- [seq p <- iota 1 x | prime p]) \sum_(j <- iota 1 x)
     (if (p ^ j <= x)%N then rlog p k else 0).
Proof.
move=> k; rewrite /psi /rsum.
have hexp : forall n, n \in iota 1 x -> vmangoldt n k =
    \sum_(p <- [seq p <- iota 1 x | prime p]) \sum_(j <- iota 1 x)
       (if n == (p ^ j)%N then rlog p k else 0).
  move=> n hn; rewrite vmangoldtE; apply: (pp_expand n (fun p _ => rlog p k)
    (P := [seq p <- iota 1 x | prime p]) (J := fun _ => iota 1 x)).
  + by apply: filter_uniq; apply: iota_uniq.
  + exact: filter_all.
  + by move=> _; apply: iota_uniq.
  + by move=> _ j; rewrite mem_iota => /andP [].
  + move=> p j hp hj hnp; move: hn; rewrite hnp !mem_iota => /andP [_ hpx].
    rewrite mem_filter hp mem_iota prime_gt0 //= hj /=; split.
    * exact: leq_ltn_trans (prime_pow_ge hp hj) hpx.
    * exact: ltn_trans (ltn_expl _ (prime_gt1 hp)) hpx.
rewrite (eq_big_seq _ hexp) exchange_big /=; apply: eq_big_seq => p.
rewrite mem_filter => /andP [hp _].
rewrite exchange_big /=; apply: eq_bigr => j _.
by rewrite sum_if_eq ?iota_uniq // mem_iota add1n ltnS expn_gt0 prime_gt0.
Qed.

Lemma psi_cauchy (x : nat) : cauchy (psi x).
Proof. by apply: cauchy_rsum => n _; apply: vmangoldt_cauchy. Qed.

Lemma psi_ge0 (x : nat) : forall k, 0 <= psi x k.
Proof. by move=> k; apply: sumr_ge0 => n _; apply: vmangoldt_ge0. Qed.

Lemma psi_theta_le (x : nat) :
  rle (psi x) (radd (theta x) (rmul (cst (Nat.sqrt x)%:R) (rlog x))).
Proof.
set s := Nat.sqrt x.
pose S p : rseq := fun k => \sum_(j <- iota 1 x) (if (p ^ j <= x)%N then rlog p k else 0).
pose T p : rseq := fun k => if (p <= s)%N then rlog x k else 0.
have hS : forall p, p \in [seq p <- iota 1 x | prime p] -> rle (S p) (radd (rlog p) (T p)).
  move=> p; rewrite mem_filter mem_iota add1n ltnS => /andP [hp /andP [hp1 hpx]].
  have hx0 : (0 < x)%N by apply: leq_trans hpx.
  have hp1' := prime_gt1 hp.
  case: (leqP p s) => hps.
  - (* small primes: total weight at most rlog x *)
    set t := trunc_log p x.
    have [htx hxt] := andP (trunc_log_bounds hp1' hx0).
    apply: rle_trans (_ : rle _ (rlog x)) _; last first.
      by apply: rle_of_ptwise => k; rewrite /radd /T hps lerDr rlog_ge0_pt.
    have hpt : (0 < p ^ t)%N by rewrite expn_gt0 prime_gt0.
    apply: rle_trans _ (rlog_mono hpt htx).
    apply: rle_of_ptwise => k; rewrite rlog_pow.
    apply: le_trans (sum_if_le t _ _ (rlog_ge0_pt p k)).
    + apply: ler_sum => j _; case: ifP => hj; case: ifP => hjt //.
      * exfalso; move/negbT: hjt; rewrite -ltnNge => hjt.
        have := leq_trans hxt (leq_pexp2l (prime_gt0 hp) hjt); rewrite ltnNge hj.
        by [].
      * exact: rlog_ge0_pt.
    + exact: iota_uniq.
    + by apply/allP => j; rewrite mem_iota => /andP [].
  - (* large primes: only j = 1 counts *)
    have hpp : (x < p * p)%N.
      have [_ h] := isqrt_spec x; apply: leq_trans h _.
      by apply: leq_mul.
    apply: rle_of_ptwise => k; rewrite /S /radd /T leqNgt hps /= addr0.
    have hio : iota 1 x = 1 :: iota 2 x.-1 by rewrite -[in LHS](prednK hx0).
    rewrite hio big_cons expn1 hpx big1_seq ?addr0 //.
    move=> j /andP [_]; rewrite mem_iota => /andP [hj _].
    case: ifP => // hjx; exfalso.
    have : (p * p <= p ^ j)%N by rewrite mulnn; apply: leq_pexp2l => //; apply: prime_gt0.
    by move=> h; have := leq_ltn_trans (leq_trans h hjx) hpp; rewrite ltnn.
have hpsi : req (psi x) (rsum S [seq p <- iota 1 x | prime p]).
  by apply: req_of_eq => k; rewrite psi_expand.
apply: req_rle_trans hpsi _.
apply: rle_trans (rle_rsum hS) _.
apply: req_rle_trans (rsum_add _ _ _) _.
apply: rle_add; first exact: rle_refl.
apply: rle_of_ptwise => k; rewrite /rsum /rmul /cst /T.
apply: sum_if_le; first by apply: filter_uniq; apply: iota_uniq.
- by apply/allP => p; rewrite mem_filter => /andP [/prime_gt0].
- exact: rlog_ge0_pt.
Qed.

Lemma psi_theta (x : nat) :
  rle (rsub (psi x) (theta x)) (rmul (cst (Nat.sqrt x)%:R) (rlog x)).
Proof.
move=> e he; apply: ev_mono (psi_theta_le x e he) => k.
rewrite /rsub /radd /rmul /cst; lra.
Qed.

Lemma isqrt_rlog_le (x : nat) : rle (rmul (cst (Nat.sqrt x)%:R) (rlog x)) (cst (2 * x%:R)).
Proof.
apply: rle_trans (rle_rmul_cst _ (ler0n _ _) (rlog_le_sqrt x)) _.
apply: rle_of_ptwise => k; rewrite /rmul /cst.
have h1 := rsqrt_isqrt x k; have h2 := rsqrt_ge0 x k; have h3 := rsqrt_sqr_le x k.
have : (Nat.sqrt x)%:R * (2 * rsqrt x k) <= rsqrt x k * (2 * rsqrt x k).
  by apply: ler_wpM2r => //; rewrite mulr_ge0.
move: h1 h2 h3; set r := rsqrt x k; set q := (Nat.sqrt x)%:R; set X := x%:R.
move=> h1 h2 h3 h4.
have : r * (2 * r) = 2 * (r * r) by rewrite mulrCA.
lra.
Qed.

Lemma psi_le (x : nat) : rle (psi x) (cst (6 * x%:R)).
Proof.
apply: rle_trans (psi_theta_le x) _.
apply: rle_trans (rle_add (theta_le x) (isqrt_rlog_le x)) _.
apply: rle_of_ptwise => k; rewrite /radd /cst; lra.
Qed.

(* ------------------------------------------------------------------ *)
(** * 7. Mertens-type lower bounds *)

Lemma rlog_div_cauchy (p : nat) : cauchy (rdiv (rlog p) (cst p%:R)).
Proof.
apply: cauchy_ext (cauchy_mul (rlog_cauchy p) (cauchy_cst (p%:R)^-1)) => k.
by rewrite /rmul /rdiv /cst.
Qed.

Lemma vmangoldt_div_cauchy (d : nat) : cauchy (rdiv (vmangoldt d) (cst d%:R)).
Proof.
apply: cauchy_ext (cauchy_mul (vmangoldt_cauchy d) (cauchy_cst (d%:R)^-1)) => k.
by rewrite /rmul /rdiv /cst.
Qed.

Lemma lsum_sum_lower {k : nat} (x : nat) : (0 < k)%N ->
  x.+1%:R * lsum k x.+1 - x%:R <= \sum_(n <- iota 1 x.+1) lsum k n.
Proof.
move=> hk; elim: x => [|x IH].
  by rewrite /= big_seq1 lsum1 mulr0 subr0.
have -> : iota 1 x.+2 = iota 1 x.+1 ++ [:: x.+2] by rewrite -[in LHS](addn1 x.+1) iotaD add1n.
rewrite big_cat /= big_seq1.
have /andP [_ h] := lsum_succ_bounds hk (ltn0Sn x).
have hX : 0 <= x.+1%:R :> rat by rewrite ler0n.
have := ler_wpM2l hX h.
rewrite mulrBr mul1r divff ?pnatr_eq0 //.
move: IH; rewrite -!(natr1 x.+1) -(natr1 x).
set a := lsum k x.+2; set b := lsum k x.+1; set X := x%:R.
move=> IH h'; lra.
Qed.

Lemma sum_rlog_lower {x : nat} : (0 < x)%N ->
  rle (rsub (rmul (cst x%:R) (rlog x)) (cst (x%:R - 1))) (rsum rlog (iota 1 x)).
Proof.
case: x => [//|x] _.
apply: req_rle_trans (req_rsub (req_rmul_cst _ (rlog_lrs (ltn0Sn x))) (req_refl _)) _.
apply: rle_req_trans _ (rsum_ext_in (F := lrs) (G := rlog) _); last first.
  move=> n; rewrite mem_iota => /andP [hn _]; exact: req_sym (rlog_lrs hn).
apply: rle_of_ptwise => k; rewrite /rsub /rmul /cst /rsum /lrs.
have := lsum_sum_lower x (ltn0Sn k); rewrite -(natr1 x).
set a := lsum k.+1 x.+1; set X := x%:R; move=> h; lra.
Qed.

Lemma divisors_perm {n : nat} : (0 < n)%N ->
  perm_eq (divisors n) [seq d <- index_iota 1 n.+1 | (d %| n)%N].
Proof.
move=> hn; apply: uniq_perm; first exact: divisors_uniq.
  by apply: filter_uniq; apply: iota_uniq.
move=> d; rewrite mem_filter mem_index_iota -dvdn_divisors //.
case hd: (d %| n)%N => //=; symmetry.
by rewrite ltnS (dvdn_leq hn hd) andbT; apply: dvdn_gt0 hd.
Qed.

Lemma sum_rlog_floor (x : nat) : forall k,
  \sum_(1 <= n < x.+1) rlog n k = \sum_(1 <= d < x.+1) vmangoldt d k * (x %/ d)%:R.
Proof.
move=> k; elim: x => [|x IH]; first by rewrite !big_geq.
rewrite big_nat_recr //= IH.
have hsplit : forall d, (1 <= d < x.+2)%N -> vmangoldt d k * (x.+1 %/ d)%:R =
    (if (d %| x.+1)%N then vmangoldt d k else 0) + vmangoldt d k * (x %/ d)%:R.
  move=> d /andP [hd _]; rewrite divnS // natrD mulrDr.
  by case: (d %| x.+1)%N; rewrite ?mulr1 ?mulr0.
rewrite (eq_big_nat _ _ hsplit) big_split /=.
rewrite [X in _ = _ + X]big_nat_recr //= divn_small // mulr0 addr0.
rewrite addrC; congr (_ + _).
rewrite -big_mkcond -big_filter -(perm_big _ (divisors_perm (ltn0Sn x))).
by rewrite vmangoldt_divisors.
Qed.

Lemma vmangoldt_div_lower {x : nat} : (0 < x)%N ->
  rle (rsub (rlog x) (cst 1)) (rsum (fun d => rdiv (vmangoldt d) (cst d%:R)) (iota 1 x)).
Proof.
move=> hx; have hX : 0 < x%:R :> rat by rewrite ltr0n.
apply: (rle_rmul_cancel_l (h := cst x%:R)); first by apply/rlt_cst.
apply: rle_trans (_ : rle _ (rsub (rmul (cst x%:R) (rlog x)) (cst (x%:R - 1)))) _.
  by apply: rle_of_ptwise => k; rewrite /rmul /rsub /cst; lra.
apply: rle_trans (sum_rlog_lower hx) _.
apply: rle_of_ptwise => k; rewrite /rsum /rmul /rdiv /cst.
have -> : iota 1 x = index_iota 1 x.+1 by rewrite /index_iota subSS subn0.
rewrite sum_rlog_floor mulr_sumr; apply: ler_sum_nat => d /andP [hd hdx].
have hD : 0 < d%:R :> rat by rewrite ltr0n.
have hq : (x %/ d)%:R <= x%:R / d%:R :> rat.
  by rewrite ler_pdivlMr // -natrM ler_nat leq_divM.
have := ler_wpM2l (vmangoldt_ge0 d k) hq.
by rewrite mulrCA mulrA.
Qed.

(** Proper prime powers contribute a bounded amount. *)
Lemma tele_step {h u v : rat} : 0 <= h -> 0 < u -> u <= 1 / 2 -> u <= v -> v - u = u * v ->
  (h + u) * (u * u) <= (h + 3 / 2) * v - (h + u + 3 / 2) * u.
Proof.
move=> h0 u0 u2 uv e.
have hA : 0 <= h + 3 / 2 by lra.
have hB : 0 <= v - u by lra.
have hC : 0 <= 1 / 2 - u by lra.
have h1 := mulr_ge0 (mulr_ge0 hA (ltW u0)) hB.
have h2 := mulr_ge0 (mulr_ge0 (ltW u0) (ltW u0)) hC.
have h3 : (h + 3 / 2) * (v - u) = (h + 3 / 2) * (u * v) by rewrite e.
nra.
Qed.

Definition hsq (n : nat) : rat := harm n / (n * n)%:R.

Lemma hsq_ge0 (n : nat) : 0 <= hsq n.
Proof. by rewrite /hsq divr_ge0 ?harm_ge0 ?ler0n. Qed.

Lemma sum_hsq_tele (m : nat) :
  \sum_(p <- iota 1 m.+1) (if (1 < p)%N then hsq p else 0) <= 5 / 2 - (harm m.+1 + 3 / 2) / m.+1%:R.
Proof.
elim: m => [|m IH].
  rewrite /= big_seq1 /= harm1 divr1; lra.
have -> : iota 1 m.+2 = iota 1 m.+1 ++ [:: m.+2] by rewrite -[in LHS](addn1 m.+1) iotaD add1n.
rewrite big_cat big_seq1 /=; move: IH.
set h := harm m.+1; set u := (m.+2%:R)^-1 : rat; set v := (m.+1%:R)^-1 : rat.
have hN : 0 < m.+2%:R :> rat by rewrite ltr0n.
have hA : 0 < m.+1%:R :> rat by rewrite ltr0n.
have hu : 0 < u by rewrite invr_gt0.
have hu2 : u <= 1 / 2 by rewrite /u div1r lef_pV2 ?posrE ?ltr0n // ler_nat.
have huv : u <= v by rewrite lef_pV2 ?posrE // ler_nat.
have he : v - u = u * v.
  rewrite /u /v -(natr1 m.+1).
  have h2 : 1 + m%:R != 0 :> rat by rewrite addrC natr1 pnatr_eq0.
  have h3 : 1 + m%:R + 1 != 0 :> rat by rewrite [1 + _]addrC !natr1 pnatr_eq0.
  by field.
have hh : harm m.+2 = h + u by rewrite harm_succ div1r.
have hs : hsq m.+2 = (h + u) * (u * u) by rewrite /hsq hh natrM invfM.
have := tele_step (harm_ge0 m.+1) hu hu2 huv he.
rewrite hs hh.
set S := \sum_(p <- _) _.
move=> T IH; move: T; rewrite -/h => T; lra.
Qed.

Lemma sum_hsq_le (x : nat) : \sum_(p <- iota 1 x) (if (1 < p)%N then hsq p else 0) <= 5 / 2.
Proof.
case: x => [|m]; first by rewrite big_nil; lra.
apply: le_trans (sum_hsq_tele m) _.
have : 0 <= (harm m.+1 + 3 / 2) / m.+1%:R.
  by rewrite divr_ge0 ?ler0n //; have := harm_ge0 m.+1; lra.
set X := (harm m.+1 + 3 / 2) / m.+1%:R; move=> hX; lra.
Qed.

Lemma geom_tail {r : rat} (m : nat) : 0 <= r -> r <= 1 / 2 ->
  \sum_(j <- iota 1 m) (if (1 < j)%N then r ^+ j else 0) <= 2 * (r * r).
Proof.
move=> r0 r2.
have key : forall m, \sum_(j <- iota 1 m.+1) (if (1 < j)%N then r ^+ j else 0) <=
                     2 * (r * r) - 2 * r ^+ m.+2.
  elim=> [|m' IH]; first by rewrite /= big_seq1 /= expr2; lra.
  have -> : iota 1 m'.+2 = iota 1 m'.+1 ++ [:: m'.+2]
    by rewrite -[in LHS](addn1 m'.+1) iotaD add1n.
  rewrite big_cat /= big_seq1 /=.
  have hp : 0 <= r ^+ m'.+2 by rewrite exprn_ge0.
  have : 0 <= r ^+ m'.+2 * (1 - 2 * r) by rewrite mulr_ge0 //; lra.
  rewrite [r ^+ m'.+3]exprS; move: IH; set y := r ^+ m'.+2; set S := \sum_(_ <- _) _.
  move=> IH h; nra.
case: m => [|m]; first by rewrite big_nil mulr_ge0 // mulr_ge0.
apply: le_trans (key m) _; have : 0 <= r ^+ m.+2 by rewrite exprn_ge0.
lra.
Qed.

Lemma prime_pow_notprime {q i : nat} : prime q -> prime (q ^ i) -> i = 1%N.
Proof.
move=> hq hqi; have hi : (0 < i)%N.
  by case: i hqi => // ; rewrite expn0.
have : (q %| q ^ i)%N by rewrite dvdn_exp.
rewrite dvdn_prime2 // => /eqP hqq.
by apply/eqP; rewrite -(eqn_exp2l _ _ (prime_gt1 hq)) expn1 -hqq.
Qed.

Lemma pp_cover_iota {x n : nat} : n \in iota 1 x -> forall p j, prime p -> (0 < j)%N -> n = (p ^ j)%N ->
  p \in [seq p <- iota 1 x | prime p] /\ j \in iota 1 x.
Proof.
move=> hn p j hp hj hnp; move: hn; rewrite hnp !mem_iota => /andP [_ hpx].
rewrite mem_filter hp mem_iota prime_gt0 //= hj /=; split.
- exact: leq_ltn_trans (prime_pow_ge hp hj) hpx.
- exact: ltn_trans (ltn_expl _ (prime_gt1 hp)) hpx.
Qed.

Definition ppterm (n : nat) : rseq :=
  if (1 < n)%N && ~~ prime n then rdiv (vmangoldt n) (cst n%:R) else cst 0.

Lemma prime_pow_tail_pt (x : nat) : forall k,
  \sum_(n <- iota 1 x) ppterm n k <= 8.
Proof.
move=> k.
pose c p j : rat := if (1 < j)%N then rlog p k / (p ^ j)%:R else 0.
have hc0 : forall p j, 0 <= c p j.
  move=> p j; rewrite /c; case: ifP => _ //.
  by rewrite divr_ge0 ?ler0n ?rlog_ge0_pt.
set PR := [seq p <- iota 1 x | prime p].
have hexp : forall n, n \in iota 1 x -> ppterm n k =
    \sum_(p <- PR) \sum_(j <- iota 1 x) (if n == (p ^ j)%N then c p j else 0).
  move=> n hn.
  have hu : uniq PR by apply: filter_uniq; apply: iota_uniq.
  have hpr : all prime PR by apply: filter_all.
  have hj : forall (p : nat) (j : nat), j \in iota 1 x -> (0 < j)%N.
    by move=> _ j; rewrite mem_iota => /andP [].
  rewrite -(pp_expand n c hu hpr (fun _ => iota_uniq 1 x) hj (pp_cover_iota hn)).
  rewrite /ppterm; case: ifP => [/andP [hn1 hnp] | hb].
    * rewrite /rdiv /cst vmangoldtE /c.
      case: ifP => [/andP [_ /eqP hnq] | _]; last by rewrite mul0r.
      set q := pdiv n in hnq *; set i := logn q n in hnq *.
      have hq : prime q by apply: pdiv_prime.
      case: ifP => hi; first by rewrite -hnq.
      exfalso; move/negP: hnp; apply.
      have hi0 : (0 < i)%N by rewrite logn_gt0 mem_primes hq (ltnW hn1) pdiv_dvd.
      have hi1 : i = 1%N by case: i hi hi0 {hnq} => [|[|]].
      by rewrite hnq hi1 expn1.
    * rewrite /cst; case: ifP => [/andP [hn1 /eqP hnq] | _] //.
      set q := pdiv n in hnq *; set i := logn q n in hnq *.
      have hq : prime q by apply: pdiv_prime.
      rewrite /c; case: ifP => hi //; exfalso.
      move: hb; rewrite hn1 /= => /negbFE hpn.
      have := prime_pow_notprime hq (_ : prime (q ^ i)); rewrite -hnq => /(_ hpn) hi1.
      by move: hi; rewrite hi1.
rewrite (eq_big_seq _ hexp) exchange_big /=.
have hp_le : forall p, p \in PR -> \sum_(j <- iota 1 x) \sum_(n <- iota 1 x)
    (if n == (p ^ j)%N then c p j else 0) <= 2 * hsq p.
  move=> p; rewrite mem_filter => /andP [hp _].
  have hp1 : 1 < p%:R :> rat by rewrite ltr1n prime_gt1.
  apply: le_trans (_ : \sum_(j <- iota 1 x) c p j <= _).
    apply: ler_sum => j _; rewrite sum_if_eq ?iota_uniq //.
    by case: ifP => _ //.
  have -> : \sum_(j <- iota 1 x) c p j =
            rlog p k * \sum_(j <- iota 1 x) (if (1 < j)%N then (p%:R^-1) ^+ j else 0).
    rewrite mulr_sumr; apply: eq_bigr => j _; rewrite /c; case: ifP => _; last by rewrite mulr0.
    by rewrite natrX exprVn.
  have hr0 : 0 <= p%:R^-1 :> rat by rewrite invr_ge0 ler0n.
  have hr2 : p%:R^-1 <= 1 / 2 :> rat.
    rewrite div1r lef_pV2 ?posrE //; try lra.
    by have := prime_gt1 hp; rewrite -(ler_nat rat) => h; apply: le_trans h.
  have hg := geom_tail x hr0 hr2.
  have hg0 : 0 <= \sum_(j <- iota 1 x) (if (1 < j)%N then (p%:R^-1) ^+ j else 0 : rat).
    by apply: sumr_ge0 => j _; case: ifP => _ //; rewrite exprn_ge0.
  have hl : rlog p k <= harm p by rewrite rlog_prime //; apply: lrs_le_harm_pt.
  apply: le_trans (ler_pM (rlog_ge0_pt p k) hg0 hl hg) _.
  rewrite /hsq natrM invfM; rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
apply: (le_trans (y := \sum_(p <- PR) 2 * hsq p)).
  rewrite big_seq [X in _ <= X]big_seq; apply: ler_sum => p hp; rewrite exchange_big; exact: hp_le p hp.
rewrite -mulr_sumr.
have : \sum_(p <- PR) hsq p <= 5 / 2.
  apply: le_trans (sum_hsq_le x); rewrite /PR big_filter big_mkcond /=.
  apply: ler_sum => p _; case: ifP => hp.
  - by rewrite prime_gt1.
  - by case: ifP => _ //; apply: hsq_ge0.
set S := \sum_(p <- PR) hsq p; move=> h; lra.
Qed.

Lemma prime_pow_tail (x : nat) :
  rle (rsum (fun n => if (1 < n)%N && ~~ prime n then rdiv (vmangoldt n) (cst n%:R) else cst 0)
            (iota 1 x)) (cst 8).
Proof. by apply: rle_of_ptwise => k; apply: (prime_pow_tail_pt x k). Qed.

Lemma vmangoldt_div_split (d : nat) : forall k,
  vmangoldt d k / d%:R = (if prime d then rlog d k / d%:R else 0) + ppterm d k.
Proof.
move=> k; rewrite /ppterm; case: ifP => hd.
- by rewrite (vmangoldt_prime hd) andbF /cst addr0.
- rewrite add0r; case: ifP => [_ | hb]; first by [].
  rewrite /cst; case: (leqP d 1) => hd1; first by rewrite vmangoldt_le1 // mul0r.
  by move: hb; rewrite hd1.
Qed.

Lemma sum_rlog_primes_lower (x : nat) :
  rle (rsub (rlog x) (cst 9)) (rsum (fun p => rdiv (rlog p) (cst p%:R)) [seq p <- iota 1 x | prime p]).
Proof.
case: x => [|x].
  by apply: rle_of_ptwise => k; rewrite /rsub /cst /rsum rlog0 big_nil; lra.
have hsplit : forall k, rsum (fun d => rdiv (vmangoldt d) (cst d%:R)) (iota 1 x.+1) k =
    rsum (fun p => rdiv (rlog p) (cst p%:R)) [seq p <- iota 1 x.+1 | prime p] k +
    \sum_(n <- iota 1 x.+1) ppterm n k.
  move=> k; rewrite /rsum /rdiv /cst (eq_bigr _ (fun d _ => vmangoldt_div_split d k)).
  by rewrite big_split [in RHS]big_filter [in RHS]big_mkcond.
move=> e he; have he2 : 0 < e / 2 by lra.
apply: ev_mono (vmangoldt_div_lower (ltn0Sn x) e he) => k.
rewrite hsplit /rsub /cst; have := prime_pow_tail_pt x.+1 k.
set A := rsum _ _ k; set T := \sum_(n <- _) _; move=> hT h; lra.
Qed.

Lemma sum_rlog_primes_unbounded (C : rat) :
  exists x, rlt (cst C) (rsum (fun p => rdiv (rlog p) (cst p%:R)) [seq p <- iota 1 x | prime p]).
Proof.
have [n [e [he [N hN]]]] := rlog_unbounded (C + 9).
exists n; apply: rlt_rle_trans (sum_rlog_primes_lower n).
exists e; split=> //; exists N => k hk; have := hN k hk; rewrite /rsub /cst; lra.
Qed.

