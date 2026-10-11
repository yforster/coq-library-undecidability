(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Analytic core, part 1: L(1, chi) converges and is positive (PLAN.md
   Phase 4, task D4a; DIRICHLET_DESIGN.md, Sec. 3 steps 1-3 and Sec. 7).
   Built on the choice-free reals of RSeq.v only; the logarithm (RLog.v)
   is combined with this file later (DirichletQuad.v).

   Contents.
   1. Generic finite-sum lemmas (in [rat]): [abel_bound] (Abel summation:
      |sum_(n0<=n<=x) a_n w_n| <= B w_n0 for w nonnegative nonincreasing
      and partial sums of a bounded by B), [abel_bound_rseq],
      [sum_divisors_nat], [pair_sum_divisors]
      (sum_(n<=x) sum_(d|n) f d (n/d) = sum_(d<=x) sum_(e<=x/d) f d e),
      [sum_swap_min], [sum_swap_tail] (the two swaps of the hyperbola
      method), [sum_squares_le], [harm_pow2], [harm_unbounded],
      [exists_small], [geom_sum].
   2. Square-root helpers: [rinv_req], [rinv_rsqrt_mul]
      (1/sqrt(de) = 1/sqrt d * 1/sqrt e as [req]), [rinv_rsqrt_eq]
      (1/sqrt d = sqrt d / d as [req]).
   3. Section [AbstractChar]: a completely multiplicative [chi : nat -> int]
      with [chi 1 = 1], [|chi| <= 1] and all window sums bounded by [M].
      - [chi_abel], [chi_abel_isq], [chi_window_sqrt]: Abel bounds for
        windows of [chi] with weights [1/n] and [1/sqrt n];
      - [Lchi] (partial sums of sum chi(n)/n), [Lchi_diff], [Lchi_tail]
        (|L - S_x| <= M/(x+1)), [Lchi_cauchy];
      - [F n := sum_(d | n) chi d], [F_pfactor] (Euler factor at a prime),
        [F_ge0], [F_square_ge1];
      - hyperbola method: [divsum x := sum_(n<=x) F n / sqrt n],
        [divsum_hyperbola] (as [req]), [divsum_lower] (>= H(isqrt x)),
        [E_delta], [A2_bound], [hypB_bound], [A1_main], [A1_L],
        [divsum_upper] (<= 2 sqrt x L + C with C = 2 + 6M);
      - [Lchi_pos : rlt (cst 0) Lchi], [Lchi_ge].

   The error term of the hyperbola method avoids pointwise monotonicity
   of [E]: [E z = - sum_(e<=z) delta e] with [delta e >= 0] (as [rle]) and
   the order of summation is swapped ([sum_swap_min]), so only bounded
   inner sums of [chi d / sqrt d] (pointwise Abel) are needed.

   Arguments of lemmas are implicit exactly when they occur in a
   hypothesis. *)

From Stdlib Require Import PeanoNat Setoid Morphisms Classical_Prop.
From mathcomp Require Import boot order algebra.
Import Order.TTheory GRing.Theory Num.Theory.
From Undecidability.H10.Rational Require Import RSeq.

Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Lemma abel_bound (a w : nat -> rat) (B : rat) (n0 x : nat) :
  (n0 <= x)%N ->
  (forall y, (n0 <= y)%N -> (y <= x)%N -> `|\sum_(n0 <= n < y.+1) a n| <= B) ->
  (forall n, (n0 <= n)%N -> (n < x)%N -> w n.+1 <= w n) ->
  (forall n, (n0 <= n)%N -> (n <= x)%N -> 0 <= w n) ->
  `|\sum_(n0 <= n < x.+1) a n * w n| <= B * w n0.
Proof.
move=> hx hA hw hw0.
pose A y := \sum_(n0 <= n < y.+1) a n.
suff H : forall j, (n0 + j <= x)%N -> exists R,
    \sum_(n0 <= n < (n0 + j)%N.+1) a n * w n = A (n0 + j)%N * w (n0 + j)%N + R /\
    `|R| <= B * (w n0 - w (n0 + j)%N).
  have hj : (n0 + (x - n0) = x)%N by rewrite subnKC.
  have [R [e hR]] := H (x - n0)%N (eq_leq hj); rewrite hj in e hR; rewrite e.
  have hAx : `|A x| <= B := hA x hx (leqnn x).
  have hwx := hw0 x hx (leqnn x).
  have h1 : `|A x| * w x <= B * w x by apply: ler_wpM2r.
  have h2 : `|A x * w x + R| <= `|A x| * w x + `|R|.
    by rewrite -{2}(ger0_norm hwx) -normrM; apply: ler_normD.
  apply: (le_trans h2); apply: le_trans (lerD h1 hR) _.
  by rewrite mulrBr addrC subrK.
elim=> [|j IH] hj.
  by exists 0; rewrite addn0 /A !big_nat1 subrr mulr0 normr0 addr0.
have hj' : (n0 + j <= x)%N by apply: leq_trans hj; rewrite addnS.
have [R [e hR]] := IH hj'.
exists (R + A (n0 + j) * (w (n0 + j) - w (n0 + j).+1)); split.
  rewrite addnS (big_nat_recr (n0 + j).+1) /= ?leqW ?leq_addr //.
  rewrite e /A (big_nat_recr (n0 + j).+1) /= ?leqW ?leq_addr //.
  ring.
have hAj : `|A (n0 + j)| <= B := hA _ (leq_addr _ _) hj'.
have hd : 0 <= w (n0 + j) - w (n0 + j).+1.
  by rewrite subr_ge0; apply: hw; [apply: leq_addr | rewrite -addnS].
have h1 : `|A (n0 + j)| * (w (n0 + j) - w (n0 + j).+1) <= B * (w (n0 + j) - w (n0 + j).+1).
  by apply: ler_wpM2r.
have h2 : `|R + A (n0 + j) * (w (n0 + j) - w (n0 + j).+1)| <=
          `|R| + `|A (n0 + j)| * (w (n0 + j) - w (n0 + j).+1).
  by rewrite -{2}(ger0_norm hd) -normrM; apply: ler_normD.
rewrite addnS; apply: (le_trans h2); apply: le_trans (lerD hR h1) _.
by rewrite -mulrDr addrA subrK.
Qed.

Lemma sum_divisors_nat (g : nat -> rat) n : (0 < n)%N ->
  \sum_(d <- divisors n) g d = \sum_(1 <= d < n.+1 | (d %| n)%N) g d.
Proof.
move=> n0; rewrite -[in RHS]big_filter; apply: perm_big; apply: uniq_perm.
- exact: divisors_uniq.
- by rewrite filter_uniq // iota_uniq.
- move=> d; rewrite mem_filter mem_index_iota -dvdn_divisors //.
  case hd: (d %| n)%N => //=; apply/esym/andP; split.
  + exact: dvdn_gt0 n0 hd.
  + by rewrite ltnS; apply: dvdn_leq.
Qed.

Lemma pair_sum_divisors (f : nat -> nat -> rat) x :
  \sum_(1 <= n < x.+1) \sum_(d <- divisors n) f d (n %/ d)%N =
  \sum_(1 <= d < x.+1) \sum_(1 <= e < (x %/ d)%N.+1) f d e.
Proof.
elim: x => [|x IH]; first by rewrite !big_geq.
have h1 : \sum_(d <- divisors x.+1) f d (x.+1 %/ d)%N =
  \sum_(1 <= d < x.+1) (if (d %| x.+1)%N then f d (x.+1 %/ d)%N else 0) + f x.+1 1.
  by rewrite sum_divisors_nat // big_mkcond (big_nat_recr x.+1) //= dvdnn divnn.
rewrite big_nat_recr //= IH h1 [RHS](big_nat_recr x.+1) //= divnn big_nat1 addrA.
congr (_ + _).
rewrite -big_split /=; apply: eq_big_nat => d /andP [hd _].
rewrite (divnS x hd); case: (d %| x.+1)%N => /=.
- by rewrite add1n (big_nat_recr (x %/ d)%N.+1).
- by rewrite ?add0n addr0.
Qed.

Lemma sum_swap_min (a b : nat -> rat) x y :
  \sum_(1 <= d < y.+1) a d * \sum_(1 <= e < (x %/ d)%N.+1) b e =
  \sum_(1 <= e < x.+1) b e * \sum_(1 <= d < (minn y (x %/ e)%N).+1) a d.
Proof.
transitivity (\sum_(1 <= d < y.+1) \sum_(1 <= e < x.+1)
                 (if (d * e <= x)%N then a d * b e else 0)).
  apply: eq_big_nat => d /andP [hd _]; rewrite mulr_sumr.
  rewrite (big_nat_widen _ _ x.+1) ?ltnS ?leq_div // big_mkcond /=.
  by apply: eq_big_nat => e _; rewrite ltnS leq_divRL // mulnC.
rewrite exchange_big /=.
apply: eq_big_nat => e /andP [he _]; rewrite mulr_sumr.
rewrite [RHS](big_nat_widen _ _ y.+1) ?ltnS ?geq_minl // [RHS]big_mkcond /=.
apply: eq_big_nat => d /andP [_ hdy]; move: hdy.
rewrite !ltnS leq_min leq_divRL // => -> /=.
by case: ifP => // _; apply: mulrC.
Qed.

Lemma sum_swap_tail (g : nat -> nat -> rat) x y : (x < y.+1 * y.+1)%N ->
  \sum_(y.+1 <= d < x.+1) \sum_(1 <= e < (x %/ d)%N.+1) g d e =
  \sum_(1 <= e < y.+1) \sum_(y.+1 <= d < (x %/ e)%N.+1) g d e.
Proof.
move=> hx.
transitivity (\sum_(y.+1 <= d < x.+1) \sum_(1 <= e < y.+1)
                 (if (d * e <= x)%N then g d e else 0)).
  apply: eq_big_nat => d /andP [hd _].
  have d0 : (0 < d)%N by apply: leq_trans (ltn0Sn y) hd.
  have hxd : (x %/ d < y.+1)%N.
    by rewrite ltn_divLR //; apply: leq_trans hx _; rewrite leq_mul2l hd orbT.
  rewrite [LHS](big_nat_widen _ _ y.+1) // [LHS]big_mkcond /=.
  by apply: eq_big_nat => e _; rewrite ltnS leq_divRL // mulnC.
rewrite exchange_big /=.
apply: eq_big_nat => e /andP [he _].
rewrite [RHS](big_nat_widen _ _ x.+1) ?ltnS ?leq_div // [RHS]big_mkcond /=.
by apply: eq_big_nat => d _; rewrite ltnS leq_divRL.
Qed.

Lemma iota1E (x : nat) : iota 1 x = index_iota 1 x.+1.
Proof. by rewrite /index_iota subSS subn0. Qed.

Lemma sum_nat_ge0 (f : nat -> rat) m n :
  (forall i, (m <= i < n)%N -> 0 <= f i) -> 0 <= \sum_(m <= i < n) f i.
Proof. by move=> h; rewrite big_nat_cond; apply: sumr_ge0 => i /andP [hi _]; apply: h. Qed.

Lemma sum_squares_le {f : nat -> rat} {y x : nat} : (forall n, (1 <= n <= x)%N -> 0 <= f n) ->
  (y * y <= x)%N -> \sum_(1 <= m < y.+1) f (m * m)%N <= \sum_(1 <= n < x.+1) f n.
Proof.
move=> hf hyx; elim: y x hf hyx => [|y IH] x hf hyx.
  by rewrite big_geq //; apply: sum_nat_ge0 => i /andP [h1 h2]; apply: hf; rewrite h1 -ltnS.
set z := (y.+1 * y.+1)%N in hyx *.
have z0 : (0 < z)%N by rewrite muln_gt0.
rewrite big_nat_recr //= [X in _ <= X](@big_cat_nat _ _ _ z) //= ?(leqW hyx) //.
apply: lerD.
  have := IH z.-1; rewrite (prednK z0); apply.
    move=> n /andP [h1 h2]; apply: hf; rewrite h1 /=; apply: leq_trans h2 _.
    by apply: leq_trans (leq_pred z) hyx.
  by rewrite -ltnS (prednK z0) ltn_mul.
rewrite big_ltn ?ltnS // lerDl; apply: sum_nat_ge0 => i /andP [h1 h2]; apply: hf.
by rewrite ltnS in h2; rewrite h2 andbT; apply: leq_trans z0 (ltnW h1).
Qed.

Lemma harm_pow2 (j : nat) : j%:R / 2 <= \sum_(1 <= i < (2 ^ j).+1) 1 / i%:R :> rat.
Proof.
elim: j => [|j IH].
  by rewrite expn0 big_nat1 mul0r divr1 ler01.
have hle : (2 ^ j <= 2 ^ j.+1)%N by rewrite leq_pexp2l.
rewrite (@big_cat_nat _ _ _ (2 ^ j).+1) //= ?ltnS ?expn_gt0 //.
have h2 : 1 / 2 <= \sum_((2 ^ j).+1 <= i < (2 ^ j.+1).+1) 1 / i%:R :> rat.
  apply: le_trans (_ : \sum_((2 ^ j).+1 <= i < (2 ^ j.+1).+1) 1 / (2 ^ j.+1)%:R <= _).
    have e1 : (2 ^ j.+1 - 2 ^ j = 2 ^ j)%N by rewrite expnS mul2n -addnn addnK.
    rewrite sumr_const_nat subSS e1 -mulr_natr expnS natrM.
    have : (2 ^ j)%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n expn_gt0.
    move=> ?; rewrite -[X in _ <= X]mulr_natr le_eqVlt; apply/orP; left; apply/eqP; field.
  apply: ler_sum_nat => i /andP [h1 h3]; rewrite ltnS in h3.
  have i0 : (0 < i)%N by apply: leq_trans h1; apply: ltn0Sn.
  by rewrite !div1r lef_pV2 ?posrE ?ltr0n ?expn_gt0 // ler_nat.
have -> : j.+1%:R / 2 = j%:R / 2 + 1 / 2 :> rat by rewrite -addn1 natrD; field.
exact: lerD.
Qed.

Lemma harm_unbounded (C : rat) : exists n, C < \sum_(1 <= i < n.+1) 1 / i%:R.
Proof.
have := archi_boundP (normr_ge0 (C * 2)); set b := Num.bound _ => hb.
exists (2 ^ b)%N; apply: lt_le_trans (harm_pow2 b).
rewrite ltr_pdivlMr; last by apply: le_lt_trans (ler_norm _) hb.
lra.
Qed.

Lemma exists_small (c e : rat) : 0 < e -> exists N : nat, c / N.+1%:R < e.
Proof.
move=> he; have := archi_boundP (normr_ge0 (c / e)); set b := Num.bound _ => hb.
exists b; have h1 : c / e < b.+1%:R.
  by apply: le_lt_trans (ler_norm _) _; apply: lt_trans hb _; rewrite ltr_nat.
rewrite ltr_pdivrMr // in h1; rewrite ltr_pdivrMr ?ltr0n //; by rewrite mulrC.
Qed.

Lemma abel_bound_rseq (a : nat -> rat) (w : nat -> rseq) (B : rat) (n0 x : nat) :
  (n0 <= x)%N ->
  (forall y, (n0 <= y)%N -> (y <= x)%N -> `|\sum_(n0 <= n < y.+1) a n| <= B) ->
  (forall k n, (n0 <= n)%N -> (n < x)%N -> w n.+1 k <= w n k) ->
  (forall k n, (n0 <= n)%N -> (n <= x)%N -> 0 <= w n k) ->
  rle (rabs (rsum (fun n => rmul (cst (a n)) (w n)) (index_iota n0 x.+1))) (rmul (cst B) (w n0)).
Proof.
move=> hx hA hw hw0; apply: rle_of_ptwise => k.
exact: (abel_bound a (fun n => w n k) B n0 x hx hA (hw k) (hw0 k)).
Qed.

Lemma rinv_req {f g : rseq} : (forall k, 1 <= f k) -> (forall k, 1 <= g k) ->
  req f g -> req (rinv f) (rinv g).
Proof.
move=> hf hg h e he; apply: ev_mono (h _ he) => k hk; rewrite /rinv.
by apply: (inv_close ltr01 he (hf k) (hg k)); rewrite !mulr1.
Qed.

Lemma rinv_rsqrt_mul {d e : nat} : (0 < d)%N -> (0 < e)%N ->
  req (rinv (rsqrt (d * e)%N)) (rmul (rinv (rsqrt d)) (rinv (rsqrt e))).
Proof.
move=> hd he; apply: req_trans (rinv_req _ _ (rsqrt_mul d e)) _.
- by apply: rsqrt_ge1; rewrite muln_gt0 hd.
- by move=> k; rewrite /rmul; apply: mulr_ege1; apply: rsqrt_ge1.
- by apply: req_of_eq => k; rewrite /rinv /rmul invfM.
Qed.

Lemma rinv_rsqrt_eq {d : nat} : (0 < d)%N ->
  req (rinv (rsqrt d)) (rmul (cst d%:R^-1) (rsqrt d)).
Proof.
move=> hd; have hc := cauchy_mul (cauchy_cst d%:R^-1) (cauchy_rinv_rsqrt d).
have H := req_rmul_l hc (rsqrt_sqr d).
have hd' : d%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n.
apply: req_sym; apply: req_trans (req_trans _ H) _; apply: req_of_eq => k; rewrite /rmul /cst /rinv.
- by have := rsqrt_neq0 hd k => ?; field.
- by have := rsqrt_neq0 hd k => ?; field.
Qed.

Lemma geom_sum {c : int} (j : nat) : `|c| <= 1 ->
  0 <= \sum_(i < j.+1) c ^+ i /\ (~~ odd j -> 1 <= \sum_(i < j.+1) c ^+ i).
Proof.
move=> hc; have [c0|c0] := lerP 0 c.
  have h : 1 <= \sum_(i < j.+1) c ^+ i.
    rewrite big_ord_recl expr0 lerDl; apply: sumr_ge0 => i _; exact: exprn_ge0.
  by split; [apply: le_trans ler01 h | move=> _].
have -> : c = -1.
  apply: le_anti; apply/andP; split; first by rewrite -ltzD1 addNr.
  by move: hc; rewrite ler_norml => /andP [].
have -> : \sum_(i < j.+1) (-1) ^+ i = (~~ odd j)%:R :> int.
  elim: j => [|j IH]; first by rewrite big_ord1 expr0.
  by rewrite big_ord_recr /= IH -signr_odd /=; case: (odd j).
by case: (odd j).
Qed.

Section AbstractChar.

Variable chi : nat -> int.
Variable M : nat.
Hypothesis M_gt0 : (0 < M)%N.
Hypothesis chi_mul : forall m n, chi (m * n)%N = chi m * chi n.
Hypothesis chi_le1 : forall n, `|chi n| <= 1.
Hypothesis chi1 : chi 1 = 1.
Hypothesis chi_window : forall x y, `|\sum_(x.+1 <= n < y.+1) (chi n)%:~R| <= M%:R :> rat.

Local Abbreviation isq n := (rinv (rsqrt n)).

Lemma chi_le1_rat n : `|(chi n)%:~R : rat| <= 1.
Proof using chi_le1. by have := chi_le1 n; rewrite -(ler_int rat) intr_norm. Qed.

Lemma chi_abel {w : nat -> rat} {x0 : nat} (X : nat) :
  (forall n, (x0 < n)%N -> w n.+1 <= w n) -> (forall n, (x0 < n)%N -> 0 <= w n) ->
  `|\sum_(x0.+1 <= n < X.+1) (chi n)%:~R * w n| <= M%:R * w x0.+1.
Proof using chi_window.
move=> hw hw0; case: (leqP x0.+1 X) => hX.
  apply: abel_bound => //.
  - by move=> n hn _; apply: hw.
  - by move=> n hn _; apply: hw0.
rewrite big_geq ?normr0 //; apply: mulr_ge0; [exact: ler0n | exact: hw0].
Qed.

Lemma chi_abel_isq (x0 X : nat) k :
  `|\sum_(x0.+1 <= n < X.+1) (chi n)%:~R * isq n k| <= M%:R * isq x0.+1 k.
Proof using chi_window.
apply: (chi_abel (w := fun n => isq n k)) => n hn.
- by apply: rinv_rsqrt_mono => //; apply: leq_trans hn.
- exact: rinv_rsqrt_ge0.
Qed.

Lemma chi_window_sqrt (x y : nat) :
  rle (rabs (rsum (fun n => rmul (cst (chi n)%:~R) (isq n)) (index_iota x.+1 y.+1)))
      (rmul (cst M%:R) (isq x.+1)).
Proof using chi_window. by apply: rle_of_ptwise => k; apply: chi_abel_isq. Qed.

(** ** The series L(1, chi) *)

Definition Lchi : rseq := fun k => \sum_(1 <= n < k.+1) (chi n)%:~R / n%:R.

Lemma Lchi_diff {x k : nat} : (x <= k)%N ->
  `|Lchi k - \sum_(1 <= n < x.+1) (chi n)%:~R / n%:R| <= M%:R / x.+1%:R.
Proof using chi_window.
move=> hk; rewrite /Lchi (@big_cat_nat _ _ _ x.+1) //=.
have -> : forall A B : rat, A + B - A = B by move=> A B; ring.
apply: (chi_abel (w := fun n => n%:R^-1)) => n hn.
- have n0 : (0 < n)%N by apply: leq_trans hn.
  by rewrite lef_pV2 ?posrE ?ltr0n // ler_nat.
- by rewrite invr_ge0 ler0n.
Qed.

Lemma Lchi_tail (x : nat) :
  rle (rabs (rsub Lchi (cst (\sum_(1 <= n < x.+1) (chi n)%:~R / n%:R))))
      (cst (M%:R / x.+1%:R)).
Proof using chi_window. by apply: rle_of_eventually; exists x => k hk; apply: Lchi_diff. Qed.

Lemma Lchi_cauchy : cauchy Lchi.
Proof using chi_window.
move=> e he; have he2 : 0 < e / 2 by lra.
have [N hN] := exists_small M%:R (e / 2) he2.
exists N => m n hm hn; have h1 := Lchi_diff hm; have h2 := Lchi_diff hn.
move: h1 h2; set S := \sum_(1 <= i < N.+1) _ => h1 h2.
have h3 : `|Lchi m - Lchi n| <= `|Lchi m - S| + `|Lchi n - S|.
  by rewrite (distrC (Lchi n)); apply: ler_distD.
apply: le_lt_trans h3 _; apply: le_lt_trans (lerD h1 h2) _.
by apply: lt_le_trans (ltrD hN hN) _; lra.
Qed.

(** ** Divisor sums of chi *)

Definition F (n : nat) : int := \sum_(d <- divisors n) chi d.

Lemma chi_exp p i : chi (p ^ i)%N = chi p ^+ i.
Proof using chi_mul chi1.
by elim: i => [|i IH]; [rewrite expn0 chi1 expr0 | rewrite expnS chi_mul IH exprS].
Qed.

Lemma F1 : F 1 = 1.
Proof using chi1. by rewrite /F (_ : divisors 1 = [:: 1%N]) // big_seq1 chi1. Qed.

Lemma F_pfactor p j m : prime p -> coprime p m -> (0 < m)%N ->
  F (m * p ^ j)%N = (\sum_(i < j.+1) chi p ^+ i) * F m.
Proof using chi_mul chi1.
move=> pp cop m0.
have p0 := prime_gt0 pp.
have hpos : (0 < m * p ^ j)%N by rewrite muln_gt0 m0 expn_gt0 p0.
have copd : forall d, d \in divisors m -> coprime p d.
  by move=> d; rewrite -dvdn_divisors // => hd; apply: coprime_dvdr hd cop.
have logpd : forall i d, coprime p d -> logn p (p ^ i * d)%N = i.
  by move=> i d hd; rewrite mulnC logn_Gauss // pfactorK.
rewrite /F (perm_big [seq (p ^ i * d)%N | i <- index_iota 0 j.+1, d <- divisors m]); last first.
  rewrite big_flatten big_map big_mkord mulr_suml; apply: eq_bigr => i _.
  rewrite big_map mulr_sumr; apply: eq_bigr => d _; by rewrite chi_mul chi_exp.
apply: uniq_perm.
- exact: divisors_uniq.
- apply: allpairs_uniq; [exact: iota_uniq | exact: divisors_uniq |].
  move=> [i1 d1] [i2 d2] /allpairsP [[i1' d1'] [_ hd1 [-> ->]]].
  move=> /allpairsP [[i2' d2'] [_ hd2 [-> ->]]] /= e; simpl in hd1, hd2.
  have ei : i1' = i2' by rewrite -(logpd i1' d1' (copd _ hd1)) e logpd // copd.
  rewrite -ei in e *; congr (_, _).
  have hp : (0 < p ^ i1')%N by rewrite expn_gt0 p0.
  by apply/eqP; rewrite -(eqn_pmul2l hp) e.
move=> z; rewrite -dvdn_divisors //; apply/idP/allpairsP.
- move=> hz; have z0 := dvdn_gt0 hpos hz.
  have [d cd ez] := pfactor_coprime pp z0.
  exists (logn p z, d) => /=; split.
  + rewrite mem_index_iota /= ltnS.
    have := dvdn_leq_log p hpos hz; rewrite logn_Gauss // pfactorK //.
  + have cdp : coprime d (p ^ j) by rewrite coprime_sym coprimeXl.
    rewrite -dvdn_divisors // -(Gauss_dvdl _ cdp); apply: dvdn_trans _ hz.
    by rewrite {1}ez; apply: dvdn_mulr.
  + by rewrite mulnC.
- move=> [[i d] /= [hi hd ->]]; rewrite mulnC; apply: dvdn_mul.
  + by rewrite dvdn_divisors.
  + by apply: dvdn_exp2l; move: hi; rewrite mem_index_iota ltnS.
Qed.

Lemma F_ge0 n : (0 < n)%N -> 0 <= F n.
Proof using chi_mul chi_le1 chi1.
elim: n {-2}n (leqnn n) => [|n IH] m hm m0; first by move: m0; rewrite leqn0 in hm; rewrite (eqP hm).
case: (ltngtP m 1) => [hlt|hm1|->]; first by rewrite ltnNge m0 in hlt.
- have pp := pdiv_prime hm1; set p := pdiv m in pp.
  have [q cop eq] := pfactor_coprime pp m0.
  have q0 : (0 < q)%N by move: m0; rewrite eq muln_gt0 => /andP [].
  have j0 : (0 < logn p m)%N by rewrite logn_gt0 mem_primes pp m0 pdiv_dvd.
  have hqm : (q < m)%N.
    rewrite {1}eq; apply: ltn_Pmulr => //; apply: leq_trans (prime_gt1 pp) _.
    by rewrite -{1}(expn1 p); apply: leq_pexp2l => //; apply: prime_gt0.
  rewrite eq F_pfactor //; apply: mulr_ge0.
  + by case: (geom_sum (logn p m) (chi_le1 p)).
  + by apply: IH => //; rewrite -ltnS; apply: leq_trans hqm hm.
- by rewrite F1.
Qed.

Lemma F_square_ge1 m : (0 < m)%N -> 1 <= F (m * m).
Proof using chi_mul chi_le1 chi1.
elim: m {-2}m (leqnn m) => [|n IH] m hm m0; first by move: m0; rewrite leqn0 in hm; rewrite (eqP hm).
case: (ltngtP m 1) => [hlt|hm1|->]; first by rewrite ltnNge m0 in hlt.
- have pp := pdiv_prime hm1; set p := pdiv m in pp.
  have [q cop eq] := pfactor_coprime pp m0.
  set j := logn p m in eq.
  have q0 : (0 < q)%N by move: m0; rewrite eq muln_gt0 => /andP [].
  have j0 : (0 < j)%N by rewrite logn_gt0 mem_primes pp m0 pdiv_dvd.
  have hqm : (q < m)%N.
    rewrite {1}eq; apply: ltn_Pmulr => //; apply: leq_trans (prime_gt1 pp) _.
    by rewrite -{1}(expn1 p); apply: leq_pexp2l => //; apply: prime_gt0.
  have -> : (m * m = (q * q) * p ^ (j + j))%N by rewrite {1 2}eq expnD mulnACA.
  rewrite F_pfactor ?coprimeMr ?cop ?muln_gt0 ?q0 //; apply: mulr_ege1.
  + by case: (geom_sum (j + j) (chi_le1 p)) => _; apply; rewrite addnn odd_double.
  + by apply: IH => //; rewrite -ltnS; apply: leq_trans hqm hm.
- by rewrite mul1n F1.
Qed.

(** ** The hyperbola method *)

Definition divsum (x : nat) : rseq :=
  rsum (fun n => rmul (cst (F n)%:~R) (isq n)) (iota 1 x).

Definition hypA (x : nat) : rseq :=
  rsum (fun d => rmul (rmul (cst (chi d)%:~R) (isq d)) (G (x %/ d)%N))
       (index_iota 1 (Nat.sqrt x).+1).

Definition hypB (x : nat) : rseq :=
  rsum (fun e => rmul (isq e)
                   (rsum (fun d => rmul (cst (chi d)%:~R) (isq d))
                         (index_iota (Nat.sqrt x).+1 (x %/ e)%N.+1)))
       (index_iota 1 (Nat.sqrt x).+1).

Lemma divsum_pt (x : nat) k : divsum x k =
  \sum_(1 <= d < x.+1) \sum_(1 <= e < (x %/ d)%N.+1) (chi d)%:~R * isq (d * e)%N k.
Proof.
rewrite /divsum /rsum iota1E -pair_sum_divisors; apply: eq_big_nat => n /andP [hn _].
rewrite /rmul /cst /F rmorph_sum /= mulr_suml; apply: eq_big_seq => d hd.
by rewrite -dvdn_divisors // in hd; rewrite mulnC divnK.
Qed.

Lemma isqrt_facts (x : nat) :
  [/\ (Nat.sqrt x * Nat.sqrt x <= x)%N, (x < (Nat.sqrt x).+1 * (Nat.sqrt x).+1)%N
    & (Nat.sqrt x <= x)%N].
Proof.
have [h1 h2] := isqrt_spec x; split => //.
case: (posnP (Nat.sqrt x)) => [->|h0] //.
by apply: leq_trans h1; rewrite leq_pmulr.
Qed.

Lemma divsum_hyperbola (x : nat) : req (divsum x) (radd (hypA x) (hypB x)).
Proof.
set y := Nat.sqrt x; have [hy1 hy2 hyx] := isqrt_facts x; rewrite -/y in hy1 hy2 hyx.
pose Apt := rsum (fun d => rsum (fun e => rmul (cst (chi d)%:~R) (isq (d * e)%N))
                                (index_iota 1 (x %/ d)%N.+1)) (index_iota 1 y.+1).
pose Bpt := rsum (fun e => rsum (fun d => rmul (cst (chi d)%:~R) (isq (d * e)%N))
                                (index_iota y.+1 (x %/ e)%N.+1)) (index_iota 1 y.+1).
apply: req_trans (_ : req _ (radd Apt Bpt)) _.
  apply: req_of_eq => k; rewrite divsum_pt /radd /Apt /Bpt /rsum /rmul /cst.
  rewrite (@big_cat_nat _ _ _ y.+1) //=; congr (_ + _).
  exact: (sum_swap_tail (fun d e => (chi d)%:~R * isq (d * e)%N k)).
apply: req_radd.
- apply: rsum_ext_in => d; rewrite mem_index_iota => /andP [hd _].
  apply: req_trans (_ : req _ (rsum (fun e => rmul (cst (chi d)%:~R) (rmul (isq d) (isq e)))
                                    (index_iota 1 (x %/ d)%N.+1))) _.
    apply: rsum_ext_in => e; rewrite mem_index_iota => /andP [he _].
    by apply: req_rmul_cst; apply: rinv_rsqrt_mul.
  apply: req_of_eq => k; rewrite /rsum /rmul /cst /G /rsum iota1E mulr_sumr.
  by apply: eq_bigr => e _; ring.
- apply: rsum_ext_in => e; rewrite mem_index_iota => /andP [he _].
  apply: req_trans (_ : req _ (rsum (fun d => rmul (cst (chi d)%:~R) (rmul (isq d) (isq e)))
                                    (index_iota y.+1 (x %/ e)%N.+1))) _.
    apply: rsum_ext_in => d; rewrite mem_index_iota => /andP [hd _].
    by apply: req_rmul_cst; apply: rinv_rsqrt_mul => //; apply: leq_trans hd.
  apply: req_of_eq => k; rewrite /rsum /rmul /cst mulr_sumr.
  by apply: eq_bigr => d _; ring.
Qed.

(** Lower bound: the squares contribute the harmonic sum. *)

Lemma divsum_lower (x : nat) :
  rle (cst (\sum_(1 <= m < (Nat.sqrt x).+1) 1 / m%:R)) (divsum x).
Proof using chi_mul chi_le1 chi1.
have [hy1 _ _] := isqrt_facts x.
apply: rle_of_ptwise => k; rewrite /divsum /rsum /cst iota1E.
apply: le_trans (sum_squares_le (f := fun n => (F n)%:~R * isq n k) _ hy1); last first.
  move=> n /andP [hn _]; apply: mulr_ge0; last exact: rinv_rsqrt_ge0.
  by rewrite ler0z; apply: F_ge0.
apply: ler_sum_nat => m /andP [hm _] /=.
rewrite /rinv rsqrt_square div1r -[X in X <= _]mul1r; apply: ler_wpM2r.
  by rewrite invr_ge0 ler0n.
by rewrite ler1z; apply: F_square_ge1.
Qed.

(** Upper bound. *)

Definition delta (e : nat) : rseq :=
  rsub (rmul (cst 2) (rsub (rsqrt e) (rsqrt e.-1))) (isq e).

Lemma E_delta (z : nat) k : E z k = - \sum_(1 <= e < z.+1) delta e k.
Proof.
elim: z => [|z IH]; first by rewrite E0 big_geq // oppr0.
rewrite big_nat_recr //= opprD -IH /E /delta /rsub /rmul /cst G_succ_pt /=; lra.
Qed.

Lemma delta_ge0 {e : nat} : (0 < e)%N -> rle (cst 0) (delta e).
Proof.
case: e => // z _ eps heps; apply: ev_mono (rinv_rsqrt_le z eps heps) => k.
by rewrite /delta /rsub /rmul /cst /=; lra.
Qed.

Lemma sum_delta_le2 (x : nat) :
  rle (rsum (fun e => rabs (delta e)) (index_iota 1 x.+1)) (cst 2).
Proof.
apply: rle_trans (_ : rle _ (rsum delta (index_iota 1 x.+1))) _.
  apply: rle_rsum => e; rewrite mem_index_iota => /andP [he _].
  apply/rabs_rle; split; last exact: rle_refl.
  move=> eps heps; have heps2 : 0 < eps / 2 by lra.
  by apply: ev_mono (delta_ge0 he _ heps2) => k; rewrite /ropp /cst; lra.
move=> eps heps; apply: ev_mono (E_ge x eps heps) => k.
by rewrite /rsum /cst E_delta; lra.
Qed.

Definition A1 (x : nat) : rseq :=
  rsum (fun d => rmul (rmul (cst (chi d)%:~R) (isq d)) (rmul (cst 2) (rsqrt (x %/ d)%N)))
       (index_iota 1 (Nat.sqrt x).+1).

Definition A2 (x : nat) : rseq :=
  rsum (fun d => rmul (rmul (cst (chi d)%:~R) (isq d)) (E (x %/ d)%N))
       (index_iota 1 (Nat.sqrt x).+1).

Lemma hypA_split (x : nat) k : hypA x k = A1 x k + A2 x k.
Proof.
rewrite /hypA /A1 /A2 /rsum -big_split; apply: eq_bigr => d _.
by rewrite /E /rmul /rsub /cst /=; ring.
Qed.

Lemma A2_bound (x : nat) : rle (rabs (A2 x)) (cst (2 * M%:R)).
Proof using chi_window.
set y := Nat.sqrt x.
apply: rle_trans (_ : rle _ (rmul (cst M%:R) (rsum (fun e => rabs (delta e)) (index_iota 1 x.+1)))) _.
  apply: rle_of_ptwise => k; rewrite /rabs /A2 -/y /rsum /rmul /cst.
  have -> : \sum_(1 <= d < y.+1) (chi d)%:~R * isq d k * E (x %/ d)%N k =
            - \sum_(1 <= e < x.+1) delta e k *
                \sum_(1 <= d < (minn y (x %/ e)%N).+1) (chi d)%:~R * isq d k.
    rewrite -(sum_swap_min (fun d => (chi d)%:~R * isq d k) (fun e => delta e k)) -sumrN.
    by apply: eq_bigr => d _; rewrite E_delta mulrN.
  rewrite normrN mulr_sumr; apply: le_trans (ler_norm_sum _ _ _) _.
  apply: ler_sum => e _; rewrite normrM mulrC; apply: ler_wpM2r; first exact: normr_ge0.
  have := chi_abel_isq 0 (minn y (x %/ e)%N) k.
  by rewrite /rinv rsqrt1 invr1 mulr1.
apply: rle_trans (rle_rmul_cst _ (ler0n _ M) (sum_delta_le2 x)) _.
by apply: rle_of_ptwise => k; rewrite /rmul /cst mulrC.
Qed.

Lemma hypB_bound (x : nat) : rle (rabs (hypB x)) (cst (2 * M%:R)).
Proof using chi_window.
set y := Nat.sqrt x.
apply: rle_trans (_ : rle _ (rmul (cst M%:R) (rmul (isq y.+1) (G y)))) _.
  apply: rle_of_ptwise => k; rewrite /rabs /hypB -/y /rsum /rmul /cst /G /rsum iota1E.
  apply: le_trans (ler_norm_sum _ _ _) _; rewrite !mulr_sumr; apply: ler_sum => e _.
  rewrite normrM ger0_norm ?rinv_rsqrt_ge0 //.
  have h := chi_abel_isq y (x %/ e)%N k.
  have -> : M%:R * (isq y.+1 k * isq e k) = isq e k * (M%:R * isq y.+1 k) by ring.
  by apply: ler_wpM2l; [apply: rinv_rsqrt_ge0 | apply: h].
have H : rle (rmul (isq y.+1) (G y)) (cst 2).
  apply: rle_trans (rle_rmul_l (h := isq y.+1) _ _ _ _ (G_le y)) _.
  - by apply: rle_of_ptwise => k; apply: rinv_rsqrt_ge0.
  - exact: cauchy_rinv_rsqrt.
  - exact: cauchy_G.
  - exact: cauchy_mul (cauchy_cst 2) (rsqrt_cauchy y).
  apply: rle_of_ptwise => k; rewrite /rmul /cst.
  have h1 := rsqrt_rinv (ltn0Sn y) k.
  have h2 : isq y.+1 k * rsqrt y k <= isq y.+1 k * rsqrt y.+1 k.
    by apply: ler_wpM2l; [apply: rinv_rsqrt_ge0 | apply: rsqrt_mono].
  rewrite mulrC in h1; rewrite mulrCA; lra.
apply: rle_trans (rle_rmul_cst _ (ler0n _ M) H) _.
by apply: rle_of_ptwise => k; rewrite /rmul /cst mulrC.
Qed.

Lemma isq_floor_div {x d : nat} : (1 <= d <= x)%N ->
  rle (rabs (rsub (rmul (isq d) (rsqrt (x %/ d)%N)) (rmul (cst d%:R^-1) (rsqrt x)))) (isq x).
Proof.
move=> hdx; have /andP [hd _] := hdx.
apply: req_rle_trans (_ : req _ (rmul (cst d%:R^-1)
         (rabs (rsub (rsqrt x) (rmul (rsqrt d) (rsqrt (x %/ d)%N)))))) _.
  apply: req_trans (req_rabs (req_rsub (req_rmul_r (rsqrt_cauchy _) (rinv_rsqrt_eq hd))
                                       (req_refl _))) _.
  apply: req_of_eq => k; rewrite /rabs /rsub /rmul /cst.
  set a := rsqrt d k; set b := rsqrt (x %/ d)%N k; set c := rsqrt x k.
  have -> : d%:R^-1 * a * b - d%:R^-1 * c = d%:R^-1 * - (c - a * b) by ring.
  by rewrite normrM normrN ger0_norm // invr_ge0 ler0n.
apply: rle_trans (rle_rmul_cst _ _ (rsqrt_floor_div x d hdx)) _; first by rewrite invr_ge0 ler0n.
apply: rle_of_ptwise => k; rewrite /rmul /rdiv /cst /rinv mulrA mulVf ?mul1r //.
by rewrite pnatr_eq0 -lt0n.
Qed.

Definition Spart (y : nat) : rat := \sum_(1 <= n < y.+1) (chi n)%:~R / n%:R.

Lemma A1_main (x : nat) :
  rle (rabs (rsub (A1 x) (rmul (rmul (cst 2) (rsqrt x)) (cst (Spart (Nat.sqrt x)))))) (cst 2).
Proof using chi_le1.
set y := Nat.sqrt x; have [_ _ hyx] := isqrt_facts x; rewrite -/y in hyx.
apply: rle_trans (_ : rle _ (rsum (fun d => rmul (cst 2) (rabs (rsub (rmul (isq d) (rsqrt (x %/ d)%N))
                    (rmul (cst d%:R^-1) (rsqrt x))))) (index_iota 1 y.+1))) _.
  apply: rle_of_ptwise => k; rewrite /rabs /rsub /rmul /cst /A1 -/y /rsum /Spart mulr_sumr -sumrB.
  apply: le_trans (ler_norm_sum _ _ _) _; apply: ler_sum => d _.
  set X := isq d k * rsqrt (x %/ d)%N k - d%:R^-1 * rsqrt x k.
  have -> : (chi d)%:~R * isq d k * (2 * rsqrt (x %/ d)%N k) -
            2 * rsqrt x k * ((chi d)%:~R / d%:R) = (2 * (chi d)%:~R) * X.
    by rewrite /X; ring.
  rewrite normrM; apply: ler_wpM2r; first exact: normr_ge0.
  by rewrite normrM ger0_norm //; have := chi_le1_rat d; lra.
apply: rle_trans (_ : rle _ (rsum (fun d => rmul (cst 2) (isq x)) (index_iota 1 y.+1))) _.
  apply: rle_rsum => d; rewrite mem_index_iota => /andP [hd hdy].
  apply: rle_rmul_cst => //; apply: isq_floor_div.
  by rewrite hd /=; apply: leq_trans hyx; rewrite -ltnS.
apply: rle_of_ptwise => k; rewrite /rsum /rmul /cst sumr_const_nat subSS subn0.
have h : y%:R * isq x k <= 1.
  case: (posnP x) => hx.
    by rewrite /y hx /= mul0r ler01.
  have hpos : 0 < rsqrt x k by apply: lt_le_trans ltr01 (rsqrt_ge1 hx k).
  by rewrite /rinv ler_pdivrMr // mul1r; apply: rsqrt_isqrt.
have -> : (2 * isq x k) *+ y = 2 * (y%:R * isq x k) by rewrite -mulr_natr; ring.
lra.
Qed.

Lemma A1_L (x : nat) :
  rle (rmul (rmul (cst 2) (rsqrt x)) (cst (Spart (Nat.sqrt x))))
      (radd (rmul (rmul (cst 2) (rsqrt x)) Lchi) (cst (2 * M%:R))).
Proof using chi_window.
set y := Nat.sqrt x; set h := rmul (cst 2) (rsqrt x).
have hc : cauchy h := cauchy_mul (cauchy_cst 2) (rsqrt_cauchy x).
have h0 : rle (cst 0) h.
  by apply: rle_of_ptwise => k; rewrite /h /rmul /cst; apply: mulr_ge0; [lra | apply: rsqrt_ge0].
have hT : rle (rsub (cst (Spart y)) Lchi) (cst (M%:R / y.+1%:R)).
  move=> e he; apply: ev_mono (Lchi_tail y e he) => k.
  rewrite /rabs /rsub /cst /Spart => H; move: H; set c := M%:R / y.+1%:R => H; nlra.
have := rle_rmul_l h0 hc (cauchy_sub (cauchy_cst _) Lchi_cauchy) (cauchy_cst _) hT.
move=> H e he; apply: ev_mono (H e he) => k; rewrite /h /rmul /rsub /radd /cst => Hk.
have hlt := rsqrt_lt_isqrt1 x k; rewrite -/y in hlt.
have h3 : rsqrt x k / y.+1%:R <= 1 by rewrite ler_pdivrMr ?ltr0n // mul1r; apply: ltW.
have h4 : M%:R * (rsqrt x k / y.+1%:R) <= M%:R * 1 := ler_wpM2l (ler0n _ _) h3.
have e1 : 2 * rsqrt x k * (M%:R / y.+1%:R) = 2 * (M%:R * (rsqrt x k / y.+1%:R)) by ring.
rewrite mulr1 in h4; rewrite mulrBr e1 in Hk.
move: h4 Hk; set t := M%:R * _ => h4 Hk; lra.
Qed.

Lemma divsum_upper : exists C : rat, forall x,
  rle (rsum (fun n => rmul (cst (F n)%:~R) (isq n)) (iota 1 x))
      (radd (rmul (rmul (cst 2) (rsqrt x)) Lchi) (cst C)).
Proof using chi_le1 chi_window.
exists (2 + 6 * M%:R) => x.
apply: req_rle_trans (divsum_hyperbola x) _.
have H1 := A1_main x; have H2 := A1_L x; have H3 := A2_bound x; have H4 := hypB_bound x.
move=> e he; have he4 : 0 < e / 4 by lra.
apply: ev_mono (evI (evI (H1 _ he4) (H2 _ he4)) (evI (H3 _ he4) (H4 _ he4))).
move=> k [[h1 h2] [h3 h4]]; move: h1 h2 h3 h4.
rewrite /radd hypA_split /rabs /rsub /rmul /cst => h1 h2 h3 h4; nlra.
Qed.

(** ** Positivity of L(1, chi) *)

Lemma Lchi_pos : rlt (cst 0) Lchi.
Proof using chi_mul chi_le1 chi1 chi_window.
case: (rlt_or_rle (cauchy_cst 0) Lchi_cauchy) => // hL; exfalso.
have [C hC] := divsum_upper.
have hb : forall n, \sum_(1 <= i < n.+1) 1 / i%:R <= C.
  move=> n; apply/rle_cst; set x := (n * n)%N.
  have := divsum_lower x; rewrite /x isqrt_square -/x => hlo.
  apply: rle_trans hlo _; apply: rle_trans (hC x) _.
  have hc : cauchy (rmul (cst 2) (rsqrt x)) := cauchy_mul (cauchy_cst 2) (rsqrt_cauchy x).
  have h0 : rle (cst 0) (rmul (cst 2) (rsqrt x)).
    by apply: rle_of_ptwise => k; rewrite /rmul /cst; apply: mulr_ge0; [lra | apply: rsqrt_ge0].
  have := rle_rmul_l h0 hc Lchi_cauchy (cauchy_cst 0) hL.
  move=> H e he; apply: ev_mono (H e he) => k; rewrite /radd /rmul /cst mulr0; lra.
have [n hn] := harm_unbounded C.
by move: (hb n); rewrite leNgt hn.
Qed.

Lemma Lchi_ge : exists c : rat, 0 < c /\ rle (cst c) Lchi.
Proof using chi_mul chi_le1 chi1 chi_window.
have [e [he [N hN]]] := Lchi_pos; exists e; split => //.
by apply: rle_of_eventually; exists N => k hk; have := hN k hk; rewrite /cst add0r.
Qed.

End AbstractChar.
