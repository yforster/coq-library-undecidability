(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Analytic core, part 2 (PLAN.md Phase 4, task D4b; DIRICHLET_DESIGN.md,
   Sec. 3 steps 4-6 and Sec. 7). Combines the logarithm of RLog.v with
   L(1, chi) > 0 of DirichletL.v.

   Contents.
   1. Generic helpers: [req_cmul_rdiv] (transport of [req] through
      [c * (f / a)]), [rabs_bound_div] (cancel a factor bounded below by a
      positive constant, with an explicit constant), [sum_le_count]
      (sums of at most three terms of size [<= 1]).
   2. Section [AbstractChar2], with exactly the hypotheses of Section
      [AbstractChar] of DirichletL.v:
      - [sum_chi_rlog_bounded]: |sum_(n<=x) chi(n) log n / n| <= C
        (Abel summation with the pointwise decreasing Riemann weights
        [lrs n k / n], n >= 4);
      - [chi_rlog_conv]: the convolution identity (pointwise)
        sum_(n<=x) chi(n) log n / n
          = sum_(d<=x) chi(d) Lambda(d)/d * sum_(e<=x/d) chi(e)/e;
      - [conv_err_pt]: |L * B(x) - sum_(n<=x) chi(n) log n / n|
        <= M/x * psi(x) (pointwise, for k >= x);
      - [sum_chi_vmangoldt_bounded]: |sum_(d<=x) chi(d) Lambda(d)/d| <= C
        (Chebyshev [psi_le] and [Lchi_ge]);
      - [sum_chi_rlog_primes_bounded]: |sum_(p<=x prime) chi(p) log p / p|
        <= C (prime powers removed by [prime_pow_tail_pt]);
      - Cauchy-ness of the sums: [cauchy_chi_rlog_sum],
        [cauchy_chi_vmangoldt_sum].
      The three [*_bounded] theorems are proved [using] all six Section
      hypotheses, so after the Section they take [chi M M_gt0 chi_mul
      chi_le1 chi1 chi_window] (the interface used by PrimePatterns.v).

   Arguments of lemmas are implicit exactly when they occur in a
   hypothesis. *)

From Stdlib Require Import PeanoNat Setoid Morphisms Classical_Prop.
From mathcomp Require Import boot order algebra.
Import Order.TTheory GRing.Theory Num.Theory.
From Undecidability.H10.Rational Require Import RSeq RLog DirichletL.

Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(** * 1. Generic helpers *)

Lemma req_cmul_rdiv (c a : rat) {f g : rseq} : req f g ->
  req (rmul (cst c) (rdiv f (cst a))) (rmul (cst c) (rdiv g (cst a))).
Proof.
move=> h; apply: req_trans (req_trans _ (req_rmul_cst (c / a) h)) _;
  by apply: req_of_eq => k; rewrite /rmul /rdiv /cst mulrA mulrAC.
Qed.

Lemma rabs_bound_div {h f : rseq} {c C : rat} :
  rle (rabs (rmul h f)) (cst C) -> rle (cst c) h -> 0 < c ->
  rle (rabs f) (cst (2 * (C + 1) / c)).
Proof.
move=> H hc c0; have c2 : 0 < c / 2 by lra.
apply: rle_of_eventually.
have [N0 hN0] := hc _ c2; have [N1 hN1] := H 1 ltr01.
exists (N0 + N1)%N => k hk.
have h0 := hN0 k (le_addl_trans hk); rewrite /cst in h0.
have := hN1 k (le_addr_trans hk); rewrite /rabs /rmul /cst normrM => H1.
have hk0 : c / 2 <= h k by lra.
rewrite (ger0_norm (le_trans (ltW c2) hk0)) in H1.
rewrite /rabs ler_pdivlMr //.
have : `|f k| * (c / 2) <= `|f k| * h k by apply: ler_wpM2l.
move: H1; set a := `|f k|; set b := h k => H1 H2.
have : a * b <= C + 1 by rewrite mulrC.
lra.
Qed.

Lemma sum_le_count (F : nat -> rat) (y : nat) : (y <= 4)%N ->
  (forall n, (1 <= n < y)%N -> `|F n| <= 1) -> `|\sum_(1 <= n < y) F n| <= 3.
Proof.
move=> hy hF; apply: le_trans (ler_norm_sum _ _ _) _.
rewrite big_nat_cond; apply: le_trans (ler_sum _ (fun n hn => hF n (andP hn).1)) _.
rewrite -big_nat_cond sumr_const_nat.
have h : (y - 1 <= 3)%N by rewrite leq_subLR.
apply: le_trans (_ : (y - 1)%:R <= 3%:R) _; first by rewrite ler_nat.
lra.
Qed.

(* ------------------------------------------------------------------ *)
(** * 2. The analytic core for one character *)

Section AbstractChar2.

Variable chi : nat -> int.
Variable M : nat.
Hypothesis M_gt0 : (0 < M)%N.
Hypothesis chi_mul : forall m n, chi (m * n)%N = chi m * chi n.
Hypothesis chi_le1 : forall n, `|chi n| <= 1.
Hypothesis chi1 : chi 1 = 1.
Hypothesis chi_window : forall x y, `|\sum_(x.+1 <= n < y.+1) (chi n)%:~R| <= M%:R :> rat.

Local Abbreviation chr n := ((chi n)%:~R : rat).

Lemma cauchy_chi_rlog_sum (s : seq nat) :
  cauchy (rsum (fun p => rmul (cst (chi p)%:~R) (rdiv (rlog p) (cst p%:R))) s).
Proof. by apply: cauchy_rsum => p _; apply: cauchy_mul (cauchy_cst _) (rlog_div_cauchy p). Qed.

Lemma cauchy_chi_vmangoldt_sum (s : seq nat) :
  cauchy (rsum (fun d => rmul (cst (chi d)%:~R) (rdiv (vmangoldt d) (cst d%:R))) s).
Proof. by apply: cauchy_rsum => d _; apply: cauchy_mul (cauchy_cst _) (vmangoldt_div_cauchy d). Qed.

(** ** Step 4: the sum of chi(n) log n / n is bounded *)

Lemma lrs_div_le1 (n : nat) k : lrs n k / n%:R <= 1.
Proof.
case: n => [|n]; first by rewrite invr0 mulr0.
rewrite ler_pdivrMr ?ltr0n // mul1r.
exact: le_trans (lrs_le_harm_pt _ k) (harm_le_nat _).
Qed.

Lemma lrs_div_ge0 (n : nat) k : 0 <= lrs n k / n%:R.
Proof. by apply: divr_ge0; [apply: lrs_ge0 | apply: ler0n]. Qed.

Lemma sum_chi_lrs_pt (x : nat) k :
  `|\sum_(1 <= n < x.+1) chr n * (lrs n k / n%:R)| <= 3 + M%:R.
Proof using chi_le1 chi_window.
have hF : forall n, `|chr n * (lrs n k / n%:R)| <= 1.
  move=> n; rewrite normrM (ger0_norm (lrs_div_ge0 n k)).
  have := chi_le1_rat chi chi_le1 n; have := lrs_div_le1 n k; have := lrs_div_ge0 n k.
  set a := `|_|; set b := lrs n k / _ => h0 h1 h2.
  by rewrite -[1]mulr1; apply: ler_pM => //; apply: normr_ge0.
have hM : 0 <= M%:R :> rat by apply: ler0n.
case: (leqP x 3) => hx.
  by apply: le_trans (sum_le_count _ x.+1 hx (fun n _ => hF n)) _; lra.
rewrite (@big_cat_nat _ _ _ 4) //=; first by apply: ltnW.
apply: le_trans (ler_normD _ _) _; apply: lerD.
  by apply: sum_le_count => // n _; apply: hF.
have := chi_abel chi M chi_window (w := fun n => lrs n k / n%:R) (x0 := 3) x.
move=> H; apply: le_trans (H _ _) _.
- by move=> n hn; apply: lrs_div_decr.
- by move=> n _; apply: lrs_div_ge0.
- by rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l => //; apply: lrs_div_le1.
Qed.

Lemma sum_chi_rlog_bounded : exists C : rat, forall x,
  rle (rabs (rsum (fun n => rmul (cst (chi n)%:~R) (rdiv (rlog n) (cst n%:R))) (iota 1 x))) (cst C).
Proof using M_gt0 chi_mul chi_le1 chi1 chi_window.
exists (3 + M%:R) => x.
have H : req (rsum (fun n => rmul (cst (chi n)%:~R) (rdiv (rlog n) (cst n%:R))) (iota 1 x))
             (rsum (fun n => rmul (cst (chi n)%:~R) (rdiv (lrs n) (cst n%:R))) (iota 1 x)).
  apply: rsum_ext_in => n; rewrite mem_iota => /andP [hn _].
  exact/req_cmul_rdiv/rlog_lrs.
apply: req_rle_trans (req_rabs H) _; apply: rle_of_ptwise => k.
by rewrite /rabs /rsum /rmul /rdiv /cst iota1E; apply: sum_chi_lrs_pt.
Qed.

(** ** Step 5: the convolution identity and the von Mangoldt sum *)

Lemma chi_rlog_conv : forall x k,
  \sum_(1 <= n < x.+1) (chi n)%:~R * rlog n k / n%:R =
  \sum_(1 <= d < x.+1) (chi d)%:~R * vmangoldt d k / d%:R *
     \sum_(1 <= e < (x %/ d)%N.+1) (chi e)%:~R / e%:R.
Proof using chi_mul.
move=> x k.
pose f d e := chr d * vmangoldt d k / d%:R * (chr e / e%:R).
transitivity (\sum_(1 <= n < x.+1) \sum_(d <- divisors n) f d (n %/ d)%N).
  apply: eq_big_nat => n /andP [hn _].
  rewrite -(vmangoldt_divisors hn k) mulr_sumr mulr_suml.
  apply: eq_big_seq => d; rewrite -dvdn_divisors // => hd.
  have hd0 : (0 < d)%N := dvdn_gt0 hn hd.
  have he0 : (0 < n %/ d)%N by rewrite divn_gt0 // dvdn_leq.
  rewrite /f; move: (divnK hd) he0; set e := (n %/ d)%N => hne he0.
  rewrite -hne chi_mul natrM intrM.
  have : d%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n.
  have : e%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n.
  by move=> ? ?; field.
rewrite pair_sum_divisors; apply: eq_big_nat => d _.
by rewrite mulr_sumr.
Qed.

Lemma floor_div_bound {x d : nat} : (1 <= d <= x)%N ->
  M%:R / (x %/ d)%N.+1%:R <= M%:R * d%:R / x%:R :> rat.
Proof.
move=> /andP [hd hdx]; have hx : (0 < x)%N by apply: leq_trans hdx.
have hxq : x%:R <= d%:R * (x %/ d)%N.+1%:R :> rat.
  by rewrite -natrM ler_nat mulnC ltnW // ltn_ceil.
rewrite ler_pdivrMr ?ltr0n // mulrAC ler_pdivlMr ?ltr0n //.
by rewrite -mulrA; apply: ler_wpM2l => //; apply: ler0n.
Qed.

Lemma conv_err_pt (x k : nat) : (x <= k)%N ->
  `|Lchi chi k * rsum (fun d => rmul (cst (chi d)%:~R) (rdiv (vmangoldt d) (cst d%:R))) (iota 1 x) k
    - rsum (fun n => rmul (cst (chi n)%:~R) (rdiv (rlog n) (cst n%:R))) (iota 1 x) k|
  <= M%:R / x%:R * psi x k.
Proof using chi_mul chi_le1 chi_window.
move=> hk; rewrite /psi /rsum /rmul /rdiv /cst !iota1E.
have e1 : \sum_(1 <= n < x.+1) chr n * (rlog n k / n%:R) =
          \sum_(1 <= n < x.+1) chr n * rlog n k / n%:R by apply: eq_bigr => n _; rewrite mulrA.
rewrite e1 chi_rlog_conv mulr_sumr -sumrB mulr_sumr.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: ler_sum_nat => d /andP [hd hdx]; rewrite ltnS in hdx.
have hd0 : d%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n.
have hx0 : x%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n; apply: leq_trans hdx.
set Sp := \sum_(1 <= e < _) _.
set V := vmangoldt d k.
have -> : Lchi chi k * (chr d * (V / d%:R)) - chr d * V / d%:R * Sp =
          (chr d * (V / d%:R)) * (Lchi chi k - Sp) by ring.
rewrite normrM.
have hV : 0 <= V / d%:R by apply: divr_ge0; [apply: vmangoldt_ge0 | apply: ler0n].
have h1 : `|chr d * (V / d%:R)| <= V / d%:R.
  rewrite normrM (ger0_norm hV); rewrite -[X in _ <= X]mul1r.
  by apply: ler_wpM2r => //; apply: chi_le1_rat.
have h2 : `|Lchi chi k - Sp| <= M%:R / (x %/ d)%N.+1%:R.
  by apply: (Lchi_diff chi M chi_window); apply: leq_trans (leq_div x d) hk.
have h3 := floor_div_bound (d := d) (x := x) (introT andP (conj hd hdx)).
apply: le_trans (ler_pM (normr_ge0 _) (normr_ge0 _) h1 (le_trans h2 h3)) _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

Lemma sum_chi_vmangoldt_bounded : exists C : rat, forall x,
  rle (rabs (rsum (fun d => rmul (cst (chi d)%:~R) (rdiv (vmangoldt d) (cst d%:R))) (iota 1 x))) (cst C).
Proof using M_gt0 chi_mul chi_le1 chi1 chi_window.
have [C1 hC1] := sum_chi_rlog_bounded.
have [c [c0 hc]] := Lchi_ge chi M chi_mul chi_le1 chi1 chi_window.
exists (2 * (C1 + 6 * M%:R + 1) / c) => x.
set B := rsum _ (iota 1 x).
pose S := rsum (fun n => rmul (cst (chi n)%:~R) (rdiv (rlog n) (cst n%:R))) (iota 1 x).
have hE : rle (rabs (rsub (rmul (Lchi chi) B) S)) (cst (6 * M%:R)).
  apply: rle_trans (_ : rle _ (rmul (cst (M%:R / x%:R)) (psi x))) _.
    by apply: rle_of_eventually; exists x => k hk; apply: conv_err_pt.
  have hMx : 0 <= M%:R / x%:R :> rat by apply: divr_ge0; apply: ler0n.
  apply: rle_trans (rle_rmul_cst _ hMx (psi_le x)) _.
  apply: rle_of_ptwise => k; rewrite /rmul /cst.
  case: x {B S hMx} => [|x]; first by rewrite invr0 mulr0 mul0r; apply: mulr_ge0 => //; apply: ler0n.
  have : 1 + x%:R != 0 :> rat by apply: lt0r_neq0; have := ler0n rat x; lra.
  by move=> ?; rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
have hT : rle (rabs (rmul (Lchi chi) B)) (cst (C1 + 6 * M%:R)).
  apply: rle_trans (_ : rle _ (radd (rabs (rsub (rmul (Lchi chi) B) S)) (rabs S))) _.
    apply: rle_of_ptwise => k; rewrite /rabs /radd /rsub /rmul.
    by have := ler_normD (Lchi chi k * B k - S k) (S k); rewrite subrK.
  apply: rle_trans (rle_add hE (hC1 x)) _.
  by apply: rle_of_ptwise => k; rewrite /radd /cst; lra.
exact: rabs_bound_div hT hc c0.
Qed.

(** ** Step 6: removing the proper prime powers *)

Lemma ppterm_ge0 (n : nat) k : 0 <= ppterm n k.
Proof.
rewrite /ppterm; case: ifP => _ //.
by rewrite /rdiv /cst; apply: divr_ge0; [apply: vmangoldt_ge0 | apply: ler0n].
Qed.

Lemma sum_chi_rlog_primes_bounded : exists C : rat, forall x,
  rle (rabs (rsum (fun p => rmul (cst (chi p)%:~R) (rdiv (rlog p) (cst p%:R)))
                  [seq p <- iota 1 x | prime p])) (cst C).
Proof using M_gt0 chi_mul chi_le1 chi1 chi_window.
have [C3 h3] := sum_chi_vmangoldt_bounded; exists (C3 + 8) => x.
set P := rsum _ _.
pose B := rsum (fun d => rmul (cst (chi d)%:~R) (rdiv (vmangoldt d) (cst d%:R))) (iota 1 x).
have hsplit : forall k, B k = P k + \sum_(n <- iota 1 x) chr n * ppterm n k.
  move=> k; rewrite /B /P /rsum /rmul /rdiv /cst.
  rewrite (eq_bigr _ (fun d _ => congr1 (fun t => chr d * t) (vmangoldt_div_split d k))).
  rewrite (eq_bigr _ (fun d _ => mulrDr _ _ _)) big_split /=; congr (_ + _).
  rewrite [RHS]big_filter [RHS]big_mkcond; apply: eq_bigr => d _.
  by case: ifP => _; rewrite ?mulr0.
have hpp : forall k, `|\sum_(n <- iota 1 x) chr n * ppterm n k| <= 8.
  move=> k; apply: le_trans (ler_norm_sum _ _ _) _.
  apply: le_trans (prime_pow_tail_pt x k); apply: ler_sum => n _.
  rewrite normrM (ger0_norm (ppterm_ge0 n k)) -[X in _ <= X]mul1r.
  by apply: ler_wpM2r; [apply: ppterm_ge0 | apply: chi_le1_rat].
apply: rle_trans (_ : rle _ (radd (rabs B) (cst 8))) _.
  apply: rle_of_ptwise => k; rewrite /rabs /radd /cst hsplit.
  have := hpp k; set T := \sum_(n <- _) _ => hT.
  have := ler_normD (P k + T) (- T); rewrite addrK normrN; lra.
apply: rle_trans (rle_add (h3 x) (rle_refl (cst 8))) _.
by apply: rle_of_ptwise => k; rewrite /radd /cst.
Qed.

End AbstractChar2.
