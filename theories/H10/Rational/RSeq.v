(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Choice-free reals as rational sequences (PLAN.md Phase 4, task D1;
   DIRICHLET_DESIGN.md, Sec. 4). A real number is represented by a
   sequence [f : rseq := nat -> rat], usually Cauchy; equality [req] and
   order [rle], [rlt] are Prop-valued "for all large k" relations. There
   is no quotient, no completeness axiom, no Stdlib [Reals] and no choice:
   the only axiom used is [Classical_Prop.classic] (in [rlt_or_rle] and
   what depends on it: [rle_total], [rlt_trichotomy], [rnot_lt],
   [rsqrt_le_of_sqr]).

   Design rules (DIRICHLET_DESIGN.md, Sec. 4).
   - All algebra is pointwise in [rat]: [radd], [rmul], [ropp], [rsub],
     [rinv] (pointwise [^-1], so [0^-1 = 0]), [rdiv], [rabs], [rsum].
     Identities between reals are proved pointwise with [req_of_eq] or
     [req_of_eventually] (using MathComp's [ring], [field], [lra]).
   - Analysis is "for all large k": [rle_of_eventually], [rle_of_ptwise],
     [rlt_of_eventually]; the converse direction is the definition itself
     (an [rle f g] hypothesis applied to [e] and [0 < e] yields an [N]).
   - Multiplication respects [req] / [rle] only for bounded (Cauchy)
     arguments; those lemmas carry [cauchy] hypotheses ([req_rmul],
     [req_rmul_l], [rle_rmul_l], [rle_rmul_nonneg]). Constants need none
     ([req_rmul_cst], [rle_rmul_cst]).
   - There is no total inverse law: [rinv_spec] gives the inverse of a
     Cauchy sequence that is eventually bounded away from 0; strict
     positivity can be cancelled ([rle_rmul_cancel_l],
     [rabs_bound_cancel_l]).
   - Reflection to [rat]: [rle_cst], [rlt_cst], [req_cst].

   Contents.
   1. Definitions: [rseq], [cauchy], [req], [rle], [rlt], [cst], [radd],
      [rmul], [ropp], [rsub], [rinv], [rdiv], [rabs], [rsum].
   2. Helpers: [ev] ("eventually"), [evI], [ev_mono]; the tactic [nlra]
      ([lra] after splitting every [`|x| < y], [`|x| <= y] in the context
      and goal); small rational lemmas ([pow2_small], [inv_close], ...).
   3. [req] is an [Equivalence], [rle] a [PreOrder]; [Proper] instances
      for [rle], [rlt] (w.r.t. [req]); transfer lemmas; [rle_antisym],
      [rlt_rle], transitivity lemmas.
   4. Reflection of constants.
   5. [Proper] instances for [radd], [ropp], [rsub], [rabs] (and the
      lemma forms [req_radd], ...); [rle_add], [rle_opp], [rle_sub], ...
   6. Absolute value: [rabs_rle], [rle_rabs], [rabs_triangle], ...
   7. Finite sums [rsum F s = fun k => \sum_(n <- s) F n k]: linearity,
      [rle_rsum], [rsum_ge0], [rabs_rsum], [rsum_proper].
   8. Cauchy sequences: closure properties, [cauchy_bounded],
      [req_cauchy].
   9. Multiplication: [req_rmul], [rle_rmul_nonneg], [rle_rmul_l],
      cancellation of a positive factor.
   10. Inverse: [rinv_spec], [rlt_rinv_pos].
   11. Totality (classical): [rlt_or_rle], [rle_total], [rlt_trichotomy].
   12. Square roots [rsqrt n k := isqrt (n 4^k) / 2^k]: [rsqrt_cauchy],
       [rsqrt_sqr], [sqr_inj_nonneg], [rsqrt_mul], [rsqrt_le_of_sqr], and
       pointwise facts ([rsqrt_mono], [rsqrt_ge1], [rsqrt_isqrt], ...).
   13. Inverse square roots: [rinv_rsqrt_pos], [rinv_rsqrt_mono]
       (pointwise), [cauchy_rinv_rsqrt].
   14. Telescoping: [rinv_rsqrt_le], [rsqrt_diff_le_rinv]; with
       [G z := sum_(1 <= e <= z) 1/sqrt e] and [E z := G z - 2 sqrt z]:
       [E_decr], [E_le], [E_ge] ([-2 <= E z <= 0]); [harm_le_sqrt]
       ([H(n) <= 2 sqrt n]); [rsqrt_floor_div]
       ([|sqrt x - sqrt d sqrt (x/d)| <= d / sqrt x]).

   Arguments of lemmas are implicit exactly when they occur in a
   hypothesis. *)

From Stdlib Require Import PeanoNat Setoid Morphisms Classical_Prop.
From mathcomp Require Import boot order algebra.
Import Order.TTheory GRing.Theory Num.Theory.

Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(** * 1. Definitions *)

Definition rseq := nat -> rat.

Definition cauchy (f : rseq) :=
  forall e : rat, 0 < e -> exists N, forall m n, (N <= m)%N -> (N <= n)%N -> `|f m - f n| < e.
Definition req (f g : rseq) :=
  forall e : rat, 0 < e -> exists N, forall k, (N <= k)%N -> `|f k - g k| < e.
Definition rle (f g : rseq) :=
  forall e : rat, 0 < e -> exists N, forall k, (N <= k)%N -> f k <= g k + e.
Definition rlt (f g : rseq) :=
  exists e : rat, 0 < e /\ exists N, forall k, (N <= k)%N -> f k + e <= g k.

Definition cst (q : rat) : rseq := fun _ => q.
Definition radd (f g : rseq) : rseq := fun k => f k + g k.
Definition rmul (f g : rseq) : rseq := fun k => f k * g k.
Definition ropp (f : rseq) : rseq := fun k => - f k.
Definition rsub (f g : rseq) : rseq := fun k => f k - g k.
Definition rinv (f : rseq) : rseq := fun k => (f k)^-1.
Definition rdiv (f g : rseq) : rseq := fun k => f k / g k.
Definition rabs (f : rseq) : rseq := fun k => `|f k|.
Definition rsum (F : nat -> rseq) (s : seq nat) : rseq := fun k => \sum_(n <- s) F n k.

(* ------------------------------------------------------------------ *)
(** * 2. "Eventually" and rational helpers *)

Definition ev (P : nat -> Prop) := exists N, forall k, (N <= k)%N -> P k.

Lemma evI {P Q : nat -> Prop} : ev P -> ev Q -> ev (fun k => P k /\ Q k).
Proof.
move=> [N1 h1] [N2 h2]; exists (N1 + N2)%N => k hk; split.
- by apply: h1; apply: leq_trans hk; apply: leq_addr.
- by apply: h2; apply: leq_trans hk; apply: leq_addl.
Qed.

Lemma ev_mono {P Q : nat -> Prop} : (forall k, P k -> Q k) -> ev P -> ev Q.
Proof. by move=> hPQ [N h]; exists N => k hk; apply/hPQ/h. Qed.

Lemma ev_all {P : nat -> Prop} : (forall k, P k) -> ev P.
Proof. by move=> h; exists 0%N. Qed.

Lemma ev_ge (N0 : nat) : ev (fun k => (N0 <= k)%N).
Proof. by exists N0. Qed.

Ltac unabs := repeat match goal with
  | H : is_true (Num.norm _ < _) |- _ => rewrite ltr_norml in H; case/andP: H => ? ?
  | H : is_true (Num.norm _ <= _) |- _ => rewrite ler_norml in H; case/andP: H => ? ?
  | |- is_true (Num.norm _ < _) => rewrite ltr_norml; apply/andP; split
  | |- is_true (Num.norm _ <= _) => rewrite ler_norml; apply/andP; split
  end.
Ltac nlra := unabs; lra.

Lemma le_addl_trans {N1 N2 k : nat} : (N1 + N2 <= k)%N -> (N1 <= k)%N.
Proof. by apply: leq_trans; apply: leq_addr. Qed.
Lemma le_addr_trans {N1 N2 k : nat} : (N1 + N2 <= k)%N -> (N2 <= k)%N.
Proof. by apply: leq_trans; apply: leq_addl. Qed.

Lemma pow2_small {e : rat} : 0 < e -> exists j : nat, 1 / (2 ^ j)%:R < e.
Proof.
move=> he; exists (Num.bound (1 / e)).
have := archi_boundP (ltW (divr_gt0 ltr01 he)).
set b := Num.bound _ => hb.
rewrite ltr_pdivrMr ?ltr0n ?expn_gt0 //.
rewrite ltr_pdivrMr // in hb.
rewrite mulrC; apply: (lt_le_trans hb); rewrite ler_pM2r // ler_nat.
by apply: ltnW; apply: ltn_expl.
Qed.

Lemma pow2_gt0 (k : nat) : 0 < (2 ^ k)%:R :> rat.
Proof. by rewrite ltr0n expn_gt0. Qed.

Lemma inv_pow2_le {j k : nat} : (j <= k)%N -> 1 / (2 ^ k)%:R <= 1 / (2 ^ j)%:R :> rat.
Proof.
move=> hjk; rewrite !div1r lef_pV2 ?posrE ?pow2_gt0 // ler_nat.
exact: leq_pexp2l.
Qed.

Lemma inv_pow2_le1 (k : nat) : 1 / (2 ^ k)%:R <= 1 :> rat.
Proof. by have := inv_pow2_le (leq0n k); rewrite expn0 divr1. Qed.

Lemma inv_pow2_gt0 (k : nat) : 0 < 1 / (2 ^ k)%:R :> rat.
Proof. by rewrite divr_gt0 ?pow2_gt0. Qed.

Lemma mul_ge_neg {x y B d : rat} :
  0 <= B -> 0 <= d -> -d <= x -> -d <= y -> x <= B -> y <= B -> -(B * d) <= x * y.
Proof.
move=> hB hd hx hy hxB hyB; have hBd := mulr_ge0 hB hd.
case: (lerP 0 x) => x0; case: (lerP 0 y) => y0.
- by have := mulr_ge0 x0 y0; lra.
- have h1 : x * -d <= x * y by apply: ler_wpM2l.
  have h2 : x * d <= B * d by apply: ler_wpM2r.
  lra.
- have h1 : -d * y <= x * y by apply: ler_wpM2r.
  have h2 : y * d <= B * d by apply: ler_wpM2r.
  lra.
- have : 0 < x * y by rewrite -mulrNN; apply: mulr_gt0; lra.
  lra.
Qed.

Lemma prod_close {a b c d B r : rat} : 0 < B -> `|a| <= B -> `|d| <= B ->
  `|b - d| < r -> `|a - c| < r -> `|a * b - c * d| < 2 * B * r.
Proof.
move=> hB ha hd h1 h2.
have -> : a * b - c * d = a * (b - d) + d * (a - c) by ring.
apply: le_lt_trans (ler_normD _ _) _; rewrite !normrM.
have h3 : `|a| * `|b - d| <= B * `|b - d| := ler_wpM2r (normr_ge0 _) ha.
have h4 : B * `|b - d| < B * r by rewrite ltr_pM2l.
have h5 : `|d| * `|a - c| <= B * `|a - c| := ler_wpM2r (normr_ge0 _) hd.
have h6 : B * `|a - c| < B * r by rewrite ltr_pM2l.
lra.
Qed.

Lemma mul_small {a x B r : rat} : 0 < B -> `|a| <= B -> `|x| < r -> `|a * x| < B * r.
Proof.
move=> hB ha hx; rewrite normrM.
have h3 : `|a| * `|x| <= B * `|x| := ler_wpM2r (normr_ge0 _) ha.
have h4 : B * `|x| < B * r by rewrite ltr_pM2l.
lra.
Qed.

Lemma sqr_lt_lt {a b : rat} : 0 <= b -> a * a < b * b -> a < b.
Proof.
move=> hb h; case: (ltrP a b) => // hba; exfalso.
have : b * b <= a * a by apply: ler_pM.
lra.
Qed.

Lemma sqr_le_le {a b : rat} : 0 <= b -> a * a <= b * b -> a <= b.
Proof.
move=> hb h; case: (lerP a b) => // hba; exfalso.
have h1 : b * b <= b * a by apply: ler_wpM2l => //; apply: ltW.
have h2 : b * a < a * a by rewrite ltr_pM2r // (le_lt_trans hb hba).
lra.
Qed.

Lemma inv_close {a b c r : rat} : 0 < c -> 0 < r -> c <= a -> c <= b ->
  `|a - b| < r * c * c -> `|a^-1 - b^-1| < r.
Proof.
move=> hc hr hca hcb h.
have a0 : 0 < a by apply: lt_le_trans hca.
have b0 : 0 < b by apply: lt_le_trans hcb.
have ha' := lt0r_neq0 a0; have hb' := lt0r_neq0 b0.
have -> : a^-1 - b^-1 = (b - a) / (a * b) by field.
rewrite normrM normfV (gtr0_norm (mulr_gt0 a0 b0)) ltr_pdivrMr ?mulr_gt0 // distrC.
have h1 : c * c <= a * b by apply: ler_pM => //; apply: ltW.
have h2 : r * (c * c) <= r * (a * b) by apply: ler_wpM2l => //; apply: ltW.
lra.
Qed.

Lemma sq_close {a b e : rat} : 0 <= a -> 0 <= b -> 0 < e ->
  `|a * a - b * b| < e * e -> `|a - b| < e.
Proof.
move=> ha hb he h; apply: sqr_lt_lt; first exact: ltW.
have e1 : a * a - b * b = (a - b) * (a + b) by ring.
rewrite e1 normrM (ger0_norm (addr_ge0 ha hb)) in h.
have h1 : `|a - b| <= a + b by nlra.
have h2 : `|a - b| * `|a - b| <= `|a - b| * (a + b) by apply: ler_wpM2l.
lra.
Qed.

(* ------------------------------------------------------------------ *)
(** * 3. Equality and order: equivalence, preorder, transfer *)

Lemma req_refl (f : rseq) : req f f.
Proof. by move=> e he; apply: ev_all => k; rewrite subrr normr0. Qed.

Lemma req_sym {f g : rseq} : req f g -> req g f.
Proof. by move=> h e he; apply: ev_mono (h _ he) => k; rewrite distrC. Qed.

Lemma req_trans {f g h : rseq} : req f g -> req g h -> req f h.
Proof.
move=> h1 h2 e he; have he2 : 0 < e / 2 by lra.
by apply: ev_mono (evI (h1 _ he2) (h2 _ he2)) => k [? ?]; nlra.
Qed.

#[export] Instance req_Equivalence : Equivalence req.
Proof. split; [exact: req_refl | move=> ? ?; exact: req_sym | move=> ? ? ?; exact: req_trans]. Qed.

Lemma req_of_eventually {f g : rseq} :
  (exists N, forall k, (N <= k)%N -> f k = g k) -> req f g.
Proof. by move=> h e he; apply: ev_mono h => k ->; rewrite subrr normr0. Qed.

Lemma req_of_eq {f g : rseq} : (forall k, f k = g k) -> req f g.
Proof. by move=> h; apply: req_of_eventually; exists 0%N. Qed.

Lemma rle_of_eventually {f g : rseq} :
  (exists N, forall k, (N <= k)%N -> f k <= g k) -> rle f g.
Proof. by move=> h e he; apply: ev_mono h => k hk; lra. Qed.

Lemma rle_of_ptwise {f g : rseq} : (forall k, f k <= g k) -> rle f g.
Proof. by move=> h; apply: rle_of_eventually; exists 0%N. Qed.

Lemma rlt_of_eventually {f g : rseq} {e : rat} : 0 < e ->
  (exists N, forall k, (N <= k)%N -> f k + e <= g k) -> rlt f g.
Proof. by move=> he h; exists e. Qed.

Lemma rle_refl (f : rseq) : rle f f.
Proof. by apply: rle_of_ptwise. Qed.

Lemma rle_trans {f g h : rseq} : rle f g -> rle g h -> rle f h.
Proof.
move=> h1 h2 e he; have he2 : 0 < e / 2 by lra.
by apply: ev_mono (evI (h1 _ he2) (h2 _ he2)) => k [? ?]; lra.
Qed.

#[export] Instance rle_PreOrder : PreOrder rle.
Proof. split; [exact: rle_refl | move=> ? ? ?; exact: rle_trans]. Qed.

Lemma req_rle {f g : rseq} : req f g -> rle f g.
Proof. by move=> h e he; apply: ev_mono (h _ he) => k ?; nlra. Qed.

Lemma req_rle' {f g : rseq} : req f g -> rle g f.
Proof. by move=> /req_sym; apply: req_rle. Qed.

Lemma rle_antisym {f g : rseq} : rle f g -> rle g f -> req f g.
Proof.
move=> h1 h2 e he; have he2 : 0 < e / 2 by lra.
by apply: ev_mono (evI (h1 _ he2) (h2 _ he2)) => k [? ?]; nlra.
Qed.

#[export] Instance rle_proper : Proper (req ==> req ==> iff) rle.
Proof.
move=> f f' hf g g' hg; split=> h.
- exact: rle_trans (req_rle' hf) (rle_trans h (req_rle hg)).
- exact: rle_trans (req_rle hf) (rle_trans h (req_rle' hg)).
Qed.

Lemma rlt_rle {f g : rseq} : rlt f g -> rle f g.
Proof. by move=> [e [he h]] d hd; apply: ev_mono h => k; lra. Qed.

Lemma rlt_irrefl (f : rseq) : ~ rlt f f.
Proof. by move=> [e [he [N h]]]; have := h N (leqnn N); lra. Qed.

Lemma rle_rlt_trans {f g h : rseq} : rle f g -> rlt g h -> rlt f h.
Proof.
move=> h1 [e [he h2]]; have he2 : 0 < e / 2 by lra.
exists (e / 2); split=> //.
by apply: ev_mono (evI (h1 _ he2) h2) => k [? ?]; lra.
Qed.

Lemma rlt_rle_trans {f g h : rseq} : rlt f g -> rle g h -> rlt f h.
Proof.
move=> [e [he h1]] h2; have he2 : 0 < e / 2 by lra.
exists (e / 2); split=> //.
by apply: ev_mono (evI h1 (h2 _ he2)) => k [? ?]; lra.
Qed.

Lemma rlt_trans {f g h : rseq} : rlt f g -> rlt g h -> rlt f h.
Proof. by move=> h1 /rlt_rle; apply: rlt_rle_trans. Qed.

#[export] Instance rlt_proper : Proper (req ==> req ==> iff) rlt.
Proof.
move=> f f' hf g g' hg; split=> h.
- exact: rle_rlt_trans (req_rle' hf) (rlt_rle_trans h (req_rle hg)).
- exact: rle_rlt_trans (req_rle hf) (rlt_rle_trans h (req_rle' hg)).
Qed.

Lemma rle_req_trans {f g h : rseq} : rle f g -> req g h -> rle f h.
Proof. by move=> h1 /req_rle; apply: rle_trans. Qed.

Lemma req_rle_trans {f g h : rseq} : req f g -> rle g h -> rle f h.
Proof. by move=> /req_rle; apply: rle_trans. Qed.

(* ------------------------------------------------------------------ *)
(** * 4. Reflection of constants *)

Lemma rle_cst (a b : rat) : rle (cst a) (cst b) <-> a <= b.
Proof.
split=> [h|h e he]; first last.
  by apply: ev_all => k; rewrite /cst; lra.
apply/ler_addgt0Pr => e he; have [N hN] := h e he; exact: hN N (leqnn N).
Qed.

Lemma rlt_cst (a b : rat) : rlt (cst a) (cst b) <-> a < b.
Proof.
split=> [[e [he [N h]]]|h]; first by have := h N (leqnn N); rewrite /cst; lra.
by exists (b - a); split; [lra | apply: ev_all => k; rewrite /cst; lra].
Qed.

Lemma req_cst (a b : rat) : req (cst a) (cst b) <-> a = b.
Proof.
split=> [h|->]; last by reflexivity.
by apply/le_anti/andP; split; apply/rle_cst; [apply: req_rle | apply: req_rle'].
Qed.

(* ------------------------------------------------------------------ *)
(** * 5. Arithmetic: compatibility and order *)

#[export] Instance radd_proper : Proper (req ==> req ==> req) radd.
Proof.
move=> f f' hf g g' hg e he; have he2 : 0 < e / 2 by lra.
by apply: ev_mono (evI (hf _ he2) (hg _ he2)) => k [? ?]; rewrite /radd; nlra.
Qed.

#[export] Instance ropp_proper : Proper (req ==> req) ropp.
Proof. by move=> f f' hf e he; apply: ev_mono (hf _ he) => k ?; rewrite /ropp; nlra. Qed.

#[export] Instance rsub_proper : Proper (req ==> req ==> req) rsub.
Proof.
move=> f f' hf g g' hg e he; have he2 : 0 < e / 2 by lra.
by apply: ev_mono (evI (hf _ he2) (hg _ he2)) => k [? ?]; rewrite /rsub; nlra.
Qed.

#[export] Instance rabs_proper : Proper (req ==> req) rabs.
Proof.
move=> f f' hf e he; apply: ev_mono (hf _ he) => k h; rewrite /rabs.
exact: le_lt_trans (ler_dist_dist _ _) h.
Qed.

Lemma req_radd {f f' g g' : rseq} : req f f' -> req g g' -> req (radd f g) (radd f' g').
Proof. by move=> h1 h2; apply: radd_proper. Qed.
Lemma req_rsub {f f' g g' : rseq} : req f f' -> req g g' -> req (rsub f g) (rsub f' g').
Proof. by move=> h1 h2; apply: rsub_proper. Qed.
Lemma req_ropp {f f' : rseq} : req f f' -> req (ropp f) (ropp f').
Proof. by move=> h1; apply: ropp_proper. Qed.
Lemma req_rabs {f f' : rseq} : req f f' -> req (rabs f) (rabs f').
Proof. by move=> h1; apply: rabs_proper. Qed.

Lemma rle_add {f g f' g' : rseq} : rle f g -> rle f' g' -> rle (radd f f') (radd g g').
Proof.
move=> h1 h2 e he; have he2 : 0 < e / 2 by lra.
by apply: ev_mono (evI (h1 _ he2) (h2 _ he2)) => k [? ?]; rewrite /radd; lra.
Qed.

Lemma rle_opp {f g : rseq} : rle f g -> rle (ropp g) (ropp f).
Proof. by move=> h e he; apply: ev_mono (h _ he) => k ?; rewrite /ropp; lra. Qed.

Lemma rle_sub {f g f' g' : rseq} : rle f g -> rle g' f' -> rle (rsub f f') (rsub g g').
Proof.
move=> h1 h2 e he; have he2 : 0 < e / 2 by lra.
by apply: ev_mono (evI (h1 _ he2) (h2 _ he2)) => k [? ?]; rewrite /rsub; lra.
Qed.

Lemma rle_add2l (h f g : rseq) : rle (radd h f) (radd h g) <-> rle f g.
Proof.
split=> H e he; apply: ev_mono (H _ he) => k; rewrite /radd; lra.
Qed.

Lemma rle_add2r (h f g : rseq) : rle (radd f h) (radd g h) <-> rle f g.
Proof.
split=> H e he; apply: ev_mono (H _ he) => k; rewrite /radd; lra.
Qed.

Lemma rle_sub_ge0 (f g : rseq) : rle (cst 0) (rsub g f) <-> rle f g.
Proof.
split=> H e he; apply: ev_mono (H _ he) => k; rewrite /rsub /cst; lra.
Qed.

Lemma radd_cst (a b : rat) : req (radd (cst a) (cst b)) (cst (a + b)).
Proof. by apply: req_of_eq. Qed.
Lemma rsub_cst (a b : rat) : req (rsub (cst a) (cst b)) (cst (a - b)).
Proof. by apply: req_of_eq. Qed.
Lemma rmul_cst (a b : rat) : req (rmul (cst a) (cst b)) (cst (a * b)).
Proof. by apply: req_of_eq. Qed.
Lemma ropp_cst (a : rat) : req (ropp (cst a)) (cst (- a)).
Proof. by apply: req_of_eq. Qed.
Lemma rdiv_rmul (f g : rseq) : req (rdiv f g) (rmul f (rinv g)).
Proof. by apply: req_of_eq. Qed.

(* ------------------------------------------------------------------ *)
(** * 6. Absolute value *)

Lemma rabs_ge0 (f : rseq) k : 0 <= rabs f k.
Proof. exact: normr_ge0. Qed.

Lemma rabs_rle0 (f : rseq) : rle (cst 0) (rabs f).
Proof. by apply: rle_of_ptwise => k; apply: normr_ge0. Qed.

Lemma rle_rabs (f : rseq) : rle f (rabs f).
Proof. by apply: rle_of_ptwise => k; apply: ler_norm. Qed.

Lemma rabs_rle (f g : rseq) : rle (rabs f) g <-> rle (ropp g) f /\ rle f g.
Proof.
split=> [h|[h1 h2] e he].
- by split=> e he; apply: ev_mono (h _ he) => k /=; rewrite /rabs /ropp => ?; nlra.
- by apply: ev_mono (evI (h1 _ he) (h2 _ he)) => k [h3 h4]; move: h3 h4; rewrite /rabs /ropp => ? ?; nlra.
Qed.

Lemma rabs_triangle (f g : rseq) : rle (rabs (radd f g)) (radd (rabs f) (rabs g)).
Proof. by apply: rle_of_ptwise => k; apply: ler_normD. Qed.

Lemma rabs_rmul (f g : rseq) : req (rabs (rmul f g)) (rmul (rabs f) (rabs g)).
Proof. by apply: req_of_eq => k; apply: normrM. Qed.

Lemma rabs_ropp (f : rseq) : req (rabs (ropp f)) (rabs f).
Proof. by apply: req_of_eq => k; apply: normrN. Qed.

Lemma rabs_cst (a : rat) : req (rabs (cst a)) (cst `|a|).
Proof. by apply: req_of_eq. Qed.

(* ------------------------------------------------------------------ *)
(** * 7. Finite sums *)

Lemma rsum_nil (F : nat -> rseq) : req (rsum F [::]) (cst 0).
Proof. by apply: req_of_eq => k; rewrite /rsum big_nil. Qed.

Lemma rsum_cons_pt (F : nat -> rseq) n s k : rsum F (n :: s) k = F n k + rsum F s k.
Proof. by rewrite /rsum big_cons. Qed.

Lemma rsum_cons (F : nat -> rseq) n s : req (rsum F (n :: s)) (radd (F n) (rsum F s)).
Proof. by apply: req_of_eq => k; apply: rsum_cons_pt. Qed.

Lemma rsum_cat (F : nat -> rseq) s1 s2 :
  req (rsum F (s1 ++ s2)) (radd (rsum F s1) (rsum F s2)).
Proof. by apply: req_of_eq => k; rewrite /rsum big_cat. Qed.

Lemma rsum_seq1 (F : nat -> rseq) n : req (rsum F [:: n]) (F n).
Proof. by apply: req_of_eq => k; rewrite /rsum big_seq1. Qed.

Lemma rsum_cst (a : nat -> rat) s : req (rsum (fun n => cst (a n)) s) (cst (\sum_(n <- s) a n)).
Proof. by apply: req_of_eq. Qed.

Lemma rsum_add (F G : nat -> rseq) s :
  req (rsum (fun n => radd (F n) (G n)) s) (radd (rsum F s) (rsum G s)).
Proof. by apply: req_of_eq => k; rewrite /rsum /radd big_split. Qed.

Lemma rsum_scale (c : rat) (F : nat -> rseq) s :
  req (rsum (fun n => rmul (cst c) (F n)) s) (rmul (cst c) (rsum F s)).
Proof. by apply: req_of_eq => k; rewrite /rsum /rmul mulr_sumr. Qed.

Lemma rsum_ext_in {F G : nat -> rseq} {s} :
  (forall n, n \in s -> req (F n) (G n)) -> req (rsum F s) (rsum G s).
Proof.
elim: s => [|n s IH] h; first by apply: req_of_eq => k; rewrite /rsum !big_nil.
apply: req_trans (rsum_cons F n s) _; apply: req_trans _ (req_sym (rsum_cons G n s)).
apply: radd_proper.
- by apply: h; rewrite mem_head.
- by apply: IH => m hm; apply: h; rewrite in_cons hm orbT.
Qed.

#[export] Instance rsum_proper : Proper (pointwise_relation nat req ==> eq ==> req) rsum.
Proof. by move=> F G hFG s _ <-; apply: rsum_ext_in => n _; apply: hFG. Qed.

Lemma rle_rsum {F G : nat -> rseq} {s} :
  (forall n, n \in s -> rle (F n) (G n)) -> rle (rsum F s) (rsum G s).
Proof.
elim: s => [|n s IH] h; first by apply: rle_of_ptwise => k; rewrite /rsum !big_nil.
apply: req_rle_trans (rsum_cons F n s) _; apply: rle_req_trans _ (req_sym (rsum_cons G n s)).
apply: rle_add.
- by apply: h; rewrite mem_head.
- by apply: IH => m hm; apply: h; rewrite in_cons hm orbT.
Qed.

Lemma rsum_ge0 {F : nat -> rseq} {s} :
  (forall n, n \in s -> rle (cst 0) (F n)) -> rle (cst 0) (rsum F s).
Proof.
move=> h; apply: rle_trans (rle_rsum (F := fun _ => cst 0) h).
by apply: rle_of_ptwise => k; rewrite /rsum /cst big1_eq.
Qed.

(** Aliases under the names used in DIRICHLET_DESIGN.md. *)
Lemma rle_sum {F G : nat -> rseq} {s} :
  (forall n, n \in s -> rle (F n) (G n)) -> rle (rsum F s) (rsum G s).
Proof. exact: rle_rsum. Qed.

Lemma rle_rsum_ge0 {F : nat -> rseq} {s} :
  (forall n, n \in s -> rle (cst 0) (F n)) -> rle (cst 0) (rsum F s).
Proof. exact: rsum_ge0. Qed.

Lemma rabs_rsum (F : nat -> rseq) s : rle (rabs (rsum F s)) (rsum (fun n => rabs (F n)) s).
Proof. by apply: rle_of_ptwise => k; apply: ler_norm_sum. Qed.
(* ------------------------------------------------------------------ *)
(** * 8. Cauchy sequences *)

Lemma cauchy_ext {f g : rseq} : (forall k, f k = g k) -> cauchy f -> cauchy g.
Proof.
move=> h hf e he; have [N hN] := hf e he; exists N => m n hm hn.
by rewrite -!h; apply: hN.
Qed.

Lemma cauchyI {f g : rseq} {e1 e2 : rat} : cauchy f -> cauchy g -> 0 < e1 -> 0 < e2 ->
  exists N, forall m n, (N <= m)%N -> (N <= n)%N ->
    `|f m - f n| < e1 /\ `|g m - g n| < e2.
Proof.
move=> hf hg h1 h2; have [N1 hN1] := hf _ h1; have [N2 hN2] := hg _ h2.
exists (N1 + N2)%N => m n hm hn; split.
- by apply: hN1; apply: le_addl_trans; eassumption.
- by apply: hN2; apply: le_addr_trans; eassumption.
Qed.

Lemma cauchy_cst (a : rat) : cauchy (cst a).
Proof. by move=> e he; exists 0%N => m n _ _; rewrite /cst subrr normr0. Qed.

Lemma cauchy_add {f g : rseq} : cauchy f -> cauchy g -> cauchy (radd f g).
Proof.
move=> hf hg e he; have he2 : 0 < e / 2 by lra.
have [N hN] := cauchyI hf hg he2 he2; exists N => m n hm hn.
by have [? ?] := hN m n hm hn; rewrite /radd; nlra.
Qed.

Lemma cauchy_opp {f : rseq} : cauchy f -> cauchy (ropp f).
Proof.
move=> hf e he; have [N hN] := hf e he; exists N => m n hm hn.
by have := hN m n hm hn; rewrite /ropp => ?; nlra.
Qed.

Lemma cauchy_sub {f g : rseq} : cauchy f -> cauchy g -> cauchy (rsub f g).
Proof.
move=> hf hg; apply: (@cauchy_ext (radd f (ropp g))) => [k //|].
exact: cauchy_add hf (cauchy_opp hg).
Qed.

Lemma cauchy_abs {f : rseq} : cauchy f -> cauchy (rabs f).
Proof.
move=> hf e he; have [N hN] := hf e he; exists N => m n hm hn.
exact: le_lt_trans (ler_dist_dist _ _) (hN m n hm hn).
Qed.

Lemma prefix_bound (f : rseq) N : exists q, 0 <= q /\ forall k, (k < N)%N -> `|f k| <= q.
Proof.
elim: N => [|N [q [q0 hq]]]; first by exists 0; split=> // k; rewrite ltn0.
have hN := normr_ge0 (f N).
exists (q + `|f N|); split; first lra.
move=> k; rewrite ltnS leq_eqVlt => /orP [/eqP -> | hk]; first lra.
by have := hq k hk; lra.
Qed.

Lemma cauchy_bounded {f : rseq} : cauchy f -> exists q : rat, forall k, `|f k| <= q.
Proof.
move=> hf; have [N hN] := hf 1 ltr01; have [q [q0 hq]] := prefix_bound f N.
exists (q + `|f N| + 1) => k; have h0 := normr_ge0 (f N).
case: (ltnP k N) => hk; first by have := hq k hk; lra.
have := hN k N hk (leqnn N); have := ler_norm (f N); have := ler_norm (- f N).
rewrite normrN => ? ? ?; nlra.
Qed.

Lemma cauchy_bounded_pos {f : rseq} : cauchy f -> exists B : rat, 0 < B /\ forall k, `|f k| <= B.
Proof.
move=> /cauchy_bounded [q hq]; exists (q + 1); split.
- by have := hq 0%N; have := normr_ge0 (f 0%N); lra.
- by move=> k; have := hq k; lra.
Qed.

Lemma cauchy_bounded2 {f g : rseq} : cauchy f -> cauchy g ->
  exists B : rat, 0 < B /\ forall k, `|f k| <= B /\ `|g k| <= B.
Proof.
move=> /cauchy_bounded_pos [B1 [h1 hB1]] /cauchy_bounded_pos [B2 [h2 hB2]].
exists (B1 + B2); split; first lra.
by move=> k; have := hB1 k; have := hB2 k; split; lra.
Qed.

Lemma cauchy_rle_cst {f : rseq} : cauchy f -> exists q, rle f (cst q).
Proof.
move=> /cauchy_bounded [q hq]; exists q; apply: rle_of_ptwise => k.
exact: le_trans (ler_norm _) (hq k).
Qed.

Lemma cauchy_rge_cst {f : rseq} : cauchy f -> exists q, rle (cst q) f.
Proof.
move=> /cauchy_bounded [q hq]; exists (- q); apply: rle_of_ptwise => k.
by have := hq k; rewrite /cst => ?; nlra.
Qed.

Lemma req_cauchy {f g : rseq} : req f g -> cauchy f -> cauchy g.
Proof.
move=> hfg hf e he; have he3 : 0 < e / 3 by lra.
have [N1 hN1] := hfg _ he3; have [N2 hN2] := hf _ he3.
exists (N1 + N2)%N => m n hm hn.
have := hN1 m (le_addl_trans hm); have := hN1 n (le_addl_trans hn).
have := hN2 m n (le_addr_trans hm) (le_addr_trans hn).
move=> ? ? ?; nlra.
Qed.

#[export] Instance cauchy_proper : Proper (req ==> iff) cauchy.
Proof. by move=> f g h; split; apply: req_cauchy; [|symmetry]. Qed.

Lemma cauchy_mul {f g : rseq} : cauchy f -> cauchy g -> cauchy (rmul f g).
Proof.
move=> hf hg e he; have [B [hB hfg]] := cauchy_bounded2 hf hg.
have hr : 0 < e / (2 * B) by apply: divr_gt0; lra.
have [N hN] := cauchyI hf hg hr hr; exists N => m n hm hn.
have [h1 h2] := hN m n hm hn.
have := prod_close hB (proj1 (hfg m)) (proj2 (hfg n)) h2 h1.
by rewrite /rmul (_ : 2 * B * (e / (2 * B)) = e) //; have := lt0r_neq0 hB => ?; field.
Qed.

Lemma cauchy_rsum {F : nat -> rseq} {s} :
  (forall n, n \in s -> cauchy (F n)) -> cauchy (rsum F s).
Proof.
elim: s => [|n s IH] h.
  by apply: (@cauchy_ext (cst 0)); [move=> k; rewrite /rsum big_nil | apply: cauchy_cst].
apply: (@cauchy_ext (radd (F n) (rsum F s))) => [k|]; first by rewrite rsum_cons_pt.
apply: cauchy_add; first by apply: h; rewrite mem_head.
by apply: IH => m hm; apply: h; rewrite in_cons hm orbT.
Qed.

(* ------------------------------------------------------------------ *)
(** * 9. Multiplication *)

Lemma req_rmul_l {h f g : rseq} : cauchy h -> req f g -> req (rmul h f) (rmul h g).
Proof.
move=> hh hfg e he; have [B [hB hb]] := cauchy_bounded_pos hh.
have hr : 0 < e / B by apply: divr_gt0.
apply: ev_mono (hfg _ hr) => k hk; rewrite /rmul -mulrBr.
have := mul_small hB (hb k) hk.
by rewrite (_ : B * (e / B) = e) //; have := lt0r_neq0 hB => ?; field.
Qed.

Lemma req_rmul_r {h f g : rseq} : cauchy h -> req f g -> req (rmul f h) (rmul g h).
Proof.
move=> hh hfg; apply: req_trans (req_trans _ (req_rmul_l hh hfg)) _;
  by apply: req_of_eq => k; rewrite /rmul mulrC.
Qed.

Lemma req_rmul_cst (c : rat) {f g : rseq} : req f g -> req (rmul (cst c) f) (rmul (cst c) g).
Proof. exact/req_rmul_l/cauchy_cst. Qed.

Lemma req_rmul {f g f' g' : rseq} : cauchy f -> cauchy g -> req f f' -> req g g' ->
  req (rmul f g) (rmul f' g').
Proof.
move=> hf hg hff hgg; apply: req_trans (req_rmul_l hf hgg) _.
by apply: req_rmul_r => //; apply: req_cauchy hgg hg.
Qed.

Lemma rmulC (f g : rseq) : req (rmul f g) (rmul g f).
Proof. by apply: req_of_eq => k; rewrite /rmul mulrC. Qed.

Lemma rle_rmul_nonneg {x y : rseq} : cauchy x -> cauchy y ->
  rle (cst 0) x -> rle (cst 0) y -> rle (cst 0) (rmul x y).
Proof.
move=> hx hy h1 h2 e he; have [B [hB hxy]] := cauchy_bounded2 hx hy.
have hd : 0 < e / B by apply: divr_gt0.
apply: ev_mono (evI (h1 _ hd) (h2 _ hd)) => k [hk1 hk2]; rewrite /rmul /cst in hk1 hk2 *.
have [hxk hyk] := hxy k.
have := @mul_ge_neg (x k) (y k) B (e / B) (ltW hB) (ltW hd).
have -> : B * (e / B) = e by have := lt0r_neq0 hB => ?; field.
move=> H; have := H ltac:(lra) ltac:(lra) (ler_normlW hxk) (ler_normlW hyk); lra.
Qed.

Lemma rle_rmul_l {h f g : rseq} : rle (cst 0) h -> cauchy h -> cauchy f -> cauchy g ->
  rle f g -> rle (rmul h f) (rmul h g).
Proof.
move=> h0 hh hf hg hfg.
have hgf : rle (cst 0) (rsub g f) by apply/rle_sub_ge0.
have := rle_rmul_nonneg hh (cauchy_sub hg hf) h0 hgf.
by move=> H e he; apply: ev_mono (H _ he) => k; rewrite /rmul /rsub /cst mulrBr; lra.
Qed.

Lemma rle_rmul_r {h f g : rseq} : rle (cst 0) h -> cauchy h -> cauchy f -> cauchy g ->
  rle f g -> rle (rmul f h) (rmul g h).
Proof.
move=> h0 hh hf hg hfg; apply: req_rle_trans (rmulC _ _) _.
by apply: rle_req_trans (rmulC _ _); apply: rle_rmul_l.
Qed.

Lemma rle_rmul_cst (c : rat) {f g : rseq} : 0 <= c -> rle f g -> rle (rmul (cst c) f) (rmul (cst c) g).
Proof.
move=> hc h e he; have hr : 0 < e / (c + 1) by apply: divr_gt0; lra.
apply: ev_mono (h _ hr) => k hk; rewrite /rmul /cst.
have h1 : c * f k <= c * (g k + e / (c + 1)) by apply: ler_wpM2l.
have h2 : c * (e / (c + 1)) <= e.
  rewrite mulrA ler_pdivrMr; [nra | lra].
lra.
Qed.

Lemma rle_rmul_cancel_l {h f g : rseq} : rlt (cst 0) h -> rle (rmul h f) (rmul h g) -> rle f g.
Proof.
move=> [c [c0 [N hN]]] H e he; have hec : 0 < e * c by apply: mulr_gt0.
apply: ev_mono (evI (ev_ge N) (H _ hec)) => k [hk H1]; move: H1; rewrite /rmul => H1.
have hc := hN k hk; rewrite /cst add0r in hc.
have hk0 : 0 < h k by apply: lt_le_trans hc.
have h2 : e * c <= e * h k by apply: ler_wpM2l => //; apply: ltW.
have : h k * (f k - (g k + e)) <= 0 by rewrite mulrBr mulrDr; lra.
by rewrite pmulr_rle0 // subr_le0.
Qed.

Lemma rle_rmul_cancel_r {h f g : rseq} : rlt (cst 0) h -> rle (rmul f h) (rmul g h) -> rle f g.
Proof.
move=> h0 H; apply: (rle_rmul_cancel_l h0).
by apply: req_rle_trans (rmulC _ _) (rle_req_trans H (rmulC _ _)).
Qed.

Lemma rabs_bound_cancel_l {h f : rseq} {C : rat} :
  rle (rabs (rmul h f)) (cst C) -> rlt (cst 0) h -> exists C' : rat, rle (rabs f) (cst C').
Proof.
move=> H [c [c0 [N hN]]]; exists ((C + 1) / c); apply: rle_of_eventually.
have [N1 hN1] := H 1 ltr01; exists (N + N1)%N => k hk.
have hc := hN k (le_addl_trans hk); rewrite /cst add0r in hc.
have := hN1 k (le_addr_trans hk); rewrite /rabs /rmul /cst normrM (ger0_norm (le_trans (ltW c0) hc)).
move=> H1; rewrite ler_pdivlMr //.
have : `|f k| * c <= `|f k| * h k by apply: ler_wpM2l.
by rewrite (mulrC (h k)) in H1; lra.
Qed.

(* ------------------------------------------------------------------ *)
(** * 10. Inverse *)

Lemma rinv_spec {f : rseq} : cauchy f -> rlt (cst 0) f ->
  cauchy (rinv f) /\ req (rmul f (rinv f)) (cst 1).
Proof.
move=> hf [c [c0 [N hN]]]; split.
- move=> e he; have hd : 0 < e * c * c by rewrite !mulr_gt0.
  have [N1 hN1] := hf _ hd; exists (N + N1)%N => m n hm hn.
  have hcm := hN m (le_addl_trans hm); have hcn := hN n (le_addl_trans hn).
  rewrite /cst add0r in hcm hcn.
  exact: inv_close c0 he hcm hcn (hN1 m n (le_addr_trans hm) (le_addr_trans hn)).
- apply: req_of_eventually; exists N => k hk; have := hN k hk; rewrite /cst add0r => hc.
  by rewrite /rmul /rinv mulfV //; apply: lt0r_neq0; apply: lt_le_trans hc.
Qed.

Lemma rlt_rinv_pos {f : rseq} : cauchy f -> rlt (cst 0) f -> rlt (cst 0) (rinv f).
Proof.
move=> hf [c [c0 [N hN]]]; have [B [hB hb]] := cauchy_bounded_pos hf.
exists B^-1; split; first by rewrite invr_gt0.
exists N => k hk; have := hN k hk; rewrite /cst /rinv !add0r => hc.
have hk0 : 0 < f k by apply: lt_le_trans hc.
by rewrite lef_pV2 ?posrE //; apply: ler_normlW.
Qed.

Lemma rinv_ge0 {f : rseq} : (forall k, 0 <= f k) -> forall k, 0 <= rinv f k.
Proof. by move=> h k; rewrite /rinv invr_ge0. Qed.

(* ------------------------------------------------------------------ *)
(** * 11. Totality (classical) *)

Lemma rlt_or_rle {f g : rseq} : cauchy f -> cauchy g -> rlt f g \/ rle g f.
Proof.
move=> hf hg; case: (classic (rle g f)) => H; [by right | left].
have [e [he He]] : exists e, 0 < e /\ forall N, exists k, (N <= k)%N /\ f k + e < g k.
  apply: NNPP => Hn; apply: H => e he.
  apply: NNPP => HN; apply: Hn; exists e; split=> // N.
  apply: NNPP => Hk; apply: HN; exists N => k hk; rewrite leNgt; apply/negP => hlt.
  by apply: Hk; exists k; split.
have he3 : 0 < e / 3 by lra.
have [N hN] := cauchyI hf hg he3 he3; have [k [hk hfk]] := He N.
exists (e / 3); split=> //; exists N => n hn.
by have [? ?] := hN k n hk hn; nlra.
Qed.

Lemma rle_total {f g : rseq} : cauchy f -> cauchy g -> rle f g \/ rle g f.
Proof. by move=> hf hg; case: (rlt_or_rle hf hg) => [/rlt_rle|]; auto. Qed.

Lemma rlt_trichotomy {f g : rseq} : cauchy f -> cauchy g -> rlt f g \/ req f g \/ rlt g f.
Proof.
move=> hf hg; case: (rlt_or_rle hf hg) => [|h1]; first by left.
case: (rlt_or_rle hg hf) => [|h2]; first by right; right.
by right; left; apply: rle_antisym.
Qed.

Lemma rnot_lt {f g : rseq} : cauchy f -> cauchy g -> ~ rlt g f -> rle f g.
Proof. by move=> hf hg H; case: (rlt_or_rle hg hf). Qed.

Lemma rle_not_lt {f g : rseq} : rle f g -> ~ rlt g f.
Proof. by move=> h1 h2; apply: (@rlt_irrefl f); apply: rle_rlt_trans h1 h2. Qed.
(* ------------------------------------------------------------------ *)
(** * 12. Square roots *)

Lemma isqrt_spec (a : nat) :
  (Nat.sqrt a * Nat.sqrt a <= a)%N /\ (a < (Nat.sqrt a).+1 * (Nat.sqrt a).+1)%N.
Proof. by have [h1 h2] := Nat.sqrt_spec' a; split; [apply/ssrnat.leP | apply/ssrnat.ltP]. Qed.

Lemma isqrt_mono {a b : nat} : (a <= b)%N -> (Nat.sqrt a <= Nat.sqrt b)%N.
Proof. by move=> /ssrnat.leP h; apply/ssrnat.leP; apply: Nat.sqrt_le_mono. Qed.

Lemma isqrt_square (a : nat) : Nat.sqrt (a * a)%N = a.
Proof. exact: Nat.sqrt_square. Qed.

Lemma four_pow (k : nat) : (4 ^ k = 2 ^ k * 2 ^ k)%N.
Proof. by rewrite -expnMn. Qed.

Definition rsqrt (n : nat) : rseq := fun k => (Nat.sqrt (n * 4 ^ k)%N)%:R / (2 ^ k)%:R.

Lemma rsqrt_ge0 (n : nat) : forall k, 0 <= rsqrt n k.
Proof. by move=> k; rewrite /rsqrt divr_ge0 ?ler0n. Qed.

Lemma rsqrt_sqr_le (n : nat) : forall k, rsqrt n k * rsqrt n k <= n%:R.
Proof.
move=> k; rewrite /rsqrt mulf_div ler_pdivrMr ?mulr_gt0 ?pow2_gt0 //.
rewrite -!natrM ler_nat -four_pow; exact: (proj1 (isqrt_spec _)).
Qed.

Lemma rsqrt_sqr_gt (n : nat) : forall k, n%:R < (rsqrt n k + 1 / (2 ^ k)%:R) ^+ 2.
Proof.
move=> k; rewrite /rsqrt -mulrDl expr2 mulf_div ltr_pdivlMr ?mulr_gt0 ?pow2_gt0 //.
rewrite -[1](mulr1n (1 : rat)) -mulrSr -!natrM ltr_nat -four_pow.
exact: (proj2 (isqrt_spec _)).
Qed.

Lemma rsqrt_mono {m n : nat} : (m <= n)%N -> forall k, rsqrt m k <= rsqrt n k.
Proof.
move=> hmn k; rewrite /rsqrt ler_wpM2r ?invr_ge0 ?ler0n // ler_nat.
by apply: isqrt_mono; rewrite leq_mul2r hmn orbT.
Qed.

Lemma rsqrt_square (m : nat) : forall k, rsqrt (m * m)%N k = m%:R.
Proof.
move=> k; rewrite /rsqrt (_ : (m * m * 4 ^ k = (m * 2 ^ k) * (m * 2 ^ k))%N).
  by rewrite four_pow mulnACA.
by rewrite isqrt_square natrM mulfK // lt0r_neq0 // pow2_gt0.
Qed.

Lemma rsqrt0 : forall k, rsqrt 0 k = 0.
Proof. by move=> k; rewrite /rsqrt mul0n /= mul0r. Qed.

Lemma rsqrt1 : forall k, rsqrt 1 k = 1.
Proof. by move=> k; have := rsqrt_square 1 k; rewrite muln1. Qed.

Lemma rsqrt_isqrt (n : nat) : forall k, (Nat.sqrt n)%:R <= rsqrt n k.
Proof.
move=> k; rewrite -(rsqrt_square (Nat.sqrt n) k).
exact: rsqrt_mono (proj1 (isqrt_spec n)) k.
Qed.

Lemma rsqrt_ge1 {n : nat} : (0 < n)%N -> forall k, 1 <= rsqrt n k.
Proof. by move=> hn k; rewrite -(rsqrt1 k); apply: rsqrt_mono. Qed.

Lemma rsqrt_lt_isqrt1 (n : nat) : forall k, rsqrt n k < (Nat.sqrt n).+1%:R.
Proof.
move=> k; apply: sqr_lt_lt; first exact: ler0n.
apply: le_lt_trans (rsqrt_sqr_le n k) _; rewrite -natrM ltr_nat.
exact: (proj2 (isqrt_spec n)).
Qed.

Lemma rsqrt_le_isqrt1 (n : nat) : rle (rsqrt n) (cst (Nat.sqrt n).+1%:R).
Proof. by apply: rle_of_ptwise => k; apply/ltW/rsqrt_lt_isqrt1. Qed.

Lemma rsqrt_le_nat (n : nat) : forall k, rsqrt n k <= n%:R.
Proof.
move=> k; apply: sqr_le_le; first exact: ler0n.
apply: le_trans (rsqrt_sqr_le n k) _; rewrite -natrM ler_nat.
by case: n => // n; rewrite leq_pmulr.
Qed.

Lemma rsqrt_close (n : nat) : forall k m, rsqrt n m < rsqrt n k + 1 / (2 ^ k)%:R.
Proof.
move=> k m; apply: sqr_lt_lt.
  by apply: addr_ge0; [apply: rsqrt_ge0 | apply/ltW/inv_pow2_gt0].
by apply: le_lt_trans (rsqrt_sqr_le n m) _; rewrite -expr2; apply: rsqrt_sqr_gt.
Qed.

Lemma rsqrt_cauchy (n : nat) : cauchy (rsqrt n).
Proof.
move=> e he; have [j hj] := pow2_small he; exists j => m p hm hp.
have := rsqrt_close n m p; have := rsqrt_close n p m.
have := inv_pow2_le hm; have := inv_pow2_le hp.
move=> ? ? ? ?; nlra.
Qed.

Lemma rsqrt_sqr (n : nat) : req (rmul (rsqrt n) (rsqrt n)) (cst n%:R).
Proof.
move=> e he; set T : rat := (Nat.sqrt n).+1%:R.
have hT : 0 <= T by apply: ler0n.
have hd : 0 < e / (2 * T + 1) by apply: divr_gt0; lra.
have [j hj] := pow2_small hd; exists j => k hk; rewrite /rmul /cst.
have r0 := rsqrt_ge0 n k; have rT := ltW (rsqrt_lt_isqrt1 n k).
have h1 := rsqrt_sqr_le n k; have h2 := rsqrt_sqr_gt n k.
have d0 := inv_pow2_gt0 k; have d1 := inv_pow2_le1 k; have dj := inv_pow2_le hk.
move: h1 h2 r0 rT d0 d1 dj; rewrite -/T expr2.
set r := rsqrt n k; set d := 1 / (2 ^ k)%:R => h1 h2 r0 rT d0 d1 dj.
have h3 : r * d <= T * d by apply: ler_wpM2r => //; apply: ltW.
have h4 : d * d <= 1 * d by apply: ler_wpM2r => //; apply: ltW.
have h5 : d * (2 * T + 1) < e by rewrite -ltr_pdivlMr; [lra | lra].
nlra.
Qed.

(** Uniqueness of nonnegative square roots. *)

Definition rpos (f : rseq) : rseq := fun k => if 0 <= f k then f k else 0.

Lemma rpos_ge0 (f : rseq) k : 0 <= rpos f k.
Proof. by rewrite /rpos; case: ifP. Qed.

Lemma req_rpos {f : rseq} : rle (cst 0) f -> req f (rpos f).
Proof.
move=> h e he; have he2 : 0 < e / 2 by lra.
apply: ev_mono (h _ he2) => k; rewrite /rpos /cst.
by case: (lerP 0 (f k)) => hk ? /=; nlra.
Qed.

Lemma sqr_inj_nonneg {x y : rseq} : cauchy x -> cauchy y -> rle (cst 0) x -> rle (cst 0) y ->
  req (rmul x x) (rmul y y) -> req x y.
Proof.
move=> hx hy hx0 hy0 hxy.
have ex := req_rpos hx0; have ey := req_rpos hy0.
have H : req (rmul (rpos x) (rpos x)) (rmul (rpos y) (rpos y)).
  apply: req_trans (req_sym (req_rmul hx hx ex ex)) _.
  exact: req_trans hxy (req_rmul hy hy ey ey).
have H' : req (rpos x) (rpos y).
  move=> e he; have he2 : 0 < e * e by apply: mulr_gt0.
  apply: ev_mono (H _ he2) => k hk.
  exact: sq_close (rpos_ge0 _ _) (rpos_ge0 _ _) he hk.
exact: req_trans ex (req_trans H' (req_sym ey)).
Qed.

Lemma rsqrt_mul (m n : nat) : req (rsqrt (m * n)%N) (rmul (rsqrt m) (rsqrt n)).
Proof.
have cm := rsqrt_cauchy m; have cn := rsqrt_cauchy n.
apply: sqr_inj_nonneg.
- exact: rsqrt_cauchy.
- exact: cauchy_mul.
- by apply: rle_of_ptwise => k; apply: rsqrt_ge0.
- by apply: rle_of_ptwise => k; rewrite /rmul /cst mulr_ge0 ?rsqrt_ge0.
apply: req_trans (rsqrt_sqr _) _; apply: req_sym.
have e1 : req (rmul (rmul (rsqrt m) (rsqrt n)) (rmul (rsqrt m) (rsqrt n)))
    (rmul (rmul (rsqrt m) (rsqrt m)) (rmul (rsqrt n) (rsqrt n))).
  by apply: req_of_eq => k; rewrite /rmul; ring.
have e2 := req_rmul (cauchy_mul cm cm) (cauchy_mul cn cn) (rsqrt_sqr m) (rsqrt_sqr n).
apply: req_trans e1 (req_trans e2 _).
by apply: req_of_eq => k; rewrite /rmul /cst natrM.
Qed.

Lemma rsqrt_le_of_sqr {n : nat} {x : rseq} : cauchy x -> rle (cst 0) x ->
  rle (rmul x x) (cst n%:R) -> rle x (rsqrt n).
Proof.
move=> hx hx0 hxx; case: (rlt_or_rle (rsqrt_cauchy n) hx) => [[c [c0 hc]]|//]; exfalso.
have hc3 : 0 < c * c / 3 by apply: divr_gt0 => //; apply: mulr_gt0.
have [N hN] := evI (evI hc (hxx _ hc3)) (rsqrt_sqr n _ hc3).
have [[h1 h2] h3] := hN N (leqnn N); have r0 := rsqrt_ge0 n N.
move: h1 h2 h3 r0; rewrite /rmul /cst.
set r := rsqrt n N; set y := x N => h1 h2 h3 r0.
have h4 : (r + c) * (r + c) <= y * y by apply: ler_pM; lra.
have h5 : 0 <= r * c by apply: mulr_ge0 => //; apply: ltW.
nlra.
Qed.

(* ------------------------------------------------------------------ *)
(** * 13. Positivity and inverses of square roots *)

Lemma rsqrt_pos {z : nat} : (0 < z)%N -> rlt (cst 0) (rsqrt z).
Proof.
move=> hz; apply: (@rlt_of_eventually _ _ 1 ltr01); exists 0%N => k _.
by rewrite /cst add0r; apply: rsqrt_ge1.
Qed.

Lemma rsqrt_neq0 {z : nat} : (0 < z)%N -> forall k, rsqrt z k != 0.
Proof. by move=> hz k; apply: lt0r_neq0; apply: lt_le_trans ltr01 (rsqrt_ge1 hz k). Qed.

Lemma rsqrt_rinv {z : nat} : (0 < z)%N -> forall k, rsqrt z k * rinv (rsqrt z) k = 1.
Proof. by move=> hz k; rewrite /rinv mulfV // rsqrt_neq0. Qed.

Lemma rinv_rsqrt_gt0 {z : nat} : (0 < z)%N -> forall k, 0 < rinv (rsqrt z) k.
Proof. by move=> hz k; rewrite /rinv invr_gt0; apply: lt_le_trans ltr01 (rsqrt_ge1 hz k). Qed.

Lemma rinv_rsqrt_ge0 (z : nat) : forall k, 0 <= rinv (rsqrt z) k.
Proof. by move=> k; rewrite /rinv invr_ge0 rsqrt_ge0. Qed.

Lemma rinv_rsqrt_le1 {z : nat} : (0 < z)%N -> forall k, rinv (rsqrt z) k <= 1.
Proof.
move=> hz k; rewrite /rinv invf_le1 ?rsqrt_ge1 //.
exact: lt_le_trans ltr01 (rsqrt_ge1 hz k).
Qed.

Lemma rinv_rsqrt_mono {m n : nat} : (0 < m)%N -> (m <= n)%N ->
  forall k, rinv (rsqrt n) k <= rinv (rsqrt m) k.
Proof.
move=> hm hmn k; have hn := leq_trans hm hmn.
rewrite /rinv lef_pV2 ?posrE ?rsqrt_mono //.
- exact: lt_le_trans ltr01 (rsqrt_ge1 hn k).
- exact: lt_le_trans ltr01 (rsqrt_ge1 hm k).
Qed.

Lemma rinv_rsqrt_pos {z : nat} : (0 < z)%N -> rlt (cst 0) (rinv (rsqrt z)).
Proof. by move=> hz; apply: rlt_rinv_pos (rsqrt_cauchy z) (rsqrt_pos hz). Qed.

Lemma cauchy_rinv_rsqrt (z : nat) : cauchy (rinv (rsqrt z)).
Proof.
case: z => [|z].
  by apply: (@cauchy_ext (cst 0)) => [k|]; [rewrite /rinv rsqrt0 invr0 | apply: cauchy_cst].
exact: (proj1 (rinv_spec (rsqrt_cauchy _) (rsqrt_pos (ltn0Sn z)))).
Qed.

(* ------------------------------------------------------------------ *)
(** * 14. Telescoping bounds for sum 1/sqrt e *)

Lemma rsqrt_diff_sqr (z : nat) :
  req (rmul (radd (rsqrt z.+1) (rsqrt z)) (rsub (rsqrt z.+1) (rsqrt z))) (cst 1).
Proof.
apply: req_trans (_ : req _ (rsub (rmul (rsqrt z.+1) (rsqrt z.+1)) (rmul (rsqrt z) (rsqrt z)))) _.
  by apply: req_of_eq => k; rewrite /rmul /radd /rsub; ring.
apply: req_trans (req_rsub (rsqrt_sqr z.+1) (rsqrt_sqr z)) _.
by apply: req_of_eq => k; rewrite /rsub /cst mulrSr; lra.
Qed.

Lemma rsqrt_sum_pos (z : nat) : rlt (cst 0) (radd (rsqrt z.+1) (rsqrt z)).
Proof.
apply: (@rlt_of_eventually _ _ 1 ltr01); exists 0%N => k _; rewrite /cst /radd add0r.
by have := rsqrt_ge1 (ltn0Sn z) k; have := rsqrt_ge0 z k; lra.
Qed.

Lemma rsqrt_diff_scaled (z : nat) :
  req (rmul (radd (rsqrt z.+1) (rsqrt z)) (rmul (cst 2) (rsub (rsqrt z.+1) (rsqrt z)))) (cst 2).
Proof.
apply: req_trans (_ : req _ (rmul (cst 2) (rmul (radd (rsqrt z.+1) (rsqrt z))
                                                 (rsub (rsqrt z.+1) (rsqrt z))))) _.
  by apply: req_of_eq => k; rewrite /rmul /cst; ring.
apply: req_trans (req_rmul_cst 2 (rsqrt_diff_sqr z)) _.
by apply: req_of_eq => k; rewrite /rmul /cst mulr1.
Qed.

Lemma rinv_rsqrt_le (z : nat) :
  rle (rinv (rsqrt z.+1)) (rmul (cst 2) (rsub (rsqrt z.+1) (rsqrt z))).
Proof.
apply: (rle_rmul_cancel_l (rsqrt_sum_pos z)).
apply: rle_req_trans _ (req_sym (rsqrt_diff_scaled z)).
apply: rle_of_ptwise => k; rewrite /rmul /radd /rinv /cst.
have ha := rsqrt_ge1 (ltn0Sn z) k; have hb := rsqrt_mono (leqnSn z) k.
by rewrite ler_pdivrMr; lra.
Qed.

Lemma rsqrt_diff_le_rinv {z : nat} : (1 <= z)%N ->
  rle (rmul (cst 2) (rsub (rsqrt z.+1) (rsqrt z))) (rinv (rsqrt z)).
Proof.
move=> hz; apply: (rle_rmul_cancel_l (rsqrt_sum_pos z)).
apply: req_rle_trans (rsqrt_diff_scaled z) _.
apply: rle_of_ptwise => k; rewrite /rmul /radd /rinv /cst.
have ha := rsqrt_ge1 hz k; have hb := rsqrt_mono (leqnSn z) k.
by rewrite ler_pdivlMr; lra.
Qed.

Definition G (z : nat) : rseq := rsum (fun e => rinv (rsqrt e)) (iota 1 z).
Definition E (z : nat) : rseq := rsub (G z) (rmul (cst 2) (rsqrt z)).

Lemma G_succ_pt (z : nat) k : G z.+1 k = G z k + rinv (rsqrt z.+1) k.
Proof. by rewrite /G /rsum; have := iotaD 1 z 1; rewrite addn1 => ->; rewrite big_cat /= big_seq1 add1n. Qed.

Lemma G0 k : G 0 k = 0.
Proof. by rewrite /G /rsum big_nil. Qed.

Lemma cauchy_G (z : nat) : cauchy (G z).
Proof. by apply: cauchy_rsum => n _; apply: cauchy_rinv_rsqrt. Qed.

Lemma cauchy_E (z : nat) : cauchy (E z).
Proof. by apply: cauchy_sub (cauchy_G z) (cauchy_mul (cauchy_cst 2) (rsqrt_cauchy z)). Qed.

Lemma E_decr (z : nat) : rle (E z.+1) (E z).
Proof.
move=> e he; apply: ev_mono (rinv_rsqrt_le z e he) => k.
by rewrite /E /rsub /rmul /cst G_succ_pt; lra.
Qed.

Lemma E0 k : E 0 k = 0.
Proof. by rewrite /E /rsub /rmul /cst G0 rsqrt0 mulr0 subr0. Qed.

Lemma E_le (z : nat) : rle (E z) (cst 0).
Proof.
elim: z => [|z IH]; first by apply: rle_of_ptwise => k; rewrite E0.
exact: rle_trans (E_decr z) IH.
Qed.

Lemma G_lower (z : nat) : rle (rmul (cst 2) (rsub (rsqrt z.+1) (cst 1))) (G z).
Proof.
elim: z => [|z IH].
  by apply: rle_of_ptwise => k; rewrite /rmul /rsub /cst rsqrt1 G0; lra.
move=> e he; have he2 : 0 < e / 2 by lra.
apply: ev_mono (evI (IH _ he2) (rsqrt_diff_le_rinv (ltn0Sn z) _ he2)) => k [h1 h2].
by move: h1 h2; rewrite /rmul /rsub /cst G_succ_pt; lra.
Qed.

Lemma E_ge (z : nat) : rle (cst (-2)) (E z).
Proof.
move=> e he; apply: ev_mono (G_lower z e he) => k.
by have := rsqrt_mono (leqnSn z) k; rewrite /E /rmul /rsub /cst; lra.
Qed.

Lemma G_le (z : nat) : rle (G z) (rmul (cst 2) (rsqrt z)).
Proof. by move=> e he; apply: ev_mono (E_le z e he) => k; rewrite /E /rsub /rmul /cst; lra. Qed.

Lemma harm_le_sqrt (n : nat) :
  rle (cst (\sum_(1 <= i < n.+1) 1 / i%:R)) (rmul (cst 2) (rsqrt n)).
Proof.
have -> : \sum_(1 <= i < n.+1) 1 / i%:R = \sum_(i <- iota 1 n) 1 / (i%:R : rat).
  by rewrite /index_iota subSS subn0.
apply: req_rle_trans (req_sym (rsum_cst (fun i => 1 / i%:R) _)) _.
apply: rle_trans (G_le n); apply: rle_rsum => i; rewrite mem_iota => /andP [hi _].
apply: rle_of_ptwise => k; rewrite /cst /rinv.
have h1 := rsqrt_ge1 hi k; have h2 := rsqrt_le_nat i k.
rewrite div1r lef_pV2 // posrE; last lra.
by rewrite ltr0n.
Qed.

Lemma rsqrt_floor_div (x d : nat) : (1 <= d <= x)%N ->
  rle (rabs (rsub (rsqrt x) (rmul (rsqrt d) (rsqrt (x %/ d)))))
      (rdiv (cst d%:R) (rsqrt x)).
Proof.
case/andP => hd hdx.
have hmx : (d * (x %/ d) <= x)%N by rewrite mulnC leq_divM.
have hxm : (x < d * (x %/ d) + d)%N.
  by rewrite mulnC {1}(divn_eq x d) ltn_add2l ltn_pmod.
have hx1 : (0 < x)%N := leq_trans hd hdx.
apply: req_rle_trans
  (req_rabs (req_rsub (req_refl (rsqrt x)) (req_sym (rsqrt_mul d (x %/ d))))) _.
apply: (rle_rmul_cancel_l (rsqrt_pos hx1)).
apply: rle_trans (_ : rle _ (rsub (rmul (rsqrt x) (rsqrt x))
                                  (rmul (rsqrt (d * (x %/ d))) (rsqrt (d * (x %/ d)))))) _.
  apply: rle_of_ptwise => k; rewrite /rmul /rabs /rsub.
  have hm := rsqrt_mono hmx k; have hm0 := rsqrt_ge0 (d * (x %/ d)) k.
  rewrite ger0_norm ?subr_ge0 //.
  have : 0 <= rsqrt (d * (x %/ d)) k * (rsqrt x k - rsqrt (d * (x %/ d)) k).
    by apply: mulr_ge0 => //; rewrite subr_ge0.
  lra.
apply: rle_trans (req_rle (req_rsub (rsqrt_sqr x) (rsqrt_sqr _))) _.
apply: rle_trans (_ : rle _ (cst d%:R)) _.
  apply: rle_of_ptwise => k; rewrite /rsub /cst lerBlDr -natrD ler_nat addnC.
  exact: ltnW.
apply: rle_of_ptwise => k; rewrite /rmul /rdiv /cst mulrC divfK //.
exact: rsqrt_neq0.
Qed.
