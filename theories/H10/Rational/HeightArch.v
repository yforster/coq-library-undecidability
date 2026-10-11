(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Archimedean estimates for the height inequalities of HeightLower.v
   (PLAN P13): bounds for |aE| and |aE'| ([A0]), the elementary
   inequality behind Gauss's lemma in degree 2 ([gelfond2]), the forms
   Nd, Dd of the duplication map with their Bezout identities
   ([bezout1], [bezout2]) and the resulting estimate [D_arch]
     |16 a^3| max(|X|,|Z|)^4 <= KD max(|Nd a X Z|, |Dd a X Z|),
   and the estimate [U_arch] for the coefficients of the quadratic whose
   roots are x(T1 + T2), x(T1 - T2).

   All statements are about the real field [RF] (NFHeight.v), i.e. about
   the first real embedding; the second one is obtained by applying them
   to conjugates.

   Implementation note: never close a goal about [RF] with [done] (or
   [by], [//]) unless it is closed syntactically: [done] may try expensive
   conversions through the order structure (transported from [algC]).
   Use [reflexivity], [exact], [lra]. Likewise avoid [set] and unguided
   rewrites with [normrM] (they unfold powers).

   No axioms. *)

From HB Require Import structures.
From mathcomp Require Import boot order algebra.

From Undecidability.H10.Rational Require Import FixedData GroupLaw NFHeight.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.

Local Open Scope ring_scope.

(** * 1. Archimedean estimates in RF *)

(* a bound for |aE| and |aE'|, via aE = - dF^2, dF = 75 - 53 sqrt2
   (no large numerals: MathComp naturals are unary) *)
HB.lock Definition A0 : RF := 2%:R ^+ 16.
Lemma A0E : A0 = 2%:R ^+ 16. Proof. by rewrite unlock. Qed.

Lemma A0_ge0 : 0 <= A0. Proof. by rewrite A0E exprn_ge0 ?ler0n. Qed.
Lemma A0_ge1 : 1 <= A0. Proof. by rewrite A0E exprn_ege1 ?ler1n. Qed.

Lemma dF_RF : (dF : RF) = QE 75%:R (- 53%:R). Proof. by []. Qed.

Lemma aE_dF : (aE : RF) = - ((dF : RF) * dF).
Proof. exact: aE_spec. Qed.

Lemma dF_le (d : RF) : d = dF \/ d = cj dF -> `|d| <= 2%:R ^+ 8.
Proof.
  have h : (75 + 2 * 53 <= 2 ^ 8)%N by vm_compute.
  move=> hd; have [a [b [ed [ha hb]]]] : exists a b : rat, d = QE a b /\ `|a| = 75%:R /\ `|b| = 53%:R.
  { case: hd => ->.
    - exists 75%:R, (- 53%:R); split; first exact: dF_RF.
      by split; [ exact: normr_nat | rewrite normrN normr_nat ].
    - exists 75%:R, (- - 53%:R); split; first by rewrite /cj /qe_conj dF_RF.
      by split; [ exact: normr_nat | rewrite normrN normrN normr_nat ]. }
  rewrite ed; apply: le_trans (norm_QE_le _ _) _.
  by rewrite -qr_nat -qr_expn qr_le ha hb -natrM -natrD -natrX ler_nat.
Qed.

Lemma aE_bound : `|aE : RF| <= A0.
Proof.
  rewrite aE_dF normrN normrM A0E (_ : 16 = 8 + 8)%N // exprD.
  by apply: ler_pM; rewrite ?normr_ge0 ?dF_le //; left.
Qed.

Lemma aE_cj_bound : `|cj aE| <= A0.
Proof.
  rewrite aE_dF cj_opp cj_mul normrN normrM A0E (_ : 16 = 8 + 8)%N // exprD.
  by apply: ler_pM; rewrite ?normr_ge0 ?dF_le //; right.
Qed.

Lemma aE_neq0 : (aE : RF) != 0.
Proof. exact: (aE_neq0_QF rat_sq2). Qed.

Lemma cj_aE_neq0 : cj (aE : RF) != 0.
Proof. by rewrite cj_eq0 aE_neq0. Qed.

Lemma isI_aE : isI (aE : RF).
Proof.
  rewrite aE_dF; apply/isI_opp/isI_mul; by exists 75, (- 53); rewrite dF_RF intrN.
Qed.

(* aE as an element of RF: arithmetic on [aF] uses the operations of
   [RF], arithmetic on [aE] those of [qe rat] (convertible, but unifying
   the two can be very slow).
   It is locked: unfolding it exposes large unary numerals, which makes
   unification (e.g. in [rewrite]) hang. *)
HB.lock Definition aF : RF := aE.

Lemma aFE : aF = aE. Proof. by rewrite unlock. Qed.
Lemma aF_bound : `|aF| <= A0. Proof. rewrite aFE; exact: aE_bound. Qed.
Lemma aF_cj_bound : `|cj aF| <= A0. Proof. rewrite aFE; exact: aE_cj_bound. Qed.
Lemma aF_neq0 : aF != 0. Proof. rewrite aFE; exact: aE_neq0. Qed.
Lemma isI_aF : isI aF. Proof. rewrite aFE; exact: isI_aE. Qed.

(* monomials *)
Lemma lexp (u v : RF) n : 0 <= u -> u <= v -> u ^+ n <= v ^+ n.
Proof. by move=> h0 h; apply: lerXn2r; rewrite ?nnegrE //; apply: le_trans h. Qed.

Lemma mon (t x z A m : RF) (i j k : nat) :
  `|t| <= A -> `|x| <= m -> `|z| <= m ->
  `|t ^+ i * x ^+ j * z ^+ k| <= A ^+ i * m ^+ (j + k).
Proof.
  move=> ht hx hz; rewrite !normrM !normrX exprD mulrA.
  apply: ler_pM; rewrite ?mulr_ge0 ?exprn_ge0 ?normr_ge0 //; last exact: lexp.
  apply: ler_pM; rewrite ?exprn_ge0 ?normr_ge0 //; exact: lexp.
Qed.

Lemma normc (c : nat) (v : RF) : `|c%:R * v| = c%:R * `|v|.
Proof. by rewrite normrM normr_nat. Qed.

(** ** The elementary inequality behind Gauss's lemma for degree 2 *)

Lemma mx_eq_l a b : `|b| <= `|a| -> mx a b = `|a|.
Proof. by move=> h; rewrite /mx max_l. Qed.
Lemma mx_eq_r a b : `|a| <= `|b| -> mx a b = `|b|.
Proof. by move=> h; rewrite /mx max_r. Qed.

Lemma gelfond2 (g1 d1 g2 d2 : RF) :
  mx g1 d1 * mx g2 d2 <= `|d1 * d2| + `|g1 * d2 + g2 * d1| + `|g1 * g2|.
Proof.
  have h0 := normr_ge0 (g1 * d2 + g2 * d1).
  have h1 := normr_ge0 (d1 * d2); have h2 := normr_ge0 (g1 * g2).
  have mix (p q r s : RF) : `|p| <= `|q| -> `|s| <= `|r| ->
    `|q| * `|r| <= `|q * s| + `|p * s + r * q| + `|p * r|.
  { move=> hpq hsr.
    have e : r * q = (p * s + r * q) - p * s by ring.
    have t := ler_normB (p * s + r * q) (p * s).
    rewrite -e normrM in t.
    have t2 : `|p * s| <= `|q * s| by rewrite !normrM ler_wpM2r ?normr_ge0.
    have := normr_ge0 (p * r); rewrite [`|r| * _]mulrC in t; lra. }
  case: (lerP `|g1| `|d1|) => c1; case: (lerP `|g2| `|d2|) => c2.
  - rewrite (mx_eq_r c1) (mx_eq_r c2) -normrM; lra.
  - rewrite (mx_eq_r c1) (mx_eq_l (ltW c2)).
    by have := mix _ _ _ _ c1 (ltW c2).
  - rewrite (mx_eq_l (ltW c1)) (mx_eq_r c2).
    have h := mix _ _ _ _ c2 (ltW c1).
    rewrite [g2 * d1 + _]addrC !normrM in h *; lra.
  - rewrite (mx_eq_l (ltW c1)) (mx_eq_l (ltW c2)) -normrM; lra.
Qed.

(** ** The forms of the duplication map and their Bezout identities *)

Definition Nd (a X Z : RF) : RF := (X ^+ 2 - a * Z ^+ 2) ^+ 2.
Definition Dd (a X Z : RF) : RF := 4%:R * X * Z * (X ^+ 2 + a * Z ^+ 2).
Definition F1 (a X Z : RF) : RF := 16%:R * X ^+ 3 + 12%:R * (a * X * Z ^+ 2).
Definition G1 (a X Z : RF) : RF := 5%:R * (a * X ^+ 2 * Z) - 3%:R * (a ^+ 2 * Z ^+ 3).
Definition F2 (a X Z : RF) : RF := 16%:R * (a * Z ^+ 3) + 12%:R * (X ^+ 2 * Z).
Definition G2 (a X Z : RF) : RF := 5%:R * (a * X * Z ^+ 2) - 3%:R * X ^+ 3.

Lemma bezout1 a X Z : F1 a X Z * Nd a X Z + G1 a X Z * Dd a X Z = 16%:R * X ^+ 7.
Proof. by rewrite /F1 /G1 /Nd /Dd; ring. Qed.

Lemma bezout2 a X Z : F2 a X Z * Nd a X Z + G2 a X Z * Dd a X Z = 16%:R * a ^+ 3 * Z ^+ 7.
Proof. by rewrite /F2 /G2 /Nd /Dd; ring. Qed.

HB.lock Definition KD : RF := A0 ^+ 3 * (16%:R + 17%:R * A0 + 3%:R * A0 ^+ 2) + 21%:R * A0 + 15%:R.
Lemma KDE : KD = A0 ^+ 3 * (16%:R + 17%:R * A0 + 3%:R * A0 ^+ 2) + 21%:R * A0 + 15%:R.
Proof. by rewrite unlock. Qed.

Lemma KD_poly_ge0 : 0 <= 16%:R + 17%:R * A0 + 3%:R * A0 ^+ 2.
Proof. have h := A0_ge1; have p2 := exprn_ge0 2 A0_ge0; lra. Qed.

Lemma KD_head_ge0 : 0 <= A0 ^+ 3 * (16%:R + 17%:R * A0 + 3%:R * A0 ^+ 2).
Proof. exact: (mulr_ge0 (exprn_ge0 3 A0_ge0) KD_poly_ge0). Qed.

Lemma KD_ge1 : 1 <= KD.
Proof. have h := A0_ge1; have h3 := KD_head_ge0; rewrite KDE; lra. Qed.

Lemma D_arch (a X Z : RF) : `|a| <= A0 ->
  `|16%:R * a ^+ 3| * mx X Z ^+ 4 <= KD * mx (Nd a X Z) (Dd a X Z).
Proof.
  move=> ha; set m := mx X Z; set M := mx (Nd a X Z) (Dd a X Z).
  have hX : `|X| <= m := mx_gel X Z. have hZ : `|Z| <= m := mx_ger X Z.
  have hm : 0 <= m := mx_ge0 X Z. have hM : 0 <= M := mx_ge0 _ _.
  have hA := A0_ge0. have hA1 := A0_ge1.
  have hNd : `|Nd a X Z| <= M := mx_gel _ _. have hDd : `|Dd a X Z| <= M := mx_ger _ _.
  have ht : `|a| <= A0 := ha.
  (* the Bezout identities, estimated *)
  have bF1 : `|F1 a X Z| <= (16%:R + 12%:R * A0) * m ^+ 3.
  { rewrite /F1; apply: le_trans (ler_normD _ _) _; rewrite !normc.
    have e1 : X ^+ 3 = a ^+ 0 * X ^+ 3 * Z ^+ 0 by ring.
    have e2 : a * X * Z ^+ 2 = a ^+ 1 * X ^+ 1 * Z ^+ 2 by ring.
    have b1 := mon 0 3 0 ht hX hZ; have b2 := mon 1 1 2 ht hX hZ.
    rewrite -e1 in b1; rewrite -e2 in b2; rewrite expr0 mul1r in b1; rewrite expr1 in b2.
    lra. }
  have bG1 : `|G1 a X Z| <= (5%:R * A0 + 3%:R * A0 ^+ 2) * m ^+ 3.
  { rewrite /G1; apply: le_trans (ler_normB _ _) _; rewrite !normc.
    have e1 : a * X ^+ 2 * Z = a ^+ 1 * X ^+ 2 * Z ^+ 1 by ring.
    have e2 : a ^+ 2 * Z ^+ 3 = a ^+ 2 * X ^+ 0 * Z ^+ 3 by ring.
    have b1 := mon 1 2 1 ht hX hZ; have b2 := mon 2 0 3 ht hX hZ.
    rewrite -e1 in b1; rewrite -e2 in b2; rewrite expr1 in b1.
    lra. }
  have bF2 : `|F2 a X Z| <= (16%:R * A0 + 12%:R) * m ^+ 3.
  { rewrite /F2; apply: le_trans (ler_normD _ _) _; rewrite !normc.
    have e1 : a * Z ^+ 3 = a ^+ 1 * X ^+ 0 * Z ^+ 3 by ring.
    have e2 : X ^+ 2 * Z = a ^+ 0 * X ^+ 2 * Z ^+ 1 by ring.
    have b1 := mon 1 0 3 ht hX hZ; have b2 := mon 0 2 1 ht hX hZ.
    rewrite -e1 in b1; rewrite -e2 in b2; rewrite expr1 in b1; rewrite expr0 mul1r in b2.
    lra. }
  have bG2 : `|G2 a X Z| <= (5%:R * A0 + 3%:R) * m ^+ 3.
  { rewrite /G2; apply: le_trans (ler_normB _ _) _; rewrite !normc.
    have e1 : a * X * Z ^+ 2 = a ^+ 1 * X ^+ 1 * Z ^+ 2 by ring.
    have e2 : X ^+ 3 = a ^+ 0 * X ^+ 3 * Z ^+ 0 by ring.
    have b1 := mon 1 1 2 ht hX hZ; have b2 := mon 0 3 0 ht hX hZ.
    rewrite -e1 in b1; rewrite -e2 in b2; rewrite expr1 in b1; rewrite expr0 mul1r in b2.
    lra. }
  have hm3 : 0 <= m ^+ 3 := exprn_ge0 3 hm.
  have tri (f g : RF) : `|f * Nd a X Z + g * Dd a X Z| <= (`|f| + `|g|) * M.
  { apply: le_trans (ler_normD _ _) _; rewrite (normrM f) (normrM g) mulrDl.
    apply: lerD.
    - apply: ler_wpM2l; [ exact: normr_ge0 | exact: hNd ].
    - apply: ler_wpM2l; [ exact: normr_ge0 | exact: hDd ]. }
  have hKD : KD = A0 ^+ 3 * (16%:R + 17%:R * A0 + 3%:R * A0 ^+ 2) + (21%:R * A0 + 15%:R).
  { rewrite KDE; ring. }
  have hP := KD_head_ge0.
  have ha3 : `|a| ^+ 3 <= A0 ^+ 3 := lexp 3 (normr_ge0 a) ha.
  have hMm : 0 <= m ^+ 3 * M := mulr_ge0 hm3 hM.
  have hC1 := KD_poly_ge0.
  have hC2 : 0 <= 21%:R * A0 + 15%:R by lra.
  have hKY : KD * (m ^+ 3 * M) = A0 ^+ 3 * ((16%:R + 17%:R * A0 + 3%:R * A0 ^+ 2) * m ^+ 3 * M)
                                + (21%:R * A0 + 15%:R) * m ^+ 3 * M.
  { rewrite KDE; ring. }
  have hC2Y : 0 <= (21%:R * A0 + 15%:R) * m ^+ 3 * M := mulr_ge0 (mulr_ge0 hC2 hm3) hM.
  have hC1Y : 0 <= (16%:R + 17%:R * A0 + 3%:R * A0 ^+ 2) * m ^+ 3 * M := mulr_ge0 (mulr_ge0 hC1 hm3) hM.
  have hA3 := mulr_ge0 (exprn_ge0 3 hA) hC1Y.
  (* the X-estimate *)
  have eX : `|16%:R * a ^+ 3| * `|X| ^+ 7 <= KD * (m ^+ 3 * M).
  { have E := bezout1 a X Z.
    have -> : `|16%:R * a ^+ 3| * `|X| ^+ 7 = `|a| ^+ 3 * `|F1 a X Z * Nd a X Z + G1 a X Z * Dd a X Z|.
    { rewrite E (normrM 16%:R (a ^+ 3)) (normrM 16%:R (X ^+ 7)) !normrX normr_nat; ring. }
    have b : `|F1 a X Z| + `|G1 a X Z| <= (16%:R + 17%:R * A0 + 3%:R * A0 ^+ 2) * m ^+ 3 by lra.
    have b' := ler_wpM2r hM b.
    have t := tri (F1 a X Z) (G1 a X Z).
    have hs : 0 <= (`|F1 a X Z| + `|G1 a X Z|) * M.
    { exact: (mulr_ge0 (addr_ge0 (normr_ge0 _) (normr_ge0 _)) hM). }
    have t1 := ler_wpM2l (exprn_ge0 3 (normr_ge0 a)) t.
    have t2 := ler_pM (exprn_ge0 3 (normr_ge0 a)) hs ha3 b'.
    lra. }
  (* the Z-estimate *)
  have eZ : `|16%:R * a ^+ 3| * `|Z| ^+ 7 <= KD * (m ^+ 3 * M).
  { have E := bezout2 a X Z.
    have -> : `|16%:R * a ^+ 3| * `|Z| ^+ 7 = `|F2 a X Z * Nd a X Z + G2 a X Z * Dd a X Z|.
    { rewrite E (normrM (16%:R * a ^+ 3) (Z ^+ 7)) (normrM 16%:R (a ^+ 3)) !normrX normr_nat; ring. }
    have t := tri (F2 a X Z) (G2 a X Z).
    have b : `|F2 a X Z| + `|G2 a X Z| <= (21%:R * A0 + 15%:R) * m ^+ 3 by lra.
    have b' := ler_wpM2r hM b.
    lra. }
  (* combine: m^7 = |X|^7 or |Z|^7 *)
  have e7 : `|16%:R * a ^+ 3| * m ^+ 7 <= KD * (m ^+ 3 * M).
  { case: (mx_cases X Z) => e.
    - have em : m ^+ 7 = `|X| ^+ 7 by rewrite /m e; reflexivity.
      rewrite em; exact: eX.
    - have em : m ^+ 7 = `|Z| ^+ 7 by rewrite /m e; reflexivity.
      rewrite em; exact: eZ. }
  case: (eqVneq m 0) => [ m0 | nm ].
  - rewrite m0 expr0n /= mulr0; exact: (mulr_ge0 (le_trans ler01 KD_ge1) hM).
  - have pm1 : 0 < m by rewrite lt_def nm hm.
    have pm : 0 < m ^+ 3 := exprn_gt0 3 pm1.
    have h : `|16%:R * a ^+ 3| * m ^+ 4 * m ^+ 3 <= KD * M * m ^+ 3 by lra.
    by move: h; rewrite (ler_pM2r pm).
Qed.

(** ** The coefficients of the quadratic with roots x(T1 + T2), x(T1 - T2) *)

HB.lock Definition KU : RF := (A0 + 3%:R) ^+ 2.
Lemma KUE : KU = (A0 + 3%:R) ^+ 2. Proof. by rewrite unlock. Qed.

Lemma KU_ge1 : 1 <= KU.
Proof.
  have h := A0_ge0; rewrite KUE.
  have h1 : 1 <= A0 + 3%:R by lra.
  have := ler_pM ler01 ler01 h1 h1; rewrite mul1r -expr2; exact.
Qed.

Lemma U_arch (a a1 b1 a2 b2 g1 d1 g2 d2 mu : RF) : `|a| <= A0 ->
  (a1 * b2 - a2 * b1) ^+ 2 = mu * (d1 * d2) ->
  2%:R * (a1 * b2 + a2 * b1) * (a1 * a2 + a * (b1 * b2)) = mu * (g1 * d2 + g2 * d1) ->
  (a1 * a2 - a * (b1 * b2)) ^+ 2 = mu * (g1 * g2) ->
  `|mu| * (mx g1 d1 * mx g2 d2) <= KU * (mx a1 b1 * mx a2 b2) ^+ 2.
Proof.
  move=> ha e0 e1 e2.
  have hm1 := mx_ge0 a1 b1; have hm2 := mx_ge0 a2 b2.
  have hP := mulr_ge0 hm1 hm2.
  have pr (u v : RF) : `|u| <= mx a1 b1 -> `|v| <= mx a2 b2 -> `|u * v| <= mx a1 b1 * mx a2 b2.
  { move=> hu hv; rewrite (normrM u v); exact: (ler_pM (normr_ge0 _) (normr_ge0 _) hu hv). }
  have t1 := pr _ _ (mx_gel a1 b1) (mx_ger a2 b2).
  have t2 : `|a2 * b1| <= mx a1 b1 * mx a2 b2.
  { rewrite mulrC; exact: (pr _ _ (mx_ger a1 b1) (mx_gel a2 b2)). }
  have t3 := pr _ _ (mx_gel a1 b1) (mx_gel a2 b2).
  have t4 := pr _ _ (mx_ger a1 b1) (mx_ger a2 b2).
  have t5 : `|a * (b1 * b2)| <= A0 * (mx a1 b1 * mx a2 b2).
  { rewrite (normrM a (b1 * b2)); exact: (ler_pM (normr_ge0 _) (normr_ge0 _) ha t4). }
  have u1 : `|a1 * b2 - a2 * b1| <= 2%:R * (mx a1 b1 * mx a2 b2).
  { have := ler_normB (a1 * b2) (a2 * b1); lra. }
  have u2 : `|a1 * b2 + a2 * b1| <= 2%:R * (mx a1 b1 * mx a2 b2).
  { have := ler_normD (a1 * b2) (a2 * b1); lra. }
  have u3 : `|a1 * a2 + a * (b1 * b2)| <= (1 + A0) * (mx a1 b1 * mx a2 b2).
  { have := ler_normD (a1 * a2) (a * (b1 * b2)); lra. }
  have u4 : `|a1 * a2 - a * (b1 * b2)| <= (1 + A0) * (mx a1 b1 * mx a2 b2).
  { have := ler_normB (a1 * a2) (a * (b1 * b2)); lra. }
  have hA := A0_ge0.
  have W0 : `|mu * (d1 * d2)| <= (2%:R * (mx a1 b1 * mx a2 b2)) ^+ 2.
  { rewrite -e0 normrX; exact: (lexp 2 (normr_ge0 _) u1). }
  have W2 : `|mu * (g1 * g2)| <= ((1 + A0) * (mx a1 b1 * mx a2 b2)) ^+ 2.
  { rewrite -e2 normrX; exact: (lexp 2 (normr_ge0 _) u4). }
  have W1 : `|mu * (g1 * d2 + g2 * d1)|
            <= 2%:R * (2%:R * (mx a1 b1 * mx a2 b2)) * ((1 + A0) * (mx a1 b1 * mx a2 b2)).
  { rewrite -e1 (normrM (2%:R * (a1 * b2 + a2 * b1))) (normrM 2%:R) normr_nat -mulrA -[X in _ <= X]mulrA.
    apply: ler_wpM2l; first exact: ler0n.
    exact: (ler_pM (normr_ge0 _) (normr_ge0 _) u2 u3). }
  rewrite (normrM mu (d1 * d2)) in W0; rewrite (normrM mu (g1 * g2)) in W2.
  rewrite (normrM mu (g1 * d2 + g2 * d1)) in W1.
  have G := ler_wpM2l (normr_ge0 mu) (gelfond2 g1 d1 g2 d2).
  rewrite KUE; nra.
Qed.
