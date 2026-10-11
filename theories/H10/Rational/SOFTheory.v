(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A: a library of setoid lemmas over [SRing] and [SOF] with the
   names of the MathComp lemmas that the analysis files use (see the
   translation table in SETOID.md). Every equation is stated with [≡],
   every MathComp boolean equivalence [(a <= b) = (c <= d)] as an [<->].

   All lemmas live in the module [SOFTheory]; import it AFTER MathComp's
   [GRing.Theory Num.Theory Order.TTheory] so that its names shadow the
   MathComp ones (use [GRing.Theory.mulr0] etc. for the latter). *)

From Stdlib Require Import Setoid Morphisms RelationClasses ZArith.
From Stdlib Require Import Ring Field Ring_theory Field_theory.

From Undecidability.H10.Rational Require Import SOF SOFTactics.

From mathcomp Require Import boot order algebra.

Local Open Scope sof_scope.

Module SOFTheory.

(** * Setoid rings (hold for an [SOF] and for [qe R]) *)

Section sring.

  Variable R : SRing.

  Add Ring sth_ring : (sr_rth R) (setoid (sr_setoid R) (sr_ext R),
    morphism (of_Z_morph R), constants [sof_cst], power_tac (sr_pow_th R) [sof_pow_cst]).

  Implicit Types x y z t : R.

  Lemma addr0 x : x + 0 ≡ x. Proof. sring. Qed.
  Lemma add0r x : 0 + x ≡ x. Proof. sring. Qed.
  Lemma addrC x y : x + y ≡ y + x. Proof. sring. Qed.
  Lemma addrA x y z : x + (y + z) ≡ x + y + z. Proof. sring. Qed.
  Lemma addrAC x y z : x + y + z ≡ x + z + y. Proof. sring. Qed.
  Lemma addrCA x y z : x + (y + z) ≡ y + (x + z). Proof. sring. Qed.
  Lemma addNr x : - x + x ≡ 0. Proof. sring. Qed.
  Lemma addrN x : x + - x ≡ 0. Proof. sring. Qed.
  Lemma subrr x : x - x ≡ 0. Proof. sring. Qed.
  Lemma subr0 x : x - 0 ≡ x. Proof. sring. Qed.
  Lemma sub0r x : 0 - x ≡ - x. Proof. sring. Qed.
  Lemma opprK x : - - x ≡ x. Proof. sring. Qed.
  Lemma oppr0 : - (0 : R) ≡ 0. Proof. sring. Qed.
  Lemma opprD x y : - (x + y) ≡ - x - y. Proof. sring. Qed.
  Lemma opprB x y : - (x - y) ≡ y - x. Proof. sring. Qed.
  Lemma addrK y x : x + y - y ≡ x. Proof. sring. Qed.
  Lemma subrK y x : x - y + y ≡ x. Proof. sring. Qed.
  Lemma addKr x y : - x + (x + y) ≡ y. Proof. sring. Qed.
  Lemma addNKr x y : x + (- x + y) ≡ y. Proof. sring. Qed.
  Lemma subrKC x y : x + (y - x) ≡ y. Proof. sring. Qed.
  Lemma subKr x y : x - (x - y) ≡ y. Proof. sring. Qed.
  Lemma subrKB x y z : (x - z) - (y - z) ≡ x - y. Proof. sring. Qed.
  Lemma mulr0 x : x * 0 ≡ 0. Proof. sring. Qed.
  Lemma mul0r x : 0 * x ≡ 0. Proof. sring. Qed.
  Lemma mulr1 x : x * 1 ≡ x. Proof. sring. Qed.
  Lemma mul1r x : 1 * x ≡ x. Proof. sring. Qed.
  Lemma mulrC x y : x * y ≡ y * x. Proof. sring. Qed.
  Lemma mulrA x y z : x * (y * z) ≡ x * y * z. Proof. sring. Qed.
  Lemma mulrAC x y z : x * y * z ≡ x * z * y. Proof. sring. Qed.
  Lemma mulrCA x y z : x * (y * z) ≡ y * (x * z). Proof. sring. Qed.
  Lemma mulrDl x y z : (x + y) * z ≡ x * z + y * z. Proof. sring. Qed.
  Lemma mulrDr x y z : x * (y + z) ≡ x * y + x * z. Proof. sring. Qed.
  Lemma mulrBl x y z : (x - y) * z ≡ x * z - y * z. Proof. sring. Qed.
  Lemma mulrBr x y z : x * (y - z) ≡ x * y - x * z. Proof. sring. Qed.
  Lemma mulrN x y : x * - y ≡ - (x * y). Proof. sring. Qed.
  Lemma mulNr x y : - x * y ≡ - (x * y). Proof. sring. Qed.
  Lemma mulrNN x y : - x * - y ≡ x * y. Proof. sring. Qed.
  Lemma mulN1r x : - (1) * x ≡ - x. Proof. sring. Qed.
  Lemma mulrN1 x : x * - (1) ≡ - x. Proof. sring. Qed.
  Lemma mulr2n x : x + x ≡ 2%:R * x. Proof. sring. Qed.
  Lemma mulr_natl x n : n%:R * x ≡ x * n%:R. Proof. sring. Qed.

  Lemma expr0 x : x ^+ 0 ≡ 1. Proof. reflexivity. Qed.
  Lemma expr1 x : x ^+ 1 ≡ x. Proof. sring. Qed.
  Lemma expr2 x : x ^+ 2 ≡ x * x. Proof. sring. Qed.
  Lemma exprS x n : x ^+ n.+1 ≡ x * x ^+ n. Proof. reflexivity. Qed.
  Lemma exprD x m n : x ^+ (m + n) ≡ x ^+ m * x ^+ n. Proof. exact (pow_add R x m n). Qed.
  Lemma exprSr x n : x ^+ n.+1 ≡ x ^+ n * x.
  Proof. rewrite -addn1 exprD expr1; reflexivity. Qed.
  Lemma exprMn x y n : (x * y) ^+ n ≡ x ^+ n * y ^+ n.
  Proof. elim: n => [ | n IH ]; [ simpl; sring | rewrite !exprS IH; sring ]. Qed.
  Lemma exprM x m n : x ^+ (m * n) ≡ (x ^+ m) ^+ n.
  Proof.
    elim: n => [ | n IH ]; first by rewrite muln0; reflexivity.
    by rewrite mulnS exprD IH exprS; reflexivity.
  Qed.
  Lemma expr1n n : (1 : R) ^+ n ≡ 1.
  Proof. elim: n => [ | n IH ]; [ reflexivity | rewrite exprS IH; sring ]. Qed.
  Lemma expr0n n : (0 : R) ^+ n ≡ (n == 0%N)%:R.
  Proof. case: n => [ | n ]; [ reflexivity | rewrite exprS; simpl; sring ]. Qed.
  Lemma exprN x n : (- x) ^+ n ≡ (- (1)) ^+ n * x ^+ n.
  Proof. rewrite -exprMn; apply pow_wd; [ sring | reflexivity ]. Qed.
  Lemma sqrrN x : (- x) ^+ 2 ≡ x ^+ 2. Proof. sring. Qed.
  Lemma sqrrD x y : (x + y) ^+ 2 ≡ x ^+ 2 + 2%:R * (x * y) + y ^+ 2. Proof. sring. Qed.
  Lemma sqrrB x y : (x - y) ^+ 2 ≡ x ^+ 2 - 2%:R * (x * y) + y ^+ 2. Proof. sring. Qed.

  Lemma subr_eq0 x y : x - y ≡ 0 <-> x ≡ y.
  Proof. split => H; [ transitivity (x - y + y); [ sring | rewrite H; sring ] | rewrite H; sring ]. Qed.
  Lemma addr_eq0 x y : x + y ≡ 0 <-> x ≡ - y.
  Proof. split => H; [ transitivity (x + y - y); [ sring | rewrite H; sring ] | rewrite H; sring ]. Qed.
  Lemma oppr_eq0 x : - x ≡ 0 <-> x ≡ 0.
  Proof. split => H; [ transitivity (- - x); [ sring | rewrite H; sring ] | rewrite H; sring ]. Qed.
  Lemma subr_eq x y z : x - z ≡ y <-> x ≡ y + z.
  Proof. split => H; [ rewrite -H; sring | rewrite H; sring ]. Qed.
  Lemma addIr z x y : x + z ≡ y + z -> x ≡ y.
  Proof. move=> H; transitivity (x + z - z); [ sring | rewrite H; sring ]. Qed.
  Lemma addrI z x y : z + x ≡ z + y -> x ≡ y.
  Proof. move=> H; transitivity (- z + (z + x)); [ sring | rewrite H; sring ]. Qed.
  Lemma eq_sym x y : x ≡ y <-> y ≡ x. Proof. split; intros H; symmetry; exact H. Qed.

  Lemma natr0 : (0%:R : R) ≡ 0. Proof. reflexivity. Qed.
  Lemma natr1 : (1%:R : R) ≡ 1. Proof. reflexivity. Qed.
  Lemma natrS n : (n.+1%:R : R) ≡ 1 + n%:R. Proof. exact (of_nat_S R n). Qed.
  Lemma natrD m n : ((m + n)%:R : R) ≡ m%:R + n%:R. Proof. exact (of_nat_add R m n). Qed.
  Lemma natrM m n : ((m * n)%:R : R) ≡ m%:R * n%:R. Proof. exact (of_nat_mul R m n). Qed.
  Lemma natrX n k : ((n ^ k)%:R : R) ≡ n%:R ^+ k.
  Proof. elim: k => [ | k IH ]; [ reflexivity | rewrite expnS natrM IH exprS; reflexivity ]. Qed.

  Lemma intr_nat n : ((n%:Z)%:~R : R) ≡ n%:R. Proof. reflexivity. Qed.
  Lemma intrN (k : int) : ((- k)%R%:~R : R) ≡ - k%:~R.
  Proof.
    case: k => [ [ | n ] | n ] /=.
    - simpl; sring.
    - reflexivity.
    - sring.
  Qed.

End sring.

(** * Setoid ordered fields *)

Section sof.

  Variable F : SOF.

  Add Field sth_field : (@sof_fth F) (setoid (sr_setoid F) (sr_ext F),
    morphism (of_Z_morph F), constants [sof_cst],
    power_tac (sr_pow_th F) [sof_pow_cst], completeness (sof_Z_complete F)).

  Implicit Types x y z t : F.

  (** equations *)


  Lemma sof_eq_dec x y : x ≡ y \/ x ≢ y. Proof. exact (SOF.sof_eq_dec F x y). Qed.
  Definition eqVneq := sof_eq_dec.

  Lemma oner_neq0 : (1 : F) ≢ 0. Proof. exact (@sof_neq_1_0 F). Qed.
  Lemma oner_eq0 : (1 : F) ≡ 0 <-> False. Proof. split; [ exact oner_neq0 | contradiction ]. Qed.

  Lemma mulrV x : x ≢ 0 -> x * x^-1 ≡ 1. Proof. intros H; sfield; exact H. Qed.
  Lemma mulVr x : x ≢ 0 -> x^-1 * x ≡ 1. Proof. intros H; sfield; exact H. Qed.
  Lemma divff x : x ≢ 0 -> x / x ≡ 1. Proof. intros H; sfield; exact H. Qed.
  Lemma mulfK y x : y ≢ 0 -> x * y / y ≡ x. Proof. intros H; sfield; exact H. Qed.
  Lemma mulrK y x : y ≢ 0 -> x * y / y ≡ x. Proof. exact (mulfK y x). Qed.
  Lemma divrK y x : y ≢ 0 -> x / y * y ≡ x. Proof. intros H; sfield; exact H. Qed.
  Lemma mulKf x y : x ≢ 0 -> x^-1 * (x * y) ≡ y. Proof. intros H; sfield; exact H. Qed.
  Lemma mulKr x y : x ≢ 0 -> x^-1 * (x * y) ≡ y. Proof. exact (mulKf x y). Qed.
  Lemma mulVKf x y : x ≢ 0 -> x * (x^-1 * y) ≡ y. Proof. intros H; sfield; exact H. Qed.
  Lemma invr0 : (0 : F)^-1 ≡ 0. Proof. exact (@sof_inv_0 F). Qed.
  Lemma invr1 : (1 : F)^-1 ≡ 1. Proof. sfield. Qed.

  Lemma mulf_eq0 x y : x * y ≡ 0 <-> x ≡ 0 \/ y ≡ 0.
  Proof.
    split.
    - intros H; destruct (sof_eq_dec x 0) as [ Hx | Hx ]; [ left; exact Hx | right ].
      rewrite -(mulKf x y Hx) H; sring.
    - intros [ H | H ]; rewrite H; sring.
  Qed.
  Lemma mulf_neq0 x y : x ≢ 0 -> y ≢ 0 -> x * y ≢ 0.
  Proof. intros Hx Hy H; apply mulf_eq0 in H; tauto. Qed.
  Lemma expf_neq0 x n : x ≢ 0 -> x ^+ n ≢ 0.
  Proof.
    intros Hx; elim: n => [ | n IH ]; [ exact oner_neq0 | ].
    rewrite exprS; apply mulf_neq0; assumption.
  Qed.
  Lemma expf_eq0 x n : x ^+ n ≡ 0 <-> (0 < n)%N /\ x ≡ 0.
  Proof.
    split.
    - case: n => [ | n ] H; first by exfalso; apply oner_neq0; exact H.
      split; first done.
      destruct (sof_eq_dec x 0) as [ Hx | Hx ]; [ exact Hx | exfalso; exact (expf_neq0 _ n.+1 Hx H) ].
    - case: n => [ | n ] [ Hn Hx ]; first done.
      rewrite exprS Hx; sring.
  Qed.
  Lemma sqrf_eq0 x : x ^+ 2 ≡ 0 <-> x ≡ 0.
  Proof. rewrite expf_eq0; split; [ tauto | done ]. Qed.
  Lemma invr_eq0 x : x^-1 ≡ 0 <-> x ≡ 0.
  Proof.
    split; intros H.
    - destruct (sof_eq_dec x 0) as [ Hx | Hx ]; [ exact Hx | exfalso ].
      apply oner_neq0; rewrite -(mulVr x Hx) H; sring.
    - rewrite H; exact invr0.
  Qed.
  Lemma invrK x : (x^-1)^-1 ≡ x.
  Proof.
    destruct (sof_eq_dec x 0) as [ Hx | Hx ].
    - rewrite Hx invr0 invr0; reflexivity.
    - have Hx' : x^-1 ≢ 0 by rewrite invr_eq0.
      sfield; repeat split; assumption.
  Qed.
  Lemma invfM x y : (x * y)^-1 ≡ x^-1 * y^-1.
  Proof.
    destruct (sof_eq_dec x 0) as [ Hx | Hx ]; first by rewrite Hx mul0r invr0 mul0r; reflexivity.
    destruct (sof_eq_dec y 0) as [ Hy | Hy ]; first by rewrite Hy mulr0 invr0 mulr0; reflexivity.
    sfield; repeat split; assumption.
  Qed.
  Lemma mulIf z x y : z ≢ 0 -> x * z ≡ y * z -> x ≡ y.
  Proof. intros Hz H; rewrite -(mulfK z x Hz) H; sfield; exact Hz. Qed.
  Lemma mulfI z x y : z ≢ 0 -> z * x ≡ z * y -> x ≡ y.
  Proof. intros Hz H; apply (mulIf z); [ exact Hz | rewrite (mulrC _ x) (mulrC _ y); exact H ]. Qed.

  (** case distinction on [c ≡ 0] (replaces [if c == 0 then a else b]) *)

  #[global] Instance sof_nz_wd : Proper (@eqv F ==> @eqv F) (@sof_nz F).
  Proof. intros x y H; unfold sof_nz; rewrite H; reflexivity. Qed.
  #[global] Instance sof_sel0_wd : Proper (@eqv F ==> @eqv F ==> @eqv F ==> @eqv F) (@sof_sel0 F).
  Proof. intros c c' Hc a a' Ha b b' Hb; unfold sof_sel0; rewrite Hc Ha Hb; reflexivity. Qed.

  Lemma nz_0 (c : F) : c ≡ 0 -> sof_nz c ≡ 0.
  Proof. intros H; unfold sof_nz; rewrite H; sring. Qed.
  Lemma nz_n (c : F) : c ≢ 0 -> sof_nz c ≡ 1.
  Proof. intros H; unfold sof_nz; sfield; exact H. Qed.
  Lemma nz_01 (c : F) : sof_nz c ≡ 0 \/ sof_nz c ≡ 1.
  Proof. destruct (sof_eq_dec c 0) as [ H | H ]; [ left; apply nz_0 | right; apply nz_n ]; exact H. Qed.
  Lemma sel0_0 (c a b : F) : c ≡ 0 -> sof_sel0 c a b ≡ a.
  Proof. intros H; unfold sof_sel0; rewrite (nz_0 c H); sring. Qed.
  Lemma sel0_n (c a b : F) : c ≢ 0 -> sof_sel0 c a b ≡ b.
  Proof. intros H; unfold sof_sel0; rewrite (nz_n c H); sring. Qed.

  (** numerals: characteristic zero *)

  Lemma eqr_nat m n : (m%:R : F) ≡ n%:R <-> m = n.
  Proof. split; [ exact (sof_of_nat_inj F m n) | move=> ->; reflexivity ]. Qed.
  Lemma pnatr_eq0 n : (n%:R : F) ≡ 0 <-> n = 0%N.
  Proof. exact (eqr_nat n 0). Qed.
  Lemma intr_eq0 (k : int) : (k%:~R : F) ≡ 0 <-> k = 0%R.
  Proof.
    split; last by move=> ->; reflexivity.
    case: k => n /= H; first by move: H => /pnatr_eq0 ->.
    exfalso; apply (sof_of_nat_neq0 F n); rewrite -(opprK F n.+1%:R) H; sring.
  Qed.

  (** order *)

  Lemma lexx x : x <= x. Proof. exact (sof_le_refl x). Qed.
  Lemma le_refl x : x <= x. Proof. exact (sof_le_refl x). Qed.
  Lemma ltxx x : ~ x < x. Proof. sof_lra. Qed.
  Lemma le_trans y x z : x <= y -> y <= z -> x <= z. Proof. sof_lra. Qed.
  Lemma lt_trans y x z : x < y -> y < z -> x < z. Proof. sof_lra. Qed.
  Lemma lt_le_trans y x z : x < y -> y <= z -> x < z. Proof. sof_lra. Qed.
  Lemma le_lt_trans y x z : x <= y -> y < z -> x < z. Proof. sof_lra. Qed.
  Lemma ltW x y : x < y -> x <= y. Proof. sof_lra. Qed.
  Lemma lt_neqAle x y : x < y <-> x ≢ y /\ x <= y. Proof. split; sof_lra. Qed.
  Lemma le_eqVlt x y : x <= y <-> x ≡ y \/ x < y.
  Proof.
    split; [ | sof_lra ].
    intros H; destruct (sof_eq_dec x y) as [ E | E ]; [ left; exact E | right; sof_lra ].
  Qed.
  Lemma eq_le x y : x ≡ y <-> x <= y /\ y <= x. Proof. split; sof_lra. Qed.
  Lemma le_total x y : x <= y \/ y <= x. Proof. exact (sof_le_total F x y). Qed.
  Lemma ltNge x y : x < y <-> ~ y <= x. Proof. split; sof_lra. Qed.
  Lemma leNgt x y : x <= y <-> ~ y < x. Proof. split; sof_lra. Qed.
  Lemma lerP x y : x <= y \/ y < x.
  Proof. destruct (sof_lt_trichotomy y x) as [ H | [ H | H ] ]; [ right | left | left ]; sof_lra. Qed.
  Lemma ltrP x y : x < y \/ y <= x.
  Proof. destruct (lerP y x); [ right | left ]; assumption. Qed.
  Lemma ltgtP x y : x < y \/ x ≡ y \/ y < x. Proof. exact (sof_lt_trichotomy x y). Qed.

  Lemma lerD x y z t : x <= y -> z <= t -> x + z <= y + t. Proof. sof_lra. Qed.
  Lemma ltrD x y z t : x < y -> z < t -> x + z < y + t. Proof. sof_lra. Qed.
  Lemma ler_ltD x y z t : x <= y -> z < t -> x + z < y + t. Proof. sof_lra. Qed.
  Lemma ltr_leD x y z t : x < y -> z <= t -> x + z < y + t. Proof. sof_lra. Qed.
  Lemma lerDl x y : x <= x + y <-> 0 <= y. Proof. split; sof_lra. Qed.
  Lemma lerDr x y : x <= y + x <-> 0 <= y. Proof. split; sof_lra. Qed.
  Lemma ltrDl x y : x < x + y <-> 0 < y. Proof. split; sof_lra. Qed.
  Lemma ltrDr x y : x < y + x <-> 0 < y. Proof. split; sof_lra. Qed.
  Lemma lerD2l x y z : x + y <= x + z <-> y <= z. Proof. split; sof_lra. Qed.
  Lemma lerD2r x y z : y + x <= z + x <-> y <= z. Proof. split; sof_lra. Qed.
  Lemma ltrD2l x y z : x + y < x + z <-> y < z. Proof. split; sof_lra. Qed.
  Lemma ltrD2r x y z : y + x < z + x <-> y < z. Proof. split; sof_lra. Qed.
  Lemma lerN2 x y : - x <= - y <-> y <= x. Proof. split; sof_lra. Qed.
  Lemma ltrN2 x y : - x < - y <-> y < x. Proof. split; sof_lra. Qed.
  Lemma subr_ge0 x y : 0 <= y - x <-> x <= y. Proof. split; sof_lra. Qed.
  Lemma subr_gt0 x y : 0 < y - x <-> x < y. Proof. split; sof_lra. Qed.
  Lemma subr_le0 x y : y - x <= 0 <-> y <= x. Proof. split; sof_lra. Qed.
  Lemma subr_lt0 x y : y - x < 0 <-> y < x. Proof. split; sof_lra. Qed.
  Lemma oppr_ge0 x : 0 <= - x <-> x <= 0. Proof. split; sof_lra. Qed.
  Lemma oppr_gt0 x : 0 < - x <-> x < 0. Proof. split; sof_lra. Qed.
  Lemma oppr_le0 x : - x <= 0 <-> 0 <= x. Proof. split; sof_lra. Qed.
  Lemma oppr_lt0 x : - x < 0 <-> 0 < x. Proof. split; sof_lra. Qed.

  Lemma ler01 : (0 : F) <= 1. Proof. sof_lra. Qed.
  Lemma ltr01 : (0 : F) < 1. Proof. sof_lra. Qed.
  Lemma ler10 : ~ (1 : F) <= 0. Proof. sof_lra. Qed.
  Lemma ler0n n : (0 : F) <= n%:R. Proof. exact (sof_of_nat_ge0 F n). Qed.
  Lemma ltr0Sn n : (0 : F) < n.+1%:R. Proof. exact (sof_of_nat_pos F n). Qed.
  Lemma ltr0n n : (0 : F) < n%:R <-> (0 < n)%N.
  Proof.
    case: n => [ | n ]; split => H //.
    - exfalso; exact: (ltxx 0 H).
    - exact: ltr0Sn.
  Qed.
  Lemma ler_nat m n : (m%:R : F) <= n%:R <-> (m <= n)%N.
  Proof.
    split.
    - move=> H; rewrite leqNgt; apply/negP => /subnKC E.
      move: H; rewrite -E natrD natrS; have := ler0n (m - n.+1)%N; sof_lra.
    - move=> /subnKC <-; rewrite natrD; have := ler0n (n - m)%N; sof_lra.
  Qed.
  Lemma ltr_nat m n : (m%:R : F) < n%:R <-> (m < n)%N.
  Proof. rewrite ltNge ler_nat ltnNge; split; [ move=> H; apply/negP; exact H | move=> /negP; done ]. Qed.
  Lemma ler1n n : (1 : F) <= n%:R <-> (1 <= n)%N. Proof. exact (ler_nat 1 n). Qed.

  Lemma mulr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x * y. Proof. sof_nra. Qed.
  Lemma mulr_gt0 x y : 0 < x -> 0 < y -> 0 < x * y. Proof. sof_nra. Qed.
  Lemma sqr_ge0 x : 0 <= x * x. Proof. sof_nra. Qed.
  Lemma ler_wpM2l x y z : 0 <= x -> y <= z -> x * y <= x * z. Proof. sof_nra. Qed.
  Lemma ler_wpM2r x y z : 0 <= x -> y <= z -> y * x <= z * x. Proof. sof_nra. Qed.
  Lemma ler_pM x1 y1 x2 y2 : 0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 -> x1 * x2 <= y1 * y2.
  Proof. sof_nra. Qed.
  Lemma ltr_pM2l x y z : 0 < x -> x * y < x * z <-> y < z. Proof. intros; split; sof_nra. Qed.
  Lemma ltr_pM2r x y z : 0 < x -> y * x < z * x <-> y < z. Proof. intros; split; sof_nra. Qed.
  Lemma ler_pM2l x y z : 0 < x -> x * y <= x * z <-> y <= z. Proof. intros; split; sof_nra. Qed.
  Lemma ler_pM2r x y z : 0 < x -> y * x <= z * x <-> y <= z. Proof. intros; split; sof_nra. Qed.
  Lemma ler_peMr x y : 0 <= x -> 1 <= y -> x <= x * y. Proof. sof_nra. Qed.
  Lemma ler_peMl x y : 0 <= x -> 1 <= y -> x <= y * x. Proof. sof_nra. Qed.

  Lemma invr_gt0 x : 0 < x^-1 <-> 0 < x.
  Proof.
    split; [ | exact (sof_inv_pos F x) ].
    intros H; rewrite -(invrK x); exact (sof_inv_pos F _ H).
  Qed.
  Lemma invr_ge0 x : 0 <= x^-1 <-> 0 <= x.
  Proof.
    rewrite !le_eqVlt invr_gt0; split; (intros [ H | H ]; [ left | right; exact H ]).
    - rewrite -(invrK x) -H invr0; reflexivity.
    - rewrite -H invr0; reflexivity.
  Qed.
  Lemma divr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x / y.
  Proof. intros Hx Hy; apply mulr_ge0; [ exact Hx | apply invr_ge0; exact Hy ]. Qed.
  Lemma divr_gt0 x y : 0 < x -> 0 < y -> 0 < x / y.
  Proof. intros Hx Hy; apply mulr_gt0; [ exact Hx | apply invr_gt0; exact Hy ]. Qed.

  Lemma exprn_ge0 x n : 0 <= x -> 0 <= x ^+ n.
  Proof. intros Hx; elim: n => [ | n IH ]; [ exact ler01 | rewrite exprS; apply mulr_ge0; assumption ]. Qed.
  Lemma exprn_gt0 x n : 0 < x -> 0 < x ^+ n.
  Proof. intros Hx; elim: n => [ | n IH ]; [ exact ltr01 | rewrite exprS; apply mulr_gt0; assumption ]. Qed.
  Lemma exprn_ege1 x n : 1 <= x -> 1 <= x ^+ n.
  Proof.
    intros Hx; elim: n => [ | n IH ]; [ exact (lexx 1) | rewrite exprS ].
    apply (le_trans (1 * 1)); [ sof_lra | apply ler_pM; sof_lra ].
  Qed.
  Lemma ler_weXn2l x m n : 1 <= x -> (m <= n)%N -> x ^+ m <= x ^+ n.
  Proof.
    move=> Hx /subnKC <-; rewrite exprD.
    have H0 : 0 <= x ^+ m by apply exprn_ge0; sof_lra.
    have H1 := exprn_ege1 x (n - m) Hx.
    apply ler_peMr; assumption.
  Qed.
  Lemma ler_pXn2r n x y : 0 <= x -> x <= y -> x ^+ n <= y ^+ n.
  Proof.
    intros Hx Hy; elim: n => [ | n IH ]; [ exact (lexx 1) | rewrite !exprS ].
    apply ler_pM; [ exact Hx | apply exprn_ge0; exact Hx | exact Hy | exact IH ].
  Qed.
  Lemma ltr_pXn2r n x y : (0 < n)%N -> 0 <= x -> x < y -> x ^+ n < y ^+ n.
  Proof.
    case: n => [ | n ] // _ Hx Hy; elim: n => [ | n IH ]; first by rewrite !expr1.
    rewrite (exprS _ x) (exprS _ y).
    have := exprn_ge0 x n.+1 Hx; sof_nra.
  Qed.
  Lemma ltrXn2r n x y : (0 < n)%N -> 0 <= x -> 0 <= y -> x ^+ n < y ^+ n <-> x < y.
  Proof.
    intros Hn Hx Hy; split; [ | exact (ltr_pXn2r n x y Hn Hx) ].
    intros H; destruct (lerP y x) as [ L | L ]; [ exfalso | exact L ].
    have := ler_pXn2r n y x Hy L; sof_lra.
  Qed.

  (** absolute value *)

  Lemma ger0_norm x : 0 <= x -> `|x| ≡ x. Proof. exact (sof_abs_pos x). Qed.
  Lemma ler0_norm x : x <= 0 -> `|x| ≡ - x. Proof. exact (sof_abs_neg x). Qed.
  Lemma gtr0_norm x : 0 < x -> `|x| ≡ x. Proof. intros H; apply ger0_norm; sof_lra. Qed.
  Lemma ltr0_norm x : x < 0 -> `|x| ≡ - x. Proof. intros H; apply ler0_norm; sof_lra. Qed.

  Lemma sof_abs_cases x : (0 <= x /\ `|x| ≡ x) \/ (x < 0 /\ `|x| ≡ - x).
  Proof.
    destruct (lerP 0 x) as [ H | H ]; [ left | right ]; split; try assumption.
    - exact (ger0_norm x H).
    - exact (ltr0_norm x H).
  Qed.

  Local Ltac abs_cases :=
    repeat match goal with
    | |- context [ sof_abs ?x ] =>
        let H := fresh in
        destruct (sof_abs_cases x) as [ [ ? H ] | [ ? H ] ]; rewrite H; clear H
    end.

  Lemma normr0 : `|0 : F| ≡ 0. Proof. apply ger0_norm, lexx. Qed.
  Lemma normr_ge0 x : 0 <= `|x|. Proof. abs_cases; sof_lra. Qed.
  Lemma normrN x : `|- x| ≡ `|x|. Proof. abs_cases; sof_lra. Qed.
  Lemma normr_id x : `| `|x| | ≡ `|x|. Proof. apply ger0_norm, normr_ge0. Qed.
  Lemma normr_nat n : `|(n%:R : F)| ≡ n%:R. Proof. apply ger0_norm, ler0n. Qed.
  Lemma normr_eq0 x : `|x| ≡ 0 <-> x ≡ 0. Proof. abs_cases; split; sof_lra. Qed.
  Lemma normr_gt0 x : 0 < `|x| <-> x ≢ 0. Proof. abs_cases; split; sof_lra. Qed.
  Lemma ler_norm x : x <= `|x|. Proof. abs_cases; sof_lra. Qed.
  Lemma ler_normD x y : `|x + y| <= `|x| + `|y|. Proof. abs_cases; sof_lra. Qed.
  Lemma ler_normB x y : `|x - y| <= `|x| + `|y|. Proof. abs_cases; sof_lra. Qed.
  Lemma ler_norml x y : `|x| <= y <-> - y <= x /\ x <= y. Proof. abs_cases; split; sof_lra. Qed.
  Lemma ltr_norml x y : `|x| < y <-> - y < x /\ x < y. Proof. abs_cases; split; sof_lra. Qed.
  Lemma normrM x y : `|x * y| ≡ `|x| * `|y|.
  Proof.
    destruct (sof_abs_cases x) as [ [ Hx Ex ] | [ Hx Ex ] ]; rewrite Ex;
    destruct (sof_abs_cases y) as [ [ Hy Ey ] | [ Hy Ey ] ]; rewrite Ey.
    - apply ger0_norm, mulr_ge0; assumption.
    - rewrite ler0_norm; [ sof_nra | sring ].
    - rewrite ler0_norm; [ sof_nra | sring ].
    - rewrite ger0_norm; [ sof_nra | sring ].
  Qed.
  Lemma real_normK x : `|x| ^+ 2 ≡ x ^+ 2. Proof. abs_cases; sring. Qed.
  Lemma normrX x n : `|x ^+ n| ≡ `|x| ^+ n.
  Proof. elim: n => [ | n IH ]; [ apply ger0_norm, ler01 | rewrite !exprS normrM IH; reflexivity ]. Qed.

  (** min and max *)

  Lemma min_l x y : x <= y -> sof_min x y ≡ x.
  Proof. intros H; unfold sof_min; rewrite (ler0_norm (x - y)); [ sof_lra | sfield ]. Qed.
  Lemma min_r x y : y <= x -> sof_min x y ≡ y.
  Proof. intros H; unfold sof_min; rewrite (ger0_norm (x - y)); [ sof_lra | sfield ]. Qed.
  Lemma max_l x y : y <= x -> sof_max x y ≡ x.
  Proof. intros H; unfold sof_max; rewrite (ger0_norm (x - y)); [ sof_lra | sfield ]. Qed.
  Lemma max_r x y : x <= y -> sof_max x y ≡ y.
  Proof. intros H; unfold sof_max; rewrite (ler0_norm (x - y)); [ sof_lra | sfield ]. Qed.

  Lemma sof_min_cases x y : (x <= y /\ sof_min x y ≡ x) \/ (y < x /\ sof_min x y ≡ y).
  Proof.
    destruct (lerP x y) as [ H | H ]; [ left | right ]; split; try assumption.
    - exact (min_l x y H).
    - apply min_r; sof_lra.
  Qed.
  Lemma sof_max_cases x y : (y <= x /\ sof_max x y ≡ x) \/ (x < y /\ sof_max x y ≡ y).
  Proof.
    destruct (lerP y x) as [ H | H ]; [ left | right ]; split; try assumption.
    - exact (max_l x y H).
    - apply max_r; sof_lra.
  Qed.

  #[global] Instance sof_min_wd : Proper (eqv ==> eqv ==> eqv) (@sof_min F).
  Proof. intros x x' Hx y y' Hy; unfold sof_min; rewrite Hx Hy; reflexivity. Qed.
  #[global] Instance sof_max_wd : Proper (eqv ==> eqv ==> eqv) (@sof_max F).
  Proof. intros x x' Hx y y' Hy; unfold sof_max; rewrite Hx Hy; reflexivity. Qed.

  Local Ltac min_cases :=
    repeat match goal with
    | |- context [ sof_min ?x ?y ] =>
        let H := fresh in
        destruct (sof_min_cases x y) as [ [ ? H ] | [ ? H ] ]; rewrite H; clear H
    | |- context [ sof_max ?x ?y ] =>
        let H := fresh in
        destruct (sof_max_cases x y) as [ [ ? H ] | [ ? H ] ]; rewrite H; clear H
    end.

  Lemma le_min z x y : z <= sof_min x y <-> z <= x /\ z <= y. Proof. min_cases; split; sof_lra. Qed.
  Lemma lt_min z x y : z < sof_min x y <-> z < x /\ z < y. Proof. min_cases; split; sof_lra. Qed.
  Lemma ge_min z x y : sof_min x y <= z <-> x <= z \/ y <= z.
  Proof. min_cases; split; sof_lra. Qed.
  Lemma le_max z x y : z <= sof_max x y <-> z <= x \/ z <= y.
  Proof. min_cases; split; sof_lra. Qed.
  Lemma ge_max z x y : sof_max x y <= z <-> x <= z /\ y <= z. Proof. min_cases; split; sof_lra. Qed.
  Lemma minC x y : sof_min x y ≡ sof_min y x. Proof. min_cases; sof_lra. Qed.
  Lemma maxC x y : sof_max x y ≡ sof_max y x. Proof. min_cases; sof_lra. Qed.
  Lemma le_min_l x y : sof_min x y <= x. Proof. min_cases; sof_lra. Qed.
  Lemma le_min_r x y : sof_min x y <= y. Proof. min_cases; sof_lra. Qed.

  (** the embedding of the rationals *)

  Lemma ratr_nat n : (of_rat n%:R%R : F) ≡ n%:R. Proof. exact (of_rat_nat F n). Qed.
  Lemma ratr_int (k : int) : (of_rat k%:~R%R : F) ≡ k%:~R. Proof. exact (of_rat_int F k). Qed.
  Lemma ratr0 : (of_rat 0%R : F) ≡ 0. Proof. exact (of_rat_0 F). Qed.
  Lemma ratr1 : (of_rat 1%R : F) ≡ 1. Proof. exact (@sof_of_rat_1 F). Qed.
  Lemma ratrD a b : (of_rat (a + b)%R : F) ≡ of_rat a + of_rat b. Proof. exact (@sof_of_rat_add F a b). Qed.
  Lemma ratrM a b : (of_rat (a * b)%R : F) ≡ of_rat a * of_rat b. Proof. exact (@sof_of_rat_mul F a b). Qed.
  Lemma ratrN a : (of_rat (- a)%R : F) ≡ - of_rat a. Proof. exact (of_rat_opp F a). Qed.
  Lemma ratrB a b : (of_rat (a - b)%R : F) ≡ of_rat a - of_rat b. Proof. exact (of_rat_sub F a b). Qed.
  Lemma ratrV a : (of_rat (a^-1)%R : F) ≡ (of_rat a)^-1. Proof. exact (of_rat_inv F a). Qed.
  Lemma ratr_le a b : (of_rat a : F) <= of_rat b <-> (a <= b)%R. Proof. exact (of_rat_le_iff F a b). Qed.
  Lemma ratr_lt a b : (of_rat a : F) < of_rat b <-> (a < b)%R. Proof. exact (of_rat_lt_iff F a b). Qed.
  Lemma ratr_eq a b : (of_rat a : F) ≡ of_rat b <-> a = b. Proof. exact (of_rat_eq_iff F a b). Qed.

End sof.

End SOFTheory.
