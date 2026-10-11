(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A: the quadratic extension  R(sqrt2)  over a setoid ring R, as
   pairs (see SETOID.md). It mirrors the [qe] API of FixedData.v, with
   the same names, so that ports are name-compatible:
   - the record is FixedData's [qe] itself ([QE a b] = a + b sqrt2), so
     the fixed data ([aE], [ct], [dF] : qe rat) map into it by [qe_rat];
   - [qe_SRing R] is the canonical setoid ring on [qe R] for any setoid
     ring R (componentwise equivalence, inverse x / (a^2 - 2 b^2));
   - over a setoid ordered field F with Z0 (no square root of 2 in F),
     [qe F] is a field: [qe_fth] (for [Add Field]), [qe_inv_l],
     [qe_norm_eq0]; without Z0, [qe_unit] (inverse of elements of
     nonzero norm).

   Import this file AFTER FixedData.v when both are imported: the names
   [qe_add], [qe_mul], [qe_of], [qe_conj], [qe_norm], [qe_e], [qe_rat],
   ... then refer to the setoid versions. *)

From Stdlib Require Import Setoid Morphisms RelationClasses ZArith.
From Stdlib Require Import Ring Field Ring_theory Field_theory.

From Undecidability.H10.Rational Require FixedData.
From Undecidability.H10.Rational Require Import SOF SOFTactics.

From mathcomp Require Import boot order algebra.
Import GRing.Theory Num.Theory.

Local Open Scope sof_scope.

Abbreviation qe := FixedData.qe.
Abbreviation QE := FixedData.QE.
Abbreviation qre := FixedData.qre.
Abbreviation qim := FixedData.qim.

(** * The setoid ring  qe R *)

Section qe_ring.

  Variable R : SRing.

  Add Ring qe_base_ring : (sr_rth R) (setoid (sr_setoid R) (sr_ext R),
    morphism (of_Z_morph R), constants [sof_cst], power_tac (sr_pow_th R) [sof_pow_cst]).

  Implicit Types x y z : qe R.

  Definition qe_eqv x y : Prop := qre x ≡ qre y /\ qim x ≡ qim y.
  Definition qe0 : qe R := QE 0 0.
  Definition qe1 : qe R := QE 1 0.
  Definition qe_opp x : qe R := QE (- qre x) (- qim x).
  Definition qe_add x y : qe R := QE (qre x + qre y) (qim x + qim y).
  Definition qe_mul x y : qe R :=
    QE (qre x * qre y + 2%:R * (qim x * qim y)) (qre x * qim y + qim x * qre y).
  Definition qe_norm x : R := qre x ^+ 2 - 2%:R * qim x ^+ 2.
  Definition qe_inv x : qe R := QE (qre x / qe_norm x) (- qim x / qe_norm x).

  Lemma qe_eqv_equiv : Equivalence qe_eqv.
  Proof.
    split.
    - intros [ a b ]; split; reflexivity.
    - intros [ a b ] [ c d ] [ H1 H2 ]; split; symmetry; assumption.
    - intros [ a b ] [ c d ] [ e f ] [ H1 H2 ] [ H3 H4 ]; split; etransitivity; eassumption.
  Qed.

  Local Ltac qe_wd :=
    repeat intros [ ? ? ]; repeat match goal with H : qe_eqv _ _ |- _ => destruct H end;
    unfold qe_eqv; simpl in *;
    repeat match goal with H : _ ≡ _ |- _ => rewrite H; clear H end; split; reflexivity.

  Lemma qe_add_wd : Proper (qe_eqv ==> qe_eqv ==> qe_eqv) qe_add.
  Proof.
    intros [ a b ] [ a' b' ] [ H1 H2 ] [ c d ] [ c' d' ] [ H3 H4 ]; unfold qe_eqv, qe_add; simpl in *.
    rewrite H1 H2 H3 H4; split; reflexivity.
  Qed.
  Lemma qe_mul_wd : Proper (qe_eqv ==> qe_eqv ==> qe_eqv) qe_mul.
  Proof.
    intros [ a b ] [ a' b' ] [ H1 H2 ] [ c d ] [ c' d' ] [ H3 H4 ]; unfold qe_eqv, qe_mul; simpl in *.
    rewrite H1 H2 H3 H4; split; reflexivity.
  Qed.
  Lemma qe_opp_wd : Proper (qe_eqv ==> qe_eqv) qe_opp.
  Proof.
    intros [ a b ] [ a' b' ] [ H1 H2 ]; unfold qe_eqv, qe_opp; simpl in *.
    rewrite H1 H2; split; reflexivity.
  Qed.
  Lemma qe_inv_wd : Proper (qe_eqv ==> qe_eqv) qe_inv.
  Proof.
    intros [ a b ] [ a' b' ] [ H1 H2 ]; unfold qe_eqv, qe_inv, qe_norm; simpl in *.
    rewrite H1 H2; split; reflexivity.
  Qed.

  Local Ltac qe_ring_tac :=
    repeat intros [ ? ? ]; unfold qe_eqv, qe_add, qe_mul, qe_opp, qe0, qe1; simpl; split; sring.

  Lemma qe_add_0_l : forall x, qe_eqv (qe_add qe0 x) x.
  Proof. qe_ring_tac. Qed.
  Lemma qe_add_comm : forall x y, qe_eqv (qe_add x y) (qe_add y x).
  Proof. qe_ring_tac. Qed.
  Lemma qe_add_assoc : forall x y z, qe_eqv (qe_add x (qe_add y z)) (qe_add (qe_add x y) z).
  Proof. qe_ring_tac. Qed.
  Lemma qe_mul_1_l : forall x, qe_eqv (qe_mul qe1 x) x.
  Proof. qe_ring_tac. Qed.
  Lemma qe_mul_comm : forall x y, qe_eqv (qe_mul x y) (qe_mul y x).
  Proof. qe_ring_tac. Qed.
  Lemma qe_mul_assoc : forall x y z, qe_eqv (qe_mul x (qe_mul y z)) (qe_mul (qe_mul x y) z).
  Proof. qe_ring_tac. Qed.
  Lemma qe_distr_l : forall x y z, qe_eqv (qe_mul (qe_add x y) z) (qe_add (qe_mul x z) (qe_mul y z)).
  Proof. qe_ring_tac. Qed.
  Lemma qe_opp_def : forall x, qe_eqv (qe_add x (qe_opp x)) qe0.
  Proof. qe_ring_tac. Qed.

  Definition qe_SRing : SRing := {|
    car := qe R;
    eqv := qe_eqv;
    sr_zero := qe0;
    sr_one := qe1;
    sr_add := qe_add;
    sr_mul := qe_mul;
    sr_opp := qe_opp;
    sr_inv := qe_inv;
    sr_equiv := qe_eqv_equiv;
    sr_add_wd := qe_add_wd;
    sr_mul_wd := qe_mul_wd;
    sr_opp_wd := qe_opp_wd;
    sr_inv_wd := qe_inv_wd;
    sr_add_0_l := qe_add_0_l;
    sr_add_comm := qe_add_comm;
    sr_add_assoc := qe_add_assoc;
    sr_mul_1_l := qe_mul_1_l;
    sr_mul_comm := qe_mul_comm;
    sr_mul_assoc := qe_mul_assoc;
    sr_distr_l := qe_distr_l;
    sr_opp_def := qe_opp_def
  |}.

End qe_ring.

Arguments qe_eqv {R} x y.
Arguments qe0 {R}.
Arguments qe1 {R}.
Arguments qe_opp {R} x.
Arguments qe_add {R} x y.
Arguments qe_mul {R} x y.
Arguments qe_norm {R} x.
Arguments qe_inv {R} x.

Canonical qe_SRing.

(** * The qe API (names as in FixedData.v) *)

Section qe_api.

  Variable R : SRing.

  Add Ring qe_api_base_ring : (sr_rth R) (setoid (sr_setoid R) (sr_ext R),
    morphism (of_Z_morph R), constants [sof_cst], power_tac (sr_pow_th R) [sof_pow_cst]).
  Add Ring qe_api_ring : (sr_rth (qe_SRing R)) (setoid (sr_setoid (qe_SRing R)) (sr_ext (qe_SRing R)),
    morphism (of_Z_morph (qe_SRing R)), constants [sof_cst],
    power_tac (sr_pow_th (qe_SRing R)) [sof_pow_cst]).

  Implicit Types (a b c d : R) (x y z : qe R).

  Lemma qe_eqvE x y : x ≡ y <-> qre x ≡ qre y /\ qim x ≡ qim y.
  Proof. reflexivity. Qed.

  #[global] Instance QE_wd : Proper (eqv ==> eqv ==> eqv) (@QE (car R)).
  Proof. intros a a' Ha b b' Hb; split; assumption. Qed.
  #[global] Instance qre_wd : Proper (eqv ==> eqv) (@qre (car R)).
  Proof. intros x y [ H _ ]; exact H. Qed.
  #[global] Instance qim_wd : Proper (eqv ==> eqv) (@qim (car R)).
  Proof. intros x y [ _ H ]; exact H. Qed.

  Lemma qeE x : x = QE (qre x) (qim x).
  Proof. destruct x; reflexivity. Qed.

  Lemma QE_inj a b c d : QE a b ≡ QE c d -> a ≡ c /\ b ≡ d.
  Proof. intros H; exact H. Qed.

  Lemma qe0E : (0 : qe R) ≡ QE 0 0. Proof. reflexivity. Qed.
  Lemma qe1E : (1 : qe R) ≡ QE 1 0. Proof. reflexivity. Qed.
  Lemma qe_addE a b c d : QE a b + QE c d ≡ QE (a + c) (b + d).
  Proof. reflexivity. Qed.
  Lemma qe_oppE a b : - QE a b ≡ QE (- a) (- b).
  Proof. reflexivity. Qed.
  Lemma qe_subE a b c d : QE a b - QE c d ≡ QE (a - c) (b - d).
  Proof. reflexivity. Qed.
  Lemma qe_mulE a b c d : QE a b * QE c d ≡ QE (a * c + 2%:R * (b * d)) (a * d + b * c).
  Proof. reflexivity. Qed.

  Lemma qe_natE n : (n%:R : qe R) ≡ QE n%:R 0.
  Proof.
    induction n as [ | n IH ]; [ reflexivity | ].
    rewrite !of_nat_S IH; split; simpl; sring.
  Qed.

  Lemma qe_ZE (k : Z) : (of_Z k : qe R) ≡ QE (of_Z k) 0.
  Proof.
    destruct k as [ | p | p ]; simpl; [ reflexivity | apply qe_natE | ].
    unfold of_pos; rewrite qe_natE; split; simpl; sring.
  Qed.

  Lemma qe_intE (k : int) : (k%:~R : qe R) ≡ QE k%:~R 0.
  Proof.
    destruct k as [ n | n ]; [ apply qe_natE | ].
    unfold of_int; rewrite qe_natE; split; simpl; sring.
  Qed.

  Lemma qe_powE x n : x ^+ n.+1 ≡ x * x ^+ n.
  Proof. reflexivity. Qed.

  (** the embedding of the base *)

  Definition qe_of (a : R) : qe R := QE a 0.

  #[global] Instance qe_of_wd : Proper (eqv ==> eqv) qe_of.
  Proof. intros a b H; split; [ exact H | reflexivity ]. Qed.

  Lemma qe_of_add a b : qe_of (a + b) ≡ qe_of a + qe_of b.
  Proof. split; simpl; sring. Qed.
  Lemma qe_of_mul a b : qe_of (a * b) ≡ qe_of a * qe_of b.
  Proof. split; simpl; sring. Qed.
  Lemma qe_of_opp a : qe_of (- a) ≡ - qe_of a.
  Proof. split; simpl; sring. Qed.
  Lemma qe_of_sub a b : qe_of (a - b) ≡ qe_of a - qe_of b.
  Proof. split; simpl; sring. Qed.
  Lemma qe_of0 : qe_of 0 ≡ 0. Proof. reflexivity. Qed.
  Lemma qe_of1 : qe_of 1 ≡ 1. Proof. reflexivity. Qed.
  Lemma qe_of_nat n : qe_of n%:R ≡ n%:R.
  Proof. symmetry; apply qe_natE. Qed.
  Lemma qe_of_int (k : int) : qe_of k%:~R ≡ k%:~R.
  Proof. symmetry; apply qe_intE. Qed.
  Lemma qe_of_pow a n : qe_of (a ^+ n) ≡ qe_of a ^+ n.
  Proof.
    induction n as [ | n IH ]; [ reflexivity | ].
    simpl; rewrite qe_of_mul IH; reflexivity.
  Qed.
  Lemma qe_of_eqv a b : qe_of a ≡ qe_of b <-> a ≡ b.
  Proof. split; [ intros [ H _ ]; exact H | apply qe_of_wd ]. Qed.

  Definition qe_sqrt2 : qe R := QE 0 1.

  Lemma qe_sqrt2_sqr : qe_sqrt2 * qe_sqrt2 ≡ 2%:R.
  Proof. rewrite qe_natE; split; simpl; sring. Qed.

  (** conjugation and norm *)

  Definition qe_conj x : qe R := QE (qre x) (- qim x).

  #[global] Instance qe_conj_wd : Proper (eqv ==> eqv) qe_conj.
  Proof. intros x y [ H1 H2 ]; split; simpl; [ exact H1 | rewrite H2; reflexivity ]. Qed.
  #[global] Instance qe_norm_wd : Proper (eqv ==> eqv) (@qe_norm R).
  Proof. intros x y [ H1 H2 ]; unfold qe_norm; rewrite H1 H2; reflexivity. Qed.

  Lemma qe_conj_add x y : qe_conj (x + y) ≡ qe_conj x + qe_conj y.
  Proof. destruct x, y; split; simpl; sring. Qed.
  Lemma qe_conj_mul x y : qe_conj (x * y) ≡ qe_conj x * qe_conj y.
  Proof. destruct x, y; split; simpl; sring. Qed.
  Lemma qe_conj_opp x : qe_conj (- x) ≡ - qe_conj x.
  Proof. destruct x; split; simpl; sring. Qed.
  Lemma qe_conj1 : qe_conj 1 ≡ 1.
  Proof. split; simpl; sring. Qed.
  Lemma qe_conjK x : qe_conj (qe_conj x) ≡ x.
  Proof. destruct x; split; simpl; sring. Qed.
  Lemma qe_conj_of a : qe_conj (qe_of a) ≡ qe_of a.
  Proof. split; simpl; sring. Qed.
  Lemma qe_mul_conj x : x * qe_conj x ≡ qe_of (qe_norm x).
  Proof. destruct x; unfold qe_norm; split; simpl; sring. Qed.
  Lemma qe_norm_mul x y : qe_norm (x * y) ≡ qe_norm x * qe_norm y.
  Proof. destruct x, y; unfold qe_norm; simpl; sring. Qed.
  Lemma qe_norm1 : qe_norm (1 : qe R) ≡ 1.
  Proof. unfold qe_norm; simpl; sring. Qed.
  Lemma qe_norm_of a : qe_norm (qe_of a) ≡ a ^+ 2.
  Proof. unfold qe_norm; simpl; sring. Qed.
  Lemma qe_norm_conj x : qe_norm (qe_conj x) ≡ qe_norm x.
  Proof. destruct x; unfold qe_norm; simpl; sring. Qed.

  (* conjugation selected by a boolean: false = identity (curve E),
     true = sigma (curve E^sigma) *)
  Definition qe_e (sg : bool) x : qe R := if sg then qe_conj x else x.

  #[global] Instance qe_e_wd sg : Proper (eqv ==> eqv) (qe_e sg).
  Proof. destruct sg; simpl; [ apply qe_conj_wd | intros x y H; exact H ]. Qed.

  Lemma qe_e_add sg x y : qe_e sg (x + y) ≡ qe_e sg x + qe_e sg y.
  Proof. destruct sg; simpl; [ apply qe_conj_add | reflexivity ]. Qed.
  Lemma qe_e_mul sg x y : qe_e sg (x * y) ≡ qe_e sg x * qe_e sg y.
  Proof. destruct sg; simpl; [ apply qe_conj_mul | reflexivity ]. Qed.
  Lemma qe_e_opp sg x : qe_e sg (- x) ≡ - qe_e sg x.
  Proof. destruct sg; simpl; [ apply qe_conj_opp | reflexivity ]. Qed.
  Lemma qe_e_of sg a : qe_e sg (qe_of a) ≡ qe_of a.
  Proof. destruct sg; simpl; [ apply qe_conj_of | reflexivity ]. Qed.
  Lemma qe_e_nat sg n : qe_e sg (n%:R) ≡ n%:R.
  Proof. rewrite -!qe_of_nat; apply qe_e_of. Qed.

  Lemma qe_e_pow sg x n : qe_e sg (x ^+ n) ≡ qe_e sg x ^+ n.
  Proof.
    induction n as [ | n IH ]; simpl; [ destruct sg; [ apply qe_conj1 | reflexivity ] | ].
    rewrite qe_e_mul IH; reflexivity.
  Qed.

End qe_api.

Arguments qe_sqrt2 {R}.
Arguments qe_of {R} a.
Arguments qe_conj {R} x.
Arguments qe_e {R} sg x.

(** * Over a setoid ordered field *)

Section qe_field.

  Variable F : SOF.

  Add Field qe_base_field : (@sof_fth F) (setoid (sr_setoid F) (sr_ext F),
    morphism (of_Z_morph F), constants [sof_cst],
    power_tac (sr_pow_th F) [sof_pow_cst], completeness (sof_Z_complete F)).
  Add Ring qe_field_ring : (sr_rth (qe_SRing F)) (setoid (sr_setoid (qe_SRing F)) (sr_ext (qe_SRing F)),
    morphism (of_Z_morph (qe_SRing F)), constants [sof_cst],
    power_tac (sr_pow_th (qe_SRing F)) [sof_pow_cst]).

  Implicit Types (a b : F) (x y : qe F).

  Lemma qe_eq_dec x y : x ≡ y \/ x ≢ y.
  Proof.
    destruct (sof_eq_dec F (qre x) (qre y)) as [ H1 | H1 ];
      [ destruct (sof_eq_dec F (qim x) (qim y)) as [ H2 | H2 ] | ].
    - left; split; assumption.
    - right; intros [ _ H ]; exact (H2 H).
    - right; intros [ H _ ]; exact (H1 H).
  Qed.

  (* the inverse of an element of nonzero norm (no hypothesis on F) *)
  Lemma qe_unit x : qe_norm x ≢ 0 -> x^-1 * x ≡ 1.
  Proof.
    destruct x as [ a b ]; intros H; unfold qe_norm in H; simpl in H.
    split; simpl; unfold qe_norm; simpl; sfield; intros N; apply H; rewrite -N; sring.
  Qed.

  Lemma qe_mulV x : qe_norm x ≢ 0 -> x * x^-1 ≡ 1.
  Proof. intros H; rewrite sr_mul_comm; apply qe_unit; exact H. Qed.

  Lemma qe_inv0 : (0 : qe F)^-1 ≡ 0.
  Proof.
    split; simpl; unfold sr_div, qe_norm; simpl.
    - transitivity ((0 : F) * (0 ^+ 2 - 2%:R * 0 ^+ 2)^-1); [ reflexivity | sring ].
    - transitivity (- (0 : F) * (0 ^+ 2 - 2%:R * 0 ^+ 2)^-1); [ reflexivity | sring ].
  Qed.

  Lemma qe_of_inv a : qe_of (a^-1) ≡ (qe_of a)^-1.
  Proof.
    destruct (sof_eq_dec F a 0) as [ H | H ].
    - rewrite H; rewrite (@sof_inv_0 F) qe_inv0; reflexivity.
    - split; simpl; unfold sr_div, qe_norm; simpl; sfield; try exact H;
        intros N; apply H; rewrite -N; sring.
  Qed.

  Lemma qe_of_div a b : qe_of (a / b) ≡ qe_of a / qe_of b.
  Proof. unfold sr_div; rewrite qe_of_mul qe_of_inv; reflexivity. Qed.

  (** the field property under Z0 (sqrt2 not in F) *)

  Hypothesis Z0 : forall a : F, a * a ≢ 2%:R.

  Lemma qe_norm_eq0 x : qe_norm x ≡ 0 <-> x ≡ 0.
  Proof using Z0.
    destruct x as [ a b ]; unfold qe_norm; simpl; split.
    - intros H.
      destruct (sof_eq_dec F b 0) as [ Hb | Hb ].
      + rewrite Hb in H; split; simpl; [ | exact Hb ].
        assert (Ha : a * a ≡ 0) by (rewrite -H; sring).
        destruct (sof_eq_dec F a 0) as [ Ha' | Ha' ]; [ exact Ha' | ].
        exfalso; apply: (@sof_neq_1_0 F); rewrite -(sof_inv_l a Ha').
        transitivity (a^-1 * a^-1 * (a * a)); [ sfield; exact Ha' | rewrite Ha; sring ].
      + exfalso; apply (Z0 (a / b)).
        transitivity ((a ^+ 2 - 2%:R * b ^+ 2) / (b * b) + 2%:R); [ sfield; exact Hb | ].
        rewrite H; sfield; exact Hb.
    - intros [ H1 H2 ]; simpl in H1, H2; rewrite H1 H2; sring.
  Qed.

  Lemma qe_inv_l x : x ≢ 0 -> x^-1 * x ≡ 1.
  Proof using Z0. intros H; apply qe_unit; intros N; apply H, qe_norm_eq0, N. Qed.

  Lemma qe_neq_1_0 : (1 : qe F) ≢ 0.
  Proof. intros [ H _ ]; exact (sof_neq_1_0 H). Qed.

  Lemma qe_fth : field_theory (@sr_zero (qe_SRing F)) sr_one sr_add sr_mul sr_sub sr_opp sr_div sr_inv eqv.
  Proof using Z0.
    constructor.
    - exact (sr_rth (qe_SRing F)).
    - exact qe_neq_1_0.
    - reflexivity.
    - exact qe_inv_l.
  Qed.

  Lemma qe_mulf_eq0 x y : x * y ≡ 0 <-> x ≡ 0 \/ y ≡ 0.
  Proof using Z0.
    split.
    - intros H; destruct (qe_eq_dec x 0) as [ Hx | Hx ]; [ left; exact Hx | right ].
      rewrite -(sr_mul_1_l y) -(qe_inv_l x Hx) -sr_mul_assoc H; split; simpl; sring.
    - intros [ H | H ]; rewrite H; sring.
  Qed.

  Lemma qe_Z_complete (a b : Z) : (of_Z a : qe F) ≡ of_Z b -> Z.eqb a b = true.
  Proof. rewrite !qe_ZE; intros [ H _ ]; exact (sof_Z_complete F a b H). Qed.

End qe_field.

(* [sfield] on qe F, under Z0 *)
Section qe_field_test.

  Variable F : SOF.
  Hypothesis Z0 : forall a : F, a * a ≢ 2%:R.

  Add Field qe_test_field : (qe_fth F Z0) (setoid (sr_setoid (qe_SRing F)) (sr_ext (qe_SRing F)),
    morphism (of_Z_morph (qe_SRing F)), constants [sof_cst],
    power_tac (sr_pow_th (qe_SRing F)) [sof_pow_cst], completeness (qe_Z_complete F)).

  Lemma qe_field_test (x y : qe F) : x ≢ 0 -> (x * y + x) / x ≡ y + 1.
  Proof using Z0. intros H; sfield; exact H. Qed.

  Lemma qe_field_test2 (x : qe F) : x ≢ 0 -> 2%:R * x / x ≡ 2%:R.
  Proof using Z0. intros H; sfield; exact H. Qed.

End qe_field_test.

(** * Mapping the fixed data:  qe rat -> qe F *)

Definition qe_rat {F : SOF} (x : qe rat) : qe F := QE (of_rat (qre x)) (of_rat (qim x)).

Section qe_rat_morph.

  Variable F : SOF.

  Implicit Types x y : qe rat.

  Lemma qe_rat_QE (a b : rat) : (qe_rat (QE a b) : qe F) ≡ QE (of_rat a) (of_rat b).
  Proof. reflexivity. Qed.

  Lemma qe_rat_add x y : (qe_rat (FixedData.qe_add x y) : qe F) ≡ qe_rat x + qe_rat y.
  Proof. destruct x, y; split; simpl; apply (@sof_of_rat_add F). Qed.

  Lemma qe_rat_opp x : (qe_rat (FixedData.qe_opp x) : qe F) ≡ - qe_rat x.
  Proof. destruct x; split; simpl; apply of_rat_opp. Qed.

  Lemma qe_rat_mul x y : (qe_rat (FixedData.qe_mul x y) : qe F) ≡ qe_rat x * qe_rat y.
  Proof.
    destruct x as [ a b ], y as [ c d ]; split; simpl;
      rewrite !sof_of_rat_add !sof_of_rat_mul ?of_rat_nat; reflexivity.
  Qed.

  Lemma qe_rat1 : (qe_rat (@FixedData.qe1 _) : qe F) ≡ 1.
  Proof. split; simpl; [ apply (@sof_of_rat_1 F) | apply of_rat_0 ]. Qed.

  Lemma qe_rat0 : (qe_rat (@FixedData.qe0 _) : qe F) ≡ 0.
  Proof. split; simpl; apply of_rat_0. Qed.

  Lemma qe_rat_conj x : (qe_rat (FixedData.qe_conj x) : qe F) ≡ qe_conj (qe_rat x).
  Proof. destruct x; split; simpl; [ reflexivity | apply of_rat_opp ]. Qed.

  Lemma qe_rat_e sg x : (qe_rat (FixedData.qe_e sg x) : qe F) ≡ qe_e sg (qe_rat x).
  Proof. destruct sg; simpl; [ apply qe_rat_conj | reflexivity ]. Qed.

  Lemma qe_rat_of (a : rat) : (qe_rat (FixedData.qe_of a) : qe F) ≡ qe_of (of_rat a).
  Proof. split; simpl; [ reflexivity | apply of_rat_0 ]. Qed.

End qe_rat_morph.
