(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A: setoid rings and setoid ordered fields (see SETOID.md).

   An ultrapower  (nat -> rat) / U  has only a Prop-valued equality, so it
   cannot be a MathComp [realFieldType]. This file provides the interface
   that replaces [sQ : realFieldType] in the ambient structure:

   - [SRing]: a commutative ring with a total [inv] operation, over a
     carrier with an equivalence [eqv] that all operations respect. No
     field law. [qe R] (pairs, R(sqrt2)) is a canonical [SRing] over any
     [SRing] R, see SOFqe.v.
   - [SOF]: a setoid ordered field: an [SRing] with the field law, a
     Prop-valued total order compatible with the operations, an absolute
     value, and the embedding [of_rat : rat -> F] of MathComp rationals
     as a field of the structure (a monotone ring morphism).

   Derived operations: [sub], [div], [pow] (nat exponent, notation
   [x ^+ n]), [of_nat] ([n%:R]), [of_int] ([z%:~R]), [of_Z], [min], [max].

   Notations live in [sof_scope] (key [%sof]); they reuse the MathComp
   spellings ([+], [*], [-], [/], [^-1], [^+], [%:R], [%:~R], [<=], [<],
   [`|x|]) so that ports are mechanical, plus [x ≡ y] for [eqv] and
   [x ≢ y] for its negation.

   Tactics: [Add Ring]/[Add Field] work for any [SOF] in a Section (see
   the one-line declarations [sof_add_ring] below and SOFTactics.v);
   since MathComp's Elpi [ring]/[field] shadow the Stdlib notations,
   the Stdlib tactics are re-exported as [sring] and [sfield]. *)

From Stdlib Require Import Setoid Morphisms RelationClasses ZArith Lia OrderedRing.
From Stdlib Require Import Ring Field Ring_theory Field_theory InitialRing.
From mathcomp Require Import boot order algebra.
Import Order.TTheory GRing.Theory Num.Theory.


(* the Stdlib setoid [ring]/[field], under names that MathComp's Elpi
   tactics do not shadow *)
Ltac sring := let G := Get_goal in ring_lookup (PackRing Ring_gen) [] G.
Ltac sfield := let G := Get_goal in field_lookup (PackField FIELD) [] G.

(** * Setoid commutative rings with a total inverse operation *)

Record SRing : Type := {
  car :> Type;
  eqv : car -> car -> Prop;
  sr_zero : car;
  sr_one : car;
  sr_add : car -> car -> car;
  sr_mul : car -> car -> car;
  sr_opp : car -> car;
  sr_inv : car -> car;
  sr_equiv : Equivalence eqv;
  sr_add_wd : Proper (eqv ==> eqv ==> eqv) sr_add;
  sr_mul_wd : Proper (eqv ==> eqv ==> eqv) sr_mul;
  sr_opp_wd : Proper (eqv ==> eqv) sr_opp;
  sr_inv_wd : Proper (eqv ==> eqv) sr_inv;
  sr_add_0_l : forall x, eqv (sr_add sr_zero x) x;
  sr_add_comm : forall x y, eqv (sr_add x y) (sr_add y x);
  sr_add_assoc : forall x y z, eqv (sr_add x (sr_add y z)) (sr_add (sr_add x y) z);
  sr_mul_1_l : forall x, eqv (sr_mul sr_one x) x;
  sr_mul_comm : forall x y, eqv (sr_mul x y) (sr_mul y x);
  sr_mul_assoc : forall x y z, eqv (sr_mul x (sr_mul y z)) (sr_mul (sr_mul x y) z);
  sr_distr_l : forall x y z, eqv (sr_mul (sr_add x y) z) (sr_add (sr_mul x z) (sr_mul y z));
  sr_opp_def : forall x, eqv (sr_add x (sr_opp x)) sr_zero
}.

Arguments eqv {s} _ _.
Arguments sr_zero {s}.
Arguments sr_one {s}.
Arguments sr_add {s} _ _.
Arguments sr_mul {s} _ _.
Arguments sr_opp {s} _.
Arguments sr_inv {s} _.
Arguments sr_add_0_l {s}.
Arguments sr_add_comm {s}.
Arguments sr_add_assoc {s}.
Arguments sr_mul_1_l {s}.
Arguments sr_mul_comm {s}.
Arguments sr_mul_assoc {s}.
Arguments sr_distr_l {s}.
Arguments sr_opp_def {s}.

#[global] Existing Instance sr_equiv.
#[global] Existing Instance sr_add_wd.
#[global] Existing Instance sr_mul_wd.
#[global] Existing Instance sr_opp_wd.
#[global] Existing Instance sr_inv_wd.

(** derived operations, generic over [SRing] *)

Definition sr_sub {R : SRing} (x y : R) : R := sr_add x (sr_opp y).
Definition sr_div {R : SRing} (x y : R) : R := sr_mul x (sr_inv y).

Fixpoint sr_pow {R : SRing} (x : R) (n : nat) : R :=
  match n with
  | O => sr_one
  | S m => sr_mul x (sr_pow x m)
  end.

(* [of_nat 0 = 0], [of_nat 1 = 1], [of_nat (S (S n)) = of_nat (S n) + 1]:
   the special case for 1 makes closed constants convertible to the
   values of the ring constant morphism [of_Z] (needed by [sring] and
   [sof_lra]) *)
Fixpoint of_nat {R : SRing} (n : nat) : R :=
  match n with
  | O => sr_zero
  | S m => match m with O => sr_one | _ => sr_add (of_nat m) sr_one end
  end.

Definition of_pos {R : SRing} (p : positive) : R := of_nat (Pos.to_nat p).

Definition of_Z {R : SRing} (z : Z) : R :=
  match z with
  | Z0 => sr_zero
  | Zpos p => of_pos p
  | Zneg p => sr_opp (of_pos p)
  end.

Arguments of_nat {R} n%_nat.
Arguments sr_pow {R} x n%_nat.
Arguments of_Z {R} z.

#[global] Instance sub_wd (R : SRing) : Proper (eqv ==> eqv ==> eqv) (@sr_sub R).
Proof. intros x x' Hx y y' Hy; unfold sr_sub; rewrite Hx Hy; reflexivity. Qed.
#[global] Instance div_wd (R : SRing) : Proper (eqv ==> eqv ==> eqv) (@sr_div R).
Proof. intros x x' Hx y y' Hy; unfold sr_div; rewrite Hx Hy; reflexivity. Qed.
#[global] Instance pow_wd (R : SRing) : Proper (eqv ==> eq ==> eqv) (@sr_pow R).
Proof.
  intros x x' Hx n n' <-; induction n as [ | n IH ]; simpl; [ reflexivity | ].
  apply sr_mul_wd; assumption.
Qed.

(** * Ring theory and the [Add Ring] ingredients *)

Section sring_theory.

  Variable R : SRing.

  Lemma sr_rth : ring_theory (@sr_zero R) sr_one sr_add sr_mul sr_sub sr_opp eqv.
  Proof.
    constructor.
    - exact (@sr_add_0_l R).
    - exact (@sr_add_comm R).
    - exact (@sr_add_assoc R).
    - exact (@sr_mul_1_l R).
    - exact (@sr_mul_comm R).
    - exact (@sr_mul_assoc R).
    - exact (@sr_distr_l R).
    - reflexivity.
    - exact (@sr_opp_def R).
  Qed.

  Lemma sr_ext : ring_eq_ext (@sr_add R) sr_mul sr_opp eqv.
  Proof. constructor; typeclasses eauto. Qed.

  Lemma sr_setoid : Setoid_Theory R eqv.
  Proof. exact (sr_equiv R). Qed.

End sring_theory.

Section sring_basic.

  Variable R : SRing.
  Add Ring sr_basic_ring : (sr_rth R) (setoid (sr_setoid R) (sr_ext R)).
  Implicit Types x y z : R.

  Lemma pow_add x m n : eqv (sr_pow x (Nat.add m n)) (sr_mul (sr_pow x m) (sr_pow x n)).
  Proof. induction m as [ | m IH ]; simpl; [ sring | rewrite IH; sring ]. Qed.

  Lemma pow_pos_nat x p : eqv (sr_pow x (Pos.to_nat p)) (pow_pos sr_mul x p).
  Proof.
    induction p as [ p IH | p IH | ].
    - rewrite Pos2Nat.inj_xI; cbn [pow_pos]; cbn [Nat.mul sr_pow].
      rewrite Nat.add_0_r pow_add IH; reflexivity.
    - rewrite Pos2Nat.inj_xO; cbn [pow_pos Nat.mul]; rewrite Nat.add_0_r pow_add IH; reflexivity.
    - simpl; sring.
  Qed.

  Lemma sr_pow_th : power_theory (@sr_one R) sr_mul eqv N.to_nat sr_pow.
  Proof.
    constructor; intros r [ | p ]; simpl; [ reflexivity | apply pow_pos_nat ].
  Qed.

  Lemma of_nat_S n : eqv (of_nat (S n) : R) (sr_add sr_one (of_nat n)).
  Proof. destruct n as [ | n ]; simpl; [ sring | sring ]. Qed.

  Lemma of_nat_add m n : eqv (of_nat (Nat.add m n) : R) (sr_add (of_nat m) (of_nat n)).
  Proof.
    induction m as [ | m IH ]; [ simpl; sring | ].
    rewrite Nat.add_succ_l !of_nat_S IH; sring.
  Qed.

  Lemma of_nat_mul m n : eqv (of_nat (Nat.mul m n) : R) (sr_mul (of_nat m) (of_nat n)).
  Proof.
    induction m as [ | m IH ]; [ simpl; sring | ].
    rewrite Nat.mul_succ_l of_nat_add IH of_nat_S; sring.
  Qed.

  Lemma of_pos_gen p : eqv (of_pos p : R) (gen_phiPOS sr_one sr_add sr_mul p).
  Proof.
    unfold of_pos; induction p as [ p IH | p IH | ].
    - rewrite Pos2Nat.inj_xI of_nat_S Nat.mul_comm of_nat_mul IH; simpl.
      destruct p; simpl; sring.
    - rewrite Pos2Nat.inj_xO Nat.mul_comm of_nat_mul IH; simpl.
      destruct p; simpl; sring.
    - reflexivity.
  Qed.

  Lemma of_Z_gen (z : Z) : eqv (of_Z z : R) (gen_phiZ sr_zero sr_one sr_add sr_mul sr_opp z).
  Proof. destruct z as [ | p | p ]; simpl; [ reflexivity | | ]; rewrite of_pos_gen; reflexivity. Qed.

  Lemma of_Z_morph :
    ring_morph (@sr_zero R) sr_one sr_add sr_mul sr_sub sr_opp eqv Z0 (Zpos xH) Z.add Z.mul Z.sub Z.opp Z.eqb of_Z.
  Proof.
    pose proof (gen_phiZ_morph (sr_setoid R) (sr_ext R) (sr_rth R)) as M.
    destruct M; constructor; intros; rewrite ?of_Z_gen; auto.
  Qed.

End sring_basic.

(* constant recognition for [Add Ring]: 0, 1 and [of_nat k] for a closed
   numeral k are mapped to the Z constant whose [of_Z] is convertible to
   the term *)
Ltac sof_cst t :=
  match t with
  | @sr_zero _ => constr:(Z0)
  | @sr_one _ => constr:(Zpos xH)
  | @of_nat _ ?n =>
      match isnatcst n with
      | true => let z := eval compute in (Z.of_nat n) in constr:(z)
      | _ => constr:(InitialRing.NotConstant)
      end
  | @of_Z _ ?z =>
      match isZcst z with
      | true => constr:(z)
      | _ => constr:(InitialRing.NotConstant)
      end
  | @of_pos _ ?p =>
      match isPcst p with
      | true => constr:(Zpos p)
      | _ => constr:(InitialRing.NotConstant)
      end
  | _ => constr:(InitialRing.NotConstant)
  end.

Ltac sof_pow_cst t :=
  match isnatcst t with
  | false => constr:(InitialRing.NotConstant)
  | _ => constr:(N.of_nat t)
  end.


(** * Notations *)

Declare Scope sof_scope.
Delimit Scope sof_scope with sof.

Notation "x ≡ y" := (eqv x y) (at level 70, no associativity) : sof_scope.
Notation "x ≢ y" := (~ eqv x y) (at level 70, no associativity) : sof_scope.

(** * Setoid ordered fields *)


Record SOF : Type := {
  sof_ring :> SRing;
  sof_le : sof_ring -> sof_ring -> Prop;
  sof_lt : sof_ring -> sof_ring -> Prop;
  sof_abs : sof_ring -> sof_ring;
  of_rat : rat -> sof_ring;
  sof_le_wd : Proper (eqv ==> eqv ==> iff) sof_le;
  sof_lt_wd : Proper (eqv ==> eqv ==> iff) sof_lt;
  (* field *)
  sof_neq_1_0 : ~ @eqv sof_ring sr_one sr_zero;
  sof_inv_l : forall x : sof_ring, ~ eqv x sr_zero -> eqv (sr_mul (sr_inv x) x) sr_one;
  sof_inv_0 : @eqv sof_ring (sr_inv sr_zero) sr_zero;
  (* order (the axioms of Stdlib's [OrderedRing.SOR]) *)
  sof_le_refl : forall x : sof_ring, sof_le x x;
  sof_le_antisym : forall x y : sof_ring, sof_le x y -> sof_le y x -> eqv x y;
  sof_le_trans : forall x y z : sof_ring, sof_le x y -> sof_le y z -> sof_le x z;
  sof_lt_le_neq : forall x y : sof_ring, sof_lt x y <-> sof_le x y /\ ~ eqv x y;
  sof_lt_trichotomy : forall x y : sof_ring, sof_lt x y \/ eqv x y \/ sof_lt y x;
  sof_add_le_mono_l : forall x y z : sof_ring, sof_le x y -> sof_le (sr_add z x) (sr_add z y);
  sof_mul_pos : forall x y : sof_ring, sof_lt sr_zero x -> sof_lt sr_zero y -> sof_lt sr_zero (sr_mul x y);
  (* absolute value *)
  sof_abs_pos : forall x : sof_ring, sof_le sr_zero x -> eqv (sof_abs x) x;
  sof_abs_neg : forall x : sof_ring, sof_le x sr_zero -> eqv (sof_abs x) (sr_opp x);
  (* the embedding of the rationals *)
  sof_of_rat_add : forall a b, eqv (of_rat (a + b)%R) (sr_add (of_rat a) (of_rat b));
  sof_of_rat_mul : forall a b, eqv (of_rat (a * b)%R) (sr_mul (of_rat a) (of_rat b));
  sof_of_rat_1 : eqv (of_rat 1%R) sr_one;
  sof_of_rat_le : forall a b, (a <= b)%R -> sof_le (of_rat a) (of_rat b)
}.

Arguments sof_le {s} _ _.
Arguments sof_lt {s} _ _.
Arguments sof_abs {s} _.
Arguments of_rat {s} _%_R.
Arguments sof_neq_1_0 {s}.
Arguments sof_inv_l {s}.
Arguments sof_inv_0 {s}.
Arguments sof_le_refl {s}.
Arguments sof_le_antisym {s}.
Arguments sof_le_trans {s}.
Arguments sof_lt_le_neq {s}.
Arguments sof_lt_trichotomy {s}.
Arguments sof_add_le_mono_l {s}.
Arguments sof_mul_pos {s}.
Arguments sof_abs_pos {s}.
Arguments sof_abs_neg {s}.
Arguments sof_of_rat_add {s}.
Arguments sof_of_rat_mul {s}.
Arguments sof_of_rat_1 {s}.
Arguments sof_of_rat_le {s}.

#[global] Existing Instance sof_le_wd.
#[global] Existing Instance sof_lt_wd.

Definition of_int {R : SRing} (z : int) : R :=
  match z with
  | Posz n => of_nat n
  | Negz n => sr_opp (of_nat n.+1)
  end.

Definition sof_min {F : SOF} (x y : F) : F :=
  sr_div (sr_sub (sr_add x y) (sof_abs (sr_sub x y))) (of_nat 2).
Definition sof_max {F : SOF} (x y : F) : F :=
  sr_div (sr_add (sr_add x y) (sof_abs (sr_sub x y))) (of_nat 2).

(* case distinction on [c ≡ 0] without a decision procedure: since
   [inv 0 ≡ 0], [sof_nz c = c / c] is 0 for c ≡ 0 and 1 otherwise, so
   [sof_sel0 c a b] is [a] for c ≡ 0 and [b] otherwise. This replaces
   every [if c == 0 then a else b] of the MathComp version (SETOID.md);
   in the ultrapower it is the pointwise case distinction. *)
Definition sof_nz {R : SRing} (c : R) : R := sr_mul c (sr_inv c).
Definition sof_sel0 {R : SRing} (c a b : R) : R := sr_add a (sr_mul (sof_nz c) (sr_sub b a)).

Notation "0" := (@sr_zero _) : sof_scope.
Notation "1" := (@sr_one _) : sof_scope.
Notation "x + y" := (sr_add x y) : sof_scope.
Notation "x * y" := (sr_mul x y) : sof_scope.
Notation "- x" := (sr_opp x) : sof_scope.
Notation "- 1" := (sr_opp (@sr_one _)) : sof_scope.
Notation "x - y" := (sr_sub x y) : sof_scope.
Notation "x ^-1" := (sr_inv x) : sof_scope.
Notation "x / y" := (sr_div x y) : sof_scope.
Notation "x ^+ n" := (sr_pow x n) : sof_scope.
Notation "n %:R" := (of_nat n) : sof_scope.
Notation "z %:~R" := (of_int z) : sof_scope.
Notation "x <= y" := (sof_le x y) : sof_scope.
Notation "x < y" := (sof_lt x y) : sof_scope.
Notation "x >= y" := (sof_le y x) (only parsing) : sof_scope.
Notation "x > y" := (sof_lt y x) (only parsing) : sof_scope.
Notation "x <= y <= z" := (sof_le x y /\ sof_le y z) : sof_scope.
Notation "x <= y < z" := (sof_le x y /\ sof_lt y z) : sof_scope.
Notation "x < y <= z" := (sof_lt x y /\ sof_le y z) : sof_scope.
Notation "x < y < z" := (sof_lt x y /\ sof_lt y z) : sof_scope.
Notation "`| x |" := (sof_abs x) : sof_scope.

(** * Theory of setoid ordered fields *)

Section sof_basics.

  Variable F : SOF.
  Implicit Types x y z : F.

  Lemma sof_fth : field_theory (@sr_zero F) sr_one sr_add sr_mul sr_sub sr_opp sr_div sr_inv eqv.
  Proof.
    constructor.
    - exact (sr_rth F).
    - exact (@sof_neq_1_0 F).
    - reflexivity.
    - exact (@sof_inv_l F).
  Qed.

  Lemma sof_sor : OrderedRing.SOR (@sr_zero F) sr_one sr_add sr_mul sr_sub sr_opp eqv sof_le sof_lt.
  Proof.
    constructor.
    - exact (sr_setoid F).
    - intros ? ? H ? ? H'; rewrite H H'; reflexivity.
    - intros ? ? H ? ? H'; rewrite H H'; reflexivity.
    - intros ? ? H; rewrite H; reflexivity.
    - intros ? ? H ? ? H'; rewrite H H'; reflexivity.
    - intros ? ? H ? ? H'; rewrite H H'; reflexivity.
    - exact (sr_rth F).
    - exact (@sof_le_refl F).
    - exact (@sof_le_antisym F).
    - exact (@sof_le_trans F).
    - exact (@sof_lt_le_neq F).
    - exact (@sof_lt_trichotomy F).
    - exact (@sof_add_le_mono_l F).
    - exact (@sof_mul_pos F).
    - intros H; apply (@sof_neq_1_0 F); symmetry; exact H.
  Qed.

  Add Field sof_basic_field : (sof_fth) (setoid (sr_setoid F) (sr_ext F),
    morphism (of_Z_morph F), constants [sof_cst], power_tac (sr_pow_th F) [sof_pow_cst]).
  (* (the completeness modifier needs characteristic 0, proved below) *)

  Local Open Scope sof_scope.

  (* a first test of [sfield] with constants and powers *)
  Lemma sof_field_test x y : x ≢ 0 -> (x + y) ^+ 2 / x ≡ x + 2%:R * y + y * y / x.
  Proof. intros; sfield; exact H. Qed.

  Lemma sof_eq_dec x y : x ≡ y \/ x ≢ y.
  Proof. exact (OrderedRing.Req_em sof_sor x y). Qed.

  Lemma sof_le_total x y : x <= y \/ y <= x.
  Proof.
    destruct (sof_lt_trichotomy x y) as [ H | [ H | H ] ].
    - left; apply sof_lt_le_neq in H; tauto.
    - left; rewrite H; apply sof_le_refl.
    - right; apply sof_lt_le_neq in H; tauto.
  Qed.

  Lemma sof_lt01 : (0 : F) < 1.
  Proof. exact (OrderedRing.Rlt_0_1 sof_sor). Qed.

  Lemma sof_of_nat_pos n : (0 : F) < (S n)%:R.
  Proof.
    induction n as [ | n IH ]; [ exact sof_lt01 | ].
    rewrite of_nat_S; apply (OrderedRing.Rplus_pos_pos sof_sor); [ exact sof_lt01 | exact IH ].
  Qed.

  Lemma sof_of_nat_ge0 n : (0 : F) <= n%:R.
  Proof.
    destruct n as [ | n ]; [ apply sof_le_refl | ].
    apply sof_lt_le_neq, sof_of_nat_pos.
  Qed.

  (* characteristic zero *)
  Lemma sof_of_nat_neq0 n : ((S n)%:R : F) ≢ 0.
  Proof. intros H; apply (OrderedRing.Rlt_neq sof_sor _ _ (sof_of_nat_pos n)); symmetry; exact H. Qed.

  Lemma sof_of_nat_inj m n : (m%:R : F) ≡ n%:R -> m = n.
  Proof.
    revert n; induction m as [ | m IH ]; intros [ | n ] H.
    - reflexivity.
    - exfalso; apply (sof_of_nat_neq0 n); symmetry; exact H.
    - exfalso; apply (sof_of_nat_neq0 m); exact H.
    - f_equal; apply IH; rewrite !of_nat_S in H.
      apply (OrderedRing.Rplus_cancel_l sof_sor _ _ 1); exact H.
  Qed.

  Lemma sof_of_pos_pos p : (0 : F) < of_pos p.
  Proof.
    unfold of_pos; destruct (Pos2Nat.is_succ p) as [ n -> ]; apply sof_of_nat_pos.
  Qed.

  Lemma sof_of_pos_neq0 p : (of_pos p : F) ≢ 0.
  Proof. intros H; apply (OrderedRing.Rlt_neq sof_sor _ _ (sof_of_pos_pos p)); symmetry; exact H. Qed.

  Lemma of_Z_pos_add (p q : positive) : (of_pos (Pos.add p q) : F) ≡ of_pos p + of_pos q.
  Proof. exact (morph_add (of_Z_morph F) (Zpos p) (Zpos q)). Qed.

  Lemma of_Z_add (a b : Z) : (of_Z (Z.add a b) : F) ≡ of_Z a + of_Z b.
  Proof. exact (morph_add (of_Z_morph F) a b). Qed.
  Lemma of_Z_mul (a b : Z) : (of_Z (Z.mul a b) : F) ≡ of_Z a * of_Z b.
  Proof. exact (morph_mul (of_Z_morph F) a b). Qed.
  Lemma of_Z_opp (a : Z) : (of_Z (Z.opp a) : F) ≡ - of_Z a.
  Proof. exact (morph_opp (of_Z_morph F) a). Qed.
  Lemma of_Z_sub (a b : Z) : (of_Z (Z.sub a b) : F) ≡ of_Z a - of_Z b.
  Proof. exact (morph_sub (of_Z_morph F) a b). Qed.

  Lemma of_Z_pos (p : positive) : (of_Z (Zpos p) : F) ≡ of_pos p.
  Proof. reflexivity. Qed.

  Lemma of_Z_ge0 (z : Z) : (Z.le 0 z) -> (0 : F) <= of_Z z.
  Proof.
    destruct z as [ | p | p ]; intros H; simpl.
    - apply sof_le_refl.
    - apply sof_lt_le_neq, sof_of_pos_pos.
    - exfalso; apply H; reflexivity.
  Qed.

  Lemma of_Z_le (a b : Z) : (Z.le a b) -> (of_Z a : F) <= of_Z b.
  Proof.
    intros H.
    assert (H' : (Z.le 0 (Z.sub b a))) by (apply Zle_minus_le_0; exact H).
    apply of_Z_ge0 in H'; rewrite of_Z_sub in H'.
    apply (proj2 (OrderedRing.Rle_le_minus sof_sor _ _)); exact H'.
  Qed.

  Lemma of_Z_lt (a b : Z) : (Z.lt a b) -> (of_Z a : F) < of_Z b.
  Proof.
    intros H.
    assert (H' : (Z.lt 0 (Z.sub b a))) by lia.
    destruct (Z.sub b a) as [ | p | p ] eqn:E; try (exfalso; lia).
    assert (K : (0 : F) < of_Z (Z.sub b a)) by (rewrite E; apply sof_of_pos_pos).
    rewrite of_Z_sub in K; apply (proj2 (OrderedRing.Rlt_lt_minus sof_sor _ _)); exact K.
  Qed.

  Lemma of_Z_inj (a b : Z) : (of_Z a : F) ≡ of_Z b -> a = b.
  Proof.
    intros H; destruct (Z.lt_total a b) as [ L | [ L | L ] ]; [ | exact L | ].
    - exfalso; apply (OrderedRing.Rlt_neq sof_sor _ _ (of_Z_lt _ _ L)); exact H.
    - exfalso; apply (OrderedRing.Rlt_neq sof_sor _ _ (of_Z_lt _ _ L)); symmetry; exact H.
  Qed.

  Lemma sof_Z_complete (a b : Z) : (of_Z a : F) ≡ of_Z b -> Z.eqb a b = true.
  Proof. move=> /of_Z_inj ->; apply Z.eqb_refl. Qed.

  (** the embedding of the rationals *)

  Lemma of_rat_0 : of_rat 0 ≡ (0 : F).
  Proof.
    have H := @sof_of_rat_add F 0%R 0%R; rewrite addr0 in H.
    apply (OrderedRing.Rplus_cancel_l sof_sor _ _ (of_rat 0)); rewrite -H; sring.
  Qed.

  Lemma of_rat_opp a : of_rat (- a)%R ≡ - (of_rat a : F).
  Proof.
    have H := @sof_of_rat_add F (- a)%R a; rewrite addNr of_rat_0 in H.
    apply (OrderedRing.Rplus_cancel_l sof_sor _ _ (of_rat a)).
    rewrite sr_add_comm -H; sring.
  Qed.

  Lemma of_rat_sub a b : of_rat (a - b)%R ≡ (of_rat a - of_rat b : F).
  Proof. rewrite sof_of_rat_add of_rat_opp; reflexivity. Qed.

  Lemma of_rat_nat n : of_rat (n%:R)%R ≡ (n%:R : F).
  Proof.
    induction n as [ | n IH ]; [ exact of_rat_0 | ].
    rewrite mulrS sof_of_rat_add sof_of_rat_1 IH of_nat_S; reflexivity.
  Qed.

  Lemma of_rat_int (z : int) : of_rat (z%:~R)%R ≡ (z%:~R : F).
  Proof.
    case: z => n; first by rewrite -pmulrn; exact: of_rat_nat.
    rewrite NegzE mulrNz of_rat_opp -pmulrn of_rat_nat; reflexivity.
  Qed.

  Lemma of_rat_neq0 a : a != 0%R -> (of_rat a : F) ≢ 0.
  Proof.
    move=> Ha H; apply (@sof_neq_1_0 F).
    rewrite -(@sof_of_rat_1 F) -(mulVf Ha) sof_of_rat_mul H; sring.
  Qed.

  Lemma of_rat_inv a : of_rat (a^-1)%R ≡ ((of_rat a)^-1 : F).
  Proof.
    case: (eqVneq a 0%R) => [ -> | Ha ].
    - rewrite invr0 of_rat_0; symmetry; exact (@sof_inv_0 F).
    - have H := @sof_of_rat_mul F (a^-1)%R a; rewrite (mulVf Ha) sof_of_rat_1 in H.
      have Ha' := of_rat_neq0 a Ha.
      transitivity ((of_rat a^-1 * of_rat a) * (of_rat a)^-1 : F); [ sfield; exact Ha' | ].
      rewrite -H; sring.
  Qed.

  Lemma of_rat_div a b : of_rat (a / b)%R ≡ (of_rat a / of_rat b : F).
  Proof. rewrite sof_of_rat_mul of_rat_inv; reflexivity. Qed.

  Lemma of_rat_inj a b : (of_rat a : F) ≡ of_rat b -> a = b.
  Proof.
    move=> H; apply/eqP; rewrite -subr_eq0; apply/negPn/negP => Hn.
    apply (of_rat_neq0 _ Hn); rewrite of_rat_sub H; sring.
  Qed.

  Lemma of_rat_lt a b : (a < b)%R -> (of_rat a : F) < of_rat b.
  Proof.
    move=> H; apply sof_lt_le_neq; split; first by apply sof_of_rat_le, ltW.
    by move=> /(of_rat_inj _ _) E; move: H; rewrite E ltxx.
  Qed.

  Lemma of_rat_le_iff a b : (of_rat a : F) <= of_rat b <-> (a <= b)%R.
  Proof.
    split; last exact: sof_of_rat_le.
    move=> H; rewrite leNgt; apply/negP => /(of_rat_lt _ _) H'.
    exact: (proj1 (OrderedRing.Rlt_nge sof_sor _ _) H' H).
  Qed.

  Lemma of_rat_lt_iff a b : (of_rat a : F) < of_rat b <-> (a < b)%R.
  Proof.
    split; last exact: of_rat_lt.
    move=> H; rewrite ltNge; apply/negP => /(@sof_of_rat_le F _ _) H'.
    exact: (proj1 (OrderedRing.Rlt_nge sof_sor _ _) H H').
  Qed.

  Lemma of_rat_eq_iff a b : (of_rat a : F) ≡ of_rat b <-> a = b.
  Proof. split; [ exact: of_rat_inj | move=> ->; reflexivity ]. Qed.

  (** absolute value, min, max *)

  #[global] Instance sof_abs_wd : Proper (eqv ==> eqv) (@sof_abs F).
  Proof.
    move=> x y H; case: (sof_le_total 0 x) => Hx.
    - have Hy : 0 <= y by rewrite -H.
      rewrite (sof_abs_pos _ Hx) (sof_abs_pos _ Hy); exact H.
    - have Hy : y <= 0 by rewrite -H.
      rewrite (sof_abs_neg _ Hx) (sof_abs_neg _ Hy) H; reflexivity.
  Qed.

  #[global] Instance sof_le_preorder : PreOrder (@sof_le F).
  Proof. split; [ exact sof_le_refl | exact sof_le_trans ]. Qed.

  #[global] Instance sof_lt_strict : StrictOrder (@sof_lt F).
  Proof.
    split.
    - intros x H; apply sof_lt_le_neq in H; apply H; reflexivity.
    - intros x y z H1 H2; exact (OrderedRing.Rlt_trans sof_sor _ _ _ H1 H2).
  Qed.

End sof_basics.

Arguments sof_fth {F}.
Arguments sof_sor {F}.

(** The one-line declarations that make [sring] and [sfield] work for
    a setoid ring [R] or a setoid ordered field [F] in a Section (they
    must be repeated in every Section, as [Add Ring] does not accept a
    parametric theory):

      Add Ring R_ring : (sr_rth R) (setoid (sr_setoid R) (sr_ext R),
        morphism (of_Z_morph R), constants [sof_cst],
        power_tac (sr_pow_th R) [sof_pow_cst]).

      Add Field F_field : (@sof_fth F) (setoid (sr_setoid F) (sr_ext F),
        morphism (of_Z_morph F), constants [sof_cst],
        power_tac (sr_pow_th F) [sof_pow_cst],
        completeness (sof_Z_complete F)).

    With [completeness], [sfield] discharges nonzero side conditions on
    numeral constants itself (characteristic 0). *)
