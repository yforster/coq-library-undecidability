(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Semi-decidability and enumerability of H10Q, H10Q_deg4, H10Q_SOS2
   and H10Z. This is the computably-enumerable half of Corollary 7.1
   (thm:degree-normal-form) of the paper: "Integer solvability is itself
   computably enumerable by enumeration of integer tuples" and "Rational
   solvability is also computably enumerable: enumerate rational tuples
   and evaluate the input polynomial exactly". H10Z_semi_decidable is
   also the enumeration half of the parallel search (FiniteTests.v).

   Valuations pos n -> X are enumerated through the DLW vectors vec X n
   (RatUtil.vec_enum); the library's enumerator__T_Vector is for the
   Stdlib Vector.t and does not apply directly. *)

From Stdlib Require Import ZArith Lia List.
From Stdlib Require Cantor.

From Undecidability.Synthetic
  Require Import Definitions EnumerabilityFacts ListEnumerabilityFacts.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos vec.

From Undecidability.H10
  Require Import H10Z.

From Undecidability.H10.Rational
  Require RatUtil.


(** * A generic semi-decider: search over all valuations pos n -> X *)

Section sdec_search.

  Variables (X : Type) (e : forall n, nat -> option (vec X n))
            (He : forall n (g : pos n -> X), exists k v, e n k = Some v /\ forall p, vec_pos v p = g p).

  Variables (I : Type) (dim : I -> nat) (test : forall i, (pos (dim i) -> X) -> bool)
            (Htest : forall i g g', (forall p, g p = g' p) -> test i g = test i g')
            (Q : I -> Prop) (HQ : forall i, Q i <-> exists g, test i g = true).

  Lemma sdec_search : semi_decidable Q.
  Proof using He Htest HQ.
    exists (fun i k => match e (dim i) k with
                      | Some v => test i (vec_pos v)
                      | None => false
                      end).
    intros i; rewrite HQ; split.
    - intros (g & Hg).
      destruct (He (dim i) g) as (k & v & H1 & H2).
      exists k; rewrite H1, <- Hg; apply Htest, H2.
    - intros (k & Hk).
      destruct (e (dim i) k) as [ v | ]; [ | discriminate ].
      exists (vec_pos v); exact Hk.
  Qed.

End sdec_search.

(** * An enumerator for Z *)

Definition Z_list (k : nat) : list Z := Z.of_nat k :: (- Z.of_nat k)%Z :: nil.

Lemma Z_list_enumerator : list_enumerator__T Z_list Z.
Proof.
  intros z; exists (Z.abs_nat z); unfold Z_list.
  destruct (Z.le_ge_cases 0 z); [ left | right; left ]; lia.
Qed.

Definition Z_enum (k : nat) : option Z :=
  let (a, b) := Cantor.of_nat k in nth_error (Z_list a) b.

Lemma enumerator__T_Z : enumerator__T Z_enum Z.
Proof.
  intros z; apply (list_enumerator_enumerator (p := fun _ => True)); auto.
  intros x; split; auto; intros _; apply Z_list_enumerator.
Qed.

Lemma Z_pos_fun_enum n (g : pos n -> Z) :
  exists k v, RatUtil.vec_enum Z_enum n k = Some v /\ forall p, vec_pos v p = g p.
Proof. apply RatUtil.pos_fun_enum, enumerator__T_Z. Qed.

(** * Semi-decidability *)

Theorem H10Z_semi_decidable : semi_decidable H10Z.
Proof.
  apply (@sdec_search Z (RatUtil.vec_enum Z_enum) Z_pos_fun_enum _ (@projT1 _ _)
           (fun i g => Z.eqb (dp_eval g (fun _ => 0%Z) (projT2 i)) 0%Z)).
  - intros [ n p ] g g' H; simpl; f_equal; apply dp_eval_ext; auto.
  - intros [ n p ]; simpl; split; intros (g & Hg); exists g; now apply Z.eqb_eq.
Qed.

(** * An enumerator for polynomials *)

Section dp_enum.

  Variables (V P : Set)
            (LV : nat -> list V) (HV : list_enumerator__T LV V)
            (LP : nat -> list P) (HP : list_enumerator__T LP P).

  Fixpoint dp_list k : list (dio_polynomial V P) :=
    match k with
    | 0 => nil
    | S k => dp_list k
          ++ map dp_cnst (Z_list k)
          ++ map dp_var (LV k)
          ++ map dp_par (LP k)
          ++ flat_map (fun p => flat_map (fun q => dp_add p q :: dp_mul p q :: nil) (dp_list k)) (dp_list k)
    end.

  Local Fact dp_list_mono k m p : le k m -> In p (dp_list k) -> In p (dp_list m).
  Proof.
    induction 1 as [ | m _ IH ]; auto.
    intros H; simpl; apply in_or_app; left; auto.
  Qed.

  Lemma dp_list_enumerator : list_enumerator__T dp_list (dio_polynomial V P).
  Proof using HV HP.
    intros p; induction p as [ z | v | i | o p (kp & Hp) q (kq & Hq) ].
    - destruct (Z_list_enumerator z) as (k & Hk); exists (S k); cbn [dp_list].
      rewrite !in_app_iff; right; left; now apply in_map.
    - destruct (HV v) as (k & Hk); exists (S k); cbn [dp_list].
      rewrite !in_app_iff; right; right; left; now apply in_map.
    - destruct (HP i) as (k & Hk); exists (S k); cbn [dp_list].
      rewrite !in_app_iff; right; right; right; left; now apply in_map.
    - exists (S (Nat.max kp kq)); cbn [dp_list].
      rewrite !in_app_iff; right; right; right; right.
      apply in_flat_map; exists p; split.
      + revert Hp; apply dp_list_mono; lia.
      + apply in_flat_map; exists q; split.
        * revert Hq; apply dp_list_mono; lia.
        * destruct o; simpl; auto.
  Qed.

  Definition dp_enum (k : nat) : option (dio_polynomial V P) :=
    let (a, b) := Cantor.of_nat k in nth_error (dp_list a) b.

  Lemma enumerator__T_dp : enumerator__T dp_enum (dio_polynomial V P).
  Proof using HV HP.
    intros p; apply (list_enumerator_enumerator (p := fun _ => True)); auto.
    intros x; split; auto; intros _; apply dp_list_enumerator.
  Qed.

End dp_enum.

Lemma pos_list_enumerator n : list_enumerator__T (fun _ => pos_list n) (pos n).
Proof. intros p; exists 0%nat; apply pos_list_prop. Qed.

Definition H10Z_PROBLEM_enum : nat -> option H10Z_PROBLEM :=
  sigT_enum nat_enum (fun n => dp_enum (pos n) (pos 0) (fun _ => pos_list n) (fun _ => pos_list 0)).

Lemma enumerator__T_H10Z_PROBLEM : enumerator__T H10Z_PROBLEM_enum H10Z_PROBLEM.
Proof.
  apply enumerator__T_sigT.
  - apply enumerator__T_nat.
  - intros n; apply enumerator__T_dp; apply pos_list_enumerator.
Qed.

Lemma enumerable__T_H10Z_PROBLEM : enumerable__T H10Z_PROBLEM.
Proof. exists H10Z_PROBLEM_enum; apply enumerator__T_H10Z_PROBLEM. Qed.

(** * The problems over Q *)

(* MathComp is imported only from here on, since its notations
   (e.g. for ++, map, <=) shadow those of the Stdlib *)

From Undecidability.H10
  Require Import H10Q.

From Undecidability.H10.Rational
  Require Import RatUtil.

From mathcomp Require Import boot algebra.

Import GRing.Theory Num.Theory.

(** * Semi-decidability over Q *)

Local Open Scope ring_scope.

Theorem H10Q_semi_decidable : semi_decidable H10Q.
Proof.
  apply (@sdec_search rat rat_vec_enum rat_pos_fun_enum _ (@projT1 _ _)
           (fun i g => dp_eval_rat g (fun _ => 0) (projT2 i) == 0)).
  - intros [ n p ] g g' H; simpl; f_equal; apply dp_eval_rat_ext; auto.
  - intros [ n p ]; simpl; split; intros (g & Hg); exists g; by apply/eqP.
Qed.

Theorem H10Q_deg4_semi_decidable : semi_decidable H10Q_deg4.
Proof.
  apply (@sdec_search rat rat_vec_enum rat_pos_fun_enum _ (@projT1 _ _)
           (fun i g => dp_eval_rat g (fun _ => 0) (proj1_sig (projT2 i)) == 0)).
  - intros [ n [ p Hp ] ] g g' H; simpl; f_equal; apply dp_eval_rat_ext; auto.
  - intros [ n [ p Hp ] ]; simpl; split; intros (g & Hg); exists g; by apply/eqP.
Qed.

Theorem H10Q_SOS2_semi_decidable : semi_decidable H10Q_SOS2.
Proof.
  apply (@sdec_search rat rat_vec_enum rat_pos_fun_enum _ (@projT1 _ _)
           (fun i g => forallb (fun q => dp_eval_rat g (fun _ => 0) q == 0) (proj1_sig (projT2 i)))).
  - intros [ n [ l Hl ] ]; simpl; intros g g' H; clear Hl.
    induction l as [ | q l IHl ]; simpl; auto.
    f_equal; auto; f_equal; apply dp_eval_rat_ext; auto.
  - intros [ n [ l Hl ] ]; rewrite H10Q_SOS2_spec; simpl.
    split; intros (g & Hg); exists g.
    + apply forallb_forall; intros q Hq.
      apply/eqP; revert q Hq; apply Forall_forall, Hg.
    + apply Forall_forall; intros q Hq.
      apply/eqP; revert q Hq; apply forallb_forall, Hg.
Qed.

(* the subtype of polynomials of degree at most d *)
Definition dp_deg_enum n d (k : nat) : option { p : dio_polynomial (pos n) (pos 0) | le (dp_deg p) d } :=
  match dp_enum (pos n) (pos 0) (fun _ => pos_list n) (fun _ => pos_list 0) k with
  | Some p =>
      match le_dec (dp_deg p) d with
      | left H => Some (exist _ p H)
      | right _ => None
      end
  | None => None
  end.

Lemma enumerator__T_dp_deg n d :
  enumerator__T (dp_deg_enum n d) { p : dio_polynomial (pos n) (pos 0) | le (dp_deg p) d }.
Proof.
  intros [ p Hp ].
  destruct (@enumerator__T_dp _ _ _ (pos_list_enumerator n) _ (pos_list_enumerator 0) p) as (k & Hk).
  exists k; unfold dp_deg_enum; rewrite Hk.
  destruct (le_dec (dp_deg p) d) as [ H | H ]; [ | tauto ].
  do 2 f_equal; apply Peano_dec.le_unique.
Qed.

Lemma enumerable__T_H10Q_deg4_PROBLEM : enumerable__T H10Q_deg4_PROBLEM.
Proof.
  exists (sigT_enum nat_enum (fun n => dp_deg_enum n 4)).
  apply enumerator__T_sigT.
  - apply enumerator__T_nat.
  - intros n; apply enumerator__T_dp_deg.
Qed.

(* lists of polynomials of degree at most 2, nonempty; the side conditions
   are decided, and their proofs are unique (le_unique, UIP on bool) *)
Definition dp_list_list n : nat -> list (list (dio_polynomial (pos n) (pos 0))) :=
  L_list (dp_list (pos n) (pos 0) (fun _ => pos_list n) (fun _ => pos_list 0)).

Definition SOS2_cond n (l : list (dio_polynomial (pos n) (pos 0))) : Prop :=
  lt 0 (List.length l) /\ forallb (fun q => Nat.leb (dp_deg q) 2) l = true.

Definition SOS2_enum n (k : nat) : option { l : list (dio_polynomial (pos n) (pos 0)) | SOS2_cond n l } :=
  match (let (a, b) := Cantor.of_nat k in nth_error (dp_list_list n a) b) with
  | Some l =>
      match lt_dec 0 (List.length l), Bool.bool_dec (forallb (fun q => Nat.leb (dp_deg q) 2) l) true with
      | left H1, left H2 => Some (exist _ l (conj H1 H2))
      | _, _ => None
      end
  | None => None
  end.

Lemma enumerator__T_SOS2 n :
  enumerator__T (SOS2_enum n) { l : list (dio_polynomial (pos n) (pos 0)) | SOS2_cond n l }.
Proof.
  intros [ l [ H1 H2 ] ].
  assert (exists k, (let (a, b) := Cantor.of_nat k in nth_error (dp_list_list n a) b) = Some l) as (k & Hk).
  { apply (list_enumerator_enumerator (p := fun _ => True) (T := dp_list_list n)); auto.
    intros x; split; auto; intros _; apply enumerator__T_list, dp_list_enumerator; apply pos_list_enumerator. }
  exists k; unfold SOS2_enum; rewrite Hk.
  destruct (lt_dec 0 (List.length l)) as [ G1 | G1 ]; [ | tauto ].
  destruct (Bool.bool_dec (forallb (fun q => Nat.leb (dp_deg q) 2) l) true) as [ G2 | G2 ]; [ | tauto ].
  do 2 f_equal; f_equal; [ apply Peano_dec.le_unique | apply Eqdep_dec.UIP_dec, Bool.bool_dec ].
Qed.

Lemma enumerable__T_H10Q_SOS2_PROBLEM : enumerable__T H10Q_SOS2_PROBLEM.
Proof.
  exists (sigT_enum nat_enum SOS2_enum).
  apply enumerator__T_sigT.
  - apply enumerator__T_nat.
  - intros n; apply enumerator__T_SOS2.
Qed.

(** * Enumerability *)

Theorem H10Z_enumerable : enumerable H10Z.
Proof.
  apply semi_decidable_enumerable.
  - apply enumerable__T_H10Z_PROBLEM.
  - apply H10Z_semi_decidable.
Qed.

Theorem H10Q_enumerable : enumerable H10Q.
Proof.
  apply semi_decidable_enumerable.
  - apply enumerable__T_H10Z_PROBLEM.
  - apply H10Q_semi_decidable.
Qed.

Theorem H10Q_deg4_enumerable : enumerable H10Q_deg4.
Proof.
  apply semi_decidable_enumerable.
  - apply enumerable__T_H10Q_deg4_PROBLEM.
  - apply H10Q_deg4_semi_decidable.
Qed.

Theorem H10Q_SOS2_enumerable : enumerable H10Q_SOS2.
Proof.
  apply semi_decidable_enumerable.
  - apply enumerable__T_H10Q_SOS2_PROBLEM.
  - apply H10Q_SOS2_semi_decidable.
Qed.
