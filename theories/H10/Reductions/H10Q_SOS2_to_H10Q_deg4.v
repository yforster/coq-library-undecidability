(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Corollary 7.1 (i) of the paper: H10Q_SOS2 many-one reduces to
   H10Q_deg4 by expanding q1^2 + ... + qm^2 into one polynomial
   (H10Q_SOS2_H10Q_deg4, the reduction S_2 <=_m H_{<=4} in the proof
   of thm:degree-normal-form); composed with H10Q_H10Q_SOS2 this gives
   H10Q_H10Q_deg4.
   Together with the trivial reductions H10Q_deg4 ⪯ H10Q and
   H10Q_SOS2 ⪯ H10Q, and H10Q ⪯ H10Q_SOS2, the three problems
   are many-one interreducible. *)

From Stdlib Require Import ZArith List.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

From Undecidability.H10
  Require Import H10Z.

From Undecidability.H10.Reductions
  Require Import H10Q_to_H10Q_SOS2.

From Undecidability.H10
  Require Import H10Q.

From Undecidability.H10.Rational
  Require Import RatUtil.

From mathcomp Require Import boot algebra.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.

Local Open Scope ring_scope.

Section sum_sqr.

  Variables (V P : Set).

  (* q1*q1 + (q2*q2 + ... + (qm*qm + 0)) *)
  Definition dp_sum_sqr (l : list (dio_polynomial V P)) : dio_polynomial V P :=
    fold_right (fun q r => dp_add (dp_mul q q) r) (dp_cnst 0%ZZ) l.

  Fact dp_sum_sqr_deg l : Forall (fun q => le (dp_deg q) 2) l -> le (dp_deg (dp_sum_sqr l)) 4.
  Proof.
    induction 1 as [ | q l Hq _ IH ]; simpl; [ auto | ].
    apply Nat.max_lub; auto.
    apply Nat.le_trans with (Nat.add 2 2); [ apply Nat.add_le_mono | ]; auto.
  Qed.

  Fact dp_sum_sqr_eval φ (ν : P -> rat) l :
    dp_eval_rat φ ν (dp_sum_sqr l) = \sum_(q <- l) (dp_eval_rat φ ν q) ^+ 2.
  Proof.
    induction l as [ | q l IHl ]; simpl.
    - by rewrite big_nil Z_to_rat_0.
    - by rewrite big_cons IHl expr2.
  Qed.

End sum_sqr.

Definition SOS2_to_deg4 (x : H10Q_SOS2_PROBLEM) : H10Q_deg4_PROBLEM :=
  match x with
    | existT n (exist l Hl) =>
        existT _ n (exist _ (dp_sum_sqr l)
                    (dp_sum_sqr_deg (proj1 (dp_deg_forallb_Forall l 2) (proj2 Hl))))
  end.

Theorem H10Q_SOS2_H10Q_deg4 : H10Q_SOS2 ⪯ H10Q_deg4.
Proof.
  exists SOS2_to_deg4; intros [ n [ l Hl ] ]; simpl.
  split; intros (Φ & HΦ); exists Φ; [ rewrite dp_sum_sqr_eval | rewrite -dp_sum_sqr_eval ]; exact HΦ.
Qed.

(** * The trivial reductions back to H10Q *)

Theorem H10Q_deg4_H10Q : H10Q_deg4 ⪯ H10Q.
Proof.
  exists (fun x : H10Q_deg4_PROBLEM => match x with existT n (exist p _) => existT _ n p end).
  intros [ n [ p Hp ] ]; simpl; tauto.
Qed.

Theorem H10Q_SOS2_H10Q : H10Q_SOS2 ⪯ H10Q.
Proof. apply reduces_transitive with (1 := H10Q_SOS2_H10Q_deg4), H10Q_deg4_H10Q. Qed.

Theorem H10Q_H10Q_deg4 : H10Q ⪯ H10Q_deg4.
Proof. apply reduces_transitive with (1 := H10Q_H10Q_SOS2), H10Q_SOS2_H10Q_deg4. Qed.
