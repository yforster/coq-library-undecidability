(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Hilbert's tenth problem over the rational numbers (H10Q):
   given a polynomial with integer coefficients, decide whether
   it has a rational zero. Polynomials are the Z-coefficient
   dio_polynomials of H10Z.v, evaluated in MathComp's rat.

   This file contains the problem definitions only:
   - H10Q, the problem of Theorem 1.1 (thm:main) of the paper,
     with the number n of variables part of the input;
   - H10Q_deg4 and H10Q_SOS2, the restricted problems (i) and (ii)
     of Corollary 7.1 (thm:degree-normal-form).
   The reductions between them are in H10/Reductions/H10Q_*.v,
   their enumerability in H10/Rational/H10Q_enum.v. *)

From Stdlib Require Import ZArith List.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos.

(* dio_logic is only Required, not Imported: its notations clash with MathComp *)
From Undecidability.H10.Dio
  Require dio_logic.

From Undecidability.H10
  Require Import H10Z.

From Undecidability.H10.Rational
  Require Import RatUtil.

From mathcomp Require Import boot algebra.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.

Local Open Scope ring_scope.

Section dp_eval_rat.

  Variable (V P : Set).

  (* evaluation of a Z-coefficient polynomial at rational values *)
  Fixpoint dp_eval_rat (φ : V -> rat) (ν : P -> rat) (p : dio_polynomial V P) : rat :=
    match p with
      | dp_cnst n => Z_to_rat n
      | dp_var v => φ v
      | dp_par i => ν i
      | dp_comp dio_logic.do_add p q => dp_eval_rat φ ν p + dp_eval_rat φ ν q
      | dp_comp dio_logic.do_mul p q => dp_eval_rat φ ν p * dp_eval_rat φ ν q
    end.

  Fact dp_eval_rat_fix_add φ ν p q :
    dp_eval_rat φ ν (dp_add p q) = dp_eval_rat φ ν p + dp_eval_rat φ ν q.
  Proof. trivial. Qed.

  Fact dp_eval_rat_fix_mul φ ν p q :
    dp_eval_rat φ ν (dp_mul p q) = dp_eval_rat φ ν p * dp_eval_rat φ ν q.
  Proof. trivial. Qed.

  Fact dp_eval_rat_ext φ ν φ' ν' p :
        (forall v, In v (dp_var_list p) -> φ v = φ' v)
     -> (forall i, In i (dp_par_list p) -> ν i = ν' i)
     -> dp_eval_rat φ ν p = dp_eval_rat φ' ν' p.
  Proof.
    induction p as [ | | | [] p Hp q Hq ]; simpl; intros H1 H2; f_equal; auto;
      ((apply Hp || apply Hq); intros; [ apply H1 | apply H2 ]; apply in_or_app; auto).
  Qed.

  (* evaluation in rat commutes with evaluation in Z *)
  Fact dp_eval_rat_Z (φ : V -> Z) (ν : P -> Z) p :
    dp_eval_rat (fun v => Z_to_rat (φ v)) (fun i => Z_to_rat (ν i)) p
      = Z_to_rat (dp_eval φ ν p).
  Proof.
    induction p as [ | | | [] p Hp q Hq ]; simpl; auto.
    + rewrite Hp Hq; symmetry; apply Z_to_rat_add.
    + rewrite Hp Hq; symmetry; apply Z_to_rat_mul.
  Qed.

  (* syntactic total degree: an upper bound for the total degree of
     the polynomial function denoted by p (cancellations, e.g. in
     x*x + (-1)*(x*x), are not taken into account) *)
  Fixpoint dp_deg (p : dio_polynomial V P) : nat :=
    match p with
      | dp_cnst _ => 0
      | dp_var _ => 1
      | dp_par _ => 0
      | dp_comp dio_logic.do_add p q => Nat.max (dp_deg p) (dp_deg q)
      | dp_comp dio_logic.do_mul p q => Nat.add (dp_deg p) (dp_deg q)
    end.

End dp_eval_rat.

(* An instance of H10Q is the same as an instance of H10Z:
   a polynomial with integer coefficients in n variables *)
Definition H10Q_PROBLEM := H10Z_PROBLEM.

(* H10Q: does the polynomial P(x1,...,xn) have a rational zero?
   (Theorem 1.1 of the paper). The parameter type pos 0 is empty, so
   the parameter valuation (fun _ => 0) is irrelevant. *)
Definition H10Q : H10Q_PROBLEM -> Prop :=
  fun '(existT n p) => exists Φ : pos n -> rat, dp_eval_rat Φ (fun _ => 0) p = 0.

(* Corollary 7.1 (i) of the paper: H10Q restricted to polynomials
   of total degree at most four.

   Since dp_deg is a syntactic upper bound, an instance is a polynomial
   together with a presentation witnessing degree <= 4. Every integral
   polynomial of total degree <= 4 has such a presentation (e.g. as a
   sum of monomials), so H10Q_deg4 is the paper's problem up to a
   computable change of presentation; formally it is a sub-problem of
   H10Q (H10Q_deg4_H10Q), which is the direction relevant for the
   hardness result H10Q ⪯ H10Q_deg4. *)
Definition H10Q_deg4_PROBLEM :=
  { n : nat & { p : dio_polynomial (pos n) (pos 0) | le (dp_deg p) 4 } }.

Definition H10Q_deg4 : H10Q_deg4_PROBLEM -> Prop :=
  fun '(existT n (exist p _)) =>
    exists Φ : pos n -> rat, dp_eval_rat Φ (fun _ => 0) p = 0.

(* Corollary 7.1 (ii) of the paper: given a nonempty list q1,...,qm of
   integral polynomials of (syntactic) total degree at most two, does
   q1^2 + ... + qm^2 have a rational zero? The list is part of the
   input; no recognition of sum-of-squares presentations is needed. *)
Definition H10Q_SOS2_PROBLEM :=
  { n : nat & { l : list (dio_polynomial (pos n) (pos 0)) |
                  lt 0 (length l) /\ forallb (fun q => Nat.leb (dp_deg q) 2) l = true } }.

(* the boolean degree check (chosen so that proofs are unique) agrees with Forall *)
Fact dp_deg_forallb_Forall n (l : list (dio_polynomial (pos n) (pos 0))) d :
  forallb (fun q => Nat.leb (dp_deg q) d) l = true <-> Forall (fun q => le (dp_deg q) d) l.
Proof.
  rewrite forallb_forall Forall_forall.
  split; intros H q Hq; apply Nat.leb_le, H, Hq.
Qed.

(* the sum of squares, evaluated in rat *)
Definition H10Q_SOS2 : H10Q_SOS2_PROBLEM -> Prop :=
  fun '(existT n (exist l _)) =>
    exists Φ : pos n -> rat, \sum_(q <- l) (dp_eval_rat Φ (fun _ => 0) q) ^+ 2 = 0.

(* over Q, a sum of squares vanishes iff every summand vanishes *)
Lemma H10Q_SOS2_spec n l H :
      H10Q_SOS2 (existT _ n (exist _ l H))
  <-> exists Φ : pos n -> rat, Forall (fun q => dp_eval_rat Φ (fun _ => 0) q = 0) l.
Proof.
  simpl; split; intros (Φ & HΦ); exists Φ.
  - apply Forall_forall, rat_sum_sqr_map_eq0_iff, HΦ.
  - apply rat_sum_sqr_map_eq0_iff, Forall_forall, HΦ.
Qed.
