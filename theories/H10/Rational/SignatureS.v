(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A (task P2a): setoid semantics for the syntax of Signature.v.

   [fml_holds] (Signature.v) compares values with Leibniz [=]; over a
   setoid ring (SOF.v, e.g. the ultrapower) the atoms must be read with
   the setoid equality. This file provides
   - [fml_holdsS val A]: same recursion as [fml_holds], atoms [≡]/[≢];
   - [ring_okS], [fun_okS]: the constraints (a), (b) of Ambient.v with
     [≡] (integer constants by [of_Z]; functionality: [≡] inputs give
     [≡] outputs);
   - [fml_holdsS_ext]: [fml_holdsS] respects pointwise-[≡] valuations
     (also as a [Proper] instance), [fml_holdsS_subst].
   The term model [TermModelS A Ax val] needs the ambient record and
   lives in AmbientS.v (it would make this file depend on AmbientS.v,
   which depends on it); the compactness statement [CompactnessT D]
   (test-specific) is in TheoryS.v. [FinSat] stays on the rat side,
   unchanged, in Ambient.v. *)

From Stdlib Require Import Setoid Morphisms RelationClasses ZArith List.

From Undecidability.H10.Rational Require Import Signature SOF.

Set Implicit Arguments.

Local Open Scope sof_scope.

(** * Truth of formulas over a setoid ring *)

Fixpoint fml_holdsS {X : Type} {R : SRing} (val : term X -> R) (A : fml X) : Prop :=
  match A with
  | f_eq s t => val s ≡ val t
  | f_ne s t => val s ≢ val t
  | f_and A B => fml_holdsS val A /\ fml_holdsS val B
  | f_or A B => fml_holdsS val A \/ fml_holdsS val B
  | f_tt => True
  | f_ff => False
  end.

Lemma fml_holdsS_subst {X Y : Type} {R : SRing} (val : term Y -> R) (σ : X -> term Y) (A : fml X) :
  fml_holdsS val (fml_subst σ A) <-> fml_holdsS (fun t => val (tsubst σ t)) A.
Proof. induction A; simpl; tauto. Qed.

(* pointwise equivalent valuations satisfy the same formulas *)
Lemma fml_holdsS_ext {X : Type} {R : SRing} (val val' : term X -> R) :
  (forall t, val t ≡ val' t) -> forall A, fml_holdsS val A <-> fml_holdsS val' A.
Proof.
  intros H A; induction A as [ s t | s t | A HA B HB | A HA B HB | | ]; simpl.
  - rewrite (H s), (H t); reflexivity.
  - rewrite (H s), (H t); reflexivity.
  - rewrite HA, HB; reflexivity.
  - rewrite HA, HB; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition val_eqv {X : Type} {R : SRing} (val val' : term X -> R) : Prop :=
  forall t, val t ≡ val' t.

#[global] Instance fml_holdsS_wd {X : Type} {R : SRing} :
  Proper (val_eqv ==> eq ==> iff) (@fml_holdsS X R).
Proof. intros val val' H A ? <-; apply fml_holdsS_ext; exact H. Qed.

(** * The constraints (a) and (b) of Ambient.v, setoid version *)

Definition ring_okS {R : SRing} (val : gterm -> R) (t : gterm) : Prop :=
  match t with
  | tapp0 s_zero => val t ≡ 0
  | tapp0 s_one => val t ≡ 1
  | tapp0 (s_int z) => val t ≡ of_Z z
  | tapp1 s_neg s => val t ≡ - val s
  | tapp2 s_add s s' => val t ≡ val s + val s'
  | tapp2 s_mul s s' => val t ≡ val s * val s'
  | _ => True
  end.

Definition fun_okS {R : SRing} (val : gterm -> R) (t t' : gterm) : Prop :=
  match t, t' with
  | tapp1 g s, tapp1 g' s' => g = g' -> val s ≡ val s' -> val t ≡ val t'
  | tapp2 g s1 s2, tapp2 g' s1' s2' =>
      g = g' -> val s1 ≡ val s1' -> val s2 ≡ val s2' -> val t ≡ val t'
  | _, _ => True
  end.

Lemma ring_okS_ext {R : SRing} (val val' : gterm -> R) :
  val_eqv val val' -> forall t, ring_okS val t <-> ring_okS val' t.
Proof.
  intros H [ x | g | g s | g s s' ]; [ destruct x | | | ].
  - destruct g; simpl; rewrite ?(H _); reflexivity.
  - destruct g; simpl; rewrite ?(H _); reflexivity.
  - destruct g; simpl; rewrite ?(H _); reflexivity.
Qed.

Lemma fun_okS_ext {R : SRing} (val val' : gterm -> R) :
  val_eqv val val' -> forall t t', fun_okS val t t' <-> fun_okS val' t t'.
Proof.
  intros H [ x | g | g s | g s s' ] [ x' | g' | g' u | g' u u' ]; simpl; try tauto.
  - rewrite (H s), (H u), (H (tapp1 g s)), (H (tapp1 g' u)); reflexivity.
  - rewrite (H s), (H s'), (H u), (H u'), (H (tapp2 g s s')), (H (tapp2 g' u u')); reflexivity.
Qed.
