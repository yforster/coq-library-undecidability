(**************************************************************)
(*   Part of the formalization of the preprint                *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026), contributed to the Rocq library of undecidable   *)
(*   problems.                                                *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Generic rat-side helpers of the Section 2 reduction (formerly the
   Phase 1 interface file; the abstract ambient record [Ambient D], its
   term model and the compactness hypothesis were removed in the final
   cleanup, task P20b: their setoid replacements are [AmbientS D],
   [TermModelS] (AmbientS.v) and the PROVED test-specific compactness
   [CompactnessT] (TheoryS.v, CompactnessT.v)).

   What is left, all used by later files:
   - [Z_to_R], [dp_evalR]: Z-coefficient polynomials in any ring
     (Theory.v, StandardModel.v);
   - [vge], [oddZ], [evenZ], [redA], [mnA], [goodA]: valuation, parity,
     reduction and good-prime predicates, here instantiated at ordinary
     rat-valued structures (OrdBridges.v, OrdHeights.v);
   - [ring_ok], [fun_ok]: constraints (a), (b) of the finite tests;
   - [FinSat D Ax]: finite satisfiability of constraints (a) to (d) in
     rat. It is the interface of the paper's compactness argument
     (Lemma red:compactness); Theory.tests_FinSat proves it for the
     instances of the theory. The final theorem does not go through it
     (it uses CompactnessT.v, which searches the tests directly).

   No axioms. *)

From Stdlib Require Import Arith ZArith Lia List.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos.

(* dio_logic is only Required, not Imported: its notations clash with MathComp *)
From Undecidability.H10.Dio
  Require dio_logic.

From Undecidability.H10
  Require Import H10Z.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** * Generic helpers *)

(* the ring morphism Z -> R (as Z_to_rat of RatUtil.v) *)
Definition Z_to_R {R : pzRingType} (z : Z) : R := (Z.to_nat z)%:R - (Z.to_nat (- z))%:R.

Lemma Z_to_R_rat z : Z_to_R z = Z_to_rat z :> rat.
Proof. by []. Qed.

(* evaluation of a Z-coefficient polynomial in a ring *)
Fixpoint dp_evalR {R : pzRingType} {V P : Set} (φ : V -> R) (ν : P -> R)
  (p : dio_polynomial V P) : R :=
  match p with
  | dp_cnst n => Z_to_R n
  | dp_var v => φ v
  | dp_par i => ν i
  | dp_comp dio_logic.do_add p q => dp_evalR φ ν p + dp_evalR φ ν q
  | dp_comp dio_logic.do_mul p q => dp_evalR φ ν p * dp_evalR φ ν q
  end.

(* "v(x) >= k", with v(0) = +oo (DESIGN, Conventions) *)
Definition vge {T : zmodType} {R : numDomainType} (v : T -> R) (x : T) (k : R) : Prop :=
  x = 0 \/ k <= v x.

(* parity in *Z *)
Definition oddZ {R : pzRingType} (isZ : R -> Prop) (x : R) : Prop :=
  exists y, isZ y /\ x = 2%:R * y + 1.
Definition evenZ {R : pzRingType} (isZ : R -> Prop) (x : R) : Prop :=
  exists y, isZ y /\ x = 2%:R * y.

(* reduction to O at a place with valuation vw: O, or vw(x) < 0, on E
   (sg = false) or for the conjugate point on E^sigma (sg = true).
   "Reduction to O" is DEFINED this way (Risk 7). *)
Definition redA {R : realFieldType} (vw : qe R -> R) (sg : bool) (p : pt R) : Prop :=
  match p with
  | None => True
  | Some (x, _) => vw (qe_e sg x) < 0
  end.

(* min{v_q(u), v_q(v)} with v_q(0) = +oo (for v <> 0) *)
Definition mnA {R : realFieldType} (vq : R -> R) (u v : R) : R :=
  if u == 0 then vq v else Num.min (vq u) (vq v).

(* q not in S_K, for an ambient prime q (FixedData.good, transferred) *)
Definition goodA (D : FixedData) {R : realFieldType} (K : nat) (q : R) : Prop :=
  (K.+1)%:R < q /\ forall p : nat, p \in Sfix D -> q != p%:R.

(** * Ground-term valuations and finite satisfiability (DESIGN 4.4)

    The ring R of the paper is the set of values [val t] of ground terms
    (DESIGN D1, term model). Constraints of the finite tests
    (02-reduction.tex, after Prop par:pole-parity):
    (a) the constants 0, 1 (and the integers) and the ring operations have
        their usual values: [ring_ok];
    (b) equal input tuples have equal outputs for each function symbol:
        [fun_ok] (stated for every head; for ring heads it follows from (a));
    (c) every ground instance of every universal axiom holds: [Ax phi ->
        fml_holds val phi], where [Ax] is the set of ground instances;
    (d) the value of every ground term satisfies Phi: [Phi_holdsR]. *)

Definition ring_ok {R : pzRingType} (val : gterm -> R) (t : gterm) : Prop :=
  match t with
  | tapp0 s_zero => val t = 0
  | tapp0 s_one => val t = 1
  | tapp0 (s_int z) => val t = Z_to_R z
  | tapp1 s_neg s => val t = - val s
  | tapp2 s_add s s' => val t = val s + val s'
  | tapp2 s_mul s s' => val t = val s * val s'
  | _ => True
  end.

Definition fun_ok {R : Type} (val : gterm -> R) (t t' : gterm) : Prop :=
  match t, t' with
  | tapp1 g s, tapp1 g' s' => g = g' -> val s = val s' -> val t = val t'
  | tapp2 g s1 s2, tapp2 g' s1' s2' =>
      g = g' -> val s1 = val s1' -> val s2 = val s2' -> val t = val t'
  | _, _ => True
  end.

Section compactness.

  Variable D : FixedData.

  (* every finite set of constraints (a) to (d), for the terms [ts] and the
     instances [fs] of [Ax], has a solution in rat *)
  Definition FinSat (Ax : gfml -> Prop) : Prop :=
    forall (ts : list gterm) (fs : list gfml),
      (forall phi, In phi fs -> Ax phi) ->
      exists rho : gterm -> rat,
           (forall t, In t ts -> ring_ok rho t)
        /\ (forall t t', In t ts -> In t' ts -> fun_ok rho t t')
        /\ (forall phi, In phi fs -> fml_holds rho phi)
        /\ (forall t, In t ts -> Phi_holdsR (fd_PhiL D) (rho t)).

End compactness.
