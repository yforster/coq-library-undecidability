(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A (task P3c): the completeness direction of the finite tests
   over a setoid ambient structure (port of Reduction.v).

   If all finite tests [test D f N] succeed, then f has an integer zero.

   This file only glues together the S files:
   - [CompactnessT D] (TheoryS.v) gives, from the tests directly, a setoid
     ambient structure [A : AmbientS D] with a term model of [Inst D f]
     (no [FinSat] step);
   - [TermModel_InstSemS] (TheoryS.v) gives the semantic reading
     [InstSemS] of the instances;
   - the hypotheses of LocalComparisonS.v are discharged by
     [TermModelS_LC_hyps]; the eta interface and [local_comparison] are
     instantiated as Section hypotheses of HeightContradictionS.v;
   - [root] is the root component of [InstSemS]; [rep] (the record
     [CoarseningS.RepSemS]) is built from the [RepSemS] component of
     [InstSemS]: the Skolem terms of ax_rep K form the witness record
     [RepTerms]; the signs and multipliers eps_j, k_j are collected by
     finite choice over the 13 members ([mem13_choice], no axiom).

   Main result: [tests_complete]. Logical assumptions: excluded middle
   (classic) only, through CoarseningS.v and HeightContradictionS.v. *)

From Stdlib Require Import Setoid Morphisms RelationClasses Arith ZArith Lia List.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos.

From Undecidability.H10.Dio
  Require dio_logic.

From Undecidability.H10
  Require Import H10Z.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData Theory.

From Undecidability.H10.Rational
  Require Import SOF SOFTactics SOFqe SOFTheory SignatureS AmbientS TheoryS.

(* qualified only: [T], [Xc], [Yc], [tmul], ... exist in several files *)
From Undecidability.H10.Rational
  Require LocalComparisonS CoarseningS HeightContradictionS.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.
Import SOFTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope sof_scope.

(** * Finite choice over the 13 members of the contact list (no axiom) *)

Lemma mem13_choice {B : Type} (b0 : B) (P : mem13 -> B -> Prop) :
  (forall j, exists b, P j b) -> exists g : mem13 -> B, forall j, P j (g j).
Proof.
  move=> H.
  have Hl : forall l : list mem13, exists g : mem13 -> B, forall j, List.In j l -> P j (g j).
  { elim=> [ | j0 l [ g Hg ] ]; first by exists (fun _ => b0).
    have [ b Hb ] := H j0.
    exists (fun j => if mem13_eq_dec j j0 then b else g j) => j /= Hj.
    case: (mem13_eq_dec j j0) => [ E | ne ]; first by subst.
    case: Hj => [ E | Hj ]; [ by case: ne | exact: Hg ]. }
  have [ g Hg ] := Hl all_mem13.
  by exists g => j; apply: Hg; apply: all_mem13_spec.
Qed.

(** * Localization witnesses: TheoryS.v (values) to CoarseningS.v (terms) *)

Section bridge.

  Variables (D : FixedData) (A : AmbientS D) (val : gterm -> sQ A).

  Lemma LOCvS_LocAS i r B s alpha (W : wcomp -> gterm) :
    LOCvS i r B s alpha (fun c => val (W c)) -> CoarseningS.LocAS val i r B s alpha.
  Proof.
    move=> [ E1 E2 ].
    by exists (W wX0), (W wX1), (W wY0), (W wY1), (W wiota), (W wkappa).
  Qed.

  Lemma FormalRS_FormalAS sg r B s p (W : wcomp -> gterm) :
    FormalRS sg r B s p (fun c => val (W c)) -> CoarseningS.FormalAS val sg r B s p.
  Proof. case=> [ H | H ]; [ by left | right; exact: LOCvS_LocAS H ]. Qed.

End bridge.

(** * The glue in a term model of [Inst D f] *)

Section glue.

  Variables (D : FixedData) (HWF : FixedWF D).
  Variables (n : nat) (f : dio_polynomial (pos n) (pos 0)).
  Variables (A : AmbientS D) (val : gterm -> sQ A).
  Hypothesis HTM : TermModelS A (Inst D (existT _ n f)) val.

  Lemma gl_sem : InstSemS D (existT _ n f) val.
  Proof using HTM. exact: TermModel_InstSemS HTM. Qed.

  (* rep, from ax_rep K at the argument tA (for all a) *)
  Lemma gl_rep : forall (K : nat) (tA : gterm), (1 <= K)%N ->
    exists W, CoarseningS.RepSemS val K tA W.
  Proof using HTM.
    move=> K tA HK; have [ _ [ _ [ _ [ _ [ _ [ _ Hrep ] ] ] ] ] ] := gl_sem.
    have HR a := Hrep K tA a HK.
    have [ Hv0 Hm0 ] := HR tA.
    pose r j := tapp1 (s_rep1 K (r_r j)) tA.
    have Hex : forall j, exists ek : int * nat,
        (ek.1 = 1%R \/ ek.1 = (-1)%R) /\ ek.2 \in fd_Kset D
        /\ memRS val D K tA j ≡ ek.1%:~R * ek.2%:R * val (r j).
    { by move=> j; have [ [ eps [ k H ] ] _ ] := Hm0 j; exists (eps, k). }
    have [ g Hg ] := mem13_choice (0%R, 0%N) Hex.
    pose W := {| CoarseningS.rp_u1 := tapp1 (s_rep1 K r_u1) tA;
                 CoarseningS.rp_u2 := tapp1 (s_rep1 K r_u2) tA;
                 CoarseningS.rp_v := tapp1 (s_rep1 K r_v) tA;
                 CoarseningS.rp_eps := fun j => (g j).1;
                 CoarseningS.rp_k := fun j => (g j).2;
                 CoarseningS.rp_r := r;
                 CoarseningS.rp_B := fun j => tapp1 (s_rep1 K (r_B j)) tA;
                 CoarseningS.rp_wB := fun j => tapp1 (s_rep1 K (r_wB j)) tA;
                 CoarseningS.rp_h := fun j s => tapp1 (s_rep1 K (r_h j s)) tA;
                 CoarseningS.rp_j0 := fun j s => tapp1 (s_rep1 K (r_j0 j s)) tA |}.
    exists W; constructor.
    - exact: Hv0.
    - by move=> j; have [ _ [ _ E ] ] := Hg j; exact: E.
    - by move=> j; have [ He _ ] := Hg j.
    - by move=> j; have [ _ [ Hk _ ] ] := Hg j.
    - by move=> j; have [ _ [ Hr _ ] ] := Hm0 j.
    - move=> j; have [ _ [ _ [ HB _ ] ] ] := Hm0 j.
      cbn [CoarseningS.rp_B CoarseningS.rp_r CoarseningS.rp_wB].
      rewrite expr2; exact: HB.
    - move=> j s; have [ _ [ _ [ _ [ _ [ _ [ _ Hb ] ] ] ] ] ] := Hm0 j.
      by have [ Hh _ ] := Hb s.
    - move=> j s; have [ _ [ _ [ _ [ _ [ _ [ _ Hb ] ] ] ] ] ] := Hm0 j.
      by have [ _ [ Hj _ ] ] := Hb s.
    - move=> j s a; have [ _ Hm ] := HR a.
      have [ _ [ _ [ _ [ _ [ _ [ _ Hb ] ] ] ] ] ] := Hm j.
      have [ _ [ _ [ F1 [ E2 [ F3 [ L4 [ F5 [ F6 L7 ] ] ] ] ] ] ] ] := Hb s.
      split; first exact: FormalRS_FormalAS F1.
      split; first exact: FormalRS_FormalAS F3.
      split; first exact: E2.
      split; first exact: LOCvS_LocAS L4.
      split; first exact: FormalRS_FormalAS F5.
      split; first exact: FormalRS_FormalAS F6.
      exact: LOCvS_LocAS L7.
  Qed.

  (** Prop red:finite-test-success for the term model *)

  Theorem finite_test_success_inst : H10Z (existT _ n f).
  Proof using HWF HTM.
    have [ Hring [ Hfun [ Hch [ Hadd HP ] ] ] ] := LocalComparisonS.TermModelS_LC_hyps HTM.
    have [ _ [ _ [ _ [ _ [ _ [ Hroot _ ] ] ] ] ] ] := TermModel_InstSemS HTM.
    exact: (@HeightContradictionS.finite_test_success D HWF A _ val HTM
      (LocalComparisonS.eta val) (LocalComparisonS.eta_isZ Hch) (LocalComparisonS.eta_spec Hch)
      (LocalComparisonS.eta_add Hring Hfun Hch Hadd) (LocalComparisonS.eta_one Hch HP)
      (LocalComparisonS.eta_val Hfun) (LocalComparisonS.local_comparison Hring Hfun Hch Hadd HP)
      n f Hroot gl_rep).
  Qed.

End glue.

(** * Completeness of the finite tests *)

(* if every finite test for f succeeds, then f has an integer zero *)
Theorem tests_complete (D : FixedData) (HWF : FixedWF D) (HC : CompactnessT D)
  n (f : dio_polynomial (pos n) (pos 0)) :
  (forall N, qf_sat (projT2 (test D (existT _ n f) N))) -> H10Z (existT _ n f).
Proof.
  move=> Ht; have [ A [ val HTM ] ] := HC _ Ht.
  exact: (@finite_test_success_inst D HWF n f A val HTM).
Qed.
