(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Parallel search with finite tests: the computability skeleton of
   the proof of Theorem 1.1 (Section 2.4, red:finite-tests, and the
   final proof of thm:main in Section 2) and of the oracle reduction
   H10(Z) <=_T H10(Q) in the proof of Corollary 7.1.

   If P is semi-decidable (for P = H10Z: enumeration of integer tuples),
   and the complement of P is witnessed by the failure of one test in a
   computable family of finite tests, each consisting of queries to Q
   (for Q = H10Q), then a decider for Q yields a decider for P:
   - dec_from_tests: each test is a single query (this suffices, since
     PosExistential.v turns a whole finite test into one H10Q instance);
   - dec_from_list_tests: each test is a finite conjunction of queries;
   - dec_from_disj_tests: each test is a finite disjunction of queries
     (the disjunctive normal form used in the paper).
   undecidable_from_*tests transfer undecidability from P to Q.

   Logical assumptions: excluded middle (classic) only, used to show
   that a non-instance of P fails some test; no choice principles.
   Unbounded search uses the choice-free
   Stdlib.Logic.ConstructiveEpsilon.constructive_indefinite_ground_description_nat. *)

From Stdlib Require Import List Bool Classical_Prop ConstructiveEpsilon.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.Undecidability.

Set Implicit Arguments.

(* Post's theorem: semi-decidability of p and of its complement give
   decidability of p, provided p x \/ ~ p x holds pointwise. *)
Lemma dec_from_sdec_compl {X} (p : X -> Prop) :
  (forall x, p x \/ ~ p x) ->
  semi_decidable p -> semi_decidable (complement p) -> decidable p.
Proof.
  intros Hp [f Hf] [g Hg].
  assert (Hex : forall x, exists n, f x n || g x n = true).
  { intros x. destruct (Hp x) as [H | H].
    - apply Hf in H as [n Hn]. exists n. now rewrite Hn.
    - apply Hg in H as [n Hn]. exists n. rewrite Hn. apply orb_true_r. }
  pose (search x := proj1_sig (constructive_indefinite_ground_description_nat
                                 (fun n => f x n || g x n = true)
                                 (fun n => bool_dec _ _) (Hex x))).
  exists (fun x => f x (search x)). intros x. unfold reflects. split.
  - intros H. destruct (f x (search x)) eqn:E; [reflexivity|]. exfalso.
    assert (Hs : f x (search x) || g x (search x) = true).
    { unfold search. now destruct (constructive_indefinite_ground_description_nat _ _ _). }
    rewrite E in Hs. simpl in Hs.
    apply (proj2 (Hg x)); [now exists (search x) | exact H].
  - intros H. apply Hf. now exists (search x).
Qed.

Section finite_tests.

  Variables (X Y : Type) (P : X -> Prop) (Q : Y -> Prop).

  (* query x k : the k-th finite test for instance x, as a single instance of Q *)
  Variable query : X -> nat -> Y.

  Hypothesis tests_sound : forall x, P x -> forall k, Q (query x k).
  Hypothesis tests_complete : forall x, (forall k, Q (query x k)) -> P x.

  Lemma compl_iff_test_fails x : ~ P x <-> exists k, ~ Q (query x k).
  Proof using tests_sound tests_complete.
    split.
    - intros H. apply NNPP. intros H'. apply H, tests_complete.
      intros k. apply NNPP. intros Hk. apply H'. now exists k.
    - intros [k Hk] H. apply Hk. now apply tests_sound.
  Qed.

  (* 1. relative semi-decidability of the complement *)
  Lemma complement_sdec_from_tests : decidable Q -> semi_decidable (complement P).
  Proof using tests_sound tests_complete.
    intros [dQ HdQ]. exists (fun x k => negb (dQ (query x k))). intros x.
    unfold complement. rewrite compl_iff_test_fails. split.
    - intros [k Hk]. exists k. apply negb_true_iff.
      destruct (dQ (query x k)) eqn:E; [|reflexivity].
      exfalso. apply Hk, HdQ, E.
    - intros [k Hk]. exists k. intros H%HdQ. now rewrite H in Hk.
  Qed.

  (* 2. with semi-decidability of P, decidability of P *)
  Lemma dec_from_tests : semi_decidable P -> decidable Q -> decidable P.
  Proof using tests_sound tests_complete.
    intros HP HQ. apply dec_from_sdec_compl.
    - intros x. apply classic.
    - exact HP.
    - now apply complement_sdec_from_tests.
  Qed.

  (* 3. undecidability transfer *)
  Lemma undecidable_from_tests : semi_decidable P -> undecidable P -> undecidable Q.
  Proof using tests_sound tests_complete.
    intros HP HuP HQ. apply HuP. now apply dec_from_tests.
  Qed.

End finite_tests.

(* Tests consisting of finitely many queries, all of which must hold. *)

Lemma decidable_Forall {Y} (Q : Y -> Prop) :
  decidable Q -> decidable (fun l => Forall Q l).
Proof.
  intros [dQ HdQ]. exists (forallb dQ). intros l. unfold reflects.
  rewrite forallb_forall, Forall_forall. split.
  - intros H y Hy. now apply HdQ, H.
  - intros H y Hy. now apply HdQ, H.
Qed.

Section finite_tests_list.

  Variables (X Y : Type) (P : X -> Prop) (Q : Y -> Prop).

  (* query x k : the finitely many queries of the k-th test for instance x *)
  Variable query : X -> nat -> list Y.

  Hypothesis tests_sound : forall x, P x -> forall k, Forall Q (query x k).
  Hypothesis tests_complete : forall x, (forall k, Forall Q (query x k)) -> P x.

  Lemma complement_sdec_from_list_tests : decidable Q -> semi_decidable (complement P).
  Proof using tests_sound tests_complete.
    intros HQ. eapply complement_sdec_from_tests with (Q := fun l => Forall Q l).
    - exact tests_sound.
    - exact tests_complete.
    - now apply decidable_Forall.
  Qed.

  Lemma dec_from_list_tests : semi_decidable P -> decidable Q -> decidable P.
  Proof using tests_sound tests_complete.
    intros HP HQ. eapply dec_from_tests with (Q := fun l => Forall Q l).
    - exact tests_sound.
    - exact tests_complete.
    - exact HP.
    - now apply decidable_Forall.
  Qed.

  Lemma undecidable_from_list_tests : semi_decidable P -> undecidable P -> undecidable Q.
  Proof using tests_sound tests_complete.
    intros HP HuP HQ. apply HuP. now apply dec_from_list_tests.
  Qed.

End finite_tests_list.

(* Tests consisting of finitely many queries, one of which must hold. *)

Lemma decidable_Exists {Y} (Q : Y -> Prop) :
  decidable Q -> decidable (fun l => Exists Q l).
Proof.
  intros [dQ HdQ]. exists (existsb dQ). intros l. unfold reflects.
  rewrite existsb_exists, Exists_exists. split.
  - intros (y & Hy & H). exists y. split; [exact Hy | now apply HdQ].
  - intros (y & Hy & H). exists y. split; [exact Hy | now apply HdQ].
Qed.

Section finite_tests_disj.

  Variables (X Y : Type) (P : X -> Prop) (Q : Y -> Prop).

  (* query x k : the finitely many alternatives of the k-th test for instance x *)
  Variable query : X -> nat -> list Y.

  Hypothesis tests_sound : forall x, P x -> forall k, Exists Q (query x k).
  Hypothesis tests_complete : forall x, (forall k, Exists Q (query x k)) -> P x.

  Lemma complement_sdec_from_disj_tests : decidable Q -> semi_decidable (complement P).
  Proof using tests_sound tests_complete.
    intros HQ. eapply complement_sdec_from_tests with (Q := fun l => Exists Q l).
    - exact tests_sound.
    - exact tests_complete.
    - now apply decidable_Exists.
  Qed.

  Lemma dec_from_disj_tests : semi_decidable P -> decidable Q -> decidable P.
  Proof using tests_sound tests_complete.
    intros HP HQ. eapply dec_from_tests with (Q := fun l => Exists Q l).
    - exact tests_sound.
    - exact tests_complete.
    - exact HP.
    - now apply decidable_Exists.
  Qed.

  Lemma undecidable_from_disj_tests : semi_decidable P -> undecidable P -> undecidable Q.
  Proof using tests_sound tests_complete.
    intros HP HuP HQ. apply HuP. now apply dec_from_disj_tests.
  Qed.

End finite_tests_disj.
