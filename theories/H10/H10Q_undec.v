Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.H10
  Require Import H10Z H10_undec H10Z_undec H10Q.

From Undecidability.H10.Reductions
  Require Import H10Q_to_H10Q_SOS2 H10Q_SOS2_to_H10Q_deg4.

From Undecidability.H10.Rational
  Require Import PosExistential FiniteTests H10Q_enum PaperInputs.

From Undecidability.H10.Rational
  Require TwoConverse PP1Glue.

From Undecidability.H10.Rational
  Require FixedData Theory StandardModel TheoryS CompactnessT ReductionS
          Generator IdxOrd.

(* H10 over Z is undecidable *)
Theorem H10Z_undecidable : undecidable H10Z.
Proof. exact (undecidability_from_reducibility H10_undec H10_H10Z). Qed.

(* the reduction of the paper: H10(Z) is decidable relative to H10(Q) *)
Theorem H10Z_dec_from_H10Q_dec :
  HeightThm -> PrimePattern -> PP1_L0 -> decidable H10Q -> decidable H10Z.
Proof.
  intros HH HP HPP.
  destruct (Generator.inputs_to_data_final HH HP HPP) as [ D [ HWF [ HS [ HO _ ] ] ] ].
  pose proof (CompactnessT.CompactnessT_StdHyps HWF HS HO
                (IdxOrd.idx_ord_spec HWF HS HO)) as HC.
  (* the N-th finite test for f, as a single H10Q instance *)
  set (query f N := qf_to_H10Q (projT2 (Theory.test D f N))).
  apply (dec_from_tests query).
  - intros [ n f ] Hf N; apply qf_to_H10Q_spec.
    exact (StandardModel.tests_sound HWF HS Hf N).
  - intros [ n f ] Hf; apply (ReductionS.tests_complete HWF HC).
    intros N; apply qf_to_H10Q_spec, Hf.
  - exact H10Z_semi_decidable.
Qed.

(* Theorem 1.1 *)
Theorem H10Q_undec : HeightThm -> PrimePattern -> PP1_L0 -> undecidable H10Q.
Proof.
  intros HH HP HPP HQ.
  apply H10Z_undecidable, (H10Z_dec_from_H10Q_dec HH HP HPP), HQ.
Qed.

(* Corollary 7.1 (ii) *)
Theorem H10Q_SOS2_undec : HeightThm -> PrimePattern -> PP1_L0 -> undecidable H10Q_SOS2.
Proof.
  intros HH HP HPP.
  exact (undecidability_from_reducibility (H10Q_undec HH HP HPP) H10Q_H10Q_SOS2).
Qed.

(* Corollary 7.1 (i) *)
Theorem H10Q_deg4_undec : HeightThm -> PrimePattern -> PP1_L0 -> undecidable H10Q_deg4.
Proof.
  intros HH HP HPP.
  exact (undecidability_from_reducibility (H10Q_undec HH HP HPP) H10Q_H10Q_deg4).
Qed.

(** The variants with PP1_L0 derived from the 2-converse *)

Theorem H10Z_dec_from_H10Q_dec' :
  HeightThm -> PrimePattern -> TwoConverse.TwoConverseSel2_El ->
  decidable H10Q -> decidable H10Z.
Proof. intros HH HP H2; exact (H10Z_dec_from_H10Q_dec HH HP (PP1Glue.PP1_L0_of_TwoConverse H2)). Qed.

Theorem H10Q_undec' :
  HeightThm -> PrimePattern -> TwoConverse.TwoConverseSel2_El ->
  undecidable H10Q.
Proof. intros HH HP H2; exact (H10Q_undec HH HP (PP1Glue.PP1_L0_of_TwoConverse H2)). Qed.

Theorem H10Q_SOS2_undec' :
  HeightThm -> PrimePattern -> TwoConverse.TwoConverseSel2_El ->
  undecidable H10Q_SOS2.
Proof. intros HH HP H2; exact (H10Q_SOS2_undec HH HP (PP1Glue.PP1_L0_of_TwoConverse H2)). Qed.

Theorem H10Q_deg4_undec' :
  HeightThm -> PrimePattern -> TwoConverse.TwoConverseSel2_El ->
  undecidable H10Q_deg4.
Proof. intros HH HP H2; exact (H10Q_deg4_undec HH HP (PP1Glue.PP1_L0_of_TwoConverse H2)). Qed.
