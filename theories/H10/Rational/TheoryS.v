(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A (task P2a): the generic semantic lemmas of Theory.v
   (sections 4 and 6) over a setoid ordered field [F : SOF] (SOF.v).

   The syntax (macros, axiom matrices, [Inst D f], the finite tests,
   [tests_FinSat], [test_sound_from_model], [RatModel]) stays in Theory.v
   and is reused. Here: the semantics of the macros and the axioms for a
   valuation [ν : term X -> F] with [ring_homS ν] (the ring symbols are
   interpreted up to [≡]), in [qe F] for F(sqrt2), and the ground
   versions; [Inst_sem_iffS] and [TermModel_InstSemS] for the setoid
   ambient structure of AmbientS.v.

   Names: the Theory.v name with suffix S ([rfvS], [frvS], [frdS], [XvS],
   [YvS], [TvS], [coordOKS], [coord_holds_iffS], [P_holds_iffS],
   [AddSemS], [add_holds_iffS], [add_ADDrelS], [QvCS], [ChainSemS],
   [chain_holds_iffS], [sqrt2_holds_iffS], [root_holds_iffS],
   [lamP_specS], [lamN_specS], [prim_specS], [LOCvS], [LOC_iffS],
   [tInvX_semS], [tZ_semS], [FormalRS], [FORMAL_iffS], [withZ_iffS],
   [BranchSemS], [branch_holds_iffS], [MemSemS], [mem_holds_iffS],
   [RepSemS], [rep_holds_iffS], [inst_*_iffS], [InstSemS],
   [Inst_sem_iffS], [TermModel_InstSemS]).

   Statement changes w.r.t. Theory.v:
   - Z0 ([HZ0 : forall x : F, x * x ≢ 2%:R]) is a hypothesis of the
     whole Section (Theory.v used it only from [qe_unitZ] on), so that
     [qe F] is a field ([Add Field] with [qe_fth F HZ0]) and [frdS z] is
     simply [rfvS z.2 ≢ 0] (instead of "is a unit"). All consumers (the
     ambient structure: [trZ0]) have Z0.
   - points are [ptS F] (flag encoding, AmbientS.v); [TvS b := (ν b,
     (XvS b, YvS b))]: the flag is ν b itself (nonzero = finite);
     equalities of points are [pt_eqv], pairs of coordinates [qp_eqv];
   - [ADDrel (Some _) (Some _) (Some _)] becomes [ADDrelS (1, _) (1, _)
     (1, _)] (equivalently [ADD3S], lemma [ADDrelS_SSS]); [ADDfin_iffS]
     states [ADD3S] directly;
   - [P_holds_iffS]: [pt_eqv (TvS to) (pt_ratS (Pgen D))];
   - [withZ_iffS] has the extra premise [Proper (eqv ==> iff) P];
   - [ellK] is [ellKS] (recursion instead of a big sum),
     [dp_evalR] is [dp_evalS], [fd_L] is [fd_LS] (AmbientS.v).
   PITFALL (as in Theory.v): never let unification compare [fr_nat _] or
   [fr_rat _] with [fr_aE] (it computes with the constants of aE); the
   rewriting tactics below instantiate every lemma explicitly by
   syntactic matching ([frv_rw], [frd_tac]), and [fr_aE] is generalized
   before rewriting ([onE_iffS], [ADDfin_iffS]). *)

From Stdlib Require Import Setoid Morphisms RelationClasses Arith ZArith Lia List.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos.

(* dio_logic is only Required, not Imported: its notations clash with MathComp *)
From Undecidability.H10.Dio
  Require dio_logic.

From Undecidability.H10
  Require Import H10Z.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData Theory.

From Undecidability.H10.Rational
  Require Import SOF SOFTactics SOFqe SOFTheory SignatureS AmbientS.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.
Import SOFTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope sof_scope.

(* sfield, then the nonzero side conditions from the context *)
Ltac sfa := sfield; repeat (assumption || split).

(** * Valuations respecting the ring symbols *)

Definition ring_okXS {X : Type} {R : SRing} (ν : term X -> R) (t : term X) : Prop :=
  match t with
  | tapp0 s_zero => ν t ≡ 0
  | tapp0 s_one => ν t ≡ 1
  | tapp0 (s_int z) => ν t ≡ of_Z z
  | tapp1 s_neg s => ν t ≡ - ν s
  | tapp2 s_add s s' => ν t ≡ ν s + ν s'
  | tapp2 s_mul s s' => ν t ≡ ν s * ν s'
  | _ => True
  end.

Definition ring_homS {X : Type} {R : SRing} (ν : term X -> R) : Prop :=
  forall t, ring_okXS ν t.

Lemma ring_hom_groundS {R : SRing} (val : gterm -> R) :
  (forall t, ring_okS val t) -> ring_homS val.
Proof. by move=> H t; apply: H. Qed.

Lemma ring_hom_substS {X : Type} {R : SRing} (val : gterm -> R) (σ : X -> gterm) :
  (forall t, ring_okS val t) -> ring_homS (fun t => val (tsubst σ t)).
Proof.
  move=> H [ x | g | g t | g s t ].
  - by [].
  - exact: (H (tapp0 g)).
  - exact: (H (tapp1 g (tsubst σ t))).
  - exact: (H (tapp2 g (tsubst σ s) (tsubst σ t))).
Qed.

(** * Integer constants in a setoid ring *)

Section int_consts.

  Variable R : SRing.

  Add Ring ic_ring : (sr_rth R) (setoid (sr_setoid R) (sr_ext R),
    morphism (of_Z_morph R), constants [sof_cst], power_tac (sr_pow_th R) [sof_pow_cst]).

  Lemma of_Z_of_nat (n : nat) : (of_Z (Z.of_nat n) : R) ≡ n%:R.
  Proof.
    elim: n => [ | n IH ]; first reflexivity.
    rewrite Nat2Z.inj_succ -Z.add_1_r (morph_add (of_Z_morph R)) IH natrS; simpl; sring.
  Qed.

  Lemma of_Z_int (i : int) : (of_Z (int_to_Z i) : R) ≡ i%:~R.
  Proof.
    case: i => n; rewrite /int_to_Z; first exact: of_Z_of_nat.
    rewrite (morph_opp (of_Z_morph R)) of_Z_of_nat; reflexivity.
  Qed.

End int_consts.

Section int_mul.

  Variable F : SOF.

  Add Field im_field : (@sof_fth F) (setoid (sr_setoid F) (sr_ext F),
    morphism (of_Z_morph F), constants [sof_cst],
    power_tac (sr_pow_th F) [sof_pow_cst], completeness (sof_Z_complete F)).

  Lemma intrMS (x y : int) : ((x * y)%R%:~R : F) ≡ x%:~R * y%:~R.
  Proof. rewrite -!ratr_int intrM ratrM; reflexivity. Qed.

  Lemma intr_neq0S (x : int) : (x != 0)%R -> (x%:~R : F) ≢ 0.
  Proof. by move=> /eqP Hx /intr_eq0. Qed.

  Lemma qe_intrMS (x y : int) : ((x * y)%R%:~R : qe F) ≡ x%:~R * y%:~R.
  Proof.
    rewrite !qe_intE intrMS; split; rewrite /=; sring.
  Qed.

  Lemma qe_intr_neq0S (x : int) : (x != 0)%R -> (x%:~R : qe F) ≢ 0.
  Proof. by move=> Hx; rewrite qe_intE => [] [ H _ ]; apply: (intr_neq0S Hx). Qed.

  Lemma of_rat_numden (a : rat) : (of_rat a : F) ≡ (numq a)%:~R / (denq a)%:~R.
  Proof. rewrite -{1}(divq_num_den a) ratrM ratrV !ratr_int; reflexivity. Qed.

End int_mul.

(** * Algebra in F(sqrt2), F an SOF without a square root of 2 *)

Section qe_algS.

  Variable F : SOF.
  Hypothesis HZ0 : forall x : F, x * x ≢ 2%:R.

  Add Field qa_field : (@sof_fth F) (setoid (sr_setoid F) (sr_ext F),
    morphism (of_Z_morph F), constants [sof_cst],
    power_tac (sr_pow_th F) [sof_pow_cst], completeness (sof_Z_complete F)).
  Add Field qa_qe_field : (qe_fth F HZ0) (setoid (sr_setoid (qe_SRing F)) (sr_ext (qe_SRing F)),
    morphism (of_Z_morph (qe_SRing F)), constants [sof_cst],
    power_tac (sr_pow_th (qe_SRing F)) [sof_pow_cst], completeness (qe_Z_complete F)).

  Implicit Types (x y u v : qe F) (d : F).

  Lemma qmulf_neq0 x y : x ≢ 0 -> y ≢ 0 -> x * y ≢ 0.
  Proof using HZ0. by move=> Hx Hy /(qe_mulf_eq0 _ HZ0) [ H | H ]; [ apply: Hx | apply: Hy ]. Qed.

  Lemma qexpf_neq0 x n : x ≢ 0 -> x ^+ n ≢ 0.
  Proof using HZ0.
    move=> Hx; elim: n => [ | n IH ] /=; first exact: (qe_neq_1_0 F).
    exact: qmulf_neq0.
  Qed.

  Lemma qinvf_neq0 x : x ≢ 0 -> x^-1 ≢ 0.
  Proof using HZ0.
    move=> Hx H; apply: (qe_neq_1_0 F).
    rewrite -(@qe_inv_l F HZ0 _ Hx) H; sring.
  Qed.

  Lemma qe_of_neq0 d : d ≢ 0 -> qe_of d ≢ 0.
  Proof. by move=> Hd [ H _ ]; apply: Hd. Qed.

  Lemma qe_e_eq0S sg x : qe_e sg x ≡ 0 <-> x ≡ 0.
  Proof.
    case: sg => /=; last reflexivity.
    case: x => a b; rewrite /qe_conj; split=> [] [ H1 H2 ]; split => //=; move: H2 => /=.
    - by rewrite oppr_eq0.
    - by move=> H2; rewrite H2; sring.
  Qed.

  Lemma qe_e_neq0S sg x : x ≢ 0 -> qe_e sg x ≢ 0.
  Proof. by move=> Hx /qe_e_eq0S. Qed.

  Lemma qe_conj_inv x : qe_conj (x^-1) ≡ (qe_conj x)^-1.
  Proof.
    case: x => a b.
    change ((qe_conj (QE a b))^-1) with (qe_inv (qe_conj (QE a b))).
    change ((QE a b)^-1) with (qe_inv (QE a b)).
    rewrite /qe_inv (qe_norm_conj _ (QE a b)); split; rewrite /= /sr_div; sring.
  Qed.

  Lemma qe_e_inv sg x : qe_e sg (x^-1) ≡ (qe_e sg x)^-1.
  Proof. case: sg => /=; [ exact: qe_conj_inv | reflexivity ]. Qed.

  Lemma qe_e_div sg x y : qe_e sg (x / y) ≡ qe_e sg x / qe_e sg y.
  Proof. rewrite /sr_div qe_e_mul qe_e_inv; reflexivity. Qed.

  Lemma qe_e_sub sg x y : qe_e sg (x - y) ≡ qe_e sg x - qe_e sg y.
  Proof. rewrite /sr_sub qe_e_add qe_e_opp; reflexivity. Qed.

  Lemma qe_div_realS x d : x / qe_of d ≡ QE (qre x / d) (qim x / d).
  Proof.
    rewrite /sr_div -qe_of_inv; case: x => a b; split; rewrite /=; sring.
  Qed.

  Lemma divr_eqES u v x y : v ≢ 0 -> y ≢ 0 -> (u / v ≡ x / y <-> u * y ≡ x * v).
  Proof using HZ0.
    move=> Hv Hy; split=> H.
    - transitivity (u / v * (v * y)); first by sfa.
      rewrite H; sfa.
    - transitivity ((u * y) / (v * y)); first by sfa.
      rewrite H; sfa.
  Qed.

  Lemma divr_mul_eqS u v x y : v ≢ 0 -> (u / v * y ≡ x <-> u * y ≡ x * v).
  Proof using HZ0.
    move=> Hv; split=> H.
    - rewrite -H; sfa.
    - transitivity ((u * y) / v); first by sfa.
      rewrite H; sfa.
  Qed.

End qe_algS.

(** * Semantics of terms, R_F and F_R *)

Section sem_macrosS.

  Variables (X : Type) (F : SOF) (ν : term X -> F).
  Hypothesis Hν : ring_homS ν.
  Hypothesis HZ0 : forall x : F, x * x ≢ 2%:R.

  Add Field sm_field : (@sof_fth F) (setoid (sr_setoid F) (sr_ext F),
    morphism (of_Z_morph F), constants [sof_cst],
    power_tac (sr_pow_th F) [sof_pow_cst], completeness (sof_Z_complete F)).
  Add Field sm_qe_field : (qe_fth F HZ0) (setoid (sr_setoid (qe_SRing F)) (sr_ext (qe_SRing F)),
    morphism (of_Z_morph (qe_SRing F)), constants [sof_cst],
    power_tac (sr_pow_th (qe_SRing F)) [sof_pow_cst], completeness (qe_Z_complete F)).

  Implicit Types (s t b : term X) (x y : RF X) (z w : FR X).

  Lemma nu_tzS : ν tz ≡ 0.               Proof using Hν. exact: (Hν tz). Qed.
  Lemma nu_toS : ν to ≡ 1.               Proof using Hν. exact: (Hν to). Qed.
  Lemma nu_tiS i : ν (ti i) ≡ i%:~R.
  Proof using Hν. rewrite -of_Z_int; exact: (Hν (ti i)). Qed.
  Lemma nu_ti_natS n : ν (ti (n%:R)%R) ≡ n%:R.
  Proof using Hν. rewrite nu_tiS natz; reflexivity. Qed.
  Lemma nu_taddS s t : ν (tadd s t) ≡ ν s + ν t.  Proof using Hν. exact: (Hν (tadd s t)). Qed.
  Lemma nu_tmulS s t : ν (tmul s t) ≡ ν s * ν t.  Proof using Hν. exact: (Hν (tmul s t)). Qed.
  Lemma nu_tnegS t : ν (tneg t) ≡ - ν t.          Proof using Hν. exact: (Hν (tneg t)). Qed.
  Lemma nu_tsubS s t : ν (tsub s t) ≡ ν s - ν t.  Proof using Hν. rewrite /tsub nu_taddS nu_tnegS; reflexivity. Qed.

  Ltac nu_simpl := repeat first [ rewrite nu_tsubS | rewrite nu_taddS | rewrite nu_tmulS | rewrite nu_tnegS ].

  Definition rfvS x : qe_SRing F := QE (ν x.1) (ν x.2).
  Definition frvS z : qe_SRing F := rfvS z.1 / rfvS z.2.
  Definition frdS z : Prop := rfvS z.2 ≢ 0.

  Lemma rfvS_add x y : rfvS (rf_add x y) ≡ rfvS x + rfvS y.
  Proof using Hν. rewrite /rfvS /rf_add qe_addE; cbn [fst snd]; rewrite !nu_taddS; reflexivity. Qed.
  Lemma rfvS_mul x y : rfvS (rf_mul x y) ≡ rfvS x * rfvS y.
  Proof using Hν.
    rewrite /rfvS /rf_mul qe_mulE; cbn [fst snd].
    rewrite !nu_taddS !nu_tmulS nu_ti_natS; reflexivity.
  Qed.
  Lemma rfvS_neg x : rfvS (rf_neg x) ≡ - rfvS x.
  Proof using Hν. rewrite /rfvS /rf_neg qe_oppE; cbn [fst snd]; rewrite !nu_tnegS; reflexivity. Qed.
  Lemma rfvS_of t : rfvS (rf_of t) ≡ qe_of (ν t).
  Proof using Hν. rewrite /rfvS /rf_of /qe_of; cbn [fst snd]; rewrite nu_tzS; reflexivity. Qed.
  Lemma rfvS0 : rfvS rf0 ≡ 0.
  Proof using Hν. rewrite /rfvS /rf0; cbn [fst snd]; rewrite nu_tzS; reflexivity. Qed.
  Lemma rfvS1 : rfvS rf1 ≡ 1.
  Proof using Hν. rewrite /rfvS /rf1; cbn [fst snd]; rewrite nu_tzS nu_toS; reflexivity. Qed.
  Lemma rfvS_int i : rfvS (rf_int i) ≡ i%:~R.
  Proof using Hν. rewrite /rf_int rfvS_of nu_tiS qe_intE; reflexivity. Qed.
  Lemma rfvS_pow x n : rfvS (rf_pow x n) ≡ rfvS x ^+ n.
  Proof using Hν.
    elim: n => [ | n IH ]; first exact: rfvS1.
    rewrite /rf_pow iterS -/(rf_pow x n) rfvS_mul IH; reflexivity.
  Qed.
  Lemma rfvS_e sg x : rfvS (rf_e sg x) ≡ qe_e sg (rfvS x).
  Proof using Hν.
    case: sg; rewrite /rfvS /rf_e /=; last reflexivity.
    rewrite nu_tnegS; reflexivity.
  Qed.

  Lemma f_all_iffS (l : list (fml X)) : fml_holdsS ν (f_all l) <-> forall A, List.In A l -> fml_holdsS ν A.
  Proof.
    elim: l => [ | A l IH ] /=; first by split.
    rewrite IH; split.
    - by case=> HA Hl B [ <- | HB ]; auto.
    - by move=> H; split; [ apply: H; left | move=> B HB; apply: H; right ].
  Qed.

  Lemma f_any_iffS (l : list (fml X)) : fml_holdsS ν (f_any l) <-> exists A, List.In A l /\ fml_holdsS ν A.
  Proof.
    elim: l => [ | A l IH ] /=; first by split => // [] [ ? [] ].
    rewrite IH; split.
    - case=> [ HA | [ B [ HB1 HB2 ] ] ]; [ by exists A; auto | by exists B; auto ].
    - by case=> B [ [ <- | HB ] HB2 ]; [ left | right; exists B ].
  Qed.

  Lemma eqRF_iffS x y : fml_holdsS ν (eqRF x y) <-> rfvS x ≡ rfvS y.
  Proof. by []. Qed.

  Lemma neRF_iffS x y : fml_holdsS ν (neRF x y) <-> rfvS x ≢ rfvS y.
  Proof.
    rewrite /neRF /rfvS /=; split.
    - by case=> H [ E1 E2 ]; [ apply: H | apply: H ].
    - move=> H; case: (sof_eq_dec _ (ν x.1) (ν y.1)) => [ E1 | ]; last by left.
      by right => E2; apply: H; split.
  Qed.

  Lemma eqFR_iffS z w : frdS z -> frdS w -> fml_holdsS ν (eqFR z w) <-> frvS z ≡ frvS w.
  Proof using Hν HZ0. by move=> Hz Hw; rewrite eqRF_iffS !rfvS_mul /frvS (divr_eqES HZ0). Qed.

  Lemma neFR_iffS z w : frdS z -> frdS w -> fml_holdsS ν (neFR z w) <-> frvS z ≢ frvS w.
  Proof using Hν HZ0. by move=> Hz Hw; rewrite neRF_iffS !rfvS_mul /frvS (divr_eqES HZ0). Qed.


  (** fractions *)

  Lemma frdS_add z w : frdS z -> frdS w -> frdS (fr_add z w).
  Proof using Hν HZ0. rewrite /frdS /fr_add; cbn [fst snd] => Hz Hw; rewrite rfvS_mul; exact: qmulf_neq0. Qed.
  Lemma frdS_mul z w : frdS z -> frdS w -> frdS (fr_mul z w).
  Proof using Hν HZ0. rewrite /frdS /fr_mul; cbn [fst snd] => Hz Hw; rewrite rfvS_mul; exact: qmulf_neq0. Qed.
  Lemma frdS_neg z : frdS z -> frdS (fr_neg z).
  Proof. by []. Qed.
  Lemma frdS_sub z w : frdS z -> frdS w -> frdS (fr_sub z w).
  Proof using Hν HZ0. by move=> Hz Hw; apply: frdS_add. Qed.
  Lemma frdS_sq z : frdS z -> frdS (fr_sq z).
  Proof using Hν HZ0. by move=> Hz; apply: frdS_mul. Qed.
  Lemma frdS_div z w : frdS z -> rfvS w.1 ≢ 0 -> frdS (fr_div z w).
  Proof using Hν HZ0. rewrite /frdS /fr_div; cbn [fst snd] => Hz Hw; rewrite rfvS_mul; exact: qmulf_neq0. Qed.
  Lemma frdS_of x : frdS (fr_of x).
  Proof using Hν. rewrite /frdS /fr_of; cbn [fst snd]; rewrite rfvS1; exact: qe_neq_1_0. Qed.
  Lemma frdS0 : frdS fr0.
  Proof using Hν. exact: frdS_of. Qed.
  Lemma frdS_nat n : frdS (fr_nat n).
  Proof using Hν. exact: frdS_of. Qed.

  Lemma frvS_add z w : frdS z -> frdS w -> frvS (fr_add z w) ≡ frvS z + frvS w.
  Proof using Hν HZ0.
    rewrite /frdS /frvS /fr_add; cbn [fst snd] => Hz Hw.
    rewrite rfvS_add !rfvS_mul; sfa.
  Qed.
  Lemma frvS_mul z w : frdS z -> frdS w -> frvS (fr_mul z w) ≡ frvS z * frvS w.
  Proof using Hν HZ0.
    rewrite /frdS /frvS /fr_mul; cbn [fst snd] => Hz Hw.
    rewrite !rfvS_mul; sfa.
  Qed.
  Lemma frvS_neg z : frvS (fr_neg z) ≡ - frvS z.
  Proof using Hν HZ0. rewrite /frvS /fr_neg; cbn [fst snd]; rewrite rfvS_neg /sr_div; sring. Qed.
  Lemma frvS_sub z w : frdS z -> frdS w -> frvS (fr_sub z w) ≡ frvS z - frvS w.
  Proof using Hν HZ0.
    move=> Hz Hw; rewrite /fr_sub (@frvS_add z (fr_neg w) Hz (frdS_neg Hw)) frvS_neg; reflexivity.
  Qed.
  Lemma frvS_sq z : frdS z -> frvS (fr_sq z) ≡ frvS z * frvS z.
  Proof using Hν HZ0. move=> Hz; rewrite /fr_sq (@frvS_mul z z Hz Hz); reflexivity. Qed.
  Lemma frvS_div z w : frdS z -> rfvS w.1 ≢ 0 -> frdS w -> frvS (fr_div z w) ≡ frvS z / frvS w.
  Proof using Hν HZ0.
    rewrite /frdS /frvS /fr_div; cbn [fst snd] => Hz Hw1 Hw2.
    rewrite !rfvS_mul; sfa.
  Qed.
  Lemma frvS_of x : frvS (fr_of x) ≡ rfvS x.
  Proof using Hν HZ0. rewrite /frvS /fr_of; cbn [fst snd]; rewrite rfvS1; sfa. Qed.
  Lemma frvS0 : frvS fr0 ≡ 0.
  Proof using Hν HZ0. rewrite /fr0 frvS_of rfvS0; reflexivity. Qed.
  Lemma frvS_nat n : frvS (fr_nat n) ≡ n%:R.
  Proof using Hν HZ0. rewrite /fr_nat frvS_of rfvS_int qe_natE qe_intE; reflexivity. Qed.

  Lemma frdS_rat c : frdS (fr_rat c).
  Proof using Hν.
    rewrite /frdS /fr_rat; cbn [fst snd]; rewrite rfvS_int.
    by apply: qe_intr_neq0S; rewrite GRing.mulf_neq0 // denq_neq0.
  Qed.

  Lemma frvS_rat c : frvS (fr_rat c) ≡ qe_rat c.
  Proof using Hν HZ0.
    have Ha : ((denq (qre c))%:~R : F) ≢ 0 by apply: intr_neq0S; exact: denq_neq0.
    have Hb : ((denq (qim c))%:~R : F) ≢ 0 by apply: intr_neq0S; exact: denq_neq0.
    rewrite /frvS /fr_rat; cbn [fst snd]; rewrite rfvS_int qe_intE -/(qe_of _) qe_div_realS.
    rewrite /qe_rat /rfvS; cbn [fst snd qre qim].
    rewrite !nu_tiS !intrMS !of_rat_numden; split; rewrite /=; sfa.
  Qed.

  Lemma frdS_aE : frdS fr_aE.
  Proof using Hν. exact: frdS_rat. Qed.
  Lemma frvS_aE : frvS fr_aE ≡ aES.
  Proof using Hν HZ0. exact: frvS_rat. Qed.

  Lemma frd_tXS b : ν (tco cx2 b) ≢ 0 -> frdS (tX b).
  Proof using Hν. move=> H; rewrite /frdS /tX; cbn [fst snd]; rewrite rfvS_of; exact: qe_of_neq0. Qed.
  Lemma frd_tYS b : ν (tco cy2 b) ≢ 0 -> frdS (tY b).
  Proof using Hν. move=> H; rewrite /frdS /tY; cbn [fst snd]; rewrite rfvS_of; exact: qe_of_neq0. Qed.

  (* syntactic dispatch (never unify fr_nat/fr_rat with fr_aE) *)
  Ltac frd_step :=
    match goal with
    | |- frdS (fr_add _ _) => apply: frdS_add
    | |- frdS (fr_mul _ _) => apply: frdS_mul
    | |- frdS (fr_neg _) => apply: frdS_neg
    | |- frdS (fr_sub _ _) => apply: frdS_sub
    | |- frdS (fr_sq _) => apply: frdS_sq
    | |- frdS (fr_of _) => apply: frdS_of
    | |- frdS fr0 => exact: frdS0
    | |- frdS (fr_nat _) => apply: frdS_nat
    | |- frdS fr_aE => exact: frdS_aE
    | |- frdS (fr_rat _) => apply: frdS_rat
    | |- frdS (tX _) => apply: frd_tXS
    | |- frdS (tY _) => apply: frd_tYS
    | |- _ => assumption
    end.
  Ltac frd_tac := solve [ repeat frd_step ].

  Ltac frv_step :=
    match goal with
    | |- context [ frvS (fr_add ?z ?w) ] => rewrite (@frvS_add z w ltac:(frd_tac) ltac:(frd_tac))
    | |- context [ frvS (fr_mul ?z ?w) ] => rewrite (@frvS_mul z w ltac:(frd_tac) ltac:(frd_tac))
    | |- context [ frvS (fr_sub ?z ?w) ] => rewrite (@frvS_sub z w ltac:(frd_tac) ltac:(frd_tac))
    | |- context [ frvS (fr_sq ?z) ] => rewrite (@frvS_sq z ltac:(frd_tac))
    | |- context [ frvS (fr_neg ?z) ] => rewrite (@frvS_neg z)
    | |- context [ frvS (fr_nat ?n) ] => rewrite (@frvS_nat n)
    | |- context [ frvS fr0 ] => rewrite frvS0
    end.
  Ltac frv_rw := repeat frv_step.

  Ltac fr_atoms :=
    repeat match goal with
    | |- context [ fml_holdsS ν (eqFR ?z ?w) ] => rewrite (@eqFR_iffS z w ltac:(frd_tac) ltac:(frd_tac))
    | |- context [ fml_holdsS ν (neFR ?z ?w) ] => rewrite (@neFR_iffS z w ltac:(frd_tac) ltac:(frd_tac))
    end.

  (** ** Points *)

  Definition XvS b : qe_SRing F := QE (ν (tco cx0 b)) (ν (tco cx1 b)) / qe_of (ν (tco cx2 b)).
  Definition YvS b : qe_SRing F := QE (ν (tco cy0 b)) (ν (tco cy1 b)) / qe_of (ν (tco cy2 b)).

  (* T_b, with T_0 = O: the flag is ν b *)
  Definition TvS b : ptS F := (ν b, (XvS b, YvS b)).

  (* the meaning of ax_coord at b *)
  Definition coordOKS b : Prop :=
    ν b ≡ 0 \/
    (   ν (tco cx2 b) ≢ 0 /\ ν (tco cy2 b) ≢ 0
     /\ QE (ν (tco cx0 b)) (ν (tco cx1 b)) ≢ 0 /\ QE (ν (tco cy0 b)) (ν (tco cy1 b)) ≢ 0
     /\ on_curveS (XvS b, YvS b)).

  Lemma frv_tXS b : frvS (tX b) ≡ XvS b.
  Proof using Hν. rewrite /frvS /tX; cbn [fst snd]; rewrite rfvS_of; reflexivity. Qed.
  Lemma frv_tYS b : frvS (tY b) ≡ YvS b.
  Proof using Hν. rewrite /frvS /tY; cbn [fst snd]; rewrite rfvS_of; reflexivity. Qed.

  Lemma onE_iffS p : frdS p.1 -> frdS p.2 -> fml_holdsS ν (onE p) <-> on_curveS (frvS p.1, frvS p.2).
  Proof using Hν HZ0.
    case: p => x y Hx Hy; rewrite /onE; cbn [fst snd].
    move: (frdS_aE) (frvS_aE); move: (@fr_aE X) => e He Ee.
    fr_atoms; frv_rw; rewrite Ee /on_curveS; cbn [fst snd].
    have E : frvS x ^+ 3 ≡ frvS x * (frvS x * frvS x) by sring.
    rewrite E; reflexivity.
  Qed.

  Lemma ADDfin_iffS p1 p2 p3 :
    frdS p1.1 -> frdS p1.2 -> frdS p2.1 -> frdS p2.2 -> frdS p3.1 -> frdS p3.2 ->
    fml_holdsS ν (ADDfin p1 p2 p3) <->
    ADD3S (frvS p1.1) (frvS p1.2) (frvS p2.1) (frvS p2.2) (frvS p3.1) (frvS p3.2).
  Proof using Hν HZ0.
    case: p1 p2 p3 => [ x1 y1 ] [ x2 y2 ] [ x3 y3 ]; cbn [fst snd] => H1 H2 H3 H4 H5 H6.
    rewrite /ADDfin; cbv zeta; cbn [fst snd].
    move: (frdS_aE) (frvS_aE); move: (@fr_aE X) => e He Ee.
    cbn [fml_holdsS]; fr_atoms; frv_rw; rewrite Ee /ADD3S !expr2; reflexivity.
  Qed.

  Lemma NEGfin_iffS p1 p2 : frdS p1.1 -> frdS p1.2 -> frdS p2.1 -> frdS p2.2 ->
    fml_holdsS ν (NEGfin p1 p2) <-> frvS p1.1 ≡ frvS p2.1 /\ frvS p2.2 ≡ - frvS p1.2.
  Proof using Hν HZ0.
    case: p1 p2 => [ x1 y1 ] [ x2 y2 ]; cbn [fst snd] => H1 H2 H3 H4.
    rewrite /NEGfin; cbn [fml_holdsS fst snd]; fr_atoms; frv_rw; reflexivity.
  Qed.

  Lemma f_all_map_iffS {T : Type} (g : T -> fml X) (l : list T) :
    fml_holdsS ν (f_all (List.map g l)) <-> forall k, List.In k l -> fml_holdsS ν (g k).
  Proof.
    rewrite f_all_iffS; split => H.
    - by move=> k Hk; apply: H; apply: List.in_map.
    - by move=> A /List.in_map_iff [ k [ <- Hk ] ]; apply: H.
  Qed.

  Lemma f_any_map_iffS {T : Type} (g : T -> fml X) (l : list T) :
    fml_holdsS ν (f_any (List.map g l)) <-> exists k, List.In k l /\ fml_holdsS ν (g k).
  Proof.
    rewrite f_any_iffS; split.
    - by case=> A [ /List.in_map_iff [ k [ <- Hk ] ] HA ]; exists k.
    - by case=> k [ Hk HA ]; exists (g k); split => //; apply: List.in_map.
  Qed.

  (** ** ax_coord *)

  Lemma onE_tPS b : ν (tco cx2 b) ≢ 0 -> ν (tco cy2 b) ≢ 0 ->
    fml_holdsS ν (onE (tP b)) <-> on_curveS (XvS b, YvS b).
  Proof using Hν HZ0.
    move=> Hx Hy; rewrite (@onE_iffS (tP b) (frd_tXS Hx) (frd_tYS Hy)) /tP; cbn [fst snd].
    rewrite frv_tXS frv_tYS; reflexivity.
  Qed.

  Lemma coord_holds_iffS b : fml_holdsS ν (coord_fml b) <-> coordOKS b.
  Proof using Hν HZ0.
    rewrite /coord_fml /coordOKS; cbn [fml_holdsS]; rewrite !nu_tzS !neRF_iffS rfvS0.
    split => [ [ H | [ Hx [ Hy [ Hx' [ Hy' Hc ] ] ] ] ] | [ H | [ Hx [ Hy [ Hx' [ Hy' Hc ] ] ] ] ] ];
      [ by left | right | by left | right ].
    - do 4 (split; first done); by apply/(onE_tPS Hx Hy).
    - do 4 (split; first done); by apply/(onE_tPS Hx Hy).
  Qed.

  Lemma coordOK_nzS b : coordOKS b -> ν b ≢ 0 ->
    ν (tco cx2 b) ≢ 0 /\ ν (tco cy2 b) ≢ 0
    /\ QE (ν (tco cx0 b)) (ν (tco cx1 b)) ≢ 0 /\ QE (ν (tco cy0 b)) (ν (tco cy1 b)) ≢ 0.
  Proof. by case=> [ H Hb | [ ? [ ? [ ? [ ? _ ] ] ] ] _ ]; [ exfalso; apply: Hb | ]. Qed.

  Lemma one_neq0 : (1 : F) ≢ 0.
  Proof. exact: sof_neq_1_0. Qed.

  (** ** ax_P *)

  Variable D : FixedData.

  Lemma P_holds_iffS : coordOKS to -> fml_holdsS ν (P_fml D X) <-> pt_eqv (TvS to) (pt_ratS (Pgen D)).
  Proof using Hν HZ0.
    have H1 : ν to ≢ 0 by rewrite nu_toS; exact: one_neq0.
    move=> /coordOK_nzS /(_ H1) [ Hx [ Hy _ ] ].
    rewrite /P_fml; case: (Pgen D) => [ [ x y ] | ]; cbn [fml_holdsS pt_ratS].
    - fr_atoms; rewrite frv_tXS frv_tYS !frvS_rat; split.
      + move=> [ E1 E2 ]; apply: pt_eqv_S; [ exact: H1 | exact: one_neq0 | split; [ exact E1 | exact E2 ] ].
      + move=> HP; have [ E1 E2 ] := pt_eqv_fin HP H1; split; [ exact E1 | exact E2 ].
    - split => // [] [ I _ ]; apply: H1; apply/I; reflexivity.
  Qed.

  (** ** ax_add *)

  Definition AddSemS a a' : Prop :=
       ν a ≡ 0 \/ ν a' ≡ 0
    \/ (ν a + ν a' ≡ 0 /\ XvS a ≡ XvS a' /\ YvS a' ≡ - YvS a)
    \/ (ν a + ν a' ≢ 0
        /\ ADDrelS (1, (XvS a, YvS a)) (1, (XvS a', YvS a')) (1, (XvS (tadd a a'), YvS (tadd a a')))).

  Lemma add_holds_iffS a a' : coordOKS a -> coordOKS a' -> coordOKS (tadd a a') ->
    fml_holdsS ν (add_fml a a') <-> AddSemS a a'.
  Proof using Hν HZ0.
    rewrite /add_fml /AddSemS; cbn [fml_holdsS]; rewrite !nu_tzS nu_taddS => Ca Ca' Caa.
    case: (sof_eq_dec _ (ν a) 0) => Ha; first by split => _; left.
    case: (sof_eq_dec _ (ν a') 0) => Ha'; first by split => _; right; left.
    move: Ca => /coordOK_nzS /(_ Ha) [ Hx [ Hy _ ] ].
    move: Ca' => /coordOK_nzS /(_ Ha') [ Hx' [ Hy' _ ] ].
    have E1 : fml_holdsS ν (NEGfin (tP a) (tP a')) <-> XvS a ≡ XvS a' /\ YvS a' ≡ - YvS a.
    { rewrite (@NEGfin_iffS (tP a) (tP a') (frd_tXS Hx) (frd_tYS Hy) (frd_tXS Hx') (frd_tYS Hy')) /tP.
      cbn [fst snd]; rewrite !frv_tXS !frv_tYS; reflexivity. }
    have E2 : ν a + ν a' ≢ 0 ->
      fml_holdsS ν (ADDfin (tP a) (tP a') (tP (tadd a a'))) <->
      ADDrelS (1, (XvS a, YvS a)) (1, (XvS a', YvS a')) (1, (XvS (tadd a a'), YvS (tadd a a'))).
    { move=> Hs; have Hs' : ν (tadd a a') ≢ 0 by rewrite nu_taddS.
      move: Caa => /coordOK_nzS /(_ Hs') [ Hx'' [ Hy'' _ ] ].
      rewrite (@ADDrelS_SSS F 1 1 1 _ _ _ _ _ _ one_neq0 one_neq0 one_neq0).
      rewrite (@ADDfin_iffS (tP a) (tP a') (tP (tadd a a')) (frd_tXS Hx) (frd_tYS Hy)
                 (frd_tXS Hx') (frd_tYS Hy') (frd_tXS Hx'') (frd_tYS Hy'')) /tP; cbn [fst snd].
      rewrite !frv_tXS !frv_tYS; reflexivity. }
    split.
    - case=> [ H | [ H | [ [ Hs HN ] | [ Hs HA ] ] ] ]; [ by exfalso; apply: Ha | by exfalso; apply: Ha' | | ];
        right; right; [ left | right ].
      + by split => //; apply/E1.
      + by split => //; apply/(E2 Hs).
    - case=> [ H | [ H | [ [ Hs HN ] | [ Hs HA ] ] ] ]; [ by exfalso; apply: Ha | by exfalso; apply: Ha' | | ];
        right; right; [ left | right ].
      + by split => //; apply/E1.
      + by split => //; apply/(E2 Hs).
  Qed.

  (* T_t only depends on the value of t, given functionality of the
     coordinate functions *)
  Lemma TvS_fun t t' :
    (forall c t t', ν t ≡ ν t' -> ν (tco c t) ≡ ν (tco c t')) ->
    ν t ≡ ν t' -> pt_eqv (TvS t) (TvS t').
  Proof.
    move=> Hf E; apply: pt_eqv_mk; first exact: E.
    by split; rewrite /XvS /YvS /= !(Hf _ t t' E); reflexivity.
  Qed.

  (* with functionality of the coordinate functions, ax_add gives the
     group law T_{a+a'} = T_a + T_{a'} in the form of [ADDrelS] *)
  Lemma add_ADDrelS a a' :
    (forall c t t', ν t ≡ ν t' -> ν (tco c t) ≡ ν (tco c t')) ->
    AddSemS a a' -> ADDrelS (TvS a) (TvS a') (TvS (tadd a a')).
  Proof using Hν HZ0.
    move=> Hf HA.
    have TvE : forall t t', ν t ≡ ν t' -> pt_eqv (TvS t) (TvS t') by move=> t t'; exact: TvS_fun.
    case: (sof_eq_dec _ (ν a) 0) => Ha.
    { left; split; first exact: Ha.
      apply: TvE; rewrite nu_taddS Ha; sring. }
    case: (sof_eq_dec _ (ν a') 0) => Ha'.
    { right; left; split; first exact: Ha.
      split; first exact: Ha'.
      apply: TvE; rewrite nu_taddS Ha'; sring. }
    right; right; split; first exact: Ha.
    split; first exact: Ha'.
    case: HA => [ H | [ H | [ [ Hs [ HX HY ] ] | [ Hs HAd ] ] ] ].
    - by exfalso; apply: Ha.
    - by exfalso; apply: Ha'.
    - left; rewrite /TvS; cbn [fst snd]; split; first exact: HX.
      split; first by rewrite HY opprK; reflexivity.
      rewrite nu_taddS; exact: Hs.
    - have Hs' : ν (tadd a a') ≢ 0 by rewrite nu_taddS.
      move: HAd; case=> [ [ N _ ] | [ [ _ [ N _ ] ] | [ _ [ _ H ] ] ] ];
        [ by exfalso; apply: one_neq0 | by exfalso; apply: one_neq0 | ].
      have E : pt_eqv (1, (XvS (tadd a a'), YvS (tadd a a'))) (TvS (tadd a a')).
      { apply: pt_eqv_S; [ exact: one_neq0 | exact: Hs' | split; reflexivity ]. }
      rewrite -E; exact: H.
  Qed.

  (** ** ax_chain *)

  Definition QvCS t (k : nat) : qe F * qe F :=
    if (k < fd_m D)%N
    then (QE (ν (tch k cx0 t)) (ν (tch k cx1 t)) / qe_of (ν (tch k cx2 t)),
          QE (ν (tch k cy0 t)) (ν (tch k cy1 t)) / qe_of (ν (tch k cy2 t)))
    else (XvS t, YvS t).

  Definition ChainSemS t : Prop :=
    ν t ≡ 0 \/
    (   (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ν (tch k cx2 t) ≢ 0 /\ ν (tch k cy2 t) ≢ 0)
     /\ on_curveS (QvCS t 1)
     /\ (forall k, (1 <= k)%N -> (k < fd_m D)%N ->
           ADDrelS (1, QvCS t k) (1, QvCS t 1%N) (1, QvCS t k.+1))).

  Lemma chain_idx_specS k : List.In k (chain_idx D) <-> (1 <= k)%N /\ (k < fd_m D)%N.
  Proof.
    rewrite /chain_idx In_mem mem_iota; case: (fd_m D) => [ | m ] /=.
    - rewrite addn0; split.
      + by case/andP; case: k.
      + by case=> _; rewrite ltn0.
    - rewrite add1n; split; [ by case/andP | by case=> -> -> ].
  Qed.

  Lemma Qf_semS t k :
    ((k < fd_m D)%N -> ν (tch k cx2 t) ≢ 0 /\ ν (tch k cy2 t) ≢ 0) ->
    (~~ (k < fd_m D)%N -> ν (tco cx2 t) ≢ 0 /\ ν (tco cy2 t) ≢ 0) ->
    frdS (Qf D t k).1 /\ frdS (Qf D t k).2 /\ qp_eqv (frvS (Qf D t k).1, frvS (Qf D t k).2) (QvCS t k).
  Proof using Hν.
    rewrite /Qf /QvCS; case: ifP => Hk H1 H2.
    - have [ Hx Hy ] := H1 isT.
      rewrite /cP /frdS /frvS; cbn [fst snd]; rewrite !rfvS_of.
      split; first exact: qe_of_neq0.
      split; first exact: qe_of_neq0.
      split; reflexivity.
    - have [ Hx Hy ] := H2 isT.
      rewrite /tP; cbn [fst snd].
      split; first exact: frd_tXS.
      split; first exact: frd_tYS.
      split; [ exact: frv_tXS | exact: frv_tYS ].
  Qed.

  Lemma chain_holds_iffS t : coordOKS t -> fml_holdsS ν (chain_fml D t) <-> ChainSemS t.
  Proof using Hν HZ0.
    rewrite /chain_fml /ChainSemS; cbn [fml_holdsS]; rewrite nu_tzS.
    case: (sof_eq_dec _ (ν t) 0) => Ht; first by split => _; left.
    move=> /coordOK_nzS /(_ Ht) [ Hx [ Hy _ ] ].
    have Hcases : forall k, (1 <= k)%N ->
        (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ν (tch k cx2 t) ≢ 0 /\ ν (tch k cy2 t) ≢ 0) ->
        frdS (Qf D t k).1 /\ frdS (Qf D t k).2 /\ qp_eqv (frvS (Qf D t k).1, frvS (Qf D t k).2) (QvCS t k).
    { move=> k Hk1 Hd; apply: Qf_semS => // Hk; exact: Hd. }
    rewrite !f_all_map_iffS.
    have Hden : (forall k, List.In k (chain_idx D) ->
                   fml_holdsS ν (f_and (f_ne (tch k cx2 t) tz) (f_ne (tch k cy2 t) tz))) <->
                (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ν (tch k cx2 t) ≢ 0 /\ ν (tch k cy2 t) ≢ 0).
    { split => H k.
      - move=> Hk1 Hk2; have [ H1 H2 ] := H k (proj2 (chain_idx_specS k) (conj Hk1 Hk2)).
        move: H1 H2; cbn [fml_holdsS]; rewrite nu_tzS; by split.
      - move=> /chain_idx_specS [ Hk1 Hk2 ]; have [ H1 H2 ] := H k Hk1 Hk2.
        by cbn [fml_holdsS]; rewrite nu_tzS; split. }
    split.
    - case=> [ E | [ Hd [ Hon Hadd ] ] ]; first by exfalso; apply: Ht.
      right; have Hd' := proj1 Hden Hd.
      split; first done.
      split.
      + have [ F1 [ F2 E ] ] := Hcases 1%N isT Hd'.
        rewrite -E; exact/(onE_iffS F1 F2).
      + move=> k Hk1 Hk2.
        have [ F1 [ F2 E1 ] ] := Hcases k Hk1 Hd'.
        have [ G1 [ G2 E2 ] ] := Hcases 1%N isT Hd'.
        have [ K1 [ K2 E3 ] ] := Hcases k.+1 isT Hd'.
        rewrite -E1 -E2 -E3 (@ADDrelS_SSS F 1 1 1 _ _ _ _ _ _ one_neq0 one_neq0 one_neq0).
        apply/(ADDfin_iffS F1 F2 G1 G2 K1 K2); apply: Hadd; exact/chain_idx_specS.
    - case=> [ E | [ Hd' [ Hon Hadd ] ] ]; first by exfalso; apply: Ht.
      right; split; first exact/Hden.
      split.
      + have [ F1 [ F2 E ] ] := Hcases 1%N isT Hd'.
        apply/(onE_iffS F1 F2); rewrite E; exact: Hon.
      + move=> k /chain_idx_specS [ Hk1 Hk2 ].
        have [ F1 [ F2 E1 ] ] := Hcases k Hk1 Hd'.
        have [ G1 [ G2 E2 ] ] := Hcases 1%N isT Hd'.
        have [ K1 [ K2 E3 ] ] := Hcases k.+1 isT Hd'.
        apply/(ADDfin_iffS F1 F2 G1 G2 K1 K2); rewrite -(@ADDrelS_SSS F 1 1 1 _ _ _ _ _ _ one_neq0 one_neq0 one_neq0).
        rewrite E1 E2 E3; exact: Hadd.
  Qed.

  (** ** ax_sqrt2 *)

  Lemma sqrt2_holds_iffS a b :
    fml_holdsS ν (sqrt2_fml a b) <-> ν b ≡ 0 \/ ν a * ν a ≢ 2%:R * (ν b * ν b).
  Proof using Hν.
    rewrite /sqrt2_fml; cbn [fml_holdsS]; rewrite !nu_tmulS nu_ti_natS nu_tzS; reflexivity.
  Qed.

  (** ** ax_root *)

  Lemma tm_of_poly_semS n (p : dio_polynomial (pos n) (pos 0)) :
    ν (tm_of_poly X p) ≡ dp_evalS (fun v => ν (tapp0 (s_cst (pos2nat v)))) (fun _ => 0) p.
  Proof using Hν.
    elim: p => [ z | v | i | [] p Hp q Hq ] /=.
    - exact: (Hν (tapp0 (s_int z))).
    - reflexivity.
    - exact: nu_tzS.
    - rewrite nu_taddS Hp Hq; reflexivity.
    - rewrite nu_tmulS Hp Hq; reflexivity.
  Qed.

  Lemma root_holds_iffS (f : H10Z_PROBLEM) :
    fml_holdsS ν (root_fml X f) <->
    dp_evalS (fun v => ν (tapp0 (s_cst (pos2nat v)))) (fun _ => 0) (projT2 f) ≡ 0.
  Proof using Hν. rewrite /root_fml; cbn [fml_holdsS]; rewrite tm_of_poly_semS nu_tzS; reflexivity. Qed.

  (** ** The truncated formal logarithm *)

  Lemma lamP_ES K (N D' N' D'' : RF X) : (lamP K N D').2 = (lamP K N' D'').2.
  Proof. by elim: K => //= K ->. Qed.

  Lemma lamP_E_neq0S K (N D' : RF X) : ((lamP K N D').2 != 0)%R.
  Proof.
    elim: K => [ | K IH ] /=; first by [].
    by rewrite GRing.mulf_neq0 // /ct_den GRing.mulf_neq0 // denq_neq0.
  Qed.

  Lemma ct_num_specS (n : nat) : rfvS (@ct_num X n) ≡ qe_rat (ct n) * (ct_den n)%:~R.
  Proof using Hν HZ0.
    have Hu : ((ct_den n)%:~R : qe F) ≢ 0.
    { by apply: qe_intr_neq0S; rewrite /ct_den GRing.mulf_neq0 // denq_neq0. }
    rewrite -(frvS_rat (ct n)) /frvS.
    change (fr_rat (ct n)).1 with (@ct_num X n).
    change (fr_rat (ct n)).2 with (@rf_int X (ct_den n)).
    rewrite rfvS_int; sfa.
  Qed.

  (* Lam_K(N, D) = E * D^K * l_K(N/D) *)
  Lemma lamP_specS K (N D' : RF X) : rfvS D' ≢ 0 ->
    rfvS (lamP K N D').1 ≡ ((lamP K N D').2)%:~R * rfvS D' ^+ K * ellKS false K (rfvS N / rfvS D').
  Proof using Hν HZ0.
    move=> HD; elim: K => [ | K IH ].
    - change (rfvS (@rf0 X) ≡ (1%R)%:~R * rfvS D' ^+ 0 * 0); rewrite rfvS0; sring.
    - have E1 : lamP K.+1 N D' =
        (rf_add (rf_mul (rf_mul (lamP K N D').1 (@rf_int X (ct_den K.+1))) D')
                (rf_mul (rf_mul (@ct_num X K.+1) (@rf_int X (lamP K N D').2)) (rf_pow N K.+1)),
         ((lamP K N D').2 * ct_den K.+1)%R) by [].
      rewrite E1 ellKS_S; cbn [fst snd].
      rewrite rfvS_add !rfvS_mul rfvS_pow !rfvS_int IH ct_num_specS qe_intrMS.
      change (FixedData.qe_e false (ct K.+1)) with (ct K.+1).
      set Z := rfvS N / rfvS D'.
      have HN : rfvS N ≡ Z * rfvS D' by rewrite /Z; sfa.
      rewrite HN exprMn.
      move: (ellKS false K Z) (qe_rat (ct K.+1) : qe F) ((lamP K N D').2%:~R : qe F)
            ((ct_den K.+1)%:~R : qe F) => l c e d.
      rewrite !exprS; sring.
  Qed.

  Lemma lamN_specS K z : frdS z ->
    rfvS (lamN K z) ≡ ((lamP K z.1 z.2).2)%:~R * rfvS z.2 ^+ K * ellKS false K (frvS z).
  Proof using Hν HZ0. exact: lamP_specS. Qed.

  (* l_K(za)/l_K(zh) - a, cleared *)
  Lemma prim_specS K a za zh : frdS za -> frdS zh -> ellKS false K (frvS zh) ≢ 0 ->
    frdS (prim K a za zh) /\
    frvS (prim K a za zh) ≡ ellKS false K (frvS za) / ellKS false K (frvS zh) - qe_of (ν a).
  Proof using Hν HZ0.
    move=> Ha Hh Hl.
    have HE : (((lamP K za.1 za.2).2)%:~R : qe F) ≢ 0.
    { by apply: qe_intr_neq0S; apply: lamP_E_neq0S. }
    move: HE; set E := (((lamP K za.1 za.2).2)%:~R : qe F) => HE.
    have Hda : rfvS za.2 ^+ K ≢ 0 by apply: qexpf_neq0.
    have Hdh : rfvS zh.2 ^+ K ≢ 0 by apply: qexpf_neq0.
    have Hden : rfvS (prim K a za zh).2 ≡ (E * rfvS zh.2 ^+ K * rfvS za.2 ^+ K) * ellKS false K (frvS zh).
    { rewrite /prim; cbn [fst snd]; rewrite rfvS_mul rfvS_pow (lamN_specS K Hh).
      rewrite (lamP_ES K zh.1 zh.2 za.1 za.2) -/E; sring. }
    have Hnum : rfvS (prim K a za zh).1 ≡
                (E * rfvS zh.2 ^+ K * rfvS za.2 ^+ K) * (ellKS false K (frvS za) - qe_of (ν a) * ellKS false K (frvS zh)).
    { rewrite /prim; cbn [fst snd].
      rewrite rfvS_add rfvS_neg !rfvS_mul !rfvS_pow rfvS_of (lamN_specS K Ha) (lamN_specS K Hh).
      rewrite (lamP_ES K zh.1 zh.2 za.1 za.2) -/E; sring. }
    have Hu : E * rfvS zh.2 ^+ K * rfvS za.2 ^+ K ≢ 0.
    { by apply: qmulf_neq0 => //; apply: qmulf_neq0. }
    clearbody E; split.
    - rewrite /frdS Hden; exact: qmulf_neq0.
    - change (frvS (prim K a za zh)) with (rfvS (prim K a za zh).1 / rfvS (prim K a za zh).2).
      rewrite Hden Hnum; sfa.
  Qed.

  (** ** Localization, formal points, z *)

  (* alpha in r^i (R_F)_p at the branch s: alpha Y = r^i X with
     (Y0 + s B Y1) iota - 1 = r kappa; the witnesses are given by w *)
  Definition LOCvS (i : nat) (r B : F) (s : sgn) (alpha : qe F) (w : wcomp -> F) : Prop :=
       alpha * QE (w wY0) (w wY1) ≡ qe_of r ^+ i * QE (w wX0) (w wX1)
    /\ (w wY0 + (sgnz s)%:~R * B * w wY1) * w wiota - 1 ≡ r * w wkappa.

  #[global] Instance LOCvS_wd i : Proper (eqv ==> eqv ==> eq ==> eqv ==> eq ==> iff) (LOCvS i).
  Proof. move=> r r' Hr B B' HB s _ <- al al' Hal w _ <-; rewrite /LOCvS Hr HB Hal; reflexivity. Qed.

  Lemma LOC_iffS i (r B : term X) (s : sgn) z (W : wcomp -> term X) : frdS z ->
    fml_holdsS ν (LOC i r B s z W) <-> LOCvS i (ν r) (ν B) s (frvS z) (fun c => ν (W c)).
  Proof using Hν HZ0.
    move=> Hz; rewrite /LOC /LOCvS; cbn [fml_holdsS].
    rewrite eqRF_iffS !rfvS_mul rfvS_pow rfvS_of /frvS (@divr_mul_eqS F HZ0 _ _ _ _ Hz).
    nu_simpl; rewrite nu_tiS nu_toS; reflexivity.
  Qed.

  Lemma tInvX_semS sg b : coordOKS b -> ν b ≢ 0 ->
    frdS (tInvX sg b) /\ frvS (tInvX sg b) ≡ (qe_e sg (XvS b))^-1.
  Proof using Hν HZ0.
    move=> /coordOK_nzS H /H [ Hx2 [ Hy2 [ Hx0 Hy0 ] ] ].
    have Hu := @qe_e_neq0S F sg _ Hx0.
    have Hq := qe_of_neq0 Hx2.
    split.
    - rewrite /frdS /tInvX; cbn [fst snd]; rewrite rfvS_e; exact: Hu.
    - rewrite /frvS /tInvX; cbn [fst snd]; rewrite rfvS_of rfvS_e /XvS qe_e_div qe_e_of.
      rewrite /rfvS; cbn [fst snd]; sfa.
  Qed.

  Lemma tZ_semS sg b : coordOKS b -> ν b ≢ 0 ->
    frdS (tZ sg b) /\ rfvS (tZ sg b).1 ≢ 0 /\ frvS (tZ sg b) ≡ zparS sg (TvS b).
  Proof using Hν HZ0.
    move=> Hc Hb; move: (Hc) => /coordOK_nzS /(_ Hb) [ Hx2 [ Hy2 [ Hx0 Hy0 ] ] ].
    have Hux := @qe_e_neq0S F sg _ Hx0.
    have Huy := @qe_e_neq0S F sg _ Hy0.
    have Hx2u := qe_of_neq0 Hx2.
    have Hy2u := qe_of_neq0 Hy2.
    rewrite (@zparS_n F sg (TvS b) Hb) /TvS; cbn [fst snd].
    rewrite /XvS /YvS !qe_e_div !qe_e_of.
    rewrite /tZ /frdS /frvS; cbn [fst snd].
    rewrite !rfvS_neg !rfvS_mul !rfvS_of !rfvS_e /rfvS; cbn [fst snd].
    split; [ | split ].
    - exact: qmulf_neq0.
    - rewrite oppr_eq0; exact: qmulf_neq0.
    - sfa.
  Qed.

  Definition FormalRS (sg : bool) (r B : F) (s : sgn) (p : ptS F) (w : wcomp -> F) : Prop :=
    p.1 ≡ 0 \/ LOCvS 1 r B s (qe_e sg p.2.1)^-1 w.

  Lemma FORMAL_iffS sg b (r B : term X) (s : sgn) (W : wcomp -> term X) : coordOKS b ->
    fml_holdsS ν (FORMAL sg b r B s W) <-> FormalRS sg (ν r) (ν B) s (TvS b) (fun c => ν (W c)).
  Proof using Hν HZ0.
    move=> Hc; rewrite /FORMAL /FormalRS; cbn [fml_holdsS]; rewrite nu_tzS.
    case: (sof_eq_dec _ (ν b) 0) => Hb; first by split => _; left.
    have [ Fd E ] := tInvX_semS sg Hc Hb.
    rewrite (LOC_iffS 1 r B s W Fd) E.
    split => [] [ H | H ]; [ by exfalso | by right | by exfalso | by right ].
  Qed.

  Lemma withZ_iffS sg b (k : FR X -> fml X) (P : qe F -> Prop) : coordOKS b ->
    Proper (eqv ==> iff) P ->
    (forall z, frdS z -> fml_holdsS ν (k z) <-> P (frvS z)) ->
    fml_holdsS ν (withZ sg b k) <-> P (zparS sg (TvS b)).
  Proof using Hν HZ0.
    move=> Hc HP Hk; rewrite /withZ; cbn [fml_holdsS]; rewrite nu_tzS.
    case: (sof_eq_dec _ (ν b) 0) => Hb.
    - have Hk0 := Hk fr0 frdS0; rewrite frvS0 in Hk0.
      rewrite (@zparS_0 F sg (TvS b) Hb).
      split => [ [ [ _ H ] | [ H _ ] ] | H ]; [ exact/Hk0 | by exfalso | left; split => //; exact/Hk0 ].
    - have [ Fz [ _ E ] ] := tZ_semS sg Hc Hb.
      have := Hk _ Fz; rewrite E => HkZ.
      split => [ [ [ E0 _ ] | [ _ H ] ] | H ]; [ by exfalso | exact/HkZ | right; split => //; exact/HkZ ].
  Qed.

  (** ** ax_rep K *)

  Section repS.

    Variables (K : nat) (A a : term X).

    Hypothesis Hc : forall t, coordOKS t.

    (* u_1, u_2, u_3 = A v - u_1 - u_2 and the 13 members *)
    Definition uRS (i : i3) : F :=
      match i with
      | I1 => ν (s1 K r_u1 A)
      | I2 => ν (s1 K r_u2 A)
      | I3 => ν A * ν (s1 K r_v A) - ν (s1 K r_u1 A) - ν (s1 K r_u2 A)
      end.

    Definition memRS (j : mem13) : F :=
      match j with
      | mem_v => ν (s1 K r_v A)
      | mem_L i b => fd_LS D b (uRS i) (ν (s1 K r_v A))
      end.

    Lemma nu_tmemS j : ν (tmem D K A j) ≡ memRS j.
    Proof using Hν.
      case: j => [ | [] b ]; rewrite /tmem /memRS /uRS /tL /tu /fd_LS; try reflexivity.
      all: nu_simpl; rewrite !nu_tiS; reflexivity.
    Qed.

    (* conditions (i) and (ii) of red:theory at the branch s of member j *)
    Definition BranchSemS (j : mem13) (s : sgn) : Prop :=
      let r := ν (s1 K (r_r j) A) in let B := ν (s1 K (r_B j) A) in
      let h := s1 K (r_h j s) A in let j0 := s1 K (r_j0 j s) A in
      let w1 tg (c : wcomp) := ν (s1 K (r_W1 j s tg c) A) in
      let w2 tg (c : wcomp) := ν (s2 K (r_W2 j s tg c) A a) in
      let ha := tmul h a in let h4a := tmul (tsub h (ti 4%R)) a in
         ν h ≢ 0
      /\ ν j0 ≢ 0
      /\ FormalRS false r B s (TvS h) (w1 tg_fh)
      /\ ellKS false K (zparS false (TvS h)) ≢ 0
      /\ FormalRS false r B s (TvS ha) (w2 tg_fha)
      /\ LOCvS K r B s (ellKS false K (zparS false (TvS ha)) / ellKS false K (zparS false (TvS h))
                        - qe_of (ν a)) (w2 tg_prim)
      /\ FormalRS true r B s (TvS j0) (w1 tg_fj0)
      /\ FormalRS true r B s (TvS h4a) (w2 tg_fh4a)
      /\ LOCvS K r B s (zparS true (TvS h4a) / zparS true (TvS j0)) (w2 tg_alt).

    Lemma branch_holds_iffS (j : mem13) (s : sgn) : fml_holdsS ν (branch_fml K A a j s) <-> BranchSemS j s.
    Proof using HZ0 Hν Hc.
      rewrite /branch_fml /BranchSemS; cbv zeta; cbn [fml_holdsS]; rewrite !nu_tzS.
      set r := s1 K (r_r j) A; set B := s1 K (r_B j) A.
      set h := s1 K (r_h j s) A; set j0 := s1 K (r_j0 j s) A.
      case: (sof_eq_dec _ (ν h) 0) => Hh.
      { split => [ [ H1 _ ] | [ H1 _ ] ]; exfalso; exact: H1 Hh. }
      case: (sof_eq_dec _ (ν j0) 0) => Hj.
      { split => [ [ _ [ H1 _ ] ] | [ _ [ H1 _ ] ] ]; exfalso; exact: H1 Hj. }
      have [ FZh [ _ EZh ] ] := tZ_semS false (Hc h) Hh.
      have [ FZj [ UZj EZj ] ] := tZ_semS true (Hc j0) Hj.
      rewrite (FORMAL_iffS _ _ _ _ _ (Hc h)) (FORMAL_iffS _ _ _ _ _ (Hc (tmul h a))).
      rewrite (FORMAL_iffS _ _ _ _ _ (Hc j0)) (FORMAL_iffS _ _ _ _ _ (Hc (tmul (tsub h (ti 4%R)) a))).
      (* the logarithm at h *)
      have El : fml_holdsS ν (neRF (lamN K (tZ false h)) rf0) <-> ellKS false K (zparS false (TvS h)) ≢ 0.
      { rewrite neRF_iffS rfvS0 (lamN_specS K FZh) EZh.
        have Hu : ((lamP K (tZ false h).1 (tZ false h).2).2%:~R * rfvS (tZ false h).2 ^+ K : qe_SRing F) ≢ 0.
        { apply: (qmulf_neq0 HZ0); [ apply: qe_intr_neq0S; exact: lamP_E_neq0S | exact: qexpf_neq0 ]. }
        split => H E; apply: H.
        - rewrite E; sring.
        - case/(qe_mulf_eq0 _ HZ0): E => // E; exfalso; exact: Hu E. }
      (* the primary test *)
      have Ep : ellKS false K (zparS false (TvS h)) ≢ 0 ->
        fml_holdsS ν (withZ false (tmul h a) (fun za => LOC K r B s (prim K a za (tZ false h))
                                                    (fun c => s2 K (r_W2 j s tg_prim c) A a))) <->
        LOCvS K (ν r) (ν B) s (ellKS false K (zparS false (TvS (tmul h a))) / ellKS false K (zparS false (TvS h))
                              - qe_of (ν a)) (fun c => ν (s2 K (r_W2 j s tg_prim c) A a)).
      { move=> Hl.
        apply: (@withZ_iffS false (tmul h a) _
                  (fun q => LOCvS K (ν r) (ν B) s (ellKS false K q / ellKS false K (zparS false (TvS h)) - qe_of (ν a))
                                 (fun c => ν (s2 K (r_W2 j s tg_prim c) A a))) (Hc (tmul h a))).
        - move=> q q' Hq; cbv beta; rewrite Hq; reflexivity.
        - move=> z Hz; cbv beta.
          have Hl' : ellKS false K (frvS (tZ false h)) ≢ 0 by rewrite EZh.
          have [ Fp Epr ] := prim_specS a Hz FZh Hl'.
          rewrite (LOC_iffS _ _ _ _ _ Fp) Epr EZh; reflexivity. }
      (* the alternate test *)
      have Ea : fml_holdsS ν (withZ true (tmul (tsub h (ti 4%R)) a)
                     (fun zb => LOC K r B s (fr_div zb (tZ true j0)) (fun c => s2 K (r_W2 j s tg_alt c) A a))) <->
        LOCvS K (ν r) (ν B) s (zparS true (TvS (tmul (tsub h (ti 4%R)) a)) / zparS true (TvS j0))
             (fun c => ν (s2 K (r_W2 j s tg_alt c) A a)).
      { apply: (@withZ_iffS true (tmul (tsub h (ti 4%R)) a) _
                  (fun q => LOCvS K (ν r) (ν B) s (q / zparS true (TvS j0))
                                 (fun c => ν (s2 K (r_W2 j s tg_alt c) A a))) (Hc (tmul (tsub h (ti 4%R)) a))).
        - move=> q q' Hq; cbv beta; rewrite Hq; reflexivity.
        - move=> z Hz; cbv beta.
          have Hd : frdS (fr_div z (tZ true j0)) by apply: frdS_div.
          rewrite (LOC_iffS _ _ _ _ _ Hd) (frvS_div Hz UZj FZj) EZj; reflexivity. }
      split.
      - case=> _ [ _ [ H1 [ H2 [ H3 [ H4 [ H5 [ H6 H7 ] ] ] ] ] ] ].
        have Hl := proj1 El H2.
        do 2 (split; first done).
        split; first done; split; first done; split; first done.
        split; first exact/(Ep Hl).
        split; first done; split; first done.
        exact/Ea.
      - case=> _ [ _ [ H1 [ H2 [ H3 [ H4 [ H5 [ H6 H7 ] ] ] ] ] ] ].
        do 2 (split; first done).
        split; first done; split; first exact/El; split; first done.
        split; first exact/(Ep H2).
        split; first done; split; first done.
        exact/Ea.
    Qed.

    Definition MemSemS (j : mem13) : Prop :=
      let r := ν (s1 K (r_r j) A) in let B := ν (s1 K (r_B j) A) in
         (exists (eps : int) (k : nat), (eps = 1 \/ eps = -1)%R /\ k \in fd_Kset D
                                        /\ memRS j ≡ eps%:~R * k%:R * r)
      /\ r ≢ 0
      /\ B * B - 2%:R ≡ r * ν (s1 K (r_wB j) A)
      /\ 2%:R * B * ν (s1 K (r_iota' j) A) - 1 ≡ r * ν (s1 K (r_kappa' j) A)
      /\ r * ν a ≢ 1
      /\ (ν a ≡ r * ν (s2 K (r_fz j) A a) \/ ν a * ν (s2 K (r_fy j) A a) - 1 ≡ r * ν (s2 K (r_fz' j) A a))
      /\ (forall s : sgn, BranchSemS j s).

    Lemma eks_specS (ek : int * nat) :
      List.In ek (eks D) <-> exists k, k \in fd_Kset D /\ (ek = (1%R, k) \/ ek = ((-1)%R, k)).
    Proof.
      rewrite /eks List.in_flat_map; split.
      - case=> k [ /In_mem Hk H ]; exists k; split => //.
        by case: H => [ <- | [ <- | [] ] ]; [ left | right ].
      - case=> k [ Hk H ]; exists k; split; first exact/In_mem.
        by case: H => ->; [ left | right; left ].
    Qed.

    Lemma mem_holds_iffS j : fml_holdsS ν (mem_fml D K A a j) <-> MemSemS j.
    Proof using HZ0 Hν Hc.
      rewrite /mem_fml /MemSemS; cbv zeta; cbn [fml_holdsS].
      rewrite f_any_map_iffS f_all_map_iffS.
      nu_simpl; rewrite !nu_tzS !nu_ti_natS nu_toS.
      have Eb : (forall s : sgn, List.In s all_sgn -> fml_holdsS ν (branch_fml K A a j s)) <->
                (forall s : sgn, BranchSemS j s).
      { split => H s; [ apply/branch_holds_iffS/H; exact: all_sgn_spec | move=> _; exact/branch_holds_iffS ]. }
      rewrite Eb.
      have Ee : (exists ek, List.In ek (eks D) /\
                   fml_holdsS ν (f_eq (tmem D K A j) (tmul (ti (ek.1 * (ek.2)%:Z)%R) (s1 K (r_r j) A)))) <->
                (exists (eps : int) (k : nat), (eps = 1 \/ eps = -1)%R /\ k \in fd_Kset D
                       /\ memRS j ≡ eps%:~R * k%:R * ν (s1 K (r_r j) A)).
      { cbn [fml_holdsS]; split.
        - case=> [ [ eps k ] [ /eks_specS [ k' [ Hk' H ] ] ] ]; cbn [fst snd].
          rewrite nu_tmemS nu_tmulS nu_tiS intrMS => E.
          have [ He Hk ] : (eps = 1 \/ eps = -1)%R /\ k = k'.
          { by case: H => [ [ -> -> ] | [ -> -> ] ]; split; auto. }
          exists eps, k; split; first exact: He.
          split; first by rewrite Hk.
          rewrite E; reflexivity.
        - case=> eps [ k [ He [ Hk E ] ] ]; exists (eps, k); split.
          + by apply/eks_specS; exists k; split => //; case: He => ->; [ left | right ].
          + cbn [fst snd]; rewrite nu_tmemS nu_tmulS nu_tiS intrMS E; reflexivity. }
      rewrite Ee; reflexivity.
    Qed.

    Definition RepSemS : Prop := ν (s1 K r_v A) ≢ 0 /\ forall j, MemSemS j.

    Lemma rep_holds_iffS : fml_holdsS ν (rep_fml D K A a) <-> RepSemS.
    Proof using HZ0 Hν Hc.
      rewrite /rep_fml /RepSemS; cbn [fml_holdsS]; rewrite f_all_map_iffS nu_tzS.
      split => [ [ H1 H2 ] | [ H1 H2 ] ]; split => //.
      - by move=> j; apply/mem_holds_iffS/H2; apply: all_mem13_spec.
      - by move=> j _; apply/mem_holds_iffS.
    Qed.

  End repS.

End sem_macrosS.

(** ** Ground instances

    For a valuation [val : gterm -> F] satisfying (a) ([ring_okS]), the
    ground instance of each matrix at the terms A, a ([sub2 A a]) means
    the semantic condition at A, a. *)

Section groundS.

  Variables (F : SOF) (val : gterm -> F) (D : FixedData).
  Hypothesis Hring : forall t, ring_okS val t.
  Hypothesis HZ0 : forall x : F, x * x ≢ 2%:R.

  Lemma coordOK_substS {X} (σ : X -> gterm) :
    (forall t, coordOKS val t) -> forall t, coordOKS (fun u => val (tsubst σ u)) t.
  Proof. by move=> H t; apply: (H (tsubst σ t)). Qed.

  (* constraint (b) gives the functionality hypothesis of [TvS_fun], [add_ADDrelS] *)
  Lemma fun_coordS : (forall t t', fun_okS val t t') ->
    forall c t t', val t ≡ val t' -> val (tco c t) ≡ val (tco c t').
  Proof. by move=> H c t t' E; exact: (H (tco c t) (tco c t') erefl E). Qed.

  Lemma inst_coord_iffS A a : fml_holdsS val (fml_subst (sub2 A a) ax_coord) <-> coordOKS val A.
  Proof using Hring HZ0.
    rewrite fml_holdsS_subst.
    exact: (coord_holds_iffS (@ring_hom_substS _ _ val (sub2 A a) Hring) HZ0 (tvar 0%N)).
  Qed.

  Lemma inst_P_iffS A a : coordOKS val (tapp0 s_one) ->
    fml_holdsS val (fml_subst (sub2 A a) (ax_P D)) <-> pt_eqv (TvS val (tapp0 s_one)) (pt_ratS (Pgen D)).
  Proof using Hring HZ0.
    move=> H; rewrite fml_holdsS_subst.
    exact: (P_holds_iffS (@ring_hom_substS _ _ val (sub2 A a) Hring) HZ0 D H).
  Qed.

  Lemma inst_add_iffS A a : coordOKS val A -> coordOKS val a -> coordOKS val (tadd A a) ->
    fml_holdsS val (fml_subst (sub2 A a) ax_add) <-> AddSemS val A a.
  Proof using Hring HZ0.
    move=> H1 H2 H3; rewrite fml_holdsS_subst.
    exact: (add_holds_iffS (@ring_hom_substS _ _ val (sub2 A a) Hring) HZ0 (a := tvar 0%N) (a' := tvar 1%N) H1 H2 H3).
  Qed.

  Lemma inst_chain_iffS A a : coordOKS val A ->
    fml_holdsS val (fml_subst (sub2 A a) (ax_chain D)) <-> ChainSemS val D A.
  Proof using Hring HZ0.
    move=> H; rewrite fml_holdsS_subst.
    exact: (chain_holds_iffS (@ring_hom_substS _ _ val (sub2 A a) Hring) HZ0 D (t := tvar 0%N) H).
  Qed.

  Lemma inst_sqrt2_iffS A a :
    fml_holdsS val (fml_subst (sub2 A a) ax_sqrt2) <-> val a ≡ 0 \/ val A * val A ≢ 2%:R * (val a * val a).
  Proof using Hring.
    rewrite fml_holdsS_subst.
    exact: (sqrt2_holds_iffS (@ring_hom_substS _ _ val (sub2 A a) Hring) (tvar 0%N) (tvar 1%N)).
  Qed.

  Lemma inst_root_iffS f A a :
    fml_holdsS val (fml_subst (sub2 A a) (ax_root f)) <->
    dp_evalS (fun v => val (tapp0 (s_cst (pos2nat v)))) (fun _ => 0) (projT2 f) ≡ 0.
  Proof using Hring.
    rewrite fml_holdsS_subst.
    exact: (root_holds_iffS (@ring_hom_substS _ _ val (sub2 A a) Hring) f).
  Qed.

  Lemma inst_rep_iffS K A a : (forall t, coordOKS val t) ->
    fml_holdsS val (fml_subst (sub2 A a) (ax_rep D K)) <-> RepSemS val D K A a.
  Proof using Hring HZ0.
    move=> Hc; rewrite fml_holdsS_subst.
    exact: (rep_holds_iffS (@ring_hom_substS _ _ val (sub2 A a) Hring) HZ0 D K (tvar 0%N) (tvar 1%N)
                           (coordOK_substS (sub2 A a) Hc)).
  Qed.

End groundS.

(** * The instances of T in a valuation, semantically (Theory.v, section 6)

    [Inst_sem_iffS]: a valuation of the ground terms (in an SOF with Z0)
    satisfying (a) satisfies all instances of [Inst D f] iff it satisfies
    the semantic conditions [InstSemS]. *)

Section inst_semS.

  Variables (D : FixedData) (f : H10Z_PROBLEM) (F : SOF) (val : gterm -> F).
  Hypothesis Hring : forall t, ring_okS val t.
  Hypothesis HZ0 : forall x : F, x * x ≢ 2%:R.

  Definition InstSemS : Prop :=
       (forall t, coordOKS val t)
    /\ pt_eqv (TvS val (tapp0 s_one)) (pt_ratS (Pgen D))
    /\ (forall A a, AddSemS val A a)
    /\ (forall A, ChainSemS val D A)
    /\ (forall A a, val a ≡ 0 \/ val A * val A ≢ 2%:R * (val a * val a))
    /\ dp_evalS (fun v => val (tapp0 (s_cst (pos2nat v)))) (fun _ => 0) (projT2 f) ≡ 0
    /\ (forall K A a, (1 <= K)%N -> RepSemS val D K A a).

  Theorem Inst_sem_iffS : (forall phi, Inst D f phi -> fml_holdsS val phi) <-> InstSemS.
  Proof using Hring HZ0.
    split.
    - move=> H.
      have Hc : forall t, coordOKS val t.
      { by move=> t; apply/(inst_coord_iffS Hring HZ0 t t)/H/Inst_coord. }
      split; first exact: Hc.
      split; first by apply/(inst_P_iffS D Hring HZ0 (tapp0 s_zero) (tapp0 s_zero) (Hc _))/H/Inst_P.
      split; first by move=> A a; apply/(inst_add_iffS Hring HZ0 (Hc _) (Hc _) (Hc _))/H/Inst_add.
      split; first by move=> A; apply/(inst_chain_iffS D Hring HZ0 A (Hc _))/H/Inst_chain.
      split; first by move=> A a; apply/(inst_sqrt2_iffS Hring)/H/Inst_sqrt2.
      split; first by apply/(inst_root_iffS Hring f (tapp0 s_zero) (tapp0 s_zero))/H/Inst_root.
      by move=> K A a HK; apply/(inst_rep_iffS D Hring HZ0 K A a Hc)/H/Inst_rep.
    - move=> [ Hc [ HP [ Hadd [ Hch [ Hs [ Hr Hrep ] ] ] ] ] ] phi [ M [ A [ a [ HM -> ] ] ] ].
      case: HM => [ HM | [ K [ HK -> ] ] ]; last exact/(inst_rep_iffS D Hring HZ0 K A a Hc)/Hrep.
      case: HM => [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [] ] ] ] ] ] ].
      + exact/(inst_coord_iffS Hring HZ0 A a)/Hc.
      + exact/(inst_P_iffS D Hring HZ0 A a (Hc _)).
      + exact/(inst_add_iffS Hring HZ0 (Hc _) (Hc _) (Hc _))/Hadd.
      + exact/(inst_chain_iffS D Hring HZ0 a (Hc A))/Hch.
      + exact/(inst_sqrt2_iffS Hring)/Hs.
      + exact/(inst_root_iffS Hring f A a).
  Qed.

End inst_semS.

(** the ambient term model (AmbientS.v) satisfies the semantic conditions *)
Corollary TermModel_InstSemS (D : FixedData) (f : H10Z_PROBLEM) (A : AmbientS D)
  (val : gterm -> sQ A) : TermModelS A (Inst D f) val -> InstSemS D f val.
Proof.
  case=> Hring _ Hinst _; exact: (proj1 (@Inst_sem_iffS D f _ val Hring (@trZ0 D A)) Hinst).
Qed.

(** * Compactness, test-specific form (to be PROVED in task P5)

    If all finite rational tests of [f] are satisfiable, there is a setoid
    ambient structure with a term model of the instances [Inst D f].
    Design note: the general form [forall Ax, Ambient.FinSat D Ax -> exists
    A val, TermModelS A Ax val] is deliberately NOT stated: in the
    ultrapower the assignment sequence must be found by search, which is
    only decidable for the (decidable) matrix of the tests, not for an
    arbitrary set Ax (that would need a choice function). *)

Definition CompactnessT (D : FixedData) : Prop :=
  forall f : H10Z_PROBLEM, (forall N, qf_sat (projT2 (test D f N))) ->
    exists (A : AmbientS D) (val : gterm -> sQ A), TermModelS A (Inst D f) val.
