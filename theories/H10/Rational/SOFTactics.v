(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A: linear (and nonlinear) arithmetic over an arbitrary setoid
   ordered field (see SETOID.md).

   [sof_lra] / [sof_nra] prove goals built from [≡], [≢], [<=], [<],
   [/\], [~], [->] and [False] over the atoms of a [F : SOF], the
   Positivstellensatz certificates being found by the micromega plugin
   ([wlra_Q] / [wnra_Q], which take a reified formula and return a
   witness) and checked by Stdlib's generic [RingMicromega] checker,
   instantiated with the setoid ordered ring of [F] and coefficients in
   Stdlib's [Q] (embedded by [of_Q]). The reification is done here in
   Ltac; numerals are [0], [1] and [of_nat k] for closed k.

   Why not [Lqa]'s [lra] directly: its reification only recognizes [Q]'s
   own operations, and its tautology layer ([Tauto.tauto_checker_sound])
   needs a boolean interpretation of atoms, i.e. decidable equality, which
   an ultrapower does not have. We therefore use the clause-level checker
   [RingMicromega.checker_nf_sound], which only needs [OrderedRing.SOR],
   and do the (simple) propositional preprocessing in Ltac.

   Also: an order-lemma library [SOFTheory] with MathComp names, proved
   with [sof_lra]. *)

From Stdlib Require Import Setoid Morphisms ZArith QArith Lia List Bool.
From Stdlib Require Import Ring Field Ring_theory Field_theory InitialRing.
From Stdlib Require Import OrderedRing RingMicromega QMicromega EnvRing Refl.
From Stdlib.micromega Require Tauto.
Declare ML Module "rocq-runtime.plugins.micromega_core".
Declare ML Module "rocq-runtime.plugins.micromega".

From Undecidability.H10.Rational Require Import SOF.

Local Open Scope list_scope.

(** * The coefficient morphism  Q -> F *)

Definition of_Q {R : SRing} (q : Q) : R :=
  match Qden q with
  | xH => of_Z (Qnum q)
  | d => sr_mul (of_Z (Qnum q)) (sr_inv (of_pos d))
  end.

Section of_Q.

  Variable F : SOF.

  Add Field sof_tac_field : (@sof_fth F) (setoid (sr_setoid F) (sr_ext F),
    morphism (of_Z_morph F), constants [sof_cst],
    power_tac (sr_pow_th F) [sof_pow_cst], completeness (sof_Z_complete F)).

  Local Open Scope sof_scope.

  Local Abbreviation sor := (@sof_sor F).

  Lemma sof_inv_pos (x : F) : 0 < x -> 0 < x^-1.
  Proof.
    intros Hx.
    assert (Nx : x ≢ 0) by (intros E; apply (OrderedRing.Rlt_neq sor _ _ Hx); symmetry; exact E).
    assert (E : x^-1 * x ≡ 1) by (apply sof_inv_l; exact Nx).
    destruct (sof_lt_trichotomy 0 (x^-1)) as [ L | [ L | L ] ]; [ exact L | | ].
    - exfalso; rewrite <- L in E; apply (@sof_neq_1_0 F); rewrite <- E; sring.
    - exfalso; apply (proj1 (OrderedRing.Rlt_nge sor 0 1) (sof_lt01 F)).
      rewrite <- E, sr_mul_comm; apply sof_lt_le_neq, (OrderedRing.Rtimes_pos_neg sor); [ exact Hx | exact L ].
  Qed.

  Lemma of_Q_spec (q : Q) : (of_Q q : F) ≡ of_Z (Qnum q) / of_pos (Qden q).
  Proof.
    destruct q as [ n d ]; unfold of_Q; simpl.
    destruct d; [ reflexivity | reflexivity | ].
    unfold of_pos; simpl; sfield.
  Qed.

  Lemma of_pos_mul (p q : positive) : (of_pos (p * q)%positive : F) ≡ of_pos p * of_pos q.
  Proof. exact (of_Z_mul F (Zpos p) (Zpos q)). Qed.

  Ltac qsimpl := repeat rewrite of_Q_spec; simpl Qnum; simpl Qden; unfold Qplus, Qmult, Qminus, Qopp;
    simpl Qnum; simpl Qden; repeat rewrite ?of_Z_add, ?of_Z_mul, ?of_Z_opp, ?of_pos_mul, ?of_Z_pos.

  Lemma of_Q_morph : ring_morph (@sr_zero F) sr_one sr_add sr_mul sr_sub sr_opp eqv
                       0%Q 1%Q Qplus Qmult Qminus Qopp Qeq_bool of_Q.
  Proof.
    assert (Hp := sof_of_pos_neq0 F).
    constructor.
    - reflexivity.
    - reflexivity.
    - intros [ a b ] [ c d ]; qsimpl; sfield; split; apply Hp.
    - intros [ a b ] [ c d ]; qsimpl; sfield; split; apply Hp.
    - intros [ a b ] [ c d ]; qsimpl; sfield; split; apply Hp.
    - intros [ a b ]; qsimpl; sfield; apply Hp.
    - intros [ a b ] [ c d ] H; apply Qeq_bool_eq in H; unfold Qeq in H; simpl in H.
      qsimpl.
      assert (K : (of_Z (a * Zpos d) : F) ≡ of_Z (c * Zpos b)) by (rewrite H; reflexivity).
      rewrite !of_Z_mul, !of_Z_pos in K.
      transitivity ((of_Z a * of_pos d / (of_pos b * of_pos d) : F)); [ sfield; split; apply Hp | ].
      rewrite K; sfield; split; apply Hp.
  Qed.

  Lemma sof_addon : SORaddon (@sr_zero F) sr_one sr_add sr_mul sr_sub sr_opp eqv sof_le
                      0%Q 1%Q Qplus Qmult Qminus Qopp Qeq_bool Qle_bool of_Q N.to_nat sr_pow.
  Proof.
    assert (Hp := sof_of_pos_neq0 F).
    assert (Hpos := sof_of_pos_pos F).
    constructor.
    - exact of_Q_morph.
    - exact (sr_pow_th F).
    - intros [ a b ] [ c d ] H E; apply Qeq_bool_neq in H; apply H; unfold Qeq; simpl.
      rewrite !of_Q_spec in E; simpl in E.
      apply (of_Z_inj F); rewrite !of_Z_mul, !of_Z_pos.
      transitivity ((of_Z a / of_pos b * (of_pos b * of_pos d) : F)); [ sfield; apply Hp | ].
      rewrite E; sfield; apply Hp.
    - intros [ a b ] [ c d ] H; apply Qle_bool_imp_le in H; unfold Qle in H; simpl in H.
      rewrite !of_Q_spec; simpl.
      apply (of_Z_le F) in H; rewrite !of_Z_mul, !of_Z_pos in H.
      apply (proj2 (OrderedRing.Rle_le_minus sor _ _)).
      assert (E : (of_Z c / of_pos d - of_Z a / of_pos b : F)
                  ≡ (of_Z c * of_pos b - of_Z a * of_pos d) * (of_pos b * of_pos d)^-1)
        by (sfield; split; apply Hp).
      rewrite E; apply (OrderedRing.Rtimes_nonneg_nonneg sor).
      + apply (proj1 (OrderedRing.Rle_le_minus sor _ _)); exact H.
      + apply sof_lt_le_neq, sof_inv_pos, (OrderedRing.Rtimes_pos_pos sor); apply Hpos.
  Qed.

End of_Q.

(** * The checker *)

Definition sof_eval_formula {F : SOF} (env : PolEnv F) (f : Formula Q) : Prop :=
  eval_formula sr_add sr_mul sr_sub sr_opp eqv sof_le sof_lt of_Q N.to_nat sr_pow env f.

(* the cnf that the micromega tautology layer computes for the formula
   [a1 -> ... -> an -> False] (this is [Tauto.xcnf true] on that shape;
   contradictions between two literals are already detected here) *)
Fixpoint sof_cnf (l : list (Formula Q)) : Tauto.cnf (NFormula Q) unit :=
  match l with
  | nil => Tauto.cnf_ff (NFormula Q) unit
  | a :: l' => Tauto.or_cnf_opt qunsat qdeduce (Qnegate unit a tt) (sof_cnf l')
  end.

Definition sof_checker (l : list (Formula Q)) (w : list (Psatz Q)) : bool :=
  Tauto.cnf_checker (fun cl => QWeakChecker (map fst cl)) (sof_cnf l) w.

Lemma make_conj_map {A B} (P : A -> Prop) (Q : B -> Prop) (f : A -> B) l :
  (forall x, P x -> Q (f x)) -> make_conj P l -> make_conj Q (map f l).
Proof.
  intros H; induction l as [ | a l IH ]; simpl map; [ tauto | ].
  rewrite !make_conj_cons; intros [ ? ? ]; split; auto.
Qed.

Section soundness.

  Variable F : SOF.
  Local Abbreviation sor := (@sof_sor F).
  Local Abbreviation addon := (sof_addon F).

  Local Abbreviation evn := (eval_nformula (@sr_zero F) sr_add sr_mul eqv sof_le sof_lt of_Q).

  Lemma sof_no_middle env d : evn env d \/ ~ evn env d.
  Proof. exact (eval_nformula_dec sor of_Q env d). Qed.

  Lemma sof_unsat_prop t : qunsat t = true -> forall env, evn env t -> False.
  Proof.
    destruct t as [ p o ]; intros H env.
    exact (check_inconsistent_sound sor addon p o H env).
  Qed.

  Lemma sof_deduce_prop t t' u : qdeduce t t' = Some u -> forall env, evn env t -> evn env t' -> evn env u.
  Proof. intros H env H1 H2; exact (nformula_plus_nformula_correct sor addon env t t' H1 H2 H). Qed.

  Lemma sof_cnf_correct env l :
    Tauto.eval_cnf evn env (sof_cnf l) -> ~ make_conj (sof_eval_formula env) l.
  Proof.
    induction l as [ | a l IH ]; simpl sof_cnf.
    - intros H; exfalso; exact (proj1 (Tauto.eval_cnf_ff _ _ _) H).
    - intros H; rewrite make_conj_cons.
      apply (Tauto.or_cnf_opt_correct _ _ _ sof_no_middle sof_unsat_prop sof_deduce_prop) in H.
      apply (Tauto.or_cnf_correct _ _ _ sof_no_middle sof_unsat_prop sof_deduce_prop) in H.
      destruct H as [ H | H ].
      + apply (cnf_negate_correct sor addon) in H; tauto.
      + apply IH in H; tauto.
  Qed.

  Lemma sof_checker_sound l w :
    sof_checker l w = true -> forall env : PolEnv F, make_impl (sof_eval_formula env) l False.
  Proof.
    intros H env; apply make_conj_impl; apply sof_cnf_correct.
    revert env; refine (Tauto.cnf_checker_sound evn (fun cl => QWeakChecker (map fst cl)) _ (sof_cnf l) w H).
    intros cl w' Hw env'; apply make_conj_impl; intros Hcl.
    apply (proj2 (make_conj_impl _ _ _) (checker_nf_sound sor addon _ _ Hw env')).
    apply (make_conj_map (Tauto.eval_tt evn env') _ fst cl); [ | exact Hcl ].
    intros x Hx; exact Hx.
  Qed.

End soundness.

(** * Reification and the tactics [sof_lra], [sof_nra] *)

Definition sof_env {R : SRing} (l : list R) : PolEnv R :=
  fun p => nth (Nat.pred (Pos.to_nat p)) l sr_zero.

Section prep.

  Variable F : SOF.
  Local Open Scope sof_scope.
  Local Abbreviation sor := (@sof_sor F).

  Lemma sof_not_lt_le (x y : F) : (y < x -> False) -> x <= y.
  Proof. intros H; apply (proj2 (OrderedRing.Rle_ngt sor _ _)); exact H. Qed.

  Lemma sof_not_le_lt (x y : F) : (y <= x -> False) -> x < y.
  Proof. intros H; apply (proj2 (OrderedRing.Rlt_nge sor _ _)); exact H. Qed.

  Lemma sof_eq_le2 (x y : F) : x <= y -> y <= x -> x ≡ y.
  Proof. apply sof_le_antisym. Qed.

  Lemma sof_neq_cases (x y : F) : x ≢ y -> x < y \/ y < x.
  Proof.
    intros H; destruct (sof_lt_trichotomy x y) as [ L | [ L | L ] ]; [ left; exact L | | right; exact L ].
    exfalso; exact (H L).
  Qed.

  Lemma sof_le_dec (x y : F) : x <= y \/ ~ x <= y.
  Proof.
    destruct (sof_lt_trichotomy y x) as [ L | [ L | L ] ]; [ right | left | left ].
    - intros H; apply (proj1 (OrderedRing.Rlt_nge sor _ _) L); exact H.
    - rewrite L; reflexivity.
    - apply sof_lt_le_neq in L; apply L.
  Qed.

  Lemma sof_lt_dec (x y : F) : x < y \/ ~ x < y.
  Proof.
    destruct (sof_le_dec y x) as [ H | H ]; [ right | left ].
    - intros L; apply (proj1 (OrderedRing.Rlt_nge sor _ _) L); exact H.
    - apply sof_not_le_lt; exact H.
  Qed.

  Lemma sof_nle_lt (x y : F) : ~ x <= y -> y < x.
  Proof. intros H; apply sof_not_le_lt; exact H. Qed.

  Lemma sof_nlt_le (x y : F) : ~ x < y -> y <= x.
  Proof. intros H; apply sof_not_lt_le; exact H. Qed.

End prep.

Ltac sof_add_fv t fv :=
  lazymatch fv with
  | nil => constr:(t :: nil)
  | t :: _ => fv
  | ?y :: ?l => let l' := sof_add_fv t l in constr:(y :: l')
  end.

Ltac sof_index t l :=
  lazymatch l with
  | t :: _ => constr:(O)
  | _ :: ?l' => let n := sof_index t l' in constr:(S n)
  end.

Ltac sof_term_fv t fv :=
  lazymatch t with
  | sr_add ?a ?b => let fv := sof_term_fv a fv in sof_term_fv b fv
  | sr_mul ?a ?b => let fv := sof_term_fv a fv in sof_term_fv b fv
  | sr_sub ?a ?b => let fv := sof_term_fv a fv in sof_term_fv b fv
  | sr_opp ?a => sof_term_fv a fv
  | sr_pow ?a ?n =>
      lazymatch isnatcst n with
      | true => sof_term_fv a fv
      | false => sof_add_fv t fv
      end
  | sr_zero => fv
  | sr_one => fv
  | of_nat ?n =>
      lazymatch isnatcst n with
      | true => fv
      | false => sof_add_fv t fv
      end
  | _ => sof_add_fv t fv
  end.

Ltac sof_term_reify t fv :=
  lazymatch t with
  | sr_add ?a ?b =>
      let x := sof_term_reify a fv in let y := sof_term_reify b fv in constr:(@PEadd Q x y)
  | sr_mul ?a ?b =>
      let x := sof_term_reify a fv in let y := sof_term_reify b fv in constr:(@PEmul Q x y)
  | sr_sub ?a ?b =>
      let x := sof_term_reify a fv in let y := sof_term_reify b fv in constr:(@PEsub Q x y)
  | sr_opp ?a => let x := sof_term_reify a fv in constr:(@PEopp Q x)
  | sr_pow ?a ?n =>
      lazymatch isnatcst n with
      | true =>
          let x := sof_term_reify a fv in
          let k := eval compute in (N.of_nat n) in constr:(@PEpow Q x k)
      | false =>
          let i := sof_index t fv in
          let p := eval compute in (Pos.of_nat (S i)) in constr:(@PEX Q p)
      end
  | sr_zero => constr:(@PEc Q (Qmake Z0 xH))
  | sr_one => constr:(@PEc Q (Qmake (Zpos xH) xH))
  | of_nat ?n =>
      lazymatch isnatcst n with
      | true => let z := eval compute in (Z.of_nat n) in constr:(@PEc Q (Qmake z xH))
      | false =>
          let i := sof_index t fv in
          let p := eval compute in (Pos.of_nat (S i)) in constr:(@PEX Q p)
      end
  | _ =>
      let i := sof_index t fv in
      let p := eval compute in (Pos.of_nat (S i)) in constr:(@PEX Q p)
  end.

Ltac sof_atom_fv P fv :=
  lazymatch P with
  | eqv ?a ?b => let fv := sof_term_fv a fv in sof_term_fv b fv
  | sof_le ?a ?b => let fv := sof_term_fv a fv in sof_term_fv b fv
  | sof_lt ?a ?b => let fv := sof_term_fv a fv in sof_term_fv b fv
  end.

Ltac sof_atom_reify P fv :=
  lazymatch P with
  | eqv ?a ?b =>
      let x := sof_term_reify a fv in let y := sof_term_reify b fv in
      constr:(@Build_Formula Q x OpEq y)
  | sof_le ?a ?b =>
      let x := sof_term_reify a fv in let y := sof_term_reify b fv in
      constr:(@Build_Formula Q x OpLe y)
  | sof_lt ?a ?b =>
      let x := sof_term_reify a fv in let y := sof_term_reify b fv in
      constr:(@Build_Formula Q x OpLt y)
  end.

Ltac sof_goal_fv G fv :=
  lazymatch G with
  | ?P -> ?G' => let fv := sof_atom_fv P fv in sof_goal_fv G' fv
  | False => fv
  end.

Ltac sof_goal_reify G fv :=
  lazymatch G with
  | ?P -> ?G' =>
      let f := sof_atom_reify P fv in let l := sof_goal_reify G' fv in constr:(f :: l)
  | False => constr:(@nil (Formula Q))
  end.

Ltac sof_bf l :=
  lazymatch l with
  | nil => constr:(@Tauto.FF (Formula Q) Tauto.eKind unit unit Tauto.isProp)
  | ?f :: ?l' =>
      let b := sof_bf l' in
      constr:(@Tauto.IMPL (Formula Q) Tauto.eKind unit unit Tauto.isProp
                (@Tauto.A (Formula Q) Tauto.eKind unit unit Tauto.isProp f tt) None b)
  end.

(* propositional preprocessing of the hypotheses over F *)
Ltac sof_prep_hyps F :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : _ \/ _ |- _ => destruct H
  | H : ~ @sof_le F _ _ |- _ => apply sof_nle_lt in H
  | H : ~ @sof_lt F _ _ |- _ => apply sof_nlt_le in H
  | H : ~ @eqv (sof_ring F) _ _ |- _ => apply sof_neq_cases in H; destruct H
  end.

Ltac sof_close_F F wtac :=
  sof_prep_hyps F;
  repeat match goal with
  | H : @sof_le F _ _ |- _ => revert H
  | H : @sof_lt F _ _ |- _ => revert H
  | H : @eqv (sof_ring F) _ _ |- _ => revert H
  end;
  lazymatch goal with
  | |- ?G =>
      let fv := sof_goal_fv G (@nil (car (sof_ring F))) in
      let l := sof_goal_reify G fv in
      let ff := sof_bf l in
      let w := fresh "__wit" in
      wtac w ff;
      exact (@sof_checker_sound F l w ltac:(vm_compute; reflexivity) (sof_env fv))
  end.

Ltac sof_close wtac :=
  lazymatch goal with
  | H : @sof_le ?F _ _ |- _ => sof_close_F F wtac
  | H : @sof_lt ?F _ _ |- _ => sof_close_F F wtac
  | H : @eqv (sof_ring ?F) _ _ |- _ => sof_close_F F wtac
  | H : ~ @eqv (sof_ring ?F) _ _ |- _ => sof_close_F F wtac
  | H : ~ @sof_le ?F _ _ |- _ => sof_close_F F wtac
  | H : ~ @sof_lt ?F _ _ |- _ => sof_close_F F wtac
  end.

Ltac sof_goal_prep :=
  lazymatch goal with
  | |- False => idtac
  | |- ~ _ => intro; sof_goal_prep
  | |- _ /\ _ => split; sof_goal_prep
  | |- @sof_le ?F ?a ?b \/ _ =>
      let H := fresh in
      destruct (sof_le_dec F a b) as [ H | H ]; [ left; exact H | right; sof_goal_prep ]
  | |- @sof_lt ?F ?a ?b \/ _ =>
      let H := fresh in
      destruct (sof_lt_dec F a b) as [ H | H ]; [ left; exact H | right; sof_goal_prep ]
  | |- @eqv (sof_ring ?F) ?a ?b \/ _ =>
      let H := fresh in
      destruct (sof_eq_dec F a b) as [ H | H ]; [ left; exact H | right; sof_goal_prep ]
  | |- @sof_le ?F _ _ => apply (sof_not_lt_le F); intro
  | |- @sof_lt ?F _ _ => apply (sof_not_le_lt F); intro
  | |- @eqv (sof_ring ?F) _ _ =>
      apply (sof_eq_le2 F); apply (sof_not_lt_le F); intro
  | |- _ => exfalso
  end.

Ltac sof_lra_wit w ff := wlra_Q w ff.
Ltac sof_nra_wit w ff := wnra_Q w ff.

(* [sof_lra]: linear arithmetic over a setoid ordered field *)
Ltac sof_lra := intros; sof_goal_prep; sof_close sof_lra_wit.
(* [sof_nra]: with products of hypotheses (Positivstellensatz degree 2) *)
Ltac sof_nra := intros; sof_goal_prep; sof_close sof_nra_wit.

Section tests.

  Variable F : SOF.
  Local Open Scope sof_scope.

  Goal forall x y : F, x <= y -> y <= x + 1 -> 0 <= y - x.
  Proof. sof_lra. Qed.

  Goal forall x y z : F, x < y -> y <= z -> x < z.
  Proof. sof_lra. Qed.

  Goal forall x y : F, 0 <= x -> 0 <= y -> x + y ≡ 0 -> x ≡ 0.
  Proof. sof_lra. Qed.

  Goal forall x : F, 2%:R * x <= 3%:R -> x <= 2%:R.
  Proof. sof_lra. Qed.

  Goal forall x y : F, x ≢ y -> x <= y -> x < y.
  Proof. sof_lra. Qed.

  Goal forall x : F, 0 <= x ^+ 2.
  Proof. sof_nra. Qed.

  Goal forall x y : F, 0 <= x -> 0 <= y -> 0 <= x * y.
  Proof. sof_nra. Qed.

  Goal forall (x y z : F) (n : nat), n = n -> x <= y -> y <= z -> z <= x -> x ≡ z /\ y ≡ x.
  Proof. sof_lra. Qed.

  Goal forall x y : F, 0 < x -> x < y -> ~ (y ≡ x).
  Proof. sof_lra. Qed.

  Goal forall (x : F) a, of_rat a <= x -> x <= of_rat a - 1 -> False.
  Proof. sof_lra. Qed.

  Goal forall (x y : F), `|x| <= y -> 0 <= `|x| -> 0 <= y.
  Proof. sof_lra. Qed.

  Goal forall (x y : F), x ≢ y -> ~ (x <= y) -> y < x.
  Proof. sof_lra. Qed.

  Goal forall (x y : F), 0 <= x -> x <= 1 -> 0 <= y -> y <= 1 -> x * y <= 1.
  Proof. sof_nra. Qed.

  Goal forall (x y : F), x <= y -> 0 <= x -> x * x <= y * y.
  Proof. sof_nra. Qed.

  Goal forall (x1 x2 x3 x4 x5 x6 : F), x1 <= x2 -> x2 <= x3 -> x3 <= x4 -> x4 <= x5 -> x5 <= x6 ->
    x1 + x2 + x3 <= x4 + x5 + x6.
  Proof. sof_lra. Qed.

End tests.
