(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Finite tests (Section 2.4 of the paper, red:finite-tests, the
   paragraph "Every finite initial part of this list is decidable"):
   an existential Boolean combination of polynomial equations p = 0
   and inequations p <> 0 with rational coefficients is satisfiable
   over Q iff a single, computable, instance of H10Q has a solution
   (qf_to_H10Q_spec, qf_SAT_H10Q, qf_SAT_dec).

   - inequations p <> 0 become p * y - 1 = 0 for a fresh variable y
   - disjunctions p = 0 \/ q = 0 become p * q = 0
   - conjunctions p = 0 /\ q = 0 become p^2 + q^2 = 0
   - denominators are cleared by multiplying with their product.
   The paper instead passes to disjunctive normal form and asks
   finitely many queries; the product encoding of disjunctions gives
   a single query (see also FiniteTests.dec_from_disj_tests).

   No axioms are used. *)

From Stdlib Require Import ZArith Lia List.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos.

From Undecidability.H10
  Require Import H10Z H10Q.

From Undecidability.H10.Rational
  Require Import RatUtil.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** * From MathComp's int to Stdlib's Z *)

Definition int_to_Z (i : int) : Z :=
  match i with
  | Posz n => Z.of_nat n
  | Negz n => (- Z.of_nat (S n))%ZZ
  end.

Lemma Z_to_rat_int (i : int) : Z_to_rat (int_to_Z i) = i%:~R.
Proof.
  destruct i as [ n | n ]; rewrite /int_to_Z.
  - by rewrite Z_to_rat_of_nat -pmulrn.
  - by rewrite Z_to_rat_opp Z_to_rat_of_nat NegzE mulrNz -pmulrn.
Qed.

Lemma int_to_Z_pos (i : int) : 0 < i -> (0 < int_to_Z i)%ZZ.
Proof.
  destruct i as [ n | n ]; simpl; [ | done ].
  rewrite ltz_nat => /ssrnat.ltP; lia.
Qed.

(** * Polynomials with rational coefficients *)

Inductive qpoly (V : Set) : Set :=
  | qp_cnst : rat -> qpoly V
  | qp_var : V -> qpoly V
  | qp_add : qpoly V -> qpoly V -> qpoly V
  | qp_mul : qpoly V -> qpoly V -> qpoly V.

Arguments qp_cnst {V}.

Section qpoly.

  Variable V : Set.

  Implicit Type φ : V -> rat.

  Fixpoint qp_eval φ (p : qpoly V) : rat :=
    match p with
    | qp_cnst c => c
    | qp_var v => φ v
    | qp_add p q => qp_eval φ p + qp_eval φ q
    | qp_mul p q => qp_eval φ p * qp_eval φ q
    end.

  Fixpoint qp_vars (p : qpoly V) : list V :=
    match p with
    | qp_cnst _ => nil
    | qp_var v => v :: nil
    | qp_add p q => List.app (qp_vars p) (qp_vars q)
    | qp_mul p q => List.app (qp_vars p) (qp_vars q)
    end.

  (* evaluation only depends on the variables occurring in p *)
  Lemma qp_eval_ext φ φ' p :
    (forall v, In v (qp_vars p) -> φ v = φ' v) -> qp_eval φ p = qp_eval φ' p.
  Proof.
    induction p as [ c | v | p Hp q Hq | p Hp q Hq ]; simpl; intros H.
    - done.
    - apply H; simpl; auto.
    1,2: f_equal; [ apply Hp | apply Hq ]; intros; apply H, in_or_app; auto.
  Qed.

  Lemma qp_eval_ext' φ φ' p : (forall v, φ v = φ' v) -> qp_eval φ p = qp_eval φ' p.
  Proof. intros H; apply qp_eval_ext; auto. Qed.

  Definition qp_sqr (p : qpoly V) := qp_mul p p.

  Fact qp_eval_sqr φ p : qp_eval φ (qp_sqr p) = (qp_eval φ p) ^+ 2.
  Proof. by rewrite /qp_sqr /= expr2. Qed.

  (** Clearing denominators: (p', d) := qp_clear p satisfies d * p = p'
      where p' has integer coefficients and d > 0 *)

  Fixpoint qp_clear (p : qpoly V) : dio_polynomial V (pos 0) * Z :=
    match p with
    | qp_cnst c => (dp_cnst (int_to_Z (numq c)), int_to_Z (denq c))
    | qp_var v => (dp_var v, 1%ZZ)
    | qp_add p q =>
        let cp := qp_clear p in
        let cq := qp_clear q in
        (dp_add (dp_mul (dp_cnst (snd cq)) (fst cp)) (dp_mul (dp_cnst (snd cp)) (fst cq)),
         (snd cp * snd cq)%ZZ)
    | qp_mul p q =>
        let cp := qp_clear p in
        let cq := qp_clear q in
        (dp_mul (fst cp) (fst cq), (snd cp * snd cq)%ZZ)
    end.

  Lemma qp_clear_pos p : (0 < snd (qp_clear p))%ZZ.
  Proof.
    induction p; simpl; try lia.
    apply int_to_Z_pos, denq_gt0.
  Qed.

  Lemma qp_clear_neq0 p : Z_to_rat (snd (qp_clear p)) <> 0.
  Proof.
    intros H; rewrite -Z_to_rat_0 in H.
    apply Z_to_rat_inj in H.
    generalize (qp_clear_pos p); lia.
  Qed.

  Lemma qp_clear_spec φ (ν : pos 0 -> rat) p :
    Z_to_rat (snd (qp_clear p)) * qp_eval φ p = dp_eval_rat φ ν (fst (qp_clear p)).
  Proof.
    induction p as [ c | v | p Hp q Hq | p Hp q Hq ]; simpl.
    - by rewrite !Z_to_rat_int numqE mulrC.
    - by rewrite Z_to_rat_1 mul1r.
    - rewrite -Hp -Hq Z_to_rat_mul.
      set (a := Z_to_rat (snd (qp_clear p))); set (b := Z_to_rat (snd (qp_clear q))).
      by rewrite mulrDr !mulrA [b * a]mulrC.
    - rewrite -Hp -Hq Z_to_rat_mul.
      by rewrite mulrACA.
  Qed.

  Corollary qp_clear_eq0 φ ν p :
    qp_eval φ p = 0 <-> dp_eval_rat φ ν (fst (qp_clear p)) = 0.
  Proof.
    rewrite -qp_clear_spec; split.
    - by move=> ->; rewrite mulr0.
    - move=> /rat_mul_eq0 [ H | H ]; auto.
      by destruct (qp_clear_neq0 H).
  Qed.

End qpoly.

Arguments qp_eval {V}.
Arguments qp_sqr {V} : simpl never.

Section qp_map.

  Variables V W : Set.

  Fixpoint qp_map (f : V -> W) (p : qpoly V) : qpoly W :=
    match p with
    | qp_cnst c => qp_cnst c
    | qp_var v => qp_var (f v)
    | qp_add p q => qp_add (qp_map f p) (qp_map f q)
    | qp_mul p q => qp_mul (qp_map f p) (qp_map f q)
    end.

  (* substitution of variables by variables *)
  Lemma qp_eval_map φ f p : qp_eval φ (qp_map f p) = qp_eval (fun v => φ (f v)) p.
  Proof. induction p; simpl; congruence. Qed.

End qp_map.

(** * Quantifier-free Boolean combinations of (in)equations *)

Inductive qform (V : Set) : Set :=
  | qf_eq0 : qpoly V -> qform V      (* p = 0 *)
  | qf_neq0 : qpoly V -> qform V     (* p <> 0 *)
  | qf_and : qform V -> qform V -> qform V
  | qf_or : qform V -> qform V -> qform V.

Fixpoint qf_holds {V : Set} (φ : V -> rat) (A : qform V) : Prop :=
  match A with
  | qf_eq0 p => qp_eval φ p = 0
  | qf_neq0 p => qp_eval φ p <> 0
  | qf_and A B => qf_holds φ A /\ qf_holds φ B
  | qf_or A B => qf_holds φ A \/ qf_holds φ B
  end.

Definition qf_sat {n} (A : qform (pos n)) : Prop := exists φ : pos n -> rat, qf_holds φ A.

Definition qf_true {V : Set} : qform V := qf_eq0 (qp_cnst 0).
Definition qf_false {V : Set} : qform V := qf_neq0 (qp_cnst 0).

Fact qf_holds_true (V : Set) (φ : V -> rat) : qf_holds φ qf_true.
Proof. done. Qed.

Fact qf_holds_false (V : Set) (φ : V -> rat) : ~ qf_holds φ qf_false.
Proof. by simpl. Qed.

Section qf_vars.

  Variable V : Set.

  Fixpoint qf_vars (A : qform V) : list V :=
    match A with
    | qf_eq0 p => qp_vars p
    | qf_neq0 p => qp_vars p
    | qf_and A B => List.app (qf_vars A) (qf_vars B)
    | qf_or A B => List.app (qf_vars A) (qf_vars B)
    end.

  (* the truth of A only depends on the variables occurring in A *)
  Lemma qf_holds_ext (φ φ' : V -> rat) A :
    (forall v, In v (qf_vars A) -> φ v = φ' v) -> qf_holds φ A <-> qf_holds φ' A.
  Proof.
    induction A as [ p | p | A HA B HB | A HA B HB ]; simpl; intros H.
    1,2: rewrite (qp_eval_ext H); tauto.
    all: assert (HA' := HA (fun v Hv => H v (in_or_app _ _ _ (or_introl Hv))));
         assert (HB' := HB (fun v Hv => H v (in_or_app _ _ _ (or_intror Hv)))); tauto.
  Qed.

  Variable W : Set.

  Fixpoint qf_map (f : V -> W) (A : qform V) : qform W :=
    match A with
    | qf_eq0 p => qf_eq0 (qp_map f p)
    | qf_neq0 p => qf_neq0 (qp_map f p)
    | qf_and A B => qf_and (qf_map f A) (qf_map f B)
    | qf_or A B => qf_or (qf_map f A) (qf_map f B)
    end.

  Lemma qf_holds_map (φ : W -> rat) f A :
    qf_holds φ (qf_map f A) <-> qf_holds (fun v => φ (f v)) A.
  Proof.
    induction A; simpl; rewrite ?qp_eval_map; tauto.
  Qed.

End qf_vars.

(** * Step (a) and (b): a formula becomes a single equation P = 0,
      with one fresh variable for each inequation *)

Section qf_to_qpoly.

  Variable V : Set.

  (* number of inequations, i.e. of fresh variables *)
  Fixpoint qf_nneq (A : qform V) : nat :=
    match A with
    | qf_eq0 _ => 0
    | qf_neq0 _ => 1
    | qf_and A B => Nat.add (qf_nneq A) (qf_nneq B)
    | qf_or A B => Nat.add (qf_nneq A) (qf_nneq B)
    end.

  Definition lift_l k m (x : V + pos k) : V + pos (Nat.add k m) :=
    match x with
    | inl v => inl v
    | inr i => inr (pos_left m i)
    end.

  Definition lift_r k m (x : V + pos m) : V + pos (Nat.add k m) :=
    match x with
    | inl v => inl v
    | inr i => inr (pos_right k i)
    end.

  Fixpoint qf_tr (A : qform V) : qpoly (V + pos (qf_nneq A)) :=
    match A return qpoly (V + pos (qf_nneq A)) with
    | qf_eq0 p => qp_map inl p
    | qf_neq0 p => qp_add (qp_mul (qp_map inl p) (qp_var (inr pos0))) (qp_cnst (-1))
    | qf_and A B => qp_add (qp_sqr (qp_map (@lift_l _ (qf_nneq B)) (qf_tr A)))
                           (qp_sqr (qp_map (@lift_r (qf_nneq A) _) (qf_tr B)))
    | qf_or A B => qp_mul (qp_map (@lift_l _ (qf_nneq B)) (qf_tr A))
                          (qp_map (@lift_r (qf_nneq A) _) (qf_tr B))
    end.

  Definition senv k (φ : V -> rat) (ψ : pos k -> rat) (x : V + pos k) : rat :=
    match x with
    | inl v => φ v
    | inr i => ψ i
    end.

  Definition pos_split k m (ψ1 : pos k -> rat) (ψ2 : pos m -> rat) (j : pos (Nat.add k m)) : rat :=
    match pos_both k m j with
    | inl i => ψ1 i
    | inr i => ψ2 i
    end.

  Local Fact senv_lift_l k m φ (ψ : pos (Nat.add k m) -> rat) p :
    qp_eval (senv φ ψ) (qp_map (@lift_l k m) p) = qp_eval (senv φ (fun i => ψ (pos_left m i))) p.
  Proof. rewrite qp_eval_map; apply qp_eval_ext'; by intros []. Qed.

  Local Fact senv_lift_r k m φ (ψ : pos (Nat.add k m) -> rat) p :
    qp_eval (senv φ ψ) (qp_map (@lift_r k m) p) = qp_eval (senv φ (fun i => ψ (pos_right k i))) p.
  Proof. rewrite qp_eval_map; apply qp_eval_ext'; by intros []. Qed.

  Local Fact pos_split_left k m ψ1 ψ2 i : @pos_split k m ψ1 ψ2 (pos_left m i) = ψ1 i.
  Proof. by rewrite /pos_split pos_both_left. Qed.

  Local Fact pos_split_right k m ψ1 ψ2 i : @pos_split k m ψ1 ψ2 (pos_right k i) = ψ2 i.
  Proof. by rewrite /pos_split pos_both_right. Qed.

  Local Fact senv_ext k φ (ψ ψ' : pos k -> rat) p :
    (forall i, ψ i = ψ' i) -> qp_eval (senv φ ψ) p = qp_eval (senv φ ψ') p.
  Proof. intros H; apply qp_eval_ext'; intros []; simpl; auto. Qed.

  Theorem qf_tr_spec (φ : V -> rat) A :
    qf_holds φ A <-> exists ψ : pos (qf_nneq A) -> rat, qp_eval (senv φ ψ) (qf_tr A) = 0.
  Proof.
    induction A as [ p | p | A HA B HB | A HA B HB ]; simpl.
    - split.
      + intros H; exists (fun _ => 0); rewrite qp_eval_map; exact H.
      + intros (ψ & H); rewrite qp_eval_map in H; exact H.
    - rewrite rat_neq0_inv; split.
      + intros (y & Hy); exists (fun _ => y); by rewrite /= qp_eval_map Hy subrr.
      + intros (ψ & H); exists (ψ pos0); apply/eqP.
        by rewrite -subr_eq0 -[qp_eval φ p](qp_eval_map (senv φ ψ) inl) H.
    - rewrite HA HB; split.
      + intros ((ψ1 & H1) & (ψ2 & H2)); exists (pos_split ψ1 ψ2).
        rewrite senv_lift_l senv_lift_r.
        rewrite (senv_ext _ _ (pos_split_left ψ1 ψ2)) (senv_ext _ _ (pos_split_right ψ1 ψ2)).
        by rewrite H1 H2 mul0r addr0.
      + intros (ψ & H); rewrite senv_lift_l senv_lift_r -!expr2 in H.
        apply rat_sum_sqr2_eq0 in H as [ H1 H2 ].
        split; eexists; eassumption.
    - rewrite HA HB; split.
      + intros [ (ψ1 & H1) | (ψ2 & H2) ].
        * exists (pos_split ψ1 (fun _ => 0)).
          rewrite senv_lift_l (senv_ext _ _ (pos_split_left ψ1 _)) H1; apply mul0r.
        * exists (pos_split (fun _ => 0) ψ2).
          rewrite senv_lift_r (senv_ext _ _ (pos_split_right _ ψ2)) H2; apply mulr0.
      + intros (ψ & H); rewrite senv_lift_l senv_lift_r in H.
        apply rat_mul_eq0 in H as [ H | H ]; [ left | right ]; eexists; eassumption.
  Qed.

End qf_to_qpoly.

(** * Step (c): the H10Q instance *)

(* the single polynomial equation in n + k variables *)
Definition qf_poly {n} (A : qform (pos n)) : qpoly (pos (Nat.add n (qf_nneq A))) :=
  qp_map (@pos_lr _ _) (qf_tr A).

Definition qf_to_H10Q {n} (A : qform (pos n)) : H10Q_PROBLEM :=
  existT _ (Nat.add n (qf_nneq A)) (fst (qp_clear (qf_poly A))).

Lemma qf_poly_spec n (A : qform (pos n)) :
  qf_sat A <-> exists Φ : pos (Nat.add n (qf_nneq A)) -> rat, qp_eval Φ (qf_poly A) = 0.
Proof.
  unfold qf_sat, qf_poly; split.
  - intros (φ & H); apply qf_tr_spec in H as (ψ & H).
    exists (pos_split φ ψ); rewrite qp_eval_map -H.
    apply qp_eval_ext'; intros x.
    by rewrite /pos_split pos_both_lr; destruct x.
  - intros (Φ & H); rewrite qp_eval_map in H.
    exists (fun i => Φ (pos_left _ i)); apply qf_tr_spec.
    exists (fun i => Φ (pos_right _ i)); rewrite -H.
    apply qp_eval_ext'; by intros [].
Qed.

Theorem qf_to_H10Q_spec n (A : qform (pos n)) : qf_sat A <-> H10Q (qf_to_H10Q A).
Proof.
  rewrite qf_poly_spec; simpl; split; intros (Φ & H); exists Φ.
  - by apply qp_clear_eq0.
  - by apply (qp_clear_eq0 Φ (fun _ => 0)).
Qed.

Definition qf_SAT : {n & qform (pos n)} -> Prop := fun s => qf_sat (projT2 s).

Corollary qf_SAT_H10Q : qf_SAT ⪯ H10Q.
Proof.
  exists (fun s => qf_to_H10Q (projT2 s)); intros [ n A ]; apply qf_to_H10Q_spec.
Qed.

(** * Lists of finite tests *)

Definition qf_list_to_H10Q (l : list {n & qform (pos n)}) : list H10Q_PROBLEM :=
  List.map (fun s => qf_to_H10Q (projT2 s)) l.

Lemma qf_list_to_H10Q_spec l :
  Forall qf_SAT l <-> Forall H10Q (qf_list_to_H10Q l).
Proof.
  induction l as [ | [ n A ] l IHl ]; simpl.
  - split; constructor.
  - rewrite !Forall_cons_iff IHl; unfold qf_SAT; simpl.
    rewrite qf_to_H10Q_spec; tauto.
Qed.

(* every finite test is decidable relative to a decider for H10Q *)
Corollary qf_SAT_dec : Definitions.decidable H10Q -> Definitions.decidable qf_SAT.
Proof. exact (dec_red qf_SAT_H10Q). Qed.

(* the same, with qf_SAT unfolded *)
Corollary qf_sat_dec :
  Definitions.decidable H10Q ->
  Definitions.decidable (fun s : {n & qform (pos n)} => qf_sat (projT2 s)).
Proof. exact qf_SAT_dec. Qed.
