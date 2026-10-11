(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Corollary 7.1 (ii) of the paper: H10Q many-one reduces to
   H10Q_SOS2 (H10Q_H10Q_SOS2, the reduction H10(Q) <=_m S_2 in the
   proof of thm:degree-normal-form), by the arithmetic-circuit
   normal form. Every node
   of the syntax tree of p receives a fresh variable Y_v, and we
   collect the degree <= 2 constraints

       Y_v - c,  Y_v - X_j,  Y_v - (Y_u + Y_w),  Y_v - Y_u * Y_w

   together with Y_root. The node variables of p live in
   pos (dp_size p): the root is pos0, the nodes of the left
   (resp. right) subtree are shifted with pos_nxt ∘ pos_left
   (resp. pos_nxt ∘ pos_right). *)

From Stdlib Require Import ZArith Lia List.

From Undecidability.Synthetic
  Require Import Definitions.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos.

From Undecidability.H10
  Require Import H10Z.

Set Implicit Arguments.

(** * The syntactic construction (Stdlib only) *)

Section circuit.

  Variables (V P : Set).

  (* renaming of variables *)
  Fixpoint dp_ren {W : Set} (f : V -> W) (p : dio_polynomial V P) : dio_polynomial W P :=
    match p with
      | dp_cnst z => dp_cnst z
      | dp_var v => dp_var (f v)
      | dp_par i => dp_par i
      | dp_comp o p q => dp_comp o (dp_ren f p) (dp_ren f q)
    end.

End circuit.

Arguments dp_ren {V P W}.

Definition dp_sub {V P : Set} (a b : dio_polynomial V P) : dio_polynomial V P :=
  dp_add a (dp_mul (dp_cnst (-1)%Z) b).

Definition sum_r {V A B : Set} (g : A -> B) (x : V + A) : V + B :=
  match x with
    | inl v => inl v
    | inr a => inr (g a)
  end.

Definition sum_f {V A : Set} {X : Type} (φ : V -> X) (ψ : A -> X) (x : V + A) : X :=
  match x with
    | inl v => φ v
    | inr a => ψ a
  end.

(* the embeddings of the nodes of the two subtrees *)
Definition pos_lft {a} b (i : pos a) : pos (S (a+b)) := pos_nxt (pos_left b i).
Definition pos_rgt a {b} (j : pos b) : pos (S (a+b)) := pos_nxt (pos_right a j).

Definition pos_case {X : Type} a b (x : X) (f : pos a -> X) (g : pos b -> X) (k : pos (S (a+b))) : X :=
  match pos_S_inv k with
    | inl _ => x
    | inr (exist _ k' _) =>
        match pos_both a b k' with
          | inl i => f i
          | inr j => g j
        end
  end.

Fact pos_case_fst X a b x f g : @pos_case X a b x f g pos0 = x.
Proof. reflexivity. Qed.

Fact pos_case_lft X a b x f g i : @pos_case X a b x f g (pos_lft b i) = f i.
Proof. unfold pos_case, pos_lft; simpl; now rewrite pos_both_left. Qed.

Fact pos_case_rgt X a b x f g j : @pos_case X a b x f g (pos_rgt a j) = g j.
Proof. unfold pos_case, pos_rgt; simpl; now rewrite pos_both_right. Qed.

Section circ.

  Variables (V P : Set).

  Implicit Type (p : dio_polynomial V P).

  Definition circ_root p : pos (dp_size p) :=
    match p return pos (dp_size p) with
      | dp_cnst _ => pos0
      | dp_var _ => pos0
      | dp_par _ => pos0
      | dp_comp _ _ _ => pos0
    end.

  (* the list of node constraints of p *)
  Fixpoint circ p : list (dio_polynomial (V + pos (dp_size p)) P) :=
    match p return list (dio_polynomial (V + pos (dp_size p)) P) with
      | dp_cnst z => dp_sub (dp_var (inr pos0)) (dp_cnst z) :: nil
      | dp_var x  => dp_sub (dp_var (inr pos0)) (dp_var (inl x)) :: nil
      | dp_par i  => dp_sub (dp_var (inr pos0)) (dp_par i) :: nil
      | dp_comp o p q =>
          dp_sub (dp_var (inr pos0))
                 (dp_comp o (dp_var (inr (pos_lft (dp_size q) (circ_root p))))
                            (dp_var (inr (pos_rgt (dp_size p) (circ_root q)))))
       :: map (dp_ren (sum_r (pos_lft (dp_size q)))) (circ p)
       ++ map (dp_ren (sum_r (pos_rgt (dp_size p)))) (circ q)
    end.

End circ.

(** * Degree and semantics over Q *)

From Undecidability.H10
  Require Import H10Q.

From Undecidability.H10.Rational
  Require Import RatUtil.

From mathcomp Require Import boot algebra.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section semantics.

  Variables (V P : Set).

  Fact dp_deg_ren (W : Set) (f : V -> W) (p : dio_polynomial V P) : dp_deg (dp_ren f p) = dp_deg p.
  Proof. induction p as [ | | | [] p Hp q Hq ]; simpl; auto. Qed.

  Fact dp_eval_rat_ren (W : Set) (f : V -> W) φ (ν : P -> rat) p :
    dp_eval_rat φ ν (dp_ren f p) = dp_eval_rat (fun x => φ (f x)) ν p.
  Proof. induction p as [ | | | [] p Hp q Hq ]; simpl; auto; now rewrite Hp Hq. Qed.

  Fact dp_eval_rat_sub φ (ν : P -> rat) (a b : dio_polynomial V P) :
    dp_eval_rat φ ν (dp_sub a b) = 0 <-> dp_eval_rat φ ν a = dp_eval_rat φ ν b.
  Proof.
    unfold dp_sub; rewrite dp_eval_rat_fix_add dp_eval_rat_fix_mul.
    have E : dp_eval_rat φ ν (dp_cnst (-1)%ZZ) = -1 by rewrite -Z_to_rat_1 -Z_to_rat_opp.
    rewrite E mulN1r.
    split; intros H.
    - by apply/eqP; rewrite -subr_eq0; apply/eqP.
    - by rewrite H subrr.
  Qed.

End semantics.

Section circ_semantics.

  Variables (V P : Set).

  Lemma circ_deg (p : dio_polynomial V P) : Forall (fun c => le (dp_deg c) 2) (circ p).
  Proof.
    induction p as [ | | | o p Hp q Hq ]; simpl.
    1-3: constructor; [ simpl; auto | constructor ].
    constructor.
    + destruct o; simpl; auto.
    + apply Forall_app; split; apply Forall_map;
        [ revert Hp | revert Hq ]; apply Forall_impl; intros c; cbv beta; now rewrite dp_deg_ren.
  Qed.

  (* soundness: the node values extend a valuation to a zero of all constraints *)
  Lemma circ_sound φ (ν : P -> rat) (p : dio_polynomial V P) :
    exists ψ : pos (dp_size p) -> rat,
        ψ (circ_root p) = dp_eval_rat φ ν p
     /\ Forall (fun c => dp_eval_rat (sum_f φ ψ) ν c = 0) (circ p).
  Proof.
    induction p as [ z | x | i | o p (ψp & Hp1 & Hp2) q (ψq & Hq1 & Hq2) ].
    1-3: match goal with |- exists _ : pos (dp_size ?p) -> _, _ => exists (fun _ => dp_eval_rat φ ν p) end;
         split; auto;
         constructor; [ apply dp_eval_rat_sub; reflexivity | constructor ].
    exists (pos_case (dp_eval_rat φ ν (dp_comp o p q)) ψp ψq); split; auto.
    constructor.
    + apply dp_eval_rat_sub; destruct o; cbn [dp_eval_rat sum_f];
        rewrite pos_case_fst pos_case_lft pos_case_rgt Hp1 Hq1; reflexivity.
    + apply Forall_app; split; apply Forall_map.
      * revert Hp2; apply Forall_impl; intros c Hc; cbv beta in Hc |- *.
        rewrite dp_eval_rat_ren -Hc; apply dp_eval_rat_ext; auto.
        intros [ v | k ] _; simpl; auto; apply pos_case_lft.
      * revert Hq2; apply Forall_impl; intros c Hc; cbv beta in Hc |- *.
        rewrite dp_eval_rat_ren -Hc; apply dp_eval_rat_ext; auto.
        intros [ v | k ] _; simpl; auto; apply pos_case_rgt.
  Qed.

  (* completeness: if all constraints vanish, the root carries the value of p *)
  Lemma circ_complete (p : dio_polynomial V P) (χ : V + pos (dp_size p) -> rat) (ν : P -> rat) :
       Forall (fun c => dp_eval_rat χ ν c = 0) (circ p)
    -> χ (inr (circ_root p)) = dp_eval_rat (fun v => χ (inl v)) ν p.
  Proof.
    revert χ; induction p as [ z | x | i | o p Hp q Hq ]; intros χ H.
    1-3: inversion H as [ | ? ? H1 _ ]; apply dp_eval_rat_sub in H1; exact H1.
    simpl in H.
    inversion H as [ | ? ? H1 H2 ]; subst.
    apply dp_eval_rat_sub in H1.
    apply Forall_app in H2 as [ H2 H3 ].
    apply Forall_map in H2, H3.
    specialize (Hp (fun x => χ (sum_r (pos_lft (dp_size q)) x))).
    specialize (Hq (fun x => χ (sum_r (pos_rgt (dp_size p)) x))).
    simpl in Hp, Hq.
    assert (Ep : χ (inr (pos_lft (dp_size q) (circ_root p))) = dp_eval_rat (fun v => χ (inl v)) ν p).
    { apply Hp; revert H2; apply Forall_impl; intros c; cbv beta; now rewrite dp_eval_rat_ren. }
    assert (Eq : χ (inr (pos_rgt (dp_size p) (circ_root q))) = dp_eval_rat (fun v => χ (inl v)) ν q).
    { apply Hq; revert H3; apply Forall_impl; intros c; cbv beta; now rewrite dp_eval_rat_ren. }
    destruct o; cbn [dp_eval_rat] in H1 |- *; rewrite -Ep -Eq; exact H1.
  Qed.

End circ_semantics.

(** * The reduction *)

Definition H10Q_SOS2_list n (p : dio_polynomial (pos n) (pos 0)) :
    list (dio_polynomial (pos (Nat.add n (dp_size p))) (pos 0)) :=
  map (dp_ren (@pos_lr n (dp_size p))) (dp_var (inr (circ_root p)) :: circ p).

Fact H10Q_SOS2_list_cond n p :
  lt 0 (length (@H10Q_SOS2_list n p)) /\ forallb (fun q => Nat.leb (dp_deg q) 2) (H10Q_SOS2_list p) = true.
Proof.
  split.
  - simpl; lia.
  - apply dp_deg_forallb_Forall, Forall_map.
    constructor.
    + simpl; lia.
    + generalize (circ_deg p); apply Forall_impl; intros c; cbv beta; now rewrite dp_deg_ren.
Qed.

Definition H10Q_to_SOS2 (x : H10Q_PROBLEM) : H10Q_SOS2_PROBLEM :=
  match x with
    | existT n p => existT _ (Nat.add n (dp_size p)) (exist _ (H10Q_SOS2_list p) (H10Q_SOS2_list_cond p))
  end.

Lemma H10Q_to_SOS2_spec x : H10Q x <-> H10Q_SOS2 (H10Q_to_SOS2 x).
Proof.
  destruct x as [ n p ]; unfold H10Q_to_SOS2; rewrite H10Q_SOS2_spec; simpl.
  split.
  - intros (Φ & HΦ).
    destruct (circ_sound Φ (fun _ => 0) p) as (ψ & H1 & H2).
    exists (fun k => sum_f Φ ψ (pos_both n (dp_size p) k)).
    unfold H10Q_SOS2_list; apply Forall_map.
    assert (forall c : dio_polynomial (pos n + pos (dp_size p)) (pos 0),
        dp_eval_rat (fun k => sum_f Φ ψ (pos_both n (dp_size p) k)) (fun _ => 0) (dp_ren (@pos_lr _ _) c)
      = dp_eval_rat (sum_f Φ ψ) (fun _ => 0) c) as E.
    { intros c; rewrite dp_eval_rat_ren; apply dp_eval_rat_ext; auto.
      intros k _; now rewrite pos_both_lr. }
    constructor.
    + rewrite E; simpl; now rewrite H1.
    + revert H2; apply Forall_impl; intros c; cbv beta; now rewrite E.
  - intros (Φ & HΦ).
    unfold H10Q_SOS2_list in HΦ; apply Forall_map in HΦ.
    inversion HΦ as [ | ? ? H1 H2 ]; subst.
    rewrite dp_eval_rat_ren in H1; cbn [dp_eval_rat] in H1.
    exists (fun i => Φ (pos_lr (inl i))).
    assert (E := circ_complete p (fun x => Φ (pos_lr x)) (fun _ => 0)); cbv beta in E.
    rewrite <- E; [ exact H1 | ].
    revert H2; apply Forall_impl; intros c; cbv beta; now rewrite dp_eval_rat_ren.
Qed.

Theorem H10Q_H10Q_SOS2 : H10Q ⪯ H10Q_SOS2.
Proof. exists H10Q_to_SOS2; exact H10Q_to_SOS2_spec. Qed.
