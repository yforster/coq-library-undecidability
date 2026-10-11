(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Tier 2: the Skolemized theory T of Section 2.3 of the paper
   (02-reduction.tex, red:theory) and the finite rational tests of
   Section 2.4 (red:finite-tests). See DESIGN.md, Sections 3 and 4.

   Contents.
   1. Enumerations (Stdlib only): symbols, ground terms [gterm_list]
      (cumulative, exhaustive), subterms, index lookup, finite choice,
      the variable layout of the tests.
   2. The macro layer (DESIGN 3.2): elements of R_F as pairs of terms
      [RF], elements of F_R as fractions [FR], the coordinates of T_b
      [tX], [tY], the curve [onE], the addition relation [ADDfin], the
      truncated formal logarithm with cleared denominators [lamP],
      localization [LOC], formal points [FORMAL], z(T_b) [withZ], and the
      primary-test fraction [prim].
   3. The axiom matrices as [fml nat] (free variables [tvar 0], [tvar 1]):
      [ax_coord], [ax_P], [ax_add], [ax_chain], [ax_sqrt2], [ax_rep K]
      (K >= 1), [ax_root f]; the set of ground instances [Inst D f].
   4. Semantic unfolding lemmas, over an arbitrary [numFieldType] R and
      any valuation [ν : term X -> R] respecting the ring symbols
      ([ring_hom ν]), so that they apply to the standard model over rat
      and to the ambient valuation into sQ: [coord_holds_iff],
      [P_holds_iff], [add_holds_iff] (and [add_ADDrel]),
      [chain_holds_iff], [sqrt2_holds_iff], [root_holds_iff],
      [rep_holds_iff] (via [branch_holds_iff], [mem_holds_iff],
      [LOC_iff], [FORMAL_iff], [withZ_iff], [prim_spec], [lamP_spec]);
      the ground-instance versions [inst_*_iff]; [rat_Z0].
   5. Enumeration of the instances [inst_list], the finite tests
      [test D f N : {n & qform (pos n)}] (constraints (a) to (d)),
      cofinality [tests_FinSat], monotonicity [test_mono], and the
      bridge for the standard model [test_sound_from_model].
   6. [Inst_sem_iff]: all instances hold iff the semantic conditions
      [InstSem] hold (the setoid version is in TheoryS.v).

   Deviation from DESIGN 3.3 (recorded for the README): the constants of
   ax_P are the coordinates of P = [m] P0 (as s_int constants of the
   cleared fractions), computed from fd_P0 by [Pgen]; the tests contain
   them, and no other data of P0.

   No axioms are used. *)

From Stdlib Require Import Arith ZArith Lia List.
From Stdlib Require Cantor.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos.

From Undecidability.H10.Rational
  Require Import Signature.

Import ListNotations.

Set Implicit Arguments.

(** * 1. Enumerations (Stdlib only) *)

Section lists.

  Definition all_coord : list coord := [cx0; cx1; cx2; cy0; cy1; cy2].
  Definition all_wcomp : list wcomp := [wX0; wX1; wY0; wY1; wiota; wkappa].
  Definition all_tag1 : list tag1 := [tg_fh; tg_fj0].
  Definition all_tag2 : list tag2 := [tg_fha; tg_prim; tg_fh4a; tg_alt].

  Lemma all_coord_spec c : In c all_coord.
  Proof. destruct c; simpl; tauto. Qed.
  Lemma all_wcomp_spec c : In c all_wcomp.
  Proof. destruct c; simpl; tauto. Qed.
  Lemma all_tag1_spec c : In c all_tag1.
  Proof. destruct c; simpl; tauto. Qed.
  Lemma all_tag2_spec c : In c all_tag2.
  Proof. destruct c; simpl; tauto. Qed.

  Definition rep1_of_mem (j : mem13) : list rep1 :=
    [r_r j; r_B j; r_wB j; r_iota' j; r_kappa' j]
    ++ flat_map (fun s => [r_h j s; r_j0 j s]
                          ++ flat_map (fun tg => map (r_W1 j s tg) all_wcomp) all_tag1) all_sgn.

  Definition all_rep1 : list rep1 := [r_u1; r_u2; r_v] ++ flat_map rep1_of_mem all_mem13.

  Definition rep2_of_mem (j : mem13) : list rep2 :=
    [r_fz j; r_fy j; r_fz' j]
    ++ flat_map (fun s => flat_map (fun tg => map (r_W2 j s tg) all_wcomp) all_tag2) all_sgn.

  Definition all_rep2 : list rep2 := flat_map rep2_of_mem all_mem13.

  Lemma all_rep1_spec c : In c all_rep1.
  Proof.
    unfold all_rep1.
    destruct c as [ | | | j | j | j | j | j | j s | j s | j s tg c ];
      try (apply in_or_app; left; simpl; tauto);
      apply in_or_app; right; apply in_flat_map; exists j; split; try apply all_mem13_spec;
      unfold rep1_of_mem; try (apply in_or_app; left; simpl; tauto);
      apply in_or_app; right; apply in_flat_map; exists s; split; try apply all_sgn_spec;
      try (apply in_or_app; left; simpl; tauto);
      apply in_or_app; right; apply in_flat_map; exists tg; split; try apply all_tag1_spec;
      apply in_map, all_wcomp_spec.
  Qed.

  Lemma all_rep2_spec c : In c all_rep2.
  Proof.
    unfold all_rep2.
    destruct c as [ j | j | j | j s tg c ];
      apply in_flat_map; exists j; split; try apply all_mem13_spec;
      unfold rep2_of_mem; try (apply in_or_app; left; simpl; tauto);
      apply in_or_app; right; apply in_flat_map; exists s; split; try apply all_sgn_spec;
      apply in_flat_map; exists tg; split; try apply all_tag2_spec;
      apply in_map, all_wcomp_spec.
  Qed.

  (* cumulative lists of symbols: stage k contains the symbols with
     parameters <= k *)
  Definition sym0_list (k : nat) : list sym0 :=
    s_zero :: s_one
      :: flat_map (fun i => [s_int (Z.of_nat i); s_int (- Z.of_nat i)%Z; s_cst i]) (seq 0 (S k)).

  Definition sym1_list (k : nat) : list sym1 :=
    s_neg :: map s_coord all_coord
      ++ flat_map (fun i => map (s_chain i) all_coord ++ map (s_rep1 i) all_rep1) (seq 0 (S k)).

  Definition sym2_list (k : nat) : list sym2 :=
    s_add :: s_mul :: flat_map (fun i => map (s_rep2 i) all_rep2) (seq 0 (S k)).

  Local Fact in_seq0 i k : i <= k -> In i (seq 0 (S k)).
  Proof. intros H; apply in_seq; lia. Qed.

  Lemma sym0_list_spec g : exists k, forall k', k <= k' -> In g (sym0_list k').
  Proof.
    destruct g as [ | | z | i ].
    - exists 0; simpl; auto.
    - exists 0; simpl; auto.
    - exists (Z.to_nat (Z.abs z)); intros k' Hk'; do 2 right.
      apply in_flat_map; exists (Z.to_nat (Z.abs z)); split; [ apply in_seq0; lia | ].
      destruct (Z.abs_spec z) as [ [ H1 H2 ] | [ H1 H2 ] ]; simpl.
      + left; f_equal; lia.
      + right; left; f_equal; lia.
    - exists i; intros k' Hk'; do 2 right.
      apply in_flat_map; exists i; split; [ apply in_seq0; lia | simpl; tauto ].
  Qed.

  Lemma sym1_list_spec g : exists k, forall k', k <= k' -> In g (sym1_list k').
  Proof.
    destruct g as [ | c | i c | i c ].
    - exists 0; simpl; auto.
    - exists 0; intros; right; apply in_or_app; left; apply in_map, all_coord_spec.
    - exists i; intros k' Hk'; right; apply in_or_app; right.
      apply in_flat_map; exists i; split; [ apply in_seq0; lia | ].
      apply in_or_app; left; apply in_map, all_coord_spec.
    - exists i; intros k' Hk'; right; apply in_or_app; right.
      apply in_flat_map; exists i; split; [ apply in_seq0; lia | ].
      apply in_or_app; right; apply in_map, all_rep1_spec.
  Qed.

  Lemma sym2_list_spec g : exists k, forall k', k <= k' -> In g (sym2_list k').
  Proof.
    destruct g as [ | | i c ].
    - exists 0; simpl; auto.
    - exists 0; simpl; auto.
    - exists i; intros k' Hk'; do 2 right.
      apply in_flat_map; exists i; split; [ apply in_seq0; lia | apply in_map, all_rep2_spec ].
  Qed.

  (** Ground terms: [gterm_list k] is cumulative and exhaustive *)

  Fixpoint gterm_list (k : nat) : list gterm :=
    match k with
    | 0 => []
    | S k => gterm_list k
          ++ map tapp0 (sym0_list k)
          ++ flat_map (fun g => map (tapp1 g) (gterm_list k)) (sym1_list k)
          ++ flat_map (fun g => flat_map (fun s => map (tapp2 g s) (gterm_list k)) (gterm_list k))
                      (sym2_list k)
    end.

  Lemma gterm_list_mono k m t : k <= m -> In t (gterm_list k) -> In t (gterm_list m).
  Proof.
    induction 1 as [ | m _ IH ]; auto.
    intros H; cbn [gterm_list]; apply in_or_app; left; auto.
  Qed.

  Lemma gterm_list_spec (t : gterm) : exists k, In t (gterm_list k).
  Proof.
    induction t as [ [] | g | g t (k & Hk) | g s (k1 & Hk1) t (k2 & Hk2) ].
    - destruct (sym0_list_spec g) as (k & Hk).
      exists (S k); cbn [gterm_list]; apply in_or_app; right; apply in_or_app; left.
      apply in_map, Hk; auto.
    - destruct (sym1_list_spec g) as (k' & Hk').
      exists (S (Nat.max k k')); cbn [gterm_list]; do 2 (apply in_or_app; right); apply in_or_app; left.
      apply in_flat_map; exists g; split; [ apply Hk'; lia | ].
      apply in_map; revert Hk; apply gterm_list_mono; lia.
    - destruct (sym2_list_spec g) as (k' & Hk').
      exists (S (Nat.max k' (Nat.max k1 k2))); cbn [gterm_list]; do 3 (apply in_or_app; right).
      apply in_flat_map; exists g; split; [ apply Hk'; lia | ].
      apply in_flat_map; exists s; split; [ revert Hk1; apply gterm_list_mono; lia | ].
      apply in_map; revert Hk2; apply gterm_list_mono; lia.
  Qed.

  (** Subterms *)

  Fixpoint subt (t : gterm) : list gterm :=
    t :: match t with
         | tvar _ => []
         | tapp0 _ => []
         | tapp1 _ s => subt s
         | tapp2 _ s s' => subt s ++ subt s'
         end.

  Lemma subt_refl t : In t (subt t).
  Proof. destruct t; simpl; auto. Qed.

  Lemma subt_trans t u v : In u (subt t) -> In v (subt u) -> In v (subt t).
  Proof.
    induction t as [ x | g | g s IHs | g s IHs s' IHs' ]; simpl.
    - intros [ <- | [] ]; simpl; auto.
    - intros [ <- | [] ]; simpl; auto.
    - intros [ <- | Hu ] Hv; simpl in Hv; auto.
    - intros [ <- | Hu ] Hv; simpl in Hv; auto.
      apply in_app_or in Hu as [ Hu | Hu ]; right; apply in_or_app; auto.
  Qed.

  Lemma subt_1 t g s : In (tapp1 g s) (subt t) -> In s (subt t).
  Proof. intros H; eapply subt_trans; [ exact H | ]; simpl; right; apply subt_refl. Qed.

  Lemma subt_2l t g s s' : In (tapp2 g s s') (subt t) -> In s (subt t).
  Proof. intros H; eapply subt_trans; [ exact H | ]; simpl; right; apply in_or_app; left; apply subt_refl. Qed.

  Lemma subt_2r t g s s' : In (tapp2 g s s') (subt t) -> In s' (subt t).
  Proof. intros H; eapply subt_trans; [ exact H | ]; simpl; right; apply in_or_app; right; apply subt_refl. Qed.

  (* the terms compared by the atoms of a formula *)
  Fixpoint fml_terms {X} (A : fml X) : list (term X) :=
    match A with
    | f_eq s t => [s; t]
    | f_ne s t => [s; t]
    | f_and A B => fml_terms A ++ fml_terms B
    | f_or A B => fml_terms A ++ fml_terms B
    | f_tt => []
    | f_ff => []
    end.

  (* lists closed under immediate subterms *)
  Definition sub_closed (L : list gterm) : Prop :=
       (forall g s, In (tapp1 g s) L -> In s L)
    /\ (forall g s s', In (tapp2 g s s') L -> In s L /\ In s' L).

  Lemma flat_map_subt_closed l : sub_closed (flat_map subt l).
  Proof.
    split.
    - intros g s H; apply in_flat_map in H as (t & Ht & H).
      apply in_flat_map; exists t; split; auto; revert H; apply subt_1.
    - intros g s s' H; apply in_flat_map in H as (t & Ht & H); split;
        apply in_flat_map; exists t; split; auto; revert H; [ apply subt_2l | apply subt_2r ].
  Qed.

  Lemma flat_map_subt_incl l t : In t l -> In t (flat_map subt l).
  Proof. intros H; apply in_flat_map; exists t; split; auto; apply subt_refl. Qed.

  (** Index lookup (first occurrence) *)

  Fixpoint ix (L : list gterm) (u : gterm) : nat :=
    match L with
    | [] => 0
    | v :: L => if gterm_eq_dec v u then 0 else S (ix L u)
    end.

  Lemma ix_nth L u d : In u L -> nth (ix L u) L d = u.
  Proof.
    induction L as [ | v L IHL ]; simpl; [ tauto | ].
    destruct (gterm_eq_dec v u) as [ -> | Hvu ]; auto.
    intros [ -> | H ]; [ tauto | auto ].
  Qed.

  (** Finite choice over a list of ground terms (no axiom) *)

  Lemma fin_choice {B : Type} (b0 : B) (P : gterm -> B -> Prop) (l : list gterm) :
    (forall u, In u l -> exists y, P u y) -> exists g : gterm -> B, forall u, In u l -> P u (g u).
  Proof.
    induction l as [ | v l IHl ]; intros H.
    - exists (fun _ => b0); simpl; tauto.
    - destruct IHl as (g & Hg); [ intros; apply H; simpl; auto | ].
      destruct (H v) as (y & Hy); [ simpl; auto | ].
      exists (fun u => if gterm_eq_dec u v then y else g u).
      intros u [ Hvu | Hu ].
      + subst u; destruct (gterm_eq_dec v v) as [ _ | [] ]; auto.
      + destruct (gterm_eq_dec u v) as [ -> | _ ]; auto.
  Qed.

  (** Substitution for the two free variables of a matrix *)

  Definition sub2 (A a : gterm) (n : nat) : gterm :=
    match n with 0 => A | 1 => a | _ => tapp0 s_zero end.

  (** Variable layout of the tests: the term at index i of the term list
      is the variable [tvq i] (even), the k-th witness of Phi for it is
      [wvq i k] (odd) *)

  Definition tvq (i : nat) : nat := 2 * i.
  Definition wvq (i k : nat) : nat := S (2 * Cantor.to_nat (i, k)).

  Definition phi_ren (i v : nat) : nat := match v with 0 => tvq i | _ => wvq i v end.

  Definition var_case {B : Type} (ft : nat -> B) (fw : nat -> nat -> B) (v : nat) : B :=
    if Nat.even v then ft (Nat.div2 v)
    else let (i, k) := Cantor.of_nat (Nat.div2 v) in fw i k.

  Lemma var_case_t {B} (ft : nat -> B) fw i : var_case ft fw (tvq i) = ft i.
  Proof.
    unfold var_case, tvq; rewrite Nat.even_mul; simpl; f_equal; apply Nat.div2_double.
  Qed.

  Lemma var_case_w {B} (ft : nat -> B) fw i k : var_case ft fw (wvq i k) = fw i k.
  Proof.
    unfold var_case, wvq; rewrite Nat.even_succ, Nat.odd_mul, Nat.div2_succ_double, Cantor.cancel_of_to.
    reflexivity.
  Qed.

  (** Closing a formula over nat variables to pos n variables *)

  Definition vmax (l : list nat) : nat := fold_right Nat.max 0 l.

  Lemma vmax_spec l v : In v l -> v < S (vmax l).
  Proof. induction l as [ | x l IHl ]; simpl; [ tauto | intros [ -> | H ]; [ | apply IHl in H ]; lia ]. Qed.

  Definition trv (n v : nat) : pos (S n) :=
    match lt_dec v (S n) with
    | left H => nat2pos H
    | right _ => pos0
    end.

  Lemma trv_spec n v : v < S n -> pos2nat (trv n v) = v.
  Proof.
    intros H; unfold trv; destruct (lt_dec v (S n)) as [ H' | ]; [ apply pos2nat_nat2pos | lia ].
  Qed.

End lists.

(** * 2. The macro layer (DESIGN 3.2) *)

(* dio_logic is only Required, not Imported: its notations clash with MathComp *)
From Undecidability.H10.Dio
  Require dio_logic.

From Undecidability.H10
  Require Import H10Z.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential FixedData Ambient.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Lemma In_mem {T : eqType} (x : T) (s : seq T) : List.In x s <-> x \in s.
Proof.
  elim: s => [ | y s IH ] /=; first by rewrite in_nil; split.
  rewrite in_cons; split.
  - case=> [ <- | /IH -> ]; [ by rewrite eqxx | by rewrite orbT ].
  - case/orP => [ /eqP -> | /IH ]; auto.
Qed.

Section macros.

  Variable X : Type.
  Implicit Types (s t b : term X).

  (** terms *)

  Definition tz : term X := tapp0 s_zero.
  Definition to : term X := tapp0 s_one.
  Definition ti (i : int) : term X := tapp0 (s_int (int_to_Z i)).
  Definition tadd s t : term X := tapp2 s_add s t.
  Definition tmul s t : term X := tapp2 s_mul s t.
  Definition tneg t : term X := tapp1 s_neg t.
  Definition tsub s t : term X := tadd s (tneg t).
  Definition tco (c : Signature.coord) t : term X := tapp1 (s_coord c) t.
  Definition tch (k : nat) (c : Signature.coord) t : term X := tapp1 (s_chain k c) t.

  (** R_F: pairs of terms, t0 + t1 sqrt2 *)

  Definition RF : Type := (term X * term X)%type.
  Implicit Types (x y : RF).

  Definition rf_add x y : RF := (tadd x.1 y.1, tadd x.2 y.2).
  Definition rf_mul x y : RF :=
    (tadd (tmul x.1 y.1) (tmul (ti 2) (tmul x.2 y.2)), tadd (tmul x.1 y.2) (tmul x.2 y.1)).
  Definition rf_neg x : RF := (tneg x.1, tneg x.2).
  Definition rf_of t : RF := (t, tz).
  Definition rf0 : RF := (tz, tz).
  Definition rf1 : RF := (to, tz).
  Definition rf_int (i : int) : RF := rf_of (ti i).
  Definition rf_pow x (n : nat) : RF := iter n (rf_mul x) rf1.
  (* identity (sg = false) or conjugation (sg = true) *)
  Definition rf_e (sg : bool) x : RF := if sg then (x.1, tneg x.2) else x.

  (** F_R: fractions of elements of R_F, numerator and denominator *)

  Definition FR : Type := (RF * RF)%type.
  Implicit Types (z w : FR).

  Definition fr_add z w : FR := (rf_add (rf_mul z.1 w.2) (rf_mul w.1 z.2), rf_mul z.2 w.2).
  Definition fr_mul z w : FR := (rf_mul z.1 w.1, rf_mul z.2 w.2).
  Definition fr_neg z : FR := (rf_neg z.1, z.2).
  Definition fr_sub z w : FR := fr_add z (fr_neg w).
  Definition fr_sq z : FR := fr_mul z z.
  Definition fr_div z w : FR := (rf_mul z.1 w.2, rf_mul z.2 w.1).
  Definition fr_of x : FR := (x, rf1).
  Definition fr0 : FR := fr_of rf0.
  Definition fr_nat (n : nat) : FR := fr_of (rf_int n%:Z).
  (* a constant of F = Q(sqrt2): (a + b sqrt2) = (na db + nb da sqrt2) / (da db) *)
  Definition fr_rat (c : qe rat) : FR :=
    ((ti (numq (qre c) * denq (qim c)), ti (numq (qim c) * denq (qre c))),
     rf_int (denq (qre c) * denq (qim c))).
  Definition fr_aE : FR := fr_rat aE.

  (** formulas *)

  Definition f_all (l : list (fml X)) : fml X := fold_right (@f_and X) f_tt l.
  Definition f_any (l : list (fml X)) : fml X := fold_right (@f_or X) f_ff l.

  Definition eqRF x y : fml X := f_and (f_eq x.1 y.1) (f_eq x.2 y.2).
  Definition neRF x y : fml X := f_or (f_ne x.1 y.1) (f_ne x.2 y.2).
  Definition eqFR z w : fml X := eqRF (rf_mul z.1 w.2) (rf_mul w.1 z.2).
  Definition neFR z w : fml X := neRF (rf_mul z.1 w.2) (rf_mul w.1 z.2).

  (** points of E(F_R): coordinates of T_b (red:coordinate-functions) *)

  Definition FP : Type := (FR * FR)%type.

  Definition tX b : FR := ((tco cx0 b, tco cx1 b), rf_of (tco cx2 b)).
  Definition tY b : FR := ((tco cy0 b, tco cy1 b), rf_of (tco cy2 b)).
  Definition tP b : FP := (tX b, tY b).

  (* y^2 = x^3 + aE x *)
  Definition onE (p : FP) : fml X :=
    eqFR (fr_mul p.2 p.2) (fr_add (fr_mul p.1 (fr_mul p.1 p.1)) (fr_mul fr_aE p.1)).

  (* p1 + p2 = p3 for three finite points: chord or tangent, cleared
     (the case "Some, Some, Some" of ADDrel, FixedData.v) *)
  Definition ADDfin (p1 p2 p3 : FP) : fml X :=
    let x1 := p1.1 in let y1 := p1.2 in
    let x2 := p2.1 in let y2 := p2.2 in
    let x3 := p3.1 in let y3 := p3.2 in
    let lt := fr_add (fr_mul (fr_nat 3) (fr_sq x1)) fr_aE in
    f_or
      (f_and (neFR x1 x2)
      (f_and (eqFR (fr_mul (fr_add (fr_add x3 x1) x2) (fr_sq (fr_sub x2 x1))) (fr_sq (fr_sub y2 y1)))
             (eqFR (fr_mul (fr_add y3 y1) (fr_sub x2 x1)) (fr_mul (fr_sub y2 y1) (fr_sub x1 x3)))))
      (f_and (eqFR x1 x2)
      (f_and (eqFR y1 y2)
      (f_and (neFR y1 fr0)
      (f_and (eqFR (fr_mul (fr_add x3 (fr_mul (fr_nat 2) x1)) (fr_sq (fr_mul (fr_nat 2) y1))) (fr_sq lt))
             (eqFR (fr_mul (fr_add y3 y1) (fr_mul (fr_nat 2) y1)) (fr_mul lt (fr_sub x1 x3))))))).

  (* p2 = - p1 *)
  Definition NEGfin (p1 p2 : FP) : fml X := f_and (eqFR p1.1 p2.1) (eqFR p2.2 (fr_neg p1.2)).

  (** the truncated formal logarithm (DESIGN 1.1) with cleared
      denominators: for c_t = g_t / e_t (g_t in Z[sqrt2], e_t in Z),
      [lamP K N D = (P, E)] with  P = E * D^K * l_K(N/D)  (lamP_spec) *)

  Definition ct_num (t : nat) : RF :=
    (ti (numq (qre (ct t)) * denq (qim (ct t))), ti (numq (qim (ct t)) * denq (qre (ct t)))).
  Definition ct_den (t : nat) : int := denq (qre (ct t)) * denq (qim (ct t)).

  Fixpoint lamP (K : nat) (N D : RF) : RF * int :=
    match K with
    | 0 => (rf0, 1)
    | S K' =>
        let PE := lamP K' N D in
        (rf_add (rf_mul (rf_mul PE.1 (rf_int (ct_den (S K')))) D)
                (rf_mul (rf_mul (ct_num (S K')) (rf_int PE.2)) (rf_pow N (S K'))),
         PE.2 * ct_den (S K'))
    end.

  Definition lamN (K : nat) z : RF := (lamP K z.1 z.2).1.

  (** localization (red:localization-definition), invertibility form:
      z = r^i X / Y  and  (Y0 + s B Y1) iota - 1 = r kappa *)

  Definition LOC (i : nat) (r B : term X) (s : sgn) z (W : wcomp -> term X) : fml X :=
    f_and (eqRF (rf_mul z.1 (W wY0, W wY1)) (rf_mul (rf_mul (rf_pow (rf_of r) i) (W wX0, W wX1)) z.2))
          (f_eq (tsub (tmul (tadd (W wY0) (tmul (tmul (ti (sgnz s)) B) (W wY1))) (W wiota)) to)
                (tmul r (W wkappa))).

  (* 1/x for T_b (sg = false) or for its conjugate (sg = true) *)
  Definition tInvX (sg : bool) b : FR := (rf_of (tco cx2 b), rf_e sg (tco cx0 b, tco cx1 b)).

  (* "T_b is formal for this localization": O, or 1/x in r (R_F)_p *)
  Definition FORMAL (sg : bool) b (r B : term X) (s : sgn) (W : wcomp -> term X) : fml X :=
    f_or (f_eq b tz) (LOC 1 r B s (tInvX sg b) W).

  (* z = -x/y of T_b (or of its conjugate) *)
  Definition tZ (sg : bool) b : FR :=
    (rf_neg (rf_mul (rf_e sg (tco cx0 b, tco cx1 b)) (rf_of (tco cy2 b))),
     rf_mul (rf_of (tco cx2 b)) (rf_e sg (tco cy0 b, tco cy1 b))).

  (* the continuation k applied to z(T_b), with z(O) = 0 *)
  Definition withZ (sg : bool) b (k : FR -> fml X) : fml X :=
    f_or (f_and (f_eq b tz) (k fr0)) (f_and (f_ne b tz) (k (tZ sg b))).

  (* l_K(za)/l_K(zh) - a, cleared (red:primary-test) *)
  Definition prim (K : nat) (a : term X) za zh : FR :=
    (rf_add (rf_mul (lamN K za) (rf_pow zh.2 K))
            (rf_neg (rf_mul (rf_mul (rf_of a) (lamN K zh)) (rf_pow za.2 K))),
     rf_mul (lamN K zh) (rf_pow za.2 K)).

End macros.

Arguments tz {X}.
Arguments to {X}.
Arguments rf0 {X}.
Arguments rf1 {X}.
Arguments fr0 {X}.
Arguments fr_aE {X}.
Arguments ti {X}.
Arguments rf_int {X}.
Arguments fr_nat {X}.
Arguments fr_rat {X}.
Arguments ct_num {X}.

(** * 3. The axiom matrices (DESIGN 3.3)

    Each matrix is first defined for arbitrary terms (over any variable
    type X); the matrix proper is its instance at [tvar 0], [tvar 1]. *)

Section axioms.

  Variable D : FixedData.
  Variable X : Type.
  Implicit Types (t A a b : term X).

  (** ax_coord: red:coordinate-functions, T_a in E(F_R) with nonzero
      denominators and x, y <> 0 for a <> 0 *)
  Definition coord_fml t : fml X :=
    f_or (f_eq t tz)
      (f_and (f_ne (tco cx2 t) tz)
      (f_and (f_ne (tco cy2 t) tz)
      (f_and (neRF (tco cx0 t, tco cx1 t) rf0)
      (f_and (neRF (tco cy0 t, tco cy1 t) rf0)
             (onE (tP t)))))).

  (** ax_P: T_1 = P *)
  Definition P_fml : fml X :=
    match Pgen D with
    | Some (x, y) => f_and (eqFR (tX to) (fr_rat x)) (eqFR (tY to) (fr_rat y))
    | None => f_ff
    end.

  (** ax_add: red:elliptic-axioms, T_{a+a'} = T_a + T_{a'}; the cases
      a = 0 and a' = 0 follow from functionality *)
  Definition add_fml a a' : fml X :=
    f_or (f_eq a tz)
   (f_or (f_eq a' tz)
   (f_or (f_and (f_eq (tadd a a') tz) (NEGfin (tP a) (tP a')))
         (f_and (f_ne (tadd a a') tz) (ADDfin (tP a) (tP a') (tP (tadd a a')))))).

  (** ax_chain: T_a in m E(F_R), by an addition chain Q_1, ..., Q_m = T_a
      with Q_{k+1} = Q_k + Q_1 and all denominators nonzero (Review fix) *)
  Definition cP (k : nat) t : FP X :=
    (((tch k cx0 t, tch k cx1 t), rf_of (tch k cx2 t)),
     ((tch k cy0 t, tch k cy1 t), rf_of (tch k cy2 t))).

  Definition Qf t (k : nat) : FP X := if (k < fd_m D)%N then cP k t else tP t.

  Definition chain_idx : seq nat := iota 1 (fd_m D).-1.

  Definition chain_fml t : fml X :=
    f_or (f_eq t tz)
      (f_and (f_all (List.map (fun k => f_and (f_ne (tch k cx2 t) tz) (f_ne (tch k cy2 t) tz)) chain_idx))
      (f_and (onE (Qf t 1))
             (f_all (List.map (fun k => ADDfin (Qf t k) (Qf t 1) (Qf t k.+1)) chain_idx)))).

  (** ax_sqrt2 (fidelity): sqrt2 not in Frac R *)
  Definition sqrt2_fml a b : fml X := f_or (f_eq b tz) (f_ne (tmul a a) (tmul (ti 2) (tmul b b))).

  (** ax_rep K: the representation axiom of precision K, Skolemized;
      A is the universal variable of the outer block, a that of the inner *)

  Definition s1 (K : nat) (c : rep1) A : term X := tapp1 (s_rep1 K c) A.
  Definition s2 (K : nat) (c : rep2) A a : term X := tapp2 (s_rep2 K c) A a.

  (* u_1, u_2 and u_3 = A v - u_1 - u_2 *)
  Definition tu (K : nat) A (i : i3) : term X :=
    match i with
    | I1 => s1 K r_u1 A
    | I2 => s1 K r_u2 A
    | I3 => tsub (tsub (tmul A (s1 K r_v A)) (s1 K r_u1 A)) (s1 K r_u2 A)
    end.

  (* L_b(u, v) = den(b) u - num(b) v *)
  Definition tL (b : i4) (u v : term X) : term X :=
    tsub (tmul (ti (denq (fd_C D b))) u) (tmul (ti (numq (fd_C D b))) v).

  (* the 13 members of red:contact-list *)
  Definition tmem (K : nat) A (j : mem13) : term X :=
    match j with
    | mem_v => s1 K r_v A
    | mem_L i b => tL b (tu K A i) (s1 K r_v A)
    end.

  (* the possible values eps * k, eps in {1,-1}, k in Kset *)
  Definition eks : list (int * nat) := List.flat_map (fun k => [:: (1, k); (-1, k)]) (fd_Kset D).

  (* the conditions (i) and (ii) at the branch s *)
  Definition branch_fml (K : nat) A a (j : mem13) (s : sgn) : fml X :=
    let r := s1 K (r_r j) A in let B := s1 K (r_B j) A in
    let h := s1 K (r_h j s) A in let j0 := s1 K (r_j0 j s) A in
    let W1 tg c := s1 K (r_W1 j s tg c) A in
    let W2 tg c := s2 K (r_W2 j s tg c) A a in
    let ha := tmul h a in let h4a := tmul (tsub h (ti 4)) a in
    f_and (f_ne h tz)
   (f_and (f_ne j0 tz)
   (f_and (FORMAL false h r B s (W1 tg_fh))
   (f_and (neRF (lamN K (tZ false h)) rf0)
   (f_and (FORMAL false ha r B s (W2 tg_fha))
   (f_and (withZ false ha (fun za => LOC K r B s (prim K a za (tZ false h)) (W2 tg_prim)))
   (f_and (FORMAL true j0 r B s (W1 tg_fj0))
   (f_and (FORMAL true h4a r B s (W2 tg_fh4a))
          (withZ true h4a (fun zb => LOC K r B s (fr_div zb (tZ true j0)) (W2 tg_alt)))))))))).

  Definition mem_fml (K : nat) A a (j : mem13) : fml X :=
    let r := s1 K (r_r j) A in let B := s1 K (r_B j) A in
    f_and (f_any (List.map (fun ek => f_eq (tmem K A j) (tmul (ti (ek.1 * (ek.2)%:Z)) r)) eks))
   (f_and (f_ne r tz)
   (f_and (f_eq (tsub (tmul B B) (ti 2)) (tmul r (s1 K (r_wB j) A)))
   (f_and (f_eq (tsub (tmul (tmul (ti 2) B) (s1 K (r_iota' j) A)) to) (tmul r (s1 K (r_kappa' j) A)))
   (f_and (f_ne (tmul r a) to)
   (f_and (f_or (f_eq a (tmul r (s2 K (r_fz j) A a)))
                (f_eq (tsub (tmul a (s2 K (r_fy j) A a)) to) (tmul r (s2 K (r_fz' j) A a))))
          (f_all (List.map (branch_fml K A a j) all_sgn))))))).

  Definition rep_fml (K : nat) A a : fml X :=
    f_and (f_ne (s1 K r_v A) tz) (f_all (List.map (mem_fml K A a) all_mem13)).

  (** ax_root: f(a_1, ..., a_n) = 0 with a_i = s_cst (i-1) *)
  Fixpoint tm_of_poly {n} (p : dio_polynomial (pos n) (pos 0)) : term X :=
    match p with
    | dp_cnst z => tapp0 (s_int z)
    | dp_var v => tapp0 (s_cst (pos2nat v))
    | dp_par _ => tz
    | dp_comp dio_logic.do_add p q => tadd (tm_of_poly p) (tm_of_poly q)
    | dp_comp dio_logic.do_mul p q => tmul (tm_of_poly p) (tm_of_poly q)
    end.

  Definition root_fml (f : H10Z_PROBLEM) : fml X := f_eq (tm_of_poly (projT2 f)) tz.

End axioms.

Section matrices.

  Variable D : FixedData.

  Definition ax_coord : fml nat := coord_fml (tvar 0).
  Definition ax_P : fml nat := P_fml D nat.
  Definition ax_add : fml nat := add_fml (tvar 0) (tvar 1).
  Definition ax_chain : fml nat := chain_fml D (tvar 0).
  Definition ax_sqrt2 : fml nat := sqrt2_fml (tvar 0) (tvar 1).
  Definition ax_rep (K : nat) : fml nat := rep_fml D K (tvar 0) (tvar 1).
  Definition ax_root (f : H10Z_PROBLEM) : fml nat := root_fml nat f.

  Definition axioms_base (f : H10Z_PROBLEM) : list (fml nat) :=
    [:: ax_coord; ax_P; ax_add; ax_chain; ax_sqrt2; ax_root f].

  Definition is_axiom (f : H10Z_PROBLEM) (M : fml nat) : Prop :=
    List.In M (axioms_base f) \/ exists K, (1 <= K)%N /\ M = ax_rep K.

  (** the ground instances of T + {f(a) = 0}, Skolemized *)
  Definition Inst (f : H10Z_PROBLEM) (phi : gfml) : Prop :=
    exists M A a, is_axiom f M /\ phi = fml_subst (sub2 A a) M.

  Lemma Inst_intro f M A a : is_axiom f M -> Inst f (fml_subst (sub2 A a) M).
  Proof. by move=> H; exists M, A, a. Qed.

  Lemma Inst_coord f A : Inst f (fml_subst (sub2 A A) ax_coord).
  Proof. apply: Inst_intro; left; simpl; tauto. Qed.
  Lemma Inst_P f : Inst f (fml_subst (sub2 (tapp0 s_zero) (tapp0 s_zero)) ax_P).
  Proof. apply: Inst_intro; left; simpl; tauto. Qed.
  Lemma Inst_add f A a : Inst f (fml_subst (sub2 A a) ax_add).
  Proof. apply: Inst_intro; left; simpl; tauto. Qed.
  Lemma Inst_chain f A : Inst f (fml_subst (sub2 A A) ax_chain).
  Proof. apply: Inst_intro; left; simpl; tauto. Qed.
  Lemma Inst_sqrt2 f A a : Inst f (fml_subst (sub2 A a) ax_sqrt2).
  Proof. apply: Inst_intro; left; simpl; tauto. Qed.
  Lemma Inst_root f : Inst f (fml_subst (sub2 (tapp0 s_zero) (tapp0 s_zero)) (ax_root f)).
  Proof. apply: Inst_intro; left; simpl; tauto. Qed.
  Lemma Inst_rep f K A a : (1 <= K)%N -> Inst f (fml_subst (sub2 A a) (ax_rep K)).
  Proof. by move=> HK; apply: Inst_intro; right; exists K. Qed.

End matrices.

(** * 4. Semantics of the macros and of the axioms

    Everything is stated for an arbitrary [numFieldType] R and an
    arbitrary valuation [ν : term X -> R] of terms (over any variable
    type X) which respects the ring symbols ([ring_hom ν]). For a ground
    valuation [val : gterm -> R] with [forall t, ring_ok val t] (the
    constraint (a) of Ambient.v), both [val] itself and
    [fun t => val (tsubst σ t)] are such valuations ([ring_hom_ground],
    [ring_hom_subst]). The semantic predicates apply ν only to terms
    built by constructors from the arguments, so for ν = val ∘ tsubst σ
    they are convertible to the same predicates for val at the
    substituted arguments; this gives the ground versions [inst_*_iff]. *)

Definition ring_okX {X : Type} {R : pzRingType} (ν : term X -> R) (t : term X) : Prop :=
  match t with
  | tapp0 s_zero => ν t = 0
  | tapp0 s_one => ν t = 1
  | tapp0 (s_int z) => ν t = Z_to_R z
  | tapp1 s_neg s => ν t = - ν s
  | tapp2 s_add s s' => ν t = ν s + ν s'
  | tapp2 s_mul s s' => ν t = ν s * ν s'
  | _ => True
  end.

Definition ring_hom {X : Type} {R : pzRingType} (ν : term X -> R) : Prop :=
  forall t, ring_okX ν t.

Lemma ring_hom_ground {R : pzRingType} (val : gterm -> R) :
  (forall t, ring_ok val t) -> ring_hom val.
Proof. by move=> H t; apply: H. Qed.

Lemma ring_hom_subst {X : Type} {R : pzRingType} (val : gterm -> R) (σ : X -> gterm) :
  (forall t, ring_ok val t) -> ring_hom (fun t => val (tsubst σ t)).
Proof.
  move=> H [ x | g | g t | g s t ].
  - by [].
  - exact: (H (tapp0 g)).
  - exact: (H (tapp1 g (tsubst σ t))).
  - exact: (H (tapp2 g (tsubst σ s) (tsubst σ t))).
Qed.

Lemma Z_to_R_int {R : pzRingType} (i : int) : Z_to_R (int_to_Z i) = i%:~R :> R.
Proof.
  case: i => n; rewrite /Z_to_R /int_to_Z.
  - rewrite Nat2Z.id (_ : Z.to_nat (Z.opp (Z.of_nat n)) = 0%N); first lia.
    by rewrite ?mulr0n subr0.
  - rewrite (_ : Z.to_nat (Z.opp (Z.of_nat n.+1)) = 0%N); first lia.
    rewrite (_ : Z.to_nat (Z.opp (Z.opp (Z.of_nat n.+1))) = n.+1); first lia.
    by rewrite ?mulr0n sub0r.
Qed.

(** ** Algebra in a commutative unit ring *)

Section unit_alg.

  Variable U : comUnitRingType.
  Implicit Types a b c d : U.

  Lemma divr_addE a b c d : b \is a GRing.unit -> d \is a GRing.unit ->
    (a * d + c * b) / (b * d) = a / b + c / d.
  Proof.
    move=> Hb Hd; rewrite invrM //.
    have -> : (a * d + c * b) * (d^-1 * b^-1) = a * (d * d^-1) * b^-1 + c * (b * b^-1) * d^-1 by ring.
    by rewrite !mulrV // !mulr1.
  Qed.

  Lemma divr_mulE a b c d : b \is a GRing.unit -> d \is a GRing.unit ->
    (a * c) / (b * d) = (a / b) * (c / d).
  Proof. by move=> Hb Hd; rewrite invrM //; ring. Qed.

  Lemma divr_eqE a b c d : b \is a GRing.unit -> d \is a GRing.unit ->
    a / b = c / d <-> a * d = c * b.
  Proof.
    move=> Hb Hd.
    have Hbd : b * d \is a GRing.unit by rewrite unitrM Hb Hd.
    have E1 : a / b * (b * d) = a * d by rewrite mulrA divrK.
    have E2 : c / d * (b * d) = c * b by rewrite [b * d]mulrC mulrA divrK.
    rewrite -E1 -E2; split => [ -> // | ]; exact: (mulIr Hbd).
  Qed.

  Lemma divr_divE a b c d : b \is a GRing.unit -> c \is a GRing.unit -> d \is a GRing.unit ->
    (a / b) / (c / d) = (a * d) / (b * c).
  Proof.
    move=> Hb Hc Hd; have Hd' : d^-1 \is a GRing.unit by rewrite unitrV.
    rewrite (@invrM _ c d^-1) // invrK (@invrM _ b c) //; ring.
  Qed.

  Lemma divr_cancelE u a b : u \is a GRing.unit -> b \is a GRing.unit -> (u * a) / (u * b) = a / b.
  Proof.
    move=> Hu Hb; rewrite invrM //.
    have -> : u * a * (b^-1 * u^-1) = a * b^-1 * (u * u^-1) by ring.
    by rewrite mulrV // mulr1.
  Qed.

  Lemma invr_divE a b : a \is a GRing.unit -> b \is a GRing.unit -> (a / b)^-1 = b / a.
  Proof.
    move=> Ha Hb; have Hb' : b^-1 \is a GRing.unit by rewrite unitrV.
    by rewrite (@invrM _ a b^-1) // invrK.
  Qed.

End unit_alg.

(** ** Algebra in R(sqrt2) *)

Section qe_alg.

  Variable R : numFieldType.
  Implicit Types (x y : qe R) (d : R).

  Lemma qe_of_unit d : d != 0 -> qe_of d \is a GRing.unit.
  Proof.
    by move=> Hd; rewrite qe_unitE /qe_norm /= expr0n /= mulr0 subr0 sqrf_eq0.
  Qed.

  Lemma qe_of_eq0 d : (qe_of d == 0) = (d == 0).
  Proof.
    apply/eqP/eqP => [ H | -> ] //; by case: (QE_inj H).
  Qed.

  Lemma qe_div_real x d : d != 0 -> x / qe_of d = QE (qre x / d) (qim x / d).
  Proof.
    move=> Hd; rewrite qe_invE /qe_inv /qe_norm /= expr0n /= mulr0 subr0 sqrf_eq0 Hd /=.
    case: x => a b; rewrite qe_mulE /=; congr QE; field; exact: Hd.
  Qed.

  Lemma qe_e_div_real sg x d : d != 0 -> qe_e sg (x / qe_of d) = qe_e sg x / qe_of d.
  Proof.
    move=> Hd; rewrite !qe_div_real //; case: sg => //.
    by case: x => a b; rewrite /qe_e /qe_conj /= mulNr.
  Qed.

  Lemma qe_e_eq0 sg x : (qe_e sg x == 0) = (x == 0).
  Proof.
    case: sg => //; case: x => a b; rewrite /qe_e /qe_conj /=.
    apply/eqP/eqP => H; case: (QE_inj H) => ->.
    - by move/eqP; rewrite oppr_eq0 => /eqP ->.
    - by move=> ->; rewrite oppr0.
  Qed.

  Lemma qe_eK sg x : qe_e sg (qe_e sg x) = x.
  Proof. by case: sg => //; apply: qe_conjK. Qed.

  (* Z0: if 2 is not a square in R, every nonzero element of R(sqrt2) is a unit *)
  Lemma qe_unit_neq0 : (forall z : R, z * z <> 2%:R) -> forall x, x != 0 -> x \is a GRing.unit.
  Proof.
    move=> HZ0 [ a b ] Hx; rewrite qe_unitE /qe_norm /=; apply/eqP => N.
    case: (eqVneq b 0) => Hb.
    - subst b; move: N; rewrite expr0n /= mulr0 subr0 => /eqP; rewrite sqrf_eq0 => /eqP Ha.
      by move: Hx; rewrite Ha eqxx.
    - apply: (HZ0 (a / b)).
      have E : a ^+ 2 = 2%:R * b ^+ 2 by apply/eqP; rewrite -subr_eq0; apply/eqP.
      rewrite -[_ * _]/((a / b) * (a / b)) -mulrA [b^-1 * _]mulrC !mulrA -expr2 E.
      by field.
  Qed.

  Lemma qe_e_unit sg x : x \is a GRing.unit -> qe_e sg x \is a GRing.unit.
  Proof.
    case: sg => //; case: x => a b; rewrite !qe_unitE /qe_norm /qe_e /qe_conj /=.
    by rewrite sqrrN.
  Qed.

  Lemma qe_intE' (i : int) : i%:~R = qe_of (i%:~R : R).
  Proof. exact: qe_intE. Qed.

  Lemma qe_natE' (n : nat) : n%:R = qe_of (n%:R : R).
  Proof. exact: qe_natE. Qed.

  Lemma qe_rat_QE (a b : rat) : qe_rat (QE a b) = QE (ratr a) (ratr b) :> qe R.
  Proof. by []. Qed.

  Lemma qe_rat_aE : qe_rat (aE : qe rat) = aE :> qe R.
  Proof.
    have H1 : forall n : nat, ratr (- (n%:R : rat)) = - (n%:R : R) by move=> n; rewrite rmorphN; congr (- _); exact: ratr_nat.
    have H2 : forall n : nat, ratr (n%:R : rat) = n%:R :> R by move=> n; exact: ratr_nat.
    exact: (congr2 QE (H1 _) (H2 _)).
  Qed.

End qe_alg.

(** the case of three finite points of [ADDrel] *)
Lemma ADDrel_SSS (U : comNzRingType) (x1 y1 x2 y2 x3 y3 : qe U) :
  ADDrel (Some (x1, y1)) (Some (x2, y2)) (Some (x3, y3)) <->
     (x1 <> x2 /\ (x3 + x1 + x2) * (x2 - x1) ^+ 2 = (y2 - y1) ^+ 2
               /\ (y3 + y1) * (x2 - x1) = (y2 - y1) * (x1 - x3))
  \/ (x1 = x2 /\ y1 = y2 /\ y1 <> 0
               /\ (x3 + 2%:R * x1) * (2%:R * y1) ^+ 2 = (3%:R * x1 ^+ 2 + aE) ^+ 2
               /\ (y3 + y1) * (2%:R * y1) = (3%:R * x1 ^+ 2 + aE) * (x1 - x3)).
Proof.
  rewrite /ADDrel; split.
  - by case=> [ [ _ [ _ ] ] // | [ x3' [ y3' [ [ <- <- ] H ] ] ] ].
  - by move=> H; right; exists x3, y3.
Qed.

(** ** Semantics of terms, R_F and F_R *)

Create HintDb frd.

Section sem_macros.

  Variables (X : Type) (R : numFieldType) (ν : term X -> R).
  Hypothesis Hν : ring_hom ν.

  Implicit Types (s t b : term X) (x y : RF X) (z w : FR X).

  Lemma nu_tz : ν tz = 0.               Proof using Hν. exact: (Hν tz). Qed.
  Lemma nu_to : ν to = 1.               Proof using Hν. exact: (Hν to). Qed.
  Lemma nu_ti i : ν (ti i) = i%:~R.     Proof using Hν. by rewrite -Z_to_R_int; exact: (Hν (ti i)). Qed.
  Lemma nu_ti_nat n : ν (ti n%:R) = n%:R.  Proof using Hν. by rewrite nu_ti natz. Qed.
  Lemma nu_tadd s t : ν (tadd s t) = ν s + ν t.  Proof using Hν. exact: (Hν (tadd s t)). Qed.
  Lemma nu_tmul s t : ν (tmul s t) = ν s * ν t.  Proof using Hν. exact: (Hν (tmul s t)). Qed.
  Lemma nu_tneg t : ν (tneg t) = - ν t.          Proof using Hν. exact: (Hν (tneg t)). Qed.
  Lemma nu_tsub s t : ν (tsub s t) = ν s - ν t.  Proof using Hν. by rewrite /tsub nu_tadd nu_tneg. Qed.

  Definition rfv x : qe R := QE (ν x.1) (ν x.2).
  Definition frv z : qe R := rfv z.1 / rfv z.2.
  Definition frd z : bool := rfv z.2 \is a GRing.unit.

  Lemma rfv_add x y : rfv (rf_add x y) = rfv x + rfv y.
  Proof using Hν. by rewrite /rfv /= !nu_tadd qe_addE. Qed.
  Lemma rfv_mul x y : rfv (rf_mul x y) = rfv x * rfv y.
  Proof using Hν. by rewrite /rfv /= !nu_tadd !nu_tmul nu_ti_nat qe_mulE. Qed.
  Lemma rfv_neg x : rfv (rf_neg x) = - rfv x.
  Proof using Hν. by rewrite /rfv /= !nu_tneg qe_oppE. Qed.
  Lemma rfv_of t : rfv (rf_of t) = qe_of (ν t).
  Proof using Hν. by rewrite /rfv /= nu_tz. Qed.
  Lemma rfv0 : rfv rf0 = 0.
  Proof using Hν. by rewrite /rfv /= nu_tz. Qed.
  Lemma rfv1 : rfv rf1 = 1.
  Proof using Hν. by rewrite /rfv /= nu_tz nu_to. Qed.
  Lemma rfv_int i : rfv (rf_int i) = i%:~R.
  Proof using Hν. by rewrite rfv_of nu_ti qe_intE. Qed.
  Lemma rfv_pow x n : rfv (rf_pow x n) = rfv x ^+ n.
  Proof using Hν. elim: n => [ | n IH ]; first exact: rfv1. by rewrite /rf_pow iterS -/(rf_pow x n) rfv_mul IH exprS. Qed.
  Lemma rfv_e sg x : rfv (rf_e sg x) = qe_e sg (rfv x).
  Proof using Hν. by case: sg; rewrite /rfv //= nu_tneg. Qed.

  Lemma f_all_iff (l : list (fml X)) : fml_holds ν (f_all l) <-> forall A, List.In A l -> fml_holds ν A.
  Proof using Hν.
    elim: l => [ | A l IH ] /=; first by split.
    rewrite IH; split.
    - by case=> HA Hl B [ <- | HB ]; auto.
    - by move=> H; split; [ apply: H; left | move=> B HB; apply: H; right ].
  Qed.

  Lemma f_any_iff (l : list (fml X)) : fml_holds ν (f_any l) <-> exists A, List.In A l /\ fml_holds ν A.
  Proof using Hν.
    elim: l => [ | A l IH ] /=; first by split => // [] [ ? [] ].
    rewrite IH; split.
    - case=> [ HA | [ B [ HB1 HB2 ] ] ]; [ by exists A; auto | by exists B; auto ].
    - by case=> B [ [ <- | HB ] HB2 ]; [ left | right; exists B ].
  Qed.

  Lemma eqRF_iff x y : fml_holds ν (eqRF x y) <-> rfv x = rfv y.
  Proof using Hν.
    rewrite /eqRF /rfv /=; split => [ [ -> -> ] // | H ].
    by case: (QE_inj H).
  Qed.

  Lemma neRF_iff x y : fml_holds ν (neRF x y) <-> rfv x <> rfv y.
  Proof using Hν.
    rewrite /neRF /rfv /=; split.
    - by case=> H E; case: (QE_inj E).
    - move=> H; case: (eqVneq (ν x.1) (ν y.1)) => [ E1 | /eqP ]; last by left.
      by right => E2; apply: H; rewrite E1 E2.
  Qed.

  Lemma eqFR_iff z w : frd z -> frd w -> fml_holds ν (eqFR z w) <-> frv z = frv w.
  Proof using Hν. by move=> Hz Hw; rewrite eqRF_iff !rfv_mul divr_eqE. Qed.

  Lemma neFR_iff z w : frd z -> frd w -> fml_holds ν (neFR z w) <-> frv z <> frv w.
  Proof using Hν. by move=> Hz Hw; rewrite neRF_iff !rfv_mul divr_eqE. Qed.

  (** fractions *)

  Lemma frd_add z w : frd z -> frd w -> frd (fr_add z w).
  Proof using Hν. by rewrite /frd /= rfv_mul unitrM => -> ->. Qed.
  Lemma frd_mul z w : frd z -> frd w -> frd (fr_mul z w).
  Proof using Hν. by rewrite /frd /= rfv_mul unitrM => -> ->. Qed.
  Lemma frd_neg z : frd z -> frd (fr_neg z).
  Proof using Hν. by []. Qed.
  Lemma frd_sub z w : frd z -> frd w -> frd (fr_sub z w).
  Proof using Hν. by move=> Hz Hw; apply: frd_add. Qed.
  Lemma frd_sq z : frd z -> frd (fr_sq z).
  Proof using Hν. by move=> Hz; apply: frd_mul. Qed.
  Lemma frd_div z w : frd z -> rfv w.1 \is a GRing.unit -> frd (fr_div z w).
  Proof using Hν. by rewrite /frd /= rfv_mul unitrM => -> ->. Qed.
  Lemma frd_of x : frd (fr_of x).
  Proof using Hν. by rewrite /frd /= rfv1 unitr1. Qed.
  Lemma frd0 : frd fr0.
  Proof using Hν. exact: frd_of. Qed.
  Lemma frd_nat n : frd (fr_nat n).
  Proof using Hν. exact: frd_of. Qed.

  Lemma frv_add z w : frd z -> frd w -> frv (fr_add z w) = frv z + frv w.
  Proof using Hν. by move=> Hz Hw; rewrite /frv /= rfv_add !rfv_mul divr_addE. Qed.
  Lemma frv_mul z w : frd z -> frd w -> frv (fr_mul z w) = frv z * frv w.
  Proof using Hν. by move=> Hz Hw; rewrite /frv /= !rfv_mul divr_mulE. Qed.
  Lemma frv_neg z : frv (fr_neg z) = - frv z.
  Proof using Hν. by rewrite /frv /= rfv_neg mulNr. Qed.
  Lemma frv_sub z w : frd z -> frd w -> frv (fr_sub z w) = frv z - frv w.
  Proof using Hν. by move=> Hz Hw; rewrite /fr_sub frv_add ?frv_neg. Qed.
  Lemma frv_sq z : frd z -> frv (fr_sq z) = frv z * frv z.
  Proof using Hν. by move=> Hz; rewrite /fr_sq frv_mul. Qed.
  Lemma frv_div z w : frd z -> rfv w.1 \is a GRing.unit -> frd w -> frv (fr_div z w) = frv z / frv w.
  Proof using Hν. by move=> Hz Hw1 Hw2; rewrite /frv /= !rfv_mul divr_divE. Qed.
  Lemma frv_of x : frv (fr_of x) = rfv x.
  Proof using Hν. by rewrite /frv /= rfv1 divr1. Qed.
  Lemma frv0 : frv fr0 = 0.
  Proof using Hν. by rewrite /fr0 frv_of rfv0. Qed.
  Lemma frv_nat n : frv (fr_nat n) = n%:R.
  Proof using Hν. by rewrite /fr_nat frv_of rfv_int qe_natE qe_intE. Qed.

  Lemma frd_rat c : frd (fr_rat c).
  Proof using Hν.
    rewrite /frd /= rfv_int qe_intE qe_of_unit // intr_eq0 mulf_neq0 //; exact: denq_neq0.
  Qed.

  Lemma frv_rat c : frv (fr_rat c) = qe_rat c.
  Proof using Hν.
    have Ha : (denq (qre c))%:~R != 0 :> R by rewrite intr_eq0 denq_neq0.
    have Hb : (denq (qim c))%:~R != 0 :> R by rewrite intr_eq0 denq_neq0.
    have Hd : (denq (qre c) * denq (qim c))%:~R != 0 :> R by rewrite intrM mulf_neq0.
    rewrite /frv /= rfv_int qe_intE (qe_div_real _ Hd).
    rewrite /rfv /= !nu_ti /qe_rat /qe_map /ratr !intrM.
    by congr QE; field; rewrite Ha Hb.
  Qed.

  Lemma frd_aE : frd fr_aE.
  Proof using Hν. exact: frd_rat. Qed.
  Lemma frv_aE : frv fr_aE = aE.
  Proof using Hν. by rewrite /fr_aE frv_rat qe_rat_aE. Qed.

  (* Beware: unifying [fr_nat _] or [fr_rat _] with [fr_aE] computes with
     the rational constants of aE; hence frd_aE / frv_aE are tried first
     and frd_rat is not a hint. *)
  #[local] Hint Resolve frd_aE | 0 : frd.
  #[local] Hint Resolve frd_add frd_mul frd_neg frd_sub frd_sq frd_of frd0 frd_nat : frd.

  Ltac frv_rw := repeat first [ rewrite frv_aE | rewrite frv0 | rewrite frv_add | rewrite frv_mul
                              | rewrite frv_sub | rewrite frv_sq | rewrite frv_neg | rewrite frv_nat ].

  (* closes the side conditions frd _ (and only those) *)
  Ltac frd_tac := try match goal with |- is_true (frd _) => solve [ auto 8 with frd ] end.

  (** ** Points *)

  Definition Xv b : qe R := QE (ν (tco cx0 b)) (ν (tco cx1 b)) / qe_of (ν (tco cx2 b)).
  Definition Yv b : qe R := QE (ν (tco cy0 b)) (ν (tco cy1 b)) / qe_of (ν (tco cy2 b)).

  (* T_b, with T_0 = O *)
  Definition Tv b : pt R := if ν b == 0 then None else Some (Xv b, Yv b).

  (* the meaning of ax_coord at b *)
  Definition coordOK b : Prop :=
    ν b = 0 \/
    (   ν (tco cx2 b) != 0 /\ ν (tco cy2 b) != 0
     /\ QE (ν (tco cx0 b)) (ν (tco cx1 b)) != 0 /\ QE (ν (tco cy0 b)) (ν (tco cy1 b)) != 0
     /\ on_curve (Xv b, Yv b)).

  Lemma frd_tX b : ν (tco cx2 b) != 0 -> frd (tX b).
  Proof using Hν. by move=> H; rewrite /frd /= rfv_of qe_of_unit. Qed.
  Lemma frd_tY b : ν (tco cy2 b) != 0 -> frd (tY b).
  Proof using Hν. by move=> H; rewrite /frd /= rfv_of qe_of_unit. Qed.
  Lemma frv_tX b : frv (tX b) = Xv b.
  Proof using Hν. by rewrite /frv /= rfv_of. Qed.
  Lemma frv_tY b : frv (tY b) = Yv b.
  Proof using Hν. by rewrite /frv /= rfv_of. Qed.

  Lemma Tv_eq0 b : ν b = 0 -> Tv b = None.
  Proof using Hν. by rewrite /Tv => ->; rewrite eqxx. Qed.
  Lemma Tv_neq0 b : ν b != 0 -> Tv b = Some (Xv b, Yv b).
  Proof using Hν. by rewrite /Tv => /negbTE ->. Qed.

  Lemma onE_iff p : frd p.1 -> frd p.2 -> fml_holds ν (onE p) <-> on_curve (frv p.1, frv p.2).
  Proof using Hν.
    move=> H1 H2; rewrite /onE eqFR_iff; frd_tac.
    all: frv_rw; frd_tac.
    by rewrite /on_curve /= !exprS expr0 mulr1.
  Qed.

  Lemma ADDfin_iff p1 p2 p3 :
    frd p1.1 -> frd p1.2 -> frd p2.1 -> frd p2.2 -> frd p3.1 -> frd p3.2 ->
    fml_holds ν (ADDfin p1 p2 p3) <->
    ADDrel (Some (frv p1.1, frv p1.2)) (Some (frv p2.1, frv p2.2)) (Some (frv p3.1, frv p3.2)).
  Proof using Hν.
    case: p1 p2 p3 => [ x1 y1 ] [ x2 y2 ] [ x3 y3 ].
    rewrite ADDrel_SSS /ADDfin; cbv zeta; cbn [fml_holds fst snd] => H1 H2 H3 H4 H5 H6.
    rewrite !neFR_iff ?eqFR_iff; frd_tac.
    all: frv_rw; frd_tac.
    by rewrite !expr2.
  Qed.

  Lemma NEGfin_iff p1 p2 : frd p1.1 -> frd p1.2 -> frd p2.1 -> frd p2.2 ->
    fml_holds ν (NEGfin p1 p2) <-> frv p1.1 = frv p2.1 /\ frv p2.2 = - frv p1.2.
  Proof using Hν.
    move=> H1 H2 H3 H4; rewrite /NEGfin; cbn [fml_holds].
    rewrite !eqFR_iff ?frv_neg //; frd_tac.
  Qed.

  #[local] Hint Resolve frd_rat frd_tX frd_tY : frd.

  Lemma f_all_map_iff {T : Type} (g : T -> fml X) (l : list T) :
    fml_holds ν (f_all (List.map g l)) <-> forall k, List.In k l -> fml_holds ν (g k).
  Proof using Hν.
    rewrite f_all_iff; split => H.
    - by move=> k Hk; apply: H; apply: List.in_map.
    - by move=> A /List.in_map_iff [ k [ <- Hk ] ]; apply: H.
  Qed.

  Lemma f_any_map_iff {T : Type} (g : T -> fml X) (l : list T) :
    fml_holds ν (f_any (List.map g l)) <-> exists k, List.In k l /\ fml_holds ν (g k).
  Proof using Hν.
    rewrite f_any_iff; split.
    - by case=> A [ /List.in_map_iff [ k [ <- Hk ] ] HA ]; exists k.
    - by case=> k [ Hk HA ]; exists (g k); split => //; apply: List.in_map.
  Qed.

  (** ** ax_coord *)

  Lemma onE_tP b : ν (tco cx2 b) != 0 -> ν (tco cy2 b) != 0 ->
    fml_holds ν (onE (tP b)) <-> on_curve (Xv b, Yv b).
  Proof using Hν. by move=> Hx Hy; rewrite onE_iff /tP /= ?frv_tX ?frv_tY; frd_tac. Qed.

  Lemma coord_holds_iff b : fml_holds ν (coord_fml b) <-> coordOK b.
  Proof using Hν.
    rewrite /coord_fml /coordOK; cbn [fml_holds]; rewrite !nu_tz !neRF_iff rfv0.
    split => [ [ -> | [ Hx [ Hy [ Hx' [ Hy' Hc ] ] ] ] ] | [ -> | [ Hx [ Hy [ Hx' [ Hy' Hc ] ] ] ] ] ];
      [ by left | right | by left | right ].
    - have Hx2 : ν (tco cx2 b) != 0 by apply/eqP.
      have Hy2 : ν (tco cy2 b) != 0 by apply/eqP.
      split; [ done | split; [ done | split; [ exact/eqP | split; [ exact/eqP | ] ] ] ].
      by rewrite -onE_tP.
    - split; [ exact/eqP | split; [ exact/eqP | split; [ exact/eqP | split; [ exact/eqP | ] ] ] ].
      by rewrite onE_tP.
  Qed.

  Lemma coordOK_nz b : coordOK b -> ν b != 0 ->
    ν (tco cx2 b) != 0 /\ ν (tco cy2 b) != 0
    /\ QE (ν (tco cx0 b)) (ν (tco cx1 b)) != 0 /\ QE (ν (tco cy0 b)) (ν (tco cy1 b)) != 0.
  Proof using Hν. by case=> [ -> | [ ? [ ? [ ? [ ? _ ] ] ] ] ]; [ rewrite eqxx | ]. Qed.

  (** ** ax_P *)

  Variable D : FixedData.

  Lemma P_holds_iff : coordOK to -> fml_holds ν (P_fml D X) <-> Tv to = pt_rat (Pgen D).
  Proof using Hν.
    have H1 : ν to != 0 by rewrite nu_to oner_eq0.
    move=> /coordOK_nz /(_ H1) [ Hx [ Hy _ ] ].
    rewrite (Tv_neq0 H1) /P_fml; case: (Pgen D) => [ [ x y ] | ]; cbn [fml_holds pt_rat]; last by split.
    rewrite !eqFR_iff ?frv_tX ?frv_tY ?frv_rat; frd_tac.
    split => [ [ -> -> ] // | H ].
    split; [ exact: (congr1 (fun p => if p is Some q then q.1 else Xv to) H)
           | exact: (congr1 (fun p => if p is Some q then q.2 else Yv to) H) ].
  Qed.

  (** ** ax_add *)

  Definition AddSem a a' : Prop :=
       ν a = 0 \/ ν a' = 0
    \/ (ν a + ν a' = 0 /\ Xv a = Xv a' /\ Yv a' = - Yv a)
    \/ (ν a + ν a' != 0
        /\ ADDrel (Some (Xv a, Yv a)) (Some (Xv a', Yv a')) (Some (Xv (tadd a a'), Yv (tadd a a')))).

  Lemma add_holds_iff a a' : coordOK a -> coordOK a' -> coordOK (tadd a a') ->
    fml_holds ν (add_fml a a') <-> AddSem a a'.
  Proof using Hν.
    rewrite /add_fml /AddSem; cbn [fml_holds]; rewrite !nu_tz nu_tadd => Ca Ca' Caa.
    case: (eqVneq (ν a) 0) => Ha; first by split => _; left.
    case: (eqVneq (ν a') 0) => Ha'; first by split => _; right; left.
    move: Ca => /coordOK_nz /(_ Ha) [ Hx [ Hy _ ] ].
    move: Ca' => /coordOK_nz /(_ Ha') [ Hx' [ Hy' _ ] ].
    have E1 : fml_holds ν (NEGfin (tP a) (tP a')) <-> Xv a = Xv a' /\ Yv a' = - Yv a.
    { by rewrite NEGfin_iff /tP /= ?frv_tX ?frv_tY; frd_tac. }
    have E2 : ν a + ν a' != 0 ->
      fml_holds ν (ADDfin (tP a) (tP a') (tP (tadd a a'))) <->
      ADDrel (Some (Xv a, Yv a)) (Some (Xv a', Yv a')) (Some (Xv (tadd a a'), Yv (tadd a a'))).
    { move=> Hs; move: Caa => /coordOK_nz; rewrite nu_tadd => /(_ Hs) [ Hx'' [ Hy'' _ ] ].
      by rewrite ADDfin_iff /tP /= ?frv_tX ?frv_tY; frd_tac. }
    have nA : ν a <> 0 by apply/eqP.
    have nA' : ν a' <> 0 by apply/eqP.
    split.
    - case=> [ // | [ // | [ [ Hs HN ] | [ Hs HA ] ] ] ]; right; right; [ left | right ].
      + by split => //; apply/E1.
      + have Hs' : ν a + ν a' != 0 by apply/eqP.
        by split => //; apply/(E2 Hs').
    - case=> [ // | [ // | [ [ Hs HN ] | [ Hs HA ] ] ] ]; right; right; [ left | right ].
      + by split => //; apply/E1.
      + by split; [ apply/eqP | apply/(E2 Hs) ].
  Qed.

  (* with functionality of the coordinate functions, ax_add gives the
     group law T_{a+a'} = T_a + T_{a'} in the form of [ADDrel] *)
  Lemma add_ADDrel a a' :
    (forall c t t', ν t = ν t' -> ν (tco c t) = ν (tco c t')) ->
    AddSem a a' -> ADDrel (Tv a) (Tv a') (Tv (tadd a a')).
  Proof using Hν.
    move=> Hf HA.
    have TvE : forall t t', ν t = ν t' -> Tv t = Tv t'.
    { by move=> t t' E; rewrite /Tv /Xv /Yv E !(Hf _ t t'). }
    case: (eqVneq (ν a) 0) => Ha.
    { by rewrite (Tv_eq0 Ha) /=; apply: TvE; rewrite nu_tadd Ha add0r. }
    case: (eqVneq (ν a') 0) => Ha'.
    { have E : ν (tadd a a') = ν a by rewrite nu_tadd Ha' addr0.
      rewrite (Tv_eq0 Ha') (TvE _ _ E).
      by case: (Tv a) => [ [] | ]. }
    rewrite (Tv_neq0 Ha) (Tv_neq0 Ha').
    case: HA => [ /eqP | [ /eqP | [ [ Hs [ HX HY ] ] | [ Hs HAd ] ] ] ].
    - by rewrite (negbTE Ha).
    - by rewrite (negbTE Ha').
    - have E : ν (tadd a a') = 0 by rewrite nu_tadd.
      by rewrite (Tv_eq0 E); left; rewrite HX HY opprK.
    - have E : ν (tadd a a') != 0 by rewrite nu_tadd.
      by rewrite (Tv_neq0 E).
  Qed.

  (** ** ax_chain *)

  Definition QvC t (k : nat) : qe R * qe R :=
    if (k < fd_m D)%N
    then (QE (ν (tch k cx0 t)) (ν (tch k cx1 t)) / qe_of (ν (tch k cx2 t)),
          QE (ν (tch k cy0 t)) (ν (tch k cy1 t)) / qe_of (ν (tch k cy2 t)))
    else (Xv t, Yv t).

  Definition ChainSem t : Prop :=
    ν t = 0 \/
    (   (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ν (tch k cx2 t) != 0 /\ ν (tch k cy2 t) != 0)
     /\ on_curve (QvC t 1)
     /\ (forall k, (1 <= k)%N -> (k < fd_m D)%N ->
           ADDrel (Some (QvC t k)) (Some (QvC t 1)) (Some (QvC t k.+1)))).

  Lemma chain_idx_spec k : List.In k (chain_idx D) <-> (1 <= k)%N /\ (k < fd_m D)%N.
  Proof using Hν.
    rewrite /chain_idx In_mem mem_iota; case: (fd_m D) => [ | m ] /=.
    - rewrite addn0; split.
      + by case/andP; case: k.
      + by case=> _; rewrite ltn0.
    - rewrite add1n; split; [ by case/andP | by case=> -> -> ].
  Qed.

  Lemma Qf_sem t k :
    ((k < fd_m D)%N -> ν (tch k cx2 t) != 0 /\ ν (tch k cy2 t) != 0) ->
    (~~ (k < fd_m D)%N -> ν (tco cx2 t) != 0 /\ ν (tco cy2 t) != 0) ->
    frd (Qf D t k).1 /\ frd (Qf D t k).2 /\ (frv (Qf D t k).1, frv (Qf D t k).2) = QvC t k.
  Proof using Hν.
    rewrite /Qf /QvC; case: ifP => Hk H1 H2.
    - have [ Hx Hy ] := H1 isT.
      by rewrite /cP /frd /frv /= !rfv_of !qe_of_unit.
    - have [ Hx Hy ] := H2 isT.
      by rewrite /tP frv_tX frv_tY; split; [ apply: frd_tX | split; [ apply: frd_tY | ] ].
  Qed.

  Lemma chain_holds_iff t : coordOK t -> fml_holds ν (chain_fml D t) <-> ChainSem t.
  Proof using Hν.
    rewrite /chain_fml /ChainSem; cbn [fml_holds]; rewrite nu_tz.
    case: (eqVneq (ν t) 0) => Ht; first by split => _; left.
    move=> /coordOK_nz /(_ Ht) [ Hx [ Hy _ ] ].
    have nT : ν t <> 0 by apply/eqP.
    have Hcases : forall k, (1 <= k)%N ->
        (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ν (tch k cx2 t) != 0 /\ ν (tch k cy2 t) != 0) ->
        frd (Qf D t k).1 /\ frd (Qf D t k).2 /\ (frv (Qf D t k).1, frv (Qf D t k).2) = QvC t k.
    { move=> k Hk1 Hd; apply: Qf_sem => // Hk; exact: Hd. }
    rewrite !f_all_map_iff.
    have Hden : (forall k, List.In k (chain_idx D) ->
                   fml_holds ν (f_and (f_ne (tch k cx2 t) tz) (f_ne (tch k cy2 t) tz))) <->
                (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ν (tch k cx2 t) != 0 /\ ν (tch k cy2 t) != 0).
    { split => H k.
      - move=> Hk1 Hk2; have /= [ H1 H2 ] := H k (proj2 (chain_idx_spec k) (conj Hk1 Hk2)).
        by move: H1 H2; rewrite nu_tz => /eqP H1 /eqP H2.
      - move=> /chain_idx_spec [ Hk1 Hk2 ]; have [ H1 H2 ] := H k Hk1 Hk2.
        by rewrite /= nu_tz; split; apply/eqP. }
    split.
    - case=> [ // | [ Hd [ Hon Hadd ] ] ]; right.
      have Hd' := proj1 Hden Hd.
      split; [ done | split ].
      + have [ F1 [ F2 E ] ] := Hcases 1%N isT Hd'.
        by rewrite -E -onE_iff.
      + move=> k Hk1 Hk2.
        have [ F1 [ F2 E1 ] ] := Hcases k Hk1 Hd'.
        have [ G1 [ G2 E2 ] ] := Hcases 1%N isT Hd'.
        have [ K1 [ K2 E3 ] ] := Hcases k.+1 isT Hd'.
        rewrite -E1 -E2 -E3 -ADDfin_iff //.
        by apply: Hadd; apply/chain_idx_spec.
    - case=> [ // | [ Hd' [ Hon Hadd ] ] ]; right.
      split; first exact/Hden.
      split.
      + have [ F1 [ F2 E ] ] := Hcases 1%N isT Hd'.
        by rewrite onE_iff // E.
      + move=> k /chain_idx_spec [ Hk1 Hk2 ].
        have [ F1 [ F2 E1 ] ] := Hcases k Hk1 Hd'.
        have [ G1 [ G2 E2 ] ] := Hcases 1%N isT Hd'.
        have [ K1 [ K2 E3 ] ] := Hcases k.+1 isT Hd'.
        by rewrite ADDfin_iff // E1 E2 E3; apply: Hadd.
  Qed.

  (** ** ax_sqrt2 *)

  Lemma sqrt2_holds_iff a b :
    fml_holds ν (sqrt2_fml a b) <-> ν b = 0 \/ ν a * ν a != 2%:R * (ν b * ν b).
  Proof using Hν.
    rewrite /sqrt2_fml; cbn [fml_holds]; rewrite !nu_tmul nu_ti_nat nu_tz.
    by split => [ [ -> | /eqP ] | [ -> | /eqP ] ]; auto.
  Qed.

  (** ** ax_root *)

  Lemma tm_of_poly_sem n (p : dio_polynomial (pos n) (pos 0)) :
    ν (tm_of_poly X p) = dp_evalR (fun v => ν (tapp0 (s_cst (pos2nat v)))) (fun _ => 0) p.
  Proof using Hν.
    elim: p => [ z | v | i | [] p Hp q Hq ] /=.
    - exact: (Hν (tapp0 (s_int z))).
    - by [].
    - exact: nu_tz.
    - by rewrite nu_tadd Hp Hq.
    - by rewrite nu_tmul Hp Hq.
  Qed.

  Lemma root_holds_iff (f : H10Z_PROBLEM) :
    fml_holds ν (root_fml X f) <->
    dp_evalR (fun v => ν (tapp0 (s_cst (pos2nat v)))) (fun _ => 0) (projT2 f) = 0.
  Proof using Hν. by rewrite /root_fml /= tm_of_poly_sem nu_tz. Qed.

  (** ** The truncated formal logarithm *)

  Lemma lamP_E K (N D' N' D'' : RF X) : (lamP K N D').2 = (lamP K N' D'').2.
  Proof using Hν. by elim: K => //= K ->. Qed.

  Lemma lamP_E_neq0 K (N D' : RF X) : (lamP K N D').2 != 0.
  Proof using Hν.
    elim: K => [ | K IH ] /=; first by [].

    by rewrite mulf_neq0 // /ct_den mulf_neq0 // denq_neq0.
  Qed.

  Lemma int_qe_unit (i : int) : i != 0 -> (i%:~R : qe R) \is a GRing.unit.
  Proof using Hν. by move=> Hi; rewrite qe_intE qe_of_unit // intr_eq0. Qed.

  Lemma ct_num_spec (n : nat) : rfv (ct_num n) = qe_rat (ct n) * (ct_den n)%:~R.
  Proof using Hν.
    have Hu : ((ct_den n)%:~R : qe R) \is a GRing.unit.
    { by apply: int_qe_unit; rewrite /ct_den mulf_neq0 // denq_neq0. }
    have := frv_rat (ct n); rewrite /frv /= rfv_int => <-.
    by rewrite /ct_num divrK.
  Qed.

  (* Lam_K(N, D) = E * D^K * l_K(N/D) *)
  Lemma lamP_spec K (N D' : RF X) : rfv D' \is a GRing.unit ->
    rfv (lamP K N D').1 = ((lamP K N D').2)%:~R * rfv D' ^+ K * ellK false K (rfv N / rfv D').
  Proof using Hν.
    move=> HD; elim: K => [ | K IH ].
    - by rewrite /= rfv0 /ellK big_geq // mulr0.
    - rewrite [lamP _ _ _]/= rfv_add !rfv_mul rfv_pow !rfv_int IH ct_num_spec.
      have -> : ellK false K.+1 (rfv N / rfv D') =
                ellK false K (rfv N / rfv D') + qe_rat (ct K.+1) * (rfv N / rfv D') ^+ K.+1.
      { by rewrite /ellK (big_nat_recr K.+1). }
      set Z := rfv N / rfv D'.
      have HN : rfv N = Z * rfv D' by rewrite /Z divrK.
      rewrite HN exprMn !exprS.
      cbn [fst snd]; rewrite intrM.
      move: (ellK false K Z) (qe_rat (ct K.+1)) ((lamP K N D').2%:~R : qe R) ((ct_den K.+1)%:~R : qe R) => l c e d.
      ring.
  Qed.

  Lemma lamN_spec K z : frd z ->
    rfv (lamN K z) = ((lamP K z.1 z.2).2)%:~R * rfv z.2 ^+ K * ellK false K (frv z).
  Proof using Hν. exact: lamP_spec. Qed.

  (** ** Under Z0 (2 is not a square in R), nonzero elements of R(sqrt2) are units *)

  Hypothesis HZ0 : forall x : R, x * x <> 2%:R.

  Lemma qe_unitZ (x : qe R) : x != 0 -> x \is a GRing.unit.
  Proof using HZ0. exact: qe_unit_neq0. Qed.

  Lemma unit_mul_neq0 (u x : qe R) : u \is a GRing.unit -> (u * x != 0) = (x != 0).
  Proof using Hν.
    move=> Hu; congr negb; apply/eqP/eqP => [ H | -> ]; last by rewrite mulr0.
    by apply: (mulrI Hu); rewrite H mulr0.
  Qed.

  (* l_K(za)/l_K(zh) - a, cleared *)
  Lemma prim_spec K a za zh : frd za -> frd zh -> ellK false K (frv zh) != 0 ->
    frd (prim K a za zh) /\
    frv (prim K a za zh) = ellK false K (frv za) / ellK false K (frv zh) - qe_of (ν a).
  Proof using HZ0 Hν.
    move=> Ha Hh Hl.
    have Hlu := qe_unitZ Hl.
    set E := ((lamP K za.1 za.2).2)%:~R : qe R.
    have HE : E \is a GRing.unit by apply: int_qe_unit; apply: lamP_E_neq0.
    have Hda : rfv za.2 ^+ K \is a GRing.unit by apply: unitrX.
    have Hdh : rfv zh.2 ^+ K \is a GRing.unit by apply: unitrX.
    have HU : E * rfv zh.2 ^+ K * rfv za.2 ^+ K \is a GRing.unit by rewrite !unitrM HE Hda Hdh.
    have Hden : rfv (prim K a za zh).2 = (E * rfv zh.2 ^+ K * rfv za.2 ^+ K) * ellK false K (frv zh).
    { rewrite /prim /= rfv_mul rfv_pow lamN_spec // (lamP_E K zh.1 zh.2 za.1 za.2) -/E; ring. }
    have Hnum : rfv (prim K a za zh).1 =
                (E * rfv zh.2 ^+ K * rfv za.2 ^+ K) * (ellK false K (frv za) - qe_of (ν a) * ellK false K (frv zh)).
    { rewrite /prim /= rfv_add rfv_neg !rfv_mul !rfv_pow rfv_of !lamN_spec //.
      rewrite (lamP_E K zh.1 zh.2 za.1 za.2) -/E; ring. }
    split.
    - by rewrite /frd Hden unitrM HU Hlu.
    - rewrite /frv Hden Hnum divr_cancelE // mulrBl mulrK //.
  Qed.

  (** ** Localization, formal points, z *)

  Lemma divr_mul_eq (n d y x : qe R) : d \is a GRing.unit -> (n / d * y = x) <-> (n * y = x * d).
  Proof using Hν.
    move=> Hd; split => H.
    - by rewrite -H mulrAC divrK.
    - by rewrite mulrAC H mulrK.
  Qed.

  (* alpha in r^i (R_F)_p at the branch s: alpha Y = r^i X with
     (Y0 + s B Y1) iota - 1 = r kappa; the witnesses are given by w *)
  Definition LOCv (i : nat) (r B : R) (s : sgn) (alpha : qe R) (w : wcomp -> R) : Prop :=
       alpha * QE (w wY0) (w wY1) = qe_of r ^+ i * QE (w wX0) (w wX1)
    /\ (w wY0 + (sgnz s)%:~R * B * w wY1) * w wiota - 1 = r * w wkappa.

  Lemma LOC_iff i (r B : term X) (s : sgn) z (W : wcomp -> term X) : frd z ->
    fml_holds ν (LOC i r B s z W) <-> LOCv i (ν r) (ν B) s (frv z) (fun c => ν (W c)).
  Proof using Hν.
    move=> Hz; rewrite /LOC /LOCv; cbn [fml_holds].
    rewrite eqRF_iff !rfv_mul rfv_pow rfv_of /frv divr_mul_eq //.
    rewrite ?nu_tsub ?nu_tmul ?nu_tadd ?nu_tmul ?nu_ti ?nu_to.
    by rewrite [rfv (W wY0, W wY1)]/rfv [rfv (W wX0, W wX1)]/rfv /=.
  Qed.

  Lemma tInvX_sem sg b : coordOK b -> ν b != 0 ->
    frd (tInvX sg b) /\ frv (tInvX sg b) = (qe_e sg (Xv b))^-1.
  Proof using HZ0 Hν.
    move=> /coordOK_nz H /H [ Hx2 [ Hy2 [ Hx0 Hy0 ] ] ].
    have Hu : qe_e sg (QE (ν (tco cx0 b)) (ν (tco cx1 b))) \is a GRing.unit.
    { exact/qe_e_unit/qe_unitZ. }
    split.
    - by rewrite /frd /= rfv_e.
    - rewrite /frv /= rfv_of rfv_e /Xv qe_e_div_real // invr_divE //; exact: qe_of_unit.
  Qed.

  Lemma tZ_sem sg b : coordOK b -> ν b != 0 ->
    frd (tZ sg b) /\ rfv (tZ sg b).1 \is a GRing.unit /\ frv (tZ sg b) = zpar sg (Tv b).
  Proof using HZ0 Hν.
    move=> Hc Hb; move: (Hc) => /coordOK_nz /(_ Hb) [ Hx2 [ Hy2 [ Hx0 Hy0 ] ] ].
    have Hux : qe_e sg (QE (ν (tco cx0 b)) (ν (tco cx1 b))) \is a GRing.unit.
    { exact/qe_e_unit/qe_unitZ. }
    have Huy : qe_e sg (QE (ν (tco cy0 b)) (ν (tco cy1 b))) \is a GRing.unit.
    { exact/qe_e_unit/qe_unitZ. }
    have Hx2u := qe_of_unit Hx2.
    have Hy2u := qe_of_unit Hy2.
    rewrite (Tv_neq0 Hb) /zpar /Xv /Yv !qe_e_div_real //.
    split; [ | split ].
    - by rewrite /frd /= rfv_mul rfv_of rfv_e unitrM Hx2u Huy.
    - by rewrite /= rfv_neg rfv_mul rfv_of rfv_e unitrN unitrM Hux Hy2u.
    - by rewrite /frv /= rfv_neg !rfv_mul !rfv_of !rfv_e !mulNr divr_divE.
  Qed.

  Definition FormalR (sg : bool) (r B : R) (s : sgn) (p : pt R) (w : wcomp -> R) : Prop :=
    match p with
    | None => True
    | Some (x, _) => LOCv 1 r B s (qe_e sg x)^-1 w
    end.

  Lemma FORMAL_iff sg b (r B : term X) (s : sgn) (W : wcomp -> term X) : coordOK b ->
    fml_holds ν (FORMAL sg b r B s W) <-> FormalR sg (ν r) (ν B) s (Tv b) (fun c => ν (W c)).
  Proof using HZ0 Hν.
    move=> Hc; rewrite /FORMAL; cbn [fml_holds]; rewrite nu_tz.
    case: (eqVneq (ν b) 0) => Hb.
    - by rewrite (Tv_eq0 Hb); split => // _; left.
    - have [ F E ] := tInvX_sem sg Hc Hb.
      rewrite (Tv_neq0 Hb) LOC_iff // E.
      split => [ [ E0 | H ] | H ]; [ by move: Hb; rewrite E0 eqxx | exact: H | by right ].
  Qed.

  Lemma withZ_iff sg b (k : FR X -> fml X) (P : qe R -> Prop) : coordOK b ->
    (forall z, frd z -> fml_holds ν (k z) <-> P (frv z)) ->
    fml_holds ν (withZ sg b k) <-> P (zpar sg (Tv b)).
  Proof using HZ0 Hν.
    move=> Hc Hk; rewrite /withZ; cbn [fml_holds]; rewrite nu_tz.
    case: (eqVneq (ν b) 0) => Hb.
    - rewrite (Tv_eq0 Hb); have := Hk fr0 frd0; rewrite frv0 => Hk0.
      change (zpar sg None) with (0 : qe R).
      split => [ [ [ _ H ] | [ H _ ] ] | H ]; [ exact/Hk0 | by [] | left; split => //; exact/Hk0 ].
    - have [ F [ _ E ] ] := tZ_sem sg Hc Hb.
      have := Hk _ F; rewrite E => HkZ.
      split => [ [ [ E0 _ ] | [ _ H ] ] | H ];
        [ by move: Hb; rewrite E0 eqxx | exact/HkZ | right; split; [ exact/eqP | exact/HkZ ] ].
  Qed.

  (** ** ax_rep K *)

  Section rep.

    Variables (K : nat) (A a : term X).

    Hypothesis Hc : forall t, coordOK t.

    (* u_1, u_2, u_3 = A v - u_1 - u_2 and the 13 members *)
    Definition uR (i : i3) : R :=
      match i with
      | I1 => ν (s1 K r_u1 A)
      | I2 => ν (s1 K r_u2 A)
      | I3 => ν A * ν (s1 K r_v A) - ν (s1 K r_u1 A) - ν (s1 K r_u2 A)
      end.

    Definition memR (j : mem13) : R :=
      match j with
      | mem_v => ν (s1 K r_v A)
      | mem_L i b => fd_L D b (uR i) (ν (s1 K r_v A))
      end.

    Lemma nu_tmem j : ν (tmem D K A j) = memR j.
    Proof using Hν.
      case: j => [ | [] b ]; rewrite /tmem /memR /uR /tL /tu //.
      all: by do 3 rewrite ?nu_tsub ?nu_tmul ?nu_ti.
    Qed.

    (* conditions (i) and (ii) of red:theory at the branch s of member j *)
    Definition BranchSem (j : mem13) (s : sgn) : Prop :=
      let r := ν (s1 K (r_r j) A) in let B := ν (s1 K (r_B j) A) in
      let h := s1 K (r_h j s) A in let j0 := s1 K (r_j0 j s) A in
      let w1 tg (c : wcomp) := ν (s1 K (r_W1 j s tg c) A) in
      let w2 tg (c : wcomp) := ν (s2 K (r_W2 j s tg c) A a) in
      let ha := tmul h a in let h4a := tmul (tsub h (ti 4)) a in
         ν h != 0
      /\ ν j0 != 0
      /\ FormalR false r B s (Tv h) (w1 tg_fh)
      /\ ellK false K (zpar false (Tv h)) != 0
      /\ FormalR false r B s (Tv ha) (w2 tg_fha)
      /\ LOCv K r B s (ellK false K (zpar false (Tv ha)) / ellK false K (zpar false (Tv h))
                       - qe_of (ν a)) (w2 tg_prim)
      /\ FormalR true r B s (Tv j0) (w1 tg_fj0)
      /\ FormalR true r B s (Tv h4a) (w2 tg_fh4a)
      /\ LOCv K r B s (zpar true (Tv h4a) / zpar true (Tv j0)) (w2 tg_alt).

    Lemma branch_holds_iff (j : mem13) (s : sgn) : fml_holds ν (branch_fml K A a j s) <-> BranchSem j s.
    Proof using HZ0 Hν Hc.
      rewrite /branch_fml /BranchSem; cbv zeta; cbn [fml_holds]; rewrite !nu_tz.
      set r := s1 K (r_r j) A; set B := s1 K (r_B j) A.
      set h := s1 K (r_h j s) A; set j0 := s1 K (r_j0 j s) A.
      case: (eqVneq (ν h) 0) => Hh.
      { by split => [ [] | [ /eqP ] ]. }
      case: (eqVneq (ν j0) 0) => Hj.
      { by split => [ [ _ [] ] | [ _ [ /eqP ] ] ]. }
      have [ FZh [ _ EZh ] ] := tZ_sem false (Hc h) Hh.
      have [ FZj [ UZj EZj ] ] := tZ_sem true (Hc j0) Hj.
      rewrite !FORMAL_iff //.
      (* the logarithm at h *)
      have El : fml_holds ν (neRF (lamN K (tZ false h)) rf0) <-> ellK false K (zpar false (Tv h)) != 0.
      { rewrite neRF_iff rfv0 lamN_spec // EZh.
        have Hu : ((lamP K (tZ false h).1 (tZ false h).2).2%:~R * rfv (tZ false h).2 ^+ K)
                    \is a GRing.unit.
        { rewrite unitrM unitrX // andbT; apply: int_qe_unit; apply: lamP_E_neq0. }
        rewrite -(unit_mul_neq0 _ Hu); split => [ H | /eqP // ]; exact/eqP. }
      (* the primary test *)
      have Ep : ellK false K (zpar false (Tv h)) != 0 ->
        fml_holds ν (withZ false (tmul h a) (fun za => LOC K r B s (prim K a za (tZ false h))
                                                    (fun c => s2 K (r_W2 j s tg_prim c) A a))) <->
        LOCv K (ν r) (ν B) s (ellK false K (zpar false (Tv (tmul h a))) / ellK false K (zpar false (Tv h))
                              - qe_of (ν a)) (fun c => ν (s2 K (r_W2 j s tg_prim c) A a)).
      { move=> Hl.
        refine (@withZ_iff false (tmul h a) _
                  (fun q : qe R => LOCv K (ν r) (ν B) s (ellK false K q / ellK false K (zpar false (Tv h)) - qe_of (ν a))
                                 (fun c => ν (s2 K (r_W2 j s tg_prim c) A a))) (Hc (tmul h a)) _).
        move=> z Hz.
        have Hl' : ellK false K (frv (tZ false h)) != 0 by rewrite EZh.
        have [ F E ] := @prim_spec K a z (tZ false h) Hz FZh Hl'.
        by rewrite LOC_iff // E EZh. }
      (* the alternate test *)
      have Ea : fml_holds ν (withZ true (tmul (tsub h (ti 4)) a)
                     (fun zb => LOC K r B s (fr_div zb (tZ true j0)) (fun c => s2 K (r_W2 j s tg_alt c) A a))) <->
        LOCv K (ν r) (ν B) s (zpar true (Tv (tmul (tsub h (ti 4)) a)) / zpar true (Tv j0))
             (fun c => ν (s2 K (r_W2 j s tg_alt c) A a)).
      { refine (@withZ_iff true (tmul (tsub h (ti 4)) a) _
                  (fun q : qe R => LOCv K (ν r) (ν B) s (q / zpar true (Tv j0))
                                 (fun c => ν (s2 K (r_W2 j s tg_alt c) A a))) (Hc (tmul (tsub h (ti 4)) a)) _).
        move=> z Hz.
        have Hd : frd (fr_div z (tZ true j0)) by apply: frd_div.
        by rewrite LOC_iff // frv_div // EZj. }
      have nh : ν h <> 0 by apply/eqP.
      have nj : ν j0 <> 0 by apply/eqP.
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

    Definition MemSem (j : mem13) : Prop :=
      let r := ν (s1 K (r_r j) A) in let B := ν (s1 K (r_B j) A) in
         (exists (eps : int) (k : nat), (eps = 1 \/ eps = -1) /\ k \in fd_Kset D
                                        /\ memR j = eps%:~R * k%:R * r)
      /\ r != 0
      /\ B * B - 2%:R = r * ν (s1 K (r_wB j) A)
      /\ 2%:R * B * ν (s1 K (r_iota' j) A) - 1 = r * ν (s1 K (r_kappa' j) A)
      /\ r * ν a != 1
      /\ (ν a = r * ν (s2 K (r_fz j) A a) \/ ν a * ν (s2 K (r_fy j) A a) - 1 = r * ν (s2 K (r_fz' j) A a))
      /\ (forall s : sgn, BranchSem j s).

    Lemma eks_spec (ek : int * nat) :
      List.In ek (eks D) <-> exists k, k \in fd_Kset D /\ (ek = (1, k) \/ ek = (-1, k)).
    Proof using Hν.
      rewrite /eks List.in_flat_map; split.
      - case=> k [ /In_mem Hk H ]; exists k; split => //.
        by case: H => [ <- | [ <- | [] ] ]; [ left | right ].
      - case=> k [ Hk H ]; exists k; split; first exact/In_mem.
        by case: H => ->; [ left | right; left ].
    Qed.

    Lemma mem_holds_iff j : fml_holds ν (mem_fml D K A a j) <-> MemSem j.
    Proof using HZ0 Hν Hc.
      rewrite /mem_fml /MemSem; cbv zeta; cbn [fml_holds].
      rewrite f_any_map_iff f_all_map_iff !nu_tz !nu_tsub !nu_tmul !nu_ti_nat nu_to.
      have Eb : (forall s : sgn, List.In s all_sgn -> fml_holds ν (branch_fml K A a j s)) <->
                (forall s : sgn, BranchSem j s).
      { split => H s; [ apply/branch_holds_iff/H; exact: all_sgn_spec | move=> _; exact/branch_holds_iff ]. }
      rewrite Eb.
      have Ee : (exists ek, List.In ek (eks D) /\ fml_holds ν (f_eq (tmem D K A j) (tmul (ti (ek.1 * (ek.2)%:Z)) (s1 K (r_r j) A)))) <->
                (exists (eps : int) (k : nat), (eps = 1 \/ eps = -1) /\ k \in fd_Kset D
                       /\ memR j = eps%:~R * k%:R * ν (s1 K (r_r j) A)).
      { cbn [fml_holds]; rewrite nu_tmem; split.
        - case=> [ [ eps k ] [ /eks_spec [ k' [ Hk' H ] ] ] ].
          rewrite nu_tmul nu_ti intrM /= => E.
          have [ He Hk ] : (eps = 1 \/ eps = -1) /\ k = k'.
          { by case: H => [ [ -> -> ] | [ -> -> ] ]; split; auto. }
          by exists eps, k; split; [ | split; [ rewrite Hk | exact: E ] ].
        - case=> eps [ k [ He [ Hk E ] ] ]; exists (eps, k); split.
          + by apply/eks_spec; exists k; split => //; case: He => ->; [ left | right ].
          + by rewrite nu_tmul nu_ti intrM /= E. }
      rewrite Ee.
      split => [ [ H1 [ H2 [ H3 [ H4 [ H5 [ H6 H7 ] ] ] ] ] ] | [ H1 [ H2 [ H3 [ H4 [ H5 [ H6 H7 ] ] ] ] ] ] ].
      - do 7 (try split) => //; try exact/eqP.
      - do 7 (try split) => //; try exact/eqP.
    Qed.

    Definition RepSem : Prop := ν (s1 K r_v A) != 0 /\ forall j, MemSem j.

    Lemma rep_holds_iff : fml_holds ν (rep_fml D K A a) <-> RepSem.
    Proof using HZ0 Hν Hc.
      rewrite /rep_fml /RepSem; cbn [fml_holds]; rewrite f_all_map_iff nu_tz.
      split => [ [ H1 H2 ] | [ H1 H2 ] ]; split.
      - exact/eqP.
      - by move=> j; apply/mem_holds_iff/H2; apply: all_mem13_spec.
      - exact/eqP.
      - by move=> j _; apply/mem_holds_iff.
    Qed.

  End rep.

End sem_macros.

(** ** Ground instances

    For a valuation [val : gterm -> R] satisfying (a), the ground
    instance of each matrix at the terms A, a ([sub2 A a]) means the
    semantic condition at A, a. These are the forms consumed by the
    standard model (R = rat) and by the ambient analysis (R = sQ). *)

Section ground.

  Variables (R : numFieldType) (val : gterm -> R) (D : FixedData).
  Hypothesis Hring : forall t, ring_ok val t.

  Lemma coordOK_subst {X} (σ : X -> gterm) :
    (forall t, coordOK val t) -> forall t, coordOK (fun u => val (tsubst σ u)) t.
  Proof. by move=> H t; apply: (H (tsubst σ t)). Qed.

  Lemma inst_coord_iff A a : fml_holds val (fml_subst (sub2 A a) ax_coord) <-> coordOK val A.
  Proof using Hring. by rewrite fml_holds_subst; apply: (coord_holds_iff (@ring_hom_subst _ _ val (sub2 A a) Hring) (tvar 0)). Qed.

  Lemma inst_P_iff A a : coordOK val (tapp0 s_one) ->
    fml_holds val (fml_subst (sub2 A a) (ax_P D)) <-> Tv val (tapp0 s_one) = pt_rat (Pgen D).
  Proof using Hring. by move=> H; rewrite fml_holds_subst; apply: (P_holds_iff (@ring_hom_subst _ _ val (sub2 A a) Hring) D H). Qed.

  Lemma inst_add_iff A a : coordOK val A -> coordOK val a -> coordOK val (tadd A a) ->
    fml_holds val (fml_subst (sub2 A a) ax_add) <-> AddSem val A a.
  Proof using Hring.
    move=> H1 H2 H3; rewrite fml_holds_subst.
    exact: (add_holds_iff (@ring_hom_subst _ _ val (sub2 A a) Hring) (a := tvar 0) (a' := tvar 1) H1 H2 H3).
  Qed.

  Lemma inst_chain_iff A a : coordOK val A ->
    fml_holds val (fml_subst (sub2 A a) (ax_chain D)) <-> ChainSem val D A.
  Proof using Hring.
    move=> H; rewrite fml_holds_subst.
    exact: (chain_holds_iff (@ring_hom_subst _ _ val (sub2 A a) Hring) D (t := tvar 0) H).
  Qed.

  Lemma inst_sqrt2_iff A a :
    fml_holds val (fml_subst (sub2 A a) ax_sqrt2) <-> val a = 0 \/ val A * val A != 2%:R * (val a * val a).
  Proof using Hring.
    rewrite fml_holds_subst.
    exact: (sqrt2_holds_iff (@ring_hom_subst _ _ val (sub2 A a) Hring) (tvar 0) (tvar 1)).
  Qed.

  Lemma inst_root_iff f A a :
    fml_holds val (fml_subst (sub2 A a) (ax_root f)) <->
    dp_evalR (fun v => val (tapp0 (s_cst (pos2nat v)))) (fun _ => 0) (projT2 f) = 0.
  Proof using Hring.
    rewrite fml_holds_subst.
    exact: (root_holds_iff (@ring_hom_subst _ _ val (sub2 A a) Hring) f).
  Qed.

  Lemma inst_rep_iff K A a : (forall x : R, x * x <> 2%:R) -> (forall t, coordOK val t) ->
    fml_holds val (fml_subst (sub2 A a) (ax_rep D K)) <-> RepSem val D K A a.
  Proof using Hring.
    move=> HZ0 Hc; rewrite fml_holds_subst.
    exact: (rep_holds_iff (@ring_hom_subst _ _ val (sub2 A a) Hring) D HZ0 K (tvar 0) (tvar 1) (coordOK_subst (sub2 A a) Hc)).
  Qed.

End ground.

(** sqrt2 is irrational: Z0 for R = rat, as needed by the standard model *)
Lemma rat_Z0 (x : rat) : x * x <> 2%:R.
Proof.
  move=> H.
  have Hx : x != 0.
  { apply/eqP => E; move: H; rewrite E mulr0 => /eqP; by rewrite eq_sym pnatr_eq0. }
  have E : numq x * numq x = 2%:Z * (denq x * denq x).
  { apply: (@intr_inj rat); rewrite !intrM !numqE mulrACA H. by []. }
  have En : (`|numq x| * `|numq x| = 2 * (`|denq x| * `|denq x|))%N.
  { by rewrite -!abszM E abszM. }
  have Hn : (0 < `|numq x|)%N by rewrite absz_gt0 numq_eq0.
  have Hd : (0 < `|denq x|)%N by rewrite absz_gt0 denq_neq0.
  move: (congr1 (logn 2) En).
  rewrite lognM // lognM ?muln_gt0 ?Hd // lognM // (@logn_prime 2 2) //=.
  move/(congr1 odd); rewrite !oddD !addbb /=.
  done.
Qed.

(** * 5. Enumeration of the instances and the finite tests (DESIGN 4) *)

Section tests.

  Variable D : FixedData.
  Variable f : H10Z_PROBLEM.

  (** ** Enumeration of the instances *)

  Definition ax_list (N : nat) : list (fml nat) :=
    List.app (axioms_base D f) (List.map (ax_rep D) (iota 1 N)).

  Definition inst_list (N : nat) : list gfml :=
    List.flat_map (fun M =>
      List.flat_map (fun A => List.map (fun a => fml_subst (sub2 A a) M) (gterm_list N)) (gterm_list N))
      (ax_list N).

  Lemma ax_list_mono N N' M : le N N' -> List.In M (ax_list N) -> List.In M (ax_list N').
  Proof.
    intros HN H; apply List.in_app_or in H as [ H | H ]; apply List.in_or_app; [ by left | right ].
    apply List.in_map_iff in H as (K & <- & HK); apply List.in_map.
    move: HK; rewrite !In_mem !mem_iota => /andP [ H1 H2 ].
    apply/andP; split => //; apply: (leq_trans H2); rewrite leq_add2l; exact/ssrnat.leP.
  Qed.

  Lemma inst_list_mono N N' phi : le N N' -> List.In phi (inst_list N) -> List.In phi (inst_list N').
  Proof.
    intros HN H.
    apply List.in_flat_map in H as (M & HM & H).
    apply List.in_flat_map in H as (A & HA & H).
    apply List.in_map_iff in H as (a & <- & Ha).
    apply List.in_flat_map; exists M; split; [ exact: ax_list_mono HM | ].
    apply List.in_flat_map; exists A; split; [ exact: gterm_list_mono HA | ].
    apply (List.in_map (fun a => fml_subst (sub2 A a) M)); exact: gterm_list_mono Ha.
  Qed.

  Lemma inst_list_spec phi : Inst D f phi <-> exists N, List.In phi (inst_list N).
  Proof.
    split.
    - intros (M & A & a & HM & ->).
      assert (exists K, forall N, le K N -> List.In M (ax_list N)) as (K & HK).
      { destruct HM as [ HM | (K & HK & ->) ].
        - exists 0%N; intros N _; apply List.in_or_app; by left.
        - exists K; intros N HN; apply List.in_or_app; right; apply List.in_map.
          apply/In_mem; rewrite mem_iota HK /= add1n ltnS; exact/ssrnat.leP. }
      destruct (gterm_list_spec A) as (k1 & Hk1).
      destruct (gterm_list_spec a) as (k2 & Hk2).
      exists (Nat.max K (Nat.max k1 k2)).
      apply List.in_flat_map; exists M; split; [ apply HK; lia | ].
      apply List.in_flat_map; exists A; split; [ apply: gterm_list_mono Hk1; lia | ].
      apply (List.in_map (fun a => fml_subst (sub2 A a) M)); apply: gterm_list_mono Hk2; lia.
    - intros (N & H).
      apply List.in_flat_map in H as (M & HM & H).
      apply List.in_flat_map in H as (A & HA & H).
      apply List.in_map_iff in H as (a & <- & Ha).
      exists M, A, a; split => //.
      apply List.in_app_or in HM as [ HM | HM ]; [ by left | right ].
      apply List.in_map_iff in HM as (K & <- & HK).
      exists K; split => //; move: HK => /In_mem; rewrite mem_iota => /andP [ H _ ]; exact H.
  Qed.

  (** ** The term list of the N-th test: closed under immediate subterms,
      containing [gterm_list N] and every term compared in an atom of an
      instance of [inst_list N] *)

  Definition tlist (N : nat) : list gterm :=
    List.flat_map subt (List.app (gterm_list N) (List.flat_map fml_terms (inst_list N))).

  Lemma tlist_closed N : sub_closed (tlist N).
  Proof. exact: flat_map_subt_closed. Qed.

  Lemma tlist_gterm N t : List.In t (gterm_list N) -> List.In t (tlist N).
  Proof. by move=> H; apply flat_map_subt_incl, List.in_or_app; left. Qed.

  Lemma tlist_inst N phi t : List.In phi (inst_list N) -> List.In t (fml_terms phi) -> List.In t (tlist N).
  Proof.
    move=> H1 H2; apply flat_map_subt_incl, List.in_or_app; right.
    apply List.in_flat_map; by exists phi.
  Qed.

  Lemma tlist_mono N N' t : le N N' -> List.In t (tlist N) -> List.In t (tlist N').
  Proof.
    intros HN H; apply List.in_flat_map in H as (u & Hu & Ht).
    apply List.in_flat_map; exists u; split => //; apply List.in_or_app.
    apply List.in_app_or in Hu as [ Hu | Hu ]; [ left; exact: gterm_list_mono Hu | right ].
    apply List.in_flat_map in Hu as (phi & H1 & H2).
    apply List.in_flat_map; exists phi; split => //; exact: inst_list_mono H1.
  Qed.

  (** ** The constraints (a) to (d) as a [qform nat] *)

  Section constraints.

    Variable L : list gterm.

    Definition qX (u : gterm) : qpolyQ nat := qp_var (tvq (ix L u)).
    Definition qeq (p q : qpolyQ nat) : qform nat := qf_eq0 (qsub p q).
    Definition qne (p q : qpolyQ nat) : qform nat := qf_neq0 (qsub p q).

    (* (a) the ring symbols *)
    Definition ring_q (u : gterm) : qform nat :=
      match u with
      | tapp0 s_zero => qeq (qX u) (qc 0)
      | tapp0 s_one => qeq (qX u) (qc 1)
      | tapp0 (s_int z) => qeq (qX u) (qc (Z_to_R z))
      | tapp1 s_neg s => qeq (qX u) (qp_mul (qc (-1)) (qX s))
      | tapp2 s_add s s' => qeq (qX u) (qp_add (qX s) (qX s'))
      | tapp2 s_mul s s' => qeq (qX u) (qp_mul (qX s) (qX s'))
      | _ => qf_true
      end.

    (* (b) functionality *)
    Definition fun_q (u u' : gterm) : qform nat :=
      match u, u' with
      | tapp1 g s, tapp1 g' s' =>
          if sym1_eq_dec g g' then qf_or (qne (qX s) (qX s')) (qeq (qX u) (qX u')) else qf_true
      | tapp2 g s1 s2, tapp2 g' s1' s2' =>
          if sym2_eq_dec g g'
          then qf_or (qne (qX s1) (qX s1')) (qf_or (qne (qX s2) (qX s2')) (qeq (qX u) (qX u')))
          else qf_true
      | _, _ => qf_true
      end.

    (* (c) an instance, atom by atom *)
    Fixpoint fml_q (phi : gfml) : qform nat :=
      match phi with
      | f_eq s t => qeq (qX s) (qX t)
      | f_ne s t => qne (qX s) (qX t)
      | f_and A B => qf_and (fml_q A) (fml_q B)
      | f_or A B => qf_or (fml_q A) (fml_q B)
      | f_tt => qf_true
      | f_ff => qf_false
      end.

    (* (d) Phi on the value of a term, with fresh witnesses *)
    Definition phi_q (u : gterm) : qform nat := qf_map (phi_ren (ix L u)) (Phi_form (fd_PhiL D)).

  End constraints.

  Definition qf_all (l : list (qform nat)) : qform nat := List.fold_right (@qf_and nat) qf_true l.

  Definition testf (N : nat) : qform nat :=
    let L := tlist N in
    qf_all (List.app (List.map (ring_q L) L)
           (List.app (List.flat_map (fun u => List.map (fun_q L u) L) L)
           (List.app (List.map (fml_q L) (inst_list N))
                     (List.map (phi_q L) L)))).

  (** the N-th finite test, with variables pos n (computable) *)
  Definition test (N : nat) : {n & qform (pos n)} :=
    let A := testf N in
    existT _ (S (vmax (qf_vars A))) (qf_map (trv (vmax (qf_vars A))) A).

End tests.

(** ** Properties of the tests *)

Section test_props.

  Variable D : FixedData.
  Variable f : H10Z_PROBLEM.

  Lemma qf_all_spec (φ : nat -> rat) l :
    qf_holds φ (qf_all l) <-> forall A, List.In A l -> qf_holds φ A.
  Proof.
    elim: l => [ | A l IH ] /=; first by split.
    rewrite IH; split.
    - by case=> HA Hl B [ <- | HB ]; auto.
    - by move=> H; split; [ apply: H; left | move=> B HB; apply: H; right ].
  Qed.

  Lemma qsub_eval (φ : nat -> rat) p q : qp_eval φ (qsub p q) = qp_eval φ p - qp_eval φ q.
  Proof. by rewrite /qsub /= mulN1r. Qed.

  Lemma qeq_holds (φ : nat -> rat) p q : qf_holds φ (qeq p q) <-> qp_eval φ p = qp_eval φ q.
  Proof.
    rewrite /qeq; cbn [qf_holds]; rewrite qsub_eval; split => [ /eqP | -> ]; last by rewrite subrr.
    by rewrite subr_eq0 => /eqP.
  Qed.

  Lemma qne_holds (φ : nat -> rat) p q : qf_holds φ (qne p q) <-> qp_eval φ p <> qp_eval φ q.
  Proof.
    rewrite /qne; cbn [qf_holds]; rewrite qsub_eval; split => H E; apply: H.
    - by rewrite E subrr.
    - by apply/eqP; rewrite -subr_eq0; apply/eqP.
  Qed.

  (* the satisfying assignments of a test are those of [testf] *)
  Lemma test_spec N : qf_sat (projT2 (test D f N)) <-> exists φ : nat -> rat, qf_holds φ (testf D f N).
  Proof.
    rewrite /test /qf_sat /=; split.
    - case=> φ' H; exists (fun v => φ' (trv (vmax (qf_vars (testf D f N))) v)); exact/qf_holds_map.
    - case=> φ H; exists (fun p => φ (pos2nat p)); apply/qf_holds_map.
      have H' : forall v, List.In v (qf_vars (testf D f N)) ->
                  φ v = φ (pos2nat (trv (vmax (qf_vars (testf D f N))) v)).
      { by move=> v Hv; rewrite trv_spec //; apply: vmax_spec. }
      exact: (qf_holds_ext H').1 H.
  Qed.

  (** the constraints, read off an assignment of the term variables *)

  Section read.

    Variables (L : list gterm) (φ : nat -> rat).

    Definition rho_of (u : gterm) : rat := φ (tvq (ix L u)).

    Lemma ring_q_iff u : qf_holds φ (ring_q L u) <-> ring_ok rho_of u.
    Proof.
      case: u => [ x | g | g s | g s s' ]; first by case: x.
      all: case: g => *; cbn [ring_q ring_ok]; rewrite ?qeq_holds /= ?mulN1r;
             try reflexivity; by split.
    Qed.

    Lemma fun_q_sound u u' : qf_holds φ (fun_q L u u') -> fun_ok rho_of u u'.
    Proof.
      destruct u as [ x | g0 | g s | g s1 s2 ]; destruct u' as [ x' | g0' | g' s' | g' s1' s2' ];
        cbn [fun_q fun_ok]; try by [].
      - intros H Hg Hs; revert H; destruct (sym1_eq_dec g g') as [ E | ]; [ | done ].
        intros [ H | H ]; [ by apply qne_holds in H | exact (proj1 (qeq_holds _ _ _) H) ].
      - intros H Hg Hs1 Hs2; revert H; destruct (sym2_eq_dec g g') as [ E | ]; [ | done ].
        intros [ H | [ H | H ] ]; [ by apply qne_holds in H | by apply qne_holds in H | ].
        exact (proj1 (qeq_holds _ _ _) H).
    Qed.

    Lemma fun_q_complete u u' : fun_ok rho_of u u' -> qf_holds φ (fun_q L u u').
    Proof.
      destruct u as [ x | g0 | g s | g s1 s2 ]; destruct u' as [ x' | g0' | g' s' | g' s1' s2' ];
        cbn [fun_q fun_ok]; try by [].
      - intros H; destruct (sym1_eq_dec g g') as [ Hg | ]; [ | done ].
        destruct (rat_eq_dec (rho_of s) (rho_of s')) as [ Hs | Hs ].
        + by right; apply/qeq_holds; apply: H.
        + by left; apply/qne_holds.
      - intros H; destruct (sym2_eq_dec g g') as [ Hg | ]; [ | done ].
        destruct (rat_eq_dec (rho_of s1) (rho_of s1')) as [ Hs1 | Hs1 ]; [ | by left; apply/qne_holds ].
        destruct (rat_eq_dec (rho_of s2) (rho_of s2')) as [ Hs2 | Hs2 ]; [ | by right; left; apply/qne_holds ].
        by right; right; apply/qeq_holds; apply: H.
    Qed.

    Lemma fml_q_iff phi : qf_holds φ (fml_q L phi) <-> fml_holds rho_of phi.
    Proof.
      elim: phi => [ s t | s t | A HA B HB | A HA B HB | | ]; cbn [fml_q fml_holds qf_holds].
      - exact: qeq_holds.
      - exact: qne_holds.
      - by rewrite HA HB.
      - by rewrite HA HB.
      - by [].
      - by split.
    Qed.

    Lemma phi_q_iff u :
      qf_holds φ (phi_q D L u) <-> qf_holds (fun v => φ (phi_ren (ix L u) v)) (Phi_form (fd_PhiL D)).
    Proof. exact: qf_holds_map. Qed.

  End read.

  Local Fact in_app3 {T} (x : T) l1 l2 l3 l4 :
    (List.In x l1 \/ List.In x l2 \/ List.In x l3 \/ List.In x l4) <->
    List.In x (List.app l1 (List.app l2 (List.app l3 l4))).
  Proof. rewrite !List.in_app_iff; tauto. Qed.

  (** cofinality, the core: an assignment satisfying test N gives a
      valuation of the ground terms satisfying (a) to (d) on the terms of
      [tlist N] and (c) on the instances of [inst_list N] *)
  Lemma testf_read N (φ : nat -> rat) :
    qf_holds φ (testf D f N) ->
    let L := tlist D f N in
       (forall u, List.In u L -> ring_ok (rho_of L φ) u)
    /\ (forall u u', List.In u L -> List.In u' L -> fun_ok (rho_of L φ) u u')
    /\ (forall phi, List.In phi (inst_list D f N) -> fml_holds (rho_of L φ) phi)
    /\ (forall u, List.In u L -> Phi_holdsR (fd_PhiL D) (rho_of L φ u)).
  Proof.
    move=> H L; rewrite /testf in H; cbv zeta in H; rewrite qf_all_spec in H.
    split; [ | split; [ | split ] ].
    - move=> u Hu; apply/ring_q_iff/H/in_app3; left; exact: List.in_map.
    - move=> u u' Hu Hu'; apply/fun_q_sound/H/in_app3; right; left.
      apply List.in_flat_map; exists u; split => //; exact: List.in_map.
    - move=> phi Hphi; apply/fml_q_iff/H/in_app3; right; right; left; exact: List.in_map.
    - move=> u Hu; have /phi_q_iff Hd : qf_holds φ (phi_q D L u).
      { apply/H/in_app3; right; right; right; exact: List.in_map. }
      apply/Phi_holds_rat; exists (fun v => φ (phi_ren (ix L u) v)).
      apply: (qf_holds_ext _).1 Hd => [] [ | v ] _ //.
  Qed.

  (** soundness, the core: a valuation satisfying (a) to (d) on the terms
      of [tlist N] and (c) on [inst_list N] satisfies test N *)
  Lemma testf_write N (rho : gterm -> rat) :
    let L := tlist D f N in
       (forall u, List.In u L -> ring_ok rho u)
    -> (forall u u', List.In u L -> List.In u' L -> fun_ok rho u u')
    -> (forall phi, List.In phi (inst_list D f N) -> fml_holds rho phi)
    -> (forall u, List.In u L -> Phi_holdsR (fd_PhiL D) (rho u))
    -> exists φ : nat -> rat, qf_holds φ (testf D f N).
  Proof.
    move=> L Ha Hb Hc Hd.
    have [ g Hg ] : exists g : gterm -> nat -> rat, forall u, List.In u L ->
        qf_holds (Phi_env (rho u) (g u)) (Phi_form (fd_PhiL D)).
    { apply: (@fin_choice (nat -> rat) (fun _ => 0)
               (fun u w => qf_holds (Phi_env (rho u) w) (Phi_form (fd_PhiL D))) L) => u Hu.
      by apply/Phi_holds_rat; apply: Hd. }
    pose φ := var_case (fun i => rho (List.nth i L (tapp0 s_zero))) (fun i k => g (List.nth i L (tapp0 s_zero)) k).
    have Hφ : forall u, List.In u L -> rho_of L φ u = rho u.
    { by move=> u Hu; rewrite /rho_of /φ var_case_t ix_nth. }
    have [ Hcl1 Hcl2 ] := tlist_closed D f N.
    exists φ; rewrite /testf; cbv zeta; rewrite qf_all_spec => A /in_app3.
    case=> [ | [ | [ | ] ] ].
    - move=> /List.in_map_iff [ u [ <- Hu ] ]; apply/ring_q_iff.
      move: (Ha u Hu); case: u Hu => [ | g0 | g1 s | g2 s s' ] Hu //=; rewrite Hφ //.
      + by case: g1 Hu => // Hu; rewrite Hφ //; apply: Hcl1 Hu.
      + have [ Hs Hs' ] := Hcl2 _ _ _ Hu.
        by case: g2 Hu => // Hu; rewrite !Hφ.
    - move=> /List.in_flat_map [ u [ Hu /List.in_map_iff [ u' [ <- Hu' ] ] ] ].
      apply: fun_q_complete; move: (Hb u u' Hu Hu').
      case: u Hu => [ | | h s | h s1 s2 ] Hu //; case: u' Hu' => [ | | h' s' | h' s1' s2' ] Hu' //=.
      + have Hs := Hcl1 _ _ Hu; have Hs' := Hcl1 _ _ Hu'.
        by rewrite !Hφ.
      + have [ ? ? ] := Hcl2 _ _ _ Hu; have [ ? ? ] := Hcl2 _ _ _ Hu'.
        by rewrite !Hφ.
    - move=> /List.in_map_iff [ phi [ <- Hphi ] ]; apply/fml_q_iff.
      have Hext : forall t, List.In t (fml_terms phi) -> rho_of L φ t = rho t.
      { move=> t Ht; apply: Hφ; exact: tlist_inst Hphi Ht. }
      move: (Hc phi Hphi); clear Hc Hphi.
      elim: phi Hext => [ s t | s t | B HB C HC | B HB C HC | | ] /= Hext.
      + by rewrite !Hext //=; auto.
      + by rewrite !Hext //=; auto.
      + case=> H1 H2; split.
        * apply: (HB _ H1) => t Ht; apply: Hext; apply List.in_or_app; auto.
        * apply: (HC _ H2) => t Ht; apply: Hext; apply List.in_or_app; auto.
      + case=> [ H1 | H2 ]; [ left | right ].
        * apply: (HB _ H1) => t Ht; apply: Hext; apply List.in_or_app; auto.
        * apply: (HC _ H2) => t Ht; apply: Hext; apply List.in_or_app; auto.
      + by [].
      + by [].
    - move=> /List.in_map_iff [ u [ <- Hu ] ]; apply/phi_q_iff.
      apply: (qf_holds_ext _).2 (Hg u Hu) => [] [ | v ] _.
      + by rewrite /= /φ var_case_t ix_nth.
      + by rewrite /= /φ var_case_w ix_nth.
  Qed.

  (** monotonicity of the tests *)
  Lemma test_mono N : qf_sat (projT2 (test D f N.+1)) -> qf_sat (projT2 (test D f N)).
  Proof.
    move=> /test_spec [ φ /testf_read [ Ha [ Hb [ Hc Hd ] ] ] ]; apply/test_spec.
    have Hle : le N N.+1 by lia.
    apply: (testf_write (rho := rho_of (tlist D f N.+1) φ)).
    - move=> u Hu; apply: Ha; exact: tlist_mono Hle Hu.
    - move=> u u' Hu Hu'; by apply: Hb; [ exact: tlist_mono Hle Hu | exact: tlist_mono Hle Hu' ].
    - move=> phi Hphi; apply: Hc; exact: inst_list_mono Hle Hphi.
    - move=> u Hu; apply: Hd; exact: tlist_mono Hle Hu.
  Qed.

  (** ** Cofinality: if every test succeeds, the constraints (a) to (d)
      are finitely satisfiable in the sense of Ambient.v *)

  Lemma gterm_list_fin (ts : list gterm) : exists N, forall t, List.In t ts -> List.In t (gterm_list N).
  Proof.
    elim: ts => [ | t ts [ N HN ] ]; first by exists 0%N.
    have [ k Hk ] := gterm_list_spec t.
    exists (Nat.max k N) => u [ <- | Hu ]; [ apply: gterm_list_mono Hk | apply: gterm_list_mono (HN u Hu) ]; lia.
  Qed.

  Lemma inst_list_fin (fs : list gfml) :
    (forall phi, List.In phi fs -> Inst D f phi) -> exists N, forall phi, List.In phi fs -> List.In phi (inst_list D f N).
  Proof.
    elim: fs => [ | phi fs IH ] H; first by exists 0%N.
    have [ N HN ] : exists N, forall psi, List.In psi fs -> List.In psi (inst_list D f N).
    { apply: IH => psi Hpsi; apply: H; by right. }
    have [ k Hk ] : exists k, List.In phi (inst_list D f k) by apply/inst_list_spec/H; left.
    exists (Nat.max k N) => psi [ <- | Hpsi ];
      [ apply: inst_list_mono Hk | apply: inst_list_mono (HN psi Hpsi) ]; lia.
  Qed.

  Theorem tests_FinSat : (forall N, qf_sat (projT2 (test D f N))) -> FinSat D (Inst D f).
  Proof.
    move=> H ts fs Hfs.
    have [ N1 HN1 ] := gterm_list_fin ts.
    have [ N2 HN2 ] := inst_list_fin Hfs.
    pose N := Nat.max N1 N2.
    have [ φ /testf_read [ Ha [ Hb [ Hc Hd ] ] ] ] := (test_spec N).1 (H N).
    have Hts : forall t, List.In t ts -> List.In t (tlist D f N).
    { move=> t Ht; apply: tlist_gterm; apply: gterm_list_mono (HN1 t Ht); lia. }
    exists (rho_of (tlist D f N) φ); split; [ | split; [ | split ] ].
    - move=> t Ht; exact/Ha/Hts.
    - move=> t t' Ht Ht'; apply: Hb; exact: Hts.
    - move=> phi Hphi; apply: Hc; apply: inst_list_mono (HN2 phi Hphi); lia.
    - move=> t Ht; exact/Hd/Hts.
  Qed.

  (** ** The bridge for the standard model (task 9b): a rational
      valuation of all ground terms satisfying (a) to (d) everywhere makes
      every test succeed *)

  Definition RatModel (rho : gterm -> rat) : Prop :=
       (forall t, ring_ok rho t)
    /\ (forall t t', fun_ok rho t t')
    /\ (forall phi, Inst D f phi -> fml_holds rho phi)
    /\ (forall t, Phi_holdsR (fd_PhiL D) (rho t)).

  Theorem test_sound_from_model rho : RatModel rho -> forall N, qf_sat (projT2 (test D f N)).
  Proof.
    move=> [ Ha [ Hb [ Hc Hd ] ] ] N; apply/test_spec.
    apply: (testf_write (rho := rho)) => // phi Hphi; apply: Hc.
    by apply/inst_list_spec; exists N.
  Qed.

End test_props.

(** * 6. The instances of T in a valuation, semantically

    [Inst_sem_iff]: a valuation of the ground terms (in any numeric field
    with Z0) satisfying (a) satisfies all instances of [Inst D f] iff it
    satisfies the semantic conditions below. The direction [->] is used by
    the ambient analysis (tasks 10, 11) through [TermModel]; the direction
    [<-] by the standard model (task 9b, with R = rat, Z0 = [rat_Z0]). *)

Section inst_sem.

  Variables (D : FixedData) (f : H10Z_PROBLEM) (R : numFieldType) (val : gterm -> R).
  Hypothesis Hring : forall t, ring_ok val t.
  Hypothesis HZ0 : forall x : R, x * x <> 2%:R.

  Definition InstSem : Prop :=
       (forall t, coordOK val t)
    /\ Tv val (tapp0 s_one) = pt_rat (Pgen D)
    /\ (forall A a, AddSem val A a)
    /\ (forall A, ChainSem val D A)
    /\ (forall A a, val a = 0 \/ val A * val A != 2%:R * (val a * val a))
    /\ dp_evalR (fun v => val (tapp0 (s_cst (pos2nat v)))) (fun _ => 0) (projT2 f) = 0
    /\ (forall K A a, (1 <= K)%N -> RepSem val D K A a).

  Theorem Inst_sem_iff : (forall phi, Inst D f phi -> fml_holds val phi) <-> InstSem.
  Proof using Hring HZ0.
    split.
    - move=> H.
      have Hc : forall t, coordOK val t.
      { by move=> t; apply/(inst_coord_iff Hring t t)/H/Inst_coord. }
      split; first exact: Hc.
      split; first by apply/(inst_P_iff D Hring (tapp0 s_zero) (tapp0 s_zero) (Hc _))/H/Inst_P.
      split; first by move=> A a; apply/(inst_add_iff Hring (Hc _) (Hc _) (Hc _))/H/Inst_add.
      split; first by move=> A; apply/(inst_chain_iff D Hring A (Hc _))/H/Inst_chain.
      split; first by move=> A a; apply/(inst_sqrt2_iff Hring)/H/Inst_sqrt2.
      split; first by apply/(inst_root_iff Hring f (tapp0 s_zero) (tapp0 s_zero))/H/Inst_root.
      by move=> K A a HK; apply/(inst_rep_iff D Hring K A a HZ0 Hc)/H/Inst_rep.
    - move=> [ Hc [ HP [ Hadd [ Hch [ Hs [ Hr Hrep ] ] ] ] ] ] phi [ M [ A [ a [ HM -> ] ] ] ].
      case: HM => [ HM | [ K [ HK -> ] ] ]; last exact/(inst_rep_iff D Hring K A a HZ0 Hc)/Hrep.
      case: HM => [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [] ] ] ] ] ] ].
      + exact/(inst_coord_iff Hring A a)/Hc.
      + exact/(inst_P_iff D Hring A a (Hc _)).
      + exact/(inst_add_iff Hring (Hc _) (Hc _) (Hc _))/Hadd.
      + exact/(inst_chain_iff D Hring a (Hc A))/Hch.
      + exact/(inst_sqrt2_iff Hring)/Hs.
      + exact/(inst_root_iff Hring f A a).
  Qed.

End inst_sem.

