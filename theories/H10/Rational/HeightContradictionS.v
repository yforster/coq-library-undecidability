(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A (task P3b): HeightContradiction.v over the setoid ambient
   structure [A : AmbientS D] of AmbientS.v (carrier [sQ A : SOF]).

   Sections 2.6 and 2.7 of the paper (02-reduction.tex; DESIGN.md,
   Section 5.4, lemmas L4 and L5; Section 2.7), a faithful port of
   HeightContradiction.v (same lemma names, same proof steps):
   - [index_congruence]: Prop red:index-congruence;
   - [finite_test_success]: Prop red:finite-test-success; its conclusion
     [H10Z (existT _ n f)] is unchanged (an ordinary statement).

   Translation (SETOID.md):
   - [=]/[!=] on [sQ A] become [≡]/[≢]; [Z_to_R] becomes [of_Z] (the
     [of_Z_*] lemmas below replace the [Z_to_R_*] lemmas); [dp_evalR] is
     [dp_evalS]; [ring]/[field]/[lra] are [sring]/[sfield]/[slra];
   - points are [ptS] (flag encoding); [T := Tpt val] (CoarseningS.v),
     convertible to [TvS val] of TheoryS.v and to the [T val] of
     LocalComparisonS.v; the side condition "T t = Some (x, y) -> x <> 0"
     becomes [(T t).1 ≢ 0 -> (T t).2.1 ≢ 0] (the form of [coarsening]);
   - [RepSem] is the record [CoarseningS.RepSemS], [slope] is [slopeS];
   - [pos_max] returns a bound [B] with [B ≡ 1 \/ exists j, B ≡ |g j|]
     (Prop case split by [lerP], no decision procedure).

   Section hypotheses (instantiated in ReductionS.v):
   - the eta interface [eta], [eta_isZ], [eta_spec], [eta_add],
     [eta_one], [eta_val] and [local_comparison]: stated EXACTLY as the
     lemmas of LocalComparisonS.v (with [T := Tpt val], convertible to
     LocalComparisonS's [T val]), so that they are discharged by [exact];
   - [root]: the root component of [InstSemS] (TheoryS.v), with
     [acst i := tapp0 (s_cst (pos2nat i))];
   - [rep]: the representation axiom as the record [CoarseningS.RepSemS]
     (its derivation from the [RepSemS] of TheoryS.v is the glue of
     ReductionS.v, as Reduction.v did for Coarsening.RepSem).

   Logical assumptions: excluded middle (classic) only (through
   CoarseningS.v). No choice: the finitely many integers of the final
   zero are collected by induction on the number of variables. *)

From Stdlib Require Import Setoid Morphisms RelationClasses Arith ZArith Lia List Classical_Prop.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos.

From Undecidability.H10.Dio
  Require dio_logic.

From Undecidability.H10
  Require Import H10Z.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData.

From Undecidability.H10.Rational
  Require Import SOF SOFTactics SOFqe SOFTheory SignatureS AmbientS CoarseningS.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.
Import SOFTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope sof_scope.

(** * Polynomials: coefficient size and degree (unchanged, nat-valued) *)

Section poly_size.

  Variables (V P : Set).

  (* the sum of the absolute values of the coefficients of the expanded
     polynomial is at most [pc p]  (C_f of red:error-bound) *)
  Fixpoint pc (p : dio_polynomial V P) : nat :=
    match p with
    | dp_cnst c => Z.abs_nat c
    | dp_var _ => 1%N
    | dp_par _ => 0%N
    | dp_comp dio_logic.do_add p q => (pc p + pc q)%N
    | dp_comp dio_logic.do_mul p q => (pc p * pc q)%N
    end.

  (* syntactic total degree (as H10Q.dp_deg) *)
  Fixpoint pdeg (p : dio_polynomial V P) : nat :=
    match p with
    | dp_cnst _ => 0%N
    | dp_var _ => 1%N
    | dp_par _ => 0%N
    | dp_comp dio_logic.do_add p q => maxn (pdeg p) (pdeg q)
    | dp_comp dio_logic.do_mul p q => (pdeg p + pdeg q)%N
    end.

End poly_size.

(** * The ring morphism of_Z : Z -> F and polynomial evaluation *)

Section of_Z.

  Variable F : SOF.

  Add Field oz_field : (@sof_fth F) (setoid (sr_setoid F) (sr_ext F),
    morphism (of_Z_morph F), constants [sof_cst],
    power_tac (sr_pow_th F) [sof_pow_cst], completeness (sof_Z_complete F)).

  Lemma of_Z_0 : (of_Z 0%ZZ : F) ≡ 0.
  Proof. reflexivity. Qed.

  Lemma of_Z_eq0 z : (of_Z z : F) ≡ 0 -> z = 0%ZZ.
  Proof. move=> h; apply: (of_Z_inj F); exact h. Qed.

  Lemma of_Z_of_nat k : (of_Z (Z.of_nat k) : F) ≡ k%:R.
  Proof.
    case: k => [ | k ]; first reflexivity.
    change ((of_nat (Pos.to_nat (Pos.of_succ_nat k)) : F) ≡ k.+1%:R).
    rewrite SuccNat2Pos.id_succ; reflexivity.
  Qed.

  Lemma of_Z_opp_of_nat k : (of_Z (- Z.of_nat k)%ZZ : F) ≡ - k%:R.
  Proof. rewrite of_Z_opp of_Z_of_nat; reflexivity. Qed.

  (* the decomposition used by Z_to_R in HeightContradiction.v *)
  Lemma of_Z_nat_split z : (of_Z z : F) ≡ (Z.to_nat z)%:R - (Z.to_nat (- z))%:R.
  Proof.
    have E : z = (Z.of_nat (Z.to_nat z) - Z.of_nat (Z.to_nat (- z)))%ZZ by lia.
    rewrite {1}E of_Z_sub !of_Z_of_nat; reflexivity.
  Qed.

  Lemma of_Z_norm z : `|of_Z z : F| ≡ (Z.abs_nat z)%:R.
  Proof.
    case: (Z.le_gt_cases 0 z) => hz.
    - rewrite ger0_norm; first by apply: of_Z_ge0.
      have -> : z = Z.of_nat (Z.abs_nat z) by lia.
      rewrite Zabs2Nat.id; exact: of_Z_of_nat.
    - rewrite ler0_norm; first by change ((of_Z z : F) <= of_Z 0%ZZ); apply: (of_Z_le F); lia.
      have -> : z = (- Z.of_nat (Z.abs_nat z))%ZZ by lia.
      rewrite of_Z_opp_of_nat opprK.
      have -> : Z.abs_nat (- Z.of_nat (Z.abs_nat z)) = Z.abs_nat z by lia.
      reflexivity.
  Qed.

  (* the cast of N1 = Nh (9 HCf + 6 + Ch), for variables (no unfolding) *)
  Lemma natr_N1 (a b c : nat) :
    (((a * (9 * b + 6 + c))%N)%:R : F) ≡ a%:R * (9%:R * b%:R + 6%:R + c%:R).
  Proof. rewrite natrM natrD natrD natrM; reflexivity. Qed.

  Variables (V P : Set).

  Lemma dp_evalS_Z (φ : V -> Z) (p : dio_polynomial V P) :
    dp_evalS (fun v => of_Z (φ v) : F) (fun _ => 0) p
    ≡ of_Z (dp_eval φ (fun _ => 0%ZZ) p).
  Proof.
    elim: p => [ c | v | i | [] p Hp q Hq ] /=.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite Hp Hq of_Z_add; reflexivity.
    - rewrite Hp Hq of_Z_mul; reflexivity.
  Qed.

  (* red:error-bound: |f(x)| <= C_f B^deg f  for |x_i| <= B, B >= 1 *)
  Lemma poly_bound (φ : V -> F) (B : F) (p : dio_polynomial V P) :
    1 <= B -> (forall v, `|φ v| <= B) ->
    `|dp_evalS φ (fun _ => 0) p| <= (pc p)%:R * B ^+ pdeg p.
  Proof.
    move=> hB hφ.
    have hB0 : 0 <= B by slra.
    elim: p => [ c | v | i | [] p Hp q Hq ] ; cbn [dp_evalS pc pdeg].
    - rewrite of_Z_norm expr0 mulr1; exact: lexx.
    - rewrite mul1r expr1; exact: hφ.
    - rewrite normr0 mul0r; exact: lexx.
    - have h1 := ler_normD _ (dp_evalS φ (fun _ => 0) p) (dp_evalS φ (fun _ => 0) q).
      have h2 : (pc p)%:R * B ^+ pdeg p <= (pc p)%:R * B ^+ maxn (pdeg p) (pdeg q).
      { apply: ler_wpM2l; first exact: ler0n.
        apply: ler_weXn2l => //; exact: leq_maxl. }
      have h3 : (pc q)%:R * B ^+ pdeg q <= (pc q)%:R * B ^+ maxn (pdeg p) (pdeg q).
      { apply: ler_wpM2l; first exact: ler0n.
        apply: ler_weXn2l => //; exact: leq_maxr. }
      rewrite natrD mulrDl; slra.
    - rewrite normrM natrM exprD.
      have E : (pc p)%:R * (pc q)%:R * (B ^+ pdeg p * B ^+ pdeg q)
              ≡ ((pc p)%:R * B ^+ pdeg p) * ((pc q)%:R * B ^+ pdeg q) by sring.
      rewrite E; apply: ler_pM => //; exact: normr_ge0.
  Qed.

End of_Z.

(** * Finite choice and maxima over positions *)

Lemma fin_choice n (Pr : pos n -> Z -> Prop) :
  (forall i, exists z, Pr i z) -> exists zs : pos n -> Z, forall i, Pr i (zs i).
Proof.
  elim: n Pr => [ | n IH ] Pr H.
  - by exists (fun _ => 0%ZZ) => i; apply: (pos_O_invert _ i).
  - have [z0 h0] := H pos_fst.
    have [zs hs] := IH (fun i => Pr (pos_nxt i)) (fun i => H (pos_nxt i)).
    exists (fun i => Fin.caseS' i (fun _ => Z) z0 zs).
    by apply: pos_S_invert.
Qed.

Lemma pos_max (F : SOF) n (g : pos n -> F) :
  exists B, 1 <= B /\ (forall i, `|g i| <= B) /\ (B ≡ 1 \/ exists j, B ≡ `|g j|).
Proof.
  elim: n g => [ | n IH ] g.
  - exists 1; split; first exact: lexx.
    split; [ move=> i; apply: (pos_O_invert _ i) | left; reflexivity ].
  - have [B' [h1 [h2 h3]]] := IH (fun i => g (pos_nxt i)).
    case: (lerP _ B' `|g pos_fst|) => hle.
    + exists `|g pos_fst|; split; first by slra.
      split; last by right; exists pos_fst; reflexivity.
      apply: pos_S_invert; first exact: lexx.
      move=> p; have := h2 p; slra.
    + exists B'; split => //; split.
      * apply: pos_S_invert; [ slra | exact: h2 ].
      * case: h3 => [ E | [j E] ]; [ by left | by right; exists (pos_nxt j) ].
Qed.

(** * Finite intervals of *Z are ordinary (DESIGN 2.6) *)

Section intervals.

  Variables (D : FixedData) (A : AmbientS D).
  Local Abbreviation sQA := (sQ A).

  Add Field iv_field : (@sof_fth sQA) (setoid (sr_setoid sQA) (sr_ext sQA),
    morphism (of_Z_morph sQA), constants [sof_cst],
    power_tac (sr_pow_th sQA) [sof_pow_cst], completeness (sof_Z_complete sQA)).

  Lemma isZ_interval_nat (N : nat) (x : sQA) :
    isZ A x -> 0 <= x -> x <= N%:R -> exists k : nat, x ≡ k%:R.
  Proof.
    elim: N x => [ | N IH ] x hx h0 hN.
    - by exists 0%N; apply/eq_le; split.
    - case: (lerP _ x N%:R) => hle; first exact: IH.
      exists N.+1.
      have hd : isZ A (x - N%:R) by apply: isZ_sub => //; apply: isZ_nat.
      have H := trV0 hd (proj2 (subr_gt0 _ _ _) hle).
      rewrite natrS in hN *; slra.
  Qed.

  Lemma isZ_interval (N : nat) (x : sQA) :
    isZ A x -> `|x| <= N%:R -> exists z : Z, x ≡ of_Z z.
  Proof.
    move=> hx; case: (lerP _ 0 x) => h0.
    - rewrite (ger0_norm _ _ h0) => hN.
      have [k hk] := isZ_interval_nat hx h0 hN.
      by exists (Z.of_nat k); rewrite of_Z_of_nat.
    - rewrite (ltr0_norm _ _ h0) => hN.
      have hx' : isZ A (- x) by apply: trZ1_opp.
      have hx0 : 0 <= - x by slra.
      have [k hk] := isZ_interval_nat hx' hx0 hN.
      exists (- Z.of_nat k)%ZZ; rewrite of_Z_opp_of_nat -hk; sring.
  Qed.

End intervals.

(** * Index congruences and the height contradiction *)

Section height.

  Variables (D : FixedData) (HWF : FixedWF D) (A : AmbientS D).
  Variables (Ax : gfml -> Prop) (val : gterm -> sQ A).
  Hypothesis HTM : TermModelS A Ax val.

  Local Abbreviation sQA := (sQ A).
  Local Abbreviation isZA := (isZ A).
  Local Abbreviation T := (Tpt val).

  Add Field hc_field : (@sof_fth sQA) (setoid (sr_setoid sQA) (sr_ext sQA),
    morphism (of_Z_morph sQA), constants [sof_cst],
    power_tac (sr_pow_th sQA) [sof_pow_cst], completeness (sof_Z_complete sQA)).
  Add Field hc_qe_field : (qe_fth sQA (@trZ0 D A))
    (setoid (sr_setoid (qe_SRing sQA)) (sr_ext (qe_SRing sQA)),
    morphism (of_Z_morph (qe_SRing sQA)), constants [sof_cst],
    power_tac (sr_pow_th (qe_SRing sQA)) [sof_pow_cst], completeness (qe_Z_complete sQA)).

  (** ** Hypotheses: the lemmas of LocalComparisonS.v (verbatim) *)

  (* LocalComparisonS.eta (red:eta) *)
  Variable eta : gterm -> sQA.
  (* LocalComparisonS.eta_isZ *)
  Hypothesis eta_isZ : forall t, isZ A (eta t).
  (* LocalComparisonS.eta_spec: T_t = eta(t) P *)
  Hypothesis eta_spec : forall t, pt_eqv (mult A (eta t)) (T t).
  (* LocalComparisonS.eta_add (red:additivity) *)
  Hypothesis eta_add : forall t t', eta (tapp2 s_add t t') ≡ eta t + eta t'.
  (* LocalComparisonS.eta_one *)
  Hypothesis eta_one : eta (tapp0 s_one) ≡ 1.
  (* LocalComparisonS.eta_val *)
  Hypothesis eta_val : forall t t', val t ≡ val t' -> eta t ≡ eta t'.

  (* LocalComparisonS.local_comparison, Lemma red:local-comparison (L1),
     with [ha a] for the term  h a  and [h4a a] for the term  (h - 4) a *)
  Hypothesis local_comparison : forall (K : nat) (q : sQA) (w : Pl A) (h j0 : gterm)
      (ha h4a : gterm -> gterm),
    (1 <= K)%N ->
    (forall p, p \in fd_SE D -> q ≢ p%:R) ->
    (K.+1)%:R < q ->
    above A w q ->
    val h ≢ 0 -> val j0 ≢ 0 ->
    (forall a, val (ha a) ≡ val h * val a) ->
    (forall a, val (h4a a) ≡ (val h - 4%:R) * val a) ->
    (* (i) *)
    (forall a,
         redAS (vP A w) false (T h) /\ redAS (vP A w) false (T (ha a))
      /\ ellKS false K (zparS false (T h)) ≢ 0
      /\ vgeS (vP A w) (ellKS false K (zparS false (T (ha a))) / ellKS false K (zparS false (T h))
                        - qe_of (val a)) K%:R) ->
    (* (ii) *)
    (forall a,
         redAS (vP A w) true (T j0) /\ redAS (vP A w) true (T (h4a a))
      /\ vgeS (vP A w) (zparS true (T (h4a a)) / zparS true (T j0)) K%:R) ->
    forall a, vgeS (vq A q) (val a) 0 /\ vgeS (vq A q) (val a - eta a) K%:R.

  (* [slra] that forgets [eta_one] (it would be reified as an atom and
     then count as used) *)
  Ltac slre := try clear eta_one; slra.

  (** ** Consequences for eta *)

  Lemma eta_zero : eta tzero ≡ 0.
  Proof using HTM eta_add eta_val.
    have h : eta (tadd tzero tzero) ≡ eta tzero.
    { apply: eta_val; rewrite (val_add HTM) (val_zero HTM); sring. }
    move: h; rewrite /tadd eta_add => h; slre.
  Qed.

  Lemma eta_neg t : eta (tneg t) ≡ - eta t.
  Proof using HTM eta_add eta_val.
    have h : eta (tadd t (tneg t)) ≡ eta tzero.
    { apply: eta_val; rewrite (val_add HTM) (val_neg HTM) (val_zero HTM); sring. }
    move: h; rewrite /tadd eta_add eta_zero => h; slre.
  Qed.

  Lemma eta_zero_val t : eta t ≡ 0 -> val t ≡ 0.
  Proof using eta_spec.
    move=> h; have E := eta_spec t; rewrite h in E.
    apply/(pt_eqv_inf E); exact: mult0_flag.
  Qed.

  Lemma eta_inj t t' : eta t ≡ eta t' -> val t ≡ val t'.
  Proof using HTM eta_spec eta_add eta_val.
    move=> h.
    have : val (tsub t t') ≡ 0.
    { apply: eta_zero_val; rewrite /tsub /tadd eta_add eta_neg h; sring. }
    by rewrite /tsub (val_add HTM) (val_neg HTM) subr_eq0.
  Qed.

  Fixpoint tnat (k : nat) : gterm :=
    match k with 0%N => tzero | k'.+1 => tadd tone (tnat k') end.

  Lemma val_tnat k : val (tnat k) ≡ k%:R.
  Proof using HTM.
    elim: k => [ | k IH ]; first exact: (val_zero HTM).
    change (val (tadd tone (tnat k)) ≡ k.+1%:R).
    rewrite (val_add HTM) (val_one HTM) IH natrS; reflexivity.
  Qed.

  Lemma eta_tnat k : eta (tnat k) ≡ k%:R.
  Proof using HTM eta_add eta_one eta_val.
    elim: k => [ | k IH ]; first exact: eta_zero.
    change (eta (tapp2 s_add (tapp0 s_one) (tnat k)) ≡ k.+1%:R).
    rewrite eta_add eta_one IH natrS; reflexivity.
  Qed.

  Lemma eta_int z : eta (tint z) ≡ of_Z z.
  Proof using HTM eta_add eta_one eta_val.
    transitivity (eta (tsub (tnat (Z.to_nat z)) (tnat (Z.to_nat (- z))))).
    { apply: eta_val; rewrite (val_int HTM) /tsub (val_add HTM) (val_neg HTM) !val_tnat.
      exact: of_Z_nat_split. }
    rewrite /tsub /tadd eta_add eta_neg !eta_tnat; symmetry; exact: of_Z_nat_split.
  Qed.

  (* the x-coordinate of a finite point T_t is nonzero (R1) *)
  Lemma T_x_neq0 t : (T t).1 ≢ 0 -> (T t).2.1 ≢ 0.
  Proof using eta_isZ eta_spec.
    move=> hT; have E := eta_spec t.
    case: (sof_eq_dec _ (eta t) 0) => [ e | ne ].
    - by exfalso; apply: hT; apply: eta_zero_val.
    - have [F1 [nx _]] := trR1 (eta_isZ t) ne.
      have [ex _] := pt_eqv_fin E F1.
      by rewrite -ex.
  Qed.

  Lemma val_tminus4 h : val (tsub h (tint 4)) ≡ val h - 4%:R.
  Proof using HTM. rewrite /tsub (val_add HTM) (val_neg HTM) (val_int HTM); sring. Qed.

  (** ** Prop red:index-congruence (DESIGN 5.4, L4) *)

  Theorem index_congruence (K : nat) (tA : gterm) (W : RepTerms) (i : i3) (q : sQA) :
    (1 <= K)%N -> CoarseningS.RepSemS val K tA W -> primeA A q ->
    0 < vq A q (MK A K (slopeS val W tA i)) ->
    forall a, vgeS (vq A q) (val a) 0 /\ vgeS (vq A q) (val a - eta a) K%:R.
  Proof using HWF HTM eta_isZ eta_spec local_comparison.
    move=> hK HR hq hM.
    (* red:odd-r *)
    have [hgood [j hodd]] := odd_contact_step HWF HR hq hM.
    (* Lemma red:coarsening *)
    have [sg [w [hw [Hloc Hform]]]] :=
      coarsening HTM hq hgood (rs_r HR j) hodd (rs_B HR j).
    set h := rp_h W j sg; set j0 := rp_j0 W j sg.
    have Hx t : (T t).1 ≢ 0 -> (T t).2.1 ≢ 0 by apply: T_x_neq0.
    apply: (local_comparison (h := h) (j0 := j0) (ha := tmul h)
              (h4a := tmul (tsub h (tint 4))) hK _ _ hw).
    - by move=> p hp; case: hgood => _ hS; apply: hS; apply: Sfix_SE.
    - by case: hgood.
    - exact: (rs_h HR j sg).
    - exact: (rs_j0 HR j sg).
    - by move=> a; exact: (val_mul HTM).
    - by move=> a; rewrite (val_mul HTM) val_tminus4; reflexivity.
    - move=> a; have [F1 [F2 [E3 [L4 _]]]] := rs_conds HR j sg a.
      split; first exact: Hform (Hx h) F1.
      split; first exact: Hform (Hx _) F2.
      split => //; exact: Hloc K _ hK L4.
    - move=> a; have [_ [_ [_ [_ [F5 [F6 L7]]]]]] := rs_conds HR j sg a.
      split; first exact: Hform (Hx j0) F5.
      split; first exact: Hform (Hx _) F6.
      exact: Hloc K _ hK L7.
  Qed.

  (** ** Prop red:finite-test-success (DESIGN 5.4 L5, 2.7) *)

  Variables (n : nat) (f : dio_polynomial (pos n) (pos 0)).

  (* the root tuple a_1, ..., a_n *)
  Definition acst (i : pos n) : gterm := tapp0 (s_cst (pos2nat i)).

  (* TheoryS.InstSemS, root component (ax_root): f(a_1, ..., a_n) = 0 in R *)
  Hypothesis root : dp_evalS (fun v => val (tapp0 (s_cst (pos2nat v)))) (fun _ => 0) f ≡ 0.

  (* ax_rep K, for all K >= 1 and all ring elements A, as the record of
     CoarseningS.v *)
  Hypothesis rep : forall (K : nat) (tA : gterm), (1 <= K)%N ->
    exists W, CoarseningS.RepSemS val K tA W.

  (* [slre] that also forgets [root] (it would be reified as an atom and
     then count as used) *)
  Ltac slrc := try clear eta_one; try clear root; slra.

  (* the indices of the root tuple and delta = f(eta a_1, ..., eta a_n) *)
  Definition ea (i : pos n) : sQA := eta (acst i).
  Definition delta : sQA := dp_evalS ea (fun _ => 0) f.

  (* the constants of red:B-D, red:error-bound and Section 2.7 *)
  Definition Dg : nat := maxn 1%N (pdeg f).
  Definition Kc : nat := (fd_c D * Dg)%N.               (* K = c max(1, deg f) *)
  Definition Cf : nat := maxn 1%N (pc f).               (* C_f >= 1 *)
  Definition HCf : nat := (HK D Kc * Cf)%N.
  Definition N1 : nat := (fd_Nh D * (9 * HCf + 6 + fd_Ch D))%N.

  Lemma Dg_pos : (0 < Dg)%N.
  Proof. by rewrite /Dg leq_maxl. Qed.

  Lemma Kc_pos : (1 <= Kc)%N.
  Proof using HWF. by rewrite /Kc muln_gt0 (wf_c HWF) Dg_pos. Qed.

  Lemma isZ_ZR z : isZA (of_Z z).
  Proof. rewrite of_Z_nat_split; apply: isZ_sub; apply: isZ_nat. Qed.

  Lemma isZ_evalR (φ : pos n -> sQA) (p : dio_polynomial (pos n) (pos 0)) :
    (forall i, isZA (φ i)) -> isZA (dp_evalS φ (fun _ => 0) p).
  Proof.
    move=> h; elim: p => [ c | v | i | [] p Hp q Hq ] /=.
    - exact: isZ_ZR.
    - exact: h.
    - exact: isZ0.
    - exact: trZ1_add.
    - exact: trZ1_mul.
  Qed.

  Lemma delta_isZ : isZA delta.
  Proof using eta_isZ. by apply: isZ_evalR => i; apply: eta_isZ. Qed.

  (* delta = 0: elementarity (SIG) gives an integer zero *)
  Lemma delta0_H10Z : delta ≡ 0 -> H10Z (existT _ n f).
  Proof using eta_isZ.
    move=> h0; have [zs hzs] := trSIG (ex_intro _ ea (conj (fun i => eta_isZ (acst i)) h0)).
    by exists zs.
  Qed.

  Section delta_neq0.

    Hypothesis hd : delta ≢ 0.

    (* polynomial congruences at a prime q (red:error-divisibility) *)
    Lemma poly_cong (q : sQA) (x y : pos n -> sQA) (k : sQA) (p : dio_polynomial (pos n) (pos 0)) :
      primeA A q ->
      (forall v, vgeS (vq A q) (x v) 0) -> (forall v, vgeS (vq A q) (y v) 0) ->
      (forall v, vgeS (vq A q) (x v - y v) k) ->
         vgeS (vq A q) (dp_evalS x (fun _ => 0) p) 0
      /\ vgeS (vq A q) (dp_evalS y (fun _ => 0) p) 0
      /\ vgeS (vq A q) (dp_evalS x (fun _ => 0) p - dp_evalS y (fun _ => 0) p) k.
    Proof.
      move=> hq hx hy hxy.
      have hZ z : vgeS (vq A q) (of_Z z) 0.
      { case: (sof_eq_dec _ (of_Z z : sQA) 0) => [ E | nz ]; first by left.
        by right; apply: trV4 => //; apply: isZ_ZR. }
      elim: p => [ c | v | i | [] p [Hp1 [Hp2 Hp3]] q' [Hq1 [Hq2 Hq3]] ] /=.
      - split; [ exact: hZ | split; [ exact: hZ | left; exact: subrr ] ].
      - by split; [ | split ].
      - split; [ left; reflexivity | split; [ left; reflexivity | left; exact: subrr ] ].
      - split; first exact: (vq_ge_add hq Hp1 Hq1).
        split; first exact: (vq_ge_add hq Hp2 Hq2).
        have E : dp_evalS x (fun=> 0) p + dp_evalS x (fun=> 0) q'
                  - (dp_evalS y (fun=> 0) p + dp_evalS y (fun=> 0) q')
                ≡ (dp_evalS x (fun=> 0) p - dp_evalS y (fun=> 0) p)
                  + (dp_evalS x (fun=> 0) q' - dp_evalS y (fun=> 0) q') by sring.
        rewrite E; exact: (vq_ge_add hq Hp3 Hq3).
      - split; first by have := vq_ge_mul hq Hp1 Hq1; rewrite addr0.
        split; first by have := vq_ge_mul hq Hp2 Hq2; rewrite addr0.
        have E : dp_evalS x (fun=> 0) p * dp_evalS x (fun=> 0) q'
                  - dp_evalS y (fun=> 0) p * dp_evalS y (fun=> 0) q'
                ≡ dp_evalS x (fun=> 0) p * (dp_evalS x (fun=> 0) q' - dp_evalS y (fun=> 0) q')
                  + (dp_evalS x (fun=> 0) p - dp_evalS y (fun=> 0) p) * dp_evalS y (fun=> 0) q'
                  by sring.
        rewrite E; apply: (vq_ge_add hq).
        + by have := vq_ge_mul hq Hp1 Hq3; rewrite add0r.
        + by have := vq_ge_mul hq Hp3 Hq2; rewrite addr0.
    Qed.

    (* red:error-divisibility: v_q(delta) >= K at every counted prime *)
    Lemma delta_div (tA : gterm) (W : RepTerms) (i : i3) (q : sQA) :
      CoarseningS.RepSemS val Kc tA W -> primeA A q ->
      0 < vq A q (MK A Kc (slopeS val W tA i)) -> Kc%:R <= vq A q delta.
    Proof using HWF HTM eta_isZ eta_spec local_comparison root hd.
      move=> HR hq hM.
      have IC := index_congruence Kc_pos HR hq hM.
      have hy : forall v, vgeS (vq A q) (ea v) 0.
      { move=> v; case: (sof_eq_dec _ (ea v) 0) => [ E | nz ]; first by left.
        by right; apply: trV4 => //; apply: eta_isZ. }
      have [_ [_ hc]] := poly_cong (x := fun v => val (acst v)) f hq
        (fun v => (IC (acst v)).1) hy (fun v => (IC (acst v)).2).
      move: hc; rewrite /acst root sub0r -/delta => hc.
      have := vq_ge_opp hq hc; rewrite opprK; case => [ e | // ].
      by exfalso; apply: hd.
    Qed.

    (* red:radical-divides and |M^K| <= |delta| *)
    Lemma MK_bound (tA : gterm) (W : RepTerms) (i : i3) :
      CoarseningS.RepSemS val Kc tA W -> MK A Kc (slopeS val W tA i) ^+ Kc <= `|delta|.
    Proof using HWF HTM eta_isZ eta_spec local_comparison root hd.
      move=> HR.
      have [nv nL] := forms_neq0 HWF HR i.
      have hM1 : 1 <= MK A Kc (slopeS val W tA i) by have [_ [h _]] := trH1 Kc nv nL; exact h.
      have [z [hz e]] := @trH2 D A Kc (slopeS val W tA i) delta delta_isZ hd
                           (fun q hq hM => delta_div HR hq hM).
      have hM0 : 0 <= MK A Kc (slopeS val W tA i) ^+ Kc.
      { apply: exprn_ge0; slrc. }
      have nz : z ≢ 0.
      { move=> hz0; apply: hd; rewrite e hz0 mulr0; reflexivity. }
      have hz1 : 1 <= `|z|.
      { case: (lerP _ 0 z) => h0.
        - rewrite (ger0_norm _ _ h0); apply: trV0 => //.
          apply/lt_neqAle; split => // E; apply: nz; symmetry; exact E.
        - rewrite (ltr0_norm _ _ h0); apply: trV0; [ exact: trZ1_opp | by apply/oppr_gt0 ]. }
      rewrite e normrM (ger0_norm _ _ hM0); exact: ler_peMr.
    Qed.

    (* a root bound:  X^d <= C B^d  gives  X <= C B *)
    Lemma root_bound (X C B : sQA) (d : nat) :
      1 <= X -> 1 <= C -> 1 <= B -> (0 < d)%N -> X ^+ d <= C * B ^+ d -> X <= C * B.
    Proof using.
      move=> hX hC hB hd0 h.
      apply/leNgt => hlt.
      have hCB : 0 <= C * B by apply: mulr_ge0; slrc.
      have h1 : (C * B) ^+ d < X ^+ d by apply/ltrXn2r => //; slrc.
      have h2 : C * B ^+ d <= (C * B) ^+ d.
      { rewrite exprMn; apply: ler_wpM2r; first by apply: exprn_ge0; slrc.
        have := @ler_weXn2l _ C 1 d hC hd0; rewrite expr1; done. }
      move: h h1 h2; clear -hd0; slrc.
    Qed.

    Section with_B.

      Variable B : sQA.
      Hypothesis hB1 : 1 <= B.
      Hypothesis hBa : forall i, `|ea i| <= B.

      Lemma delta_bound : `|delta| <= Cf%:R * B ^+ Dg.
      Proof using hB1 hBa.
        have H := @poly_bound _ _ _ ea B f hB1 hBa.
        have H2 : (pc f)%:R * B ^+ pdeg f <= Cf%:R * B ^+ Dg.
        { apply: ler_pM.
          - exact: ler0n.
          - by apply: exprn_ge0; slrc.
          - by apply/ler_nat; exact: leq_maxr.
          - apply: ler_weXn2l => //; exact: leq_maxr. }
        rewrite /delta; move: H H2; clear -hB1; slrc.
      Qed.

      (* M_K(s_i)^c <= C_f B *)
      Lemma MKc_bound (tA : gterm) (W : RepTerms) (i : i3) :
        CoarseningS.RepSemS val Kc tA W -> MK A Kc (slopeS val W tA i) ^+ fd_c D <= Cf%:R * B.
      Proof using HWF HTM eta_isZ eta_spec local_comparison root hd hB1 hBa.
        move=> HR.
        have [nv nL] := forms_neq0 HWF HR i.
        have hM1 : 1 <= MK A Kc (slopeS val W tA i) by have [_ [h _]] := trH1 Kc nv nL; exact h.
        apply: (root_bound (d := Dg)).
        - exact: exprn_ege1.
        - by apply/ler1n; exact: leq_maxl.
        - exact: hB1.
        - exact: Dg_pos.
        - rewrite -exprM -/Kc.
          have := MK_bound i HR; have := delta_bound.
          clear -hB1; slrc.
      Qed.

      (* red:slope-height *)
      Lemma slope_height (tA : gterm) (W : RepTerms) (i : i3) :
        CoarseningS.RepSemS val Kc tA W -> ht A (slopeS val W tA i) <= HCf%:R * B.
      Proof using HWF HTM eta_isZ eta_spec local_comparison root hd hB1 hBa.
        move=> HR.
        have [nv nL] := forms_neq0 HWF HR i.
        have H3 : ht A (slopeS val W tA i) <= (HK D Kc)%:R * MK A Kc (slopeS val W tA i) ^+ fd_c D.
        { exact: (trH3 Kc nv nL). }
        have H4 : (HK D Kc)%:R * MK A Kc (slopeS val W tA i) ^+ fd_c D
                  <= (HK D Kc)%:R * (Cf%:R * B).
        { apply: ler_wpM2l; first exact: ler0n.
          exact: (MKc_bound i HR). }
        rewrite /HCf natrM -mulrA; move: H3 H4; clear -hB1; slrc.
      Qed.

      (* red:all-ring-height *)
      Lemma ring_height (tA : gterm) : ht A (val tA) <= 3%:R * HCf%:R * B + 2%:R.
      Proof using HWF HTM eta_isZ eta_spec local_comparison root hd hB1 hBa rep.
        have [W HR] := rep tA Kc_pos.
        have nv := rs_v HR.
        have E : val tA ≡ slopeS val W tA I1 + slopeS val W tA I2 + slopeS val W tA I3.
        { rewrite /slopeS; cbn [uvalS]; sfield; exact: nv. }
        rewrite E.
        have := @trHS D A (slopeS val W tA I1) (slopeS val W tA I2) (slopeS val W tA I3).
        have := slope_height I1 HR; have := slope_height I2 HR;
          have := slope_height I3 HR.
        clear -hB1; slrc.
      Qed.

      (* red:elliptic-upper and red:elliptic-lower: B <= N1 *)
      Lemma B_bound : B ≡ 1 \/ (exists j, B ≡ `|ea j|) -> B <= N1%:R.
      Proof using HWF HTM eta_isZ eta_spec local_comparison root hd hB1 hBa rep.
        have hN1 : (1 <= N1)%N.
        { rewrite /N1 muln_gt0 (wf_Nh HWF) /=.
          apply: (leq_trans _ (leq_addr _ _)); exact: (leq_trans _ (leq_addl _ _)). }
        case => [ E | [j hj] ]; first by rewrite E; apply/ler1n.
        have nea : ea j ≢ 0.
        { move=> e; move: hB1; rewrite hj e normr0; exact: ler10. }
        have [x [y [hm [nx _]]]] := trR1_ex (eta_isZ (acst j)) nea.
        have hT : pt_eqv (1, (x, y)) (T (acst j)).
        { etransitivity; [ symmetry; exact: hm | exact: eta_spec ]. }
        have [ex _] := pt_eqv_fin hT (oner_neq0 _).
        cbn [fst snd] in ex.
        set x0 := val (tcoord cx0 (acst j)); set x1 := val (tcoord cx1 (acst j)).
        set x2 := val (tcoord cx2 (acst j)).
        have ex' : x ≡ QE x0 x1 / qe_of x2 by exact: ex.
        have nx2 : x2 ≢ 0.
        { move=> e; apply: nx; rewrite ex' e qe_of0 /sr_div qe_inv0 mulr0; reflexivity. }
        have hex : exists y0, pt_eqv (mult A (ea j)) (1, (QE x0 x1 / qe_of x2, y0)).
        { exists y; rewrite hm; apply: pt_eqv_mk; first reflexivity.
          split; [ exact: ex' | reflexivity ]. }
        have hHL := trHL (eta_isZ (acst j)) nea nx2 hex.
        have h0 := ring_height (tcoord cx0 (acst j)).
        have h1 := ring_height (tcoord cx1 (acst j)).
        have h2 := ring_height (tcoord cx2 (acst j)).
        rewrite -/x0 in h0; rewrite -/x1 in h1; rewrite -/x2 in h2.
        (* B^2 <= Nh (9 H C_f B + 6 + Ch) <= N1 B *)
        have e2 : ea j ^+ 2 ≡ B * B by rewrite hj -real_normK; sring.
        have hNh : (0 : sQA) <= (fd_Nh D)%:R by apply: ler0n.
        have hC : ((fd_Ch D)%:R : sQA) <= (fd_Ch D)%:R * B by apply: ler_peMr => //; apply: ler0n.
        have hsum : ht A x0 + ht A x1 + ht A x2 + (fd_Ch D)%:R
                    <= (9%:R * HCf%:R + 6%:R + (fd_Ch D)%:R) * B.
        { move: h0 h1 h2 hC; clear -hB1; slrc. }
        have hB2 : B * B <= ((fd_Nh D)%:R * (9%:R * HCf%:R + 6%:R + (fd_Ch D)%:R)) * B.
        { have H := @ler_wpM2l _ _ _ _ hNh hsum.
          rewrite e2 in hHL.
          have E : ((fd_Nh D)%:R * (9%:R * HCf%:R + 6%:R + (fd_Ch D)%:R)) * B
                   ≡ (fd_Nh D)%:R * ((9%:R * HCf%:R + 6%:R + (fd_Ch D)%:R) * B) by sring.
          rewrite E; move: hHL H; slrc. }
        have EN : (N1%:R : sQA) ≡ (fd_Nh D)%:R * (9%:R * HCf%:R + 6%:R + (fd_Ch D)%:R).
        { exact: (natr_N1 sQA (fd_Nh D) HCf (fd_Ch D)). }
        have hB0 : 0 < B by slrc.
        rewrite EN; apply/(ler_pM2r _ _ _ _ hB0); exact: hB2.
      Qed.

    End with_B.

    (* every index eta(a_j) is an ordinary integer *)
    Lemma ea_ordinary : forall i, exists z : Z, ea i ≡ of_Z z.
    Proof using HWF HTM eta_isZ eta_spec local_comparison root hd rep.
      have [B [hB1 [hBa hBm]]] := pos_max ea.
      have hB := B_bound hB1 hBa hBm.
      move=> i; apply: (isZ_interval (N := N1)); first exact: eta_isZ.
      have := hBa i; move: hB; slrc.
    Qed.

  End delta_neq0.

  (* Prop red:finite-test-success *)
  Theorem finite_test_success : H10Z (existT _ n f).
  Proof using HWF HTM eta_isZ eta_spec eta_add eta_one eta_val local_comparison root rep.
    case: (sof_eq_dec _ delta 0) => [ h0 | hd ]; first exact: delta0_H10Z.
    have [zs hzs] := fin_choice (ea_ordinary hd).
    (* val a_j = n_j by eta (n_j) = n_j and injectivity of eta *)
    have hv i : val (acst i) ≡ of_Z (zs i).
    { transitivity (val (tint (zs i))); last exact: (val_int HTM).
      apply: eta_inj; rewrite eta_int; exact: hzs. }
    exists zs; apply: (@of_Z_eq0 (sQ A)).
    rewrite -dp_evalS_Z.
    transitivity (dp_evalS (fun v => val (tapp0 (s_cst (pos2nat v)))) (fun _ => 0) f); last exact: root.
    apply: dp_evalS_ext => i; [ symmetry; exact: hv | reflexivity ].
  Qed.

End height.
