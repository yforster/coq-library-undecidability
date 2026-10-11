(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A (task P2b): LocalComparison.v over the setoid ambient
   structure [A : AmbientS D] of AmbientS.v (carrier [sQ A : SOF]).

   A faithful port of LocalComparison.v (same lemma names, same proofs
   step by step), with the conventions of SETOID.md:
   - the generic valuation Section is over [F : SRing], [R : SOF],
     [v : F -> R] with the new hypotheses [v_wd] (Proper) and [F_dec]
     (Prop-level decidability, [sof_eq_dec] / [qe_eq_dec]), [F_1_neq_0];
     "u is a unit" becomes the explicit [u^-1 * u ≡ 1];
   - points are [ptS] (flag encoding); [T t := TvS val t = (val t, (Xc t,
     Yc t))]: the flag is [val t] itself; [Xc], [Yc], [Qch] are [XvS],
     [YvS], [QvCS] of TheoryS.v;
   - [eta t := sof_nz (val t) * idx A (Xc t, Yc t)] (the [if val t == 0
     then 0 else idx ...] of LocalComparison.v);
   - the Section hypotheses are stated EXACTLY as the components of
     [InstSemS] (TheoryS.v), so that the glue with [TermModel_InstSemS]
     is trivial:
       Hring : forall t, ring_okS val t           (tm_ring)
       Hfun  : forall t t', fun_okS val t t'       (tm_fun)
       H_chain : forall t, ChainSemS val D t       (InstSemS, 4th)
       H_add : forall t t', AddSemS val t t'       (InstSemS, 3rd)
       H_P : pt_eqv (T (tapp0 s_one)) (pt_ratS (Pgen D))   (InstSemS, 2nd)
     The group law [ADDrelS (T t) (T t') (T (tapp2 s_add t t'))] of
     LocalComparison.v is derived here ([H_addrel], via [add_ADDrelS]);
     [TermModelS_LC_hyps] (end of file) extracts all five from a
     [TermModelS A (Inst D f) val].
   Statement changes: [=]/[!=] become [≡]/[≢], [redA vge ellK zpar goodA]
   become [redAS vgeS ellKS zparS goodAS]; [eta_spec] is [pt_eqv (mult A
   (eta t)) (T t)], [eta_conj] and [eta_zpar] are up to [pt_eqv]/[≡];
   [ADDrel_fun] becomes [ADDrelS_fun] (conclusion [pt_eqv]); [mult_inj]
   has premise [pt_eqv]. Everything is closed under the global context. *)

From Stdlib Require Import Setoid Morphisms RelationClasses ZArith.

From Undecidability.H10 Require H10Z.

From Undecidability.H10.Rational
  Require Import RatUtil Signature FixedData Theory.

From Undecidability.H10.Rational
  Require Import SOF SOFTactics SOFqe SOFTheory SignatureS AmbientS TheoryS.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.
Import SOFTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope sof_scope.

(** * Generic valuation algebra *)

Section valuation.

  Variables (F : SRing) (R : SOF) (v : F -> R).

  Add Ring F_ring : (sr_rth F) (setoid (sr_setoid F) (sr_ext F),
    morphism (of_Z_morph F), constants [sof_cst], power_tac (sr_pow_th F) [sof_pow_cst]).
  Add Field R_field : (@sof_fth R) (setoid (sr_setoid R) (sr_ext R),
    morphism (of_Z_morph R), constants [sof_cst],
    power_tac (sr_pow_th R) [sof_pow_cst], completeness (sof_Z_complete R)).

  (* new: v respects the setoid equality; Prop-level decidability of ≡ in F *)
  Hypothesis v_wd : Proper (eqv ==> eqv) v.
  Hypothesis F_dec : forall x y : F, x ≡ y \/ x ≢ y.
  Hypothesis F_1_neq_0 : (1 : F) ≢ 0.

  Hypothesis vdom : forall x y : F, x ≢ 0 -> y ≢ 0 -> x * y ≢ 0.
  Hypothesis vmul : forall x y : F, x ≢ 0 -> y ≢ 0 -> v (x * y) ≡ v x + v y.
  Hypothesis vultra : forall x y : F, x ≢ 0 -> y ≢ 0 -> x + y ≢ 0 ->
                        sof_min (v x) (v y) <= v (x + y).

  Existing Instance v_wd.

  Lemma val1 : v 1 ≡ 0.
  Proof using F_1_neq_0 vmul v_wd.
    have h := vmul F_1_neq_0 F_1_neq_0; rewrite mulr1 in h; sof_lra.
  Qed.

  Lemma valN1 : v (- 1) ≡ 0.
  Proof using F_1_neq_0 vmul v_wd.
    have hN : (- (1) : F) ≢ 0 by rewrite oppr_eq0; exact F_1_neq_0.
    have h := vmul hN hN; rewrite mulrNN mulr1 val1 in h; sof_lra.
  Qed.

  Lemma valN x : x ≢ 0 -> v (- x) ≡ v x.
  Proof using F_1_neq_0 vmul v_wd.
    move=> hx; have hN : (- (1) : F) ≢ 0 by rewrite oppr_eq0; exact F_1_neq_0.
    rewrite -mulN1r vmul // valN1 add0r; reflexivity.
  Qed.

  Lemma vge_le x k k' : k' <= k -> vgeS v x k -> vgeS v x k'.
  Proof. by move=> Hk [ H | H ]; [ left | right; exact: le_trans H ]. Qed.

  Lemma vge0 k : vgeS v 0 k.
  Proof. by left; reflexivity. Qed.

  Lemma vge_opp x k : vgeS v x k -> vgeS v (- x) k.
  Proof using F_1_neq_0 vmul v_wd F_dec.
    case=> [ h | h ]; first by left; rewrite h oppr0; reflexivity.
    case: (F_dec x 0) => [ h0 | hx ]; first by left; rewrite h0 oppr0; reflexivity.
    by right; rewrite valN.
  Qed.

  Lemma vge_add x y k : vgeS v x k -> vgeS v y k -> vgeS v (x + y) k.
  Proof using vultra F_dec v_wd.
    case=> [ hx0 | hx ]; first by rewrite hx0 add0r.
    case=> [ hy0 | hy ]; first by rewrite hy0 addr0; right.
    case: (F_dec x 0) => [ h | nx ]; first by rewrite h add0r; right.
    case: (F_dec y 0) => [ h | ny ]; first by rewrite h addr0; right.
    case: (F_dec (x + y) 0) => [ h | nxy ]; first by left.
    right; apply: le_trans (vultra nx ny nxy); by apply/le_min.
  Qed.

  Lemma vge_sub x y k : vgeS v x k -> vgeS v y k -> vgeS v (x - y) k.
  Proof using F_1_neq_0 vmul vultra F_dec v_wd.
    by move=> Hx Hy; apply: vge_add => //; apply: vge_opp.
  Qed.

  Lemma vge_mul x y k l : vgeS v x k -> vgeS v y l -> vgeS v (x * y) (k + l).
  Proof using vmul F_dec v_wd.
    case=> [ h | Hx ]; first by left; rewrite h mul0r; reflexivity.
    case=> [ h | Hy ]; first by left; rewrite h mulr0; reflexivity.
    case: (F_dec x 0) => [ h | nx ]; first by left; rewrite h mul0r; reflexivity.
    case: (F_dec y 0) => [ h | ny ]; first by left; rewrite h mulr0; reflexivity.
    by right; rewrite vmul //; apply: lerD.
  Qed.

  (* "u is a unit" is stated as u^-1 * u ≡ 1 *)
  Lemma val_div x u : x ≢ 0 -> u ≢ 0 -> u^-1 * u ≡ 1 -> v (x / u) ≡ v x - v u.
  Proof using F_1_neq_0 vdom vmul v_wd.
    move=> nx nu uu.
    have nu' : u^-1 ≢ 0.
    { move=> H; apply: F_1_neq_0; rewrite -uu H; sring. }
    have nxu : x / u ≢ 0 by exact: vdom.
    have := vmul nxu nu.
    have -> : x / u * u ≡ x by rewrite /sr_div -mulrA uu mulr1; reflexivity.
    move=> H; sof_lra.
  Qed.

  (* dividing by a unit of valuation 0 preserves lower bounds *)
  Lemma vge_div_unit x u k : u ≢ 0 -> u^-1 * u ≡ 1 -> v u ≡ 0 -> vgeS v x k -> vgeS v (x / u) k.
  Proof using F_1_neq_0 vdom vmul v_wd F_dec.
    move=> nu uu vu [ h | H ]; first by left; rewrite h /sr_div mul0r; reflexivity.
    case: (F_dec x 0) => [ h | nx ]; first by left; rewrite h /sr_div mul0r; reflexivity.
    by right; rewrite val_div // vu subr0.
  Qed.

  (* the strict ultrametric inequality *)
  Lemma val_add_lt x y : x ≢ 0 -> y ≢ 0 -> v x < v y -> x + y ≢ 0 /\ v (x + y) ≡ v x.
  Proof using F_1_neq_0 vmul vultra v_wd.
    move=> nx ny lt.
    have nxy : x + y ≢ 0.
    { move=> H; have Hx : x ≡ - y by transitivity ((x + y) - y); [ sring | rewrite H; sring ].
      move: lt; rewrite Hx valN //; sof_lra. }
    split => //.
    have ny' : - y ≢ 0 by rewrite oppr_eq0.
    have H1 := vultra nx ny nxy.
    have := vultra nxy ny'.
    have -> : x + y + - y ≡ x by sring.
    move=> H2; have {}H2 := H2 nx.
    move: H1 H2; rewrite valN // !ge_min => [] [ H1 | H1 ] [ H2 | H2 ]; sof_lra.
  Qed.

End valuation.

(** * Algebra in the ambient structure *)

Section ambient_alg.

  Variables (D : FixedData) (A : AmbientS D).

  Local Abbreviation sQA := (sQ A).

  Add Field aa_field : (@sof_fth sQA) (setoid (sr_setoid sQA) (sr_ext sQA),
    morphism (of_Z_morph sQA), constants [sof_cst],
    power_tac (sr_pow_th sQA) [sof_pow_cst], completeness (sof_Z_complete sQA)).
  Add Field aa_qe_field : (qe_fth sQA (@trZ0 D A))
    (setoid (sr_setoid (qe_SRing sQA)) (sr_ext (qe_SRing sQA)),
    morphism (of_Z_morph (qe_SRing sQA)), constants [sof_cst],
    power_tac (sr_pow_th (qe_SRing sQA)) [sof_pow_cst], completeness (qe_Z_complete sQA)).

  (* Z0 makes qe sQ a field: nonzero elements are units (replaces
     [qe_neq0_unit]: "x is a unit" is [x^-1 * x ≡ 1]) *)
  Lemma qe_neq0_unit (x : qe_SRing sQA) : x ≢ 0 -> x^-1 * x ≡ 1.
  Proof. exact: (@qe_inv_l sQA (@trZ0 D A) x). Qed.

  Lemma qe_mulf_neq0 (x y : qe_SRing sQA) : x ≢ 0 -> y ≢ 0 -> x * y ≢ 0.
  Proof. exact: (qmulf_neq0 (@trZ0 D A)). Qed.

  Lemma qe_mulIf (c a b : qe_SRing sQA) : c ≢ 0 -> a * c ≡ b * c -> a ≡ b.
  Proof.
    move=> nc H; transitivity (a * c / c); first by sfield.
    rewrite H; sfield; exact nc.
  Qed.

  Lemma qe_nat_neq0 (n : nat) : (0 < n)%N -> (n%:R : qe_SRing sQA) ≢ 0.
  Proof.
    move=> n0; rewrite qe_natE => -[ H _ ]; move: H; rewrite pnatr_eq0 => Hn.
    by rewrite Hn in n0.
  Qed.

  Lemma qe_inv_neq0 (x : qe_SRing sQA) : x ≢ 0 -> x^-1 ≢ 0.
  Proof. exact: (qinvf_neq0 (@trZ0 D A)). Qed.

  Lemma qe_conj_neq0 (x : qe_SRing sQA) : x ≢ 0 -> qe_conj x ≢ 0.
  Proof. exact: (@qe_e_neq0S sQA true x). Qed.

  Lemma qe_e_neq0 sg (x : qe_SRing sQA) : x ≢ 0 -> qe_e sg x ≢ 0.
  Proof. exact: qe_e_neq0S. Qed.

  Lemma qe_of_eq0 (x : sQA) : qe_of x ≡ 0 -> x ≡ 0.
  Proof. by case. Qed.

  (* functionality of the addition relation (DESIGN 1.3); uses Z0 *)
  Lemma ADDrelS_fun (p1 p2 p3 p3' : ptS sQA) :
    ADDrelS p1 p2 p3 -> ADDrelS p1 p2 p3' -> pt_eqv p3 p3'.
  Proof.
    have two0 : (2%:R : qe_SRing sQA) ≢ 0 by apply: qe_nat_neq0.
    have y0 (y1 y2 : qe_SRing sQA) : y1 ≡ - y2 -> y1 ≡ y2 -> y1 ≡ 0.
    { move=> E1 E2; case: (qe_eq_dec _ y1 0) => // ny; exfalso.
      have H : y1 + y2 ≡ 0 by rewrite E1; sring.
      apply: (qe_mulf_neq0 two0 ny).
      transitivity (y1 + y2); [ rewrite -E2; sring | exact H ]. }
    case: p1 => z1 [ x1 y1 ]; case: p2 => z2 [ x2 y2 ].
    case: p3 => z3 [ x3 y3 ]; case: p3' => z3' [ x3' y3' ].
    change (car (qe_SRing sQA)) in x1, y1, x2, y2, x3, y3, x3', y3'.
    case: (sof_eq_dec _ z1 0) => Z1.
    { move=> /(@ADDrelS_O_l _ (z1, (x1, y1)) _ _ Z1) E /(@ADDrelS_O_l _ (z1, (x1, y1)) _ _ Z1) E'.
      etransitivity; [ exact E | symmetry; exact E' ]. }
    case: (sof_eq_dec _ z2 0) => Z2.
    { move=> /(@ADDrelS_O_r _ (z1, (x1, y1)) (z2, (x2, y2)) _ Z1 Z2) E
             /(@ADDrelS_O_r _ (z1, (x1, y1)) (z2, (x2, y2)) _ Z1 Z2) E'.
      etransitivity; [ exact E | symmetry; exact E' ]. }
    move=> [ [ N _ ] | [ [ _ [ N _ ] ] | [ _ [ _ H ] ] ] ]; [ by exfalso; apply: Z1 | by exfalso; apply: Z2 | ].
    move=> [ [ N _ ] | [ [ _ [ N _ ] ] | [ _ [ _ H' ] ] ] ]; [ by exfalso; apply: Z1 | by exfalso; apply: Z2 | ].
    move: H H'; rewrite /ADDfinS; cbn [fst snd].
    case=> [ [ e1 [ e2 Z3 ] ] | [ Z3 H ] ]; case=> [ [ e1' [ e2' Z3' ] ] | [ Z3' H' ] ].
    - exact: pt_eqv_O.
    - exfalso; case: H' => [ [ ne _ ] | [ _ [ ey [ ny _ ] ] ] ]; first by apply: ne.
      by apply: ny; apply: y0 e2 ey.
    - exfalso; case: H => [ [ ne _ ] | [ _ [ ey [ ny _ ] ] ] ]; first by apply: ne.
      by apply: ny; apply: y0 e2' ey.
    - apply: pt_eqv_S => //.
      case: H => [ [ ne [ c1 c2 ] ] | [ e [ ey [ ny [ t1 t2 ] ] ] ] ];
      case: H' => [ [ ne' [ c1' c2' ] ] | [ e' [ ey' [ ny' [ t1' t2' ] ] ] ] ];
        try by exfalso; first [ apply: ne; exact e' | apply: ne'; exact e ].
      + have nd : x2 - x1 ≢ 0 by rewrite subr_eq0 => N; apply: ne; symmetry.
        have nd2 : (x2 - x1) ^+ 2 ≢ 0 by apply: (qexpf_neq0 (@trZ0 D A)).
        have ex : x3 ≡ x3'.
        { have E : (x3 + x1 + x2) * (x2 - x1) ^+ 2 ≡ (x3' + x1 + x2) * (x2 - x1) ^+ 2.
          { rewrite c1 c1'; reflexivity. }
          have {}E := qe_mulIf nd2 E.
          transitivity (x3 + x1 + x2 - x1 - x2); first by sring.
          rewrite E; sring. }
        have ey3 : y3 ≡ y3'.
        { have E : (y3 + y1) * (x2 - x1) ≡ (y3' + y1) * (x2 - x1).
          { rewrite c2 c2' ex; reflexivity. }
          have {}E := qe_mulIf nd E.
          transitivity (y3 + y1 - y1); first by sring.
          rewrite E; sring. }
        by split.
      + have nd : 2%:R * y1 ≢ 0 by apply: qe_mulf_neq0.
        have nd2 : (2%:R * y1) ^+ 2 ≢ 0 by apply: (qexpf_neq0 (@trZ0 D A)).
        have ex : x3 ≡ x3'.
        { have E : (x3 + 2%:R * x1) * (2%:R * y1) ^+ 2 ≡ (x3' + 2%:R * x1) * (2%:R * y1) ^+ 2.
          { rewrite t1 t1'; reflexivity. }
          have {}E := qe_mulIf nd2 E.
          transitivity (x3 + 2%:R * x1 - 2%:R * x1); first by sring.
          rewrite E; sring. }
        have ey3 : y3 ≡ y3'.
        { have E : (y3 + y1) * (2%:R * y1) ≡ (y3' + y1) * (2%:R * y1).
          { rewrite t2 t2' ex; reflexivity. }
          have {}E := qe_mulIf nd E.
          transitivity (y3 + y1 - y1); first by sring.
          rewrite E; sring. }
        by split.
  Qed.

  (* "unique expression nP": mult is injective on *Z (from R1, R3 and
     functionality of ADDrelS; DESIGN 2.1) *)
  Lemma mult_inj n n' : isZ A n -> isZ A n' -> pt_eqv (mult A n) (mult A n') -> n ≡ n'.
  Proof.
    move=> zn zn' E.
    have zN := trZ1_opp zn'.
    have H1 := trR3 zn zN; have H2 := trR3 zn' zN.
    rewrite E in H1.
    have H := ADDrelS_fun H1 H2.
    case: (sof_eq_dec _ (n - n') 0) => [ E0 | nz ]; first by apply/subr_eq0.
    have [ F1 _ ] := trR1 (isZ_sub zn zn') nz.
    exfalso; apply: F1; apply/(pt_eqv_inf H).
    have Z : n' + - n' ≡ 0 by sring.
    apply/(pt_eqv_inf (@mult_wd D A _ _ Z)); exact: mult0_flag.
  Qed.

  (* nonzero multiples have nonzero formal parameter on both curves *)
  Lemma zpar_mult_neq0 sg n : isZ A n -> n ≢ 0 -> zparS sg (mult A n) ≢ 0.
  Proof.
    move=> zn nn; have [ F1 [ nx [ ny _ ] ] ] := trR1 zn nn.
    rewrite (zparS_n sg F1).
    apply: qe_mulf_neq0; first by rewrite oppr_eq0; apply: qe_e_neq0.
    by apply: qe_inv_neq0; apply: qe_e_neq0.
  Qed.

  (* the valuations of A, in the form consumed by the generic lemmas *)
  Lemma vq_wdq q : Proper (eqv ==> eqv) (vq A q).
  Proof. move=> x y E; rewrite E; reflexivity. Qed.

  Lemma vq_mul q (pq : primeA A q) :
    forall x y : sQA, x ≢ 0 -> y ≢ 0 -> vq A q (x * y) ≡ vq A q x + vq A q y.
  Proof. by move=> x y; apply: trV2_mul. Qed.

  Lemma vq_ultra q (pq : primeA A q) :
    forall x y : sQA, x ≢ 0 -> y ≢ 0 -> x + y ≢ 0 ->
      sof_min (vq A q x) (vq A q y) <= vq A q (x + y).
  Proof. by move=> x y; apply: trV2_ultra. Qed.

  Lemma vq_dom : forall x y : sQA, x ≢ 0 -> y ≢ 0 -> x * y ≢ 0.
  Proof. by move=> x y; apply: mulf_neq0. Qed.

  Lemma vP_mul w q (wq : above A w q) :
    forall x y : qe_SRing sQA, x ≢ 0 -> y ≢ 0 -> vP A w (x * y) ≡ vP A w x + vP A w y.
  Proof. by move=> x y; apply: trPL2_mul wq. Qed.

  Lemma vP_ultra w q (wq : above A w q) :
    forall x y : qe_SRing sQA, x ≢ 0 -> y ≢ 0 -> x + y ≢ 0 ->
      sof_min (vP A w x) (vP A w y) <= vP A w (x + y).
  Proof. by move=> x y; apply: trPL2_ultra wq. Qed.

  (* integers have nonnegative valuation, including 0 (vgeS convention) *)
  Lemma vge_isZ q x : primeA A q -> isZ A x -> vgeS (vq A q) x 0.
  Proof.
    move=> pq zx; case: (sof_eq_dec _ x 0) => [ E | nx ]; first by left.
    by right; apply: trV4.
  Qed.

  (* restriction of vP to sQ, in vgeS form (PL3) *)
  Lemma vge_restr w q x k : above A w q -> vgeS (vP A w) (qe_of x) k -> vgeS (vq A q) x k.
  Proof.
    move=> wq [ /qe_of_eq0 E | H ]; first by left.
    case: (sof_eq_dec _ x 0) => [ E | nx ]; first by left.
    by right; rewrite -(trPL3 wq nx).
  Qed.

  (* v_q(4) = 0 for an odd prime q (V5) *)
  Lemma vq4 q : primeA A q -> q ≢ 2%:R -> vq A q 4%:R ≡ 0.
  Proof.
    move=> pq q2; apply: (@trV5 D A (Posz 4) q isT pq).
    have -> : primes (absz (Posz 4)) = [:: 2%N] by [].
    by move=> p; rewrite inE => /eqP ->.
  Qed.

End ambient_alg.

Section subrKBS.

  Variable R : SRing.

  Add Ring sk_ring : (sr_rth R) (setoid (sr_setoid R) (sr_ext R),
    morphism (of_Z_morph R), constants [sof_cst], power_tac (sr_pow_th R) [sof_pow_cst]).

  Lemma subrKBS (l x y : R) : (l - x) - (l - y) ≡ y - x.
  Proof. sring. Qed.

End subrKBS.

(** * L0: the index map eta (red:eta, red:additivity; DESIGN 5.3, 5.4 L0) *)

Section term_model.

  Variables (D : FixedData) (A : AmbientS D) (val : gterm -> sQ A).

  Local Abbreviation sQA := (sQ A).

  Add Field tm_field : (@sof_fth sQA) (setoid (sr_setoid sQA) (sr_ext sQA),
    morphism (of_Z_morph sQA), constants [sof_cst],
    power_tac (sr_pow_th sQA) [sof_pow_cst], completeness (sof_Z_complete sQA)).
  Add Field tm_qe_field : (qe_fth sQA (@trZ0 D A))
    (setoid (sr_setoid (qe_SRing sQA)) (sr_ext (qe_SRing sQA)),
    morphism (of_Z_morph (qe_SRing sQA)), constants [sof_cst],
    power_tac (sr_pow_th (qe_SRing sQA)) [sof_pow_cst], completeness (qe_Z_complete sQA)).

  (* constraints (a) and (b) of the term model: [tm_ring], [tm_fun] of
     [TermModelS A Ax val] *)
  Hypothesis Hring : forall t, ring_okS val t.
  Hypothesis Hfun : forall t t', fun_okS val t t'.

  (** the coordinate functions and the points T_t *)

  Definition tcoord (c : Signature.coord) (t : gterm) : gterm := tapp1 (s_coord c) t.
  Definition tchain (k : nat) (c : Signature.coord) (t : gterm) : gterm := tapp1 (s_chain k c) t.

  (* (n0 + n1 sqrt2) / d *)
  Definition qfrac (n0 n1 d : sQA) : qe_SRing sQA := QE n0 n1 / qe_of d.

  (* red:coordinate-functions (= XvS, YvS of TheoryS.v) *)
  Definition Xc (t : gterm) : qe_SRing sQA := XvS val t.
  Definition Yc (t : gterm) : qe_SRing sQA := YvS val t.

  Lemma Xc_def t : Xc t = qfrac (val (tcoord cx0 t)) (val (tcoord cx1 t)) (val (tcoord cx2 t)).
  Proof. reflexivity. Qed.
  Lemma Yc_def t : Yc t = qfrac (val (tcoord cy0 t)) (val (tcoord cy1 t)) (val (tcoord cy2 t)).
  Proof. reflexivity. Qed.

  (* the point T_t (= TvS of TheoryS.v); its flag is val t: T_t = O iff val t ≡ 0 *)
  Definition T (t : gterm) : ptS sQA := TvS val t.

  Lemma T_def t : T t = (val t, (Xc t, Yc t)).
  Proof. reflexivity. Qed.

  (* the chain point Q_k of ax_chain, for 1 <= k <= m-1, read off the chain
     symbols; Q_k := (X t, Y t) for k >= m, so Q_m is T_t *)
  Definition chain_pt (k : nat) (t : gterm) : qe sQA * qe sQA :=
    ( qfrac (val (tchain k cx0 t)) (val (tchain k cx1 t)) (val (tchain k cx2 t)),
      qfrac (val (tchain k cy0 t)) (val (tchain k cy1 t)) (val (tchain k cy2 t)) ).

  (* (= QvCS of TheoryS.v) *)
  Definition Qch (t : gterm) (k : nat) : qe sQA * qe sQA := QvCS val D t k.

  Lemma Qch_def t k : Qch t k = if (k < fd_m D)%N then chain_pt k t else (Xc t, Yc t).
  Proof. reflexivity. Qed.

  (* red:eta: T_t = eta(t) P, with eta(t) read off by idx (R5); the
     [if val t == 0 then 0 else idx ...] of LocalComparison.v *)
  Definition eta (t : gterm) : sQA := sof_nz (val t) * idx A (Xc t, Yc t).

  (** semantic consequences of the axioms of T (DESIGN 3.3), for this val,
      stated as the components of [InstSemS] (TheoryS.v) *)

  (* ax_chain (T_a in m E(F_R)) *)
  Hypothesis H_chain : forall t, ChainSemS val D t.

  (* ax_add (T_{a+a'} = T_a + T_{a'}) *)
  Hypothesis H_add : forall t t', AddSemS val t t'.

  (* ax_P (T_1 = P) *)
  Hypothesis H_P : pt_eqv (T (tapp0 s_one)) (pt_ratS (Pgen D)).

  (** values of ring terms *)

  Lemma val_add s s' : val (tapp2 s_add s s') ≡ val s + val s'.
  Proof using Hring. exact: (Hring (tapp2 s_add s s')). Qed.

  Lemma val_mul s s' : val (tapp2 s_mul s s') ≡ val s * val s'.
  Proof using Hring. exact: (Hring (tapp2 s_mul s s')). Qed.

  Lemma val_neg s : val (tapp1 s_neg s) ≡ - val s.
  Proof using Hring. exact: (Hring (tapp1 s_neg s)). Qed.

  Lemma val_one : val (tapp0 s_one) ≡ 1.
  Proof using Hring. exact: (Hring (tapp0 s_one)). Qed.

  Lemma val_int z : val (tapp0 (s_int z)) ≡ of_Z z.
  Proof using Hring. exact: (Hring (tapp0 (s_int z))). Qed.

  (** the group law in the form of LocalComparison.v (from [add_ADDrelS]) *)

  Lemma H_addrel t t' : ADDrelS (T t) (T t') (T (tapp2 s_add t t')).
  Proof using Hring Hfun H_add.
    exact: (add_ADDrelS (ring_hom_groundS Hring) (@trZ0 D A) (fun_coordS Hfun) (H_add t t')).
  Qed.

  (** T and eta depend only on the value *)

  Lemma Xc_val t t' : val t ≡ val t' -> Xc t ≡ Xc t' /\ Yc t ≡ Yc t'.
  Proof using Hfun.
    move=> E; have hc c : val (tco c t) ≡ val (tco c t') by exact: (fun_coordS Hfun c E).
    by rewrite /Xc /Yc /XvS /YvS !hc; split; reflexivity.
  Qed.

  Lemma T_val t t' : val t ≡ val t' -> pt_eqv (T t) (T t').
  Proof using Hfun. exact: (TvS_fun (fun_coordS Hfun)). Qed.

  Lemma eta_val t t' : val t ≡ val t' -> eta t ≡ eta t'.
  Proof using Hfun.
    move=> E; have [ E1 E2 ] := Xc_val E; rewrite /eta E E1 E2; reflexivity.
  Qed.

  Lemma eta_0 t : val t ≡ 0 -> eta t ≡ 0.
  Proof. move=> E; rewrite /eta (nz_0 _ _ E) mul0r; reflexivity. Qed.

  Lemma eta_n t : val t ≢ 0 -> eta t ≡ idx A (Xc t, Yc t).
  Proof. move=> E; rewrite /eta (nz_n _ _ E) mul1r; reflexivity. Qed.

  (** L0 *)

  Lemma eta_chain t : val t ≢ 0 -> isZ A (eta t) /\ pt_eqv (mult A (eta t)) (1, (Xc t, Yc t)).
  Proof using H_chain.
    move=> nt; case: (H_chain t) => [ H | [ _ [ Hc Hs ] ] ]; first by exfalso; apply: nt.
    have [ Hz Hm ] := trR5 (Q := QvCS val D t) Hc Hs.
    have EQ : QvCS val D t (fd_m D) = (Xc t, Yc t) by rewrite /QvCS ltnn.
    rewrite EQ in Hz Hm; rewrite (eta_n nt); split; [ exact Hz | exact Hm ].
  Qed.

  Lemma eta_isZ t : isZ A (eta t).
  Proof using H_chain.
    case: (sof_eq_dec _ (val t) 0) => [ E | nt ]; first by rewrite (eta_0 E); apply: isZ0.
    by have [] := eta_chain nt.
  Qed.

  (* red:eta *)
  Lemma eta_spec t : pt_eqv (mult A (eta t)) (T t).
  Proof using H_chain.
    case: (sof_eq_dec _ (val t) 0) => [ E | nt ].
    - rewrite (eta_0 E); etransitivity; first exact: mult0.
      rewrite T_def; apply: pt_eqv_O => //; reflexivity.
    - have [ _ H ] := eta_chain nt; etransitivity; first exact: H.
      rewrite T_def; apply: pt_eqv_S => //; [ exact: sof_neq_1_0 | split; reflexivity ].
  Qed.

  (* conjugating red:eta: T_t^sigma = eta(t) P^sigma *)
  Lemma eta_conj t : pt_eqv (pt_conjS (T t)) (pt_conjS (mult A (eta t))).
  Proof using H_chain. rewrite eta_spec; reflexivity. Qed.

  Lemma eta_zpar sg t : zparS sg (T t) ≡ zparS sg (mult A (eta t)).
  Proof using H_chain. rewrite eta_spec; reflexivity. Qed.

  Lemma eta_zero_iff t : eta t ≡ 0 <-> val t ≡ 0.
  Proof using H_chain.
    split; last exact: eta_0.
    move=> E; case: (sof_eq_dec _ (val t) 0) => // nt; exfalso.
    have := eta_spec t; rewrite E => /pt_eqv_inf I.
    apply: nt; apply/I; exact: mult0_flag.
  Qed.

  Lemma eta_neq0 t : val t ≢ 0 -> eta t ≢ 0.
  Proof using H_chain. by move=> nt /eta_zero_iff. Qed.

  (* red:additivity *)
  Lemma eta_add t t' : eta (tapp2 s_add t t') ≡ eta t + eta t'.
  Proof using Hring Hfun H_chain H_add.
    apply: mult_inj; [ exact: eta_isZ | apply: trZ1_add; exact: eta_isZ | ].
    have := H_addrel t t'; rewrite -!eta_spec => H.
    exact: ADDrelS_fun H (trR3 (eta_isZ t) (eta_isZ t')).
  Qed.

  Lemma eta_one : eta (tapp0 s_one) ≡ 1.
  Proof using H_chain H_P.
    apply: mult_inj; [ exact: eta_isZ | exact: isZ1 | ].
    rewrite eta_spec H_P; symmetry; exact: (trR2 A 1%R).
  Qed.

  Lemma eta_neg t : eta (tapp1 s_neg t) ≡ - eta t.
  Proof using Hring Hfun H_chain H_add.
    have E0 : eta (tapp2 s_add t (tapp1 s_neg t)) ≡ 0.
    { apply/eta_zero_iff; rewrite val_add val_neg; sring. }
    have := eta_add t (tapp1 s_neg t); rewrite E0 => H.
    transitivity ((eta t + eta (tapp1 s_neg t)) - eta t); first by sring.
    rewrite -H; sring.
  Qed.

  (* injectivity of eta (via additivity and the finite-point axiom) *)
  Lemma eta_inj t t' : eta t ≡ eta t' -> val t ≡ val t'.
  Proof using Hring Hfun H_chain H_add.
    move=> E; apply/subr_eq0.
    transitivity (val (tapp2 s_add t (tapp1 s_neg t'))).
    { rewrite val_add val_neg; sring. }
    apply/eta_zero_iff; rewrite eta_add eta_neg E; sring.
  Qed.

  (* 4 a, as a term *)
  Definition tfour (t : gterm) : gterm :=
    tapp2 s_add (tapp2 s_add t t) (tapp2 s_add t t).

  Lemma val_tfour t : val (tfour t) ≡ 4%:R * val t.
  Proof using Hring. rewrite /tfour !val_add; sring. Qed.

  Lemma eta_tfour t : eta (tfour t) ≡ 4%:R * eta t.
  Proof using Hring Hfun H_chain H_add. rewrite /tfour !eta_add; sring. Qed.

  (** * L1: Lemma red:local-comparison (DESIGN 5.4 L1)

      [ha a] stands for the term  h a  and [h4a a] for  (h - 4) a; only their
      values matter (see [local_comparison_good] for the literal terms). *)

  Theorem local_comparison (K : nat) (q : sQA) (w : Pl A) (h j0 : gterm)
      (ha h4a : gterm -> gterm) :
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
  Proof using Hring Hfun H_chain H_add H_P.
    move=> K1 qSE qK wq nh nj0 vha vh4a Hi Hii.
    have [ pq q2 ] := trPL0 wq.
    have K0 : (0 : sQA) <= K%:R by exact: ler0n.
    have Kp : (0 : sQA) < K%:R by apply/ltr0n.
    (* the generic valuation lemmas, for v_q on sQ and w on qe sQ *)
    have vqwd := @vq_wdq D A q.
    have qdec : forall x y : sQA, x ≡ y \/ x ≢ y by exact: sof_eq_dec.
    have q10 : (1 : sQA) ≢ 0 by exact: sof_neq_1_0.
    have Pwd : Proper (eqv ==> eqv) (vP A w) by exact: vP_wd.
    have Pdec : forall x y : qe_SRing sQA, x ≡ y \/ x ≢ y by exact: qe_eq_dec.
    have P10 : (1 : qe_SRing sQA) ≢ 0 by apply: qe_neq_1_0; exact: trZ0.
    have qsub := vge_sub vqwd qdec q10 (vq_mul pq) (vq_ultra pq).
    have qadd := vge_add vqwd qdec (vq_ultra pq).
    have qmul := vge_mul vqwd qdec (vq_mul pq).
    have qdivu := vge_div_unit vqwd qdec q10 (@vq_dom D A) (vq_mul pq).
    have qaddlt := val_add_lt vqwd q10 (vq_mul pq) (vq_ultra pq).
    have Pdiv := val_div Pwd P10 (@qe_mulf_neq0 D A) (vP_mul wq).
    have Psub := vge_sub Pwd Pdec P10 (vP_mul wq) (vP_ultra wq).
    (* red:alternate-index, from F1 on the conjugate curve *)
    have alt b : vgeS (vq A q) (eta (h4a b)) K%:R.
    { have [ r0 [ rb Hv ] ] := Hii b.
      have nj := eta_neq0 nj0.
      rewrite !eta_zpar in Hv; rewrite -!eta_spec in r0 rb.
      case: (trF1 pq qSE wq (eta_isZ (h4a b)) (eta_isZ j0) nj rb r0) => [ E0 | E ];
        first by left.
      case: (sof_eq_dec _ (eta (h4a b)) 0) => [ E0 | nb ]; first by left.
      right.
      have z0 := zpar_mult_neq0 (sg := true) (eta_isZ j0) nj.
      have zb := zpar_mult_neq0 (sg := true) (eta_isZ (h4a b)) nb.
      case: Hv => [ Hv | Hv ].
      { exfalso; move: Hv; exact: (qe_mulf_neq0 zb (qe_inv_neq0 z0)). }
      rewrite (Pdiv _ _ zb z0 (qe_neq0_unit z0)) in Hv.
      have := trV4 pq (eta_isZ j0) nj; sof_lra. }
    (* the indices V_a = eta (h a): V_a = 4 eta a, V_1 = 4 mod q^K *)
    have eV b : eta (h4a b) ≡ eta (ha b) - 4%:R * eta b.
    { transitivity (eta (tapp2 s_add (ha b) (tapp1 s_neg (tfour b)))).
      - apply: eta_val; rewrite val_add val_neg val_tfour vh4a vha; sring.
      - rewrite eta_add eta_neg eta_tfour; sring. }
    have eV1 : eta (ha (tapp0 s_one)) ≡ eta h.
    { apply: eta_val; rewrite vha val_one; sring. }
    have e1 : vgeS (vq A q) (eta h - 4%:R) K%:R.
    { have := alt (tapp0 s_one); rewrite eV eV1 eta_one mulr1; done. }
    (* V_1 is a q-unit, since q <> 2 *)
    have zh := eta_isZ h; have nV1 := eta_neq0 nh.
    have uV1 : vq A q (eta h) ≡ 0.
    { case: (sof_eq_dec _ (eta h - 4%:R) 0) => [ E | nE ].
      - have -> : eta h ≡ 4%:R by apply/subr_eq0.
        exact: vq4.
      - have n4 : (4%:R : sQA) ≢ 0 by rewrite pnatr_eq0.
        case: e1 => [ E | e1 ]; first by exfalso.
        have lt : vq A q 4%:R < vq A q (eta h - 4%:R).
        { have := vq4 pq q2; sof_lra. }
        have [ _ ] := qaddlt _ _ n4 nE lt.
        have -> : 4%:R + (eta h - 4%:R) ≡ eta h by sring.
        move=> H; rewrite H; exact: vq4. }
    have uuV1 : (eta h)^-1 * eta h ≡ 1 by apply: mulVr.
    move=> a.
    have ze := eta_isZ a; have zV := eta_isZ (ha a).
    have cA : vgeS (vq A q) (eta (ha a) - 4%:R * eta a) K%:R by rewrite -eV; apply: alt.
    (* red:actual-slope *)
    have slope : vgeS (vq A q) (eta (ha a) / eta h - eta a) K%:R.
    { have -> : eta (ha a) / eta h - eta a
              ≡ ((eta (ha a) - 4%:R * eta a) - eta a * (eta h - 4%:R)) / eta h.
      { sfield; exact nV1. }
      apply: (qdivu _ _ _ nV1 uuV1 uV1).
      apply: (qsub _ _ _ cA).
      apply: (vge_le (k := 0 + K%:R)); first by sof_lra.
      exact: qmul (vge_isZ pq ze) e1. }
    (* F2 on the primary curve, for the indices V_1 and V_a *)
    have [ rh [ ra [ _ Hl ] ] ] := Hi a.
    rewrite -!eta_spec in rh ra; rewrite !eta_zpar in Hl.
    have cond : eta (ha a) ≡ 0 \/ vq A q (eta h) <= vq A q (eta (ha a)).
    { case: (sof_eq_dec _ (eta (ha a)) 0) => [ E | nV ]; [ by left | right ].
      rewrite uV1; exact: trV4 pq zV nV. }
    have [ _ HF ] := trF2 K1 pq qSE qK wq zV zh nV1 ra rh cond.
    have HL : vgeS (vq A q) (eta (ha a) / eta h - val a) K%:R.
    { apply: (vge_restr wq).
      have := Psub _ _ _ Hl HF; rewrite subrKBS -qe_of_sub; done. }
    have fin : vgeS (vq A q) (val a - eta a) K%:R.
    { have := qsub _ _ _ slope HL; rewrite subrKBS; done. }
    split => //.
    have -> : val a ≡ eta a + (val a - eta a) by sring.
    apply: qadd; first exact: vge_isZ pq ze.
    exact: vge_le K0 fin.
  Qed.

  (* h - 4, as a term *)
  Definition tminus4 (h : gterm) : gterm :=
    tapp2 s_add h (tapp1 s_neg (tapp0 (s_int 4%ZZ))).

  Lemma val_tminus4 h : val (tminus4 h) ≡ val h - 4%:R.
  Proof using Hring. rewrite /tminus4 val_add val_neg val_int; sring. Qed.

  (* Lemma red:local-comparison with q good (q notin S_K) and the literal
     terms  h a  and  (h - 4) a *)
  Corollary local_comparison_good (K : nat) (q : sQA) (w : Pl A) (h j0 : gterm) :
    (1 <= K)%N -> goodAS D K q -> above A w q ->
    val h ≢ 0 -> val j0 ≢ 0 ->
    (forall a,
         redAS (vP A w) false (T h) /\ redAS (vP A w) false (T (tapp2 s_mul h a))
      /\ ellKS false K (zparS false (T h)) ≢ 0
      /\ vgeS (vP A w) (ellKS false K (zparS false (T (tapp2 s_mul h a)))
                          / ellKS false K (zparS false (T h)) - qe_of (val a)) K%:R) ->
    (forall a,
         redAS (vP A w) true (T j0) /\ redAS (vP A w) true (T (tapp2 s_mul (tminus4 h) a))
      /\ vgeS (vP A w) (zparS true (T (tapp2 s_mul (tminus4 h) a)) / zparS true (T j0)) K%:R) ->
    forall a, vgeS (vq A q) (val a) 0 /\ vgeS (vq A q) (val a - eta a) K%:R.
  Proof using Hring Hfun H_chain H_add H_P.
    move=> K1 [ qK qS ] wq nh nj0 Hi Hii.
    apply: (local_comparison (ha := tapp2 s_mul h) (h4a := tapp2 s_mul (tminus4 h))
              K1 _ qK wq nh nj0 _ _ Hi Hii).
    - by move=> p Hp; apply: qS; rewrite /Sfix !mem_cat Hp orTb !orbT.
    - by move=> a; exact: val_mul.
    - by move=> a; rewrite val_mul val_tminus4; reflexivity.
  Qed.

End term_model.

(** glue: a term model of [Inst D f] satisfies the Section hypotheses *)
Lemma TermModelS_LC_hyps (D : FixedData) (f : H10Z.H10Z_PROBLEM) (A : AmbientS D)
    (val : gterm -> sQ A) :
  TermModelS A (Inst D f) val ->
       (forall t, ring_okS val t) /\ (forall t t', fun_okS val t t')
    /\ (forall t, ChainSemS val D t) /\ (forall t t', AddSemS val t t')
    /\ pt_eqv (T val (tapp0 s_one)) (pt_ratS (Pgen D)).
Proof.
  move=> HM; have [ _ [ HP [ Hadd [ Hch _ ] ] ] ] := TermModel_InstSemS HM.
  by case: HM => Hring Hfun _ _.
Qed.
