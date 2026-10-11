(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A (task P3a): Coarsening.v over the setoid ambient structure
   [AmbientS D] of AmbientS.v (carrier [sQ A : SOF], Prop equality [≡]).

   Same content and proof structure as Coarsening.v (Section 2.5 of the
   paper, "Odd valuations select a tested branch"; DESIGN 5.4, L2, L3):
   - [odd_contact_step]: eq. red:odd-r;
   - [coarsening]: Lemma red:coarsening in the choice-free form with the
     predicate [poswS] ("positive for the coarsened valuation").

   Translation (SETOID.md, "Porting recipe"):
   - [=] on [sQ A] / [qe (sQ A)] becomes [≡], [!= 0] becomes [≢ 0];
     [ring]/[field]/[lra] become [sring]/[sfield]/[sof_lra]; [eqVneq]
     becomes [sof_eq_dec]/[qe_eq_dec] (Prop case splits only);
   - the generic valuation lemmas [cv_*] are over [F : SRing], [R : SOF]
     with the extra hypotheses [v_wd] (Proper), [F_dec], [F_1_neq_0];
     [cv_inv] takes the inverse law [x^-1 * x ≡ 1] as premise;
   - points use the flag encoding of AmbientS.v:
       Tpt val t := (val t, (Xc t, Yc t))   (flag = val t, nonzero = finite),
     the same point as [TvS val t] of TheoryS.v (convertible);
   - [FormalAS sg r B s p := p.1 ≡ 0 \/ LocAS 1 r B s (qe_e sg p.2.1)^-1]
     (the [match] of [FormalA], as [FormalRS] of TheoryS.v);
   - the side condition "x <> 0 for the finite point (x, y)" of
     [formal_reduces]/[coarsening] becomes [p.1 ≢ 0 -> p.2.1 ≢ 0];
   - [ellK] is [ellKS], [zpar] is [zparS], [redA] is [redAS], [vge] is
     [vgeS], [oddZ]/[evenZ] are [oddZS]/[evenZS], [goodA] is [goodAS],
     [fd_L] is [fd_LS], [Phi_holdsR] is [Phi_holdsS], [TermModel] is
     [TermModelS];
   - semantic definitions carry the suffix S ([LocAS], [FormalAS],
     [RepCondsAS], [uvalS], [mvalS], [slopeS], [RepSemS], [inRS],
     [poswS]); [Tpt], [Xc], [Yc], the term constructors, [RepTerms] and
     the lemma names are those of Coarsening.v.
   [RepSemS] (a record over witness terms) is a different object from the
   [RepSemS] of TheoryS.v (the semantics of ax_rep); this file does not
   import TheoryS.v; use qualified names downstream.

   Logical assumptions: excluded middle (classic) only, for the primality
   of the center of the coarsened valuation ([posw_prime]). No choice. *)

From Stdlib Require Import Setoid Morphisms RelationClasses Arith ZArith Lia List
  Classical_Prop Classical_Pred_Type.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos.

From Undecidability.H10.Dio
  Require dio_logic.

From Undecidability.H10
  Require Import H10Z.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData.

From Undecidability.H10.Rational
  Require Import SOF SOFTactics SOFqe SOFTheory SignatureS AmbientS.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.
Import SOFTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope sof_scope.

(* [sof_lra] splits every [≢] hypothesis by trichotomy (2^n cases), and
   its proof term mentions every hypothesis it reified (so [Proof using]
   would have to list unused section hypotheses): clear the negated
   hypotheses first (and [hB] in the coarsening Section, tactic [slrb]) *)
Ltac slra := repeat match goal with H : ~ _ |- _ => clear H end; sof_lra.

(** * Generic valuation lemmas (prefix cv_)

    For a map v : F -> R on a setoid ring without zero divisors which is
    multiplicative and ultrametric on nonzero elements. Used for vq q on
    *Q and for vP w on *F. *)

Section cvaluation.

  Variables (F : SRing) (R : SOF) (v : F -> R).

  Add Ring cv_F_ring : (sr_rth F) (setoid (sr_setoid F) (sr_ext F),
    morphism (of_Z_morph F), constants [sof_cst], power_tac (sr_pow_th F) [sof_pow_cst]).
  Add Field cv_R_field : (@sof_fth R) (setoid (sr_setoid R) (sr_ext R),
    morphism (of_Z_morph R), constants [sof_cst],
    power_tac (sr_pow_th R) [sof_pow_cst], completeness (sof_Z_complete R)).

  Hypothesis v_wd : Proper (eqv ==> eqv) v.
  Hypothesis F_dec : forall x y : F, x ≡ y \/ x ≢ y.
  Hypothesis F_1_neq_0 : (1 : F) ≢ 0.
  Hypothesis vdom : forall x y : F, x ≢ 0 -> y ≢ 0 -> x * y ≢ 0.
  Hypothesis vmul : forall x y : F, x ≢ 0 -> y ≢ 0 -> v (x * y) ≡ v x + v y.
  Hypothesis vultra : forall x y : F, x ≢ 0 -> y ≢ 0 -> x + y ≢ 0 ->
                        sof_min (v x) (v y) <= v (x + y).

  Lemma cv_1 : v 1 ≡ 0.
  Proof using F_1_neq_0 vmul v_wd.
    have h := vmul F_1_neq_0 F_1_neq_0; rewrite mulr1 in h; sof_lra.
  Qed.

  Lemma cv_N1 : v (- 1) ≡ 0.
  Proof using F_1_neq_0 vmul v_wd.
    have hN : (- (1) : F) ≢ 0 by rewrite oppr_eq0; exact F_1_neq_0.
    have h := vmul hN hN; rewrite mulrNN mulr1 cv_1 in h; sof_lra.
  Qed.

  Lemma cv_N x : x ≢ 0 -> v (- x) ≡ v x.
  Proof using F_1_neq_0 vmul v_wd.
    move=> hx; have hN : (- (1) : F) ≢ 0 by rewrite oppr_eq0; exact F_1_neq_0.
    rewrite -mulN1r (vmul hN hx) cv_N1 add0r; reflexivity.
  Qed.

  Lemma cv_ge0 k : vgeS v 0 k.
  Proof. by left; reflexivity. Qed.

  Lemma cv_ge_le x k k' : k' <= k -> vgeS v x k -> vgeS v x k'.
  Proof. by move=> hk [ h | h ]; [ left | right; apply: le_trans h ]. Qed.

  Lemma cv_ge_opp x k : vgeS v x k -> vgeS v (- x) k.
  Proof using F_1_neq_0 vmul v_wd F_dec.
    case=> [ h | h ]; first by left; rewrite h oppr0; reflexivity.
    case: (F_dec x 0) => [ h0 | hx ]; first by left; rewrite h0 oppr0; reflexivity.
    by right; rewrite cv_N.
  Qed.

  Lemma cv_ge_add x y k : vgeS v x k -> vgeS v y k -> vgeS v (x + y) k.
  Proof using vultra F_dec v_wd.
    case=> [ hx0 | hx ]; first by rewrite hx0 add0r.
    case=> [ hy0 | hy ]; first by rewrite hy0 addr0; right.
    case: (F_dec x 0) => [ h | nx ]; first by rewrite h add0r; right.
    case: (F_dec y 0) => [ h | ny ]; first by rewrite h addr0; right.
    case: (F_dec (x + y) 0) => [ h | nxy ]; first by left.
    right; apply: le_trans (vultra nx ny nxy); by apply/le_min.
  Qed.

  Lemma cv_ge_sub x y k : vgeS v x k -> vgeS v y k -> vgeS v (x - y) k.
  Proof using F_1_neq_0 vmul vultra F_dec v_wd.
    by move=> hx hy; apply: cv_ge_add => //; apply: cv_ge_opp.
  Qed.

  Lemma cv_ge_mul x y k l : vgeS v x k -> vgeS v y l -> vgeS v (x * y) (k + l).
  Proof using vmul F_dec v_wd.
    case=> [ h | hx ]; first by left; rewrite h mul0r; reflexivity.
    case=> [ h | hy ]; first by left; rewrite h mulr0; reflexivity.
    case: (F_dec x 0) => [ h | nx ]; first by left; rewrite h mul0r; reflexivity.
    case: (F_dec y 0) => [ h | ny ]; first by left; rewrite h mulr0; reflexivity.
    by right; rewrite (vmul nx ny); apply: lerD.
  Qed.

  Lemma cv_lt_add x y : x ≢ 0 -> y ≢ 0 -> v x < v y -> x + y ≢ 0 /\ v (x + y) ≡ v x.
  Proof using F_1_neq_0 vmul vultra v_wd.
    move=> nx ny hlt.
    have nxy : x + y ≢ 0.
    { move=> h; have hy : y ≡ - x.
      { transitivity (- x + (x + y)); first sring.
        rewrite h; sring. }
      by move: hlt; rewrite hy (cv_N nx); apply: ltxx. }
    split => //.
    have h1 := vultra nx ny nxy; rewrite (min_l _ _ _ (ltW _ _ _ hlt)) in h1.
    have nNy : - y ≢ 0 by rewrite oppr_eq0.
    have E : x + y + - y ≡ x by sring.
    have h2 := vultra nxy nNy; rewrite E (cv_N ny) in h2.
    have {}h2 := h2 nx; rewrite ge_min in h2.
    case: h2 => h2; first by sof_lra.
    by exfalso; sof_lra.
  Qed.

  Lemma cv_exp x n : x ≢ 0 -> x ^+ n ≢ 0 /\ v (x ^+ n) ≡ n%:R * v x.
  Proof using F_1_neq_0 vdom vmul v_wd.
    move=> nx; elim: n => [ | n [ IH1 IH2 ] ].
    - split; first exact: F_1_neq_0.
      change (v 1 ≡ 0 * v x); rewrite mul0r; exact: cv_1.
    - change (x * x ^+ n ≢ 0 /\ v (x * x ^+ n) ≡ n.+1%:R * v x).
      split; first exact: vdom.
      rewrite (vmul nx IH1) IH2 natrS; sring.
  Qed.

  Lemma cv_inv x : x ≢ 0 -> x^-1 * x ≡ 1 -> v (x^-1) ≡ - v x.
  Proof using F_1_neq_0 vmul v_wd.
    move=> nx ux.
    have nix : x^-1 ≢ 0.
    { move=> h; apply: F_1_neq_0; rewrite -ux h; sring. }
    have h := vmul nix nx; rewrite ux cv_1 in h; sof_lra.
  Qed.

End cvaluation.

(** * The quadratic extension of an ambient field: *F has no zero divisors *)

Section qe_facts.

  Variable R : SOF.
  Hypothesis Z0 : forall x : R, x * x ≢ 2%:R.

  Add Field qf_R_field : (@sof_fth R) (setoid (sr_setoid R) (sr_ext R),
    morphism (of_Z_morph R), constants [sof_cst],
    power_tac (sr_pow_th R) [sof_pow_cst], completeness (sof_Z_complete R)).
  Add Ring qf_qe_ring : (sr_rth (qe_SRing R)) (setoid (sr_setoid (qe_SRing R)) (sr_ext (qe_SRing R)),
    morphism (of_Z_morph (qe_SRing R)), constants [sof_cst],
    power_tac (sr_pow_th (qe_SRing R)) [sof_pow_cst]).

  Implicit Types (x y : qe R) (a : R).

  Lemma cq_norm_eq0 x : qe_norm x ≡ 0 -> x ≡ 0.
  Proof using Z0. exact: (proj1 (qe_norm_eq0 _ Z0 x)). Qed.

  Lemma cq_unit x : x ≢ 0 -> x^-1 * x ≡ 1.
  Proof using Z0. exact: (@qe_inv_l R Z0 x). Qed.

  Lemma cq_mul_neq0 x y : x ≢ 0 -> y ≢ 0 -> x * y ≢ 0.
  Proof using Z0. by move=> nx ny /(qe_mulf_eq0 _ Z0) [ h | h ]; [ apply: nx | apply: ny ]. Qed.

  Lemma cq_of_eq0 a : qe_of a ≡ 0 <-> a ≡ 0.
  Proof. exact: (qe_of_eqv _ a 0). Qed.

  Lemma cq_of_neq0 a : a ≢ 0 -> qe_of a ≢ 0.
  Proof. by move=> na /cq_of_eq0. Qed.

  Lemma cq_of1 : qe_of 1 ≡ (1 : qe R).
  Proof. reflexivity. Qed.

  Lemma cq_conj_neq0 x : x ≢ 0 -> qe_conj x ≢ 0.
  Proof.
    move=> nx h; apply: nx; rewrite -(qe_conjK _ x) h.
    split; rewrite /=; sring.
  Qed.

  Lemma cq_e_neq0 sg x : x ≢ 0 -> qe_e sg x ≢ 0.
  Proof. by case: sg => //=; apply: cq_conj_neq0. Qed.

  Lemma cq_neq_1_0 : (1 : qe R) ≢ 0.
  Proof. by move=> [ h _ ]; apply: (oner_neq0 R). Qed.

End qe_facts.

(** * Terms, points of terms, and the semantics of the representation axiom *)

Definition tadd (s t : gterm) : gterm := tapp2 s_add s t.
Definition tmul (s t : gterm) : gterm := tapp2 s_mul s t.
Definition tneg (t : gterm) : gterm := tapp1 s_neg t.
Definition tsub (s t : gterm) : gterm := tadd s (tneg t).
Definition tint (z : Z) : gterm := tapp0 (s_int z).
Definition tone : gterm := tapp0 s_one.
Definition tzero : gterm := tapp0 s_zero.
Definition tcoord (c : Signature.coord) (t : gterm) : gterm := tapp1 (s_coord c) t.

(* the unary data of one instance of Rep_K at an argument A: the Skolem
   terms u1, u2, v and, per member j of the contact list, the sign eps_j,
   the multiplier k_j, the terms r_j, B_j, wB_j, and per branch s the terms
   h, j0 (DESIGN 3.3, item 6; FixedData.RepWit1). Unchanged (syntax). *)
Record RepTerms : Type := {
  rp_u1 : gterm;
  rp_u2 : gterm;
  rp_v : gterm;
  rp_eps : mem13 -> int;
  rp_k : mem13 -> nat;
  rp_r : mem13 -> gterm;
  rp_B : mem13 -> gterm;
  rp_wB : mem13 -> gterm;
  rp_h : mem13 -> sgn -> gterm;
  rp_j0 : mem13 -> sgn -> gterm
}.

Section term_model.

  Variables (D : FixedData) (A : AmbientS D) (val : gterm -> sQ A).

  Local Abbreviation sQA := (sQ A).

  (* the point T_t of DESIGN 5.3 in the flag encoding: flag val t
     (O iff val t ≡ 0), coordinates X t = (x0 + x1 sqrt2)/x2 and
     Y t = (y0 + y1 sqrt2)/y2 *)
  Definition Xc (t : gterm) : qe_SRing sQA :=
    QE (val (tcoord cx0 t)) (val (tcoord cx1 t)) / qe_of (val (tcoord cx2 t)).
  Definition Yc (t : gterm) : qe_SRing sQA :=
    QE (val (tcoord cy0 t)) (val (tcoord cy1 t)) / qe_of (val (tcoord cy2 t)).
  Definition Tpt (t : gterm) : ptS sQA := (val t, (Xc t, Yc t)).

  (* membership of alpha in r^i (R_F)_p at the branch sqrt2 |-> s B
     (red:localization-definition), in the invertibility encoding LOC of
     the theory: alpha Y = r^i X with X, Y in R_F and Y(sB) invertible
     modulo r R; all witnesses are values of terms. *)
  Definition LocAS (i : nat) (r Bv : sQA) (s : sgn) (alpha : qe sQA) : Prop :=
    exists X0 X1 Y0 Y1 io ka : gterm,
         alpha * QE (val Y0) (val Y1) ≡ qe_of r ^+ i * QE (val X0) (val X1)
      /\ (val Y0 + (sgnz s)%:~R * Bv * val Y1) * val io - 1 ≡ r * val ka.

  (* formal for the tested localization: O, or 1/x in r (R_F)_p, on E
     (sg = false) or for the conjugate point on E^sigma (sg = true) *)
  Definition FormalAS (sg : bool) (r Bv : sQA) (s : sgn) (p : ptS sQA) : Prop :=
    p.1 ≡ 0 \/ LocAS 1 r Bv s (qe_e sg p.2.1)^-1.

  (* conditions (i) and (ii) of the representation axiom at the branch s,
     for one a (red:primary-test, red:alternate-test) *)
  Definition RepCondsAS (K : nat) (r Bv : sQA) (s : sgn) (h j0 a : gterm) : Prop :=
       FormalAS false r Bv s (Tpt h)
    /\ FormalAS false r Bv s (Tpt (tmul h a))
    /\ ellKS false K (zparS false (Tpt h)) ≢ 0
    /\ LocAS K r Bv s (ellKS false K (zparS false (Tpt (tmul h a)))
                        / ellKS false K (zparS false (Tpt h)) - qe_of (val a))
    /\ FormalAS true r Bv s (Tpt j0)
    /\ FormalAS true r Bv s (Tpt (tmul (tsub h (tint 4)) a))
    /\ LocAS K r Bv s (zparS true (Tpt (tmul (tsub h (tint 4)) a)) / zparS true (Tpt j0)).

  (* u_1, u_2, u_3 = A v - u_1 - u_2 *)
  Definition uvalS (W : RepTerms) (tA : gterm) (i : i3) : sQA :=
    match i with
    | I1 => val (rp_u1 W)
    | I2 => val (rp_u2 W)
    | I3 => val tA * val (rp_v W) - val (rp_u1 W) - val (rp_u2 W)
    end.

  (* the 13 members v, L_b(u_i, v) of red:contact-list *)
  Definition mvalS (W : RepTerms) (tA : gterm) (j : mem13) : sQA :=
    match j with
    | mem_v => val (rp_v W)
    | mem_L i b => fd_LS D b (uvalS W tA i) (val (rp_v W))
    end.

  (* the slope s_i = (u_i : v) *)
  Definition slopeS (W : RepTerms) (tA : gterm) (i : i3) : sQA := uvalS W tA i / val (rp_v W).

  (* The semantic content of the representation axiom at precision K for
     the ring element A (Coarsening.RepSem, setoid version): with the
     Skolem terms W, v ≢ 0, and for each member j:
       mem_j ≡ eps_j k_j r_j with eps_j = +-1, k_j in Kset, r_j ≢ 0,
       B_j^2 - 2 ≡ r_j wB_j, and for each branch s: h, j0 ≢ 0 and the
       conditions (i), (ii) for every term a. *)
  Record RepSemS (K : nat) (tA : gterm) (W : RepTerms) : Prop := {
    rs_v : val (rp_v W) ≢ 0;
    rs_mem : forall j, mvalS W tA j ≡ (rp_eps W j)%:~R * (rp_k W j)%:R * val (rp_r W j);
    rs_eps : forall j, rp_eps W j = 1%R \/ rp_eps W j = (-1)%R;
    rs_k : forall j, rp_k W j \in fd_Kset D;
    rs_r : forall j, val (rp_r W j) ≢ 0;
    rs_B : forall j, val (rp_B W j) ^+ 2 - 2%:R ≡ val (rp_r W j) * val (rp_wB W j);
    rs_h : forall j s, val (rp_h W j s) ≢ 0;
    rs_j0 : forall j s, val (rp_j0 W j s) ≢ 0;
    rs_conds : forall j s a,
        RepCondsAS K (val (rp_r W j)) (val (rp_B W j)) s (rp_h W j s) (rp_j0 W j s) a
  }.

End term_model.

Arguments Tpt {D A} val t.
Arguments Xc {D A} val t.
Arguments Yc {D A} val t.
Arguments LocAS {D A} val i r Bv s alpha.
Arguments FormalAS {D A} val sg r Bv s p.
Arguments RepCondsAS {D A} val K r Bv s h j0 a.
Arguments uvalS {D A} val W tA i.
Arguments mvalS {D} {A} val W tA j.
Arguments slopeS {D A} val W tA i.
Arguments RepSemS {D A} val K tA W.
(* [≢] is a negation, so with Implicit Arguments the member/branch of these
   fields would be implicit; make them explicit as in Coarsening.v *)
Arguments rs_r {D A val K tA W} _ j _.
Arguments rs_h {D A val K tA W} _ j s _.
Arguments rs_j0 {D A val K tA W} _ j s _.

(** * Membership in the exceptional set (unchanged, ordinary) *)

Section Sfix_mem.

  Variable D : FixedData.

  Lemma Sfix_S1 p : p \in S1 D -> p \in Sfix D.
  Proof. by rewrite /Sfix !mem_cat => ->; rewrite orbT. Qed.

  Lemma Sfix_SE p : p \in fd_SE D -> p \in Sfix D.
  Proof. by rewrite /Sfix !mem_cat => ->; rewrite !orbT. Qed.

  Lemma Sfix_K k p : k \in fd_Kset D -> p \in primes k -> p \in Sfix D.
  Proof.
    move=> hk hp; rewrite /Sfix !mem_cat.
    have -> : p \in flatten [seq primes k | k <- fd_Kset D] by apply/flatten_mapP; exists k.
    by rewrite !orbT.
  Qed.

  Lemma Sfix_den i p : p \in primes (absz (denq (fd_C D i))) -> p \in Sfix D.
  Proof.
    move=> hp.
    have hd : p \in Sdet D.
    { rewrite /Sdet mem_cat; apply/orP; left.
      by case: i hp => hp; rewrite /= !mem_cat hp ?orbT. }
    by rewrite /Sfix; do 4 (rewrite mem_cat; apply/orP; right); rewrite mem_cat hd.
  Qed.

  Lemma Sfix_2 : 2%N \in Sfix D.
  Proof. by rewrite /Sfix !mem_cat mem_seq1 eqxx !orbT. Qed.

End Sfix_mem.

(** * The ambient term model *)

Section ambient.

  Variables (D : FixedData) (HWF : FixedWF D) (A : AmbientS D).
  Variables (Ax : gfml -> Prop) (val : gterm -> sQ A).
  Hypothesis HTM : TermModelS A Ax val.

  Local Abbreviation sQA := (sQ A).
  Local Abbreviation isZA := (isZ A).

  Add Field am_field : (@sof_fth sQA) (setoid (sr_setoid sQA) (sr_ext sQA),
    morphism (of_Z_morph sQA), constants [sof_cst],
    power_tac (sr_pow_th sQA) [sof_pow_cst], completeness (sof_Z_complete sQA)).
  Add Field am_qe_field : (qe_fth sQA (@trZ0 D A)) (setoid (sr_setoid (qe_SRing sQA)) (sr_ext (qe_SRing sQA)),
    morphism (of_Z_morph (qe_SRing sQA)), constants [sof_cst],
    power_tac (sr_pow_th (qe_SRing sQA)) [sof_pow_cst], completeness (qe_Z_complete sQA)).

  (** ring structure of term values *)

  Lemma val_mul s t : val (tmul s t) ≡ val s * val t.
  Proof using HTM. exact: (tm_ring HTM (tmul s t)). Qed.
  Lemma val_add s t : val (tadd s t) ≡ val s + val t.
  Proof using HTM. exact: (tm_ring HTM (tadd s t)). Qed.
  Lemma val_neg t : val (tneg t) ≡ - val t.
  Proof using HTM. exact: (tm_ring HTM (tneg t)). Qed.
  Lemma val_one : val tone ≡ 1.
  Proof using HTM. exact: (tm_ring HTM tone). Qed.
  Lemma val_zero : val tzero ≡ 0.
  Proof using HTM. exact: (tm_ring HTM tzero). Qed.
  Lemma val_int z : val (tint z) ≡ of_Z z.
  Proof using HTM. exact: (tm_ring HTM (tint z)). Qed.

  (* the ring R of the paper: values of ground terms (up to ≡) *)
  Definition inRS (x : sQA) : Prop := exists t, val t ≡ x.

  #[local] Instance inRS_wd : Proper (eqv ==> iff) inRS.
  Proof.
    move=> x x' E; rewrite /inRS; split=> [] [ t Et ]; exists t; [ rewrite -E | rewrite E ]; exact Et.
  Qed.

  Lemma inR_val t : inRS (val t).
  Proof. by exists t; reflexivity. Qed.
  Lemma inR_mul x y : inRS x -> inRS y -> inRS (x * y).
  Proof using HTM. by move=> [s Es] [t Et]; exists (tmul s t); rewrite val_mul Es Et; reflexivity. Qed.
  Lemma inR_opp x : inRS x -> inRS (- x).
  Proof using HTM. by move=> [s Es]; exists (tneg s); rewrite val_neg Es; reflexivity. Qed.
  Lemma inR_1 : inRS 1.
  Proof using HTM. by exists tone; rewrite val_one; reflexivity. Qed.

  (** valuations: instances of the generic lemmas *)

  Lemma sQ_dec (x y : sQA) : x ≡ y \/ x ≢ y.
  Proof. exact: sof_eq_dec. Qed.
  Lemma qe_dec (x y : qe sQA) : x ≡ y \/ x ≢ y.
  Proof. exact: qe_eq_dec. Qed.
  Lemma sQ_1_neq_0 : (1 : sQA) ≢ 0.
  Proof. exact: oner_neq0. Qed.
  Lemma qe_1_neq_0 : (1 : qe sQA) ≢ 0.
  Proof. exact: cq_neq_1_0. Qed.

  Section at_prime.

    Variable q : sQA.
    Hypothesis hq : primeA A q.

    Let vq_wd1 : Proper (eqv ==> eqv) (vq A q).
    Proof. move=> x y E; rewrite E; reflexivity. Qed.

    Lemma vq_mul (x y : sQA) : x ≢ 0 -> y ≢ 0 -> vq A q (x * y) ≡ vq A q x + vq A q y.
    Proof using hq. exact: trV2_mul. Qed.
    Lemma vq_ultra (x y : sQA) : x ≢ 0 -> y ≢ 0 -> x + y ≢ 0 ->
        sof_min (vq A q x) (vq A q y) <= vq A q (x + y).
    Proof using hq. exact: trV2_ultra. Qed.
    Lemma vq_N x : x ≢ 0 -> vq A q (- x) ≡ vq A q x.
    Proof using hq. exact: (cv_N vq_wd1 sQ_1_neq_0 vq_mul). Qed.
    Lemma vq_ge_add x y k : vgeS (vq A q) x k -> vgeS (vq A q) y k -> vgeS (vq A q) (x + y) k.
    Proof using hq. exact: (cv_ge_add vq_wd1 sQ_dec vq_ultra). Qed.
    Lemma vq_ge_opp x k : vgeS (vq A q) x k -> vgeS (vq A q) (- x) k.
    Proof using hq. exact: (cv_ge_opp vq_wd1 sQ_dec sQ_1_neq_0 vq_mul). Qed.
    Lemma vq_ge_sub x y k : vgeS (vq A q) x k -> vgeS (vq A q) y k -> vgeS (vq A q) (x - y) k.
    Proof using hq. exact: (cv_ge_sub vq_wd1 sQ_dec sQ_1_neq_0 vq_mul vq_ultra). Qed.
    Lemma vq_ge_mul x y k l : vgeS (vq A q) x k -> vgeS (vq A q) y l -> vgeS (vq A q) (x * y) (k + l).
    Proof using hq. exact: (cv_ge_mul vq_wd1 sQ_dec vq_mul). Qed.
    Lemma vq_lt_add x y : x ≢ 0 -> y ≢ 0 -> vq A q x < vq A q y ->
                          x + y ≢ 0 /\ vq A q (x + y) ≡ vq A q x.
    Proof using hq. exact: (cv_lt_add vq_wd1 sQ_1_neq_0 vq_mul vq_ultra). Qed.

    (* V5 for an ordinary integer all of whose primes lie in Sfix, at a
       prime outside Sfix *)
    Lemma vq_unit_int (k : int) : (k != 0)%R ->
      (forall p : nat, p \in primes (absz k) -> p \in Sfix D) ->
      (forall p : nat, p \in Sfix D -> q ≢ p%:R) ->
      vq A q k%:~R ≡ 0.
    Proof using hq.
      move=> nk hk hS; apply: trV5 => // p hp; exact/hS/hk.
    Qed.

  End at_prime.

  Section at_place.

    Variables (w : Pl A) (q : sQA).
    Hypothesis hw : above A w q.

    Lemma qe_dom (x y : qe sQA) : x ≢ 0 -> y ≢ 0 -> x * y ≢ 0.
    Proof. exact: (cq_mul_neq0 (@trZ0 D A)). Qed.
    Lemma vP_mul (x y : qe sQA) : x ≢ 0 -> y ≢ 0 -> vP A w (x * y) ≡ vP A w x + vP A w y.
    Proof using hw. exact: trPL2_mul hw. Qed.
    Lemma vP_ultra (x y : qe sQA) : x ≢ 0 -> y ≢ 0 -> x + y ≢ 0 ->
        sof_min (vP A w x) (vP A w y) <= vP A w (x + y).
    Proof using hw. exact: trPL2_ultra hw. Qed.
    Lemma vP_1 : vP A w 1 ≡ 0.
    Proof using hw. exact: (cv_1 (@vP_wd D A w) qe_1_neq_0 vP_mul). Qed.
    Lemma vP_ge_add x y k : vgeS (vP A w) x k -> vgeS (vP A w) y k -> vgeS (vP A w) (x + y) k.
    Proof using hw. exact: (cv_ge_add (@vP_wd D A w) qe_dec vP_ultra). Qed.
    Lemma vP_lt_add x y : x ≢ 0 -> y ≢ 0 -> vP A w x < vP A w y ->
                          x + y ≢ 0 /\ vP A w (x + y) ≡ vP A w x.
    Proof using hw. exact: (cv_lt_add (@vP_wd D A w) qe_1_neq_0 vP_mul vP_ultra). Qed.
    Lemma vP_exp x n : x ≢ 0 -> x ^+ n ≢ 0 /\ vP A w (x ^+ n) ≡ n%:R * vP A w x.
    Proof using hw. exact: (cv_exp (@vP_wd D A w) qe_1_neq_0 qe_dom vP_mul). Qed.
    Lemma vP_inv x : x ≢ 0 -> vP A w (x^-1) ≡ - vP A w x.
    Proof using hw.
      move=> nx; apply: (cv_inv (@vP_wd D A w) qe_1_neq_0 vP_mul nx).
      exact: (cq_unit (@trZ0 D A)).
    Qed.
    Lemma vP_int x : x ≢ 0 -> isZA (vP A w x).
    Proof using hw. exact: trPL2_int hw. Qed.

  End at_place.

  (** parity and discreteness in *Z *)

  Lemma isZ_le0 x : isZA x -> x < 1 -> x <= 0.
  Proof.
    move=> hx h1; case: (lerP _ x 0) => h0 //.
    by have := trV0 hx h0; slra.
  Qed.

  Lemma even_odd_false x : evenZS isZA x -> oddZS isZA x -> False.
  Proof.
    move=> [y [hy ey]] [z [hz ez]].
    have hd : isZA (y - z) by apply: isZ_sub.
    case: (ltrP _ 0 (y - z)) => h.
    - have := trV0 hd h; slra.
    - slra.
  Qed.

  Lemma odd_neq0 x : oddZS isZA x -> x ≢ 0.
  Proof.
    move=> ho h0; apply: (even_odd_false (x := x)) => //.
    exists 0; split; first exact: isZ0.
    rewrite h0; sring.
  Qed.

  Lemma isZ_min x y : isZA x -> isZA y -> isZA (sof_min x y).
  Proof. by move=> hx hy; case: (sof_min_cases _ x y) => [] [ _ E ]; rewrite E. Qed.

  (** * Odd contact: eq. red:odd-r (DESIGN 5.4, L2) *)

  Section odd_contact.

    Variables (K : nat) (tA : gterm) (W : RepTerms).
    Hypothesis HR : RepSemS val K tA W.

    Local Abbreviation u i := (uvalS val W tA i).
    Local Abbreviation v := (val (rp_v W)).

    Lemma eps_neq0 j : ((rp_eps W j)%:~R : sQA) ≢ 0.
    Proof using HR. by move/intr_eq0; case: (rs_eps HR j) => ->. Qed.

    Lemma k_neq0 j : ((rp_k W j)%:R : sQA) ≢ 0.
    Proof using HWF HR.
      move/pnatr_eq0 => E; move: (wf_K HWF (rs_k HR j)); by rewrite E.
    Qed.

    Lemma mval_neq0 j : mvalS val W tA j ≢ 0.
    Proof using HWF HR.
      rewrite (rs_mem HR j); apply: mulf_neq0; last exact: (rs_r HR).
      apply: mulf_neq0; [ exact: eps_neq0 | exact: k_neq0 ].
    Qed.

    Lemma forms_neq0 i : v ≢ 0 /\ (forall b, fd_LS D b (u i) v ≢ 0).
    Proof using HWF HR.
      split; first exact: (rs_v HR).
      move=> b; exact: (mval_neq0 (j := mem_L i b)).
    Qed.

    Variable q : sQA.
    Hypothesis hq : primeA A q.
    Hypothesis hgood : goodAS D K q.

    Lemma good_Sfix p : p \in Sfix D -> q ≢ p%:R.
    Proof using hgood. by case: hgood => _ h; apply: h. Qed.

    (* the multipliers eps_j k_j are q-units *)
    Lemma vq_mval j : vq A q (mvalS val W tA j) ≡ vq A q (val (rp_r W j)).
    Proof using HWF HR hq hgood.
      have nk := k_neq0 (j := j).
      have ne := eps_neq0 (j := j).
      rewrite (rs_mem HR j) (vq_mul hq (mulf_neq0 _ _ _ ne nk) (rs_r HR j)) (vq_mul hq ne nk).
      have -> : vq A q (rp_eps W j)%:~R ≡ 0.
      { apply: (vq_unit_int hq) => //; last exact: good_Sfix.
        - by case: (rs_eps HR j) => ->.
        - by case: (rs_eps HR j) => -> p. }
      have -> : vq A q (rp_k W j)%:R ≡ 0.
      { change (vq A q ((rp_k W j)%:Z)%:~R ≡ 0).
        apply: (vq_unit_int hq) => //; last exact: good_Sfix.
        - rewrite eqz_nat -lt0n; exact: (wf_K HWF (rs_k HR j)).
        - move=> p hp; exact: (Sfix_K (rs_k HR j) hp). }
      rewrite !add0r; reflexivity.
    Qed.

    (* some contact form attains the minimum mn = min(v_q(u), v_q(v)) *)
    Lemma form_attains_min i :
      vq A q v ≡ mnAS (vq A q) (u i) v \/
      vq A q (fd_LS D B1 (u i) v) ≡ mnAS (vq A q) (u i) v.
    Proof using HWF HR hq hgood.
      have [nv nL] := forms_neq0 i.
      case: (sof_eq_dec _ (u i) 0) => [ h0 | nu ].
      { by left; rewrite (@mnAS_0 _ (vq A q) (u i) v h0); reflexivity. }
      rewrite (@mnAS_n _ (vq A q) (u i) v nu).
      case: (lerP _ (vq A q v) (vq A q (u i))) => hle.
      { by left; rewrite (min_r _ _ _ hle); reflexivity. }
      right; rewrite (min_l _ _ _ (ltW _ _ _ hle)).
      set c := fd_C D B1.
      have nd : ((denq c)%:~R : sQA) ≢ 0 by move/intr_eq0 => E; move: (denq_neq0 c); rewrite E.
      have vd : vq A q (denq c)%:~R ≡ 0.
      { apply: (vq_unit_int hq); [ by rewrite denq_neq0 | | exact: good_Sfix ].
        move=> p hp; exact: (Sfix_den hp). }
      have hdu : vq A q ((denq c)%:~R * u i) ≡ vq A q (u i).
      { rewrite (vq_mul hq nd nu) vd add0r; reflexivity. }
      rewrite /fd_LS -/c.
      case: (numq c =P 0%R) => [ hn | nn ].
      - have h0 : ((numq c)%:~R : sQA) ≡ 0 by apply/intr_eq0.
        rewrite h0 mul0r subr0; exact: hdu.
      - have nn' : ((numq c)%:~R : sQA) ≢ 0 by move/intr_eq0.
        have h0 : 0 <= vq A q (numq c)%:~R by apply: trV4 => //; apply: trZ1_int.
        have hlt : vq A q ((denq c)%:~R * u i) < vq A q (- ((numq c)%:~R * v)).
        { rewrite (vq_N hq (mulf_neq0 _ _ _ nn' nv)) hdu (vq_mul hq nn' nv); slra. }
        have nN : - ((numq c)%:~R * v) ≢ 0 by rewrite oppr_eq0; exact: mulf_neq0.
        have [_ E] := vq_lt_add hq (mulf_neq0 _ _ _ nd nu) nN hlt.
        etransitivity; [ exact: E | exact: hdu ].
    Qed.

    (* eq. red:odd-r *)
    Lemma odd_member i :
      0 < vq A q (MK A K (slopeS val W tA i)) ->
      exists j, oddZS isZA (vq A q (val (rp_r W j))).
    Proof using HWF HR hq hgood.
      move=> hM.
      have [nv nL] := forms_neq0 i.
      have [_ [_ H1]] := trH1 K nv nL.
      have [_ hodd] := H1 q hq hM.
      (* mn is in *Z *)
      have hmn : isZA (mnAS (vq A q) (u i) v).
      { case: (sof_eq_dec _ (u i) 0) => [ h0 | nu ].
        - rewrite (@mnAS_0 _ (vq A q) (u i) v h0); exact: trV2_int.
        - rewrite (@mnAS_n _ (vq A q) (u i) v nu); by apply: isZ_min; apply: trV2_int. }
      have [y [hy [ hev | hod ]]] := trZ2 hmn.
      - (* mn even: the odd contact depth gives an odd valuation *)
        have hsh : forall x, oddZS isZA (x - mnAS (vq A q) (u i) v) -> oddZS isZA x.
        { move=> x [z [hz e]]; exists (y + z); split; first exact: trZ1_add.
          move: e hev; slra. }
        case: hodd => [ ho | [ b ho ] ].
        + exists mem_v; rewrite -(vq_mval mem_v); exact: (hsh _ ho).
        + exists (mem_L i b); rewrite -(vq_mval (mem_L i b)); exact: (hsh _ ho).
      - (* mn odd: a form attaining the minimum *)
        have hm : oddZS isZA (mnAS (vq A q) (u i) v) by exists y.
        case: (form_attains_min i) => e.
        + exists mem_v; rewrite -(vq_mval mem_v); change (oddZS isZA (vq A q v)).
          by rewrite e.
        + exists (mem_L i B1); rewrite -(vq_mval (mem_L i B1)).
          change (oddZS isZA (vq A q (fd_LS D B1 (u i) v))).
          by rewrite e.
    Qed.

  End odd_contact.

  (* eq. red:odd-r, packaged: q is good and some r_j has odd valuation *)
  Theorem odd_contact_step K tA W i q :
    RepSemS val K tA W -> primeA A q ->
    0 < vq A q (MK A K (slopeS val W tA i)) ->
    goodAS D K q /\ exists j, oddZS isZA (vq A q (val (rp_r W j))).
  Proof using HWF.
    move=> HR hq hM.
    have [nv nL] := forms_neq0 HR i.
    have [_ [_ H1]] := trH1 K nv nL.
    have [hgood _] := H1 q hq hM.
    split => //; exact: (odd_member HR hq hgood hM).
  Qed.

  (** * Lemma red:coarsening (DESIGN 5.4, L3) *)

  Section coarsening.

    Variables (K : nat) (q : sQA).
    Hypothesis hq : primeA A q.
    Hypothesis hgood : goodAS D K q.
    Variables (rt Bt wBt : gterm).
    Hypothesis hr : val rt ≢ 0.
    Hypothesis hodd : oddZS isZA (vq A q (val rt)).
    Hypothesis hB : val Bt ^+ 2 - 2%:R ≡ val rt * val wBt.

    Ltac slrb := clear hB; slra.

    Local Abbreviation r := (val rt).
    Local Abbreviation vqq := (vq A q).

    Lemma notS1 p : p \in S1 D -> q ≢ p%:R.
    Proof using hgood. by move=> hp; case: hgood => _ h; apply/h/Sfix_S1. Qed.

    (* Step 1, parity: v(b) < 0 and v(a) <= -v(b) give an even v(a);
       uses pole parity (PP2) on b*b and a*(b*b), both values of terms *)
    Lemma parity_step a b : inRS a -> inRS b -> a ≢ 0 -> b ≢ 0 ->
      vqq b < 0 -> vqq a <= - vqq b -> evenZS isZA (vqq a).
    Proof using HTM hq hgood.
      move=> [ta Ea] [tb Eb]; rewrite -Ea -Eb => na nb hb hab.
      have nbb : val tb * val tb ≢ 0 by apply: mulf_neq0.
      have nabb : val ta * (val tb * val tb) ≢ 0 by apply: mulf_neq0.
      have Hbb : Phi_holdsS (fd_PhiL D) (val tb * val tb).
      { rewrite -val_mul; exact: (tm_phi HTM). }
      have Habb : Phi_holdsS (fd_PhiL D) (val ta * (val tb * val tb)).
      { rewrite -!val_mul; exact: (tm_phi HTM). }
      have e1 : vqq (val tb * val tb) ≡ vqq (val tb) + vqq (val tb) by rewrite (vq_mul hq nb nb); reflexivity.
      have e2 : vqq (val ta * (val tb * val tb)) ≡ vqq (val ta) + (vqq (val tb) + vqq (val tb)).
      { rewrite (vq_mul hq na nbb) e1; reflexivity. }
      have [y1 [hy1 ey1]] : evenZS isZA (vqq (val tb * val tb)).
      { apply: (trPP2 nbb Hbb hq notS1); rewrite e1; slrb. }
      have [y2 [hy2 ey2]] : evenZS isZA (vqq (val ta * (val tb * val tb))).
      { apply: (trPP2 nabb Habb hq notS1); rewrite e2; slrb. }
      exists (y2 - y1); split; first exact: isZ_sub.
      move: ey1 ey2; rewrite e1 e2; slrb.
    Qed.

    Lemma vqr_int : isZA (vqq r).
    Proof using hq hr. exact: trV2_int. Qed.

    (* v_q(r) >= 1 *)
    Lemma vqr_ge1 : 1 <= vqq r.
    Proof using HTM hq hgood hr hodd.
      case: (lerP _ 1 (vqq r)) => // h.
      have h0 := isZ_le0 vqr_int h.
      have n0 : vqq r ≢ 0 by apply: odd_neq0.
      have hlt : vqq r < 0 by apply/lt_neqAle; split.
      have hev := parity_step (inR_val rt) (inR_val rt) hr hr hlt ltac:(slrb).
      by exfalso; exact: even_odd_false hev hodd.
    Qed.

    (* Step 2: r is positive for the coarsened valuation: v_q(r b) >= 1 for
       every nonzero ring element b *)
    Lemma r_pos b : inRS b -> b ≢ 0 -> 1 <= vqq r + vqq b.
    Proof using HTM hq hgood hr hodd.
      move=> hbR nb.
      have h1 := vqr_ge1.
      case: (ltrP _ (vqq b) 0) => hb; last by slrb.
      case: (lerP _ 1 (vqq r + vqq b)) => // hlt.
      have hZ : isZA (vqq r + vqq b) by apply: trZ1_add; [ exact: vqr_int | exact: trV2_int ].
      have h0 := isZ_le0 hZ hlt.
      have hev := parity_step (inR_val rt) hbR hr nb hb ltac:(slrb).
      by exfalso; exact: even_odd_false hev hodd.
    Qed.

    Lemma q_neq2 : q ≢ 2%:R.
    Proof using hgood. by case: hgood => _ h; apply: h; apply: Sfix_2. Qed.

    Section at_w.

      Variable w : Pl A.
      Hypothesis hw : above A w q.

      Local Abbreviation vw := (vP A w).

      (* "w_*(x) > 0" for the coarsened valuation w_* (DESIGN 5.4, L3) *)
      Definition poswS (x : qe sQA) : Prop :=
        forall b, inRS b -> b ≢ 0 -> vgeS vw (x * qe_of b) 1.

      #[local] Instance poswS_wd : Proper (eqv ==> iff) poswS.
      Proof. move=> x x' E; rewrite /poswS; setoid_rewrite E; reflexivity. Qed.

      Let qnz (x y : qe sQA) : x ≢ 0 -> y ≢ 0 -> x * y ≢ 0.
      Proof. exact: (cq_mul_neq0 (@trZ0 D A)). Qed.

      Lemma qe_sqrt2_neq0 : qe_sqrt2 ≢ (0 : qe sQA).
      Proof. by move=> [ _ h ]; apply: sQ_1_neq_0. Qed.

      Lemma vw_of x : x ≢ 0 -> vw (qe_of x) ≡ vqq x.
      Proof using hw. exact: trPL3 hw. Qed.

      Lemma vw_sqrt2 : vw qe_sqrt2 ≡ 0.
      Proof using hw hq hgood.
        have ns := qe_sqrt2_neq0.
        have h := vP_mul hw ns ns.
        have n2 : (2%:R : sQA) ≢ 0 by move/pnatr_eq0.
        rewrite qe_sqrt2_sqr qe_natE in h.
        change (vw (qe_of 2%:R) ≡ vw qe_sqrt2 + vw qe_sqrt2) in h.
        rewrite (vw_of n2) in h.
        have hq2 : vqq 2%:R ≡ 0.
        { change (vqq (Posz 2)%:~R ≡ 0).
          apply: trV5 => // p; rewrite primes_prime // mem_seq1 => /eqP ->.
          exact: q_neq2. }
        rewrite hq2 in h; slrb.
      Qed.

      Lemma posw_add x y : poswS x -> poswS y -> poswS (x + y).
      Proof using hw.
        move=> hx hy b hb nb; rewrite mulrDl; exact: (vP_ge_add hw (hx b hb nb) (hy b hb nb)).
      Qed.

      Lemma posw_mulR x c : poswS x -> inRS c -> poswS (x * qe_of c).
      Proof using HTM.
        move=> hx hc b hb nb; rewrite -mulrA -qe_of_mul.
        case: (sof_eq_dec _ (c * b) 0) => [ h | ncb ].
        - by left; rewrite h qe_of0 mulr0; reflexivity.
        - exact: hx (inR_mul hc hb) ncb.
      Qed.

      Lemma posw_sqrt2 x : poswS x -> poswS (x * qe_sqrt2).
      Proof using hw hq hgood.
        have ns := qe_sqrt2_neq0.
        move=> hx b hb nb; rewrite mulrAC.
        case: (hx b hb nb) => [ h | h ]; first by left; rewrite h mul0r; reflexivity.
        case: (qe_dec (x * qe_of b) 0) => [ h0 | nxb ]; first by left; rewrite h0 mul0r; reflexivity.
        by right; rewrite (vP_mul hw nxb ns) vw_sqrt2 addr0.
      Qed.

      Lemma QE_split (c0 c1 : sQA) : QE c0 c1 ≡ qe_of c0 + qe_of c1 * qe_sqrt2.
      Proof. by split; rewrite /=; sring. Qed.

      (* posw is an R_F-ideal *)
      Lemma posw_mulRF x c0 c1 : poswS x -> inRS c0 -> inRS c1 -> poswS (x * QE c0 c1).
      Proof using HTM hw hq hgood.
        move=> hx h0 h1; rewrite QE_split mulrDr mulrA.
        apply: posw_add; first exact: posw_mulR.
        apply: posw_sqrt2; exact: posw_mulR.
      Qed.

      Lemma posw_r : poswS (qe_of r).
      Proof using HTM hq hgood hr hodd hw.
        move=> b hb nb; right; rewrite -qe_of_mul (vw_of (mulf_neq0 _ _ _ hr nb)) (vq_mul hq hr nb).
        exact: r_pos.
      Qed.

      (* the center is prime (uses excluded middle) *)
      Lemma posw_prime x y : poswS (x * y) -> poswS x \/ poswS y.
      Proof using HTM hw.
        move=> hxy; case: (classic (poswS x)) => hx; first by left.
        right; move: hx; rewrite /poswS => /not_all_ex_not [b0 /not_all_ex_not [hb0 /not_all_ex_not [nb0 hn]]].
        have nxb0 : x * qe_of b0 ≢ 0 by move=> h; apply: hn; left.
        have hlt : vw (x * qe_of b0) < 1.
        { case: (ltrP _ (vw (x * qe_of b0)) 1) => // h; exfalso; apply: hn; right; exact h. }
        have hle := isZ_le0 (vP_int hw nxb0) hlt.
        move=> b hb nb.
        case: (qe_dec (y * qe_of b) 0) => [ h | nyb ]; first by left.
        have nbb : b * b0 ≢ 0 by apply: mulf_neq0.
        have E : x * y * qe_of (b * b0) ≡ (x * qe_of b0) * (y * qe_of b) by rewrite qe_of_mul; sring.
        case: (hxy _ (inR_mul hb hb0) nbb) => [ h0 | h ].
        - by exfalso; apply: (qnz nxb0 nyb); rewrite -E h0; reflexivity.
        - right; move: h; rewrite E (vP_mul hw nxb0 nyb); slrb.
      Qed.

      (* Step 4, branch selection:  (sqrt2 - B)(sqrt2 + B) = -(r wB) *)
      Lemma branch_exists : exists sg : sgn, poswS (QE (- ((sgnz sg)%:~R * val Bt)) 1).
      Proof using HTM hq hgood hr hodd hB hw.
        have hprod : poswS (QE (- val Bt) 1 * QE (val Bt) 1).
        { have -> : QE (- val Bt) 1 * QE (val Bt) 1 ≡ qe_of r * qe_of (- val wBt).
          { split; rewrite /=; last by sring.
            transitivity (- (val Bt ^+ 2 - 2%:R)); first by sring.
            rewrite hB; sring. }
          apply: posw_mulR; [ exact: posw_r | apply: inR_opp; exact: inR_val ]. }
        case: (posw_prime hprod) => h.
        - exists sg_p.
          have E : QE (- ((sgnz sg_p)%:~R * val Bt)) 1 ≡ QE (- val Bt) 1 by split; rewrite /=; sring.
          by rewrite E.
        - exists sg_m.
          have E : QE (- ((sgnz sg_m)%:~R * val Bt)) 1 ≡ QE (val Bt) 1 by split; rewrite /=; sring.
          by rewrite E.
      Qed.

      Variable sg : sgn.
      Hypothesis hsg : poswS (QE (- ((sgnz sg)%:~R * val Bt)) 1).

      (* Step 5, red:valuation-transfer *)
      Lemma loc_transfer (l : nat) alpha : (1 <= l)%N ->
        LocAS val l r (val Bt) sg alpha -> vgeS vw alpha l%:R.
      Proof using HTM hq hgood hr hodd hw hsg.
        move=> hl [X0 [X1 [Y0 [Y1 [io [ka [e1 e2]]]]]]].
        case: (qe_dec alpha 0) => [ h | na ]; first by left.
        right.
        (* pi := Y io - 1 is positive *)
        set Yi := QE (val Y0) (val Y1) * qe_of (val io).
        have hpi : poswS (Yi - 1).
        { have -> : Yi - 1 ≡ qe_of r * qe_of (val ka)
                          + QE (- ((sgnz sg)%:~R * val Bt)) 1 * qe_of (val Y1 * val io).
          { rewrite /Yi; split; rewrite /=; last by sring.
            transitivity ((val Y0 + (sgnz sg)%:~R * val Bt * val Y1) * val io - 1
                          - (sgnz sg)%:~R * val Bt * (val Y1 * val io)); first by sring.
            rewrite e2; sring. }
          apply: posw_add.
          - apply: posw_mulR; [ exact: posw_r | exact: inR_val ].
          - apply: posw_mulR; [ exact: hsg | apply: inR_mul; exact: inR_val ]. }
        have nr : qe_of r ≢ 0 by apply: cq_of_neq0.
        have hpi1 : vgeS vw (Yi - 1) 1.
        { have := hpi 1 inR_1 sQ_1_neq_0; by rewrite cq_of1 mulr1. }
        (* hence v(Y io) = 0 *)
        have [nYi vYi] : Yi ≢ 0 /\ vw Yi ≡ 0.
        { have -> : Yi ≡ 1 + (Yi - 1) by sring.
          case: hpi1 => [ h | h ].
          { rewrite h addr0; split; [ exact: qe_1_neq_0 | exact: (vP_1 hw) ]. }
          case: (qe_dec (Yi - 1) 0) => [ h0 | npi ].
          { rewrite h0 addr0; split; [ exact: qe_1_neq_0 | exact: (vP_1 hw) ]. }
          have hlt : vw 1 < vw (Yi - 1) by rewrite (vP_1 hw); slrb.
          have [n1 E1] := vP_lt_add hw qe_1_neq_0 npi hlt.
          by split => //; rewrite E1 (vP_1 hw); reflexivity. }
        (* alpha Y io = r^l (X io) with X io in R_F *)
        have e3 : alpha * Yi ≡ qe_of r ^+ l * QE (val X0 * val io) (val X1 * val io).
        { rewrite /Yi mulrA e1 -mulrA.
          have -> : QE (val X0) (val X1) * qe_of (val io) ≡ QE (val X0 * val io) (val X1 * val io).
          { by split; rewrite /=; sring. }
          reflexivity. }
        have nl : alpha * Yi ≢ 0 by apply: qnz.
        have nXi : QE (val X0 * val io) (val X1 * val io) ≢ 0.
        { by move=> h; apply: nl; rewrite e3 h mulr0; reflexivity. }
        have hrX : poswS (qe_of r * QE (val X0 * val io) (val X1 * val io)).
        { apply: posw_mulRF; [ exact: posw_r | apply: inR_mul; exact: inR_val
                             | apply: inR_mul; exact: inR_val ]. }
        have nrX : qe_of r * QE (val X0 * val io) (val X1 * val io) ≢ 0 by apply: qnz.
        have vrX : 1 <= vw (qe_of r * QE (val X0 * val io) (val X1 * val io)).
        { case: (hrX 1 inR_1 sQ_1_neq_0); rewrite cq_of1 mulr1 => h.
          - by exfalso; apply: nrX.
          - exact: h. }
        move: e3; case: l hl e1 => // l _ _.
        rewrite exprSr -mulrA => e3.
        have [nrl vrl] := vP_exp hw l nr.
        have E := @vP_wd D A w _ _ e3.
        rewrite (vP_mul hw na nYi) vYi addr0 (vP_mul hw nrl nrX) vrl (vw_of hr) in E.
        rewrite E natrS.
        have h1 := vqr_ge1.
        have hl0 : (0 : sQA) <= l%:R by apply: ler0n.
        have : l%:R * 1 <= l%:R * vqq r by apply: ler_wpM2l.
        slrb.
      Qed.

      (* Step 6: tested formal points reduce to O at w *)
      Lemma formal_reduces (e : bool) (p : ptS sQA) :
        (p.1 ≢ 0 -> p.2.1 ≢ 0) ->
        FormalAS val e r (val Bt) sg p -> redAS vw e p.
      Proof using HTM hq hgood hr hodd hw hsg.
        move=> hx [ h0 | hF ]; first by left.
        case: (sof_eq_dec _ p.1 0) => [ h0 | np ]; first by left.
        right.
        have nx : qe_e e p.2.1 ≢ 0 by apply: cq_e_neq0; exact: (hx np).
        have nix : (qe_e e p.2.1)^-1 ≢ 0.
        { move=> h; apply: qe_1_neq_0; rewrite -(@qe_inv_l sQA (@trZ0 D A) _ nx) h; sring. }
        case: (loc_transfer (isT : (1 <= 1)%N) hF) => [ h | h ]; first by exfalso; apply: nix.
        move: h; rewrite (vP_inv hw nx); change ((1%:R : sQA)) with (1 : sQA); slrb.
      Qed.

    End at_w.

    (* Lemma red:coarsening *)
    Theorem coarsening : exists (sg : sgn) (w : Pl A),
         above A w q
      /\ (forall (l : nat) (alpha : qe sQA), (1 <= l)%N ->
            LocAS val l r (val Bt) sg alpha -> vgeS (vP A w) alpha l%:R)
      /\ (forall (e : bool) (p : ptS sQA), (p.1 ≢ 0 -> p.2.1 ≢ 0) ->
            FormalAS val e r (val Bt) sg p -> redAS (vP A w) e p).
    Proof using HTM hq hgood hr hodd hB.
      have [w hw] := trPL1 hq q_neq2.
      have [sg hsg] := branch_exists hw.
      exists sg, w; split => //; split.
      - move=> l alpha; exact: (loc_transfer hw hsg).
      - move=> e p; exact: (formal_reduces hw hsg).
    Qed.

  End coarsening.

End ambient.
