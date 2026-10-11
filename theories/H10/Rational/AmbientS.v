(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A (task P2a): the ambient structure of Ambient.v over a setoid
   ordered field (SOF.v), so that it can be instantiated by the
   ultrapower  rat^nat / U  (Ultrapower.v), whose equality is a Prop.

   The record [AmbientS D] mirrors [Ambient D] field by field (same names,
   same comments: ordinary statement and consuming lemma), with
   - carrier [sQ : SOF]; [=] becomes [≡], [<>]/[!= 0] becomes [≢];
   - points [ptS F := F * (qe F * qe F)] with a flag (see below) instead
     of [option];
   - one [Proper] field per parameter function or predicate ([isZ_wd],
     [primeA_wd], [vq_wd], [above_wd], [vP_wd], [mult_wd], [idx_wd],
     [MK_wd], [ht_wd]); [Pl] stays a bare Type (no equality on places
     is ever used);
   - the derived notions of Ambient.v / FixedData.v redefined generically
     over [SRing]/[SOF]: [vgeS], [oddZS], [evenZS], [redAS], [mnAS],
     [goodAS], [dp_evalS], [fd_LS], [qp_evalS], [qf_holdsS], [Phi_envS],
     [Phi_holdsS], [aES], [on_curveS], [ADD3S], [ADDfinS], [ADDrelS],
     [pt_negS], [pt_conjS], [zparS], [ellKS], [pt_ratS].
   The term model [TermModelS] is at the end; the compactness statement
   [CompactnessT D] (test-specific) is in TheoryS.v.

   POINTS. [ptS F := F * (qe F * qe F)]: the flag [p.1 ≡ 0] means O, a
   flag [p.1 ≢ 0] means the finite point [p.2]. Deviation from SETOID.md
   (which proposed [z ≡ z'] in [pt_eqv]): the equality is
     pt_eqv p q := (p.1 ≡ 0 <-> q.1 ≡ 0) /\ (p.1 ≢ 0 -> p.2 ≡ q.2)
   so every nonzero flag means "finite" (no normalization to 1 needs to
   be proved for [mult] or for [T t]); [val t] itself, [sof_nz (val t)]
   and 1 are all valid flags of a finite point. Where the flag enters a
   value it is normalized by [sof_nz] ([zparS]). A [match p with None => A
   | Some (x, y) => B end] of Ambient.v becomes [(p.1 ≡ 0 /\ A) \/
   (p.1 ≢ 0 /\ B)], or [p.1 ≡ 0 \/ B] when A is True.

   ULTRAPOWER CHECK (for task P5). Every field is a first-order statement
   about the parameters whose ordinary version holds, so it is proved in
   [ultrapower_SOF U HU] by Łoś for its own shape: atoms are pointwise
   modulo U, universal quantifiers are pointwise, and an existential
   needs a witness SEQUENCE, i.e. a function nat -> rat (or nat -> Pl_ord)
   computed from the data at index k without choice. Field by field:
   - [isZ], [primeA], [above] are pointwise predicates "U-a.e."; [vq],
     [vP], [mult], [MK], [ht], [idx] are pointwise images of ordinary
     total FUNCTIONS (vqr, place valuations, mulP, MK_ord, htb, idx_ord);
     their [Proper] fields hold since U-a.e. equal inputs give U-a.e.
     equal outputs. [Pl] := nat -> Pl_ord.
   - [trZ2] (parity): witness y_k := floor (x_k / 2), computable.
   - [trPL1]: witness w_k := a place above q_k; computable if ordinary
     places above an odd prime p are represented concretely (e.g. by p
     and the least root of X^2 - 2 mod p, a bounded search).
   - [trR1]: REFORMULATED without the existential of Ambient.v (the
     witnesses x, y were the coordinates of [mult n] anyway): it states
     the flag and coordinate conditions of [mult n] directly. The
     original form is recovered as [trR1_ex].
   - [trR5]: no existential; but [idx] must be the pointwise image of an
     ordinary total function idx_ord : qe rat * qe rat -> rat with
     idx_ord X = n whenever X = nP. NOTE: idx_ord cannot be defined by
     "the unique n with nP = X" (unique choice); it must be computable,
     e.g. a bounded search over |n| <= B(X) with B from the height
     comparison O_HL (red:elliptic-lower), or 0 outside. This is the only
     parameter whose ordinary definition is not elementary.
   - [trH2]: witness z_k := delta_k / MK_k^K (0 if MK_k = 0), computable.
   - [trHL], [trPP2], [trSIG]: the existentials are in premises. For
     [trSIG] the conclusion is a Prop existential over Z: the set of
     indices where all xs_i are integers and f vanishes is in U, hence
     (as a Prop) nonempty, and at such an index k the integers
     numq (xs_i k) are a zero (Sigma_1 reflection is FREE in the
     ultrapower).
   - [trH1]: the inner existential ranges over the finite type i4.
   - [trPP2]: conclusion [evenZS]: witness vq_k / 2, computable.
   No field needs a choice function, given computable idx_ord and a
   concrete representation of ordinary places. *)

From Stdlib Require Import Setoid Morphisms RelationClasses Arith ZArith Lia List.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos.

(* dio_logic is only Required, not Imported: its notations clash with MathComp *)
From Undecidability.H10.Dio
  Require dio_logic.

From Undecidability.H10
  Require Import H10Z.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData.

From Undecidability.H10.Rational
  Require Import SOF SOFTactics SOFqe SOFTheory SignatureS.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.
Import SOFTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope sof_scope.

(** * Generic helpers (Ambient.v, FixedData.v), setoid versions *)

(* evaluation of a Z-coefficient polynomial in a setoid ring *)
Fixpoint dp_evalS {R : SRing} {V P : Set} (φ : V -> R) (ν : P -> R)
  (p : dio_polynomial V P) : R :=
  match p with
  | dp_cnst n => of_Z n
  | dp_var v => φ v
  | dp_par i => ν i
  | dp_comp dio_logic.do_add p q => dp_evalS φ ν p + dp_evalS φ ν q
  | dp_comp dio_logic.do_mul p q => dp_evalS φ ν p * dp_evalS φ ν q
  end.

Lemma dp_evalS_ext {R : SRing} {V P : Set} (φ φ' : V -> R) (ν ν' : P -> R) p :
  (forall v, φ v ≡ φ' v) -> (forall i, ν i ≡ ν' i) -> dp_evalS φ ν p ≡ dp_evalS φ' ν' p.
Proof.
  move=> H1 H2; elim: p => [ z | v | i | [] p Hp q Hq ] /=.
  - reflexivity.
  - exact: H1.
  - exact: H2.
  - rewrite Hp Hq; reflexivity.
  - rewrite Hp Hq; reflexivity.
Qed.

(* "v(x) >= k", with v(0) = +oo *)
Definition vgeS {F : SRing} {R : SOF} (v : F -> R) (x : F) (k : R) : Prop :=
  x ≡ 0 \/ k <= v x.

#[global] Instance vgeS_wd {F : SRing} {R : SOF} (v : F -> R) :
  Proper (eqv ==> eqv) v -> Proper (eqv ==> eqv ==> iff) (vgeS v).
Proof. move=> Hv x x' Hx k k' Hk; rewrite /vgeS Hx Hk; reflexivity. Qed.

(* parity in *Z *)
Definition oddZS {R : SRing} (isZ : R -> Prop) (x : R) : Prop :=
  exists y, isZ y /\ x ≡ 2%:R * y + 1.
Definition evenZS {R : SRing} (isZ : R -> Prop) (x : R) : Prop :=
  exists y, isZ y /\ x ≡ 2%:R * y.

#[global] Instance oddZS_wd {R : SRing} (isZ : R -> Prop) : Proper (eqv ==> iff) (oddZS isZ).
Proof.
  move=> x x' Hx; rewrite /oddZS; split=> [] [ y [ Hy E ] ]; exists y; split => //.
  - rewrite -Hx; exact E.
  - rewrite Hx; exact E.
Qed.
#[global] Instance evenZS_wd {R : SRing} (isZ : R -> Prop) : Proper (eqv ==> iff) (evenZS isZ).
Proof.
  move=> x x' Hx; rewrite /evenZS; split=> [] [ y [ Hy E ] ]; exists y; split => //.
  - rewrite -Hx; exact E.
  - rewrite Hx; exact E.
Qed.

(* min{v_q(u), v_q(v)} with v_q(0) = +oo (for v <> 0) *)
Definition mnAS {F : SOF} (vq : F -> F) (u v : F) : F :=
  sof_sel0 u (vq v) (sof_min (vq u) (vq v)).

#[global] Instance mnAS_wd {F : SOF} (vq : F -> F) :
  Proper (eqv ==> eqv) vq -> Proper (eqv ==> eqv ==> eqv) (mnAS vq).
Proof. move=> Hv u u' Hu v v' Hw; rewrite /mnAS Hu Hw; reflexivity. Qed.

Lemma mnAS_0 {F : SOF} (vq : F -> F) u v : u ≡ 0 -> mnAS vq u v ≡ vq v.
Proof. exact: sel0_0. Qed.
Lemma mnAS_n {F : SOF} (vq : F -> F) u v : u ≢ 0 -> mnAS vq u v ≡ sof_min (vq u) (vq v).
Proof. exact: sel0_n. Qed.

(* q not in S_K, for an ambient prime q *)
Definition goodAS (D : FixedData) {F : SOF} (K : nat) (q : F) : Prop :=
  (K.+1)%:R < q /\ forall p : nat, p \in Sfix D -> q ≢ p%:R.

#[global] Instance goodAS_wd (D : FixedData) {F : SOF} (K : nat) : Proper (eqv ==> iff) (@goodAS D F K).
Proof. move=> q q' Hq; rewrite /goodAS; setoid_rewrite Hq; reflexivity. Qed.

(* the linear form L_b(U,V) = den(b) U - num(b) V (FixedData.fd_L) *)
Definition fd_LS (D : FixedData) {R : SRing} (i : i4) (u v : R) : R :=
  (denq (fd_C D i))%:~R * u - (numq (fd_C D i))%:~R * v.

#[global] Instance fd_LS_wd (D : FixedData) {R : SRing} (i : i4) : Proper (eqv ==> eqv ==> eqv) (@fd_LS D R i).
Proof. move=> u u' Hu v v' Hv; rewrite /fd_LS Hu Hv; reflexivity. Qed.

(** formulas with rational coefficients (FixedData.qp_evalR etc.) *)

Section qf_holdsS.

  Variable F : SOF.

  Fixpoint qp_evalS {V : Set} (φ : V -> F) (p : PosExistential.qpoly V) : F :=
    match p with
    | qp_cnst c => of_rat c
    | qp_var v => φ v
    | qp_add p q => qp_evalS φ p + qp_evalS φ q
    | qp_mul p q => qp_evalS φ p * qp_evalS φ q
    end.

  Fixpoint qf_holdsS {V : Set} (φ : V -> F) (A : qform V) : Prop :=
    match A with
    | qf_eq0 p => qp_evalS φ p ≡ 0
    | qf_neq0 p => qp_evalS φ p ≢ 0
    | qf_and A B => qf_holdsS φ A /\ qf_holdsS φ B
    | qf_or A B => qf_holdsS φ A \/ qf_holdsS φ B
    end.

  Lemma qp_evalS_ext {V : Set} (φ φ' : V -> F) p :
    (forall v, φ v ≡ φ' v) -> qp_evalS φ p ≡ qp_evalS φ' p.
  Proof.
    move=> H; elim: p => [ c | v | p Hp q Hq | p Hp q Hq ] /=.
    - reflexivity.
    - exact: H.
    - rewrite Hp Hq; reflexivity.
    - rewrite Hp Hq; reflexivity.
  Qed.

  Lemma qf_holdsS_ext {V : Set} (φ φ' : V -> F) A :
    (forall v, φ v ≡ φ' v) -> qf_holdsS φ A <-> qf_holdsS φ' A.
  Proof.
    move=> H; elim: A => [ p | p | A HA B HB | A HA B HB ] /=.
    - rewrite (qp_evalS_ext p H); reflexivity.
    - rewrite (qp_evalS_ext p H); reflexivity.
    - rewrite HA HB; reflexivity.
    - rewrite HA HB; reflexivity.
  Qed.

  Definition Phi_envS (b : F) (w : nat -> F) (i : nat) : F :=
    if i is 0 then b else w i.

  (* Phi(b) in an SOF: witnesses range over F *)
  Definition Phi_holdsS (L : seq (rat * seq rat)) (b : F) : Prop :=
    exists w : nat -> F, qf_holdsS (Phi_envS b w) (Phi_form L).

  #[global] Instance Phi_holdsS_wd L : Proper (eqv ==> iff) (Phi_holdsS L).
  Proof.
    move=> b b' Hb; rewrite /Phi_holdsS; split=> [] [ w Hw ]; exists w.
    - apply/(qf_holdsS_ext _ _ (φ := Phi_envS b w)) => // [] [ | i ] //=; reflexivity.
    - apply/(qf_holdsS_ext _ _ (φ := Phi_envS b' w)) => // [] [ | i ] //=; [ symmetry; exact Hb | reflexivity ].
  Qed.

End qf_holdsS.

Arguments qp_evalS {F V}.
Arguments qf_holdsS {F V}.
Arguments Phi_envS {F}.
Arguments Phi_holdsS {F}.

(** * Points (flag encoding) *)

Definition ptS (F : SRing) : Type := (F * (qe F * qe F))%type.

Section points.

  Variable F : SOF.

  Add Field pts_field : (@sof_fth F) (setoid (sr_setoid F) (sr_ext F),
    morphism (of_Z_morph F), constants [sof_cst],
    power_tac (sr_pow_th F) [sof_pow_cst], completeness (sof_Z_complete F)).
  Add Ring pts_qe_ring : (sr_rth (qe_SRing F)) (setoid (sr_setoid (qe_SRing F)) (sr_ext (qe_SRing F)),
    morphism (of_Z_morph (qe_SRing F)), constants [sof_cst],
    power_tac (sr_pow_th (qe_SRing F)) [sof_pow_cst]).

  Implicit Types (x y : qe F) (P Q : qe F * qe F) (p q : ptS F).

  (* NOTE: definitions with values in qe F are declared with the type
     [qe_SRing F] (convertible to [qe F]): [sring]/[sfield] find the ring
     structure from the type of the left-hand side of the goal, and fail
     ("Cannot find a declared ring structure over (qe F)") when it is
     syntactically [qe F]. *)

  (* equality of pairs of qe F *)
  Definition qp_eqv P Q : Prop := P.1 ≡ Q.1 /\ P.2 ≡ Q.2.

  #[global] Instance qp_eqv_equiv : Equivalence qp_eqv.
  Proof.
    split.
    - move=> P; split; reflexivity.
    - move=> P Q [ H1 H2 ]; split; symmetry; assumption.
    - move=> P Q R [ H1 H2 ] [ H3 H4 ]; split; etransitivity; eassumption.
  Qed.

  #[global] Instance pair_qp_wd : Proper (eqv ==> eqv ==> qp_eqv) (@pair (qe F) (qe F)).
  Proof. move=> x x' Hx y y' Hy; split; assumption. Qed.
  #[global] Instance fst_qp_wd : Proper (qp_eqv ==> eqv) (@fst (qe F) (qe F)).
  Proof. by move=> P Q []. Qed.
  #[global] Instance snd_qp_wd : Proper (qp_eqv ==> eqv) (@snd (qe F) (qe F)).
  Proof. by move=> P Q []. Qed.

  (* equality of points: same flag class, same coordinates if finite *)
  Definition pt_eqv p q : Prop := (p.1 ≡ 0 <-> q.1 ≡ 0) /\ (p.1 ≢ 0 -> qp_eqv p.2 q.2).

  #[global] Instance pt_eqv_equiv : Equivalence pt_eqv.
  Proof.
    split.
    - move=> p; split; [ reflexivity | move=> _; reflexivity ].
    - move=> p q [ H1 H2 ]; split; first by symmetry.
      move=> Hq; symmetry; apply: H2 => Hp; apply: Hq; exact/H1.
    - move=> p q r [ H1 H2 ] [ H3 H4 ]; split; first by rewrite H1.
      move=> Hp; have Hq : q.1 ≢ 0 by move=> Hq; apply: Hp; exact/H1.
      etransitivity; [ exact: H2 | exact: H4 ].
  Qed.

  Lemma pt_eqv_inf p q : pt_eqv p q -> (p.1 ≡ 0 <-> q.1 ≡ 0).
  Proof. by case. Qed.
  Lemma pt_eqv_fin p q : pt_eqv p q -> p.1 ≢ 0 -> qp_eqv p.2 q.2.
  Proof. by case. Qed.
  Lemma pt_eqv_fin' p q : pt_eqv p q -> q.1 ≢ 0 -> p.1 ≢ 0.
  Proof. by case=> H _ Hq Hp; apply: Hq; apply/H. Qed.

  (* constructors *)
  Lemma pt_eqv_O z z' P P' : z ≡ 0 -> z' ≡ 0 -> pt_eqv (z, P) (z', P').
  Proof. move=> /= H H'; split=> /=; [ by split | by move=> Hn; exfalso ]. Qed.
  Lemma pt_eqv_S z z' P P' : z ≢ 0 -> z' ≢ 0 -> qp_eqv P P' -> pt_eqv (z, P) (z', P').
  Proof. move=> /= H H' HP; split=> /=; last by move=> _. by split=> N; exfalso; [ exact: H | exact: H' ]. Qed.
  Lemma pt_eqv_mk z z' P P' : z ≡ z' -> qp_eqv P P' -> pt_eqv (z, P) (z', P').
  Proof. move=> Hz HP; split => /=; [ by rewrite Hz | by move=> _ ]. Qed.

  (* a point from a flag and coordinates *)
  #[global] Instance pair_pt_wd : Proper (eqv ==> qp_eqv ==> pt_eqv) (@pair F (qe F * qe F)).
  Proof.
    move=> z z' Hz P P' HP; split => /=; first by rewrite Hz.
    by move=> _.
  Qed.

  (** the curve E : y^2 = x^3 + aE x over qe F *)

  Definition aES : qe_SRing F := qe_rat (aE : qe rat).

  (* NOTE: do not state aES with the numerals 11243, 7950 in nat: they are
     unary, and unification with the rat constants of aE does not finish *)

  Definition on_curveS P : Prop := P.2 * P.2 ≡ P.1 ^+ 3 + aES * P.1.

  #[global] Instance on_curveS_wd : Proper (qp_eqv ==> iff) on_curveS.
  Proof. move=> P Q [ H1 H2 ]; rewrite /on_curveS H1 H2; reflexivity. Qed.

  (* p1 + p2 = p3 for three finite points (the case "Some, Some, Some" of ADDrel) *)
  Definition ADD3S (x1 y1 x2 y2 x3 y3 : qe F) : Prop :=
       (x1 ≢ x2
        /\ (x3 + x1 + x2) * (x2 - x1) ^+ 2 ≡ (y2 - y1) ^+ 2
        /\ (y3 + y1) * (x2 - x1) ≡ (y2 - y1) * (x1 - x3))
    \/ (x1 ≡ x2 /\ y1 ≡ y2 /\ y1 ≢ 0
        /\ (x3 + 2%:R * x1) * (2%:R * y1) ^+ 2 ≡ (3%:R * x1 ^+ 2 + aES) ^+ 2
        /\ (y3 + y1) * (2%:R * y1) ≡ (3%:R * x1 ^+ 2 + aES) * (x1 - x3)).

  #[global] Instance ADD3S_wd :
    Proper (eqv ==> eqv ==> eqv ==> eqv ==> eqv ==> eqv ==> iff) ADD3S.
  Proof.
    move=> x1 x1' H1 y1 y1' H2 x2 x2' H3 y2 y2' H4 x3 x3' H5 y3 y3' H6.
    rewrite /ADD3S H1 H2 H3 H4 H5 H6; reflexivity.
  Qed.

  (* p1 + p2 = p3 for finite p1, p2 *)
  Definition ADDfinS P1 P2 (p3 : ptS F) : Prop :=
       (P1.1 ≡ P2.1 /\ P1.2 ≡ - P2.2 /\ p3.1 ≡ 0)
    \/ (p3.1 ≢ 0 /\ ADD3S P1.1 P1.2 P2.1 P2.2 p3.2.1 p3.2.2).

  #[global] Instance ADDfinS_wd : Proper (qp_eqv ==> qp_eqv ==> pt_eqv ==> iff) ADDfinS.
  Proof.
    move=> P1 P1' [ E1 E2 ] P2 P2' [ E3 E4 ] p3 p3' Hp.
    have I := pt_eqv_inf Hp.
    rewrite /ADDfinS E1 E2 E3 E4.
    split=> [] [ [ H1 [ H2 H3 ] ] | [ Hn H ] ].
    - by left; split => //; split => //; apply/I.
    - right; have Hn' : p3'.1 ≢ 0 by move=> N; apply: Hn; apply/I.
      have [ E5 E6 ] := pt_eqv_fin Hp Hn.
      by split => //; rewrite -E5 -E6.
    - by left; split => //; split => //; apply/I.
    - right; have Hn' : p3.1 ≢ 0 by move=> N; apply: Hn; apply/I.
      have [ E5 E6 ] := pt_eqv_fin Hp Hn'.
      by split => //; rewrite E5 E6.
  Qed.

  (* the addition relation  p1 + p2 = p3  (FixedData.ADDrel) *)
  Definition ADDrelS (p1 p2 p3 : ptS F) : Prop :=
       (p1.1 ≡ 0 /\ pt_eqv p3 p2)
    \/ (p1.1 ≢ 0 /\ p2.1 ≡ 0 /\ pt_eqv p3 p1)
    \/ (p1.1 ≢ 0 /\ p2.1 ≢ 0 /\ ADDfinS p1.2 p2.2 p3).

  Lemma ADDrelS_mono p1 p1' p2 p2' p3 p3' : pt_eqv p1 p1' -> pt_eqv p2 p2' -> pt_eqv p3 p3' ->
    ADDrelS p1 p2 p3 -> ADDrelS p1' p2' p3'.
  Proof.
    move=> H1 H2 H3; have I1 := pt_eqv_inf H1; have I2 := pt_eqv_inf H2.
    case=> [ [ Z1 E ] | [ [ Z1 [ Z2 E ] ] | [ Z1 [ Z2 E ] ] ] ].
    - left; split; first exact/I1.
      by rewrite -H3 -H2.
    - have Z1' : p1'.1 ≢ 0 by move=> N; apply: Z1; apply/I1.
      right; left; split; first exact: Z1'.
      split; first exact/I2.
      by rewrite -H3 -H1.
    - have Z1' : p1'.1 ≢ 0 by move=> N; apply: Z1; apply/I1.
      have Z2' : p2'.1 ≢ 0 by move=> N; apply: Z2; apply/I2.
      right; right; split; first exact: Z1'.
      split; first exact: Z2'.
      by rewrite -(pt_eqv_fin H1 Z1) -(pt_eqv_fin H2 Z2) -H3.
  Qed.

  #[global] Instance ADDrelS_wd : Proper (pt_eqv ==> pt_eqv ==> pt_eqv ==> iff) ADDrelS.
  Proof.
    move=> p1 p1' H1 p2 p2' H2 p3 p3' H3; split; first exact: ADDrelS_mono.
    by apply: ADDrelS_mono; symmetry.
  Qed.

  (* the case of three finite points *)
  Lemma ADDrelS_SSS (z1 z2 z3 : F) x1 y1 x2 y2 x3 y3 : z1 ≢ 0 -> z2 ≢ 0 -> z3 ≢ 0 ->
    ADDrelS (z1, (x1, y1)) (z2, (x2, y2)) (z3, (x3, y3)) <-> ADD3S x1 y1 x2 y2 x3 y3.
  Proof.
    move=> H1 H2 H3; rewrite /ADDrelS /ADDfinS /=; split.
    - by case=> [ [] | [ [ _ [] ] | [ _ [ _ [ [ _ [ _ ] ] | [ _ H ] ] ] ] ] ].
    - by move=> H; right; right; split => //; split => //; right.
  Qed.

  Lemma ADDrelS_O_l p1 p2 p3 : p1.1 ≡ 0 -> ADDrelS p1 p2 p3 <-> pt_eqv p3 p2.
  Proof.
    move=> H; rewrite /ADDrelS; split; first by case=> [ [] | [ [] | [] ] ].
    by move=> E; left.
  Qed.

  Lemma ADDrelS_O_r p1 p2 p3 : p1.1 ≢ 0 -> p2.1 ≡ 0 -> ADDrelS p1 p2 p3 <-> pt_eqv p3 p1.
  Proof.
    move=> H1 H2; rewrite /ADDrelS; split; last by move=> E; right; left.
    by case=> [ [] | [ [ _ [] ] | [ _ [] ] ] ].
  Qed.

  Definition pt_negS p : ptS F := (p.1, (p.2.1, - p.2.2)).
  (* the conjugate point on E^sigma *)
  Definition pt_conjS p : ptS F := (p.1, (qe_conj p.2.1, qe_conj p.2.2)).

  #[global] Instance pt_negS_wd : Proper (pt_eqv ==> pt_eqv) pt_negS.
  Proof.
    move=> p q H; split; first exact: (pt_eqv_inf H).
    move=> Hp; have [ E1 E2 ] := pt_eqv_fin H Hp; split; rewrite /= ?E1 ?E2; reflexivity.
  Qed.
  #[global] Instance pt_conjS_wd : Proper (pt_eqv ==> pt_eqv) pt_conjS.
  Proof.
    move=> p q H; split; first exact: (pt_eqv_inf H).
    move=> Hp; have [ E1 E2 ] := pt_eqv_fin H Hp; split; rewrite /= ?E1 ?E2; reflexivity.
  Qed.

  (* the formal parameter z = -x/y with z(O) = 0, on E (sg = false) or
     E^sigma (sg = true); the flag is normalized by sof_nz *)
  Definition zparS (sg : bool) p : qe_SRing F :=
    qe_of (sof_nz p.1) * (- qe_e sg p.2.1 / qe_e sg p.2.2).

  Lemma zparS_0 sg p : p.1 ≡ 0 -> zparS sg p ≡ 0.
  Proof. move=> H; rewrite /zparS (nz_0 _ _ H) qe_of0; sring. Qed.
  Lemma zparS_n sg p : p.1 ≢ 0 -> zparS sg p ≡ - qe_e sg p.2.1 / qe_e sg p.2.2.
  Proof. move=> H; rewrite /zparS (nz_n _ _ H) qe_of1; sring. Qed.

  #[global] Instance zparS_wd sg : Proper (pt_eqv ==> eqv) (zparS sg).
  Proof.
    move=> p q H; case: (sof_eq_dec _ p.1 0) => Hp.
    - rewrite (@zparS_0 sg p Hp) (@zparS_0 sg q (proj1 (pt_eqv_inf H) Hp)); reflexivity.
    - have Hq : q.1 ≢ 0 by move=> N; apply: Hp; apply/(pt_eqv_inf H).
      have [ E1 E2 ] := pt_eqv_fin H Hp.
      rewrite (@zparS_n sg p Hp) (@zparS_n sg q Hq) E1 E2; reflexivity.
  Qed.

  (* reduction to O at a place with valuation vw *)
  Definition redAS (vw : qe F -> F) (sg : bool) p : Prop :=
    p.1 ≡ 0 \/ vw (qe_e sg p.2.1) < 0.

  #[global] Instance redAS_wd (vw : qe F -> F) sg :
    Proper (eqv ==> eqv) vw -> Proper (pt_eqv ==> iff) (redAS vw sg).
  Proof.
    move=> Hv p q H; rewrite /redAS (pt_eqv_inf H).
    case: (sof_eq_dec _ q.1 0) => Hq; first by split=> _; left.
    have Hp : p.1 ≢ 0 by move=> N; apply: Hq; apply/(pt_eqv_inf H).
    by rewrite (pt_eqv_fin H Hp).
  Qed.

  (** the truncated formal logarithm  l_K(Z) = sum_{t=1}^K c_t Z^t
      (FixedData.ellK, by recursion on K) *)

  Fixpoint ellKS (sg : bool) (K : nat) (Z : qe F) : qe_SRing F :=
    match K with
    | 0 => 0
    | S K' => ellKS sg K' Z + qe_rat (FixedData.qe_e sg (ct K)) * Z ^+ K
    end.

  Lemma ellKS_S sg K Z :
    ellKS sg K.+1 Z = ellKS sg K Z + qe_rat (FixedData.qe_e sg (ct K.+1)) * Z ^+ K.+1.
  Proof. reflexivity. Qed.

  #[global] Instance ellKS_wd sg K : Proper (eqv ==> eqv) (ellKS sg K).
  Proof.
    move=> Z Z' H; elim: K => [ | K IH ] /=; first reflexivity.
    rewrite IH H; reflexivity.
  Qed.

  (** ordinary points *)

  Definition pt_ratS (p : pt rat) : ptS F :=
    match p with
    | None => (0, (0, 0))
    | Some (x, y) => (1, (qe_rat x, qe_rat y))
    end.

  Lemma pt_ratS_None : (pt_ratS None).1 ≡ 0.
  Proof. reflexivity. Qed.
  Lemma pt_ratS_Some (x y : qe rat) : pt_eqv (pt_ratS (Some (x, y))) (1, (qe_rat x, qe_rat y)).
  Proof. reflexivity. Qed.

End points.

Arguments qp_eqv {F} P Q.
Arguments pt_eqv {F} p q.
Arguments aES {F}.
Arguments on_curveS {F} P.
Arguments ADD3S {F}.
Arguments ADDfinS {F} P1 P2 p3.
Arguments ADDrelS {F} p1 p2 p3.
Arguments pt_negS {F} p.
Arguments pt_conjS {F} p.
Arguments zparS {F} sg p.
Arguments redAS {F} vw sg p.
Arguments ellKS {F} sg K Z.
Arguments pt_ratS {F} p.

(** * The ambient structure (Ambient.v, setoid version) *)

Record AmbientS (D : FixedData) : Type := {

  (** signature *)
  sQ : SOF;                           (* *Q; ordinary rationals are of_rat x *)
  isZ : sQ -> Prop;                   (* *Z *)
  primeA : sQ -> Prop;                (* primes of *Z *)
  vq : sQ -> sQ -> sQ;                (* vq q x = v_q(x), for q prime and x <> 0 *)
  Pl : Type;                          (* internal places of *F = qe sQ (Risk 6) *)
  above : Pl -> sQ -> Prop;           (* w is above q, normalized w(q) = 1 *)
  vP : Pl -> qe sQ -> sQ;             (* vP w x = w(x), for x <> 0 *)
  mult : sQ -> ptS sQ;                (* n |-> nP, for n in *Z *)
  idx : qe sQ * qe sQ -> sQ;          (* the n with X = nP, for X in m E( *F) *)
  MK : nat -> sQ -> sQ;               (* MK K s = M_{S_K}(s), transfer of MK_ord *)
  ht : sQ -> sQ;                      (* bit height, transfer of x |-> (htb x)%:Z *)

  (** setoid compatibility of the parameters (new; pointwise in the ultrapower) *)
  isZ_wd : Proper (eqv ==> iff) isZ;
  primeA_wd : Proper (eqv ==> iff) primeA;
  vq_wd : Proper (eqv ==> eqv ==> eqv) vq;
  above_wd : forall w, Proper (eqv ==> iff) (above w);
  vP_wd : forall w, Proper (eqv ==> eqv) (vP w);
  mult_wd : Proper (eqv ==> pt_eqv) mult;
  idx_wd : Proper (qp_eqv ==> eqv) idx;
  MK_wd : forall K, Proper (eqv ==> eqv) (MK K);
  ht_wd : Proper (eqv ==> eqv) ht;

  (** structure of *Z (5.2) *)

  (* Z0: sqrt2 is not in *Q (so qe sQ is a field). Ordinary: sqrt2 irrational.
     Consumers: L0 (functionality of ADDrel), L1, L3 (inverses in qe sQ). *)
  trZ0 : forall x : sQ, x * x ≢ 2%:R;
  (* Z1: *Z contains the ordinary integers and is a subring.
     Consumers: everywhere. *)
  trZ1_int : forall z : int, isZ z%:~R;
  trZ1_add : forall x y, isZ x -> isZ y -> isZ (x + y);
  trZ1_opp : forall x, isZ x -> isZ (- x);
  trZ1_mul : forall x y, isZ x -> isZ y -> isZ (x * y);
  (* V0: discreteness. Ordinary: an integer > 0 is >= 1.
     Consumers: L2, L5 (finite intervals, |x| <= |delta| for x | delta). *)
  trV0 : forall x, isZ x -> 0 < x -> 1 <= x;
  (* Z2: parity. Ordinary: every integer is 2y or 2y+1.
     Consumers: L2, L3 (parity is exhaustive). *)
  trZ2 : forall x, isZ x -> exists y, isZ y /\ (x ≡ 2%:R * y \/ x ≡ 2%:R * y + 1);

  (** primes and valuations on *Q *)

  (* ordinary primes are exactly the ordinary elements that are ambient primes.
     Ordinary: definitional. Consumers: L2, L3 (q notin S_K for ordinary data). *)
  trPR : forall p : nat, primeA p%:R <-> prime p;
  (* V1. Ordinary: a prime is an integer > 1. Consumers: L2, L5. *)
  trV1 : forall q, primeA q -> isZ q /\ 1 < q;
  (* V2: v_q is a valuation on *Q^x with values in *Z. Ordinary: v_q on Q^x.
     Consumers: L1, L2, L3, L5. *)
  trV2_int : forall q x, primeA q -> x ≢ 0 -> isZ (vq q x);
  trV2_mul : forall q x y, primeA q -> x ≢ 0 -> y ≢ 0 -> vq q (x * y) ≡ vq q x + vq q y;
  trV2_ultra : forall q x y, primeA q -> x ≢ 0 -> y ≢ 0 -> x + y ≢ 0 ->
                 sof_min (vq q x) (vq q y) <= vq q (x + y);
  (* V3: normalization. Ordinary: v_q(q) = 1. Consumers: L1, L3. *)
  trV3 : forall q, primeA q -> vq q q ≡ 1;
  (* V4: integers are q-integral. Ordinary: v_q(x) >= 0 on Z \ 0. Consumers: L1, L2, L5. *)
  trV4 : forall q x, primeA q -> isZ x -> x ≢ 0 -> 0 <= vq q x;
  (* V5 (scheme over ordinary k): v_q(k) = 0 for q not dividing k. Ordinary: idem.
     Used for 2, 3, 4, the elements of Kset, the Phi entries, the determinants.
     Consumers: L1 (v_q(4) = 0), L2 (multipliers, determinants), L3. *)
  trV5 : forall (k : int) q, (k != 0)%R -> primeA q ->
           (forall p : nat, p \in primes (absz k) -> q ≢ p%:R) -> vq q k%:~R ≡ 0;

  (** internal places of *F *)

  (* PL0: places are above odd primes (Risk 19). Ordinary: the family of places
     of F above odd primes. Consumers: L1, L3. *)
  trPL0 : forall w q, above w q -> primeA q /\ q ≢ 2%:R;
  (* PL1: every odd prime has a place above it. Ordinary: idem.
     Consumers: L3 (choice of w; must be internal, Risk 6). *)
  trPL1 : forall q, primeA q -> q ≢ 2%:R -> exists w, above w q;
  (* PL2: vP w is a valuation on *F^x with values in *Z. Ordinary: odd primes are
     unramified in F, so v(F^x) = Z when v(p) = 1. Consumers: L1, L3. *)
  trPL2_int : forall w q x, above w q -> x ≢ 0 -> isZ (vP w x);
  trPL2_mul : forall w q x y, above w q -> x ≢ 0 -> y ≢ 0 -> vP w (x * y) ≡ vP w x + vP w y;
  trPL2_ultra : forall w q x y, above w q -> x ≢ 0 -> y ≢ 0 -> x + y ≢ 0 ->
                  sof_min (vP w x) (vP w y) <= vP w (x + y);
  (* PL3: restriction to *Q is v_q. Ordinary: idem. Consumers: L1, L3. *)
  trPL3 : forall w q x, above w q -> x ≢ 0 -> vP w (qe_of x) ≡ vq q x;

  (** Prop ell:rank (DESIGN 2.1), ordinary version [O_rank] and [E1], [E2] *)

  (* R1: nonzero multiples are finite points with x, y <> 0 on E.
     Ordinary: E2 for P. Consumers: L0 (injectivity of eta, ax_coord).
     (Ambient.v: exists x y, mult n = Some (x, y) /\ ...; see [trR1_ex].) *)
  trR1 : forall n, isZ n -> n ≢ 0 ->
           (mult n).1 ≢ 0 /\ (mult n).2.1 ≢ 0 /\ (mult n).2.2 ≢ 0 /\ on_curveS (mult n).2;
  (* R2: on ordinary integers, mult is n |-> nP. Ordinary: definitional.
     Consumers: L0 (eta 1 = 1, with ax_P), L5. Implies mult 0 = O. *)
  trR2 : forall n : int, pt_eqv (mult n%:~R) (pt_ratS (mulP D n));
  (* R3: group law on *Z P. Ordinary: E1 for P. Consumers: L0 (additivity). *)
  trR3 : forall n n', isZ n -> isZ n' -> ADDrelS (mult n) (mult n') (mult (n + n'));
  (* R5: m E( *F) is contained in *Z P, read off an addition chain
     Q_1, ..., Q_m = m Q_1. Ordinary: O_rank (m E(F) = Z P).
     Consumers: L0 (definition of eta from ax_chain). *)
  trR5 : forall Q : nat -> qe sQ * qe sQ,
           on_curveS (Q 1%N) ->
           (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ADDrelS (1, Q k) (1, Q 1%N) (1, Q k.+1)) ->
           isZ (idx (Q (fd_m D))) /\ pt_eqv (mult (idx (Q (fd_m D)))) (1, Q (fd_m D));

  (** Prop ell:formal (DESIGN 2.2), ordinary version [O_F1], [O_F2] *)

  (* F1, eq. ell:ratio. Consumers: L1 with sg = true (the alternate test). *)
  trF1 : forall (sg : bool) q, primeA q -> (forall p, p \in fd_SE D -> q ≢ p%:R) ->
           forall w, above w q -> forall n n', isZ n -> isZ n' -> n' ≢ 0 ->
           redAS (vP w) sg (mult n) -> redAS (vP w) sg (mult n') ->
           n ≡ 0 \/ vP w (zparS sg (mult n)) - vP w (zparS sg (mult n')) ≡ vq q n - vq q n';
  (* F2, eq. ell:truncation. Consumers: L1 with sg = false (the primary test). *)
  trF2 : forall (sg : bool) (K : nat) q, (1 <= K)%N -> primeA q ->
           (forall p, p \in fd_SE D -> q ≢ p%:R) -> (K.+1)%:R < q ->
           forall w, above w q -> forall n n', isZ n -> isZ n' -> n' ≢ 0 ->
           redAS (vP w) sg (mult n) -> redAS (vP w) sg (mult n') ->
           (n ≡ 0 \/ vq q n' <= vq q n) ->
           ellKS sg K (zparS sg (mult n')) ≢ 0 /\
           vgeS (vP w) (ellKS sg K (zparS sg (mult n)) / ellKS sg K (zparS sg (mult n'))
                        - qe_of (n / n')) K%:R;

  (** Thm hei:height and Cor hei:enlarge-exceptions (DESIGN 2.3),
      ordinary versions [O_height], [hei_enlarge_ord], [radical_divides_ord] *)

  (* H1: the primes counted by MK K (u/v) are good and have an odd contact
     order (hei:radical, for arbitrary homogeneous coordinates, by scaling
     invariance). Consumers: L2 (red:odd-r). *)
  trH1 : forall (K : nat) u v, v ≢ 0 -> (forall i, fd_LS D i u v ≢ 0) ->
           isZ (MK K (u / v)) /\ 1 <= MK K (u / v) /\
           forall q, primeA q -> 0 < vq q (MK K (u / v)) ->
             goodAS D K q /\
             (oddZS isZ (vq q v - mnAS (vq q) u v)
              \/ exists i, oddZS isZ (vq q (fd_LS D i u v) - mnAS (vq q) u v));
  (* H2: MK is squarefree, so q^K | delta for its primes gives MK^K | delta.
     Ordinary: radical_divides_ord. Consumers: L5 step 3 (red:radical-divides). *)
  trH2 : forall (K : nat) s delta, isZ delta -> delta ≢ 0 ->
           (forall q, primeA q -> 0 < vq q (MK K s) -> K%:R <= vq q delta) ->
           exists z, isZ z /\ delta ≡ MK K s ^+ K * z;
  (* H3: the height bound with S' = S_K. Ordinary: hei_enlarge_ord.
     Consumers: L5 step 5 (red:slope-height). *)
  trH3 : forall (K : nat) u v, v ≢ 0 -> (forall i, fd_LS D i u v ≢ 0) ->
           ht (u / v) <= (HK D K)%:R * MK K (u / v) ^+ fd_c D;

  (** further height facts (DESIGN 2.6, 2.7) *)

  (* heights are nonnegative elements of *Z. Ordinary: htb is a nat.
     Consumers: L5. *)
  trHT0 : forall x, isZ (ht x) /\ 0 <= ht x;
  (* HS, red:all-ring-height. Ordinary: O_HS. Consumers: L5 step 5. *)
  trHS : forall x1 x2 x3, ht (x1 + x2 + x3) <= ht x1 + ht x2 + ht x3 + 2%:R;
  (* HL, red:elliptic-upper/lower with heights over F. Ordinary: O_HL.
     Consumers: L5 step 6. *)
  trHL : forall n x0 x1 x2, isZ n -> n ≢ 0 -> x2 ≢ 0 ->
           (exists y, pt_eqv (mult n) (1, (QE x0 x1 / qe_of x2, y))) ->
           n ^+ 2 <= (fd_Nh D)%:R * (ht x0 + ht x1 + ht x2 + (fd_Ch D)%:R);

  (** elementarity (DESIGN 2.6, Risk 4) *)

  (* SIG (scheme over polynomials): an ambient integer zero gives an ordinary one.
     This is Sigma_1 reflection, a genuine use of elementarity.
     Consumers: L5 step 1 (delta = 0). *)
  trSIG : forall n (f : dio_polynomial (pos n) (pos 0)),
            (exists xs : pos n -> sQ, (forall i, isZ (xs i)) /\ dp_evalS xs (fun _ => 0) f ≡ 0) ->
            exists zs : pos n -> Z, dp_eval zs (fun _ => 0%ZZ) f = 0%ZZ;

  (** Prop par:pole-parity part 2 (DESIGN 2.4, PLAN Q4): PP2, literal transfer
      (the witnesses of Phi range over sQ). Ordinary: O_PP2. Consumers: L3
      step 1. *)
  trPP2 : forall b, b ≢ 0 -> Phi_holdsS (fd_PhiL D) b ->
            forall q, primeA q -> (forall p, p \in S1 D -> q ≢ p%:R) ->
            vq q b < 0 -> evenZS isZ (vq q b)
}.

Arguments sQ {D}.
Arguments isZ {D}.
Arguments primeA {D}.
Arguments vq {D}.
Arguments Pl {D}.
Arguments above {D}.
Arguments vP {D}.
Arguments mult {D}.
Arguments idx {D}.
Arguments MK {D}.
Arguments ht {D}.

#[global] Existing Instance isZ_wd.
#[global] Existing Instance primeA_wd.
#[global] Existing Instance vq_wd.
#[global] Existing Instance above_wd.
#[global] Existing Instance vP_wd.
#[global] Existing Instance mult_wd.
#[global] Existing Instance idx_wd.
#[global] Existing Instance MK_wd.
#[global] Existing Instance ht_wd.

(** small consequences, as sanity checks of the interface *)

Lemma mulP0 (D : FixedData) : mulP D 0%R = None.
Proof. by rewrite /mulP GRing.mul0r. Qed.

Section ambient_facts.

  Variables (D : FixedData) (A : AmbientS D).

  Lemma mult0 : pt_eqv (mult A 0) (0, (0, 0)).
  Proof. by have := trR2 A 0%R; rewrite mulP0. Qed.

  Lemma mult0_flag : (mult A 0).1 ≡ 0.
  Proof. apply/(pt_eqv_inf mult0); reflexivity. Qed.

  Lemma isZ0 : isZ A 0.
  Proof. exact: (trZ1_int A 0%R). Qed.

  Lemma isZ1 : isZ A 1.
  Proof. exact: (trZ1_int A 1%R). Qed.

  Lemma isZ_nat (n : nat) : isZ A n%:R.
  Proof. exact: (trZ1_int A n). Qed.

  Lemma isZ_sub x y : isZ A x -> isZ A y -> isZ A (x - y).
  Proof. by move=> Hx Hy; apply: trZ1_add => //; apply: trZ1_opp. Qed.

  (* the form of R1 in Ambient.v *)
  Lemma trR1_ex n : isZ A n -> n ≢ 0 ->
    exists x y, pt_eqv (mult A n) (1, (x, y)) /\ x ≢ 0 /\ y ≢ 0 /\ on_curveS (x, y).
  Proof.
    move=> Hn Hn0; have [ H1 [ H2 [ H3 H4 ] ] ] := trR1 Hn Hn0.
    exists (mult A n).2.1, (mult A n).2.2; split; last by [].
    apply: pt_eqv_S => //; first exact: sof_neq_1_0.
    by case: (mult A n).2 => ? ?; split; reflexivity.
  Qed.

End ambient_facts.

(** * Ground-term valuations and the compactness hypothesis, setoid version

    Constraints (a) to (d) of Ambient.v with [ring_okS], [fun_okS] and
    [fml_holdsS] (SignatureS.v) and [Phi_holdsS]. *)

Section compactness.

  Variable D : FixedData.

  (* a valuation of all ground terms in the ambient *Q satisfying (a) to (d) *)
  Record TermModelS (A : AmbientS D) (Ax : gfml -> Prop) (val : gterm -> sQ A) : Prop := {
    tm_ring : forall t, ring_okS val t;                           (* (a) *)
    tm_fun : forall t t', fun_okS val t t';                       (* (b) *)
    tm_inst : forall phi, Ax phi -> fml_holdsS val phi;           (* (c) *)
    tm_phi : forall t, Phi_holdsS (fd_PhiL D) (val t)             (* (d) *)
  }.

  (* NOTE (design change, coordinator): the general form
       forall Ax, Ambient.FinSat D Ax -> exists A val, TermModelS A Ax val
     is NOT used: for an arbitrary set Ax of instances the search for the
     assignment sequence in the ultrapower is not decidable, so it would
     need a choice function. The compactness statement used downstream is
     the test-specific [CompactnessT D] of TheoryS.v (it needs [Inst] and
     [test] of Theory.v), for which the matrix is decidable. *)

End compactness.

Arguments TermModelS {D} A Ax val.
