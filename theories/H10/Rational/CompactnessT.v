(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2B (task P5): the test-specific compactness statement
   [CompactnessT D] (TheoryS.v) is PROVED, by an ultrapower
   rat^nat / U over a nonprincipal ultrafilter U (Ultrafilter.v,
   Ultrapower.v), without any choice function.

   1-2. Pointwise evaluation ([ev_*], [qev_*]) and Łoś for atoms,
        connectives, points ([ptE]), the addition relation
        ([ADDrelE]), the curve ([on_curveE]), formulas ([qfE], [fmlE]).
   3.   The parameters, all pointwise images of ordinary total
        functions/predicates: isZ = a.e. isZo, primeA = a.e. primeo,
        vq = vqo, Pl = nat -> OPl, above = a.e. oaboveR, vP = ovP,
        mult n = mulP D (numq n_k) (flag encoding [liftpt]),
        idx = idx_ord (a Section variable: a TOTAL ordinary function
        with idx_ord (nP) = n), MK = MK_ord, ht = htb; their [Proper]
        fields.
   4-6. Every transfer field of [AmbientS D], from its ordinary
        statement (OrdinaryFacts, OrdPlaces, OrdHeights, OrdBridges,
        PoleParity) pointwise; existential conclusions by computable
        witness sequences (zhalf, oplaceR, delta / MK^K, the least bad
        prime for H2); trSIG by nonemptiness of a U-set (classic);
        the elliptic fields from E1, E2, O_rank, O_F1, O_F2, O_HL.
   7.   [upwAmbient]: the record.
   8.   The term model: for each N an assignment of test N is FOUND by
        [constructive_indefinite_ground_description_nat] over the
        enumeration of rational vectors (the matrix of a test is
        decidable, [qf_holdsb]); the value of a ground term t is the
        sequence of its values in these assignments; constraints
        (a)-(d) hold for all N beyond the index where t (resp. the
        instance) is listed: a cofinite set, in U by nonprincipality.
        The witnesses of Phi are variables of the test, so they come
        from the same search.
   9.   [CompactnessT_fine], [CompactnessT_thm]: the only use of
        [ultrafilter_exists], inside the Prop goal.

   Trust boundary of [CompactnessT_thm]: FixedWF D, E1, E2 (types of the
   StdHyps fields), OrdHyps D (only O_rank, O_F1, O_F2, O_height, O_HL
   are used; see [CompactnessT_fine]), and a total idx_ord with
   [forall n X, mulP D n = Some X -> idx_ord X = n].
   Print Assumptions: ultrafilter_exists, classic.

   PITFALL: never let unification see [aE] / [aES] (unary numerals):
   they are generalized before the Łoś tactics ([ADDrelE]). *)

From Stdlib Require Import Setoid Morphisms RelationClasses Arith ZArith Lia List.
From Stdlib Require Import ConstructiveEpsilon Classical_Prop.
From Stdlib Require Bool.

From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.H10.Dio Require dio_logic.
From Undecidability.H10 Require Import H10Z H10Q.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData Ambient Theory RatVal
                 OrdinaryFacts OrdPlaces OrdHeights OrdBridges PoleParity.

From Undecidability.H10.Rational
  Require Import Ultrafilter Ultrapower SOF SOFTactics SOFqe SOFTheory SignatureS AmbientS TheoryS.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.


(** * 1. Pointwise evaluation in the ultrapower *)

Section ev.

  Variables (U : (nat -> Prop) -> Prop) (HUf : ultrafilter U).
  Local Abbreviation F := (ultrapower_SOF U HUf).

  Implicit Types (x y : F) (k : nat).

  Lemma ev_add x y k : (x + y)%sof k = x k + y k. Proof. reflexivity. Qed.
  Lemma ev_mul x y k : (x * y)%sof k = x k * y k. Proof. reflexivity. Qed.
  Lemma ev_sub x y k : (x - y)%sof k = x k - y k. Proof. reflexivity. Qed.
  Lemma ev_opp x k : (- x)%sof k = - x k. Proof. reflexivity. Qed.
  Lemma ev_inv x k : (x^-1)%sof k = (x k)^-1. Proof. reflexivity. Qed.
  Lemma ev_div x y k : (x / y)%sof k = x k / y k. Proof. reflexivity. Qed.
  Lemma ev_abs x k : (`|x|)%sof k = `|x k|. Proof. reflexivity. Qed.
  Lemma ev_0 k : (0 : F)%sof k = 0. Proof. reflexivity. Qed.
  Lemma ev_1 k : (1 : F)%sof k = 1. Proof. reflexivity. Qed.
  Lemma ev_rat (a : rat) k : (of_rat a : F) k = a. Proof. reflexivity. Qed.

  Lemma ev_nat n k : (n%:R : F)%sof k = n%:R.
  Proof.
    elim: n => [ | [ | n ] IH ] //.
    transitivity ((n.+1%:R : F)%sof k + 1); first reflexivity.
    by rewrite IH -[(n.+2)%N]addn1 natrD.
  Qed.

  Lemma ev_int (z : int) k : (z%:~R : F)%sof k = z%:~R.
  Proof.
    case: z => n; first exact: ev_nat.
    transitivity (- ((n.+1)%:R : F)%sof k); first reflexivity.
    by rewrite ev_nat NegzE mulrNz.
  Qed.

  Lemma ev_Z (z : Z) k : (of_Z z : F) k = Z_to_rat z.
  Proof.
    rewrite /Z_to_rat; case: z => [ | p | p ] /=.
    - by rewrite subrr.
    - by rewrite /of_pos ev_nat subr0.
    - transitivity (- ((Pos.to_nat p)%:R : F)%sof k); first reflexivity.
      by rewrite ev_nat sub0r.
  Qed.

  Lemma ev_pow x n k : (x ^+ n)%sof k = x k ^+ n.
  Proof.
    elim: n => [ | n IH ] //.
    transitivity (x k * (x ^+ n)%sof k); first reflexivity.
    by rewrite IH exprS.
  Qed.

  Lemma rat_min_abs (a b : rat) : (a + b - `|a - b|) / 2%:R = Num.min a b.
  Proof.
    by case: (lerP a b) => h; field.
  Qed.

  Lemma ev_min x y k : (sof_min x y) k = Num.min (x k) (y k).
  Proof.
    rewrite -rat_min_abs.
    transitivity ((x k + y k - `|x k - y k|) / (2%:R : F)%sof k); first reflexivity.
    by rewrite ev_nat.
  Qed.

  Lemma ev_nz x k : (sof_nz x) k = if x k == 0 then 0 else 1.
  Proof.
    transitivity (x k * (x k)^-1); first reflexivity.
    case: eqP => [ -> | /eqP h ]; [ by rewrite mul0r | exact: mulfV ].
  Qed.

  Lemma ev_sel0 (c a b : F) k : (sof_sel0 c a b) k = if c k == 0 then a k else b k.
  Proof.
    transitivity (a k + (sof_nz c) k * (b k - a k)); first reflexivity.
    rewrite ev_nz; case: ifP => _; [ by rewrite mul0r addr0 | by rewrite mul1r addrC subrK ].
  Qed.

  (** elements of qe F, pointwise *)

  Definition qev (x : qe F) k : qe rat := QE (qre x k) (qim x k).

  Implicit Types (u v : qe F).

  Lemma qev_QE (a b : F) k : qev (QE a b) k = QE (a k) (b k). Proof. reflexivity. Qed.
  Lemma qev_add u v k : qev (u + v)%sof k = qev u k + qev v k. Proof. reflexivity. Qed.
  Lemma qev_opp u k : qev (- u)%sof k = - qev u k. Proof. reflexivity. Qed.
  Lemma qev_sub u v k : qev (u - v)%sof k = qev u k - qev v k. Proof. reflexivity. Qed.
  Lemma qev_0 k : qev 0%sof k = 0. Proof. reflexivity. Qed.
  Lemma qev_1 k : qev 1%sof k = 1. Proof. reflexivity. Qed.

  Lemma qev_mul u v k : qev (u * v)%sof k = qev u k * qev v k.
  Proof.
    case: u => a b; case: v => c d; rewrite /qev FixedData.qe_mulE; congr QE.
  Qed.

  Lemma qev_pow u n k : qev (u ^+ n)%sof k = qev u k ^+ n.
  Proof.
    elim: n => [ | n IH ] //.
    transitivity (qev (u * u ^+ n)%sof k); first reflexivity.
    by rewrite qev_mul IH exprS.
  Qed.

  Lemma qev_nat n k : qev (n%:R)%sof k = n%:R.
  Proof.
    elim: n => [ | [ | n ] IH ] //.
    transitivity (qev ((n.+1%:R) + 1)%sof k); first reflexivity.
    by rewrite qev_add IH -[(n.+2)%N]addn1 natrD.
  Qed.

  Lemma qev_int (z : int) k : qev (z%:~R)%sof k = z%:~R.
  Proof.
    case: z => n; first exact: qev_nat.
    transitivity (qev (- (n.+1)%:R)%sof k); first reflexivity.
    by rewrite qev_opp qev_nat NegzE mulrNz.
  Qed.

  Lemma qev_of (a : F) k : qev (qe_of a) k = FixedData.qe_of (a k). Proof. reflexivity. Qed.
  Lemma qev_conj u k : qev (qe_conj u) k = FixedData.qe_conj (qev u k). Proof. reflexivity. Qed.
  Lemma qev_e sg u k : qev (qe_e sg u) k = FixedData.qe_e sg (qev u k).
  Proof. by case: sg. Qed.
  Lemma qev_rat (c : qe rat) k : qev (qe_rat c : qe F) k = c.
  Proof. by case: c. Qed.

  Lemma qev_norm u k : (qe_norm u) k = FixedData.qe_norm (qev u k).
  Proof.
    rewrite /FixedData.qe_norm /=.
    transitivity ((qre u ^+ 2)%sof k - (2%:R : F)%sof k * (qim u ^+ 2)%sof k); first reflexivity.
    by rewrite !ev_pow ev_nat.
  Qed.

  Lemma qev_inv u k : qev (u^-1)%sof k = (qev u k)^-1.
  Proof.
    rewrite FixedData.qe_invE /FixedData.qe_inv -qev_norm.
    case: ifP => [ _ | /negbFE /eqP H ].
    - reflexivity.
    - have H0 : qev u k = 0.
      { apply/eqP; apply: contraTT (isT : true) => Hn.
        by move: (qe_norm_neq0 Hn); rewrite -qev_norm H eqxx. }
      rewrite H0; transitivity (QE (qre u k / (qe_norm u) k) (- qim u k / (qe_norm u) k)); first reflexivity.
      by rewrite H !invr0 !mulr0.
  Qed.

  Lemma qev_div u v k : qev (u / v)%sof k = qev u k / qev v k.
  Proof. by rewrite -qev_inv -qev_mul. Qed.

End ev.

(** * 2. Łoś for atoms and connectives *)

Section los.

  Variables (U : (nat -> Prop) -> Prop) (HUf : ultrafilter U).
  Local Abbreviation F := (ultrapower_SOF U HUf).

  Implicit Types (A B : nat -> Prop) (x y : F) (u v : qe F).

  Lemma uf_iff_ext A B : (forall k, A k <-> B k) -> (U A <-> U B).
  Proof using HUf. by move=> H; split => HA; apply: (uf_ae1 HUf _ _ HA) => k; apply H. Qed.

  Lemma los_and A B : U A /\ U B <-> U (fun k => A k /\ B k).
  Proof using HUf.
    split; first by case=> H1 H2; apply: (uf_inter HUf).
    by move=> H; split; apply: (uf_ae1 HUf _ _ H) => k [].
  Qed.

  Lemma los_or A B : U A \/ U B <-> U (fun k => A k \/ B k).
  Proof using HUf.
    split; last exact: (uf_or HUf).
    by case=> H; apply: (uf_ae1 HUf _ _ H) => k; auto.
  Qed.

  Lemma los_not A : ~ U A <-> U (fun k => ~ A k).
  Proof using HUf. exact: (uf_compl_iff HUf). Qed.

  Lemma los_True : True <-> U (fun _ => True).
  Proof using HUf. split => // _; exact: (uf_full HUf). Qed.

  Lemma los_False : False <-> U (fun _ => False).
  Proof using HUf. split => // H; exact: (uf_proper HUf H). Qed.

  Lemma uf_ex A : U A -> exists k, A k.
  Proof using HUf.
    move=> H; apply: NNPP => N; apply: (uf_proper HUf).
    apply: (uf_ae1 HUf _ _ H) => k Hk; apply: N; by exists k.
  Qed.

  Lemma uf_const (P : Prop) : U (fun _ => P) -> P.
  Proof using HUf. by move=> /uf_ex []. Qed.

  Lemma uf_list {X : Type} (l : list X) (A : X -> nat -> Prop) :
    (forall a, List.In a l -> U (A a)) -> U (fun k => forall a, List.In a l -> A a k).
  Proof using HUf.
    elim: l => [ | a l IH ] H; first by apply: (uf_all HUf) => k a [].
    apply: (uf_ae2 HUf _ _ _ (H a (or_introl erefl)) (IH (fun b Hb => H b (or_intror Hb)))).
    by move=> k h1 h2 b [ <- | Hb ]; [ exact: h1 | exact: h2 ].
  Qed.

  Lemma uf_or_list {X : Type} (l : list X) (A : X -> nat -> Prop) :
    U (fun k => exists a, List.In a l /\ A a k) -> exists a, List.In a l /\ U (A a).
  Proof using HUf.
    elim: l => [ | a l IH ] H.
    - exfalso; apply: (uf_proper HUf); apply: (uf_ae1 HUf _ _ H) => k [ ? [ [] ] ].
    - have H' : U (fun k => A a k \/ exists b, List.In b l /\ A b k).
      { apply: (uf_ae1 HUf _ _ H) => k [ b [ [ <- | Hb ] Hk ] ]; [ by left | by right; exists b ]. }
      case: (uf_or HUf _ _ H') => [ H1 | H2 ].
      + by exists a; split; [ left | ].
      + by have [ b [ Hb Hb' ] ] := IH H2; exists b; split; [ right | ].
  Qed.

  Lemma uf_cofinite (HNP : nonprincipal U) (N : nat) : U (fun k => le N k).
  Proof using HUf.
    apply: (uf_ae1 HUf (fun k => ~ lt k N)).
    - apply: (uf_compl HUf (fun k => lt k N)) => H; apply: (HNP _ _ H); by exists N.
    - move=> k; lia.
  Qed.

  (** atoms *)

  Lemma iff_and (P Q : Prop) A B : (P <-> U A) -> (Q <-> U B) -> (P /\ Q <-> U (fun k => A k /\ B k)).
  Proof using HUf. by move=> -> ->; exact: los_and. Qed.
  Lemma iff_or (P Q : Prop) A B : (P <-> U A) -> (Q <-> U B) -> (P \/ Q <-> U (fun k => A k \/ B k)).
  Proof using HUf. by move=> -> ->; exact: los_or. Qed.
  Lemma iff_not (P : Prop) A : (P <-> U A) -> (~ P <-> U (fun k => ~ A k)).
  Proof using HUf. by move=> ->; exact: los_not. Qed.

  Lemma eqvE x y : (x ≡ y)%sof <-> U (fun k => x k = y k). Proof. reflexivity. Qed.
  Lemma eq0E x : (x ≡ 0)%sof <-> U (fun k => x k = 0). Proof. reflexivity. Qed.
  Lemma neqE x y : (x ≢ y)%sof <-> U (fun k => x k <> y k).
  Proof using HUf. exact: los_not. Qed.
  Lemma neq0E x : (x ≢ 0)%sof <-> U (fun k => x k <> 0).
  Proof using HUf. exact: los_not. Qed.
  Lemma neq0U x : (x ≢ 0)%sof -> U (fun k => x k <> 0).
  Proof using HUf. exact: (proj1 (neq0E x)). Qed.
  Lemma neqU x y : (x ≢ y)%sof -> U (fun k => x k <> y k).
  Proof using HUf. exact: (proj1 (neqE x y)). Qed.

  Lemma leE x y : (x <= y)%sof <-> U (fun k => x k <= y k). Proof. reflexivity. Qed.
  Lemma ltE x y : (x < y)%sof <-> U (fun k => x k < y k). Proof. reflexivity. Qed.

  Lemma qeqvE u v : (u ≡ v)%sof <-> U (fun k => qev u k = qev v k).
  Proof using HUf.
    transitivity (U (fun k => qre u k = qre v k) /\ U (fun k => qim u k = qim v k)); first reflexivity.
    rewrite los_and; apply: uf_iff_ext => k; rewrite /qev; split; [ by case=> -> -> | by case ].
  Qed.

  Lemma qneqU u v : (u ≢ v)%sof -> U (fun k => qev u k <> qev v k).
  Proof using HUf. move=> H; apply/los_not; by rewrite -qeqvE. Qed.

  Lemma qeqvE' u v (a b : nat -> qe rat) : (forall k, qev u k = a k) -> (forall k, qev v k = b k) ->
    ((u ≡ v)%sof <-> U (fun k => a k = b k)).
  Proof using HUf. move=> Ha Hb; rewrite qeqvE; apply: uf_iff_ext => k; by rewrite Ha Hb. Qed.

  Lemma qneqE u v : (u ≢ v)%sof <-> U (fun k => qev u k <> qev v k).
  Proof using HUf. rewrite qeqvE; exact: los_not. Qed.

  (** points *)

  Definition fl (z : rat) (P : qe rat * qe rat) : pt rat := if z == 0 then None else Some P.

  Definition ptev (p : ptS F) k : pt rat := fl (p.1 k) (qev p.2.1 k, qev p.2.2 k).

  Lemma fl_None z P : fl z P = None <-> z = 0.
  Proof. rewrite /fl; case: eqP => //. Qed.

  Lemma fl_Some z P Q : fl z P = Some Q <-> z <> 0 /\ P = Q.
  Proof.
    rewrite /fl; case: eqP => [ -> | Hz ]; split.
    - by [].
    - by case.
    - by case=> ->.
    - by case=> _ ->.
  Qed.

  Lemma ptE (p q : ptS F) : pt_eqv p q <-> U (fun k => ptev p k = ptev q k).
  Proof using HUf.
    split.
    - case=> H1 H2; case: (uf_total HUf (fun k => p.1 k = 0)) => Z.
      + have Zq : U (fun k => q.1 k = 0) by apply/eq0E/H1.
        by apply: (uf_ae2 HUf _ _ _ Z Zq) => k h1 h2; rewrite /ptev (proj2 (fl_None _ _) h1) (proj2 (fl_None _ _) h2).
      + have NZp : (p.1 ≢ 0)%sof by apply/neq0E.
        have NZq : (q.1 ≢ 0)%sof by move=> /H1.
        have [ E1 E2 ] := H2 NZp; move: E1 E2 => /qeqvE E1 /qeqvE E2; move/neq0E: NZq => NZq.
        apply: (uf_ae2 HUf _ _ _ (uf_inter HUf _ _ Z NZq) (uf_inter HUf _ _ E1 E2)) => k [ h1 h2 ] [ e1 e2 ].
        by rewrite /ptev /fl; move/eqP/negbTE: h1 => ->; move/eqP/negbTE: h2 => ->; rewrite e1 e2.
    - move=> H; split; first split.
      + move/eq0E => Z; apply/eq0E; apply: (uf_ae2 HUf _ _ _ Z H) => k h e.
        by move: e; rewrite /ptev (proj2 (fl_None _ _) h) => /esym /fl_None.
      + move/eq0E => Z; apply/eq0E; apply: (uf_ae2 HUf _ _ _ Z H) => k h e.
        by move: e; rewrite /ptev (proj2 (fl_None _ _) h) => /fl_None.
      + move/neq0E => NZ; split; apply/qeqvE; apply: (uf_ae2 HUf _ _ _ NZ H) => k h e.
        * move: e; rewrite /ptev {1}/fl; move/eqP/negbTE: h => -> /esym /fl_Some [ _ E ].
          exact: (esym (f_equal fst E)).
        * move: e; rewrite /ptev {1}/fl; move/eqP/negbTE: h => -> /esym /fl_Some [ _ E ].
          exact: (esym (f_equal snd E)).
  Qed.

  (** the addition relation and the curve *)

  Definition ADD3r (x1 y1 x2 y2 x3 y3 : qe rat) : Prop :=
       (x1 <> x2
        /\ (x3 + x1 + x2) * (x2 - x1) ^+ 2 = (y2 - y1) ^+ 2
        /\ (y3 + y1) * (x2 - x1) = (y2 - y1) * (x1 - x3))
    \/ (x1 = x2 /\ y1 = y2 /\ y1 <> 0
        /\ (x3 + 2%:R * x1) * (2%:R * y1) ^+ 2 = (3%:R * x1 ^+ 2 + aE) ^+ 2
        /\ (y3 + y1) * (2%:R * y1) = (3%:R * x1 ^+ 2 + aE) * (x1 - x3)).

  Lemma fl_0 P : fl 0 P = None. Proof. by rewrite /fl eqxx. Qed.
  Lemma fl_n z P : z <> 0 -> fl z P = Some P.
  Proof. by move=> /eqP /negbTE H; rewrite /fl H. Qed.

  Lemma ADDrel_fl (z1 z2 z3 : rat) (x1 y1 x2 y2 x3 y3 : qe rat) :
    ADDrel (fl z1 (x1, y1)) (fl z2 (x2, y2)) (fl z3 (x3, y3)) <->
       (z1 = 0 /\ fl z3 (x3, y3) = fl z2 (x2, y2))
    \/ (z1 <> 0 /\ z2 = 0 /\ fl z3 (x3, y3) = fl z1 (x1, y1))
    \/ (z1 <> 0 /\ z2 <> 0 /\
          ((x1 = x2 /\ y1 = - y2 /\ z3 = 0) \/ (z3 <> 0 /\ ADD3r x1 y1 x2 y2 x3 y3))).
  Proof.
    case: (eqVneq z1 0) => [ -> | /eqP H1 ].
    { rewrite fl_0 /=; split; first by move=> E; left.
      by case=> [ [ _ E ] | [ [ H _ ] | [ H _ ] ] ]; [ exact: E | by [] | by [] ]. }
    case: (eqVneq z2 0) => [ -> | /eqP H2 ].
    { rewrite fl_0 (fl_n _ H1) /=; split.
      - by move=> E; right; left.
      - by case=> [ [ H _ ] | [ [ _ [ _ E ] ] | [ _ [ H _ ] ] ] ]; [ by [] | exact: E | by [] ]. }
    rewrite (fl_n _ H1) (fl_n _ H2) /=.
    case: (eqVneq z3 0) => [ -> | /eqP H3 ].
    { rewrite fl_0; split.
      - case=> [ E | [ x3' [ y3' [ E _ ] ] ] ]; last by [].
        by right; right; split => //; split => //; left; split; [ apply E | split; [ apply E | ] ].
      - case=> [ [ H _ ] | [ [ _ [ H _ ] ] | [ _ [ _ [ [ E1 [ E2 _ ] ] | [ H _ ] ] ] ] ] ].
        + by [].
        + by [].
        + by left.
        + by []. }
    rewrite (fl_n _ H3); split.
    - case=> [ [ _ [ _ E ] ] | [ x3' [ y3' [ E H ] ] ] ]; first by [].
      case: E => E1 E2; rewrite -E1 -E2 in H.
      by right; right; split => //; split => //; right.
    - case=> [ [ H _ ] | [ [ _ [ H _ ] ] | [ _ [ _ [ [ _ [ _ E ] ] | [ _ H ] ] ] ] ] ].
      + by [].
      + by [].
      + by exfalso; exact: (H3 E).
      + by right; exists x3, y3.
  Qed.

  Lemma aEv k : qev (aES : qe F) k = aE. Proof. exact: qev_rat. Qed.

  Local Ltac qev_rw := rewrite ?(qev_pow, qev_nat, qev_0, qev_1, qev_sub, qev_mul, qev_add, qev_opp).
  Local Ltac qev_rwA Ha := rewrite ?(qev_pow, qev_nat, qev_0, qev_1, qev_sub, qev_mul, qev_add, qev_opp, Ha).

  Ltac los_step :=
    lazymatch goal with
    | |- _ \/ _ <-> _ => apply: iff_or
    | |- _ /\ _ <-> _ => apply: iff_and
    | |- ~ _ <-> _ => apply: iff_not
    | |- pt_eqv _ _ <-> _ => apply: ptE
    | |- @eqv (sof_ring _) _ _ <-> _ => apply: eq0E
    | |- @eqv (qe_SRing _) _ _ <-> _ => apply: qeqvE'; move=> k; qev_rw; reflexivity
    end.
  Ltac los_tac := repeat los_step.
  Ltac los_stepA Ha :=
    lazymatch goal with
    | |- _ \/ _ <-> _ => apply: iff_or
    | |- _ /\ _ <-> _ => apply: iff_and
    | |- ~ _ <-> _ => apply: iff_not
    | |- pt_eqv _ _ <-> _ => apply: ptE
    | |- @eqv (sof_ring _) _ _ <-> _ => apply: eq0E
    | |- @eqv (qe_SRing _) _ _ <-> _ => apply: qeqvE'; move=> k; qev_rwA Ha; reflexivity
    end.

  Lemma ADDrelE (p1 p2 p3 : ptS F) :
    ADDrelS p1 p2 p3 <-> U (fun k => ADDrel (ptev p1 k) (ptev p2 k) (ptev p3 k)).
  Proof using HUf.
    rewrite (uf_iff_ext (fun k => ADDrel_fl (p1.1 k) (p2.1 k) (p3.1 k) _ _ _ _ _ _)).
    rewrite /ADDrelS /ADDfinS /ADD3S /ADD3r.
    move: (aEv); generalize (aES : qe F) => a; generalize (aE : qe rat) => e Ha.
    repeat los_stepA Ha.
  Qed.

  Lemma on_curveE (P : qe F * qe F) : on_curveS P <-> U (fun k => on_curve (qev P.1 k, qev P.2 k)).
  Proof using HUf.
    rewrite /on_curveS /on_curve.
    move: (aEv); generalize (aES : qe F) => a; generalize (aE : qe rat) => e Ha.
    apply: qeqvE'; move=> k; qev_rwA Ha; reflexivity.
  Qed.

  (** formulas *)

  Lemma qp_ev {V : Set} (φ : V -> F) (p : PosExistential.qpoly V) k :
    (@qp_evalS F V φ p) k = qp_eval (fun w => φ w k) p.
  Proof.
    elim: p => [ c | w | p Hp q Hq | p Hp q Hq ]; cbn [qp_evalS qp_eval] => //.
    - by rewrite ev_add Hp Hq.
    - by rewrite ev_mul Hp Hq.
  Qed.

  Lemma qfE {V : Set} (φ : V -> F) (A : qform V) :
    @qf_holdsS F V φ A <-> U (fun k => qf_holds (fun w => φ w k) A).
  Proof using HUf.
    elim: A => [ p | p | A HA B HB | A HA B HB ]; cbn [qf_holdsS qf_holds].
    - rewrite eq0E; apply: uf_iff_ext => k; by rewrite qp_ev.
    - rewrite neq0E; apply: uf_iff_ext => k; by rewrite qp_ev.
    - by rewrite HA HB los_and.
    - by rewrite HA HB los_or.
  Qed.

  Lemma fmlE (val : gterm -> F) (phi : gfml) :
    fml_holdsS val phi <-> U (fun k => fml_holds (fun t => val t k) phi).
  Proof using HUf.
    elim: phi => [ s t | s t | A HA B HB | A HA B HB | | ]; cbn [fml_holdsS fml_holds].
    - exact: eqvE.
    - exact: neqE.
    - by rewrite HA HB los_and.
    - by rewrite HA HB los_or.
    - exact: los_True.
    - exact: los_False.
  Qed.

  Lemma dpE {n : nat} (xs : pos n -> F) (f : dio_polynomial (pos n) (pos 0)) k :
    (dp_evalS xs (fun _ => 0%sof) f) k = dp_eval_rat (fun i => xs i k) (fun _ => 0) f.
  Proof.
    elim: f => [ z | w | i | [] p Hp q Hq ]; cbn [dp_evalS dp_eval_rat].
    - exact: ev_Z.
    - by [].
    - by [].
    - by rewrite ev_add Hp Hq.
    - by rewrite ev_mul Hp Hq.
  Qed.

End los.

(** * 3. The parameters of the ambient structure, pointwise *)

Lemma chain_idx_iff (D : FixedData) k : List.In k (chain_idx D) <-> (1 <= k)%N /\ (k < fd_m D)%N.
Proof.
  rewrite /chain_idx Theory.In_mem mem_iota; case: (fd_m D) => [ | m ] /=.
  - rewrite addn0; split.
    + by case/andP; case: k.
    + by case=> _; rewrite ltn0.
  - rewrite add1n; split; [ by case/andP | by case=> -> -> ].
Qed.

Section params.

  Variable D : FixedData.
  Variable idx_ord : qe rat * qe rat -> int.
  Variables (U : (nat -> Prop) -> Prop) (HUf : ultrafilter U).
  Local Abbreviation F := (ultrapower_SOF U HUf).

  Implicit Types (x y q n s : F) (j : nat).

  Definition isZu x : Prop := U (fun j => isZo (x j)).
  Definition primeu q : Prop := U (fun j => primeo (q j)).
  Definition vqu q x : F := fun j => (vqo (q j) (x j))%:~R.
  Definition Plu : Type := nat -> OPl.
  Definition aboveu (w : Plu) q : Prop := U (fun j => oaboveR (w j) (q j)).
  Definition vPu (w : Plu) (x : qe F) : F := fun j => (ovP (w j) (qev x j))%:~R.

  Definition ptc (p : pt rat) : rat * (qe rat * qe rat) :=
    match p with None => (0, (0, 0)) | Some P => (1, P) end.

  Definition liftpt (p : nat -> pt rat) : ptS F :=
    ((fun j => (ptc (p j)).1 : rat) : F,
     ((QE (fun j => qre (ptc (p j)).2.1) (fun j => qim (ptc (p j)).2.1) : qe F),
      (QE (fun j => qre (ptc (p j)).2.2) (fun j => qim (ptc (p j)).2.2) : qe F))).

  Definition multu n : ptS F := liftpt (fun j => mulP D (numq (n j))).
  Definition idxu (X : qe F * qe F) : F := fun j => (idx_ord (qev X.1 j, qev X.2 j))%:~R.
  Definition MKu (K : nat) s : F := fun j => (MK_ord D K (s j))%:R.
  Definition htu x : F := fun j => (htb (x j))%:R.

  Lemma lift1 p j : (liftpt p).1 j = (ptc (p j)).1. Proof. reflexivity. Qed.
  Lemma lift21 p j : qev (liftpt p).2.1 j = (ptc (p j)).2.1.
  Proof. by rewrite /qev /=; case: (ptc (p j)).2.1. Qed.
  Lemma lift22 p j : qev (liftpt p).2.2 j = (ptc (p j)).2.2.
  Proof. by rewrite /qev /=; case: (ptc (p j)).2.2. Qed.

  Lemma ptev_lift p j : ptev (liftpt p) j = p j.
  Proof.
    rewrite /ptev lift1 lift21 lift22; case: (p j) => [ [ X Y ] | ] /=.
    - by rewrite fl_n ?oner_neq0.
    - by rewrite fl_0.
  Qed.

  Lemma ptev_1 (P : qe F * qe F) j : ptev ((1 : F)%sof, P) j = Some (qev P.1 j, qev P.2 j).
  Proof. by rewrite /ptev fl_n //= => /eqP; rewrite oner_eq0. Qed.

  Lemma ptev_ratS (p : pt rat) j : ptev (pt_ratS p : ptS F) j = p.
  Proof.
    case: p => [ [ X Y ] | ] /=.
    - by rewrite ptev_1 /= !qev_rat.
    - by rewrite /ptev fl_0.
  Qed.

  (** setoid compatibility *)

  Lemma isZu_wd : Proper (eqv ==> iff) isZu.
  Proof using HUf.
    move=> x x' H; split=> H'; apply: (uf_ae2 HUf _ _ _ H H') => j e h; by rewrite ?e // -e.
  Qed.
  Lemma primeu_wd : Proper (eqv ==> iff) primeu.
  Proof using HUf.
    move=> x x' H; split=> H'; apply: (uf_ae2 HUf _ _ _ H H') => j e h; by rewrite ?e // -e.
  Qed.
  Lemma vqu_wd : Proper (eqv ==> eqv ==> eqv) vqu.
  Proof using HUf.
    move=> q q' Hq x x' Hx; apply: (uf_ae2 HUf _ _ _ Hq Hx) => j e1 e2; by rewrite /vqu e1 e2.
  Qed.
  Lemma aboveu_wd w : Proper (eqv ==> iff) (aboveu w).
  Proof using HUf.
    move=> x x' H; split=> H'; apply: (uf_ae2 HUf _ _ _ H H') => j e h; by rewrite ?e // -e.
  Qed.
  Lemma vPu_wd w : Proper (eqv ==> eqv) (vPu w).
  Proof using HUf.
    move=> x x' /qeqvE H; apply: (uf_ae1 HUf _ _ H) => j e; by rewrite /vPu e.
  Qed.
  Lemma multu_wd : Proper (eqv ==> pt_eqv) multu.
  Proof using HUf.
    move=> n n' H; apply/ptE; apply: (uf_ae1 HUf _ _ H) => j e; by rewrite /multu !ptev_lift e.
  Qed.
  Lemma idxu_wd : Proper (qp_eqv ==> eqv) idxu.
  Proof using HUf.
    move=> X X' [ /qeqvE H1 /qeqvE H2 ]; apply: (uf_ae2 HUf _ _ _ H1 H2) => j e1 e2.
    by rewrite /idxu e1 e2.
  Qed.
  Lemma MKu_wd K : Proper (eqv ==> eqv) (MKu K).
  Proof using HUf. move=> x x' H; apply: (uf_ae1 HUf _ _ H) => j e; by rewrite /MKu e. Qed.
  Lemma htu_wd : Proper (eqv ==> eqv) htu.
  Proof using HUf. move=> x x' H; apply: (uf_ae1 HUf _ _ H) => j e; by rewrite /htu e. Qed.

End params.

(** * 4. The elementary transfer fields *)

Section elementary.

  Variable D : FixedData.
  Variables (U : (nat -> Prop) -> Prop) (HUf : ultrafilter U).
  Local Abbreviation F := (ultrapower_SOF U HUf).

  Implicit Types (x y q n s : F) (j : nat).

  Local Abbreviation isZ := (@isZu U HUf).
  Local Abbreviation primeA := (@primeu U HUf).
  Local Abbreviation vq := (@vqu U HUf).
  Local Abbreviation above := (@aboveu U HUf).
  Local Abbreviation vP := (@vPu U HUf).

  Lemma neq0P (a : rat) : a <> 0 -> a != 0. Proof. by move/eqP. Qed.

  Lemma f_trZ0 x : (x * x ≢ 2%:R)%sof.
  Proof using HUf.
    apply/neqE; apply: (uf_all HUf) => j; rewrite ev_mul ev_nat; exact: ord_Z0.
  Qed.

  Lemma f_trZ1_int (z : int) : isZ (z%:~R)%sof.
  Proof using HUf. apply: (uf_all HUf) => j; rewrite /= ev_int; exact: ord_Z1_int. Qed.
  Lemma f_trZ1_add x y : isZ x -> isZ y -> isZ (x + y)%sof.
  Proof using HUf. move=> H1 H2; apply: (uf_ae2 HUf _ _ _ H1 H2) => j; exact: ord_Z1_add. Qed.
  Lemma f_trZ1_opp x : isZ x -> isZ (- x)%sof.
  Proof using HUf. move=> H1; apply: (uf_ae1 HUf _ _ H1) => j; exact: ord_Z1_opp. Qed.
  Lemma f_trZ1_mul x y : isZ x -> isZ y -> isZ (x * y)%sof.
  Proof using HUf. move=> H1 H2; apply: (uf_ae2 HUf _ _ _ H1 H2) => j; exact: ord_Z1_mul. Qed.

  Lemma f_trV0 x : isZ x -> (0 < x)%sof -> (1 <= x)%sof.
  Proof using HUf. move=> H1 H2; apply: (uf_ae2 HUf _ _ _ H1 H2) => j; exact: ord_V0. Qed.

  Lemma f_trZ2 x : isZ x -> exists y, isZ y /\ (x ≡ 2%:R * y \/ x ≡ 2%:R * y + 1)%sof.
  Proof using HUf.
    move=> H; exists (fun j => zhalf (x j)); split.
    - by apply: (uf_ae1 HUf _ _ H) => j /ord_Z2_fun [].
    - have H' := uf_ae1 HUf _ _ H (fun j h => proj2 (ord_Z2_fun h)).
      case: (uf_or HUf _ _ H') => H''; [ left | right ]; apply: (uf_ae1 HUf _ _ H'') => j ->.
      + by rewrite ev_mul ev_nat.
      + by rewrite ev_add ev_mul ev_nat.
  Qed.

  Lemma f_trPR (p : nat) : primeA (p%:R)%sof <-> prime p.
  Proof using HUf.
    split.
    - move=> H; apply: (uf_const HUf); apply: (uf_ae1 HUf _ _ H) => j; cbv beta; rewrite ev_nat; by move=> /ord_PR.
    - move=> H; apply: (uf_all HUf) => j; rewrite ev_nat; exact/ord_PR.
  Qed.

  Lemma f_trV1 q : primeA q -> isZ q /\ (1 < q)%sof.
  Proof using HUf.
    move=> H; split; apply: (uf_ae1 HUf _ _ H) => j /ord_V1 []; done.
  Qed.

  Lemma f_trV2_int q x : primeA q -> (x ≢ 0)%sof -> isZ (vq q x).
  Proof using HUf. move=> _ _; apply: (uf_all HUf) => j; exact: ord_Z1_int. Qed.

  Lemma f_trV2_mul q x y : primeA q -> (x ≢ 0)%sof -> (y ≢ 0)%sof -> (vq q (x * y) ≡ vq q x + vq q y)%sof.
  Proof using HUf.
    move=> H /neq0U Hx /neq0U Hy; apply: (uf_ae3 HUf _ _ _ _ H Hx Hy) => j h hx hy.
    rewrite ev_add /vqu ev_mul; apply: ord_V2_mulR => //; exact/eqP.
  Qed.

  Lemma f_trV2_ultra q x y : primeA q -> (x ≢ 0)%sof -> (y ≢ 0)%sof -> (x + y ≢ 0)%sof ->
    (sof_min (vq q x) (vq q y) <= vq q (x + y))%sof.
  Proof using HUf.
    move=> H /neq0U Hx /neq0U Hy /neq0U Hxy.
    apply: (uf_ae3 HUf _ _ _ _ (uf_inter HUf _ _ H Hxy) Hx Hy) => j [ h hxy ] hx hy.
    rewrite ev_min /vqu ev_add; apply: ord_V2_ultraR => //; apply/eqP => //.
  Qed.

  Lemma f_trV3 q : primeA q -> (vq q q ≡ 1)%sof.
  Proof using HUf. move=> H; apply: (uf_ae1 HUf _ _ H) => j h; by rewrite /vqu ord_V3. Qed.

  Lemma f_trV4 q x : primeA q -> isZ x -> (x ≢ 0)%sof -> (0 <= vq q x)%sof.
  Proof using HUf.
    move=> H Hx /neq0U Hn; apply: (uf_ae3 HUf _ _ _ _ H Hx Hn) => j h hx hn.
    rewrite /vqu ler0z; apply: ord_V4 => //; exact/eqP.
  Qed.

  Lemma f_trV5 (k : int) q : (k != 0)%R -> primeA q ->
    (forall p : nat, p \in primes (absz k) -> (q ≢ p%:R)%sof) -> (vq q k%:~R ≡ 0)%sof.
  Proof using HUf.
    move=> Hk H Hp.
    have Hl := uf_list HUf (l := primes (absz k)) (A := fun p j => q j <> p%:R).
    have Hl' : U (fun j => forall p, List.In p (primes (absz k)) -> q j <> p%:R).
    { apply: Hl => p /Theory.In_mem /Hp /neqU H'; apply: (uf_ae1 HUf _ _ H') => j; by rewrite ev_nat. }
    apply: (uf_ae2 HUf _ _ _ H Hl') => j h hl.
    rewrite /vqu ev_int ord_V5 // => p /Theory.In_mem /hl h0; exact/eqP.
  Qed.

  (** places *)

  Lemma f_trPL0 w q : above w q -> primeA q /\ (q ≢ 2%:R)%sof.
  Proof using HUf.
    move=> H; split; first by apply: (uf_ae1 HUf _ _ H) => j /ord_PL0R [].
    apply: (proj2 (neqE _ _)); apply: (uf_ae1 HUf _ _ H) => j /ord_PL0R [ _ h ].
    by rewrite ev_nat; apply/eqP.
  Qed.

  Lemma f_trPL1 q : primeA q -> (q ≢ 2%:R)%sof -> exists w, above w q.
  Proof using HUf.
    move=> H /neqU H2; exists (fun j => oplaceR (q j)).
    apply: (uf_ae2 HUf _ _ _ H H2) => j h1 h2; apply: ord_PL1R => //.
    by move: h2; rewrite ev_nat => /eqP.
  Qed.

  Lemma f_trPL2_int w q (x : qe F) : above w q -> (x ≢ 0)%sof -> isZ (vP w x).
  Proof using HUf. move=> _ _; apply: (uf_all HUf) => j; exact: ord_Z1_int. Qed.

  Lemma f_trPL2_mul w q (x y : qe F) : above w q -> (x ≢ 0)%sof -> (y ≢ 0)%sof ->
    (vP w (x * y) ≡ vP w x + vP w y)%sof.
  Proof using HUf.
    move=> H /qneqU Hx /qneqU Hy; apply: (uf_ae3 HUf _ _ _ _ H Hx Hy) => j h hx hy.
    rewrite qev_0 in hx hy; rewrite ev_add /vPu qev_mul; apply: ord_PL2_mulR h _ _; exact/eqP.
  Qed.

  Lemma f_trPL2_ultra w q (x y : qe F) : above w q -> (x ≢ 0)%sof -> (y ≢ 0)%sof -> (x + y ≢ 0)%sof ->
    (sof_min (vP w x) (vP w y) <= vP w (x + y))%sof.
  Proof using HUf.
    move=> H /qneqU Hx /qneqU Hy /qneqU Hxy.
    apply: (uf_ae3 HUf _ _ _ _ (uf_inter HUf _ _ H Hxy) Hx Hy) => j [ h hxy ] hx hy.
    rewrite qev_0 in hx hy hxy; rewrite ev_min /vPu qev_add; apply: ord_PL2_ultraR h _ _ _; exact/eqP.
  Qed.

  Lemma f_trPL3 w q x : above w q -> (x ≢ 0)%sof -> (vP w (qe_of x) ≡ vq q x)%sof.
  Proof using HUf.
    move=> H /neq0U Hx; apply: (uf_ae2 HUf _ _ _ H Hx) => j h hx.
    rewrite /vPu /vqu qev_of (ord_PL3R h) //; exact/eqP.
  Qed.

  (** R2 *)

  Lemma f_trR2 (n : int) : pt_eqv (multu D (n%:~R : F)%sof) (pt_ratS (mulP D n)).
  Proof using HUf.
    apply/ptE; apply: (uf_all HUf) => j; by rewrite /multu ptev_lift ptev_ratS ev_int numq_int.
  Qed.

  (** heights *)

  Lemma f_trHT0 x : isZ (htu x) /\ (0 <= htu x)%sof.
  Proof using HUf. split; apply: (uf_all HUf) => j; have [ ? ? ] := ord_HT0 (x j); done. Qed.

  Lemma f_trHS x1 x2 x3 : (htu (x1 + x2 + x3) <= htu x1 + htu x2 + htu x3 + 2%:R)%sof.
  Proof using HUf.
    apply: (uf_all HUf) => j; rewrite !ev_add ev_nat /htu; exact: ord_HS.
  Qed.

  (** Sigma_1 reflection *)

  Lemma f_trSIG (n : nat) (f : dio_polynomial (pos n) (pos 0)) :
    (exists xs : pos n -> F, (forall i, isZ (xs i)) /\ (dp_evalS xs (fun _ => 0) f ≡ 0)%sof) ->
    exists zs : pos n -> Z, dp_eval zs (fun _ => 0%ZZ) f = 0%ZZ.
  Proof using HUf.
    move=> [ xs [ Hxs Hf ] ].
    have Hl := uf_list HUf (l := pos_list n) (A := fun i j => isZo (xs i j)) (fun i _ => Hxs i).
    have [ j [ h1 h2 ] ] := uf_ex HUf (uf_inter HUf _ _ Hl Hf).
    exists (fun i => int_to_Z (numq (xs i j))).
    apply: Z_to_rat_inj; rewrite -dp_eval_rat_Z Z_to_rat_0.
    transitivity ((dp_evalS xs (fun _ => 0%sof) f) j); last exact: h2.
    rewrite dpE.
    apply: dp_eval_rat_ext => [ v _ | i _ ].
    - by rewrite Z_to_rat_int -isZo_numq //; apply: h1; apply: pos_list_prop.
    - by [].
  Qed.

End elementary.

(** * 5. The height and parity fields *)

Lemma oddZ_zhalf (x : rat) : oddZ isZo x -> isZo (zhalf x) /\ x = 2%:R * zhalf x + 1.
Proof.
  move=> Ho; have Hx : isZo x.
  { case: Ho => y [ Hy -> ]; apply: ord_Z1_add; [ apply: ord_Z1_mul => //; exact: isZo_nat | exact: (ord_Z1_int 1) ]. }
  have [ Hh [ E | E ] ] := ord_Z2_fun Hx; last by [].
  exfalso; have [ c Hc ] := Hh.
  have Ex : x = (2 * c)%:~R by rewrite E Hc intrM.
  move: Ho; rewrite Ex => /oddZ_int; by rewrite abszM oddM.
Qed.

Lemma evenZ_zhalf (z : int) : ~~ odd `|z| -> isZo (zhalf z%:~R) /\ (z%:~R : rat) = 2%:R * zhalf z%:~R.
Proof.
  move=> He; have [ Hh [ E | E ] ] := ord_Z2_fun (ord_Z1_int z); first by [].
  exfalso; move/negP: He; apply; apply/oddZ_int; by exists (zhalf z%:~R).
Qed.

Section heights.

  Variable D : FixedData.
  Variables (U : (nat -> Prop) -> Prop) (HUf : ultrafilter U).
  Local Abbreviation F := (ultrapower_SOF U HUf).

  Implicit Types (x y q n s : F) (j : nat).

  Local Abbreviation isZ := (@isZu U HUf).
  Local Abbreviation primeA := (@primeu U HUf).
  Local Abbreviation vq := (@vqu U HUf).

  Lemma oddZ_lift x : U (fun j => oddZ isZo (x j)) -> oddZS isZ x.
  Proof using HUf.
    move=> H; exists (fun j => zhalf (x j)); split.
    - by apply: (uf_ae1 HUf _ _ H) => j /oddZ_zhalf [].
    - apply: (uf_ae1 HUf _ _ H) => j /oddZ_zhalf [ _ E ].
      by rewrite ev_add ev_mul ev_nat ev_1.
  Qed.

  Lemma evenZ_lift x : U (fun j => exists z : int, x j = z%:~R /\ ~~ odd `|z|) -> evenZS isZ x.
  Proof using HUf.
    move=> H; exists (fun j => zhalf (x j)); split.
    - by apply: (uf_ae1 HUf _ _ H) => j [ z [ -> /evenZ_zhalf [] ] ].
    - apply: (uf_ae1 HUf _ _ H) => j [ z [ E /evenZ_zhalf [ _ E' ] ] ].
      by rewrite ev_mul ev_nat E.
  Qed.

  Lemma fdL_ev (i : i4) u v j : (fd_LS D i u v : F) j = fd_L D i (u j) (v j).
  Proof. by rewrite /fd_LS ev_sub !ev_mul !ev_int. Qed.

  Lemma mnA_ev q u v j : (mnAS (vq q) u v) j = mnA (fun t => (vqo (q j) t)%:~R) (u j) (v j).
  Proof. by rewrite /mnAS ev_sel0 ev_min. Qed.

  Lemma all_i4_U (A : i4 -> nat -> Prop) : (forall i, U (A i)) -> U (fun j => forall i, A i j).
  Proof using HUf.
    move=> H; have Hl := uf_list HUf (l := all_i4) (A := A) (fun i _ => H i).
    apply: (uf_ae1 HUf _ _ Hl) => j h i; apply: h; exact: all_i4_spec.
  Qed.

  Lemma f_trH1 (K : nat) u v : (v ≢ 0)%sof -> (forall i, fd_LS D i u v ≢ 0)%sof ->
    isZ (MKu D K (u / v)%sof) /\ (1 <= MKu D K (u / v)%sof)%sof /\
    forall q, primeA q -> (0 < vq q (MKu D K (u / v)%sof))%sof ->
      goodAS D K q /\
      (oddZS isZ (vq q v - mnAS (vq q) u v)%sof
       \/ exists i, oddZS isZ (vq q (fd_LS D i u v) - mnAS (vq q) u v)%sof).
  Proof using HUf.
    move=> /neq0U Hv HL.
    have HL' : U (fun j => forall i, fd_L D i (u j) (v j) != 0).
    { apply: all_i4_U => i; apply: (uf_ae1 HUf _ _ (neq0U (HL i))) => j; cbv beta; rewrite fdL_ev => h; exact/eqP. }
    have H := uf_ae2 HUf _ _ _ Hv HL' (fun j hv hl => @ord_H1 D K (u j) (v j) (introN eqP hv) hl).
    split; first by apply: (uf_ae1 HUf _ _ H) => j [].
    split; first by apply: (uf_ae1 HUf _ _ H) => j [ _ [] ].
    move=> q Hq Hpos.
    have H' : U (fun j => goodA D K (q j) /\
      (oddZ isZo ((vqo (q j) (v j))%:~R - mnA (fun t => (vqo (q j) t)%:~R) (u j) (v j))
       \/ exists i, oddZ isZo ((vqo (q j) (fd_L D i (u j) (v j)))%:~R
                               - mnA (fun t => (vqo (q j) t)%:~R) (u j) (v j)))).
    { apply: (uf_ae3 HUf _ _ _ _ H Hq Hpos) => j h hq hp; apply: (proj2 (proj2 h)) => //.
      by move: hp; rewrite /vqu /MKu ev_div ltr0z. }
    split.
    - split.
      + apply: (uf_ae1 HUf _ _ H') => j [ [ h _ ] _ ]; by rewrite ev_nat.
      + move=> p Hp; apply: (proj2 (neqE _ _)); apply: (uf_ae1 HUf _ _ H') => j [ [ _ h ] _ ].
        rewrite ev_nat; apply/eqP; exact: h.
    - have H'' := uf_ae1 HUf _ _ H' (fun j h => proj2 h).
      case: (uf_or HUf _ _ H'') => [ H1 | H2 ].
      + left; apply: oddZ_lift; apply: (uf_ae1 HUf _ _ H1) => j.
        by rewrite ev_sub mnA_ev.
      + right.
        have [ i [ _ Hi ] ] := uf_or_list HUf (l := all_i4)
          (A := fun i j => oddZ isZo ((vqo (q j) (fd_L D i (u j) (v j)))%:~R
                                       - mnA (fun t => (vqo (q j) t)%:~R) (u j) (v j)))
          (uf_ae1 HUf _ _ H2 (fun j '(ex_intro i h) => ex_intro _ i (conj (all_i4_spec i) h))).
        exists i; apply: oddZ_lift; apply: (uf_ae1 HUf _ _ Hi) => j.
        by rewrite ev_sub mnA_ev /vqu fdL_ev.
  Qed.

  Lemma vqo_natnat (p m : nat) : vqo p%:R m%:R = (logn p m)%:Z.
  Proof. by rewrite vqo_nat natr_intr vqr_int. Qed.

  Lemma f_trH2 (K : nat) s delta : isZ delta -> (delta ≢ 0)%sof ->
    (forall q, primeA q -> (0 < vq q (MKu D K s))%sof -> (K%:R <= vq q delta)%sof) ->
    exists z, isZ z /\ (delta ≡ MKu D K s ^+ K * z)%sof.
  Proof using HUf.
    move=> Hd /neq0U Hd0 Hq.
    pose M j := MK_ord D K (s j).
    pose a j := fun p : nat => (vqr p (delta j) < K%:Z)%R.
    pose bad j := has (a j) (primes (M j)).
    have Hgood : U (fun j => ~~ bad j).
    { case: (uf_total HUf (fun j => bad j)) => Hb; last by apply: (uf_ae1 HUf _ _ Hb) => j /negP.
      exfalso.
      pose qs j : nat := nth 2%N [seq p <- primes (M j) | a j p] 0.
      have Hqs : forall j, bad j -> qs j \in [seq p <- primes (M j) | a j p].
      { move=> j hb; apply: mem_nth; rewrite lt0n size_eq0 -has_filter; exact: hb. }
      pose q : F := fun j => (qs j)%:R.
      have Hpr : primeA q.
      { apply: (uf_ae1 HUf _ _ Hb) => j /Hqs; rewrite mem_filter mem_primes => /andP [ _ /and3P [ hp _ _ ] ].
        by exists (qs j). }
      have Hpos : (0 < vq q (MKu D K s))%sof.
      { apply: (uf_ae1 HUf _ _ Hb) => j /Hqs; rewrite mem_filter => /andP [ _ hm ].
        by rewrite /vqu /q /MKu vqo_natnat ltr0z ltz_nat logn_gt0. }
      have H := Hq q Hpr Hpos.
      apply: (uf_proper HUf); apply: (uf_ae2 HUf _ _ _ H Hb) => j h hb.
      move: (Hqs j hb); rewrite mem_filter => /andP [ ha _ ].
      move: h; rewrite /vqu /q ev_nat vqo_nat natr_intr ler_int => h.
      by move: ha; rewrite /a ltNge h. }
    have Hpt : forall j, ~~ bad j -> forall r : rat, primeo r -> 0 < vqo r (M j)%:R -> K%:Z <= vqo r (delta j).
    { move=> j hg r hr; have [ E Hp ] := primeo_nat hr.
      rewrite E vqo_natnat ltz_nat logn_gt0 vqo_nat => hm.
      rewrite leNgt; apply/negP => hlt; move/negP: hg; apply; apply/hasP.
      by exists (absz (numq r)). }
    have H := uf_ae3 HUf _ _ _ _ Hd (uf_ae1 HUf _ _ Hd0 (fun j h => introN eqP h)) Hgood
      (fun j hd hd0 hg => @ord_H2 D K (s j) (delta j) hd hd0 (Hpt j hg)).
    exists (fun j => delta j / (MK_ord D K (s j))%:R ^+ K); split.
    - by apply: (uf_ae1 HUf _ _ H) => j [].
    - by apply: (uf_ae1 HUf _ _ H) => j [ _ E ]; rewrite ev_mul ev_pow.
  Qed.

  Lemma f_trH3 : hei_enlarge_ord D ->
    forall (K : nat) (u v : F), (v ≢ 0)%sof -> (forall i, fd_LS D i u v ≢ 0)%sof ->
      (htu (u / v) <= (HK D K)%:R * MKu D K (u / v) ^+ fd_c D)%sof.
  Proof using HUf.
    move=> He K u v /neq0U Hv HL.
    have HL' : U (fun j => forall i, fd_L D i (u j) (v j) != 0).
    { apply: all_i4_U => i; apply: (uf_ae1 HUf _ _ (neq0U (HL i))) => j; cbv beta; rewrite fdL_ev => h; exact/eqP. }
    apply: (uf_ae2 HUf _ _ _ Hv HL') => j hv hl.
    rewrite ev_mul ev_nat ev_pow /htu /MKu ev_div; apply: ord_H3 => //; exact/eqP.
  Qed.

  Lemma f_trPP2 : FixedWF D ->
    forall b, (b ≢ 0)%sof -> Phi_holdsS (fd_PhiL D) b ->
      forall q, primeA q -> (forall p, p \in S1 D -> q ≢ p%:R)%sof ->
        (vq q b < 0)%sof -> evenZS isZ (vq q b).
  Proof using HUf.
    move=> HWF b /neq0U Hb [ w /qfE Hw ] q Hq HS Hlt.
    have HS' : U (fun j => forall p, List.In p (S1 D) -> q j <> p%:R).
    { apply: (uf_list HUf (l := S1 D) (A := fun p j => q j <> p%:R)) => p /Theory.In_mem /HS /neqU H.
      by apply: (uf_ae1 HUf _ _ H) => j; rewrite ev_nat. }
    apply: evenZ_lift.
    apply: (uf_ae3 HUf _ _ _ _ (uf_inter HUf _ _ Hb Hw) (uf_inter HUf _ _ Hq HS') Hlt) => j [ hb hw ] [ hq hs ] hlt.
    have [ E Hp ] := primeo_nat hq.
    exists (vqo (q j) (b j)); split => //.
    rewrite /vqo; apply: (PP2_thm HWF) => //.
    - exact/eqP.
    - apply/Phi_holds_rat; exists (fun i => w i j).
      apply: (qf_holds_ext _).1 hw => [] [ | i ] _ //.
    - apply/negP => /Theory.In_mem /hs; by rewrite {1}E.
    - by move: hlt; rewrite /vqu ltrz0.
  Qed.

End heights.

(** * 6. The elliptic fields (from E1, E2, O_rank, O_F1, O_F2, O_HL) *)

Lemma rat_sqr_absz (a : int) : (a%:~R : rat) ^+ 2 = ((absz a) ^ 2)%N%:R.
Proof.
  rewrite natrX; have -> : ((absz a)%:R : rat) = `|a%:~R| by rewrite -intr_norm -abszE.
  by rewrite real_normK // num_real.
Qed.

Section elliptic.

  Variable D : FixedData.
  Variable idx_ord : qe rat * qe rat -> int.
  Variables (U : (nat -> Prop) -> Prop) (HUf : ultrafilter U).
  Local Abbreviation F := (ultrapower_SOF U HUf).

  Implicit Types (x y q n s : F) (j : nat).

  Local Abbreviation isZ := (@isZu U HUf).
  Local Abbreviation primeA := (@primeu U HUf).
  Local Abbreviation vq := (@vqu U HUf).
  Local Abbreviation above := (@aboveu U HUf).
  Local Abbreviation vP := (@vPu U HUf).
  Local Abbreviation mult := (@multu D U HUf).

  Lemma zpar_lift sg (p : nat -> pt rat) j : qev (zparS sg (liftpt HUf p)) j = zpar sg (p j).
  Proof.
    rewrite /zparS qev_mul qev_of ev_nz lift1 qev_div qev_opp !qev_e lift21 lift22.
    case: (p j) => [ [ X Y ] | ] /=.
    - have E1 : FixedData.qe_of (1 : rat) = 1 by []. by rewrite E1 mul1r.
    - have E0 : FixedData.qe_of (0 : rat) = 0 by []. by rewrite E0 mul0r.
  Qed.

  Lemma red_lift (w : Plu) sg (p : nat -> pt rat) :
    redAS (vP w) sg (liftpt HUf p) -> U (fun j => red_ord sg (ovP (w j)) (p j)).
  Proof using HUf.
    case=> H; apply: (uf_ae1 HUf _ _ H) => j; cbv beta.
    - by rewrite lift1; case: (p j) => [ P | ].
    - rewrite /vPu qev_e lift21; case: (p j) => [ [ X Y ] | ] //=.
      by rewrite ltrz0.
  Qed.

  Lemma ellK_ev sg K (Z : qe F) j : qev (ellKS sg K Z) j = ellK sg K (qev Z j).
  Proof.
    elim: K => [ | K IH ].
    - by rewrite /ellK big_geq.
    - rewrite ellKS_S qev_add IH qev_mul qev_rat qev_pow /ellK [in RHS]big_nat_recr // qe_rat_id.
      move: (FixedData.qe_e sg (ct K.+1)) => c; by [].
  Qed.

  Lemma isZ_int x j : isZo (x j) -> exists a : int, x j = a%:~R /\ numq (x j) = a.
  Proof. by case=> a ->; exists a; rewrite numq_int. Qed.

  Hypothesis HWF : FixedWF D.

  Lemma f_trR1 (HE2 : forall n : int, n != 0 ->
      exists X Y, mulQ D n = Some (X, Y) /\ X != 0 /\ Y != 0 /\ on_curve (X, Y)) n :
    isZ n -> (n ≢ 0)%sof ->
    ((mult n).1 ≢ 0)%sof /\ ((mult n).2.1 ≢ 0)%sof /\ ((mult n).2.2 ≢ 0)%sof /\ on_curveS (mult n).2.
  Proof using HUf HWF.
    move=> Hn /neq0U Hn0.
    have H : U (fun j => exists X Y, mulP D (numq (n j)) = Some (X, Y) /\ X != 0 /\ Y != 0 /\ on_curve (X, Y)).
    { apply: (uf_ae2 HUf _ _ _ Hn Hn0) => j /isZ_int [ a [ Ea -> ] ] h; apply: HE2.
      apply: mulf_neq0; first by apply/eqP => E; apply: h; rewrite Ea E.
      by rewrite eqz_nat -lt0n (wf_m HWF). }
    split; [ | split; [ | split ] ].
    - apply: (proj2 (neq0E _)); apply: (uf_ae1 HUf _ _ H) => j [ X [ Y [ E _ ] ] ].
      by rewrite /multu lift1 E /= => /eqP; rewrite oner_eq0.
    - apply: (proj2 (qneqE _ _)); apply: (uf_ae1 HUf _ _ H) => j [ X [ Y [ E [ h _ ] ] ] ].
      by rewrite /multu lift21 E qev_0 /=; apply/eqP.
    - apply: (proj2 (qneqE _ _)); apply: (uf_ae1 HUf _ _ H) => j [ X [ Y [ E [ _ [ h _ ] ] ] ] ].
      by rewrite /multu lift22 E qev_0 /=; apply/eqP.
    - apply/on_curveE; apply: (uf_ae1 HUf _ _ H) => j [ X [ Y [ E [ _ [ _ h ] ] ] ] ].
      by rewrite /multu lift21 lift22 E.
  Qed.

  Lemma f_trR3 (HE1 : forall n n' : int, ADDrel (mulQ D n) (mulQ D n') (mulQ D (n + n'))) n n' :
    isZ n -> isZ n' -> ADDrelS (mult n) (mult n') (mult (n + n')%sof).
  Proof using HUf.
    move=> Hn Hn'; apply/ADDrelE; apply: (uf_ae2 HUf _ _ _ Hn Hn') => j [ a Ea ] [ b Eb ].
    rewrite /multu !ptev_lift ev_add Ea Eb -intrD !numq_int /mulP mulrDl; exact: HE1.
  Qed.

  Lemma f_trR5
    (Hrank : forall Q : nat -> qe rat * qe rat,
      on_curve (Q 1%N) ->
      (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ADDrel (Some (Q k)) (Some (Q 1%N)) (Some (Q k.+1))) ->
      exists n : int, mulP D n = Some (Q (fd_m D)))
    (Hidx : forall (n : int) X, mulP D n = Some X -> idx_ord X = n)
    (Q : nat -> qe F * qe F) :
    on_curveS (Q 1%N) ->
    (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ADDrelS ((1 : F)%sof, Q k) (1%sof, Q 1%N) (1%sof, Q k.+1)) ->
    isZ (idxu idx_ord (Q (fd_m D))) /\ pt_eqv (mult (idxu idx_ord (Q (fd_m D)))) (1%sof, Q (fd_m D)).
  Proof using HUf.
    move=> /on_curveE H1 Hch.
    pose Qj j i := (qev (Q i).1 j, qev (Q i).2 j).
    have H2 : U (fun j => forall i, List.In i (chain_idx D) ->
                ADDrel (Some (Qj j i)) (Some (Qj j 1%N)) (Some (Qj j i.+1))).
    { apply: (uf_list HUf (l := chain_idx D)) => i /chain_idx_iff [ h1 h2 ].
      have /ADDrelE H := Hch i h1 h2; apply: (uf_ae1 HUf _ _ H) => j; by rewrite !ptev_1. }
    split; first by apply: (uf_all HUf) => j; exact: ord_Z1_int.
    apply/ptE; apply: (uf_ae2 HUf _ _ _ H1 H2) => j h1 h2.
    have [ m Em ] := Hrank (Qj j) h1 (fun i a b => h2 i (proj2 (chain_idx_iff D i) (conj a b))).
    by rewrite /multu ptev_lift ptev_1 /idxu numq_int (Hidx m _ Em) Em.
  Qed.

  Lemma SE_U q (L : seq nat) : (forall p, p \in L -> q ≢ p%:R)%sof ->
    U (fun j => forall p, List.In p L -> q j <> p%:R).
  Proof using HUf.
    move=> HS; apply: (uf_list HUf (l := L) (A := fun p j => q j <> p%:R)) => p /Theory.In_mem /HS /neqU H.
    by apply: (uf_ae1 HUf _ _ H) => j; rewrite ev_nat.
  Qed.

  Lemma f_trF1
    (HF1 : forall (sg : bool) (p : nat), prime p -> p \notin fd_SE D ->
      forall v, is_place_above v p ->
      forall n n' : int, n' != 0 ->
      red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
      n = 0 \/ v (zpar sg (mulP D n)) - v (zpar sg (mulP D n')) = vqr p n%:~R - vqr p n'%:~R)
    (sg : bool) q : primeA q -> (forall p, p \in fd_SE D -> q ≢ p%:R)%sof ->
    forall w, above w q -> forall n n', isZ n -> isZ n' -> (n' ≢ 0)%sof ->
      redAS (vP w) sg (mult n) -> redAS (vP w) sg (mult n') ->
      (n ≡ 0)%sof \/ (vP w (zparS sg (mult n)) - vP w (zparS sg (mult n')) ≡ vq q n - vq q n')%sof.
  Proof using HUf.
    move=> Hq /SE_U HS w Hw n n' Hn Hn' /neq0U Hn0 /red_lift Hr /red_lift Hr'.
    have H : U (fun j => n j = 0 \/
       (vP w (zparS sg (mult n)) - vP w (zparS sg (mult n')))%sof j = (vq q n - vq q n')%sof j).
    { apply: (uf_ae3 HUf _ _ _ _ (uf_inter HUf _ _ Hw HS) (uf_inter HUf _ _ Hn Hn')
                (uf_inter HUf _ _ Hn0 (uf_inter HUf _ _ Hr Hr'))) => j [ hw hs ] [ hn hn' ] [ h0 [ hr hr' ] ].
      have [ a [ Ea Na ] ] := isZ_int hn; have [ b [ Eb Nb ] ] := isZ_int hn'.
      rewrite Na in hr; rewrite Nb in hr'.
      case: hw => Eq Hab; case: (Hab) => _ [ Hp _ ].
      have HpS : (w j).1 \notin fd_SE D.
      { apply/negP => /Theory.In_mem /hs; by rewrite Eq. }
      have Hb0 : b != 0 by apply/eqP => E; apply: h0; rewrite Eb E.
      case: (HF1 sg _ Hp HpS _ (ovP_is_place Hab) a b Hb0 hr hr') => [ E | E ]; [ left | right ].
      - by rewrite Ea E.
      - rewrite !ev_sub /vPu !zpar_lift /vqu /mult /multu Na Nb Eq !vqo_nat Ea Eb -!intrB E.
        by []. }
    case: (uf_or HUf _ _ H) => H'; [ left | right ]; exact: H'.
  Qed.

  Lemma f_trF2
    (HF2 : forall (sg : bool) (K p : nat), (1 <= K)%N -> prime p -> p \notin fd_SE D -> (K.+1 < p)%N ->
      forall v, is_place_above v p ->
      forall n n' : int, n' != 0 ->
      red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
      (n = 0 \/ vqr p n'%:~R <= vqr p n%:~R) ->
      ellK sg K (zpar sg (mulP D n')) != 0 /\
      (let x := ellK sg K (zpar sg (mulP D n)) / ellK sg K (zpar sg (mulP D n'))
                - FixedData.qe_of (n%:~R / n'%:~R) in x = 0 \/ K%:Z <= v x))
    (sg : bool) (K : nat) q : (1 <= K)%N -> primeA q -> (forall p, p \in fd_SE D -> q ≢ p%:R)%sof ->
    ((K.+1)%:R < q)%sof ->
    forall w, above w q -> forall n n', isZ n -> isZ n' -> (n' ≢ 0)%sof ->
      redAS (vP w) sg (mult n) -> redAS (vP w) sg (mult n') ->
      ((n ≡ 0)%sof \/ (vq q n' <= vq q n)%sof) ->
      (ellKS sg K (zparS sg (mult n')) ≢ 0)%sof /\
      (vgeS (vP w) (ellKS sg K (zparS sg (mult n)) / ellKS sg K (zparS sg (mult n'))
                   - qe_of (n / n')) K%:R)%sof.
  Proof using HUf.
    move=> HK Hq /SE_U HS HqK w Hw n n' Hn Hn' /neq0U Hn0 /red_lift Hr /red_lift Hr' Hcmp.
    have Hcmp' : U (fun j => n j = 0 \/ (vq q n') j <= (vq q n) j).
    { case: Hcmp => H; apply: (uf_ae1 HUf _ _ H) => j; auto. }
    pose X := (ellKS sg K (zparS sg (mult n)) / ellKS sg K (zparS sg (mult n')) - qe_of (n / n'))%sof.
    have H : U (fun j => qev (ellKS sg K (zparS sg (mult n'))) j != 0 /\
                          (qev X j = 0 \/ K%:Z <= ovP (w j) (qev X j))).
    { apply: (uf_ae3 HUf _ _ _ _ (uf_inter HUf _ _ (uf_inter HUf _ _ Hw HS) HqK) (uf_inter HUf _ _ Hn Hn')
                (uf_inter HUf _ _ (uf_inter HUf _ _ Hn0 Hcmp') (uf_inter HUf _ _ Hr Hr')))
        => j [ [ hw hs ] hk ] [ hn hn' ] [ [ h0 hc ] [ hr hr' ] ].
      have [ a [ Ea Na ] ] := isZ_int hn; have [ b [ Eb Nb ] ] := isZ_int hn'.
      rewrite Na in hr; rewrite Nb in hr'.
      case: hw => Eq Hab; case: (Hab) => _ [ Hp _ ].
      have HpS : (w j).1 \notin fd_SE D.
      { apply/negP => /Theory.In_mem /hs; by rewrite Eq. }
      have Hb0 : b != 0 by apply/eqP => E; apply: h0; rewrite Eb E.
      have HKp : (K.+1 < (w j).1)%N by move: hk; rewrite ev_nat Eq ltr_nat.
      have Hc : a = 0 \/ vqr (w j).1 b%:~R <= vqr (w j).1 a%:~R.
      { case: hc => [ E | E ]; [ left | right ].
        - by apply/eqP; rewrite -(intr_eq0 rat) -Ea E.
        - by move: E; rewrite /vqu Eq !vqo_nat Ea Eb ler_int. }
      have [ R1 R2 ] := HF2 sg K _ HK Hp HpS HKp _ (ovP_is_place Hab) a b Hb0 hr hr' Hc.
      rewrite /X qev_sub qev_div !ellK_ev /mult /multu !zpar_lift qev_of ev_div Na Nb Ea Eb.
      by split. }
    split.
    - apply: (proj2 (qneqE _ _)); apply: (uf_ae1 HUf _ _ H) => j [ h _ ]; rewrite qev_0; exact/eqP.
    - case: (uf_or HUf _ _ (uf_ae1 HUf _ _ H (fun j h => proj2 h))) => H'; [ left | right ].
      + by apply/qeqvE; apply: (uf_ae1 HUf _ _ H') => j ->.
      + apply: (uf_ae1 HUf _ _ H') => j h; by rewrite ev_nat /vPu -/X -[(K%:R : rat)]/((K%:Z)%:~R) ler_int.
  Qed.

  Lemma f_trHL
    (HHL : forall (n : int) (x0 x1 x2 : rat), n != 0 -> x2 != 0 ->
      (exists Y, mulP D n = Some (QE x0 x1 / FixedData.qe_of x2, Y)) ->
      ((absz n) ^ 2 <= fd_Nh D * (htb x0 + htb x1 + htb x2 + fd_Ch D))%N)
    n x0 x1 x2 : isZ n -> (n ≢ 0)%sof -> (x2 ≢ 0)%sof ->
      (exists y : qe F, pt_eqv (mult n) ((1 : F)%sof, ((QE x0 x1 / qe_of x2)%sof, y))) ->
      (n ^+ 2 <= (fd_Nh D)%:R * (htu x0 + htu x1 + htu x2 + (fd_Ch D)%:R))%sof.
  Proof using HUf.
    move=> Hn /neq0U Hn0 /neq0U Hx2 [ y /ptE Hy ].
    apply: (uf_ae3 HUf _ _ _ _ (uf_inter HUf _ _ Hn Hn0) Hx2 Hy) => j [ hn h0 ] h2 hy.
    have [ a [ Ea Na ] ] := isZ_int hn.
    move: hy; rewrite /multu ptev_lift ptev_1 Na qev_div qev_QE qev_of /= => hy.
    have Ha : a != 0 by apply/eqP => E; apply: h0; rewrite Ea E.
    have := HHL a (x0 j) (x1 j) (x2 j) Ha (introN eqP h2) (ex_intro _ _ hy).
    rewrite -(ler_nat rat) => Hle.
    rewrite /upw_mul /upw_add /upw_one !ev_nat /htu Ea mulr1 -expr2 rat_sqr_absz.
    by move: Hle; rewrite natrM !natrD.
  Qed.

End elliptic.

(** * 7. The ultrapower ambient structure *)

Section ambient.

  Variable D : FixedData.
  Hypothesis HWF : FixedWF D.

  (* the ordinary hypotheses (trust boundary of this file), with the exact
     types of the fields of StdHyps / OrdHyps (FixedData.v) *)
  Hypothesis HE1 : forall n n' : int, ADDrel (mulQ D n) (mulQ D n') (mulQ D (n + n')).
  Hypothesis HE2 : forall n : int, n != 0 ->
    exists X Y, mulQ D n = Some (X, Y) /\ X != 0 /\ Y != 0 /\ on_curve (X, Y).
  Hypothesis Hrank : forall Q : nat -> qe rat * qe rat,
    on_curve (Q 1%N) ->
    (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ADDrel (Some (Q k)) (Some (Q 1%N)) (Some (Q k.+1))) ->
    exists n : int, mulP D n = Some (Q (fd_m D)).
  Hypothesis HF1 : forall (sg : bool) (p : nat), prime p -> p \notin fd_SE D ->
    forall v, is_place_above v p ->
    forall n n' : int, n' != 0 ->
    red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
    n = 0 \/ v (zpar sg (mulP D n)) - v (zpar sg (mulP D n')) = vqr p n%:~R - vqr p n'%:~R.
  Hypothesis HF2 : forall (sg : bool) (K p : nat), (1 <= K)%N -> prime p -> p \notin fd_SE D -> (K.+1 < p)%N ->
    forall v, is_place_above v p ->
    forall n n' : int, n' != 0 ->
    red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
    (n = 0 \/ vqr p n'%:~R <= vqr p n%:~R) ->
    ellK sg K (zpar sg (mulP D n')) != 0 /\
    (let x := ellK sg K (zpar sg (mulP D n)) / ellK sg K (zpar sg (mulP D n'))
              - FixedData.qe_of (n%:~R / n'%:~R) in x = 0 \/ K%:Z <= v x).
  Hypothesis Hheight : forall s : rat, (forall i, s != fd_C D i) ->
    (htb s <= fd_Hb D * (MS D (fd_S D) s) ^ fd_c D)%N.
  Hypothesis HHL : forall (n : int) (x0 x1 x2 : rat), n != 0 -> x2 != 0 ->
    (exists Y, mulP D n = Some (QE x0 x1 / FixedData.qe_of x2, Y)) ->
    ((absz n) ^ 2 <= fd_Nh D * (htb x0 + htb x1 + htb x2 + fd_Ch D))%N.
  Variable idx_ord : qe rat * qe rat -> int.
  Hypothesis Hidx : forall (n : int) X, mulP D n = Some X -> idx_ord X = n.

  Variables (U : (nat -> Prop) -> Prop) (HUf : ultrafilter U).
  Local Abbreviation F := (ultrapower_SOF U HUf).

  Definition upwAmbient : AmbientS D := {|
    sQ := F;
    isZ := @isZu U HUf;
    primeA := @primeu U HUf;
    vq := @vqu U HUf;
    Pl := Plu;
    above := @aboveu U HUf;
    vP := @vPu U HUf;
    mult := @multu D U HUf;
    idx := @idxu idx_ord U HUf;
    MK := @MKu D U HUf;
    ht := @htu U HUf;
    isZ_wd := @isZu_wd U HUf;
    primeA_wd := @primeu_wd U HUf;
    vq_wd := @vqu_wd U HUf;
    above_wd := @aboveu_wd U HUf;
    vP_wd := @vPu_wd U HUf;
    mult_wd := @multu_wd D U HUf;
    idx_wd := @idxu_wd idx_ord U HUf;
    MK_wd := @MKu_wd D U HUf;
    ht_wd := @htu_wd U HUf;
    trZ0 := @f_trZ0 U HUf;
    trZ1_int := @f_trZ1_int U HUf;
    trZ1_add := @f_trZ1_add U HUf;
    trZ1_opp := @f_trZ1_opp U HUf;
    trZ1_mul := @f_trZ1_mul U HUf;
    trV0 := @f_trV0 U HUf;
    trZ2 := @f_trZ2 U HUf;
    trPR := @f_trPR U HUf;
    trV1 := @f_trV1 U HUf;
    trV2_int := @f_trV2_int U HUf;
    trV2_mul := @f_trV2_mul U HUf;
    trV2_ultra := @f_trV2_ultra U HUf;
    trV3 := @f_trV3 U HUf;
    trV4 := @f_trV4 U HUf;
    trV5 := @f_trV5 U HUf;
    trPL0 := @f_trPL0 U HUf;
    trPL1 := @f_trPL1 U HUf;
    trPL2_int := @f_trPL2_int U HUf;
    trPL2_mul := @f_trPL2_mul U HUf;
    trPL2_ultra := @f_trPL2_ultra U HUf;
    trPL3 := @f_trPL3 U HUf;
    trR1 := @f_trR1 D U HUf HWF HE2;
    trR2 := @f_trR2 D U HUf;
    trR3 := @f_trR3 D U HUf HE1;
    trR5 := @f_trR5 D idx_ord U HUf Hrank Hidx;
    trF1 := @f_trF1 D U HUf HF1;
    trF2 := @f_trF2 D U HUf HF2;
    trH1 := @f_trH1 D U HUf;
    trH2 := @f_trH2 D U HUf;
    trH3 := @f_trH3 D U HUf (hei_enlarge_thm HWF Hheight);
    trHT0 := @f_trHT0 U HUf;
    trHS := @f_trHS U HUf;
    trHL := @f_trHL D U HUf HHL;
    trSIG := @f_trSIG U HUf;
    trPP2 := @f_trPP2 D U HUf HWF
  |}.

End ambient.

(** * 8. The term model, from the tests, by search (no choice) *)

Fixpoint qf_holdsb {V : Set} (φ : V -> rat) (A : qform V) : bool :=
  match A with
  | qf_eq0 p => qp_eval φ p == 0
  | qf_neq0 p => qp_eval φ p != 0
  | qf_and A B => qf_holdsb φ A && qf_holdsb φ B
  | qf_or A B => qf_holdsb φ A || qf_holdsb φ B
  end.

Lemma qf_holdsbP {V : Set} (φ : V -> rat) A : qf_holdsb φ A = true <-> qf_holds φ A.
Proof.
  elim: A => [ p | p | A HA B HB | A HA B HB ] /=.
  - by split => [ /eqP | -> ].
  - by split => [ /eqP | /eqP ].
  - by rewrite -HA -HB; split => [ /andP | [ -> -> ] ].
  - rewrite -HA -HB; split => [ /orP | [ -> | -> ] ] //; by rewrite orbT.
Qed.

Section search.

  Variables (D : FixedData) (f : H10Z_PROBLEM).
  Hypothesis Htests : forall N, qf_sat (projT2 (test D f N)).

  Definition tst (N k : nat) : bool :=
    match rat_vec_enum (projT1 (test D f N)) k with
    | Some v => qf_holdsb (vec_pos v) (projT2 (test D f N))
    | None => false
    end.

  Lemma tst_ex N : exists k, tst N k = true.
  Proof using Htests.
    have [ φ Hφ ] := Htests N.
    have [ k [ v [ Hk Hv ] ] ] := rat_pos_fun_enum φ.
    exists k; rewrite /tst Hk; apply/qf_holdsbP.
    by apply: (qf_holds_ext _).2 Hφ => p _.
  Qed.

  Definition kN (N : nat) : nat :=
    proj1_sig (constructive_indefinite_ground_description_nat (fun k => tst N k = true)
                 (fun k => Bool.bool_dec (tst N k) true) (tst_ex N)).

  Lemma kN_spec N : tst N (kN N) = true.
  Proof using.
    rewrite /kN; exact: (proj2_sig (constructive_indefinite_ground_description_nat (fun k => tst N k = true)
                 (fun k => Bool.bool_dec (tst N k) true) (tst_ex N))).
  Qed.

  Definition asg (N : nat) : pos (projT1 (test D f N)) -> rat :=
    match rat_vec_enum (projT1 (test D f N)) (kN N) with
    | Some v => vec_pos v
    | None => fun _ => 0
    end.

  Lemma asg_spec N : qf_holds (@asg N) (projT2 (test D f N)).
  Proof.
    have := kN_spec N; rewrite /tst /asg.
    case: (rat_vec_enum _ (kN N)) => [ v | ] // /qf_holdsbP; exact.
  Qed.

  (* the N-th assignment of the variables of testf N *)
  Definition phiN (N : nat) : nat -> rat :=
    fun v => @asg N (trv (vmax (qf_vars (testf D f N))) v).

  Lemma phiN_spec N : qf_holds (phiN N) (testf D f N).
  Proof. exact: (proj1 (qf_holds_map _ _ _) (asg_spec N)). Qed.

End search.

Section term_model.

  Variables (D : FixedData) (f : H10Z_PROBLEM).
  Hypothesis Htests : forall N, qf_sat (projT2 (test D f N)).
  Variables (U : (nat -> Prop) -> Prop) (HUf : ultrafilter U) (HNP : nonprincipal U).
  Local Abbreviation F := (ultrapower_SOF U HUf).

  Definition tval (t : gterm) : F := fun N => rho_of (tlist D f N) (phiN Htests N) t.

  Lemma tl_cof t : exists k, forall N, le k N -> List.In t (tlist D f N).
  Proof.
    have [ k Hk ] := gterm_list_spec t; exists k => N HN.
    apply: tlist_gterm; exact: gterm_list_mono HN Hk.
  Qed.

  Lemma tm_ringU t : ring_okS tval t.
  Proof using HUf HNP.
    have [ k Hk ] := tl_cof t.
    have H : U (fun N => ring_ok (fun u => tval u N) t).
    { apply: (uf_ae1 HUf _ _ (uf_cofinite HUf HNP k)) => N hN.
      have [ Ha _ ] := testf_read (phiN_spec Htests N); exact: Ha (Hk N hN). }
    case: t H {Hk} => [ x | g | g s | g s s' ] H; first by case: x.
    - case: g H => [ | | z | i ] H //=; apply: (uf_ae1 HUf _ _ H) => N h //.
      cbv beta; rewrite ev_Z -Z_to_R_rat; exact: h.
    - case: g H => [ | c | k' c | K' c ] H //=; apply: (uf_ae1 HUf _ _ H) => N h //.
    - case: g H => [ | | K' c ] H //=; apply: (uf_ae1 HUf _ _ H) => N h //.
  Qed.

  Lemma tm_funU t t' : fun_okS tval t t'.
  Proof using HUf HNP.
    have [ k1 H1 ] := tl_cof t; have [ k2 H2 ] := tl_cof t'.
    have H : U (fun N => fun_ok (fun u => tval u N) t t').
    { apply: (uf_ae1 HUf _ _ (uf_cofinite HUf HNP (Nat.max k1 k2))) => N hN.
      have [ _ [ Hb _ ] ] := testf_read (phiN_spec Htests N).
      apply: Hb; [ apply: H1 | apply: H2 ]; lia. }
    case: t t' H {H1 H2} => [ x | g | g s | g s s' ] [ x' | g' | g' u | g' u u' ] H //=.
    - move=> Hg Hs; apply: (uf_ae2 HUf _ _ _ H Hs) => N h hs; exact: h Hg hs.
    - move=> Hg Hs1 Hs2; apply: (uf_ae3 HUf _ _ _ _ H Hs1 Hs2) => N h h1 h2; exact: h Hg h1 h2.
  Qed.

  Lemma tm_instU phi : Inst D f phi -> fml_holdsS tval phi.
  Proof using HUf HNP.
    move=> /inst_list_spec [ N0 HN0 ]; apply/fmlE.
    apply: (uf_ae1 HUf _ _ (uf_cofinite HUf HNP N0)) => N hN.
    have [ _ [ _ [ Hc _ ] ] ] := testf_read (phiN_spec Htests N).
    apply: Hc; exact: inst_list_mono hN HN0.
  Qed.

  Lemma tm_phiU t : Phi_holdsS (fd_PhiL D) (tval t).
  Proof using HUf HNP.
    have [ k Hk ] := tl_cof t.
    exists (fun i => (fun N => phiN Htests N (phi_ren (ix (tlist D f N) t) i)) : F).
    apply/qfE; apply: (uf_ae1 HUf _ _ (uf_cofinite HUf HNP k)) => N hN.
    have Hq : qf_holds (phiN Htests N) (phi_q D (tlist D f N) t).
    { move: (phiN_spec Htests N); rewrite /testf; cbv zeta; rewrite qf_all_spec; apply.
      do 3 (apply List.in_or_app; right); apply: List.in_map; exact: Hk. }
    move/phi_q_iff: Hq => Hq.
    by apply: (qf_holds_ext _).1 Hq => [] [ | i ] _.
  Qed.


End term_model.

(** * 9. Compactness *)

Section compactness.

  Variable D : FixedData.
  Hypothesis HWF : FixedWF D.
  Hypothesis HE1 : forall n n' : int, ADDrel (mulQ D n) (mulQ D n') (mulQ D (n + n')).
  Hypothesis HE2 : forall n : int, n != 0 ->
    exists X Y, mulQ D n = Some (X, Y) /\ X != 0 /\ Y != 0 /\ on_curve (X, Y).
  Hypothesis Hrank : forall Q : nat -> qe rat * qe rat,
    on_curve (Q 1%N) ->
    (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ADDrel (Some (Q k)) (Some (Q 1%N)) (Some (Q k.+1))) ->
    exists n : int, mulP D n = Some (Q (fd_m D)).
  Hypothesis HF1 : forall (sg : bool) (p : nat), prime p -> p \notin fd_SE D ->
    forall v, is_place_above v p ->
    forall n n' : int, n' != 0 ->
    red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
    n = 0 \/ v (zpar sg (mulP D n)) - v (zpar sg (mulP D n')) = vqr p n%:~R - vqr p n'%:~R.
  Hypothesis HF2 : forall (sg : bool) (K p : nat), (1 <= K)%N -> prime p -> p \notin fd_SE D -> (K.+1 < p)%N ->
    forall v, is_place_above v p ->
    forall n n' : int, n' != 0 ->
    red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
    (n = 0 \/ vqr p n'%:~R <= vqr p n%:~R) ->
    ellK sg K (zpar sg (mulP D n')) != 0 /\
    (let x := ellK sg K (zpar sg (mulP D n)) / ellK sg K (zpar sg (mulP D n'))
              - FixedData.qe_of (n%:~R / n'%:~R) in x = 0 \/ K%:Z <= v x).
  Hypothesis Hheight : forall s : rat, (forall i, s != fd_C D i) ->
    (htb s <= fd_Hb D * (MS D (fd_S D) s) ^ fd_c D)%N.
  Hypothesis HHL : forall (n : int) (x0 x1 x2 : rat), n != 0 -> x2 != 0 ->
    (exists Y, mulP D n = Some (QE x0 x1 / FixedData.qe_of x2, Y)) ->
    ((absz n) ^ 2 <= fd_Nh D * (htb x0 + htb x1 + htb x2 + fd_Ch D))%N.
  Variable idx_ord : qe rat * qe rat -> int.
  Hypothesis Hidx : forall (n : int) X, mulP D n = Some X -> idx_ord X = n.

  (** the term model, for a fixed nonprincipal ultrafilter *)
  Lemma CompactnessT_upw (U : (nat -> Prop) -> Prop) (HUf : ultrafilter U) (HNP : nonprincipal U)
    (f : H10Z_PROBLEM) (Htests : forall N, qf_sat (projT2 (test D f N))) :
    TermModelS (@upwAmbient D HWF HE1 HE2 Hrank HF1 HF2 Hheight HHL idx_ord Hidx U HUf)
               (Inst D f) (tval Htests HUf).
  Proof.
    split.
    - exact: tm_ringU HNP.
    - exact: tm_funU HNP.
    - exact: tm_instU HNP.
    - exact: tm_phiU HNP.
  Qed.

  (** the only use of the axiom [ultrafilter_exists] (in a Prop goal) *)
  Theorem CompactnessT_fine : CompactnessT D.
  Proof using HWF HE1 HE2 Hrank HF1 HF2 Hheight HHL idx_ord Hidx.
    move=> f Htests.
    case: ultrafilter_exists => U [ HUf HNP ].
    eexists; eexists; exact: (@CompactnessT_upw U HUf HNP f Htests).
  Qed.

End compactness.

(** The form with the records of FixedData.v: the ordinary hypotheses
    used are E1, E2 (fields of [StdHyps]) and O_rank, O_F1, O_F2,
    O_height, O_HL (fields of [OrdHyps]; O_HS and O_PP2 are proved,
    OrdHeights.O_HS_thm and PoleParity.PP2_thm, and not used here), plus a
    total ordinary index function [idx_ord] inverting n |-> nP. *)
Theorem CompactnessT_thm (D : FixedData) : FixedWF D ->
  (forall n n' : int, ADDrel (mulQ D n) (mulQ D n') (mulQ D (n + n'))) ->
  (forall n : int, n != 0 ->
     exists X Y, mulQ D n = Some (X, Y) /\ X != 0 /\ Y != 0 /\ on_curve (X, Y)) ->
  OrdHyps D ->
  forall idx_ord : qe rat * qe rat -> int,
    (forall (n : int) X, mulP D n = Some X -> idx_ord X = n) ->
  CompactnessT D.
Proof.
  move=> HWF HE1 HE2 HO idx_ord Hidx.
  exact: (CompactnessT_fine HWF HE1 HE2 (O_rank HO) (O_F1 HO) (O_F2 HO) (O_height HO) (O_HL HO) Hidx).
Qed.

Corollary CompactnessT_StdHyps (D : FixedData) : FixedWF D -> StdHyps D -> OrdHyps D ->
  forall idx_ord : qe rat * qe rat -> int,
    (forall (n : int) X, mulP D n = Some X -> idx_ord X = n) ->
  CompactnessT D.
Proof. move=> HWF HS; exact: (CompactnessT_thm HWF (E1 HS) (E2 HS)). Qed.
