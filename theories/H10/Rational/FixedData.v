(**************************************************************)
(*   Part of the formalization of the preprint                *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026), contributed to the Rocq library of undecidable   *)
(*   problems.                                                *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Tier 2 interface: the fixed data of Section 2 of the paper and the
   ordinary (Tier 3) hypotheses on them. See DESIGN.md, Sections 1 and 2.

   TRUST BOUNDARY. Nothing in this file is proved about the arithmetic;
   the records list what the paper's Sections 3 to 6 and compactness
   provide. Concretely:
   - [FixedData] collects the fixed objects. Some are explicit in the
     paper ([explicit]), the others exist only via a theorem of the paper
     ([thm]); the latter are fields, so that every statement is
     parametric in them.
   - [FixedWF] lists the side conditions that these theorems assert
     about the fixed objects (positivity, distinctness, nonemptiness).
   - [StdHyps] lists the ordinary hypotheses consumed by the standard
     model (Lemma red:standard-model, test soundness): E1, E2, HCov, PP1.
   - [OrdHyps] lists the ordinary versions of the facts that the ambient
     structure (AmbientS.v) transfers. They are consumed by the ultrapower
     construction (CompactnessT.v) and are all PROVED for the explicit
     data (Generator.inputs_to_data_final).

   Everything is a Record field or a Definition. There are no Axioms.

   Proved here (small lemmas): the ring structure on Q(sqrt2)-style
   pairs [qe R], sanity values of the formal logarithm coefficients [ct],
   and [Phi_holds_iff] relating the formula Phi (a [qform] with fixed
   rational coefficients) to the paper's condition (03-parity.tex,
   par:auxiliary-functions). *)

From Stdlib Require Import Arith ZArith Lia List.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature.

From HB Require Import structures.
From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** * 1. The quadratic extension  R(sqrt 2)  as pairs (DESIGN, Conventions)

    [QE a b] means  a + b sqrt2. We use [F := qe rat] for  F = Q(sqrt2)
    and, in the ambient structure, [qe sQ] for  *F. *)

Record qe (R : Type) : Type := QE { qre : R ; qim : R }.
Arguments QE {R}.

Definition qe_pair {R} (x : qe R) := (qre x, qim x).
Definition pair_qe {R} (p : R * R) := QE p.1 p.2.
Lemma qe_pairK R : cancel (@qe_pair R) (@pair_qe R). Proof. by case. Qed.
HB.instance Definition _ (R : choiceType) :=
  Choice.copy (qe R) (can_type (@qe_pairK R)).

Lemma qeE R (x : qe R) : x = QE (qre x) (qim x). Proof. by case: x. Qed.

Lemma QE_inj R (a b c d : R) : QE a b = QE c d -> a = c /\ b = d.
Proof. by case=> -> ->. Qed.

Section qe_ring.

  Variable R : comNzRingType.
  Implicit Types x y z : qe R.

  Definition qe0 : qe R := QE 0 0.
  Definition qe1 : qe R := QE 1 0.
  Definition qe_opp x := QE (- qre x) (- qim x).
  Definition qe_add x y := QE (qre x + qre y) (qim x + qim y).
  Definition qe_mul x y :=
    QE (qre x * qre y + 2%:R * (qim x * qim y)) (qre x * qim y + qim x * qre y).

  Fact qe_addA : associative qe_add.
  Proof. by move=> [a b] [c d] [e f]; rewrite /qe_add /=; congr QE; ring. Qed.
  Fact qe_addC : commutative qe_add.
  Proof. by move=> [a b] [c d]; rewrite /qe_add /=; congr QE; ring. Qed.
  Fact qe_add0 : left_id qe0 qe_add.
  Proof. by move=> [a b]; rewrite /qe_add /=; congr QE; ring. Qed.
  Fact qe_addN : left_inverse qe0 qe_opp qe_add.
  Proof. by move=> [a b]; rewrite /qe_add /=; congr QE; ring. Qed.

  HB.instance Definition _ :=
    GRing.isZmodule.Build (qe R) qe_addA qe_addC qe_add0 qe_addN.

  Fact qe_mulA : associative qe_mul.
  Proof. by move=> [a b] [c d] [e f]; rewrite /qe_mul /=; congr QE; ring. Qed.
  Fact qe_mulC : commutative qe_mul.
  Proof. by move=> [a b] [c d]; rewrite /qe_mul /=; congr QE; ring. Qed.
  Fact qe_mul1 : left_id qe1 qe_mul.
  Proof. by move=> [a b]; rewrite /qe_mul /=; congr QE; ring. Qed.
  Fact qe_mulDl : left_distributive qe_mul qe_add.
  Proof. by move=> [a b] [c d] [e f]; rewrite /qe_mul /qe_add /=; congr QE; ring. Qed.
  Fact qe_one_neq0 : qe1 != qe0.
  Proof. apply/eqP => [[]] /eqP; by rewrite oner_eq0. Qed.

  HB.instance Definition _ :=
    GRing.Zmodule_isComNzRing.Build (qe R) qe_mulA qe_mulC qe_mul1 qe_mulDl qe_one_neq0.

  Lemma qe0E : 0 = QE 0 0 :> qe R. Proof. by []. Qed.
  Lemma qe1E : 1 = QE 1 0 :> qe R. Proof. by []. Qed.
  Lemma qe_addE a b c d : QE a b + QE c d = QE (a + c) (b + d) :> qe R.
  Proof. by []. Qed.
  Lemma qe_oppE a b : - QE a b = QE (- a) (- b) :> qe R. Proof. by []. Qed.
  Lemma qe_subE a b c d : QE a b - QE c d = QE (a - c) (b - d) :> qe R.
  Proof. by []. Qed.
  Lemma qe_mulE a b c d :
    QE a b * QE c d = QE (a * c + 2%:R * (b * d)) (a * d + b * c) :> qe R.
  Proof. by []. Qed.

  Lemma qe_natE n : n%:R = QE n%:R 0 :> qe R.
  Proof.
    elim: n => [ | n IHn ]; first by [].
    by rewrite -addn1 !natrD IHn qe_addE addr0.
  Qed.

  Lemma qe_intE (z : int) : z%:~R = QE z%:~R 0 :> qe R.
  Proof.
    case: z => n; first exact: qe_natE.
    by rewrite /intmul qe_natE qe_oppE oppr0.
  Qed.

  (* the embedding  R -> R(sqrt2) *)
  Definition qe_of (a : R) : qe R := QE a 0.

  Lemma qe_of_add a b : qe_of (a + b) = qe_of a + qe_of b.
  Proof. by rewrite /qe_of qe_addE addr0. Qed.
  Lemma qe_of_mul a b : qe_of (a * b) = qe_of a * qe_of b.
  Proof. by rewrite /qe_of qe_mulE !mul0r !mulr0 !addr0. Qed.
  Lemma qe_of_opp a : qe_of (- a) = - qe_of a.
  Proof. by rewrite /qe_of qe_oppE oppr0. Qed.

  Definition qe_sqrt2 : qe R := QE 0 1.

  Lemma qe_sqrt2_sqr : qe_sqrt2 * qe_sqrt2 = 2%:R.
  Proof. by rewrite qe_natE /qe_sqrt2 qe_mulE; congr QE; ring. Qed.

  (* the nontrivial automorphism sigma of F/Q *)
  Definition qe_conj x := QE (qre x) (- qim x).

  (* the norm  N(a + b sqrt2) = a^2 - 2 b^2 *)
  Definition qe_norm x : R := qre x ^+ 2 - 2%:R * qim x ^+ 2.

  Lemma qe_conj_add x y : qe_conj (x + y) = qe_conj x + qe_conj y.
  Proof. by move: x y => [a b] [c d]; rewrite /qe_conj !qe_addE /=; congr QE; ring. Qed.
  Lemma qe_conj_mul x y : qe_conj (x * y) = qe_conj x * qe_conj y.
  Proof. by move: x y => [a b] [c d]; rewrite /qe_conj !qe_mulE /=; congr QE; ring. Qed.
  Lemma qe_conj_opp x : qe_conj (- x) = - qe_conj x.
  Proof. by case: x => *; rewrite /qe_conj !qe_oppE. Qed.
  Lemma qe_conj1 : qe_conj 1 = 1.
  Proof. by rewrite /qe_conj /= oppr0. Qed.
  Lemma qe_conjK x : qe_conj (qe_conj x) = x.
  Proof. by case: x => *; rewrite /qe_conj /= opprK. Qed.
  Lemma qe_mul_conj x : x * qe_conj x = qe_of (qe_norm x).
  Proof. by case: x => a b; rewrite /qe_conj /qe_norm /qe_of qe_mulE /=; congr QE; ring. Qed.
  Lemma qe_norm_mul x y : qe_norm (x * y) = qe_norm x * qe_norm y.
  Proof. by move: x y => [a b] [c d]; rewrite /qe_norm qe_mulE /=; ring. Qed.
  Lemma qe_norm1 : qe_norm 1 = 1.
  Proof. by rewrite /qe_norm /=; ring. Qed.

  (* conjugation selected by a boolean: false = identity (curve E),
     true = sigma (curve E^sigma) *)
  Definition qe_e (sg : bool) x := if sg then qe_conj x else x.

  Lemma qe_e_add sg x y : qe_e sg (x + y) = qe_e sg x + qe_e sg y.
  Proof. by case: sg => //=; rewrite qe_conj_add. Qed.
  Lemma qe_e_mul sg x y : qe_e sg (x * y) = qe_e sg x * qe_e sg y.
  Proof. by case: sg => //=; rewrite qe_conj_mul. Qed.

End qe_ring.

Arguments qe_sqrt2 {R}.

(** Over a field, [qe R] is a commutative unit ring: the units are the
    elements of nonzero norm. (It is a field iff 2 is not a square in R;
    this is the ambient field Z0.) *)

Section qe_unit.

  Variable R : fieldType.
  Implicit Types x y : qe R.

  Definition qe_unit : pred (qe R) := fun x => qe_norm x != 0.
  Definition qe_inv x : qe R :=
    if qe_norm x != 0 then QE (qre x / qe_norm x) (- qim x / qe_norm x) else x.

  Fact qe_mulVx : {in qe_unit, left_inverse 1 qe_inv *%R}.
  Proof.
    move=> [a b]; rewrite /in_mem /= /qe_unit /qe_inv /qe_norm /= => H; rewrite H.
    rewrite qe_mulE qe1E; congr QE; field; exact/eqP.
  Qed.

  Fact qe_unitPl x y : y * x = 1 -> qe_unit x.
  Proof.
    move=> /(congr1 (@qe_norm _)); rewrite qe_norm_mul qe_norm1 => H.
    rewrite /qe_unit; apply/eqP => H0; move: H; rewrite H0 mulr0 => /eqP.
    by rewrite eq_sym oner_eq0.
  Qed.

  Fact qe_invr_out : {in [predC qe_unit], qe_inv =1 id}.
  Proof.
    move=> x; rewrite inE /qe_inv => /negbTE H.
    by move: H; rewrite /in_mem /= /qe_unit => ->.
  Qed.

  HB.instance Definition _ :=
    GRing.ComNzRing_hasMulInverse.Build (qe R) qe_mulVx qe_unitPl qe_invr_out.

  Lemma qe_unitE x : (x \is a GRing.unit) = (qe_norm x != 0).
  Proof. by []. Qed.

  Lemma qe_invE x : x^-1 = qe_inv x.
  Proof. by []. Qed.

End qe_unit.

(** Mapping coefficients: [qe_rat] embeds  F = Q(sqrt2)  into  R(sqrt2)
    for any numeric field R (used with R = sQ, the ambient *Q) *)

Definition qe_map {R S : Type} (f : R -> S) (x : qe R) : qe S :=
  QE (f (qre x)) (f (qim x)).

Definition qe_rat {R : numFieldType} (x : qe rat) : qe R := qe_map (@ratr R) x.

Lemma ratr_id (x : rat) : ratr x = x.
Proof. exact: divq_num_den. Qed.

Lemma qe_rat_id (x : qe rat) : qe_rat x = x.
Proof. by case: x => a b; rewrite /qe_rat /qe_map /= !ratr_id. Qed.

Section qe_rat_morph.

  Variable R : numFieldType.
  Implicit Types x y : qe rat.

  Lemma qe_rat_add x y : qe_rat (x + y) = qe_rat x + qe_rat y :> qe R.
  Proof. by case: x; case: y => *; rewrite /qe_rat /qe_map /= !rmorphD. Qed.
  Lemma qe_rat_opp x : qe_rat (- x) = - qe_rat x :> qe R.
  Proof. by case: x => *; rewrite /qe_rat /qe_map /= !rmorphN. Qed.
  Lemma qe_rat_mul x y : qe_rat (x * y) = qe_rat x * qe_rat y :> qe R.
  Proof.
    case: x; case: y => *; rewrite /qe_rat /qe_map /= !qe_mulE /=.
    by rewrite !rmorphD !rmorphM /= ratr_nat.
  Qed.
  Lemma qe_rat1 : qe_rat 1 = 1 :> qe R.
  Proof. by rewrite /qe_rat /qe_map /= rmorph1 rmorph0. Qed.
  Lemma qe_rat0 : qe_rat 0 = 0 :> qe R.
  Proof. by rewrite /qe_rat /qe_map /= rmorph0. Qed.
  Lemma qe_rat_conj x : qe_rat (qe_conj x) = qe_conj (qe_rat x) :> qe R.
  Proof. by case: x => *; rewrite /qe_rat /qe_map /qe_conj /= rmorphN. Qed.
  Lemma qe_rat_e sg x : qe_rat (qe_e sg x) = qe_e sg (qe_rat x) :> qe R.
  Proof. by case: sg => //=; apply qe_rat_conj. Qed.

End qe_rat_morph.

(** * 2. The curve  E : y^2 = x^3 + aE x  over R(sqrt2)  (DESIGN 1.3)

    [ell:data]: d = 75 - 53 sqrt2 and E : y^2 = x^3 - d^2 x, so
    aE = - d^2 = -11243 + 7950 sqrt2. [explicit] *)

Definition dF : qe rat := QE 75%:R (- 53%:R).

(* aE, as a constant of any commutative ring *)
Definition aE {R : comNzRingType} : qe R := QE (- 11243%:R) 7950%:R.

Lemma aE_spec : aE = - (dF * dF).
Proof. by apply/eqP; vm_compute. Qed.

(* the norm of d is 7 *)
Lemma dF_norm : qe_norm dF = 7%:R.
Proof. by apply/eqP; vm_compute. Qed.

(* points: None is the point at infinity O *)
Definition pt (R : Type) := option (qe R * qe R).

Section curve.

  Variable R : comNzRingType.
  Implicit Types (x y : qe R) (p : pt R).

  Definition on_curve (P : qe R * qe R) : Prop :=
    P.2 * P.2 = P.1 ^+ 3 + aE * P.1.

  (* the addition relation  p1 + p2 = p3  on E (DESIGN 1.3), all
     denominators cleared; used both by the theory T (ax_add, ax_chain)
     and by the ambient fields R3, R5 *)
  Definition ADDrel (p1 p2 p3 : pt R) : Prop :=
    match p1, p2 with
    | None, _ => p3 = p2
    | _, None => p3 = p1
    | Some (x1, y1), Some (x2, y2) =>
           (x1 = x2 /\ y1 = - y2 /\ p3 = None)
        \/ exists x3 y3, p3 = Some (x3, y3) /\
           (   (x1 <> x2
                /\ (x3 + x1 + x2) * (x2 - x1) ^+ 2 = (y2 - y1) ^+ 2
                /\ (y3 + y1) * (x2 - x1) = (y2 - y1) * (x1 - x3))
            \/ (x1 = x2 /\ y1 = y2 /\ y1 <> 0
                /\ (x3 + 2%:R * x1) * (2%:R * y1) ^+ 2 = (3%:R * x1 ^+ 2 + aE) ^+ 2
                /\ (y3 + y1) * (2%:R * y1) = (3%:R * x1 ^+ 2 + aE) * (x1 - x3)))
    end.

  Definition pt_neg (p : pt R) : pt R :=
    match p with None => None | Some (x, y) => Some (x, - y) end.

  (* the conjugate point on E^sigma *)
  Definition pt_conj (p : pt R) : pt R :=
    match p with None => None | Some (x, y) => Some (qe_conj x, qe_conj y) end.

End curve.

(* the chord-tangent law, computed (over a field R, in R(sqrt2)) *)
Definition ec_add {R : fieldType} (p1 p2 : pt R) : pt R :=
  match p1, p2 with
  | None, _ => p2
  | _, None => p1
  | Some (x1, y1), Some (x2, y2) =>
      if x1 == x2 then
        if y1 == - y2 then None
        else let l := (3%:R * x1 ^+ 2 + aE) / (2%:R * y1) in
             let x3 := l ^+ 2 - 2%:R * x1 in
             Some (x3, l * (x1 - x3) - y1)
      else let l := (y2 - y1) / (x2 - x1) in
           let x3 := l ^+ 2 - x1 - x2 in
           Some (x3, l * (x1 - x3) - y1)
  end.

(* the formal parameter  z = -x/y  with z(O) = 0, on E (sg = false)
   or on E^sigma (sg = true, applied to the conjugate point) *)
Definition zpar {R : fieldType} (sg : bool) (p : pt R) : qe R :=
  match p with
  | None => 0
  | Some (x, y) => - qe_e sg x / qe_e sg y
  end.

Definition pt_rat {R : numFieldType} (p : pt rat) : pt R :=
  match p with None => None | Some (x, y) => Some (qe_rat x, qe_rat y) end.

(** * 3. The formal logarithm coefficients  c_t  (DESIGN 1.1, Risk 22)

    [ct] is part of the trust boundary: Prop ell:formal (F2) is a
    statement about these coefficients. Following the review, they are
    DEFINED by the paper's recipe (05-elliptic.tex, "effective
    computation"), not by the closed form:
    - z = -x/y, w = -1/y; then w = z^3 + aE z w^2. Write w = z^3 g, so
      g = 1 + aE z^4 g^2, solved by the iteration
      g_{k+1} = 1 + aE z^4 g_k^2  (mod z^{N+1});
    - the invariant differential is  omega = dx/(2y) = (1 + z g'/(2g)) dz
      (x = z/w = 1/(z^2 g), y = -1/w = -1/(z^3 g));
    - the formal logarithm is  l(z) = int omega,  so
      c_t = [z^{t-1}] (1 + z g'/(2g)) / t.
    Truncated power series are coefficient lists of length N+1. Sums are
    plain list folds, so that the definition computes. *)

Section formal_log.

  Variable R : comUnitRingType.
  Variable A : R.

  Definition lsum (f : nat -> R) (lo n : nat) : R :=
    foldr (fun i acc => f i + acc) 0 (iota lo n).

  (* product of truncated series, degree <= N *)
  Definition sr_mul (N : nat) (a b : seq R) : seq R :=
    mkseq (fun n => lsum (fun i => nth 0 a i * nth 0 b (n - i)) 0 n.+1) N.+1.

  Definition sr_one (N : nat) : seq R := mkseq (fun n => (n == 0)%:R) N.+1.

  (* one step  g |-> 1 + A z^4 g^2 *)
  Definition g_step (N : nat) (g : seq R) : seq R :=
    let g2 := sr_mul N g g in
    mkseq (fun n => (n == 0)%:R + (if (4 <= n)%N then A * nth 0 g2 (n - 4) else 0)) N.+1.

  (* g mod z^{N+1}; N+1 iterations suffice since each gains 4 degrees *)
  Definition g_ser (N : nat) : seq R := iter N.+1 (g_step N) (sr_one N).

  (* inverse of a series with constant coefficient 1: coefficients 0..n *)
  Fixpoint sr_inv_aux (g : seq R) (n : nat) : seq R :=
    match n with
    | 0 => [:: 1]
    | n'.+1 =>
        let b := sr_inv_aux g n' in
        rcons b (- lsum (fun i => nth 0 g i * nth 0 b (n'.+1 - i)) 1 n'.+1)
    end.

  (* the coefficients of  omega/dz = 1 + z g' / (2 g)  up to degree N *)
  Definition omega_ser (N : nat) : seq R :=
    let g := g_ser N in
    let b := sr_inv_aux g N in
    mkseq (fun n => (n == 0)%:R
                    + (2%:R)^-1 * lsum (fun i => i%:R * nth 0 g i * nth 0 b (n - i)) 0 n.+1) N.+1.

  (* c_t, t >= 1, and c_0 = 0 *)
  Definition ct_gen (t : nat) : R :=
    match t with
    | 0 => 0
    | t'.+1 => (t%:R)^-1 * nth 0 (omega_ser t') t'
    end.

End formal_log.

(* the closed form of DESIGN 1.1, for comparison only (NOT used as the
   definition):  c_{4n+1} = binom(2n,n) aE^n / (4n+1), c_t = 0 otherwise *)
Definition ct_closed {R : comUnitRingType} (A : R) (t : nat) : R :=
  if (t %% 4 == 1)%N then ((4 * (t %/ 4) + 1)%:R)^-1 * ('C(2 * (t %/ 4), t %/ 4))%:R * A ^+ (t %/ 4)
  else 0.

(* the coefficients of the formal logarithm of E over F [explicit] *)
Definition ct (t : nat) : qe rat := ct_gen aE t.


(** Sanity checks of the recipe against the closed form (Risk 22): for
    the generic parameter A = 1 over rat up to t = 21, and for the actual
    parameter aE over F up to t = 8. (Beyond t = 8, aE^2 is too large for
    kernel computation with MathComp's unary integers.) The closed form
    for general t is NOT proved; it is not needed by any consumer. *)

Lemma ct_gen_closed_check :
  all (fun t => ct_gen (1 : rat) t == ct_closed 1 t) (iota 0 22).
Proof. by vm_compute. Qed.

Lemma ct_closed_check_aux :
  (fun A : qe rat => all (fun t => ct_gen A t == ct_closed A t) (iota 0 9)) aE.
Proof. by vm_compute. Qed.

Lemma ct_closed_check : all (fun t => ct t == ct_closed aE t) (iota 0 9).
Proof. exact: ct_closed_check_aux. Qed.

(* the truncated formal logarithm  l_K(Z) = sum_{t=1}^K c_t Z^t  on E
   (sg = false), and  l_K^sigma  with conjugated coefficients on E^sigma
   (sg = true), evaluated in R(sqrt2) for any numeric field R (R = rat
   for F, R = sQ for *F). Only these finite polynomials are ever
   transferred (02-reduction.tex, after Prop ell:formal). *)
Definition ellK {R : numFieldType} (sg : bool) (K : nat) (Z : qe R) : qe R :=
  \sum_(1 <= t < K.+1) qe_rat (qe_e sg (ct t)) * Z ^+ t.

(** * 4. Formulas with rational coefficients evaluated in a numeric field

    [qpoly]/[qform] are those of PosExistential.v (rational coefficients).
    [qp_evalR] maps the coefficients by [ratr]; over rat it is [qp_eval]. *)

(* MathComp also has a [qpoly]; ours is the one of PosExistential.v *)
Abbreviation qpolyQ := PosExistential.qpoly.

Section qf_holdsR.

  Variable R : numFieldType.

  Fixpoint qp_evalR {V : Set} (φ : V -> R) (p : qpolyQ V) : R :=
    match p with
    | qp_cnst c => ratr c
    | qp_var v => φ v
    | qp_add p q => qp_evalR φ p + qp_evalR φ q
    | qp_mul p q => qp_evalR φ p * qp_evalR φ q
    end.

  Fixpoint qf_holdsR {V : Set} (φ : V -> R) (A : qform V) : Prop :=
    match A with
    | qf_eq0 p => qp_evalR φ p = 0
    | qf_neq0 p => qp_evalR φ p <> 0
    | qf_and A B => qf_holdsR φ A /\ qf_holdsR φ B
    | qf_or A B => qf_holdsR φ A \/ qf_holdsR φ B
    end.

End qf_holdsR.

Lemma qp_evalR_rat (V : Set) (φ : V -> rat) p : qp_evalR φ p = qp_eval φ p.
Proof. by elim: p => [c | v | p Hp q Hq | p Hp q Hq] //=; rewrite ?ratr_id ?Hp ?Hq. Qed.

Lemma qf_holdsR_rat (V : Set) (φ : V -> rat) A : qf_holdsR φ A <-> qf_holds φ A.
Proof. by elim: A => [p | p | A HA B HB | A HA B HB] /=; rewrite ?qp_evalR_rat; tauto. Qed.

(** * 5. The positive existential formula Phi (DESIGN 1.2)

    03-parity.tex, par:auxiliary-functions, with  E_l : y^2 = x(x-l)(x+3l).
    Phi(b) holds if b = 0, or if b <> 0 and for some m in M, m_d in D_m and
    t, e in Q:  d = m_d b, b' = m b, U = b (1 - d t^2)/(1 + d t^2),
    H' = b'(b' - U^2), 1 + d t^2 <> 0, e H' <> 0, and each of E_e and
    E_{eH'} has a rational point with x-coordinate in b' Q^{x2}.

    As a [qform nat]: variable 0 is b, variables 1..14 are the witnesses
    t, e, U, H', i1, i2, x1, y1, z1, j1, x2, y2, z2, j2. The existential
    over the witnesses is outside the disjunction (it commutes with it). *)

Section Phi.

  Definition qv (i : nat) : qpolyQ nat := qp_var i.
  Definition qc (c : rat) : qpolyQ nat := qp_cnst c.
  Definition qsub (p q : qpolyQ nat) : qpolyQ nat := qp_add p (qp_mul (qc (-1)) q).

  Definition pv_b := 0%N.   Definition pv_t := 1%N.   Definition pv_e := 2%N.
  Definition pv_U := 3%N.   Definition pv_H := 4%N.   Definition pv_i1 := 5%N.
  Definition pv_i2 := 6%N.  Definition pv_x1 := 7%N.  Definition pv_y1 := 8%N.
  Definition pv_z1 := 9%N.  Definition pv_j1 := 10%N. Definition pv_x2 := 11%N.
  Definition pv_y2 := 12%N. Definition pv_z2 := 13%N. Definition pv_j2 := 14%N.

  (* y^2 = x (x - l) (x + 3 l), as  lhs - rhs *)
  Definition qcurve (l x y : qpolyQ nat) : qform nat :=
    qf_eq0 (qsub (qp_mul y y) (qp_mul x (qp_mul (qsub x l) (qp_add x (qp_mul (qc 3%:R) l))))).

  Definition Phi_block (mm md : rat) : qform nat :=
    let b := qv pv_b in
    let t := qv pv_t in let e := qv pv_e in let U := qv pv_U in let H := qv pv_H in
    let d := qp_mul (qc md) b in
    let b' := qp_mul (qc mm) b in
    let dt2 := qp_mul d (qp_mul t t) in
    let onep := qp_add (qc 1) dt2 in
    let onem := qsub (qc 1) dt2 in
    let eH := qp_mul e H in
    qf_and (qf_eq0 (qsub (qp_mul U onep) (qp_mul b onem)))                 (* U (1 + d t^2) = b (1 - d t^2) *)
   (qf_and (qf_eq0 (qsub H (qp_mul b' (qsub b' (qp_mul U U)))))            (* H' = b' (b' - U^2) *)
   (qf_and (qf_eq0 (qsub (qp_mul onep (qv pv_i1)) (qc 1)))                 (* 1 + d t^2 <> 0 *)
   (qf_and (qf_eq0 (qsub (qp_mul eH (qv pv_i2)) (qc 1)))                   (* e H' <> 0 *)
   (qf_and (qcurve e (qv pv_x1) (qv pv_y1))                                (* (x1,y1) on E_e *)
   (qf_and (qf_eq0 (qsub (qv pv_x1) (qp_mul b' (qp_mul (qv pv_z1) (qv pv_z1)))))  (* x1 = b' z1^2 *)
   (qf_and (qf_eq0 (qsub (qp_mul (qv pv_z1) (qv pv_j1)) (qc 1)))           (* z1 <> 0 *)
   (qf_and (qcurve eH (qv pv_x2) (qv pv_y2))                               (* (x2,y2) on E_{eH'} *)
   (qf_and (qf_eq0 (qsub (qv pv_x2) (qp_mul b' (qp_mul (qv pv_z2) (qv pv_z2)))))  (* x2 = b' z2^2 *)
           (qf_eq0 (qsub (qp_mul (qv pv_z2) (qv pv_j2)) (qc 1))))))))))).  (* z2 <> 0 *)

  Definition qor_l (l : list (qform nat)) : qform nat := foldr (@qf_or nat) qf_false l.

  (* the lists: pairs (m, D_m) *)
  Definition Phi_form (L : seq (rat * seq rat)) : qform nat :=
    qf_or (qf_eq0 (qv pv_b))
          (qor_l (List.flat_map (fun mD => List.map (Phi_block mD.1) mD.2) L)).

  Variable R : numFieldType.

  Definition Phi_env (b : R) (w : nat -> R) (i : nat) : R :=
    if i is 0 then b else w i.

  (* Phi(b) in a numeric field: witnesses range over R *)
  Definition Phi_holdsR (L : seq (rat * seq rat)) (b : R) : Prop :=
    exists w : nat -> R, qf_holdsR (Phi_env b w) (Phi_form L).

  (* the mathematical condition of 03-parity.tex *)
  Definition El_point (l b' : R) : Prop :=
    exists x y z : R, z != 0 /\ x = b' * z ^+ 2 /\ y ^+ 2 = x * (x - l) * (x + 3%:R * l).

  Definition Phi_U (d b t : R) : R := b * (1 - d * t ^+ 2) / (1 + d * t ^+ 2).

  Definition Phi_math (L : seq (rat * seq rat)) (b : R) : Prop :=
    b = 0 \/
    (b != 0 /\ exists mm Dm md t e,
        List.In (mm, Dm) L /\ List.In md Dm /\
        let d := ratr md * b in
        let b' := ratr mm * b in
        let H' := b' * (b' - Phi_U d b t ^+ 2) in
        1 + d * t ^+ 2 != 0 /\ e * H' != 0 /\ El_point e b' /\ El_point (e * H') b').

  Lemma qor_l_spec (φ : nat -> R) l :
    qf_holdsR φ (qor_l l) <-> exists A, List.In A l /\ qf_holdsR φ A.
  Proof.
    elim: l => [ | A l IHl ] /=.
    - split; [ by rewrite rmorph0; case | by case=> ? [] ].
    - rewrite IHl; split.
      + case=> [ HA | [ B [ HB1 HB2 ] ] ]; [ exists A | exists B ]; tauto.
      + case=> B [ [ <- | HB ] HB2 ]; [ by left | right; exists B; tauto ].
  Qed.

  Lemma qsub_spec (φ : nat -> R) p q :
    qp_evalR φ (qsub p q) = 0 <-> qp_evalR φ p = qp_evalR φ q.
  Proof.
    rewrite /qsub /= rmorphN1 mulN1r; split => [ /eqP | -> ].
    - by rewrite subr_eq0 => /eqP.
    - exact: subrr.
  Qed.

End Phi.

(* the satisfaction lemma: Phi as a formula expresses the paper's condition *)
Section Phi_holds_iff.
  Variable R : numFieldType.

  Lemma qf_eq0_sub_spec (φ : nat -> R) p q :
    qf_holdsR φ (qf_eq0 (qsub p q)) <-> qp_evalR φ p = qp_evalR φ q.
  Proof. exact: qsub_spec. Qed.

  Lemma Phi_holds_iff L (b : R) : Phi_holdsR L b <-> Phi_math L b.
  Proof.
    split.
    - move=> [w [Hb | /qor_l_spec [A [HA HAh]]]]; first by left.
      move: HA => /in_flat_map [[mm Dm] [HmD /in_map_iff [md [HA Hmd]]]].
      subst A; move: HAh.
      rewrite /Phi_block /qcurve.
      move=> [/qf_eq0_sub_spec E1 [/qf_eq0_sub_spec E2 [/qf_eq0_sub_spec E3 [/qf_eq0_sub_spec E4
              [/qf_eq0_sub_spec E5 [/qf_eq0_sub_spec E6 [/qf_eq0_sub_spec E7 [/qf_eq0_sub_spec E8
              [/qf_eq0_sub_spec E9 /qf_eq0_sub_spec E10]]]]]]]]].
      move: E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 => /=.
      rewrite !rmorph1 ratr_nat.
      set t := w 1%N; set e := w 2%N; set U := w 3%N; set H := w 4%N.
      set i1 := w 5%N; set i2 := w 6%N.
      set x1 := w 7%N; set y1 := w 8%N; set z1 := w 9%N; set j1 := w 10%N.
      set x2 := w 11%N; set y2 := w 12%N; set z2 := w 13%N; set j2 := w 14%N.
      set d := ratr md * b; set b' := ratr mm * b.
      rewrite rmorphN1 !mulN1r -!expr2.
      move=> E1 E2 E3 E4 E5 E6 E7 E8 E9 E10.
      have nz1 : 1 + d * t ^+ 2 != 0.
      { apply/eqP => H0; move: E3; rewrite H0 mul0r => /eqP; by rewrite eq_sym oner_eq0. }
      have nz2 : e * H != 0.
      { apply/eqP => H0; move: E4; rewrite H0 mul0r => /eqP; by rewrite eq_sym oner_eq0. }
      have nzz1 : z1 != 0.
      { apply/eqP => H0; move: E7; rewrite H0 mul0r => /eqP; by rewrite eq_sym oner_eq0. }
      have nzz2 : z2 != 0.
      { apply/eqP => H0; move: E10; rewrite H0 mul0r => /eqP; by rewrite eq_sym oner_eq0. }
      have hU : Phi_U d b t = U by rewrite /Phi_U -E1 mulfK.
      have hH : b' * (b' - Phi_U d b t ^+ 2) = H by rewrite hU E2.
      right; split.
      { apply/eqP => Hb0; move: nz2; rewrite -hH /b' Hb0 mulr0 mul0r mulr0 eqxx. done. }
      exists mm, Dm, md, t, e; do 2 (split; first done).
      rewrite /= -/d -/b' hH; do 2 (split; first done).
      split.
      + exists x1, y1, z1; do 2 (split; first done); by rewrite E5 mulrA.
      + exists x2, y2, z2; do 2 (split; first done); by rewrite E8 mulrA.
    - case=> [ Hb | [ Hb [ mm [ Dm [ md [ t [ e [ HmD [ Hmd ] ] ] ] ] ] ] ] ].
      { exists (fun _ => 0); by left. }
      rewrite /=.
      set d := ratr md * b; set b' := ratr mm * b.
      set U := Phi_U d b t; set H := b' * (b' - U ^+ 2).
      move=> [ nz1 [ nz2 [ [ x1 [ y1 [ z1 [ Hz1 [ Hx1 Hy1 ] ] ] ] ] [ x2 [ y2 [ z2 [ Hz2 [ Hx2 Hy2 ] ] ] ] ] ] ] ].
      pose w (i : nat) : R :=
        match i with
        | 1%N => t | 2%N => e | 3%N => U | 4%N => H | 5%N => (1 + d * t ^+ 2)^-1 | 6%N => (e * H)^-1
        | 7%N => x1 | 8%N => y1 | 9%N => z1 | 10%N => z1^-1
        | 11%N => x2 | 12%N => y2 | 13%N => z2 | 14%N => z2^-1
        | _ => 0 end.
      exists w; right; apply/qor_l_spec; exists (Phi_block mm md); split.
      { apply/in_flat_map; exists (mm, Dm); split; first done.
        apply/in_map_iff; exists md; by split. }
      rewrite /Phi_block /qcurve.
      repeat split; apply/qf_eq0_sub_spec; rewrite /= ?rmorph1 ?rmorphN1 ?ratr_nat ?mulN1r -?expr2 -/d -/b'.
      + rewrite /U /Phi_U; field; exact nz1.
      + done.
      + by rewrite mulfV.
      + by rewrite mulfV.
      + by rewrite Hy1 [RHS]mulrA.
      + done.
      + by rewrite mulfV.
      + by rewrite Hy2 [RHS]mulrA.
      + done.
      + by rewrite mulfV.
  Qed.
End Phi_holds_iff.

(* over rat, [qf_holdsR] is [qf_holds] of PosExistential.v *)
Lemma Phi_holds_rat L (b : rat) :
  Phi_holdsR L b <-> exists w : nat -> rat, qf_holds (Phi_env b w) (Phi_form L).
Proof. by split=> [] [w Hw]; exists w; apply/qf_holdsR_rat. Qed.

(** * 6. Ordinary arithmetic helpers (computable on rat / int) *)

(* bit height  htb(x) = log2_up max(|num x|, den x)  (DESIGN D3, 2.7) *)
Definition htb (x : rat) : nat :=
  Nat.log2_up (maxn (absz (numq x)) (absz (denq x))).

(* the q-adic valuation of a nonzero rational (junk 0 at x = 0) *)
Definition vqr (p : nat) (x : rat) : int :=
  (logn p (absz (numq x)))%:Z - (logn p (absz (denq x)))%:Z.

(* the sign of a branch *)
Definition sgnz (s : sgn) : int := if s is sg_p then 1 else -1.

(* membership in  r^i (Z[sqrt2])_p  at the branch  sqrt2 |-> s B  of the
   prime r (localization form, 02-reduction.tex red:localization-definition
   and the paragraph after Cor pri:integer-coverage):
   alpha = r^i X / Y with X, Y in Z[sqrt2] and Y(sB) invertible modulo r.
   For a prime r, "Y(sB) invertible mod r" is equivalent to the paper's
   "Y(sB) nonzero mod r"; we state the invertibility form, with its
   witnesses iota, kappa, which is exactly the encoding LOC of the theory
   (DESIGN 3.2, Risk 8). See the Implementation notes (task 8). *)
Definition LocZ (i : nat) (r B : int) (s : sgn) (alpha : qe rat) : Prop :=
  exists X0 X1 Y0 Y1 iota kappa : int,
       alpha * QE Y0%:~R Y1%:~R = (r%:~R) ^+ i * QE X0%:~R X1%:~R
    /\ (Y0 + sgnz s * B * Y1) * iota - 1 = r * kappa.

(* "formal for this localization": O, or 1/x in r (Z[sqrt2])_p,
   on E (sg = false) or for the conjugate point on E^sigma (sg = true) *)
Definition FormalZ (sg : bool) (r B : int) (s : sgn) (p : pt rat) : Prop :=
  match p with
  | None => True
  | Some (x, _) => LocZ 1 r B s (qe_e sg x)^-1
  end.

(** * 7. The fixed data (DESIGN 1, table)

    [explicit] items are definitions above ([dF], [aE], [ct], [ellK]) or
    below ([fd_L], [Phi]); [thm] items are fields. *)

Record FixedData : Type := {
  fd_m : nat;                        (* [thm] Prop ell:rank: m E(F) = Z P *)
  fd_P0 : qe rat * qe rat;           (* [thm] Prop ell:rank: a point with P = [m] P0 *)
  fd_C : i4 -> rat;                  (* [thm] Thm hei:height: the four finite points of C
                                        (C = these and oo); branch values of [H], not explicit *)
  fd_S : seq nat;                    (* [thm] Thm hei:height: exceptional primes S *)
  fd_Hb : nat;                       (* [thm] Thm hei:height: constant H, bit version (D3) *)
  fd_c : nat;                        (* [thm] Thm hei:height: exponent c (enlarged to an integer) *)
  fd_Kset : seq nat;                 (* [thm] Lemma pri:pattern: multiplier set \mathcal K *)
  fd_SE : seq nat;                   (* [thm] Prop ell:formal: S_E (by [E] it is {2,7}) *)
  fd_PhiL : seq (rat * seq rat);     (* [thm] [P] Sec. 3.2: the lists M and D_m, as pairs (m, D_m) *)
  fd_Nh : nat;                       (* [thm] canonical height lower bound, red:elliptic-lower (2.6, 2.7) *)
  fd_Ch : nat                        (* [thm] idem, additive constant *)
}.

Section derived.

  Variable D : FixedData.

  (* n P0 for n : nat, by iterated chord-tangent addition *)
  Definition mulQn (n : nat) : pt rat := iter n (ec_add (Some (fd_P0 D))) None.

  (* n P0 for n : int *)
  Definition mulQ (n : int) : pt rat :=
    match n with
    | Posz k => mulQn k
    | Negz k => pt_neg (mulQn k.+1)
    end.

  (* n P = (n m) P0 *)
  Definition mulP (n : int) : pt rat := mulQ (n * (fd_m D)%:Z).

  (* the generator P of m E(F) = Z P  [derived] *)
  Definition Pgen : pt rat := mulP 1.

  (* the primitive integral linear form  L_b(U,V) = den(b) U - num(b) V
     vanishing at b = fd_C D i  [derived]; L_oo(U,V) = V  [explicit] *)
  Definition fd_L {R : pzRingType} (i : i4) (u v : R) : R :=
    (denq (fd_C D i))%:~R * u - (numq (fd_C D i))%:~R * v.

  Definition fd_Lint (i : i4) (u v : int) : int :=
    denq (fd_C D i) * u - numq (fd_C D i) * v.

  (* S_1: 2, 3 and the supports of all entries of the Phi lists  [derived] *)
  Definition rat_support (x : rat) : seq nat := primes (absz (numq x)) ++ primes (absz (denq x)).

  Definition S1 : seq nat :=
    2%N :: 3%N :: flatten [seq rat_support x | x <- flatten [seq mD.1 :: mD.2 | mD <- fd_PhiL D]].

  (* primes of the pairwise determinants of the five forms  [derived] *)
  Definition Sdet : seq nat :=
       flatten [seq primes (absz (denq (fd_C D i))) | i <- all_i4]
    ++ flatten [seq primes (absz (numq (fd_C D i) * denq (fd_C D j) - numq (fd_C D j) * denq (fd_C D i))%R)
               | i <- all_i4, j <- all_i4].

  (* Sfix := S u S_1 u S_E u supp(Kset) u S_det u {2}  [derived] *)
  Definition Sfix : seq nat :=
    fd_S D ++ S1 ++ fd_SE D ++ flatten [seq primes k | k <- fd_Kset D] ++ Sdet ++ [:: 2%N].

  (* S_K := Sfix u {p <= K+1}  (02-reduction.tex Sec. 2.5, Risk 17) *)
  Definition SK (K : nat) : seq nat := undup (Sfix ++ [seq p <- iota 0 K.+2 | prime p]).

  (* q not in S_K, for a prime q *)
  Definition good (K q : nat) : bool := (K.+1 < q)%N && (q \notin Sfix).

  (* H_K of Cor hei:enlarge-exceptions with S' = S_K  [derived] *)
  Definition HK (K : nat) : nat :=
    (fd_Hb D * (\prod_(p <- SK K | p \notin fd_S D) p) ^ fd_c D)%N.

  (* the contact radical M_{S'}(s) of hei:radical, for s = num/den  [derived] *)
  Definition odd_contact (q : nat) (s : rat) : bool :=
    odd (logn q (absz (denq s)))
    || has (fun i => odd (logn q (absz (fd_Lint i (numq s) (denq s))))) all_i4.

  Definition contact_support (s : rat) : nat :=
    (absz (denq s) * \prod_(i <- all_i4) absz (fd_Lint i (numq s) (denq s)))%N.

  Definition MS (S' : seq nat) (s : rat) : nat :=
    \prod_(q <- primes (contact_support s) | (q \notin S') && odd_contact q s) q.

  (* the ordinary function whose transfer is the ambient MK *)
  Definition MK_ord (K : nat) (s : rat) : nat := MS (SK K) s.

  (** Witnesses of Cor pri:integer-coverage (DESIGN 2.5): only the unary
      data u1, u2, v, and per member j: eps_j, k_j, r_j, B_j, and per
      (j, s): h, j0. The per-a localization witnesses are NOT part of it
      (they are existentials inside [RepSpec], under the forall a). *)
  Record RepWit1 : Type := {
    rw_u1 : int;
    rw_u2 : int;
    rw_v : int;
    rw_eps : mem13 -> int;
    rw_k : mem13 -> nat;
    rw_r : mem13 -> int;
    rw_B : mem13 -> int;
    rw_h : mem13 -> sgn -> int;
    rw_j0 : mem13 -> sgn -> int
  }.

  (* u_3 := A v - u_1 - u_2 *)
  Definition rw_u (W : RepWit1) (A : int) (i : i3) : int :=
    match i with
    | I1 => rw_u1 W
    | I2 => rw_u2 W
    | I3 => A * rw_v W - rw_u1 W - rw_u2 W
    end.

  (* the 13 members  v, L_b(u_i, v)  of pri:coverage-list *)
  Definition rw_mem (W : RepWit1) (A : int) (j : mem13) : int :=
    match j with
    | mem_v => rw_v W
    | mem_L i b => fd_Lint b (rw_u W A i) (rw_v W)
    end.

  (* conditions (i) and (ii) of Lemma red:local-comparison in the ordinary
     setting R = Z, T_a = aP, q = r, at the branch s, in localization form *)
  Definition RepConds (K : nat) (r B : int) (s : sgn) (h j0 a : int) : Prop :=
       FormalZ false r B s (mulP h)
    /\ FormalZ false r B s (mulP (h * a))
    /\ ellK false K (zpar false (mulP h)) != 0
    /\ LocZ K r B s (ellK false K (zpar false (mulP (h * a)))
                       / ellK false K (zpar false (mulP h)) - a%:~R)          (* red:primary-test *)
    /\ FormalZ true r B s (mulP j0)
    /\ FormalZ true r B s (mulP ((h - 4) * a))
    /\ LocZ K r B s (zpar true (mulP ((h - 4) * a)) / zpar true (mulP j0)).   (* red:alternate-test *)

  Definition RepSpec (K : nat) (A : int) (W : RepWit1) : Prop :=
    rw_v W != 0 /\
    forall j : mem13,
         rw_mem W A j = rw_eps W j * (rw_k W j)%:Z * rw_r W j
      /\ (rw_eps W j = 1 \/ rw_eps W j = -1)
      /\ rw_k W j \in fd_Kset D
      /\ 0 < rw_r W j
      /\ prime (absz (rw_r W j))
      /\ (K.+1 < absz (rw_r W j))%N
      /\ (exists wB : int, rw_B W j ^+ 2 - 2 = rw_r W j * wB)          (* r | B^2 - 2: r splits *)
      /\ forall s : sgn,
              rw_h W j s != 0
           /\ rw_j0 W j s != 0
           /\ forall a : int, RepConds K (rw_r W j) (rw_B W j) s (rw_h W j s) (rw_j0 W j s) a.

  (** Valuations at places of F, ordinary: a place of F above p normalized
      by v(p) = 1 is the same as a map v : F^x -> Z which is multiplicative,
      ultrametric and has v(p) = 1 (its restriction to Q is then v_p, and no
      such map exists at a ramified p). Values at 0 are junk. *)
  Definition is_place_above (v : qe rat -> int) (p : nat) : Prop :=
       (forall x y, x != 0 -> y != 0 -> v (x * y) = v x + v y)
    /\ (forall x y, x != 0 -> y != 0 -> x + y != 0 -> Num.min (v x) (v y) <= v (x + y))
    /\ v (p%:R) = 1.

  (* reduction to O at v:  O, or v(x) < 0 *)
  Definition red_ord (sg : bool) (v : qe rat -> int) (p : pt rat) : Prop :=
    match p with
    | None => True
    | Some (x, _) => v (qe_e sg x) < 0
    end.

End derived.

(** * 8. Well-formedness of the fixed data (asserted by the same theorems) *)

Record FixedWF (D : FixedData) : Prop := {
  wf_m : (0 < fd_m D)%N;                                     (* Prop ell:rank *)
  wf_C : forall i j, fd_C D i = fd_C D j -> i = j;           (* Thm hei:height: distinct points *)
  wf_K : forall k, k \in fd_Kset D -> (0 < k)%N;             (* Lemma pri:pattern *)
  wf_PhiL_nonempty : fd_PhiL D <> [::];                      (* [P] Sec. 3.1: M nonempty *)
  wf_PhiL : forall mm Dm, List.In (mm, Dm) (fd_PhiL D) ->    (* [P] Sec. 3.1: entries in Q^x, D_m nonempty *)
              mm != 0 /\ Dm <> [::] /\ forall md, List.In md Dm -> md != 0;
  wf_c : (0 < fd_c D)%N;                                     (* Thm hei:height *)
  wf_Hb : (0 < fd_Hb D)%N;                                   (* Thm hei:height *)
  wf_Nh : (0 < fd_Nh D)%N;                                   (* canonical height bound *)
  wf_S : all prime (fd_S D);                                 (* Thm hei:height *)
  wf_SE : all prime (fd_SE D)                                (* Prop ell:formal *)
}.

(** * 9. Ordinary hypotheses consumed by the standard model (DESIGN 2.1,
      2.4, 2.5). These are the only Tier 3 inputs on the ordinary side. *)

Record StdHyps (D : FixedData) : Prop := {
  (* (E1) group law on the multiples of P0: chord-tangent addition is
     associative. Classical (not specific to the paper), Risk 11.
     Consumed by: standard model (ax_add, ax_chain). *)
  E1 : forall n n' : int, ADDrel (mulQ D n) (mulQ D n') (mulQ D (n + n'));
  (* (E2) Prop ell:rank: P0 is nontorsion; nonzero multiples avoid O and the
     two-torsion points, hence have x, y <> 0.
     Consumed by: standard model (ax_coord). *)
  E2 : forall n : int, n != 0 ->
         exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y);
  (* (HCov) Cor pri:integer-coverage, in the paper's forall-exists form
     (PLAN Q1, revised), localization form, with the lower bound Y_0 and the
     good-reduction / r notin S_E clauses dropped (weakenings, DESIGN 2.5).
     Consumed by: standard model (ax_rep K). *)
  HCov : forall (K : nat) (A : int), (1 <= K)%N -> exists W : RepWit1, RepSpec D K A W;
  (* (PP1) Prop par:pole-parity, part 1: Q |= Phi(b) for every b in Z.
     Consumed by: test soundness, constraint (d). *)
  PP1 : forall b : int, Phi_holdsR (fd_PhiL D) (b%:~R : rat)
}.

(** * 10. Ordinary versions of the transferred facts

    (Phase 1: documentation only.) These records state what is true
    ordinarily, i.e. why each ambient field is the transfer of a true
    statement (Risk 14). In the final development they are the input of
    the ultrapower model (CompactnessT.CompactnessT_StdHyps), and they are
    proved for the explicit data (Generator.inputs_to_data_final). *)

Section ordinary_doc.

  Variable D : FixedData.

  (* Cor hei:enlarge-exceptions with S' = S_K: provable from O_height
     (three lines in [R]); recorded as a statement *)
  Definition hei_enlarge_ord : Prop :=
    forall (K : nat) (s : rat), (forall i, s != fd_C D i) ->
      (htb s <= HK D K * (MK_ord D K s) ^ fd_c D)%N.

  (* red:radical-divides, ordinary (elementary): transferred as field H2 *)
  Definition radical_divides_ord : Prop :=
    forall (K : nat) (s : rat) (delta : int), delta != 0 ->
      (forall q : nat, prime q -> (q %| MK_ord D K s)%N -> (q ^ K %| absz delta)%N) ->
      ((MK_ord D K s) ^ K %| absz delta)%N.

End ordinary_doc.

Record OrdHyps (D : FixedData) : Prop := {
  (* Prop ell:rank: m E(F) = Z P (with P = m P0); ordinary R5.
     Points of m E(F) are given by addition chains Q_1, ..., Q_m = m Q_1. *)
  O_rank : forall Q : nat -> qe rat * qe rat,
      on_curve (Q 1%N) ->
      (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ADDrel (Some (Q k)) (Some (Q 1%N)) (Some (Q k.+1))) ->
      exists n : int, mulP D n = Some (Q (fd_m D));
  (* Prop ell:formal, eq. ell:ratio (both curves, sg = false: E, sg = true: E^sigma) *)
  O_F1 : forall (sg : bool) (p : nat), prime p -> p \notin fd_SE D ->
      forall v, is_place_above v p ->
      forall n n' : int, n' != 0 ->
      red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
      n = 0 \/ v (zpar sg (mulP D n)) - v (zpar sg (mulP D n')) = vqr p n%:~R - vqr p n'%:~R;
  (* Prop ell:formal, eq. ell:truncation *)
  O_F2 : forall (sg : bool) (K p : nat), (1 <= K)%N -> prime p -> p \notin fd_SE D -> (K.+1 < p)%N ->
      forall v, is_place_above v p ->
      forall n n' : int, n' != 0 ->
      red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
      (n = 0 \/ vqr p n'%:~R <= vqr p n%:~R) ->
      ellK sg K (zpar sg (mulP D n')) != 0 /\
      (let x := ellK sg K (zpar sg (mulP D n)) / ellK sg K (zpar sg (mulP D n'))
                - qe_of (n%:~R / n'%:~R) in x = 0 \/ K%:Z <= v x);
  (* Thm hei:height, eq. hei:height-bound, in bits (D3) *)
  O_height : forall s : rat, (forall i, s != fd_C D i) ->
      (htb s <= fd_Hb D * (MS D (fd_S D) s) ^ fd_c D)%N;
  (* red:all-ring-height: H(x+y+z) <= 3 H(x) H(y) H(z), in bits *)
  O_HS : forall x1 x2 x3 : rat, (htb (x1 + x2 + x3) <= htb x1 + htb x2 + htb x3 + 2)%N;
  (* red:elliptic-lower with heights over F: h(x(nP)) >= 2 hhat(P) n^2 - C *)
  O_HL : forall (n : int) (x0 x1 x2 : rat), n != 0 -> x2 != 0 ->
      (exists y, mulP D n = Some (QE x0 x1 / qe_of x2, y)) ->
      ((absz n) ^ 2 <= fd_Nh D * (htb x0 + htb x1 + htb x2 + fd_Ch D))%N;
  (* Prop par:pole-parity, part 2 *)
  O_PP2 : forall b : rat, b != 0 -> Phi_holdsR (fd_PhiL D) b ->
      forall q : nat, prime q -> q \notin S1 D -> vqr q b < 0 -> ~~ odd (absz (vqr q b))
}.
