(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* E(F) is finitely generated (PLAN P14b-i, Phase 2E), for
   E : y^2 = x^3 + aE x over F = Q(sqrt2): the descent via heights,
   from the weak Mordell-Weil theorem of Descent.v and the height
   inequalities of HeightLower.v. An existence statement: the
   generating set is explicit, but its height bound is astronomically
   large and is never evaluated.

   MAIN RESULTS.
   - [EF_fingen]: there is a list L of points of E(F) such that every
     R in E(F) is  R = lincomb cs = sum_i c_i P_i  with (c_i, P_i) in
     cs, c_i : int and P_i in L ([mulZ n P] is n P by iterated
     chord-tangent addition, the recipe of [mulQ]).
   - [EF_fingen_subgroup]: the same with the inductive predicate
     [incomb L] (generated from O by adding and subtracting elements
     of L): on_curve_pt R <-> incomb L R.
   - [EF_fingen_reps]: moreover the eight representatives [reps] of
     E(F)/2E(F) (Descent.v) lie in L.
   - Tools for later use: [incomb_add], [incomb_neg], [incomb_sub],
     [incomb_mulZ], [incomb_on], [incomb_iff]; [mulZ_add], [mulZ_neg],
     [mulZ_mul], [mulZ_on], [mulQ_mulZ] (mulQ D n = n P0).

   PROOF. L := reps ++ (points of height <= B0), with
     MS := sum of the heights of the eight representatives,
     CC := KD^2 KU^2 MS^2,  B0 := an integer >= 16 CC.
   For R in E(F) with Ht R > B0, write R = 2 R2 + S (weak_MW). Either
   x(R) = x(S), so R = +-S is in L up to sign, or (Ht_par, Ht >= 1)
     Ht(2 R2) = Ht(R - S) <= KU^2 Ht R^2 Ht S^2,
   and with Ht_dbl
     Ht R2^4 <= KD^2 Ht(2 R2) <= CC Ht R^2 <= Ht R^4 / 16,
   i.e. 2 Ht R2 <= Ht R. Induction on k with Ht R <= 2^k.
   The finite part (Northcott): x is in [candX B0] (NFHeight.v), and
   y is found among finitely many candidates [candY (x^3 + aF x)]
   computed with an exact rational square root [rsqrt] (from
   Nat.sqrt of numerator and denominator): if y = u + v sqrt2 and
   y^2 = c0 + c1 sqrt2, then |u^2 - 2 v^2| = sqrt(c0^2 - 2 c1^2), so
   u^2 and 2 v^2 are (c0 +- that) / 2. The list is filtered by the
   (boolean) curve equation, so all its elements lie on E.

   Implementation notes (HeightArch.v): the constants MS, CC, B0 are
   locked; RF goals are never closed by [done].

   No axioms. *)

From Stdlib Require Import Arith Lia List.
From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From Undecidability.H10.Rational
  Require Import FixedData GroupLaw NFHeight HeightArch HeightCore HeightLower ExplicitData Descent.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.

Local Open Scope ring_scope.

(** * An exact square root on rat, and the square roots in F *)

(* rsqrt (r * r) = |r| *)
Definition rsqrt (q : rat) : rat := (Nat.sqrt (absz (numq q)))%:R / (Nat.sqrt (absz (denq q)))%:R.

Lemma sqrt_sqn (n : nat) : Nat.sqrt (n * n) = n.
Proof. rewrite -multE; exact: Nat.sqrt_square. Qed.

Lemma rsqrt_sq (r : rat) : rsqrt (r * r) = `|r|.
Proof.
  have Er : r = (numq r)%:~R / (denq r)%:~R by rewrite divq_num_den.
  have hb : 0 < denq r := denq_gt0 r.
  have cab : div.coprime (absz (numq r)) (absz (denq r)) := coprime_num_den r.
  move: Er hb cab; set a := numq r; set b := denq r => Er hb cab.
  have hbb : 0 < b * b by apply: mulr_gt0.
  have E2 : r * r = (a * a)%:~R / (b * b)%:~R by rewrite {1 2}Er mulf_div -!intrM.
  have cab2 : div.coprime (absz (a * a)) (absz (b * b)) by rewrite !abszM coprimeMl !coprimeMr cab.
  have En : numq (r * r) = a * a by rewrite E2 coprimeq_num // gtr0_sg // mul1r.
  have Ed : denq (r * r) = b * b.
  { rewrite E2 coprimeq_den // (gt_eqF hbb) gtr0_norm //. }
  rewrite /rsqrt En Ed !abszM !sqrt_sqn.
  rewrite [in RHS]Er normrM normfV -!intr_norm -!natr_absz.
  reflexivity.
Qed.

Definition pm (u : rat) : seq rat := [:: u; - u].

Lemma pm_mem (u : rat) : u \in pm (rsqrt (u * u)).
Proof.
  rewrite rsqrt_sq /pm !inE; case: (lerP 0 u) => hu.
  - by rewrite (ger0_norm hu) eqxx.
  - by rewrite (ltr0_norm hu) opprK eqxx orbT.
Qed.

Definition dsc (c0 c1 : rat) : rat := rsqrt (c0 * c0 - 2%:R * (c1 * c1)).
Definition candU (c0 c1 : rat) : seq rat :=
  pm (rsqrt ((c0 + dsc c0 c1) / 2%:R)) ++ pm (rsqrt ((c0 - dsc c0 c1) / 2%:R)).
Definition candV (c0 c1 : rat) : seq rat :=
  pm (rsqrt ((c0 + dsc c0 c1) / 4%:R)) ++ pm (rsqrt ((c0 - dsc c0 c1) / 4%:R)).
Definition candY2 (c0 c1 : rat) : seq RF :=
  [seq (QE u v : RF) | u <- candU c0 c1, v <- candV c0 c1].
Definition candY (c : RF) : seq RF := candY2 (qre c) (qim c).

Lemma QE_sqr (u v : rat) : (QE u v : RF) * QE u v = QE (u * u + 2%:R * (v * v)) (u * v + v * u).
Proof. reflexivity. Qed.

Lemma candY_spec (y c : RF) : y * y = c -> y \in candY c.
Proof.
  case: y => u v; rewrite QE_sqr => <-; rewrite /candY.
  change ((QE u v : RF) \in candY2 (u * u + 2%:R * (v * v)) (u * v + v * u)).
  have Ed : (u * u + 2%:R * (v * v)) * (u * u + 2%:R * (v * v))
            - 2%:R * ((u * v + v * u) * (u * v + v * u))
          = (u * u - 2%:R * (v * v)) * (u * u - 2%:R * (v * v)) by ring.
  have two0 : (2%:R : rat) != 0 by rewrite pnatr_eq0.
  have four0 : (4%:R : rat) != 0 by rewrite pnatr_eq0.
  have Es : dsc (u * u + 2%:R * (v * v)) (u * v + v * u) = `|u * u - 2%:R * (v * v)|.
  { by rewrite /dsc Ed rsqrt_sq. }
  rewrite /candY2; apply: (allpairs_f (fun u v => (QE u v : RF))).
  - rewrite /candU Es.
    case: (lerP 0 (u * u - 2%:R * (v * v))) => h.
    + rewrite (ger0_norm h).
      have -> : (u * u + 2%:R * (v * v) + (u * u - 2%:R * (v * v))) / 2%:R = u * u.
      { by field. }
      by rewrite mem_cat pm_mem.
    + rewrite (ltr0_norm h).
      have -> : (u * u + 2%:R * (v * v) - - (u * u - 2%:R * (v * v))) / 2%:R = u * u.
      { by field. }
      by rewrite mem_cat pm_mem orbT.
  - rewrite /candV Es.
    case: (lerP 0 (u * u - 2%:R * (v * v))) => h.
    + rewrite (ger0_norm h).
      have -> : (u * u + 2%:R * (v * v) - (u * u - 2%:R * (v * v))) / 4%:R = v * v.
      { by field. }
      by rewrite mem_cat pm_mem orbT.
    + rewrite (ltr0_norm h).
      have -> : (u * u + 2%:R * (v * v) + - (u * u - 2%:R * (v * v))) / 4%:R = v * v.
      { by field. }
      by rewrite mem_cat pm_mem.
Qed.

(** * Points of bounded height *)

Definition oncb (P : pt rat) : bool :=
  if P is Some (x, y) then (y : RF) * y == (x : RF) ^+ 3 + aF * x else true.

Definition candP (X : nat) : seq (pt rat) :=
  filter oncb [seq Some ((x : RF), (y : RF)) | x <- candX X, y <- candY ((x : RF) ^+ 3 + aF * x)].

Lemma oncb_on (P : pt rat) : oncb P -> on_curve_pt P.
Proof.
  case: P => [ [ x y ] | ] h; last exact: I.
  move: h => /eqP h; exact: (proj2 (on_curveE x y) h).
Qed.

Lemma candP_on X (P : pt rat) : P \in candP X -> on_curve_pt P.
Proof. rewrite mem_filter => /andP [ h _ ]; exact: oncb_on. Qed.

Lemma candP_spec X (P : pt rat) : on_curve_pt P -> Ht P <= X%:R -> P <> None -> P \in candP X.
Proof.
  case: P => [ [ x y ] | ] hc hH hN; last by case: hN.
  have oc := proj1 (on_curveE x y) hc.
  rewrite mem_filter; apply/andP; split; first exact: (introT eqP oc).
  rewrite /Ht crepP_Some in hH.
  exact: (allpairs_f_dep (fun (x : RF) (y : RF) => (Some (x, y) : pt rat)) (Mh_bounded_mem hH) (candY_spec oc)).
Qed.

Lemma mem_In (T : eqType) (x : T) (s : seq T) : x \in s -> List.In x s.
Proof.
  elim: s => [ | a s IH ] //; rewrite in_cons => /orP [ /eqP -> | h ]; [ left | right; exact: IH ].
  reflexivity.
Qed.

(** * Multiples and integer combinations *)

Local Abbreviation K := (@QF rat rat_sq2).

Lemma pt_negK (P : pt rat) : pt_neg (pt_neg P) = P.
Proof. case: P => [ [ x y ] | ]; last reflexivity. by rewrite /pt_neg opprK. Qed.

Lemma pt_neg_add (P Q : pt rat) : pt_neg (ec_add P Q) = ec_add (pt_neg P) (pt_neg Q).
Proof.
  have E := wneg_add (K := K) 0 aE P Q.
  rewrite -!(pt_neg_w rat_sq2) -!(ec_add_w rat_sq2) in E; exact: E.
Qed.

(* n P for n : nat and n : int, by iterated chord-tangent addition
   (the same recipe as [mulQn], [mulQ] of FixedData.v) *)
Definition mulZn (k : nat) (P : pt rat) : pt rat := iter k (ec_add P) None.

Definition mulZ (n : int) (P : pt rat) : pt rat :=
  match n with
  | Posz k => mulZn k P
  | Negz k => pt_neg (mulZn k.+1 P)
  end.

Lemma mulQ_mulZ (D : FixedData) (n : int) : mulQ D n = mulZ n (Some (fd_P0 D)).
Proof. by case: n. Qed.

Lemma mulZn_w k P : mulZn k P = wmuln (K := K) 0 aE P k.
Proof. rewrite /mulZn /wmuln; elim: k => [ | k IHk ] //; rewrite !iterS IHk; exact: ec_add_w. Qed.

Lemma mulZ_w n P : mulZ n P = wmul (K := K) 0 aE P n.
Proof. case: n => k; first exact: mulZn_w. by rewrite /mulZ /wmul mulZn_w (pt_neg_w rat_sq2). Qed.

Section mulZ.

  Variable P : pt rat.
  Hypothesis hP : on_curve_pt P.

  Lemma hPw : won_pt (K := K) 0 aE 0 P.
  Proof. exact: (proj1 (on_curve_pt_w rat_sq2 P) hP). Qed.

  Lemma mulZ_on n : on_curve_pt (mulZ n P).
  Proof. apply/(on_curve_pt_w rat_sq2); rewrite mulZ_w; exact: (wmul_on (two0_QF rat_sq2) hPw). Qed.

  Lemma mulZ_add (n m : int) : mulZ (n + m) P = ec_add (mulZ n P) (mulZ m P).
  Proof.
    rewrite !mulZ_w (ec_add_w rat_sq2).
    exact: (wmul_add (two0_QF rat_sq2) (@nonsing_QF _ rat_sq2) hPw n m).
  Qed.

  Lemma mulZ0 : mulZ 0 P = None. Proof. reflexivity. Qed.

  Lemma mulZ1 : mulZ 1 P = P. Proof. exact: ec_addP0. Qed.

  Lemma mulZS (k : nat) : mulZ k.+1%:Z P = ec_add P (mulZ k%:Z P). Proof. reflexivity. Qed.

  Lemma mulZN1 : mulZ (-1) P = pt_neg P. Proof. by rewrite /mulZ /= ec_addP0. Qed.

End mulZ.

(* the inverse is unique *)
Lemma ec_add_eq0 (A B : pt rat) : on_curve_pt A -> on_curve_pt B -> ec_add A B = None -> A = pt_neg B.
Proof.
  move=> hA hB e.
  have hnB := pt_neg_on rat_sq2 hB.
  by rewrite -(ec_addP0 A) -(ec_addN rat_sq2 B) -(ec_add_assoc rat_sq2 hA hB hnB) e.
Qed.

Lemma mulZ_neg (n : int) (P : pt rat) : on_curve_pt P -> mulZ (- n) P = pt_neg (mulZ n P).
Proof.
  move=> hP; apply: ec_add_eq0; [ exact: mulZ_on | exact: mulZ_on | ].
  by rewrite -mulZ_add // addNr.
Qed.

Lemma mulZ_mul (m n : int) (P : pt rat) : on_curve_pt P -> mulZ (m * n) P = mulZ m (mulZ n P).
Proof.
  move=> hP.
  have Hnat (k : nat) : mulZ (k%:Z * n) P = mulZ k%:Z (mulZ n P).
  { elim: k => [ | k IH ]; first by rewrite mul0r.
    have -> : k.+1%:Z * n = n + k%:Z * n by rewrite -addn1 PoszD mulrDl mul1r addrC.
    by rewrite mulZ_add // IH mulZS. }
  case: m => k; first exact: Hnat.
  rewrite NegzE mulNr mulZ_neg // Hnat -mulZ_neg //; exact: mulZ_on.
Qed.

(** ** Integer combinations of the elements of a list *)

(* R is an integer combination of elements of L: built from O by adding
   and subtracting elements of L *)
Inductive incomb (L : list (pt rat)) : pt rat -> Prop :=
| inc0 : incomb L None
| incA R P : incomb L R -> List.In P L -> incomb L (ec_add R P)
| incS R P : incomb L R -> List.In P L -> incomb L (ec_add R (pt_neg P)).

(* explicit linear combinations  sum_i c_i P_i *)
Definition lincomb (cs : list (int * pt rat)) : pt rat :=
  List.fold_right (fun c acc => ec_add (mulZ c.1 c.2) acc) None cs.

Section incomb.

  Variable L : list (pt rat).
  Hypothesis hL : forall P, List.In P L -> on_curve_pt P.

  Lemma incomb_on A : incomb L A -> on_curve_pt A.
  Proof.
    elim=> [ | R P _ IH hP | R P _ IH hP ]; first exact: I.
    - exact: (ec_add_on rat_sq2 IH (hL hP)).
    - exact: (ec_add_on rat_sq2 IH (pt_neg_on rat_sq2 (hL hP))).
  Qed.

  Lemma incomb_in P : List.In P L -> incomb L P.
  Proof. move=> hP; exact: (incA (inc0 L) hP). Qed.

  Lemma incomb_add A B : incomb L A -> incomb L B -> incomb L (ec_add A B).
  Proof.
    move=> hA; elim=> [ | R P hR IH hP | R P hR IH hP ].
    - by rewrite ec_addP0.
    - rewrite -(ec_add_assoc rat_sq2 (incomb_on hA) (incomb_on hR) (hL hP)); exact: incA IH hP.
    - rewrite -(ec_add_assoc rat_sq2 (incomb_on hA) (incomb_on hR) (pt_neg_on rat_sq2 (hL hP))).
      exact: incS IH hP.
  Qed.

  Lemma incomb_neg A : incomb L A -> incomb L (pt_neg A).
  Proof.
    elim=> [ | R P hR IH hP | R P hR IH hP ].
    - exact: inc0.
    - rewrite pt_neg_add; exact: incS IH hP.
    - rewrite pt_neg_add pt_negK; exact: incA IH hP.
  Qed.

  Lemma incomb_sub A B : incomb L A -> incomb L B -> incomb L (ec_add A (pt_neg B)).
  Proof. move=> hA hB; apply: incomb_add hA (incomb_neg hB). Qed.

  Lemma incomb_mulZ n A : incomb L A -> incomb L (mulZ n A).
  Proof.
    move=> hA.
    have Hn (k : nat) : incomb L (mulZn k A).
    { elim: k => [ | k IH ]; first exact: inc0.
      exact: (incomb_add hA IH). }
    case: n => k; first exact: Hn.
    exact: (incomb_neg (Hn k.+1)).
  Qed.

  Lemma lincomb_incomb (cs : list (int * pt rat)) :
    (forall c, List.In c cs -> List.In c.2 L) -> incomb L (lincomb cs).
  Proof.
    elim: cs => [ | c cs IH ] hc; first exact: inc0.
    apply: incomb_add.
    - apply: incomb_mulZ; apply: incomb_in; apply: hc; left; reflexivity.
    - apply: IH => c' h; apply: hc; right; exact: h.
  Qed.

  Lemma incomb_lincomb A : incomb L A ->
    exists cs : list (int * pt rat), (forall c, List.In c cs -> List.In c.2 L) /\ A = lincomb cs.
  Proof.
    elim=> [ | R P hR [ cs [ hcs E ] ] hP | R P hR [ cs [ hcs E ] ] hP ].
    - exists nil; split; [ move=> c [] | reflexivity ].
    - exists ((1, P) :: cs); split.
      + move=> c [ <- | h ]; [ exact: hP | exact: hcs ].
      + have -> : lincomb ((1, P) :: cs) = ec_add (mulZ 1 P) (lincomb cs) by reflexivity.
        rewrite -E mulZ1 (ec_add_comm rat_sq2 (incomb_on hR) (hL hP)); reflexivity.
    - exists ((-1, P) :: cs); split.
      + move=> c [ <- | h ]; [ exact: hP | exact: hcs ].
      + have -> : lincomb ((-1, P) :: cs) = ec_add (mulZ (-1) P) (lincomb cs) by reflexivity.
        rewrite -E mulZN1 (ec_add_comm rat_sq2 (incomb_on hR) (pt_neg_on rat_sq2 (hL hP))).
        reflexivity.
  Qed.

  Lemma incomb_iff R : incomb L R <->
    exists cs : list (int * pt rat), (forall c, List.In c cs -> List.In c.2 L) /\ R = lincomb cs.
  Proof.
    split; first exact: incomb_lincomb.
    by move=> [ cs [ hcs -> ] ]; apply: lincomb_incomb.
  Qed.

End incomb.

(** * The representatives *)

Lemma reps_on S : List.In S reps -> on_curve_pt S.
Proof.
  have hQ (s b : bool) : on_curve_pt (ec_add (Some Q0) (rep s false b)).
  { apply/on_curve_pt_onc; apply: onc_Q0_add; exact: onc_T. }
  rewrite /reps /E2pts; move=> [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [] ] ] ] ] ] ] ] ].
  - exact: (on_curve_rep false false false).
  - exact: (on_curve_rep true false false).
  - exact: (on_curve_rep false false true).
  - exact: (on_curve_rep true false true).
  - exact: (hQ false false).
  - exact: (hQ true false).
  - exact: (hQ false true).
  - exact: (hQ true true).
Qed.

Lemma None_reps : List.In None reps.
Proof. exact: (rep_in false false false). Qed.

(** * Heights: the constants *)

Fixpoint sumH (l : list (pt rat)) : RF :=
  match l with nil => 0 | T :: l => Ht T + sumH l end.

Lemma sumH_ge0 l : 0 <= sumH l.
Proof.
  elim: l => [ | T l IH ] /=; first exact: lexx.
  have := Ht_ge0 T; lra.
Qed.

Lemma sumH_in S l : List.In S l -> Ht S <= sumH l.
Proof.
  elim: l => [ | T l IH ] //= [ e | h ].
  - rewrite e; have := sumH_ge0 l; lra.
  - have := IH h; have := Ht_ge0 T; lra.
Qed.

(* a bound for the heights of the eight representatives *)
HB.lock Definition MS : RF := sumH reps.

Lemma MS_ge S : List.In S reps -> Ht S <= MS.
Proof. rewrite unlock; exact: sumH_in. Qed.

Lemma MS_ge1 : 1 <= MS.
Proof. have := MS_ge None_reps; rewrite Ht_None; exact. Qed.

HB.lock Definition CC : RF := KD ^+ 2 * KU ^+ 2 * MS ^+ 2.

Lemma CCE : CC = KD ^+ 2 * KU ^+ 2 * MS ^+ 2. Proof. by rewrite unlock. Qed.

Lemma ge1_mul (a b : RF) : 1 <= a -> 1 <= b -> 1 <= a * b.
Proof. move=> ha hb; have := ler_pM ler01 ler01 ha hb; rewrite mulr1; exact. Qed.

Lemma ge1_exp (a : RF) n : 1 <= a -> 1 <= a ^+ n.
Proof. move=> ha; exact: exprn_ege1. Qed.

Lemma CC_ge1 : 1 <= CC.
Proof.
  rewrite CCE; apply: ge1_mul; [ apply: ge1_mul | ]; apply: ge1_exp;
    [ exact: KD_ge1 | exact: KU_ge1 | exact: MS_ge1 ].
Qed.

(* the height bound of the finite part of the generating set *)
HB.lock Definition B0 : nat := RFb (16%:R * CC).

Lemma B0_ge : 16%:R * CC <= B0%:R.
Proof. rewrite B0.unlock; exact: RFb_spec. Qed.

(** * The descent step *)

Lemma le_sq_k (a k : RF) : 1 <= a -> 1 <= k -> a <= k * a ^+ 2.
Proof.
  move=> ha hk; have ha0 := le_trans ler01 ha; rewrite expr2.
  apply: le_trans (ler_peMl ha0 ha) _; exact: (ler_peMl (mulr_ge0 ha0 ha0) hk).
Qed.

Lemma Ht_sub (R S : pt rat) : on_curve_pt R -> on_curve_pt S ->
  R = S \/ R = pt_neg S \/ Ht (ec_add R (pt_neg S)) <= KU ^+ 2 * (Ht R ^+ 2 * Ht S ^+ 2).
Proof.
  have hKU := KU_ge1.
  case: S => [ [ x2 y2 ] | ] hR hS; last first.
  { right; right; rewrite ec_addP0.
    rewrite Ht_None expr1n mulr1; exact: (le_sq_k (Ht_ge1 R) (ge1_exp 2 hKU)). }
  case: R hR => [ [ x1 y1 ] | ] hR; last first.
  { right; right; rewrite ec_add0P Ht_neg Ht_None expr1n mul1r.
    exact: (le_sq_k (Ht_ge1 _) (ge1_exp 2 hKU)). }
  have o1 := proj1 (on_curveE x1 y1) hR; have o2 := proj1 (on_curveE x2 y2) hS.
  case: (eqVneq (x1 : RF) x2) => [ ex | nx ].
  - have e : ((y1 : RF) - y2) * (y1 + y2) = 0.
    { have -> : ((y1 : RF) - y2) * (y1 + y2) = y1 * y1 - y2 * y2 by ring.
      rewrite o1 o2 ex; exact: subrr. }
    move/eqP: e; rewrite mulf_eq0 => /orP [ /eqP e | /eqP e ].
    + left; have ey : (y1 : RF) = y2 by apply/eqP; rewrite -subr_eq0; apply/eqP.
      rewrite ex ey; reflexivity.
    + right; left; have ey : (y1 : RF) = - y2 by apply/eqP; rewrite -addr_eq0; apply/eqP.
      rewrite ex ey; reflexivity.
  - right; right.
    have h := Ht_par hR hS nx (erefl (- (y2 : RF))).
    change (pt_neg (Some (x2, y2))) with (Some (x2, - (y2 : RF))).
    apply: le_trans h.
    exact: (ler_peMl (Ht_ge0 _) (Ht_ge1 _)).
Qed.

Lemma desc_arith (a b s t : RF) : 1 <= a -> 1 <= b -> 1 <= s ->
  b ^+ 4 <= KD ^+ 2 * t -> t <= KU ^+ 2 * (a ^+ 2 * s ^+ 2) -> s <= MS -> 16%:R * CC <= a ->
  2%:R * b <= a.
Proof.
  move=> ha hb hs h1 h2 h3 h4.
  have ha0 := le_trans ler01 ha; have hb0 := le_trans ler01 hb; have hs0 := le_trans ler01 hs.
  have hKD2 : 0 <= KD ^+ 2 := exprn_ge0 2 (le_trans ler01 KD_ge1).
  have hKU2 : 0 <= KU ^+ 2 := exprn_ge0 2 (le_trans ler01 KU_ge1).
  have ha2 : 0 <= a ^+ 2 := exprn_ge0 2 ha0.
  have h5 : b ^+ 4 <= CC * a ^+ 2.
  { apply: le_trans h1 _; rewrite CCE.
    have -> : KD ^+ 2 * KU ^+ 2 * MS ^+ 2 * a ^+ 2 = KD ^+ 2 * (KU ^+ 2 * (a ^+ 2 * MS ^+ 2)) by ring.
    apply: (ler_wpM2l hKD2); apply: le_trans h2 _.
    apply: (ler_wpM2l hKU2); apply: (ler_wpM2l ha2); exact: (lexp 2 hs0 h3). }
  have h6 : 16%:R * CC * a ^+ 2 <= a ^+ 4.
  { apply: le_trans (ler_wpM2r ha2 h4) _.
    have -> : a ^+ 4 = (a * a ^+ 2) * a by ring.
    exact: (ler_peMr (mulr_ge0 ha0 ha2) ha). }
  have h7 : (2%:R * b) ^+ 4 <= a ^+ 4.
  { rewrite exprMn -natrX; apply: le_trans _ h6; rewrite -mulrA.
    exact: (ler_wpM2l (ler0n _ _) h5). }
  have nn1 : (2%:R * b) \is Num.nneg by rewrite nnegrE; exact: (mulr_ge0 (ler0n _ 2) hb0).
  have nn2 : a \is Num.nneg by rewrite nnegrE; exact: ha0.
  move: h7; rewrite (ler_pXn2r (isT : (0 < 4)%N) nn1 nn2); exact.
Qed.

Lemma desc_step (R R2 S : pt rat) : on_curve_pt R2 -> List.In S reps ->
  R = ec_add (ec_add R2 R2) S -> B0%:R < Ht R ->
  R = S \/ R = pt_neg S \/ 2%:R * Ht R2 <= Ht R.
Proof.
  move=> hR2 hSin eR hB.
  have hS := reps_on hSin.
  have h22 := ec_add_on rat_sq2 hR2 hR2.
  have hR : on_curve_pt R by rewrite eR; exact: (ec_add_on rat_sq2 h22 hS).
  case: (Ht_sub hR hS) => [ e | [ e | hb ] ]; [ by left | by right; left | right; right ].
  have E2 : ec_add R (pt_neg S) = ec_add R2 R2.
  { rewrite {1}eR (ec_add_assoc rat_sq2 h22 hS (pt_neg_on rat_sq2 hS)) (ec_addN rat_sq2 S).
    exact: ec_addP0. }
  rewrite E2 in hb.
  apply: (desc_arith (Ht_ge1 R) (Ht_ge1 R2) (Ht_ge1 S) (Ht_dbl hR2) hb (MS_ge hSin)).
  exact: (le_trans B0_ge (ltW hB)).
Qed.

Definition Lgen : list (pt rat) := List.app reps (candP B0).

Lemma Lgen_on P : List.In P Lgen -> on_curve_pt P.
Proof.
  move=> h; case: (List.in_app_or _ _ _ h) => h'; first exact: (reps_on h').
  apply: (candP_on (X := B0)).
  move: h'; elim: (candP B0) => [ | a s IH ] //= [ <- | h' ].
  - by rewrite in_cons eqxx.
  - by rewrite in_cons (IH h') orbT.
Qed.

Lemma reps_Lgen S : List.In S reps -> List.In S Lgen.
Proof. move=> h; exact: (List.in_or_app reps (candP B0) S (or_introl h)). Qed.

Lemma base_case R : on_curve_pt R -> Ht R <= B0%:R -> incomb Lgen R.
Proof.
  case: R => [ p | ] hR hH; last exact: inc0.
  have hN : Some p <> None by discriminate.
  have hm := candP_spec hR hH hN.
  have hi := mem_In hm.
  apply: incomb_in.
  exact: (List.in_or_app reps (candP B0) _ (or_intror hi)).
Qed.

Lemma desc_case R : on_curve_pt R ->
  (forall R2, on_curve_pt R2 -> 2%:R * Ht R2 <= Ht R -> incomb Lgen R2) -> incomb Lgen R.
Proof.
  move=> hR IH.
  case: (lerP (Ht R) B0%:R) => hB; first exact: base_case.
  have [ R2 [ S [ hR2 [ hSin eR ] ] ] ] := weak_MW hR.
  case: (desc_step hR2 hSin eR hB) => [ e | [ e | h ] ].
  - rewrite e; exact: (incomb_in (reps_Lgen hSin)).
  - rewrite e; exact: (incomb_neg (incomb_in (reps_Lgen hSin))).
  - rewrite eR; have c2 := IH R2 hR2 h.
    apply: (incomb_add Lgen_on (incomb_add Lgen_on c2 c2)).
    exact: (incomb_in (reps_Lgen hSin)).
Qed.

Lemma incomb_Lgen_k (k : nat) R : on_curve_pt R -> Ht R <= 2%:R ^+ k -> incomb Lgen R.
Proof.
  elim: k R => [ | k IH ] R hR hk; apply: (desc_case hR) => R2 hR2 h.
  - exfalso; have := Ht_ge1 R2; move: hk; rewrite expr0 => hk; lra.
  - apply: (IH R2 hR2); move: hk; rewrite exprS => hk; lra.
Qed.
Theorem incomb_Lgen R : on_curve_pt R -> incomb Lgen R.
Proof. move=> hR; exact: (incomb_Lgen_k hR (RFb_pow2 (Ht R))). Qed.

(** ** Main results *)

(* E(F) is finitely generated: every point is an integer combination
   sum_i c_i P_i of the elements of a finite list L of points of E(F) *)
Theorem EF_fingen : exists L : list (pt rat),
  (forall P, List.In P L -> on_curve_pt P) /\
  forall R, on_curve_pt R -> exists cs : list (int * pt rat),
    (forall c, List.In c cs -> List.In c.2 L) /\ R = lincomb cs.
Proof.
  exists Lgen; split; first exact: Lgen_on.
  move=> R hR; exact: (incomb_lincomb Lgen_on (incomb_Lgen hR)).
Qed.

(* the subgroup generated by L is E(F) *)
Theorem EF_fingen_subgroup : exists L : list (pt rat),
  (forall P, List.In P L -> on_curve_pt P) /\ forall R, on_curve_pt R <-> incomb L R.
Proof.
  exists Lgen; split; first exact: Lgen_on.
  move=> R; split; [ exact: incomb_Lgen | move=> h; exact: (incomb_on Lgen_on h) ].
Qed.

(* the same, with the eight representatives of E(F)/2E(F) in L *)
Theorem EF_fingen_reps : exists L : list (pt rat),
  (forall P, List.In P L -> on_curve_pt P) /\ (forall S, List.In S reps -> List.In S L) /\
  forall R, on_curve_pt R <-> incomb L R.
Proof.
  exists Lgen; split; first exact: Lgen_on. split; first exact: reps_Lgen.
  move=> R; split; [ exact: incomb_Lgen | move=> h; exact: (incomb_on Lgen_on h) ].
Qed.

