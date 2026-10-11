(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* PLAN P14b-iv-B (Phase 2E): an abstract generator of E(F).

   1. [EF]: the points of E(F), F = Q(sqrt2), as a MathComp [zmodType]
      (subtype of [pt rat] by the boolean curve equation [oncb]; zero
      O = None, addition [ec_add], opposite [pt_neg]; the laws from
      GroupLaw.v). [val_mulrz]: val (x *~ n) = mulZ n (val x).
   2. [EF_structure]: by FGAbelian.fg_rank_one with
      L := the finite generating list of FinGen.EF_fingen_reps,
      R := the eight representatives rep s e b (Descent.v),
      T := E2pts (Torsion.v): there is G with ~ tors G and
      every point a = n G + t, t in E[2].
   3. [generator_thm : generator_stmt] (DataG.v), [rank_one_thm] and
      [inputs_to_data_final].

   Assumptions: [classic] only (from FGAbelian.v). *)

From Stdlib Require Import List.

From HB Require Import structures.
From mathcomp Require Import boot order algebra.

From Undecidability.H10.Rational
  Require Import FixedData GroupLaw Descent FinGen Torsion FGAbelian.
From Undecidability.H10.Rational
  Require Import Signature PaperInputs DataG.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.

Local Open Scope ring_scope.

(** * 0. The two definitions of integer multiples agree *)

Lemma mulZ_FinGen_Torsion (n : int) (P : pt rat) : FinGen.mulZ n P = Torsion.mulZ n P.
Proof. reflexivity. Qed.

Lemma mulG_mulZ (P0 : qe rat * qe rat) (n : int) : mulG P0 n = mulZ n (Some P0).
Proof. by case: n. Qed.

(** * 1. The group E(F) as a zmodType *)

Definition oncb (P : pt rat) : bool :=
  if P is Some p then p.2 * p.2 == p.1 ^+ 3 + aE * p.1 else true.

Lemma oncbP (P : pt rat) : reflect (on_curve_pt P) (oncb P).
Proof. case: P => [ p | ]; [ exact: eqP | exact: ReflectT ]. Qed.

Definition EF : Type := {P : pt rat | oncb P}.

HB.instance Definition _ := Choice.on EF.

Implicit Types (x y z : EF).

Lemma EF_on x : on_curve_pt (val x).
Proof. exact: (elimT (oncbP _) (valP x)). Qed.

Definition EF0 : EF := exist _ None isT.

Definition EFadd x y : EF :=
  exist _ (ec_add (val x) (val y)) (introT (oncbP _) (ec_add_on rat_sq2 (EF_on x) (EF_on y))).

Definition EFopp x : EF :=
  exist _ (pt_neg (val x)) (introT (oncbP _) (pt_neg_on rat_sq2 (EF_on x))).

Fact EFaddA : associative EFadd.
Proof. move=> x y z; apply: val_inj; exact: (esym (ec_add_assoc rat_sq2 (EF_on x) (EF_on y) (EF_on z))). Qed.

Fact EFaddC : commutative EFadd.
Proof. move=> x y; apply: val_inj; exact: (ec_add_comm rat_sq2 (EF_on x) (EF_on y)). Qed.

Fact EFadd0 : left_id EF0 EFadd.
Proof. move=> x; apply: val_inj; exact: ec_add0P. Qed.

Fact EFaddN : left_inverse EF0 EFopp EFadd.
Proof.
  move=> x; apply: val_inj.
  change (ec_add (pt_neg (val x)) (val x) = None).
  rewrite (ec_add_comm rat_sq2 (pt_neg_on rat_sq2 (EF_on x)) (EF_on x)).
  exact: (ec_addN rat_sq2).
Qed.

HB.instance Definition _ := GRing.isZmodule.Build EF EFaddA EFaddC EFadd0 EFaddN.

Lemma val0 : val (0 : EF) = None. Proof. reflexivity. Qed.
Lemma valD x y : val (x + y) = ec_add (val x) (val y). Proof. reflexivity. Qed.
Lemma valN x : val (- x) = pt_neg (val x). Proof. reflexivity. Qed.

Lemma val_mulrn x (k : nat) : val (x *+ k) = mulZn k (val x).
Proof.
  elim: k => [ | k IH ]; first reflexivity.
  by rewrite mulrS valD IH.
Qed.

Lemma val_mulrz x (n : int) : val (x *~ n) = mulZ n (val x).
Proof.
  case: n => k; first exact: val_mulrn.
  by rewrite NegzE mulrNz valN -pmulrn val_mulrn.
Qed.

Lemma val_mulrz2 x : val (x *~ 2) = ec_add (val x) (val x).
Proof. by rewrite val_mulrz (mulZ2 (EF_on x)). Qed.

Lemma val_eq0 x : val x = None -> x = 0.
Proof. by move=> e; apply: val_inj. Qed.

(* points of the curve as elements of EF *)
Definition toEF (P : pt rat) : EF := insubd (0 : EF) P.

Lemma toEFK (P : pt rat) : on_curve_pt P -> val (toEF P) = P.
Proof. by move=> h; rewrite /toEF insubdK //; apply/oncbP. Qed.

Lemma valK' x : toEF (val x) = x.
Proof. by apply: val_inj; rewrite toEFK //; exact: EF_on. Qed.

(** ** Torsion *)

Lemma tors_torsion x : tors x <-> torsion_pt (val x).
Proof.
  split.
  - move=> [ n [ n0 e ] ]; split; first exact: EF_on.
    by exists n; split; [ exact/eqP | rewrite -val_mulrz e ].
  - move=> [ _ [ n [ n0 e ] ] ]; exists n; split; first exact/eqP.
    by apply: val_eq0; rewrite val_mulrz.
Qed.

(** * 2. The structure of E(F) *)

(** ** Finite generation *)

Section lcomb_span.

  Variable A : zmodType.

  Definition inlc (L : seq A) (a : A) : Prop := exists c, a = lcomb c L.

  Lemma inlc_mem (L : seq A) a : List.In a L -> inlc L a.
  Proof.
    elim: L a => [ | x L' IH ] a //= [ <- | h ].
    - exists (fun i => if i is 0%N then 1 else 0); rewrite /=.
      by rewrite (lcomb0 L') mulr1z addr0.
    - have [ c -> ] := IH a h; exists (fun i => if i is j.+1 then c j else 0).
      by rewrite /= mulr0z add0r.
  Qed.

  Lemma inlc0 (L : seq A) : inlc L 0.
  Proof. by exists (fun _ => 0); rewrite lcomb0. Qed.

  Lemma inlcD (L : seq A) a b : inlc L a -> inlc L b -> inlc L (a + b).
  Proof. by move=> [ c -> ] [ d -> ]; exists (fun i => c i + d i); rewrite lcombD. Qed.

  Lemma inlcN (L : seq A) a : inlc L a -> inlc L (- a).
  Proof. by move=> [ c -> ]; exists (fun i => - c i); rewrite lcombN. Qed.

End lcomb_span.

Lemma In_map_toEF (L : list (pt rat)) P : List.In P L -> List.In (toEF P) (List.map toEF L).
Proof. exact: List.in_map. Qed.

Lemma EF_fingen_lcomb : exists L : seq EF, fingen L.
Proof.
  have [ L [ hL [ _ hinc ] ] ] := EF_fingen_reps.
  exists (List.map toEF L).
  have key : forall R, incomb L R -> on_curve_pt R -> inlc (List.map toEF L) (toEF R).
  { move=> R; elim=> [ | R' P hR' IH hP | R' P hR' IH hP ] hR.
    - have -> : toEF None = 0 by apply: val_inj; rewrite toEFK.
      exact: inlc0.
    - have hR'on := incomb_on hL hR'.
      have -> : toEF (ec_add R' P) = toEF R' + toEF P.
      { by apply: val_inj; rewrite valD !toEFK //; exact: hL. }
      apply: inlcD; first exact: IH.
      exact: (inlc_mem (In_map_toEF hP)).
    - have hR'on := incomb_on hL hR'.
      have -> : toEF (ec_add R' (pt_neg P)) = toEF R' - toEF P.
      { by apply: val_inj; rewrite valD valN !toEFK //; exact: hL. }
      apply: inlcD; first exact: IH.
      exact: (inlcN (inlc_mem (In_map_toEF hP))). }
  move=> a; rewrite -(valK' a); apply: key; last exact: EF_on.
  exact: (proj1 (hinc _) (EF_on a)).
Qed.

(** ** The representatives of E(F)/2E(F) *)

Lemma rep_inj s e b s' e' b' : rep s e b = rep s' e' b' -> (s, e, b) = (s', e', b').
Proof.
  move=> E.
  have [ -> [ -> -> ] ] := reps_distinct_mod2 (R2 := None) I E.
  reflexivity.
Qed.

Definition trip8 : seq (bool * bool * bool) :=
  [:: (false, false, false); (false, false, true); (false, true, false); (false, true, true);
      (true, false, false); (true, false, true); (true, true, false); (true, true, true)].

Definition R8 : seq EF := [seq toEF (rep p.1.1 p.1.2 p.2) | p <- trip8].

Lemma toEF_rep_inj : injective (fun p : bool * bool * bool => toEF (rep p.1.1 p.1.2 p.2)).
Proof.
  move=> [ [ s e ] b ] [ [ s' e' ] b' ] /(congr1 val); cbn [fst snd].
  rewrite !toEFK; [ exact: on_curve_rep | exact: on_curve_rep | exact: rep_inj ].
Qed.

Lemma mem_R8 s e b : toEF (rep s e b) \in R8.
Proof.
  apply: (map_f (fun p : bool * bool * bool => toEF (rep p.1.1 p.1.2 p.2)) (x := (s, e, b))).
  by case: s; case: e; case: b.
Qed.

Lemma R8_cosets : two_cosets R8.
Proof.
  split.
  - by rewrite map_inj_uniq //; exact: toEF_rep_inj.
  - by rewrite size_map.
  - move=> a; have [ R2 [ s [ e [ b [ hR2 E ] ] ] ] ] := weak_MW_rep (EF_on a).
    exists (toEF R2), (toEF (rep s e b)); split; first exact: mem_R8.
    apply: val_inj; rewrite valD val_mulrz2 !toEFK //; exact: on_curve_rep.
Qed.

(** ** The torsion subgroup *)

Definition P4 : seq (bool * bool) := [:: (false, false); (true, false); (false, true); (true, true)].

Definition T4 : seq EF := [seq toEF (rep p.1 false p.2) | p <- P4].

Lemma rep_E2 s b : List.In (rep s false b) E2pts.
Proof. case: s; case: b; rewrite /E2pts /=; tauto. Qed.

Lemma toEF_rep2_inj : injective (fun p : bool * bool => toEF (rep p.1 false p.2)).
Proof.
  move=> [ s b ] [ s' b' ] /(congr1 val); cbn [fst snd].
  rewrite !toEFK; [ exact: on_curve_rep | exact: on_curve_rep | ].
  move=> /rep_inj [ -> -> ]; reflexivity.
Qed.

Lemma memT4 x : x \in T4 <-> List.In (val x) E2pts.
Proof.
  split.
  - move=> /mapP [ [ s b ] _ -> ]; cbn [fst snd].
    rewrite (toEFK (on_curve_rep _ _ _)); exact: rep_E2.
  - move=> h; rewrite -(valK' x); move: h; rewrite /E2pts /=.
    case=> [ <- | [ <- | [ <- | [ <- | [] ] ] ] ]; apply/mapP.
    + by exists (false, false); [ | reflexivity ].
    + by exists (true, false); [ | reflexivity ].
    + by exists (false, true); [ | reflexivity ].
    + by exists (true, true); [ | reflexivity ].
Qed.

Lemma T4_V4 : tors_V4 T4.
Proof.
  split.
  - by rewrite map_inj_uniq //; exact: toEF_rep2_inj.
  - by rewrite size_map.
  - move=> t /memT4 ht; apply: val_eq0; rewrite val_mulrz2; exact: E2pts_torsion.
  - move=> a /tors_torsion ha; apply/memT4; exact: torsion_E2.
  - move=> a /memT4; rewrite val_mulrz2 => h; apply/memT4; exact: (no_4_torsion (EF_on a)).
Qed.

(** ** The structure theorem *)

Theorem EF_structure : exists G : EF, ~ tors G /\
  forall a : EF, exists (n : int) t, t \in T4 /\ a = G *~ n + t.
Proof.
  have [ L hL ] := EF_fingen_lcomb.
  exact: (fg_rank_one hL R8_cosets T4_V4).
Qed.

(** * 3. The generator statement *)

Theorem generator_thm : generator_stmt.
Proof.
  have [ G [ nG hG ] ] := EF_structure.
  case EG : (val G) => [ G0 | ]; last first.
  { exfalso; apply: nG; rewrite (val_eq0 EG); exact: tors0. }
  have hG0 : on_curve G0 by have := EF_on G; rewrite EG.
  exists G0; split; first exact: hG0.
  have mulG_val : forall n : int, mulG G0 n = val (G *~ n).
  { by move=> n; rewrite mulG_mulZ val_mulrz EG. }
  split.
  - move=> n n0 e; apply: nG; exists n; split; first exact: n0.
    apply: val_eq0; rewrite -mulG_val; exact: e.
  - move=> Q1 Q2 hQ1 hadd.
    have e2 : Some Q2 = ec_add (Some Q1) (Some Q1) := proj1 (@ADDrel_iff rat rat_sq2 (Some Q1) (Some Q1) (Some Q2) hQ1 hQ1) hadd.
    have [ n [ t [ tT ea ] ] ] := hG (toEF (Some Q1)).
    exists n; rewrite mulG_val e2.
    have t2 : t *~ 2 = 0.
    { case: T4_V4 => _ _ h _ _; exact: h. }
    have -> : G *~ (n * (2%N)%:Z) = toEF (Some Q1) *~ 2.
    { by rewrite ea mulrzDl t2 addr0 mulrzA. }
    by rewrite val_mulrz2 toEFK.
Qed.

Theorem rank_one_thm : forall (C : i4 -> rat) (S : seq nat) (Hb c : nat) (Kset : seq nat) (Nh Ch : nat),
  exists P0, on_curve P0 /\ nontorsion P0 /\ O_rank_stmt (mkDataG P0 C S Hb c Kset Nh Ch).
Proof.
  move=> C S Hb c Kset Nh Ch.
  have [ G [ hG [ hnt hr ] ] ] := generator_thm.
  exists G; split; first exact: hG.
  split; first exact: hnt.
  exact: O_rank_of_rank_one.
Qed.

Theorem inputs_to_data_final : HeightThm -> PrimePattern -> PP1_L0 ->
  exists D : FixedData, FixedWF D /\ StdHyps D /\ OrdHyps D /\ hei_enlarge_ord D.
Proof. exact: (inputs_to_dataG generator_thm). Qed.

(* Print Assumptions inputs_to_data_final.  ==>  Axioms: classic *)
