(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* PLAN P14b-ii (Phase 2E): the torsion subgroup of E(F), F = Q(sqrt2),
   E : y^2 = x^3 + aE x, is exactly E[2] = {O, (0,0), (d,0), (-d,0)}.

   Main results:
   - [mulZ], [mulZ_add]: integer multiples n P by iterated [ec_add], with
     the same recursion as FixedData.mulQ (in fact [mulZ n (Some p)] is
     convertible to [mulQ (dataP p) n], [mulZ_mulQ]);
   - [torsion_E2]: a torsion point lies in E2pts;
   - [E2pts_torsion]: the points of E2pts satisfy 2T = O;
   - [no_4_torsion]: 2R in E[2] implies R in E[2].

   ROUTE.
   1. Two places above 17: v = ovP (wsplit 17 6 +) (sqrt2 |-> 6) and its
      conjugate (sqrt2 |-> -6 = 11). By HCov.kernel_countF (reduction is a
      homomorphism + Lagrange in E(F_17)) and ExplicitData.countF17,
      20 P is in the kernel of reduction at v and 16 P at the conjugate.
   2. The kernel is torsion free (KernelReduction.nontorsion_of_kernel, via
      kernel_mul); so for a torsion point P, 20 P = O and 16 P = O, hence
      4 P = 16 P * 4 - 20 P * 3 = O.
   3. 2-torsion: 2R = O iff y(R) = 0 iff R in E2pts.
   4. No 4-torsion: if 2R = T in E[2], then T = 2R + O, so by
      Descent.reps_distinct_mod2 (the connecting map alpha separates the
      classes of E[2] modulo 2E(F); it uses that -1, d, -d are not squares
      in F) T = O.

   Assumptions: none (Print Assumptions torsion_E2 is closed). *)

From Stdlib Require Import ZArith Lia List.

From HB Require Import structures.
From mathcomp Require Import boot order algebra.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData ExplicitData
                 RatVal OrdinaryFacts OrdPlaces OrdBridges GroupLaw
                 KernelReduction HCov Descent.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.

Local Open Scope ring_scope.

Local Abbreviation KQ := (@QF rat rat_sq2).

(** * 1. Integer multiples of an arbitrary point *)

Definition mulZn (k : nat) (P : pt rat) : pt rat := iter k (ec_add P) None.

Definition mulZ (n : int) (P : pt rat) : pt rat :=
  match n with
  | Posz k => mulZn k P
  | Negz k => pt_neg (mulZn k.+1 P)
  end.

(* a FixedData record with base point p (all other fields are dummies) *)
Definition dataP (p : qe rat * qe rat) : FixedData :=
  {| fd_m := 0; fd_P0 := p; fd_C := fun _ => 0; fd_S := [::]; fd_Hb := 0; fd_c := 0;
     fd_Kset := [::]; fd_SE := [::]; fd_PhiL := [::]; fd_Nh := 0; fd_Ch := 0 |}.

Lemma mulZ_mulQ (p : qe rat * qe rat) (n : int) : mulZ n (Some p) = mulQ (dataP p) n.
Proof. by []. Qed.

Lemma mulZ_mulQD (D : FixedData) (n : int) : mulZ n (Some (fd_P0 D)) = mulQ D n.
Proof. by []. Qed.

Lemma mulZn_None (k : nat) : mulZn k None = None.
Proof. by elim: k => [ | k IH ] //; rewrite /mulZn iterS -/(mulZn k None) IH. Qed.

Lemma mulZ_None (n : int) : mulZ n None = None.
Proof. by case: n => k; rewrite /= mulZn_None. Qed.

Theorem mulZ_on (n : int) (P : pt rat) : on_curve_pt P -> on_curve_pt (mulZ n P).
Proof.
  case: P => [ p | ] hP; last by rewrite mulZ_None.
  rewrite mulZ_mulQ; exact: (mulQ_on (D := dataP p) hP).
Qed.

Theorem mulZ_add (n m : int) (P : pt rat) : on_curve_pt P ->
  mulZ (n + m) P = ec_add (mulZ n P) (mulZ m P).
Proof.
  case: P => [ p | ] hP; last by rewrite !mulZ_None.
  rewrite !mulZ_mulQ; exact: (mulQ_add (D := dataP p) hP).
Qed.

Lemma mulZ0 (P : pt rat) : mulZ 0 P = None.
Proof. by []. Qed.

Lemma mulZ1 (P : pt rat) : mulZ 1 P = P.
Proof. exact: ec_addP0. Qed.

Lemma mulZ_neg (n : int) (P : pt rat) : mulZ (- n) P = pt_neg (mulZ n P).
Proof.
  case: P => [ p | ]; last by rewrite !mulZ_None.
  rewrite !mulZ_mulQ; exact: mulQ_neg.
Qed.

Lemma mulZ2 (P : pt rat) : on_curve_pt P -> mulZ 2 P = ec_add P P.
Proof. move=> hP; rewrite (mulZ_add 1 1 hP) mulZ1; by []. Qed.

(* nP = O implies (n k) P = O *)
Lemma mulZ_none_mul (n : int) (P : pt rat) : on_curve_pt P -> mulZ n P = None ->
  forall k : int, mulZ (n * k) P = None.
Proof.
  move=> hP Hn.
  have Hnat : forall j : nat, mulZ (n * j%:Z) P = None.
  { elim=> [ | j IH ]; first by rewrite mulr0.
    by rewrite -addn1 PoszD mulrDr mulr1 (mulZ_add _ _ hP) IH Hn. }
  case=> j; first exact: Hnat.
  by rewrite NegzE mulrN mulZ_neg Hnat.
Qed.

(** * 2. The two places above 17 and the kernel of reduction *)

Definition tors_pt (P : pt rat) : Prop := exists n : int, n <> 0 /\ mulZ n P = None.

Definition torsion_pt (P : pt rat) : Prop :=
  on_curve_pt P /\ exists n : int, n <> 0 /\ mulZ n P = None.

Lemma prime17' : prime 17. Proof. by []. Qed.
Lemma n17_2 : 17%N != 2%N. Proof. by []. Qed.
Lemma n17_7 : 17%N != 7%N. Proof. by []. Qed.

(* if N P lies in the kernel of reduction at a place above 17, and P is torsion,
   then N P = O *)
Lemma kern_torsion (v : qe rat -> int) (p : qe rat * qe rat) (N : int) :
  is_place_above v 17 -> on_curve p -> HCov.kern v (mulQ (dataP p) N) ->
  tors_pt (Some p) -> mulQ (dataP p) N = None.
Proof.
  move=> Hv hP Hk [ n [ Hn Hnone ] ].
  case E : (mulQ (dataP p) N) Hk => [ [ x y ] | ] Hk; last by [].
  exfalso; case: Hk => Hx Hvx.
  have Hn' : n != 0 by apply/eqP.
  have mon : forall D : FixedData, on_curve (fd_P0 D) -> forall n : int, onp (mulQ D n).
  { move=> D hD m; exact: (mulQ_on hD m). }
  have madd : forall D : FixedData, on_curve (fd_P0 D) ->
      forall n n' : int, mulQ D (n + n') = ec_add (mulQ D n) (mulQ D n').
  { move=> D hD m m'; exact: (mulQ_add hD m m'). }
  exact: (nontorsion_of_kernel mon madd (D := dataP p) hP prime17' Hv E Hx Hvx Hn' Hnone).
Qed.

Lemma B6_root : exists wB : int, (6 : int) ^+ 2 - 2 = (17%N)%:Z * wB.
Proof. by exists 2. Qed.

Local Abbreviation v17 := (ovP (wsplit 17 6 sg_p)).

Lemma v17_place : is_place_above v17 17.
Proof. exact: (wsplit_place prime17' n17_2 B6_root sg_p). Qed.

Lemma v17_root : 1 <= v17 (tcq (sgnz sg_p * 6)).
Proof. exact: (wsplit_root prime17' n17_2 B6_root sg_p). Qed.

Lemma c17_root : ((17%N)%:Z %| (sgnz sg_p * 6) ^+ 2 - 2)%Z.
Proof. exact: (c_root_of B6_root sg_p). Qed.

Lemma v17c_place : is_place_above (fun x => v17 (qe_conj x)) 17.
Proof. exact: (conj_place v17_place). Qed.

Lemma conj_root (v : qe rat -> int) (r : nat) (c : int) : is_place_above v r ->
  1 <= v (tcq c) -> 1 <= (fun x => v (qe_conj x)) (tcq (- c)).
Proof. move=> Hv H; by rewrite /= conj_tcq (vbN Hv) ?tcq_neq0. Qed.

Lemma v17c_root : 1 <= (fun x => v17 (qe_conj x)) (tcq (- (sgnz sg_p * 6))).
Proof. exact: (conj_root v17_place v17_root). Qed.

Lemma c17c_root : ((17%N)%:Z %| (- (sgnz sg_p * 6)) ^+ 2 - 2)%Z.
Proof. by rewrite sqrrN; exact: c17_root. Qed.

Lemma count20 : countF (Z.of_nat 17) (aEmod (Z.of_nat 17) (int_to_Z (sgnz sg_p * 6))) = 20%N.
Proof.
  have -> : aEmod (Z.of_nat 17) (int_to_Z (sgnz sg_p * 6)) = aEmod 17 6 by vm_compute.
  exact: (proj1 countF17).
Qed.

Lemma count16 : countF (Z.of_nat 17) (aEmod (Z.of_nat 17) (int_to_Z (- (sgnz sg_p * 6)))) = 16%N.
Proof.
  have -> : aEmod (Z.of_nat 17) (int_to_Z (- (sgnz sg_p * 6))) = aEmod 17 11 by vm_compute.
  exact: (proj2 countF17).
Qed.

Lemma torsion_20 (p : qe rat * qe rat) : on_curve p -> tors_pt (Some p) ->
  mulQ (dataP p) 20 = None.
Proof.
  move=> hP Ht; apply: (kern_torsion v17_place hP _ Ht).
  apply: (kernel_countF (D := dataP p) prime17' n17_2 n17_7 v17_place c17_root v17_root hP).
  by rewrite count20.
Qed.

Lemma torsion_16 (p : qe rat * qe rat) : on_curve p -> tors_pt (Some p) ->
  mulQ (dataP p) 16 = None.
Proof.
  move=> hP Ht; apply: (kern_torsion v17c_place hP _ Ht).
  apply: (kernel_countF (D := dataP p) prime17' n17_2 n17_7 v17c_place c17c_root v17c_root hP).
  by rewrite count16.
Qed.

(* every torsion point is killed by 4 *)
Theorem torsion_4 (P : pt rat) : torsion_pt P -> mulZ 4 P = None.
Proof.
  case: P => [ p | ] [ hP Ht ]; last by rewrite mulZ_None.
  have H20 : mulZ 20 (Some p) = None by rewrite mulZ_mulQ; exact: torsion_20.
  have H16 : mulZ 16 (Some p) = None by rewrite mulZ_mulQ; exact: torsion_16.
  have -> : (4 : int) = 20 * (- 3) + 16 * 4 by [].
  by rewrite (mulZ_add _ _ hP) (mulZ_none_mul hP H20) (mulZ_none_mul hP H16).
Qed.

(** * 3. The 2-torsion *)

Lemma two_torsion (R : pt rat) : on_curve_pt R -> ec_add R R = None -> List.In R E2pts.
Proof.
  case: R => [ [ x y ] | ] hR; last by left.
  move/on_curve_pt_onc: hR; rewrite /oncP /onc /= => hR.
  rewrite /ec_add eqxx.
  case: (eqVneq y (- y)) => [ Ey | _ ] //= _.
  have y0 : y = 0 :> KQ.
  { have H : (2%:R : KQ) * y = 0 by rewrite mulr_natl mulr2n {2}Ey subrr.
    by move/eqP: H; rewrite mulf_eq0 (negbTE two_neq0K) /= => /eqP. }
  rewrite aE_dK in hR.
  have E : (x : KQ) * ((x - dK) * (x + dK)) = 0.
  { have -> : (x : KQ) * ((x - dK) * (x + dK)) = x ^+ 3 + - (dK * dK) * x by ring.
    by rewrite -hR y0 expr2 mulr0. }
  rewrite /E2pts /T0 /Td /Tmd /= y0.
  move/eqP: E; rewrite !mulf_eq0 => /orP [ /eqP -> | /orP [ E | E ] ]; first by right; left.
  - by right; right; left; rewrite subr_eq0 in E; rewrite (eqP E).
  - by right; right; right; left; rewrite addr_eq0 in E; rewrite (eqP E).
Qed.

Theorem E2pts_torsion (P : pt rat) : List.In P E2pts -> ec_add P P = None.
Proof.
  rewrite /E2pts /=.
  case=> [ <- | [ <- | [ <- | [ <- | [] ] ] ] ] //; rewrite /T0 /Td /Tmd /ec_add eqxx oppr0 eqxx //.
Qed.

Lemma E2pts_on (P : pt rat) : List.In P E2pts -> on_curve_pt P.
Proof.
  rewrite /E2pts /=.
  case=> [ <- | [ <- | [ <- | [ <- | [] ] ] ] ];
    [ exact: I | exact: (on_curve_rep true false false)
    | exact: (on_curve_rep false false true) | exact: (on_curve_rep true false true) ].
Qed.

(** * 4. No F-rational 4-torsion *)

Theorem no_4_torsion (R : pt rat) : on_curve_pt R ->
  List.In (ec_add R R) E2pts -> List.In R E2pts.
Proof.
  move=> hR HT; apply: (two_torsion hR).
  have [ s [ b Es ] ] : exists s b, ec_add R R = rep s false b.
  { move: HT; rewrite /E2pts /=.
    case=> [ E | [ E | [ E | [ E | [] ] ] ] ].
    - by exists false, false.
    - by exists true, false.
    - by exists false, true.
    - by exists true, true. }
  have E : rep s false b = ec_add (ec_add R R) (rep false false false).
  { by rewrite ec_addP0 Es. }
  case: (reps_distinct_mod2 hR E) => Hs [ _ Hb ].
  by rewrite Es Hs Hb.
Qed.

(** * 5. Torsion = E[2] *)

Theorem torsion_E2 (P : pt rat) : torsion_pt P -> List.In P E2pts.
Proof.
  move=> HP; have hP := proj1 HP.
  have H4 := torsion_4 HP.
  have h2 : on_curve_pt (ec_add P P) := ec_add_on rat_sq2 hP hP.
  apply: (no_4_torsion hP); apply: (two_torsion h2).
  rewrite -(mulZ2 hP) -(mulZ_add _ _ hP); exact: H4.
Qed.

Theorem E2pts_torsion_pt (P : pt rat) : List.In P E2pts -> torsion_pt P.
Proof.
  move=> HP; split; first exact: E2pts_on.
  exists 2; split => //; rewrite (mulZ2 (E2pts_on HP)); exact: E2pts_torsion.
Qed.

Corollary torsion_iff (P : pt rat) : torsion_pt P <-> List.In P E2pts.
Proof. split; [ exact: torsion_E2 | exact: E2pts_torsion_pt ]. Qed.
