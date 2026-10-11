(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* PLAN P20a: the total index function [idx_ord D] consumed by
   CompactnessT.CompactnessT_StdHyps.

   [idx_ord D X] is the index n with  mulP D n = Some X  (i.e. X = n P),
   found by bounded search: by the canonical-height lower bound O_HL
   (OrdHyps), |n|^2 <= Nh (htb x0 + htb x1 + htb 1 + Ch) for x = x0 + x1 sqrt2;
   the first n in [0..B] ++ [0,-1..-B] with mulP D n == Some X is returned
   (default 0). By nontorsion (E2) and the group law (GroupLaw.mulQ_add)
   n |-> mulP D n is injective, so the search returns the right index.
   On points that are not multiples of P the value is junk.

   Assumptions: none (closed). *)

From HB Require Import structures.
From mathcomp Require Import boot order algebra.

From Undecidability.H10.Rational
  Require Import FixedData GroupLaw.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section idx_ord.

  Variable D : FixedData.

  (* the search bound for X = (x, y) *)
  Definition idx_bound (X : qe rat * qe rat) : nat :=
    (fd_Nh D * (htb (qre X.1) + htb (qim X.1) + htb 1 + fd_Ch D))%N.

  (* the candidate indices  0, ..., B, 0, -1, ..., -B *)
  Definition idx_cands (B : nat) : seq int :=
    [seq Posz k | k <- iota 0 B.+1] ++ [seq - Posz k | k <- iota 0 B.+1].

  Definition idx_ord (X : qe rat * qe rat) : int :=
    let l := idx_cands (idx_bound X) in
    nth 0 l (find (fun n => mulP D n == Some X) l).

  Lemma idx_cands_mem (B : nat) (n : int) : (absz n <= B)%N -> n \in idx_cands B.
  Proof.
    move=> Hn; rewrite mem_cat; apply/orP.
    case: n Hn => k Hk.
    - by left; apply/mapP; exists k => //; rewrite mem_iota add0n ltnS.
    - right; apply/mapP; exists k.+1; first by rewrite mem_iota add0n ltnS.
      by rewrite NegzE.
  Qed.

  Hypothesis HWF : FixedWF D.
  Hypothesis HS : StdHyps D.
  Hypothesis HO : OrdHyps D.

  Lemma P0_on_curve : on_curve (fd_P0 D).
  Proof using HS.
    have [x [y [Hxy [_ [_ Hon]]]]] := E2 HS (n := 1) isT.
    move: Hxy; rewrite /mulQ /mulQn /=; case: (fd_P0 D) => a b /=.
    by case=> -> ->.
  Qed.

  (* n |-> n P0 is injective (E2: nontorsion) *)
  Lemma mulQ_inj (a b : int) : mulQ D a = mulQ D b -> a = b.
  Proof using HS.
    move=> Hab; apply/eqP; rewrite -subr_eq0; apply/negPn/negP => Hne.
    have [x [y [Hxy _]]] := E2 HS Hne.
    have H0 : mulQ D (a - b) = mulQ D (b - b).
    { by rewrite !(mulQ_add P0_on_curve) Hab. }
    by rewrite subrr Hxy in H0.
  Qed.

  Lemma mulP_inj (a b : int) : mulP D a = mulP D b -> a = b.
  Proof using HWF HS.
    rewrite /mulP => /mulQ_inj /eqP; rewrite -subr_eq0 -mulrBl mulf_eq0 orbC.
    rewrite eqz_nat eqn0Ngt (wf_m HWF) /= subr_eq0 => /eqP //.
  Qed.

  Lemma idx_bound_spec (n : int) X : mulP D n = Some X -> (absz n <= idx_bound X)%N.
  Proof using HO.
    case: (eqVneq n 0) => [-> // | Hn] HX.
    have H := O_HL HO (x0 := qre X.1) (x1 := qim X.1) (x2 := 1) Hn (oner_neq0 _).
    have {}H : (absz n ^ 2 <= idx_bound X)%N.
    { apply: H; exists X.2; rewrite HX; case: X {HX} => [[a b] c] /=.
      by rewrite /qe_of -qe1E divr1. }
    apply: leq_trans H; rewrite expnS expn1.
    case: (absz n) => // k; exact: leq_pmulr.
  Qed.

  (* the specification consumed by CompactnessT_StdHyps *)
  Theorem idx_ord_spec (n : int) X : mulP D n = Some X -> idx_ord X = n.
  Proof using HWF HS HO.
    move=> HX; apply: mulP_inj; rewrite HX /idx_ord.
    set l := idx_cands _; set p := fun _ => _.
    have Hhas : has p l.
    { apply/hasP; exists n; first exact/idx_cands_mem/idx_bound_spec.
      by rewrite /p HX. }
    by have /eqP := nth_find 0 Hhas.
  Qed.

End idx_ord.
