(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2C, part 2: the ordinary places of F = Q(sqrt2) above the odd
   primes, and the ORDINARY statements behind the Ambient fields trPL0,
   trPL1, trPL2_int, trPL2_mul, trPL2_ultra, trPL3.

   Design. An ordinary place is a pair [w = (q, sg) : OPl] of a prime and
   a sign; [oabove w q] holds iff q is an odd prime and, when sg = true,
   q splits in F (2 is a square mod q). The valuation [ovP w : qe rat ->
   int] (junk at 0, as in Ambient, where every use is guarded by x != 0
   or [vge]) is:
   - split q (2 = s^2 mod q for some s): the two places
     sqrt2 |-> +- sigma, sigma a q-adic square root of 2, WITHOUT q-adic
     numbers: a Hensel sequence s_K (s_K^2 = 2 mod q^(K+1), s_K' = s_K
     mod q^(K+1) for K <= K') is computed from s and an inverse of 2s mod
     q, and  v(a + b sqrt2) := v_q(a + b s_K)  for one explicit K = [bnd
     x] that is large enough: for all K >= [bnd x] the value is the same
     ([phi_stable]). Multiplicativity and the ultrametric inequality are
     proved by going to a common large K;
   - inert q: the unique place  v(a + b sqrt2) := min(v_q a, v_q b), with
     v_q(N x) = 2 v(x) ([vin_norm], since 2 is not a square mod q), from
     which multiplicativity follows.
   The root s and the inverse are found by bounded search in [0, q), so
   [ovP] and the canonical place [oplace q] are functions (no choice):
   the ultrapower can use them pointwise.

   Main results (ordinary versions of the Ambient fields):
   - [ord_PL0]  above w q -> prime q /\ q <> 2   (trPL0)
   - [ord_PL1]  odd prime q -> oabove (oplace q) q   (trPL1, function form)
   - [ord_PL2_mul], [ord_PL2_ultra]   (trPL2_mul, trPL2_ultra; trPL2_int is
     the int typing of [ovP])
   - [ord_PL3]  ovP w (qe_of x) = vqr q x   (trPL3)
   - [ovP_is_place]  is_place_above (ovP w) q   (FixedData.v)
   - [oconj], [ovP_conj]: conjugation permutes the places above q
     (swaps the two split places, fixes the inert one)
   - [split_places_distinct]: at a split prime the two places differ.
   - for an ARBITRARY place in the sense of FixedData.is_place_above at an
     odd prime p (as quantified in O_F1, O_F2): [vo_vqr] (its restriction
     to Q is v_p), [v_sqrt2] (v(sqrt2) = 0), [v_Zsqrt2_ge0] (v >= 0 on
     Z[sqrt2] \ 0).
   The same statements with the prime given as a rational ([oaboveR],
   [vqo] of OrdinaryFacts.v) are the [*_R] versions at the end.

   No axioms. *)

From Stdlib Require Import ZArith Lia List.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential FixedData RatVal OrdinaryFacts.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

(** * Helpers: int arithmetic through Z *)

Lemma iz_0 : int_to_Z 0 = 0%ZZ. Proof. by []. Qed.
Lemma iz_1 : int_to_Z 1 = 1%ZZ. Proof. by []. Qed.

Lemma iz_eq (a b : int) : a = b <-> int_to_Z a = int_to_Z b.
Proof. split; [ by move=> -> | exact: iz_inj ]. Qed.

Lemma PoszS (n : nat) : (n.+1)%:Z = n%:Z + 1.
Proof. by rewrite -addn1 PoszD. Qed.

Lemma absz_bounds (z : int) : - (`|z|%:Z) <= z /\ z <= `|z|%:Z.
Proof. split; apply/iz_le; rewrite ?iz_opp iz_nat; case: z => n /=; lia. Qed.

Ltac iz_hyp :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with H : is_true (@Order.le _ _ _ _) |- _ => apply iz_le in H end;
  repeat match goal with H : is_true (@Order.lt _ _ _ _) |- _ => apply iz_lt in H end;
  repeat match goal with H : @eq ?T _ _ |- _ => unify T int; apply iz_eq in H end.

(* close a goal of linear int arithmetic by lia; facts about absz must be
   supplied as hypotheses (absz_bounds) *)
Ltac ilia_gen := idtac.

Ltac ilia :=
  iz_hyp;
  first [ apply/iz_le | apply/iz_lt | apply/iz_eq | idtac ];
  repeat match goal with H : context [int_to_Z _] |- _ => revert H end;
  repeat match goal with H : context [absz _] |- _ => revert H end;
  repeat match goal with |- context [vqr ?q ?x] => generalize (vqr q x); intro end;
  ilia_gen;
  rewrite ?PoszD ?PoszM ?PoszS;
  do 4 rewrite ?iz_add ?iz_opp ?iz_mul;
  rewrite ?iz_nat ?iz_0 ?iz_1;
  intros; lia.

Lemma intr_neq0 (z : int) : z != 0 -> z%:~R != 0 :> rat.
Proof. by rewrite intr_eq0. Qed.

(** * Hensel lifting of a square root of 2 modulo an odd prime *)

Section hensel.

  Variables (q : nat) (s0 i : int).
  Hypothesis s0_root : exists t : int, s0 ^+ 2 - 2 = q%:Z * t.
  Hypothesis i_inv : exists j : int, 2 * s0 * i - 1 = q%:Z * j.

  Fixpoint hensel (K : nat) : int :=
    match K with
    | 0 => s0
    | K'.+1 => hensel K' - (hensel K' ^+ 2 - 2) * i
    end.

  Lemma hensel_inv K :
    (exists t : int, hensel K ^+ 2 - 2 = q%:Z ^+ K.+1 * t)
    /\ (exists m : int, hensel K - s0 = q%:Z * m).
  Proof using s0_root i_inv.
    elim: K => [ | K [ [ t Ht ] [ m Hm ] ] ].
    - split; last by exists 0; rewrite subrr mulr0.
      by move: s0_root => [ t Ht ]; exists t; rewrite expr1.
    - move: i_inv => [ j Hj ].
      set h := hensel K.
      have Hh : h = s0 + q%:Z * m by rewrite -Hm addrC subrK.
      split.
      + exists (t * (- j - 2 * m * i) + q%:Z ^+ K * t ^+ 2 * i ^+ 2).
        rewrite /= -/h.
        have E : (h - (h ^+ 2 - 2) * i) ^+ 2 - 2
                 = (h ^+ 2 - 2) * (1 - 2 * h * i) + (h ^+ 2 - 2) ^+ 2 * i ^+ 2 by ring.
        have E2 : 1 - 2 * h * i = q%:Z * (- j - 2 * m * i).
        { rewrite Hh; apply/eqP; rewrite -subr_eq0; apply/eqP.
          transitivity (- (2 * s0 * i - 1 - q%:Z * j)); first ring.
          by rewrite Hj subrr oppr0. }
        rewrite E E2 Ht !exprS; ring.
      + exists (m - q%:Z ^+ K * t * i).
        rewrite /= -/h Ht !exprS mulrBr -Hm /h; ring.
  Qed.

  Lemma hensel_step K : exists r : int, hensel K.+1 - hensel K = q%:Z ^+ K.+1 * r.
  Proof using s0_root i_inv.
    have [ [ t Ht ] _ ] := hensel_inv K.
    exists (- (t * i)); rewrite /= Ht; ring.
  Qed.

  Lemma hensel_root K : exists t : int, hensel K ^+ 2 - 2 = q%:Z ^+ K.+1 * t.
  Proof using s0_root i_inv. by have [] := hensel_inv K. Qed.

End hensel.

(** * The valuation at a split place, given a Hensel sequence

    [s K] is a square root of 2 modulo q^(K+1), and the sequence is
    q-adically coherent. The place is  sqrt2 |-> lim s_K. *)

Section split_place.

  Variable q : nat.
  Hypothesis q_prime : prime q.
  Variable s : nat -> int.
  Hypothesis s_root : forall K, exists t : int, s K ^+ 2 - 2 = q%:Z ^+ K.+1 * t.
  Hypothesis s_step : forall K, exists r : int, s K.+1 - s K = q%:Z ^+ K.+1 * r.

  Local Abbreviation v := (vqr q).

  Lemma s_coh K d : exists r : int, s (K + d)%N - s K = q%:Z ^+ K.+1 * r.
  Proof using s_step.
    elim: d => [ | d [ r Hr ] ]; first by exists 0; rewrite addn0 subrr mulr0.
    have [ r' Hr' ] := s_step (K + d).
    exists (q%:Z ^+ d * r' + r).
    have -> : s (K + d.+1)%N - s K = (s (K + d).+1 - s (K + d)%N) + (s (K + d)%N - s K).
    { rewrite addnS; ring. }
    rewrite Hr' Hr -addSn exprD; ring.
  Qed.

  Definition sK (K : nat) : rat := (s K)%:~R.

  (* the image of a + b sqrt2 under sqrt2 |-> s_K *)
  Definition phi (K : nat) (x : qe rat) : rat := qre x + qim x * sK K.

  (* a level from which on the value is stable *)
  Definition bnd (x : qe rat) : nat :=
    S (Nat.add `|v (qe_norm x)| (Nat.mul 2 (Nat.add `|v (qre x)| `|v (qim x)|))).

  (* the valuation *)
  Definition vsp (x : qe rat) : int := v (phi (bnd x) x).

  Lemma v_qpow (K : nat) (r : int) : r != 0 ->
    v (q%:R ^+ K * r%:~R) = K%:Z + v r%:~R.
  Proof using q_prime.
    move=> Hr; rewrite vqrM ?expf_neq0 ?intr_neq0 ?pnatr_eq0 -?lt0n ?prime_gt0 //.
    by rewrite vqr_expq.
  Qed.

  Lemma qpow_neq0 (K : nat) (r : int) : r != 0 -> q%:R ^+ K * r%:~R != 0 :> rat.
  Proof using q_prime.
    move=> Hr; by rewrite mulf_neq0 ?expf_neq0 ?intr_neq0 ?pnatr_eq0 -?lt0n ?prime_gt0.
  Qed.

  Lemma sK_root K : exists t : int, sK K ^+ 2 - 2%:R = q%:R ^+ K.+1 * t%:~R.
  Proof using s_root.
    have [ t Ht ] := s_root K; exists t.
    have := congr1 (fun z : int => z%:~R : rat) Ht.
    by rewrite /= intrB intrM !rmorphXn /= -natr_intr.
  Qed.

  Lemma sK_coh K d : exists r : int, sK (K + d)%N - sK K = q%:R ^+ K.+1 * r%:~R.
  Proof using s_step.
    have [ r Hr ] := s_coh K d; exists r.
    have := congr1 (fun z : int => z%:~R : rat) Hr.
    by rewrite /= intrB intrM !rmorphXn /= -natr_intr.
  Qed.

  Lemma sK_ge0 K : 0 <= v (sK K).
  Proof. exact: vqr_int_ge0. Qed.

  (* the key estimate: phi K x is nonzero with bounded valuation *)
  Lemma phi_bound (a b : rat) K : QE a b != 0 -> b != 0 -> (bnd (QE a b) <= K)%coq_nat ->
    phi K (QE a b) != 0 /\
    v (phi K (QE a b)) <= v (qe_norm (QE a b)) + `|v a|%:Z + `|v b|%:Z.
  Proof using q_prime s_root.
    move=> Hx Hb HK.
    have HN := qe_norm_neq0 Hx.
    move: HK; rewrite /bnd /= => HK.
    move: HK; move En : (v (qe_norm (QE a b))) => n HK.
    have Bn := absz_bounds n; have Ba := absz_bounds (v a); have Bb := absz_bounds (v b).
    have [ t Ht ] := sK_root K.
    set u := phi K (QE a b).
    set u' := a - b * sK K.
    have Huu : u * u' = qe_norm (QE a b) + - (b ^+ 2 * (q%:R ^+ K.+1 * t%:~R)).
    { rewrite -Ht /u /u' /phi /qe_norm /=; ring. }
    have [ Hnz Hv ] : u * u' != 0 /\ v (u * u') = n.
    { case: (eqVneq t 0) => Ht0.
      - rewrite Huu Ht0 mulr0 mulr0 oppr0 addr0; by split.
      - have He : - (b ^+ 2 * (q%:R ^+ K.+1 * t%:~R)) != 0.
        { by rewrite oppr_eq0 !mulf_neq0 ?expf_neq0 ?intr_neq0 ?pnatr_eq0 -?lt0n ?prime_gt0. }
        have Hve : v (- (b ^+ 2 * (q%:R ^+ K.+1 * t%:~R))) = v b + v b + K.+1%:Z + v t%:~R.
        { have Hb2 : b ^+ 2 != 0 by rewrite expf_neq0.
          by rewrite vqrN vqrM ?qpow_neq0 // vqrX2 // v_qpow // !addrA. }
        have Ht0' := vqr_int_ge0 q t.
        have Hlt : v (qe_norm (QE a b)) < v (- (b ^+ 2 * (q%:R ^+ K.+1 * t%:~R))).
        { rewrite En Hve; ilia. }
        have [ H1 H2 ] := vqr_add_lt q_prime HN He Hlt.
        by rewrite Huu H2 En; split. }
    move: Hnz; rewrite mulf_eq0 negb_or => /andP [ Hu Hu' ].
    have Hsum : v u + v u' = n by rewrite -vqrM.
    have Hlow : - (`|v a|%:Z + `|v b|%:Z) <= v u'.
    { have Hs := sK_ge0 K.
      case: (eqVneq a 0) => Ha.
      - move: Hu'; rewrite /u' Ha sub0r => Hu'.
        have Hs0 : sK K != 0 by apply: contraNneq Hu' => ->; rewrite mulr0 oppr0.
        rewrite vqrN vqrM //; ilia.
      case: (eqVneq (sK K) 0) => Hs0.
      - rewrite /u' Hs0 mulr0 subr0; ilia.
      apply: vqr_add_ge => //; rewrite ?oppr_eq0 ?mulf_neq0 //.
      - ilia.
      - rewrite vqrN vqrM //; ilia. }
    split => //; ilia.
  Qed.

  (* stability: for K >= bnd x the value v (phi K x) does not depend on K *)
  Lemma phi_stable (x : qe rat) K K' : x != 0 -> (bnd x <= K)%coq_nat -> (K <= K')%coq_nat ->
    phi K' x != 0 /\ v (phi K' x) = v (phi K x).
  Proof using q_prime s_root s_step.
    case: x => a b Hx HK HK'.
    case: (eqVneq b 0) => Hb.
    - have E : forall L, phi L (QE a b) = a by move=> L; rewrite /phi /= Hb mul0r addr0.
      rewrite !E; split => //; apply: contraNneq Hx => Ha; by rewrite Ha Hb.
    have [ Hu Hvu ] := phi_bound Hx Hb HK.
    have [ d -> ] : exists d, K' = (K + d)%N.
    { exists (K' - K)%N; rewrite subnKC //; exact/ssrnat.leP. }
    have [ r Hr ] := sK_coh K d.
    have E : phi (K + d)%N (QE a b) = phi K (QE a b) + b * (q%:R ^+ K.+1 * r%:~R).
    { rewrite /phi /= -Hr; ring. }
    case: (eqVneq r 0) => Hr0.
    - by rewrite E Hr0 mulr0 mulr0 addr0.
    have He : b * (q%:R ^+ K.+1 * r%:~R) != 0.
    { by rewrite !mulf_neq0 ?expf_neq0 ?intr_neq0 ?pnatr_eq0 -?lt0n ?prime_gt0. }
    have Hve : v (b * (q%:R ^+ K.+1 * r%:~R)) = v b + K.+1%:Z + v r%:~R.
    { by rewrite vqrM ?qpow_neq0 // v_qpow // addrA. }
    have Hr0' := vqr_int_ge0 q r.
    move: HK; rewrite /bnd /= => HK.
    have Bn := absz_bounds (v (qe_norm (QE a b))).
    have Ba := absz_bounds (v a); have Bb := absz_bounds (v b).
    have Hlt : v (phi K (QE a b)) < v (b * (q%:R ^+ K.+1 * r%:~R)) by rewrite Hve; ilia.
    have [ H1 H2 ] := vqr_add_lt q_prime Hu He Hlt.
    by rewrite E; split.
  Qed.

  Lemma vsp_spec (x : qe rat) K : x != 0 -> (bnd x <= K)%coq_nat ->
    phi K x != 0 /\ v (phi K x) = vsp x.
  Proof using q_prime s_root s_step.
    move=> Hx HK; exact: (phi_stable Hx (le_n _) HK).
  Qed.

  Lemma qe_mul_neq0 (x y : qe rat) : x != 0 -> y != 0 -> x * y != 0.
  Proof.
    move=> /qe_norm_neq0 Hx /qe_norm_neq0 Hy; apply/eqP => E.
    have H0 : qe_norm (0 : qe rat) = 0 by rewrite /qe_norm /=; ring.
    have := qe_norm_mul x y; rewrite E H0 => /esym /eqP.
    by rewrite mulf_eq0 (negbTE Hx) (negbTE Hy).
  Qed.

  (* multiplicativity *)
  Lemma vsp_mul (x y : qe rat) : x != 0 -> y != 0 -> vsp (x * y) = vsp x + vsp y.
  Proof using q_prime s_root s_step.
    move=> Hx Hy; have Hxy := qe_mul_neq0 Hx Hy.
    pose K := Nat.add (Nat.add (Nat.add (bnd x) (bnd y)) (bnd (x * y)))
                (Nat.add (Nat.add `|vsp x| `|vsp y|) (Nat.add `|v (qim x)| `|v (qim y)|)).
    have [ Hpx Ex ] := vsp_spec Hx (K := K) ltac:(rewrite /K; lia).
    have [ Hpy Ey ] := vsp_spec Hy (K := K) ltac:(rewrite /K; lia).
    have [ Hpxy Exy ] := vsp_spec Hxy (K := K) ltac:(rewrite /K; lia).
    have HK : (Nat.add (Nat.add `|vsp x| `|vsp y|) (Nat.add `|v (qim x)| `|v (qim y)|) <= K)%coq_nat.
    { rewrite /K; lia. }
    clearbody K.
    have B1 := absz_bounds (vsp x); have B2 := absz_bounds (vsp y).
    have B3 := absz_bounds (v (qim x)); have B4 := absz_bounds (v (qim y)).
    have [ t Ht ] := sK_root K.
    have E : phi K (x * y) = phi K x * phi K y + - (qim x * qim y * (q%:R ^+ K.+1 * t%:~R)).
    { rewrite -Ht; move: x y {Hx Hy Hxy Hpx Hpy Hpxy Ex Ey Exy HK B1 B2 B3 B4} => [ a b ] [ c d ].
      rewrite /phi qe_mulE /=; ring. }
    have Hp : phi K x * phi K y != 0 by rewrite mulf_neq0.
    rewrite -Exy -Ex -Ey -vqrM // E.
    set e := - (qim x * qim y * (q%:R ^+ K.+1 * t%:~R)).
    case: (eqVneq e 0) => He; first by rewrite He addr0.
    move: (He); rewrite /e oppr_eq0 !mulf_eq0 !negb_or => /andP [ /andP [ Hb Hd ] /andP [ _ Ht0 ] ].
    have Hve : v e = v (qim x) + v (qim y) + K.+1%:Z + v t%:~R.
    { have Ht1 : t != 0 by apply: contraNneq Ht0 => ->.
      have Hbd : qim x * qim y != 0 by rewrite mulf_neq0.
      rewrite /e vqrN (@vqrM q _ _ Hbd (qpow_neq0 K.+1 Ht1)) (@vqrM q _ _ Hb Hd).
      by rewrite v_qpow // !addrA. }
    have Ht0' := vqr_int_ge0 q t.
    have Hlt : v (phi K x * phi K y) < v e.
    { rewrite vqrM // Ex Ey Hve; ilia. }
    by have [ _ -> ] := vqr_add_lt q_prime Hp He Hlt.
  Qed.

  (* the ultrametric inequality *)
  Lemma vsp_ultra (x y : qe rat) : x != 0 -> y != 0 -> x + y != 0 ->
    Num.min (vsp x) (vsp y) <= vsp (x + y).
  Proof using q_prime s_root s_step.
    move=> Hx Hy Hxy.
    pose K := Nat.add (Nat.add (bnd x) (bnd y)) (bnd (x + y)).
    have [ Hpx Ex ] := vsp_spec Hx (K := K) ltac:(rewrite /K; lia).
    have [ Hpy Ey ] := vsp_spec Hy (K := K) ltac:(rewrite /K; lia).
    have [ Hpxy Exy ] := vsp_spec Hxy (K := K) ltac:(rewrite /K; lia).
    clearbody K.
    have E : phi K (x + y) = phi K x + phi K y.
    { move: x y {Hx Hy Hxy Hpx Hpy Hpxy Ex Ey Exy} => [ a b ] [ c d ].
      rewrite /phi qe_addE /=; ring. }
    rewrite -Ex -Ey -Exy E; apply: vqr_ultra => //; by rewrite -E.
  Qed.

  (* restriction to Q *)
  Lemma vsp_of (a : rat) : vsp (qe_of a) = v a.
  Proof. by rewrite /vsp /phi /= mul0r addr0. Qed.

End split_place.

Arguments bnd q x : clear implicits.

Lemma bnd_conj q (x : qe rat) : bnd q (qe_conj x) = bnd q x.
Proof.
  case: x => a b; rewrite /bnd /qe_conj /qe_norm /= vqrN; congr (S (Nat.add `|vqr q (_ - _)| _)).
  by rewrite sqrrN.
Qed.

(* conjugation exchanges the roots s and -s *)
Lemma vsp_conj q (s : nat -> int) (x : qe rat) :
  vsp q (fun K => - s K) (qe_conj x) = vsp q s x.
Proof.
  rewrite /vsp bnd_conj; congr vqr.
  by case: x => a b; rewrite /phi /sK /qe_conj /= intrN mulrNN.
Qed.

(** * The valuation at an inert place *)

Section inert_place.

  Variable q : nat.
  Hypothesis q_prime : prime q.
  Hypothesis q_odd : q != 2%N.
  Hypothesis q_inert : forall z : int, ~~ (q%:Z %| z ^+ 2 - 2)%Z.

  Local Abbreviation v := (vqr q).

  Definition vin (x : qe rat) : int :=
    if qre x == 0 then v (qim x)
    else if qim x == 0 then v (qre x)
    else Num.min (v (qre x)) (v (qim x)).

  (* 2 is not a square modulo q: c^2 - 2 is a q-unit for q-integral c *)
  Lemma inert_unit (c : rat) : 0 <= v c -> v (c ^+ 2 - 2%:R) = 0.
  Proof using q_prime q_odd q_inert.
    move=> Hc.
    have H2 : c ^+ 2 - 2%:R != 0.
    { rewrite subr_eq0 expr2; apply/eqP; exact: ord_Z0. }
    have H2' : v (- 2%:R) = 0 by rewrite vqrN vqr_2.
    apply/eqP; rewrite eq_le; apply/andP; split; last first.
    { case: (eqVneq c 0) => Hc0.
      - by rewrite Hc0 expr0n /= sub0r H2'.
      - apply: vqr_add_ge => //; rewrite ?expf_neq0 ?oppr_eq0 ?pnatr_eq0 ?H2' //.
        by rewrite vqrX2 // addr_ge0. }
    rewrite leNgt; apply/negP => Hpos.
    have Hd := vqr_ge0_den q_prime Hc.
    have Hd0 : denq c != 0 := denq_neq0 c.
    have Ec : c = (numq c)%:~R / (denq c)%:~R by rewrite divq_num_den.
    pose N := numq c ^+ 2 - 2 * denq c ^+ 2.
    have EN : c ^+ 2 - 2%:R = N%:~R / (denq c ^+ 2)%:~R.
    { rewrite {1}Ec /N intrB intrM !rmorphXn /=; have Hd1 : (denq c)%:~R != 0 :> rat by rewrite intr_eq0.
      field. }
    have HN0 : N != 0.
    { apply: contraNneq H2 => HN; by rewrite EN HN mul0r. }
    move: Hpos; rewrite EN vqr_frac ?expf_neq0 //.
    have -> : logn q `|denq c ^+ 2| = 0%N.
    { apply: logn_ndvd; by rewrite abszX Euclid_dvdX // negb_and Hd. }
    rewrite subr0 ltz_nat logn_gt0 mem_primes => /andP [ _ /andP [ _ HqN ] ].
    have HqNz : (q%:Z %| N)%Z by rewrite dvdzE.
    have Hcop : coprimez q%:Z (denq c) by rewrite coprimezE /= prime_coprime.
    have [ u [ w Huw ] ] := Bezoutz q%:Z (denq c).
    move: Hcop; rewrite /coprimez => /eqP Hg; rewrite Hg in Huw.
    move: HqNz => /dvdzP [ m Hm ].
    apply: (negP (q_inert (numq c * w))); apply/dvdzP.
    exists (w ^+ 2 * m + 2 * (u ^+ 2 * q%:Z - 2 * u)).
    apply/eqP; rewrite -subr_eq0; apply/eqP.
    transitivity (w ^+ 2 * (N - m * q%:Z) + 2 * (w * denq c - u * q%:Z + 1) * (u * q%:Z + w * denq c - 1)).
    { rewrite /N; ring. }
    by rewrite Hm Huw !subrr !mulr0 addr0.
  Qed.

  Lemma vin_norm (x : qe rat) : x != 0 -> v (qe_norm x) = vin x + vin x.
  Proof using q_prime q_odd q_inert.
    case: x => a b Hx; rewrite /vin /qe_norm /=.
    have Hab : a != 0 \/ b != 0.
    { case: (eqVneq a 0) => [ Ha | ]; last by left.
      right; apply: contraNneq Hx => Hb; by rewrite Ha Hb. }
    case: (eqVneq a 0) => Ha.
    - have Hb : b != 0 by case: Hab => //; rewrite Ha eqxx.
      rewrite Ha expr0n /= sub0r vqrN vqrM ?pnatr_eq0 ?expf_neq0 //.
      by rewrite vqr_2 // vqrX2 // add0r.
    case: (eqVneq b 0) => Hb.
    - by rewrite Hb expr0n /= mulr0 subr0 vqrX2.
    have E2 : v (- (2%:R * b ^+ 2)) = v b + v b.
    { by rewrite vqrN vqrM ?pnatr_eq0 ?expf_neq0 // vqr_2 // vqrX2 // add0r. }
    have Hn2 : - (2%:R * b ^+ 2) != 0 by rewrite oppr_eq0 mulf_neq0 ?pnatr_eq0 ?expf_neq0.
    have Ha2 : a ^+ 2 != 0 by rewrite expf_neq0.
    case: (ltgtP (v a) (v b)) => Hab'.
    - have Hlt : v (a ^+ 2) < v (- (2%:R * b ^+ 2)) by rewrite E2 vqrX2 // ltrD.
      have [ _ -> ] := vqr_add_lt q_prime Ha2 Hn2 Hlt.
      by rewrite vqrX2.
    - have Hlt : v (- (2%:R * b ^+ 2)) < v (a ^+ 2) by rewrite E2 vqrX2 // ltrD.
      have [ _ E ] := vqr_add_lt q_prime Hn2 Ha2 Hlt.
      by rewrite [a ^+ 2 - _]addrC E E2.
    - have Hc : 0 <= v (a / b) by rewrite vqr_div // Hab' subrr.
      have E : a ^+ 2 - 2%:R * b ^+ 2 = b ^+ 2 * ((a / b) ^+ 2 - 2%:R).
      { field; exact: Hb. }
      have Hc2 : (a / b) ^+ 2 - 2%:R != 0.
      { rewrite subr_eq0 expr2; apply/eqP; exact: ord_Z0. }
      rewrite E vqrM ?expf_neq0 // inert_unit // addr0 vqrX2 //.
      by rewrite Hab'.
  Qed.

  Lemma vin_le_re (x : qe rat) : qre x != 0 -> vin x <= v (qre x).
  Proof.
    rewrite /vin => /negbTE ->; case: ifP => _ //; by rewrite ge_min lexx.
  Qed.

  Lemma vin_le_im (x : qe rat) : qim x != 0 -> vin x <= v (qim x).
  Proof.
    rewrite /vin => /negbTE Hb; rewrite Hb; case: ifP => _ //; by rewrite ge_min lexx orbT.
  Qed.

  Lemma vin_ge (x : qe rat) (k : int) : x != 0 ->
    (qre x != 0 -> k <= v (qre x)) -> (qim x != 0 -> k <= v (qim x)) -> k <= vin x.
  Proof.
    case: x => a b Hx; rewrite /vin /= => H1 H2.
    case: (eqVneq a 0) => Ha.
    - apply: H2; apply: contraNneq Hx => Hb; by rewrite Ha Hb.
    case: (eqVneq b 0) => Hb; first exact: H1.
    by rewrite le_min H1 ?H2.
  Qed.

  Lemma comp_ge (a c : rat) (k : int) : a + c != 0 ->
    (a != 0 -> k <= v a) -> (c != 0 -> k <= v c) -> k <= v (a + c).
  Proof using q_prime.
    move=> Hac H1 H2.
    case: (eqVneq a 0) => Ha; first by move: Hac H2; rewrite Ha add0r => Hc; apply.
    case: (eqVneq c 0) => Hc; first by move: Hac H1; rewrite Hc addr0 => Ha'; apply.
    by apply: vqr_add_ge => //; [ apply: H1 | apply: H2 ].
  Qed.

  (* the ultrametric inequality *)
  Lemma vin_ultra (x y : qe rat) : x != 0 -> y != 0 -> x + y != 0 ->
    Num.min (vin x) (vin y) <= vin (x + y).
  Proof using q_prime.
    move=> Hx Hy Hxy; apply: vin_ge => //.
    - move: Hx Hy Hxy => _ _; case: x => a b; case: y => c d /= _ Hac.
      apply: comp_ge => // H.
      + apply: le_trans (vin_le_re (x := QE a b) H); by rewrite ge_min lexx.
      + apply: le_trans (vin_le_re (x := QE c d) H); by rewrite ge_min lexx orbT.
    - move: Hx Hy Hxy => _ _; case: x => a b; case: y => c d /= _ Hbd.
      apply: comp_ge => // H.
      + apply: le_trans (vin_le_im (x := QE a b) H); by rewrite ge_min lexx.
      + apply: le_trans (vin_le_im (x := QE c d) H); by rewrite ge_min lexx orbT.
  Qed.

  (* multiplicativity, from v_q(N x) = 2 v(x) *)
  Lemma vin_mul (x y : qe rat) : x != 0 -> y != 0 -> vin (x * y) = vin x + vin y.
  Proof using q_prime q_odd q_inert.
    move=> Hx Hy; have Hxy := qe_mul_neq0 Hx Hy.
    have := vin_norm Hxy; rewrite qe_norm_mul vqrM ?qe_norm_neq0 // !vin_norm //.
    move: (vin x) (vin y) (vin (x * y)) => i j k E.
    ilia.
  Qed.

  (* restriction to Q *)
  Lemma vin_of (a : rat) : vin (qe_of a) = v a.
  Proof. rewrite /vin /=; case: (eqVneq a 0) => [ -> | ]; by rewrite ?eqxx // => /negbTE ->. Qed.

  Lemma vin_conj (x : qe rat) : vin (qe_conj x) = vin x.
  Proof. by case: x => a b; rewrite /vin /qe_conj /= oppr_eq0 vqrN. Qed.

End inert_place.

(** * Splitting type of q and the data of the split places, by bounded search *)

Definition sq2P (q s : nat) : bool := (q%:Z %| (s%:Z) ^+ 2 - 2)%Z.

(* q splits in F iff 2 is a square modulo q *)
Definition qsplitb (q : nat) : bool := has (sq2P q) (iota 0 q).

(* a square root of 2 modulo q *)
Definition qroot (q : nat) : nat := nth 0%N (iota 0 q) (find (sq2P q) (iota 0 q)).

Definition invP (q s i : nat) : bool := (q%:Z %| 2 * s%:Z * i%:Z - 1)%Z.

(* an inverse of 2 s modulo q *)
Definition qinv (q : nat) : nat :=
  nth 0%N (iota 0 q) (find (invP q (qroot q)) (iota 0 q)).

(* the Hensel sequence of the root *)
Definition hroot (q : nat) : nat -> int := hensel (qroot q)%:Z (qinv q)%:Z.

Lemma qroot_spec q : qsplitb q -> sq2P q (qroot q).
Proof. exact: nth_find. Qed.

Lemma dvdz_ex (d m : int) : (d %| m)%Z -> exists t, m = d * t.
Proof. by move=> /dvdzP [ t -> ]; exists t; rewrite mulrC. Qed.

Lemma ex_dvdz (d m t : int) : m = d * t -> (d %| m)%Z.
Proof. by move=> ->; apply/dvdzP; exists t; rewrite mulrC. Qed.

(* reduction of an integer modulo q into [0, q) *)
Lemma modz_iota (q : nat) (z : int) : (0 < q)%N ->
  (absz (z %% q%:Z)%Z) \in iota 0 q /\ ((absz (z %% q%:Z)%Z)%:Z = z - (z %/ q%:Z)%Z * q%:Z).
Proof.
  move=> Hq; have Hq0 : q%:Z != 0 by apply/eqP => [] [] H; move: Hq; rewrite H.
  have H0 := modz_ge0 z Hq0.
  split.
  - rewrite mem_iota add0n /= -ltz_nat gez0_abs //; exact: ltz_mod.
  - by rewrite gez0_abs // {2}(divz_eq z q%:Z) addrC addKr.
Qed.

Section odd_prime.

  Variable q : nat.
  Hypothesis q_prime : prime q.
  Hypothesis q_odd : q != 2%N.

  Lemma q_ndvd2 : ~~ (q %| 2)%N.
  Proof using q_prime q_odd. by rewrite (dvdn_prime2 q_prime (isT : prime 2)). Qed.

  (* a root of 2 modulo q is prime to q, and so is 2 s *)
  Lemma root_coprime (s : int) : (q%:Z %| s ^+ 2 - 2)%Z -> coprimez q%:Z (2 * s).
  Proof using q_prime q_odd.
    move=> /dvdz_ex [ m Hm ].
    rewrite coprimezMr; apply/andP; split.
    - by rewrite coprimezE /= prime_coprime // q_ndvd2.
    - rewrite coprimezE /= prime_coprime //; apply/negP => Hs.
      have : (q%:Z %| s)%Z by rewrite dvdzE.
      move=> /dvdz_ex [ k Hk ].
      have : (q%:Z %| 2)%Z.
      { apply: (@ex_dvdz _ _ (q%:Z * k ^+ 2 - m)).
        transitivity (s ^+ 2 - (s ^+ 2 - 2)); first ring.
        by rewrite Hm Hk; ring. }
      by rewrite dvdzE /= (negbTE q_ndvd2).
  Qed.

  Lemma qinv_spec : qsplitb q -> invP q (qroot q) (qinv q).
  Proof using q_prime q_odd.
    move=> Hs; apply: nth_find.
    have Hr := qroot_spec Hs.
    have /eqP Hcop := root_coprime Hr.
    have [ u [ w Huw ] ] := Bezoutz q%:Z (2 * (qroot q)%:Z).
    rewrite Hcop in Huw.
    have [ Hi Ei ] := modz_iota w (prime_gt0 q_prime).
    apply/hasP; exists (absz (w %% q%:Z)%Z) => //.
    rewrite /invP Ei.
    apply: (@ex_dvdz _ _ (- u - 2 * (qroot q)%:Z * (w %/ q%:Z)%Z)).
    transitivity (2 * (qroot q)%:Z * w - 1 - 2 * (qroot q)%:Z * (w %/ q%:Z)%Z * q%:Z); first ring.
    have -> : 2 * (qroot q)%:Z * w - 1 = - (u * q%:Z).
    { apply/eqP; rewrite -subr_eq0; apply/eqP.
      transitivity (u * q%:Z + w * (2 * (qroot q)%:Z) - 1); first ring.
      by rewrite Huw subrr. }
    ring.
  Qed.

  Lemma hroot_hyps : qsplitb q ->
    (exists t : int, (qroot q)%:Z ^+ 2 - 2 = q%:Z * t)
    /\ (exists j : int, 2 * (qroot q)%:Z * (qinv q)%:Z - 1 = q%:Z * j).
  Proof using q_prime q_odd.
    move=> Hs; split; apply: dvdz_ex; [ exact: qroot_spec | exact: qinv_spec ].
  Qed.

  Lemma hroot_root : qsplitb q ->
    forall K, exists t : int, hroot q K ^+ 2 - 2 = q%:Z ^+ K.+1 * t.
  Proof using q_prime q_odd.
    move=> /hroot_hyps [ H1 H2 ]; exact: hensel_root.
  Qed.

  Lemma hroot_step : qsplitb q ->
    forall K, exists r : int, hroot q K.+1 - hroot q K = q%:Z ^+ K.+1 * r.
  Proof using q_prime q_odd.
    move=> /hroot_hyps [ H1 H2 ]; exact: hensel_step.
  Qed.

  Lemma hroot_root_neg : qsplitb q ->
    forall K, exists t : int, (- hroot q K) ^+ 2 - 2 = q%:Z ^+ K.+1 * t.
  Proof using q_prime q_odd.
    move=> Hs K; rewrite sqrrN; exact: hroot_root.
  Qed.

  Lemma hroot_step_neg : qsplitb q ->
    forall K, exists r : int, - hroot q K.+1 - - hroot q K = q%:Z ^+ K.+1 * r.
  Proof using q_prime q_odd.
    move=> Hs K; have [ r Hr ] := hroot_step Hs K; exists (- r).
    by rewrite -opprD Hr mulrN.
  Qed.

  (* not split: 2 is not a square modulo q *)
  Lemma inert_hyp : ~~ qsplitb q -> forall z : int, ~~ (q%:Z %| z ^+ 2 - 2)%Z.
  Proof using q_prime.
    move=> Hn z; apply/negP => /dvdz_ex [ m Hm ].
    have [ Hi Ei ] := modz_iota z (prime_gt0 q_prime).
    move: Hn => /hasP; apply; exists (absz (z %% q%:Z)%Z) => //.
    rewrite /sq2P Ei.
    pose k := (z %/ q%:Z)%Z.
    apply: (@ex_dvdz _ _ (m - k * (2 * z - k * q%:Z))).
    transitivity (z ^+ 2 - 2 - k * q%:Z * (2 * z - k * q%:Z)); first by rewrite /k; ring.
    by rewrite Hm; ring.
  Qed.

End odd_prime.

(** * The ordinary places of F above odd primes *)

(* a place is a prime and a sign (the sign selects sqrt2 |-> +- sigma at a split prime) *)
Definition OPl : Type := (nat * bool)%type.

Definition oabove (w : OPl) (q : nat) : Prop :=
  w.1 = q /\ prime q /\ q != 2%N /\ (w.2 -> qsplitb q).

(* the valuation of the place w on F (junk at 0) *)
Definition ovP (w : OPl) (x : qe rat) : int :=
  if qsplitb w.1 then vsp w.1 (if w.2 then (fun K => - hroot w.1 K) else hroot w.1) x
  else vin w.1 x.

(* the canonical place above q *)
Definition oplace (q : nat) : OPl := (q, false).

(* the conjugate place: x |-> w(sigma x) *)
Definition oconj (w : OPl) : OPl := (w.1, ~~ w.2 && qsplitb w.1).

Section places.

  Variables (w : OPl) (q : nat).
  Hypothesis Hw : oabove w q.

  Let Hq1 : w.1 = q. Proof. by case: Hw. Qed.
  Let q_prime : prime q. Proof. by case: Hw => _ []. Qed.
  Let q_odd : q != 2%N. Proof. by case: Hw => _ [] _ []. Qed.
  Let Hsg : w.2 -> qsplitb q. Proof. by case: Hw => _ [] _ []. Qed.

  Lemma ovPE (x : qe rat) : ovP w x =
    if qsplitb q then vsp q (if w.2 then (fun K => - hroot q K) else hroot q) x else vin q x.
  Proof using Hw Hq1. by rewrite /ovP Hq1. Qed.

  (* ordinary version of trPL2_mul *)
  Lemma ord_PL2_mul (x y : qe rat) : x != 0 -> y != 0 -> ovP w (x * y) = ovP w x + ovP w y.
  Proof using Hw Hq1 q_prime q_odd Hsg.
    move=> Hx Hy; rewrite !ovPE; case: ifP => Hs.
    - case: (w.2).
      + exact: (vsp_mul q_prime (hroot_root_neg q_prime q_odd Hs) (hroot_step_neg q_prime q_odd Hs)).
      + exact: (vsp_mul q_prime (hroot_root q_prime q_odd Hs) (hroot_step q_prime q_odd Hs)).
    - exact: (vin_mul q_prime q_odd (inert_hyp q_prime (negbT Hs))).
  Qed.

  (* ordinary version of trPL2_ultra *)
  Lemma ord_PL2_ultra (x y : qe rat) : x != 0 -> y != 0 -> x + y != 0 ->
    Num.min (ovP w x) (ovP w y) <= ovP w (x + y).
  Proof using Hw Hq1 q_prime q_odd Hsg.
    move=> Hx Hy Hxy; rewrite !ovPE; case: ifP => Hs.
    - case: (w.2).
      + exact: (vsp_ultra q_prime (hroot_root_neg q_prime q_odd Hs) (hroot_step_neg q_prime q_odd Hs)).
      + exact: (vsp_ultra q_prime (hroot_root q_prime q_odd Hs) (hroot_step q_prime q_odd Hs)).
    - exact: (vin_ultra q_prime).
  Qed.

  (* ordinary version of trPL3 (it even holds at x = 0) *)
  Lemma ord_PL3 (x : rat) : ovP w (qe_of x) = vqr q x.
  Proof using Hw Hq1 q_prime q_odd Hsg.
    by rewrite ovPE; case: ifP => _; rewrite ?vsp_of ?vin_of.
  Qed.

  Lemma ovP_q : ovP w q%:R = 1.
  Proof using Hw Hq1 q_prime q_odd Hsg.
    have -> : q%:R = qe_of q%:R :> qe rat by rewrite qe_natE.
    by rewrite ord_PL3 vqr_prime.
  Qed.

  (* the place in the sense of FixedData.v *)
  Lemma ovP_is_place : is_place_above (ovP w) q.
  Proof using Hw Hq1 q_prime q_odd Hsg.
    split; [ exact: ord_PL2_mul | split; [ exact: ord_PL2_ultra | exact: ovP_q ] ].
  Qed.

  (* conjugation permutes the places above q *)
  Lemma oconj_above : oabove (oconj w) q.
  Proof using Hw Hq1 q_prime q_odd Hsg.
    rewrite /oconj Hq1; split => //; do 2 (split => //); by move=> /= /andP [].
  Qed.

  Lemma ovP_conj (x : qe rat) : ovP (oconj w) (qe_conj x) = ovP w x.
  Proof using Hw Hq1 q_prime q_odd Hsg.
    rewrite (ovPE x) /ovP /oconj /= Hq1; case: ifP => Hs.
    - case: (w.2); rewrite /= ?Hs /=.
      + by rewrite -(vsp_conj q (hroot q) (qe_conj x)) qe_conjK.
      + exact: vsp_conj.
    - exact: vin_conj.
  Qed.

End places.

Lemma oconjK (w : OPl) q : oabove w q -> oconj (oconj w) = w.
Proof.
  case: w => q' sg [ /= -> [ _ [ _ Hsg ] ] ]; rewrite /oconj /=.
  case: sg Hsg => /= [ H | _ ]; first by rewrite (H isT).
  by case: (qsplitb q).
Qed.

(* ordinary version of trPL0 *)
Lemma ord_PL0 (w : OPl) (q : nat) : oabove w q -> prime q /\ q != 2%N.
Proof. by move=> [ _ [ Hp [ Hq _ ] ] ]. Qed.

(* every ordinary place is above exactly one prime *)
Lemma oabove_uniq (w : OPl) (q q' : nat) : oabove w q -> oabove w q' -> q = q'.
Proof. by move=> [ <- _ ] [ <- _ ]. Qed.

(* ordinary version of trPL1, in function form: the canonical place *)
Lemma ord_PL1 (q : nat) : prime q -> q != 2%N -> oabove (oplace q) q.
Proof. by move=> Hp Hq; do 3 (split => //). Qed.

Lemma ord_PL1_ex (q : nat) : prime q -> q != 2%N -> exists w, oabove w q.
Proof. move=> Hp Hq; exists (oplace q); exact: ord_PL1. Qed.

(* every valuation of the family is a place in the sense of FixedData.v *)
Lemma ord_place_family (q : nat) : prime q -> q != 2%N ->
  exists v : qe rat -> int, is_place_above v q.
Proof. move=> Hp Hq; exists (ovP (oplace q)); apply: ovP_is_place; exact: ord_PL1. Qed.

(** * At a split prime the two places are different *)

Lemma split_places_distinct (q : nat) : prime q -> q != 2%N -> qsplitb q ->
  oabove (q, true) q /\
  exists x : qe rat, x != 0 /\ ovP (q, false) x != ovP (q, true) x.
Proof.
  move=> Hp Hq Hs; split; first by do 3 (split => //).
  exists (QE (- (qroot q)%:R) 1); split; first by apply/eqP => [] [] _ /eqP; rewrite oner_eq0.
  set x := QE (- (qroot q)%:R) 1.
  have Hx : x != 0 by apply/eqP => [] [] _ /eqP; rewrite oner_eq0.
  rewrite /ovP /= Hs.
  set K := bnd q x.
  have [ Hnz1 E1 ] := vsp_spec Hp (hroot_root Hp Hq Hs) (hroot_step Hp Hq Hs) Hx (le_n K).
  have [ Hnz2 E2 ] := vsp_spec Hp (hroot_root_neg Hp Hq Hs) (hroot_step_neg Hp Hq Hs) Hx (le_n K).
  rewrite -E1 -E2 /phi /sK /x /= !mul1r.
  have [ H1 H2 ] := hroot_hyps Hp Hq Hs.
  have [ _ [ m Hm ] ] := hensel_inv H1 H2 K.
  rewrite -/(hroot q K) in Hm.
  (* first place: - s + s_K = q m has positive valuation *)
  have E3 : - (qroot q)%:R + (hroot q K)%:~R = (q%:Z * m)%:~R :> rat.
  { by rewrite -Hm intrB natr_intr addrC. }
  (* second place: - s - s_K = - (2 s + q m) is a unit *)
  have E4 : - (qroot q)%:R + (- hroot q K)%:~R = (- (2 * (qroot q)%:Z + q%:Z * m))%:~R :> rat.
  { rewrite -Hm !(intrN, intrD, intrM) natr_intr; ring. }
  rewrite E3 E4 intrN vqrN !vqr_int.
  have -> : logn q `|2 * (qroot q)%:Z + q%:Z * m| = 0%N.
  { apply: logn_ndvd; apply/negP => Hd.
    have Hd' : (q%:Z %| 2 * (qroot q)%:Z + q%:Z * m)%Z by rewrite dvdzE.
    have /dvdz_ex [ k Hk ] := Hd'.
    have : (q%:Z %| 2 * (qroot q)%:Z)%Z.
    { apply: (@ex_dvdz _ _ (k - m)); rewrite mulrBr -Hk; ring. }
    have := root_coprime Hp Hq (qroot_spec Hs).
    rewrite coprimezE /= prime_coprime // dvdzE => /negbTE ->.
    done. }
  rewrite eqz_nat -lt0n logn_gt0 mem_primes Hp /= absz_gt0.
  have Hm0 : q%:Z * m != 0.
  { apply: contraNneq Hnz1; rewrite /phi /sK /x /= mul1r => H0.
    by rewrite E3 H0. }
  rewrite Hm0 /=.
  by rewrite abszM /= dvdn_mulr.
Qed.

(** * The ambient-shaped versions, with the prime given as a rational *)

Definition oaboveR (w : OPl) (q : rat) : Prop := q = (w.1)%:R /\ oabove w w.1.

Definition oplaceR (q : rat) : OPl := oplace `|numq q|.

(* ordinary version of trPL0 *)
Lemma ord_PL0R (w : OPl) (q : rat) : oaboveR w q -> primeo q /\ q != 2%:R.
Proof.
  move=> [ -> [ _ [ Hp [ Hq _ ] ] ] ]; split; first by apply/ord_PR.
  by rewrite eqr_nat.
Qed.

(* ordinary version of trPL1, function form *)
Lemma ord_PL1R (q : rat) : primeo q -> q != 2%:R -> oaboveR (oplaceR q) q.
Proof.
  move=> Hq Hq2; have [ E Hp ] := primeo_nat Hq.
  split; first exact: E.
  apply: ord_PL1 => //; apply: contraNneq Hq2 => H; by rewrite E H.
Qed.

(* ordinary version of trPL2_int *)
Lemma ord_PL2_intR (w : OPl) (q : rat) (x : qe rat) : oaboveR w q -> x != 0 ->
  isZo (ovP w x)%:~R.
Proof. by move=> _ _; exists (ovP w x). Qed.

(* ordinary version of trPL2_mul, in sQ = rat *)
Lemma ord_PL2_mulR (w : OPl) (q : rat) (x y : qe rat) : oaboveR w q -> x != 0 -> y != 0 ->
  (ovP w (x * y))%:~R = (ovP w x)%:~R + (ovP w y)%:~R :> rat.
Proof. by move=> [ _ Hw ] Hx Hy; rewrite (ord_PL2_mul Hw) // intrD. Qed.

(* ordinary version of trPL2_ultra, in sQ = rat *)
Lemma ord_PL2_ultraR (w : OPl) (q : rat) (x y : qe rat) : oaboveR w q ->
  x != 0 -> y != 0 -> x + y != 0 ->
  Num.min (ovP w x)%:~R (ovP w y)%:~R <= (ovP w (x + y))%:~R :> rat.
Proof.
  move=> [ _ Hw ] Hx Hy Hxy; have H := ord_PL2_ultra Hw Hx Hy Hxy.
  by rewrite ge_min !ler_int -!ge_min.
Qed.

(* ordinary version of trPL3 *)
Lemma ord_PL3R (w : OPl) (q x : rat) : oaboveR w q -> x != 0 -> ovP w (qe_of x) = vqo q x.
Proof. by move=> [ -> Hw ] _; rewrite (ord_PL3 Hw) vqo_nat. Qed.

(** * Arbitrary places above an odd prime (FixedData.is_place_above)

    For any multiplicative, ultrametric v : F^x -> Z with v(p) = 1 and p
    odd: the restriction of v to Q is v_p ("Ostrowski-lite"), v(sqrt2) = 0,
    and v >= 0 on Z[sqrt2]. These are used with the abstract places of the
    ordinary statements O_F1, O_F2 of OrdHyps. *)

Lemma qe_of0 : qe_of 0 = 0 :> qe rat.
Proof. by []. Qed.

Section any_place.

  Variable p : nat.
  Hypothesis p_prime : prime p.
  Hypothesis p_odd : p != 2%N.
  Variable v : qe rat -> int.
  Hypothesis Hv : is_place_above v p.

  Let vM : forall x y, x != 0 -> y != 0 -> v (x * y) = v x + v y.
  Proof. by case: Hv. Qed.
  Let vU : forall x y, x != 0 -> y != 0 -> x + y != 0 -> Num.min (v x) (v y) <= v (x + y).
  Proof. by case: Hv => _ []. Qed.
  Let vp : v p%:R = 1.
  Proof. by case: Hv => _ []. Qed.

  Local Abbreviation vo x := (v (qe_of x)).

  Lemma qe_of_neq0 (x : rat) : x != 0 -> qe_of x != 0.
  Proof. by move=> Hx; apply/eqP => [] [] /eqP; rewrite (negbTE Hx). Qed.

  Lemma vo_mul (x y : rat) : x != 0 -> y != 0 -> vo (x * y) = vo x + vo y.
  Proof using vM. by move=> Hx Hy; rewrite qe_of_mul vM ?qe_of_neq0. Qed.

  Lemma vo1 : vo 1 = 0.
  Proof using vM.
    have := vo_mul (oner_neq0 rat) (oner_neq0 rat); rewrite mulr1.
    move: (v (qe_of 1)) => a H; ilia.
  Qed.

  Lemma voN1 : vo (-1) = 0.
  Proof using vM.
    have H1 : (-1 : rat) != 0 by rewrite oppr_eq0 oner_neq0.
    have := vo_mul H1 H1; rewrite mulrNN mulr1 vo1.
    move: (v (qe_of (-1))) => a H; ilia.
  Qed.

  Lemma voN (x : rat) : x != 0 -> vo (- x) = vo x.
  Proof using vM.
    move=> Hx; rewrite -mulN1r vo_mul ?oppr_eq0 ?oner_neq0 // voN1 add0r //.
  Qed.

  Lemma voV (x : rat) : x != 0 -> vo x^-1 = - vo x.
  Proof using vM.
    move=> Hx; have := vo_mul Hx (invr_neq0 Hx); rewrite mulfV // vo1 => /eqP.
    by rewrite eq_sym addr_eq0 => /eqP ->; rewrite opprK.
  Qed.

  Lemma vo_ultra (x y : rat) : x != 0 -> y != 0 -> x + y != 0 ->
    Num.min (vo x) (vo y) <= vo (x + y).
  Proof using vU. by move=> Hx Hy Hxy; rewrite qe_of_add vU ?qe_of_neq0 // -qe_of_add qe_of_neq0. Qed.

  Lemma vo_add_ge (x y : rat) (k : int) : x != 0 -> y != 0 -> x + y != 0 ->
    k <= vo x -> k <= vo y -> k <= vo (x + y).
  Proof using vU.
    move=> Hx Hy Hxy H1 H2; apply: le_trans (vo_ultra Hx Hy Hxy); by rewrite le_min H1 H2.
  Qed.

  Lemma vo_nat_ge0 (n : nat) : (0 < n)%N -> 0 <= vo n%:R.
  Proof using vM vU.
    elim: n => [ // | [ | n ] IH _ ]; first by rewrite vo1.
    rewrite -addn1 natrD; apply: vo_add_ge; rewrite ?pnatr_eq0 ?oner_neq0 -?natrD ?pnatr_eq0 ?addn1 //.
    - exact: IH.
    - by rewrite vo1.
  Qed.

  Lemma vo_int_ge0 (z : int) : z != 0 -> 0 <= vo z%:~R.
  Proof using vM vU.
    case: z => n Hn.
    - by rewrite -natr_intr; apply: vo_nat_ge0; rewrite lt0n; apply: contraNneq Hn => ->.
    - rewrite NegzE intrN voN ?oppr_eq0 ?intr_eq0 // -natr_intr; exact: vo_nat_ge0.
  Qed.

  Lemma vo_p : vo p%:R = 1.
  Proof using vp. by rewrite -vp qe_natE. Qed.

  Lemma vo_pexp (k : nat) : vo (p%:R ^+ k) = k%:Z.
  Proof using vM vp p_prime.
    have Hp0 : p%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n prime_gt0.
    elim: k => [ | k IH ]; first by rewrite expr0 vo1.
    by rewrite exprS vo_mul ?expf_neq0 // IH vo_p PoszS addrC.
  Qed.

  (* integers prime to p are units *)
  Lemma vo_unit (n : nat) : (0 < n)%N -> ~~ (p %| n)%N -> vo n%:R = 0.
  Proof using vM vU vp p_prime.
    move=> Hn Hpn.
    have Hcop : coprimez n%:Z p%:Z by rewrite coprimezE /= coprime_sym prime_coprime.
    have [ u [ w Huw ] ] := Bezoutz n%:Z p%:Z.
    move: Hcop; rewrite /coprimez => /eqP Hg; rewrite Hg in Huw.
    have E : (u%:~R * n%:R + w%:~R * p%:R : rat) = 1.
    { have := congr1 (fun z : int => z%:~R : rat) Huw; by rewrite /= intrD !intrM -!natr_intr. }
    have Hn0 : n%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n.
    have Hp0 : p%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n prime_gt0.
    apply/eqP; rewrite eq_le vo_nat_ge0 // andbT; rewrite leNgt; apply/negP => Hpos.
    case: (eqVneq u 0) => Hu.
    - move: E; rewrite Hu mul0r add0r => E.
      have Hw : w != 0 by apply: contra_eq_neq E => ->; rewrite mul0r eq_sym oner_neq0.
      have := congr1 (fun x => vo x) E; rewrite /= vo_mul ?intr_eq0 // vo1 vo_p.
      have := vo_int_ge0 Hw => H0 H1; move: H0; rewrite -[vo _]addr0 -(subrr 1) addrA H1 => /=.
      by rewrite sub0r oppr_ge0.
    case: (eqVneq w 0) => Hw.
    - move: E; rewrite Hw mul0r addr0 => E.
      have := congr1 (fun x => vo x) E; rewrite /= vo_mul ?intr_eq0 // vo1 => H0.
      have := vo_int_ge0 Hu; move: Hpos H0; move: (vo u%:~R) (vo n%:R) => a b Ha Hab Hb.
      ilia.
    - have Hx : u%:~R * n%:R != 0 :> rat by rewrite mulf_neq0 ?intr_eq0.
      have Hy : w%:~R * p%:R != 0 :> rat by rewrite mulf_neq0 ?intr_eq0.
      have Hxy : u%:~R * n%:R + w%:~R * p%:R != 0 :> rat by rewrite E oner_neq0.
      have := vo_add_ge (k := 1) Hx Hy Hxy.
      rewrite E vo1 vo_mul ?intr_eq0 // vo_mul ?intr_eq0 // vo_p.
      have := vo_int_ge0 Hu; have := vo_int_ge0 Hw.
      move: Hpos; move: (vo u%:~R) (vo n%:R) (vo w%:~R) => a b c Hb Hc Ha H.
      have : (1 <= (0 : int)) -> False by [].
      move=> HF; apply: HF; apply: H; ilia.
  Qed.

  (* Ostrowski-lite: the restriction of v to Q is v_p *)
  Lemma vo_int (z : int) : z != 0 -> vo z%:~R = (logn p `|z|)%:Z.
  Proof using vM vU vp p_prime.
    move=> Hz.
    have -> : vo z%:~R = vo (`|z|%N)%:R.
    { case: z Hz => n Hn; first by rewrite -natr_intr.
      by rewrite NegzE intrN voN ?oppr_eq0 ?intr_eq0 // -natr_intr. }
    set n := `|z|%N.
    have Hn : (0 < n)%N by rewrite absz_gt0.
    set l := logn p n.
    have Hdvd := pfactor_dvdnn p n; rewrite -/l in Hdvd.
    set m := (n %/ p ^ l)%N.
    have En : n = (p ^ l * m)%N by rewrite mulnC divnK.
    have Hm : (0 < m)%N by move: Hn; rewrite En muln_gt0 => /andP [].
    have Hpm : ~~ (p %| m)%N.
    { apply/negP => Hpm.
      have : (p ^ l.+1 %| n)%N by rewrite En expnSr dvdn_mul.
      by rewrite pfactor_dvdn // -/l ltnn. }
    have Hp0 : p%:R ^+ l != 0 :> rat by rewrite expf_neq0 // pnatr_eq0 -lt0n prime_gt0.
    have Hm0 : m%:R != 0 :> rat by rewrite pnatr_eq0 -lt0n.
    rewrite En natrM natrX vo_mul // vo_pexp vo_unit // addr0.
    by [].
  Qed.

  Theorem vo_vqr (x : rat) : x != 0 -> vo x = vqr p x.
  Proof using vM vU vp p_prime.
    move=> Hx.
    have Hn : numq x != 0 by rewrite numq_eq0.
    have Hd : denq x != 0 := denq_neq0 x.
    rewrite -[x in LHS]divq_num_den vo_mul ?invr_eq0 ?intr_eq0 // voV ?intr_eq0 //.
    by rewrite !vo_int // /vqr.
  Qed.

  Lemma v_sqrt2 : v qe_sqrt2 = 0.
  Proof using vM vU vp p_prime p_odd.
    have Hs : qe_sqrt2 != 0 :> qe rat.
    { apply/eqP => /(congr1 (@qim rat)) /= /eqP; by rewrite oner_eq0. }
    have := vM Hs Hs; rewrite qe_sqrt2_sqr.
    have -> : (2%:R : qe rat) = qe_of 2%:R by rewrite qe_natE.
    rewrite vo_vqr ?pnatr_eq0 // vqr_2 //.
    move: (v qe_sqrt2) => a H; ilia.
  Qed.

  (* nonnegativity on Z[sqrt2] *)
  Theorem v_Zsqrt2_ge0 (a b : int) : QE (a%:~R : rat) b%:~R != 0 -> 0 <= v (QE a%:~R b%:~R).
  Proof using vM vU vp p_prime p_odd.
    move=> Hx.
    have E : QE (a%:~R : rat) b%:~R = qe_of a%:~R + qe_of b%:~R * qe_sqrt2.
    { by rewrite /qe_of /qe_sqrt2 qe_mulE qe_addE; congr QE; ring. }
    have Hs : qe_sqrt2 != 0 :> qe rat.
    { apply/eqP => /(congr1 (@qim rat)) /= /eqP; by rewrite oner_eq0. }
    case: (eqVneq a 0) => Ha.
    - have Hb : b != 0 by apply: contraNneq Hx => Hb; rewrite Ha Hb.
      rewrite E Ha qe_of0 add0r vM ?qe_of_neq0 ?intr_eq0 // v_sqrt2 addr0.
      exact: vo_int_ge0.
    case: (eqVneq b 0) => Hb.
    - rewrite E Hb qe_of0 mul0r addr0; exact: vo_int_ge0.
    have Hbs : qe_of b%:~R * qe_sqrt2 != 0 :> qe rat := qe_mul_neq0 (qe_of_neq0 (intr_neq0 Hb)) Hs.
    rewrite E; apply: le_trans (vU (qe_of_neq0 (intr_neq0 Ha)) Hbs _); last by rewrite -E.
    rewrite le_min vo_int_ge0 // vM ?qe_of_neq0 ?intr_eq0 // v_sqrt2 addr0.
    exact: vo_int_ge0.
  Qed.

End any_place.
