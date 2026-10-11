(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2C, part 4: two bridges between the ordinary data of FixedData.v
   and valuations, completing the ordinary versions of Ambient fields.

   1. Scaling invariance of odd contact (Ambient.trH1). The contact radical
      [MK_ord] counts the primes q with odd contact in the REDUCED
      coordinates (num s, den s); trH1 speaks of arbitrary homogeneous
      coordinates (u, v), v <> 0, with depths  v_q(L_b(u,v)) - mn(u,v),
      mn(u,v) = min(v_q u, v_q v)  (v_q 0 = +oo, as Ambient.mnA), and
      L_oo = V. Multiplying (u, v) by c <> 0 adds v_q(c) to all of them.
      - [mnr]                  mn(u, v), int-valued
      - [contact_depths]       the depths in (u, v) are those in (num, den)
      - [odd_contact_homog]    odd_contact D q (u/v) = odd contact in (u, v)
                               (an equality: both directions)
      - [ord_H1]               the ordinary version of trH1, read at
                               sQ = rat with vq := vqo, MK := MK_ord,
                               using Ambient's goodA, mnA, oddZ.
   2. LocZ / FormalZ at a split prime r (r odd, B^2 = 2 mod r, branch
      sqrt2 |-> s B). For ANY place v above r (FixedData.is_place_above)
      with v(sqrt2 - sB) >= 1 ([tcq c] is sqrt2 - c):
      - [LocZ_val]    alpha <> 0 -> LocZ i r B s alpha -> i <= v alpha
      - [val_LocZ]    alpha <> 0 -> i <= v alpha -> LocZ i r B s alpha
      - [FormalZ_red] FormalZ sg r B s P -> (x-coordinate <> 0) -> red_ord sg v P
      The ordinary place is [wsplit r B s] = (r, sg) with sg = false iff
      s B = qroot r (mod r), i.e. iff the branch is the Hensel root
      [hroot r] (and sg = true: the branch -hroot r):
      - [wsplit_above]  oabove (wsplit r B s) r
      - [wsplit_root]   1 <= ovP (wsplit r B s) (sqrt2 - s B)
      - [LocZ_ovP]      alpha <> 0 -> (LocZ i r B s alpha <-> i <= ovP w alpha)
      - [FormalZ_ovP]   FormalZ -> red_ord at ovP w
      - [*_int]         the same with r : int, 0 < r, prime |r| (RepSpec form).

   No axioms. *)

From Stdlib Require Import ZArith Lia List.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData Ambient RatVal
                 OrdinaryFacts OrdPlaces OrdHeights.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.


(** * 1. Scaling invariance of the contact depths (trH1) *)

Section scaling.

  Variable D : FixedData.
  Variable q : nat.
  Hypothesis q_prime : prime q.

  Local Abbreviation v := (vqr q).

  (* min (v_q u, v_q v) with v_q 0 = +oo, as Ambient.mnA *)
  Definition mnr (u w : rat) : int := if u == 0 then v w else Num.min (v u) (v w).

  Lemma min_addl (a b c : int) : Num.min (a + b) (a + c) = a + Num.min b c.
  Proof.
    case: (lerP b c) => H.
    - by rewrite !min_l // lerD2l.
    - by rewrite !min_r ?lerD2l // ltW.
  Qed.

  Lemma mnr_scale (c u w : rat) : c != 0 -> w != 0 ->
    mnr (c * u) (c * w) = v c + mnr u w.
  Proof.
    move=> Hc Hw; rewrite /mnr mulf_eq0 (negbTE Hc) /=.
    case: ifP => Hu; first by rewrite vqrM.
    by rewrite !vqrM ?Hu // min_addl.
  Qed.

  Lemma mnr_numden (s : rat) : mnr (numq s)%:~R (denq s)%:~R = 0.
  Proof using q_prime.
    rewrite /mnr intr_eq0 !vqr_int.
    case: ifP => Hn.
    - have -> : s = 0 by apply/eqP; rewrite -numq_eq0 Hn.
      by rewrite /= logn1.
    have Hcop := coprime_num_den s.
    have : (logn q `|numq s| = 0)%N \/ (logn q `|denq s| = 0)%N.
    { case E1 : (logn q `|numq s|) => [ | a ]; first by left.
      case E2 : (logn q `|denq s|) => [ | b ]; first by right.
      exfalso.
      have H1 : (0 < logn q `|numq s|)%N by rewrite E1.
      have H2 : (0 < logn q `|denq s|)%N by rewrite E2.
      move: H1 H2; rewrite !logn_gt0 !mem_primes => /and3P [ _ _ D1 ] /and3P [ _ _ D2 ].
      have : (q %| gcdn `|numq s| `|denq s|)%N by rewrite dvdn_gcd D1 D2.
      move: Hcop; rewrite /coprime => /eqP ->; rewrite dvdn1 => /eqP Hq1.
      by move: q_prime; rewrite Hq1. }
    case=> ->; [ apply: min_l | apply: min_r ]; by rewrite lez_nat.
  Qed.

  Lemma fd_L_scale (c : rat) (i : i4) (n d : int) :
    fd_L D i (c * n%:~R) (c * d%:~R) = c * (fd_Lint D i n d)%:~R.
  Proof. rewrite /fd_L /fd_Lint intrB !intrM; ring. Qed.

  (* the reduced representative of u / v *)
  Lemma homog_rep (u w : rat) : w != 0 ->
    let c := w / (denq (u / w))%:~R in
    c != 0 /\ u = c * (numq (u / w))%:~R /\ w = c * (denq (u / w))%:~R.
  Proof.
    move=> Hw c.
    have Hd : (denq (u / w))%:~R != 0 :> rat by rewrite intr_eq0 denq_neq0.
    split; first by rewrite /c mulf_neq0 ?invr_eq0.
    split; last by rewrite /c divfK.
    rewrite /c -mulrA [_^-1 * _]mulrC -[(numq _)%:~R / _]/((numq (u / w))%:~R / (denq (u / w))%:~R).
    by rewrite divq_num_den mulrC divfK.
  Qed.

  (* the contact depths in arbitrary homogeneous coordinates (u, w) are the
     q-adic orders of den(s) and L_i(num s, den s), s = u / w *)
  Theorem contact_depths (u w : rat) : w != 0 -> (forall i, fd_L D i u w != 0) ->
       v w - mnr u w = (logn q `|denq (u / w)|)%:Z
    /\ forall i, fd_Lint D i (numq (u / w)) (denq (u / w)) != 0
                 /\ v (fd_L D i u w) - mnr u w
                    = (logn q `|fd_Lint D i (numq (u / w)) (denq (u / w))|)%:Z.
  Proof using q_prime.
    move=> Hw HL.
    have [ Hc [ Eu Ew ] ] := homog_rep u Hw.
    move: (w / _) Hc Eu Ew => c Hc Eu Ew.
    move: (u / w) Eu Ew => s Eu Ew.
    have Hd : (denq s)%:~R != 0 :> rat by rewrite intr_eq0 denq_neq0.
    have Em : mnr u w = v c.
    { by rewrite Eu Ew mnr_scale // mnr_numden addr0. }
    rewrite Em; split.
    - by rewrite Ew vqrM // vqr_int addrC addKr.
    - move=> i; have H := HL i; rewrite Eu Ew fd_L_scale in H *.
      have Hi : fd_Lint D i (numq s) (denq s) != 0.
      { by apply: contraNneq H => ->; rewrite mulr0. }
      split => //.
      by rewrite vqrM ?intr_eq0 // vqr_int addrC addKr.
  Qed.

  (* scaling invariance: odd_contact (in the reduced coordinates) is odd
     contact in arbitrary homogeneous coordinates *)
  Theorem odd_contact_homog (u w : rat) : w != 0 -> (forall i, fd_L D i u w != 0) ->
    odd_contact D q (u / w)
    = odd `|v w - mnr u w| || has (fun i => odd `|v (fd_L D i u w) - mnr u w|) all_i4.
  Proof using q_prime.
    move=> Hw HL; have [ E1 E2 ] := contact_depths Hw HL.
    rewrite /odd_contact E1 absz_nat; congr orb.
    have Heq : (fun i => odd (logn q `|fd_Lint D i (numq (u / w)) (denq (u / w))|))
               =1 (fun i => odd `|v (fd_L D i u w) - mnr u w|).
    { move=> i /=; by have [ _ -> ] := E2 i. }
    by rewrite (eq_has Heq).
  Qed.

End scaling.

(** ** The ordinary version of trH1, exactly as Ambient reads it at sQ = rat *)

(* the parity predicate of Ambient at the ordinary integers *)
Lemma oddZ_int (z : int) : oddZ isZo (z%:~R : rat) <-> odd `|z|.
Proof.
  split.
  - move=> [ y [ [ w -> ] Hz ] ].
    have E : z = (w + w) + 1.
    { apply: (@intr_inj rat); by rewrite Hz intrD intrD mulr2n -mulr2n mulr_natl. }
    by rewrite E odd_add odd_dbl.
  - move=> Ho; have [ Hh [ E | E ] ] := ord_Z2_fun (ord_Z1_int z).
    + exfalso; move: Hh => [ w Hw ]; move: E; rewrite Hw => E.
      have Ez : z = w + w.
      { apply: (@intr_inj rat); by rewrite E intrD mulr_natl mulr2n. }
      by move: Ho; rewrite Ez odd_dbl.
    + by exists (zhalf z%:~R).
Qed.

Lemma mnA_vqo (q : nat) (u w : rat) :
  mnA (fun x => (vqo q%:R x)%:~R) u w = ((mnr q u w)%:~R : rat).
Proof.
  rewrite /mnA /mnr !vqo_nat; case: ifP => _ //.
  case: (lerP (vqr q u) (vqr q w)) => H.
  - by rewrite !min_l // ler_int.
  - by rewrite !min_r // ?ler_int ltW.
Qed.

Lemma has_ex (T : Type) (a : pred T) (l : seq T) : has a l -> exists x, a x.
Proof. elim: l => [ // | x l IH ] /= /orP [ H | /IH // ]; by exists x. Qed.

Section ordH1.

  Variable D : FixedData.

  (* trH1, ordinary: MK K (u/v) is a positive integer, and its primes are
     good and have odd contact depth in the coordinates (u, v) *)
  Theorem ord_H1 (K : nat) (u w : rat) : w != 0 -> (forall i, fd_L D i u w != 0) ->
    isZo (MK_ord D K (u / w))%:R /\ 1 <= (MK_ord D K (u / w))%:R :> rat /\
    forall q : rat, primeo q -> 0 < vqo q (MK_ord D K (u / w))%:R ->
      goodA D K q /\
      (oddZ isZo ((vqo q w)%:~R - mnA (fun x => (vqo q x)%:~R) u w)
       \/ exists i, oddZ isZo ((vqo q (fd_L D i u w))%:~R - mnA (fun x => (vqo q x)%:~R) u w)).
  Proof.
    move=> Hw HL; have [ H1 H2 ] := ord_H1_int D K (u / w).
    do 2 (split => //).
    move=> q Hq; have [ Eq Hp ] := primeo_nat Hq.
    move: (`|numq q|)%N Eq Hp => p -> Hp.
    rewrite vqo_nat vqr_MK // ltz_nat => Hdvd.
    have Hd : (p %| MK_ord D K (u / w))%N by case: (p %| _)%N Hdvd.
    split.
    - have := MK_ord_good Hp Hd; rewrite /good => /andP [ Hlt HS ].
      split; first by rewrite ltr_nat.
      move=> p' Hp'; rewrite eqr_nat; apply: contraNneq HS => ->; exact: Hp'.
    - have := MK_ord_odd_contact Hp Hd; rewrite (odd_contact_homog Hp Hw HL).
      rewrite mnA_vqo !vqo_nat -!intrB.
      case/orP => [ Ho | Ho ]; [ left; exact/oddZ_int | right ].
      have [ i Hi ] := has_ex Ho.
      exists i; rewrite ?mnA_vqo ?vqo_nat -?intrB; exact/oddZ_int.
  Qed.

End ordH1.

(** * 2. Localizations at a split prime: LocZ and FormalZ versus valuations *)

(* sqrt2 - c *)
Definition tcq (c : int) : qe rat := QE (- c%:~R) 1.

Lemma tcq_neq0 c : tcq c != 0.
Proof. by apply/eqP => [] [] _ /eqP; rewrite oner_eq0. Qed.

Lemma qe_one_of : (1 : qe rat) = qe_of 1.
Proof. by []. Qed.

Lemma qe_oppN1 (x : qe rat) : - x = qe_of (-1) * x.
Proof. by case: x => a b; rewrite /qe_of qe_mulE qe_oppE; congr QE; ring. Qed.

Lemma qe_intpow (r : nat) (i : nat) : ((r%:Z)%:~R ^+ i : qe rat) = qe_of (r%:R ^+ i).
Proof. by rewrite pmulrn -natrX qe_natE natrX. Qed.

Lemma qe_intpow_neq0 (r : nat) (i : nat) : (0 < r)%N -> ((r%:Z)%:~R ^+ i : qe rat) != 0.
Proof. by move=> Hr; rewrite qe_intpow qe_of_neq0 // expf_neq0 // pnatr_eq0 -lt0n. Qed.

Lemma dvdz_prime_1 (r : nat) : prime r -> ~~ (r%:Z %| 1)%Z.
Proof. move=> Hr; rewrite dvdzE /= dvdn1; apply/negP => /eqP H; by move: Hr; rewrite H. Qed.

Section split_bridge.

  Variable r : nat.
  Hypothesis r_prime : prime r.
  Hypothesis r_odd : r != 2%N.
  Variable v : qe rat -> int.
  Hypothesis Hv : is_place_above v r.
  Variable c : int.
  Hypothesis c_root : (r%:Z %| c ^+ 2 - 2)%Z.
  Hypothesis c_place : 1 <= v (tcq c).

  Let vM : forall x y, x != 0 -> y != 0 -> v (x * y) = v x + v y.
  Proof. by case: Hv. Qed.
  Let vU : forall x y, x != 0 -> y != 0 -> x + y != 0 -> Num.min (v x) (v y) <= v (x + y).
  Proof. by case: Hv => _ []. Qed.

  Lemma vb1 : v 1 = 0.
  Proof using Hv. rewrite qe_one_of; exact: vo1 Hv. Qed.

  Lemma vbN (x : qe rat) : x != 0 -> v (- x) = v x.
  Proof using Hv.
    move=> Hx; rewrite qe_oppN1 vM ?qe_of_neq0 ?oppr_eq0 ?oner_eq0 //.
    by rewrite (voN1 Hv) add0r.
  Qed.

  (* the strict ultrametric inequality *)
  Lemma vb_strict (x y : qe rat) : x != 0 -> y != 0 -> v x < v y ->
    x + y != 0 /\ v (x + y) = v x.
  Proof using Hv.
    move=> Hx Hy Hlt.
    have Hxy : x + y != 0.
    { apply/eqP => H0; have Ey : y = - x by apply/eqP; rewrite -addr_eq0 addrC H0.
      by move: Hlt; rewrite Ey vbN // ltxx. }
    split => //.
    have H1 := vU Hx Hy Hxy.
    have Hny : - y != 0 by rewrite oppr_eq0.
    have Hs : x + y + - y != 0 by rewrite addrK.
    have H2 := vU Hxy Hny Hs; rewrite addrK vbN // in H2.
    move: H1 H2; rewrite (min_l (ltW Hlt)).
    case: (lerP (v (x + y)) (v y)) => H.
    - move=> H1 H2; apply/eqP; by rewrite eq_le H1 H2.
    - move=> H1 H2; exfalso; move: Hlt; by rewrite ltNge H2.
  Qed.

  Lemma vb_int (z : int) : z != 0 -> v (qe_of z%:~R) = (logn r `|z|)%:Z.
  Proof using Hv r_prime. move=> Hz; by rewrite (vo_vqr r_prime Hv) ?intr_eq0 // vqr_int. Qed.

  Lemma vb_pow (i : nat) : v ((r%:Z)%:~R ^+ i) = i%:Z.
  Proof using Hv r_prime. by rewrite qe_intpow (vo_pexp r_prime Hv). Qed.

  Lemma decomp_tc (Y0 Y1 : int) :
    QE (Y0%:~R : rat) Y1%:~R = qe_of (Y0 + c * Y1)%:~R + qe_of Y1%:~R * tcq c.
  Proof. by rewrite /qe_of /tcq qe_mulE qe_addE intrD intrM; congr QE; ring. Qed.

  (* an element of Z[sqrt2] whose image under sqrt2 |-> c is prime to r is a unit at v *)
  Lemma vb_unit (Y0 Y1 : int) : ~~ (r%:Z %| Y0 + c * Y1)%Z ->
    QE (Y0%:~R : rat) Y1%:~R != 0 /\ v (QE Y0%:~R Y1%:~R) = 0.
  Proof using Hv r_prime c_place.
    move=> Hn; rewrite decomp_tc.
    move: (Y0 + c * Y1) Hn => a Hn.
    have Ha : a != 0 by apply: contraNneq Hn => ->; exact: dvdz0.
    have Ea : v (qe_of a%:~R) = 0.
    { rewrite vb_int // logn_ndvd //; by rewrite dvdzE in Hn. }
    have Ha' : qe_of (a%:~R : rat) != 0 by rewrite qe_of_neq0 ?intr_eq0.
    case: (eqVneq Y1 0) => H1.
    - by rewrite H1 mulr0z qe_of0 mul0r addr0.
    have Hb : qe_of (Y1%:~R : rat) * tcq c != 0.
    { by rewrite qe_mul_neq0 ?tcq_neq0 // qe_of_neq0 ?intr_eq0. }
    have Hvb : 0 < v (qe_of Y1%:~R * tcq c).
    { rewrite vM ?tcq_neq0 ?qe_of_neq0 ?intr_eq0 // vb_int //.
      move: c_place; move: (v (tcq c)) (logn r `|Y1|) => t n Ht; ilia. }
    have [ H H' ] := vb_strict Ha' Hb ltac:(by rewrite Ea).
    by rewrite H' Ea.
  Qed.

  (* conversely, divisibility of the image gives positive valuation *)
  Lemma vb_root_ge1 (Z0 Z1 : int) : (r%:Z %| Z0 + c * Z1)%Z -> QE (Z0%:~R : rat) Z1%:~R != 0 ->
    1 <= v (QE Z0%:~R Z1%:~R).
  Proof using Hv r_prime c_place.
    move=> /dvdz_ex [ t Ht ] HZ; move: HZ; rewrite decomp_tc Ht => HZ.
    have Hr0 : r%:Z != 0 by rewrite eqz_nat -lt0n prime_gt0.
    have Ht1 : 1 <= v (qe_of (r%:Z * t)%:~R) \/ t = 0.
    { case: (eqVneq t 0) => Ht0; [ by right | left ].
      rewrite vb_int ?mulf_neq0 // abszM lognM ?absz_gt0 //= logn_prime // eqxx.
      by rewrite PoszD lerDl. }
    case: (eqVneq Z1 0) => H1.
    - move: HZ; rewrite H1 mulr0z qe_of0 mul0r addr0 => HZ.
      case: Ht1 => // Ht0; move: HZ; by rewrite Ht0 mulr0 mulr0z qe_of0 eqxx.
    have Hb : qe_of (Z1%:~R : rat) * tcq c != 0.
    { by rewrite qe_mul_neq0 ?tcq_neq0 // qe_of_neq0 ?intr_eq0. }
    have Hvb : 1 <= v (qe_of Z1%:~R * tcq c).
    { rewrite vM ?tcq_neq0 ?qe_of_neq0 ?intr_eq0 // vb_int //.
      move: c_place; move: (v (tcq c)) (logn r `|Z1|) => t0 n Ht0; ilia. }
    case: (eqVneq t 0) => Ht0.
    - move: HZ; by rewrite Ht0 mulr0 mulr0z qe_of0 add0r.
    case: Ht1 => [ Ht1 | Ht2 ]; last by move: Ht0; rewrite Ht2 eqxx.
    have Ha : qe_of ((r%:Z * t)%:~R : rat) != 0 by rewrite qe_of_neq0 ?intr_eq0 ?mulf_neq0.
    have := vU Ha Hb HZ; apply: le_trans; by rewrite le_min Ht1 Hvb.
  Qed.

  Lemma not_dvd_unit (a iota kappa : int) : a * iota - 1 = r%:Z * kappa -> ~~ (r%:Z %| a)%Z.
  Proof using r_prime.
    move=> E; apply/negP => /dvdz_ex [ t Ht ].
    apply/negP: (dvdz_prime_1 r_prime).
    apply/negPn; apply: (@ex_dvdz _ _ (t * iota - kappa)).
    transitivity (a * iota - (a * iota - 1)); first ring.
    by rewrite E Ht; ring.
  Qed.

  (* LocZ gives a lower bound on the valuation *)
  Theorem LocZ_val (i : nat) (B : int) (s : sgn) (alpha : qe rat) : c = sgnz s * B ->
    alpha != 0 -> LocZ i r%:Z B s alpha -> i%:Z <= v alpha.
  Proof using Hv r_prime r_odd c_place.
    move=> Ec Ha [ X0 [ X1 [ Y0 [ Y1 [ io [ ka [ E Hu ] ] ] ] ] ] ].
    rewrite -Ec in Hu.
    have [ HY HvY ] := vb_unit (not_dvd_unit Hu).
    have HaY := qe_mul_neq0 Ha HY.
    have Hp := qe_intpow_neq0 i (prime_gt0 r_prime).
    have HX : QE (X0%:~R : rat) X1%:~R != 0.
    { apply: contraNneq HaY => H0; by rewrite E H0 mulr0. }
    have := congr1 v E; rewrite vM // vM // HvY addr0 vb_pow => ->.
    by rewrite lerDl (v_Zsqrt2_ge0 r_prime r_odd Hv).
  Qed.

  Lemma vb_inv (z : qe rat) : z != 0 -> z^-1 != 0 /\ v z^-1 = - v z.
  Proof using Hv.
    move=> Hz.
    have Hu : z \is a GRing.unit by rewrite qe_unitE qe_norm_neq0.
    have Hz' : z^-1 != 0.
    { apply/eqP => H; have := mulVr Hu; rewrite H mul0r => /eqP; by rewrite eq_sym oner_eq0. }
    split => //; have := vM Hz' Hz; rewrite mulVr // vb1 => /eqP.
    by rewrite eq_sym addr_eq0 => /eqP.
  Qed.

  (* FormalZ means reduction to O at v *)
  Theorem FormalZ_red (sg : bool) (B : int) (s : sgn) (P : pt rat) : c = sgnz s * B ->
    FormalZ sg r%:Z B s P -> (forall x y, P = Some (x, y) -> qe_e sg x != 0) -> red_ord sg v P.
  Proof using Hv r_prime r_odd c_place.
    move=> Ec; case: P => [ [ x y ] | ] //= HL Hx.
    have Hx' := Hx x y erefl.
    have [ Hz Ez ] := vb_inv Hx'.
    have := LocZ_val Ec Hz HL; rewrite Ez => H.
    rewrite -oppr_gt0; exact: lt_le_trans H.
  Qed.

End split_bridge.

(** ** The converse: a lower bound on the valuation gives LocZ *)

Lemma qe_conj_neq0 (x : qe rat) : x != 0 -> qe_conj x != 0.
Proof.
  move=> Hx; apply: contraNneq Hx => H.
  by rewrite -(qe_conjK x) H /qe_conj /= oppr0.
Qed.

Lemma qe_conj_nat (n : nat) : qe_conj (n%:R : qe rat) = n%:R.
Proof. by rewrite qe_natE /qe_conj /= oppr0. Qed.

(* the conjugate place  x |-> v (conj x) *)
Lemma conj_place (r : nat) (v : qe rat -> int) : is_place_above v r ->
  is_place_above (fun x => v (qe_conj x)) r.
Proof.
  move=> [ vM [ vU vp ] ]; split; [ | split ].
  - move=> x y Hx Hy; by rewrite qe_conj_mul vM ?qe_conj_neq0.
  - move=> x y Hx Hy Hxy; by rewrite qe_conj_add vU ?qe_conj_neq0 // -qe_conj_add qe_conj_neq0.
  - by rewrite qe_conj_nat.
Qed.

Lemma conj_tcq (c : int) : qe_conj (tcq (- c)) = - tcq c.
Proof. by rewrite /tcq /qe_conj qe_oppE /= intrN opprK. Qed.

(* Z[sqrt2] *)
Definition isZs (x : qe rat) : Prop := exists a b : int, x = QE a%:~R b%:~R.

Lemma isZs_mul x y : isZs x -> isZs y -> isZs (x * y).
Proof.
  move=> [ a [ b -> ] ] [ c [ d -> ] ]; exists (a * c + 2 * (b * d)), (a * d + b * c).
  by rewrite qe_mulE !intrD !intrM; congr QE; rewrite -?natr_intr.
Qed.

Lemma isZs_of (z : int) : isZs (qe_of z%:~R).
Proof. by exists z, 0. Qed.

Lemma isZs_exp x m : isZs x -> isZs (x ^+ m).
Proof.
  move=> Hx; elim: m => [ | m IH ]; first by exists 1, 0; rewrite expr0.
  by rewrite exprS; apply: isZs_mul.
Qed.

Lemma qe_exp_neq0 (x : qe rat) m : x != 0 -> x ^+ m != 0.
Proof.
  move=> Hx; elim: m => [ | m IH ]; first by rewrite expr0 oner_eq0.
  by rewrite exprS qe_mul_neq0.
Qed.

Lemma qe_of_unit (a : rat) : a != 0 -> qe_of a \is a GRing.unit.
Proof.
  move=> Ha; rewrite qe_unitE /qe_norm /= expr0n /= mulr0 subr0.
  by rewrite expf_neq0.
Qed.

Lemma dvdz_primeM (r : nat) (a b : int) : prime r ->
  (r%:Z %| a * b)%Z -> (r%:Z %| a)%Z || (r%:Z %| b)%Z.
Proof. move=> Hr; by rewrite !dvdzE abszM /= Euclid_dvdM. Qed.

Lemma place_exp (r : nat) (v : qe rat -> int) : is_place_above v r ->
  forall (x : qe rat) (m : nat), x != 0 -> v (x ^+ m) = m%:Z * v x.
Proof.
  move=> Hv x m Hx; have [ vM _ ] := Hv.
  elim: m => [ | m IH ]; first by rewrite expr0 mul0r; exact: vb1 Hv.
  by rewrite exprS vM ?qe_exp_neq0 // IH PoszS mulrDl mul1r addrC.
Qed.

Section converse.

  Variable r : nat.
  Hypothesis r_prime : prime r.
  Hypothesis r_odd : r != 2%N.
  Variable v : qe rat -> int.
  Hypothesis Hv : is_place_above v r.
  Variable c : int.
  Hypothesis c_root : (r%:Z %| c ^+ 2 - 2)%Z.
  Hypothesis c_place : 1 <= v (tcq c).

  Local Abbreviation v' := (fun x => v (qe_conj x)).

  Let Hv' : is_place_above v' r. Proof. exact: conj_place. Qed.

  Let vM : forall x y, x != 0 -> y != 0 -> v (x * y) = v x + v y.
  Proof. by case: Hv. Qed.
  Let vM' : forall x y, x != 0 -> y != 0 -> v' (x * y) = v' x + v' y.
  Proof. by case: Hv'. Qed.

  Let c_place' : 1 <= v' (tcq (- c)).
  Proof. by rewrite /= conj_tcq (vbN Hv) ?tcq_neq0. Qed.

  Let c_root' : (r%:Z %| (- c) ^+ 2 - 2)%Z.
  Proof. by rewrite sqrrN. Qed.

  Let r_ndvd_2c : ~~ (r%:Z %| 2 * c)%Z.
  Proof.
    have /eqP Hcop := root_coprime r_prime r_odd c_root.
    apply/negP => H.
    have : (r%:Z %| gcdz r%:Z (2 * c))%Z by rewrite dvdz_gcd dvdzz H.
    rewrite Hcop; exact/negP/dvdz_prime_1.
  Qed.

  (* positive valuation at v and at its conjugate means divisibility by r^k in Z[sqrt2] *)
  Lemma div_both (k : nat) (Z0 Z1 : int) : QE (Z0%:~R : rat) Z1%:~R != 0 ->
    k%:Z <= v (QE Z0%:~R Z1%:~R) -> k%:Z <= v' (QE Z0%:~R Z1%:~R) ->
    exists X0 X1 : int, QE (Z0%:~R : rat) Z1%:~R = (r%:Z)%:~R ^+ k * QE X0%:~R X1%:~R.
  Proof using Hv r_prime r_odd c_root c_place.
    elim: k Z0 Z1 => [ | k IH ] Z0 Z1 HZ H1 H2; first by exists Z0, Z1; rewrite expr0 mul1r.
    have D1 : (r%:Z %| Z0 + c * Z1)%Z.
    { apply/negPn/negP => Hn; have [ _ E ] := vb_unit r_prime Hv c_place Hn.
      move: H1; rewrite E => H0; exfalso; ilia. }
    have D2 : (r%:Z %| Z0 + (- c) * Z1)%Z.
    { apply/negPn/negP => Hn; have [ _ E ] := vb_unit r_prime Hv' c_place' Hn.
      move: H2; rewrite E => H0; exfalso; ilia. }
    have D3 : (r%:Z %| (2 * c) * Z1)%Z.
    { have -> : (2 * c) * Z1 = (Z0 + c * Z1) - (Z0 + (- c) * Z1) by ring.
      by rewrite rpredB. }
    have D4 : (r%:Z %| Z1)%Z by move: (dvdz_primeM r_prime D3); rewrite (negbTE r_ndvd_2c).
    have D5 : (r%:Z %| Z0)%Z.
    { have -> : Z0 = (Z0 + c * Z1) - c * Z1 by ring.
      by rewrite rpredB // dvdz_mull. }
    move: D4 D5 => /dvdz_ex [ W1 E1 ] /dvdz_ex [ W0 E0 ].
    have Hr : (r%:Z)%:~R != 0 :> qe rat.
    { rewrite -pmulrn qe_natE; apply/eqP => [] [] /eqP; rewrite pnatr_eq0; apply/negP.
      by rewrite -lt0n prime_gt0. }
    have ER : (r%:Z)%:~R = qe_of (r%:R : rat) by rewrite -pmulrn qe_natE.
    have E : QE (Z0%:~R : rat) Z1%:~R = (r%:Z)%:~R * QE W0%:~R W1%:~R.
    { by rewrite ER /qe_of qe_mulE E0 E1 !intrM -pmulrn; congr QE; ring. }
    have HW : QE (W0%:~R : rat) W1%:~R != 0 by apply: contraNneq HZ => H0; rewrite E H0 mulr0.
    have Vr : v (r%:Z)%:~R = 1 by rewrite -pmulrn; case: Hv => _ [].
    have Vr' : v' (r%:Z)%:~R = 1 by rewrite /= -pmulrn qe_conj_nat; case: Hv => _ [].
    have [ X0 [ X1 EX ] ] : exists X0 X1 : int,
        QE (W0%:~R : rat) W1%:~R = (r%:Z)%:~R ^+ k * QE X0%:~R X1%:~R.
    { apply: IH => //.
      - move: H1; rewrite E vM // Vr PoszS addrC lerD2l. by [].
      - move: H2; rewrite E vM' // Vr' PoszS addrC lerD2l. by []. }
    exists X0, X1; by rewrite E EX exprS mulrA.
  Qed.

  (* the converse of LocZ_val *)
  Theorem val_LocZ (i : nat) (B : int) (s : sgn) (alpha : qe rat) : c = sgnz s * B ->
    alpha != 0 -> i%:Z <= v alpha -> LocZ i r%:Z B s alpha.
  Proof using Hv r_prime r_odd c_root c_place.
    move=> Ec Ha Hi.
    (* clearing denominators *)
    have [ n [ A0 [ A1 [ Hn EA ] ] ] ] : exists (n : nat) (A0 A1 : int),
        (0 < n)%N /\ alpha * qe_of n%:R = QE A0%:~R A1%:~R.
    { case: alpha {Ha Hi} => a b.
      exists (`|denq a| * `|denq b|)%N, (numq a * denq b), (numq b * denq a); split.
      - by rewrite muln_gt0 !absz_gt0 !denq_neq0.
      - have Ea : a * (denq a)%:~R = (numq a)%:~R.
        { by rewrite -{1}(divq_num_den a) divfK // intr_eq0 denq_neq0. }
        have Eb : b * (denq b)%:~R = (numq b)%:~R.
        { by rewrite -{1}(divq_num_den b) divfK // intr_eq0 denq_neq0. }
        have En : ((`|denq a| * `|denq b|)%N%:R : rat) = (denq a)%:~R * (denq b)%:~R.
        { by rewrite natrM !natr_intr !gtz0_abs ?denq_gt0. }
        rewrite En /qe_of qe_mulE !mulr0 addr0 add0r !intrM; congr QE.
        + by rewrite mulrA Ea.
        + by rewrite mulrCA Eb mulrC. }
    (* the r-part of the denominator *)
    set e := logn r n.
    have [ n' [ En' Hn' ] ] : exists n', n = (r ^ e * n')%N /\ ~~ (r %| n')%N.
    { exists (n %/ r ^ e)%N; split; first by rewrite mulnC divnK // pfactor_dvdnn.
      apply/negP => Hpm.
      have : (r ^ e.+1 %| n)%N.
      { by rewrite -[X in (_ %| X)%N](divnK (pfactor_dvdnn r n)) expnSr mulnC dvdn_mul. }
      by rewrite pfactor_dvdn // ltnn. }
    have Hn'0 : (0 < n')%N by move: Hn; rewrite En' muln_gt0 => /andP [].
    (* sqrt2 + c, a unit at v and divisible at the conjugate place *)
    set T : qe rat := QE c%:~R 1.
    have ET : T = QE c%:~R (1 : int)%:~R by [].
    have HT : T != 0 by apply/eqP => [] [] _ /eqP; rewrite oner_eq0.
    have VT : v T = 0.
    { have Hn2 : ~~ (r%:Z %| c + c * 1)%Z.
      { have -> : c + c * 1 = 2 * c by ring. exact: r_ndvd_2c. }
      have [ _ E ] := vb_unit r_prime Hv c_place Hn2; by rewrite ET. }
    have VT' : 1 <= v' T.
    { have -> : qe_conj T = - tcq c by rewrite /T /tcq /qe_conj qe_oppE opprK.
      by rewrite /= (vbN Hv) ?tcq_neq0. }
    set m := (e + i)%N.
    have HTm := qe_exp_neq0 m HT.
    have Hn0 : (n%:R : rat) != 0 by rewrite pnatr_eq0 -lt0n.
    have Hn'0' : (n'%:R : rat) != 0 by rewrite pnatr_eq0 -lt0n.
    have HA : QE (A0%:~R : rat) A1%:~R != 0 by rewrite -EA qe_mul_neq0 // qe_of_neq0.
    set Y := qe_of n'%:R * T ^+ m.
    set Z := QE (A0%:~R : rat) A1%:~R * T ^+ m.
    have HY : Y != 0 by rewrite qe_mul_neq0 // qe_of_neq0.
    have HZ : Z != 0 by rewrite qe_mul_neq0.
    have [ Y0 [ Y1 EY ] ] : isZs Y.
    { apply: isZs_mul; [ rewrite natr_intr; exact: isZs_of | apply: isZs_exp; by exists c, 1 ]. }
    have [ Z0 [ Z1 EZ ] ] : isZs Z.
    { apply: isZs_mul; [ by exists A0, A1 | apply: isZs_exp; by exists c, 1 ]. }
    have VY : v Y = 0.
    { rewrite vM ?qe_of_neq0 // (place_exp Hv) // VT mulr0 addr0 natr_intr (vb_int r_prime Hv) //.
      - by rewrite eqz_nat -lt0n.
      - by rewrite /= logn_ndvd. }
    have Vn : v (qe_of n%:R) = e%:Z.
    { by rewrite natr_intr (vb_int r_prime Hv) // eqz_nat -lt0n. }
    have VZ : (e + i)%N%:Z <= v Z.
    { rewrite vM // (place_exp Hv) // VT mulr0 addr0 -EA vM ?qe_of_neq0 // Vn.
      by rewrite PoszD addrC lerD2r. }
    have VZ' : (e + i)%N%:Z <= v' Z.
    { have E := vM' HA HTm; have E2 := place_exp Hv' m HT; rewrite /= in E E2.
      rewrite /Z /= E E2.
      have H0 := v_Zsqrt2_ge0 r_prime r_odd Hv' HA.
      have H1 : m%:Z * 1 <= m%:Z * v' T by rewrite ler_wpM2l.
      rewrite mulr1 in H1; rewrite -[X in X <= _]add0r; exact: lerD. }
    rewrite EZ in HZ VZ VZ'.
    have [ X0 [ X1 EX ] ] := div_both HZ VZ VZ'.
    rewrite -EZ in EX.
    (* the unit condition *)
    have Hu : ~~ (r%:Z %| Y0 + c * Y1)%Z.
    { apply/negP => H; have HY' : QE (Y0%:~R : rat) Y1%:~R != 0 by rewrite -EY.
      have := vb_root_ge1 r_prime Hv c_place H HY'; by rewrite -EY VY. }
    have Hcop : coprimez r%:Z (Y0 + c * Y1).
    { by rewrite coprimezE /= prime_coprime // -[X in (_ %| X)%N]/(`|Y0 + c * Y1|)%N -dvdzE. }
    have [ u [ w Huw ] ] := Bezoutz r%:Z (Y0 + c * Y1).
    move: Hcop; rewrite /coprimez => /eqP Hg; rewrite Hg in Huw.
    exists X0, X1, Y0, Y1, w, (- u); rewrite -Ec; split; last first.
    { have -> : (Y0 + c * Y1) * w - 1 = (u * r%:Z + w * (Y0 + c * Y1)) - 1 - u * r%:Z by ring.
      rewrite Huw; ring. }
    (* cancel the r-part of the denominator *)
    set R : qe rat := qe_of (r%:R ^+ e).
    have HR : R \is a GRing.unit by rewrite qe_of_unit // expf_neq0 // pnatr_eq0 -lt0n prime_gt0.
    apply: (mulIr HR).
    rewrite -EY.
    have E1 : alpha * Y * R = Z.
    { rewrite /Y /Z /R -EA En' natrM natrX qe_of_mul; ring. }
    rewrite E1 EX /R -qe_intpow -mulrA [_ * (_ ^+ e)]mulrC mulrA -exprD addnC.
    by [].
  Qed.

End converse.

(** ** The ordinary place selected by a root B of 2 modulo r and a sign s *)

(* The two places above a split r are sqrt2 |-> +- (the Hensel root lifting
   qroot r). The branch sqrt2 |-> sgnz s * B is the place (r, false) when
   sgnz s * B = qroot r mod r, and (r, true) when sgnz s * B = - qroot r mod r. *)
Definition wsplit (r : nat) (B : int) (s : sgn) : OPl :=
  (r, ~~ (r%:Z %| sgnz s * B - (qroot r)%:Z)%Z).

Lemma sgnz_sqr (s : sgn) (B : int) : (sgnz s * B) ^+ 2 = B ^+ 2.
Proof. by case: s; rewrite /sgnz ?mul1r ?mulN1r ?sqrrN. Qed.

Section wsplit.

  Variable r : nat.
  Hypothesis r_prime : prime r.
  Hypothesis r_odd : r != 2%N.
  Variable B : int.
  Hypothesis B_root : exists wB : int, B ^+ 2 - 2 = r%:Z * wB.
  Variable s : sgn.

  Local Abbreviation c := (sgnz s * B).

  Lemma c_root_of : (r%:Z %| c ^+ 2 - 2)%Z.
  Proof using B_root.
    have [ wB E ] := B_root; by rewrite sgnz_sqr E dvdz_mulr.
  Qed.

  Lemma split_of_root : qsplitb r.
  Proof using r_prime B_root.
    have [ wB E ] := B_root.
    apply/negPn/negP => H; have := inert_hyp r_prime H B; by rewrite (ex_dvdz E).
  Qed.

  Lemma wsplit_above : oabove (wsplit r B s) r.
  Proof using r_prime r_odd B_root.
    split => //; do 2 (split => //); move=> _; exact: split_of_root.
  Qed.

  Lemma hroot_cong K : exists m : int, hroot r K - (qroot r)%:Z = r%:Z * m.
  Proof using r_prime r_odd B_root.
    have [ H1 H2 ] := hroot_hyps r_prime r_odd split_of_root.
    by have [ _ ] := hensel_inv H1 H2 K.
  Qed.

  Lemma vqr_dvd1 (z : int) : z != 0 -> (r%:Z %| z)%Z -> 1 <= vqr r z%:~R.
  Proof using r_prime.
    move=> Hz Hd; rewrite (vqr_dvd_int r_prime 1 Hz) expn1; by rewrite dvdzE in Hd.
  Qed.

  (* the place w = wsplit r B s satisfies w(sqrt2 - s B) >= 1 *)
  Theorem wsplit_root : 1 <= ovP (wsplit r B s) (tcq c).
  Proof using r_prime r_odd B_root.
    have Hs := split_of_root.
    rewrite /ovP /= Hs.
    have [ t Ht ] : exists t : int, (c - (qroot r)%:Z) * (c + (qroot r)%:Z) = r%:Z * t.
    { have [ t1 E1 ] := dvdz_ex c_root_of.
      have [ t2 E2 ] := dvdz_ex (qroot_spec Hs).
      exists (t1 - t2).
      transitivity ((c ^+ 2 - 2) - ((qroot r)%:Z ^+ 2 - 2)); first ring.
      by rewrite E1 E2; ring. }
    have Hx := tcq_neq0 c.
    case Hd : (r%:Z %| c - (qroot r)%:Z)%Z => /=.
    - have [ Hnz E ] := vsp_spec r_prime (hroot_root r_prime r_odd Hs) (hroot_step r_prime r_odd Hs)
                          Hx (le_n (bnd r (tcq c))).
      have [ m Hm ] := hroot_cong (bnd r (tcq c)).
      move: (bnd r (tcq c)) Hnz E Hm => K Hnz E Hm.
      rewrite -E; move: Hnz; rewrite /phi /sK /tcq /= mul1r -intrN -intrD => Hnz.
      apply: vqr_dvd1; first by apply: contraNneq Hnz => ->.
      have [ t' Ht' ] := dvdz_ex Hd.
      apply: (@ex_dvdz _ _ (m - t')).
      transitivity ((hroot r K - (qroot r)%:Z) - (c - (qroot r)%:Z)); first ring.
      by rewrite Hm Ht'; ring.
    - have Hd' : (r%:Z %| c + (qroot r)%:Z)%Z.
      { have := dvdz_primeM r_prime (ex_dvdz Ht); by rewrite Hd. }
      have [ Hnz E ] := vsp_spec r_prime (hroot_root_neg r_prime r_odd Hs)
                          (hroot_step_neg r_prime r_odd Hs) Hx (le_n (bnd r (tcq c))).
      have [ m Hm ] := hroot_cong (bnd r (tcq c)).
      move: (bnd r (tcq c)) Hnz E Hm => K Hnz E Hm.
      rewrite -E; move: Hnz; rewrite /phi /sK /tcq /= mul1r -intrN -intrD => Hnz.
      apply: vqr_dvd1; first by apply: contraNneq Hnz => ->.
      have [ t' Ht' ] := dvdz_ex Hd'.
      apply: (@ex_dvdz _ _ (- m - t')).
      transitivity (- (hroot r K - (qroot r)%:Z) - (c + (qroot r)%:Z)); first ring.
      by rewrite Hm Ht'; ring.
  Qed.

  Lemma wsplit_place : is_place_above (ovP (wsplit r B s)) r.
  Proof using r_prime r_odd B_root. exact: ovP_is_place wsplit_above. Qed.

  (* the bridge at the split prime r, for the branch sqrt2 |-> s B *)
  Theorem LocZ_ovP (i : nat) (alpha : qe rat) : alpha != 0 ->
    LocZ i r%:Z B s alpha <-> i%:Z <= ovP (wsplit r B s) alpha.
  Proof using r_prime r_odd B_root.
    move=> Ha; split.
    - exact: (LocZ_val r_prime r_odd wsplit_place wsplit_root erefl Ha).
    - exact: (val_LocZ r_prime r_odd wsplit_place c_root_of wsplit_root erefl Ha).
  Qed.

  Theorem FormalZ_ovP (sg : bool) (P : pt rat) : FormalZ sg r%:Z B s P ->
    (forall x y, P = Some (x, y) -> qe_e sg x != 0) -> red_ord sg (ovP (wsplit r B s)) P.
  Proof using r_prime r_odd B_root.
    exact: (FormalZ_red r_prime r_odd wsplit_place wsplit_root erefl).
  Qed.

End wsplit.

(** ** The same with the prime given as a positive int (as in RepSpec) *)

Section wsplit_int.

  Variables (r B : int) (s : sgn).
  Hypothesis r_pos : 0 < r.
  Hypothesis r_prime : prime `|r|.
  Hypothesis r_odd : `|r| != 2%N.
  Hypothesis B_root : exists wB : int, B ^+ 2 - 2 = r * wB.

  Let Er : r = (`|r|%N)%:Z. Proof. by rewrite gtz0_abs. Qed.

  Let B_root' : exists wB : int, B ^+ 2 - 2 = (`|r|%N)%:Z * wB.
  Proof. by rewrite -Er. Qed.

  Theorem LocZ_ovP_int (i : nat) (alpha : qe rat) : alpha != 0 ->
    LocZ i r B s alpha <-> i%:Z <= ovP (wsplit `|r| B s) alpha.
  Proof using r_pos r_prime r_odd B_root.
    rewrite {1}Er; exact: LocZ_ovP.
  Qed.

  Theorem FormalZ_ovP_int (sg : bool) (P : pt rat) : FormalZ sg r B s P ->
    (forall x y, P = Some (x, y) -> qe_e sg x != 0) -> red_ord sg (ovP (wsplit `|r| B s)) P.
  Proof using r_pos r_prime r_odd B_root.
    rewrite {1}Er; exact: FormalZ_ovP.
  Qed.

  Lemma wsplit_above_int : oabove (wsplit `|r| B s) `|r|.
  Proof using r_pos r_prime r_odd B_root. exact: wsplit_above. Qed.

  Lemma wsplit_root_int : 1 <= ovP (wsplit `|r| B s) (tcq (sgnz s * B)).
  Proof using r_pos r_prime r_odd B_root. exact: wsplit_root. Qed.

End wsplit_int.
