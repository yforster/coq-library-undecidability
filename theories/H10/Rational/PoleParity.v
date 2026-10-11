(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Prop par:pole-parity, part 2 (Lemma par:soundness of
   03-parity.tex), as a theorem: for any multiplier lists, if a nonzero
   rational b satisfies Phi(b) and q is a prime outside S_1, then
   v_q(b) < 0 implies that v_q(b) is even. This proves the field
   [O_PP2] of [OrdHyps] (FixedData.v), see [PP2_thm].

   The proof follows the paper:
   - if k = v_q(b) < 0 is odd, then v_q(d) = v_q(b') = v_q(U) = k,
     v_q(b' - U^2) = 2k and v_q(H') = 3k (the case analysis on the
     sign of the odd valuation v_q(d t^2));
   - one of e, eH' has even valuation;
   - on y^2 = x (x - l) (x + 3l) with v_q(l) even and q <> 3 every
     nonzero x has even valuation [curve_even] (three cases
     v_q(x) <, =, > v_q(l); no rescaling needed);
   - but x = b' z^2 has odd valuation. *)

From Stdlib Require Import ZArith Lia List.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData RatVal.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

Lemma In_mem (T : eqType) (x : T) (s : seq T) : List.In x s -> x \in s.
Proof.
  elim: s => [ // | y s IH ] /= [ -> | /IH H ]; rewrite inE ?eqxx //.
  by rewrite H orbT.
Qed.

(* the members of the lists have support inside S_1 *)
Lemma S1_support (D : FixedData) (q : nat) mm Dm x :
  List.In (mm, Dm) (fd_PhiL D) -> (x = mm \/ List.In x Dm) ->
  q \notin S1 D -> q \notin rat_support x.
Proof.
  move=> HmD Hx; apply: contra => Hq.
  rewrite /S1 !inE; apply/orP; right; apply/orP; right.
  apply/flatten_mapP; exists x => //.
  apply/flatten_mapP; exists (mm, Dm); first exact: In_mem.
  rewrite /= inE; case: Hx => [ -> | /In_mem -> ]; by rewrite ?eqxx ?orbT.
Qed.

Lemma S1_3 (D : FixedData) (q : nat) : q \notin S1 D -> q != 3%N.
Proof. by rewrite /S1 !inE !negb_or => /andP [ _ /andP [ H _ ] ]. Qed.

Section curve.

  Variable q : nat.
  Hypothesis q_prime : prime q.
  Hypothesis q_ne3 : q != 3%N.

  Local Abbreviation v := (vqr q).

  Lemma vqr3 : v 3%:R = 0.
  Proof using q_prime q_ne3.
    apply: vqr_nat_ndvd.
    by rewrite dvdn_prime2.
  Qed.

  Lemma vqr_3l (l : rat) : l != 0 -> 3%:R * l != 0 /\ v (3%:R * l) = v l.
  Proof using q_prime q_ne3.
    move=> Hl; have H3 : 3%:R != 0 :> rat by [].
    by rewrite mulf_neq0 // vqrM // vqr3 add0r.
  Qed.

  (* on  y^2 = x (x - l) (x + 3l)  with v(l) even, every nonzero x has
     even valuation *)
  Lemma curve_even (l x y : rat) : l != 0 -> x != 0 -> ~~ odd `|v l| ->
    y ^+ 2 = x * (x - l) * (x + 3%:R * l) -> ~~ odd `|v x|.
  Proof using q_prime q_ne3.
    move=> Hl Hx Hvl Hy.
    have [H3l Hv3l] := vqr_3l Hl.
    have Hnl : - l != 0 by rewrite oppr_eq0.
    (* both sides are nonzero; take valuations *)
    have key : forall a c : rat, a != 0 -> c != 0 ->
      x - l = a -> x + 3%:R * l = c -> v y + v y = v x + v a + v c.
    { move=> a c Ha Hc Ea Ec.
      have HR : x * a * c != 0 by rewrite !mulf_neq0.
      have Hy0 : y != 0.
      { apply/eqP => Hy0; move: HR; by rewrite -Ea -Ec -Hy Hy0 expr2 mulr0 eqxx. }
      by rewrite -vqrX2 // Hy Ea Ec !vqrM // mulf_neq0. }
    case: (ltrgtP (v x) (v l)) => Hc.
    - (* v x < v l: all three factors have valuation v x *)
      have [Ha Hva] := @vqr_add_lt q q_prime x (- l) Hx Hnl ltac:(by rewrite vqrN).
      have [Hb Hvb] := @vqr_add_lt q q_prime x (3%:R * l) Hx H3l ltac:(by rewrite Hv3l).
      have := key _ _ Ha Hb erefl erefl.
      rewrite Hva Hvb => /(congr1 (fun k : int => odd `|k|)).
      by rewrite odd_dbl (odd_add (v x + v x)) odd_dbl /= => <-.
    - (* v l < v x: the other two factors have valuation v l *)
      have [Ha Hva] := @vqr_add_lt q q_prime (- l) x Hnl Hx ltac:(by rewrite vqrN).
      have [Hb Hvb] := @vqr_add_lt q q_prime (3%:R * l) x H3l Hx ltac:(by rewrite Hv3l).
      rewrite [- l + x]addrC in Ha Hva; rewrite [3%:R * l + x]addrC in Hb Hvb.
      have := key _ _ Ha Hb erefl erefl.
      rewrite Hva Hvb vqrN Hv3l => /(congr1 (fun k : int => odd `|k|)).
      by rewrite odd_dbl -addrA odd_add_dbl => <-.
    - by rewrite Hc.
  Qed.

  (* no point of  E_l  has x-coordinate in  b' Q^{x2}  if v(l) is even
     and v(b') is odd *)
  Lemma El_point_odd (l b' : rat) : l != 0 -> b' != 0 ->
    ~~ odd `|v l| -> odd `|v b'| -> ~ El_point l b'.
  Proof using q_prime q_ne3.
    move=> Hl Hb' Hvl Hvb' [x [y [z [Hz [Hx Hy]]]]].
    have Hx0 : x != 0 by rewrite Hx mulf_neq0 // expf_neq0.
    have := curve_even Hl Hx0 Hvl Hy.
    by rewrite Hx vqrM ?expf_neq0 // vqrX2 // odd_add_dbl Hvb'.
  Qed.

End curve.

(** * Lemma par:soundness *)

Section soundness.

  Variable q : nat.
  Hypothesis q_prime : prime q.
  Hypothesis q_ne3 : q != 3%N.

  Local Abbreviation v := (vqr q).

  Lemma Phi_soundness (b mm md t e : rat) :
    b != 0 -> mm != 0 -> md != 0 ->
    q \notin rat_support mm -> q \notin rat_support md ->
    let d := md * b in
    let b' := mm * b in
    let H' := b' * (b' - Phi_U d b t ^+ 2) in
    1 + d * t ^+ 2 != 0 -> e * H' != 0 -> El_point e b' -> El_point (e * H') b' ->
    v b < 0 -> ~~ odd `|v b|.
  Proof using q_prime q_ne3.
    move=> Hb Hmm Hmd Smm Smd d b' H' Hnz1 HeH P1 P2 Hneg.
    apply/negP => Hodd.
    set k := v b in Hneg Hodd.
    have Hd : d != 0 by rewrite mulf_neq0.
    have Hb' : b' != 0 by rewrite mulf_neq0.
    have vd : v d = k by rewrite vqrM // vqr_unit // add0r.
    have vb' : v b' = k by rewrite vqrM // vqr_unit // add0r.
    set w := d * t ^+ 2 in Hnz1.
    (* the quotient (1 - w)/(1 + w) is a unit *)
    have Hw : 1 - w != 0 /\ v (1 - w) = v (1 + w).
    { case: (eqVneq t 0) => [ Ht | Ht ].
      - by rewrite /w Ht expr2 !mulr0 subr0 ?addr0 oner_eq0.
      have Hw0 : w != 0 by rewrite mulf_neq0 // expf_neq0.
      have Hnw : - w != 0 by rewrite oppr_eq0.
      have H10 : (1 : rat) != 0 by rewrite oner_eq0.
      have vw : odd `|v w| by rewrite vqrM ?expf_neq0 // vqrX2 // vd odd_add_dbl.
      case: (ltrgtP (v w) 0) => Hc.
      + have [Ha Hva] := @vqr_add_lt q q_prime w 1 Hw0 H10 ltac:(by rewrite vqr1).
        have [Hb2 Hvb] := @vqr_add_lt q q_prime (- w) 1 Hnw H10 ltac:(by rewrite vqr1 vqrN).
        rewrite [w + 1]addrC in Ha Hva; rewrite [- w + 1]addrC in Hb2 Hvb.
        by rewrite Hva Hvb vqrN.
      + have [Ha Hva] := @vqr_add_lt q q_prime 1 w H10 Hw0 ltac:(by rewrite vqr1).
        have [Hb2 Hvb] := @vqr_add_lt q q_prime 1 (- w) H10 Hnw ltac:(by rewrite vqr1 vqrN).
        by rewrite Hva Hvb.
      + by move: vw; rewrite Hc. }
    have [Hw1 Hvw] := Hw.
    have HU : Phi_U d b t = b * (1 - w) / (1 + w) by [].
    have HU0 : (Phi_U d b t) != 0 by rewrite HU !mulf_neq0 ?invr_eq0.
    have vU : v (Phi_U d b t) = k by rewrite HU vqr_div ?mulf_neq0 // vqrM // Hvw addrK.
    have Hkk : k + k < k.
    { apply/iz_lt; rewrite iz_add; move: Hneg => /iz_lt /=; lia. }
    have HU2 : - (Phi_U d b t) ^+ 2 != 0 by rewrite oppr_eq0 expf_neq0.
    have [HS0 vS] := @vqr_add_lt q q_prime (- (Phi_U d b t) ^+ 2) b' HU2 Hb' ltac:(by rewrite vqrN vqrX2 // vU vb').
    rewrite [- (Phi_U d b t) ^+ 2 + b']addrC vqrN vqrX2 // vU in HS0 vS.
    have HH0 : H' != 0 by rewrite mulf_neq0.
    have vH : v H' = k + (k + k) by rewrite vqrM // vS vb'.
    have He : e != 0 by move: HeH; rewrite mulf_eq0 negb_or => /andP [].
    have vk3 : odd `|k + (k + k)| by rewrite odd_add_dbl.
    case Hve : (odd `|v e|).
    - (* v(e H') = v e + 3k is even *)
      apply: (El_point_odd q_prime q_ne3 HeH Hb' _ _ P2); last by rewrite vb'.
      by rewrite vqrM // vH odd_add Hve vk3.
    - apply: (El_point_odd q_prime q_ne3 He Hb' _ _ P1); last by rewrite vb'.
      by rewrite Hve.
  Qed.

End soundness.

(** * Prop par:pole-parity, part 2: the field [O_PP2] of [OrdHyps] *)

Theorem PP2_thm (D : FixedData) : FixedWF D ->
  forall b : rat, b != 0 -> Phi_holdsR (fd_PhiL D) b ->
  forall q : nat, prime q -> q \notin S1 D -> vqr q b < 0 -> ~~ odd (absz (vqr q b)).
Proof.
  move=> WF b Hb /Phi_holds_iff [ Hb0 | [ _ [ mm [ Dm [ md [ t [ e [ HmD [ Hmd ] ] ] ] ] ] ] ] ].
  { by move: Hb; rewrite Hb0 eqxx. }
  rewrite /= !ratr_id => [[ Hnz1 [ HeH [ P1 P2 ] ] ]] q Hq HS.
  have [ Hmm [ _ HDm ] ] := wf_PhiL WF HmD.
  apply: (@Phi_soundness q Hq (S1_3 HS) b mm md t e) => //.
  - exact: HDm.
  - apply: (S1_support HmD _ HS); by left.
  - apply: (S1_support HmD _ HS); by right.
Qed.
