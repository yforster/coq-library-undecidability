(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The kernel-of-reduction lemma (PLAN.md, Phase 2D, task P11):
   05-elliptic.tex, Prop ell:formal, eq. ell:ratio, without power series;
   from it the fields E2 (StdHyps) and O_F1 (OrdHyps) for the explicit
   data [mkData] of ExplicitData.v.

   ROUTE (elementary, Silverman IV.1-IV.2 with exact identities instead of
   formal power series). v is any [is_place_above v p] (multiplicative,
   ultrametric, v(p) = 1, junk at 0); nothing else about v is used: v >= 0
   on Z[sqrt2] and v(aE) >= 0 are derived (v(1) = 0, ultrametricity,
   v(sqrt2)^2 = v(2)), and v(n) = 0 for n prime to p by Bezout. Good
   reduction is NOT needed (v(aE) >= 0 suffices), so p \notin S_E is unused.
   1. [kv], [kv']: a point (x, y) with x <> 0, v(x) < 0 has v(z) = k >= 1
      and v(w) = 3k for z = -x/y, w = -1/y; conversely v(w) >= 1 gives
      v(x) < 0.
   2. [line_step], [add_kern]: for P1, P2 in the kernel with v(z_i) >= k,
      the line y = l x + m through them (chord or tangent) is, in the
      (z, w) chart, w = lam z + nu with lam = -l/m and nu = -1/m. Exact
      identities ([chord_free], [tangent_free], proved by [field] for the
      curve y^2 = x^3 + A x + B with A, B interpolated, then specialised to
      B = 0): lam * D = N with N = z1^2 + z1 z2 + z2^2 + a w2^2,
      D = 1 - a z1 (w1 + w2), and the Vieta relation
      z(P1 + P2) = z1 + z2 + 2 a lam nu / (1 + a lam^2).
      Valuations: v(N) >= 2k, v(D) = 0, v(lam) >= 2k, v(nu) >= 3k,
      v(1 + a lam^2) = 0, hence v(z(P1+P2) - z1 - z2) >= 3k, and
      P1 + P2 is O or again in the kernel. (m <> 0 and y3 <> 0 follow from
      the identities; no case P1 + P2 = (0,0) arises.)
   3. [mul_kern]: for a homomorphism Pn : Z -> E(F) and R = Pn b in the
      kernel with v(z(R)) >= k: z(nR) = n z(R) mod p^(3k), by induction on
      n using only Pn (n + n') = Pn n + Pn n'.
   4. [mul_val]: if v(n) < 2 v(z(R)) then nR <> O, nR is in the kernel and
      v(z(nR)) = v(n) + v(z(R)); this gives (KR) [kernel_KR] (p does not
      divide n) and (KR') [kernel_KR'] (n = p), and by induction on v_p(n)
      [kernel_mul]: v(z(nR)) = v(z(R)) + v_p(n) for all n <> 0, and the
      ratio form [kernel_ratio] (eq. ell:ratio).
   5. Applications:
      - general D (with [on_curve (fd_P0 D)]):
        [E2_of_nontorsion]: nontorsion of P0 implies the field E2;
        [nontorsion_of_kernel]: one nonzero multiple bP0 with v(x) < 0 at
        some place implies nontorsion;
        [O_F1_of_E2]: E2 and 0 < fd_m D imply the field O_F1 (both curves:
        sg = true uses the conjugate place x |-> v(sigma x), [conj_place]).
      - explicit data: [pole_val] (bridging TODO (a) of ExplicitData.v),
        [place17_sqrt2_6] (every place above 17 or its conjugate sends
        sqrt2 to 6), [mkData_10_kernel], [mkData_nontorsion], [E2_mkData],
        [O_F1_mkData], and [StdHyps_mkData] (E2 slots into StdHyps).

   TO-MERGE section hypotheses (all three are discharged by existing
   theorems, checked by a scratch build; see the comments at their
   declarations):
   - [mulQ_on_h]  = GroupLaw.mulQ_on  (on_curve_pt is our [onp]);
   - [mulQ_add_h] = GroupLaw.mulQ_add;
   - [place17]    : exists v, is_place_above v 17, e.g.
     OrdPlaces.ovP_is_place (OrdPlaces.ord_PL1 (q := 17) isT isT).

   Implementation notes. [KRF] is a copy of [qe rat] carrying a field
   structure (for [field]); terms of [qe rat] and [KRF] are convertible.
   [aK] is a locked copy of [aE] so that unification never unfolds unary
   literals. No axioms. *)

From Stdlib Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData RatVal ExplicitData.
Import Order.TTheory GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.
Local Open Scope ring_scope.

Section free.
  Variable K : fieldType.
  Implicit Types l m A B : K.

  Definition zc (x : K) l m : K := - x / (l * x + m).
  Definition wc (x : K) l m : K := - 1 / (l * x + m).
  Definition Nf A (z1 z2 w2 : K) : K := z1 ^+ 2 + z1 * z2 + z2 ^+ 2 + A * w2 ^+ 2.
  Definition Df A B (z1 w1 w2 : K) : K := 1 - A * z1 * (w1 + w2) - B * (w1 ^+ 2 + w1 * w2 + w2 ^+ 2).
  Definition x3f (x1 x2 : K) l : K := l ^+ 2 - x1 - x2.
  Definition y3f (x1 x2 : K) l m : K := l * (x1 - x3f x1 x2 l) - (l * x1 + m).
  Definition Ef A B l m : K := 1 + A * (- l / m) ^+ 2 + B * (- l / m) ^+ 3.
  Definition Cf A B l m : K := 2%:R * A * (- l / m) * (- 1 / m) + 3%:R * B * (- l / m) ^+ 2 * (- 1 / m).

  Definition VB A B (x1 x2 : K) l m : K :=
    Ef A B l m * (x3f x1 x2 l + y3f x1 x2 l m * (zc x1 l m + zc x2 l m))
    + y3f x1 x2 l m * Cf A B l m.
  Definition CB A B (x1 x2 : K) l m : K :=
    Nf A (zc x1 l m) (zc x2 l m) (wc x2 l m) * (1 + l * zc x1 l m)
    - l * wc x1 l m * Df A B (zc x1 l m) (wc x1 l m) (wc x2 l m).

  Lemma chord_free (x1 x2 : K) l m A B :
    x2 - x1 != 0 -> l * x1 + m != 0 -> l * x2 + m != 0 ->
    A = (((l * x2 + m) ^+ 2 - x2 ^+ 3) - ((l * x1 + m) ^+ 2 - x1 ^+ 3)) / (x2 - x1) ->
    B = (l * x1 + m) ^+ 2 - x1 ^+ 3 - A * x1 ->
    CB A B x1 x2 l m = 0 /\ (m != 0 -> VB A B x1 x2 l m = 0).
  Proof.
    move=> H1 H2 H3 HA HB; subst B A; split.
    - rewrite /CB /Nf /Df /zc /wc; field.
    - move=> Hm; rewrite /VB /Ef /Cf /y3f /x3f /zc; field.
  Qed.

  Lemma tangent_free (x1 : K) l m A B :
    l * x1 + m != 0 ->
    A = 2%:R * (l * x1 + m) * l - 3%:R * x1 ^+ 2 ->
    B = (l * x1 + m) ^+ 2 - x1 ^+ 3 - A * x1 ->
    CB A B x1 x1 l m = 0 /\ (m != 0 -> VB A B x1 x1 l m = 0).
  Proof.
    move=> H2 HA HB; subst B A; split.
    - rewrite /CB /Nf /Df /zc /wc; field.
    - move=> Hm; rewrite /VB /Ef /Cf /y3f /x3f /zc; field.
  Qed.
End free.

(** * The field structure on F = Q(sqrt2) *)

Lemma kr_sq2 (x : rat) : x * x <> 2%:R.
Proof.
  move=> H.
  have Hx : x != 0.
  { apply/eqP => E; move: H; rewrite E mulr0 => /eqP; by rewrite eq_sym pnatr_eq0. }
  have E : numq x * numq x = 2%:Z * (denq x * denq x).
  { apply: (@intr_inj rat); rewrite !intrM !numqE mulrACA H. by []. }
  have En : (`|numq x| * `|numq x| = 2 * (`|denq x| * `|denq x|))%N.
  { by rewrite -!abszM E abszM. }
  have Hn : (0 < `|numq x|)%N by rewrite absz_gt0 numq_eq0.
  have Hd : (0 < `|denq x|)%N by rewrite absz_gt0 denq_neq0.
  move: (congr1 (logn 2) En).
  rewrite lognM // lognM ?muln_gt0 ?Hd // lognM // (@logn_prime 2 2) //=.
  move/(congr1 odd); rewrite !oddD !addbb /=.
  done.
Qed.

Lemma kr_unit (x : qe rat) : x != 0 -> x \is a GRing.unit.
Proof.
  case: x => a b Hx; rewrite qe_unitE /qe_norm /=; apply/eqP => N.
  case: (eqVneq b 0) => Hb.
  - subst b; move: N; rewrite expr0n /= mulr0 subr0 => /eqP; rewrite sqrf_eq0 => /eqP Ha.
    by move: Hx; rewrite Ha eqxx.
  - apply: (@kr_sq2 (a / b)).
    have E : a ^+ 2 = 2%:R * b ^+ 2 by apply/eqP; rewrite -subr_eq0; apply/eqP.
    rewrite -[_ * _]/((a / b) * (a / b)) -mulrA [b^-1 * _]mulrC !mulrA -expr2 E.
    by field.
Qed.

(* a copy of [qe rat] carrying its field structure *)
Definition KRF : Type := qe rat.
HB.instance Definition _ := GRing.ComUnitRing.on KRF.
HB.instance Definition _ := GRing.ComUnitRing_isField.Build KRF kr_unit.

(* the curve coefficient, as an element of KRF *)
(* locked: unification must never unfold the unary literals of aE *)
HB.lock Definition aK : KRF := aE.

Lemma KRF_nat_neq0 (n : nat) : (0 < n)%N -> n%:R != 0 :> KRF.
Proof.
  move=> Hn; rewrite (qe_natE rat n) qe0E; apply/eqP => -[] /eqP.
  rewrite pnatr_eq0 => /eqP Hn0; by rewrite Hn0 in Hn.
Qed.

(** * The int <-> Z bridge for lia *)

Lemma kr_iz_eq (a b : int) : a = b <-> int_to_Z a = int_to_Z b.
Proof. by split => [ -> // | ]; apply: iz_inj. Qed.

Lemma kr_iz0 : int_to_Z 0 = 0%ZZ. Proof. by []. Qed.
Lemma kr_iz1 : int_to_Z 1 = 1%ZZ. Proof. by []. Qed.
Lemma kr_iz_natr (n : nat) : int_to_Z (n%:R) = Z.of_nat n.
Proof. by rewrite natz. Qed.

Ltac kr_iz_hyp :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with H : is_true (@Order.le _ _ _ _) |- _ => apply iz_le in H end;
  repeat match goal with H : is_true (@Order.lt _ _ _ _) |- _ => apply iz_lt in H end;
  repeat match goal with H : @eq ?T _ _ |- _ => unify T int; apply kr_iz_eq in H end.

Ltac ilia :=
  kr_iz_hyp;
  first [ apply/iz_le | apply/iz_lt | apply/kr_iz_eq | idtac ];
  repeat match goal with H : context [int_to_Z _] |- _ => revert H end;
  rewrite ?PoszD ?PoszM;
  do 4 rewrite ?iz_add ?iz_opp ?iz_mul;
  rewrite ?iz_nat ?kr_iz_natr ?kr_iz0 ?kr_iz1;
  intros; lia.

Lemma int_aaa (a : int) : a = a + a -> a = 0. Proof. move=> H; ilia. Qed.
Lemma int_aaa0 (a : int) : a + a = 0 -> a = 0. Proof. move=> H; ilia. Qed.
Lemma int_neg (a b : int) : 0 = a + b -> b = - a. Proof. move=> H; ilia. Qed.

(** * Valuations at a place of F *)

Section place.

  Variable v : qe rat -> int.
  Variable p : nat.
  Hypothesis Hv : is_place_above v p.

  Implicit Types x y t : KRF.

  Lemma vM x y : x != 0 -> y != 0 -> v (x * y) = v x + v y.
  Proof. by case: Hv => H _; apply: H. Qed.

  Lemma vU x y : x != 0 -> y != 0 -> x + y != 0 -> Num.min (v x) (v y) <= v (x + y).
  Proof. by case: Hv => _ [H _]; apply: H. Qed.

  Lemma vP : v (p%:R : KRF) = 1.
  Proof. by case: Hv => _ [_ H]. Qed.

  Lemma v1 : v (1 : KRF) = 0.
  Proof.
    have := vM (oner_neq0 KRF) (oner_neq0 KRF); rewrite mulr1 => H.
    exact: int_aaa H.
  Qed.

  Lemma vN1 : v (-1 : KRF) = 0.
  Proof.
    have Hn : (-1 : KRF) != 0 by rewrite oppr_eq0 oner_eq0.
    have := vM Hn Hn; rewrite mulrNN mulr1 v1 => H.
    by apply: int_aaa0; rewrite -H.
  Qed.

  Lemma vN x : v (- x) = v x.
  Proof.
    case: (eqVneq x 0) => [ -> | Hx ]; first by rewrite oppr0.
    have Hn : (-1 : KRF) != 0 by rewrite oppr_eq0 oner_eq0.
    by rewrite -mulN1r vM // vN1 add0r.
  Qed.

  Lemma vV x : x != 0 -> v x^-1 = - v x.
  Proof.
    move=> Hx; have Hi : x^-1 != 0 by rewrite invr_eq0.
    have := vM Hx Hi; rewrite mulfV // v1 => H.
    exact: int_neg H.
  Qed.

  Lemma vdiv x y : x != 0 -> y != 0 -> v (x / y) = v x - v y.
  Proof. by move=> Hx Hy; rewrite vM ?invr_eq0 // vV. Qed.

  (* "x = 0 or v(x) >= k" *)
  Definition vge (k : int) x : Prop := x = 0 \/ k <= v x.

  Lemma vge0 k : vge k 0. Proof. by left. Qed.

  Lemma vge_nz k x : x != 0 -> vge k x -> k <= v x.
  Proof. by move=> /eqP Hx [ // | ]. Qed.

  Lemma vge_le k k' x : k' <= k -> vge k x -> vge k' x.
  Proof. by move=> H [ -> | H' ]; [ left | right; exact: le_trans H H' ]. Qed.

  Lemma vge_opp k x : vge k x -> vge k (- x).
  Proof. by move=> [ -> | H ]; [ left; rewrite oppr0 | right; rewrite vN ]. Qed.

  Lemma vge_add k x y : vge k x -> vge k y -> vge k (x + y).
  Proof.
    move=> [ -> | Hx ]; first by rewrite add0r.
    move=> [ -> | Hy ]; first by rewrite addr0; right.
    case: (eqVneq x 0) => [ -> | nx ]; first by rewrite add0r; right.
    case: (eqVneq y 0) => [ -> | ny ]; first by rewrite addr0; right.
    case: (eqVneq (x + y) 0) => [ -> | nxy ]; first by left.
    right; apply: le_trans (vU nx ny nxy).
    by rewrite le_min Hx Hy.
  Qed.

  Lemma vge_sub k x y : vge k x -> vge k y -> vge k (x - y).
  Proof. by move=> Hx Hy; apply: vge_add Hx (vge_opp Hy). Qed.

  Lemma vge_mul k k' x y : vge k x -> vge k' y -> vge (k + k') (x * y).
  Proof.
    move=> [ -> | Hx ]; first by rewrite mul0r; left.
    move=> [ -> | Hy ]; first by rewrite mulr0; left.
    case: (eqVneq x 0) => [ -> | nx ]; first by rewrite mul0r; left.
    case: (eqVneq y 0) => [ -> | ny ]; first by rewrite mulr0; left.
    right; rewrite vM //; exact: lerD.
  Qed.

  Lemma vge_1 : vge 0 (1 : KRF).
  Proof. by right; rewrite v1. Qed.

  Lemma vge_nat (n : nat) : vge 0 (n%:R : KRF).
  Proof.
    elim: n => [ | n IH ]; first by left.
    by rewrite mulrS; apply: vge_add vge_1 IH.
  Qed.

  Lemma vge_p : vge 1 (p%:R : KRF).
  Proof. by right; rewrite vP. Qed.

  (* strict ultrametric inequality *)
  Lemma vge_strict k x y : y != 0 -> vge k x -> v y < k -> y + x != 0 /\ v (y + x) = v y.
  Proof.
    move=> ny [ -> | Hx ] Hlt; first by rewrite addr0.
    case: (eqVneq x 0) => [ -> | nx ]; first by rewrite addr0.
    have Hyx : v y < v x by exact: lt_le_trans Hlt Hx.
    have nyx : y + x != 0.
    { apply/eqP => E; have : x = - y by apply/eqP; rewrite -addr_eq0 addrC E.
      by move=> Ex; move: Hyx; rewrite Ex vN ltxx. }
    split => //.
    have H1 := vU ny nx nyx.
    have nnx : - x != 0 by rewrite oppr_eq0.
    have E : (y + x) + - x = y by rewrite addrK.
    have Hs : (y + x) + - x != 0 by rewrite E.
    have H2 := vU nyx nnx Hs; rewrite E vN in H2.
    apply/eqP; rewrite eq_le; apply/andP; split.
    - by move: H2; rewrite ge_min => /orP [ // | H ]; move: Hyx; rewrite ltNge H.
    - by move: H1; rewrite (min_idPl (ltW Hyx)).
  Qed.

  Lemma one_plus t : vge 1 t -> 1 + t != 0 /\ v (1 + t) = 0.
  Proof.
    move=> Ht; have H0 : v (1 : KRF) < 1 by rewrite v1.
    have [H1 H2] := vge_strict (oner_neq0 KRF) Ht H0.
    by rewrite H2 v1.
  Qed.

  Lemma vge_div_unit k x u : vge k x -> u != 0 -> v u = 0 -> vge k (x / u).
  Proof.
    move=> Hx Hu Hu0; rewrite -[k]addr0; apply: vge_mul Hx _.
    by right; rewrite vV // Hu0 oppr0.
  Qed.

  (* integers are integral; coprime integers are units *)
  Lemma v_nat_ge0 (n : nat) : (0 < n)%N -> 0 <= v (n%:R : KRF).
  Proof. by move=> Hn; apply: vge_nz (KRF_nat_neq0 Hn) (vge_nat n). Qed.

  Lemma v_coprime (n : nat) : (0 < n)%N -> coprime n p -> v (n%:R : KRF) = 0.
  Proof.
    move=> Hn /(coprimeP _ Hn) [[u1 u2] /= Hu].
    have Hlt : (u2 * p < u1 * n)%N by rewrite -subn_gt0 Hu.
    have E : (u1 * n = 1 + u2 * p)%N by rewrite -Hu subnK // ltnW.
    have H0 := v_nat_ge0 Hn.
    case: (lerP (v (n%:R : KRF)) 0) => H; first by apply/eqP; rewrite eq_le H H0.
    exfalso.
    have Hn1 : vge 1 (n%:R : KRF) by right.
    have H1 : vge 1 ((u1 * n)%:R - (u2 * p)%:R : KRF).
    { rewrite !natrM; apply: vge_sub.
      - rewrite -[1]add0r; exact: vge_mul (vge_nat _) Hn1.
      - rewrite -[1]add0r; exact: vge_mul (vge_nat _) vge_p. }
    move: H1; rewrite E natrD addrK => -[ /eqP | ]; first by rewrite oner_eq0.
    by rewrite v1.
  Qed.


  (** ** Integrality of sqrt2, of binary integers and of aE *)

  Lemma int_half (a b : int) : a + a = b -> 0 <= b -> 0 <= a.
  Proof. move=> H1 H2; ilia. Qed.

  Lemma sqrt2_neq0 : (qe_sqrt2 : KRF) != 0.
  Proof. by apply/eqP => -[] /eqP; rewrite oner_eq0. Qed.

  Lemma vge_sqrt2 : vge 0 (qe_sqrt2 : KRF).
  Proof.
    right; apply: int_half (vge_nz _ (vge_nat 2)).
    - by rewrite -vM ?sqrt2_neq0 // qe_sqrt2_sqr.
    - exact: KRF_nat_neq0.
  Qed.

  Lemma vge_zr (z : Z) : vge 0 (QE (zr z) 0 : KRF).
  Proof.
    case: z => [ | q | q ].
    - by rewrite zr0; left.
    - by rewrite zr_pos -qe_natE; apply: vge_nat.
    - rewrite zr_neg.
      have -> : QE (- (Pos.to_nat q)%:R) 0 = - ((Pos.to_nat q)%:R : KRF).
      { by rewrite qe_natE qe_oppE oppr0. }
      by apply/vge_opp/vge_nat.
  Qed.

  Lemma zq_split (a b : Z) : (zq a b : KRF) = QE (zr a) 0 + QE (zr b) 0 * qe_sqrt2.
  Proof.
    rewrite zq.unlock /qe_sqrt2 qe_mulE qe_addE.
    by rewrite !(mulr0, mul0r, addr0, add0r, mulr1).
  Qed.

  Lemma vge_zq (a b : Z) : vge 0 (zq a b : KRF).
  Proof.
    rewrite zq_split; apply: vge_add (vge_zr a) _.
    rewrite -[0]addr0; exact: vge_mul (vge_zr b) vge_sqrt2.
  Qed.

  Lemma vge_aE : vge 0 aK.
  Proof. rewrite aK.unlock aE_zq; exact: vge_zq. Qed.

End place.

Lemma aK_neq0 : aK != 0.
Proof.
  rewrite aK.unlock aE_zq zq.unlock; apply/eqP; rewrite qe0E => -[] _ /eqP.
  by rewrite zr_eq0.
Qed.

(** * The kernel of reduction: valuations of points with v(x) < 0 *)

Definition kern (v : qe rat -> int) (P : pt rat) : Prop :=
  if P is Some (x, _) then (x : KRF) != 0 /\ v x < 0 else True.

(* the formal parameter z = -x/y (zpar false), in KRF *)
Definition zk (P : pt rat) : KRF := if P is Some (x, y) then - (x : KRF) / y else 0.

Lemma zk_zpar (P : pt rat) : zpar false P = zk P.
Proof. by case: P => [ [ x y ] | ]. Qed.

Definition onp (P : pt rat) : Prop := if P is Some q then on_curve q else True.

Lemma kv_int (a b : int) : b + b = a + a + a -> a < 0 ->
  1 <= a - b /\ 0 - b = 3 * (a - b).
Proof. move=> H1 H2; split; ilia. Qed.

Lemma kv_int' (b : int) : 1 <= 0 - b -> 0 <= b + b -> False.
Proof. move=> H1 H2; ilia. Qed.

Lemma lt3 (a : int) : a < 0 -> a + a + a < a.
Proof. move=> H; ilia. Qed.

Section kernel.

  Variable v : qe rat -> int.
  Variable p : nat.
  Hypothesis Hv : is_place_above v p.

  Implicit Types x y : KRF.

  Lemma vX3 x : x != 0 -> v (x ^+ 3) = v x + v x + v x.
  Proof.
    move=> Hx; rewrite !exprS expr0 mulr1 !(vM Hv) ?mulf_neq0 //.
    by rewrite addrA.
  Qed.

  Lemma vneg_inv y : y != 0 -> v (- 1 / y) = 0 - v y.
  Proof.
    move=> Hy; rewrite (vdiv Hv) ?oppr_eq0 ?oner_eq0 //.
    by rewrite (vN1 Hv).
  Qed.

  Lemma vz x y : x != 0 -> y != 0 -> v (- x / y) = v x - v y.
  Proof. by move=> Hx Hy; rewrite (vdiv Hv) ?oppr_eq0 // (vN Hv). Qed.

  (* a point with v(x) < 0: v(x) = -2k, v(y) = -3k, v(z) = k >= 1, v(w) = 3k *)
  Lemma kv x y : y * y = x ^+ 3 + aK * x -> x != 0 -> v x < 0 ->
    y != 0 /\ - x / y != 0 /\ - 1 / y != 0 /\
    1 <= v (- x / y) /\ v (- 1 / y) = 3 * v (- x / y).
  Proof.
    move=> Hc Hx Hvx.
    have hax : vge v (v x) (aK * x).
    { have hx : vge v (v x) x by right.
      by have := vge_mul Hv (vge_aE Hv) hx; rewrite add0r. }
    have HX : x ^+ 3 != 0 by rewrite expf_neq0.
    have Hlt : v (x ^+ 3) < v x by rewrite vX3 //; exact: lt3.
    have [Hs Hvs] := vge_strict Hv HX hax Hlt.
    have Hy : y != 0.
    { apply/eqP => Hy0; move: Hs; by rewrite -Hc Hy0 mulr0 eqxx. }
    have Hyy : v y + v y = v x + v x + v x.
    { by rewrite -(vM Hv Hy Hy) Hc Hvs vX3. }
    have [H1 H2] := kv_int Hyy Hvx.
    have Hz : - x / y != 0 by rewrite mulf_neq0 ?oppr_eq0 ?invr_eq0.
    have Hw : - 1 / y != 0 by rewrite mulf_neq0 ?oppr_eq0 ?oner_eq0 ?invr_eq0.
    split; first exact: Hy.
    split; first exact: Hz.
    split; first exact: Hw.
    rewrite (vz Hx Hy).
    rewrite (vneg_inv Hy).
    split; [ exact: H1 | exact: H2 ].
  Qed.

  Lemma kv' x y : y * y = x ^+ 3 + aK * x -> y != 0 -> 1 <= v (- 1 / y) ->
    x != 0 /\ v x < 0.
  Proof.
    move=> Hc Hy Hw; rewrite vneg_inv // in Hw.
    have Hx : x != 0.
    { apply/eqP => Hx0; move: Hc; rewrite Hx0 mulr0 expr0n addr0 => /eqP.
      by rewrite mulf_eq0 (negbTE Hy). }
    split => //; rewrite ltNge; apply/negP => H0.
    have hx : vge v 0 x by right.
    have h1 : vge v 0 (x ^+ 3).
    { have := vge_mul Hv hx (vge_mul Hv hx hx).
      by rewrite !add0r !exprS expr0 mulr1. }
    have h2 : vge v 0 (aK * x).
    { by have := vge_mul Hv (vge_aE Hv) hx; rewrite add0r. }
    have H : vge v 0 (y * y).
    { rewrite Hc; exact (vge_add Hv h1 h2). }
    have Hyy : y * y != 0 by rewrite mulf_neq0.
    have := vge_nz Hyy H; rewrite (vM Hv) //.
    exact: kv_int' Hw.
  Qed.

End kernel.

(** * Two rational identities with simple denominators *)

Section lin.
  Variable K : fieldType.

  Lemma solve_lin (E X Y Z C : K) : E != 0 -> Y != 0 ->
    E * (X + Y * Z) + Y * C = 0 -> - X / Y - Z = C / E.
  Proof.
    move=> HE HY H; apply/eqP; rewrite -subr_eq0; apply/eqP.
    have -> : - X / Y - Z - C / E = - (E * (X + Y * Z) + Y * C) / (E * Y) by field.
    by rewrite H oppr0 mul0r.
  Qed.

  Lemma w3_id (X Y l m : K) : Y = - l * X - m -> Y != 0 -> m != 0 ->
    - 1 / Y = (- l / m) * (- X / Y) - (- 1 / m).
  Proof.
    move=> HY HY0 Hm; apply/eqP; rewrite -subr_eq0; apply/eqP.
    have -> : - 1 / Y - ((- l / m) * (- X / Y) - (- 1 / m)) = - (l * X + Y + m) / (m * Y) by field.
    have -> : l * X + Y + m = 0 by rewrite HY; ring.
    by rewrite oppr0 mul0r.
  Qed.

  Lemma line_I1 (x1 l m : K) : l * x1 + m != 0 ->
    1 + l * zc x1 l m = - m * wc x1 l m.
  Proof. move=> H; rewrite /zc /wc; field. Qed.

  Lemma line_I2 (x1 l m : K) : l * x1 + m != 0 -> m != 0 ->
    - 1 / m = wc x1 l m - (- l / m) * zc x1 l m.
  Proof. move=> H Hm; rewrite /zc /wc; field. Qed.
End lin.

Lemma int_3k (k a : int) : k <= a -> 3 * k <= 3 * a.
Proof. move=> H; ilia. Qed.

(** * The addition step in the kernel of reduction

    For points P1, P2 with v(x) < 0 (so v(z) >= k, v(w) >= 3k, k >= 1)
    on the line y = l x + m, the slope of the same line in the (z, w)
    chart is lam = -l/m = N/D with v(N) >= 2k, v(D) = 0, its intercept is
    nu = -1/m with v(nu) >= 3k, and z(P1 + P2) = z1 + z2 + 2 a lam nu / E
    with v(E) = 0. *)

Section addition.

  Variable v : qe rat -> int.
  Variable p : nat.
  Hypothesis Hv : is_place_above v p.

  Lemma line_step (k : int) (x1 x2 l m y1 y2 X3 Y3 : KRF) :
    1 <= k ->
    y1 = l * x1 + m -> y2 = l * x2 + m ->
    y1 * y1 = x1 ^+ 3 + aK * x1 -> y2 * y2 = x2 ^+ 3 + aK * x2 ->
    y1 != 0 -> y2 != 0 ->
    vge v k (- x1 / y1) -> vge v k (- x2 / y2) ->
    vge v (3 * k) (- 1 / y1) -> vge v (3 * k) (- 1 / y2) ->
    (x2 - x1 != 0 \/ (x2 = x1 /\ 2%:R * y1 * l = 3%:R * x1 ^+ 2 + aK)) ->
    X3 = x3f x1 x2 l -> Y3 = l * (x1 - X3) - y1 ->
    Y3 * Y3 = X3 ^+ 3 + aK * X3 ->
    X3 != 0 /\ v X3 < 0 /\ vge v (3 * k) (- X3 / Y3 - (- x1 / y1) - (- x2 / y2)).
  Proof.
    move=> Hk Hy1 Hy2 Hc1 Hc2 Hn1 Hn2 hz1 hz2 hw1 hw2 Hcase HX3 HY3 Hc3.
    have HC : CB aK 0 x1 x2 l m = 0 /\ (m != 0 -> VB aK 0 x1 x2 l m = 0).
    { case: Hcase => [ Hx | [ Hx Hl ] ].
      - have HA : aK = (((l * x2 + m) ^+ 2 - x2 ^+ 3) - ((l * x1 + m) ^+ 2 - x1 ^+ 3)) / (x2 - x1).
        { rewrite -Hy1 -Hy2 !expr2 Hc1 Hc2; field. }
        have HB : 0 = (l * x1 + m) ^+ 2 - x1 ^+ 3 - aK * x1.
        { rewrite -Hy1 expr2 Hc1; ring. }
        have H1 : l * x1 + m != 0 by rewrite -Hy1.
        have H2 : l * x2 + m != 0 by rewrite -Hy2.
        exact ((chord_free Hx H1 H2 HA HB)).
      - subst x2.
        have HA : aK = 2%:R * (l * x1 + m) * l - 3%:R * x1 ^+ 2.
        { rewrite -Hy1 Hl; ring. }
        have HB : 0 = (l * x1 + m) ^+ 2 - x1 ^+ 3 - aK * x1.
        { rewrite -Hy1 expr2 Hc1; ring. }
        have H1 : l * x1 + m != 0 by rewrite -Hy1.
        exact ((tangent_free H1 HA HB)). }
    case: HC => HC HV.
    have Hn1' : l * x1 + m != 0 by rewrite -Hy1.
    have EY3 : Y3 = - l * X3 - m by rewrite HY3 Hy1; ring.
    subst y1 y2.
    have hz1' : vge v k (zc x1 l m) by exact (hz1).
    have hz2' : vge v k (zc x2 l m) by exact (hz2).
    have hw1' : vge v (3 * k) (wc x1 l m) by exact (hw1).
    have hw2' : vge v (3 * k) (wc x2 l m) by exact (hw2).
    suff : X3 != 0 /\ v X3 < 0 /\ vge v (3 * k) (- X3 / Y3 - zc x1 l m - zc x2 l m).
    { move=> H; exact (H). }
    move: HC HV; rewrite /CB /VB -HX3.
    have I1 := line_I1 Hn1'.
    have I2 : m != 0 -> - 1 / m = wc x1 l m - (- l / m) * zc x1 l m.
    { move=> Hm; exact (line_I2 Hn1' Hm). }
    have Hw1 : wc x1 l m != 0 by rewrite /wc mulf_neq0 ?oppr_eq0 ?oner_eq0 ?invr_eq0.
    move: hz1' hz2' hw1' hw2' I1 I2 Hw1.
    generalize (zc x1 l m) (zc x2 l m) (wc x1 l m) (wc x2 l m) => z1 z2 w1 w2.
    move=> hz1' hz2' hw1' hw2' I1 I2 Hw1 HC HV.
    have EY : y3f x1 x2 l m = Y3 by rewrite /y3f -HX3 -HY3.
    rewrite EY in HV.
    (* D *)
    set D := Df aK 0 z1 w1 w2.
    have ED : D = 1 + (- (aK * z1 * (w1 + w2)) - 0 * (w1 ^+ 2 + w1 * w2 + w2 ^+ 2)).
    { rewrite /D /Df; ring. }
    have hD : vge v 1 (- (aK * z1 * (w1 + w2)) - 0 * (w1 ^+ 2 + w1 * w2 + w2 ^+ 2)).
    { rewrite mul0r subr0; apply: (vge_opp Hv).
      have h := vge_mul Hv (vge_mul Hv (vge_aE Hv) hz1') (vge_add Hv hw1' hw2').
      apply: vge_le h; ilia. }
    have [HD0 HvD] := one_plus Hv hD; rewrite -ED in HD0 HvD.
    (* N *)
    set N := Nf aK z1 z2 w2.
    have hN : vge v (k + k) N.
    { rewrite /N /Nf !expr2; apply: (vge_add Hv); [ apply: (vge_add Hv); [ apply: (vge_add Hv) | ] | ].
      - exact (vge_mul Hv hz1' hz1').
      - exact (vge_mul Hv hz1' hz2').
      - exact (vge_mul Hv hz2' hz2').
      - have h := vge_mul Hv (vge_aE Hv) (vge_mul Hv hw2' hw2').
        apply: vge_le h; ilia. }
    (* m <> 0 *)
    have Hm : m != 0.
    { apply/eqP => Hm0; move: HC; rewrite I1 Hm0 oppr0 mul0r mulr0 sub0r => /eqP.
      rewrite oppr_eq0 !mulf_eq0 (negbTE Hw1) (negbTE HD0) !orbF => /eqP Hl0.
      move: I1; rewrite Hl0 Hm0 mul0r oppr0 mul0r addr0 => /eqP; by rewrite oner_eq0. }
    (* lam = -l/m = N/D *)
    have HL : - l / m = N / D.
    { have E1 : w1 * (N * m + l * D) = - (N * (- m * w1) - l * w1 * D) by ring.
      rewrite -I1 HC oppr0 in E1.
      move/eqP: E1; rewrite mulf_eq0 (negbTE Hw1) /= => /eqP E1.
      apply/eqP; rewrite eqr_div //; apply/eqP.
      have E2 : l * D = - (N * m) by apply/eqP; rewrite -addr_eq0 addrC E1.
      by rewrite mulNr E2 opprK. }
    have hlam : vge v (k + k) (- l / m) by rewrite HL; exact (vge_div_unit Hv hN HD0 HvD).
    (* nu = -1/m *)
    have hnu : vge v (3 * k) (- 1 / m).
    { rewrite (I2 Hm); apply: (vge_sub Hv hw1').
      have h := vge_mul Hv hlam hz1'; apply: vge_le h; ilia. }
    (* E *)
    have EE : Ef aK 0 l m = 1 + (aK * ((- l / m) * (- l / m)) + 0 * (- l / m) ^+ 3).
    { rewrite /Ef; ring. }
    have hE : vge v 1 (aK * ((- l / m) * (- l / m)) + 0 * (- l / m) ^+ 3).
    { rewrite mul0r addr0.
      have h := vge_mul Hv (vge_aE Hv) (vge_mul Hv hlam hlam).
      apply: vge_le h; ilia. }
    have [HE0 HvE] := one_plus Hv hE; rewrite -EE in HE0 HvE.
    have HV' := HV Hm.
    (* y3 <> 0 *)
    have HY0 : Y3 != 0.
    { apply/eqP => HY; move: HV'; rewrite HY !mul0r !addr0 => /eqP.
      rewrite mulf_eq0 (negbTE HE0) /= => /eqP HX.
      move: EY3; rewrite HY HX mulr0 sub0r => /eqP; rewrite eq_sym oppr_eq0.
      by rewrite (negbTE Hm). }
    (* z3 - z1 - z2 = C / E *)
    have Hz3 := solve_lin HE0 HY0 HV'.
    have ECf : Cf aK 0 l m = 2%:R * aK * (- l / m) * (- 1 / m) by rewrite /Cf; ring.
    have hC : vge v (3 * k) (Cf aK 0 l m / Ef aK 0 l m).
    { apply: (vge_div_unit Hv) HE0 HvE; rewrite ECf.
      have h := vge_mul Hv (vge_mul Hv (vge_mul Hv (vge_nat Hv 2) (vge_aE Hv)) hlam) hnu.
      apply: vge_le h; ilia. }
    have hz3 : vge v k (- X3 / Y3).
    { have -> : - X3 / Y3 = (- X3 / Y3 - (z1 + z2)) + z1 + z2 by ring.
      rewrite Hz3; apply: (vge_add Hv); [ apply: (vge_add Hv) | exact hz2' ].
      - apply: vge_le hC; ilia.
      - exact (hz1'). }
    have hw3 : vge v (3 * k) (- 1 / Y3).
    { rewrite (w3_id EY3 HY0 Hm); apply: (vge_sub Hv) hnu.
      have h := vge_mul Hv hlam hz3; apply: vge_le h; ilia. }
    have Hw3 : - 1 / Y3 != 0 by rewrite mulf_neq0 ?oppr_eq0 ?oner_eq0 ?invr_eq0.
    have Hw3v : 1 <= v (- 1 / Y3).
    { have := vge_nz Hw3 hw3 => H; apply: le_trans H; ilia. }
    have [HX0 HvX] := kv' Hv Hc3 HY0 Hw3v.
    split; first exact (HX0).
    split; first exact (HvX).
    have -> : - X3 / Y3 - z1 - z2 = - X3 / Y3 - (z1 + z2) by ring.
    by rewrite Hz3.
  Qed.

End addition.

(** * The three cases of the chord-tangent law *)

Lemma ec_add_opp (x1 y1 x2 y2 : qe rat) : x1 = x2 -> y1 = - y2 ->
  ec_add (Some (x1, y1)) (Some (x2, y2)) = None.
Proof. move=> -> ->; by rewrite /ec_add eqxx eqxx. Qed.

Definition slope_tan (x1 y1 : qe rat) : qe rat := (3%:R * x1 ^+ 2 + aE) / (2%:R * y1).
Definition slope_ch (x1 y1 x2 y2 : qe rat) : qe rat := (y2 - y1) / (x2 - x1).

Lemma ec_add_tan (x1 y1 x2 y2 : qe rat) : x1 = x2 -> y1 != - y2 ->
  ec_add (Some (x1, y1)) (Some (x2, y2)) =
  Some (slope_tan x1 y1 ^+ 2 - 2%:R * x1,
        slope_tan x1 y1 * (x1 - (slope_tan x1 y1 ^+ 2 - 2%:R * x1)) - y1).
Proof. move=> Ex Hy; rewrite /ec_add Ex eqxx -Ex (negbTE Hy). by []. Qed.

Lemma ec_add_ch (x1 y1 x2 y2 : qe rat) : x1 != x2 ->
  ec_add (Some (x1, y1)) (Some (x2, y2)) =
  Some (slope_ch x1 y1 x2 y2 ^+ 2 - x1 - x2,
        slope_ch x1 y1 x2 y2 * (x1 - (slope_ch x1 y1 x2 y2 ^+ 2 - x1 - x2)) - y1).
Proof. move=> Hx; rewrite /ec_add (negbTE Hx). by []. Qed.

Lemma KRF_two_neq0 : 2%:R != 0 :> KRF.
Proof. exact: KRF_nat_neq0. Qed.

Lemma on_curveK (x y : qe rat) : on_curve (x, y) -> (y : KRF) * y = x ^+ 3 + aK * x.
Proof. by rewrite aK.unlock. Qed.

Section add_points.

  Variable v : qe rat -> int.
  Variable p : nat.
  Hypothesis Hv : is_place_above v p.

  Lemma kern_vw (x y : qe rat) (k : int) : on_curve (x, y) -> kern v (Some (x, y)) ->
    vge v k (zk (Some (x, y))) ->
    (y : KRF) != 0 /\ vge v k (- (x : KRF) / y) /\ vge v (3 * k) (- 1 / (y : KRF)).
  Proof.
    move=> /on_curveK Hc [Hx Hvx] hz.
    have [Hy [Hz [Hw [H1 H2]]]] := kv Hv Hc Hx Hvx.
    split; first exact Hy.
    split; first exact hz.
    right; rewrite H2; apply: int_3k; exact (vge_nz Hz hz).
  Qed.

  (* the addition step for points *)
  Theorem add_kern (P1 P2 : pt rat) (k : int) : 1 <= k ->
    onp P1 -> onp P2 -> onp (ec_add P1 P2) -> kern v P1 -> kern v P2 ->
    vge v k (zk P1) -> vge v k (zk P2) ->
    kern v (ec_add P1 P2) /\ vge v (3 * k) (zk (ec_add P1 P2) - zk P1 - zk P2).
  Proof.
    case: P1 => [ [ x1 y1 ] | ]; last first.
    { move=> _ _ _ _ _ H _ _; split; first exact H.
      rewrite /= subr0 subrr; exact: vge0. }
    case: P2 => [ [ x2 y2 ] | ]; last first.
    { move=> _ _ _ _ H _ _ _; split; first exact H.
      rewrite /= subr0 subrr; exact: vge0. }
    move=> Hk Hc1 Hc2 Hc3 Hk1 Hk2 hz1 hz2.
    have [Hn1 [hz1' hw1]] := kern_vw Hc1 Hk1 hz1.
    have [Hn2 [hz2' hw2]] := kern_vw Hc2 Hk2 hz2.
    have Hc1' := on_curveK Hc1; have Hc2' := on_curveK Hc2.
    case: (eqVneq x1 x2) => [ Ex | Nx ].
    - case: (eqVneq y1 (- y2)) => [ Ey | Ny ].
      + rewrite (ec_add_opp Ex Ey); split; first exact I.
        rewrite /= Ex Ey.
        have -> : (0 - (- x2 / - y2) - (- x2 / y2) : KRF) = 0 by rewrite invrN mulrN opprK add0r subrr.
        exact: vge0.
      + (* tangent: P1 = P2 *)
        have Ey : y2 = y1.
        { move: Hc1' Hc2'; rewrite -Ex => H1 H2.
          have : (y2 - y1) * (y2 + y1) = 0 :> KRF.
          { rewrite mulrDr !mulrBl H1 H2 (mulrC y1 y2); ring. }
          move/eqP; rewrite mulf_eq0 => /orP [ /eqP H | /eqP H ].
          - by apply/eqP; rewrite -subr_eq0 H.
          - exfalso; move: Ny; rewrite (_ : y1 = - y2) ?eqxx //.
            by apply/eqP; rewrite -addr_eq0 addrC H. }
        move: Hc3; rewrite (ec_add_tan Ex Ny) => Hc3.
        set l := slope_tan x1 y1 in Hc3 *.
        have Hl : 2%:R * (y1 : KRF) * l = 3%:R * x1 ^+ 2 + aK.
        { rewrite /l /slope_tan aK.unlock; field. }
        have HX3 : (l ^+ 2 - 2%:R * x1 : KRF) = x3f (K := KRF) x1 x1 l by rewrite /x3f; ring.
        have Hy1 : (y1 : KRF) = l * x1 + (y1 - l * x1) by ring.
        subst x2 y2.
        have := line_step Hv Hk Hy1 Hy1 Hc1' Hc1' Hn1 Hn1 hz1' hz1' hw1 hw1
                  (or_intror (conj erefl Hl)) HX3 erefl (on_curveK Hc3).
        move=> [H1 [H2 H3]]; split; [ split; [ exact H1 | exact H2 ] | exact H3 ].
    - (* chord *)
      move: Hc3; rewrite (ec_add_ch y1 y2 Nx) => Hc3.
      set l := slope_ch x1 y1 x2 y2 in Hc3 *.
      have Hx : (x2 : KRF) - x1 != 0 by rewrite subr_eq0 eq_sym.
      have Hy1 : (y1 : KRF) = l * x1 + (y1 - l * x1) by ring.
      have Hy2 : (y2 : KRF) = l * x2 + (y1 - l * x1) by rewrite /l /slope_ch; field.
      have := line_step Hv Hk Hy1 Hy2 Hc1' Hc2' Hn1 Hn2 hz1' hz2' hw1 hw2
                (or_introl Hx) erefl erefl (on_curveK Hc3).
      move=> [H1 [H2 H3]]; split; [ split; [ exact H1 | exact H2 ] | exact H3 ].
  Qed.

End add_points.

(** * Multiples: the kernel-of-reduction lemma

    [Pn : int -> pt rat] is any homomorphism from Z to E(F) (for the
    application: n |-> n P0, or n |-> n P). *)

Lemma int_kr (e k : int) : 1 <= k -> e < k + k -> e + k < 3 * k.
Proof. move=> H1 H2; ilia. Qed.

Lemma int_k1 (k : int) : 1 <= k -> 1 < k + k.
Proof. move=> H; ilia. Qed.

Lemma int_k0 (k : int) : 1 <= k -> 0 < k + k.
Proof. move=> H; ilia. Qed.

Lemma int_ratio (a b c d e : int) : a = b + c -> a = d + e -> d - b = c - e.
Proof. move=> H1 H2; ilia. Qed.

Section multiples.

  Variable v : qe rat -> int.
  Variable p : nat.
  Hypothesis Hp : prime p.
  Hypothesis Hv : is_place_above v p.

  Variable Pn : int -> pt rat.
  Hypothesis Pn_on : forall n, onp (Pn n).
  Hypothesis Pn_add : forall n n', Pn (n + n') = ec_add (Pn n) (Pn n').
  Hypothesis Pn_0 : Pn 0 = None.
  Hypothesis Pn_neg : forall n, Pn (- n) = pt_neg (Pn n).

  (* z(n R) = n z(R) mod p^(3k) *)
  Lemma mul_kern (b : int) (k : int) : 1 <= k -> kern v (Pn b) -> vge v k (zk (Pn b)) ->
    forall n : nat, kern v (Pn (b * n%:Z)) /\
      vge v (3 * k) (zk (Pn (b * n%:Z)) - n%:R * zk (Pn b)) /\ vge v k (zk (Pn (b * n%:Z))).
  Proof.
    move=> Hk Hb hb; elim=> [ | n [IH1 [IH2 IH3]] ].
    { rewrite mulr0 Pn_0 /= mul0r subr0; split; first exact I.
      split; exact: vge0. }
    have E : b * (n.+1)%:Z = b * n%:Z + b by rewrite -addn1 PoszD mulrDr mulr1.
    rewrite E Pn_add.
    have Hon3 : onp (ec_add (Pn (b * n%:Z)) (Pn b)) by rewrite -Pn_add; exact: Pn_on.
    have [H1 H2] := add_kern Hv Hk (Pn_on _) (Pn_on _) Hon3 IH1 Hb IH3 hb.
    split; first exact H1.
    have H3 : vge v (3 * k) (zk (ec_add (Pn (b * n%:Z)) (Pn b)) - (n.+1)%:R * zk (Pn b)).
    { have -> : zk (ec_add (Pn (b * n%:Z)) (Pn b)) - (n.+1)%:R * zk (Pn b)
               = (zk (ec_add (Pn (b * n%:Z)) (Pn b)) - zk (Pn (b * n%:Z)) - zk (Pn b))
                 + (zk (Pn (b * n%:Z)) - n%:R * zk (Pn b)).
      { rewrite -addn1 natrD; ring. }
      exact (vge_add Hv H2 IH2). }
    split; first exact H3.
    have -> : zk (ec_add (Pn (b * n%:Z)) (Pn b))
             = (zk (ec_add (Pn (b * n%:Z)) (Pn b)) - (n.+1)%:R * zk (Pn b)) + (n.+1)%:R * zk (Pn b)
      by rewrite subrK.
    apply: (vge_add Hv).
    - apply: vge_le H3; ilia.
    - have := vge_mul Hv (vge_nat Hv n.+1) hb; rewrite add0r => H; exact H.
  Qed.

  (* v(n) < 2 v(z(R))  ==>  v(z(n R)) = v(n) + v(z(R)) *)
  Lemma mul_val (b : int) (x y : qe rat) (n : nat) :
    Pn b = Some (x, y) -> (x : KRF) != 0 -> v x < 0 -> (0 < n)%N ->
    v (n%:R : KRF) < v (zk (Pn b)) + v (zk (Pn b)) ->
    exists x' y', Pn (b * n%:Z) = Some (x', y') /\ (x' : KRF) != 0 /\ v x' < 0 /\
      v (zk (Pn (b * n%:Z))) = v (n%:R : KRF) + v (zk (Pn b)).
  Proof.
    move=> Hb Hx Hvx Hn Hlt.
    have Hc : on_curve (x, y) by have := Pn_on b; rewrite Hb.
    have [Hy [Hz [_ [Hz1 _]]]] := kv Hv (on_curveK Hc) Hx Hvx.
    set k := v (zk (Pn b)).
    have Hk : 1 <= k by rewrite /k Hb.
    have Hkern : kern v (Pn b) by rewrite Hb; split.
    have hb : vge v k (zk (Pn b)) by right.
    have [H1 [H2 _]] := mul_kern Hk Hkern hb n.
    have Hnz : (n%:R : KRF) * zk (Pn b) != 0.
    { by rewrite mulf_neq0 ?KRF_nat_neq0 // Hb. }
    have Hvn : v ((n%:R : KRF) * zk (Pn b)) = v (n%:R : KRF) + k.
    { by rewrite (vM Hv) ?KRF_nat_neq0 // Hb. }
    have Hlt3 : v ((n%:R : KRF) * zk (Pn b)) < 3 * k by rewrite Hvn; exact: int_kr.
    have [Hs Hvs] := vge_strict Hv Hnz H2 Hlt3.
    rewrite addrC subrK in Hs Hvs.
    move: H1 Hs Hvs; case: (Pn (b * n%:Z)) => [ [ x' y' ] | ].
    - move=> [Hx' Hvx'] _ Hvs; exists x', y'; split; first by [].
      split; first exact Hx'.
      split; first exact Hvx'.
      by rewrite Hvs Hvn.
    - move=> _ /negP H; exfalso; apply: H; apply/eqP; reflexivity.
  Qed.

  (* induction on the p-adic valuation of the multiplier *)
  Lemma mul_val_pe (e : nat) : forall (b : int) (x y : qe rat) (m : nat),
    Pn b = Some (x, y) -> (x : KRF) != 0 -> v x < 0 -> (0 < m)%N -> coprime m p ->
    exists x' y', Pn (b * (m * p ^ e)%N%:Z) = Some (x', y') /\ (x' : KRF) != 0 /\ v x' < 0 /\
      v (zk (Pn (b * (m * p ^ e)%N%:Z))) = v (zk (Pn b)) + e%:Z.
  Proof.
    elim: e => [ | e IH ] b x y m Hb Hx Hvx Hm Hcop.
    - rewrite expn0 muln1.
      have Hb' : kern v (Pn b) by rewrite Hb; split.
      have Hc : on_curve (x, y) by have := Pn_on b; rewrite Hb.
      have [_ [_ [_ [Hz1 _]]]] := kv Hv (on_curveK Hc) Hx Hvx.
      have Hlt : v (m%:R : KRF) < v (zk (Pn b)) + v (zk (Pn b)).
      { rewrite (v_coprime Hv Hm Hcop) Hb; exact (int_k0 Hz1). }
      have [x' [y' [H1 [H2 [H3 H4]]]]] := mul_val Hb Hx Hvx Hm Hlt.
      exists x', y'; split; first exact H1.
      split; first exact H2.
      split; first exact H3.
      by rewrite H4 (v_coprime Hv Hm Hcop) add0r addr0.
    - have Hc : on_curve (x, y) by have := Pn_on b; rewrite Hb.
      have [_ [_ [_ [Hz1 _]]]] := kv Hv (on_curveK Hc) Hx Hvx.
      have Hp0 : (0 < p)%N by exact: prime_gt0.
      have Hlt : v (p%:R : KRF) < v (zk (Pn b)) + v (zk (Pn b)).
      { rewrite (vP Hv) Hb; exact (int_k1 Hz1). }
      have [x1 [y1 [H1 [H2 [H3 H4]]]]] := mul_val Hb Hx Hvx Hp0 Hlt.
      have [x' [y' [G1 [G2 [G3 G4]]]]] := IH (b * p%:Z) x1 y1 m H1 H2 H3 Hm Hcop.
      have E : b * (m * p ^ e.+1)%N%:Z = b * p%:Z * (m * p ^ e)%N%:Z.
      { rewrite expnSr mulnA !PoszM; ring. }
      exists x', y'; rewrite E; split; first exact G1.
      split; first exact G2.
      split; first exact G3.
      rewrite G4 H4 (vP Hv) -addn1 PoszD; ring.
  Qed.

  (* (KR): multipliers prime to p preserve v(z) *)
  Corollary kernel_KR (b : int) (x y : qe rat) (n : nat) :
    Pn b = Some (x, y) -> (x : KRF) != 0 -> v x < 0 -> (0 < n)%N -> coprime n p ->
    exists x' y', Pn (b * n%:Z) = Some (x', y') /\ (x' : KRF) != 0 /\ v x' < 0 /\
      v (zk (Pn (b * n%:Z))) = v (zk (Pn b)).
  Proof.
    move=> Hb Hx Hvx Hn Hc.
    have := mul_val_pe 0 Hb Hx Hvx Hn Hc; rewrite expn0 muln1 addr0 => H; exact H.
  Qed.

  (* (KR'): multiplication by p raises v(z) by one *)
  Corollary kernel_KR' (b : int) (x y : qe rat) :
    Pn b = Some (x, y) -> (x : KRF) != 0 -> v x < 0 ->
    exists x' y', Pn (b * p%:Z) = Some (x', y') /\ (x' : KRF) != 0 /\ v x' < 0 /\
      v (zk (Pn (b * p%:Z))) = v (zk (Pn b)) + 1.
  Proof.
    move=> Hb Hx Hvx.
    have H1 : (0 < 1)%N by [].
    have Hc : coprime 1 p by exact: coprime1n.
    have := mul_val_pe 1 Hb Hx Hvx H1 Hc; rewrite mul1n expn1 => H; exact H.
  Qed.

  Lemma zk_neg (P : pt rat) : zk (pt_neg P) = - zk P.
  Proof.
    case: P => [ [ x y ] | ] /=; last by rewrite oppr0.
    by rewrite invrN mulrN.
  Qed.

  (* eq. ell:ratio, one base point: for R = b P in the kernel and n <> 0,
     nR is finite, in the kernel, and v(z(nR)) = v(z(R)) + v_p(n) *)
  Theorem kernel_mul (b : int) (x y : qe rat) (n : int) :
    Pn b = Some (x, y) -> (x : KRF) != 0 -> v x < 0 -> n != 0 ->
    exists x' y', Pn (b * n) = Some (x', y') /\ (x' : KRF) != 0 /\ v x' < 0 /\
      v (zk (Pn (b * n))) = v (zk (Pn b)) + vqr p n%:~R.
  Proof.
    move=> Hb Hx Hvx Hn.
    have Hn0 : (0 < `|n|)%N by rewrite absz_gt0.
    have [m Hcop Em] := pfactor_coprime Hp Hn0.
    have Hm : (0 < m)%N.
    { by move: Hn0; rewrite Em muln_gt0 => /andP []. }
    have Hcop' : coprime m p by rewrite coprime_sym.
    have [x' [y' [H1 [H2 [H3 H4]]]]] := mul_val_pe (logn p `|n|) Hb Hx Hvx Hm Hcop'.
    rewrite -Em in H1 H4.
    rewrite (vqr_int p n).
    case: n Hn Hn0 Em H1 H4 => [ n | n ] Hn Hn0 Em H1 H4.
    - exists x', y'; split; first exact H1.
      split; first exact H2.
      split; first exact H3.
      exact H4.
    - have E : b * Negz n = - (b * `|Negz n|%:Z) by rewrite NegzE mulrN.
      exists x', (- y'); rewrite E Pn_neg H1; split; first by [].
      split; first exact H2.
      split; first exact H3.
      by rewrite zk_neg (vN Hv) -H4 H1.
  Qed.

  (* eq. ell:ratio *)
  Theorem kernel_ratio (n n' : int) (x y x' y' : qe rat) :
    Pn n = Some (x, y) -> (x : KRF) != 0 -> v x < 0 ->
    Pn n' = Some (x', y') -> (x' : KRF) != 0 -> v x' < 0 ->
    v (zk (Pn n)) - v (zk (Pn n')) = vqr p n%:~R - vqr p n'%:~R.
  Proof.
    move=> H1 H2 H3 H1' H2' H3'.
    have Hn : n != 0 by apply/eqP => E; move: H1; rewrite E Pn_0.
    have Hn' : n' != 0 by apply/eqP => E; move: H1'; rewrite E Pn_0.
    have [a [b [G1 [_ [_ G4]]]]] := kernel_mul H1' H2' H3' Hn.
    have [a' [b' [G1' [_ [_ G4']]]]] := kernel_mul H1 H2 H3 Hn'.
    rewrite mulrC in G4.
    exact: int_ratio G4 G4'.
  Qed.

End multiples.

(** * Conjugate places (for the curve E^sigma) *)

Lemma qe_conj0 : qe_conj (0 : qe rat) = 0.
Proof. rewrite qe0E /qe_conj /=; congr QE; exact: oppr0. Qed.

Lemma qe_conj_neq0 (x : qe rat) : x != 0 -> qe_conj x != 0.
Proof.
  move=> Hx; apply/eqP => H; move: Hx; rewrite -[x]qe_conjK H qe_conj0.
  by rewrite eqxx.
Qed.

Lemma qe_conj_nat (n : nat) : qe_conj (n%:R : qe rat) = n%:R.
Proof. rewrite qe_natE /qe_conj /=; congr QE; exact: oppr0. Qed.

Lemma qe_conj_inv (x : KRF) : qe_conj (x^-1) = (qe_conj x)^-1 :> KRF.
Proof.
  case: (eqVneq x 0) => [ -> | Hx ].
  { have E : (0 : KRF)^-1 = 0 := invr0 _.
    have E2 : qe_conj (0 : KRF) = (0 : KRF) := qe_conj0.
    rewrite E E2; exact (esym E). }
  have Hc : (qe_conj x : KRF) != 0 by exact: qe_conj_neq0.
  apply: (mulIf Hc); rewrite mulVf // -qe_conj_mul.
  have -> : (x^-1 * x : KRF) = 1 by rewrite mulVf.
  exact: qe_conj1.
Qed.

Lemma qe_conj_zk (x y : qe rat) : zpar true (Some (x, y)) = qe_conj (zk (Some (x, y))).
Proof.
  rewrite /zpar /zk /= qe_conj_mul qe_conj_opp.
  by rewrite (qe_conj_inv y).
Qed.

Lemma conj_place (v : qe rat -> int) (p : nat) :
  is_place_above v p -> is_place_above (fun x => v (qe_conj x)) p.
Proof.
  move=> [HM [HU HP]]; split; [ | split ].
  - move=> x y Hx Hy /=; rewrite qe_conj_mul; apply: HM; exact: qe_conj_neq0.
  - move=> x y Hx Hy Hxy /=; rewrite qe_conj_add; apply: HU.
    + exact: qe_conj_neq0 Hx.
    + exact: qe_conj_neq0 Hy.
    + rewrite -qe_conj_add; exact: qe_conj_neq0 Hxy.
  - by rewrite /= qe_conj_nat.
Qed.

(** * Homomorphisms n |-> n P0 and n |-> n P *)

Lemma mulQ_neg (D : FixedData) (n : int) : mulQ D (- n) = pt_neg (mulQ D n).
Proof.
  case: n => [ [ | k ] | k ].
  - by [].
  - have -> : - (k.+1)%:Z = Negz k by rewrite NegzE.
    by [].
  - have -> : - Negz k = (k.+1)%:Z by rewrite NegzE opprK.
    rewrite /mulQ; case: (mulQn D k.+1) => [ [ x y ] | ] //=.
    by rewrite opprK.
Qed.

Section group_law.

  (* TO-MERGE from GroupLaw.v: [mulQ_on] (there stated with
     [on_curve_pt], which is [onp]) *)
  Hypothesis mulQ_on_h : forall D : FixedData, on_curve (fd_P0 D) ->
    forall n : int, onp (mulQ D n).
  (* TO-MERGE from GroupLaw.v: [mulQ_add] *)
  Hypothesis mulQ_add_h : forall D : FixedData, on_curve (fd_P0 D) ->
    forall n n' : int, mulQ D (n + n') = ec_add (mulQ D n) (mulQ D n').

  Variable D : FixedData.
  Hypothesis HP0 : on_curve (fd_P0 D).

  Lemma mulQ_0 : mulQ D 0 = None. Proof. by []. Qed.

  Lemma mulPn_on (m : int) n : onp (mulQ D (n * m)).
  Proof. exact: mulQ_on_h. Qed.

  Lemma mulPn_add (m : int) n n' : mulQ D ((n + n') * m) = ec_add (mulQ D (n * m)) (mulQ D (n' * m)).
  Proof. by rewrite mulrDl mulQ_add_h. Qed.

  Lemma mulPn_0 (m : int) : mulQ D (0 * m) = None.
  Proof. by rewrite mul0r. Qed.

  Lemma mulPn_neg (m : int) n : mulQ D (- n * m) = pt_neg (mulQ D (n * m)).
  Proof. by rewrite mulNr mulQ_neg. Qed.

  Lemma mulQ_none_mul (n : int) : mulQ D n = None -> forall j : nat, mulQ D (n * j%:Z) = None.
  Proof.
    move=> Hn; elim=> [ | j IH ]; first by rewrite mulr0.
    by rewrite -addn1 PoszD mulrDr mulr1 mulQ_add_h // IH Hn.
  Qed.

  (** E2 from nontorsion *)
  Theorem E2_of_nontorsion :
    (forall n : int, n != 0 -> mulQ D n <> None) ->
    forall n : int, n != 0 ->
      exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y).
  Proof.
    move=> Hnt n Hn.
    have Hon := mulQ_on_h HP0 n.
    case E : (mulQ D n) Hon => [ [ x y ] | ] Hon; last by exfalso; exact: Hnt E.
    have Hy : y != 0.
    { apply/eqP => Hy0.
      have H2 : mulQ D (n + n) = None.
      { rewrite mulQ_add_h // E; apply: ec_add_opp => //; by rewrite Hy0 oppr0. }
      have Hnn : n + n != 0.
      { apply/eqP => H0; move: Hn; rewrite -mulr2n -mulr_natl in H0.
        move/eqP: H0; rewrite mulf_eq0 => /orP [ // | /eqP -> ]; by rewrite eqxx. }
      exact: Hnt Hnn H2. }
    have Hx : x != 0.
    { apply/eqP => Hx0; have := on_curveK Hon; rewrite Hx0 expr0n /= mulr0 addr0 => /eqP.
      rewrite mulf_eq0 orbb => /eqP Hy0; move: Hy; by rewrite Hy0 eqxx. }
    by exists x, y.
  Qed.

  (** nontorsion from one multiple in the kernel of reduction at some place *)
  Theorem nontorsion_of_kernel (v : qe rat -> int) (p : nat) (b : int) (x y : qe rat) :
    prime p -> is_place_above v p ->
    mulQ D b = Some (x, y) -> (x : KRF) != 0 -> v x < 0 ->
    forall n : int, n != 0 -> mulQ D n <> None.
  Proof.
    move=> Hp Hv Hb Hx Hvx n Hn Hnone.
    have Hb1 : mulQ D (b * 1) = Some (x, y) by rewrite mulr1.
    have [x' [y' [H1 _]]] :=
      kernel_mul Hp Hv (mulPn_on 1) (mulPn_add 1) (mulPn_0 1) (mulPn_neg 1) Hb1 Hx Hvx Hn.
    have Hn' : mulQ D (n * `|b|%:Z) = None by exact: mulQ_none_mul.
    move: H1; rewrite mulr1.
    case: b Hb Hb1 Hn' => [ b | b ] Hb Hb1 Hn'.
    - by rewrite mulrC Hn'.
    - rewrite NegzE mulNr mulQ_neg mulrC.
      by move: Hn'; rewrite NegzE => ->.
  Qed.

  (** O_F1 (eq. ell:ratio) from E2 *)
  Theorem O_F1_of_E2 : (0 < fd_m D)%N ->
    (forall n : int, n != 0 ->
       exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y)) ->
    forall (sg : bool) (p : nat), prime p ->
      forall v, is_place_above v p ->
      forall n n' : int, n' != 0 ->
      red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
      n = 0 \/ v (zpar sg (mulP D n)) - v (zpar sg (mulP D n')) = vqr p n%:~R - vqr p n'%:~R.
  Proof.
    move=> Hm0 HE2 sg p Hp v Hv n n' Hn' Hr Hr'.
    case: (eqVneq n 0) => [ -> | Hn ]; [ by left | right ].
    have Hm : (fd_m D)%:Z != 0 by rewrite -lt0n.
    have [x [y [E1 [Hx [_ _]]]]] := HE2 _ (mulf_neq0 Hn Hm).
    have [x' [y' [E1' [Hx' [_ _]]]]] := HE2 _ (mulf_neq0 Hn' Hm).
    move: Hr Hr'; rewrite /mulP E1 E1'.
    have Hon := mulPn_on (fd_m D); have Had := mulPn_add (fd_m D).
    have H0 := mulPn_0 (fd_m D); have Hng := mulPn_neg (fd_m D).
    case: sg => Hr Hr'.
    - have Hw := conj_place Hv.
      have := kernel_ratio Hp Hw Hon Had H0 Hng E1 Hx Hr E1' Hx' Hr'.
      rewrite E1 E1' => H; rewrite !qe_conj_zk; exact H.
    - have := kernel_ratio Hp Hv Hon Had H0 Hng E1 Hx Hr E1' Hx' Hr'.
      rewrite E1 E1' => H; rewrite !zk_zpar; exact H.
  Qed.

End group_law.

(** * The explicit data: 10 Q0 lies in the kernel of reduction at a place above 17

    Bridging TODO (a) of ExplicitData.v. *)

Lemma int_pos1 (a : int) : 0 < a -> 1 <= a.
Proof. move=> H; ilia. Qed.

Lemma int_neg1 (a : int) : 1 <= a -> 0 - a < 0.
Proof. move=> H; ilia. Qed.

Lemma Zmod17_mul (j : nat) : Z.modulo (Z.of_nat (j * 17)) 17 = 0%ZZ.
Proof. rewrite Nat2Z.inj_mul; exact: Z_mod_mult. Qed.

Section place17.

  Variable v : qe rat -> int.
  Hypothesis Hv : is_place_above v 17.
  Hypothesis H6 : 0 < v (qe_sqrt2 - 6%:R).

  Lemma prime17 : prime 17. Proof. by []. Qed.

  Lemma coprime17 (n : nat) : Z.modulo (Z.of_nat n) 17 <> 0%ZZ -> coprime n 17.
  Proof.
    move=> H; rewrite coprime_sym prime_coprime //; apply/negP => /dvdnP [j Hj].
    by apply: H; rewrite Hj Zmod17_mul.
  Qed.

  (* integers prime to 17 are units at v *)
  Lemma vzr_unit (u : Z) : Z.modulo u 17 <> 0%ZZ ->
    (QE (zr u) 0 : KRF) != 0 /\ v (QE (zr u) 0) = 0.
  Proof.
    case: u => [ | q | q ] Hu; first by exfalso; apply: Hu.
    - have Hq : (0 < Pos.to_nat q)%N by case: (Pos2Nat.is_succ q) => j ->.
      have Hc : coprime (Pos.to_nat q) 17.
      { apply: coprime17; by rewrite positive_nat_Z. }
      rewrite zr_pos -qe_natE; split; [ exact (KRF_nat_neq0 Hq) | exact (v_coprime Hv Hq Hc) ].
    - have Hq : (0 < Pos.to_nat q)%N by case: (Pos2Nat.is_succ q) => j ->.
      have Hc : coprime (Pos.to_nat q) 17.
      { apply: coprime17; rewrite positive_nat_Z => H0; apply: Hu.
        rewrite -Pos2Z.opp_pos; apply/Z_mod_zero_opp_full; exact: H0. }
      have -> : QE (zr (Z.neg q)) 0 = - ((Pos.to_nat q)%:R : KRF).
      { by rewrite zr_neg qe_natE qe_oppE oppr0. }
      rewrite oppr_eq0 (vN Hv); split; [ exact (KRF_nat_neq0 Hq) | exact (v_coprime Hv Hq Hc) ].
  Qed.

  Lemma s6_neq0 : (qe_sqrt2 - 6%:R : KRF) != 0.
  Proof.
    rewrite subr_eq0; apply/eqP => /(congr1 (@qim rat)).
    rewrite qe_natE /qe_sqrt2 /= => /eqP; by rewrite oner_eq0.
  Qed.

  Lemma tq_split (a b : Z) :
    (QE (zr a) (zr b) : KRF) = QE (zr (a + 6 * b)) 0 + QE (zr b) 0 * (qe_sqrt2 - 6%:R).
  Proof.
    rewrite /qe_sqrt2 qe_natE qe_subE qe_mulE qe_addE zr_add zr_mul.
    have -> : zr 6 = 6%:R := zr_nat 6.
    congr QE; ring.
  Qed.

  Lemma tq_mul_den (a b c : Z) : c <> 0%ZZ ->
    (tq (a, b, c) : KRF) * QE (zr c) 0 = QE (zr a) (zr b).
  Proof.
    move=> Hc; have Hc' := zr_neq0 Hc.
    rewrite /tq qe_mulE; congr QE; field.
  Qed.

  (* a reduced triple with a pole at sqrt2 |-> 6 has negative valuation *)
  Lemma pole_val (t : zt) : wfz t -> pole_at 17 6 t ->
    (tq t : KRF) != 0 /\ v (tq t) < 0.
  Proof.
    case: t => [ [ a b ] c ] Hc Hp; simpl in Hc.
    have /andP [ /Z.eqb_eq Hc17 Hab ] :
      ((Z.modulo c 17 =? 0) && ~~ (Z.modulo (a + 6 * b) 17 =? 0))%ZZ := Hp.
    have Hab' : Z.modulo (a + 6 * b) 17 <> 0%ZZ by move=> H; move: Hab; rewrite H.
    have [HU0 HvU] := vzr_unit Hab'.
    have h6 : vge v 1 (qe_sqrt2 - 6%:R : KRF) by right; exact: int_pos1.
    have hb : vge v 1 ((QE (zr b) 0 : KRF) * (qe_sqrt2 - 6%:R)).
    { have := vge_mul Hv (vge_zr Hv b) h6; rewrite add0r => H; exact H. }
    have HUlt : v (QE (zr (a + 6 * b)) 0 : KRF) < 1 by rewrite HvU.
    have [HA0 HvA] := vge_strict Hv HU0 hb HUlt.
    rewrite -tq_split in HA0 HvA; rewrite HvU in HvA.
    (* the denominator *)
    have [c' Ec] : exists c', c = (17 * c')%ZZ.
    { exists (c / 17)%ZZ; have := Z_div_mod_eq_full c 17; rewrite Hc17; lia. }
    have HC0 : (QE (zr c) 0 : KRF) != 0.
    { rewrite qe0E; apply/eqP => -[] /eqP; by rewrite (negbTE (zr_neq0 Hc)). }
    have hC : vge v 1 (QE (zr c) 0 : KRF).
    { have -> : (QE (zr c) 0 : KRF) = 17%:R * QE (zr c') 0.
      { have Z17 : zr 17 = 17%:R := zr_nat 17.
        rewrite Ec zr_mul Z17 qe_natE qe_mulE.
        by rewrite !(mulr0, mul0r, addr0). }
      have := vge_mul Hv (vge_p Hv) (vge_zr Hv c'); rewrite addr0 => H; exact H. }
    have HvC := vge_nz HC0 hC.
    have Et : (tq (a, b, c) : KRF) = QE (zr a) (zr b) / QE (zr c) 0.
    { apply: (mulIf HC0); rewrite (tq_mul_den a b Hc).
      by rewrite divfK. }
    rewrite Et; split; first by rewrite mulf_neq0 ?invr_eq0.
    rewrite (vdiv Hv) // HvA; exact: int_neg1.
  Qed.

End place17.

(* every place above 17 has sqrt2 |-> 6 or sqrt2 |-> -6, so either v or
   its conjugate has v(sqrt2 - 6) > 0 *)
Lemma int_one_of (a b : int) : 0 <= a -> 0 <= b -> a + b = 1 -> 0 < a \/ 0 < b.
Proof. move=> H1 H2 H3; case: (ltrP 0 a) => H; [ by left | right; ilia ]. Qed.

Lemma place17_sqrt2_6 (v : qe rat -> int) : is_place_above v 17 ->
  exists w : qe rat -> int, is_place_above w 17 /\ 0 < w (qe_sqrt2 - 6%:R).
Proof.
  move=> Hv.
  set a : KRF := qe_sqrt2 - 6%:R; set b : KRF := qe_sqrt2 + 6%:R.
  have Hab : a * b = - (2%:R * 17%:R).
  { rewrite /a /b /qe_sqrt2 !qe_natE qe_subE qe_addE qe_mulE qe_oppE.
    congr QE; ring. }
  have Ha0 : a != 0 by exact: s6_neq0.
  have Hb0 : b != 0.
  { rewrite /b -[6%:R]opprK subr_eq0; apply/eqP => /(congr1 (@qim rat)).
    rewrite qe_natE /qe_sqrt2 /= oppr0 => /eqP; by rewrite oner_eq0. }
  have h6 : vge v 0 (6%:R : KRF) := vge_nat Hv 6.
  have ha : vge v 0 a := vge_sub Hv (vge_sqrt2 Hv) h6.
  have hb : vge v 0 b := vge_add Hv (vge_sqrt2 Hv) h6.
  have H20 : (0 < 2)%N by [].
  have H21 : coprime 2 17 by [].
  have H2 : v (2%:R : KRF) = 0 := v_coprime Hv H20 H21.
  have Hs : v a + v b = 1.
  { have N2 : (2%:R : KRF) != 0 := KRF_nat_neq0 H20.
    have H170 : (0 < 17)%N by [].
    have N17 : (17%:R : KRF) != 0 := KRF_nat_neq0 H170.
    rewrite -(vM Hv Ha0 Hb0) Hab (vN Hv) (vM Hv N2 N17) H2 (vP Hv).
    exact: add0r. }
  case: (int_one_of (vge_nz Ha0 ha) (vge_nz Hb0 hb) Hs) => H.
  - exists v; split; [ exact Hv | exact H ].
  - exists (fun x => v (qe_conj x)); split; first exact (conj_place Hv).
    have -> : qe_conj (qe_sqrt2 - 6%:R) = - b.
    { rewrite /b /qe_sqrt2 !qe_natE qe_subE qe_addE qe_oppE /qe_conj /=.
      congr QE; ring. }
    rewrite (vN Hv); exact H.
Qed.

(** * E2 and O_F1 for the explicit data *)

Section explicit.

  (* TO-MERGE from GroupLaw.v: [mulQ_on] (stated there with [on_curve_pt] = [onp]) *)
  Hypothesis mulQ_on_h : forall D : FixedData, on_curve (fd_P0 D) ->
    forall n : int, onp (mulQ D n).
  (* TO-MERGE from GroupLaw.v: [mulQ_add] *)
  Hypothesis mulQ_add_h : forall D : FixedData, on_curve (fd_P0 D) ->
    forall n n' : int, mulQ D (n + n') = ec_add (mulQ D n) (mulQ D n').
  (* TO-MERGE from OrdPlaces.v: a place of F above 17, e.g.
     [ovP_is_place (ord_PL1 (q := 17) isT isT) : is_place_above (ovP (oplace 17)) 17] *)
  Hypothesis place17 : exists v : qe rat -> int, is_place_above v 17.

  Variables (C : i4 -> rat) (S : seq nat) (Hb c : nat) (Kset : seq nat) (Nh Ch : nat).
  Local Abbreviation D := (mkData C S Hb c Kset Nh Ch).

  (* 10 Q0 lies in the kernel of reduction at v *)
  Lemma mkData_10_kernel (v : qe rat -> int) :
    is_place_above v 17 -> 0 < v (qe_sqrt2 - 6%:R) ->
    exists x y : qe rat, mulQ D 10%:Z = Some (x, y) /\ (x : KRF) != 0 /\ v x < 0.
  Proof.
    move=> Hv H6.
    have [x [y [H10 [Hx [Hy [Px Py]]]]]] := mkData_mulQ10 C S Hb c Kset Nh Ch.
    have [Hx0 Hvx] := pole_val Hv H6 Hx Px.
    exists (tq x), (tq y); split; first exact H10.
    split; [ exact Hx0 | exact Hvx ].
  Qed.

  Theorem mkData_nontorsion : forall n : int, n != 0 -> mulQ D n <> None.
  Proof.
    have [v0 Hv0] := place17.
    have [v [Hv H6]] := place17_sqrt2_6 Hv0.
    have [x [y [H10 [Hx Hvx]]]] := mkData_10_kernel Hv H6.
    exact: (nontorsion_of_kernel mulQ_on_h mulQ_add_h (mkData_P0_on_curve C S Hb c Kset Nh Ch)
              prime17 Hv H10 Hx Hvx).
  Qed.

  (* the field E2 of StdHyps for the explicit data *)
  Theorem E2_mkData : forall n : int, n != 0 ->
    exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y).
  Proof.
    exact: (E2_of_nontorsion mulQ_on_h mulQ_add_h (mkData_P0_on_curve C S Hb c Kset Nh Ch)
              mkData_nontorsion).
  Qed.

  (* the field O_F1 of OrdHyps for the explicit data *)
  Theorem O_F1_mkData : forall (sg : bool) (p : nat), prime p -> p \notin fd_SE D ->
      forall v, is_place_above v p ->
      forall n n' : int, n' != 0 ->
      red_ord sg v (mulP D n) -> red_ord sg v (mulP D n') ->
      n = 0 \/ v (zpar sg (mulP D n)) - v (zpar sg (mulP D n')) = vqr p n%:~R - vqr p n'%:~R.
  Proof.
    have H := O_F1_of_E2 mulQ_on_h mulQ_add_h (mkData_P0_on_curve C S Hb c Kset Nh Ch)
              (mkData_wf_m C S Hb c Kset Nh Ch) E2_mkData.
    move=> sg p Hp _; exact (H sg p Hp).
  Qed.

  (* the statements are literally the record fields: *)
  Lemma StdHyps_mkData :
    (forall n n' : int, ADDrel (mulQ D n) (mulQ D n') (mulQ D (n + n'))) ->
    (forall (K : nat) (A : int), (1 <= K)%N -> exists W : RepWit1, RepSpec D K A W) ->
    (forall b : int, Phi_holdsR (fd_PhiL D) (b%:~R : rat)) ->
    StdHyps D.
  Proof. move=> H1 H3 H4; exact: (Build_StdHyps H1 E2_mkData H3 H4). Qed.

End explicit.
