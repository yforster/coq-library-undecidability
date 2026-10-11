(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* A special case of the structure theorem for finitely generated
   abelian groups (PLAN P14b-iii, Phase 2E). Pure abstract algebra.

   SETTING. An arbitrary MathComp [zmodType] A (Leibniz equality);
   integer scaling is MathComp's [x *~ n] (element on the LEFT).
   - [tors a]       : exists n <> 0, a *~ n = 0;
   - [lcomb c L]    : sum_i L_i *~ c i  (c : nat -> int), see [lcomb_sum];
   - [fingen L]     : every a is [lcomb c L] for some c;
   - [two_cosets R] : R is a duplicate-free list of 8 elements and every
                      a is  b *~ 2 + r  with r in R  (|A/2A| <= 8 and 8
                      representatives; pairwise incongruence of R is NOT
                      needed);
   - [tors_V4 T]    : T is a duplicate-free list of 4 elements, 2 t = 0
                      on T, every torsion element is in T, and there is
                      no element of order 4:  a *~ 2 \in T -> a \in T.

   MAIN THEOREM [fg_rank_one]:
     fingen L -> two_cosets R -> tors_V4 T ->
     exists G, ~ tors G /\ forall a, exists n t, t \in T /\ a = G *~ n + t.
   Corollaries: [nontors_mulz_inj], [decomp_unique], [twoA_cyclic].

   ROUTE ("free basis modulo torsion" by Euclid on generators; no
   quotients, no lattices). Everything is done modulo torsion:
   [inspan L a] := exists c, tors (a - lcomb c L), and
   [indep L]     := tors (lcomb c L) -> c i = 0 for all i < size L.
   1. [euclid2]: for x, y and c <> 0, d there are z, w, g <> 0 with
      x c + y d = z g and x, y in Z z + Z w (Euclid on (c, d) by
      unimodular changes of the pair of generators; measure |d|).
   2. [red]: a relation  x c + lcomb ds L1 in tors  with c <> 0 lets us
      replace x :: L1 by a list of length <= size L1 spanning at least
      as much modulo torsion (fold [euclid2] along L1, keeping the
      "w"s; at the end x' g in tors with g <> 0, so x' in tors and is
      dropped). [notindep_red]: the same for a relation with any
      nonzero coefficient.
   3. [basis]: every L has an independent (modulo torsion) list E with
      size E <= size L and inspan L <= inspan E (strong induction on
      the size; classical case split on [indep L]).
   4. Counting, for an independent generating E:
      - E = []   : A = T, so the 8 distinct elements of R lie in T (4).
      - E = [G]  : the conclusion.
      - |E| >= 2 : with e1, e2 the first two entries, the 16 elements
        (eps1 e1 + eps2 e2) + t (eps in {0,1}, t in T) are pairwise
        incongruent modulo 2A (independence of e1, e2 modulo torsion,
        2 T = 0, and "no order 4"), contradicting the 8 coset
        representatives (pigeonhole [pigeon]).
   Only [classic] is used (via NNPP / case splits). *)

From Stdlib Require Import Classical_Prop.
From mathcomp Require Import boot algebra.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section FGAbelian.

Variable A : zmodType.
Implicit Types (a b s t x y z w : A) (L E : seq A) (c d : nat -> int).

(* ------------------------------------------------------------------ *)
(* Torsion                                                              *)

Definition tors a := exists n : int, n != 0 /\ a *~ n = 0.

Lemma tors0 : tors 0.
Proof. by exists 1; rewrite mul0rz. Qed.

Lemma torsD a b : tors a -> tors b -> tors (a + b).
Proof.
move=> [n [n0 an]] [m [m0 bm]]; exists (n * m); split; first by rewrite mulf_neq0.
rewrite mulrzDl mulrzA an mul0rz add0r.
by rewrite mulrC mulrzA bm mul0rz.
Qed.

Lemma torsN a : tors a -> tors (- a).
Proof. by move=> [n [n0 an]]; exists n; rewrite mulNrz an oppr0. Qed.

Lemma torsB a b : tors a -> tors b -> tors (a - b).
Proof. by move=> ta tb; apply: torsD => //; apply: torsN. Qed.

Lemma torsZ a k : tors a -> tors (a *~ k).
Proof. by move=> [n [n0 an]]; exists n; rewrite mulrzAC an mul0rz. Qed.

Lemma tors_div a k : k != 0 -> tors (a *~ k) -> tors a.
Proof.
move=> k0 [n [n0 an]]; exists (k * n); split; first by rewrite mulf_neq0.
by rewrite mulrzA.
Qed.

(* ------------------------------------------------------------------ *)
(* Integer combinations                                                 *)

Fixpoint lcomb c L : A :=
  if L is x :: L' then x *~ c 0%N + lcomb (fun i => c i.+1) L' else 0.

Lemma lcomb_sum c L : lcomb c L = \sum_(i < size L) L`_i *~ c i.
Proof.
elim: L c => [|x L IH] c /=; first by rewrite big_ord0.
by rewrite big_ord_recl IH.
Qed.

Definition fingen L := forall a, exists c, a = lcomb c L.

Lemma lcomb_ext c d L : (forall i, c i = d i) -> lcomb c L = lcomb d L.
Proof.
elim: L c d => [|x L IH] c d //= h.
by rewrite h (IH _ (fun i => d i.+1)).
Qed.

Lemma lcomb0 L : lcomb (fun _ => 0) L = 0.
Proof. by elim: L => [|x L IH] //=; rewrite IH addr0. Qed.

Lemma lcombD c d L :
  lcomb (fun i => c i + d i) L = lcomb c L + lcomb d L.
Proof.
elim: L c d => [|x L IH] c d /=; first by rewrite addr0.
by rewrite mulrzDr IH addrACA.
Qed.

Lemma lcombN c L : lcomb (fun i => - c i) L = - lcomb c L.
Proof.
elim: L c => [|x L IH] c /=; first by rewrite oppr0.
by rewrite mulrNz IH opprD.
Qed.

Lemma lcombZ c L k : lcomb c L *~ k = lcomb (fun i => c i * k) L.
Proof.
elim: L c => [|x L IH] c /=; first by rewrite mul0rz.
by rewrite mulrzDl IH mulrzA.
Qed.

(* ------------------------------------------------------------------ *)
(* Span and independence modulo torsion                                 *)

Definition inspan L a := exists c, tors (a - lcomb c L).

Definition indep L :=
  forall c, tors (lcomb c L) -> forall i, (i < size L)%N -> c i = 0.

Lemma inspan_nil a : inspan [::] a <-> tors a.
Proof.
split; first by move=> [c]; rewrite /= subr0.
by move=> ta; exists (fun _ => 0); rewrite /= subr0.
Qed.

Lemma inspan_cons x L a :
  inspan (x :: L) a <-> exists k, inspan L (a - x *~ k).
Proof.
split.
  by move=> [c tc]; exists (c 0%N), (fun i => c i.+1); rewrite -addrA -opprD.
move=> [k [c tc]]; exists (fun i => if i is j.+1 then c j else k) => /=.
by rewrite opprD addrA.
Qed.

Lemma fingen_inspan L : fingen L -> forall a, inspan L a.
Proof. by move=> hL a; have [c ->] := hL a; exists c; rewrite subrr; apply: tors0. Qed.

(* ------------------------------------------------------------------ *)
(* Step 1: Euclid on a pair of generators                               *)

Definition span2 z w a := exists k m, a = z *~ k + w *~ m.

Lemma span2D z w a b : span2 z w a -> span2 z w b -> span2 z w (a + b).
Proof.
move=> [k [m ->]] [k' [m' ->]]; exists (k + k'), (m + m').
by rewrite !mulrzDr addrACA.
Qed.

Lemma span2Z z w a n : span2 z w a -> span2 z w (a *~ n).
Proof.
by move=> [k [m ->]]; exists (k * n), (m * n); rewrite mulrzDl !mulrzA.
Qed.

Lemma span2B z w a b : span2 z w a -> span2 z w b -> span2 z w (a - b).
Proof.
move=> ha hb; apply: span2D => //; rewrite -mulrN1z; exact: span2Z.
Qed.

Lemma euclid2 (n : nat) x y (c d : int) : (`|d| <= n)%N -> c != 0 ->
  exists z w (g : int), [/\ g != 0, x *~ c + y *~ d = z *~ g,
                            span2 z w x & span2 z w y].
Proof.
elim: n x y c d => [|n IH] x y c d hd c0.
  move: hd; rewrite leqn0 absz_eq0 => /eqP ->.
  exists x, y, c; split => //; last by exists 0, 1; rewrite mulr0z add0r.
    by rewrite mulr0z addr0.
  by exists 1, 0; rewrite mulr0z addr0.
have [d0|d0] := eqVneq d 0.
  rewrite d0; exists x, y, c; split => //; last by exists 0, 1; rewrite mulr0z add0r.
    by rewrite mulr0z addr0.
  by exists 1, 0; rewrite mulr0z addr0.
pose q := (c %/ d)%Z; pose r := (c %% d)%Z.
have hr : (`|r| <= n)%N.
  have := ltz_mod c d0; rewrite -/r -[r](gez0_abs (modz_ge0 c d0)) ltz_nat => h.
  by rewrite -ltnS (leq_trans h hd).
have [z [w [g [g0 e hx1 hy1]]]] := IH (x *~ q + y) x d r hr d0.
exists z, w, g; split => //.
- rewrite -e {1}(divz_eq c d) -/q -/r mulrzDr mulrzA mulrzDl.
  by rewrite addrAC.
- have -> : y = (x *~ q + y) - x *~ q by rewrite addrC addKr.
  by apply: span2B => //; apply: span2Z.
Qed.

(* ------------------------------------------------------------------ *)
(* Step 2: a relation lets us drop one generator                        *)

Lemma red L1 : forall x (c : int) ds, c != 0 -> tors (x *~ c + lcomb ds L1) ->
  exists L', (size L' <= size L1)%N /\ forall a, inspan (x :: L1) a -> inspan L' a.
Proof.
elim: L1 => [|y L2 IH] x c ds c0 /=.
  rewrite addr0 => /(tors_div c0) tx; exists [::]; split => // a.
  move=> /inspan_cons [k /inspan_nil h]; apply/inspan_nil.
  by rewrite -(subrK (x *~ k) a); apply: torsD => //; apply: torsZ.
move=> h.
have [z [w [g [g0 e hx hy]]]] := euclid2 x y (leqnn `|ds 0%N|) c0.
have h' : tors (z *~ g + lcomb (fun i => ds i.+1) L2) by rewrite -e -addrA.
have [L'' [hs hL'']] := IH z g _ g0 h'.
exists (w :: L''); split => //= a /inspan_cons [k1 /inspan_cons [k2 hk]].
have [k [m e2]] : span2 z w (x *~ k1 + y *~ k2) by apply: span2D; apply: span2Z.
apply/inspan_cons; exists m; apply: hL''; apply/inspan_cons; exists k.
by rewrite -addrA -opprD [w *~ m + _]addrC -e2 opprD addrA.
Qed.

Lemma notindep_red L : forall c, tors (lcomb c L) ->
  (exists i, (i < size L)%N /\ c i != 0) ->
  exists L', (size L' < size L)%N /\ forall a, inspan L a -> inspan L' a.
Proof.
elim: L => [|x L0 IH] c tc [i [hi ci]] //.
have [c0|c0] := eqVneq (c 0%N) 0; last first.
  by have [L' [hs hL]] := @red L0 x (c 0%N) (fun i => c i.+1) c0 tc; exists L'.
move: tc; rewrite /= c0 mulr0z add0r => tc.
case: i hi ci => [|j] hj cj; first by rewrite c0 eqxx in cj.
have [L' [hs hL]] := IH _ tc (ex_intro _ j (conj hj cj)).
exists (x :: L'); split => // a /inspan_cons [k hk].
by apply/inspan_cons; exists k; apply: hL.
Qed.

(* ------------------------------------------------------------------ *)
(* Step 3: an independent generating list modulo torsion                *)

Lemma basis n L : (size L <= n)%N ->
  exists E, [/\ (size E <= size L)%N, indep E & forall a, inspan L a -> inspan E a].
Proof.
elim: n L => [|n IH] L hL.
  by exists L; split => // c _ i hi; move: (leq_trans hi hL).
case: (classic (indep L)) => [iL|nI]; first by exists L.
have [c [tc hc]] : exists c, tors (lcomb c L) /\ exists i, (i < size L)%N /\ c i != 0.
  apply: NNPP => H; apply: nI => c tc i hi; apply/eqP; apply/negPn/negP => ci.
  by apply: H; exists c; split => //; exists i.
have [L' [hs hL']] := notindep_red tc hc.
have [E [hE iE sE]] := IH L' (leq_trans hs hL).
exists E; split => //; first exact: leq_trans hE (ltnW hs).
by move=> a /hL' /sE.
Qed.

(* ------------------------------------------------------------------ *)
(* Step 4: counting                                                     *)

Lemma pigeon (rel : A -> A -> Prop) (R S : seq A) : uniq S ->
  (forall s, s \in S -> exists r, r \in R /\ rel s r) ->
  (forall s s' r, s \in S -> s' \in S -> rel s r -> rel s' r -> s = s') ->
  (size S <= size R)%N.
Proof.
elim: R S => [|r R IH] S uS hcov hinj.
  case: S uS hcov hinj => // s S _ hcov _.
  by have [r' []] := hcov s (mem_head _ _).
case: (classic (exists s0, s0 \in S /\ rel s0 r)) => [[s0 [s0S rs0]]|hn].
  have hm : forall s, s \in rem s0 S -> s != s0 /\ s \in S.
    by move=> s; rewrite mem_rem_uniq // => /andP.
  have h1 : forall s, s \in rem s0 S -> exists r', r' \in R /\ rel s r'.
    move=> s /hm [ns sS]; have [r' []] := hcov s sS.
    rewrite in_cons => /orP [/eqP -> rs|r'R rs]; last by exists r'.
    by case/eqP: ns; apply: hinj rs rs0.
  have h2 : forall s s' r', s \in rem s0 S -> s' \in rem s0 S ->
      rel s r' -> rel s' r' -> s = s'.
    by move=> s s' r' /hm [_ sS] /hm [_ s'S]; apply: hinj.
  have := IH _ (rem_uniq _ uS) h1 h2; rewrite size_rem //=.
  by case: (size S).
apply: leqW; apply: IH => // s sS; have [r' []] := hcov s sS.
rewrite in_cons => /orP [/eqP -> rs|r'R rs]; last by exists r'.
by exfalso; apply: hn; exists s.
Qed.

Lemma bool_parity (u v : bool) (k : int) :
  (nat_of_bool u)%:Z - (nat_of_bool v)%:Z = k * 2 -> u = v.
Proof.
case: u; case: v => //= h; have := dvdz_mull k (dvdzz 2); rewrite -h //.
Qed.

Definition two_cosets (R : seq A) :=
  [/\ uniq R, size R = 8%N & forall a, exists b r, r \in R /\ a = b *~ 2 + r].

Definition tors_V4 (T : seq A) :=
  [/\ uniq T, size T = 4%N, (forall t, t \in T -> t *~ 2 = 0),
      (forall a, tors a -> a \in T) & (forall a, a *~ 2 \in T -> a \in T)].

Section Rank2.

Variables (T : seq A) (e1 e2 : A) (E' : seq A).
Hypothesis hT2 : forall t, t \in T -> t *~ 2 = 0.
Hypothesis hTt : forall a, tors a -> a \in T.
Hypothesis hT4 : forall a, a *~ 2 \in T -> a \in T.
Hypothesis iE : indep [:: e1, e2 & E'].
Hypothesis sE : forall a, inspan [:: e1, e2 & E'] a.

Lemma memT_tors t : t \in T -> tors t.
Proof using hT2. by move=> tT; exists 2; split => //; apply: hT2. Qed.

Definition xp (p : bool * bool) :=
  e1 *~ (nat_of_bool p.1)%:Z + e2 *~ (nat_of_bool p.2)%:Z.

Lemma addsub_helper (X X' t t' : A) : X - X' - (X + t - (X' + t')) = t' - t.
Proof.
by rewrite opprB addrA addrA subrK opprD addrACA subrr add0r.
Qed.

Lemma cong_inj p p' t t' b : t \in T -> t' \in T ->
  xp p + t = b *~ 2 + (xp p' + t') -> p = p' /\ t = t'.
Proof using hT2 hTt hT4 iE sE.
move=> tT t'T e.
have [c tc] := sE b.
set s := b - lcomb c _ in tc.
have s2 : s *~ 2 = 0 by apply: hT2; apply: hTt.
have hl : lcomb c [:: e1, e2 & E'] = b - s by rewrite /s opprB addrC subrK.
have eb : b *~ 2 = xp p + t - (xp p' + t') by rewrite e addrK.
pose d1 i := if i is 0 then (nat_of_bool p.1)%:Z - (nat_of_bool p'.1)%:Z
             else if i is 1 then (nat_of_bool p.2)%:Z - (nat_of_bool p'.2)%:Z
             else 0.
pose d i := d1 i - c i * 2.
have hd1 : lcomb d1 [:: e1, e2 & E'] = xp p - xp p'.
  rewrite /= lcomb0 addr0 /xp !mulrzBr opprD addrACA //.
have hd : lcomb d [:: e1, e2 & E'] = t' - t.
  rewrite /d lcombD lcombN -lcombZ hd1 hl mulrzBl s2 subr0 eb.
  exact: addsub_helper.
have td : tors (lcomb d [:: e1, e2 & E']) by rewrite hd; apply: torsB; apply: memT_tors.
have d0 := iE td (i := 0%N) isT.
have d1' := iE td (i := 1%N) isT.
move/subr0_eq/bool_parity: d0 => h1; move/subr0_eq/bool_parity: d1' => h2.
have pp : p = p' := @injective_projections _ _ p p' h1 h2.
split => //; move: e; rewrite -pp addrCA => /addrI et.
have b2T : b *~ 2 \in T.
  have -> : b *~ 2 = t - t' by rewrite et addrK.
  by apply: hTt; apply: torsB; apply: memT_tors.
by rewrite et hT2 ?add0r //; apply: hT4.
Qed.

Lemma no_rank2 (R : seq A) : uniq T -> size T = 4%N -> size R = 8%N ->
  (forall a, exists b r, r \in R /\ a = b *~ 2 + r) -> False.
Proof using hT2 hTt hT4 iE sE.
move=> uT sT sR hR.
pose P4 := [:: (false, false); (false, true); (true, false); (true, true)].
pose S := [seq xp p + t | p <- P4, t <- T].
suff : (size S <= size R)%N by rewrite /S size_allpairs sT sR.
apply: (@pigeon (fun u v => exists b, u = b *~ 2 + v)).
- apply: allpairs_uniq => // -[p t] [p' t'].
  move=> /allpairsP [[q1 q2] [_ q2T eq1]].
  move=> /allpairsP [[q1' q2'] [_ q2T' eq2]].
  move: eq1 eq2 => /= [-> ->] [-> ->] /= e.
  have e' : xp q1 + q2 = 0 *~ 2 + (xp q1' + q2') by rewrite mul0rz add0r.
  by have [-> ->] := @cong_inj q1 q1' q2 q2' _ q2T q2T' e'.
- move=> s _; have [b [r [rR ->]]] := hR s.
  by exists r; split => //; exists b.
- move=> s s' r /allpairsP [[q1 q2] [_ q2T ->]] /allpairsP [[q1' q2'] [_ q2T' ->]].
  move=> [b eb] [b' eb'].
  have e' : xp q1 + q2 = (b - b') *~ 2 + (xp q1' + q2').
    by rewrite eb eb' mulrzBl addrA subrK.
  by have [-> ->] := @cong_inj q1 q1' q2 q2' _ q2T q2T' e'.
Qed.

End Rank2.

(* ------------------------------------------------------------------ *)
(* Main theorem                                                         *)

Theorem fg_rank_one L R T : fingen L -> two_cosets R -> tors_V4 T ->
  exists G, ~ tors G /\ forall a, exists n t, t \in T /\ a = G *~ n + t.
Proof.
move=> hL [uR sR hR] [uT sT hT2 hTt hT4].
have [E [_ iE sE]] := @basis _ L (leqnn _).
have {sE}sE' : forall a, inspan E a by move=> a; apply: sE; apply: fingen_inspan.
case: E iE sE' => [|G [|e2 E']] iE sE'.
- exfalso; have : (size R <= size T)%N.
    by apply: uniq_leq_size => // r _; apply: hTt; apply/inspan_nil.
  by rewrite sR sT.
- exists G; split.
    move=> tG; have h1 : tors (lcomb (fun _ => 1) [:: G]) by rewrite /= mulr1z addr0.
    by have := iE _ h1 0%N isT.
  move=> a; have /inspan_cons [k /inspan_nil ta] := sE' a.
  exists k, (a - G *~ k); split; first exact: hTt.
  by rewrite addrC subrK.
- exfalso; exact: (no_rank2 hT2 hTt hT4 iE sE' uT sT sR hR).
Qed.

(* ------------------------------------------------------------------ *)
(* Corollaries                                                          *)

Lemma nontors_mulz_inj G (n m : int) : ~ tors G -> G *~ n = G *~ m -> n = m.
Proof.
move=> nG e; apply/eqP; apply/negPn/negP => nm; apply: nG.
by exists (n - m); split; [rewrite subr_eq0 | rewrite mulrzBr e subrr].
Qed.

Lemma decomp_unique (T : seq A) G (n m : int) t t' :
  (forall t, t \in T -> t *~ 2 = 0) -> ~ tors G -> t \in T -> t' \in T ->
  G *~ n + t = G *~ m + t' -> n = m /\ t = t'.
Proof.
move=> hT2 nG tT t'T e.
have tt : forall u, u \in T -> tors u by move=> u uT; exists 2; split => //; apply: hT2.
have nm : n = m.
  apply/eqP; apply/negPn/negP => nm; apply: nG; apply: (@tors_div _ (n - m)).
    by rewrite subr_eq0.
  have -> : G *~ (n - m) = t' - t.
    have e1 : G *~ n = t' - t + G *~ m.
      by apply: (addIr t); rewrite e addrAC subrK addrC.
    by rewrite mulrzBr e1 addrK.
  by apply: torsB; apply: tt.
by split => //; move: e; rewrite nm => /addrI.
Qed.

Lemma twoA_cyclic (T : seq A) G : (forall t, t \in T -> t *~ 2 = 0) ->
  (forall a, exists n t, t \in T /\ a = G *~ n + t) ->
  forall a, (exists b, a = b *~ 2) <-> exists n : int, a = (G *~ 2) *~ n.
Proof.
move=> hT2 hG a; split.
  move=> [b ->]; have [n [t [tT ->]]] := hG b.
  by exists n; rewrite mulrzDl (hT2 _ tT) addr0 mulrzAC.
by move=> [n ->]; exists (G *~ n); rewrite mulrzAC.
Qed.

End FGAbelian.

(* Print Assumptions fg_rank_one.  ==>  Axioms: classic *)
