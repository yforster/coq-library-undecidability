(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Heights on P^1(F), F = Q(sqrt2), without real numbers (PLAN P13).

   1. [RF]: the field F = Q(sqrt2) (the field copy [QF rat rat_sq2] of
      GroupLaw.v) with the ORDER of its first real embedding
      sigma1 : a + b sqrt2 |-> a + b sqrt2 in R. The order is obtained by
      transport along the injective ring morphism [s1] into MathComp's
      algebraic numbers [algC] (closed under the global context), so
      [RF] is a [realFieldType] and [lra], [Num.max], ... are available.
      [`|x|] is |sigma1 x|, [`|qe_conj x|] is |sigma2 x|.
   2. [isI]: the ring of integers Z[sqrt2]; the norm of a nonzero
      element of Z[sqrt2] is a nonzero integer.
   3. A Euclidean algorithm on Z[sqrt2] ([egcd], rounding of both
      coordinates) and from it a COMPUTABLE coprime representative
      [crepx x = (a, b)] of the point [x : 1] of P^1(F): a, b in Z[sqrt2],
      u a + w b = 1 for some u, w in Z[sqrt2], a = x b, b <> 0.
   4. The (squared, multiplicative) height of a representative,
        Mh (a, b) = max(|a|, |b|) * max(|a'|, |b'|)   (' = conjugation),
      which for a coprime representative is exactly the relative
      multiplicative height H_F(x) = H(x)^2 (H the absolute multiplicative
      Weil height; the finite places contribute nothing, Z[sqrt2] being a
      PID). Proved: Mh >= 1 on coprime
      representatives, Mh is minimal at the coprime representative among
      all integral representatives ([Mh_min]), the height of
      (x0 + x1 sqrt2)/x2 in terms of the bit heights [htb] of x0, x1, x2
      ([Mh_htb]), and a Northcott property ([Mh_bounded_mem]): the
      points of height <= X lie in an explicit finite list.

   No axioms. *)

From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp Require Import algC.

From Undecidability.H10.Rational Require Import FixedData GroupLaw OrdHeights.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.

Local Open Scope ring_scope.

Local Set Warnings "-redundant-canonical-projection".

(** * 1. The real field  F = Q(sqrt2)  ordered by its first embedding *)

Definition RF : Type := @QF rat rat_sq2.

HB.instance Definition _ := GRing.Field.on RF.



(* sigma1 : F -> algC *)
Definition s1 (x : RF) : algC := ratr (qre x) + ratr (qim x) * sqrtC 2%:R.

Lemma sqrt2C_sqr : sqrtC 2%:R * sqrtC 2%:R = 2%:R :> algC.
Proof. by rewrite -expr2 sqrtCK. Qed.

Lemma sqrt2C_real : (sqrtC 2%:R : algC) \is Num.real.
Proof. by apply: ger0_real; rewrite sqrtC_ge0 ler0n. Qed.

Lemma s1_real x : s1 x \is Num.real.
Proof.
  have hr (q : rat) : (ratr q : algC) \is Num.real by apply: Creal_Crat; apply: Crat_rat.
  by rewrite /s1; apply: rpredD; [ exact: hr | apply: rpredM; [ exact: hr | exact: sqrt2C_real ] ].
Qed.

Lemma RF_addE (a b c d : rat) : QE a b + QE c d = QE (a + c) (b + d) :> RF.
Proof. by []. Qed.
Lemma RF_oppE (a b : rat) : - QE a b = QE (- a) (- b) :> RF.
Proof. by []. Qed.
Lemma RF_mulE (a b c d : rat) :
  QE a b * QE c d = QE (a * c + 2%:R * (b * d)) (a * d + b * c) :> RF.
Proof. by []. Qed.
Lemma RF_0E : 0 = QE 0 0 :> RF. Proof. by []. Qed.
Lemma RF_1E : 1 = QE 1 0 :> RF. Proof. by []. Qed.

Lemma s1_add x y : s1 (x + y) = s1 x + s1 y.
Proof.
  case: x y => a b [c d]; rewrite RF_addE /s1 /= !rmorphD /=.
  by rewrite mulrDl; ring.
Qed.

Lemma s1_opp x : s1 (- x) = - s1 x.
Proof. by case: x => a b; rewrite RF_oppE /s1 /= !rmorphN /= mulNr opprD. Qed.

Lemma s1_mul x y : s1 (x * y) = s1 x * s1 y.
Proof.
  case: x y => a b [c d]; rewrite RF_mulE /s1 /= !rmorphD !rmorphM /= ratr_nat.
  set s := sqrtC _.
  have E : (ratr a + ratr b * s) * (ratr c + ratr d * s)
         = ratr a * ratr c + ratr b * ratr d * (s * s) + (ratr a * ratr d + ratr b * ratr c) * s
         :> algC by ring.
  by rewrite E sqrt2C_sqr; ring.
Qed.

Lemma s1_0 : s1 0 = 0. Proof. by rewrite /s1 /= rmorph0 mul0r addr0. Qed.
Lemma s1_1 : s1 1 = 1. Proof. by rewrite /s1 /= rmorph0 rmorph1 mul0r addr0. Qed.

Lemma s1_sub x y : s1 (y - x) = s1 y - s1 x.
Proof. by rewrite s1_add s1_opp. Qed.

Lemma s1_inj0 x : s1 x = 0 -> x = 0.
Proof.
  case: x => a b; rewrite /s1 /= => E.
  case: (eqVneq b 0) => [ eb | nb ].
  - move: E; rewrite eb rmorph0 mul0r addr0 => /eqP; rewrite fmorph_eq0 => /eqP ->.
    by [].
  - exfalso; apply: (@rat_sq2 (- a / b)).
    have Es : sqrtC 2%:R = ratr (- a / b) :> algC.
    { rewrite fmorph_div rmorphN /=.
      have nb' : ratr b != 0 :> algC by rewrite fmorph_eq0.
      apply: (mulIf nb'); rewrite divfK //.
      by apply/eqP; rewrite -subr_eq0 opprK; apply/eqP; rewrite -E; ring. }
    apply: (fmorph_inj (@ratr algC)); rewrite rmorphM /= -Es sqrt2C_sqr.
    by rewrite rmorph_nat.
Qed.

Lemma s1_inj x y : s1 x = s1 y -> x = y.
Proof. by move=> E; apply/eqP; rewrite -subr_eq0; apply/eqP/s1_inj0; rewrite s1_sub E subrr. Qed.

(* locked: the order of [algC] must never be computed (it would not
   terminate in practice), e.g. by [done] trying to evaluate a comparison *)
HB.lock Definition RFle (x y : RF) : bool := 0 <= s1 (y - x).
Lemma RFleE x y : RFle x y = (0 <= s1 (y - x)). Proof. by rewrite unlock. Qed.
Definition RFlt (x y : RF) : bool := (y != x) && RFle x y.
Definition RFnorm (x : RF) : RF := if RFle 0 x then x else - x.

Fact RF_le0_add x y : RFle 0 x -> RFle 0 y -> RFle 0 (x + y).
Proof. by rewrite !RFleE !subr0 s1_add; apply: addr_ge0. Qed.
Fact RF_le0_mul x y : RFle 0 x -> RFle 0 y -> RFle 0 (x * y).
Proof. by rewrite !RFleE !subr0 s1_mul; apply: mulr_ge0. Qed.
Fact RF_le0_anti x : RFle 0 x -> RFle x 0 -> x = 0.
Proof.
  rewrite !RFleE subr0 sub0r s1_opp oppr_ge0 => h1 h2; apply: s1_inj0.
  by apply/eqP; rewrite eq_le h1 h2.
Qed.
Fact RF_sub_ge0 x y : RFle 0 (y - x) = RFle x y.
Proof. by rewrite !RFleE subr0. Qed.
Fact RF_le0_total x : RFle 0 x || RFle x 0.
Proof.
  rewrite !RFleE subr0 sub0r s1_opp oppr_ge0.
  by have := s1_real x; rewrite realE orbC.
Qed.
Fact RFle_x0 x : RFle x 0 = RFle 0 (- x).
Proof. by rewrite !RFleE sub0r subr0. Qed.
Fact RF_normN x : RFnorm (- x) = RFnorm x.
Proof.
  rewrite /RFnorm; case: (boolP (RFle 0 x)) => h1; case: (boolP (RFle 0 (- x))) => h2 //.
  - have h2' : RFle x 0 by rewrite RFle_x0.
    by rewrite (RF_le0_anti h1 h2') oppr0.
  - by rewrite opprK.
  - by move: (RF_le0_total x); rewrite (negbTE h1) RFle_x0 (negbTE h2).
Qed.
Fact RF_ge0_norm x : RFle 0 x -> RFnorm x = x.
Proof. by rewrite /RFnorm => ->. Qed.
Fact RF_lt_def x y : RFlt x y = (y != x) && RFle x y.
Proof. by []. Qed.

HB.instance Definition _ := Num.IntegralDomain_isLeReal.Build RF
  RF_le0_add RF_le0_mul RF_le0_anti RF_sub_ge0 RF_le0_total RF_normN RF_ge0_norm RF_lt_def.

Lemma RF_leE (x y : RF) : (x <= y) = (s1 x <= s1 y).
Proof. by rewrite [LHS]/<=%O /= RFleE s1_sub subr_ge0. Qed.

(* sanity: [RF] is a real field *)
Example RF_lra (x y : RF) : x <= y -> y <= x + 1 -> x <= y + 1.
Proof. move=> *; lra. Qed.

(** ** Rationals and sqrt2 inside RF *)

Definition qr (a : rat) : RF := QE a 0.

Lemma s1_qr a : s1 (qr a) = ratr a.
Proof. by rewrite /s1 /= rmorph0 mul0r addr0. Qed.

Lemma qr_le a b : (qr a <= qr b) = (a <= b).
Proof. by rewrite RF_leE !s1_qr ler_rat. Qed.

Lemma qr_inj : injective qr. Proof. by move=> a b []. Qed.

Lemma qr_lt a b : (qr a < qr b) = (a < b).
Proof. by rewrite !lt_def qr_le (inj_eq qr_inj). Qed.

Lemma qr_add a b : qr (a + b) = qr a + qr b. Proof. by []. Qed.
Lemma qr_opp a : qr (- a) = - qr a. Proof. by []. Qed.
Lemma qr_mul a b : qr (a * b) = qr a * qr b.
Proof. by rewrite RF_mulE /qr; congr QE; ring. Qed.
Lemma qr0 : qr 0 = 0. Proof. by []. Qed.
Lemma qr1 : qr 1 = 1. Proof. by []. Qed.
Lemma qr_nat n : qr n%:R = n%:R.
Proof. by elim: n => // n IH; rewrite -addn1 !natrD qr_add IH. Qed.
Lemma qr_int (z : int) : qr z%:~R = z%:~R.
Proof. by case: z => n; rewrite ?NegzE ?mulrNz ?qr_opp qr_nat. Qed.
Lemma qr_expn a n : qr (a ^+ n) = qr a ^+ n.
Proof. by elim: n => // n IH; rewrite !exprS qr_mul IH. Qed.

Lemma qr_norm a : `|qr a| = qr `|a|.
Proof.
  case: (lerP 0 a) => h.
  - by rewrite ger0_norm ?ger0_norm // -qr0 qr_le.
  - by rewrite ltr0_norm ?ltr0_norm // -qr0 qr_lt.
Qed.

Definition sq2 : RF := QE 0 1.

Lemma sq2_sqr : sq2 * sq2 = 2%:R.
Proof. by rewrite RF_mulE -qr_nat. Qed.

Lemma s1_sq2 : s1 sq2 = sqrtC 2%:R.
Proof. by rewrite /s1 /= rmorph0 rmorph1 mul1r add0r. Qed.

Lemma sq2_ge0 : 0 <= sq2.
Proof. by rewrite RF_leE s1_0 s1_sq2 sqrtC_ge0 ler0n. Qed.

Lemma sq2_ge1 : 1 <= sq2.
Proof. have h0 := sq2_ge0; have e := sq2_sqr; nra. Qed.

Lemma sq2_le2 : sq2 <= 2%:R.
Proof. have h0 := sq2_ge0; have e := sq2_sqr; nra. Qed.

Lemma QE_split (a b : rat) : QE a b = qr a + qr b * sq2 :> RF.
Proof. by rewrite RF_mulE RF_addE /qr; congr QE; ring. Qed.

Lemma norm_QE_le (a b : rat) : `|QE a b : RF| <= qr (`|a| + 2%:R * `|b|).
Proof.
  rewrite QE_split qr_add qr_mul qr_nat -!qr_norm.
  apply: le_trans (ler_normD _ _) _; rewrite lerD2l normrM (ger0_norm sq2_ge0).
  have h1 := sq2_le2; have h2 := normr_ge0 (qr b); nra.
Qed.

(** ** Conjugation on RF *)

Definition cj (x : RF) : RF := qe_conj x.

Lemma cj_add x y : cj (x + y) = cj x + cj y. Proof. exact: qe_conj_add. Qed.
Lemma cj_mul x y : cj (x * y) = cj x * cj y. Proof. exact: qe_conj_mul. Qed.
Lemma cj_opp x : cj (- x) = - cj x. Proof. exact: qe_conj_opp. Qed.
Lemma cj_sub x y : cj (x - y) = cj x - cj y. Proof. by rewrite cj_add cj_opp. Qed.
Lemma cj1 : cj 1 = 1. Proof. exact: qe_conj1. Qed.
Lemma cj0 : cj 0 = 0. Proof. by rewrite /cj /qe_conj /= oppr0. Qed.
Lemma cjK x : cj (cj x) = x. Proof. exact: qe_conjK. Qed.
Lemma cj_qr a : cj (qr a) = qr a. Proof. by rewrite /cj /qe_conj /= oppr0. Qed.
Lemma cj_nat n : cj n%:R = n%:R. Proof. by rewrite -qr_nat cj_qr. Qed.
Lemma cj_expn x n : cj (x ^+ n) = cj x ^+ n.
Proof. by elim: n => [ | n IH ]; rewrite ?cj1 // !exprS cj_mul IH. Qed.
Lemma cj_eq0 x : (cj x == 0) = (x == 0).
Proof. by apply/eqP/eqP => [ h | -> ]; [ rewrite -[x]cjK h cj0 | exact: cj0 ]. Qed.

Lemma mul_cj x : x * cj x = qr (qe_norm x).
Proof. by case: x => a b; rewrite /cj /qe_conj RF_mulE /qe_norm /qr /=; congr QE; ring. Qed.

Lemma qe_norm_eq0 (x : RF) : (qe_norm x == 0) = (x == 0).
Proof.
  apply/eqP/eqP => [ h | -> ]; last by rewrite /qe_norm /= expr0n /= mulr0 subr0.
  have : x * cj x = 0 by rewrite mul_cj h.
  by move/eqP; rewrite mulf_eq0 cj_eq0 orbb => /eqP.
Qed.

Lemma norm_cj_prod x : `|x| * `|cj x| = qr `|qe_norm x|.
Proof. by rewrite -normrM mul_cj qr_norm. Qed.

(** * 2. The ring of integers  Z[sqrt2] *)

Definition isI (x : RF) : Prop := exists A B : int, x = QE A%:~R B%:~R.

Lemma isI_int (z : int) : isI z%:~R.
Proof. by exists z, 0; rewrite -qr_int. Qed.
Lemma isI_nat n : isI n%:R. Proof. exact: (isI_int n). Qed.
Lemma isI0 : isI 0. Proof. exact: (isI_nat 0). Qed.
Lemma isI1 : isI 1. Proof. exact: (isI_nat 1). Qed.
Lemma isI_sq2 : isI sq2. Proof. by exists 0, 1. Qed.
Lemma isI_add x y : isI x -> isI y -> isI (x + y).
Proof. by move=> [A [B ->]] [C [D ->]]; exists (A + C), (B + D); rewrite RF_addE !intrD. Qed.
Lemma isI_opp x : isI x -> isI (- x).
Proof. by move=> [A [B ->]]; exists (- A), (- B); rewrite RF_oppE !intrN. Qed.
Lemma isI_sub x y : isI x -> isI y -> isI (x - y).
Proof. by move=> hx hy; apply: isI_add hx (isI_opp hy). Qed.
Lemma isI_mul x y : isI x -> isI y -> isI (x * y).
Proof.
  move=> [A [B ->]] [C [D ->]]; exists (A * C + 2 * (B * D)), (A * D + B * C).
  by rewrite RF_mulE !intrD !intrM.
Qed.
Lemma isI_expn x n : isI x -> isI (x ^+ n).
Proof. by move=> h; elim: n => [ | n IH ]; [ exact: isI1 | rewrite exprS; apply: isI_mul ]. Qed.
Lemma isI_cj x : isI x -> isI (cj x).
Proof. by move=> [A [B ->]]; exists A, (- B); rewrite /cj /qe_conj /= intrN. Qed.
Lemma isI_natmul x n : isI x -> isI (x *+ n).
Proof. by move=> h; rewrite -mulr_natr; apply: isI_mul h (isI_nat n). Qed.

(* the norm of an element of Z[sqrt2] is an integer *)
Lemma isI_norm x : isI x -> exists z : int, qe_norm x = z%:~R.
Proof.
  move=> [A [B ->]]; exists (A ^+ 2 - 2 * B ^+ 2).
  by rewrite /qe_norm /= rmorphB rmorphM /= !rmorphXn.
Qed.

Lemma int_norm_ge1 (z : int) : z != 0 -> 1 <= `|z%:~R : rat|.
Proof.
  by move=> nz; rewrite -intr_norm ler1z -gtz0_ge1 normr_gt0.
Qed.

(* |N x| >= 1 for a nonzero element of Z[sqrt2] *)
Lemma isI_normN_ge1 x : isI x -> x != 0 -> 1 <= `|x| * `|cj x|.
Proof.
  move=> hx nx; rewrite norm_cj_prod -qr1 qr_le.
  case: (isI_norm hx) => z ez; rewrite ez; apply: int_norm_ge1.
  apply: contraNneq nx => e; move: ez; rewrite e /= => /eqP; rewrite qe_norm_eq0.
  by move/eqP => ->.
Qed.

(** * 3. Euclid's algorithm in Z[sqrt2] and coprime representatives *)

(* rounding to a nearest integer *)
Definition rnd (r : rat) : rat := (Num.floor (r + 2%:R^-1))%:~R.

Lemma rnd_err (r : rat) : - 2%:R^-1 <= r - rnd r <= 2%:R^-1.
Proof.
  rewrite /rnd; set y := r + 2%:R^-1.
  have h1 := real_floor_le (num_real y).
  have h2 := real_floorD1_gt (num_real y).
  move: h2; rewrite rmorphD /= rmorph1 => h2.
  by apply/andP; split; rewrite /y in h1 h2 *; lra.
Qed.

Definition qrnd (z : RF) : RF := QE (rnd (qre z)) (rnd (qim z)).

Lemma isI_qrnd z : isI (qrnd z).
Proof. by exists (Num.floor (qre z + 2%:R^-1)), (Num.floor (qim z + 2%:R^-1)). Qed.

Lemma qrnd_err z : `|qe_norm (z - qrnd z)| <= 2%:R^-1.
Proof.
  case: z => a b; rewrite /qrnd /qe_norm /=.
  have := rnd_err a; have := rnd_err b.
  set e1 := a - rnd a; set e2 := b - rnd b => /andP [h1 h2] /andP [h3 h4].
  rewrite ler_norml; apply/andP; split; nra.
Qed.

Lemma qe_normM (x y : RF) : qe_norm (x * y) = qe_norm x * qe_norm y.
Proof. exact: qe_norm_mul. Qed.

(* (g, u, w, a', b') with  u a + w b = g,  a = g a',  b = g b' *)
Fixpoint egcd (k : nat) (a b : RF) : RF * RF * RF * RF * RF :=
  match k with
  | 0 => (a, 1, 0, 1, 0)
  | k'.+1 =>
      if b == 0 then (a, 1, 0, 1, 0)
      else let q := qrnd (a / b) in
           match egcd k' b (a - q * b) with
           | (g, u, w, b', r') => (g, w, u - q * w, q * b' + r', b')
           end
  end.

Definition egcd_spec (a b : RF) (r : RF * RF * RF * RF * RF) : Prop :=
  match r with
  | (g, u, w, a', b') =>
      u * a + w * b = g /\ a = g * a' /\ b = g * b' /\
      isI g /\ isI u /\ isI w /\ isI a' /\ isI b'
  end.

Lemma egcd_ok k : forall a b, isI a -> isI b -> `|qe_norm b| <= k%:R -> egcd_spec a b (egcd k a b).
Proof.
  elim: k => [ | k IH ] a b ha hb hk.
  - have eb : b = 0.
    { apply/eqP; rewrite -qe_norm_eq0 -normr_eq0; apply/eqP/le_anti.
      by rewrite hk normr_ge0. }
    rewrite /= eb; do !split; rewrite ?mulr1 ?mulr0 ?mul1r ?mul0r ?addr0 //;
      by [ exact: isI1 | exact: isI0 ].
  - rewrite /=; case: (eqVneq b 0) => [ eb | nb ].
    { rewrite eb /=; do !split; rewrite ?mulr1 ?mulr0 ?mul1r ?mul0r ?addr0 //;
        by [ exact: isI1 | exact: isI0 ]. }
    set q := qrnd (a / b); set r := a - q * b.
    have hq : isI q by exact: isI_qrnd.
    have hr : isI r by apply: isI_sub ha (isI_mul hq hb).
    have er : r = b * (a / b - q) by rewrite mulrBr mulrCA divff // mulr1 /r [q * b]mulrC.
    have hrk : `|qe_norm r| <= k%:R.
    { have e1 : `|qe_norm r| <= `|qe_norm b| * 2%:R^-1.
      { rewrite er qe_normM normrM; apply: ler_wpM2l; first exact: normr_ge0.
        exact: qrnd_err. }
      case: (eqVneq r 0) => [ -> | nr ].
      - have /eqP -> : qe_norm (0 : RF) == 0 by rewrite qe_norm_eq0.
        by rewrite normr0 ler0n.
      - have h1 : 1 <= `|qe_norm r|.
        { case: (isI_norm hr) => z ez; rewrite ez; apply: int_norm_ge1.
          apply: contraNneq nr => e; move: ez; rewrite e /= => /eqP; rewrite qe_norm_eq0.
          by []. }
        move: hk; rewrite -natr1 => hk; lra. }
    have := IH b r hb hr hrk.
    case: (egcd k b r) => [ [ [ [ g u ] w ] b' ] r' ] [ e1 [ e2 [ e3 [ hg [ hu [ hw [ hb' hr' ] ] ] ] ] ] ].
    do !split => //.
    + have ea : a = q * b + r by rewrite /r; ring.
      by rewrite ea -e1; ring.
    + have ea : a = q * b + r by rewrite /r; ring.
      by rewrite ea e2 {1}e3; ring.
    + by apply: isI_sub hu (isI_mul hq hw).
    + by apply: isI_add (isI_mul hq hb') hr'.
Qed.

Definition coprime (a b : RF) : Prop :=
  exists u w, isI u /\ isI w /\ u * a + w * b = 1.

(* the common denominator of the coordinates of x *)
Definition cden (x : RF) : int := denq (qre x) * denq (qim x).

Lemma cden_neq0 x : cden x != 0.
Proof. by rewrite /cden mulf_neq0 ?denq_neq0. Qed.

Lemma isI_cden x : isI (x * (cden x)%:~R).
Proof.
  case: x => a b; rewrite /cden /= -qr_int RF_mulE /= !mulr0 !addr0.
  exists (numq a * denq b), (numq b * denq a).
  by rewrite !intrM !numqE; congr QE; ring.
Qed.

(* a coprime representative of the point  x : 1  of P^1(F) *)
Definition crepx (x : RF) : RF * RF :=
  match egcd (`|cden x| ^ 2)%N (x * (cden x)%:~R) (cden x)%:~R with
  | (g, u, w, a', b') => (a', b')
  end.

Definition crep_spec (x : RF) (v : RF * RF) : Prop :=
  isI v.1 /\ isI v.2 /\ coprime v.1 v.2 /\ v.1 = x * v.2 /\ v.2 != 0.

Lemma crepx_ok x : crep_spec x (crepx x).
Proof.
  have hd : (cden x)%:~R != 0 :> RF by rewrite intr_eq0 cden_neq0.
  have hk : `|qe_norm ((cden x)%:~R : RF)| <= ((`|cden x| ^ 2)%N)%:R.
  { have -> : qe_norm ((cden x)%:~R : RF) = (cden x)%:~R ^+ 2.
    { by rewrite -qr_int /qe_norm /= expr0n /= mulr0 subr0. }
    by rewrite normrX -intr_norm natrX natr_absz. }
  have := egcd_ok (isI_cden x) (isI_int (cden x)) hk.
  rewrite /crepx; case: (egcd _ _ _) => [ [ [ [ g u ] w ] a' ] b' ].
  move=> [ e1 [ e2 [ e3 [ hg [ hu [ hw [ ha' hb' ] ] ] ] ] ] ].
  have ng : g != 0 by apply: contraNneq hd => eg; rewrite e3 eg mul0r.
  have nb' : b' != 0 by apply: contraNneq hd => eb; rewrite e3 eb mulr0.
  do !split => //=.
  - exists u, w; do !split => //; apply: (mulfI ng).
    have E : g * (u * a' + w * b') = u * (g * a') + w * (g * b') by ring.
    by rewrite E -e2 -e3 e1 mulr1.
  - apply: (mulfI ng); rewrite -e2.
    have E : g * (x * b') = x * (g * b') by ring.
    by rewrite E -e3.
Qed.

(** * 4. Heights of representatives *)

Definition mx (a b : RF) : RF := Num.max `|a| `|b|.

(* squared multiplicative height of the representative (a, b) *)
Definition Mh (v : RF * RF) : RF := mx v.1 v.2 * mx (cj v.1) (cj v.2).

Lemma mx_ge0 a b : 0 <= mx a b.
Proof. by rewrite /mx le_max normr_ge0. Qed.

Lemma mx_gel a b : `|a| <= mx a b. Proof. by rewrite /mx le_max lexx. Qed.
Lemma mx_ger a b : `|b| <= mx a b. Proof. by rewrite /mx le_max lexx orbT. Qed.

Lemma mx_le a b c : `|a| <= c -> `|b| <= c -> mx a b <= c.
Proof. by move=> h1 h2; rewrite /mx ge_max h1 h2. Qed.

Lemma mx_cases a b : mx a b = `|a| \/ mx a b = `|b|.
Proof. by rewrite /mx; case: (leP `|a| `|b|) => _; [ right | left ]. Qed.

Lemma Mh_ge0 v : 0 <= Mh v.
Proof. by rewrite /Mh mulr_ge0 ?mx_ge0. Qed.

Lemma mx_scale g a b : mx (g * a) (g * b) = `|g| * mx a b.
Proof. by rewrite /mx !normrM maxr_pMr ?normr_ge0. Qed.

Lemma Mh_scale g a b : Mh (g * a, g * b) = (`|g| * `|cj g|) * Mh (a, b).
Proof. by rewrite /Mh /= !cj_mul !mx_scale; ring. Qed.

Lemma coprime_nz a b : coprime a b -> a != 0 \/ b != 0.
Proof.
  move=> [ u [ w [ _ [ _ e ] ] ] ]; case: (eqVneq a 0) => [ ea | ]; last by left.
  right; apply: contra_eq_neq e => eb; by rewrite ea eb !mulr0 addr0 eq_sym oner_neq0.
Qed.

Lemma Mh_ge1 a b : isI a -> isI b -> (a != 0 \/ b != 0) -> 1 <= Mh (a, b).
Proof.
  move=> ha hb hab; rewrite /Mh /=.
  have h1 : `|a| * `|cj a| <= mx a b * mx (cj a) (cj b).
  { by apply: ler_pM; rewrite ?normr_ge0 ?mx_gel. }
  have h2 : `|b| * `|cj b| <= mx a b * mx (cj a) (cj b).
  { by apply: ler_pM; rewrite ?normr_ge0 ?mx_ger. }
  case: hab => h.
  - exact: le_trans (isI_normN_ge1 ha h) h1.
  - exact: le_trans (isI_normN_ge1 hb h) h2.
Qed.

(* the coprime representative has the least height among the integral
   representatives of the same point *)
Lemma Mh_min a b c d : isI a -> isI b -> (a != 0 \/ b != 0) ->
  coprime c d -> a * d = b * c -> Mh (c, d) <= Mh (a, b).
Proof.
  move=> ha hb hab [ u [ w [ hu [ hw e ] ] ] ] ead.
  set g := u * a + w * b.
  have hg : isI g by apply: isI_add; apply: isI_mul.
  have ea : a = g * c.
  { have E : g * c = a * (u * c + w * d) + w * (b * c - a * d) by rewrite /g; ring.
    by rewrite E e ead subrr mulr0 addr0 mulr1. }
  have eb : b = g * d.
  { have E : g * d = b * (u * c + w * d) + u * (a * d - b * c) by rewrite /g; ring.
    by rewrite E e ead subrr mulr0 addr0 mulr1. }
  have ng : g != 0.
  { case: hab => h; apply: contraNneq h => eg; by rewrite ?ea ?eb eg mul0r. }
  rewrite ea eb Mh_scale; apply: ler_peMl; first exact: Mh_ge0.
  exact: isI_normN_ge1.
Qed.

(** * 5. Comparison with the bit heights of the coordinates *)

Lemma pow2E k : Nat.pow 2 k = (2 ^ k)%N.
Proof. by elim: k => // k IH; rewrite expnS -IH. Qed.

Lemma htb_num (x : rat) : `|(numq x)%:~R : rat| <= 2%:R ^+ htb x.
Proof.
  rewrite -intr_norm -natr_absz -natrX ler_nat.
  apply: leq_trans (Hq_num x) _; rewrite -pow2E; apply/ssrnat.leP; exact: htb_spec.
Qed.

Lemma htb_den (x : rat) : `|(denq x)%:~R : rat| <= 2%:R ^+ htb x.
Proof.
  rewrite -intr_norm -natr_absz -natrX ler_nat.
  apply: leq_trans (Hq_den x) _; rewrite -pow2E; apply/ssrnat.leP; exact: htb_spec.
Qed.

Lemma norm_prod3 (u v w : int) (h1 h2 h3 : nat) :
  `|u%:~R : rat| <= 2%:R ^+ h1 -> `|v%:~R : rat| <= 2%:R ^+ h2 -> `|w%:~R : rat| <= 2%:R ^+ h3 ->
  `|(u * v * w)%:~R : rat| <= 2%:R ^+ (h1 + h2 + h3).
Proof.
  move=> e1 e2 e3; rewrite !intrM !normrM !exprD.
  by apply: ler_pM; rewrite ?mulr_ge0 ?normr_ge0 //; apply: ler_pM; rewrite ?normr_ge0.
Qed.

(* H(x)^4 <= 9 * 4^(htb x0 + htb x1 + htb x2)  for  x = (x0 + x1 sqrt2) / x2 *)
Theorem Mh_htb (x0 x1 x2 : rat) : x2 != 0 ->
  Mh (crepx (QE x0 x1 / qr x2)) <= qr (9%:R * 4%:R ^+ (htb x0 + htb x1 + htb x2)).
Proof.
  move=> nx2.
  set x : RF := QE x0 x1 / qr x2.
  set p0 := numq x0; set p1 := numq x1; set p2 := numq x2.
  set q0 := denq x0; set q1 := denq x1; set q2 := denq x2.
  set A := p0 * q1 * q2; set B := p1 * q0 * q2; set C := p2 * q0 * q1.
  set al : RF := QE A%:~R B%:~R; set be : RF := C%:~R.
  have np2 : p2 != 0 by rewrite numq_eq0.
  have nq (y : rat) : (denq y)%:~R != 0 :> rat by rewrite intr_eq0 denq_neq0.
  have nbe : be != 0.
  { by rewrite /be intr_eq0 /C !mulf_neq0 ?denq_neq0. }
  have nqx2 : qr x2 != 0 by apply: contraNneq nx2 => /qr_inj ->.
  have eal : al = x * be.
  { rewrite /x /al /be -qr_int.
    apply: (mulIf nqx2); rewrite mulrAC divfK //.
    rewrite !RF_mulE /= /A /B /C !intrM.
    have e0 := divq_num_den x0; have e1 := divq_num_den x1; have e2 := divq_num_den x2.
    rewrite -/p0 -/p1 -/p2 -/q0 -/q1 -/q2 in e0 e1 e2.
    have n0 := nq x0; have n1 := nq x1; have n2 := nq x2.
    rewrite -/q0 -/q1 -/q2 in n0 n1 n2.
    rewrite -e0 -e1 -e2; congr QE; field; by rewrite n0 n1 n2. }
  have [ hc [ hd [ hcop [ ec nd ] ] ] ] := crepx_ok x.
  have hal : isI al by exists A, B.
  have hbe : isI be by rewrite /be; exact: isI_int.
  apply: le_trans (Mh_min hal hbe (or_intror nbe) hcop _) _.
  { by rewrite eal ec; ring. }
  set H := (htb x0 + htb x1 + htb x2)%N.
  have bA : `|A%:~R : rat| <= 2%:R ^+ H by apply: norm_prod3; rewrite ?htb_num ?htb_den.
  have bB : `|B%:~R : rat| <= 2%:R ^+ H.
  { rewrite /H [(htb x0 + htb x1)%N]addnC.
    by apply: norm_prod3; rewrite ?htb_num ?htb_den. }
  have bC : `|C%:~R : rat| <= 2%:R ^+ H.
  { rewrite /H addnC addnA.
    by apply: norm_prod3; rewrite ?htb_num ?htb_den. }
  have bm : mx al be <= qr (3%:R * 2%:R ^+ H).
  { apply: mx_le.
    - apply: le_trans (norm_QE_le _ _) _; rewrite qr_le; lra.
    - rewrite /be -qr_int qr_norm qr_le; have := normr_ge0 (A%:~R : rat); lra. }
  have bm' : mx (cj al) (cj be) <= qr (3%:R * 2%:R ^+ H).
  { apply: mx_le.
    - rewrite /cj /qe_conj /= -mulrNz.
      apply: le_trans (norm_QE_le _ _) _; rewrite qr_le mulrNz normrN; lra.
    - rewrite /be -qr_int cj_qr qr_norm qr_le; have := normr_ge0 (A%:~R : rat); lra. }
  rewrite /Mh /=.
  have -> : (9%:R * 4%:R ^+ H : rat) = (3%:R * 2%:R ^+ H) * (3%:R * 2%:R ^+ H).
  { by rewrite mulrACA -exprMn -!natrM. }
  rewrite qr_mul; apply: ler_pM; rewrite ?mx_ge0 //.
Qed.

(** * 6. Northcott: points of bounded height lie in an explicit finite list *)

Definition rngX (X : nat) : seq rat := [seq (i%:Z - X%:Z)%:~R | i <- iota 0 (2 * X).+1].

Definition candX (X : nat) : seq RF :=
  [seq QE (ab.1 / n) (ab.2 / n) | ab <- [seq (a, b) | a <- rngX X, b <- rngX X], n <- rngX X].

Lemma mem_rngX (z : int) (X : nat) : `|z%:~R : rat| <= X%:R -> z%:~R \in rngX X.
Proof.
  rewrite -intr_norm -natr_absz ler_nat => hz.
  have h : `|z|%R <= X%:Z :> int by rewrite -abszE lez_nat.
  move: h; rewrite ler_norml => /andP [ h1 h2 ].
  have hzX : 0 <= z + X%:Z by rewrite -[X%:Z]opprK subr_ge0.
  apply/mapP; exists (absz (z + X%:Z)); last by rewrite gez0_abs // addrK.
  rewrite mem_iota add0n ltnS.
  have h := absz_triangle z X%:Z; apply: leq_trans h _.
  by rewrite absz_nat mul2n -addnn leq_add2r.
Qed.

Lemma Mh_bounded_mem (x : RF) (X : nat) : Mh (crepx x) <= X%:R -> x \in candX X.
Proof.
  have [ hc [ hd [ hcop [ ec nd ] ] ] ] := crepx_ok x.
  case: (crepx x) hc hd hcop ec nd => c d /= hc hd hcop ec nd hM.
  set z := c * cj d.
  have hz : isI z by apply: isI_mul hc (isI_cj hd).
  case: hz => A [ B ez ].
  case: (isI_norm hd) => N eN.
  have nN : N != 0.
  { apply: contraNneq nd => e; move: eN; rewrite e /= => /eqP; by rewrite qe_norm_eq0. }
  have nNr : (N%:~R : rat) != 0 by rewrite intr_eq0.
  (* x = z / N *)
  have ex : x = QE (A%:~R / N%:~R) (B%:~R / N%:~R).
  { have edd : d * cj d = qr N%:~R by rewrite mul_cj eN.
    have nq : qr N%:~R != 0 by apply: contraNneq nNr => /qr_inj ->.
    have e1 : QE (A%:~R / N%:~R) (B%:~R / N%:~R) * qr N%:~R = z.
    { rewrite ez /qr RF_mulE /=; congr QE; field; exact: nNr. }
    have e2 : x * qr N%:~R = z by rewrite -edd /z ec; ring.
    by apply: (mulIf nq); rewrite e1 e2. }
  have bz : `|z| <= Mh (c, d).
  { rewrite /z normrM /Mh /=; apply: ler_pM; rewrite ?normr_ge0 ?mx_gel ?mx_ger //. }
  have bz' : `|cj z| <= Mh (c, d).
  { rewrite /z cj_mul cjK normrM /Mh /= mulrC; apply: ler_pM; rewrite ?normr_ge0 ?mx_gel ?mx_ger //. }
  have bN : `|qr N%:~R| <= Mh (c, d).
  { rewrite -eN -mul_cj normrM /Mh /=; apply: ler_pM; rewrite ?normr_ge0 ?mx_ger //. }
  have eA : z + cj z = qr (2%:R * A%:~R).
  { by rewrite ez /cj /qe_conj RF_addE /qr; congr QE; ring. }
  have eB : z - cj z = qr (2%:R * B%:~R) * sq2.
  { by rewrite ez /cj /qe_conj /= RF_oppE RF_addE /qr /sq2 RF_mulE; congr QE; ring. }
  have bA : `|qr A%:~R| <= X%:R.
  { have h : `|z + cj z| <= Mh (c, d) + Mh (c, d) by apply: le_trans (ler_normD _ _) _; lra.
    move: h; rewrite eA qr_mul normrM qr_nat normr_nat; lra. }
  have bB : `|qr B%:~R| <= X%:R.
  { have h : `|z - cj z| <= Mh (c, d) + Mh (c, d).
    { apply: le_trans (ler_normB _ _) _; lra. }
    move: h; rewrite eB !normrM qr_mul normrM qr_nat normr_nat (ger0_norm sq2_ge0) => h.
    have h1 := sq2_ge1; have h2 := normr_ge0 (qr B%:~R); nra. }
  have bN' : `|qr N%:~R| <= X%:R by lra.
  have cv (r : rat) : `|qr r| <= X%:R -> `|r| <= X%:R by rewrite qr_norm -qr_nat qr_le.
  rewrite ex /candX; apply: (allpairs_f (fun ab n => QE (ab.1 / n) (ab.2 / n)) (x := (A%:~R, B%:~R))).
  - by apply: (allpairs_f pair); apply: mem_rngX; apply: cv.
  - by apply: mem_rngX; apply: cv.
Qed.
