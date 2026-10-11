(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The two core height inequalities of HeightLower.v (PLAN P13), stated
   for representatives in Z[sqrt2] (NFHeight.v):
   - [dup_core]: if (al, be) and (ga, de) are coprime representatives of
     x and of x(2T) = Nd(al,be) / Dd(al,be), then
       Mh(al, be)^4 <= KD^2 Mh(ga, de);
   - [par_core]: if (a_i, b_i) represent x_i (x1 <> x2) and (g_i, d_i)
     represent the two roots s, t of
       (x1 - x2)^2 X^2 - 2 (x1 + x2)(x1 x2 + aE) X + (x1 x2 - aE)^2,
     then Mh(g1, d1) Mh(g2, d2) <= KU^2 Mh(a1, b1)^2 Mh(a2, b2)^2.
   See the header of HeightLower.v for the mathematics. The implementation
   note of HeightArch.v applies.

   No axioms. *)

From HB Require Import structures.
From mathcomp Require Import boot order algebra.

From Undecidability.H10.Rational Require Import FixedData GroupLaw NFHeight HeightArch.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.

Local Open Scope ring_scope.

(** * 1. Conjugation of the forms *)

Lemma cj_Nd a X Z : cj (Nd a X Z) = Nd (cj a) (cj X) (cj Z).
Proof. rewrite /Nd !cj_expn cj_sub cj_mul !cj_expn; reflexivity. Qed.

Lemma cj_Dd a X Z : cj (Dd a X Z) = Dd (cj a) (cj X) (cj Z).
Proof. rewrite /Dd !cj_mul cj_nat cj_add cj_mul !cj_expn; reflexivity. Qed.

Lemma isI_Nd a X Z : isI a -> isI X -> isI Z -> isI (Nd a X Z).
Proof.
  move=> ha hX hZ; rewrite /Nd; apply: isI_expn; apply: isI_sub; first exact: isI_expn.
  by apply: isI_mul ha (isI_expn _ hZ).
Qed.

Lemma isI_Dd a X Z : isI a -> isI X -> isI Z -> isI (Dd a X Z).
Proof.
  move=> ha hX hZ; rewrite /Dd; apply: isI_mul; last first.
  - by apply: isI_add; [ exact: isI_expn | apply: isI_mul ha (isI_expn _ hZ) ].
  - by apply: isI_mul hZ; apply: isI_mul hX; exact: isI_nat.
Qed.

Lemma isI_F1 a X Z : isI a -> isI X -> isI Z -> isI (F1 a X Z).
Proof.
  move=> ha hX hZ; rewrite /F1; apply: isI_add; apply: isI_mul; try exact: isI_nat.
  - exact: isI_expn.
  - by apply: isI_mul; [ apply: isI_mul | exact: isI_expn ].
Qed.

Lemma isI_G1 a X Z : isI a -> isI X -> isI Z -> isI (G1 a X Z).
Proof.
  move=> ha hX hZ; rewrite /G1; apply: isI_sub; apply: isI_mul; try exact: isI_nat.
  - by apply: isI_mul hZ; apply: isI_mul ha (isI_expn _ hX).
  - by apply: isI_mul; exact: isI_expn.
Qed.

Lemma isI_F2 a X Z : isI a -> isI X -> isI Z -> isI (F2 a X Z).
Proof.
  move=> ha hX hZ; rewrite /F2; apply: isI_add; apply: isI_mul; try exact: isI_nat.
  - by apply: isI_mul ha (isI_expn _ hZ).
  - by apply: isI_mul (isI_expn _ hX) hZ.
Qed.

Lemma isI_G2 a X Z : isI a -> isI X -> isI Z -> isI (G2 a X Z).
Proof.
  move=> ha hX hZ; rewrite /G2; apply: isI_sub; apply: isI_mul; try exact: isI_nat.
  - by apply: isI_mul; [ apply: isI_mul | exact: isI_expn ].
  - exact: isI_expn.
Qed.

(** * 2. Divisibility: z a^n and z b^n multiples of g, (a, b) coprime ==> z multiple of g *)

Definition dvdI (g z : RF) : Prop := exists h, isI h /\ z = g * h.

Lemma dvdI_mulr g z c : isI c -> dvdI g z -> dvdI g (z * c).
Proof. move=> hc [ h [ hh -> ] ]; exists (h * c); split; [ exact: isI_mul | ring ]. Qed.

Lemma dvdI_add g z1 z2 : dvdI g z1 -> dvdI g z2 -> dvdI g (z1 + z2).
Proof.
  move=> [ h1 [ hh1 -> ] ] [ h2 [ hh2 -> ] ]; exists (h1 + h2); split; [ exact: isI_add | ring ].
Qed.

Lemma coprime_pow_dvd (a b g z : RF) (n : nat) : isI a -> isI b -> coprime a b ->
  dvdI g (z * a ^+ n) -> dvdI g (z * b ^+ n) -> dvdI g z.
Proof.
  move=> ha hb [ u [ w [ hu [ hw e ] ] ] ] hA hB.
  (* Q i j := dvdI g (z * a^i * b^j), for i + j + k = 2 n *)
  have Q : forall k i j, (i + j + k = n + n)%N -> dvdI g (z * a ^+ i * b ^+ j).
  { elim=> [ | k IH ] i j hij.
    - rewrite addn0 in hij.
      case: (leqP n i) => hi.
      + have -> : z * a ^+ i * b ^+ j = z * a ^+ n * (a ^+ (i - n) * b ^+ j).
        { rewrite -[in LHS](subnKC hi) exprD; ring. }
        by apply: dvdI_mulr hA; apply: isI_mul; apply: isI_expn.
      + have hj : (n <= j)%N.
        { rewrite leqNgt; apply/negP => hj.
          have h1 : (i + j < n + j)%N by rewrite ltn_add2r.
          have h2 : (n + j <= n + n)%N by rewrite leq_add2l ltnW.
          by move: (leq_trans h1 h2); rewrite hij ltnn. }
        have -> : z * a ^+ i * b ^+ j = z * b ^+ n * (a ^+ i * b ^+ (j - n)).
        { rewrite -[in LHS](subnKC hj) exprD; ring. }
        by apply: dvdI_mulr hB; apply: isI_mul; apply: isI_expn.
    - have h1 := IH i.+1 j; have h2 := IH i j.+1.
      have e1 : (i.+1 + j + k)%N = (n + n)%N by rewrite -hij addSn addnS addSn.
      have e2 : (i + j.+1 + k)%N = (n + n)%N by rewrite -hij addnS !addSn addnS.
      have E : z * a ^+ i * b ^+ j = (z * a ^+ i.+1 * b ^+ j) * u + (z * a ^+ i * b ^+ j.+1) * w.
      { rewrite -[LHS]mulr1 -e !exprS; ring. }
      rewrite E; apply: dvdI_add; apply: dvdI_mulr; [ exact: hu | exact: h1 e1 | exact: hw | exact: h2 e2 ]. }
  have := Q (n + n)%N 0%N 0%N (add0n _); rewrite !expr0 !mulr1; exact.
Qed.

(** * 3. The duplication inequality for representatives *)

Lemma R16_neq0 : (16%:R * aF ^+ 3 : RF) != 0.
Proof.
  apply: mulf_neq0; last exact: (expf_neq0 3 aF_neq0).
  by rewrite pnatr_eq0.
Qed.

Lemma cj_R16 : cj (16%:R * aF ^+ 3 : RF) = 16%:R * cj aF ^+ 3.
Proof. rewrite cj_mul cj_nat cj_expn; reflexivity. Qed.

Lemma Mh_split (a b : RF) : Mh (a, b) = mx a b * mx (cj a) (cj b).
Proof. reflexivity. Qed.

Lemma dup_core (al be ga de : RF) : isI al -> isI be -> coprime al be ->
  isI ga -> isI de -> coprime ga de ->
  ga * Dd aF al be = de * Nd aF al be -> Mh (al, be) ^+ 4 <= KD ^+ 2 * Mh (ga, de).
Proof.
  move=> hal hbe cab hga hde [ u [ w [ hu [ hw e ] ] ] ] ecr.
  have hA := isI_aF.
  (* the common factor g *)
  have [ g [ hg [ eN eD ] ] ] : exists g, isI g /\ Nd aF al be = g * ga /\ Dd aF al be = g * de.
  { exists (u * Nd aF al be + w * Dd aF al be); split.
    { by apply: isI_add; apply: isI_mul => //; [ apply: isI_Nd | apply: isI_Dd ]. }
    split.
    - have E : (u * Nd aF al be + w * Dd aF al be) * ga
             = Nd aF al be * (u * ga + w * de) + w * (ga * Dd aF al be - de * Nd aF al be) by ring.
      rewrite E e ecr subrr mulr0 addr0 mulr1; reflexivity.
    - have E : (u * Nd aF al be + w * Dd aF al be) * de
             = Dd aF al be * (u * ga + w * de) + u * (de * Nd aF al be - ga * Dd aF al be) by ring.
      rewrite E e ecr subrr mulr0 addr0 mulr1; reflexivity. }
  (* g divides R = 16 aF^3 *)
  have hR1 : dvdI g (16%:R * aF ^+ 3 * al ^+ 7).
  { exists (aF ^+ 3 * (F1 aF al be * ga + G1 aF al be * de)); split.
    { apply: isI_mul; first exact: isI_expn.
      by apply: isI_add; apply: isI_mul => //; [ apply: isI_F1 | apply: isI_G1 ]. }
    have E : g * (aF ^+ 3 * (F1 aF al be * ga + G1 aF al be * de))
           = aF ^+ 3 * (F1 aF al be * (g * ga) + G1 aF al be * (g * de)) by ring.
    rewrite E -eN -eD bezout1; ring. }
  have hR2 : dvdI g (16%:R * aF ^+ 3 * be ^+ 7).
  { exists (F2 aF al be * ga + G2 aF al be * de); split.
    { by apply: isI_add; apply: isI_mul => //; [ apply: isI_F2 | apply: isI_G2 ]. }
    have E : g * (F2 aF al be * ga + G2 aF al be * de)
           = F2 aF al be * (g * ga) + G2 aF al be * (g * de) by ring.
    rewrite E -eN -eD bezout2; reflexivity. }
  have [ h [ hh eR ] ] := coprime_pow_dvd hal hbe cab hR1 hR2.
  have nR := R16_neq0.
  have ng : g != 0 by apply: contraNneq nR => eg; rewrite eR eg mul0r.
  have nh : h != 0 by apply: contraNneq nR => eh; rewrite eR eh mulr0.
  (* the two archimedean estimates *)
  have A1 := D_arch al be aF_bound.
  rewrite eN eD mx_scale in A1.
  have A2 := D_arch (cj al) (cj be) aF_cj_bound.
  rewrite -cj_Nd -cj_Dd eN eD (cj_mul g ga) (cj_mul g de) mx_scale in A2.
  have eRc : 16%:R * cj aF ^+ 3 = cj g * cj h.
  { have := congr1 cj eR; rewrite cj_R16 cj_mul; exact. }
  have hG1 := normr_ge0 g; have hG2 := normr_ge0 (cj g).
  have hm1 := mx_ge0 ga de; have hm2 := mx_ge0 (cj ga) (cj de).
  have hKD := le_trans ler01 KD_ge1.
  have P := ler_pM (mulr_ge0 (normr_ge0 _) (exprn_ge0 4 (mx_ge0 al be)))
                   (mulr_ge0 (normr_ge0 _) (exprn_ge0 4 (mx_ge0 (cj al) (cj be)))) A1 A2.
  have eL : `|16%:R * aF ^+ 3| * mx al be ^+ 4 * (`|16%:R * cj aF ^+ 3| * mx (cj al) (cj be) ^+ 4)
            = (`|g| * `|cj g|) * (`|h| * `|cj h|) * Mh (al, be) ^+ 4.
  { rewrite eR eRc (normrM g h) (normrM (cj g) (cj h)) Mh_split exprMn; ring. }
  have eRr : KD * (`|g| * mx ga de) * (KD * (`|cj g| * mx (cj ga) (cj de)))
            = (`|g| * `|cj g|) * (KD ^+ 2 * Mh (ga, de)).
  { rewrite Mh_split; ring. }
  have P2 : (`|g| * `|cj g|) * ((`|h| * `|cj h|) * Mh (al, be) ^+ 4)
            <= (`|g| * `|cj g|) * (KD ^+ 2 * Mh (ga, de)).
  { rewrite mulrA -eL -eRr; exact: P. }
  have pG : 0 < `|g| * `|cj g|.
  { apply: mulr_gt0; rewrite normr_gt0 //; by rewrite cj_eq0. }
  rewrite (ler_pM2l pG) in P2.
  have H1 := isI_normN_ge1 hh nh.
  have hM4 := exprn_ge0 4 (Mh_ge0 (al, be)).
  apply: le_trans P2; exact: (ler_peMl hM4 H1).
Qed.

(** * 4. The upper parallelogram inequality for representatives *)

Ltac isI_auto :=
  repeat first [ exact: isI_nat | exact: isI_aF | apply: isI_expn | apply: isI_cj
               | apply: isI_sub | apply: isI_add | apply: isI_opp | apply: isI_mul | assumption ].

Lemma par_core (x1 x2 s t : RF) : x1 != x2 ->
  (x1 - x2) ^+ 2 * (s + t) = 2%:R * (x1 + x2) * (x1 * x2 + aF) ->
  (x1 - x2) ^+ 2 * (s * t) = (x1 * x2 - aF) ^+ 2 ->
  Mh (crepx s) * Mh (crepx t) <= KU ^+ 2 * (Mh (crepx x1) ^+ 2 * Mh (crepx x2) ^+ 2).
Proof.
  move=> nx hst hpt.
  have := crepx_ok x1; case: (crepx x1) => a1 b1; rewrite /crep_spec /=; move=> [ ha1 [ hb1 [ cop1 [ ea1 nb1 ] ] ] ].
  have := crepx_ok x2; case: (crepx x2) => a2 b2; rewrite /crep_spec /=; move=> [ ha2 [ hb2 [ cop2 [ ea2 nb2 ] ] ] ].
  have := crepx_ok s; case: (crepx s) => g1 d1; rewrite /crep_spec /=; move=> [ hg1 [ hd1 [ [ p1 [ q1 [ hp1 [ hq1 e1 ] ] ] ] [ eg1 nd1 ] ] ] ].
  have := crepx_ok t; case: (crepx t) => g2 d2; rewrite /crep_spec /=; move=> [ hg2 [ hd2 [ [ p2 [ q2 [ hp2 [ hq2 e2 ] ] ] ] [ eg2 nd2 ] ] ] ].
  move: ea1 ea2 eg1 eg2 => ea1 ea2 eg1 eg2.
  have nc0 : d1 * d2 != 0 := mulf_neq0 nd1 nd2.
  have [ mu Emu ] : exists mu, mu = (a1 * b2 - a2 * b1) ^+ 2 / (d1 * d2) by eexists.
  have E0 : (a1 * b2 - a2 * b1) ^+ 2 = mu * (d1 * d2).
  { rewrite Emu (divfK nc0); try reflexivity. }
  have Ew : (a1 * b2 - a2 * b1) ^+ 2 = (b1 * b2) ^+ 2 * (x1 - x2) ^+ 2.
  { rewrite ea1 ea2; ring. }
  have E1 : 2%:R * (a1 * b2 + a2 * b1) * (a1 * a2 + aF * (b1 * b2)) = mu * (g1 * d2 + g2 * d1).
  { have F : mu * (g1 * d2 + g2 * d1) = mu * (d1 * d2) * (s + t) by rewrite eg1 eg2; ring.
    rewrite F -E0 Ew.
    have G : (b1 * b2) ^+ 2 * (x1 - x2) ^+ 2 * (s + t) = (b1 * b2) ^+ 2 * ((x1 - x2) ^+ 2 * (s + t)).
    { ring. }
    rewrite G hst ea1 ea2; ring. }
  have E2 : (a1 * a2 - aF * (b1 * b2)) ^+ 2 = mu * (g1 * g2).
  { have F : mu * (g1 * g2) = mu * (d1 * d2) * (s * t) by rewrite eg1 eg2; ring.
    rewrite F -E0 Ew.
    have G : (b1 * b2) ^+ 2 * (x1 - x2) ^+ 2 * (s * t) = (b1 * b2) ^+ 2 * ((x1 - x2) ^+ 2 * (s * t)).
    { ring. }
    rewrite G hpt ea1 ea2; ring. }
  (* mu is in Z[sqrt2] *)
  have hmu : isI mu.
  { pose w0 := (a1 * b2 - a2 * b1) ^+ 2.
    pose w1 := 2%:R * (a1 * b2 + a2 * b1) * (a1 * a2 + aF * (b1 * b2)).
    pose w2 := (a1 * a2 - aF * (b1 * b2)) ^+ 2.
    have M : mu = (p1 * p2 * (g1 * g2) + q1 * q2 * (d1 * d2)) * (p1 * p2 * w2 + q1 * q2 * w0)
                + 2%:R * (p1 * q2 * (g1 * d2) + q1 * p2 * (g2 * d1)) * (p1 * p2 * w2 + q1 * q2 * w0)
                + (p1 * q2) ^+ 2 * (g1 * d2 * w1 - d1 * d2 * w2)
                + 2%:R * (p1 * q2) * (q1 * p2) * (d1 * d2) * w2
                + (q1 * p2) ^+ 2 * (g2 * d1 * w1 - d1 * d2 * w2).
    { rewrite /w0 /w1 /w2 E0 E1 E2.
      have H : mu = mu * ((p1 * g1 + q1 * d1) * (p2 * g2 + q2 * d2)) ^+ 2.
      { rewrite e1 e2 mul1r expr1n mulr1; reflexivity. }
      rewrite {1}H; ring. }
    rewrite M /w0 /w1 /w2; isI_auto. }
  have nmu : mu != 0.
  { apply: contraNneq nx => em.
    have : (b1 * b2) ^+ 2 * (x1 - x2) ^+ 2 = 0 by rewrite -Ew E0 em mul0r.
    move/eqP; rewrite mulf_eq0 => /orP [].
    - by rewrite expf_eq0 /= mulf_eq0 (negbTE nb1) (negbTE nb2).
    - by rewrite expf_eq0 /= subr_eq0. }
  (* the two archimedean estimates *)
  have U1 := U_arch aF_bound E0 E1 E2.
  have E0' := congr1 cj E0; have E1' := congr1 cj E1; have E2' := congr1 cj E2.
  rewrite !cj_expn !cj_sub !cj_mul in E0'.
  rewrite !cj_mul (cj_nat 2) !cj_add !cj_mul in E1'.
  rewrite !cj_expn !cj_sub !cj_mul in E2'.
  have U2 := U_arch aF_cj_bound E0' E1' E2'.
  have P := ler_pM (mulr_ge0 (normr_ge0 _) (mulr_ge0 (mx_ge0 _ _) (mx_ge0 _ _)))
                   (mulr_ge0 (normr_ge0 _) (mulr_ge0 (mx_ge0 _ _) (mx_ge0 _ _))) U1 U2.
  have eL : `|mu| * (mx g1 d1 * mx g2 d2) * (`|cj mu| * (mx (cj g1) (cj d1) * mx (cj g2) (cj d2)))
            = (`|mu| * `|cj mu|) * (Mh (g1, d1) * Mh (g2, d2)).
  { rewrite !Mh_split; ring. }
  have eR : KU * (mx a1 b1 * mx a2 b2) ^+ 2 * (KU * (mx (cj a1) (cj b1) * mx (cj a2) (cj b2)) ^+ 2)
            = KU ^+ 2 * (Mh (a1, b1) ^+ 2 * Mh (a2, b2) ^+ 2).
  { rewrite !Mh_split; ring. }
  have P2 : (`|mu| * `|cj mu|) * (Mh (g1, d1) * Mh (g2, d2))
            <= KU ^+ 2 * (Mh (a1, b1) ^+ 2 * Mh (a2, b2) ^+ 2).
  { rewrite -eL -eR; exact: P. }
  have H1 := isI_normN_ge1 hmu nmu.
  have h0 := mulr_ge0 (Mh_ge0 (g1, d1)) (Mh_ge0 (g2, d2)).
  apply: le_trans P2; exact: (ler_peMl h0 H1).
Qed.
