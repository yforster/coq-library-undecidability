(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The canonical-height lower bound O_HL (PLAN P13, Phase 2D;
   02-reduction.tex eq. red:elliptic-lower), without real numbers and
   without the canonical height.

   SETTING. E : y^2 = x^3 + aE x over F = Q(sqrt2). For a point T we use
   the height  Ht T := Mh (crepP T)  of NFHeight.v: for T = (x, y) it is
   max(|a|,|b|) max(|a'|,|b'|) for the coprime representative x = a / b in
   Z[sqrt2], and Ht O = 1 (O |-> [1 : 0]). This is H_F(x) = H(x)^2, H the
   absolute multiplicative Weil height. All heights are elements of the
   real field [RF] (NFHeight.v); only the final statement is in bits.

   ROUTE (all inequalities multiplicative, constants explicit in RF):
   (D)  duplication lower bound   Ht T ^ 4 <= KD^2 Ht (2T).
        x(2T) = Nd(a,b) / Dd(a,b),  Nd = (a^2 - aE b^2)^2,
        Dd = 4 a b (a^2 + aE b^2), and the explicit Bezout identities
          F1 Nd + G1 Dd = 16 a^7,   F2 Nd + G2 Dd = 16 aE^3 b^7
        (resultant R = 16 aE^3) give at each real embedding
        |R| max(|a|,|b|)^4 <= KD max(|Nd|,|Dd|); the common factor g of
        (Nd, Dd) over the coprime representative of x(2T) divides R
        (using 1 = (u a + w b)^13 = a^7 P1 + b^7 P2), so |N g| <= |N R|.
   (U)  upper parallelogram   Ht(T1+T2) Ht(T1-T2) <= KU^2 Ht T1^2 Ht T2^2
        for x(T1) <> x(T2): x(T1 +- T2) are the roots of
          w0 X^2 - w1 X + w2,  w0 = (a1 b2 - a2 b1)^2,
          w1 = 2 (a1 b2 + a2 b1)(a1 a2 + aE b1 b2),  w2 = (a1 a2 - aE b1 b2)^2,
        so (w0, w1, w2) = mu (d1 d2, g1 d2 + g2 d1, g1 g2) with mu in
        Z[sqrt2] (explicit Bezout combination, Gauss's lemma), mu <> 0,
        and the elementary inequality
          max(|g1|,|d1|) max(|g2|,|d2|) <= |d1 d2| + |g1 d2 + g2 d1| + |g1 g2|.
   (L)  lower parallelogram, from (U) applied to (T1+T2, T1-T2) and (D):
          (Ht T1 Ht T2)^4 <= K (Ht(T1+T2) Ht(T1-T2))^2,  K = KD^4 KU^2.
   (C)  convexity. For a multiple P' = m P0 with Ht(P')^4 >= 4 K, the
        sequence g(n) = Ht(n P')^2 satisfies g(n+1) g(n-1) >= 4 g(n)^2,
        hence g(n+1) >= 4^n g(n) and g(n) >= 2^(n(n-1)).
   (N)  Such an m exists: by Northcott (NFHeight.v) and nontorsion, the
        heights of the multiples of P0 are unbounded.
   (R)  For N = n m + r (0 <= r < m), (U) with (N P0, r P0) gives
        Ht(N P0)^4 * KU^4 B^4 >= 2^(n(n-1)),  B = sum_(r < m) Ht(r P0).
   (H)  Ht(x) <= 9 * 4^(htb x0 + htb x1 + htb x2) for x = (x0 + x1 sqrt2)/x2
        (NFHeight.Mh_htb) turns this into  n^2 <= Nh (htb x0 + htb x1 +
        htb x2 + Ch)  with  Nh = 32 m^2, Ch = 3 + k, where 2^k bounds
        KU^4 B^4 (and m0 = fd_m D is absorbed since |n| <= |n m0|).

   RESULT. For every D satisfying the nontorsion hypothesis E2 (the field
   of StdHyps; it also gives that P0 lies on the curve):
   - [O_HL_explicit]: the field [O_HL] of OrdHyps holds with the explicit
     constants [HL_Nh D = 32 m^2], [HL_Ch D = k + 3], where m = [HL_m D] is
     the first i in 1..L+1 (L the size of the Northcott list for the bound
     4 K) with Ht(i P0) > 4 K, and k = [RFb] (KU^4 B^4); 0 < HL_Nh D;
   - [O_HL_thm]: the same with "exists Nh Ch";
   - [O_HL_field]: the literal field O_HL for D with fd_Nh D = HL_Nh D and
     fd_Ch D = HL_Ch D;
   - [HL_P0]: HL_Nh, HL_Ch depend only on fd_P0 D (so they can be used to
     define the fields fd_Nh, fd_Ch of a FixedData with a given P0).
   The constants are closed terms but are not meant to be evaluated (the
   comparisons in [RF] go through algC).

   Files: NFHeight.v (heights on F, Euclid in Z[sqrt2], Northcott),
   HeightArch.v (archimedean estimates), HeightCore.v (the inequalities
   for representatives), this file (points, convexity, O_HL).

   No axioms. *)

From Stdlib Require Import Lia.

From HB Require Import structures.
From mathcomp Require Import boot order algebra.

From Undecidability.H10.Rational Require Import FixedData GroupLaw NFHeight HeightArch HeightCore.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.

Local Open Scope ring_scope.

(** * 1. The chord-tangent law in coordinates of RF *)

(* the curve equation with the operations of RF *)
Lemma on_curveE (x y : RF) : on_curve (x, y) <-> y * y = x ^+ 3 + aF * x.
Proof. rewrite aFE; split => h; exact: h. Qed.

Lemma two_neq0 : (2%:R : RF) != 0. Proof. by rewrite pnatr_eq0. Qed.

Lemma y_opp_eq (y : RF) : (y == - y) = (y == 0).
Proof.
  apply/eqP/eqP => [ e | -> ]; last by rewrite oppr0.
  have : 2%:R * y = 0 by rewrite mulr_natl mulr2n {1}e addNr.
  move/eqP; rewrite mulf_eq0 (negbTE two_neq0) /=; move/eqP; exact.
Qed.

Definition dblx (x y : RF) : RF := ((3%:R * x ^+ 2 + aF) / (2%:R * y)) ^+ 2 - 2%:R * x.
Definition dbly (x y : RF) : RF :=
  (3%:R * x ^+ 2 + aF) / (2%:R * y) * (x - dblx x y) - y.
Definition chx (x1 y1 x2 y2 : RF) : RF := ((y2 - y1) / (x2 - x1)) ^+ 2 - x1 - x2.
Definition chy (x1 y1 x2 y2 : RF) : RF := (y2 - y1) / (x2 - x1) * (x1 - chx x1 y1 x2 y2) - y1.

Lemma ec_dbl0 (x y : RF) : y = 0 -> ec_add (Some (x, y)) (Some (x, y)) = None.
Proof.
  move=> ey; have h : (y == - y) = true by rewrite y_opp_eq ey eqxx.
  rewrite /ec_add eqxx h; reflexivity.
Qed.

Lemma ec_dbl (x y : RF) : y != 0 ->
  ec_add (Some (x, y)) (Some (x, y)) = Some (dblx x y, dbly x y).
Proof.
  move=> ny; have h : (y == - y) = false by rewrite y_opp_eq (negbTE ny).
  rewrite /ec_add eqxx h /dbly /dblx aFE; reflexivity.
Qed.

Lemma ec_ch (x1 y1 x2 y2 : RF) : x1 != x2 ->
  ec_add (Some (x1, y1)) (Some (x2, y2)) = Some (chx x1 y1 x2 y2, chy x1 y1 x2 y2).
Proof.
  move=> nx; have h : (x1 == x2) = false by exact: negbTE nx.
  rewrite /ec_add h /chy /chx; reflexivity.
Qed.

(** * 2. The height of a point *)

Definition crepP (P : pt rat) : RF * RF := if P is Some (x, _) then crepx x else (1, 0).

Definition Ht (P : pt rat) : RF := Mh (crepP P).

Lemma crepP_Some (x y : RF) : crepP (Some (x, y)) = crepx x. Proof. reflexivity. Qed.
Lemma crepP_None : crepP None = (1, 0). Proof. reflexivity. Qed.

Lemma Ht_None : Ht None = 1.
Proof.
  rewrite /Ht /crepP Mh_split /= cj1 cj0 /mx normr1 normr0 (max_l ler01) mulr1.
  reflexivity.
Qed.

Lemma crepP_ok P : isI (crepP P).1 /\ isI (crepP P).2 /\ coprime (crepP P).1 (crepP P).2.
Proof.
  case: P => [ [ x y ] | ] /=.
  - by have [ h1 [ h2 [ h3 _ ] ] ] := crepx_ok x.
  - split; first exact: isI1. split; first exact: isI0.
    exists 1, 0; split; first exact: isI1. split; first exact: isI0.
    rewrite mulr1 mulr0 addr0; reflexivity.
Qed.

Lemma Ht_ge1 P : 1 <= Ht P.
Proof.
  have [ h1 [ h2 h3 ] ] := crepP_ok P.
  rewrite /Ht; case: (crepP P) h1 h2 h3 => a b /= h1 h2 h3.
  exact: (Mh_ge1 h1 h2 (coprime_nz h3)).
Qed.

Lemma Ht_ge0 P : 0 <= Ht P.
Proof. exact: (le_trans ler01 (Ht_ge1 P)). Qed.

Lemma Ht_x (x y y' : RF) : Ht (Some (x, y)) = Ht (Some (x, y')).
Proof. reflexivity. Qed.

Lemma Ht_neg P : Ht (pt_neg P) = Ht P.
Proof. case: P => [ [ x y ] | ] //=. Qed.

(** * 3. Duplication: Ht T ^ 4 <= KD^2 Ht (2T) *)

Lemma Ht_dbl_Some (x y : RF) : on_curve (x, y) ->
  Ht (Some (x, y)) ^+ 4 <= KD ^+ 2 * Ht (ec_add (Some (x, y)) (Some (x, y))).
Proof.
  move=> hc; have oc := proj1 (on_curveE x y) hc.
  have := crepx_ok x; rewrite /Ht crepP_Some.
  case: (crepx x) => al be; rewrite /crep_spec; move=> [ hal [ hbe [ cab [ eal nbe ] ] ] ].
  rewrite /= in hal hbe cab eal nbe.
  case: (eqVneq y 0) => [ ey | ny ].
  - rewrite (ec_dbl0 x ey) crepP_None.
    apply: (dup_core hal hbe cab isI1 isI0).
    exists 1, 0; split; first exact: isI1. split; first exact: isI0.
    rewrite mulr1 mulr0 addr0; reflexivity.
    have E : Dd aF al be = 4%:R * be ^+ 4 * (x ^+ 3 + aF * x) by rewrite /Dd eal; ring.
    rewrite mul1r mul0r E -oc ey mul0r mulr0; reflexivity.
  - rewrite (ec_dbl x ny) crepP_Some.
    have := crepx_ok (dblx x y).
    case: (crepx (dblx x y)) => ga de; rewrite /crep_spec; move=> [ hga [ hde [ cgd [ ega nde ] ] ] ].
    rewrite /= in hga hde cgd ega nde.
    apply: (dup_core hal hbe cab hga hde cgd).
    have K : dblx x y * (4%:R * (y * y)) = (3%:R * x ^+ 2 + aF) ^+ 2 - 8%:R * x * (y * y).
    { rewrite /dblx; field; exact: (mulf_neq0 two_neq0 ny). }
    rewrite oc in K.
    have ED : Dd aF al be = be ^+ 4 * (4%:R * (x ^+ 3 + aF * x)) by rewrite /Dd eal; ring.
    have EN : Nd aF al be = be ^+ 4 * (x ^+ 2 - aF) ^+ 2 by rewrite /Nd eal; ring.
    rewrite ega ED EN.
    have E2 : dblx x y * de * (be ^+ 4 * (4%:R * (x ^+ 3 + aF * x)))
            = de * be ^+ 4 * (dblx x y * (4%:R * (x ^+ 3 + aF * x))) by ring.
    rewrite E2 K; ring.
Qed.

Lemma Ht_dbl P : on_curve_pt P -> Ht P ^+ 4 <= KD ^+ 2 * Ht (ec_add P P).
Proof.
  case: P => [ [ x y ] | ] hc; first exact: (Ht_dbl_Some hc).
  have -> : ec_add None None = (None : pt rat) by reflexivity.
  rewrite Ht_None expr1n mulr1; exact: (exprn_ege1 2 KD_ge1).
Qed.

(** * 4. Upper parallelogram: Ht (T1 + T2) Ht (T1 - T2) <= KU^2 Ht T1^2 Ht T2^2 *)

Lemma Ht_par (x1 y1 x2 y2 y2n : RF) : on_curve (x1, y1) -> on_curve (x2, y2) -> x1 != x2 ->
  y2n = - y2 ->
  Ht (ec_add (Some (x1, y1)) (Some (x2, y2))) * Ht (ec_add (Some (x1, y1)) (Some (x2, y2n)))
  <= KU ^+ 2 * (Ht (Some (x1, y1)) ^+ 2 * Ht (Some (x2, y2)) ^+ 2).
Proof.
  move=> h1 h2 nx ey.
  have o1 := proj1 (on_curveE x1 y1) h1; have o2 := proj1 (on_curveE x2 y2) h2.
  rewrite (ec_ch _ _ nx) (ec_ch _ _ nx) /Ht !crepP_Some.
  have nd : x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
  have nd' : x1 - x2 != 0 by rewrite subr_eq0.
  apply: par_core; first exact: nx.
  - have K : (x1 - x2) ^+ 2 * (chx x1 y1 x2 y2 + chx x1 y1 x2 y2n)
           = 2%:R * (y1 * y1) + 2%:R * (y2 * y2) - 2%:R * (x1 + x2) * (x1 - x2) ^+ 2.
    { rewrite /chx ey; field; exact: nd. }
    rewrite K o1 o2; ring.
  - have K : (x1 - x2) ^+ 2 * (chx x1 y1 x2 y2 * chx x1 y1 x2 y2n)
           = ((y2 * y2 - y1 * y1) ^+ 2
              - (x1 + x2) * (x1 - x2) ^+ 2 * (2%:R * (y1 * y1) + 2%:R * (y2 * y2))
              + (x1 + x2) ^+ 2 * (x1 - x2) ^+ 4) / (x1 - x2) ^+ 2.
    { rewrite /chx ey; field; exact: nd. }
    rewrite K o1 o2; field; exact: nd'.
Qed.

(** * 5. The multiples of a nontorsion point *)

Section Multiples.

  Variable D : FixedData.

  (* the nontorsion hypothesis, exactly the field E2 of StdHyps *)
  Hypothesis E2 : forall n : int, n != 0 ->
    exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y).

  Let hP0 : on_curve (fd_P0 D) := P0_on_curve_of_E2 E2.

  Lemma mQ_on n : on_curve_pt (mulQ D n). Proof. exact: mulQ_on hP0 n. Qed.

  Lemma mQ_add n m : mulQ D (n + m) = ec_add (mulQ D n) (mulQ D m).
  Proof. exact: mulQ_add hP0 n m. Qed.

  Lemma mQ0 : mulQ D 0 = None. Proof. reflexivity. Qed.

  Lemma mQ_neg n : mulQ D (- n) = pt_neg (mulQ D n).
  Proof.
    rewrite -[mulQ D (- n)](ec_addP0) -(ec_addN rat_sq2 (mulQ D n)).
    rewrite -(ec_add_assoc rat_sq2 (mQ_on _) (mQ_on _) (pt_neg_on rat_sq2 (mQ_on _))).
    rewrite -mQ_add addNr mQ0; reflexivity.
  Qed.

  Lemma mQ_tors n : mulQ D n = None -> n = 0.
  Proof.
    move=> e; apply/eqP; apply/negP => /negP nz.
    have [ x [ y [ e' _ ] ] ] := E2 nz; by rewrite e in e'.
  Qed.

  Lemma mQ_Some n : n != 0 -> exists x y : RF, mulQ D n = Some (x, y) /\ on_curve (x, y).
  Proof. move=> nz; have [ x [ y [ e [ _ [ _ h ] ] ] ] ] := E2 nz; by exists x, y. Qed.

  Lemma y_sqr_eq (x y1 y2 : RF) : on_curve (x, y1) -> on_curve (x, y2) -> y1 = y2 \/ y1 = - y2.
  Proof.
    move=> /on_curveE h1 /on_curveE h2.
    have : (y1 - y2) * (y1 + y2) = 0.
    { have E : (y1 - y2) * (y1 + y2) = y1 * y1 - y2 * y2 by ring.
      rewrite E h1 h2 subrr; reflexivity. }
    move/eqP; rewrite mulf_eq0 => /orP [ /eqP e | /eqP e ].
    - left; apply/eqP; rewrite -subr_eq0; apply/eqP; exact: e.
    - right; apply/eqP; rewrite -subr_eq0 opprK; apply/eqP; exact: e.
  Qed.

  Lemma mQ_eqx (i j : int) (x y1 y2 : RF) :
    mulQ D i = Some (x, y1) -> mulQ D j = Some (x, y2) -> i = j \/ i = - j.
  Proof.
    move=> ei ej.
    have h1 : on_curve (x, y1) by have := mQ_on i; rewrite ei.
    have h2 : on_curve (x, y2) by have := mQ_on j; rewrite ej.
    case: (y_sqr_eq h1 h2) => ey.
    - left; apply/eqP; rewrite -subr_eq0; apply/eqP; apply: mQ_tors.
      rewrite mQ_add mQ_neg ei ej ey; exact: (ec_addN rat_sq2 (Some (x, y2))).
    - right; apply/eqP; rewrite -subr_eq0 opprK; apply/eqP; apply: mQ_tors.
      have e : mulQ D i = pt_neg (mulQ D j) by rewrite ei ej ey; reflexivity.
      rewrite mQ_add e (ec_add_comm rat_sq2 (pt_neg_on rat_sq2 (mQ_on j)) (mQ_on j)).
      exact: (ec_addN rat_sq2 (mulQ D j)).
  Qed.

  Lemma Ht_mneg n : Ht (mulQ D (- n)) = Ht (mulQ D n).
  Proof. rewrite mQ_neg; exact: Ht_neg. Qed.

  (* (D) for multiples *)
  Lemma Ht_mdbl n : Ht (mulQ D n) ^+ 4 <= KD ^+ 2 * Ht (mulQ D (n + n)).
  Proof. rewrite mQ_add; exact: (Ht_dbl (mQ_on n)). Qed.

  (* (U) for multiples *)
  Lemma Ht_mpar (i j : int) : i != 0 -> j != 0 -> i != j -> i != - j ->
    Ht (mulQ D (i + j)) * Ht (mulQ D (i - j))
    <= KU ^+ 2 * (Ht (mulQ D i) ^+ 2 * Ht (mulQ D j) ^+ 2).
  Proof.
    move=> ni nj nij nij'.
    have [ x1 [ y1 [ e1 h1 ] ] ] := mQ_Some ni.
    have [ x2 [ y2 [ e2 h2 ] ] ] := mQ_Some nj.
    have nx : x1 != x2.
    { apply/eqP => ex; rewrite ex in e1.
      by case: (mQ_eqx e1 e2) => e; [ move: nij | move: nij' ]; rewrite e eqxx. }
    rewrite mQ_add [mulQ D (i - j)]mQ_add mQ_neg e1 e2.
    exact: (Ht_par h1 h2 nx (erefl _)).
  Qed.

  Definition KK : RF := KD ^+ 4 * KU ^+ 2.

  Lemma KK_ge1 : 1 <= KK.
  Proof.
    rewrite /KK -[1]mulr1; apply: ler_pM; [ exact: ler01 | exact: ler01 | | ].
    - exact: (exprn_ege1 4 KD_ge1).
    - exact: (exprn_ege1 2 KU_ge1).
  Qed.

  (* (L) lower parallelogram for multiples *)
  Lemma Ht_mlow (i j : int) : i != 0 -> j != 0 -> i != j -> i != - j ->
    Ht (mulQ D i) ^+ 4 * Ht (mulQ D j) ^+ 4
    <= KK * (Ht (mulQ D (i + j)) * Ht (mulQ D (i - j))) ^+ 2.
  Proof.
    move=> ni nj nij nij'.
    have nA : i + j != 0 by rewrite addr_eq0.
    have nB : i - j != 0 by rewrite subr_eq0.
    have nAB : i + j != i - j.
    { apply: contraNneq nj => e; have : j + j = 0.
      { have E : j + j = (i + j) - (i - j) by ring.
        by rewrite E e subrr. }
      by move/eqP; rewrite -mulr2n mulrn_eq0 /=. }
    have nAB' : i + j != - (i - j).
    { apply: contraNneq ni => e; have : i + i = 0.
      { have E : i + i = (i + j) + (i - j) by ring.
        by rewrite E e addNr. }
      by move/eqP; rewrite -mulr2n mulrn_eq0 /=. }
    have U := Ht_mpar nA nB nAB nAB'.
    have e1 : i + j + (i - j) = i + i by ring.
    have e2 : i + j - (i - j) = j + j by ring.
    rewrite e1 e2 in U.
    have Di := Ht_mdbl i; have Dj := Ht_mdbl j.
    have h0 := Ht_ge0 (mulQ D (i + i)); have h0' := Ht_ge0 (mulQ D (j + j)).
    have hKD := le_trans ler01 KD_ge1.
    have P := ler_pM (exprn_ge0 4 (Ht_ge0 _)) (exprn_ge0 4 (Ht_ge0 _)) Di Dj.
    apply: le_trans P _.
    have E : KD ^+ 2 * Ht (mulQ D (i + i)) * (KD ^+ 2 * Ht (mulQ D (j + j)))
           = KD ^+ 4 * (Ht (mulQ D (i + i)) * Ht (mulQ D (j + j))) by ring.
    rewrite E /KK -mulrA; apply: ler_wpM2l; first exact: (exprn_ge0 4 hKD).
    apply: le_trans U _.
    have E' : KU ^+ 2 * (Ht (mulQ D (i + j)) ^+ 2 * Ht (mulQ D (i - j)) ^+ 2)
            = KU ^+ 2 * (Ht (mulQ D (i + j)) * Ht (mulQ D (i - j))) ^+ 2 by ring.
    rewrite E'; exact: lexx.
  Qed.

End Multiples.

(** * 6. Convexity *)

Lemma conv_seq (g : nat -> RF) : g 0%N = 1 -> (forall n, 1 <= g n) ->
  (forall n, 4%:R * g n.+1 ^+ 2 <= g n.+2 * g n) ->
  forall n, 2%:R ^+ (n * n.-1) <= g n.
Proof.
  move=> g0 hge1 hrec.
  have A : forall n, 4%:R ^+ n * g n <= g n.+1.
  { elim=> [ | n IH ].
    - rewrite expr0 mul1r g0; exact: hge1.
    - have r := hrec n.
      have pos : 0 < g n by apply: lt_le_trans (hge1 n); exact: ltr01.
      have h1 := ler_wpM2r (le_trans ler01 (hge1 n.+1)) IH.
      have h2 : g n * (4%:R ^+ n.+1 * g n.+1) <= g n * g n.+2.
      { rewrite exprS; lra. }
      by move: h2; rewrite (ler_pM2l pos). }
  elim=> [ | n IH ].
  - rewrite mul0n expr0 g0; exact: lexx.
  - have e : (n.+1 * n.+1.-1 = n.*2 + n * n.-1)%N.
    { case: n {IH} => [ | n ] //=; rewrite !mulSn !mulnS -!addnn; ring. }
    rewrite e exprD -mul2n exprM.
    have h4 : (2%:R : RF) ^+ 2 = 4%:R by rewrite -natrX.
    rewrite h4.
    apply: le_trans (A n).
    apply: ler_wpM2l; [ exact: (exprn_ge0 n (ler0n _ 4)) | exact: IH ].
Qed.

Lemma sum_ge (F : nat -> RF) (m r : nat) : (forall i, 0 <= F i) -> (r < m)%N ->
  F r <= \sum_(i < m) F i.
Proof.
  move=> h0; elim: m => [ | m IH ] // hr.
  rewrite big_ord_recr /=.
  case: (ltngtP r m) => hrm.
  - have := IH hrm; have := h0 m; lra.
  - by move: hr; rewrite ltnS leqNgt hrm.
  - rewrite hrm; have : 0 <= \sum_(i < m) F i by apply: sumr_ge0 => i _; exact: h0.
    lra.
Qed.

(* an explicit natural upper bound for an element of RF *)
Definition RFb (x : RF) : nat := Num.bound (`|qre x| + 2%:R * `|qim x|).

Lemma RFb_spec (x : RF) : x <= (RFb x)%:R.
Proof.
  case: x => a b; rewrite /RFb /=.
  have h := norm_QE_le a b.
  have h0 : 0 <= `|a| + 2%:R * `|b| :> rat.
  { by apply: addr_ge0; [ exact: normr_ge0 | apply: mulr_ge0; [ exact: ler0n | exact: normr_ge0 ] ]. }
  apply: le_trans (ler_norm _) _; apply: le_trans h _.
  rewrite -qr_nat qr_le; exact: ltW (archi_boundP h0).
Qed.

Lemma RF_bound (x : RF) : exists k : nat, x <= k%:R.
Proof. exists (RFb x); exact: RFb_spec. Qed.

Lemma nat_le_pow2 (k : nat) : (k%:R : RF) <= 2%:R ^+ k.
Proof. rewrite -natrX ler_nat; exact: ltnW (ltn_expl k (ltnSn 1)). Qed.

Lemma RFb_pow2 (x : RF) : x <= 2%:R ^+ RFb x.
Proof. exact: le_trans (RFb_spec x) (nat_le_pow2 _). Qed.

Lemma posz_neq0 (a : nat) : (0 < a)%N -> a%:Z != 0.
Proof.
  move=> h; apply/negP => /eqP e.
  have := congr1 absz e; rewrite absz_nat /= => ea.
  by rewrite ea in h.
Qed.

Lemma posz_neqN (a b : nat) : (0 < a)%N -> a%:Z != - b%:Z.
Proof.
  move=> ha; apply/negP => /eqP e.
  have e2 : (a + b)%N%:Z = 0 by rewrite PoszD e addNr.
  have := congr1 absz e2; rewrite absz_nat /= => /eqP.
  by rewrite addn_eq0 => /andP [ /eqP h _ ]; rewrite h in ha.
Qed.

Section Growth.

  Variable D : FixedData.

  Hypothesis E2 : forall n : int, n != 0 ->
    exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y).

  Definition xco (P : pt rat) : RF := if P is Some (x, _) then x else 0.

  (* (N) Northcott + nontorsion: the heights of the multiples are unbounded *)
  Lemma unbounded_has (X : nat) :
    has (fun i : nat => X%:R < Ht (mulQ D i%:Z)) (iota 1 (size (candX X)).+1).
  Proof.
    pose L := size (candX X).
    pose s := [seq xco (mulQ D i%:Z) | i <- iota 1 L.+1].
    have pos (i : nat) : i \in iota 1 L.+1 -> (i%:Z != 0).
    { by rewrite mem_iota => /andP [ h _ ]; apply: posz_neq0. }
    have nall : ~~ all (fun i : nat => Ht (mulQ D i%:Z) <= X%:R) (iota 1 L.+1).
    { apply/negP => /allP hall.
      have sub : {subset s <= candX X}.
      { move=> x /mapP [ i hi -> ].
        have [ x' [ y' [ e _ ] ] ] := mQ_Some E2 (pos i hi).
        have hb := hall i hi; rewrite e in hb *.
        exact: (Mh_bounded_mem hb). }
      have uq : uniq s.
      { rewrite map_inj_in_uniq ?iota_uniq // => i j hi hj.
        have [ x1 [ y1 [ e1 _ ] ] ] := mQ_Some E2 (pos i hi).
        have [ x2 [ y2 [ e2 _ ] ] ] := mQ_Some E2 (pos j hj).
        rewrite e1 e2 /= => ex; rewrite ex in e1.
        case: (mQ_eqx E2 e1 e2) => [ [] // | e ].
        exfalso; move: hi hj; rewrite !mem_iota => /andP [ hi _ ] /andP [ hj _ ].
        by move: (posz_neqN j hi); rewrite e eqxx. }
      have := uniq_leq_size uq sub.
      by rewrite size_map size_iota ltnn. }
    apply/hasP; case/allPn: nall => i hi hlt.
    exists i; first exact: hi.
    by rewrite ltNge.
  Qed.

  (* an explicit multiple of large height *)
  Definition HL_X : nat := RFb (4%:R * KK).
  Definition HL_iota : seq nat := iota 1 (size (candX HL_X)).+1.
  Definition HL_m : nat :=
    nth 0%N HL_iota (find (fun i : nat => HL_X%:R < Ht (mulQ D i%:Z)) HL_iota).

  Lemma HL_m_spec : (0 < HL_m)%N /\ HL_X%:R < Ht (mulQ D HL_m%:Z).
  Proof.
    have h := unbounded_has HL_X.
    split.
    - have : HL_m \in HL_iota by rewrite /HL_m mem_nth // -has_find.
      by rewrite /HL_iota mem_iota => /andP [].
    - exact: (nth_find 0%N h).
  Qed.

  (* the recursion for g n = Ht (n m P0)^2 *)
  Section with_m.

    Variable m : nat.
    Hypothesis hm : (0 < m)%N.
    Hypothesis hHm : 4%:R * KK <= Ht (mulQ D m%:Z) ^+ 4.

    Definition gm (n : nat) : RF := Ht (mulQ D (n * m)%N%:Z) ^+ 2.

    Lemma gm_rec n : 4%:R * gm n.+1 ^+ 2 <= gm n.+2 * gm n.
    Proof.
      have hKK := le_trans ler01 KK_ge1.
      have pKK : 0 < KK by apply: lt_le_trans KK_ge1; exact: ltr01.
      case: n => [ | n ].
      - (* duplication *)
        rewrite /gm mul0n mQ0 Ht_None expr1n mulr1 mul1n.
        have Dm := Ht_mdbl E2 m%:Z.
        have e2 : (m%:Z + m%:Z) = (2 * m)%N%:Z by rewrite -PoszD addnn mul2n.
        rewrite e2 in Dm.
        set h1 := Ht (mulQ D m%:Z); set h2 := Ht (mulQ D (2 * m)%N%:Z).
        have h1ge := Ht_ge1 (mulQ D m%:Z); have h2ge := Ht_ge1 (mulQ D (2 * m)%N%:Z).
        have hHm' := hHm.
        rewrite -/h1 -/h2 in h1ge h2ge Dm hHm'.
        have hKD := le_trans ler01 KD_ge1.
        have hKD4 : KD ^+ 4 <= KK.
        { rewrite /KK -[X in X <= _]mulr1; apply: ler_wpM2l; first exact: exprn_ge0.
          exact: (exprn_ege1 2 KU_ge1). }
        (* h1^8 <= KD^4 h2^2 and 4 KD^4 h1^4 <= h1^8 *)
        have s1 : (h1 ^+ 4) ^+ 2 <= (KD ^+ 2 * h2) ^+ 2.
        { apply: lexp; [ exact: exprn_ge0 (le_trans ler01 h1ge) | exact: Dm ]. }
        have s2 : 4%:R * KD ^+ 4 * h1 ^+ 4 <= h1 ^+ 4 * h1 ^+ 4.
        { have h14 : 0 <= h1 ^+ 4 := exprn_ge0 4 (le_trans ler01 h1ge).
          have := ler_wpM2r h14 (le_trans (ler_wpM2l (ler0n _ 4) hKD4) hHm'); exact. }
        have pKD4 : 0 < KD ^+ 4 by apply: exprn_gt0; apply: lt_le_trans KD_ge1; exact: ltr01.
        rewrite -(ler_pM2l pKD4).
        have E1 : (h1 ^+ 4) ^+ 2 = h1 ^+ 4 * h1 ^+ 4 by rewrite expr2.
        have E2' : (KD ^+ 2 * h2) ^+ 2 = KD ^+ 4 * h2 ^+ 2 by rewrite exprMn -exprM.
        have E3 : (h1 ^+ 2) ^+ 2 = h1 ^+ 4 by rewrite -exprM.
        rewrite E1 E2' in s1; rewrite E3.
        have : 4%:R * KD ^+ 4 * h1 ^+ 4 <= KD ^+ 4 * h2 ^+ 2 by apply: le_trans s2 s1.
        have E4 : KD ^+ 4 * (4%:R * h1 ^+ 4) = 4%:R * KD ^+ 4 * h1 ^+ 4 by ring.
        rewrite E4; exact.
      - (* lower parallelogram with i = (n+2) m, j = m *)
        pose i := (n.+2 * m)%N.
        have hi : (0 < i)%N by rewrite /i muln_gt0 hm.
        have nij : i%:Z != m%:Z.
        { apply/negP; rewrite eqz_nat => /eqP e.
          have : (m < i)%N by rewrite /i; apply: ltn_Pmull.
          by rewrite e ltnn. }
        have L := Ht_mlow E2 (posz_neq0 hi) (posz_neq0 hm) nij (posz_neqN m hi).
        have ea : i%:Z + m%:Z = (n.+3 * m)%N%:Z by rewrite -PoszD /i [(n.+3 * m)%N]mulSn addnC.
        have eb : i%:Z - m%:Z = (n.+1 * m)%N%:Z.
        { rewrite /i [(n.+2 * m)%N]mulSn PoszD addrAC subrr add0r; reflexivity. }
        rewrite ea eb in L.
        rewrite /gm -/i.
        set a := Ht (mulQ D i%:Z); set b := Ht (mulQ D (n.+3 * m)%N%:Z).
        set c := Ht (mulQ D (n.+1 * m)%N%:Z); set h1 := Ht (mulQ D m%:Z).
        have hHm' := hHm.
        rewrite -/a -/b -/c -/h1 in L hHm'.
        have ha4 : 0 <= a ^+ 4 := exprn_ge0 4 (Ht_ge0 _).
        have P := ler_wpM2l ha4 hHm'.
        have E5 : (a ^+ 2) ^+ 2 = a ^+ 4 by rewrite -exprM.
        have E6 : (b * c) ^+ 2 = b ^+ 2 * c ^+ 2 by rewrite exprMn.
        rewrite E5; rewrite E6 in L.
        rewrite -(ler_pM2l pKK).
        have E7 : KK * (4%:R * a ^+ 4) = a ^+ 4 * (4%:R * KK) by ring.
        rewrite E7; apply: le_trans P _.
        have E8 : a ^+ 4 * h1 ^+ 4 <= KK * (b ^+ 2 * c ^+ 2) := L.
        exact: E8.
    Qed.

    Lemma gm_growth n : 2%:R ^+ (n * n.-1) <= gm n.
    Proof.
      apply: conv_seq.
      - rewrite /gm mul0n mQ0 Ht_None expr1n; reflexivity.
      - move=> k; rewrite /gm; exact: (exprn_ege1 2 (Ht_ge1 _)).
      - exact: gm_rec.
    Qed.

    Definition Fm (i : nat) : RF := Ht (mulQ D i%:Z).
    Definition Bm : RF := \sum_(r < m) Fm r.

    Lemma Bm_ge (r : nat) : (r < m)%N -> Ht (mulQ D r%:Z) <= Bm.
    Proof. move=> hr; exact: (@sum_ge Fm m r (fun i => Ht_ge0 _) hr). Qed.

    Lemma Bm_ge1 : 1 <= Bm.
    Proof. have := Bm_ge hm; rewrite mQ0 Ht_None; exact. Qed.

    (* (R): all N *)
    Lemma growth_all (N : nat) :
      2%:R ^+ ((N %/ m) * (N %/ m).-1) <= (KU ^+ 4 * Bm ^+ 4) * Ht (mulQ D N%:Z) ^+ 4.
    Proof.
      have hW : 1 <= KU ^+ 4 * Bm ^+ 4.
      { rewrite -[1]mulr1; apply: ler_pM; [ exact: ler01 | exact: ler01 | | ].
        - exact: (exprn_ege1 4 KU_ge1).
        - exact: (exprn_ege1 4 Bm_ge1). }
      have hH := Ht_ge1 (mulQ D N%:Z).
      have hH4 : 1 <= Ht (mulQ D N%:Z) ^+ 4 := exprn_ege1 4 hH.
      have h2 : Ht (mulQ D N%:Z) ^+ 2 <= Ht (mulQ D N%:Z) ^+ 4.
      { have E : Ht (mulQ D N%:Z) ^+ 4 = Ht (mulQ D N%:Z) ^+ 2 * Ht (mulQ D N%:Z) ^+ 2.
        { by rewrite -exprD. }
        rewrite E; exact: (ler_peMr (exprn_ge0 2 (Ht_ge0 _)) (exprn_ege1 2 hH)). }
      have W0 : 0 <= KU ^+ 4 * Bm ^+ 4 := le_trans ler01 hW.
      set n := (N %/ m)%N; set r := (N %% m)%N.
      have eN : N = (n * m + r)%N by exact: divn_eq.
      have G := gm_growth n.
      case: (posnP r) => hr.
      - (* r = 0 *)
        have eN' : N = (n * m)%N by rewrite eN hr addn0.
        rewrite /gm -eN' in G.
        apply: le_trans G _; apply: le_trans h2 _.
        exact: (ler_peMl (exprn_ge0 4 (Ht_ge0 _)) hW).
      case: (posnP n) => hn.
      - rewrite hn mul0n expr0.
        have := ler_pM ler01 ler01 hW hH4; rewrite mulr1; exact.
      (* n >= 1, r >= 1: (U) with (N, r) *)
      have hrm : (r < m)%N by exact: ltn_pmod.
      have hN : (0 < N)%N by rewrite eN addn_gt0 hr orbT.
      have nNr : N%:Z != r%:Z.
      { apply/negP; rewrite eqz_nat => /eqP e.
        have : (r < N)%N by rewrite eN -{1}[r]add0n ltn_add2r muln_gt0 hn hm.
        by rewrite e ltnn. }
      have U := Ht_mpar E2 (posz_neq0 hN) (posz_neq0 hr) nNr (posz_neqN r hN).
      have eb : N%:Z - r%:Z = (n * m)%N%:Z by rewrite eN PoszD addrK.
      rewrite eb in U.
      have hBr := Bm_ge hrm.
      set hN' := Ht (mulQ D N%:Z) in hH h2 U *; set hr' := Ht (mulQ D r%:Z) in U hBr.
      set hA := Ht (mulQ D (N%:Z + r%:Z)) in U.
      set hnm := Ht (mulQ D (n * m)%N%:Z) in U G.
      have hA1 := Ht_ge1 (mulQ D (N%:Z + r%:Z)); rewrite -/hA in hA1.
      have hnm0 : 0 <= hnm := Ht_ge0 _.
      have hr0 : 0 <= hr' := Ht_ge0 _.
      have s1 : hnm <= KU ^+ 2 * (hN' ^+ 2 * Bm ^+ 2).
      { apply: le_trans (ler_peMl hnm0 hA1) _; apply: le_trans U _.
        apply: ler_wpM2l; first exact: (exprn_ge0 2 (le_trans ler01 KU_ge1)).
        apply: ler_wpM2l; first exact: (exprn_ge0 2 (Ht_ge0 _)).
        exact: lexp 2 hr0 hBr. }
      have s2 : hnm ^+ 2 <= (KU ^+ 2 * (hN' ^+ 2 * Bm ^+ 2)) ^+ 2 := lexp 2 hnm0 s1.
      have E : (KU ^+ 2 * (hN' ^+ 2 * Bm ^+ 2)) ^+ 2 = KU ^+ 4 * Bm ^+ 4 * hN' ^+ 4.
      { ring. }
      rewrite E in s2.
      rewrite /gm -/hnm in G; exact: le_trans G s2.
    Qed.

  End with_m.

End Growth.

(** * 7. The theorem O_HL *)

Lemma nat_sq_bound (q : nat) : (q.+1 * q.+1 <= 4 * (q * q.-1) + 9)%N.
Proof.
  case: q => [ | q ]; first by [].
  rewrite [q.+1.-1]/=.
  apply/ssrnat.leP; rewrite -!plusE -!multE; nia.
Qed.

(* the explicit constants: they depend only on fd_P0 D (see [HL_P0]) *)
Definition HL_Nh (D : FixedData) : nat := (32 * HL_m D ^ 2)%N.
Definition HL_Ch (D : FixedData) : nat := (RFb (KU ^+ 4 * Bm D (HL_m D) ^+ 4)%R + 3)%N.

Theorem O_HL_explicit (D : FixedData) :
  (forall n : int, n != 0 ->
     exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y)) ->
  (0 < HL_Nh D)%N /\
    forall (n : int) (x0 x1 x2 : rat), n != 0 -> x2 != 0 ->
      (exists y, mulP D n = Some (QE x0 x1 / qe_of x2, y)) ->
      ((absz n) ^ 2 <= HL_Nh D * (htb x0 + htb x1 + htb x2 + HL_Ch D))%N.
Proof.
  move=> E2.
  have hX := RFb_spec (4%:R * KK).
  have [ hm hmX ] := HL_m_spec E2.
  rewrite /HL_Nh /HL_Ch; set m := HL_m D in hm hmX *.
  rewrite -/(HL_X) in hX.
  have hHm : 4%:R * KK <= Ht (mulQ D m%:Z) ^+ 4.
  { have h1 := Ht_ge1 (mulQ D m%:Z).
    apply: le_trans hX _; apply: le_trans (ltW hmX) _.
    exact: (ler_eXnr (ltn0Sn 3) h1). }
  have hk := RFb_pow2 (KU ^+ 4 * Bm D m ^+ 4).
  set k := RFb (KU ^+ 4 * Bm D m ^+ 4) in hk *.
  split.
  { by rewrite muln_gt0 expn_gt0 hm. }
  move=> n x0 x1 x2 nn nx2 [ y hy ].
  rewrite /mulP in hy.
  set m0 := fd_m D in hy.
  set N := absz (n * m0%:Z).
  (* m0 > 0 *)
  have hm0 : (0 < m0)%N.
  { rewrite lt0n; apply/negP => /eqP e.
    have e' : n * m0%:Z = 0 by rewrite e mulr0.
    by move: hy; rewrite e' mQ0. }
  (* the height of the point *)
  have eHt : Ht (mulQ D N%:Z) = Ht (mulQ D (n * m0%:Z)).
  { rewrite /N; case: (lerP 0 (n * m0%:Z)) => h.
    - rewrite (gez0_abs h); try reflexivity.
    - rewrite (ltz0_abs h); exact: Ht_mneg. }
  have hHtx : Ht (mulQ D (n * m0%:Z)) = Mh (crepx (QE x0 x1 / qr x2)).
  { rewrite hy; reflexivity. }
  have hb := Mh_htb x0 x1 nx2.
  set H := (htb x0 + htb x1 + htb x2)%N in hb *.
  have G := growth_all E2 hm hHm N.
  set q := (N %/ m)%N in G.
  (* the height in bits *)
  have hH : Ht (mulQ D N%:Z) <= 2%:R ^+ (4 + 2 * H).
  { rewrite eHt hHtx; apply: le_trans hb _.
    rewrite qr_mul qr_nat qr_expn qr_nat exprD exprM.
    have e4 : (2%:R : RF) ^+ 2 = 4%:R by rewrite -natrX.
    rewrite e4; apply: ler_wpM2r; first exact: (exprn_ge0 H (ler0n _ 4)).
    rewrite -natrX ler_nat; exact: isT. }
  have hH4 : Ht (mulQ D N%:Z) ^+ 4 <= 2%:R ^+ (16 + 8 * H).
  { have e : (16 + 8 * H = (4 + 2 * H) * 4)%N.
    { apply/eqP; rewrite eqn_leq; apply/andP; split; apply/ssrnat.leP; rewrite -!plusE -!multE; lia. }
    rewrite e exprM; exact: (lexp 4 (Ht_ge0 _) hH). }
  have hW0 : 0 <= KU ^+ 4 * Bm D m ^+ 4.
  { apply: mulr_ge0; [ exact: (exprn_ge0 4 (le_trans ler01 KU_ge1)) | exact: (exprn_ge0 4 (le_trans ler01 (Bm_ge1 D hm))) ]. }
  have Hb : (2%:R : RF) ^+ (q * q.-1) <= 2%:R ^+ (k + (16 + 8 * H)).
  { apply: le_trans G _; rewrite exprD.
    exact: (ler_pM hW0 (exprn_ge0 4 (Ht_ge0 _)) hk hH4). }
  have h12 : (1 : RF) < 2%:R by rewrite ltr1n.
  rewrite (ler_eXn2l h12) in Hb.
  (* nat arithmetic *)
  have s1 : (absz n <= N)%N.
  { rewrite /N abszM absz_nat; exact: leq_pmulr hm0. }
  have s2 : (N <= q.+1 * m)%N by exact: ltnW (ltn_ceil N hm).
  have s3 := nat_sq_bound q.
  pose T := (32 * (H + (k + 3)))%N.
  have s4 : (4 * (q * q.-1) + 9 <= T)%N.
  { move: Hb; rewrite /T => /ssrnat.leP Hb; apply/ssrnat.leP; rewrite -!plusE -!multE in Hb *; lia. }
  have s5 : (absz n <= q.+1 * m)%N := leq_trans s1 s2.
  rewrite -mulnn.
  apply: leq_trans (leq_mul s5 s5) _.
  have e1 : (q.+1 * m * (q.+1 * m) = (q.+1 * q.+1) * (m * m))%N by rewrite mulnACA.
  rewrite e1.
  apply: leq_trans (leq_mul (leq_trans s3 s4) (leqnn (m * m))) _.
  have e2 : (T * (m * m) = 32 * m ^ 2 * (H + (k + 3)))%N.
  { rewrite /T -mulnn; apply/eqP; rewrite eqn_leq; apply/andP; split;
      apply/ssrnat.leP; rewrite -!plusE -!multE; nia. }
  by rewrite e2.
Qed.

Theorem O_HL_thm (D : FixedData) :
  (forall n : int, n != 0 ->
     exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y)) ->
  exists Nh Ch : nat, (0 < Nh)%N /\
    forall (n : int) (x0 x1 x2 : rat), n != 0 -> x2 != 0 ->
      (exists y, mulP D n = Some (QE x0 x1 / qe_of x2, y)) ->
      ((absz n) ^ 2 <= Nh * (htb x0 + htb x1 + htb x2 + Ch))%N.
Proof. move=> E2; exists (HL_Nh D), (HL_Ch D); exact: O_HL_explicit E2. Qed.

(* the field O_HL of OrdHyps (FixedData.v), for data whose constants are
   the explicit ones *)
Corollary O_HL_field (D : FixedData) :
  (forall n : int, n != 0 ->
     exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y)) ->
  fd_Nh D = HL_Nh D -> fd_Ch D = HL_Ch D ->
  forall (n : int) (x0 x1 x2 : rat), n != 0 -> x2 != 0 ->
    (exists y, mulP D n = Some (QE x0 x1 / qe_of x2, y)) ->
    ((absz n) ^ 2 <= fd_Nh D * (htb x0 + htb x1 + htb x2 + fd_Ch D))%N.
Proof. move=> E2 -> ->; exact: (proj2 (O_HL_explicit E2)). Qed.

Corollary HL_Nh_pos (D : FixedData) :
  (forall n : int, n != 0 ->
     exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y)) ->
  (0 < HL_Nh D)%N.
Proof. move=> E2; exact: (proj1 (O_HL_explicit E2)). Qed.

(* the constants depend only on the point P0 *)
Lemma mulQ_P0 (D D' : FixedData) : fd_P0 D = fd_P0 D' -> mulQ D =1 mulQ D'.
Proof. by move=> e [] k; rewrite /mulQ /mulQn e. Qed.

Lemma HL_P0 (D D' : FixedData) : fd_P0 D = fd_P0 D' ->
  HL_Nh D = HL_Nh D' /\ HL_Ch D = HL_Ch D'.
Proof.
  move=> e; have eQ := mulQ_P0 e.
  have em : HL_m D = HL_m D'.
  { rewrite /HL_m; congr nth; apply: eq_find => i /=.
    have -> : Ht (mulQ D i%:Z) = Ht (mulQ D' i%:Z) by congr Ht; exact: eQ.
    reflexivity. }
  have eB : forall m, Bm D m = Bm D' m.
  { move=> m; apply: eq_bigr => i _; congr Ht; exact: eQ. }
  by rewrite /HL_Nh /HL_Ch em eB.
Qed.

