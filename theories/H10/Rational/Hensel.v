(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Local theory over Q without q-adic numbers (PLAN.md, Phase 3, task Q3;
   PP1_DESIGN.md, Sec. 3, items I2 and I7, and the Hensel steps of
   Sec. 2.3). Everything is stated with congruences "for all k" on
   integers (Stdlib Z); no Q_p is constructed.

   PROVED here (no axioms):
   - Sec. 2: Hensel lifting for an explicit integer function with a
     Taylor expansion, in the general form  f'(x0) = p^e u0 (u0 a unit),
     p^(2e+1) | f(x0)  =>  for all k a root mod p^k congruent to x0 mod
     p^(e+1), with an explicit coherent sequence [hs] ([hensel_gen],
     [hs_coh], [hs_root]); the classical case e = 0 ([hensel_fun]) and
     the form [hensel_fun_e] for a prime p;
   - Sec. 3: the instance for integer polynomials given by coefficient
     lists ([peval], [pderv]: [hensel_poly], [hensel_poly_e]) and for
     one-variable quadratics ([hensel_quad], [hensel_quad_e]);
   - Sec. 4: square roots of units: [sqrt_lift_odd] (odd p, a root mod
     p lifts), [sqrt_lift_two] (a = c mod 8 lifts), coherent sequences
     [sqrt_seq_spec], [sqrt_seq2_spec]; [usq p a c] (a/c is a square mod
     p^k for all k) and its finite criteria [usq_odd], [usq_two]; the
     trivial direction [sqmodk_le]; [usq_mul], [usq_transfer];
   - Sec. 5: local solvability of quadrics: [diag3_lift],
     [diag3_lift_two] (a1 x1^2 + a2 x2^2 + a3 x3^2), and [cov_lift_odd],
     [cov_lift_two] for the 2-covering equations [cov1], [cov2] of
     PP1_DESIGN.md 1.4: a solution mod p (resp. mod 8) with d2 z2 and
     d1 d2 z3 units lifts to primitive solutions mod p^k for all k;
   - Sec. 6: CRT for pairwise coprime moduli ([crt_list]) and for
     distinct primes with explicit precisions ([crt_primes]);
   - Sec. 9: [is_locsq q x] (x = y^2 a/c, a/c a square mod q^k for all
     k) and its equivalence with PhiCovering's [locsq] ([locsq_is_locsq]);
     representation independence ([locsq_rep], [is_locsq_rep]); the
     finite criterion, both directions: [locsq_numden] (on the reduced
     fraction via [vu]), [locsq_iff_val] (v_q(x) even and unit part a
     square mod q, resp. = 1 mod 8), [locsq_iff_rep], [locsq_val],
     [locsq_odd_val]; the unit part as a Legendre-type condition
     [sqmod_odd_prod] (a c a square mod q) and [sqmod_two_prod]
     (a c = 1 mod 8); the real place [locsq_inf] (sign);
   - Sec. 10: [locsq_mul], [locsq_inv], [locsq_div], [locsq_sq],
     [locsq_near1] (1 + q^K s/t with K >= 1, resp. K >= 3 at 2) and the
     stability [locsq_close] (v_q(x' - x) >= v_q(x) + 1, resp. + 3);
   - Sec. 11: weak approximation for Q at finitely many primes with
     explicit precisions ([weak_approx]) and simultaneously at infinity
     ([weak_approx_inf]: |x - r| < eps).

   NOT formalized: q-adic numbers themselves (the "for all k"
   congruences are the stand-in), and a lifting lemma for arbitrary
   multivariate polynomials (the quadric lemmas lift one variable). *)

From Stdlib Require Import ZArith Zdivisibility Lia List.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential FixedData ExplicitData PaperInputs PhiCovering RatVal OrdinaryFacts.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

(** * 1. Arithmetic in Z *)

Section ZAux.

  Local Open Scope Z_scope.

  Lemma pz_add (p a b : Z) : 0 <= a -> 0 <= b -> p ^ (a + b) = p ^ a * p ^ b.
  Proof. exact: Z.pow_add_r. Qed.


  Lemma pz_neq0 (p a : Z) : 0 < p -> 0 <= a -> p ^ a <> 0.
  Proof. move=> Hp Ha; have := Z.pow_pos_nonneg p a Hp Ha; lia. Qed.

  Lemma pz_dvd (p a b : Z) : 0 <= a <= b -> (p ^ a | p ^ b).
  Proof.
    move=> Hab; have -> : b = (b - a) + a by lia.
    rewrite pz_add; [ lia | lia | exact: Z.divide_factor_r ].
  Qed.

  Lemma dvd_trans_pz (p a b x : Z) : 0 <= a <= b -> (p ^ b | x) -> (p ^ a | x).
  Proof. move=> Hab; apply: Z.divide_trans; exact: pz_dvd. Qed.

  Lemma inv_coprime (m a : Z) : Z.coprime m a -> exists i, (m | a * i - 1).
  Proof. move=> /Z.Bezout_coprime [ u [ v H ] ]; exists v; exists (- u); lia. Qed.

  Lemma coprime_pz (p k a : Z) : Z.prime p -> 0 <= k -> ~ (p | a) -> Z.coprime (p ^ k) a.
  Proof. move=> Hp Hk Ha; apply: Z.coprime_pow_l => //; exact: Z.coprime_prime_l. Qed.

  Lemma inv_prime (p a : Z) : Z.prime p -> ~ (p | a) -> exists i, (p | a * i - 1).
  Proof. move=> Hp Ha; apply: inv_coprime; exact: Z.coprime_prime_l. Qed.

  Lemma inv_pz (p k a : Z) : Z.prime p -> 0 <= k -> ~ (p | a) -> exists i, (p ^ k | a * i - 1).
  Proof. move=> Hp Hk Ha; apply: inv_coprime; exact: coprime_pz. Qed.

  Lemma dvd_cancel (m a w : Z) : Z.coprime m a -> (m | a * w) -> (m | w).
  Proof. move=> Hc H; exact: Z.gauss H Hc. Qed.

  Lemma prime_ndvd_mul (p a b : Z) : Z.prime p -> ~ (p | a) -> ~ (p | b) -> ~ (p | a * b).
  Proof. by move=> Hp Ha Hb /(Z.divide_prime_mul _ _ _ Hp) [ ]. Qed.

  Lemma dvd_sub_trans (m x y z : Z) : (m | x - y) -> (m | y - z) -> (m | x - z).
  Proof. move=> [ a Ha ] [ b Hb ]; exists (a + b); lia. Qed.

  Lemma dvd_sym (m x y : Z) : (m | x - y) -> (m | y - x).
  Proof. move=> [ a Ha ]; exists (- a); lia. Qed.

  (* an odd square is 1 mod 8 *)
  Lemma odd_sq8 (z : Z) : ~ (2 | z) -> (8 | z * z - 1).
  Proof.
    move=> Hz.
    have [ m Hm ] : exists m, z = 2 * m + 1.
    { exists (z / 2); have := Z.mod_pos_bound z 2; have := Z.div_mod z 2.
      have : z mod 2 <> 0 by move=> H; apply: Hz; exact: (proj1 (Z.mod_divide z 2 ltac:(lia)) H).
      lia. }
    subst z.
    have [ n [ Hn | Hn ] ] : exists n, m = 2 * n \/ m = 2 * n + 1.
    { exists (m / 2); have := Z.mod_pos_bound m 2; have := Z.div_mod m 2; lia. }
    - subst m; exists (n * (2 * n + 1)); lia.
    - subst m; exists ((2 * n + 1) * (n + 1)); lia.
  Qed.

  Lemma two_dvd_of_sq8 (z c : Z) : ~ (2 | c) -> (2 | z * z * c) -> (2 | z).
  Proof.
    move=> Hc H.
    have Hp := Z.prime_2.
    move: H => /(Z.divide_prime_mul _ _ _ Hp) [ /(Z.divide_prime_mul _ _ _ Hp) [ | ] | ] //.
  Qed.

End ZAux.

(** * 2. Hensel lifting for an explicit function with a Taylor expansion

    [f : Z -> Z] with a "derivative" [f'] such that
      f (x + h) = f x + h f'(x) + h^2 g(x, h)   (some integer g), and
      x = y mod M  implies  f' x = f' y mod M  (for every modulus M).
    Every integer polynomial satisfies both (Sec. 3). If p^e exactly
    divides f'(x0) (f'(x0) = p^e u0 with u0 a unit mod p, inverse i) and
    p^(2e+1) divides f(x0), the Newton-type sequence

      hs 0 = x0,  hs (m+1) = hs m - p^(e+1+m) * (f (hs m) / p^(2e+1+m)) * i

    is coherent (hs (m+1) = hs m mod p^(e+1+m)), stays congruent to x0
    modulo p^(e+1), and f (hs m) = 0 mod p^(2e+1+m). The case e = 0 is the
    classical lemma (f(x0) = 0 mod p, f'(x0) a unit mod p); e = 1 at p = 2
    is the 2-adic form (f(x0) = 0 mod 8, f'(x0) = 2 * odd). *)

Section HenselGen.

  Local Open Scope Z_scope.

  Variables (p : Z) (f f' : Z -> Z).
  Hypothesis p_pos : 0 < p.
  Hypothesis f_taylor : forall x h, exists g, f (x + h) = f x + h * f' x + h * h * g.
  Hypothesis f'_cong : forall M x y, (M | x - y) -> (M | f' x - f' y).
  Variables (e : Z) (x0 u0 i : Z).
  Hypothesis e_ge0 : 0 <= e.
  Hypothesis f'x0 : f' x0 = p ^ e * u0.
  Hypothesis u0_inv : (p | u0 * i - 1).
  Hypothesis fx0 : (p ^ (2 * e + 1) | f x0).

  Fixpoint hs (m : nat) : Z :=
    match m with
    | O => x0
    | S m' => hs m' - p ^ (e + 1 + Z.of_nat m') * ((f (hs m') / p ^ (2 * e + 1 + Z.of_nat m')) * i)
    end.

  Lemma hs_inv (m : nat) :
    (p ^ (e + 1) | hs m - x0) /\ (p ^ (2 * e + 1 + Z.of_nat m) | f (hs m)).
  Proof using All.
    elim: m => [ | m [ IH1 IH2 ] ].
    - split; first by exists 0; rewrite /=; lia.
      by rewrite /= Z.add_0_r.
    - set x := hs m; set mm := Z.of_nat m.
      have Hmm : 0 <= mm by rewrite /mm; lia.
      set P := p ^ e; set pm := p ^ mm.
      have E1 : p ^ (e + 1) = P * p by rewrite pz_add ?Z.pow_1_r; lia.
      have E2 : p ^ (e + 1 + mm) = P * p * pm by rewrite pz_add ?E1; lia.
      have E3 : p ^ (2 * e + 1 + mm) = P * P * p * pm.
      { have -> : 2 * e + 1 + mm = e + (e + 1 + mm) by lia.
        rewrite pz_add ?E2; lia. }
      have E4 : p ^ (2 * e + 1 + Z.of_nat m.+1) = P * P * p * pm * p.
      { have -> : 2 * e + 1 + Z.of_nat m.+1 = (2 * e + 1 + mm) + 1 by rewrite /mm; lia.
        rewrite pz_add ?E3 ?Z.pow_1_r; lia. }
      have HP : P * P * p * pm <> 0 by rewrite -E3; apply: pz_neq0; lia.
      move: IH2; rewrite -/x -/mm E3 => - [ c Hc ].
      have Ht : f x / (P * P * p * pm) = c by rewrite Hc Z.div_mul.
      have Hx' : hs m.+1 = x + - (P * p * pm * (c * i)).
      { by rewrite /= -/x -/mm E2 E3 Ht; lia. }
      have [ w Hw ] : (P * p | f' x - f' x0) by rewrite -E1; exact: f'_cong IH1.
      move: u0_inv => [ j Hj ].
      have [ g Hg ] := f_taylor x (- (P * p * pm * (c * i))).
      split.
      + rewrite Hx' E1.
        have Hd : (P * p | - (P * p * pm * (c * i))) by exists (- (pm * (c * i))); lia.
        move: IH1; rewrite E1 => - [ a Ha ]; move: Hd => [ b Hb ].
        exists (a + b); lia.
      + rewrite E4 Hx' Hg Hc.
        have Hf' : f' x = P * u0 + w * (P * p) by rewrite -f'x0; lia.
        rewrite Hf'.
        exists (c * (- j - i * w) + pm * c * c * i * i * g).
        have Hz : u0 * i - 1 - j * p = 0 by lia.
        transitivity ((c * (- j - i * w) + pm * c * c * i * i * g) * (P * P * p * pm * p)
                      - c * P * P * p * pm * (u0 * i - 1 - j * p)); first by lia.
        rewrite Hz; lia.
  Qed.

  Lemma hs_coh (m : nat) : (p ^ (e + 1 + Z.of_nat m) | hs m.+1 - hs m).
  Proof using p_pos e_ge0. exists (- ((f (hs m) / p ^ (2 * e + 1 + Z.of_nat m)) * i)); rewrite /=; lia. Qed.

  Lemma hs_root (m : nat) : (p ^ (2 * e + 1 + Z.of_nat m) | f (hs m)).
  Proof using All. by have [] := hs_inv m. Qed.

  Lemma hs_near (m : nat) : (p ^ (e + 1) | hs m - x0).
  Proof using All. by have [] := hs_inv m. Qed.

  Theorem hensel_gen (k : nat) : exists x, (p ^ (e + 1) | x - x0) /\ (p ^ Z.of_nat k | f x).
  Proof using All.
    exists (hs k); split; first exact: hs_near.
    apply: dvd_trans_pz (hs_root k); lia.
  Qed.

End HenselGen.

(** The classical case e = 0 and the case p = 2, e = 1, with the
    inverse obtained from primality. *)

Section HenselPrime.

  Local Open Scope Z_scope.

  Theorem hensel_fun (p : Z) (f f' : Z -> Z) (x0 : Z) :
    Z.prime p ->
    (forall x h, exists g, f (x + h) = f x + h * f' x + h * h * g) ->
    (forall M x y, (M | x - y) -> (M | f' x - f' y)) ->
    (p | f x0) -> ~ (p | f' x0) ->
    forall k : nat, exists x, (p | x - x0) /\ (p ^ Z.of_nat k | f x).
  Proof.
    move=> Hp Ht Hc Hf Hf' k.
    have [ i Hi ] := inv_prime Hp Hf'.
    have Hp0 : 0 < p by have := Z.prime_ge_2 _ Hp; lia.
    have Hd : f' x0 = p ^ 0 * f' x0 by rewrite Z.pow_0_r; lia.
    have Hf1 : (p ^ (2 * 0 + 1) | f x0).
    { have -> : 2 * 0 + 1 = 1 by lia. by rewrite Z.pow_1_r. }
    have [ x [ H1 H2 ] ] := @hensel_gen p f f' Hp0 Ht Hc 0 x0 (f' x0) i ltac:(lia) Hd Hi Hf1 k.
    by exists x; split => //; move: H1; rewrite Z.pow_1_r.
  Qed.

  (* the general form: p^e exactly divides f'(x0), p^(2e+1) divides f(x0) *)
  Theorem hensel_fun_e (p : Z) (f f' : Z -> Z) (e x0 u0 : Z) :
    Z.prime p -> 0 <= e ->
    (forall x h, exists g, f (x + h) = f x + h * f' x + h * h * g) ->
    (forall M x y, (M | x - y) -> (M | f' x - f' y)) ->
    f' x0 = p ^ e * u0 -> ~ (p | u0) -> (p ^ (2 * e + 1) | f x0) ->
    forall k : nat, exists x, (p ^ (e + 1) | x - x0) /\ (p ^ Z.of_nat k | f x).
  Proof.
    move=> Hp He Ht Hc Hd Hu Hf k.
    have [ i Hi ] := inv_prime Hp Hu.
    have Hp0 : 0 < p by have := Z.prime_ge_2 _ Hp; lia.
    exact: (@hensel_gen p f f' Hp0 Ht Hc e x0 u0 i He Hd Hi Hf k).
  Qed.

End HenselPrime.

(** * 3. Integer polynomials (coefficient lists) and quadratics *)

Section Poly.

  Local Open Scope Z_scope.

  (* coefficients from the constant term upwards, Horner evaluation *)
  Fixpoint peval (l : list Z) (x : Z) : Z :=
    match l with
    | nil => 0
    | c :: l => c + x * peval l x
    end.

  (* the value of the formal derivative, by the product rule on Horner form *)
  Fixpoint pderv (l : list Z) (x : Z) : Z :=
    match l with
    | nil => 0
    | c :: l => peval l x + x * pderv l x
    end.

  Lemma pderv_example (c0 c1 c2 x : Z) : pderv (c0 :: c1 :: c2 :: nil) x = c1 + 2 * c2 * x.
  Proof. cbn [peval pderv]; lia. Qed.

  Lemma peval_taylor l x h : exists g, peval l (x + h) = peval l x + h * pderv l x + h * h * g.
  Proof.
    elim: l => [ | c l [ g IH ] ]; cbn [peval pderv]; first by exists 0; lia.
    exists (pderv l x + x * g + h * g); rewrite IH; lia.
  Qed.

  Lemma peval_cong M l x y : (M | x - y) -> (M | peval l x - peval l y).
  Proof.
    move=> [ d Hd ]; elim: l => [ | c l [ a Ha ] ]; cbn [peval pderv]; first by exists 0; lia.
    exists (x * a + d * peval l y).
    have -> : peval l x = peval l y + a * M by lia.
    have -> : x = y + d * M by lia.
    lia.
  Qed.

  Lemma pderv_cong M l x y : (M | x - y) -> (M | pderv l x - pderv l y).
  Proof.
    move=> Hxy; have [ d Hd ] := Hxy.
    elim: l => [ | c l [ a Ha ] ]; cbn [peval pderv]; first by exists 0; lia.
    have [ b Hb ] := peval_cong l Hxy.
    exists (b + x * a + d * pderv l y).
    have -> : pderv l x = pderv l y + a * M by lia.
    have -> : peval l x = peval l y + b * M by lia.
    have -> : x = y + d * M by lia.
    lia.
  Qed.

  (** Hensel's lemma for integer polynomials *)
  Theorem hensel_poly (p : Z) (l : list Z) (x0 : Z) :
    Z.prime p -> (p | peval l x0) -> ~ (p | pderv l x0) ->
    forall k : nat, exists x, (p | x - x0) /\ (p ^ Z.of_nat k | peval l x).
  Proof. move=> Hp; apply: hensel_fun => //; [ exact: peval_taylor | move=> M x y; exact: pderv_cong ]. Qed.

  Theorem hensel_poly_e (p : Z) (l : list Z) (e x0 u0 : Z) :
    Z.prime p -> 0 <= e -> pderv l x0 = p ^ e * u0 -> ~ (p | u0) -> (p ^ (2 * e + 1) | peval l x0) ->
    forall k : nat, exists x, (p ^ (e + 1) | x - x0) /\ (p ^ Z.of_nat k | peval l x).
  Proof. move=> Hp He; apply: hensel_fun_e => //; [ exact: peval_taylor | move=> M x y; exact: pderv_cong ]. Qed.

  (** Quadratics in one variable  A t^2 + B t + C *)

  Definition qf (A B C t : Z) : Z := A * t * t + B * t + C.

  Lemma qf_taylor A B C x h : exists g, qf A B C (x + h) = qf A B C x + h * (2 * A * x + B) + h * h * g.
  Proof. exists A; rewrite /qf; lia. Qed.

  Lemma qf'_cong A B M x y : (M | x - y) -> (M | (2 * A * x + B) - (2 * A * y + B)).
  Proof. move=> [ d Hd ]; exists (2 * A * d); lia. Qed.

  Theorem hensel_quad (p A B C t0 : Z) :
    Z.prime p -> (p | qf A B C t0) -> ~ (p | 2 * A * t0 + B) ->
    forall k : nat, exists t, (p | t - t0) /\ (p ^ Z.of_nat k | qf A B C t).
  Proof.
    move=> Hp H1 H2.
    exact: (@hensel_fun p (qf A B C) (fun t => 2 * A * t + B) t0 Hp (qf_taylor A B C)
              (fun M x y => @qf'_cong A B M x y) H1 H2).
  Qed.

  Theorem hensel_quad_e (p A B C e t0 u0 : Z) :
    Z.prime p -> 0 <= e -> 2 * A * t0 + B = p ^ e * u0 -> ~ (p | u0) ->
    (p ^ (2 * e + 1) | qf A B C t0) ->
    forall k : nat, exists t, (p ^ (e + 1) | t - t0) /\ (p ^ Z.of_nat k | qf A B C t).
  Proof.
    move=> Hp He H1 H2 H3.
    exact: (@hensel_fun_e p (qf A B C) (fun t => 2 * A * t + B) e t0 u0 Hp He (qf_taylor A B C)
              (fun M x y => @qf'_cong A B M x y) H1 H2 H3).
  Qed.

End Poly.

(** * 4. Square roots of units modulo p^k *)

Section SqrtLift.

  Local Open Scope Z_scope.

  (* a / c is a square modulo p^k (c a unit): a = z^2 c mod p^k *)
  Definition sqmodk (p : Z) (k : nat) (a c : Z) : Prop :=
    exists z, (p ^ Z.of_nat k | a - z * z * c).

  (* a / c is a p-adic square: a square modulo every power of p *)
  Definition usq (p a c : Z) : Prop := forall k : nat, sqmodk p k a c.

  Lemma qf_sq a c z : qf (- c) 0 a z = a - z * z * c.
  Proof. rewrite /qf; lia. Qed.

  (** odd p: a root mod p of a unit lifts *)
  Theorem sqrt_lift_odd (p a c z0 : Z) :
    Z.prime p -> ~ (p | 2) -> ~ (p | a) -> ~ (p | c) -> (p | a - z0 * z0 * c) ->
    forall k : nat, exists z, (p | z - z0) /\ (p ^ Z.of_nat k | a - z * z * c).
  Proof.
    move=> Hp H2 Ha Hc H0 k.
    have Hz0 : ~ (p | z0).
    { move=> [ w Hw ]; apply: Ha; move: H0 => [ v Hv ]; exists (v + w * z0 * c); lia. }
    have Hd : ~ (p | 2 * - c * z0 + 0).
    { rewrite Z.add_0_r.
      have -> : 2 * - c * z0 = 2 * (- c * z0) by lia.
      apply: prime_ndvd_mul => //; apply: prime_ndvd_mul => //.
      by move=> /Z.divide_opp_r. }
    have [ z [ H1 H3 ] ] := @hensel_quad p (- c) 0 a z0 Hp ltac:(by rewrite qf_sq) Hd k.
    by exists z; split => //; rewrite -qf_sq.
  Qed.

  (** p = 2: a = c mod 8 (c odd) lifts, with a root z = 1 mod 4 *)
  Theorem sqrt_lift_two (a c : Z) :
    ~ (2 | c) -> (8 | a - c) ->
    forall k : nat, exists z, (4 | z - 1) /\ (2 ^ Z.of_nat k | a - z * z * c).
  Proof.
    move=> Hc H8 k.
    have Hd : 2 * - c * 1 + 0 = 2 ^ 1 * (- c) by rewrite Z.pow_1_r; lia.
    have Hu : ~ (2 | - c) by move=> /Z.divide_opp_r.
    have H0 : (2 ^ (2 * 1 + 1) | qf (- c) 0 a 1) by rewrite qf_sq (_ : 2 ^ (2 * 1 + 1) = 8) //; move: H8 => [ w Hw ]; exists w; lia.
    have [ z [ H1 H3 ] ] := @hensel_quad_e 2 (- c) 0 a 1 1 (- c) Z.prime_2 ltac:(lia) Hd Hu H0 k.
    by exists z; split; [ move: H1; rewrite (_ : 2 ^ (1 + 1) = 4) | rewrite -qf_sq ].
  Qed.

  (** the coherent sequence of square roots (odd p): [i] is an inverse
      of the derivative -2 c z0 modulo p *)
  Definition sqrt_seq (p a c z0 i : Z) : nat -> Z := hs p (qf (- c) 0 a) 0 z0 i.

  Lemma sqrt_seq_spec (p a c z0 i : Z) :
    1 < p -> (p | a - z0 * z0 * c) -> (p | (- 2 * c * z0) * i - 1) ->
    forall m : nat,
      (p | sqrt_seq p a c z0 i m - z0) /\
      (p ^ (Z.of_nat m + 1) | a - sqrt_seq p a c z0 i m * sqrt_seq p a c z0 i m * c) /\
      (p ^ (Z.of_nat m + 1) | sqrt_seq p a c z0 i m.+1 - sqrt_seq p a c z0 i m).
  Proof.
    move=> Hp H0 Hi m.
    have Hp0 : 0 < p by lia.
    have Hd : 2 * - c * z0 + 0 = p ^ 0 * (- 2 * c * z0) by rewrite Z.pow_0_r; lia.
    have Hf1 : (p ^ (2 * 0 + 1) | qf (- c) 0 a z0).
    { have -> : 2 * 0 + 1 = 1 by lia. by rewrite Z.pow_1_r qf_sq. }
    have Ht := qf_taylor (- c) 0 a.
    have Hc : forall M x y, (M | x - y) -> (M | (fun t => 2 * - c * t + 0) x - (fun t => 2 * - c * t + 0) y).
    { move=> M x y; exact: qf'_cong. }
    have [ H1 H2 ] := @hs_inv p (qf (- c) 0 a) (fun t => 2 * - c * t + 0) Hp0 Ht Hc 0 z0 (- 2 * c * z0) i
                        ltac:(lia) Hd Hi Hf1 m.
    have H3 := @hs_coh p (qf (- c) 0 a) Hp0 0 z0 i ltac:(lia) m.
    rewrite /sqrt_seq -qf_sq; split; [ | split ].
    - by move: H1; rewrite Z.add_0_l Z.pow_1_r.
    - by move: H2; have -> : 2 * 0 + 1 + Z.of_nat m = Z.of_nat m + 1 by lia.
    - by move: H3; have -> : 0 + 1 + Z.of_nat m = Z.of_nat m + 1 by lia.
  Qed.

  (** the coherent sequence of square roots at p = 2 (c odd, a = c mod 8):
      the 2-adic variant with e = 1, starting from z0 = 1 *)
  Definition sqrt_seq2 (a c : Z) : nat -> Z := hs 2 (qf (- c) 0 a) 1 1 1.

  Lemma sqrt_seq2_spec (a c : Z) :
    ~ (2 | c) -> (8 | a - c) ->
    forall m : nat,
      (4 | sqrt_seq2 a c m - 1) /\
      (2 ^ (Z.of_nat m + 3) | a - sqrt_seq2 a c m * sqrt_seq2 a c m * c) /\
      (2 ^ (Z.of_nat m + 2) | sqrt_seq2 a c m.+1 - sqrt_seq2 a c m).
  Proof.
    move=> Hc H8 m.
    have Hd : 2 * - c * 1 + 0 = 2 ^ 1 * (- c) by rewrite Z.pow_1_r; lia.
    have Hi : (2 | - c * 1 - 1).
    { have [ w Hw ] : exists w, c = 2 * w + 1.
      { exists (c / 2); have := Z.mod_pos_bound c 2; have := Z.div_mod c 2.
        have : c mod 2 <> 0 by move=> H; apply: Hc; exact: (proj1 (Z.mod_divide c 2 ltac:(lia)) H).
        lia. }
      exists (- w - 1); lia. }
    have Hf1 : (2 ^ (2 * 1 + 1) | qf (- c) 0 a 1).
    { rewrite qf_sq (_ : 2 ^ (2 * 1 + 1) = 8) //; move: H8 => [ w Hw ]; exists w; lia. }
    have Ht := qf_taylor (- c) 0 a.
    have Hcg : forall M x y, (M | x - y) -> (M | (fun t => 2 * - c * t + 0) x - (fun t => 2 * - c * t + 0) y).
    { move=> M x y; exact: qf'_cong. }
    have [ H1 H2 ] := @hs_inv 2 (qf (- c) 0 a) (fun t => 2 * - c * t + 0) ltac:(lia) Ht Hcg 1 1 (- c) 1
                        ltac:(lia) Hd Hi Hf1 m.
    have H3 := @hs_coh 2 (qf (- c) 0 a) ltac:(lia) 1 1 1 ltac:(lia) m.
    rewrite /sqrt_seq2 -qf_sq; split; [ | split ].
    - by move: H1; rewrite (_ : 2 ^ (1 + 1) = 4).
    - by move: H2; have -> : 2 * 1 + 1 + Z.of_nat m = Z.of_nat m + 3 by lia.
    - by move: H3; have -> : 1 + 1 + Z.of_nat m = Z.of_nat m + 2 by lia.
  Qed.

  (** the finite criteria *)
  Theorem usq_odd (p a c : Z) :
    Z.prime p -> ~ (p | 2) -> ~ (p | a) -> ~ (p | c) ->
    usq p a c <-> exists z, (p | a - z * z * c).
  Proof.
    move=> Hp H2 Ha Hc; split.
    - by move=> /(_ 1%nat) [ z Hz ]; exists z; move: Hz; rewrite (_ : Z.of_nat 1 = 1) // Z.pow_1_r.
    - move=> [ z0 H0 ] k.
      have [ z [ _ Hz ] ] := sqrt_lift_odd Hp H2 Ha Hc H0 k.
      by exists z.
  Qed.

  Theorem usq_two (a c : Z) :
    ~ (2 | a) -> ~ (2 | c) -> usq 2 a c <-> (8 | a - c).
  Proof.
    move=> Ha Hc; split.
    - move=> /(_ 3%nat) [ z Hz ]; move: Hz; rewrite (_ : 2 ^ Z.of_nat 3 = 8) // => Hz.
      have Hz2 : ~ (2 | z).
      { move=> [ w Hw ]; apply: Ha; move: Hz => [ v Hv ]; exists (4 * v + w * z * c); lia. }
      have [ s Hs ] := odd_sq8 Hz2.
      move: Hz => [ v Hv ]; exists (v + s * c); lia.
    - move=> H8 k.
      have [ z [ _ Hz ] ] := sqrt_lift_two Hc H8 k.
      by exists z.
  Qed.

  (** the trivial direction: a square mod p^k is a square mod p^j, j <= k *)
  Lemma sqmodk_le (p : Z) (j k : nat) (a c : Z) : (j <= k)%coq_nat -> sqmodk p k a c -> sqmodk p j a c.
  Proof. move=> Hjk [ z Hz ]; exists z; apply: dvd_trans_pz Hz; lia. Qed.

  (** multiplicativity *)
  Lemma usq_mul (p a c a' c' : Z) : usq p a c -> usq p a' c' -> usq p (a * a') (c * c').
  Proof.
    move=> H H' k; have [ z [ u Hu ] ] := H k; have [ z' [ u' Hu' ] ] := H' k.
    exists (z * z'); exists (u * a' + z * z * c * u').
    have -> : a * a' - z * z' * (z * z') * (c * c') = (a - z * z * c) * a' + z * z * c * (a' - z' * z' * c') by lia.
    rewrite Hu Hu'; lia.
  Qed.

  Lemma usq_refl (p c : Z) : usq p c c.
  Proof. move=> k; exists 1; exists 0; lia. Qed.

  Lemma usq_sq (p n c : Z) : usq p (n * n * c) c.
  Proof. move=> k; exists n; exists 0; lia. Qed.

  (** transfer along an equation  n^2 a' c = d^2 a c'  with n, c units *)
  Theorem usq_transfer (p a c a' c' n d : Z) :
    Z.prime p -> ~ (p | n) -> ~ (p | c) -> n * n * a' * c = d * d * a * c' ->
    usq p a c -> usq p a' c'.
  Proof.
    move=> Hp Hn Hc E H k.
    set P := p ^ Z.of_nat k.
    have [ z [ u Hu ] ] := H k.
    have [ ni [ s Hs ] ] := @inv_pz p (Z.of_nat k) n Hp ltac:(lia) Hn.
    have Hr : (P | c * (n * n * a' - d * z * d * z * c')).
    { exists (d * d * c' * u).
      transitivity (d * d * c' * (a - z * z * c) + (n * n * a' * c - d * d * a * c')); first lia.
      rewrite Hu E; lia. }
    have [ r Hr' ] := dvd_cancel (@coprime_pz p (Z.of_nat k) c Hp ltac:(lia) Hc) Hr.
    exists (ni * d * z); exists (- a' * (n * ni + 1) * s + ni * ni * r).
    transitivity (- a' * (n * ni + 1) * (n * ni - 1) + ni * ni * (n * n * a' - d * z * d * z * c')); first lia.
    rewrite Hs Hr' -/P; lia.
  Qed.

End SqrtLift.

(** * 5. Local solvability of quadrics by Hensel

    A solution modulo p (resp. 8) with a nonvanishing partial derivative
    (a unit, resp. twice an odd number) in one variable lifts to
    solutions modulo p^k for all k, congruent in that variable modulo p
    (resp. 4); the lifted variable stays a unit, so the solutions are
    primitive. Two instances: the diagonal ternary form, and the
    2-covering of y^2 = (x - e1)(x - e2)(x - e3) (PP1_DESIGN.md, 1.4)

      C_d :  d1 z1^2 - d2 z2^2    = (e2 - e1) z0^2,
             d1 z1^2 - d1 d2 z3^2 = (e3 - e1) z0^2,

    lifted in z2 and z3 (each occurs in one equation only). *)

Section Quadrics.

  Local Open Scope Z_scope.

  Lemma unit_of_cong (p x y : Z) : (p | x - y) -> ~ (p | y) -> ~ (p | x).
  Proof. move=> [ a Ha ] Hy [ b Hb ]; apply: Hy; exists (b - a); lia. Qed.

  (* lifting the last variable of  a1 x1^2 + a2 x2^2 + a3 x3^2 *)
  Theorem diag3_lift (p a1 a2 a3 x1 x2 x3 : Z) :
    Z.prime p -> (p | a1 * x1 * x1 + a2 * x2 * x2 + a3 * x3 * x3) -> ~ (p | 2 * a3 * x3) ->
    forall k : nat, exists y3, (p | y3 - x3) /\ ~ (p | y3) /\
      (p ^ Z.of_nat k | a1 * x1 * x1 + a2 * x2 * x2 + a3 * y3 * y3).
  Proof.
    move=> Hp H0 Hd k.
    have Hq : forall t, qf a3 0 (a1 * x1 * x1 + a2 * x2 * x2) t = a1 * x1 * x1 + a2 * x2 * x2 + a3 * t * t.
    { move=> t; rewrite /qf; lia. }
    have Hx3 : ~ (p | x3) by move=> H; apply: Hd; apply: Z.divide_mul_r.
    have H0' : (p | qf a3 0 (a1 * x1 * x1 + a2 * x2 * x2) x3) by rewrite Hq.
    have Hd' : ~ (p | 2 * a3 * x3 + 0) by rewrite Z.add_0_r.
    have [ y [ H1 H2 ] ] := hensel_quad Hp H0' Hd' k.
    exists y; split => //; split; first exact: unit_of_cong H1 Hx3.
    by rewrite -Hq.
  Qed.

  Theorem diag3_lift_two (a1 a2 a3 x1 x2 x3 : Z) :
    (8 | a1 * x1 * x1 + a2 * x2 * x2 + a3 * x3 * x3) -> ~ (2 | a3 * x3) ->
    forall k : nat, exists y3, (4 | y3 - x3) /\ ~ (2 | y3) /\
      (2 ^ Z.of_nat k | a1 * x1 * x1 + a2 * x2 * x2 + a3 * y3 * y3).
  Proof.
    move=> H0 Hd k.
    have Hq : forall t, qf a3 0 (a1 * x1 * x1 + a2 * x2 * x2) t = a1 * x1 * x1 + a2 * x2 * x2 + a3 * t * t.
    { move=> t; rewrite /qf; lia. }
    have Hx3 : ~ (2 | x3) by move=> H; apply: Hd; apply: Z.divide_mul_r.
    have E : 2 * a3 * x3 + 0 = 2 ^ 1 * (a3 * x3) by rewrite Z.pow_1_r; lia.
    have H0' : (2 ^ (2 * 1 + 1) | qf a3 0 (a1 * x1 * x1 + a2 * x2 * x2) x3) by rewrite Hq.
    have [ y [ H1 H2 ] ] := hensel_quad_e Z.prime_2 Z.le_0_1 E Hd H0' k.
    move: H1; rewrite (_ : 2 ^ (1 + 1) = 4) // => H1.
    exists y; split => //; split.
    - apply: unit_of_cong Hx3; move: H1 => [ w Hw ]; exists (2 * w); lia.
    - by rewrite -Hq.
  Qed.

  Definition cov1 (d1 d2 e21 z0 z1 z2 : Z) : Z := d1 * z1 * z1 - d2 * z2 * z2 - e21 * z0 * z0.
  Definition cov2 (d1 d2 e31 z0 z1 z3 : Z) : Z := d1 * z1 * z1 - d1 * d2 * z3 * z3 - e31 * z0 * z0.

  Lemma cov1_qf d1 d2 e21 z0 z1 t : cov1 d1 d2 e21 z0 z1 t = qf (- d2) 0 (d1 * z1 * z1 - e21 * z0 * z0) t.
  Proof. rewrite /cov1 /qf; lia. Qed.

  Lemma cov2_qf d1 d2 e31 z0 z1 t : cov2 d1 d2 e31 z0 z1 t = qf (- (d1 * d2)) 0 (d1 * z1 * z1 - e31 * z0 * z0) t.
  Proof. rewrite /cov2 /qf; lia. Qed.

  Theorem cov_lift_odd (p d1 d2 e21 e31 z0 z1 z2 z3 : Z) :
    Z.prime p -> ~ (p | 2) ->
    (p | cov1 d1 d2 e21 z0 z1 z2) -> (p | cov2 d1 d2 e31 z0 z1 z3) ->
    ~ (p | d2 * z2) -> ~ (p | d1 * d2 * z3) ->
    forall k : nat, exists y2 y3,
      (p | y2 - z2) /\ (p | y3 - z3) /\ ~ (p | y2) /\ ~ (p | y3) /\
      (p ^ Z.of_nat k | cov1 d1 d2 e21 z0 z1 y2) /\ (p ^ Z.of_nat k | cov2 d1 d2 e31 z0 z1 y3).
  Proof.
    move=> Hp H2 Hc1 Hc2 Hd2 Hd3 k.
    have Hz2 : ~ (p | z2) by move=> H; apply: Hd2; apply: Z.divide_mul_r.
    have Hz3 : ~ (p | z3) by move=> H; apply: Hd3; apply: Z.divide_mul_r.
    have D2 : ~ (p | 2 * - d2 * z2 + 0).
    { have -> : 2 * - d2 * z2 + 0 = 2 * - (d2 * z2) by lia.
      apply: prime_ndvd_mul => //; by move=> /Z.divide_opp_r. }
    have D3 : ~ (p | 2 * - (d1 * d2) * z3 + 0).
    { have -> : 2 * - (d1 * d2) * z3 + 0 = 2 * - (d1 * d2 * z3) by lia.
      apply: prime_ndvd_mul => //; by move=> /Z.divide_opp_r. }
    move: Hc1 Hc2; rewrite cov1_qf cov2_qf => Hc1 Hc2.
    have [ y2 [ H21 H22 ] ] := hensel_quad Hp Hc1 D2 k.
    have [ y3 [ H31 H32 ] ] := hensel_quad Hp Hc2 D3 k.
    exists y2, y3; rewrite !cov1_qf !cov2_qf.
    split; first done; split; first done.
    split; first exact: unit_of_cong H21 Hz2.
    by split; first exact: unit_of_cong H31 Hz3.
  Qed.

  Theorem cov_lift_two (d1 d2 e21 e31 z0 z1 z2 z3 : Z) :
    (8 | cov1 d1 d2 e21 z0 z1 z2) -> (8 | cov2 d1 d2 e31 z0 z1 z3) ->
    ~ (2 | d2 * z2) -> ~ (2 | d1 * d2 * z3) ->
    forall k : nat, exists y2 y3,
      (4 | y2 - z2) /\ (4 | y3 - z3) /\ ~ (2 | y2) /\ ~ (2 | y3) /\
      (2 ^ Z.of_nat k | cov1 d1 d2 e21 z0 z1 y2) /\ (2 ^ Z.of_nat k | cov2 d1 d2 e31 z0 z1 y3).
  Proof.
    move=> Hc1 Hc2 Hd2 Hd3 k.
    have Hz2 : ~ (2 | z2) by move=> H; apply: Hd2; apply: Z.divide_mul_r.
    have Hz3 : ~ (2 | z3) by move=> H; apply: Hd3; apply: Z.divide_mul_r.
    have E2 : 2 * - d2 * z2 + 0 = 2 ^ 1 * (- (d2 * z2)) by rewrite Z.pow_1_r; lia.
    have E3 : 2 * - (d1 * d2) * z3 + 0 = 2 ^ 1 * (- (d1 * d2 * z3)) by rewrite Z.pow_1_r; lia.
    have U2 : ~ (2 | - (d2 * z2)) by move=> /Z.divide_opp_r.
    have U3 : ~ (2 | - (d1 * d2 * z3)) by move=> /Z.divide_opp_r.
    move: Hc1 Hc2; rewrite cov1_qf cov2_qf (_ : 8 = 2 ^ (2 * 1 + 1)) // => Hc1 Hc2.
    have [ y2 [ H21 H22 ] ] := hensel_quad_e Z.prime_2 Z.le_0_1 E2 U2 Hc1 k.
    have [ y3 [ H31 H32 ] ] := hensel_quad_e Z.prime_2 Z.le_0_1 E3 U3 Hc2 k.
    move: H21 H31; rewrite (_ : 2 ^ (1 + 1) = 4) // => H21 H31.
    exists y2, y3; rewrite !cov1_qf !cov2_qf.
    split; first done; split; first done.
    split; first by apply: unit_of_cong Hz2; move: H21 => [ w Hw ]; exists (2 * w); lia.
    split; first by apply: unit_of_cong Hz3; move: H31 => [ w Hw ]; exists (2 * w); lia.
    done.
  Qed.

End Quadrics.

(** * 6. Chinese remainder theorem with explicit precisions *)

Section CRT.

  Local Open Scope Z_scope.

  Lemma crt2 (m1 m2 r1 r2 : Z) : Z.coprime m1 m2 -> exists x, (m1 | x - r1) /\ (m2 | x - r2).
  Proof.
    move=> /Z.Bezout_coprime [ u [ v H ] ].
    have H0 : u * m1 + v * m2 - 1 = 0 by lia.
    exists (r1 * v * m2 + r2 * u * m1); split.
    - exists ((r2 - r1) * u).
      transitivity (r1 * (u * m1 + v * m2 - 1) + (r2 - r1) * u * m1); first lia.
      rewrite H0; lia.
    - exists ((r1 - r2) * v).
      transitivity (r2 * (u * m1 + v * m2 - 1) + (r1 - r2) * v * m2); first lia.
      rewrite H0; lia.
  Qed.

  Fixpoint pw_coprime (l : list Z) : Prop :=
    match l with
    | nil => True
    | m :: l => Forall (Z.coprime m) l /\ pw_coprime l
    end.

  Fixpoint prodZ (l : list Z) : Z :=
    match l with
    | nil => 1
    | m :: l => m * prodZ l
    end.

  Lemma coprime_prodZ m l : Forall (Z.coprime m) l -> Z.coprime m (prodZ l).
  Proof.
    elim: l => [ | a l IH ] H; cbn [prodZ]; first exact: Z.coprime_1_r.
    inversion H; subst; apply: Z.coprime_mul_r => //; exact: IH.
  Qed.

  Lemma dvd_prodZ m l : In m l -> (m | prodZ l).
  Proof.
    elim: l => [ | a l IH ] //= [ <- | H ]; first exact: Z.divide_factor_l.
    apply: Z.divide_mul_r; exact: IH.
  Qed.

  (** CRT for a list of (modulus, residue) pairs with pairwise coprime moduli *)
  Theorem crt_list (l : list (Z * Z)) :
    pw_coprime (map fst l) -> exists x, Forall (fun mr => (fst mr | x - snd mr)) l.
  Proof.
    elim: l => [ | [ m r ] l IH ] /=; first by exists 0.
    move=> [ Hc Hl ]; have [ x' Hx' ] := IH Hl.
    have [ x [ H1 H2 ] ] := crt2 r x' (coprime_prodZ Hc).
    exists x; constructor => //=.
    apply/Forall_forall => [ [ mi ri ] Hin ] /=.
    move: Hx' => /Forall_forall /(_ _ Hin) /= Hi.
    apply: dvd_sub_trans Hi; apply: Z.divide_trans H2.
    apply: dvd_prodZ; apply/in_map_iff; by exists (mi, ri).
  Qed.

  Lemma coprime_prime_pows (p q a b : Z) : Z.prime p -> Z.prime q -> p <> q -> 0 <= a -> 0 <= b ->
    Z.coprime (p ^ a) (q ^ b).
  Proof.
    move=> Hp Hq Hpq Ha Hb; apply: Z.coprime_pow_l => //; apply: Z.Symmetric_coprime.
    apply: Z.coprime_pow_l => //; apply: Z.Symmetric_coprime.
    by apply: Z.coprime_prime_l => // /(Z.divide_prime_prime _ _ Hp Hq).
  Qed.

  (** a target (p, k, r): x = r mod p^k *)
  Definition tgt_ok (x : Z) (t : Z * nat * Z) : Prop :=
    let '(p, k, r) := t in (p ^ Z.of_nat k | x - r).

  Definition tgt_p (t : Z * nat * Z) : Z := let '(p, _, _) := t in p.

  (** CRT for finitely many distinct primes with explicit precisions *)
  Theorem crt_primes (l : list (Z * nat * Z)) :
    NoDup (map tgt_p l) -> Forall (fun t => Z.prime (tgt_p t)) l ->
    exists x, Forall (tgt_ok x) l.
  Proof.
    move=> Hnd Hpr.
    have Hc : pw_coprime (map fst (map (fun t => let '(p, k, r) := t in (p ^ Z.of_nat k, r)) l)).
    { elim: l Hnd Hpr => [ | [ [ p k ] r ] l IH ] //=.
      move=> /NoDup_cons_iff [ Hnin Hnd ] /Forall_cons_iff [ Hp Hpr ]; split; last exact: IH.
      apply/Forall_forall => m /in_map_iff [ [ m' r' ] [ <- /in_map_iff [ [ [ q j ] s ] [ Eq Hin ] ] ] ] /=.
      move: Eq => [ <- _ ].
      have Hq : Z.prime q by move: Hpr => /Forall_forall /(_ _ Hin).
      apply: coprime_prime_pows => //; try lia.
      move=> E; apply: Hnin; apply/in_map_iff; exists (q, j, s); by rewrite E. }
    have [ x Hx ] := crt_list Hc.
    exists x; apply/Forall_forall => [ [ [ p k ] r ] Hin ] /=.
    move: Hx => /Forall_forall /(_ (p ^ Z.of_nat k, r)); apply.
    apply/in_map_iff; by exists (p, k, r).
  Qed.

End CRT.

(** * 7. Stripping powers of p from integer equations *)

Section Strip.

  Local Open Scope Z_scope.

  Lemma pow_unit_eq (p A B : Z) (i j : nat) : Z.prime p -> ~ (p | A) -> ~ (p | B) ->
    p ^ Z.of_nat i * A = p ^ Z.of_nat j * B -> i = j.
  Proof.
    move=> Hp HA HB E.
    have Hp2 := Z.prime_ge_2 _ Hp.
    have Hnz : forall n : nat, p ^ Z.of_nat n <> 0 by move=> n; apply: pz_neq0; lia.
    have Hsplit : forall a t : nat, p ^ Z.of_nat (a + S t)%coq_nat = p ^ Z.of_nat a * (p * p ^ Z.of_nat t).
    { move=> a t; rewrite Nat2Z.inj_add Nat2Z.inj_succ Z.pow_add_r; try lia.
      by rewrite Z.pow_succ_r; lia. }
    case: (Nat.lt_total i j) => [ Hij | [ // | Hij ] ].
    - exfalso; apply: HA.
      have [ t Et ] : exists t, j = (i + S t)%coq_nat by exists (Nat.sub (Nat.sub j i) 1); lia.
      move: E; rewrite Et Hsplit => E.
      have -> : A = p * (p ^ Z.of_nat t * B).
      { apply/(Z.mul_cancel_l _ _ (p ^ Z.of_nat i) (Hnz i)); lia. }
      exact: Z.divide_factor_l.
    - exfalso; apply: HB.
      have [ t Et ] : exists t, i = (j + S t)%coq_nat by exists (Nat.sub (Nat.sub i j) 1); lia.
      move: E; rewrite Et Hsplit => E.
      have -> : B = p * (p ^ Z.of_nat t * A).
      { apply/(Z.mul_cancel_l _ _ (p ^ Z.of_nat j) (Hnz j)); lia. }
      exact: Z.divide_factor_l.
  Qed.

  Lemma vu_dec (p z : Z) : Z.prime p -> z <> 0 ->
    exists (i : nat) (u : Z), z = p ^ Z.of_nat i * u /\ ~ (p | u).
  Proof.
    move=> Hp Hz; have Hp2 := Z.prime_ge_2 _ Hp.
    exists (fst (vu p z)), (snd (vu p z)); split; first by apply: vu_eq; lia.
    move=> H; apply: (vu_unit Hp2 Hz); apply/Z.mod_divide => //; lia.
  Qed.

  (* N^2 U = D^2 V with units U, V: the same with units N1, D1 *)
  Lemma strip_sq (p N D U V : Z) : Z.prime p -> N <> 0 -> D <> 0 -> ~ (p | U) -> ~ (p | V) ->
    N * N * U = D * D * V -> exists N1 D1, ~ (p | N1) /\ ~ (p | D1) /\ N1 * N1 * U = D1 * D1 * V.
  Proof.
    move=> Hp HN HD HU HV E.
    have Hp2 := Z.prime_ge_2 _ Hp.
    have [ i [ N1 [ EN HN1 ] ] ] := vu_dec Hp HN.
    have [ j [ D1 [ ED HD1 ] ] ] := vu_dec Hp HD.
    exists N1, D1; do 2 (split => //).
    have Pii : forall n : nat, p ^ Z.of_nat (n + n)%coq_nat = p ^ Z.of_nat n * p ^ Z.of_nat n.
    { by move=> n; rewrite Nat2Z.inj_add; apply: Z.pow_add_r; lia. }
    have E2 : p ^ Z.of_nat (i + i)%coq_nat * (N1 * N1 * U) = p ^ Z.of_nat (j + j)%coq_nat * (D1 * D1 * V).
    { rewrite !Pii; move: E; rewrite EN ED; lia. }
    have Hij := pow_unit_eq Hp (prime_ndvd_mul Hp (prime_ndvd_mul Hp HN1 HN1) HU)
                  (prime_ndvd_mul Hp (prime_ndvd_mul Hp HD1 HD1) HV) E2.
    rewrite -Hij in E2.
    have Hnz : p ^ Z.of_nat (i + i)%coq_nat <> 0 by apply: pz_neq0; lia.
    by apply/(Z.mul_cancel_l _ _ _ Hnz).
  Qed.

  (* p N^2 U = D^2 V with units U, V is impossible *)
  Lemma strip_odd (p N D U V : Z) : Z.prime p -> N <> 0 -> D <> 0 -> ~ (p | U) -> ~ (p | V) ->
    p * (N * N * U) <> D * D * V.
  Proof.
    move=> Hp HN HD HU HV E.
    have Hp2 := Z.prime_ge_2 _ Hp.
    have [ i [ N1 [ EN HN1 ] ] ] := vu_dec Hp HN.
    have [ j [ D1 [ ED HD1 ] ] ] := vu_dec Hp HD.
    have Pii : forall n : nat, p ^ Z.of_nat (n + n)%coq_nat = p ^ Z.of_nat n * p ^ Z.of_nat n.
    { by move=> n; rewrite Nat2Z.inj_add; apply: Z.pow_add_r; lia. }
    have E2 : p ^ Z.of_nat (S (i + i)%coq_nat) * (N1 * N1 * U) = p ^ Z.of_nat (j + j)%coq_nat * (D1 * D1 * V).
    { rewrite Nat2Z.inj_succ Z.pow_succ_r; first lia.
      rewrite !Pii; move: E; rewrite EN ED; lia. }
    have := pow_unit_eq Hp (prime_ndvd_mul Hp (prime_ndvd_mul Hp HN1 HN1) HU)
              (prime_ndvd_mul Hp (prime_ndvd_mul Hp HD1 HD1) HV) E2.
    lia.
  Qed.

End Strip.

(** * 8. Bridges between nat primes, Z, int and rat *)

Section Bridges.

  Lemma primeZ (q : nat) : prime q -> Z.prime (Z.of_nat q).
  Proof.
    move=> /primeP [ Hq1 H ]; move/ssrnat.ltP: Hq1 => Hq1.
    split; first lia.
    move=> n Hn [ k Hk ].
    have Hk0 : (0 < k)%ZZ by nia.
    have Hd : (Z.to_nat n %| q)%N.
    { apply/dvdnP; exists (Z.to_nat k); rewrite -multE; lia. }
    by move: (H _ Hd) => /orP [ /eqP | /eqP ] E; lia.
  Qed.

  Lemma zr_Z (a : Z) : zr a = (Z_to_int a)%:~R.
  Proof. by rewrite -zr_iz iz_Z_to_int. Qed.

  Lemma qunit_ndvd (q : nat) (a : Z) : qunit q a -> ~~ (q %| `|Z_to_int a|)%N.
  Proof.
    move=> Ha; apply/negP => H; apply: Ha.
    have : (q%:Z %| Z_to_int a)%Z by rewrite dvdzE.
    move=> /dvdzP [ t Ht ]; exists (int_to_Z t).
    by rewrite -(iz_Z_to_int a) Ht iz_mul iz_nat.
  Qed.

  Lemma qunit_neq0 (q : nat) (a : Z) : qunit q a -> a <> 0%ZZ.
  Proof. by move=> Ha E; apply: Ha; rewrite E; exact: Z.divide_0_r. Qed.

  Lemma vqr_zr_unit (q : nat) (a : Z) : qunit q a -> vqr q (zr a) = 0.
  Proof. by move=> Ha; rewrite zr_Z vqr_int logn_ndvd //; exact: qunit_ndvd. Qed.

  Lemma zr_pow (b : Z) (n : nat) : zr (b ^ Z.of_nat n)%ZZ = zr b ^+ n.
  Proof.
    elim: n => [ | n IH ]; first by rewrite expr0 Z.pow_0_r zr1.
    by rewrite Nat2Z.inj_succ Z.pow_succ_r ?zr_mul ?IH ?exprS //; lia.
  Qed.

  Lemma vqr_zr_dec (q : nat) (z u : Z) (i : nat) : prime q -> qunit q u ->
    z = (Z.of_nat q ^ Z.of_nat i * u)%ZZ -> vqr q (zr z) = i%:Z.
  Proof.
    move=> Hq Hu ->.
    have Hq0 : (0 < Z.of_nat q)%ZZ by have := Z.prime_ge_2 _ (primeZ Hq); lia.
    have Hu0 := qunit_neq0 Hu.
    have Hp0 : (Z.of_nat q ^ Z.of_nat i <> 0)%ZZ by apply: pz_neq0; lia.
    by rewrite zr_mul vqrM ?zr_neq0 // (vqr_zr_unit Hu) addr0 zr_pow zr_nat vqr_expq.
  Qed.

  Lemma vqr_zr_ge (q : nat) (z : Z) (j : nat) : prime q -> z <> 0%ZZ ->
    (Z.of_nat q ^ Z.of_nat j | z)%ZZ -> j%:Z <= vqr q (zr z).
  Proof.
    move=> Hq Hz [ w Hw ].
    have Hq0 : (0 < Z.of_nat q)%ZZ by have := Z.prime_ge_2 _ (primeZ Hq); lia.
    have Hw0 : w <> 0%ZZ by move=> E; apply: Hz; rewrite Hw E.
    have Hp0 : (Z.of_nat q ^ Z.of_nat j <> 0)%ZZ by apply: pz_neq0; lia.
    rewrite Hw zr_mul vqrM ?zr_neq0 //.
    by rewrite zr_pow zr_nat vqr_expq // addrC lerDl zr_Z vqr_int.
  Qed.

  Lemma zr_frac_eq (A B C D : Z) : B <> 0%ZZ -> D <> 0%ZZ ->
    zr A / zr B = zr C / zr D -> (A * D = C * B)%ZZ.
  Proof.
    move=> HB HD /eqP; rewrite eqr_div ?zr_neq0 // -!zr_mul => /eqP; exact: zr_inj.
  Qed.

  Lemma rep_frac (n d a c : Z) : d <> 0%ZZ -> c <> 0%ZZ ->
    (zr n / zr d) ^+ 2 * (zr a / zr c) = zr (n * n * a) / zr (d * d * c).
  Proof. by move=> Hd Hc; rewrite !zr_mul expr2 !mulf_div. Qed.

End Bridges.

(** * 9. Local square classes over Q

    [is_locsq q x]: x = y^2 a / c with q-units a, c such that a / c is a
    square modulo q^k for EVERY k ("x in Q_q^{x2}" without q-adic
    numbers). [PhiCovering.locsq] asks the same modulo q only (resp.
    modulo 8 at q = 2). By Hensel the two agree, and both are
    independent of the representation; the finite criterion is
    "v_q(x) even and unit part a square mod q (resp. = 1 mod 8)". *)

Definition is_locsq (q : nat) (x : rat) : Prop :=
  exists (y : rat) (a c : Z),
    y != 0 /\ qunit q a /\ qunit q c /\ x = y ^+ 2 * (zr a / zr c) /\ usq (Z.of_nat q) a c.

(* the real place: x is a square in R *)
Definition locsq_inf (x : rat) : Prop := 0 < x.

Section LocSq.

  Variable q : nat.
  Hypothesis q_prime : prime q.

  Local Abbreviation qZ := (Z.of_nat q).

  Lemma qZ_prime : Z.prime qZ.
  Proof using q_prime. exact: primeZ. Qed.

  Lemma qZ_gt0 : (0 < qZ)%ZZ.
  Proof using q_prime. have := Z.prime_ge_2 _ qZ_prime; lia. Qed.

  Lemma neq0_mul (a b : Z) : a <> 0%ZZ -> b <> 0%ZZ -> (a * b <> 0)%ZZ.
  Proof. by move=> Ha Hb; apply/Z.neq_mul_0. Qed.

  Lemma qunit_mul (a b : Z) : qunit q a -> qunit q b -> qunit q (a * b).
  Proof using q_prime. exact: prime_ndvd_mul qZ_prime. Qed.

  Theorem usq_sqmod (a c : Z) : qunit q a -> qunit q c -> usq qZ a c <-> sqmod q a c.
  Proof using q_prime.
    move=> Ha Hc; rewrite /sqmod; case: eqP => [ Eq | Hq2 ].
    - move: Ha Hc; rewrite /qunit Eq => Ha Hc; exact: usq_two.
    - apply: usq_odd => //; first exact: qZ_prime.
      move=> /(Z.divide_prime_prime _ _ qZ_prime Z.prime_2) E; apply: Hq2; lia.
  Qed.

  Theorem locsq_is_locsq (x : rat) : locsq q x <-> is_locsq q x.
  Proof using q_prime.
    split => - [ y [ a [ c [ Hy [ Ha [ Hc [ Ex H ] ] ] ] ] ] ]; exists y, a, c;
      (split; first done); (split; first done); (split; first done); (split; first done).
    - by apply/usq_sqmod.
    - by apply/usq_sqmod.
  Qed.

  (** representation independence *)
  Lemma rep_usq (y y' : rat) (a c a' c' : Z) : y != 0 -> y' != 0 ->
    qunit q a -> qunit q c -> qunit q a' -> qunit q c' ->
    y ^+ 2 * (zr a / zr c) = y' ^+ 2 * (zr a' / zr c') -> usq qZ a c -> usq qZ a' c'.
  Proof using q_prime.
    move=> Hy Hy' Ha Hc Ha' Hc' E H.
    have [ n [ d [ Hn [ Hd Ey ] ] ] ] := rat_frac Hy.
    have [ n' [ d' [ Hn' [ Hd' Ey' ] ] ] ] := rat_frac Hy'.
    have Hc0 := qunit_neq0 Hc; have Hc0' := qunit_neq0 Hc'.
    move: E; rewrite Ey Ey' !rep_frac // => /zr_frac_eq.
    move=> /(_ (neq0_mul (neq0_mul Hd Hd) Hc0) (neq0_mul (neq0_mul Hd' Hd') Hc0')) E.
    have E' : ((n * d') * (n * d') * (a * c') = (n' * d) * (n' * d) * (a' * c))%ZZ by lia.
    have [ N1 [ D1 [ HN1 [ HD1 E1 ] ] ] ] := strip_sq qZ_prime (neq0_mul Hn Hd') (neq0_mul Hn' Hd)
      (qunit_mul Ha Hc') (qunit_mul Ha' Hc) E'.
    have E2 : (D1 * D1 * a' * c = N1 * N1 * a * c')%ZZ by lia.
    exact: (@usq_transfer qZ a c a' c' D1 N1 qZ_prime HD1 Hc E2 H).
  Qed.

  Lemma rep_parity (y y' : rat) (a c a' c' : Z) : y != 0 -> y' != 0 ->
    qunit q a -> qunit q c -> qunit q a' -> qunit q c' ->
    q%:R * (y ^+ 2 * (zr a / zr c)) <> y' ^+ 2 * (zr a' / zr c').
  Proof using q_prime.
    move=> Hy Hy' Ha Hc Ha' Hc' E.
    have [ n [ d [ Hn [ Hd Ey ] ] ] ] := rat_frac Hy.
    have [ n' [ d' [ Hn' [ Hd' Ey' ] ] ] ] := rat_frac Hy'.
    have Hc0 := qunit_neq0 Hc; have Hc0' := qunit_neq0 Hc'.
    move: E; rewrite Ey Ey' !rep_frac // -zr_nat mulrA -zr_mul => /zr_frac_eq.
    move=> /(_ (neq0_mul (neq0_mul Hd Hd) Hc0) (neq0_mul (neq0_mul Hd' Hd') Hc0')) E.
    have E' : (qZ * ((n * d') * (n * d') * (a * c')) = (n' * d) * (n' * d) * (a' * c))%ZZ by lia.
    exact: (strip_odd qZ_prime (neq0_mul Hn Hd') (neq0_mul Hn' Hd) (qunit_mul Ha Hc') (qunit_mul Ha' Hc) E').
  Qed.

  Lemma pw_even (p : Z) (i s : nat) : i = (s + s)%coq_nat -> (p ^ Z.of_nat i = p ^ Z.of_nat s * p ^ Z.of_nat s)%ZZ.
  Proof. move=> ->; rewrite Nat2Z.inj_add; apply: Z.pow_add_r; lia. Qed.

  Lemma pw_odd (p : Z) (i s : nat) : i = S (s + s)%coq_nat -> (p ^ Z.of_nat i = p * (p ^ Z.of_nat s * p ^ Z.of_nat s))%ZZ.
  Proof. move=> ->; rewrite Nat2Z.inj_succ Z.pow_succ_r; first lia. by rewrite -(pw_even p (erefl _)). Qed.

  Lemma even_or_odd (i : nat) : (exists s, i = (s + s)%coq_nat) \/ (exists s, i = S (s + s)%coq_nat).
  Proof. case: (Nat.Even_or_Odd i) => [ [ s Hs ] | [ s Hs ] ]; [ left | right ]; exists s; lia. Qed.

  Lemma vu_qunit (z : Z) : z <> 0%ZZ -> qunit q (snd (vu qZ z)).
  Proof using q_prime.
    move=> Hz H; have Hq2 := Z.prime_ge_2 _ qZ_prime.
    apply: (vu_unit Hq2 Hz); apply/Z.mod_divide => //; lia.
  Qed.

  (** the representation of N / D from the q-adic decompositions of N and D *)
  Lemma unit_rep_ND (N D : Z) : N <> 0%ZZ -> D <> 0%ZZ ->
    exists y : rat, y != 0 /\
      zr N / zr D = (if Nat.odd (fst (vu qZ N) + fst (vu qZ D))%coq_nat then q%:R else 1) *
                    (y ^+ 2 * (zr (snd (vu qZ N)) / zr (snd (vu qZ D)))).
  Proof using q_prime.
    move=> HN HD.
    have Hq2 := Z.prime_ge_2 _ qZ_prime.
    have EN := @vu_eq (Z.of_nat q) N ltac:(lia); have ED := @vu_eq (Z.of_nat q) D ltac:(lia).
    move: EN ED.
    set i := fst (vu qZ N); set u1 := snd (vu qZ N); set j := fst (vu qZ D); set u2 := snd (vu qZ D).
    have Hu2 : u2 <> 0%ZZ by apply: qunit_neq0; exact: vu_qunit.
    move=> EN ED.
    have Hpw : forall n : nat, (qZ ^ Z.of_nat n <> 0)%ZZ by move=> n; apply: pz_neq0; lia.
    have Hodd : forall s t : nat, Nat.odd (s + t)%coq_nat = true -> Nat.odd (s + t)%coq_nat = true by [].
    case: (even_or_odd i) => [ [ s Hs ] | [ s Hs ] ]; case: (even_or_odd j) => [ [ t Ht ] | [ t Ht ] ].
    - (* even, even *)
      have -> : Nat.odd (i + j)%coq_nat = false.
      { rewrite -Nat.negb_even; apply/negbF/Nat.even_spec; exists (s + t)%coq_nat; lia. }
      exists (zr (qZ ^ Z.of_nat s) / zr (qZ ^ Z.of_nat t)); split.
      { by rewrite mulf_neq0 ?invr_eq0 ?zr_neq0. }
      rewrite mul1r; apply: frac_eq => //.
      rewrite EN ED (pw_even _ Hs) (pw_even _ Ht); lia.
    - (* even, odd *)
      have -> : Nat.odd (i + j)%coq_nat = true.
      { apply/Nat.odd_spec; exists (s + t)%coq_nat; lia. }
      exists (zr (qZ ^ Z.of_nat s) / zr (qZ ^ Z.of_nat t.+1)); split.
      { by rewrite mulf_neq0 ?invr_eq0 ?zr_neq0. }
      rewrite -zr_nat mulrCA [zr qZ * _]mulrA -zr_mul; apply: frac_eq => //.
      rewrite EN ED (pw_even _ Hs) (pw_odd _ Ht) Nat2Z.inj_succ Z.pow_succ_r; last lia.
      lia.
    - (* odd, even *)
      have -> : Nat.odd (i + j)%coq_nat = true.
      { apply/Nat.odd_spec; exists (s + t)%coq_nat; lia. }
      exists (zr (qZ ^ Z.of_nat s) / zr (qZ ^ Z.of_nat t)); split.
      { by rewrite mulf_neq0 ?invr_eq0 ?zr_neq0. }
      rewrite -zr_nat mulrCA [zr qZ * _]mulrA -zr_mul; apply: frac_eq => //.
      rewrite EN ED (pw_odd _ Hs) (pw_even _ Ht); lia.
    - (* odd, odd *)
      have -> : Nat.odd (i + j)%coq_nat = false.
      { rewrite -Nat.negb_even; apply/negbF/Nat.even_spec; exists (S (s + t)%coq_nat); lia. }
      exists (zr (qZ ^ Z.of_nat s) / zr (qZ ^ Z.of_nat t)); split.
      { by rewrite mulf_neq0 ?invr_eq0 ?zr_neq0. }
      rewrite mul1r; apply: frac_eq => //.
      rewrite EN ED (pw_odd _ Hs) (pw_odd _ Ht); lia.
  Qed.

End LocSq.

Section LocSqMain.

  Variable q : nat.
  Hypothesis q_prime : prime q.

  Local Abbreviation qZ := (Z.of_nat q).

  Lemma rat_numden (x : rat) : x = zr (int_to_Z (numq x)) / zr (int_to_Z (denq x)).
  Proof. by rewrite !zr_iz divq_num_den. Qed.

  Lemma int_to_Z_neq0 (i : int) : i != 0 -> int_to_Z i <> 0%ZZ.
  Proof.
    move=> Hi H; move: (zr_iz i); rewrite H zr0 => /esym /eqP.
    by rewrite intr_eq0 (negbTE Hi).
  Qed.

  Lemma zr_frac_neq0 (a c : Z) : a <> 0%ZZ -> c <> 0%ZZ -> zr a / zr c != 0.
  Proof. by move=> Ha Hc; rewrite mulf_neq0 ?invr_eq0 ?zr_neq0. Qed.

  Lemma rep_neq0 (y : rat) (a c : Z) : y != 0 -> qunit q a -> qunit q c -> y ^+ 2 * (zr a / zr c) != 0.
  Proof.
    move=> Hy Ha Hc; apply: mulf_neq0; first exact: expf_neq0.
    exact: (zr_frac_neq0 (qunit_neq0 Ha) (qunit_neq0 Hc)).
  Qed.

  Lemma vqr_rep (y : rat) (a c : Z) : y != 0 -> qunit q a -> qunit q c ->
    vqr q (y ^+ 2 * (zr a / zr c)) = vqr q y + vqr q y.
  Proof.
    move=> Hy Ha Hc.
    have Ha0 := qunit_neq0 Ha; have Hc0 := qunit_neq0 Hc.
    rewrite vqrM ?expf_neq0 ?(zr_frac_neq0 Ha0 Hc0) // vqrX2 // vqr_div ?zr_neq0 //.
    by rewrite (vqr_zr_unit Ha) (vqr_zr_unit Hc) subr0 addr0.
  Qed.

  Theorem locsq_neq0 (x : rat) : locsq q x -> x != 0.
  Proof. move=> [ y [ a [ c [ Hy [ Ha [ Hc [ -> _ ] ] ] ] ] ] ]; exact: rep_neq0. Qed.

  (** necessary direction, for every representation *)
  Theorem locsq_rep (x y : rat) (a c : Z) : locsq q x -> y != 0 -> qunit q a -> qunit q c ->
    x = y ^+ 2 * (zr a / zr c) -> sqmod q a c.
  Proof using q_prime.
    move=> [ y0 [ a0 [ c0 [ Hy0 [ Ha0 [ Hc0 [ E0 H0 ] ] ] ] ] ] ] Hy Ha Hc E.
    apply/(usq_sqmod q_prime Ha Hc).
    apply: (rep_usq q_prime Hy0 Hy Ha0 Hc0 Ha Hc); first by rewrite -E0 -E.
    exact/(usq_sqmod q_prime Ha0 Hc0).
  Qed.

  Theorem is_locsq_rep (x y : rat) (a c : Z) : is_locsq q x -> y != 0 -> qunit q a -> qunit q c ->
    x = y ^+ 2 * (zr a / zr c) -> usq qZ a c.
  Proof using q_prime.
    move=> /(locsq_is_locsq q_prime) Hx Hy Ha Hc E.
    apply/(usq_sqmod q_prime Ha Hc); exact: locsq_rep Hx Hy Ha Hc E.
  Qed.

  (** the valuation of a local square is even *)
  Theorem locsq_val (x : rat) : locsq q x -> exists m : int, vqr q x = m + m.
  Proof.
    move=> [ y [ a [ c [ Hy [ Ha [ Hc [ -> _ ] ] ] ] ] ] ].
    by exists (vqr q y); rewrite vqr_rep.
  Qed.

  (** the finite criterion, on the reduced fraction x = N / D *)
  Theorem locsq_numden (x : rat) : x != 0 ->
    let N := int_to_Z (numq x) in let D := int_to_Z (denq x) in
    locsq q x <->
      Nat.even (fst (vu qZ N) + fst (vu qZ D))%coq_nat = true /\
      sqmod q (snd (vu qZ N)) (snd (vu qZ D)).
  Proof using q_prime.
    move=> Hx N D.
    have HN : N <> 0%ZZ by apply: int_to_Z_neq0; rewrite numq_eq0.
    have HD : D <> 0%ZZ by apply: int_to_Z_neq0; exact: denq_neq0.
    have Hu1 := vu_qunit q_prime HN; have Hu2 := vu_qunit q_prime HD.
    have [ y [ Hy E ] ] := unit_rep_ND q_prime HN HD.
    have Ex : x = zr N / zr D by exact: rat_numden.
    rewrite -Ex in E.
    move: E; rewrite -Nat.negb_even.
    case: (Nat.even _) => /= E.
    - rewrite mul1r in E; split.
      + move=> Hl; split => //; exact: locsq_rep Hl Hy Hu1 Hu2 E.
      + move=> [ _ Hs ]; exists y, (snd (vu qZ N)), (snd (vu qZ D)); do 4 (split => //).
    - split => [ Hl | [ // ] ].
      exfalso; move: Hl => [ y' [ a' [ c' [ Hy' [ Ha' [ Hc' [ E' _ ] ] ] ] ] ] ].
      apply: (rep_parity q_prime Hy Hy' Hu1 Hu2 Ha' Hc'); by rewrite -E -E'.
  Qed.

  (** the same with the valuation *)
  Lemma vqr_numden (x : rat) : x != 0 ->
    vqr q x = (fst (vu qZ (int_to_Z (numq x))))%:Z - (fst (vu qZ (int_to_Z (denq x))))%:Z.
  Proof using q_prime.
    move=> Hx.
    have HN : int_to_Z (numq x) <> 0%ZZ by apply: int_to_Z_neq0; rewrite numq_eq0.
    have HD : int_to_Z (denq x) <> 0%ZZ by apply: int_to_Z_neq0; exact: denq_neq0.
    have Hq0 : (Z.of_nat q <> 0)%ZZ by have := qZ_gt0 q_prime; lia.
    rewrite {1}(rat_numden x) vqr_div ?zr_neq0 //.
    by rewrite (vqr_zr_dec q_prime (vu_qunit q_prime HN) (vu_eq _ Hq0))
               (vqr_zr_dec q_prime (vu_qunit q_prime HD) (vu_eq _ Hq0)).
  Qed.

  Lemma even_int (i j : nat) : Nat.even (i + j)%coq_nat = true <-> exists m : int, i%:Z - j%:Z = m + m.
  Proof.
    split.
    - move=> /Nat.even_spec [ k Hk ]; exists (Z_to_int (Z.of_nat k - Z.of_nat j)).
      apply: iz_inj; rewrite iz_add !iz_opp !iz_add ?iz_nat iz_Z_to_int; lia.
    - move=> [ m Hm ]; apply/Nat.even_spec.
      move: Hm => /(congr1 int_to_Z); rewrite iz_add iz_opp !iz_nat iz_add => Hm.
      exists (Z.to_nat (int_to_Z m + Z.of_nat j)); lia.
  Qed.

  Theorem locsq_iff_val (x : rat) : x != 0 ->
    locsq q x <->
      (exists m : int, vqr q x = m + m) /\
      sqmod q (snd (vu qZ (int_to_Z (numq x)))) (snd (vu qZ (int_to_Z (denq x)))).
  Proof using q_prime.
    move=> Hx; rewrite (locsq_numden Hx) (vqr_numden Hx).
    have := even_int (fst (vu qZ (int_to_Z (numq x)))) (fst (vu qZ (int_to_Z (denq x)))).
    tauto.
  Qed.

  (** for any representation with even valuation *)
  Theorem locsq_iff_rep (x y : rat) (a c : Z) : y != 0 -> qunit q a -> qunit q c ->
    x = y ^+ 2 * (zr a / zr c) -> (locsq q x <-> sqmod q a c).
  Proof using q_prime.
    move=> Hy Ha Hc E; split => [ H | H ]; first exact: locsq_rep H Hy Ha Hc E.
    by exists y, a, c.
  Qed.

  (** odd valuation: never a local square *)
  Theorem locsq_odd_val (x : rat) : (exists m : int, vqr q x = m + m + 1) -> ~ locsq q x.
  Proof.
    move=> [ m Hm ] /locsq_val [ m' Hm' ]; move: Hm; rewrite Hm' => /(congr1 int_to_Z).
    rewrite !iz_add (_ : int_to_Z 1 = 1%ZZ) // => H; lia.
  Qed.

  (** the unit part: "a / c is a square mod q" is "a c is a square mod q"
      (Legendre symbol (a c / q) = 1) for odd q, and a c = 1 mod 8 at 2 *)
  Lemma sqmod_odd_prod (a c : Z) : q != 2%N -> qunit q a -> qunit q c ->
    sqmod q a c <-> exists w, (qZ | a * c - w * w)%ZZ.
  Proof using q_prime.
    move=> Hq2 Ha Hc; rewrite /sqmod (negbTE Hq2); split.
    - move=> [ z [ t Ht ] ]; exists (z * c)%ZZ; exists (t * c)%ZZ; lia.
    - move=> [ w [ t Ht ] ].
      have [ ci [ s Hs ] ] := inv_prime (qZ_prime q_prime) Hc.
      exists (w * ci)%ZZ; exists (- a * (c * ci + 1) * s + ci * ci * c * t)%ZZ.
      transitivity (- a * (c * ci + 1) * (c * ci - 1) + ci * ci * c * (a * c - w * w))%ZZ; first lia.
      rewrite Hs Ht; lia.
  Qed.

  Lemma sqmod_two_prod (a c : Z) : q = 2%N -> qunit q a -> qunit q c ->
    sqmod q a c <-> (8 | a * c - 1)%ZZ.
  Proof.
    move=> Hq2 Ha Hc; rewrite /sqmod Hq2 /=.
    move: Ha Hc; rewrite /qunit Hq2 => Ha Hc.
    have [ s Hs ] := odd_sq8 Hc.
    split.
    - move=> [ t Ht ]; exists (t * c + s)%ZZ; lia.
    - move=> [ t Ht ].
      have Hco : Z.coprime (2 ^ 3) c by apply: coprime_pz => //; exact: Z.prime_2.
      apply: (dvd_cancel Hco); exists (t - s)%ZZ; lia.
  Qed.

End LocSqMain.

(** * 10. Multiplicativity, squares, and stability under small perturbations *)

Section LocSqAlg.

  Variable q : nat.
  Hypothesis q_prime : prime q.

  Local Abbreviation qZ := (Z.of_nat q).

  Lemma qunit1 : qunit q 1.
  Proof using q_prime.
    move=> H; have := Z.divide_pos_le _ _ Z.lt_0_1 H; have := Z.prime_ge_2 _ (qZ_prime q_prime); lia.
  Qed.

  Theorem locsq_mul (x x' : rat) : locsq q x -> locsq q x' -> locsq q (x * x').
  Proof using q_prime.
    move=> /(locsq_is_locsq q_prime) [ y [ a [ c [ Hy [ Ha [ Hc [ -> H ] ] ] ] ] ] ].
    move=> /(locsq_is_locsq q_prime) [ y' [ a' [ c' [ Hy' [ Ha' [ Hc' [ -> H' ] ] ] ] ] ] ].
    apply/(locsq_is_locsq q_prime); exists (y * y'), (a * a')%ZZ, (c * c')%ZZ.
    split; first by rewrite mulf_neq0.
    split; first exact: qunit_mul.
    split; first exact: qunit_mul.
    split; last exact: usq_mul.
    by rewrite !zr_mul exprMn invfM; ring.
  Qed.

  Theorem locsq_sq (y : rat) : y != 0 -> locsq q (y ^+ 2).
  Proof using q_prime.
    move=> Hy; exists y, 1%ZZ, 1%ZZ; split => //; split; first exact: qunit1.
    split; first exact: qunit1.
    split; first by rewrite zr1 invr1 !mulr1.
    apply/(usq_sqmod q_prime qunit1 qunit1); exact: usq_refl.
  Qed.

  Theorem locsq_inv (x : rat) : locsq q x -> locsq q x^-1.
  Proof using q_prime.
    move=> /(locsq_is_locsq q_prime) [ y [ a [ c [ Hy [ Ha [ Hc [ -> H ] ] ] ] ] ] ].
    apply/(locsq_is_locsq q_prime); exists y^-1, c, a.
    split; first by rewrite invr_eq0.
    do 2 (split => //).
    split; first by rewrite invfM exprVn invf_div.
    apply: (@usq_transfer qZ a c c a a c (qZ_prime q_prime) Ha Hc) => //; lia.
  Qed.

  Theorem locsq_div (x x' : rat) : locsq q x -> locsq q x' -> locsq q (x / x').
  Proof using q_prime. by move=> H H'; apply: locsq_mul H (locsq_inv H'). Qed.

  (* the threshold: u = 1 mod q (odd q), resp. u = 1 mod 8, is a square *)
  Definition cq : nat := if q == 2%N then 3%N else 1%N.

  Theorem locsq_near1 (s t : Z) (K : nat) : qunit q t -> (cq <= K)%N ->
    locsq q (1 + zr (qZ ^ Z.of_nat K * s) / zr t).
  Proof using q_prime.
    move=> Ht HK.
    have Ht0 := qunit_neq0 Ht.
    have HK1 : (1 <= K)%coq_nat by move: HK; rewrite /cq; case: eqP => _ /ssrnat.leP; lia.
    have Hdiv : (qZ | qZ ^ Z.of_nat K * s)%ZZ.
    { apply: Z.divide_mul_l; rewrite -{1}(Z.pow_1_r qZ); apply: pz_dvd; lia. }
    exists 1, (t + qZ ^ Z.of_nat K * s)%ZZ, t.
    split; first exact: oner_neq0.
    split.
    { move=> H; apply: Ht; move: H Hdiv => [ u Hu ] [ w Hw ]; exists (u - w)%ZZ; lia. }
    split => //.
    split; first by rewrite expr1n mul1r zr_add mulrDl divff ?zr_neq0.
    rewrite /sqmod; move: HK; rewrite /cq; case: eqP => [ Eq | Hq ] HK.
    - move/ssrnat.leP: HK => HK.
      have : (2 ^ 3 | qZ ^ Z.of_nat K * s)%ZZ.
      { apply: Z.divide_mul_l; rewrite Eq; apply: pz_dvd; lia. }
      move=> [ w Hw ]; exists w; rewrite /= in Hw |- *; lia.
    - exists 1%ZZ; move: Hdiv => [ w Hw ]; exists w; lia.
  Qed.

  (** stability: x' close to the local square x is a local square *)
  Theorem locsq_close (x x' : rat) : locsq q x -> x' != 0 ->
    x' = x \/ vqr q x + cq%:Z <= vqr q (x' - x) -> locsq q x'.
  Proof using q_prime.
    move=> Hx Hx' [ -> // | Hv ].
    have Hx0 := locsq_neq0 Hx.
    case: (eqVneq x' x) => [ -> // | Hne ].
    have Hd : x' - x != 0 by rewrite subr_eq0.
    set w := (x' - x) / x.
    have Hw : w != 0 by rewrite /w mulf_neq0 ?invr_eq0.
    have Hvw : cq%:Z <= vqr q w.
    { rewrite /w vqr_div //; move: Hv; move: (vqr q x) (vqr q (x' - x)) => va vb.
      rewrite !iz_le !iz_add iz_opp iz_nat; lia. }
    have E : x' = x * (1 + w) by rewrite /w mulrDr mulr1 mulrCA divff // mulr1 addrC subrK.
    rewrite E; apply: locsq_mul => //.
    have HN : int_to_Z (numq w) <> 0%ZZ by apply: int_to_Z_neq0; rewrite numq_eq0.
    have HD : int_to_Z (denq w) <> 0%ZZ by apply: int_to_Z_neq0; exact: denq_neq0.
    have Hq0 : (qZ <> 0)%ZZ by have := qZ_gt0 q_prime; lia.
    move: Hvw; rewrite (vqr_numden q_prime Hw).
    have EN := vu_eq (int_to_Z (numq w)) Hq0; have ED := vu_eq (int_to_Z (denq w)) Hq0.
    have Hu1 := vu_qunit q_prime HN; have Hu2 := vu_qunit q_prime HD.
    move: EN ED Hu1 Hu2.
    set i := fst (vu qZ (int_to_Z (numq w))); set u1 := snd (vu qZ (int_to_Z (numq w))).
    set j := fst (vu qZ (int_to_Z (denq w))); set u2 := snd (vu qZ (int_to_Z (denq w))).
    move=> EN ED Hu1 Hu2 Hij.
    have Hij' : (Nat.add cq j <= i)%coq_nat.
    { move: Hij; rewrite iz_le iz_add iz_opp !iz_nat; lia. }
    have Ew : w = zr (qZ ^ Z.of_nat (Nat.sub i j) * u1) / zr u2.
    { rewrite {1}(rat_numden w); apply/eqP; have Hu20 := qunit_neq0 Hu2; rewrite eqr_div ?zr_neq0 //.
      rewrite -!zr_mul; apply/eqP; congr zr.
      rewrite EN ED.
      have -> : Z.of_nat i = (Z.of_nat j + Z.of_nat (Nat.sub i j))%ZZ by lia.
      rewrite Z.pow_add_r; lia. }
    rewrite Ew; apply: locsq_near1 => //.
    apply/ssrnat.leP; lia.
  Qed.

End LocSqAlg.

(** The real place *)

Lemma locsq_inf_sq (y : rat) : y != 0 -> locsq_inf (y ^+ 2).
Proof. by move=> Hy; rewrite /locsq_inf exprn_even_gt0. Qed.

Lemma locsq_inf_mul (x y : rat) : locsq_inf x -> locsq_inf y -> locsq_inf (x * y).
Proof. exact: mulr_gt0. Qed.

Lemma locsq_inf_inv (x : rat) : locsq_inf x -> locsq_inf x^-1.
Proof. by rewrite /locsq_inf invr_gt0. Qed.

(** * 11. Weak approximation for Q at finitely many primes

    Targets (q, k, x_q): x is q-adically within q^k of x_q, i.e.
    x = x_q or v_q(x - x_q) >= k. The approximation x = X / D has as
    denominator the product D of the denominators of the targets; X
    comes from the CRT with precisions q^(k + v_q(D)). *)

Definition close_at (x : rat) (t : nat * nat * rat) : Prop :=
  let '(q, k, xt) := t in x = xt \/ k%:Z <= vqr q (x - xt).

Definition tq (t : nat * nat * rat) : nat := let '(q, _, _) := t in q.

Section WeakApprox.

  Lemma prodZ_pos (l : list Z) : Forall (fun d => 0 < d)%ZZ l -> (0 < prodZ l)%ZZ.
  Proof. elim: l => [ | a l IH ] H //=; inversion H; subst; have := IH H3; nia. Qed.

  Lemma denZ_pos (x : rat) : (0 < int_to_Z (denq x))%ZZ.
  Proof. by have := denq_gt0 x; rewrite iz_lt. Qed.

  Lemma close_of_cong (q k : nat) (xt : rat) (X D T : Z) : prime q -> D <> 0%ZZ ->
    zr D * xt = zr T ->
    (Z.of_nat q ^ Z.of_nat (Nat.add k (fst (vu (Z.of_nat q) D))) | X - T)%ZZ ->
    close_at (zr X / zr D) (q, k, xt).
  Proof.
    move=> Hq HD E Hc; rewrite /close_at.
    have HD' := zr_neq0 HD.
    have Ext : xt = zr T / zr D by apply: (mulfI HD'); rewrite E mulrCA divff // mulr1.
    have Ed : zr X / zr D - xt = zr (X - T) / zr D by rewrite Ext zr_sub mulrBl.
    case: (Z.eq_dec (X - T) 0) => [ H0 | H0 ]; [ left | right ].
    - by apply/eqP; rewrite -subr_eq0 Ed H0 zr0 mul0r.
    - have Hq0 : (Z.of_nat q <> 0)%ZZ by have := qZ_gt0 Hq; lia.
      rewrite Ed vqr_div ?zr_neq0 //.
      rewrite (vqr_zr_dec Hq (vu_qunit Hq HD) (vu_eq D Hq0)).
      have := vqr_zr_ge Hq H0 Hc; move: (vqr q (zr (X - T))) => v.
      rewrite !iz_le iz_add iz_opp !iz_nat; lia.
  Qed.

  Lemma den_mul_eq (D : Z) (xt : rat) : (int_to_Z (denq xt) | D)%ZZ ->
    zr D * xt = zr (int_to_Z (numq xt) * (D / int_to_Z (denq xt))).
  Proof.
    move=> [ c Hc ].
    have Hd := denZ_pos xt.
    have -> : (D / int_to_Z (denq xt))%ZZ = c by rewrite Hc Z.div_mul; lia.
    have Hz : zr (int_to_Z (denq xt)) != 0 by apply: zr_neq0; lia.
    move: (rat_numden xt) Hz Hc.
    set N := int_to_Z (numq xt); set Dt := int_to_Z (denq xt) => Ex Hz Hc.
    rewrite Hc !zr_mul Ex; field; exact: Hz.
  Qed.

  Lemma map_tgt_p (F : nat * nat * rat -> Z * nat * Z) (l : list (nat * nat * rat)) :
    (forall t, tgt_p (F t) = Z.of_nat (tq t)) -> map tgt_p (map F l) = map Z.of_nat (map tq l).
  Proof. move=> H; elim: l => [ | t l IH ] //=; by rewrite H IH. Qed.

  Theorem weak_approx (l : list (nat * nat * rat)) :
    NoDup (map tq l) -> Forall (fun t => prime (tq t)) l ->
    exists x : rat, Forall (close_at x) l.
  Proof.
    move=> Hnd Hpr.
    set D := prodZ (map (fun t => int_to_Z (denq t.2)) l).
    have HD : (0 < D)%ZZ.
    { apply: prodZ_pos; apply/Forall_forall => d /in_map_iff [ t [ <- _ ] ]; exact: denZ_pos. }
    set T := fun xt : rat => (int_to_Z (numq xt) * (D / int_to_Z (denq xt)))%ZZ.
    set L := map (fun t : nat * nat * rat =>
                    let '(q, k, xt) := t in (Z.of_nat q, (Nat.add k (fst (vu (Z.of_nat q) D))), T xt)) l.
    have HL1 : NoDup (map tgt_p L).
    { have -> : map tgt_p L = map Z.of_nat (map tq l).
      { apply: map_tgt_p => - [ [ q k ] xt ] //. }
      apply: Finite.Injective_map_NoDup => //; exact: Nat2Z.inj. }
    have HL2 : Forall (fun t => Z.prime (tgt_p t)) L.
    { apply/Forall_forall => t /in_map_iff [ [ [ q k ] xt ] [ <- Hin ] ] /=.
      apply: primeZ; by move: Hpr => /Forall_forall /(_ _ Hin). }
    have [ X HX ] := crt_primes HL1 HL2.
    exists (zr X / zr D); apply/Forall_forall => - [ [ q k ] xt ] Hin.
    have Hq : prime q by move: Hpr => /Forall_forall /(_ _ Hin).
    have Hok : tgt_ok X (Z.of_nat q, (Nat.add k (fst (vu (Z.of_nat q) D))), T xt).
    { move: HX => /Forall_forall; apply; apply/in_map_iff; by exists (q, k, xt). }
    apply: (close_of_cong Hq _ _ Hok); first lia.
    apply: den_mul_eq; apply: dvd_prodZ; apply/in_map_iff; by exists (q, k, xt).
  Qed.

  (** with the real place: in addition |x - r| < eps *)

  Lemma zr_pos (z : Z) : (0 < z)%ZZ <-> 0 < zr z.
  Proof.
    split; first exact: zr_gt0.
    move=> H; case: (Z.lt_ge_cases 0 z) => // Hz; exfalso.
    case: (Z.eq_dec z 0) => [ E | Hne ]; first by move: H; rewrite E zr0 ltxx.
    have : 0 < zr (- z) by apply: zr_gt0; lia.
    rewrite zr_opp oppr_gt0 => H'; move: (lt_trans H H'); by rewrite ltxx.
  Qed.

  Lemma close_of_cong' (q k K : nat) (xt : rat) (X D T : Z) : prime q -> D <> 0%ZZ ->
    zr D * xt = zr T -> (Nat.add k (fst (vu (Z.of_nat q) D)) <= K)%coq_nat ->
    (Z.of_nat q ^ Z.of_nat K | X - T)%ZZ ->
    close_at (zr X / zr D) (q, k, xt).
  Proof.
    move=> Hq HD E HK Hc; apply: close_of_cong Hq HD E _.
    apply: dvd_trans_pz Hc; lia.
  Qed.

  Lemma vu_fst_unit (q : nat) (D R : Z) : prime q -> D <> 0%ZZ -> qunit q R ->
    fst (vu (Z.of_nat q) (D * R)) = fst (vu (Z.of_nat q) D).
  Proof.
    move=> Hq HD HR.
    have Hq0 : (Z.of_nat q <> 0)%ZZ by have := qZ_gt0 Hq; lia.
    have HDR : (D * R <> 0)%ZZ by apply/Z.neq_mul_0; split => //; exact: (qunit_neq0 HR).
    have E1 := vu_eq (D * R) Hq0; have E2 := vu_eq D Hq0.
    apply: (pow_unit_eq (qZ_prime Hq) (vu_qunit Hq HDR) (qunit_mul Hq (vu_qunit Hq HD) HR)).
    rewrite -E1 {1}E2; lia.
  Qed.

  Theorem weak_approx_inf (l : list (nat * nat * rat)) (r eps : rat) :
    NoDup (map tq l) -> Forall (fun t => prime (tq t)) l -> 0 < eps ->
    exists x : rat, `|x - r| < eps /\ Forall (close_at x) l.
  Proof.
    move=> Hnd Hpr Heps.
    set D := prodZ (map (fun t => int_to_Z (denq t.2)) l).
    have HD : (0 < D)%ZZ.
    { apply: prodZ_pos; apply/Forall_forall => d /in_map_iff [ t [ <- _ ] ]; exact: denZ_pos. }
    set T := fun xt : rat => (int_to_Z (numq xt) * (D / int_to_Z (denq xt)))%ZZ.
    have HT : forall q k xt, In (q, k, xt) l -> zr D * xt = zr (T xt).
    { move=> q k xt Hin; apply: den_mul_eq; apply: dvd_prodZ; apply/in_map_iff; by exists (q, k, xt). }
    set Kt := fun q k : nat => S (Nat.add k (fst (vu (Z.of_nat q) D))).
    set M := prodZ (map (fun t : nat * nat * rat => let '(q, k, _) := t in (Z.of_nat q ^ Z.of_nat (Kt q k))%ZZ) l).
    have HM : (0 < M)%ZZ.
    { apply: prodZ_pos; apply/Forall_forall => d /in_map_iff [ [ [ q k ] xt ] [ <- Hin ] ].
      have Hq : prime q by move: Hpr => /Forall_forall /(_ _ Hin).
      apply: Z.pow_pos_nonneg; [ exact: qZ_gt0 | lia ]. }
    have HqM : forall q k xt, In (q, k, xt) l -> (Z.of_nat q ^ Z.of_nat (Kt q k) | M)%ZZ.
    { move=> q k xt Hin; apply: dvd_prodZ; apply/in_map_iff; by exists (q, k, xt). }
    (* the auxiliary unit R = 1 + M n, large *)
    have HD' : 0 < zr D by apply/zr_pos.
    have HM' : 0 < zr M by apply/zr_pos.
    set n := (int_to_Z (Num.floor ((zr D * eps)^-1)) + 1)%ZZ.
    have Hn : (zr D * eps)^-1 < zr n.
    { by rewrite /n zr_add zr_iz zr1 -intrD1 floorD1_gt. }
    have HDe : 0 < zr D * eps by apply: mulr_gt0.
    have HDe' : zr D * eps * (zr D * eps)^-1 = 1 by rewrite divff // gt_eqF.
    have Hn1 : 1 < zr D * eps * zr n by nra.
    have Hn0 : 0 < zr n by nra.
    set R := (1 + M * n)%ZZ.
    have HR' : zr R = 1 + zr M * zr n by rewrite /R zr_add zr_mul zr1.
    have HR0 : (0 < R)%ZZ by apply/zr_pos; rewrite HR'; nra.
    have HRu : forall q k xt, In (q, k, xt) l -> prime q -> qunit q R.
    { move=> q k xt Hin Hq HqR.
      have HqM' : (Z.of_nat q | M)%ZZ.
      { apply: Z.divide_trans (HqM _ _ _ Hin); rewrite -{1}(Z.pow_1_r (Z.of_nat q)).
        apply: pz_dvd; rewrite /Kt; lia. }
      have Hq1 : (Z.of_nat q | 1)%ZZ.
      { move: HqR HqM' => [ a Ha ] [ b Hb ]; exists (a - b * n)%ZZ; rewrite /R in Ha; lia. }
      have := Z.divide_pos_le _ _ Z.lt_0_1 Hq1; have := Z.prime_ge_2 _ (qZ_prime Hq); lia. }
    (* the CRT *)
    set L := map (fun t : nat * nat * rat => let '(q, k, xt) := t in (Z.of_nat q, Kt q k, (R * T xt)%ZZ)) l.
    have HL1 : NoDup (map tgt_p L).
    { have -> : map tgt_p L = map Z.of_nat (map tq l) by apply: map_tgt_p => - [ [ q k ] xt ].
      apply: Finite.Injective_map_NoDup => //; exact: Nat2Z.inj. }
    have HL2 : Forall (fun t => Z.prime (tgt_p t)) L.
    { apply/Forall_forall => t /in_map_iff [ [ [ q k ] xt ] [ <- Hin ] ] /=.
      apply: primeZ; by move: Hpr => /Forall_forall /(_ _ Hin). }
    have [ X HX ] := crt_primes HL1 HL2.
    (* the real approximation *)
    set A := zr (D * R).
    have HA : A = zr D * (1 + zr M * zr n) by rewrite /A zr_mul HR'.
    have HA0 : 0 < A by rewrite HA; nra.
    have HepsA : zr M < eps * A by rewrite HA; nra.
    set s := (r * A - zr X) / zr M.
    have Es : s * zr M = r * A - zr X by rewrite /s mulfVK // gt_eqF.
    set j := int_to_Z (Num.floor s).
    have Hj1 : zr j <= s by rewrite /j zr_iz floor_le.
    have Hj2 : s < zr j + 1 by rewrite /j zr_iz -intrD1 floorD1_gt.
    exists (zr (X + j * M) / A); split.
    - rewrite zr_add zr_mul.
      set Ai := A^-1.
      have HAi : 0 < Ai by rewrite /Ai invr_gt0.
      have HAAi : A * Ai = 1 by rewrite /Ai divff // gt_eqF.
      have H1 : zr j * zr M <= s * zr M by nra.
      have H2 : s * zr M < zr j * zr M + zr M by nra.
      have -> : (zr X + zr j * zr M) / A - r = (zr X + zr j * zr M - r * A) * Ai.
      { rewrite /Ai mulrBl -mulrA HAAi mulr1. by []. }
      rewrite ltr_norml; apply/andP; split; nra.
    - apply/Forall_forall => - [ [ q k ] xt ] Hin.
      have Hq : prime q by move: Hpr => /Forall_forall /(_ _ Hin).
      have HRq := HRu _ _ _ Hin Hq.
      apply: (@close_of_cong' q k (Kt q k) xt _ _ (R * T xt)%ZZ Hq).
      + by apply/Z.neq_mul_0; split; lia.
      + by rewrite zr_mul [_ * zr R]mulrC -mulrA (HT _ _ _ Hin) zr_mul.
      + rewrite (vu_fst_unit Hq _ HRq) /Kt; lia.
      + have Hok : tgt_ok X (Z.of_nat q, Kt q k, (R * T xt)%ZZ).
        { move: HX => /Forall_forall; apply; apply/in_map_iff; by exists (q, k, xt). }
        move: Hok (HqM _ _ _ Hin) => /= [ a Ha ] [ b Hb ].
        exists (a + j * b)%ZZ; lia.
  Qed.

End WeakApprox.
