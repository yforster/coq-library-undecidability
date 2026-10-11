(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Legendre and Jacobi symbols, Euler's criterion and quadratic
   reciprocity with both supplements (PLAN.md Phase 3, task Q2;
   PP1_DESIGN.md, item I1). Self-contained number theory over
   MathComp; no axioms.

   Route. Quadratic reciprocity is proved with GAUSS SUMS IN A FINITE
   FIELD OF CHARACTERISTIC q (Sec. 4, 5): for distinct odd primes p, q
   take a finite field F with q^(p-1) elements ([pPrimePowerField]),
   which contains a primitive p-th root of unity z because p divides
   q^(p-1) - 1 (Fermat). With chi the quadratic character of 'F_p, the
   Gauss sum g = sum_x chi(x) z^x satisfies
     g^2 = chi(-1) p          (reindex y = x c, sum of chi is 0),
     g^q = chi(q) g           (Frobenius is additive in char q),
   and g^q = g (g^2)^((q-1)/2) = g ((chi(-1) p)/q) by Euler's criterion
   in F. As g <> 0, (q/p) = ((-1/p) p / q), whence reciprocity. The
   second supplement is the same argument with tau = z + z^7 for a
   primitive 8th root z in the field with p^2 elements: tau^2 = 2 and
   tau^p = +tau or -tau according to p mod 8 (Sec. 6). Euler's criterion
   comes from a primitive (|F|-1)-th root of unity in a finite field
   ([has_prim_root], Sec. 1). This avoids Gauss's lemma and lattice-point
   counting entirely.

   Main results (p, q odd primes; n, m odd naturals):
   - [legendre a p] : int (a : int), via the character [lchi p] of 'F_p;
     [legendre_sgn3] (values 0, 1, -1), [legendre_mod], [legendreM],
     [legendreX], [legendre_eq0] ((a/p) = 0 iff p | a),
     [legendre_euler] ((a/p) = a^((p-1)/2) mod p, also in 'F_p and in
     any ring of characteristic p), [legendre_eq1] ((a/p) = 1 iff p does
     not divide a and a is a square mod p), [legendre_eqN1];
   - [legendre_minus_one] : (-1/p) = (-1)^((p-1)/2);
     [legendre_two] : (2/p) = (-1)^((p^2-1)/8), and
     [legendre_two_mod8_global] : (2/p) = 1 iff p = 1, 7 mod 8;
   - [quadratic_reciprocity] :
       (p/q) (q/p) = (-1)^(((p-1)/2) ((q-1)/2));
   - [jacobi a n] = prod_{p | n} (a/p)^(v_p n); [jacobiMl], [jacobiMr],
     [jacobi_mod], [jacobi_prime], [jacobi_sqr], [jacobi_minus_one],
     [jacobi_two], [jacobi_reciprocity] (coprime odd m, n);
   - Sec. 8, the CRT consequence used for Lemma par:simultaneous-matrices:
     for a list ps of distinct odd primes, signs eps and an odd r there is
     a residue a mod M = 8 prod ps with a = r mod 8, coprime to M, such
     that [legendre_pattern] every integer x = a mod M has (x/p) = eps p
     for p in ps, and [legendre_pattern_prime] every PRIME q = a mod M
     moreover has (p/q) = eps p (-1)^((p-1)/2 (r-1)/2),
     (-1/q) = (-1)^((r-1)/2) and (2/q) = (-1)^((r^2-1)/8). Such primes
     exist by Dirichlet's theorem (proved in PrimePatterns.v, Phase 4).
   Conventions: exponents are written with MathComp's (n.-1)./2 for
   (n-1)/2 and (n ^ 2).-1 %/ 8 for (n^2-1)/8; nat arguments are coerced
   to int. *)

From mathcomp Require Import boot order algebra finite_group.
From mathcomp Require Import cyclic finfield.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(* 1. Finite fields: primitive roots and Euler's criterion            *)
(* ------------------------------------------------------------------ *)

Section FinFieldEuler.

Variable F : finFieldType.
Local Abbreviation n := #|F|.

Lemma card_gt1 : (1 < n)%N.
Proof. exact: finNzRing_gt1. Qed.

Lemma card1_gt0 : (0 < n.-1)%N.
Proof. by rewrite -ltnS prednK ?card_gt1 // ltnW ?card_gt1. Qed.

Lemma expf_card1 (x : F) : x != 0 -> x ^+ n.-1 = 1.
Proof.
move=> nz; apply: (mulIf nz); rewrite mul1r -exprSr prednK ?expf_card //.
by apply: ltnW; exact: card_gt1.
Qed.

Lemma exists_prim_root : exists w : F, (n.-1).-primitive_root w.
Proof.
pose rs := enum [pred x : F | x != 0].
have n1_gt0 := card1_gt0.
have: has (n.-1).-primitive_root rs.
  apply: has_prim_root => //.
  - by apply/allP => x; rewrite mem_enum => nz; apply/unity_rootP/expf_card1.
  - exact: enum_uniq.
  - rewrite -cardE.
    have := cardC1 (0 : F); rewrite /predC1 => <-.
    by apply/eq_leq/eq_card => x; rewrite !inE.
by case/hasP => w _ pw; exists w.
Qed.

Hypothesis n_odd : odd n.
Local Abbreviation m := (n.-1)./2.

Lemma half_card : n.-1 = m.*2.
Proof using F n_odd.
rewrite -[LHS](odd_double_half) /=; have: ~~ odd n.-1.
  by move: n_odd card_gt1; case: (n) => [|k] //= ->.
by move/negbTE ->.
Qed.

Lemma m_gt0 : (0 < m)%N.
Proof using F n_odd.
have := card_gt1; rewrite -[n](prednK (ltnW card_gt1)) ltnS half_card.
by case: (m).
Qed.

Lemma euler_sqrt1 (x : F) : x != 0 -> (x ^+ m = 1) \/ (x ^+ m = -1).
Proof using F n_odd.
move=> nz; have: (x ^+ m) ^+ 2 == 1.
  by rewrite -exprM muln2 -half_card expf_card1.
by rewrite sqrf_eq1 => /orP[] /eqP; [left | right].
Qed.

Lemma euler_crit (x : F) : x != 0 ->
  (x ^+ m = 1) <-> (exists y, y ^+ 2 = x).
Proof using F n_odd.
move=> nz; split => [xm1 | [y yx]]; last first.
  have ynz : y != 0 by apply: contra_neq nz => y0; rewrite -yx y0 expr0n.
  by rewrite -yx -exprM mulnC muln2 -half_card expf_card1.
have [w pw] := exists_prim_root.
have [[i /= _] xi] := prim_rootP pw (expf_card1 nz).
move: xm1; rewrite xi -exprM => /eqP; rewrite -(prim_order_dvd pw) half_card.
rewrite doubleK -muln2 mulnC dvdn_pmul2r ?m_gt0 // => /dvdnP[j ij].
by exists (w ^+ j); rewrite -exprM ij.
Qed.

Lemma exists_nonsq : exists x : F, x ^+ m = -1.
Proof using F n_odd.
have [w pw] := exists_prim_root.
have wnz : w != 0 by rewrite (prim_root_eq0 pw) -lt0n card1_gt0.
exists w; case: (euler_sqrt1 wnz) => // /eqP; rewrite -(prim_order_dvd pw).
move/dvdn_leq => /(_ m_gt0); rewrite half_card doubleK -addnn -{3}[m]add0n leq_add2r.
by rewrite leqn0 => /eqP m0; move: m_gt0; rewrite m0.
Qed.

End FinFieldEuler.

Lemma odd_halfE n : odd n -> n = ((n.-1)./2).*2.+1.
Proof.
case: n => [//|n] /= en; congr _.+1.
by rewrite -[LHS](odd_double_half n) (negbTE en).
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Integers in rings of prime characteristic                       *)
(* ------------------------------------------------------------------ *)

Section IntChar.

Variables (R : nzRingType) (p : nat).
Hypothesis pR : p \in [pchar R].

Lemma intr_pchar_eq0 (a : int) : (a%:~R == 0 :> R) = (p %| a)%Z.
Proof using R p pR.
rewrite dvdzE; case: a => k; first by rewrite -(dvdn_pcharf pR).
by rewrite NegzE mulrNz oppr_eq0 abszN -(dvdn_pcharf pR).
Qed.

Lemma intr_pchar_eq (a b : int) : (a%:~R == b%:~R :> R) = (a == b %[mod p])%Z.
Proof using R p pR. by rewrite eqz_mod_dvd -intr_pchar_eq0 rmorphB /= subr_eq0. Qed.

Lemma intr_pchar_mod (a b : int) : (a == b %[mod p])%Z -> a%:~R = b%:~R :> R.
Proof using R p pR. by rewrite -intr_pchar_eq => /eqP. Qed.

Definition sgn3 (u : int) := (u == 0) || (u == 1) || (u == -1).

Lemma sgn3_inj (u v : int) : odd p -> sgn3 u -> sgn3 v ->
  u%:~R = v%:~R :> R -> u = v.
Proof using R p pR.
move=> p_odd hu hv /eqP; rewrite intr_pchar_eq eqz_mod_dvd dvdzE.
have p_pr := pcharf_prime pR.
have n1 : ~~ (p %| 1)%N by rewrite dvdn1; apply/eqP => p1; move: p_pr; rewrite p1.
have n2 : ~~ (p %| 2)%N.
  apply/negP=> h; have := dvdn_leq (isT : (0 < 2)%N) h; rewrite leq_eqVlt ltnS => /orP[/eqP p2|].
    by move: p_odd; rewrite p2.
  by rewrite leqNgt prime_gt1.
by case/orP: hu => [/orP[]|] /eqP->; case/orP: hv => [/orP[]|] /eqP->;
   rewrite //= ?(negbTE n1) ?(negbTE n2).
Qed.

End IntChar.

(* ------------------------------------------------------------------ *)
(* 3. The Legendre symbol                                             *)
(* ------------------------------------------------------------------ *)

(* The quadratic character of 'F_p, with values 0, 1, -1. *)
Definition lchi (p : nat) (x : 'F_p) : int :=
  if x == 0 then 0 else if x ^+ (p.-1)./2 == 1 then 1 else -1.
Arguments lchi p x : clear implicits.

(* The Legendre symbol (a/p); meaningful for odd primes p. *)
Definition legendre (a : int) (p : nat) : int := lchi p (a%:~R : 'F_p).

Section Legendre.

Variable p : nat.
Hypotheses (p_pr : prime p) (p_odd : odd p).
Local Abbreviation m := (p.-1)./2.

Lemma card_Fp_odd : odd #|'F_p|.
Proof using p p_odd p_pr. by rewrite card_Fp. Qed.

Lemma lchi_sgn3 x : sgn3 (lchi p x).
Proof. by rewrite /lchi /sgn3; case: ifP => //; case: ifP. Qed.

Lemma lchi_euler x : (lchi p x)%:~R = x ^+ m.
Proof using p p_odd p_pr.
have Ec := card_Fp p_pr; rewrite /lchi; case: eqP => [->|/eqP nz].
  by rewrite expr0n -Ec gtn_eqF ?(m_gt0 card_Fp_odd).
case: eqP => [-> //|/eqP h].
have := euler_sqrt1 card_Fp_odd nz; rewrite Ec.
by case => // /eqP; rewrite (negbTE h).
Qed.

Lemma lchi_inj (u v : int) : sgn3 u -> sgn3 v -> u%:~R = v%:~R :> 'F_p -> u = v.
Proof using p p_odd p_pr. exact: (sgn3_inj (pchar_Fp p_pr)). Qed.

Lemma lchiM x y : lchi p (x * y) = lchi p x * lchi p y.
Proof using p p_odd p_pr.
apply: lchi_inj; rewrite ?lchi_sgn3 //.
  by have := lchi_sgn3 x; have := lchi_sgn3 y; rewrite /sgn3 =>
     /orP[/orP[]|] /eqP-> /orP[/orP[]|] /eqP->.
by rewrite rmorphM /= !lchi_euler exprMn.
Qed.

Lemma lchi0 : lchi p 0 = 0.
Proof. by rewrite /lchi eqxx. Qed.

Lemma lchi_eq0 x : (lchi p x == 0) = (x == 0).
Proof.
rewrite /lchi; case: (boolP (x == 0)) => [_|nz] //.
by case: (x ^+ _ == 1).
Qed.

Lemma lchi_sqr x : x != 0 -> lchi p x * lchi p x = 1.
Proof. by move=> nz; rewrite /lchi (negbTE nz); case: (x ^+ _ == 1). Qed.

Lemma lchi1 : lchi p 1 = 1.
Proof. by rewrite /lchi oner_eq0 expr1n eqxx. Qed.

Lemma lchi_eq1 x : lchi p x = 1 <-> x != 0 /\ exists y, y ^+ 2 = x.
Proof using p p_odd p_pr.
have Ec := card_Fp p_pr.
rewrite /lchi; case: (boolP (x == 0)) => [_|nz]; first by split=> // [[]].
have := euler_crit card_Fp_odd nz; rewrite Ec => ec.
case: eqP => h; split => //.
- by move=> _; split => //; apply/ec.
- by case=> _ /ec.

Qed.

Lemma exists_lchi_neg : exists x : 'F_p, lchi p x = -1.
Proof using p p_odd p_pr.
have [x] := exists_nonsq card_Fp_odd; rewrite card_Fp // => xm.
exists x; apply: lchi_inj; rewrite ?lchi_sgn3 // lchi_euler xm.
by rewrite rmorphN rmorph1.
Qed.

Lemma sum_lchi : \sum_(x : 'F_p) lchi p x = 0.
Proof using p p_odd p_pr.
have [g gm] := exists_lchi_neg.
have gnz : g != 0 by rewrite -lchi_eq0 gm.
have : \sum_(x : 'F_p) lchi p x = - \sum_(x : 'F_p) lchi p x.
  rewrite {1}(reindex_inj (mulfI gnz)) /= -sumrN.
  by apply: eq_bigr => x _; rewrite lchiM gm mulN1r.
by move/eqP; rewrite -addr_eq0 -mulr2n mulrn_eq0 /= => /eqP.
Qed.

(* Basic properties of the Legendre symbol. *)

Lemma legendre_sgn3 a : sgn3 (legendre a p).
Proof. exact: lchi_sgn3. Qed.

Lemma legendre_mod a b : (a == b %[mod p])%Z -> legendre a p = legendre b p.
Proof using p p_pr.
by move=> /(intr_pchar_mod (pchar_Fp p_pr)) h; rewrite /legendre h.
Qed.

Lemma legendreM a b : legendre (a * b) p = legendre a p * legendre b p.
Proof using p p_odd p_pr. by rewrite /legendre rmorphM lchiM. Qed.

Lemma legendreX a k : legendre (a ^+ k) p = legendre a p ^+ k.
Proof using p p_odd p_pr.
elim: k => [|k IH]; first by rewrite !expr0 /legendre rmorph1 lchi1.
by rewrite !exprS legendreM IH.
Qed.

Lemma legendre1 : legendre 1 p = 1.
Proof. by rewrite /legendre rmorph1 lchi1. Qed.

Lemma legendre_eq0 a : (legendre a p == 0) = (p %| a)%Z.
Proof using p p_pr. by rewrite /legendre lchi_eq0 (intr_pchar_eq0 (pchar_Fp p_pr)). Qed.

Lemma legendre_sqr a : ~~ (p %| a)%Z -> legendre a p * legendre a p = 1.
Proof using p p_pr. by rewrite -(intr_pchar_eq0 (pchar_Fp p_pr)) => /lchi_sqr. Qed.

(* Euler's criterion, in 'F_p and as an integer congruence. *)
Lemma legendre_euler_Fp a : (legendre a p)%:~R = (a%:~R : 'F_p) ^+ m.
Proof using p p_odd p_pr. exact: lchi_euler. Qed.

Lemma legendre_euler a : (legendre a p == a ^+ m %[mod p])%Z.
Proof using p p_odd p_pr.
by rewrite -(intr_pchar_eq (pchar_Fp p_pr)) legendre_euler_Fp rmorphXn.
Qed.

(* Euler's criterion in any ring of characteristic p. *)
Lemma legendre_euler_pchar (R : nzRingType) a : p \in [pchar R] ->
  (legendre a p)%:~R = (a%:~R : R) ^+ m.
Proof using p p_odd p_pr.
by move=> pR; rewrite -rmorphXn /=; apply/(intr_pchar_mod pR)/legendre_euler.
Qed.

(* (a/p) = 1 iff a is a nonzero square mod p. *)
Lemma legendre_eq1 a : legendre a p = 1 <->
  ~~ (p %| a)%Z /\ exists z : int, (z ^+ 2 == a %[mod p])%Z.
Proof using p p_odd p_pr.
have pF := pchar_Fp p_pr; rewrite /legendre; split.
- case/lchi_eq1 => nz [y yE]; split; first by rewrite -(intr_pchar_eq0 pF).
  exists (y : nat)%:Z; rewrite -(intr_pchar_eq pF) -yE rmorphXn /=.
  by rewrite -pmulrn natr_Zp.
- case=> na [z zE]; apply/lchi_eq1; split; first by rewrite (intr_pchar_eq0 pF).
  by exists z%:~R; rewrite -rmorphXn /=; apply/eqP; rewrite (intr_pchar_eq pF).
Qed.

Lemma legendre_eqN1 a : legendre a p = -1 <->
  ~~ (p %| a)%Z /\ ~ exists z : int, (z ^+ 2 == a %[mod p])%Z.
Proof using p p_odd p_pr.
have h0 := legendre_eq0 a; have h1 := legendre_eq1 a.
split.
- move=> e; have na : ~~ (p %| a)%Z by rewrite -h0 e.
  split=> // hz; have := h1.2 (conj na hz); rewrite e.
  by move=> e'; have := congr1 (fun z : int => z == 1) e'.
- case=> na nz; have n0 : legendre a p != 0 by rewrite h0.
  have n1 : legendre a p <> 1 by case/h1 => _ /nz.
  move: n0 n1; case/orP: (legendre_sgn3 a) => [/orP[]|] /eqP -> //.
Qed.

(* First supplement. *)
Lemma legendre_N1 : legendre (-1) p = (-1) ^+ m.
Proof using p p_odd p_pr.
apply: lchi_inj; rewrite ?lchi_sgn3 //.
  by rewrite /sgn3 -signr_odd; case: odd.
by rewrite lchi_euler rmorphXn /= rmorphN rmorph1.
Qed.

End Legendre.

(* ------------------------------------------------------------------ *)
(* 4. Gauss sums                                                      *)
(* ------------------------------------------------------------------ *)

Section GaussSum.

Variables p q : nat.
Hypotheses (p_pr : prime p) (p_odd : odd p) (q_pr : prime q) (q_odd : odd q).
Hypothesis pq : p != q.
Variable F : finFieldType.
Hypothesis qF : q \in [pchar F].
Variable z : F.
Hypothesis zp : p.-primitive_root z.

Let e (x : 'F_p) : F := z ^+ (x : nat).
Let chi (x : 'F_p) : F := (lchi p x)%:~R.

Let e_nat k : e k%:R = z ^+ k.
Proof. by rewrite /e val_Fp_nat // prim_expr_mod. Qed.

Let eD x y : e (x + y) = e x * e y.
Proof. by rewrite -[x]natr_Zp -[y]natr_Zp -natrD !e_nat exprD. Qed.

Let e0 : e 0 = 1.
Proof. by have := e_nat 0; rewrite mulr0n expr0. Qed.

Let e1 : e 1 = z.
Proof. by have := e_nat 1; rewrite mulr1n expr1. Qed.

Let eMn x k : e (x *+ k) = e x ^+ k.
Proof. by elim: k => [|k IH]; rewrite ?mulr0n ?expr0 ?e0 // mulrS eD IH exprS. Qed.

Let z_neq1 : z != 1.
Proof.
apply/eqP => z1; have := prim_order_dvd zp 1; rewrite expr1 z1 eqxx dvdn1.
by move/eqP => p1; move: p_pr; rewrite p1.
Qed.

Let sum_e : \sum_(x : 'F_p) e x = 0.
Proof.
have h : (\sum_(x : 'F_p) e x) * z = \sum_(x : 'F_p) e x.
  rewrite -e1 mulr_suml [RHS](reindex_inj (addIr (1 : 'F_p))) /=.
  by apply: eq_bigr => x _; rewrite eD.
have : (\sum_(x : 'F_p) e x) * (z - 1) = 0 by rewrite mulrBr mulr1 h subrr.
by move/eqP; rewrite mulf_eq0 subr_eq0 (negbTE z_neq1) orbF => /eqP.
Qed.

Let sum_eM t : \sum_(x : 'F_p) e (x * t) = if t == 0 then p%:R else 0.
Proof.
case: eqP => [->|/eqP tnz].
  have -> : \sum_(x : 'F_p) e (x * 0) = \sum_(x : 'F_p) 1.
    by apply: eq_bigr => x _; rewrite mulr0 e0.
  by rewrite sumr_const card_Fp.
by have := sum_e; rewrite (reindex_inj (mulIf tnz)) /= => ->.
Qed.

Let chi_sum : \sum_(x : 'F_p) chi x = 0.
Proof. by rewrite /chi -rmorph_sum /= sum_lchi // mulr0z. Qed.

Let chiM x y : chi (x * y) = chi x * chi y.
Proof. by rewrite /chi lchiM // rmorphM. Qed.

Let chi_sqr x : x != 0 -> chi x * chi x = 1.
Proof. by move=> nz; rewrite /chi -rmorphM /= lchi_sqr. Qed.

Let chi0 : chi 0 = 0.
Proof. by rewrite /chi lchi0. Qed.

Definition gauss_sum := \sum_(x : 'F_p) (lchi p x)%:~R * z ^+ (x : nat).

Let gaussE : gauss_sum = \sum_(x : 'F_p) chi x * e x.
Proof. by []. Qed.

Lemma gauss_sqr : gauss_sum ^+ 2 = (lchi p (-1))%:~R * p%:R.
Proof using F chi chi0 chiM chi_sqr chi_sum e e0 e1 eD e_nat gaussE p p_odd.
have step x : chi x * e x * gauss_sum = \sum_(c : 'F_p) chi c * e (x * (1 + c)).
  have [->|nz] := eqVneq x 0.
    rewrite chi0 !mul0r (eq_bigr (fun c => chi c)) ?chi_sum // => c _.
    by rewrite mul0r e0 mulr1.
  rewrite gaussE mulr_sumr (reindex_inj (mulfI nz)); apply: eq_bigr => c _.
  rewrite chiM mulrDr mulr1 eD.
  transitivity ((chi x * chi x) * (chi c * (e x * e (x * c)))); first by ring.
  by rewrite chi_sqr // mul1r.
rewrite expr2 {1}gaussE mulr_suml (eq_bigr _ (fun x _ => step x)).
rewrite exchange_big /= (eq_bigr (fun c => chi c * (\sum_(x : 'F_p) e (x * (1 + c))))).
  1: by move=> c _; rewrite mulr_sumr.
rewrite (bigD1 (-1)) //= addrC subrr sum_eM eqxx big1 ?add0r // => c cN1.
by rewrite sum_eM addrC addr_eq0 (negbTE cN1) mulr0.
Qed.

Let pF_neq0 : p%:R != 0 :> F.
Proof. by rewrite -(dvdn_pcharf qF) dvdn_prime2 // eq_sym. Qed.

Let chi_neq0 x : x != 0 -> chi x != 0.
Proof.
move=> nz; apply/eqP => c0; have := chi_sqr nz.
by rewrite c0 mul0r => /eqP; rewrite eq_sym oner_eq0.
Qed.

Lemma gauss_neq0 : gauss_sum != 0.
Proof using All.
have c1 : (lchi p (-1))%:~R != 0 :> F.
  by apply: (chi_neq0 (x := -1)); rewrite oppr_eq0 oner_eq0.
apply/negP => /eqP g0; have := gauss_sqr; rewrite g0 expr0n /= => /esym/eqP.
by rewrite mulf_eq0 (negbTE c1) (negbTE pF_neq0).
Qed.

Let chi_q : (q%:R : 'F_p) != 0.
Proof.
by rewrite -(dvdn_pcharf (pchar_Fp p_pr)) dvdn_prime2.
Qed.

Lemma gauss_frob : gauss_sum ^+ q = chi q%:R * gauss_sum.
Proof using All.
have chiq : chi q%:R * chi q%:R = 1 by exact: chi_sqr.
have h : gauss_sum ^+ q = \sum_(x : 'F_p) chi x * e (x * q%:R).
  rewrite gaussE -(pFrobenius_autE qF) rmorph_sum; apply: eq_bigr => x _.
  rewrite rmorphM /= !(pFrobenius_autE qF) mulr_natr eMn; congr (_ * _).
  rewrite /chi -rmorphXn /=; congr (_%:~R).
  have := lchi_sgn3 x; rewrite /sgn3 => /orP[/orP[]|] /eqP->.
  - by rewrite expr0n gtn_eqF ?prime_gt0.
  - by rewrite expr1n.
  - by rewrite -signr_odd q_odd.
have h' : chi q%:R * gauss_sum ^+ q = gauss_sum.
  rewrite h mulr_sumr gaussE [RHS](reindex_inj (mulIf chi_q)) /=.
  by apply: eq_bigr => x _; rewrite mulrA -chiM [_ * x]mulrC.
by rewrite -[in RHS]h' mulrA chiq mul1r.
Qed.

Lemma gauss_reciprocity :
  lchi p (q%:R) = legendre (lchi p (-1) * p%:Z) q.
Proof using All.
apply: (sgn3_inj qF) => //; rewrite ?lchi_sgn3 //.
rewrite (legendre_euler_pchar q_pr q_odd _ qF) rmorphM /= -pmulrn -gauss_sqr.
apply: (mulfI gauss_neq0); rewrite -exprM -exprS mul2n -odd_halfE // gauss_frob.
by rewrite mulrC.
Qed.

End GaussSum.

(* ------------------------------------------------------------------ *)
(* 5. Quadratic reciprocity                                           *)
(* ------------------------------------------------------------------ *)

(* A finite field of characteristic q containing a primitive k-th root
   of unity, for k dividing q^e - 1 (the field with q^e elements). *)
Lemma exists_field_prim_root (k q e : nat) : prime q -> (0 < e)%N ->
  (k %| (q ^ e).-1)%N ->
  exists (F : finFieldType) (z : F), q \in [pchar F] /\ k.-primitive_root z.
Proof.
move=> q_pr e_gt0 dk.
have [F qF cardF] := pPrimePowerField q_pr e_gt0.
have [w pw] := exists_prim_root F.
exists F, (w ^+ (#|F|.-1 %/ k)); split => //.
by apply: (dvdn_prim_root pw); rewrite cardF.
Qed.

Lemma dvdn_fermat (p q : nat) : prime p -> ~~ (p %| q)%N -> (p %| (q ^ p.-1).-1)%N.
Proof.
move=> p_pr npq; rewrite (dvdn_pcharf (pchar_Fp p_pr)) -subn1.
have q0 : (0 < q)%N by rewrite lt0n; apply: contraNneq npq => ->; exact: dvdn0.
rewrite natrB ?expn_gt0 ?q0 // natrX subr_eq0.
have qnz : (q%:R : 'F_p) != 0 by rewrite -(dvdn_pcharf (pchar_Fp p_pr)).
by have := expf_card1 qnz; rewrite card_Fp // => ->.
Qed.

Lemma legendre_nat_Fp (a : nat) (p : nat) : legendre a%:Z p = lchi p a%:R.
Proof. by rewrite /legendre -pmulrn. Qed.

Lemma legendreN1_lchi (p : nat) : legendre (-1) p = lchi p (-1).
Proof. by rewrite /legendre rmorphN1. Qed.

Theorem quadratic_reciprocity (p q : nat) :
  prime p -> prime q -> odd p -> odd q -> p != q ->
  legendre p q * legendre q p = (-1) ^+ ((p.-1)./2 * (q.-1)./2).
Proof.
move=> p_pr q_pr p_odd q_odd pq.
have npq : ~~ (p %| q)%N by rewrite dvdn_prime2.
have nqp : ~~ (q %| p)%N by rewrite dvdn_prime2 // eq_sym.
have k0 : (0 < p.-1)%N by rewrite -ltnS prednK ?prime_gt0 ?prime_gt1.
have [F [z [qF zp]]] := exists_field_prim_root q_pr k0 (dvdn_fermat p_pr npq).
have := gauss_reciprocity p_pr p_odd q_pr q_odd pq qF zp.
rewrite -legendre_nat_Fp legendreM // -legendreN1_lchi legendre_N1 //.
rewrite legendreX // legendre_N1 // -exprM mulnC => ->.
by rewrite mulrA mulrC mulrA legendre_sqr ?mul1r.
Qed.



(* ------------------------------------------------------------------ *)
(* 6. The second supplement: (2/p)                                    *)
(* ------------------------------------------------------------------ *)

Lemma odd_sqr_mod8 (p : nat) : odd p -> (p ^ 2 %% 8 = 1)%N.
Proof.
move=> po; rewrite -modnXm.
have : odd (p %% 8)%N by rewrite (@odd_mod p 8 erefl) po.
have : (p %% 8 < 8)%N by rewrite ltn_mod.
by case: (p %% 8)%N => [|[|[|[|[|[|[|[|]]]]]]]].
Qed.

Section Supplement2.

Variable p : nat.
Hypotheses (p_pr : prime p) (p_odd : odd p).
Variable F : finFieldType.
Hypothesis pF : p \in [pchar F].
Variable z : F.
Hypothesis z8 : 8.-primitive_root z.

Let z4 : z ^+ 4 = -1.
Proof.
have : (z ^+ 4) ^+ 2 == 1 by rewrite -exprM (prim_expr_order z8).
rewrite sqrf_eq1 => /orP[/eqP|/eqP //].
by move/eqP; rewrite -(prim_order_dvd z8).
Qed.

Let tau := z + z ^+ 7.

Let tau_sqr : tau ^+ 2 = 2%:R.
Proof.
rewrite /tau sqrrD -exprS (prim_expr_order z8) -exprM.
have -> : z ^+ (7 * 2) = - z ^+ 2.
  by rewrite -(prim_expr_mod z8) (_ : (7 * 2) %% 8 = 4 + 2)%N // exprD z4 mulN1r.
by rewrite addrC addrA addNr add0r.
Qed.

Let two_neq0 : 2%:R != 0 :> F.
Proof.
rewrite -(dvdn_pcharf pF); apply/negP => h.
have := dvdn_leq (isT : (0 < 2)%N) h; rewrite leq_eqVlt ltnS => /orP[/eqP p2|].
  by move: p_odd; rewrite p2.
by rewrite leqNgt prime_gt1.
Qed.

Let tau_neq0 : tau != 0.
Proof. by apply: contra_neq two_neq0 => t0; rewrite -tau_sqr t0 expr0n. Qed.

Let tau_frob : tau ^+ p =
  if (p %% 8 == 1)%N || (p %% 8 == 7)%N then tau else - tau.
Proof.
rewrite /tau -(pFrobenius_autE pF) rmorphD /= !(pFrobenius_autE pF) -exprM.
rewrite -(prim_expr_mod z8) -[(z ^+ (7 * p))](prim_expr_mod z8) -modnMmr.
have : odd (p %% 8)%N by rewrite (@odd_mod p 8 erefl) p_odd.
have : (p %% 8 < 8)%N by rewrite ltn_mod.
have z3 : z ^+ 3 = - z ^+ 7.
  by rewrite (_ : 7 = 4 + 3)%N // exprD z4 mulN1r opprK.
have z5 : z ^+ 5 = - z.
  by rewrite (_ : 5 = 4 + 1)%N // exprD z4 mulN1r expr1.
case: (p %% 8)%N => [|[|[|[|[|[|[|[|]]]]]]]] //= _ _.
- by rewrite (_ : (7 * 3) %% 8 = 5)%N // z3 z5 opprD addrC.
- by rewrite (_ : (7 * 5) %% 8 = 3)%N // z3 z5 opprD.
- by rewrite (_ : (7 * 7) %% 8 = 1)%N // expr1 addrC.
Qed.

Lemma legendre_two_mod8 :
  legendre 2 p = if (p %% 8 == 1)%N || (p %% 8 == 7)%N then 1 else -1.
Proof using F p pF p_odd p_pr tau tau_frob tau_neq0 tau_sqr two_neq0 z z4 z8.
apply: (sgn3_inj pF p_odd); [exact: legendre_sgn3 | by case: ifP | ].
apply: (mulfI tau_neq0); rewrite (legendre_euler_pchar p_pr p_odd _ pF).
have t2 : (2%:~R : F) = tau ^+ 2 by rewrite tau_sqr.
rewrite t2 -exprM -exprS mul2n -odd_halfE //.
rewrite tau_frob; case: ifP => _; by rewrite ?rmorph1 ?rmorphN1 ?mulr1 ?mulrN1.
Qed.

End Supplement2.

Lemma sign_mod8 (p : nat) : odd p ->
  (-1) ^+ ((p ^ 2).-1 %/ 8) =
  (if (p %% 8 == 1)%N || (p %% 8 == 7)%N then 1 else -1) :> int.
Proof.
move=> po; have ro : odd (p %% 8)%N by rewrite (@odd_mod p 8 erefl) po.
have rl : (p %% 8 < 8)%N by rewrite ltn_mod.
set r := (p %% 8)%N in ro rl *; set k := (p %/ 8)%N.
have r0 : (0 < r ^ 2)%N by rewrite expn_gt0; case: (r) ro.
have -> : (p ^ 2).-1 = (2 * (k * k * 4 + k * r)) * 8 + (r ^ 2).-1.
  rewrite {1}(divn_eq p 8) -/r -/k.
  have -> : ((k * 8 + r) ^ 2 = (2 * (k * k * 4 + k * r)) * 8 + r ^ 2)%N by ring.
  by rewrite -(prednK r0) addnS.
rewrite divnMDl // exprD exprM sqrrN !expr1n mul1r.
by move: ro rl; case: (r) => [|[|[|[|[|[|[|[|]]]]]]]].
Qed.

Theorem legendre_two_mod8_global (p : nat) : prime p -> odd p ->
  legendre 2 p = if (p %% 8 == 1)%N || (p %% 8 == 7)%N then 1 else -1.
Proof.
move=> p_pr p_odd.
have d8 : (8 %| (p ^ 2).-1)%N.
  have := odd_sqr_mod8 p_odd; rewrite {2}(divn_eq (p ^ 2) 8) => ->.
  by rewrite addn1 /= dvdn_mull.
have [F [z [pF z8]]] := exists_field_prim_root p_pr (isT : (0 < 2)%N) d8.
exact: (legendre_two_mod8 p_pr p_odd pF z8).
Qed.

(* Second supplement: (2/p) = (-1)^((p^2-1)/8). *)
Theorem legendre_two (p : nat) : prime p -> odd p ->
  legendre 2 p = (-1) ^+ ((p ^ 2).-1 %/ 8).
Proof. by move=> p_pr p_odd; rewrite sign_mod8 // legendre_two_mod8_global. Qed.

(* First supplement, restated. *)
Theorem legendre_minus_one (p : nat) : prime p -> odd p ->
  legendre (-1) p = (-1) ^+ (p.-1)./2.
Proof. exact: legendre_N1. Qed.

(* ------------------------------------------------------------------ *)
(* 7. The Jacobi symbol                                               *)
(* ------------------------------------------------------------------ *)

(* (a/n) = prod_{p | n} (a/p)^(v_p(n)); meaningful for odd n > 0. *)
Definition jacobi (a : int) (n : nat) : int :=
  \prod_(p < n.+1 | prime p) legendre a p ^+ logn p n.

Lemma logn_gt_eq0 (p n : nat) : (n < p)%N -> logn p n = 0%N.
Proof.
move=> np; apply/eqP; rewrite eqn0Ngt logn_gt0 mem_primes; apply/negP.
case/and3P=> _ n0 /(dvdn_leq n0); by rewrite leqNgt np.
Qed.

Lemma jacobi_bound (a : int) (n N : nat) : (n <= N)%N ->
  jacobi a n = \prod_(p < N.+1 | prime p) legendre a p ^+ logn p n.
Proof.
move=> nN; rewrite /jacobi (big_ord_widen_cond N.+1 (fun p => prime p)
  (fun p => legendre a p ^+ logn p n)) ?ltnS //.
rewrite [RHS](bigID (fun p : 'I_N.+1 => (p < n.+1)%N)) /= [X in _ = _ * X]big1 ?mulr1 //.
by move=> i /andP[_]; rewrite -leqNgt => /logn_gt_eq0 ->.
Qed.

Lemma jacobiMr (a : int) (n k : nat) : (0 < n)%N -> (0 < k)%N ->
  jacobi a (n * k) = jacobi a n * jacobi a k.
Proof.
move=> n0 k0; rewrite (jacobi_bound a (leqnn (n * k))).
rewrite (jacobi_bound a (leq_pmulr n k0)) (jacobi_bound a (leq_pmull k n0)).
rewrite -big_split /=; apply: eq_bigr => p pp.
by rewrite lognM // exprD.
Qed.

Lemma jacobi1 (a : int) : jacobi a 1 = 1.
Proof. by rewrite /jacobi big1 // => p _; rewrite logn1 expr0. Qed.

Lemma jacobi_prime (a : int) (p : nat) : prime p -> jacobi a p = legendre a p.
Proof.
move=> p_pr; rewrite /jacobi (bigD1 (Ordinal (ltnSn p))) //=.
rewrite logn_prime // eqxx expr1 big1 ?mulr1 // => -[i ip] /= /andP[i_pr ne].
rewrite logn_prime //.
by rewrite (_ : (i == p) = false) ?expr0 //; apply: contraNF ne => /eqP ie;
   apply/eqP/val_inj; rewrite /= ie.
Qed.

Section JacobiOdd.

Variable n : nat.
Hypothesis n_odd : odd n.

Let factor_odd (p : nat) : prime p -> (0 < logn p n)%N -> odd p /\ (p %| n)%N.
Proof.
move=> p_pr; rewrite logn_gt0 mem_primes => /and3P[_ _ pn]; split => //.
by apply: contraLR n_odd; rewrite -!dvdn2 => h; exact: dvdn_trans h pn.
Qed.

Lemma jacobiMl (a b : int) : jacobi (a * b) n = jacobi a n * jacobi b n.
Proof using factor_odd n n_odd.
rewrite /jacobi -big_split /=; apply: eq_bigr => p p_pr.
have [e0|/(factor_odd p_pr)[p_odd _]] := posnP (logn p n).
  by rewrite e0 !expr0 mulr1.
by rewrite legendreM // exprMn.
Qed.

Lemma jacobi_mod (a b : int) : (a == b %[mod n])%Z -> jacobi a n = jacobi b n.
Proof using factor_odd n n_odd.
move=> ab; rewrite /jacobi; apply: eq_bigr => p p_pr.
have [e0|/(factor_odd p_pr)[p_odd pn]] := posnP (logn p n).
  by rewrite e0 !expr0.
congr (_ ^+ _); apply: legendre_mod => //.
move: ab; rewrite !eqz_mod_dvd => /(dvdz_trans _); apply.
by rewrite dvdzE.
Qed.

Lemma jacobi_sqr (a : int) : coprime `|a| n -> jacobi a n * jacobi a n = 1.
Proof using factor_odd n n_odd.
move=> co; rewrite /jacobi -big_split /= big1 // => p p_pr.
have [e0|/(factor_odd p_pr)[p_odd pn]] := posnP (logn p n).
  by rewrite e0 !expr0 mulr1.
rewrite -exprMn legendre_sqr ?expr1n //; rewrite dvdzE /=.
apply/negP => pa; have := co; rewrite /coprime => /eqP g1.
have : (p %| gcdn `|a| n)%N by rewrite dvdn_gcd pa pn.
by rewrite g1 dvdn1 => /eqP p1; move: p_pr; rewrite p1.
Qed.

End JacobiOdd.

(* Multiplicative induction over odd positive integers. *)
Lemma odd_mult_ind (P : nat -> Prop) :
  P 1%N -> (forall p, prime p -> odd p -> P p) ->
  (forall a b, odd a -> odd b -> P a -> P b -> P (a * b)%N) ->
  forall n, odd n -> P n.
Proof.
move=> P1 Pp PM n; elim/ltn_ind: n => n IH n_odd.
have [n1|n1] := leqP n 1.
  by have -> : n = 1%N by apply/eqP; rewrite eqn_leq n1; case: (n) n_odd.
have d_pr := pdiv_prime n1; have dn := pdiv_dvd n.
have dpos := prime_gt1 d_pr.
rewrite -(divnK dn).
have : odd (n %/ pdiv n * pdiv n)%N by rewrite divnK.
rewrite oddM => /andP[o1 o2].
apply: PM => //; last by apply: Pp.
apply: IH => //; rewrite ltn_Pdiv //.
by case: (n) n1.
Qed.

Lemma sign4M (a b : nat) : odd a -> odd b ->
  (-1) ^+ ((a * b).-1)./2 = (-1) ^+ (a.-1)./2 * (-1) ^+ (b.-1)./2 :> int.
Proof.
move=> /odd_halfE ea /odd_halfE eb; rewrite {1}ea {1}eb.
set x := (a.-1)./2; set y := (b.-1)./2.
have -> : (x.*2.+1 * y.*2.+1 = (2 * x * y + x + y).*2.+1)%N.
  by rewrite -!muln2; ring.
rewrite /= !doubleK -signr_odd !oddD !oddM /= signr_addb.
by rewrite !signr_odd.
Qed.

Lemma sign8M (a b : nat) : odd a -> odd b ->
  (-1) ^+ (((a * b) ^ 2).-1 %/ 8) =
  (-1) ^+ ((a ^ 2).-1 %/ 8) * (-1) ^+ ((b ^ 2).-1 %/ 8) :> int.
Proof.
move=> oa ob; rewrite !sign_mod8 ?oddM ?oa ?ob //.
rewrite -modnMm.
have ra : odd (a %% 8)%N by rewrite (@odd_mod a 8 erefl).
have rb : odd (b %% 8)%N by rewrite (@odd_mod b 8 erefl).
have la : (a %% 8 < 8)%N by rewrite ltn_mod.
have lb : (b %% 8 < 8)%N by rewrite ltn_mod.
move: ra rb la lb; case: (a %% 8)%N => [|[|[|[|[|[|[|[|]]]]]]]] //;
  case: (b %% 8)%N => [|[|[|[|[|[|[|[|]]]]]]]] //.
Qed.

Lemma jacobi_1l (n : nat) : jacobi 1 n = 1.
Proof. by rewrite /jacobi big1 // => p _; rewrite legendre1 expr1n. Qed.

(* The supplements for the Jacobi symbol. *)
Theorem jacobi_minus_one (n : nat) : odd n -> jacobi (-1) n = (-1) ^+ (n.-1)./2.
Proof.
elim/odd_mult_ind => [|p p_pr p_odd|a b oa ob IHa IHb].
- by rewrite jacobi1.
- by rewrite jacobi_prime // legendre_N1.
- by rewrite jacobiMr ?odd_gt0 // IHa IHb sign4M.
Qed.

Theorem jacobi_two (n : nat) : odd n -> jacobi 2 n = (-1) ^+ ((n ^ 2).-1 %/ 8).
Proof.
elim/odd_mult_ind => [|p p_pr p_odd|a b oa ob IHa IHb].
- by rewrite jacobi1.
- by rewrite jacobi_prime // legendre_two.
- by rewrite jacobiMr ?odd_gt0 // IHa IHb sign8M.
Qed.

Section JacobiReciprocity.

Let eps (m n : nat) : int := (-1) ^+ ((m.-1)./2 * (n.-1)./2).

Let epsC m n : eps m n = eps n m.
Proof. by rewrite /eps mulnC. Qed.

Let epsMl a b n : odd a -> odd b -> eps (a * b) n = eps a n * eps b n.
Proof. by move=> oa ob; rewrite /eps !exprM sign4M // exprMn. Qed.

Let eps1 n : eps 1 n = 1.
Proof. by rewrite /eps mul0n expr0. Qed.

Let rec_prime (q : nat) : prime q -> odd q ->
  forall m, odd m -> coprime m q -> jacobi m q * jacobi q m = eps m q.
Proof.
move=> q_pr q_odd.
apply: odd_mult_ind => [|p p_pr p_odd|a b oa ob IHa IHb] co.
- by rewrite jacobi1 jacobi_1l mul1r eps1.
- have pq : p != q.
    by apply: contraTneq co => ->; rewrite prime_coprime // dvdnn.
  by rewrite !jacobi_prime // quadratic_reciprocity.
- move: co; rewrite coprimeMl => /andP[ca cb].
  rewrite PoszM jacobiMl // jacobiMr ?odd_gt0 // epsMl // -IHa // -IHb //.
  by rewrite mulrACA.
Qed.

(* Reciprocity for the Jacobi symbol. *)
Theorem jacobi_reciprocity (m n : nat) : odd m -> odd n -> coprime m n ->
  jacobi m n * jacobi n m = (-1) ^+ ((m.-1)./2 * (n.-1)./2).
Proof.
move=> om on; rewrite -/(eps m n); move: m om; move: n on.
apply: odd_mult_ind => [|q q_pr q_odd|a b oa ob IHa IHb] m om co.
- by rewrite jacobi1 jacobi_1l mul1r epsC eps1.
- exact: rec_prime.
- move: co; rewrite coprimeMr => /andP[ca cb].
  rewrite PoszM jacobiMl // jacobiMr ?odd_gt0 // epsC epsMl // -!(epsC m).
  by rewrite -IHa // -IHb // mulrACA.
Qed.

End JacobiReciprocity.

(* ------------------------------------------------------------------ *)
(* 8. Prescribing Legendre symbols by a residue class (CRT)           *)
(* ------------------------------------------------------------------ *)

Lemma eqz_mod_nat (a b m : nat) : (a%:Z == b%:Z %[mod m])%Z = (a == b %[mod m])%N.
Proof. by rewrite !modz_nat eqz_nat. Qed.

Lemma eqz_mod_dvdm (x y : int) (d m : nat) : (d %| m)%N ->
  (x == y %[mod m])%Z -> (x == y %[mod d])%Z.
Proof.
move=> dm; rewrite !eqz_mod_dvd => /(dvdz_trans _); apply; by rewrite dvdzE.
Qed.

Lemma sign_half_mod4 (a : nat) : odd a ->
  (-1) ^+ (a.-1)./2 = (-1) ^+ ((a %% 4).-1)./2 :> int.
Proof.
move=> ao; have so : odd (a %% 4)%N by rewrite (@odd_mod a 4 erefl).
rewrite {1}(divn_eq a 4); set k := (a %/ 4)%N; set s := (a %% 4)%N in so *.
have s0 : (0 < s)%N by case: (s) so.
rewrite -(prednK s0) addnS /= -!divn2.
rewrite (_ : k * 4 = k * 2 * 2)%N; first by rewrite -mulnA.
by rewrite divnMDl // exprD mulnC exprM sqrrN !expr1n mul1r.
Qed.

(* A residue (as a natural number) with prescribed Legendre symbol. *)
Lemma exists_legendre_value (p : nat) (b : bool) : prime p -> odd p ->
  exists c : nat, legendre c p = (if b then 1 else -1).
Proof.
move=> p_pr p_odd; case: b; first by exists 1%N; rewrite legendre1.
have [x xE] := exists_lchi_neg p_pr p_odd.
by exists (x : nat); rewrite legendre_nat_Fp natr_Zp.
Qed.

Lemma prime_coprime_prod (p : nat) (ps : seq nat) : prime p -> odd p ->
  all prime ps -> p \notin ps -> coprime p (8 * \prod_(q <- ps) q).
Proof.
move=> p_pr p_odd aps nps; rewrite coprimeMr; apply/andP; split.
  rewrite (_ : 8 = 2 ^ 3)%N // coprime_pexpr // coprimen2 //.
rewrite prime_coprime // Euclid_dvd_prod //; apply/negP.
elim: ps aps nps => [|q ps IH]; first by rewrite big_nil.
rewrite big_cons inE negb_or /=.
case/andP=> q_pr aps /andP[pq nps] /orP[|/(IH aps nps)//].
by rewrite dvdn_prime2 // (negbTE pq).
Qed.

Lemma prod_primes_gt0 (ps : seq nat) : all prime ps -> (0 < \prod_(p <- ps) p)%N.
Proof.
elim: ps => [|q ps IH]; first by rewrite big_nil.
move=> /= /andP[q_pr aps]; rewrite big_cons muln_gt0 (prime_gt0 q_pr).
exact: IH.
Qed.

Section Pattern.

Variable eps : nat -> bool.
Variable r : nat.
Hypothesis r_odd : odd r.

Local Abbreviation sgn b := (if b then 1 else -1 : int).

Lemma legendre_pattern_nat (ps : seq nat) :
  uniq ps -> all prime ps -> all odd ps ->
  exists a : nat, coprime a (8 * \prod_(p <- ps) p) /\ (a = r %[mod 8])%N /\
    forall p, p \in ps -> legendre a p = sgn (eps p).
Proof using eps r r_odd.
elim: ps => [|p ps IH] /=.
  move=> _ _ _; exists r; split; last by [].
  by rewrite big_nil muln1 (_ : 8 = 2 ^ 3)%N // coprime_pexpr // coprimen2.
case/andP=> nps ups /andP[p_pr aps] /andP[p_odd ops].
have [a0 [co0 [a0r a0e]]] := IH ups aps ops.
set M0 := (8 * \prod_(q <- ps) q)%N in co0 *.
have [c ce] := exists_legendre_value (eps p) p_pr p_odd.
have coM : coprime M0 p by rewrite coprime_sym prime_coprime_prod.
set a := chinese M0 p a0 c.
have aM0 : (a = a0 %[mod M0])%N by apply: chinese_modl.
have ap : (a = c %[mod p])%N by apply: chinese_modr.
have d8 : (8 %| M0)%N by apply: dvdn_mulr.
exists a; split; [|split].
- rewrite big_cons mulnCA coprimeMr; apply/andP; split.
    rewrite -coprime_modl ap coprime_modl coprime_sym prime_coprime //.
    have : legendre c p != 0 by rewrite ce; case: (eps p).
    by rewrite legendre_eq0 // dvdzE.
  by rewrite -coprime_modl aM0 coprime_modl.
- by rewrite -(modn_dvdm _ d8) aM0 (modn_dvdm _ d8).
- move=> q; rewrite inE => /orP[/eqP->|qps].
    by rewrite -ce; apply: legendre_mod => //; rewrite eqz_mod_nat; apply/eqP.
  rewrite -a0e //; apply: (legendre_mod (allP aps q qps)).
  apply: (@eqz_mod_dvdm _ _ _ M0); last by rewrite eqz_mod_nat; apply/eqP.
  by apply: dvdn_mull; rewrite (big_rem q qps) /= dvdn_mulr.
Qed.

(* Main form: a residue class a mod M = 8 * prod ps, a = r mod 8, such that
   every integer x = a mod M has the prescribed symbols (x/p). *)
Theorem legendre_pattern (ps : seq nat) :
  uniq ps -> all prime ps -> all odd ps ->
  exists a : nat, let M := (8 * \prod_(p <- ps) p)%N in
    [/\ (a < M)%N, coprime a M, (a = r %[mod 8])%N &
    forall x : int, (x = a %[mod M])%Z ->
      forall p, p \in ps -> legendre x p = sgn (eps p)].
Proof using eps r r_odd.
move=> ups aps ops; have [a [co [ar ae]]] := legendre_pattern_nat ups aps ops.
set M := (8 * \prod_(p <- ps) p)%N in co *.
have M0 : (0 < M)%N by rewrite muln_gt0 prod_primes_gt0.
exists (a %% M)%N; split.
- by rewrite ltn_mod.
- by rewrite coprime_modl.
- by rewrite (modn_dvdm _ (dvdn_mulr _ (dvdnn 8))).
- move=> x xa p pps; rewrite -ae //.
  apply: (legendre_mod (allP aps p pps)).
  apply: (@eqz_mod_dvdm _ _ _ M); first by apply: dvdn_mull; rewrite (big_rem p pps) /= dvdn_mulr.
  by apply/eqP; rewrite xa modz_nat modn_mod -modz_nat.
Qed.

(* For a prime q in the class a mod M, all symbols (q/p), (p/q), (-1/q),
   (2/q) are determined: (q/p) = eps p, and by reciprocity
   (p/q) = eps p * (-1)^((p-1)/2 * (r-1)/2). *)
Theorem legendre_pattern_prime (ps : seq nat) :
  uniq ps -> all prime ps -> all odd ps ->
  exists a : nat, let M := (8 * \prod_(p <- ps) p)%N in
    [/\ (a < M)%N, coprime a M, (a = r %[mod 8])%N &
    forall q : nat, prime q -> (q%:Z = a %[mod M])%Z ->
      [/\ forall p, p \in ps -> legendre q p = sgn (eps p),
          forall p, p \in ps ->
            legendre p q = sgn (eps p) * (-1) ^+ ((p.-1)./2 * (r.-1)./2),
          legendre (-1) q = (-1) ^+ (r.-1)./2 &
          legendre 2 q = (-1) ^+ ((r ^ 2).-1 %/ 8)]].
Proof using eps r r_odd.
move=> ups aps ops; have [a [aM co ar ae]] := legendre_pattern ups aps ops.
set M := (8 * \prod_(p <- ps) p)%N in aM co ae *.
exists a; split => // q q_pr qa.
have qaN : (q = a %[mod M])%N by apply/eqP; rewrite -eqz_mod_nat; apply/eqP.
have d8M : (8 %| M)%N by apply: dvdn_mulr.
have q8 : (q = r %[mod 8])%N.
  by rewrite -(modn_dvdm q d8M) qaN (modn_dvdm a d8M) ar.
have q4 : (q = r %[mod 4])%N.
  by rewrite -(@modn_dvdm 8 q 4 isT) q8 (@modn_dvdm 8 r 4 isT).
have q_odd : odd q by rewrite -(@odd_mod q 8 erefl) q8 (@odd_mod r 8 erefl).
have sq : (-1) ^+ (q.-1)./2 = (-1) ^+ (r.-1)./2 :> int.
  by rewrite sign_half_mod4 // q4 -sign_half_mod4.
have qp p : p \in ps -> legendre q p = sgn (eps p) by move=> pps; exact: ae.
split => //.
- move=> p pps; have p_pr := allP aps p pps; have p_odd := allP ops p pps.
  have pq : p != q.
    apply/eqP => e; have := qp p pps; rewrite e.
    have /eqP -> : legendre q q == 0 by rewrite legendre_eq0 // dvdzE dvdnn.
    by case: (eps q).
  have := quadratic_reciprocity p_pr q_pr p_odd q_odd pq.
  rewrite qp // mulnC exprM sq -exprM mulnC => <-.
  by rewrite mulrCA; case: (eps p); rewrite ?mulr1 ?mulrNN ?mulr1.
- by rewrite legendre_N1 // sq.
- by rewrite legendre_two // !sign_mod8 // q8.
Qed.

End Pattern.
