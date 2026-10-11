(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Assembly: Dirichlet's theorem for Legendre-symbol patterns (PLAN.md
   Phase 4, task D5; DIRICHLET_DESIGN.md, Sec. 8). For a list ps of
   distinct odd primes, signs eps and an odd residue r mod 8 there are
   arbitrarily large primes q with q = r (mod 8) and (q/p) = eps p for
   all p in ps. This replaces the [Dirichlet] hypothesis of
   PP1Assembly.new_prime.

   Route (DIRICHLET_DESIGN.md, Sec. 3 "Conclusion"). With M := DMod ps
   = 8 * prod ps, the basis of quadratic characters and [chiS] of
   DChar.v, and sigma : basis -> {+-1}:
   - [PS sigma x := sum_(p <= x prime, pattern sigma p) log p / p];
   - [PS_expand] (orthogonality, pointwise in the precision index k):
       2^(k+2) PS x = sum_S (prod_(b in S) sigma b) *
                       sum_(p <= x prime, coprime p M) chiS S p log p / p;
   - [PS_split]: the S = set0 term is the sum of log p / p over the
     primes p <= x coprime to M; every S <> set0 term is bounded
     ([Bco_bound], from the analytic core applied to [chiS S], plus the
     finitely many primes dividing M, [noncop_sum_le]);
   - [PS_lower]: log x - C <= 2^(k+2) PS x (from [sum_rlog_primes_lower]);
   - [pattern_primes_unbounded]: if the pattern primes were bounded by N,
     PS x = PS N for x >= N would be bounded, contradicting
     [rlog_unbounded] (classical: [NNPP]);
   - [legendre_pattern_exists] (via [pattern_sigma_ofP]) and
     [new_prime_nodir_gt], [new_prime_nodir] (second conjunct by
     [quadratic_reciprocity], as in QuadRec.legendre_pattern_prime).
   Generic helper: [exists_bound_big] (finitely many uniformly bounded
   sequences have a uniformly bounded sum; induction on the index list,
   no choice).

   The analytic core is DirichletQuad.sum_chi_rlog_primes_bounded
   (sum_(p <= x) chi(p) log p / p = O(1) for a nontrivial quadratic
   character chi), used once, in [chiS_bound]. The file is closed: the
   only axiom used is [Classical_Prop.classic].

   [sgnb] (DChar.v) is convertible to PP1Assembly's [sgn_bool].

   Arguments of lemmas are implicit exactly when they occur in a
   hypothesis. *)

From Stdlib Require Import PeanoNat Setoid Morphisms Classical_Prop.
From mathcomp Require Import boot order algebra.
From Undecidability.H10.Rational Require Import RSeq RLog QuadRec DChar DirichletQuad.
Import Order.TTheory GRing.Theory Num.Theory.

Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(** * 1. Generic helpers *)

(* Finitely many uniformly bounded families have a uniformly bounded sum.
   The constants are collected one at a time by induction on the index
   list: no choice. *)
Lemma exists_bound_big {T : Type} (I : seq T) (P : pred T) {G : T -> nat -> rseq} :
  (forall i, P i -> exists C : rat, forall x, rle (rabs (G i x)) (cst C)) ->
  exists C : rat, forall x, rle (rabs (fun k => \sum_(i <- I | P i) G i x k)) (cst C).
Proof.
move=> hG; elim: I => [|i I [C hC]].
  by exists 0 => x; apply: rle_of_ptwise => k; rewrite /rabs /cst big_nil normr0.
case: (boolP (P i)) => Pi.
  have [Ci hCi] := hG i Pi; exists (Ci + C) => x.
  apply: rle_trans (_ : rle _ (radd (rabs (G i x))
                         (rabs (fun k => \sum_(j <- I | P j) G j x k)))) _.
    by apply: rle_of_ptwise => k; rewrite /rabs /radd big_cons Pi ler_normD.
  exact: rle_req_trans (rle_add (hCi x) (hC x)) (radd_cst _ _).
exists C => x; apply: rle_trans (hC x).
by apply: rle_of_ptwise => k; rewrite /rabs big_cons (negbTE Pi).
Qed.

Lemma sum1_size (s : seq nat) : \sum_(p <- s) (1 : rat) = (size s)%:R.
Proof.
elim: s => [|a s IH]; first by rewrite big_nil.
by rewrite big_cons IH /= -addn1 natrD addrC.
Qed.

Lemma rlog_mono' {m n : nat} : (m <= n)%N -> rle (rlog m) (rlog n).
Proof.
case: m => [|m] h; last exact: rlog_mono.
by apply: rle_of_ptwise => k; rewrite rlog0; apply: rlog_ge0_pt.
Qed.

Lemma wlog_ge0 (p : nat) k : 0 <= rdiv (rlog p) (cst p%:R) k.
Proof. by rewrite /rdiv /cst divr_ge0 ?rlog_ge0_pt ?ler0n. Qed.

Lemma wlog_le1 {p : nat} : prime p -> forall k, rdiv (rlog p) (cst p%:R) k <= 1.
Proof.
move=> pp k; rewrite /rdiv /cst ler_pdivrMr ?ltr0n ?prime_gt0 // mul1r.
rewrite (rlog_prime pp); exact: le_trans (lrs_le_harm_pt p k) (harm_le_nat p).
Qed.

(* ------------------------------------------------------------------ *)
(** * 2. Pattern primes are unbounded *)

Section Patterns.

Variable ps : seq nat.
Hypotheses (ps_uniq : uniq ps) (ps_prime : all prime ps) (ps_odd : all odd ps).

Local Abbreviation M := (DMod ps).
Local Abbreviation basis := 'I_(size ps).+2.
Local Abbreviation w p := (rdiv (rlog p) (cst p%:R)).

Lemma chiS_1 (S : {set basis}) : chiS S 1 = 1.
Proof using ps_odd ps_prime.
have h := chiS_mul ps_prime ps_odd S 1 1; rewrite muln1 in h.
have nz := chiS_coprime ps_prime S (coprime1n M).
by apply/esym/(mulfI nz); rewrite mulr1 -h.
Qed.

(* The analytic core, applied to chiS S. *)
Lemma chiS_bound {S : {set basis}} : S != set0 ->
  exists C : rat, forall x, rle (rabs (rsum (fun p => rmul (cst (chiS S p)%:~R) (w p))
                                         [seq p <- iota 1 x | prime p])) (cst C).
Proof using ps_odd ps_prime ps_uniq.
move=> S0; apply: (sum_chi_rlog_primes_bounded (chiS S) M (M_gt0 ps_prime)).
- exact: chiS_mul ps_prime ps_odd S.
- exact: chiS_le1.
- exact: chiS_1.
- by move=> x y; have := chiS_window_rat ps_uniq ps_prime ps_odd x y S0.
Qed.

(* Splitting a prime sum into primes coprime / not coprime to M. *)
Lemma split_cop (F : nat -> rseq) x k :
  rsum F [seq p <- iota 1 x | prime p] k =
  rsum F [seq p <- iota 1 x | prime p && coprime p M] k +
  \sum_(p <- iota 1 x | prime p && ~~ coprime p M) F p k.
Proof. by rewrite /rsum !big_filter (bigID (fun p => coprime p M)). Qed.

(* The primes not coprime to M are among the divisors of M. *)
Lemma noncop_size x : (size [seq p <- iota 1 x | prime p && ~~ coprime p M] <= M)%N.
Proof using ps_prime.
have sub : {subset [seq p <- iota 1 x | prime p && ~~ coprime p M] <= iota 1 M}.
  move=> p; rewrite mem_filter => /andP[/andP[pp]]; rewrite prime_coprime // negbK => pM _.
  rewrite mem_iota add1n ltnS (dvdn_leq (M_gt0 ps_prime) pM) andbT; exact: prime_gt0.
apply: leq_trans (uniq_leq_size (filter_uniq _ (iota_uniq 1 x)) sub) _.
by rewrite size_iota.
Qed.

Lemma noncop_norm_le (c : nat -> rat) x k : (forall p, `|c p| <= 1) ->
  `|\sum_(p <- iota 1 x | prime p && ~~ coprime p M) c p * w p k| <= M%:R.
Proof using ps_prime.
move=> hc; apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (_ : _ <= \sum_(p <- iota 1 x | prime p && ~~ coprime p M) 1) _.
  apply: ler_sum => p /andP[pp _]; rewrite normrM (ger0_norm (wlog_ge0 p k)).
  by apply: mulr_ile1; rewrite ?normr_ge0 ?wlog_ge0 ?hc ?wlog_le1.
by rewrite -big_filter sum1_size ler_nat noncop_size.
Qed.

Lemma noncop_sum_le x k :
  0 <= \sum_(p <- iota 1 x | prime p && ~~ coprime p M) w p k <= M%:R.
Proof using ps_prime.
apply/andP; split; first by apply: sumr_ge0 => p _; apply: wlog_ge0.
have h1 : forall p : nat, `|(fun _ : nat => 1 : rat) p| <= 1 by move=> _; rewrite normr1.
have := noncop_norm_le (fun _ => 1) x k h1.
by under eq_bigr do rewrite mul1r; move/(le_trans (ler_norm _)).
Qed.

(* The character sums over primes coprime to M. *)
Definition Bco (S : {set basis}) (x : nat) : rseq :=
  rsum (fun p => rmul (cst (chiS S p)%:~R) (w p)) [seq p <- iota 1 x | prime p && coprime p M].

Lemma Bco_bound {S : {set basis}} : S != set0 ->
  exists C : rat, forall x, rle (rabs (Bco S x)) (cst C).
Proof using ps_odd ps_prime ps_uniq.
move=> S0; have [C hC] := chiS_bound S0; exists (C + M%:R) => x.
apply: rle_trans (_ : rle _ (radd (rabs (rsum (fun p => rmul (cst (chiS S p)%:~R) (w p))
                                         [seq p <- iota 1 x | prime p])) (cst M%:R))) _.
  apply: rle_of_ptwise => k; rewrite /rabs /radd /cst /Bco.
  have eA := split_cop (fun p => rmul (cst (chiS S p)%:~R) (w p)) x k.
  have hE := noncop_norm_le (fun p => (chiS S p)%:~R) x k.
  move: eA hE; rewrite /rmul /cst /=.
  set F := rsum _ [seq p <- iota 1 x | prime p] k.
  set A := rsum _ [seq p <- iota 1 x | prime p && coprime p M] k.
  set E := \sum_(_ <- _ | _) _.
  move=> eA hE; have hE' : `|E| <= M%:R.
    by apply: hE => p; rewrite -intr_norm lerz1 chiS_le1.
  have eA2 : A = F - E by rewrite eA addrK.
  by rewrite eA2; apply: le_trans (ler_normB F E) _; rewrite lerD2l.
exact: rle_req_trans (rle_add (hC x) (rle_refl _)) (radd_cst _ _).
Qed.

Section Pattern.

Variable sigma : basis -> int.
Hypothesis sigma_pm1 : forall b, sigma b = 1 \/ sigma b = -1.

Lemma sigma_neq0 b : sigma b != 0.
Proof using sigma_pm1. by case: (sigma_pm1 b) => ->. Qed.

Lemma prod_sigma_norm (S : {set basis}) : `|(\prod_(b in S) sigma b)%:~R : rat| = 1.
Proof using sigma_pm1.
rewrite -intr_norm normr_prod big1 // => b _.
by case: (sigma_pm1 b) => ->; rewrite ?normrN normr1.
Qed.

(* The weighted sum over the primes with pattern sigma. *)
Definition PS (x : nat) : rseq :=
  rsum (fun p => rdiv (rlog p) (cst p%:R)) [seq p <- iota 1 x | prime p && pattern sigma p].

Lemma PS_expand x k :
  (2 ^ (size ps).+2)%:R * PS x k =
  \sum_(S : {set basis}) (\prod_(b in S) sigma b)%:~R *
     rsum (fun p => rmul (cst (chiS S p)%:~R) (rdiv (rlog p) (cst p%:R)))
          [seq p <- iota 1 x | prime p && coprime p M] k.
Proof using ps_prime sigma_pm1.
rewrite /PS /rsum big_filter.
have -> : \sum_(p <- iota 1 x | prime p && pattern sigma p) w p k =
          \sum_(p <- iota 1 x | prime p && coprime p M) (pattern sigma p)%:R * w p k.
  rewrite big_mkcond [RHS]big_mkcond; apply: eq_bigr => p _.
  case: (prime p) => //=; case: (boolP (pattern sigma p)) => pat.
    by rewrite (pattern_coprime ps_prime sigma_neq0 pat) mul1r.
  by case: coprime; rewrite ?mul0r.
have hexp : forall p, prime p && coprime p M ->
    (2 ^ (size ps).+2)%:R * ((pattern sigma p)%:R * w p k) =
    \sum_(S : {set basis}) (\prod_(b in S) sigma b)%:~R * (chiS S p)%:~R * w p k.
  by move=> p /andP[_ cop]; rewrite mulrA (pattern_expand ps_prime sigma_pm1 cop) mulr_suml.
rewrite mulr_sumr (eq_bigr _ hexp).
rewrite exchange_big /=; apply: eq_bigr => S _.
by rewrite big_filter mulr_sumr; apply: eq_bigr => p _; rewrite /rmul /cst mulrA.
Qed.

Lemma PS_expand_req x :
  req (rmul (cst (2 ^ (size ps).+2)%:R) (PS x))
      (fun k => \sum_(S : {set basis}) (\prod_(b in S) sigma b)%:~R *
         rsum (fun p => rmul (cst (chiS S p)%:~R) (rdiv (rlog p) (cst p%:R)))
              [seq p <- iota 1 x | prime p && coprime p M] k).
Proof using ps_prime sigma_pm1. by apply: req_of_eq => k; apply: PS_expand. Qed.

Lemma PS_split x k :
  (2 ^ (size ps).+2)%:R * PS x k =
  rsum (fun p => w p) [seq p <- iota 1 x | prime p && coprime p M] k +
  \sum_(S | S != set0) (\prod_(b in S) sigma b)%:~R * Bco S x k.
Proof using ps_prime sigma_pm1.
rewrite PS_expand (bigD1 set0) //= big_set0 mul1r; congr (_ + _).
by apply: eq_bigr => p _; rewrite /rmul /cst chiS_set0 mul1r.
Qed.

Lemma PS_lower : exists C : rat, forall x,
  rle (rsub (rlog x) (cst C)) (rmul (cst (2 ^ (size ps).+2)%:R) (PS x)).
Proof using ps_odd ps_prime ps_uniq sigma_pm1.
have hG : forall S : {set basis}, S != set0 -> exists C : rat, forall x,
    rle (rabs (fun k => (\prod_(b in S) sigma b)%:~R * Bco S x k)) (cst C).
  move=> S S0; have [C hC] := Bco_bound S0; exists C => x; apply: rle_trans (hC x).
  by apply: rle_of_ptwise => k; rewrite /rabs normrM prod_sigma_norm mul1r.
have [C1 hC1] := exists_bound_big (index_enum {set basis}) (fun S => S != set0) hG.
exists (9 + M%:R + C1) => x e he; have he2 : 0 < e / 2 by lra.
have [N1 h1] := sum_rlog_primes_lower x (e / 2) he2.
have [N2 h2] := hC1 x (e / 2) he2.
exists (N1 + N2)%N => k hk.
have := h1 k (le_addl_trans hk); have := h2 k (le_addr_trans hk).
rewrite /rsub /rmul /cst /rabs PS_split.
have := split_cop (fun p => w p) x k; have := noncop_sum_le x k.
set F := rsum _ [seq p <- _ | prime p] k; set A := rsum _ _ k.
set E := \sum_(_ <- _ | _) _; set Z := \sum_(_ | _) _; set L := rlog x k.
move=> /andP[hE0 hE1] eF hZ hL; rewrite eF in hL; nlra.
Qed.

Lemma PS_stable {N x : nat} : (forall q, prime q -> pattern sigma q -> (q <= N)%N) ->
  (N <= x)%N -> forall k, PS x k = PS N k.
Proof.
move=> hq hNx k; rewrite /PS -(subnKC hNx) iotaD filter_cat /rsum big_cat /=.
have -> : [seq p <- iota (1 + N) (x - N) | prime p && pattern sigma p] = [::].
  apply/eqP; rewrite -size_eq0 size_filter -leqn0 leqNgt -has_count; apply/hasPn => p.
  rewrite mem_iota add1n => /andP[Np _]; apply/negP => /andP[pp pat].
  by move: (hq p pp pat); rewrite leqNgt Np.
by rewrite big_nil addr0.
Qed.

Theorem pattern_primes_unbounded (N : nat) :
  exists q, [/\ prime q, (N < q)%N & pattern sigma q].
Proof using ps_odd ps_prime ps_uniq sigma_pm1.
apply: NNPP => hno.
have hq : forall q, prime q -> pattern sigma q -> (q <= N)%N.
  move=> q pq pat; rewrite leqNgt; apply/negP => Nq; apply: hno; by exists q.
have [C hC] := PS_lower.
have cN : cauchy (PS N) by apply: cauchy_rsum => p _; apply: rlog_div_cauchy.
have [B hB] := cauchy_rle_cst cN.
set c : rat := (2 ^ (size ps).+2)%:R.
have c0 : 0 <= c by apply: ler0n.
have [n hn] := rlog_unbounded (c * B + C).
set x := maxn n N.
have h2 : rle (rsub (rlog x) (cst C)) (cst (c * B)).
  apply: rle_trans (hC x) _.
  apply: req_rle_trans (_ : req _ (rmul (cst c) (PS N))) _.
    by apply: req_of_eq => k; rewrite /rmul (PS_stable hq (leq_maxr n N)).
  exact: rle_req_trans (rle_rmul_cst c c0 hB) (rmul_cst _ _).
have [e [he [N1 h1]]] := rlt_rle_trans hn (rlog_mono' (leq_maxl n N)).
have he2 : 0 < e / 2 by lra.
have [N2 h2'] := h2 (e / 2) he2.
have := h1 (N1 + N2)%N (leq_addr _ _); have := h2' (N1 + N2)%N (leq_addl _ _).
rewrite /rsub /cst; lra.
Qed.

End Pattern.

(* ------------------------------------------------------------------ *)
(** * 3. Primes with prescribed Legendre symbols *)

Theorem legendre_pattern_exists (eps : nat -> bool) (r N : nat) : odd r ->
  exists q, [/\ prime q, (N < q)%N, q \notin ps, (q %% 8 = r %% 8)%N &
    forall p, p \in ps -> legendre q%:Z p = sgnb (eps p)].
Proof using ps_odd ps_prime ps_uniq.
move=> ro.
have [q [qp Nq pat]] :=
  pattern_primes_unbounded _ (sigma_of_pm1 (ps:=ps) r eps) (maxn N (maxn 2 (\max_(p <- ps) p))).
move: Nq; rewrite !gtn_max => /andP[Nq /andP[q2 qmax]].
have qodd : odd q by case: (even_prime qp) => // e; rewrite e in q2.
have qnot : q \notin ps.
  apply/negP => qin; have := @leq_bigmax_seq _ ps xpredT (fun p => p) q qin isT.
  by rewrite leqNgt qmax.
have [h8 hl] := (pattern_sigma_ofP eps ro qodd qp qnot).1 pat.
by exists q; split.
Qed.

End Patterns.

(* The replacement for PP1Assembly.new_prime, without the [Dirichlet]
   premise, and with an additional lower bound N < q. *)
Theorem new_prime_nodir_gt (eps : nat -> bool) (r N : nat) (ps : seq nat) :
  odd r -> uniq ps -> all prime ps -> all odd ps ->
  exists q : nat, [/\ prime q, (N < q)%N, q \notin ps, (q %% 8 = r %% 8)%N &
    forall p, p \in ps -> legendre q%:Z p = sgnb (eps p) /\
      legendre p%:Z q = sgnb (eps p) * (-1) ^+ ((p.-1)./2 * (r.-1)./2)].
Proof.
move=> ro ups aps ops.
have [q [qp Nq qnot q8 hl]] := legendre_pattern_exists _ ups aps ops eps r N ro.
exists q; split => // p pps; split; first exact: hl.
have p_pr := allP aps p pps; have p_odd := allP ops p pps.
have q4 : (q = r %[mod 4])%N.
  by rewrite -(@modn_dvdm 8 q 4 isT) q8 (@modn_dvdm 8 r 4 isT).
have q_odd : odd q by rewrite -(@odd_mod q 8 erefl) q8 (@odd_mod r 8 erefl).
have sq : (-1) ^+ (q.-1)./2 = (-1) ^+ (r.-1)./2 :> int.
  by rewrite sign_half_mod4 // q4 -sign_half_mod4.
have pq : p != q by apply: contraNneq qnot => <-.
have := quadratic_reciprocity p_pr qp p_odd q_odd pq.
rewrite hl // mulnC exprM sq -exprM mulnC => <-.
by rewrite mulrCA /sgnb; case: (eps p); rewrite ?mulr1 ?mulrNN ?mulr1.
Qed.

Theorem new_prime_nodir (eps : nat -> bool) (r : nat) (ps : seq nat) :
  odd r -> uniq ps -> all prime ps -> all odd ps ->
  exists q : nat, [/\ prime q, q \notin ps, (q %% 8 = r %% 8)%N &
    forall p, p \in ps -> legendre q%:Z p = sgnb (eps p) /\
      legendre p%:Z q = sgnb (eps p) * (-1) ^+ ((p.-1)./2 * (r.-1)./2)].
Proof.
move=> ro ups aps ops.
have [q [qp _ qnot q8 hl]] := new_prime_nodir_gt eps r 0 ps ro ups aps ops.
by exists q; split.
Qed.

