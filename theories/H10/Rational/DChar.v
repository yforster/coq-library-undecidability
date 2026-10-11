(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Real (quadratic) Dirichlet characters modulo M = 8 * prod ps and the
   orthogonality identity for Legendre-symbol patterns (PLAN.md Phase 4,
   task D3; DIRICHLET_DESIGN.md, Sec. 6). Purely algebraic and
   combinatorial; no analysis, no axioms.

   Setting: ps is a list of distinct odd primes, M := [DMod ps] =
   8 * prod ps. The "basis" of characters is 'I_(size ps).+2: index 0 is
   the symbol -1, index 1 is the symbol 2, index i+2 is the prime
   nth 0 ps i. For b in the basis, [chi_b b : nat -> int] is
     [chi_m1 n] = (-1)^((n-1)/2)    (n odd; 0 for n even),
     [chi_2 n]  = (-1)^((n^2-1)/8)  (n odd; 0 for n even),
     [chi_p p n] = (n/p)            (Legendre symbol of QuadRec.v),
   and for a subset S : {set basis}, [chiS S n] = prod_(b in S) chi_b b n.

   Main results:
   - [chi_b_mul], [chiS_mul]: complete multiplicativity;
   - [chi_b_sgn3], [chi_b_le1], [chiS_sgn3], [chiS_le1]: values in {-1,0,1};
   - [chi_b_mod], [chiS_mod]: M-periodicity;
   - [coprime_chiP]: coprime n M iff all chi_b b n are nonzero;
     [chiS_coprime]: chiS S n <> 0 for n coprime to M;
   - [chiS_sum_period]: S <> set0 -> sum_(n < M) chiS S n = 0;
   - [chiS_sum_window], [chiS_partial_bound], [chiS_window_rat]:
     |sum_(x < n <= y) chiS S n| <= M for S <> set0;
   - [pattern_expand] (orthogonality): for sigma with values +-1 and n
     coprime to M,
       2^(k+2) [forall b, chi_b b n = sigma b]
         = sum_S (prod_(b in S) sigma b) chiS S n;
   - bridge to the assembly: [sigma_of r eps] and [pattern_sigma_ofP]:
     an odd prime q not in ps has the pattern (sigma_of r eps) iff
     q = r mod 8 and (q/p) = sgnb (eps p) for all p in ps;
     [coprime_M_of_prime].
   [sgnb e] is (if e then 1 else -1), convertible to PP1Assembly's
   [sgn_bool]. *)

From mathcomp Require Import boot order algebra.
From Undecidability.H10.Rational Require Import QuadRec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(* 1. The individual characters                                       *)
(* ------------------------------------------------------------------ *)

Definition sgnb (e : bool) : int := if e then 1 else -1.

Definition chi_m1 (n : nat) : int := if odd n then (-1) ^+ (n.-1)./2 else 0.
Definition chi_2 (n : nat) : int := if odd n then (-1) ^+ ((n ^ 2).-1 %/ 8) else 0.
Definition chi_p (p n : nat) : int := legendre n%:Z p.

Lemma sign_pm1 (k : nat) : ((-1) ^+ k = 1 :> int) \/ ((-1) ^+ k = -1 :> int).
Proof. by rewrite -signr_odd; case: odd; [right|left]. Qed.

Lemma sgnb_pm1 (e : bool) : sgnb e = 1 \/ sgnb e = -1.
Proof. by case: e; [left|right]. Qed.

Lemma pm1_sgn3 (u : int) : u = 1 \/ u = -1 -> sgn3 u.
Proof. by case=> ->. Qed.

Lemma sgn3P (u : int) : sgn3 u -> [\/ u = 0, u = 1 | u = -1].
Proof. by case/orP => [/orP[]|]/eqP->; [constructor 1|constructor 2|constructor 3]. Qed.

Lemma sgn3M (u v : int) : sgn3 u -> sgn3 v -> sgn3 (u * v).
Proof.
by move=> /sgn3P[]-> /sgn3P[]->;
  rewrite ?mul0r ?mulr0 ?mul1r ?mulr1 ?mulrNN ?mulr1.
Qed.

Lemma sgn3_le1 (u : int) : sgn3 u -> `|u| <= 1.
Proof. by move=> /sgn3P[]->. Qed.

Lemma sgn3_pm1 (u : int) : sgn3 u -> u != 0 -> u = 1 \/ u = -1.
Proof. by move=> /sgn3P[]->; [rewrite eqxx|left|right]. Qed.

Lemma chi_m1_mul (m n : nat) : chi_m1 (m * n) = chi_m1 m * chi_m1 n.
Proof.
rewrite /chi_m1 oddM; case: (boolP (odd m)) => om; case: (boolP (odd n)) => on;
  rewrite ?mul0r ?mulr0 //.
exact: sign4M.
Qed.

Lemma chi_2_mul (m n : nat) : chi_2 (m * n) = chi_2 m * chi_2 n.
Proof.
rewrite /chi_2 oddM; case: (boolP (odd m)) => om; case: (boolP (odd n)) => on;
  rewrite ?mul0r ?mulr0 //.
exact: sign8M.
Qed.

Lemma chi_p_mul (p m n : nat) : prime p -> odd p ->
  chi_p p (m * n) = chi_p p m * chi_p p n.
Proof. by move=> p_pr p_odd; rewrite /chi_p PoszM legendreM. Qed.

Lemma chi_m1_sgn3 n : sgn3 (chi_m1 n).
Proof. by rewrite /chi_m1; case: odd => //; apply/pm1_sgn3/sign_pm1. Qed.

Lemma chi_2_sgn3 n : sgn3 (chi_2 n).
Proof. by rewrite /chi_2; case: odd => //; apply/pm1_sgn3/sign_pm1. Qed.

Lemma chi_m1_mod4 (m n : nat) : (m = n %[mod 4])%N -> chi_m1 m = chi_m1 n.
Proof.
move=> mn; rewrite /chi_m1.
have omn : odd m = odd n by rewrite -(@odd_mod m 4 erefl) mn (@odd_mod n 4 erefl).
rewrite omn; case: (boolP (odd n)) => // on.
by rewrite (sign_half_mod4 on) sign_half_mod4 ?omn // mn.
Qed.

Lemma chi_2_mod8 (m n : nat) : (m = n %[mod 8])%N -> chi_2 m = chi_2 n.
Proof.
move=> mn; rewrite /chi_2.
have omn : odd m = odd n by rewrite -(@odd_mod m 8 erefl) mn (@odd_mod n 8 erefl).
rewrite omn; case: (boolP (odd n)) => // on.
by rewrite (sign_mod8 on) sign_mod8 ?omn // mn.
Qed.

Lemma mod8_mod4 (m n : nat) : (m = n %[mod 8])%N -> (m = n %[mod 4])%N.
Proof. by move=> mn; rewrite -(@modn_dvdm 8 m 4 isT) mn (@modn_dvdm 8 n 4 isT). Qed.

Lemma if_sign (c : bool) : (if c then 1 else -1 : int) = (-1) ^+ (~~ c).
Proof. by case: c; rewrite /= ?expr0 ?expr1. Qed.

(* The two "sign" characters determine an odd residue mod 8. *)
Lemma mod8_of_signs (a c : nat) : odd a -> odd c ->
  (-1) ^+ (a.-1)./2 = (-1) ^+ (c.-1)./2 :> int ->
  (-1) ^+ ((a ^ 2).-1 %/ 8) = (-1) ^+ ((c ^ 2).-1 %/ 8) :> int ->
  (a %% 8 = c %% 8)%N.
Proof.
move=> oa oc; rewrite !sign_mod8 // !if_sign (sign_half_mod4 oa) (sign_half_mod4 oc).
rewrite -(@modn_dvdm 8 a 4 isT) -(@modn_dvdm 8 c 4 isT).
rewrite -[LHS]signr_odd -[RHS]signr_odd => /signr_inj h1 /signr_inj h2.
have ra : odd (a %% 8)%N by rewrite (@odd_mod a 8 erefl).
have rc : odd (c %% 8)%N by rewrite (@odd_mod c 8 erefl).
have la : (a %% 8 < 8)%N by rewrite ltn_mod.
have lc : (c %% 8 < 8)%N by rewrite ltn_mod.
move: ra rc la lc h1 h2; case: (a %% 8)%N => [|[|[|[|[|[|[|[|]]]]]]]] //;
  by case: (c %% 8)%N => [|[|[|[|[|[|[|[|]]]]]]]].
Qed.

Lemma coprime_prod_seq (n : nat) (qs : seq nat) :
  (forall q, q \in qs -> coprime n q) -> coprime n (\prod_(q <- qs) q).
Proof.
elim: qs => [|q qs IH] h; first by rewrite big_nil coprimen1.
rewrite big_cons coprimeMr h ?mem_head //=; apply: IH => x xq.
by apply: h; rewrite inE xq orbT.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Characters modulo M = 8 * prod ps                               *)
(* ------------------------------------------------------------------ *)

Section Characters.

Variable ps : seq nat.
Hypotheses (ps_uniq : uniq ps) (ps_prime : all prime ps) (ps_odd : all odd ps).

Definition DMod : nat := (8 * \prod_(p <- ps) p)%N.
Local Abbreviation M := DMod.
Local Abbreviation basis := 'I_(size ps).+2.

(* The prime attached to a basis index >= 2. *)
Definition bprime (b : basis) : nat := nth 0%N ps (b - 2).

(* The basis index of a prime of ps. *)
Definition bidx (p : nat) : basis := inord (index p ps).+2.

Definition chi_b (b : basis) : nat -> int :=
  if (val b == 0)%N then chi_m1
  else if (val b == 1)%N then chi_2
  else chi_p (bprime b).

Definition chiS (S : {set basis}) (n : nat) : int := \prod_(b in S) chi_b b n.

Definition pattern (sigma : basis -> int) (n : nat) : bool :=
  [forall b, chi_b b n == sigma b].

Definition sigma_of (r : nat) (eps : nat -> bool) (b : basis) : int :=
  if (val b == 0)%N then (-1) ^+ (r.-1)./2
  else if (val b == 1)%N then (-1) ^+ ((r ^ 2).-1 %/ 8)
  else sgnb (eps (bprime b)).

Definition b_m1 : basis := ord0.
Definition b_2 : basis := @Ordinal (size ps).+2 1 isT.

Lemma M_gt0 : (0 < M)%N.
Proof using ps_prime. by rewrite muln_gt0 prod_primes_gt0. Qed.

Lemma dvd8M : (8 %| M)%N.
Proof. exact: dvdn_mulr. Qed.

Lemma dvdpM p : p \in ps -> (p %| M)%N.
Proof. by move=> pps; apply: dvdn_mull; rewrite (big_rem p pps) /= dvdn_mulr. Qed.

Lemma bprime_in (b : basis) : (val b != 0)%N -> (val b != 1)%N -> bprime b \in ps.
Proof.
move=> b0 b1; rewrite /bprime mem_nth //.
have b2 : (2 <= b)%N by case: b b0 b1 => [[|[|b]]].
by rewrite ltn_subLR // add2n.
Qed.

Lemma bidx_val p : p \in ps -> val (bidx p) = (index p ps).+2.
Proof. by move=> pps; rewrite /bidx /= inordK // !ltnS index_mem. Qed.

Lemma bprime_bidx p : p \in ps -> bprime (bidx p) = p.
Proof. by move=> pps; rewrite /bprime bidx_val // subn2 /= nth_index. Qed.

Lemma bprime_inj (b c : basis) : (1 < b)%N -> (1 < c)%N ->
  (bprime b == bprime c) = (b == c).
Proof using ps_uniq.
move=> b1 c1; rewrite /bprime nth_uniq ?ltn_subLR ?add2n //.
apply/eqP/eqP => [h|-> //]; apply: val_inj.
by rewrite /= -(subnK b1) -(subnK c1) h.
Qed.

Variant chi_b_spec (b : basis) : (nat -> int) -> Type :=
| ChiM1 of val b = 0%N : chi_b_spec b chi_m1
| Chi2 of val b = 1%N : chi_b_spec b chi_2
| ChiP of (1 < b)%N & bprime b \in ps : chi_b_spec b (chi_p (bprime b)).

Lemma chi_bP b : chi_b_spec b (chi_b b).
Proof.
rewrite /chi_b; case: ifP => [/eqP|b0]; first exact: ChiM1.
case: ifP => [/eqP|b1]; first exact: Chi2.
apply: ChiP; last by rewrite bprime_in ?b0 ?b1.
by case: b b0 b1 => [[|[|b]]].
Qed.

Lemma chi_b_mul b m n : chi_b b (m * n) = chi_b b m * chi_b b n.
Proof using ps_odd ps_prime.
case: chi_bP => [_|_|_ pps]; [exact: chi_m1_mul|exact: chi_2_mul|].
by apply: chi_p_mul; [apply: (allP ps_prime)|apply: (allP ps_odd)].
Qed.

Lemma chiS_mul S m n : chiS S (m * n) = chiS S m * chiS S n.
Proof using ps_odd ps_prime.
by rewrite /chiS -big_split; apply: eq_bigr => b _; rewrite chi_b_mul.
Qed.

Lemma chiS_set0 n : chiS set0 n = 1.
Proof. by rewrite /chiS big_set0. Qed.

Lemma chi_b_sgn3 b n : sgn3 (chi_b b n).
Proof.
case: chi_bP => *; [exact: chi_m1_sgn3|exact: chi_2_sgn3|exact: legendre_sgn3].
Qed.

Lemma chiS_sgn3 S n : sgn3 (chiS S n).
Proof.
rewrite /chiS; elim/big_ind: _ => //; [exact: sgn3M|move=> b _; exact: chi_b_sgn3].
Qed.

Lemma chi_b_le1 b n : `|chi_b b n| <= 1.
Proof. exact/sgn3_le1/chi_b_sgn3. Qed.

Lemma chiS_le1 S n : `|chiS S n| <= 1.
Proof. exact/sgn3_le1/chiS_sgn3. Qed.

Lemma chi_b_mod b n : chi_b b (n %% M) = chi_b b n.
Proof using ps_prime.
case: chi_bP => [_|_|_ pps].
- by apply: chi_m1_mod4; rewrite modn_dvdm // (dvdn_trans _ dvd8M).
- by apply: chi_2_mod8; rewrite modn_dvdm // dvd8M.
- apply: (legendre_mod (allP ps_prime _ pps)).
  apply: (@eqz_mod_dvdm _ _ _ M); first exact: dvdpM.
  by rewrite eqz_mod_nat modn_mod.
Qed.

Lemma chiS_mod S n : chiS S (n %% M) = chiS S n.
Proof using ps_prime. by apply: eq_bigr => b _; rewrite chi_b_mod. Qed.

Lemma chi_b_coprime b n : coprime n M -> chi_b b n != 0.
Proof using ps_prime.
rewrite /M coprimeMr => /andP[c8 cP].
case: chi_bP => [_|_|_ pps].
- rewrite /chi_m1; have -> : odd n.
    by move: c8; rewrite (_ : 8 = 2 ^ 3)%N // coprime_pexpr // coprimen2.
  by case: (sign_pm1 (n.-1)./2) => ->.
- rewrite /chi_2; have -> : odd n.
    by move: c8; rewrite (_ : 8 = 2 ^ 3)%N // coprime_pexpr // coprimen2.
  by case: (sign_pm1 ((n ^ 2).-1 %/ 8)) => ->.
- rewrite /chi_p legendre_eq0 ?(allP ps_prime _ pps) // dvdzE /=.
  have pP : (bprime b %| \prod_(p <- ps) p)%N by rewrite (big_rem _ pps) /= dvdn_mulr.
  by rewrite -prime_coprime ?(allP ps_prime _ pps) // coprime_sym (coprime_dvdr pP cP).
Qed.

Lemma chiS_coprime S n : coprime n M -> chiS S n != 0.
Proof using ps_prime.
by move=> co; apply/prodf_neq0 => b _; apply: chi_b_coprime.
Qed.

Lemma chi_b_pm1 b n : coprime n M -> chi_b b n = 1 \/ chi_b b n = -1.
Proof using ps_prime.
by move=> co; apply: sgn3_pm1; [apply: chi_b_sgn3|apply: chi_b_coprime].
Qed.

Lemma coprime_of_chi (n : nat) : (forall b, chi_b b n != 0) -> coprime n M.
Proof using ps_prime.
move=> h; rewrite /M coprimeMr; apply/andP; split.
  rewrite (_ : 8 = 2 ^ 3)%N // coprime_pexpr // coprimen2.
  by have := h b_m1; rewrite /chi_b /=; rewrite /chi_m1; case: odd; rewrite ?eqxx.
apply: coprime_prod_seq => p pps.
have := h (bidx p); rewrite /chi_b bidx_val //= bprime_bidx // /chi_p.
rewrite legendre_eq0 ?(allP ps_prime _ pps) // dvdzE /= => npn.
by rewrite coprime_sym prime_coprime ?(allP ps_prime _ pps).
Qed.

Lemma coprime_chiP (n : nat) : coprime n M = [forall b, chi_b b n != 0].
Proof using ps_prime.
apply/idP/forallP => [co b|h]; [exact: chi_b_coprime|exact: coprime_of_chi].
Qed.

Lemma pattern_coprime sigma n : (forall b, sigma b != 0) ->
  pattern sigma n -> coprime n M.
Proof using ps_prime.
by move=> s0 /forallP h; apply: coprime_of_chi => b; rewrite (eqP (h b)).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Sums over a period and over windows                             *)
(* ------------------------------------------------------------------ *)

Lemma sigma_of_pm1 r eps b : sigma_of r eps b = 1 \/ sigma_of r eps b = -1.
Proof.
rewrite /sigma_of; case: ifP => _; first exact: sign_pm1.
case: ifP => _; [exact: sign_pm1|exact: sgnb_pm1].
Qed.

Lemma chi_b_sigma_of r eps n b : odd r -> odd n -> (n = r %[mod 8])%N ->
  (forall p, p \in ps -> legendre n%:Z p = sgnb (eps p)) ->
  chi_b b n = sigma_of r eps b.
Proof.
move=> ro no nr he; rewrite /chi_b /sigma_of.
case: ifP => b0.
  by rewrite /chi_m1 no sign_half_mod4 // (mod8_mod4 nr) -sign_half_mod4.
case: ifP => b1; first by rewrite /chi_2 no !sign_mod8 // nr.
by apply: he; rewrite bprime_in ?b0 ?b1.
Qed.

(* Signs for which exactly the basis element b0 has value -1. *)
Definition r_of (b0 : basis) : nat :=
  if (val b0 == 0)%N then 7%N else if (val b0 == 1)%N then 5%N else 1%N.
Definition eps_of (b0 : basis) (p : nat) : bool :=
  (1 < val b0)%N ==> (p != bprime b0).

Lemma r_of_odd b0 : odd (r_of b0).
Proof. by rewrite /r_of; case: ifP => _ //; case: ifP. Qed.

Lemma sigma_of_unit (b0 b : basis) :
  sigma_of (r_of b0) (eps_of b0) b = if b == b0 then -1 else 1.
Proof using ps_uniq.
rewrite /sigma_of /r_of /eps_of /sgnb.
have -> : (b == b0) = (val b == val b0) by [].
case: (ltnP 1 b0) => b01; last first.
  by case: b0 b01 => [[|[|i0]] h0] //= _; case: b => [[|[|i]] h].
case: b0 b01 => [[|[|i0]] h0] //= _; case: b => [[|[|i]] h] //=.
by rewrite bprime_inj // -(inj_eq val_inj) /=; case: eqP.
Qed.

Lemma exists_neg_char (b0 : basis) : exists n0 : nat,
  coprime n0 M /\ forall b, chi_b b n0 = if b == b0 then -1 else 1.
Proof using ps_odd ps_prime ps_uniq.
have [a [_ co ar ae]] :=
  legendre_pattern (eps_of b0) (r_of_odd b0) ps_uniq ps_prime ps_odd.
exists a; split => // b; rewrite -sigma_of_unit; apply: chi_b_sigma_of => //.
- exact: r_of_odd.
- by rewrite -(@odd_mod a 8 erefl) ar (@odd_mod _ 8 erefl) r_of_odd.
- by move=> p pps; apply: ae.
Qed.

Lemma chiS_sum_period S : S != set0 -> \sum_(n < M) chiS S n = 0.
Proof using ps_odd ps_prime ps_uniq.
case/set0Pn => b0 b0S.
have [n0 [co n0E]] := exists_neg_char b0.
have cS : chiS S n0 = -1.
  rewrite /chiS (bigD1 b0) //= n0E eqxx big1 ?mulr1 // => b /andP[_ bb0].
  by rewrite n0E (negbTE bb0).
have M0 := M_gt0.
pose h (i : 'I_M) : 'I_M := Ordinal (ltn_pmod (n0 * i) M0).
have h_inj : injective h.
  move=> i j /(congr1 val) /= /eqP hij; apply: val_inj => /=.
  wlog le : i j hij / (j <= i)%N.
    move=> W; case: (leqP j i) => [|/ltnW] l; first exact: W.
    by apply/esym/W => //; rewrite eq_sym.
  have : (M %| n0 * i - n0 * j)%N by rewrite -eqn_mod_dvd ?leq_mul2l ?le ?orbT.
  have cM : coprime M n0 by rewrite coprime_sym.
  rewrite -mulnBr (Gauss_dvdr _ cM).
  move=> d; have lt : (i - j < M)%N := leq_ltn_trans (leq_subr j i) (ltn_ord i).
  have [z|nz] := eqVneq (i - j)%N 0%N.
    by apply/eqP; rewrite eqn_leq -subn_eq0 z le.
  have pos : (0 < i - j)%N by rewrite lt0n.
  by have := dvdn_leq pos d; rewrite leqNgt lt.
have e : \sum_(n < M) chiS S n = - \sum_(n < M) chiS S n.
  rewrite {1}(reindex_inj h_inj) -sumrN; apply: eq_bigr => i _ /=.
  by rewrite chiS_mod chiS_mul cS mulN1r.
have : (\sum_(n < M) chiS S n) *+ 2 = 0 by rewrite mulr2n {1}e addNr.
by move/eqP; rewrite mulrn_eq0 /= => /eqP.
Qed.

Lemma chiS_shift S x : \sum_(x <= n < x + M) chiS S n = \sum_(n < M) chiS S n.
Proof using ps_prime.
have M0 := M_gt0.
elim: x => [|x IH]; first by rewrite add0n big_mkord.
have xM : (x < x + M)%N by rewrite -{1}(addn0 x) ltn_add2l.
rewrite -IH addSn big_nat_recr //= [in RHS]big_ltn //.
by rewrite addrC -(chiS_mod S (x + M)) modnDr chiS_mod.
Qed.

Lemma chiS_window_k S x k : S != set0 ->
  `|\sum_(x <= n < x + k) chiS S n| <= M%:Z.
Proof using ps_odd ps_prime ps_uniq.
move=> S0; elim/ltn_ind: k x => k IH x.
have M0 := M_gt0.
case: (ltnP k M) => [kM|Mk].
  apply: le_trans (ler_norm_sum _ _ _) _.
  apply: (@le_trans _ _ (\sum_(x <= n < x + k) (1 : int))).
    by apply: ler_sum => n _; apply: chiS_le1.
  by rewrite sumr_const_nat addKn -natz ler_nat ltnW.
rewrite (@big_cat_nat _ _ _ (x + M)) ?leq_addr ?leq_add2l //=.
rewrite chiS_shift chiS_sum_period // add0r.
have -> : (x + k = (x + M) + (k - M))%N by rewrite -addnA subnKC.
apply: IH; rewrite ltn_subrL M0 /=.
exact: leq_trans Mk.
Qed.

(* |sum_(x < n <= y) chiS S n| <= M. *)
Lemma chiS_sum_window S x y : S != set0 ->
  `|\sum_(x.+1 <= n < y.+1) chiS S n| <= M%:Z.
Proof using ps_odd ps_prime ps_uniq.
move=> S0; case: (leqP x y) => [le|lt].
  by rewrite -(subnKC le) -addSn; apply: chiS_window_k.
by rewrite big_geq ?normr0 // ltnS ltnW.
Qed.

Lemma chiS_partial_bound S x : S != set0 ->
  `|\sum_(1 <= n < x.+1) chiS S n| <= M%:Z.
Proof using ps_odd ps_prime ps_uniq. exact: chiS_sum_window. Qed.

Lemma chiS_window_rat S x y : S != set0 ->
  `|\sum_(x.+1 <= n < y.+1) (chiS S n)%:~R| <= M%:R :> rat.
Proof using ps_odd ps_prime ps_uniq.
move=> S0; have := chiS_sum_window x y S0.
by rewrite -(ler_int rat) intr_norm rmorph_sum -pmulrn.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Orthogonality: expansion of the pattern indicator               *)
(* ------------------------------------------------------------------ *)

Lemma pattern_factor sigma n b : sigma b = 1 \/ sigma b = -1 -> coprime n M ->
  sigma b * chi_b b n + 1 = if chi_b b n == sigma b then 2 else 0.
Proof using ps_prime.
move=> hs co; case: (chi_b_pm1 b co) => ->; case: hs => ->;
  by rewrite ?mulr1 ?mulrNN ?mulN1r ?mulrN1 ?addNr ?eqxx.
Qed.

Lemma prod_const_basis (x : int) : \prod_(b : basis) x = x ^+ (size ps).+2.
Proof. by rewrite -(big_mkord xpredT (fun _ => x)) prodr_const_nat subn0. Qed.

Lemma pattern_prod_int sigma n : (forall b, sigma b = 1 \/ sigma b = -1) ->
  coprime n M ->
  \prod_(b : basis) (sigma b * chi_b b n + 1) =
    (2 ^ (size ps).+2)%:R * (pattern sigma n)%:R.
Proof using ps_prime.
move=> hs co.
under eq_bigr => b _ do rewrite (pattern_factor (hs b) co).
rewrite /pattern; case: (boolP [forall b, _]) => [/forallP h|/forallPn [b nb]].
  under eq_bigr => b _ do rewrite h.
  by rewrite prod_const_basis natrX mulr1.
by rewrite (bigD1 b) //= ifN // mul0r mulr0.
Qed.

Lemma pattern_expand_int sigma n : (forall b, sigma b = 1 \/ sigma b = -1) ->
  coprime n M ->
  (2 ^ (size ps).+2)%:R * (pattern sigma n)%:R =
    \sum_(S : {set basis}) (\prod_(b in S) sigma b) * chiS S n :> int.
Proof using ps_prime.
move=> hs co; rewrite -pattern_prod_int // bigA_distr.
apply: eq_bigr => S _.
by rewrite -big_mkcond /= big_split.
Qed.

Lemma pattern_expand sigma n : (forall b, sigma b = 1 \/ sigma b = -1) ->
  coprime n M ->
  (2 ^ (size ps).+2)%:R * (pattern sigma n)%:R =
    \sum_(S : {set basis}) (\prod_(b in S) sigma b)%:~R * (chiS S n)%:~R :> rat.
Proof using ps_prime.
move=> hs co; have := congr1 (fun z : int => z%:~R : rat) (pattern_expand_int hs co).
rewrite /= rmorphM /= !rmorph_nat rmorph_sum /= => ->.
by apply: eq_bigr => S _; rewrite rmorphM.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. Bridge to the assembly                                          *)
(* ------------------------------------------------------------------ *)

Lemma pattern_sigma_of_gen r eps n : odd r -> odd n ->
  pattern (sigma_of r eps) n <->
  (n %% 8 = r %% 8)%N /\ (forall p, p \in ps -> legendre n%:Z p = sgnb (eps p)).
Proof.
move=> ro no; split => [/forallP h|[nr he]].
  split.
    have := eqP (h b_m1); have := eqP (h b_2).
    rewrite /chi_b /sigma_of /= /chi_m1 /chi_2 no => e2 e1.
    exact: mod8_of_signs no ro e1 e2.
  move=> p pps; have := eqP (h (bidx p)).
  by rewrite /chi_b /sigma_of bidx_val //= bprime_bidx.
by apply/forallP => b; apply/eqP; apply: chi_b_sigma_of.
Qed.

Lemma pattern_sigma_ofP r eps q : odd r -> odd q -> prime q -> q \notin ps ->
  pattern (sigma_of r eps) q <->
  (q %% 8 = r %% 8)%N /\ (forall p, p \in ps -> legendre q%:Z p = sgnb (eps p)).
Proof. by move=> ro qo _ _; apply: pattern_sigma_of_gen. Qed.

Lemma coprime_M_of_prime q : prime q -> q \notin ps -> q != 2%N -> coprime q M.
Proof using ps_prime.
move=> qp qn q2; case: (even_prime qp) => [qe|qo]; first by rewrite qe in q2.
exact: prime_coprime_prod.
Qed.

End Characters.
