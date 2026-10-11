(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Glue between PP1Assembly.v and SelDescent.v (PLAN.md, Phase 3, task Q5b):
   the hypothesis [PP1Assembly.global_point_El] (Lemmas par:descent and
   par:global-point) follows from the elementary 2-converse
   [TwoConverseSel2_El] by Lemma par:descent ([SelDescent.descent_main]).

   MAIN RESULTS (PROVED; Print Assumptions: [Classical_Prop.classic] only,
   from Dirichlet's theorem for quadratic characters in PrimePatterns.v):
   - [global_point_El_of_TwoConverse : TwoConverseSel2_El -> global_point_El];
   - [PP1_paper_of_TwoConverse : TwoConverseSel2_El -> PP1_paper];
   - [PP1_L0_of_TwoConverse : TwoConverseSel2_El -> PP1_L0].

   BRIDGE. For beta = prod B, the hypotheses of [descent_main] are obtained
   from those of [global_point_El]:
   - 0 < beta, beta | l (B is a set of primes of the squarefree l),
     beta <> l (a prime of Q = primes |l| outside B), the congruences;
   - the two matrix formalizations agree: PP1Assembly.v works with functions
     u : nat -> F_2 on the list Q and the bit [nsq_bit a q] = [legendre a q
     == -1], SelDescent.v with column vectors indexed by 'I_|Q| (q_i =
     [qi i]) and the bit [nbit a q] = [legendre a q != 1]. The two bits agree
     when the symbol is +-1, which is the case for all entries used: [q_j/q_i]
     with i <> j (distinct primes) and [3/q_i] (q_i <> 3 since l = 2 mod 3).
     Then (K v)_i = [Kmat Q u q_i] for v_i = u q_i ([Kmx_col]); a vector v
     is transported back by u p = sum_(i | q_i = p) v_i ([uf]). *)

From mathcomp Require Import boot order algebra finite_group.
From Undecidability.H10.Rational
  Require Import RatUtil PaperInputs PhiCovering QuadRec TwoConverse SelDescent.
From Undecidability.H10.Rational Require PP1Assembly.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** * The two Legendre bits *)

Lemma nsq_nbit (a : int) (p : nat) : pm1 (legendre a p) ->
  PP1Assembly.nsq_bit a p = nbit a p.
Proof. by rewrite /PP1Assembly.nsq_bit /PP1Assembly.bitF2 /nbit /bitv; case/orP => /eqP ->. Qed.

Lemma F2_cases2 (x : 'F_2) : x = 0 \/ x = 1.
Proof. exact: PP1Assembly.F2_cases. Qed.

(** * Indices of Q = primes |l| *)

Lemma qs_ex (l : int) (p : nat) : p \in qs l -> exists i : 'I_(nq l), qi i = p.
Proof.
  move=> Hp; have Hi : (index p (qs l) < nq l)%N by rewrite /nq index_mem.
  by exists (Ordinal Hi); rewrite /qi /= nth_index.
Qed.

(* vectors from functions and back *)
Definition colu (l : int) (u : nat -> 'F_2) : 'cV['F_2]_(nq l) := \col_i u (qi i).

Definition uf (l : int) (v : 'cV['F_2]_(nq l)) (p : nat) : 'F_2 :=
  \sum_(i < nq l | qi i == p) v i 0.

Lemma uf_qi (l : int) (v : 'cV['F_2]_(nq l)) (i : 'I_(nq l)) : uf v (qi i) = v i 0.
Proof.
  rewrite /uf (big_pred1 i) // => j /=.
  by apply/eqP/eqP => [ /qi_inj | -> ].
Qed.

Lemma colu_uf (l : int) (v : 'cV['F_2]_(nq l)) : colu l (uf v) = v.
Proof. by apply/matrixP => i j; rewrite !mxE uf_qi ord1. Qed.

(** * The matrices agree *)

Lemma Kmx_col (l : int) (u : nat -> 'F_2) (i : 'I_(nq l)) : admissible_l l ->
  (Kmx l *m colu l u) i 0 = PP1Assembly.Kmat (qs l) u (qi i).
Proof.
  move=> Hl.
  have Hnb : forall j : 'I_(nq l), j != i ->
      PP1Assembly.nsq_bit (qi j)%:Z (qi i) = nbit (qi j) (qi i).
  { move=> j Hji; apply: nsq_nbit; apply: (legendre_pm1 (qi_prime i)).
    by apply: qi_ndvd; rewrite eq_sym. }
  rewrite /PP1Assembly.Kmat (big_nth 0%N) big_mkord.
  rewrite -/(nq l).
  have -> : \sum_(j < nq l | nth 0%N (qs l) j != qi i)
              PP1Assembly.nsq_bit (nth 0%N (qs l) j)%:Z (qi i) * (u (nth 0%N (qs l) j) + u (qi i))
          = \sum_(j < nq l | j != i) nbit (qi j) (qi i) * (u (qi j) + u (qi i)).
  { apply: eq_big => [ j | j Hj ].
    - by rewrite -/(qi j) (inj_eq (@qi_inj l)).
    - by rewrite -/(qi j) Hnb // -(inj_eq (@qi_inj l)). }
  rewrite mxE (bigD1 i) //= !mxE eqxx.
  rewrite [X in _ + X](eq_bigr (fun j => nbit (qi j) (qi i) * u (qi j))).
  { by move=> j Hj; rewrite !mxE eq_sym (negbTE Hj). }
  rewrite mulr_suml addrC.
  under [RHS]eq_bigr do rewrite mulrDr.
  by rewrite big_split.
Qed.

(** * Products of the primes of B *)

Lemma prod_qs (l : int) : admissible_l l -> (\prod_(p <- qs l) p)%N = absz l.
Proof. by move=> Hl; rewrite (big_nth 0%N) big_mkord; exact: (prod_qi Hl). Qed.

Lemma prodB_dvd (l : int) (B : seq nat) : admissible_l l -> uniq B ->
  {subset B <= primes (absz l)} -> (\prod_(p <- B) p %| absz l)%N.
Proof.
  move=> Hl HB Hsub.
  have -> : (\prod_(p <- B) p = \prod_(p <- [seq p <- qs l | p \in B]) p)%N.
  { apply: perm_big; apply: uniq_perm => //; first by apply: filter_uniq; exact: primes_uniq.
    by move=> p; rewrite mem_filter; case: (boolP (p \in B)) => //= /Hsub. }
  rewrite -(prod_qs Hl) big_filter [X in (_ %| X)%N](bigID (fun p => p \in B)) /=.
  exact: dvdn_mulr.
Qed.

(** * Lemma par:global-point from the 2-converse *)

Lemma global_point_El_of_TwoConverse : TwoConverseSel2_El -> PP1Assembly.global_point_El.
Proof.
  move=> H2c l B Hl HBu HBp Hb8 Hb3 Hsub [ p0 [ Hp0 Hp0B ] ] Hker Hlam.
  set b := (\prod_(p <- B) p)%N.
  set beta : int := b%:Z.
  have HoneB : oneB l beta = colu l (fun p => PP1Assembly.bitF2 (p \in B)).
  { apply/matrixP => i j; rewrite !mxE /PP1Assembly.bitF2; congr (_%:R).
    by rewrite dvdzE /= PP1Assembly.dvd_prod_primes // (qi_prime i). }
  have Hb0 : 0 < beta by rewrite ltz_nat PP1Assembly.prod_gt0.
  have Hbl : (beta %| l)%Z by rewrite dvdzE /=; exact: prodB_dvd.
  have Hbl' : beta != l.
  { apply/eqP => E; have Ebl : b = absz l by rewrite -E.
    move: Hp0; rewrite mem_primes => /and3P [ Hp0p _ Hp0l ].
    by move: Hp0B; rewrite -PP1Assembly.dvd_prod_primes // -/b Ebl Hp0l. }
  have Hb8' : (beta %% 8)%Z = 1 by rewrite modz_nat Hb8.
  have Hb3' : (beta %% 3)%Z = 2 by rewrite modz_nat Hb3.
  have HK0 : Kmx l *m oneB l beta = 0.
  { apply/matrixP => i j; rewrite ord1 HoneB Kmx_col // mxE.
    apply: (proj2 (Hker _)); last exact: qi_mem.
    by exists 0, 1 => p _; rewrite add0r mul1r. }
  have Hker' : forall v : 'cV['F_2]_(nq l), Kmx l *m v = 0 ->
      v = 0 \/ v = const_mx 1 \/ v = oneB l beta \/ v = const_mx 1 + oneB l beta.
  { move=> v Hv.
    have [ c [ c' Hc ] ] : exists c c' : 'F_2, forall p, p \in primes `|l| ->
        uf v p = c + c' * PP1Assembly.bitF2 (p \in B).
    { apply/(Hker (uf v)) => p /qs_ex [ i <- ].
      by rewrite -Kmx_col // colu_uf Hv mxE. }
    have Ev : v = c *: const_mx 1 + c' *: oneB l beta.
    { apply/matrixP => i j; rewrite ord1 HoneB !mxE -uf_qi Hc ?qi_mem //.
      by rewrite mulr1. }
    rewrite Ev; case: (F2_cases2 c) => ->; case: (F2_cases2 c') => ->;
      rewrite ?scale0r ?scale1r ?add0r ?addr0;
      [ left | right; right; left | right; left | right; right; right ]; by []. }
  have Hlam' : forall v : 'cV['F_2]_(nq l), Kmx l *m v != lamv l.
  { move=> v; apply/eqP => Hv; apply: Hlam; exists (uf v) => p /qs_ex [ i <- ].
    rewrite -Kmx_col // colu_uf Hv mxE nsq_nbit //.
    apply: (legendre_pm1 (qi_prime i)); apply: (prime_ndvd (qi_prime i)) => //.
    exact: (qi_ne3 Hl). }
  have [ H1 [ H2 H3 ] ] := descent_main Hl Hb0 Hbl Hbl' Hb8' Hb3' HK0 Hker' Hlam'.
  exact: (H2c l Hl beta 1 H1 H2 H3).
Qed.

Theorem PP1_paper_of_TwoConverse : TwoConverseSel2_El -> PP1_paper.
Proof.
  move=> H2c; exact: PP1Assembly.PP1_paper_of_global_point (global_point_El_of_TwoConverse H2c).
Qed.

Theorem PP1_L0_of_TwoConverse : TwoConverseSel2_El -> PP1_L0.
Proof.
  move=> H2c; exact: PP1Assembly.PP1_L0_of_global_point (global_point_El_of_TwoConverse H2c).
Qed.
