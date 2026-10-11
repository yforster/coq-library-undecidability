(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Truncated power series as polynomials (PLAN.md, Phase 2D, task P12b;
   F2_DESIGN.md, steps F1, F2, F2' and F3).

   Everything here is generic: [F] is any field in which the positive
   integers are nonzero (characteristic 0).
   - F1 [tc n f g]: f = g modulo X^n on [{poly F}], a ring congruence,
     compatible with composition (inner constant term 0), derivative and
     integration; approximate inverses [ginv]; uniqueness of inverses and
     of square roots with constant term 1.
   - F2 the bridge to FixedData's list-based recipe [ct_gen]: with
     [gP N = Poly (g_ser A N)], [SP N = 1 - 2 A X^4 gP N],
     [wP N = Poly (omega_ser A N)] and [LK K = \poly_(t < K.+1) ct_gen A t]:
       [g_fix]   gP N = 1 + A X^4 (gP N)^2           mod X^(N+1),
       [S_sq]    (SP N)^2 = 1 - 4 A X^4              mod X^(N+1),
       [omega_S] wP N * SP N = 1                     mod X^(N+1),
       [g_indep], [omega_indep]: independence of the truncation level,
       [LK_deriv] (LK K)' = wP K mod X^K, [LK_0], [LK_1].
   - F2' integrality: for a subring [O] (a predicate closed under 0, 1,
     +, -, * ) containing A, the polynomials gP, SP and the coefficients
     of wP lie in O ([pint]); evaluation lemmas [eval_tc0] (a polynomial
     divisible by X^n evaluates to x^n times an integral value) and
     [lipschitz] (f(a) - f(b) = (a - b) c with c integral).
   - F3 the formal addition theorem of the lemniscatic logarithm
     [log_add_formal]: if S(0) = 1, S^2 = 1 - 4 A X^4 mod X^(K+1),
     w S = 1 mod X^K, L' = w mod X^K and L(0) = 0, then for all u1, u2 in
     F, with S_i = S(u_i X), Q = 1 + 4 A u1^2 u2^2 X^4, I = Q^-1 mod
     X^(K+1) and g = X (u1 S_2 + u2 S_1) I,
       L(g) = L(u1 X) + L(u2 X)   mod X^(K+1).
     The proof is "derivative zero, constant term zero" (Euler's addition
     theorem made univariate by the common scale X); the two polynomial
     certificates are those of F2_DESIGN.md, Appendix B. *)

From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From Undecidability.H10.Rational Require Import FixedData.
Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.
Local Open Scope ring_scope.

(** * F1. The truncation congruence *)

Section trunc.

  Variable F : fieldType.
  Implicit Types f g h d : {poly F}.

  (* a Variant, so that implicit arguments are not computed through it *)
  Variant tc (n : nat) f g : Prop := TcI of (forall i, (i < n)%N -> f`_i = g`_i).

  Lemma tcE n f g : tc n f g -> forall i, (i < n)%N -> f`_i = g`_i.
  Proof. by case. Qed.

  Lemma tc_refl n f : tc n f f. Proof. by constructor. Qed.
  Lemma tc_sym n f g : tc n f g -> tc n g f.
  Proof. by move=> [H]; constructor=> i Hi; rewrite H. Qed.
  Lemma tc_trans n f g h : tc n f g -> tc n g h -> tc n f h.
  Proof. by move=> [H1] [H2]; constructor=> i Hi; rewrite H1 // H2. Qed.
  Lemma tc_le m n f g : (m <= n)%N -> tc n f g -> tc m f g.
  Proof. by move=> Hm [H]; constructor=> i Hi; apply: H; exact: leq_trans Hi Hm. Qed.
  Lemma tc0n f g : tc 0 f g. Proof. by constructor. Qed.

  Lemma tc_add n f f' g g' : tc n f g -> tc n f' g' -> tc n (f + f') (g + g').
  Proof. by move=> [H1] [H2]; constructor=> i Hi; rewrite !coefD H1 // H2. Qed.
  Lemma tc_opp n f g : tc n f g -> tc n (- f) (- g).
  Proof. by move=> [H]; constructor=> i Hi; rewrite !coefN H. Qed.
  Lemma tc_sub n f f' g g' : tc n f g -> tc n f' g' -> tc n (f - f') (g - g').
  Proof. by move=> H1 H2; apply: tc_add H1 (tc_opp H2). Qed.

  Lemma tc_subE n f g : tc n f g <-> tc n (f - g) 0.
  Proof.
    split=> -[H]; constructor=> i Hi.
    - by rewrite coefB coef0 H // subrr.
    - by apply/eqP; rewrite -subr_eq0 -coefB H // coef0.
  Qed.

  Lemma tc_sub0 n f g : tc n f g -> tc n (f - g) 0.
  Proof. exact: (proj1 (@tc_subE n f g)). Qed.
  Lemma tc_of_sub0 n f g : tc n (f - g) 0 -> tc n f g.
  Proof. exact: (proj2 (@tc_subE n f g)). Qed.

  Lemma tc0_add n f g : tc n f 0 -> tc n g 0 -> tc n (f + g) 0.
  Proof. by move=> H1 H2; have := tc_add H1 H2; rewrite addr0. Qed.
  Lemma tc0_sub n f g : tc n f 0 -> tc n g 0 -> tc n (f - g) 0.
  Proof. by move=> H1 H2; have := tc_sub H1 H2; rewrite subr0. Qed.

  Lemma tc_mul n f f' g g' : tc n f g -> tc n f' g' -> tc n (f * f') (g * g').
  Proof.
    move=> [H1] [H2]; constructor=> i Hi; rewrite !coefM; apply: eq_bigr => j _.
    have Hj : (j < n)%N by apply: leq_ltn_trans Hi; rewrite -ltnS.
    have Hij : (i - j < n)%N by apply: leq_ltn_trans Hi; exact: leq_subr.
    by rewrite H1 // H2.
  Qed.

  Lemma tc_mull n f g g' : tc n g g' -> tc n (f * g) (f * g').
  Proof. exact: tc_mul. Qed.
  Lemma tc_mulr n f g g' : tc n g g' -> tc n (g * f) (g' * f).
  Proof. by move=> H; apply: tc_mul. Qed.

  Lemma tc_exp n f g k : tc n f g -> tc n (f ^+ k) (g ^+ k).
  Proof.
    move=> H; elim: k => [ | k IH ]; first by rewrite !expr0.
    by rewrite !exprS; apply: tc_mul.
  Qed.

  Lemma tc_sum n (I : Type) (r : seq I) (P : pred I) (G H : I -> {poly F}) :
    (forall i, P i -> tc n (G i) (H i)) ->
    tc n (\sum_(i <- r | P i) G i) (\sum_(i <- r | P i) H i).
  Proof.
    move=> HG; elim: r => [ | a r IH ]; first by rewrite !big_nil.
    rewrite !big_cons; case: (P a) / boolP => Ha //.
    by apply: tc_add => //; apply: HG.
  Qed.

  Lemma tc_scale n c f g : tc n f g -> tc n (c *: f) (c *: g).
  Proof. by move=> [H]; constructor=> i Hi; rewrite !coefZ H. Qed.

  (* divisibility by X^n *)
  Definition rsh (n : nat) d : {poly F} := \poly_(i < size d) d`_(i + n).

  Lemma tc0P n d : tc n d 0 -> d = rsh n d * 'X^n.
  Proof.
    move=> [H]; apply/polyP => i; rewrite coefMXn.
    case: ltnP => Hi; first by rewrite H // coef0.
    rewrite coef_poly subnK //; case: ltnP => // Hs.
    by rewrite nth_default //; apply: leq_trans Hs (leq_subr _ _).
  Qed.

  Lemma tc_Xn0 n f : tc n (f * 'X^n) 0.
  Proof. by constructor=> i Hi; rewrite coefMXn Hi coef0. Qed.

  Lemma tc_Xn0' n m f : (n <= m)%N -> tc n (f * 'X^m) 0.
  Proof. by move=> Hm; exact: (tc_le Hm (tc_Xn0 m f)). Qed.

  Lemma tc0_mulr n d f : tc n d 0 -> tc n (d * f) 0.
  Proof. by move=> H; have := tc_mulr f H; rewrite mul0r. Qed.

  Lemma tc0_mull n d f : tc n d 0 -> tc n (f * d) 0.
  Proof. by move=> H; have := tc_mull f H; rewrite mulr0. Qed.

  Lemma tc0_mulXn n k d : tc n d 0 -> tc (n + k) (d * 'X^k) 0.
  Proof.
    move=> [H]; constructor=> i Hi; rewrite coefMXn coef0; case: ltnP => // Hk.
    by rewrite H ?coef0 // ltn_subLR // addnC.
  Qed.

  Lemma tc_mulXn n k f g : tc n f g -> tc (n + k) (f * 'X^k) (g * 'X^k).
  Proof.
    move=> /tc_subE H; apply/tc_subE; rewrite -mulrBl; exact: tc0_mulXn.
  Qed.

  Lemma tc_mulX n f g : tc n f g -> tc n.+1 ('X * f) ('X * g).
  Proof.
    move=> H; have := tc_mulXn 1 H; rewrite addn1 expr1 => H'.
    by rewrite ![ 'X * _ ]mulrC.
  Qed.

  (* constant terms by evaluation at 0 *)
  Lemma coef0E f : f`_0 = f.[0].
  Proof. by rewrite horner_coef0. Qed.

  Lemma coef0_comp f h : (f \Po h)`_0 = f.[h`_0].
  Proof. by rewrite !coef0E horner_comp. Qed.

  Lemma tc1_split f : f`_0 = 0 -> f = rsh 1 f * 'X.
  Proof.
    move=> H; rewrite -[ 'X ]expr1; apply: tc0P; constructor=> i.
    by rewrite ltnS leqn0 => /eqP ->; rewrite H coef0.
  Qed.

  (* composition *)
  Lemma tc_comp_l n f g h : h`_0 = 0 -> tc n f g -> tc n (f \Po h) (g \Po h).
  Proof.
    move=> Hh /tc_subE H; apply/tc_subE; rewrite -comp_polyB (tc0P H).
    rewrite comp_polyM (tc1_split Hh) rmorphXn /= comp_polyX exprMn mulrA.
    exact: tc_Xn0.
  Qed.

  Lemma tc_comp_r n f h h' : tc n h h' -> tc n (f \Po h) (f \Po h').
  Proof.
    move=> H; rewrite !comp_polyE; apply: tc_sum => i _.
    by apply/tc_scale/tc_exp.
  Qed.

  Lemma tc_comp n f f' h h' : h`_0 = 0 -> tc n f f' -> tc n h h' ->
    tc n (f \Po h) (f' \Po h').
  Proof.
    move=> Hh H1 H2; apply: tc_trans (tc_comp_l Hh H1) _; exact: tc_comp_r.
  Qed.

  (* derivative *)
  Lemma tc_deriv n f g : tc n.+1 f g -> tc n f^`() g^`().
  Proof. by move=> [H]; constructor=> i Hi; rewrite !coef_deriv H. Qed.

  Hypothesis natf_neq0 : forall n : nat, (0 < n)%N -> n%:R != 0 :> F.

  Lemma tc_integ n f g : f`_0 = g`_0 -> tc n f^`() g^`() -> tc n.+1 f g.
  Proof.
    move=> H0 [H]; constructor=> -[ | i ] Hi //.
    have := H i Hi; rewrite !coef_deriv => E.
    apply: (mulIf (natf_neq0 (ltn0Sn i))); rewrite !mulr_natr; exact: E.
  Qed.

  (* approximate inverses *)
  Definition ginv (n : nat) f : {poly F} := \sum_(j < n) (1 - f) ^+ j.

  Lemma ginv_tele n f : ginv n f * f = 1 - (1 - f) ^+ n.
  Proof.
    rewrite /ginv; elim: n => [ | n IH ]; first by rewrite big_ord0 mul0r expr0 subrr.
    rewrite big_ord_recr /= mulrDl IH exprSr.
    move: ((1 - f) ^+ n) => u; ring.
  Qed.

  Lemma ginvP n f : f`_0 = 1 -> tc n (ginv n f * f) 1.
  Proof.
    move=> H; rewrite ginv_tele; apply/tc_subE.
    have -> : 1 - (1 - f) ^+ n - 1 = - ((1 - f) ^+ n) by rewrite addrC addKr.
    have H0 : (1 - f)`_0 = 0 by rewrite coefB coef1 H subrr.
    rewrite (tc1_split H0) exprMn -oppr0; apply: tc_opp; exact: tc_Xn0.
  Qed.

  Lemma tc_inv_uniq n f (a b : {poly F}) : tc n (a * f) 1 -> tc n (b * f) 1 -> tc n a b.
  Proof.
    move=> Ha Hb.
    have E1 : tc n a (a * (b * f)) by rewrite -[X in tc n X]mulr1; apply/tc_mull/tc_sym.
    have E2 : tc n (b * (a * f)) b by rewrite -[X in tc n _ X]mulr1; apply/tc_mull.
    apply: tc_trans E1 _; rewrite mulrCA; exact: E2.
  Qed.

  Lemma tc_sqrt_uniq n (a b : {poly F}) : a`_0 = 1 -> b`_0 = 1 -> tc n (a ^+ 2) (b ^+ 2) -> tc n a b.
  Proof.
    move=> Ha Hb H.
    have H2 : (2%:R : F) != 0 := natf_neq0 (isT : (0 < 2)%N).
    set e := (2%:R^-1)%:P * (a + b).
    have He0 : e`_0 = 1 by rewrite coefCM coefD Ha Hb -[1 + 1]/(2%:R) mulVf.
    have Hi := @ginvP n e He0.
    have Hab : tc n ((a - b) * (a + b)) 0.
    { have -> : (a - b) * (a + b) = a ^+ 2 - b ^+ 2 by ring.
      exact: tc_sub0. }
    apply: tc_of_sub0.
    have E1 : tc n (a - b) ((a - b) * (ginv n e * e)).
    { rewrite -[X in tc n X]mulr1; apply/tc_mull/tc_sym; exact: Hi. }
    apply: tc_trans E1 _.
    have -> : (a - b) * (ginv n e * e) = ((a - b) * (a + b)) * (ginv n e * (2%:R^-1)%:P).
    { rewrite /e; ring. }
    exact: tc0_mulr.
  Qed.

End trunc.

(** * F2. The recipe [ct_gen] of FixedData.v as polynomials *)

Section recipe.

  Variable F : fieldType.
  Hypothesis natf_neq0 : forall n : nat, (0 < n)%N -> n%:R != 0 :> F.
  Variable A : F.

  Lemma lsum_big (f : nat -> F) lo n : lsum f lo n = \sum_(lo <= i < lo + n) f i.
  Proof.
    rewrite /lsum /index_iota addKn.
    elim: (iota lo n) => [ | i s IH ] /=; first by rewrite big_nil.
    by rewrite big_cons IH.
  Qed.

  Lemma lsum_shift (f : nat -> F) n : lsum f 1 n = lsum (fun i => f i.+1) 0 n.
  Proof.
    rewrite /lsum; have -> : iota 1 n = map succn (iota 0 n) by rewrite -(iotaDl 1 0).
    by rewrite foldr_map.
  Qed.

  Lemma nth_mkseq0 (f : nat -> F) m i :
    nth 0 (mkseq f m) i = if (i < m)%N then f i else 0.
  Proof.
    case: ltnP => H; first by rewrite nth_mkseq.
    by rewrite nth_default ?size_mkseq.
  Qed.

  Lemma lsum_coefM (a b : seq F) n :
    lsum (fun i => nth 0 a i * nth 0 b (n - i)) 0 n.+1 = (Poly a * Poly b)`_n.
  Proof.
    rewrite lsum_big add0n big_mkord coefM; apply: eq_bigr => i _.
    by rewrite !coef_Poly.
  Qed.

  Lemma sr_mul_coef N (a b : seq F) i :
    (Poly (sr_mul N a b))`_i = if (i < N.+1)%N then (Poly a * Poly b)`_i else 0.
  Proof. by rewrite coef_Poly /sr_mul nth_mkseq0 lsum_coefM. Qed.

  (* the contraction  G |-> 1 + A X^4 G^2 *)
  Definition Phi (G : {poly F}) : {poly F} := 1 + A%:P * 'X^4 * G ^+ 2.

  Lemma g_step_coef N (g : seq F) i :
    (Poly (g_step A N g))`_i = if (i < N.+1)%N then (Phi (Poly g))`_i else 0.
  Proof.
    rewrite coef_Poly /g_step nth_mkseq0; case: ifP => // Hi.
    rewrite /Phi coefD coef1 -mulrA coefCM coefXnM.
    case: (ltnP i 4) => H4.
    - by rewrite mulr0.
    - by rewrite -(coef_Poly (sr_mul N g g)) sr_mul_coef expr2 ifT // (leq_ltn_trans (leq_subr 4 i) Hi).
  Qed.

  Lemma Phi_contract m (G G' : {poly F}) : tc m G G' -> tc (m + 4) (Phi G) (Phi G').
  Proof.
    move=> H; apply: tc_of_sub0.
    have -> : Phi G - Phi G' = A%:P * (G - G') * (G + G') * 'X^4 by rewrite /Phi; ring.
    apply: tc0_mulXn; apply: tc0_mulr; apply: tc0_mull; exact: tc_sub0.
  Qed.

  Definition Gj N j : {poly F} := Poly (iter j (g_step A N) (@sr_one F N)).

  Lemma Gj_step N j : tc N.+1 (Gj N j.+1) (Phi (Gj N j)).
  Proof. by constructor=> i Hi; rewrite /Gj iterS g_step_coef Hi. Qed.

  Lemma Gj_chain N j : (j <= N.+1)%N -> tc j (Gj N j) (Gj N j.+1).
  Proof.
    elim: j => [ | j IH ] Hj; first exact: tc0n.
    have H1 := Phi_contract (IH (ltnW Hj)).
    apply: tc_trans (tc_le Hj (Gj_step N j)) _.
    apply: tc_trans (tc_le _ H1) _; first by rewrite -addn1 leq_add2l.
    exact: tc_sym (tc_le Hj (Gj_step N j.+1)).
  Qed.

  Definition gP N : {poly F} := Poly (g_ser A N).

  Lemma g_fix N : tc N.+1 (gP N) (Phi (gP N)).
  Proof. exact: tc_trans (Gj_chain (leqnn N.+1)) (Gj_step N N.+1). Qed.

  Lemma fix_uniq n (G G' : {poly F}) : tc n G (Phi G) -> tc n G' (Phi G') -> tc n G G'.
  Proof.
    move=> H H'; suff : forall m, (m <= n)%N -> tc m G G' by apply.
    elim=> [ | m IH ] Hm; first exact: tc0n.
    have H1 := Phi_contract (IH (ltnW Hm)).
    apply: tc_trans (tc_le Hm H) _; apply: tc_trans (tc_le _ H1) (tc_sym (tc_le Hm H')).
    by rewrite -addn1 leq_add2l.
  Qed.

  Lemma g_indep N M : (N <= M)%N -> tc N.+1 (gP N) (gP M).
  Proof. by move=> H; apply: fix_uniq (g_fix N) (tc_le _ (g_fix M)). Qed.

  Lemma gP0 N : (gP N)`_0 = 1.
  Proof.
    rewrite (tcE (g_fix N) (ltn0Sn N)) /Phi coefD coef1 -mulrA coefCM coefXnM /=.
    by rewrite mulr0 addr0.
  Qed.

  Definition SP N : {poly F} := 1 - (2%:R * A)%:P * 'X^4 * gP N.

  Lemma SP0 N : (SP N)`_0 = 1.
  Proof. by rewrite /SP coefB coef1 -mulrA coefCM coefXnM /= mulr0 subr0. Qed.

  Lemma S_sq N : tc N.+1 (SP N ^+ 2) (1 - (4%:R * A)%:P * 'X^4).
  Proof.
    apply: tc_of_sub0.
    have -> : SP N ^+ 2 - (1 - (4%:R * A)%:P * 'X^4)
            = ((4%:R * A)%:P * 'X^4) * (Phi (gP N) - gP N) by rewrite /SP /Phi; ring.
    apply: tc0_mull; apply: tc_sub0; exact: tc_sym (g_fix N).
  Qed.

  Lemma SP_indep N M : (N <= M)%N -> tc N.+1 (SP N) (SP M).
  Proof. by move=> H; apply: tc_sub (tc_refl _ _) (tc_mull _ (g_indep H)). Qed.

  (* the inverse of a series with constant term 1 *)
  Lemma inv_size (g : seq F) n : size (sr_inv_aux g n) = n.+1.
  Proof. by elim: n => [ | n IH ] //=; rewrite size_rcons IH. Qed.

  Definition Bd (g : seq F) j : F := nth 0 (sr_inv_aux g j) j.

  Lemma inv_nth (g : seq F) n j :
    nth 0 (sr_inv_aux g n) j = if (j <= n)%N then Bd g j else 0.
  Proof.
    elim: n => [ | n IH ]; first by case: j => [ | [ | j ] ].
    rewrite /= nth_rcons inv_size.
    case: ltnP => Hj; first by rewrite IH -ltnS Hj (ltnW Hj).
    case: eqP => Ej.
    - by rewrite Ej leqnn /Bd /= nth_rcons inv_size ltnn eqxx.
    - by rewrite leqNgt ltn_neqAle Hj eq_sym; move/eqP: Ej => ->.
  Qed.

  Lemma Bd_rec (g : seq F) m :
    Bd g m.+1 = - \sum_(i < m.+1) nth 0 g i.+1 * Bd g (m - i).
  Proof.
    rewrite {1}/Bd /= nth_rcons inv_size ltnn eqxx lsum_shift lsum_big add0n big_mkord.
    congr (- _); apply: eq_bigr => i _.
    by rewrite subSS inv_nth leq_subr.
  Qed.

  Lemma inv_aux_tc (g : seq F) N : nth 0 g 0 = 1 ->
    tc N.+1 (Poly g * Poly (sr_inv_aux g N)) 1.
  Proof.
    move=> H0; constructor=> i Hi; rewrite coefM coef1.
    have -> : \sum_(j < i.+1) (Poly g)`_j * (Poly (sr_inv_aux g N))`_(i - j)
            = \sum_(j < i.+1) nth 0 g j * Bd g (i - j).
    { apply: eq_bigr => j _; rewrite !coef_Poly inv_nth ifT //.
      exact: leq_trans (leq_subr _ _) _. }
    case: i Hi => [ | m ] Hi; first by rewrite big_ord1 H0 mul1r.
    rewrite big_ord_recl /= H0 mul1r Bd_rec.
    have -> : \sum_(i < m.+1) nth 0 g (bump 0 i) * Bd g (m.+1 - bump 0 i)
            = \sum_(i < m.+1) nth 0 g i.+1 * Bd g (m - i) by [].
    by rewrite addNr.
  Qed.

  (* the invariant differential *)
  Definition wP N : {poly F} := Poly (omega_ser A N).
  Definition Bi N : {poly F} := Poly (sr_inv_aux (g_ser A N) N).

  Lemma w_tc N : tc N.+1 (wP N) (1 + (2%:R^-1)%:P * ('X * (gP N)^`() * Bi N)).
  Proof.
    constructor=> i Hi; rewrite coef_Poly /omega_ser nth_mkseq0 Hi coefD coef1 coefCM.
    congr (_ + _ * _); rewrite lsum_big add0n big_mkord coefM; apply: eq_bigr => j _.
    rewrite coefXM coef_deriv /Bi /gP !coef_Poly.
    case: j => j Hj /=; case: j Hj => [ | k ] Hk /=; first by rewrite !mul0r.
    by rewrite mulr_natl.
  Qed.

  Lemma XdPhi (G : {poly F}) :
    'X * (Phi G)^`() = (4%:R * A)%:P * 'X^4 * G ^+ 2 + (2%:R * A)%:P * 'X^4 * G * ('X * G^`()).
  Proof. rewrite /Phi expr2 !derivE /=; ring. Qed.

  Lemma half4 : (2%:R^-1 * 4%:R : F) = 2%:R.
  Proof. have H2 := natf_neq0 (isT : (0 < 2)%N); field. Qed.

  Lemma omega_S N : tc N.+1 (wP N * SP N) 1.
  Proof.
    set G := gP N; set H := 'X * G^`(); set B := Bi N.
    have Hd : tc N.+1 H ('X * (Phi G)^`()) by apply/tc_mulX/tc_deriv/g_fix.
    have HS : tc N.+1 (H * SP N) ((4%:R * A)%:P * 'X^4 * G ^+ 2).
    { apply: tc_of_sub0.
      have -> : H * SP N - (4%:R * A)%:P * 'X^4 * G ^+ 2 = H - 'X * (Phi G)^`()
        by rewrite XdPhi /SP -/G -/H; ring.
      exact: tc_sub0. }
    have GB : tc N.+1 (G * B) 1 by apply: inv_aux_tc; rewrite -coef_Poly; exact: gP0.
    apply: tc_trans (tc_mulr (SP N) (w_tc N)) _.
    have -> : (1 + (2%:R^-1)%:P * ('X * G^`() * B)) * SP N
            = SP N + (2%:R^-1)%:P * B * (H * SP N) by rewrite -/H; ring.
    apply: tc_trans (tc_add (tc_refl _ _) (tc_mull _ HS)) _.
    have -> : SP N + (2%:R^-1)%:P * B * ((4%:R * A)%:P * 'X^4 * G ^+ 2)
            = SP N + (2%:R^-1 * 4%:R)%:P * A%:P * 'X^4 * G * (G * B) by ring.
    apply: tc_trans (tc_add (tc_refl _ _) (tc_mull _ GB)) _.
    rewrite half4 /SP -/G; have -> : 1 - (2%:R * A)%:P * 'X^4 * G + (2%:R)%:P * A%:P * 'X^4 * G * 1 = 1
      by ring.
    exact: tc_refl.
  Qed.

  Lemma omega_indep N M : (N <= M)%N -> tc N.+1 (wP N) (wP M).
  Proof.
    move=> H; apply: tc_inv_uniq (omega_S N) _.
    apply: tc_trans (tc_mull _ (SP_indep H)) _.
    exact: tc_le _ (omega_S M).
  Qed.

  Lemma wP0 N : (wP N)`_0 = 1.
  Proof. by have := tcE (omega_S N) (ltn0Sn N); rewrite coef0M SP0 mulr1 coef1. Qed.

  (* the truncated logarithm *)
  Definition LK K : {poly F} := \poly_(t < K.+1) ct_gen A t.

  Lemma LK_deriv K : tc K (LK K)^`() (wP K).
  Proof.
    constructor=> i Hi; rewrite coef_deriv coef_poly ltnS Hi /=.
    rewrite -mulr_natl mulrA mulfV ?natf_neq0 // mul1r.
    rewrite -coef_Poly -/(wP i); exact: tcE (omega_indep (ltnW Hi)) i (ltnSn i).
  Qed.

  Lemma LK_0 K : (LK K)`_0 = 0.
  Proof. by rewrite coef_poly. Qed.

  Lemma LK_1 K : (0 < K)%N -> (LK K)`_1 = 1.
  Proof.
    move=> HK; have := tcE (LK_deriv K) HK; rewrite coef_deriv wP0 => <-.
    by rewrite mulr1n.
  Qed.

End recipe.

(** * F2'. Integrality with respect to a subring *)

Section integral.

  Variable F : fieldType.

  (* subring predicates (Prop-valued) *)
  Record sring (O : F -> Prop) : Prop := SRing {
    sr0 : O 0; sr1 : O 1; sradd : forall x y, O x -> O y -> O (x + y);
    sropp : forall x, O x -> O (- x); srmul : forall x y, O x -> O y -> O (x * y) }.

  Variable O : F -> Prop.
  Hypothesis HO : sring O.
  Let O0 : O 0 := sr0 HO.
  Let O1 : O 1 := sr1 HO.
  Let Oadd : forall x y, O x -> O y -> O (x + y) := sradd HO.
  Let Oopp : forall x, O x -> O (- x) := sropp HO.
  Let Omul : forall x y, O x -> O y -> O (x * y) := srmul HO.

  Lemma O_sub x y : O x -> O y -> O (x - y).
  Proof. by move=> Hx Hy; apply: Oadd Hx (Oopp Hy). Qed.

  Lemma O_nat (n : nat) : O n%:R.
  Proof. by elim: n => [ | n IH ] //; rewrite mulrS; apply: Oadd. Qed.

  Lemma O_exp x n : O x -> O (x ^+ n).
  Proof. by move=> Hx; elim: n => [ | n IH ]; rewrite ?expr0 // exprS; apply: Omul. Qed.

  Lemma O_sum (I : Type) (r : seq I) (P : pred I) (G : I -> F) :
    (forall i, P i -> O (G i)) -> O (\sum_(i <- r | P i) G i).
  Proof. by move=> H; apply: big_ind => //; exact: Oadd. Qed.

  (* integral polynomials *)
  Variant pint (f : {poly F}) : Prop := PintI of (forall i, O f`_i).

  Lemma pintE f i : pint f -> O f`_i. Proof. by case. Qed.

  Lemma pint_add f g : pint f -> pint g -> pint (f + g).
  Proof. by move=> [Hf] [Hg]; constructor=> i; rewrite coefD; apply: Oadd. Qed.
  Lemma pint_opp f : pint f -> pint (- f).
  Proof. by move=> [Hf]; constructor=> i; rewrite coefN; apply: Oopp. Qed.
  Lemma pint_sub f g : pint f -> pint g -> pint (f - g).
  Proof. by move=> Hf Hg; apply: pint_add Hf (pint_opp Hg). Qed.
  Lemma pint_C c : O c -> pint c%:P.
  Proof. by move=> Hc; constructor=> i; rewrite coefC; case: (i == 0). Qed.
  Lemma pint_1 : pint 1. Proof. exact: pint_C. Qed.
  Lemma pint_0 : pint 0. Proof. by constructor=> i; rewrite coef0. Qed.
  Lemma pint_X : pint 'X. Proof. by constructor=> i; rewrite coefX; apply: O_nat. Qed.
  Lemma pint_mul f g : pint f -> pint g -> pint (f * g).
  Proof.
    move=> [Hf] [Hg]; constructor=> i; rewrite coefM; apply: O_sum => j _.
    exact: Omul.
  Qed.
  Lemma pint_exp f n : pint f -> pint (f ^+ n).
  Proof.
    move=> Hf; elim: n => [ | n IH ]; first by rewrite expr0; exact: pint_1.
    by rewrite exprS; apply: pint_mul.
  Qed.
  Lemma pint_Xn n : pint 'X^n. Proof. exact: pint_exp pint_X. Qed.
  Lemma pint_scale c f : O c -> pint f -> pint (c *: f).
  Proof. by move=> Hc [Hf]; constructor=> i; rewrite coefZ; apply: Omul. Qed.
  Lemma pint_sum (I : Type) (r : seq I) (P : pred I) (G : I -> {poly F}) :
    (forall i, P i -> pint (G i)) -> pint (\sum_(i <- r | P i) G i).
  Proof.
    move=> H; constructor=> k; rewrite coef_sum; apply: O_sum => i Hi.
    exact: pintE (H i Hi).
  Qed.
  Lemma pint_comp f h : pint f -> pint h -> pint (f \Po h).
  Proof.
    move=> Hf Hh; rewrite comp_polyE; apply: pint_sum => i _.
    by apply: pint_scale (pintE _ Hf) (pint_exp _ Hh).
  Qed.
  Lemma horner_O f x : pint f -> O x -> O f.[x].
  Proof.
    move=> [Hf] Hx; rewrite horner_coef; apply: O_sum => i _.
    exact: Omul (Hf i) (O_exp i Hx).
  Qed.
  Lemma pint_ginv n f : pint f -> pint (ginv n f).
  Proof. by move=> Hf; apply: pint_sum => i _; apply: pint_exp; apply: pint_sub pint_1 Hf. Qed.

  Lemma pint_rsh n d : pint d -> pint (rsh n d).
  Proof. by move=> [Hd]; constructor=> i; rewrite coef_poly; case: ifP. Qed.

  (* a polynomial divisible by X^n evaluates to x^n times an integral value *)
  Lemma eval_tc0 n d x : pint d -> tc n d 0 -> O x -> exists r, O r /\ d.[x] = x ^+ n * r.
  Proof.
    move=> Hd H Hx; exists (rsh n d).[x]; split; first exact: horner_O (pint_rsh n Hd) Hx.
    by rewrite {1}(tc0P H) hornerM hornerXn mulrC.
  Qed.

  (* f(a) - f(b) = (a - b) c with c integral *)
  Lemma lipschitz f a b : pint f -> O a -> O b ->
    exists c, O c /\ f.[a] - f.[b] = (a - b) * c.
  Proof.
    move=> [Hf] Ha Hb.
    exists (\sum_(i < size f) f`_i * \sum_(j < i) a ^+ (i.-1 - j) * b ^+ j); split.
    - apply: O_sum => i _; apply: Omul (Hf i) _; apply: O_sum => j _.
      by apply: Omul; apply: O_exp.
    - rewrite !horner_coef -sumrB mulr_sumr; apply: eq_bigr => i _.
      by rewrite -mulrBr subrXX mulrCA.
  Qed.

  (* the recipe is integral *)
  Section recipe_int.

    Hypothesis natf_neq0 : forall n : nat, (0 < n)%N -> n%:R != 0 :> F.
    Variable A : F.
    Hypothesis OA : O A.

    Lemma pint_Phi G : pint G -> pint (Phi A G).
    Proof.
      move=> HG; apply: pint_add pint_1 _.
      by apply: pint_mul (pint_mul (pint_C OA) (pint_Xn 4)) (pint_exp 2 HG).
    Qed.

    Lemma pint_Gj N j : pint (Gj A N j).
    Proof.
      elim: j => [ | j IH ].
      - constructor=> i; rewrite /Gj coef_Poly /= /sr_one nth_mkseq0.
        by case: ifP => _ //; apply: O_nat.
      - constructor=> i; rewrite /Gj iterS g_step_coef.
        by case: ifP => _ //; apply: pintE (pint_Phi IH).
    Qed.

    Lemma pint_gP N : pint (gP A N). Proof. exact: (pint_Gj N N.+1). Qed.

    Lemma pint_SP N : pint (SP A N).
    Proof.
      apply: pint_sub pint_1 _; apply: pint_mul (pint_gP N).
      by apply: pint_mul (pint_Xn 4); apply/pint_C/Omul/OA/O_nat.
    Qed.

    Lemma wP_int N i : (i <= N)%N -> O (wP A N)`_i.
    Proof.
      move=> Hi.
      have H := tc_inv_uniq (omega_S natf_neq0 A N) (ginvP N.+1 (SP0 A N)).
      by rewrite (tcE H Hi); apply: pintE (pint_ginv _ (pint_SP N)).
    Qed.

    Lemma pint_LK K : (forall t : nat, (0 < t <= K)%N -> O (t%:R^-1)) -> pint (LK A K).
    Proof.
      move=> Ht; constructor=> i; rewrite coef_poly; case: ifP => // Hi.
      case: i Hi => [ | t ] Hi //=; apply: Omul; first by apply: Ht; rewrite ltn0Sn -ltnS.
      by rewrite -coef_Poly; apply: wP_int.
    Qed.

  End recipe_int.

End integral.

(** * F3. The formal addition theorem *)

Section euler.

  Variable F : fieldType.
  Hypothesis natf_neq0 : forall n : nat, (0 < n)%N -> n%:R != 0 :> F.
  Variables (A u1 u2 : F) (K : nat) (S w L : {poly F}).
  Hypotheses (S0 : S`_0 = 1) (Ssq : tc K.+1 (S ^+ 2) (1 - (4%:R * A)%:P * 'X^4))
             (wS : tc K (w * S) 1) (Ld : tc K L^`() w) (L0 : L`_0 = 0).

  Definition scl (u : F) : {poly F} := u%:P * 'X.

  Lemma scl0 u : (scl u)`_0 = 0.
  Proof. by rewrite coef0E /scl !hornerE. Qed.

  Lemma deriv_scl u : (scl u)^`() = u%:P.
  Proof. by rewrite /scl derivM derivC derivX mul0r add0r mulr1. Qed.

  Local Abbreviation C := ((4%:R * A)%:P : {poly F}).
  Local Abbreviation p := (scl u1).
  Local Abbreviation q := (scl u2).
  Local Abbreviation U1 := (u1%:P : {poly F}).
  Local Abbreviation U2 := (u2%:P : {poly F}).
  Local Abbreviation S1 := (S \Po scl u1).
  Local Abbreviation S2 := (S \Po scl u2).

  Definition Qe : {poly F} := 1 + C * p ^+ 2 * q ^+ 2.
  Definition Ie : {poly F} := ginv K.+1 Qe.
  Definition N0 : {poly F} := p * S2 + q * S1.
  Definition ge : {poly F} := N0 * Ie.
  Definition T0 : {poly F} :=
    (1 - C * p ^+ 2 * q ^+ 2) * S1 * S2 - 2%:R * C * p * q * (p ^+ 2 + q ^+ 2).
  Definition Te : {poly F} := T0 * Ie ^+ 2.

  Lemma Si0 u : (S \Po scl u)`_0 = 1.
  Proof. by rewrite coef0_comp scl0 horner_coef0. Qed.

  Lemma Si_sq u : tc K.+1 ((S \Po scl u) ^+ 2) (1 - C * scl u ^+ 4).
  Proof.
    have H := tc_comp_l (scl0 u) Ssq; rewrite rmorphXn /= in H.
    apply: tc_trans H _.
    by rewrite rmorphB rmorph1 rmorphM rmorphXn /= comp_polyC comp_polyX; exact: tc_refl.
  Qed.

  Lemma half2 : (2%:R^-1 * 2%:R : F) = 1.
  Proof. by rewrite mulVf // natf_neq0. Qed.

  Lemma SSd : tc K (S * S^`()) (- (2%:R * C) * 'X ^+ 3).
  Proof.
    have H := tc_mull (2%:R^-1)%:P (tc_deriv Ssq).
    have E1 : (2%:R^-1)%:P * (S ^+ 2)^`() = (2%:R^-1 * 2%:R)%:P * (S * S^`()).
    { rewrite expr2 derivM; ring. }
    have E2 : (2%:R^-1)%:P * (1 - C * 'X^4)^`() = (2%:R^-1 * 2%:R)%:P * (- (2%:R * C) * 'X ^+ 3).
    { rewrite derivB derivC deriv_mulC derivXn /=; ring. }
    by rewrite E1 E2 half2 polyC1 !mul1r in H.
  Qed.

  Lemma SiSid u : tc K ((S \Po scl u) * (S \Po scl u)^`()) (- (2%:R * C) * scl u ^+ 3 * u%:P).
  Proof.
    rewrite deriv_comp deriv_scl mulrA -rmorphM.
    apply: tc_mulr; have H := tc_comp_l (scl0 u) SSd.
    apply: tc_trans H _.
    rewrite rmorphM rmorphN rmorphM rmorphXn rmorph_nat /= !comp_polyC comp_polyX; exact: tc_refl.
  Qed.

  Lemma Qe0 : Qe`_0 = 1.
  Proof. by rewrite coef0E /Qe /scl !hornerE ?expr0n /= ?(mulr0, mul0r, addr0). Qed.

  Lemma IQ : tc K.+1 (Ie * Qe) 1.
  Proof. exact: ginvP Qe0. Qed.

  Lemma Ie0 : Ie`_0 = 1.
  Proof. by have := tcE IQ (ltn0Sn K); rewrite coef0M Qe0 mulr1 coef1. Qed.

  Lemma ge0 : ge`_0 = 0.
  Proof. by rewrite /ge coef0M coef0E /N0 /scl !hornerE ?(mulr0, mul0r, addr0). Qed.

  (* certificate 1 *)
  Definition cert_a : {poly F} :=
    - C ^+ 2 * p ^+ 4 * q ^+ 4 + C * q ^+ 4 * S1 ^+ 2 + 4%:R * C * p * q ^+ 3 * S1 * S2
    + C * q ^+ 4 + S2 ^+ 2 * (C ^+ 2 * p ^+ 4 * q ^+ 4 + 4%:R * C * p ^+ 2 * q ^+ 2 + 1).
  Definition cert_b : {poly F} :=
    - C ^+ 3 * p ^+ 8 * q ^+ 4 - 4%:R * C ^+ 2 * p ^+ 6 * q ^+ 2 + 4%:R * C * p ^+ 3 * q * S1 * S2
    + C * p ^+ 4 * S2 ^+ 2 + 4%:R * C * p ^+ 2 * q ^+ 2 + 1.

  Lemma cert1 : T0 ^+ 2 + C * N0 ^+ 4 - Qe ^+ 4
              = cert_a * (S1 ^+ 2 - (1 - C * p ^+ 4)) + cert_b * (S2 ^+ 2 - (1 - C * q ^+ 4)).
  Proof. rewrite /T0 /N0 /Qe /cert_a /cert_b; ring. Qed.

  Lemma Sg_sq : tc K.+1 ((S \Po ge) ^+ 2) (1 - C * ge ^+ 4).
  Proof.
    have H := tc_comp_l ge0 Ssq; rewrite rmorphXn /= in H.
    apply: tc_trans H _.
    by rewrite rmorphB rmorph1 rmorphM rmorphXn /= comp_polyC comp_polyX; exact: tc_refl.
  Qed.

  Lemma Te_sq : tc K.+1 (Te ^+ 2) (1 - C * ge ^+ 4).
  Proof.
    apply: tc_of_sub0.
    have -> : Te ^+ 2 - (1 - C * ge ^+ 4)
            = (T0 ^+ 2 + C * N0 ^+ 4 - Qe ^+ 4) * Ie ^+ 4 + ((Ie * Qe) ^+ 4 - 1)
      by rewrite /Te /ge; ring.
    rewrite cert1; apply: tc_of_sub0; rewrite subr0 -[0]addr0.
    apply: tc_add; last by rewrite -(expr1n _ 4); apply: tc_sub0; apply/tc_exp/IQ.
    rewrite -[0](mulr0 (Ie ^+ 4)) mulrC; apply: tc_mull.
    rewrite -[0]addr0; apply: tc_add; apply: tc0_mull; apply: tc_sub0; exact: Si_sq.
  Qed.

  Lemma scl_at0 u : (scl u).[0] = 0.
  Proof. by rewrite /scl hornerCM hornerX mulr0. Qed.

  Lemma Si_at0 u : (S \Po scl u).[0] = 1.
  Proof. by rewrite horner_comp scl_at0 horner_coef0. Qed.

  Lemma Te0 : Te`_0 = 1.
  Proof.
    rewrite coef0E -horner_evalE /Te /T0.
    rewrite !(rmorphB, rmorphD, rmorphM, rmorphXn, rmorph1, rmorph_nat) /= !horner_evalE.
    rewrite !hornerC hornerX !Si_at0 horner_coef0 Ie0; ring.
  Qed.

  Lemma S_comp_g : tc K.+1 (S \Po ge) Te.
  Proof.
    have H1 : (S \Po ge)`_0 = 1 by rewrite coef0_comp ge0 horner_coef0.
    exact: (tc_sqrt_uniq natf_neq0 H1 Te0 (tc_trans Sg_sq (tc_sym Te_sq))).
  Qed.

  (* certificate 2 *)
  Lemma N0_deriv : N0^`() = U1 * S2 + p * S2^`() + U2 * S1 + q * S1^`().
  Proof. by rewrite /N0 derivD (derivM (scl u1)) (derivM (scl u2)) !deriv_scl; ring. Qed.

  Lemma Qe_deriv : Qe^`() = 2%:R * C * p * q * (U1 * q + U2 * p).
  Proof.
    rewrite /Qe derivD derivC !expr2 (derivM _ (scl u2 * scl u2)) (derivM (scl u2)).
    rewrite deriv_mulC (derivM (scl u1)) !deriv_scl; ring.
  Qed.

  Lemma cert2 :
    (N0^`() * Qe - N0 * Qe^`()) * S1 * S2 - T0 * (U1 * S2 + U2 * S1)
    = S2 * q * Qe * (S1 * S1^`() + 2%:R * C * p ^+ 3 * U1)
    + S1 * p * Qe * (S2 * S2^`() + 2%:R * C * q ^+ 3 * U2)
    - 2%:R * C * p ^+ 2 * q ^+ 2 * U2 * S2 * (S1 ^+ 2 - (1 - C * p ^+ 4))
    - 2%:R * C * p ^+ 2 * q ^+ 2 * U1 * S1 * (S2 ^+ 2 - (1 - C * q ^+ 4)).
  Proof. rewrite N0_deriv Qe_deriv /N0 /Qe /T0 /scl; ring. Qed.

  Lemma Ie_deriv : tc K (Ie^`()) (- (Ie ^+ 2 * Qe^`())).
  Proof.
    have D : tc K ((Ie * Qe)^`()) 0 by rewrite -(@derivC _ 1); apply: tc_deriv IQ.
    rewrite derivM in D.
    have E : Ie^`() + Ie ^+ 2 * Qe^`() = Ie^`() * (1 - Ie * Qe) + Ie * (Ie^`() * Qe + Ie * Qe^`())
      by ring.
    apply: tc_of_sub0; rewrite opprK E -[0]addr0.
    apply: tc_add; first by apply: tc0_mull; apply: tc_sub0; exact: tc_sym (tc_le (leqnSn K) IQ).
    exact: tc0_mull D.
  Qed.

  Lemma g_deriv : tc K (ge^`() * S1 * S2) (Te * (U1 * S2 + U2 * S1)).
  Proof.
    have IQK := tc_le (leqnSn K) IQ.
    have H1 : tc K ge^`() ((N0^`() * Qe - N0 * Qe^`()) * Ie ^+ 2).
    { apply: tc_of_sub0.
      have -> : ge^`() - (N0^`() * Qe - N0 * Qe^`()) * Ie ^+ 2
              = N0^`() * Ie * (1 - Ie * Qe) + N0 * (Ie^`() - - (Ie ^+ 2 * Qe^`()))
        by rewrite /ge derivM; ring.
      rewrite -[0]addr0; apply: tc_add; apply: tc0_mull; apply: tc_sub0.
      - exact: tc_sym IQK.
      - exact: Ie_deriv. }
    have H2 : tc K ((N0^`() * Qe - N0 * Qe^`()) * S1 * S2) (T0 * (U1 * S2 + U2 * S1)).
    { apply: tc_of_sub0; rewrite cert2.
      have Z1 : tc K (S1 * S1^`() + 2%:R * C * p ^+ 3 * U1) 0.
      { have E : S1 * S1^`() - (- (2%:R * C) * scl u1 ^+ 3 * u1%:P)
               = S1 * S1^`() + 2%:R * C * p ^+ 3 * U1 by ring.
        rewrite -E; exact: tc_sub0 (SiSid u1). }
      have Z2 : tc K (S2 * S2^`() + 2%:R * C * q ^+ 3 * U2) 0.
      { have E : S2 * S2^`() - (- (2%:R * C) * scl u2 ^+ 3 * u2%:P)
               = S2 * S2^`() + 2%:R * C * q ^+ 3 * U2 by ring.
        rewrite -E; exact: tc_sub0 (SiSid u2). }
      have Z3 := tc_sub0 (tc_le (leqnSn K) (Si_sq u1)).
      have Z4 := tc_sub0 (tc_le (leqnSn K) (Si_sq u2)).
      apply: tc0_sub; [ apply: tc0_sub; [ apply: tc0_add | ] | ]; apply: tc0_mull.
      - exact: Z1.
      - exact: Z2.
      - exact: Z3.
      - exact: Z4. }
    apply: tc_trans (tc_mulr S2 (tc_mulr S1 H1)) _.
    have -> : (N0^`() * Qe - N0 * Qe^`()) * Ie ^+ 2 * S1 * S2
            = ((N0^`() * Qe - N0 * Qe^`()) * S1 * S2) * Ie ^+ 2 by ring.
    apply: tc_trans (tc_mulr _ H2) _.
    have -> : T0 * (U1 * S2 + U2 * S1) * Ie ^+ 2 = Te * (U1 * S2 + U2 * S1) by rewrite /Te; ring.
    exact: tc_refl.
  Qed.

  Lemma comp_inv u : tc K ((w \Po scl u) * (S \Po scl u)) 1.
  Proof.
    have H := tc_comp_l (scl0 u) wS; rewrite rmorphM rmorph1 /= in H; exact: H.
  Qed.

  (* the formal addition theorem *)
  Theorem log_add_formal : tc K.+1 (L \Po ge) ((L \Po scl u1) + (L \Po scl u2)).
  Proof.
    have H0 : (L \Po ge)`_0 = ((L \Po scl u1) + (L \Po scl u2))`_0.
    { by rewrite coefD !coef0_comp ge0 !scl0 horner_coef0 L0 addr0. }
    apply: (tc_integ natf_neq0 H0).
    rewrite derivD !deriv_comp !deriv_scl.
    set W := w \Po ge; set w1 := w \Po scl u1; set w2 := w \Po scl u2.
    have HW : tc K (L^`() \Po ge) W := tc_comp_l ge0 Ld.
    have HL1 : tc K (L^`() \Po scl u1) w1 := tc_comp_l (scl0 u1) Ld.
    have HL2 : tc K (L^`() \Po scl u2) w2 := tc_comp_l (scl0 u2) Ld.
    apply: tc_trans (tc_mulr _ HW) _.
    apply: tc_trans _ (tc_sym (tc_add (tc_mulr _ HL1) (tc_mulr _ HL2))).
    have WS : tc K (W * (S \Po ge)) 1.
    { have H := tc_comp_l ge0 wS; rewrite rmorphM rmorph1 /= in H; exact: H. }
    have WT : tc K (W * Te) 1.
    { apply: tc_trans _ WS; apply: tc_mull; apply: tc_sym; exact: tc_le (leqnSn K) S_comp_g. }
    have W1 := comp_inv u1; have W2 := comp_inv u2.
    have E1 : tc K (W * ge^`()) (W * ge^`() * ((w1 * S1) * (w2 * S2))).
    { rewrite -[X in tc K X]mulr1; apply: tc_mull; apply: tc_sym.
      by rewrite -[1](mulr1 1); apply: tc_mul. }
    apply: tc_trans E1 _.
    have -> : W * ge^`() * ((w1 * S1) * (w2 * S2)) = W * (ge^`() * S1 * S2) * (w1 * w2) by ring.
    apply: tc_trans (tc_mulr _ (tc_mull _ g_deriv)) _.
    have -> : W * (Te * (U1 * S2 + U2 * S1)) * (w1 * w2) = (W * Te) * ((U1 * S2 + U2 * S1) * w1 * w2)
      by ring.
    apply: tc_trans (tc_mulr _ WT) _.
    have -> : 1 * ((U1 * S2 + U2 * S1) * w1 * w2) = U1 * w1 * (w2 * S2) + U2 * w2 * (w1 * S1) by ring.
    apply: tc_trans (tc_add (tc_mull _ W2) (tc_mull _ W1)) _.
    have -> : U1 * w1 * 1 + U2 * w2 * 1 = w1 * U1 + w2 * U2 by ring.
    exact: tc_refl.
  Qed.

End euler.
