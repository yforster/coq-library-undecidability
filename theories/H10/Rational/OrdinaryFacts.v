(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2C, part 1: the ORDINARY statements behind the elementary
   transfer fields of Ambient.v about *Z, primes and the valuations
   v_q on *Q (fields trZ0, trZ1_*, trV0, trZ2, trPR, trV1, trV2_*,
   trV3, trV4, trV5), proved for rat.

   Shape. The ultrapower (Phase 2B) interprets each ambient symbol
   pointwise by an ordinary one; the ordinary interpretations are:
   - [isZo x]     for  isZ x      (x is an integer),
   - [primeo q]   for  primeA q   (q is a prime number),
   - [vqo q x]    for  vq q x     (v_q(x), int-valued, junk 0 at x = 0
                                   or when q is not a prime).
   Every theorem below is the Ambient field with these substitutions
   (and casts int -> rat where the ambient field lives in sQ). The
   existential field trZ2 comes with an explicit witness function
   [zhalf], so that no choice is needed pointwise.

   Additional nat-indexed facts about [vqr] (RatVal.v) used in the
   other files of Phase 2C: values at q^k, 2, 4, integrality, and
   [vqr_lt0_notZ] (negative valuation implies non-integer).

   No axioms. *)

From Stdlib Require Import ZArith Lia List.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential FixedData RatVal.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

(** * The ordinary interpretations *)

Definition isZo (x : rat) : Prop := exists z : int, x = z%:~R.
Definition primeo (x : rat) : Prop := exists p : nat, x = p%:R /\ prime p.
Definition vqo (q x : rat) : int := vqr `|numq q| x.

(* the witness for parity (trZ2): floor (x / 2) for an integer x *)
Definition zhalf (x : rat) : rat := ((numq x %/ 2)%Z)%:~R.

Lemma natr_intr (n : nat) : n%:R = (n%:Z)%:~R :> rat.
Proof. by rewrite -pmulrn. Qed.

Lemma isZo_nat (n : nat) : isZo n%:R.
Proof. by exists n; rewrite natr_intr. Qed.

Lemma isZo_numq (x : rat) : isZo x -> x = (numq x)%:~R.
Proof. by move=> [z ->]; rewrite numq_int. Qed.

Lemma primeo_nat (q : rat) : primeo q -> q = (`|numq q|)%:R /\ prime `|numq q|.
Proof.
  move=> [p [-> Hp]]; rewrite natr_intr numq_int /=.
  by rewrite -natr_intr.
Qed.

Lemma vqo_nat (p : nat) (x : rat) : vqo p%:R x = vqr p x.
Proof. by rewrite /vqo natr_intr numq_int. Qed.

(** * *Z (Z0, Z1, V0, Z2) *)

(* ordinary version of trZ0: sqrt2 is irrational *)
Lemma ord_Z0 (x : rat) : x * x <> 2%:R.
Proof.
  move=> H.
  have Hx : x != 0.
  { apply/eqP => E; move: H; rewrite E mulr0 => /eqP; by rewrite eq_sym pnatr_eq0. }
  have E : numq x * numq x = 2%:Z * (denq x * denq x).
  { apply: (@intr_inj rat); rewrite !intrM !numqE mulrACA H. by []. }
  have En : (`|numq x| * `|numq x| = 2 * (`|denq x| * `|denq x|))%N.
  { by rewrite -!abszM E abszM. }
  have Hn : (0 < `|numq x|)%N by rewrite absz_gt0 numq_eq0.
  have Hd : (0 < `|denq x|)%N by rewrite absz_gt0 denq_neq0.
  move: (congr1 (logn 2) En).
  rewrite lognM // lognM ?muln_gt0 ?Hd // lognM // (@logn_prime 2 2) //=.
  move/(congr1 odd); rewrite !oddD !addbb /=.
  done.
Qed.

(* the norm of a nonzero element of F = Q(sqrt2) is nonzero (consequence of Z0) *)
Lemma qe_norm_neq0 (x : qe rat) : x != 0 -> qe_norm x != 0.
Proof.
  case: x => a b Hx; rewrite /qe_norm /=; apply/eqP => H.
  case: (eqVneq b 0) => [Hb | Hb].
  - move: H Hx; rewrite Hb expr0n /= mulr0 subr0 => /eqP; rewrite sqrf_eq0 => /eqP ->.
    by rewrite qe0E eqxx.
  - apply: (@ord_Z0 (a / b)).
    have : a ^+ 2 = 2%:R * b ^+ 2 by apply/eqP; rewrite -subr_eq0 H.
    by move=> E; rewrite -expr2 expr_div_n E mulfK // sqrf_eq0.
Qed.

(* ordinary versions of trZ1_int, trZ1_add, trZ1_opp, trZ1_mul *)
Lemma ord_Z1_int (z : int) : isZo z%:~R.
Proof. by exists z. Qed.

Lemma ord_Z1_add (x y : rat) : isZo x -> isZo y -> isZo (x + y).
Proof. by move=> [a ->] [b ->]; exists (a + b); rewrite intrD. Qed.

Lemma ord_Z1_opp (x : rat) : isZo x -> isZo (- x).
Proof. by move=> [a ->]; exists (- a); rewrite intrN. Qed.

Lemma ord_Z1_mul (x y : rat) : isZo x -> isZo y -> isZo (x * y).
Proof. by move=> [a ->] [b ->]; exists (a * b); rewrite intrM. Qed.

Lemma ord_Z1_sub (x y : rat) : isZo x -> isZo y -> isZo (x - y).
Proof. by move=> Hx Hy; apply: ord_Z1_add => //; apply: ord_Z1_opp. Qed.

(* ordinary version of trV0: an integer > 0 is >= 1 *)
Lemma ord_V0 (x : rat) : isZo x -> 0 < x -> 1 <= x.
Proof. by move=> [z ->]; rewrite ltr0z ler1z. Qed.

(* ordinary version of trZ2: parity, with the witness [zhalf x] *)
Lemma ord_Z2_fun (x : rat) : isZo x ->
  isZo (zhalf x) /\ (x = 2%:R * zhalf x \/ x = 2%:R * zhalf x + 1).
Proof.
  move=> Hx; split; first by exists (numq x %/ 2)%Z.
  move: Hx => [z ->]; rewrite /zhalf numq_int.
  have E := divz_eq z 2.
  have H0 : 0 <= (z %% 2)%Z by rewrite modz_ge0.
  have H1 : (z %% 2)%Z < 2 by have := ltz_mod z (d := 2); rewrite /=; apply.
  have : (z %% 2)%Z = 0 \/ (z %% 2)%Z = 1.
  { move: H0 H1; case: (z %% 2)%Z => [ [ | [ | n ] ] | n ] //=; auto. }
  case=> Hm; [ left | right ]; rewrite {1}E Hm ?addr0 ?intrD intrM mulrC //.
Qed.

Lemma ord_Z2 (x : rat) : isZo x -> exists y, isZo y /\ (x = 2%:R * y \/ x = 2%:R * y + 1).
Proof. move=> /ord_Z2_fun H; by exists (zhalf x). Qed.

(** * Primes (PR, V1) *)

(* ordinary version of trPR *)
Lemma ord_PR (p : nat) : primeo p%:R <-> prime p.
Proof.
  split.
  - move=> [p' [/eqP E Hp']]; move: E; rewrite eqr_nat => /eqP ->; exact Hp'.
  - move=> Hp; by exists p.
Qed.

(* ordinary version of trV1 *)
Lemma ord_V1 (q : rat) : primeo q -> isZo q /\ 1 < q.
Proof.
  move=> [p [-> Hp]]; split; first exact: isZo_nat.
  by rewrite ltr1n prime_gt1.
Qed.

Lemma primeo_neq0 (q : rat) : primeo q -> q != 0.
Proof. move=> /ord_V1 [_ H]; apply/eqP => E; move: H; by rewrite E ltr10. Qed.

(** * Valuations: nat-indexed facts complementing RatVal.v *)

Section vqr_more.

  Variable q : nat.
  Hypothesis q_prime : prime q.

  Local Abbreviation v := (vqr q).

  Lemma vqr0 : v 0 = 0.
  Proof. by rewrite /vqr /= logn0 logn1. Qed.

  Lemma vqr_int_ge0 (z : int) : 0 <= v z%:~R.
  Proof. by rewrite vqr_int. Qed.

  Lemma vqr_nat_ge0 (n : nat) : 0 <= v n%:R.
  Proof. by rewrite natr_intr vqr_int_ge0. Qed.

  Lemma vqr_expq (k : nat) : v (q%:R ^+ k) = k%:Z.
  Proof using q_prime.
    rewrite -natrX natr_intr vqr_int /= lognX.
    by rewrite (@logn_prime q q q_prime) eqxx muln1.
  Qed.

  Lemma vqrX (x : rat) (k : nat) : x != 0 -> v (x ^+ k) = (k%:Z * v x)%R.
  Proof using.
    move=> Hx; elim: k => [ | k IH ]; first by rewrite expr0 vqr1 mul0r.
    rewrite exprS vqrM ?expf_neq0 // IH -[k.+1]addn1 PoszD mulrDl mul1r addrC.
    by [].
  Qed.

  (* for an odd prime, 2 and 4 are q-adic units (cf. trV5 for k = 2, 4) *)
  Lemma vqr_2 : q != 2%N -> v 2%:R = 0.
  Proof using q_prime.
    move=> Hq; apply: vqr_nat_ndvd.
    by rewrite (dvdn_prime2 q_prime (isT : prime 2)).
  Qed.

  Lemma vqr_4 : q != 2%N -> v 4%:R = 0.
  Proof using q_prime.
    move=> Hq; have -> : 4%:R = 2%:R * 2%:R :> rat by rewrite -natrM.
    by rewrite vqrM ?pnatr_eq0 // vqr_2.
  Qed.

  (* integers have nonnegative valuation; negative valuation means non-integer *)
  Lemma vqr_isZ_ge0 (x : rat) : isZo x -> 0 <= v x.
  Proof. by move=> [z ->]; apply: vqr_int_ge0. Qed.

  Lemma vqr_lt0_notZ (x : rat) : v x < 0 -> ~ isZo x.
  Proof. by move=> H /vqr_isZ_ge0 H'; move: H; rewrite ltNge H'. Qed.

  (* the min form of the ultrametric inequality *)
  Lemma vqr_ultra (x y : rat) : x != 0 -> y != 0 -> x + y != 0 ->
    Num.min (v x) (v y) <= v (x + y).
  Proof using q_prime.
    move=> Hx Hy Hxy; apply: vqr_add_ge => //; by rewrite ?ge_min ?lexx ?orbT.
  Qed.

  (* the valuation of a nonzero integer bounds its q-power divisibility *)
  Lemma vqr_dvd_int (z : int) (k : nat) : z != 0 ->
    (k%:Z <= v z%:~R) = (q ^ k %| `|z|)%N.
  Proof using q_prime.
    move=> Hz; rewrite vqr_int lez_nat pfactor_dvdn // absz_gt0 //.
  Qed.

End vqr_more.

(** * Valuations: the ambient-shaped ordinary statements (V2 to V5) *)

(* ordinary version of trV2_int: the values are integers *)
Lemma ord_V2_int (q x : rat) : primeo q -> x != 0 -> isZo (vqo q x)%:~R.
Proof. by move=> _ _; exists (vqo q x). Qed.

(* ordinary version of trV2_mul *)
Lemma ord_V2_mul (q x y : rat) : primeo q -> x != 0 -> y != 0 ->
  vqo q (x * y) = vqo q x + vqo q y.
Proof. move=> /primeo_nat [_ Hp]; exact: vqrM. Qed.

(* ordinary version of trV2_ultra *)
Lemma ord_V2_ultra (q x y : rat) : primeo q -> x != 0 -> y != 0 -> x + y != 0 ->
  Num.min (vqo q x) (vqo q y) <= vqo q (x + y).
Proof. move=> /primeo_nat [_ Hp]; exact: vqr_ultra. Qed.

(* ordinary version of trV3 *)
Lemma ord_V3 (q : rat) : primeo q -> vqo q q = 1.
Proof. move=> Hq; have [E Hp] := primeo_nat Hq; rewrite {2}E; exact: vqr_prime. Qed.

(* ordinary version of trV4 *)
Lemma ord_V4 (q x : rat) : primeo q -> isZo x -> x != 0 -> 0 <= vqo q x.
Proof. move=> _ Hx _; exact: vqr_isZ_ge0. Qed.

(* ordinary version of trV5 *)
Lemma ord_V5 (k : int) (q : rat) : k != 0 -> primeo q ->
  (forall p : nat, p \in primes `|k| -> q != p%:R) -> vqo q k%:~R = 0.
Proof.
  move=> Hk Hq H; have [E Hp] := primeo_nat Hq.
  rewrite /vqo vqr_int; congr Posz; apply/eqP; rewrite -leqn0 leqNgt logn_gt0.
  apply/negP => /H; by rewrite {1}E eqxx.
Qed.

(* the cast versions, as the ambient fields read them in sQ = rat *)
Lemma ord_V2_mulR (q x y : rat) : primeo q -> x != 0 -> y != 0 ->
  (vqo q (x * y))%:~R = (vqo q x)%:~R + (vqo q y)%:~R :> rat.
Proof. by move=> Hq Hx Hy; rewrite ord_V2_mul // intrD. Qed.

Lemma ord_V2_ultraR (q x y : rat) : primeo q -> x != 0 -> y != 0 -> x + y != 0 ->
  Num.min (vqo q x)%:~R (vqo q y)%:~R <= (vqo q (x + y))%:~R :> rat.
Proof.
  move=> Hq Hx Hy Hxy; have H := ord_V2_ultra Hq Hx Hy Hxy.
  by rewrite ge_min !ler_int -!ge_min.
Qed.
