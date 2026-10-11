(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Arithmetic in the ring Z[sqrt2] (PLAN P14a, Phase 2E).

   Everything here is about binary integers (Stdlib [Z]); there is no
   MathComp. The ring [Z2] of pairs (a, b) = a + b sqrt2 carries a
   Stdlib [ring] structure. Proved:
   - the norm is multiplicative and vanishes only at 0 (sqrt2 is
     irrational), so Z2 is an integral domain; units are the elements of
     norm +-1; divisibility is decidable;
   - Z2 is norm-Euclidean (rounding), hence Bezout (gcd as a linear
     combination);
   - prime elements ([z2prime]: Euclid's property): every element of
     prime norm is prime, every rational prime p with no square root of
     2 mod p is prime, and every nonzero nonunit has a prime divisor;
   - the unit group: every unit is +-(1+sqrt2)^e w^2 with e in {0,1}
     and w a unit (descent on the norm equation);
   - the factorization lemma used by the 2-isogeny descent
     ([factor_even]): an element whose exact power of every prime not
     dividing d (respectively of every prime) is even is
     unit * d^j * square (respectively unit * square);
   - the constants d = 75 - 53 sqrt2 (norm 7) and sqrt2 (norm -2) are
     prime, and divisibility by d is the vanishing of the reduction map
     Z2 -> Z/7, a + b sqrt2 |-> a + 3 b.

   No axioms. *)

From Stdlib Require Import ZArith Lia Zdivisibility Ring Wf_nat.


Local Open Scope Z_scope.

(** * 1. The ring Z[sqrt2] *)

Record Z2 : Set := Z2c { re : Z ; im : Z }.

Definition z2add (x y : Z2) : Z2 := Z2c (re x + re y) (im x + im y).
Definition z2mul (x y : Z2) : Z2 :=
  Z2c (re x * re y + 2 * (im x * im y)) (re x * im y + im x * re y).
Definition z2opp (x : Z2) : Z2 := Z2c (- re x) (- im x).
Definition z2sub (x y : Z2) : Z2 := z2add x (z2opp y).
Definition z20 : Z2 := Z2c 0 0.
Definition z21 : Z2 := Z2c 1 0.
Definition z2conj (x : Z2) : Z2 := Z2c (re x) (- im x).
Definition z2N (x : Z2) : Z := re x * re x - 2 * (im x * im x).
Definition z2of (n : Z) : Z2 := Z2c n 0.

Declare Scope z2_scope.
Delimit Scope z2_scope with z2.
Bind Scope z2_scope with Z2.
Infix "+" := z2add : z2_scope.
Infix "*" := z2mul : z2_scope.
Infix "-" := z2sub : z2_scope.
Notation "- x" := (z2opp x) : z2_scope.

Lemma Z2_ext a b c d : a = c -> b = d -> Z2c a b = Z2c c d.
Proof. intros -> ->; reflexivity. Qed.

Ltac z2_destr :=
  repeat match goal with x : Z2 |- _ => destruct x end;
  unfold z2sub, z2add, z2mul, z2opp, z20, z21, z2conj, z2N, z2of in *; cbn [re im] in *.

Lemma Z2_rt : ring_theory z20 z21 z2add z2mul z2sub z2opp (@eq Z2).
Proof. constructor; intros; z2_destr; apply Z2_ext; ring. Qed.

Add Ring Z2ring : Z2_rt.

Lemma Z2_eq_dec (x y : Z2) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Local Open Scope z2_scope.

Fixpoint z2pow (x : Z2) (n : nat) : Z2 :=
  match n with O => z21 | S n => x * z2pow x n end.

Lemma z2pow_add x i j : z2pow x (i + j) = z2pow x i * z2pow x j.
Proof. induction i; simpl; [ ring | rewrite IHi; ring ]. Qed.

Lemma z2pow_mul x y i : z2pow (x * y) i = z2pow x i * z2pow y i.
Proof. induction i; simpl; [ ring | rewrite IHi; ring ]. Qed.

Lemma z2pow_2 x i : z2pow x (2 * i) = z2pow x i * z2pow x i.
Proof. replace (2 * i)%nat with (i + i)%nat by lia; apply z2pow_add. Qed.

Lemma z2conj_mul x y : z2conj (x * y) = z2conj x * z2conj y.
Proof. z2_destr; apply Z2_ext; ring. Qed.

Lemma z2conj_inv x : z2conj (z2conj x) = x.
Proof. z2_destr; apply Z2_ext; ring. Qed.

Lemma z2N_mul x y : z2N (x * y) = (z2N x * z2N y)%Z.
Proof. z2_destr; ring. Qed.

Lemma z2N_conj x : z2N (z2conj x) = z2N x.
Proof. z2_destr; ring. Qed.

Lemma z2_mul_conj x : x * z2conj x = z2of (z2N x).
Proof. z2_destr; apply Z2_ext; ring. Qed.

Lemma z2of_mul a b : z2of (a * b) = z2of a * z2of b.
Proof. unfold z2of, z2mul; cbn [re im]; apply Z2_ext; ring. Qed.

Lemma z2N_of a : z2N (z2of a) = (a * a)%Z.
Proof. unfold z2N, z2of; cbn [re im]; ring. Qed.

Lemma z2N_pow x i : z2N (z2pow x i) = Z.pow (z2N x) (Z.of_nat i).
Proof.
  induction i; [ reflexivity | ].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; simpl; rewrite z2N_mul, IHi; ring.
Qed.

(** sqrt2 is irrational *)

Lemma sqrt2_irr_aux (n : nat) : forall a b : Z,
  (Z.abs_nat a < n)%nat -> (a * a = 2 * (b * b))%Z -> a = 0%Z.
Proof.
  induction n as [ | n IH ]; intros a b Hn H; [ lia | ].
  destruct (Z.eq_dec a 0) as [ | Ha ]; [ assumption | exfalso ].
  destruct (Z.Even_or_Odd a) as [ [ c Hc ] | [ c Hc ] ]; subst a.
  - assert (Hb : (b * b = 2 * (c * c))%Z) by nia.
    assert (Hlt : (Z.abs b < Z.abs (2 * c))%Z) by nia.
    assert (E : b = 0%Z) by (apply (IH b c); [ lia | exact Hb ]).
    subst b; nia.
  - assert (E : (2 * (2 * c * c + 2 * c - b * b) = -1)%Z) by nia. lia.
Qed.

Lemma sqrt2_irr_Z (a b : Z) : (a * a = 2 * (b * b))%Z -> a = 0%Z /\ b = 0%Z.
Proof.
  intros H; assert (Ha : a = 0%Z) by (apply (sqrt2_irr_aux (S (Z.abs_nat a)) a b); [ lia | exact H ]).
  subst a; split; [ reflexivity | nia ].
Qed.

Lemma z2N_eq0 x : z2N x = 0%Z -> x = z20.
Proof.
  destruct x as [ a b ]; unfold z2N; cbn [re im]; intros H.
  destruct (sqrt2_irr_Z a b) as [ -> -> ]; [ lia | reflexivity ].
Qed.

Lemma z2N_neq0 x : x <> z20 -> z2N x <> 0%Z.
Proof. intros H E; apply H, z2N_eq0, E. Qed.

Lemma z2_integral x y : x * y = z20 -> x = z20 \/ y = z20.
Proof.
  intros H; assert (E : (z2N x * z2N y = 0)%Z) by (rewrite <- z2N_mul, H; reflexivity).
  apply Z.mul_eq_0 in E; destruct E; [ left | right ]; apply z2N_eq0; assumption.
Qed.

Lemma z2_mul_neq0 x y : x <> z20 -> y <> z20 -> x * y <> z20.
Proof. intros Hx Hy H; destruct (z2_integral _ _ H); auto. Qed.

Lemma z2_cancel a b c : a <> z20 -> a * b = a * c -> b = c.
Proof.
  intros Ha H.
  assert (E : a * (b - c) = z20) by
     (transitivity (a * b - a * c); [ ring | rewrite H; ring ]).
  destruct (z2_integral _ _ E) as [ | E' ]; [ contradiction | ].
  transitivity (c + (b - c)); [ ring | rewrite E'; ring ].
Qed.

Lemma z21_neq0 : z21 <> z20.
Proof. discriminate. Qed.

(** ** Units *)

Definition z2unit (u : Z2) : Prop := exists v, u * v = z21.

Lemma z2unit_norm u : z2unit u <-> (z2N u = 1 \/ z2N u = -1)%Z.
Proof.
  split.
  - intros [ v Hv ]; assert (E : (z2N u * z2N v = 1)%Z) by (rewrite <- z2N_mul, Hv; reflexivity).
    destruct (Z.mul_eq_1 _ _ E); [ left | right ]; assumption.
  - intros [ E | E ].
    + exists (z2conj u); rewrite z2_mul_conj, E; reflexivity.
    + exists (z2opp (z2conj u)).
      transitivity (z2opp (u * z2conj u)); [ ring | rewrite z2_mul_conj, E; reflexivity ].
Qed.

Lemma z2unit_neq0 u : z2unit u -> u <> z20.
Proof. intros [ v Hv ] ->; discriminate Hv. Qed.

Lemma z2unit_mul u v : z2unit u -> z2unit v -> z2unit (u * v).
Proof.
  intros [ u' Hu ] [ v' Hv ]; exists (u' * v').
  transitivity ((u * u') * (v * v')); [ ring | rewrite Hu, Hv; ring ].
Qed.

Lemma z2unit_mul_inv u v : z2unit (u * v) -> z2unit u.
Proof. intros [ w Hw ]; exists (v * w); rewrite <- Hw; ring. Qed.

Lemma z2unit_1 : z2unit z21.
Proof. exists z21; ring. Qed.

Lemma z2unit_opp u : z2unit u -> z2unit (- u).
Proof. intros [ v Hv ]; exists (- v); rewrite <- Hv; ring. Qed.

Lemma z2unit_pow u i : z2unit u -> z2unit (z2pow u i).
Proof. intros Hu; induction i; simpl; [ apply z2unit_1 | apply z2unit_mul; assumption ]. Qed.

Lemma z2unit_dec u : {z2unit u} + {~ z2unit u}.
Proof.
  destruct (Z.eq_dec (z2N u) 1) as [ E | E ]; [ left; apply z2unit_norm; auto | ].
  destruct (Z.eq_dec (z2N u) (-1)) as [ E' | E' ]; [ left; apply z2unit_norm; auto | ].
  right; rewrite z2unit_norm; intros [ | ]; contradiction.
Defined.

(** ** Divisibility *)

Definition z2dvd (a b : Z2) : Prop := exists c, b = a * c.

Lemma z2dvd_refl a : z2dvd a a.
Proof. exists z21; ring. Qed.

Lemma z2dvd_0 a : z2dvd a z20.
Proof. exists z20; ring. Qed.

Lemma z2dvd_mul_r a b c : z2dvd a b -> z2dvd a (b * c).
Proof. intros [ x -> ]; exists (x * c); ring. Qed.

Lemma z2dvd_mul_l a b c : z2dvd a c -> z2dvd a (b * c).
Proof. intros [ x -> ]; exists (b * x); ring. Qed.

Lemma z2dvd_trans a b c : z2dvd a b -> z2dvd b c -> z2dvd a c.
Proof. intros [ x -> ] [ y -> ]; exists (x * y); ring. Qed.

Lemma z2dvd_add a b c : z2dvd a b -> z2dvd a c -> z2dvd a (b + c).
Proof. intros [ x -> ] [ y -> ]; exists (x + y); ring. Qed.

Lemma z2dvd_sub a b c : z2dvd a b -> z2dvd a c -> z2dvd a (b - c).
Proof. intros [ x -> ] [ y -> ]; exists (x - y); ring. Qed.

Lemma z2dvd_unit a u : z2unit u -> z2dvd a u -> z2unit a.
Proof. intros [ v Hv ] [ x -> ]; exists (x * v); rewrite <- Hv; ring. Qed.

Lemma z2dvd_unit_l u b : z2unit u -> z2dvd u b.
Proof. intros [ v Hv ]; exists (v * b); transitivity ((u * v) * b); [ rewrite Hv; ring | ring ]. Qed.

Lemma z2dvd_norm a b : z2dvd a b -> Z.divide (z2N a) (z2N b).
Proof. intros [ c -> ]; exists (z2N c); rewrite z2N_mul; ring. Qed.

Lemma z2dvd_conj a b : z2dvd a b -> z2dvd (z2conj a) (z2conj b).
Proof. intros [ c -> ]; exists (z2conj c); apply z2conj_mul. Qed.

(* a | b iff N(a) divides both components of b * conj a *)
Lemma z2dvd_iff a b : a <> z20 -> (z2dvd a b <->
  (Z.divide (z2N a) (re (b * z2conj a)) /\ Z.divide (z2N a) (im (b * z2conj a)))).
Proof.
  intros Ha; split.
  - intros [ c -> ].
    replace (a * c * z2conj a) with (z2of (z2N a) * c)
      by (rewrite <- z2_mul_conj; ring).
    destruct c as [ c1 c2 ]; unfold z2of, z2mul; cbn [re im]; split.
    + exists c1; ring.
    + exists c2; ring.
  - intros [ [ c1 H1 ] [ c2 H2 ] ]; exists (Z2c c1 c2).
    assert (Hc : z2conj a <> z20) by
      (intros E; apply Ha; rewrite <- (z2conj_inv a), E; reflexivity).
    apply (z2_cancel (z2conj a)); [ exact Hc | ].
    transitivity (Z2c (re (b * z2conj a)) (im (b * z2conj a))); [ rewrite (Z2_rt.(Rmul_comm) (z2conj a) b); destruct (b * z2conj a); reflexivity | ].
    rewrite H1, H2.
    transitivity (a * z2conj a * Z2c c1 c2); [ | ring ].
    rewrite z2_mul_conj; unfold z2of, z2mul; cbn [re im]; apply Z2_ext; ring.
Qed.

Lemma Zdvd_dec (a b : Z) : {Z.divide a b} + {~ Z.divide a b}.
Proof.
  destruct (Z.eq_dec a 0) as [ -> | Ha ].
  - destruct (Z.eq_dec b 0) as [ -> | Hb ]; [ left; exists 0%Z; ring | right ].
    intros [ c -> ]; apply Hb; ring.
  - destruct (Z.eq_dec (b mod a) 0) as [ E | E ].
    + left; apply Z.mod_divide; assumption.
    + right; intros H; apply E, Z.mod_divide; assumption.
Defined.

Lemma z2dvd_dec a b : {z2dvd a b} + {~ z2dvd a b}.
Proof.
  destruct (Z2_eq_dec a z20) as [ -> | Ha ].
  - destruct (Z2_eq_dec b z20) as [ -> | Hb ]; [ left; apply z2dvd_0 | right ].
    intros [ c -> ]; apply Hb; ring.
  - destruct (Zdvd_dec (z2N a) (re (b * z2conj a))) as [ H1 | H1 ];
    [ destruct (Zdvd_dec (z2N a) (im (b * z2conj a))) as [ H2 | H2 ] | ].
    + left; apply z2dvd_iff; auto.
    + right; rewrite z2dvd_iff by exact Ha; intros [ _ ? ]; contradiction.
    + right; rewrite z2dvd_iff by exact Ha; intros [ ? _ ]; contradiction.
Defined.

Lemma z2dvd_0_inv b : z2dvd z20 b -> b = z20.
Proof. intros [ c -> ]; ring. Qed.

(* divisibility up to a unit: if a | b and |N a| = |N b|, b <> 0, then b = a * unit *)
Lemma z2dvd_same_norm a b : b <> z20 -> z2dvd a b -> Z.abs (z2N a) = Z.abs (z2N b) ->
  exists e, z2unit e /\ b = a * e.
Proof.
  intros Hb [ e -> ] E; exists e; split; [ | reflexivity ].
  rewrite z2N_mul, Z.abs_mul in E.
  assert (Ha : z2N a <> 0%Z) by (intros E'; apply Hb; rewrite (z2N_eq0 _ E'); ring).
  apply z2unit_norm.
  assert (Z.abs (z2N e) = 1)%Z by nia. lia.
Qed.

(** * 2. Euclidean division and Bezout *)

Local Open Scope Z_scope.

Definition rq (g n : Z) : Z := (2 * g + n) / (2 * n).

Lemma rq_spec g n : n <> 0 -> Z.abs (2 * (g - rq g n * n)) <= Z.abs n.
Proof.
  intros Hn; unfold rq.
  assert (H2 : 2 * n <> 0) by lia.
  pose proof (Z.div_mod (2 * g + n) (2 * n) H2) as E.
  destruct (Z_lt_le_dec 0 n) as [ Hp | Hp ].
  - pose proof (Z.mod_pos_bound (2 * g + n) (2 * n) ltac:(lia)).
    revert E H; generalize ((2 * g + n) / (2 * n)) ((2 * g + n) mod (2 * n)); intros; lia.
  - pose proof (Z.mod_neg_bound (2 * g + n) (2 * n) ltac:(lia)).
    revert E H; generalize ((2 * g + n) / (2 * n)) ((2 * g + n) mod (2 * n)); intros; lia.
Qed.

Local Open Scope z2_scope.

Lemma z2_euclid a b : b <> z20 -> exists q r, a = q * b + r /\ (Z.abs (z2N r) < Z.abs (z2N b))%Z.
Proof.
  intros Hb.
  set (n := z2N b). assert (Hn : n <> 0%Z) by (apply z2N_neq0; exact Hb).
  set (g := a * z2conj b).
  set (q := Z2c (rq (re g) n) (rq (im g) n)).
  exists q, (a - q * b); split; [ ring | ].
  pose proof (rq_spec (re g) n Hn) as H1; pose proof (rq_spec (im g) n Hn) as H2.
  set (e1 := (re g - rq (re g) n * n)%Z) in *; set (e2 := (im g - rq (im g) n * n)%Z) in *.
  assert (E : (z2N (a - q * b) * n = e1 * e1 - 2 * (e2 * e2))%Z).
  { unfold e1, e2, q, n, g; generalize (rq (re (a * z2conj b)) (z2N b)) (rq (im (a * z2conj b)) (z2N b)).
    intros q1 q2; destruct a, b; unfold z2N, z2sub, z2add, z2opp, z2mul, z2conj; cbn [re im]; ring. }
  assert (F1 : (4 * (e1 * e1) <= n * n)%Z) by nia.
  assert (F2 : (4 * (e2 * e2) <= n * n)%Z) by nia.
  assert (F : (2 * Z.abs (e1 * e1 - 2 * (e2 * e2)) <= n * n)%Z) by nia.
  rewrite <- E, Z.abs_mul in F.
  assert (0 < Z.abs n)%Z by lia.
  assert (n * n = Z.abs n * Z.abs n)%Z by nia.
  nia.
Qed.

(* the gcd as a linear combination *)
Lemma z2_bezout a b : exists g s t, g = s * a + t * b /\ z2dvd g a /\ z2dvd g b.
Proof.
  remember (Z.abs_nat (z2N b)) as n eqn:En.
  revert a b En; induction n as [ n IH ] using (well_founded_induction lt_wf); intros a b En.
  destruct (Z2_eq_dec b z20) as [ -> | Hb ].
  - exists a, z21, z20; split; [ ring | split; [ apply z2dvd_refl | apply z2dvd_0 ] ].
  - destruct (z2_euclid a b Hb) as [ q [ r [ Er Hr ] ] ].
    destruct (IH (Z.abs_nat (z2N r)) ltac:(lia) b r eq_refl) as [ g [ s [ t [ Eg [ Gb Gr ] ] ] ] ].
    exists g, t, (s - t * q); split; [ rewrite Eg, Er; ring | split; [ | exact Gb ] ].
    rewrite Er; apply z2dvd_add; [ apply z2dvd_mul_l; exact Gb | exact Gr ].
Qed.

(** * 3. Rational integers: bounded search, prime divisors *)

Lemma bsearch (P : Z -> Prop) (dec : forall r, {P r} + {~ P r}) (n : nat) :
  {r | (0 <= r < Z.of_nat n)%Z /\ P r} + {forall r, (0 <= r < Z.of_nat n)%Z -> ~ P r}.
Proof.
  induction n as [ | n IH ].
  - right; intros r Hr; lia.
  - destruct IH as [ [ r [ Hr Pr ] ] | H ]; [ left; exists r; split; [ lia | exact Pr ] | ].
    destruct (dec (Z.of_nat n)) as [ Pn | Pn ]; [ left; exists (Z.of_nat n); split; [ lia | exact Pn ] | ].
    right; intros r Hr; destruct (Z.eq_dec r (Z.of_nat n)) as [ -> | Hne ]; [ exact Pn | apply H; lia ].
Defined.

Local Open Scope Z_scope.

Lemma Z_prime_divisor (n : Z) : 1 < n -> exists p, Z.prime p /\ (p | n).
Proof.
  remember (Z.to_nat n) as k eqn:Ek; revert n Ek.
  induction k as [ k IH ] using (well_founded_induction lt_wf); intros n Ek Hn.
  destruct (bsearch (fun m => 1 < m /\ (m | n))
              (fun m => match Z_lt_dec 1 m, Zdvd_dec m n with
                        | left h1, left h2 => left (conj h1 h2)
                        | right h1, _ => right (fun h => h1 (proj1 h))
                        | _, right h2 => right (fun h => h2 (proj2 h)) end)
              (Z.to_nat n)) as [ [ m [ Hm [ Hm1 Hmn ] ] ] | H ].
  - destruct (IH (Z.to_nat m) ltac:(lia) m eq_refl Hm1) as [ p [ Hp Hpm ] ].
    exists p; split; [ exact Hp | eapply Z.divide_trans; eassumption ].
  - exists n; split; [ | apply Z.divide_refl ].
    split; [ exact Hn | intros m Hm Hd; apply (H m); [ lia | split; [ lia | exact Hd ] ] ].
Qed.

Lemma Z_prime_divisors_sq (p d : Z) : Z.prime p -> 0 <= d -> (d | p * p) -> d = 1 \/ d = p \/ d = p * p.
Proof.
  intros Hp Hd H; pose proof (Z.prime_ge_2 _ Hp).
  destruct (Zdvd_dec p d) as [ [ d' -> ] | Hn ].
  - assert (H' : (d' | p)).
    { destruct H as [ k Hk ]; exists k; nia. }
    destruct (Z.divide_prime_r _ _ Hp H') as [ E | [ E | [ E | E ] ] ]; subst d'; nia.
  - assert (Hc : Z.coprime p d) by (apply Z.coprime_prime_l; assumption).
    assert (H' : (d | p)).
    { apply (Z.gauss d p p); [ exact H | ].
      unfold Z.coprime in *; rewrite Z.gcd_comm; exact Hc. }
    destruct (Z.divide_prime_r _ _ Hp H') as [ E | [ E | [ E | E ] ] ]; subst d; try lia; try (left; reflexivity).
    all: exfalso; apply Hn; try apply Z.divide_refl; apply Z.divide_opp_r, Z.divide_refl.
Qed.

Local Open Scope z2_scope.

(** * 4. Prime elements *)

Definition z2prime (p : Z2) : Prop :=
  p <> z20 /\ ~ z2unit p /\ forall a b, z2dvd p (a * b) -> z2dvd p a \/ z2dvd p b.

Lemma z2prime_neq0 p : z2prime p -> p <> z20. Proof. intros [ H _ ]; exact H. Qed.
Lemma z2prime_nunit p : z2prime p -> ~ z2unit p. Proof. intros [ _ [ H _ ] ]; exact H. Qed.
Arguments z2prime_neq0 {p}. Arguments z2prime_nunit {p}.

Lemma z2prime_mul p a b : z2prime p -> ~ z2dvd p a -> ~ z2dvd p b -> ~ z2dvd p (a * b).
Proof. intros [ _ [ _ H ] ] Ha Hb Hab; destruct (H _ _ Hab); contradiction. Qed.

Lemma z2prime_pow p a i : z2prime p -> ~ z2dvd p a -> ~ z2dvd p (z2pow a i).
Proof.
  intros Hp Ha; induction i; simpl.
  - intros H; apply (z2prime_nunit Hp); eapply z2dvd_unit; [ apply z2unit_1 | exact H ].
  - apply z2prime_mul; assumption.
Qed.

Lemma z2prime_norm_ge2 p : z2prime p -> (2 <= Z.abs (z2N p))%Z.
Proof.
  intros Hp; pose proof (z2N_neq0 _ (z2prime_neq0 Hp)).
  assert (z2N p <> 1 /\ z2N p <> -1)%Z as [ ].
  { split; intros E; apply (z2prime_nunit Hp), z2unit_norm; auto. }
  lia.
Qed.

Lemma z2_unit_of_norm1 g : Z.abs (z2N g) = 1%Z -> z2unit g.
Proof. intros E; apply z2unit_norm; lia. Qed.

(* an element of prime norm is prime *)
Lemma z2prime_of_norm p : Z.prime (Z.abs (z2N p)) -> z2prime p.
Proof.
  intros Hp; pose proof (Z.prime_ge_2 _ Hp).
  split; [ intros -> ; cbn in H; lia | split ].
  - intros Hu%z2unit_norm; lia.
  - intros a b Hab.
    destruct (z2_bezout p a) as [ g [ s [ t [ Eg [ [ h Eh ] Ga ] ] ] ] ].
    assert (Hd : (Z.abs (z2N g) | Z.abs (z2N p))).
    { apply Z.divide_abs_l, Z.divide_abs_r, z2dvd_norm; exists h; exact Eh. }
    destruct (Z.divide_prime_r _ _ Hp Hd) as [ E | [ E | [ E | E ] ] ]; try lia.
    + (* g is a unit: p | b *)
      right; destruct (z2_unit_of_norm1 _ E) as [ gi Hgi ].
      destruct Hab as [ c Hc ].
      exists (gi * (s * b + t * c)).
      transitivity ((g * gi) * b); [ rewrite Hgi; ring | ].
      rewrite Eg at 1.
      transitivity (gi * (s * p * b + t * (a * b))); [ ring | rewrite Hc; ring ].
    + (* g is associate to p: p | a *)
      left; assert (Hg0 : z2N g <> 0%Z) by lia.
      rewrite Eh, z2N_mul, Z.abs_mul in E.
      assert (Z.abs (z2N h) = 1)%Z by nia.
      destruct (z2_unit_of_norm1 _ H0) as [ hi Hhi ].
      eapply z2dvd_trans; [ | exact Ga ].
      exists hi; rewrite Eh; transitivity (g * (h * hi)); [ rewrite Hhi; ring | ring ].
Qed.

Lemma z2dvd_of_iff (p : Z) (z : Z2) : z2dvd (z2of p) z <-> ((p | re z) /\ (p | im z))%Z.
Proof.
  split.
  - intros [ c -> ]; unfold z2of, z2mul; cbn [re im]; split; [ exists (re c) | exists (im c) ]; ring.
  - intros [ [ c1 H1 ] [ c2 H2 ] ]; exists (Z2c c1 c2); destruct z as [ z1 z2 ]; cbn [re im] in *.
    unfold z2of, z2mul; cbn [re im]; apply Z2_ext; [ rewrite H1 | rewrite H2 ]; ring.
Qed.

(* p | N(a) implies (p) | a, for p without square root of 2 *)
Lemma inert_dvd (p : Z) (a : Z2) : Z.prime p -> (forall r, ~ (p | r * r - 2))%Z ->
  (p | z2N a)%Z -> z2dvd (z2of p) a.
Proof.
  intros Hp Hr H; apply z2dvd_of_iff; destruct a as [ a1 a2 ]; unfold z2N in H; cbn [re im] in *.
  destruct (Zdvd_dec p a2) as [ H2 | H2 ].
  - split; [ | exact H2 ].
    assert (H1 : (p | a1 * a1)%Z).
    { destruct H as [ k Hk ]; destruct H2 as [ l Hl ]; exists (k + 2 * l * l * p)%Z; nia. }
    apply Z.divide_prime_mul in H1; [ | exact Hp ]; destruct H1; assumption.
  - exfalso.
    destruct (Z.Bezout_coprime p a2 (Z.coprime_prime_l _ _ Hp H2)) as [ v [ u Huv ] ].
    apply (Hr (a1 * u)%Z).
    destruct H as [ k Hk ].
    exists (k * u * u + 2 * v * v * p - 4 * v)%Z.
    assert (u * a2 = 1 - v * p)%Z as E by lia.
    replace ((a1 * u) * (a1 * u) - 2)%Z with ((a1 * a1 - 2 * (a2 * a2)) * (u * u) + 2 * ((u * a2) * (u * a2)) - 2)%Z by ring.
    rewrite Hk, E; ring.
Qed.

Lemma z2prime_inert (p : Z) : Z.prime p -> (forall r, ~ (p | r * r - 2))%Z -> z2prime (z2of p).
Proof.
  intros Hp Hr; pose proof (Z.prime_ge_2 _ Hp).
  split; [ intros E; injection E; lia | split ].
  - intros Hu%z2unit_norm; rewrite z2N_of in Hu; nia.
  - intros a b Hab.
    apply z2dvd_norm in Hab; rewrite z2N_of, z2N_mul in Hab.
    assert (Hpd : (p | z2N a * z2N b)%Z) by (eapply Z.divide_trans; [ exists p; reflexivity | exact Hab ]).
    apply Z.divide_prime_mul in Hpd; [ | exact Hp ].
    destruct Hpd; [ left | right ]; apply inert_dvd; assumption.
Qed.

Definition z2sqrt2 : Z2 := Z2c 0 1.

Lemma z2prime_sqrt2 : z2prime z2sqrt2.
Proof. apply z2prime_of_norm; exact Z.prime_2. Qed.

Lemma z2dvd_conj_iff a b : z2dvd (z2conj a) b <-> z2dvd a (z2conj b).
Proof.
  split; intros H.
  - apply z2dvd_conj in H; rewrite z2conj_inv in H; exact H.
  - apply z2dvd_conj in H; rewrite z2conj_inv in H; exact H.
Qed.

Lemma z2prime_conj q : z2prime q -> z2prime (z2conj q).
Proof.
  intros [ Hq0 [ Hqu Hqm ] ]; split; [ | split ].
  - intros E; apply Hq0; rewrite <- (z2conj_inv q), E; reflexivity.
  - intros Hu%z2unit_norm; rewrite z2N_conj in Hu; apply Hqu, z2unit_norm; exact Hu.
  - intros a b H; apply z2dvd_conj_iff in H; rewrite z2conj_mul in H.
    destruct (Hqm _ _ H); [ left | right ]; apply z2dvd_conj_iff; assumption.
Qed.

(* every nonzero nonunit has a prime divisor *)
Lemma z2_prime_divisor x : x <> z20 -> ~ z2unit x -> exists q, z2prime q /\ z2dvd q x.
Proof.
  intros Hx Hu.
  assert (Hn : (1 < Z.abs (z2N x))%Z).
  { pose proof (z2N_neq0 _ Hx).
    assert (z2N x <> 1 /\ z2N x <> -1)%Z as [ ] by (split; intros E; apply Hu, z2unit_norm; auto).
    lia. }
  destruct (Z_prime_divisor _ Hn) as [ p [ Hp Hpx ] ].
  pose proof (Z.prime_ge_2 _ Hp).
  rewrite Z.divide_abs_r in Hpx.
  (* p divides x * conj x *)
  assert (Hpxx : z2dvd (z2of p) (x * z2conj x)).
  { destruct Hpx as [ k Hk ]; exists (z2of k); rewrite z2_mul_conj, Hk, z2of_mul; ring. }
  (* from a prime divisor q of (p), get a prime divisor of x *)
  assert (Hfrom : forall q, z2prime q -> z2dvd q (z2of p) -> exists q', z2prime q' /\ z2dvd q' x).
  { intros q Hq Hqp; destruct Hq as [ Hq0 [ Hqu Hqm ] ].
    destruct (Hqm x (z2conj x) (z2dvd_trans _ _ _ Hqp Hpxx)) as [ H1 | H1 ].
    - exists q; split; [ split; auto | exact H1 ].
    - exists (z2conj q); split; [ | apply z2dvd_conj_iff; exact H1 ].
      apply z2prime_conj; split; auto. }
  assert (Hp0 : p <> 0%Z) by lia.
  destruct (bsearch (fun r => (p | r * r - 2)%Z) (fun r => Zdvd_dec p (r * r - 2)) (Z.to_nat p))
    as [ [ r [ Hr Hpr ] ] | Hin ].
  - (* p splits: gcd (r + sqrt2, p) is a prime of norm +-p *)
    set (beta := Z2c r 1).
    destruct (z2_bezout beta (z2of p)) as [ g [ s [ t [ Eg [ Gb Gp ] ] ] ] ].
    assert (Hg : (Z.abs (z2N g) | p * p)%Z).
    { apply Z.divide_abs_l; rewrite <- z2N_of; apply z2dvd_norm; exact Gp. }
    destruct (Z_prime_divisors_sq p _ Hp (Z.abs_nonneg _) Hg) as [ E | [ E | E ] ].
    + exfalso; destruct (z2_unit_of_norm1 _ E) as [ gi Hgi ].
      assert (Hc : z2dvd (z2of p) (z2conj beta)).
      { destruct Hpr as [ k Hk ].
        exists (gi * (s * z2of k + t * z2conj beta)).
        transitivity ((g * gi) * z2conj beta); [ rewrite Hgi; ring | ].
        rewrite Eg.
        transitivity (gi * (s * (beta * z2conj beta) + t * z2of p * z2conj beta)); [ ring | ].
        assert (HN : z2N beta = (r * r - 2)%Z) by (unfold beta, z2N; cbn [re im]; ring).
        rewrite z2_mul_conj, HN, Hk, z2of_mul; ring. }
      apply z2dvd_of_iff in Hc; destruct Hc as [ _ Hc ]; cbn in Hc.
      apply Z.divide_opp_r in Hc; apply Z.divide_1_r in Hc; lia.
    + destruct (Hfrom g); [ | exact Gp | eauto ].
      apply z2prime_of_norm; rewrite E; exact Hp.
    + exfalso.
      destruct (z2dvd_same_norm g (z2of p)) as [ e [ He Ee ] ];
        [ intros Ep; injection Ep; lia | exact Gp | rewrite z2N_of, E; nia | ].
      destruct He as [ ei Hei ].
      assert (Hb : z2dvd (z2of p) beta).
      { eapply z2dvd_trans; [ | exact Gb ]. exists ei; rewrite Ee.
        transitivity (g * (e * ei)); [ rewrite Hei; ring | ring ]. }
      apply z2dvd_of_iff in Hb; destruct Hb as [ _ Hb ]; cbn in Hb.
      apply Z.divide_1_r in Hb; lia.
  - (* p is inert *)
    assert (Hin' : forall r, ~ (p | r * r - 2)%Z).
    { intros r Hd; apply (Hin (r mod p)%Z).
      - pose proof (Z.mod_pos_bound r p ltac:(lia)); lia.
      - pose proof (Z.div_mod r p Hp0) as Er.
        destruct Hd as [ k Hk ]; exists (k - 2 * (r / p) * (r mod p) - p * (r / p) * (r / p))%Z.
        rewrite Er in Hk at 1 2; nia. }
    apply (Hfrom (z2of p)); [ apply z2prime_inert; assumption | apply z2dvd_refl ].
Qed.

Lemma z2prime_assoc q q' : z2prime q -> z2prime q' -> z2dvd q' q -> z2dvd q q'.
Proof.
  intros Hq Hq' [ f Ef ].
  destruct Hq as [ Hq0 [ Hqu Hqm ] ].
  destruct (Hqm q' f) as [ H | [ g Eg ] ]; [ rewrite <- Ef; apply z2dvd_refl | exact H | ].
  exfalso; apply (z2prime_nunit Hq'); exists g.
  apply (z2_cancel q); [ exact Hq0 | ].
  transitivity (q' * (q * g)); [ ring | rewrite <- Eg, <- Ef; ring ].
Qed.

(** * 5. Exact powers of a prime *)

Lemma abs_nat_mul_lt (a b : Z) : (2 <= Z.abs a)%Z -> b <> 0%Z -> (Z.abs_nat b < Z.abs_nat (a * b))%nat.
Proof. intros Ha Hb; rewrite Zabs2Nat.inj_mul; nia. Qed.

Lemma abs_nat_mul_le (a b : Z) : a <> 0%Z -> (Z.abs_nat b <= Z.abs_nat (a * b))%nat.
Proof. intros Ha; rewrite Zabs2Nat.inj_mul; nia. Qed.

Lemma z2pow_neq0 q i : q <> z20 -> z2pow q i <> z20.
Proof. intros Hq; induction i; simpl; [ discriminate | apply z2_mul_neq0; assumption ]. Qed.

Lemma z2_val q X : z2prime q -> X <> z20 -> exists i X', X = z2pow q i * X' /\ ~ z2dvd q X'.
Proof.
  intros Hq; remember (Z.abs_nat (z2N X)) as n eqn:En; revert X En.
  induction n as [ n IH ] using (well_founded_induction lt_wf); intros X En HX.
  destruct (z2dvd_dec q X) as [ [ Y EY ] | H ].
  - assert (HY : Y <> z20) by (intros ->; apply HX; rewrite EY; ring).
    pose proof (z2prime_norm_ge2 _ Hq). pose proof (z2N_neq0 _ HY).
    assert (Hlt : (Z.abs_nat (z2N Y) < n)%nat).
    { subst n X; rewrite z2N_mul; apply abs_nat_mul_lt; assumption. }
    destruct (IH _ Hlt Y eq_refl HY) as [ i [ X' [ E HX' ] ] ].
    exists (S i), X'; split; [ rewrite EY, E; simpl; ring | exact HX' ].
  - exists O, X; split; [ simpl; ring | exact H ].
Qed.

Definition evenval (q X : Z2) : Prop :=
  forall i X', X = z2pow q i * X' -> ~ z2dvd q X' -> Nat.Even i.

(** * 6. The unit group: every unit is +-(1+sqrt2)^e w^2 *)

Definition z2eps : Z2 := Z2c 1 1.
Definition z2epsi : Z2 := Z2c (-1) 1.

Lemma z2eps_inv : z2eps * z2epsi = z21.
Proof. reflexivity. Qed.

Lemma z2unit_eps : z2unit z2eps. Proof. exists z2epsi; reflexivity. Qed.
Lemma z2unit_epsi : z2unit z2epsi. Proof. exists z2eps; reflexivity. Qed.

Definition z2sg (s : bool) : Z2 := if s then z2opp z21 else z21.
Definition z2ep (e : bool) : Z2 := if e then z2eps else z21.

Lemma unit_class u : z2unit u ->
  exists s e w, z2unit w /\ u = z2sg s * z2ep e * (w * w).
Proof.
  intros Hu; remember (Z.abs_nat (im u)) as n eqn:En; revert u En Hu.
  induction n as [ n IH ] using (well_founded_induction lt_wf); intros [ a b ] En Hu.
  pose proof (proj1 (z2unit_norm _) Hu) as HN; unfold z2N in HN; cbn [re im] in HN, En.
  destruct (Z.eq_dec b 0) as [ -> | Hb ].
  - assert (a = 1 \/ a = -1)%Z as [ -> | -> ] by nia.
    + exists false, false, z21; split; [ apply z2unit_1 | reflexivity ].
    + exists true, false, z21; split; [ apply z2unit_1 | reflexivity ].
  - assert (Ha : a <> 0%Z) by nia.
    destruct (Z_lt_le_dec 0 (a * b)) as [ Hab | Hab ].
    + (* multiply by eps^-1 *)
      assert (Hlt : (Z.abs_nat (a - b) < n)%nat).
      { subst n; destruct (Z_lt_le_dec 0 b).
        - assert (0 < a)%Z by nia. assert (b <= a)%Z by nia. assert (a < 2 * b)%Z by nia. lia.
        - assert (a < 0)%Z by nia. assert (a <= b)%Z by nia. assert (2 * b < a)%Z by nia. lia. }
      destruct (IH _ Hlt (Z2c a b * z2epsi)) as [ s [ e [ w [ Hw E ] ] ] ];
        [ unfold z2mul, z2epsi, z2eps; cbn [re im]; f_equal; ring | apply z2unit_mul; [ exact Hu | apply z2unit_epsi ] | ].
      assert (Eu : Z2c a b = z2sg s * z2ep e * (w * w) * z2eps).
      { rewrite <- E; transitivity (Z2c a b * (z2eps * z2epsi)); [ rewrite z2eps_inv; ring | ring ]. }
      destruct e.
      * exists s, false, (z2eps * w); split; [ apply z2unit_mul; [ apply z2unit_eps | exact Hw ] | ].
        rewrite Eu; unfold z2ep; ring.
      * exists s, true, w; split; [ exact Hw | rewrite Eu; unfold z2ep; ring ].
    + (* multiply by eps *)
      assert (Hab' : (a * b < 0)%Z) by nia.
      assert (Hlt : (Z.abs_nat (a + b) < n)%nat).
      { subst n; destruct (Z_lt_le_dec 0 b).
        - assert (a < 0)%Z by nia. assert (a <= - b)%Z by nia. assert (- 2 * b < a)%Z by nia. lia.
        - assert (0 < a)%Z by nia. assert (- b <= a)%Z by nia. assert (a < - 2 * b)%Z by nia. lia. }
      destruct (IH _ Hlt (Z2c a b * z2eps)) as [ s [ e [ w [ Hw E ] ] ] ];
        [ unfold z2mul, z2epsi, z2eps; cbn [re im]; f_equal; ring | apply z2unit_mul; [ exact Hu | apply z2unit_eps ] | ].
      assert (Eu : Z2c a b = z2sg s * z2ep e * (w * w) * z2epsi).
      { rewrite <- E; transitivity (Z2c a b * (z2eps * z2epsi)); [ rewrite z2eps_inv; ring | ring ]. }
      destruct e.
      * exists s, false, w; split; [ exact Hw | ].
        rewrite Eu; unfold z2ep; transitivity (z2sg s * (w * w) * (z2eps * z2epsi)); [ ring | rewrite z2eps_inv; ring ].
      * exists s, true, (z2epsi * w); split; [ apply z2unit_mul; [ apply z2unit_epsi | exact Hw ] | ].
        rewrite Eu; unfold z2ep.
        transitivity (z2sg s * (w * w) * z2epsi * (z2eps * z2epsi)); [ rewrite z2eps_inv; ring | ring ].
Qed.

(** * 7. The factorization lemma *)

Lemma z2pow_S q i : z2pow q (S i) = q * z2pow q i. Proof. reflexivity. Qed.

Lemma z2dvd_pow_S q i X : z2dvd q (z2pow q (S i) * X).
Proof. exists (z2pow q i * X); simpl; ring. Qed.

Theorem factor_even (D : Z2) (allow : bool) : z2prime D -> forall X, X <> z20 ->
  (forall q, z2prime q -> (allow = true -> ~ z2dvd q D) -> evenval q X) ->
  exists e j S, z2unit e /\ X = e * z2pow D j * (S * S) /\ (allow = false -> j = O).
Proof.
  intros HD X; remember (Z.abs_nat (z2N X)) as n eqn:En; revert X En.
  induction n as [ n IH ] using (well_founded_induction lt_wf); intros X En HX Hev.
  destruct (z2unit_dec X) as [ Hu | Hu ].
  { exists X, O, z21; split; [ exact Hu | split; [ simpl; ring | reflexivity ] ]. }
  destruct (z2_prime_divisor X HX Hu) as [ q [ Hq Hqx ] ].
  assert (Hok : {allow = false \/ ~ z2dvd q D} + {allow = true /\ z2dvd q D}).
  { destruct allow; [ | left; left; reflexivity ].
    destruct (z2dvd_dec q D); [ right; split; auto | left; right; assumption ]. }
  destruct Hok as [ Hok | [ Hal HqD ] ].
  - destruct (z2_val q X Hq HX) as [ i [ X' [ EX Hq' ] ] ].
    assert (Hi : Nat.Even i).
    { apply (Hev q Hq) with X'; [ | exact EX | exact Hq' ].
      intros Ha; destruct Hok as [ Hok | Hok ]; [ congruence | exact Hok ]. }
    destruct i as [ | i' ].
    { exfalso; apply Hq'; rewrite EX in Hqx; simpl in Hqx.
      replace (z21 * X') with X' in Hqx by ring; exact Hqx. }
    destruct Hi as [ m Hm ].
    assert (HX' : X' <> z20) by (intros ->; apply HX; rewrite EX; ring).
    pose proof (z2prime_norm_ge2 _ Hq). pose proof (z2N_neq0 _ HX').
    assert (Hlt : (Z.abs_nat (z2N X') < n)%nat).
    { subst n; rewrite EX, z2pow_S, <- Z2_rt.(Rmul_assoc), z2N_mul.
      eapply Nat.le_lt_trans; [ | apply abs_nat_mul_lt; [ eassumption | ] ].
      - rewrite z2N_mul; apply abs_nat_mul_le, z2N_neq0, z2pow_neq0, (z2prime_neq0 Hq).
      - rewrite z2N_mul; apply Z.neq_mul_0; split; [ | assumption ].
        apply z2N_neq0, z2pow_neq0, (z2prime_neq0 Hq). }
    destruct (IH _ Hlt X' eq_refl HX') as [ e [ j [ T [ He [ E Hj ] ] ] ] ].
    + intros q' Hq'p Hal' k X'' EX' Hq''.
      destruct (z2dvd_dec q' q) as [ Hqq | Hqq ].
      * destruct k as [ | k ]; [ exists O; reflexivity | ].
        exfalso; apply Hq'.
        apply z2dvd_trans with q'; [ apply (z2prime_assoc q q' Hq Hq'p Hqq) | ].
        rewrite EX'; apply z2dvd_pow_S.
      * apply (Hev q' Hq'p Hal' k (z2pow q (S i') * X'')).
        -- rewrite EX, EX'; ring.
        -- apply z2prime_mul; [ exact Hq'p | apply z2prime_pow; assumption | exact Hq'' ].
    + exists e, j, (z2pow q m * T); split; [ exact He | split; [ | exact Hj ] ].
      rewrite EX, E, Hm, z2pow_2; ring.
  - (* q divides D, so D divides X *)
    assert (HDq : z2dvd D q) by (apply z2prime_assoc; assumption).
    destruct (z2dvd_trans _ _ _ HDq Hqx) as [ Y EY ].
    assert (HY : Y <> z20) by (intros ->; apply HX; rewrite EY; ring).
    pose proof (z2prime_norm_ge2 _ HD). pose proof (z2N_neq0 _ HY).
    assert (Hlt : (Z.abs_nat (z2N Y) < n)%nat) by (subst n X; rewrite z2N_mul; apply abs_nat_mul_lt; assumption).
    destruct (IH _ Hlt Y eq_refl HY) as [ e [ j [ T [ He [ E Hj ] ] ] ] ].
    + intros q' Hq'p Hal' k Y'' EY' Hq''.
      apply (Hev q' Hq'p Hal' k (D * Y'')).
      * rewrite EY, EY'; ring.
      * apply z2prime_mul; [ exact Hq'p | apply Hal'; exact Hal | exact Hq'' ].
    + exists e, (S j), T; split; [ exact He | split; [ rewrite EY, E; simpl; ring | congruence ] ].
Qed.

(** * 8. The constants d = 75 - 53 sqrt2, its conjugate, sqrt2 *)

Definition z2d : Z2 := Z2c 75 (-53).

Lemma Z_prime_7 : Z.prime 7.
Proof.
  split; [ lia | ]; intros n Hn [ k Hk ].
  assert (n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6)%Z as H by lia.
  destruct H as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; lia.
Qed.

Lemma z2prime_d : z2prime z2d.
Proof. apply z2prime_of_norm; exact Z_prime_7. Qed.

(* the reduction map Z2 -> Z/7 with sqrt2 |-> 3 *)
Definition rho7 (z : Z2) : Z := (re z + 3 * im z)%Z.

Lemma rho7_mul a b : ((rho7 (a * b) - rho7 a * rho7 b) mod 7 = 0)%Z.
Proof.
  destruct a as [ a1 a2 ], b as [ b1 b2 ]; unfold rho7, z2mul; cbn [re im].
  replace (a1 * b1 + 2 * (a2 * b2) + 3 * (a1 * b2 + a2 * b1) - (a1 + 3 * a2) * (b1 + 3 * b2))%Z
    with ((- a2 * b2) * 7)%Z by ring.
  apply Z_mod_mult.
Qed.

Lemma z2dvd_d_iff z : z2dvd z2d z <-> (rho7 z mod 7 = 0)%Z.
Proof.
  rewrite z2dvd_iff by discriminate.
  destruct z as [ z1 z2 ]; unfold rho7, z2d, z2conj, z2N, z2mul; cbn [re im].
  replace (75 * 75 - 2 * (-53 * - 53))%Z with 7%Z by reflexivity.
  split.
  - intros [ [ k1 H1 ] [ k2 H2 ] ].
    replace (z1 + 3 * z2)%Z with ((- 12 * k1 + 17 * k2) * 7)%Z by lia.
    apply Z_mod_mult.
  - intros H; apply Z.mod_divide in H; [ | lia ]; destruct H as [ k Hk ].
    split; [ exists (75 * k - 17 * z2)%Z | exists (53 * k - 12 * z2)%Z ]; lia.
Qed.

Lemma Z_mod7_sqsum (s t : Z) : ((s * s + t * t) mod 7 = 0 -> s mod 7 = 0)%Z.
Proof.
  rewrite Z.add_mod, (Z.mul_mod s s), (Z.mul_mod t t) by lia.
  pose proof (Z.mod_pos_bound s 7 ltac:(lia)); pose proof (Z.mod_pos_bound t 7 ltac:(lia)).
  revert H H0; generalize (s mod 7)%Z (t mod 7)%Z; intros s' t' Hs Ht.
  assert (s' = 0 \/ s' = 1 \/ s' = 2 \/ s' = 3 \/ s' = 4 \/ s' = 5 \/ s' = 6)%Z as Es by lia.
  assert (t' = 0 \/ t' = 1 \/ t' = 2 \/ t' = 3 \/ t' = 4 \/ t' = 5 \/ t' = 6)%Z as Et by lia.
  destruct Es as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ];
  destruct Et as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ];
  vm_compute; congruence.
Qed.

(* -1 is not a square modulo d *)
Lemma d_sqsum a c : z2dvd z2d (a * a + c * c) -> z2dvd z2d a.
Proof.
  rewrite !z2dvd_d_iff; intros H.
  apply (Z_mod7_sqsum (rho7 a) (rho7 c)).
  pose proof (rho7_mul a a); pose proof (rho7_mul c c).
  assert (E : rho7 (a * a + c * c) = (rho7 (a * a) + rho7 (c * c))%Z)
    by (unfold rho7, z2add; cbn [re im]; ring).
  rewrite E in H.
  apply Z.mod_divide in H; [ | lia ]; apply Z.mod_divide in H0; [ | lia ];
    apply Z.mod_divide in H1; [ | lia ].
  apply Z.mod_divide; [ lia | ].
  destruct H as [ k1 ?], H0 as [ k2 ? ], H1 as [ k3 ? ]; exists (k1 - k2 - k3)%Z; lia.
Qed.

Lemma d_ndvd_2 : ~ z2dvd z2d (z2of 2).
Proof. rewrite z2dvd_d_iff; vm_compute; discriminate. Qed.

Lemma sqrt2_ndvd_d : ~ z2dvd z2sqrt2 z2d.
Proof.
  intros H%z2dvd_norm; unfold z2N, z2sqrt2, z2d in H; cbn [re im] in H; destruct H as [ k Hk ]; lia.
Qed.

(* a prime dividing d (resp. sqrt2) is d (resp. sqrt2) times a unit *)
Lemma prime_dvd_assoc q D : z2prime q -> z2prime D -> z2dvd q D -> exists f, z2unit f /\ D = q * f.
Proof.
  intros Hq HD [ f Ef ]; exists f; split; [ | exact Ef ].
  destruct (z2prime_assoc D q HD Hq) as [ g Eg ]; [ exists f; exact Ef | ].
  exists g; apply (z2_cancel q); [ apply (z2prime_neq0 Hq) | ].
  transitivity (q * f * g); [ ring | rewrite <- Ef, <- Eg; ring ].
Qed.

Lemma aE_z2 : Z2c (-11243) 7950 = z2opp (z2d * z2d).
Proof. reflexivity. Qed.

(* the Stdlib [ring] on Z2 and Z, under a name that survives MathComp's [ring] *)
Ltac z2ring := ring.

(** * 9. Small helpers for the descent *)

Lemma z2dvd_opp a b : z2dvd a (- b) -> z2dvd a b.
Proof. intros [ c Hc ]; exists (- c); transitivity (- (- b)); [ ring | rewrite Hc; ring ]. Qed.

Lemma z2prime_unit_ndvd q f : z2prime q -> z2unit f -> ~ z2dvd q f.
Proof. intros Hq Hf H; apply (z2prime_nunit Hq); exact (z2dvd_unit q f Hf H). Qed.

Lemma z2of2_sqrt2 : z2of 2 = z2sqrt2 * z2sqrt2.
Proof. reflexivity. Qed.

Lemma z2of4_sqrt2 : z2of 4 = z2pow z2sqrt2 4.
Proof. reflexivity. Qed.

Lemma z2prime_dvd_pow q a i : z2prime q -> z2dvd q (z2pow a i) -> z2dvd q a.
Proof.
  intros Hq; induction i as [ | i IH ]; simpl; intros H.
  - exfalso; apply (z2prime_nunit Hq); exact (z2dvd_unit q z21 z2unit_1 H).
  - destruct (proj2 (proj2 Hq) _ _ H); auto.
Qed.

Lemma z2dvd_assoc_r q D f z : D = q * f -> z2unit f -> z2dvd q z -> z2dvd D z.
Proof.
  intros -> [ fi Hfi ] [ g -> ]; exists (fi * g).
  transitivity (q * (f * fi) * g); [ rewrite Hfi; ring | ring ].
Qed.
