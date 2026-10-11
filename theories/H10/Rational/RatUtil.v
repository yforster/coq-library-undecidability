(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Elementary facts about MathComp's rational numbers used in
   the formalization of H10 over Q:
   - a hand-written ring morphism Z_to_rat : Z -> rat
   - sums of squares vanish only trivially
   - enumerability and discreteness of rat and of vectors.
   No result of the paper is formalized here; the facts are used in
   H10Q.v, H10Q_enum.v, PosExistential.v and the Section 7 reductions. *)

From Stdlib Require Import ZArith Lia.

From Undecidability.Synthetic
  Require Import Definitions DecidabilityFacts EnumerabilityFacts.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos vec.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

(** * The ring morphism Z -> rat *)

Definition Z_to_rat (z : Z) : rat :=
  (Z.to_nat z)%:R - (Z.to_nat (- z))%:R.

Local Lemma natr_add (m n : nat) : (Nat.add m n)%:R = m%:R + n%:R :> rat.
Proof. exact: natrD. Qed.

Local Lemma natr_mul (m n : nat) : (Nat.mul m n)%:R = m%:R * n%:R :> rat.
Proof. exact: natrM. Qed.

Local Lemma Z_to_rat_diff (m n : nat) :
  Z_to_rat (Z.of_nat m - Z.of_nat n)%ZZ = m%:R - n%:R.
Proof.
  unfold Z_to_rat.
  destruct (Nat.le_ge_cases m n) as [ H | H ].
  - destruct (Nat.le_exists_sub m n H) as (k & -> & _).
    replace (Z.to_nat (Z.of_nat m - Z.of_nat (Nat.add k m))%ZZ) with 0%nat by lia.
    replace (Z.to_nat (- (Z.of_nat m - Z.of_nat (Nat.add k m)))%ZZ) with k by lia.
    rewrite natr_add mulr0n sub0r.
    by rewrite opprD addrCA subrr addr0.
  - destruct (Nat.le_exists_sub n m H) as (k & -> & _).
    replace (Z.to_nat (Z.of_nat (Nat.add k n) - Z.of_nat n)%ZZ) with k by lia.
    replace (Z.to_nat (- (Z.of_nat (Nat.add k n) - Z.of_nat n))%ZZ) with 0%nat by lia.
    rewrite natr_add mulr0n subr0.
    by rewrite -addrA subrr addr0.
Qed.

Local Lemma Z_decomp (z : Z) :
  z = (Z.of_nat (Z.to_nat z) - Z.of_nat (Z.to_nat (- z)))%ZZ.
Proof. lia. Qed.

Lemma Z_to_rat_of_nat (n : nat) : Z_to_rat (Z.of_nat n) = n%:R.
Proof.
  rewrite -(subr0 (n%:R)).
  rewrite -(Z_to_rat_diff n 0); f_equal; lia.
Qed.

Lemma Z_to_rat_0 : Z_to_rat 0 = 0.
Proof. exact: (Z_to_rat_of_nat 0). Qed.

Lemma Z_to_rat_1 : Z_to_rat 1 = 1.
Proof. exact: (Z_to_rat_of_nat 1). Qed.

Lemma Z_to_rat_add (a b : Z) : Z_to_rat (a + b) = Z_to_rat a + Z_to_rat b.
Proof.
  rewrite (Z_decomp a) (Z_decomp b).
  set (m := Z.to_nat a); set (n := Z.to_nat (-a)).
  set (m' := Z.to_nat b); set (n' := Z.to_nat (-b)).
  replace (Z.of_nat m - Z.of_nat n + (Z.of_nat m' - Z.of_nat n'))%ZZ
    with (Z.of_nat (Nat.add m m') - Z.of_nat (Nat.add n n'))%ZZ by lia.
  rewrite !Z_to_rat_diff !natr_add.
  by rewrite opprD addrACA.
Qed.

Lemma Z_to_rat_opp (a : Z) : Z_to_rat (- a) = - Z_to_rat a.
Proof.
  rewrite (Z_decomp a).
  set (m := Z.to_nat a); set (n := Z.to_nat (-a)).
  replace (- (Z.of_nat m - Z.of_nat n))%ZZ with (Z.of_nat n - Z.of_nat m)%ZZ by lia.
  by rewrite !Z_to_rat_diff opprB.
Qed.

Lemma Z_to_rat_mul (a b : Z) : Z_to_rat (a * b) = Z_to_rat a * Z_to_rat b.
Proof.
  rewrite (Z_decomp a) (Z_decomp b).
  set (m := Z.to_nat a); set (n := Z.to_nat (-a)).
  set (m' := Z.to_nat b); set (n' := Z.to_nat (-b)).
  replace ((Z.of_nat m - Z.of_nat n) * (Z.of_nat m' - Z.of_nat n'))%ZZ
    with (Z.of_nat (Nat.add (Nat.mul m m') (Nat.mul n n')) - Z.of_nat (Nat.add (Nat.mul m n') (Nat.mul n m')))%ZZ by lia.
  rewrite !Z_to_rat_diff !natr_add !natr_mul.
  rewrite mulrBl !mulrBr.
  by rewrite [in RHS]opprB [in LHS]opprD addrACA.
Qed.

Lemma Z_to_rat_inj (a b : Z) : Z_to_rat a = Z_to_rat b -> a = b.
Proof.
  rewrite (Z_decomp a) (Z_decomp b).
  set (m := Z.to_nat a); set (n := Z.to_nat (-a)).
  set (m' := Z.to_nat b); set (n' := Z.to_nat (-b)).
  rewrite !Z_to_rat_diff.
  move=> /eqP; rewrite subr_eq addrAC eq_sym subr_eq -!natr_add eqr_nat => /eqP H.
  lia.
Qed.

Lemma Z_to_rat_sub (a b : Z) : Z_to_rat (a - b)%ZZ = Z_to_rat a - Z_to_rat b.
Proof. by rewrite -Z.add_opp_r Z_to_rat_add Z_to_rat_opp. Qed.

(** * Field facts *)

Lemma rat_sqr_ge0 (x : rat) : 0 <= x ^+ 2.
Proof. exact: sqr_ge0. Qed.

Lemma rat_sqr_eq0 (x : rat) : x ^+ 2 = 0 <-> x = 0.
Proof. by split => [/eqP|->]; [rewrite sqrf_eq0 => /eqP | rewrite expr0n]. Qed.

Lemma rat_sum_sqr2_eq0 (x y : rat) : x ^+ 2 + y ^+ 2 = 0 -> x = 0 /\ y = 0.
Proof.
  move=> /eqP; rewrite paddr_eq0 ?sqr_ge0 // !sqrf_eq0 => /andP [/eqP -> /eqP ->].
  by split.
Qed.

Lemma rat_sum_sqr_eq0 (s : seq rat) :
  \sum_(x <- s) x ^+ 2 = 0 -> forall x, x \in s -> x = 0.
Proof.
  move=> /eqP; rewrite psumr_eq0; first by move=> i _; exact: sqr_ge0.
  move=> /allP H x Hx.
  have := H x Hx; rewrite implyTb sqrf_eq0; by move/eqP.
Qed.

Lemma rat_sum_sqr_eq0_iff (s : seq rat) :
  \sum_(x <- s) x ^+ 2 = 0 <-> forall x, x \in s -> x = 0.
Proof.
  split; first exact: rat_sum_sqr_eq0.
  move=> H; rewrite big_seq big1 // => x /H ->; exact: expr0n.
Qed.

(* the same for a sum of squares of the images of a list under a map *)
Lemma rat_sum_sqr_map_eq0_iff {X : Type} (F : X -> rat) (l : list X) :
  \sum_(q <- l) (F q) ^+ 2 = 0 <-> forall q, List.In q l -> F q = 0.
Proof.
  induction l as [ | q l IHl ]; simpl.
  - by rewrite big_nil; split => // _ ? [].
  - rewrite big_cons; split.
    + have Hs : 0 <= \sum_(r <- l) (F r) ^+ 2 by apply: sumr_ge0 => i _; exact: sqr_ge0.
      move=> /eqP; rewrite paddr_eq0 ?sqr_ge0 //.
      rewrite sqrf_eq0 => /andP [/eqP H1 /eqP H2] r [<- | Hr] //.
      by apply IHl.
    + move=> H.
      have -> : \sum_(r <- l) (F r) ^+ 2 = 0.
      { apply IHl => r Hr; apply: H; by right. }
      have -> : F q = 0 by apply: H; left.
      by rewrite expr0n addr0.
Qed.

Lemma rat_mul_eq0 (x y : rat) : x * y = 0 <-> x = 0 \/ y = 0.
Proof.
  split.
  - move=> /eqP; rewrite mulf_eq0 => /orP [/eqP|/eqP]; tauto.
  - by move=> [->|->]; rewrite ?mul0r ?mulr0.
Qed.

Lemma rat_neq0_inv (x : rat) : x <> 0 <-> exists y, x * y = 1.
Proof.
  split.
  - move=> H; exists (x^-1); apply: mulfV; exact/eqP.
  - move=> [y Hy] Hx; move: Hy; rewrite Hx mul0r => /eqP; by rewrite eq_sym oner_eq0.
Qed.

Lemma rat_neq0_inv' (x : rat) : x != 0 <-> exists y, x * y = 1.
Proof. rewrite -rat_neq0_inv; split; by move/eqP. Qed.

(** * Discreteness and enumerability *)

Definition rat_eq_dec (x y : rat) : { x = y } + { x <> y } :=
  match @eqP _ x y with
  | ReflectT H => left H
  | ReflectF H => right H
  end.

Lemma discrete_rat : discrete rat.
Proof.
  exists (fun '(x,y) => x == y :> rat); intros [x y].
  unfold reflects; split; [ move=> -> | move=> /eqP ]; auto.
  exact: eqxx.
Qed.

Definition rat_enum : nat -> option rat := @unpickle rat.

Lemma enumerator__T_rat : enumerator__T rat_enum rat.
Proof. intros x; exists (pickle x); exact: pickleK. Qed.

Lemma enumerable__T_rat : enumerable__T rat.
Proof. exists rat_enum; exact enumerator__T_rat. Qed.

(** Enumeration of vectors and of functions pos n -> X (up to extensionality) *)

Section vec_enum.

  Variables (X : Type) (f : nat -> option X) (Hf : enumerator__T f X).

  Fixpoint vec_enum n : nat -> option (vec X n) :=
    match n with
    | 0   => fun _ => Some vec_nil
    | S n => fun k =>
        match EnumerabilityFacts.prod_enum f (vec_enum n) k with
        | Some (x, v) => Some (x ## v)
        | None => None
        end
    end.

  Lemma enumerator__T_vec n : enumerator__T (vec_enum n) (vec X n).
  Proof using Hf.
    induction n as [ | n IHn ]; intros v.
    - exists 0%nat; simpl; f_equal; symmetry; exact (vec_0_nil v).
    - rewrite (vec_head_tail v).
      destruct (@enumerator__T_prod _ _ _ _ Hf IHn (vec_head v, vec_tail v)) as [ k Hk ].
      exists k; simpl; by rewrite Hk.
  Qed.

  (* functions on finite positions are enumerated up to extensional equality *)
  Lemma pos_fun_enum n (g : pos n -> X) :
    exists k v, vec_enum n k = Some v /\ forall p, vec_pos v p = g p.
  Proof using Hf.
    destruct (enumerator__T_vec (vec_set_pos g)) as [ k Hk ].
    exists k, (vec_set_pos g); split; auto.
    intros p; apply vec_pos_set.
  Qed.

End vec_enum.

Lemma enumerable__T_vec X n : enumerable__T X -> enumerable__T (vec X n).
Proof. intros [f Hf]; exists (vec_enum f n); now apply enumerator__T_vec. Qed.

Definition rat_vec_enum n := vec_enum rat_enum n.

Lemma rat_pos_fun_enum n (g : pos n -> rat) :
  exists k v, rat_vec_enum n k = Some v /\ forall p, vec_pos v p = g p.
Proof. apply pos_fun_enum, enumerator__T_rat. Qed.
