(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2A: MathComp's [rat] as a setoid ordered field with Leibniz
   equality (sanity check: the interface of SOF.v is satisfiable, and
   the standard model is an instance). *)

From Stdlib Require Import Setoid Morphisms RelationClasses.

From Undecidability.H10.Rational Require Import SOF.

From mathcomp Require Import boot order algebra.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Definition rat_SRing : SRing := {|
  car := rat;
  eqv := @eq rat;
  sr_zero := 0;
  sr_one := 1;
  sr_add := +%R;
  sr_mul := *%R;
  sr_opp := -%R;
  sr_inv := GRing.inv;
  sr_equiv := eq_equivalence;
  sr_add_wd := ltac:(by move=> ? ? -> ? ? ->);
  sr_mul_wd := ltac:(by move=> ? ? -> ? ? ->);
  sr_opp_wd := ltac:(by move=> ? ? ->);
  sr_inv_wd := ltac:(by move=> ? ? ->);
  sr_add_0_l := @add0r _;
  sr_add_comm := @addrC _;
  sr_add_assoc := @addrA _;
  sr_mul_1_l := @mul1r _;
  sr_mul_comm := @mulrC _;
  sr_mul_assoc := @mulrA _;
  sr_distr_l := @mulrDl _;
  sr_opp_def := @subrr _
|}.

Lemma rat_lt_le_neq (x y : rat) : x < y <-> x <= y /\ x <> y.
Proof.
  rewrite lt_neqAle; split; first by case/andP => /eqP H ->.
  by case=> -> H; rewrite andbT; apply/eqP.
Qed.

Lemma rat_trichotomy (x y : rat) : x < y \/ x = y \/ y < x.
Proof. by case: (ltgtP x y) => H; auto. Qed.

Definition rat_SOF : SOF := {|
  sof_ring := rat_SRing;
  sof_le := fun x y : rat => x <= y;
  sof_lt := fun x y : rat => x < y;
  sof_abs := fun x : rat => `|x|;
  of_rat := fun x : rat => x;
  sof_le_wd := ltac:(by move=> ? ? -> ? ? ->);
  sof_lt_wd := ltac:(by move=> ? ? -> ? ? ->);
  sof_neq_1_0 := ltac:(by move=> /eqP; rewrite oner_eq0);
  sof_inv_l := ltac:(by move=> x /eqP Hx; rewrite /= mulVf);
  sof_inv_0 := @invr0 _;
  sof_le_refl := @lexx _ _;
  sof_le_antisym := ltac:(by move=> x y H1 H2; apply/le_anti/andP);
  sof_le_trans := ltac:(by move=> x y z; apply: le_trans);
  sof_lt_le_neq := rat_lt_le_neq;
  sof_lt_trichotomy := rat_trichotomy;
  sof_add_le_mono_l := ltac:(by move=> x y z /=; rewrite lerD2l);
  sof_mul_pos := ltac:(by move=> x y; apply: mulr_gt0);
  sof_abs_pos := ltac:(by move=> x /= H; rewrite ger0_norm);
  sof_abs_neg := ltac:(by move=> x /= H; rewrite ler0_norm);
  sof_of_rat_add := ltac:(by []);
  sof_of_rat_mul := ltac:(by []);
  sof_of_rat_1 := ltac:(by []);
  sof_of_rat_le := ltac:(by [])
|}.
