(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2B carrier: the ultrapower  rat^nat / U  as a setoid ordered
   field, for an ultrafilter U given as a Section variable (Ultrafilter.v).

   - carrier [nat -> rat], equality "agree on a set in U", pointwise
     operations (inverse pointwise, with 0^-1 = 0), order and absolute
     value pointwise modulo U, [of_rat] the constant sequences;
   - [ultrapower_SOF U HU : SOF] (all field and order laws are proved;
     only the ultrafilter properties of U are used, no axiom);
   - with a nonprincipal U, the sequence [upw_omega = fun n => n%:R] is
     larger than every standard natural number ([upw_omega_gt]);
   - [ultrapower_nonstandard]: there is a setoid ordered field with an
     element above all standard naturals. This is the only statement
     here that uses the axiom [ultrafilter_exists]; note that it is a
     Prop, as the existential of the axiom cannot be eliminated into
     Type (no choice). *)

From Stdlib Require Import Setoid Morphisms RelationClasses.

From Undecidability.H10.Rational Require Import Ultrafilter SOF.

From mathcomp Require Import boot order algebra.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section ultrapower.

  Variables (U : (nat -> Prop) -> Prop) (HU : ultrafilter U).

  Definition upw := nat -> rat.

  Implicit Types f g h : upw.

  Definition upw_eqv f g : Prop := U (fun n => f n = g n).
  Definition upw_le f g : Prop := U (fun n => f n <= g n).
  Definition upw_lt f g : Prop := U (fun n => f n < g n).

  Definition upw_zero : upw := fun _ => 0.
  Definition upw_one : upw := fun _ => 1.
  Definition upw_add f g : upw := fun n => f n + g n.
  Definition upw_mul f g : upw := fun n => f n * g n.
  Definition upw_opp f : upw := fun n => - f n.
  Definition upw_inv f : upw := fun n => (f n)^-1.
  Definition upw_abs f : upw := fun n => `|f n|.
  Definition upw_of_rat (a : rat) : upw := fun _ => a.

  Local Ltac pw := apply (uf_all HU); intros n; unfold upw_add, upw_mul, upw_opp, upw_zero, upw_one; simpl.

  Lemma upw_equiv : Equivalence upw_eqv.
  Proof using HU.
    split.
    - intros f; apply (uf_all HU); reflexivity.
    - intros f g H; apply (uf_ae1 HU _ _ H); intros n; apply esym.
    - intros f g h H1 H2; apply (uf_ae2 HU _ _ _ H1 H2); intros n; apply etrans.
  Qed.

  Lemma upw_add_wd : Proper (upw_eqv ==> upw_eqv ==> upw_eqv) upw_add.
  Proof using HU. intros f f' Hf g g' Hg; apply (uf_ae2 HU _ _ _ Hf Hg); intros n e1 e2; rewrite /upw_add e1 e2; reflexivity. Qed.
  Lemma upw_mul_wd : Proper (upw_eqv ==> upw_eqv ==> upw_eqv) upw_mul.
  Proof using HU. intros f f' Hf g g' Hg; apply (uf_ae2 HU _ _ _ Hf Hg); intros n e1 e2; rewrite /upw_mul e1 e2; reflexivity. Qed.
  Lemma upw_opp_wd : Proper (upw_eqv ==> upw_eqv) upw_opp.
  Proof using HU. intros f f' Hf; apply (uf_ae1 HU _ _ Hf); intros n e; rewrite /upw_opp e; reflexivity. Qed.
  Lemma upw_inv_wd : Proper (upw_eqv ==> upw_eqv) upw_inv.
  Proof using HU. intros f f' Hf; apply (uf_ae1 HU _ _ Hf); intros n e; rewrite /upw_inv e; reflexivity. Qed.

  Definition upw_SRing : SRing := {|
    car := upw;
    eqv := upw_eqv;
    sr_zero := upw_zero;
    sr_one := upw_one;
    sr_add := upw_add;
    sr_mul := upw_mul;
    sr_opp := upw_opp;
    sr_inv := upw_inv;
    sr_equiv := upw_equiv;
    sr_add_wd := upw_add_wd;
    sr_mul_wd := upw_mul_wd;
    sr_opp_wd := upw_opp_wd;
    sr_inv_wd := upw_inv_wd;
    sr_add_0_l := ltac:(intros f; pw; apply add0r);
    sr_add_comm := ltac:(intros f g; pw; apply addrC);
    sr_add_assoc := ltac:(intros f g h; pw; apply addrA);
    sr_mul_1_l := ltac:(intros f; pw; apply mul1r);
    sr_mul_comm := ltac:(intros f g; pw; apply mulrC);
    sr_mul_assoc := ltac:(intros f g h; pw; apply mulrA);
    sr_distr_l := ltac:(intros f g h; pw; apply mulrDl);
    sr_opp_def := ltac:(intros f; pw; apply subrr)
  |}.

  Lemma upw_le_wd : Proper (upw_eqv ==> upw_eqv ==> iff) upw_le.
  Proof using HU.
    intros f f' Hf g g' Hg; split; intros H.
    - apply (uf_ae3 HU _ _ _ _ Hf Hg H); intros n e1 e2 h; rewrite -e1 -e2; exact h.
    - apply (uf_ae3 HU _ _ _ _ Hf Hg H); intros n e1 e2 h; rewrite e1 e2; exact h.
  Qed.
  Lemma upw_lt_wd : Proper (upw_eqv ==> upw_eqv ==> iff) upw_lt.
  Proof using HU.
    intros f f' Hf g g' Hg; split; intros H.
    - apply (uf_ae3 HU _ _ _ _ Hf Hg H); intros n e1 e2 h; rewrite -e1 -e2; exact h.
    - apply (uf_ae3 HU _ _ _ _ Hf Hg H); intros n e1 e2 h; rewrite e1 e2; exact h.
  Qed.

  Lemma upw_neq_1_0 : ~ upw_eqv upw_one upw_zero.
  Proof using HU.
    intros H; apply (uf_proper HU); apply (uf_ae1 HU _ _ H).
    intros n E; move: E; rewrite /upw_one /upw_zero => /eqP; rewrite oner_eq0.
    discriminate.
  Qed.

  Lemma upw_inv_l f : ~ upw_eqv f upw_zero -> upw_eqv (upw_mul (upw_inv f) f) upw_one.
  Proof using HU.
    intros H; apply (uf_compl HU) in H; apply (uf_ae1 HU _ _ H).
    intros n Hn; rewrite /upw_mul /upw_inv /upw_one mulVf //; apply/eqP; exact Hn.
  Qed.

  Lemma upw_inv_0 : upw_eqv (upw_inv upw_zero) upw_zero.
  Proof using HU. apply (uf_all HU); intros n; apply invr0. Qed.

  Lemma upw_le_refl f : upw_le f f.
  Proof using HU. apply (uf_all HU); intros n; apply lexx. Qed.

  Lemma upw_le_antisym f g : upw_le f g -> upw_le g f -> upw_eqv f g.
  Proof using HU. intros H1 H2; apply (uf_ae2 HU _ _ _ H1 H2); intros n h1 h2; apply/le_anti/andP; split; assumption. Qed.

  Lemma upw_le_trans f g h : upw_le f g -> upw_le g h -> upw_le f h.
  Proof using HU. intros H1 H2; apply (uf_ae2 HU _ _ _ H1 H2); intros n h1 h2; exact (le_trans h1 h2). Qed.

  Lemma upw_lt_le_neq f g : upw_lt f g <-> upw_le f g /\ ~ upw_eqv f g.
  Proof using HU.
    split.
    - intros H; split.
      + apply (uf_ae1 HU _ _ H); intros n; apply ltW.
      + intros E; apply (uf_proper HU); apply (uf_ae2 HU _ _ _ H E).
        intros n h e; move: h; rewrite e ltxx; discriminate.
    - intros [ H E ]; apply (uf_compl HU) in E; apply (uf_ae2 HU _ _ _ H E).
      intros n h e; rewrite lt_neqAle h andbT; apply/eqP; exact e.
  Qed.

  Lemma upw_lt_trichotomy f g : upw_lt f g \/ upw_eqv f g \/ upw_lt g f.
  Proof using HU.
    destruct (uf_total HU (fun n => f n < g n)) as [ H | H ]; [ left; exact H | right ].
    destruct (uf_total HU (fun n => f n = g n)) as [ E | E ]; [ left; exact E | right ].
    apply (uf_ae2 HU _ _ _ H E); intros n h e.
    rewrite lt_neqAle; apply/andP; split.
    - apply/eqP => e'; exact (e (esym e')).
    - by rewrite leNgt; apply/negP.
  Qed.

  Lemma upw_add_le_mono_l f g h : upw_le f g -> upw_le (upw_add h f) (upw_add h g).
  Proof using HU. intros H; apply (uf_ae1 HU _ _ H); intros n h1; rewrite /upw_add lerD2l; exact h1. Qed.

  Lemma upw_mul_pos f g : upw_lt upw_zero f -> upw_lt upw_zero g -> upw_lt upw_zero (upw_mul f g).
  Proof using HU. intros H1 H2; apply (uf_ae2 HU _ _ _ H1 H2); intros n h1 h2; exact (mulr_gt0 h1 h2). Qed.

  Lemma upw_abs_pos f : upw_le upw_zero f -> upw_eqv (upw_abs f) f.
  Proof using HU. intros H; apply (uf_ae1 HU _ _ H); intros n h; exact (ger0_norm h). Qed.

  Lemma upw_abs_neg f : upw_le f upw_zero -> upw_eqv (upw_abs f) (upw_opp f).
  Proof using HU. intros H; apply (uf_ae1 HU _ _ H); intros n h; exact (ler0_norm h). Qed.

  Definition ultrapower_SOF : SOF := {|
    sof_ring := upw_SRing;
    sof_le := upw_le;
    sof_lt := upw_lt;
    sof_abs := upw_abs;
    of_rat := upw_of_rat;
    sof_le_wd := upw_le_wd;
    sof_lt_wd := upw_lt_wd;
    sof_neq_1_0 := upw_neq_1_0;
    sof_inv_l := upw_inv_l;
    sof_inv_0 := upw_inv_0;
    sof_le_refl := upw_le_refl;
    sof_le_antisym := upw_le_antisym;
    sof_le_trans := upw_le_trans;
    sof_lt_le_neq := upw_lt_le_neq;
    sof_lt_trichotomy := upw_lt_trichotomy;
    sof_add_le_mono_l := upw_add_le_mono_l;
    sof_mul_pos := upw_mul_pos;
    sof_abs_pos := upw_abs_pos;
    sof_abs_neg := upw_abs_neg;
    sof_of_rat_add := ltac:(intros a b; apply (uf_all HU); reflexivity);
    sof_of_rat_mul := ltac:(intros a b; apply (uf_all HU); reflexivity);
    sof_of_rat_1 := ltac:(apply (uf_all HU); reflexivity);
    sof_of_rat_le := ltac:(intros a b H; apply (uf_all HU); intros n; exact H)
  |}.

  (** Łoś for atoms: the order and equality of [ultrapower_SOF] are the
      pointwise ones modulo U, by definition *)

  Lemma upw_eqvE (f g : ultrapower_SOF) : (f ≡ g)%sof <-> U (fun n => f n = g n).
  Proof using HU. reflexivity. Qed.
  Lemma upw_leE (f g : ultrapower_SOF) : (f <= g)%sof <-> U (fun n => f n <= g n).
  Proof using HU. reflexivity. Qed.
  Lemma upw_ltE (f g : ultrapower_SOF) : (f < g)%sof <-> U (fun n => f n < g n).
  Proof using HU. reflexivity. Qed.

  (** a nonstandard element, for a nonprincipal U *)

  Definition upw_omega : ultrapower_SOF := fun n => n%:R.

  Lemma upw_omega_gt (HN : nonprincipal U) (k : nat) : ((k%:R : ultrapower_SOF) < upw_omega)%sof.
  Proof using HU.
    rewrite -(of_rat_nat ultrapower_SOF k) upw_ltE.
    destruct (uf_total HU (fun n => (k%:R < upw_omega n :> rat))) as [ H | H ]; first exact H.
    exfalso; refine (HN _ _ H); exists k.+1; intros n Hn; apply/ssrnat.ltP.
    rewrite ltnS leqNgt; apply/negP => Hk; apply: Hn; rewrite /upw_omega ltr_nat; exact Hk.
  Qed.

End ultrapower.

Arguments upw_omega {U}.

(** The only use of the axiom in this file. *)
Theorem ultrapower_nonstandard :
  exists (F : SOF) (w : F), forall k : nat, ((k%:R : F) < w)%sof.
Proof.
  destruct ultrafilter_exists as [ U [ HU HN ] ].
  exists (ultrapower_SOF U HU), (upw_omega HU); exact (upw_omega_gt U HU HN).
Qed.
