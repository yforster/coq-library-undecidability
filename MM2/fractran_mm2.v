(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import utils pos vec gcd.
Require Import subcode sss mm2_defs mm2_utils. 
Require Import fractran_defs.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "P /MM2/ s -+> t" := (sss_progress (@mm2_sss _) P s t) (at level 70, no associativity).
Local Notation "P /MM2/ s ->> t" := (sss_compute (@mm2_sss _) P s t) (at level 70, no associativity).
Local Notation "P /MM2/ s ↓" := (sss_terminates (@mm2_sss _) P s) (at level 70, no associativity). 

Local Notation "l /F/ x → y" := (fractran_step l x y) (at level 70, no associativity).

(** FRACTRAN with two counter *)

Section Fractran_with_two_counters.

  Hint Resolve subcode_refl.
  Hint Rewrite mm2_null_length mm2_transfert_length mm2_incs_length mm2_decs_copy_length 
               mm2_mult_cst_length mm2_decs_length mm2_mod_cst_length mm2_div_cst_length : length_db.

  Let src : pos 2 := pos0.
  Let dst : pos 2 := pos1.

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Let Hsrc_dst : src <> dst.    Proof. discriminate. Qed.
  Let Hdst_src : dst <> src.    Proof. discriminate. Qed.

  Section mm2_fractran_one.

    (* FRACTRAN computation, try one fraction a/b *)

    Variables (a b : nat) (p i : nat).

    Definition mm2_fractran_one :=
           mm2_mult_cst src dst a i
        ++ mm2_mod_cst dst src (11+a+4*b+i) (21+a+7*b+i) b (5+a+i)
        ++ mm2_div_cst src dst b (11+a+4*b+i)
        ++ mm2_transfert dst src (16+a+7*b+i)
        ++ INC dst :: DEC dst p
        :: mm2_div_cst src dst a (21+a+7*b+i)
        ++ mm2_transfert dst src (26+4*a+7*b+i).

    Fact mm2_fractran_one_length : length mm2_fractran_one = 29+4*a+7*b.
    Proof. unfold mm2_fractran_one; rew length; omega. Qed.

    Hypothesis (Ha : a <> 0) (Hb : b <> 0).

    (* If the state in src is compatible with a/b then
       src becomes src*a/b and jump at p *)

    Fact mm2_fractran_one_ok_progress k v :
            k*b = a*(v#>src)
         -> v#>dst = 0
         -> (i,mm2_fractran_one) /MM2/ (i,v) -+> (p,v[k/src]).
    Proof.
      intros H1 H2; unfold mm2_fractran_one.
      apply sss_progress_trans with (5+a+i,v[0/src][(k*b)/dst]).
      { apply subcode_sss_progress with (P := (i,mm2_mult_cst src dst a i)); auto.
        apply mm2_mult_cst_progress; auto.
        rewrite H2, <- H1; do 2 f_equal; omega. }
      apply sss_progress_trans with (11+a+4*b+i,v[(k*b)/src][0/dst]).
      { apply subcode_sss_progress with (P := (5+a+i,mm2_mod_cst dst src (11+a+4*b+i) (21+a+7*b+i) b (5+a+i))); auto.
        apply mm2_mod_cst_divides_progress with k; rew vec; try omega.
        f_equal; apply vec_pos_ext; intros y; dest y dst; try omega; dest y src. }
      apply sss_progress_trans with (16+a+7*b+i,v[0/src][k/dst]).
      { apply subcode_sss_progress with (P := (11+a+4*b+i,mm2_div_cst src dst b (11+a+4*b+i))); auto.
        apply mm2_div_cst_progress with k; auto; rew vec; try omega.
        f_equal; try omega.
        apply vec_pos_ext; intros y; dest y dst; try omega; dest y src. }
      apply sss_progress_trans with (19+a+7*b+i,v[k/src][0/dst]).
      { apply subcode_sss_progress with (P := (16+a+7*b+i,mm2_transfert dst src (16+a+7*b+i))); auto.
        apply mm2_transfert_progress; auto.
        f_equal; try omega.
        apply vec_pos_ext; intros y; dest y dst; try omega; dest y src. }
      mm2 sss INC with dst.
      mm2 sss DEC S with dst p 0; rew vec.
      mm2 sss stop; f_equal.
      apply vec_pos_ext; intros y; dest y dst; try omega; dest y src. 
    Qed.

    (* If the state in src is not compatible with a/b then jump at the end of the code *)

    Fact mm2_fractran_one_nok_progress v :
            ~ divides b (a*(v#>src))
         -> v#>dst = 0
         -> (i,mm2_fractran_one) /MM2/ (i,v) -+> (length mm2_fractran_one+i,v).
    Proof.
      rewrite mm2_fractran_one_length.
      intros H1 H2; unfold mm2_fractran_one.
      rewrite divides_rem_eq in H1.
      revert H1.
      generalize (div_rem_spec1 (a*(v#>src)) b)
                 (div_rem_spec2 (a*(v#>src)) Hb).
      generalize (div (a*(v#>src)) b) (rem (a*(v#>src)) b); intros x y H3 H4 H5.
      apply sss_progress_trans with (5+a+i,v[0/src][(x*b+y)/dst]).
      { apply subcode_sss_progress with (P := (i,mm2_mult_cst src dst a i)); auto.
        apply mm2_mult_cst_progress; auto.
        rewrite H2, <- H3; do 2 f_equal; omega. }
      apply sss_progress_trans with (21+a+7*b+i,v[(a*(v#>src))/src][0/dst]).
      { apply subcode_sss_progress with (P := (5+a+i,mm2_mod_cst dst src (11+a+4*b+i) (21+a+7*b+i) b (5+a+i))); auto.
        apply mm2_mod_cst_not_divides_progress with x y; rew vec; try omega.
        f_equal; apply vec_pos_ext; intros c; dest c dst; try omega; dest c src; omega. }
      apply sss_progress_trans with (26+4*a+7*b+i,v[0/src][(v#>src)/dst]).
      { apply subcode_sss_progress with (P := (21+a+7*b+i,mm2_div_cst src dst a (21+a+7*b+i))); auto.
        apply mm2_div_cst_progress with (v#>src); auto; rew vec; try omega; try ring.
        f_equal; try omega.
        apply vec_pos_ext; intros c; dest c dst; try omega; dest c src. }
      apply subcode_sss_progress with (P := (26+4*a+7*b+i,mm2_transfert dst src (26+4*a+7*b+i))); auto.
      apply mm2_transfert_progress; auto.
      f_equal; try omega.
      apply vec_pos_ext; intros c; dest c dst; try omega; dest c src. 
    Qed.

  End mm2_fractran_one.

  Hint Rewrite mm2_fractran_one_length : length_db.

  Section mm2_fractran_step.

    (* One step of Fractran computation *)

    Variable (p : nat).

    Fixpoint mm2_fractran_step ll i { struct ll } :=
      match ll with
        | nil       => nil
        | (a,b)::ll => let P := mm2_fractran_one a b p i
                       in  P ++ mm2_fractran_step ll (length P+i)
      end.

    Fact mm2_fractran_step_success_progress ll i x y v : 
            Forall (fun c => fst c <> 0 /\ snd c <> 0) ll
         -> ll /F/ x → y
         -> v#>src = x
         -> v#>dst = 0
         -> (i,mm2_fractran_step ll i) /MM2/ (i,v) -+> (p,v[y/src]).
    Proof.
      intros H1 H2; revert H2 i v H1.
      induction 1 as [ a b ll x y H1 | a b ll x y H1 H2 IH2 ];
        intros i v H3 H6 H7; rewrite Forall_cons_inv in H3; destruct H3 as ((H3 & H4) & H5); simpl in H3, H4;
        unfold mm2_fractran_step; fold mm2_fractran_step.
      + apply subcode_sss_progress with (P := (i,mm2_fractran_one a b p i)); auto.
        apply mm2_fractran_one_ok_progress; auto; rewrite H6, <- H1; ring.
      + apply sss_progress_trans with (length (mm2_fractran_one a b p i)+i,v).
        { apply subcode_sss_progress with (P := (i,mm2_fractran_one a b p i)); auto.
          apply mm2_fractran_one_nok_progress; auto; rewrite H6; auto. }
        { apply subcode_sss_progress with (P := (length (mm2_fractran_one a b p i)+i,
                                                 mm2_fractran_step ll (length (mm2_fractran_one a b p i)+i))); auto.
          apply subcode_right; omega. }
    Qed.

    Fact mm2_fractran_step_failure_compute ll i v : 
            Forall (fun c => fst c <> 0 /\ snd c <> 0) ll
         -> fractran_stop ll (v#>src)
         -> v#>dst = 0
         -> (i,mm2_fractran_step ll i) /MM2/ (i,v) ->> (length (mm2_fractran_step ll i)+i,v).
    Proof.
      intros H1 H2 H3; revert H1 i H2.
      induction 1 as [ | (a,b) ll (Ha & Hb) Hll IH ]; intros i H4.
      + mm2 sss stop.
      + apply fractan_stop_cons_inv in H4; destruct H4 as (H4 & H5).
        unfold mm2_fractran_step; fold mm2_fractran_step.
        set (P := mm2_fractran_one a b p i); rew length.
        apply sss_compute_trans with (length P+i,v).
        { apply subcode_sss_compute with (P := (i,P)); auto.
          apply sss_progress_compute, mm2_fractran_one_nok_progress; auto. }
        { apply subcode_sss_compute with (P := (length P+i,mm2_fractran_step ll (length P + i))); auto.
          { apply subcode_right; omega. }
            replace (length P+length (mm2_fractran_step ll (length P + i))+i)
            with    (length (mm2_fractran_step ll (length P + i)) + (length P+i)) by omega.
            auto. }
    Qed.

  End mm2_fractran_step.

  Section fractran_mm2.

    Variables (ll : list (nat*nat)) (Hll : Forall (fun c => fst c <> 0 /\ snd c <> 0) ll).

    Let i := 1.

    Definition fractran_mm2 := mm2_fractran_step i ll i.

    Lemma fractran_mm2_sound v x w : 
               v#>dst = 0 
            -> fractran_compute ll (v#>src) x
            -> fractran_stop ll x 
            -> w = v[x/src]
            -> (i,fractran_mm2) /MM2/ (i,v) ->> (length fractran_mm2+i,w).
    Proof.
      intros H1 (u & H2) H3 ?; subst w.
      revert v x H1 H2 H3.
      induction u as [ | u IHu ]; simpl; intros v y H1 H2 H3.
      + rewrite <- H2; rew vec.
        apply mm2_fractran_step_failure_compute; auto.
        rewrite H2; auto.
      + destruct H2 as (z & H2 & H4).
        apply mm2_fractran_step_success_progress 
          with (1 := Hll) (p := i) (i := i) (v := v) in H2; auto.
        apply IHu with (v := v[z/src]) in H3; auto; rew vec.
        revert H3; rew vec; intros H3.
        apply sss_compute_trans with (2 := H3).
        apply sss_progress_compute; auto.
    Qed.

    Lemma fractran_mm2_complete v : 
               v#>dst = 0 
            -> (i,fractran_mm2) /MM2/ (i,v) ↓
            -> ll /F/ (v#>src) ↓.
    Proof.
      intros H1 ((j,w) & (u & H2) & H3); simpl fst in H3.
      revert v H1 H2.
      induction on u as IHu with measure u; intros v H1 H2.
      destruct (fractran_step_dec ll (v#>src)) as [ (y & Hy) | H4 ].
      2: { exists (v#>src); split; auto; exists 0; simpl; auto. }
      generalize Hy; intros H4.
      apply mm2_fractran_step_success_progress 
        with (1 := Hll) (p := i) (i := i) (v := v) 
        in H4; auto.
      fold fractran_mm2 in H4.
      destruct subcode_sss_progress_inv with (4 := H4) (5 := H2)
        as (p & H5 & H6); auto.
      1: apply mm2_sss_fun.
      apply IHu in H6; auto; rew vec.
      destruct H6 as (z & (k & Hk) & Hz2).
      exists z; split; auto; exists (S k), y; split; auto.
      revert Hk; rew vec.
    Qed.
   
    Theorem fractran_mm2_reduction x : 
        ll /F/ x ↓ <-> (i,fractran_mm2) /MM2/ (i,x##0##vec_nil) ↓.
    Proof.
      split; auto.
      + intros (y & H2 & H3).
        exists (length fractran_mm2+i,y##0##vec_nil); split; simpl; auto; try omega.
        apply fractran_mm2_sound with (x := y); auto.
      + apply fractran_mm2_complete; auto.
    Qed.

  End fractran_mm2.

End Fractran_with_two_counters.

Check fractran_mm2.
Check fractran_mm2_reduction.