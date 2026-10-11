(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Tier 2: soundness of the finite tests (02-reduction.tex, Lemma
   red:standard-model and the soundness paragraph of Section 2.4):
   if f has an integer zero, then every finite test [test D f N]
   succeeds. See DESIGN.md, Section 4.4.

   Construction. All values are integers. A valuation [ev T : gterm -> int]
   is defined by structural recursion on ground terms:
   - ring symbols by their meaning, s_cst i by the i-th component of the
     integer zero;
   - the coordinate functions by the cleared coordinates [clr] of
     [mulP D a], the chain functions by those of [mulQ D (k a)];
   - the Skolem functions of ax_rep K by a pair of finite tables
     [T : Tab] keyed by integers: (K, A) for the unary symbols and
     (K, A, a) for the binary ones.
   Hypothesis HCov is in forall-exists form, so the tables cannot be
   chosen globally without choice. Instead, for a fixed N, the finitely
   many keys needed by the instances of [inst_list D f N] are filled
   in by structural induction on the requested terms ([okt_build]):
   entries are only ever added, and the value of a term whose keys are
   all present does not change when entries are added ([ev_ext]). Each
   entry satisfies the specification [Spec1] / [Spec2]; the witnesses are
   extracted from HCov (RepSpec), Bezout modulo the prime r (fidelity
   witnesses), and finite choice over the 13 members ([fchoice]).
   Then (a), (b), (d) hold everywhere, every instance holds by E1, E2,
   [rat_Z0], the integer zero, and the table specifications, and
   [testf_write] (Theory.v) gives the satisfying assignment.

   Main result: [tests_sound]. No axioms (not even classic). *)

From Stdlib Require Import Arith ZArith Lia List.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos.

From Undecidability.H10.Dio
  Require dio_logic.

From Undecidability.H10
  Require Import H10Z.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData Ambient Theory.

Import ListNotations.

(** * Stdlib helpers *)

(* the components of an integer vector, as a function on nat *)
Definition zcst {n} (Φ : pos n -> Z) (i : nat) : Z :=
  match lt_dec i n with
  | left H => Φ (nat2pos H)
  | right _ => 0%Z
  end.

Lemma zcst_pos n (Φ : pos n -> Z) (v : pos n) : zcst Φ (pos2nat v) = Φ v.
Proof.
  unfold zcst; destruct (lt_dec (pos2nat v) n) as [ H | H ].
  - apply f_equal, nat2pos_pos2nat.
  - exfalso; apply H, pos2nat_prop.
Qed.

(* finite choice over a list with decidable equality (no axiom) *)
Lemma fchoice {T B : Type} (dec : forall x y : T, {x = y} + {x <> y}) (b0 : B)
  (P : T -> B -> Prop) (l : list T) :
  (forall x, In x l -> exists y, P x y) -> exists g : T -> B, forall x, In x l -> P x (g x).
Proof.
  induction l as [ | v l IHl ]; intros H.
  - exists (fun _ => b0); simpl; tauto.
  - destruct IHl as (g & Hg); [ intros; apply H; simpl; auto | ].
    destruct (H v) as (y & Hy); [ simpl; auto | ].
    exists (fun u => if dec u v then y else g u).
    intros u [ Hvu | Hu ].
    + subst u; destruct (dec v v) as [ _ | [] ]; auto.
    + destruct (dec u v) as [ -> | _ ]; auto.
Qed.

Lemma mem13_fchoice {B : Type} (b0 : B) (P : mem13 -> B -> Prop) :
  (forall j, exists y, P j y) -> exists g : mem13 -> B, forall j, P j (g j).
Proof.
  intros H; destruct (@fchoice _ _ mem13_eq_dec b0 P all_mem13) as (g & Hg).
  - intros x _; apply H.
  - exists g; intros j; apply Hg, all_mem13_spec.
Qed.

Lemma sgn_fchoice {B : Type} (P : sgn -> B -> Prop) :
  (forall s, exists y, P s y) -> exists g : sgn -> B, forall s, P s (g s).
Proof.
  intros H; destruct (H sg_p) as (y1 & H1); destruct (H sg_m) as (y2 & H2).
  exists (fun s => match s with sg_p => y1 | sg_m => y2 end); intros []; auto.
Qed.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** * Integer arithmetic *)

Lemma Z_to_R_intr (z : Z) : ((Z_to_R z : int)%:~R : rat) = Z_to_R z.
Proof. by rewrite /Z_to_R intrB !rmorph_nat. Qed.

Lemma dp_evalR_rat {V P : Set} (φ : V -> Z) (p : dio_polynomial V P) :
  dp_evalR (fun v => Z_to_R (φ v) : rat) (fun _ => 0) p = Z_to_R (dp_eval φ (fun _ => 0%ZZ) p).
Proof.
  elim: p => [ c | v | i | [] p Hp q Hq ] //=.
  - by rewrite Hp Hq !Z_to_R_rat Z_to_rat_add.
  - by rewrite Hp Hq !Z_to_R_rat Z_to_rat_mul.
Qed.

(* r * a <> 1 for |r| > 1 *)
Lemma mul_neq1 (r a : int) : (1 < `|r|)%N -> r * a != 1.
Proof.
  move=> Hr; apply/eqP => /(congr1 absz); rewrite abszM /= => /eqP.
  rewrite muln_eq1 => /andP [ /eqP H _ ]; by move: Hr; rewrite H.
Qed.

(* the fidelity witnesses "R/rR is a field": r | a, or a invertible mod r *)
Lemma fid_exists (r a : int) : prime `|r| ->
  exists fz fy fz' : int, a = r * fz \/ a * fy - 1 = r * fz'.
Proof.
  move=> Hp; case: (boolP (r %| a)%Z) => Hd.
  - exists (a %/ r)%Z, 0, 0; left; by rewrite mulrC divzK.
  - have Hc : coprimez a r.
    { rewrite coprimezE coprime_sym prime_coprime //. }
    case/coprimezP: Hc => [ [ u v ] /= E ].
    exists 0, u, (- v); right; rewrite -E; ring.
Qed.

(* 2B is invertible modulo r, for a prime r > 2 dividing B^2 - 2 *)
Lemma bez2B (r B wB : int) : prime `|r| -> (2 < `|r|)%N -> B ^+ 2 - 2 = r * wB ->
  exists io ka : int, 2 * B * io - 1 = r * ka.
Proof.
  move=> Hp Hr EB.
  have Hc : coprimez (2 * B) r.
  { rewrite coprimezE coprime_sym prime_coprime // abszM Euclid_dvdM //.
    apply/negP => /orP [ H2 | HB ].
    - by move: (dvdn_leq (isT : (0 < 2)%N) H2); rewrite leqNgt Hr.
    - have /dvdzP [ q Eq ] : (r %| B)%Z by [].
      have E2 : 2 = r * (r * q * q - wB).
      { have -> : (2 : int) = B ^+ 2 - (B ^+ 2 - 2) by ring.
        rewrite EB Eq; ring. }
      have H2 : (r %| 2)%Z by apply/dvdzP; exists (r * q * q - wB); rewrite mulrC -E2.
      by move: (dvdn_leq (isT : (0 < `|2%R : int|)%N) H2); rewrite leqNgt Hr. }
  case/coprimezP: Hc => [ [ u v ] /= E ].
  exists u, (- v).
  have -> : 2 * B * u - 1 = 2 * B * u - (u * (2 * B) + v * r) by rewrite E.
  ring.
Qed.

(** * Cleared coordinates *)

(* x = (x0 + x1 sqrt2) / x2 with integers and x2 <> 0 *)
Definition clr (x : qe rat) : int * int * int :=
  (numq (qre x) * denq (qim x), numq (qim x) * denq (qre x), denq (qre x) * denq (qim x)).

Lemma clr_den x : (clr x).2 != 0.
Proof. by rewrite /clr /= mulf_neq0 // denq_neq0. Qed.

Lemma clr_spec x :
  QE ((clr x).1.1)%:~R ((clr x).1.2)%:~R / qe_of (((clr x).2)%:~R : rat) = x.
Proof.
  have Hd : (((clr x).2)%:~R : rat) != 0 by rewrite intr_eq0 clr_den.
  rewrite qe_div_real //; case: x Hd => a b; rewrite /clr /= => Hd.
  have Ha : (denq a)%:~R != 0 :> rat by rewrite intr_eq0 denq_neq0.
  have Hb : (denq b)%:~R != 0 :> rat by rewrite intr_eq0 denq_neq0.
  rewrite !intrM; congr QE.
  - by rewrite -[RHS]divq_num_den; field; rewrite Ha Hb.
  - by rewrite -[RHS]divq_num_den; field; rewrite Ha Hb.
Qed.

Lemma clr_nz x : x != 0 -> QE (((clr x).1.1)%:~R : rat) ((clr x).1.2)%:~R != 0.
Proof.
  move=> Hx; apply/eqP => E; move: Hx; by rewrite -(clr_spec x) E mul0r eqxx.
Qed.

Definition cint (c : Signature.coord) (p : pt rat) : int :=
  match p with
  | None => 0
  | Some (x, y) =>
      match c with
      | cx0 => (clr x).1.1 | cx1 => (clr x).1.2 | cx2 => (clr x).2
      | cy0 => (clr y).1.1 | cy1 => (clr y).1.2 | cy2 => (clr y).2
      end
  end.

Lemma pt_rat_id (p : pt rat) : pt_rat p = p.
Proof. by case: p => [ [ x y ] | ] //=; rewrite !qe_rat_id. Qed.

(** * The integer valuation, given finite tables for the Skolem functions *)

Record Tab : Type := {
  t1 : nat -> int -> option (rep1 -> int);
  t2 : nat -> int -> int -> option (rep2 -> int)
}.

Section standard_model.

  Variable D : FixedData.
  Hypothesis HWF : FixedWF D.
  Hypothesis HS : StdHyps D.

  (* the integer zero, as a function of the index of s_cst *)
  Variable zc : nat -> int.

  Section eval.

    Variable T : Tab.

    Fixpoint ev (t : gterm) : int :=
      match t with
      | tvar x => match x with end
      | tapp0 g =>
          match g with
          | s_zero => 0
          | s_one => 1
          | s_int z => Z_to_R z
          | s_cst i => zc i
          end
      | tapp1 g s =>
          match g with
          | s_neg => - ev s
          | s_coord c => cint c (mulP D (ev s))
          | s_chain k c => cint c (mulQ D (k%:Z * ev s))
          | s_rep1 K c => if t1 T K (ev s) is Some w then w c else 0
          end
      | tapp2 g s s' =>
          match g with
          | s_add => ev s + ev s'
          | s_mul => ev s * ev s'
          | s_rep2 K c => if t2 T K (ev s) (ev s') is Some w then w c else 0
          end
      end.

    Definition rho (t : gterm) : rat := (ev t)%:~R.

    Lemma rho_ring t : ring_ok rho t.
    Proof.
      case: t => [ [] | g | g s | g s s' ]; case: g => * //=; rewrite /rho /=.
      - exact: Z_to_R_intr.
      - exact: intrN.
      - exact: intrD.
      - exact: intrM.
    Qed.

    Lemma rho_fun t t' : fun_ok rho t t'.
    Proof.
      case: t => [ [] | g | g s | g s1 s2 ]; case: t' => [ [] | g' | g' s' | g' s1' s2' ] //=.
      - move=> <- /intr_inj E; by rewrite /rho /= E.
      - move=> <- /intr_inj E1 /intr_inj E2; by rewrite /rho /= E1 E2.
    Qed.

    Lemma rho_Phi t : Phi_holdsR (fd_PhiL D) (rho t).
    Proof using HS. exact: (PP1 HS). Qed.

    (** ** The points T_a *)

    Lemma mulQ_some (n : int) : n != 0 ->
      exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y).
    Proof using HS. exact: (E2 HS). Qed.

    Lemma mulP_some (n : int) : n != 0 ->
      exists x y, mulP D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y).
    Proof using HS HWF.
      move=> Hn; apply: mulQ_some; rewrite mulf_neq0 //.
      apply/eqP => [] [] E; move: (wf_m HWF); by rewrite E.
    Qed.

    Lemma mulP0 : mulP D 0 = None.
    Proof. by rewrite /mulP mul0r. Qed.

    Lemma XYv_eq t x y : mulP D (ev t) = Some (x, y) -> Xv rho t = x /\ Yv rho t = y.
    Proof.
      move=> H; rewrite /Xv /Yv /rho /tco /= H /=; split; exact: clr_spec.
    Qed.

    Lemma Tv_ev t : Tv rho t = mulP D (ev t).
    Proof using HS HWF.
      rewrite /Tv /rho intr_eq0; case: (eqVneq (ev t) 0) => Ht.
      - by rewrite Ht mulP0.
      - have [ x [ y [ E _ ] ] ] := mulP_some Ht.
        by have [ -> -> ] := XYv_eq E; rewrite E.
    Qed.

    Lemma coordOK_rho t : coordOK rho t.
    Proof using HS HWF.
      rewrite /coordOK; case: (eqVneq (ev t) 0) => Ht; [ by left; rewrite /rho Ht | right ].
      have [ x [ y [ E [ Hx [ Hy Hc ] ] ] ] ] := mulP_some Ht.
      have [ EX EY ] := XYv_eq E.
      rewrite EX EY /rho /tco /= E /= !intr_eq0 !clr_den.
      do 2 (split; first done).
      split; [ exact: (clr_nz Hx) | split; [ exact: (clr_nz Hy) | exact: Hc ] ].
    Qed.

    Lemma P_rho : Tv rho (tapp0 s_one) = pt_rat (Pgen D).
    Proof using HS HWF. by rewrite Tv_ev pt_rat_id. Qed.

    Lemma AddSem_rho a a' : AddSem rho a a'.
    Proof using HS HWF.
      have HA : ADDrel (Tv rho a) (Tv rho a') (Tv rho (tadd a a')).
      { rewrite !Tv_ev /mulP /tadd /= mulrDl; exact: (E1 HS). }
      rewrite /AddSem /rho.
      case: (eqVneq (ev a) 0) => Ha; first by left; rewrite Ha.
      case: (eqVneq (ev a') 0) => Ha'; first by right; left; rewrite Ha'.
      right; right.
      have Ea : Tv rho a = Some (Xv rho a, Yv rho a) by rewrite /Tv /rho intr_eq0 (negbTE Ha).
      have Ea' : Tv rho a' = Some (Xv rho a', Yv rho a') by rewrite /Tv /rho intr_eq0 (negbTE Ha').
      move: HA; rewrite Ea Ea' -intrD.
      case: (eqVneq (ev a + ev a') 0) => Hs.
      - have E0 : Tv rho (tadd a a') = None by rewrite /Tv /rho /= intr_eq0 Hs eqxx.
        rewrite E0 /= => [] [ [ HX [ HY _ ] ] | [ ? [ ? [ ? _ ] ] ] ] //.
        left; rewrite Hs; split => //; split => //; by rewrite HY opprK.
      - have E0 : Tv rho (tadd a a') = Some (Xv rho (tadd a a'), Yv rho (tadd a a')).
        { by rewrite /Tv /rho /= intr_eq0 (negbTE Hs). }
        rewrite E0 => H; right; split => //; by rewrite intr_eq0.
    Qed.

    Lemma QvC_some t k : ev t != 0 -> (1 <= k)%N -> (k <= fd_m D)%N ->
      mulQ D (k%:Z * ev t) = Some (QvC rho D t k).
    Proof using HS HWF.
      move=> Ht Hk1 Hk2; rewrite /QvC; case: ifP => Hk.
      - have Hn : k%:Z * ev t != 0 by rewrite mulf_neq0 // -lt0n.
        have [ x [ y [ E _ ] ] ] := mulQ_some Hn.
        by rewrite /rho /tch /= E /= !clr_spec.
      - have Ek : k = fd_m D by apply/eqP; rewrite eqn_leq Hk2 leqNgt Hk.
        have := Tv_ev t; rewrite /Tv /rho intr_eq0 (negbTE Ht) /mulP => ->.
        by rewrite Ek mulrC.
    Qed.

    Lemma ChainSem_rho t : ChainSem rho D t.
    Proof using HS HWF.
      rewrite /ChainSem; case: (eqVneq (ev t) 0) => Ht; [ by left; rewrite /rho Ht | right ].
      have Hm := wf_m HWF.
      split; [ | split ].
      - move=> k Hk1 Hk2.
        have Hn : k%:Z * ev t != 0 by rewrite mulf_neq0 // -lt0n.
        have [ x [ y [ E _ ] ] ] := mulQ_some Hn.
        by rewrite /rho /tch /= E /= !intr_eq0 !clr_den.
      - have := QvC_some Ht (isT : (1 <= 1)%N) Hm; rewrite mul1r.
        have [ x [ y [ E [ _ [ _ Hc ] ] ] ] ] := mulQ_some Ht.
        by rewrite E => [] [] <-.
      - move=> k Hk1 Hk2.
        have := (E1 HS) (k%:Z * ev t) (ev t).
        rewrite (QvC_some Ht Hk1 (ltnW Hk2)).
        have := QvC_some Ht (isT : (1 <= 1)%N) Hm; rewrite mul1r => ->.
        have -> : k%:Z * ev t + ev t = k.+1%:Z * ev t by rewrite intS mulrDl mul1r addrC.
        by rewrite (QvC_some Ht (isT : (1 <= k.+1)%N) Hk2).
    Qed.

    Lemma sqrt2_rho A a : rho a = 0 \/ rho A * rho A != 2%:R * (rho a * rho a).
    Proof.
      case: (eqVneq (rho a) 0) => Ha; [ by left | right ].
      apply/eqP => E; apply: (@rat_Z0 (rho A / rho a)).
      by rewrite mulrACA -invfM E mulfK // mulf_neq0.
    Qed.

  End eval.

  (** ** Specifications of the table entries *)

  Definition icast (w : wcomp -> int) : wcomp -> rat := fun c => (w c)%:~R.

  (* the unary Skolem values at (K, A): from a witness of HCov *)
  Definition Spec1 (K : nat) (A : int) (w : rep1 -> int) : Prop :=
    (1 <= K)%N -> exists W : RepWit1, RepSpec D K A W
      /\ rw_u1 W = w r_u1 /\ rw_u2 W = w r_u2 /\ rw_v W = w r_v
      /\ forall j, rw_r W j = w (r_r j) /\ rw_B W j = w (r_B j)
          /\ w (r_B j) * w (r_B j) - 2 = w (r_r j) * w (r_wB j)
          /\ 2 * w (r_B j) * w (r_iota' j) - 1 = w (r_r j) * w (r_kappa' j)
          /\ forall s, rw_h W j s = w (r_h j s) /\ rw_j0 W j s = w (r_j0 j s)
              /\ FormalR false (w (r_r j))%:~R (w (r_B j))%:~R s (mulP D (w (r_h j s)))
                         (icast (w \o r_W1 j s tg_fh))
              /\ FormalR true (w (r_r j))%:~R (w (r_B j))%:~R s (mulP D (w (r_j0 j s)))
                         (icast (w \o r_W1 j s tg_fj0)).

  (* the binary Skolem values at (K, A, a), relative to the unary ones *)
  Definition Spec2 (K : nat) (A a : int) (w : rep1 -> int) (w2 : rep2 -> int) : Prop :=
    (1 <= K)%N -> forall j,
         (a = w (r_r j) * w2 (r_fz j) \/ a * w2 (r_fy j) - 1 = w (r_r j) * w2 (r_fz' j))
      /\ forall s,
           FormalR false (w (r_r j))%:~R (w (r_B j))%:~R s (mulP D (w (r_h j s) * a))
                   (icast (w2 \o r_W2 j s tg_fha))
        /\ LOCv K (w (r_r j))%:~R (w (r_B j))%:~R s
                (ellK false K (zpar false (mulP D (w (r_h j s) * a)))
                   / ellK false K (zpar false (mulP D (w (r_h j s)))) - qe_of a%:~R)
                (icast (w2 \o r_W2 j s tg_prim))
        /\ FormalR true (w (r_r j))%:~R (w (r_B j))%:~R s (mulP D ((w (r_h j s) - 4) * a))
                   (icast (w2 \o r_W2 j s tg_fh4a))
        /\ LOCv K (w (r_r j))%:~R (w (r_B j))%:~R s
                (zpar true (mulP D ((w (r_h j s) - 4) * a)) / zpar true (mulP D (w (r_j0 j s))))
                (icast (w2 \o r_W2 j s tg_alt)).

  (** ** Existence of entries *)

  Lemma LOCv_ext i (r B : rat) s alpha (w w' : wcomp -> rat) :
    LOCv i r B s alpha w -> (forall c, w c = w' c) -> LOCv i r B s alpha w'.
  Proof. by rewrite /LOCv => H E; rewrite -!E. Qed.

  Lemma FormalR_ext sg (r B : rat) s p (w w' : wcomp -> rat) :
    FormalR sg r B s p w -> (forall c, w c = w' c) -> FormalR sg r B s p w'.
  Proof. case: p => [ [ x y ] | ] //= H E; exact: LOCv_ext H E. Qed.

  Lemma LocZ_R i r B s alpha : LocZ i r B s alpha ->
    exists w : wcomp -> int, LOCv i r%:~R B%:~R s alpha (icast w).
  Proof.
    case=> X0 [ X1 [ Y0 [ Y1 [ io [ ka [ H1 H2 ] ] ] ] ] ].
    exists (fun c => match c with wX0 => X0 | wX1 => X1 | wY0 => Y0 | wY1 => Y1
                             | wiota => io | wkappa => ka end).
    rewrite /LOCv /icast /=; split.
    - by rewrite H1 /qe_of -qe_intE.
    - move: (congr1 (fun z : int => z%:~R : rat) H2) => /=.
      by rewrite !(intrB, intrD, intrM).
  Qed.

  Lemma FormalZ_R sg r B s p : FormalZ sg r B s p ->
    exists w : wcomp -> int, FormalR sg r%:~R B%:~R s p (icast w).
  Proof.
    case: p => [ [ x y ] | ] /=; last by exists (fun _ => 0).
    exact: LocZ_R.
  Qed.

  Lemma Spec1_exists K A : exists w, Spec1 K A w.
  Proof using HS.
    case: (leqP 1 K) => HK; last by exists (fun _ => 0); rewrite /Spec1 leqNgt HK.
    have [ W HW ] := HCov HS A HK.
    have Hj : forall j, exists y : int * int * int * (sgn -> wcomp -> int) * (sgn -> wcomp -> int),
        rw_B W j * rw_B W j - 2 = rw_r W j * y.1.1.1.1
     /\ 2 * rw_B W j * y.1.1.1.2 - 1 = rw_r W j * y.1.1.2
     /\ forall s, FormalR false (rw_r W j)%:~R (rw_B W j)%:~R s (mulP D (rw_h W j s)) (icast (y.1.2 s))
               /\ FormalR true (rw_r W j)%:~R (rw_B W j)%:~R s (mulP D (rw_j0 W j s)) (icast (y.2 s)).
    { move=> j; have [ _ [ _ [ _ [ Hr0 [ Hpr [ HrK [ [ wB EwB ] Hs ] ] ] ] ] ] ] := HW.2 j.
      have Hr2 : (2 < `|rw_r W j|)%N by apply: leq_ltn_trans HrK.
      have [ io [ ka Eio ] ] := bez2B Hpr Hr2 EwB.
      have [ gh Hgh ] : exists gh : sgn -> wcomp -> int, forall s,
          FormalR false (rw_r W j)%:~R (rw_B W j)%:~R s (mulP D (rw_h W j s)) (icast (gh s)).
      { apply: (@sgn_fchoice _ (fun s w => FormalR false (rw_r W j)%:~R (rw_B W j)%:~R s
                                             (mulP D (rw_h W j s)) (icast w))) => s.
        have [ _ [ _ HC ] ] := Hs s; have [ C1 _ ] := HC 0.
        exact: FormalZ_R C1. }
      have [ gj Hgj ] : exists gj : sgn -> wcomp -> int, forall s,
          FormalR true (rw_r W j)%:~R (rw_B W j)%:~R s (mulP D (rw_j0 W j s)) (icast (gj s)).
      { apply: (@sgn_fchoice _ (fun s w => FormalR true (rw_r W j)%:~R (rw_B W j)%:~R s
                                             (mulP D (rw_j0 W j s)) (icast w))) => s.
        have [ _ [ _ HC ] ] := Hs s.
        have [ _ [ _ [ _ [ _ [ C5 _ ] ] ] ] ] := HC 0.
        exact: FormalZ_R C5. }
      exists (wB, io, ka, gh, gj); split; [ by rewrite -EwB expr2 | split; first exact: Eio ].
      move=> s; split; [ exact: Hgh | exact: Hgj ]. }
    have [ g Hg ] := @mem13_fchoice _ (0, 0, 0, (fun _ _ => 0), (fun _ _ => 0)) _ Hj.
    exists (fun c => match c with
                     | r_u1 => rw_u1 W | r_u2 => rw_u2 W | r_v => rw_v W
                     | r_r j => rw_r W j | r_B j => rw_B W j
                     | r_wB j => (g j).1.1.1.1 | r_iota' j => (g j).1.1.1.2 | r_kappa' j => (g j).1.1.2
                     | r_h j s => rw_h W j s | r_j0 j s => rw_j0 W j s
                     | r_W1 j s tg_fh c => (g j).1.2 s c
                     | r_W1 j s tg_fj0 c => (g j).2 s c
                     end) => _.
    exists W; split; first exact: HW.
    do 3 (split; first done).
    move=> j; have [ H1 [ H2 H3 ] ] := Hg j.
    do 2 (split; first done); split; first exact: H1; split; first exact: H2.
    move=> s; do 2 (split; first done); exact: H3 s.
  Qed.

  Lemma Spec2_exists K A a w : Spec1 K A w -> exists w2, Spec2 K A a w w2.
  Proof.
    move=> S1; case: (leqP 1 K) => HK; last by exists (fun _ => 0); rewrite /Spec2 leqNgt HK.
    have [ W [ HW [ _ [ _ [ _ HWj ] ] ] ] ] := S1 HK.
    have Hj : forall j, exists y : int * int * int * (sgn -> Signature.tag2 -> wcomp -> int),
        (a = w (r_r j) * y.1.1.1 \/ a * y.1.1.2 - 1 = w (r_r j) * y.1.2)
     /\ forall s,
           FormalR false (w (r_r j))%:~R (w (r_B j))%:~R s (mulP D (w (r_h j s) * a)) (icast (y.2 s tg_fha))
        /\ LOCv K (w (r_r j))%:~R (w (r_B j))%:~R s
                (ellK false K (zpar false (mulP D (w (r_h j s) * a)))
                   / ellK false K (zpar false (mulP D (w (r_h j s)))) - qe_of a%:~R)
                (icast (y.2 s tg_prim))
        /\ FormalR true (w (r_r j))%:~R (w (r_B j))%:~R s (mulP D ((w (r_h j s) - 4) * a))
                   (icast (y.2 s tg_fh4a))
        /\ LOCv K (w (r_r j))%:~R (w (r_B j))%:~R s
                (zpar true (mulP D ((w (r_h j s) - 4) * a)) / zpar true (mulP D (w (r_j0 j s))))
                (icast (y.2 s tg_alt)).
    { move=> j; have [ Er [ EB [ _ [ _ Hs ] ] ] ] := HWj j.
      have [ _ [ _ [ _ [ Hr0 [ Hpr [ HrK [ _ Hrs ] ] ] ] ] ] ] := HW.2 j.
      have [ fz [ fy [ fz' Hf ] ] ] := fid_exists a Hpr.
      have Hs' : forall s, exists y : Signature.tag2 -> wcomp -> int,
           FormalR false (w (r_r j))%:~R (w (r_B j))%:~R s (mulP D (w (r_h j s) * a)) (icast (y tg_fha))
        /\ LOCv K (w (r_r j))%:~R (w (r_B j))%:~R s
                (ellK false K (zpar false (mulP D (w (r_h j s) * a)))
                   / ellK false K (zpar false (mulP D (w (r_h j s)))) - qe_of a%:~R)
                (icast (y tg_prim))
        /\ FormalR true (w (r_r j))%:~R (w (r_B j))%:~R s (mulP D ((w (r_h j s) - 4) * a))
                   (icast (y tg_fh4a))
        /\ LOCv K (w (r_r j))%:~R (w (r_B j))%:~R s
                (zpar true (mulP D ((w (r_h j s) - 4) * a)) / zpar true (mulP D (w (r_j0 j s))))
                (icast (y tg_alt)).
      { move=> s; have [ Eh [ Ej0 _ ] ] := Hs s.
        have [ _ [ _ HC ] ] := Hrs s.
        have [ _ [ C2 [ _ [ C4 [ _ [ C6 C7 ] ] ] ] ] ] := HC a.
        rewrite -Er -EB -Eh -Ej0.
        have [ w1 H1 ] := FormalZ_R C2.
        have [ w2 H2 ] := LocZ_R C4.
        have [ w3 H3 ] := FormalZ_R C6.
        have [ w4 H4 ] := LocZ_R C7.
        exists (fun tg => match tg with tg_fha => w1 | tg_prim => w2 | tg_fh4a => w3 | tg_alt => w4 end).
        split; first exact: H1.
        split; first by rewrite /qe_of -qe_intE.
        by split. }
      have [ g Hg ] := @sgn_fchoice _ _ Hs'.
      exists (fz, fy, fz', g); split; first by rewrite -Er.
      exact: Hg. }
    have [ g Hg ] := @mem13_fchoice _ (0, 0, 0, (fun _ _ _ => 0)) _ Hj.
    exists (fun c => match c with
                     | r_fz j => (g j).1.1.1 | r_fy j => (g j).1.1.2 | r_fz' j => (g j).1.2
                     | r_W2 j s tg c => (g j).2 s tg c
                     end) => _ j.
    exact: Hg j.
  Qed.

  (** ** The semantics of ax_rep K from the table entries *)

  Section rep.

    Variables (T : Tab) (K : nat) (A a : gterm) (w1 : rep1 -> int) (w2 : rep2 -> int).
    Hypothesis HK : (1 <= K)%N.
    Hypothesis H1 : t1 T K (ev T A) = Some w1.
    Hypothesis H2 : t2 T K (ev T A) (ev T a) = Some w2.
    Hypothesis S1 : Spec1 K (ev T A) w1.
    Hypothesis S2 : Spec2 K (ev T A) (ev T a) w1 w2.

    Lemma ev_s1 c : ev T (s1 K c A) = w1 c.
    Proof using H1. by rewrite /s1 /= H1. Qed.

    Lemma ev_s2 c : ev T (s2 K c A a) = w2 c.
    Proof using H2. by rewrite /s2 /= H2. Qed.

    Lemma rho_s1 c : rho T (s1 K c A) = (w1 c)%:~R.
    Proof using H1. by rewrite /rho ev_s1. Qed.

    Lemma rho_s2 c : rho T (s2 K c A a) = (w2 c)%:~R.
    Proof using H2. by rewrite /rho ev_s2. Qed.

    Lemma RepSem_rho : RepSem (rho T) D K A a.
    Proof using HS HWF HK H1 H2 S1 S2.
      have [ W [ [ HWv HWj ] [ Eu1 [ Eu2 [ Ev Hj ] ] ] ] ] := S1 HK.
      have Hj2 := S2 HK.
      rewrite /RepSem rho_s1 intr_eq0 -Ev; split; first exact: HWv.
      move=> j.
      have [ Hm [ He [ Hk [ Hr0 [ Hpr [ HrK [ _ Hs ] ] ] ] ] ] ] := HWj j.
      have [ Er [ EB [ EwB [ Eio Hjs ] ] ] ] := Hj j.
      have [ Hfid Hjs2 ] := Hj2 j.
      have Hr2 : (1 < `|w1 (r_r j)|)%N by rewrite -Er; apply: leq_ltn_trans HrK.
      rewrite /MemSem; cbv zeta; rewrite !rho_s1 !rho_s2.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ] ].
      - exists (rw_eps W j), (rw_k W j); do 2 (split; first done).
        have -> : memR (rho T) D K A j = (rw_mem D W (ev T A) j)%:~R.
        { case: j {Hm He Hk Hr0 Hpr HrK Hs Er EB EwB Eio Hjs Hfid Hjs2 Hr2} => [ | i b ];
            rewrite /memR /rw_mem ?rho_s1 ?Ev //.
          rewrite /fd_L /fd_Lint !(intrB, intrM); congr (_ * _ - _ * _).
          by case: i; rewrite /uR /rw_u ?rho_s1 ?Eu1 ?Eu2 ?Ev // !(intrB, intrM). }
        by rewrite Hm -Er !intrM.
      - by rewrite intr_eq0 -Er lt0r_neq0.
      - by rewrite -!intrM -[2%:R]/(2%:~R) -intrB EwB.
      - by rewrite -[2%:R]/(2%:~R) -!intrM -[1]/(1%:~R) -intrB Eio.
      - by rewrite /rho -intrM -[1]/(1%:~R) eqr_int mul_neq1.
      - case: Hfid => E; [ left | right ]; rewrite /rho; [ by rewrite E intrM | ].
        by rewrite -intrM -[1]/(1%:~R) -intrB E intrM.
      - move=> s; rewrite /BranchSem; cbv zeta; rewrite !rho_s1 !intr_eq0.
        have [ Eh [ Ej0 [ F1 F2 ] ] ] := Hjs s.
        have [ G1 [ G2 [ G3 G4 ] ] ] := Hjs2 s.
        have [ Hh [ Hj0 HC ] ] := Hs s.
        have [ _ [ _ [ C3 _ ] ] ] := HC 0.
        have Eha : ev T (tmul (s1 K (r_h j s) A) a) = w1 (r_h j s) * ev T a.
        { exact: (congr1 (fun z => z * ev T a) (ev_s1 _)). }
        have Eh4 : ev T (tmul (tsub (s1 K (r_h j s) A) (ti 4)) a) = (w1 (r_h j s) - 4) * ev T a.
        { have E4 : ev T (ti 4) = 4 by reflexivity.
          have -> : ev T (tmul (tsub (s1 K (r_h j s) A) (ti 4)) a)
                    = (ev T (s1 K (r_h j s) A) - ev T (ti 4)) * ev T a by [].
          by rewrite E4 ev_s1. }
        rewrite !Tv_ev Eha Eh4 !ev_s1.
        split; first by rewrite -Eh.
        split; first by rewrite -Ej0.
        split; first by apply: (FormalR_ext F1) => c; rewrite rho_s1.
        split; first by rewrite -Eh.
        split; first by apply: (FormalR_ext G1) => c; rewrite rho_s2.
        split; first by apply: (LOCv_ext G2) => c; rewrite rho_s2.
        split; first by apply: (FormalR_ext F2) => c; rewrite rho_s1.
        split; first by apply: (FormalR_ext G3) => c; rewrite rho_s2.
        by apply: (LOCv_ext G4) => c; rewrite rho_s2.
    Qed.

  End rep.

  (** ** Growing the tables *)

  Definition ext (T T' : Tab) : Prop :=
       (forall K v w, t1 T K v = Some w -> t1 T' K v = Some w)
    /\ (forall K v v' w, t2 T K v v' = Some w -> t2 T' K v v' = Some w).

  Lemma ext_refl T : ext T T.
  Proof. by split. Qed.

  Lemma ext_trans T1 T2 T3 : ext T1 T2 -> ext T2 T3 -> ext T1 T3.
  Proof.
    move=> [ A1 B1 ] [ A2 B2 ]; split.
    - by move=> K v w H; apply: A2; apply: A1.
    - by move=> K v v' w H; apply: B2; apply: B1.
  Qed.

  (* all table keys consulted by the evaluation of t are present *)
  Fixpoint okt (T : Tab) (t : gterm) : Prop :=
    match t with
    | tvar _ => True
    | tapp0 _ => True
    | tapp1 g s => okt T s /\ (if g is s_rep1 K _ then t1 T K (ev T s) <> None else True)
    | tapp2 g s s' =>
        okt T s /\ okt T s' /\
        (if g is s_rep2 K _ then t1 T K (ev T s) <> None /\ t2 T K (ev T s) (ev T s') <> None
         else True)
    end.

  Lemma ev_ext T T' t : ext T T' -> okt T t -> ev T' t = ev T t.
  Proof.
    move=> [ X1 X2 ]; elim: t => [ [] | g | g s IH | g s IH s' IH' ] //=.
    - case=> Hs Hg; rewrite IH //; case: g Hg => // K c.
      by case E: (t1 T K (ev T s)) => [ w | ] // _; rewrite (X1 _ _ _ E).
    - case=> Hs [ Hs' Hg ]; rewrite IH // IH' //; case: g Hg => // K c [ _ ].
      by case E: (t2 T K (ev T s) (ev T s')) => [ w | ] // _; rewrite (X2 _ _ _ _ E).
  Qed.

  Lemma okt_ext T T' t : ext T T' -> okt T t -> okt T' t.
  Proof.
    move=> HT; elim: t => [ [] | g | g s IH | g s IH s' IH' ] //=.
    - case=> Hs Hg; split; first exact: IH.
      case: g Hg => // K c; rewrite (ev_ext HT Hs).
      by case E: (t1 T K (ev T s)) => [ w | ] // _; rewrite (HT.1 _ _ _ E).
    - case=> Hs [ Hs' Hg ]; split; first exact: IH.
      split; first exact: IH'.
      case: g Hg => // K c; rewrite (ev_ext HT Hs) (ev_ext HT Hs').
      case=> H1 H2; split.
      + by case E: (t1 T K (ev T s)) H1 => [ w | ] // _; rewrite (HT.1 _ _ _ E).
      + by case E: (t2 T K (ev T s) (ev T s')) H2 => [ w | ] // _; rewrite (HT.2 _ _ _ _ E).
  Qed.

  Definition good (T : Tab) : Prop :=
       (forall K v w, t1 T K v = Some w -> Spec1 K v w)
    /\ (forall K v v' w2, t2 T K v v' = Some w2 -> exists w, t1 T K v = Some w /\ Spec2 K v v' w w2).

  Definition upd1 (T : Tab) K v w : Tab :=
    {| t1 := fun K' v' => if (K' == K) && (v' == v) then Some w else t1 T K' v';
       t2 := t2 T |}.

  Definition upd2 (T : Tab) K v v' w2 : Tab :=
    {| t1 := t1 T;
       t2 := fun K' u u' => if [&& K' == K, u == v & u' == v'] then Some w2 else t2 T K' u u' |}.

  Lemma ensure1 T K v : good T -> exists T', good T' /\ ext T T' /\ t1 T' K v <> None.
  Proof using HS.
    move=> [ G1 G2 ]; case E: (t1 T K v) => [ w | ].
    - by exists T; split; [ | split; [ exact: ext_refl | rewrite E ] ].
    - have [ w Hw ] := Spec1_exists K v.
      exists (upd1 T K v w); split; [ split | split; [ split | ] ].
      + move=> K' v' w' /=; case: andP => [ [ /eqP -> /eqP -> ] [] <- // | _ ]; exact: G1.
      + move=> K' u u' w2 /= /G2 [ w' [ H1 H2 ] ]; exists w'; split => //.
        case: andP => [ [ /eqP E1 /eqP E2 ] | _ ] //; by rewrite E1 E2 E in H1.
      + move=> K' v' w' /= H; case: andP => [ [ /eqP E1 /eqP E2 ] | _ ] //; by rewrite E1 E2 E in H.
      + by [].
      + by rewrite /= !eqxx.
  Qed.

  Lemma ensure2 T K v v' : good T -> t1 T K v <> None ->
    exists T', good T' /\ ext T T' /\ t2 T' K v v' <> None.
  Proof.
    move=> [ G1 G2 ] Hv; case E: (t2 T K v v') => [ w2 | ].
    - by exists T; split; [ | split; [ exact: ext_refl | rewrite E ] ].
    - case E1: (t1 T K v) Hv => [ w | ] // _.
      have [ w2 Hw2 ] := Spec2_exists v' (G1 _ _ _ E1).
      exists (upd2 T K v v' w2); split; [ split | split; [ split | ] ].
      + exact: G1.
      + move=> K' u u' w2' /=.
        case: and3P => [ [ /eqP -> /eqP -> /eqP -> ] [] <- | _ ]; [ by exists w | exact: G2 ].
      + by [].
      + move=> K' u u' w2' /= H.
        case: and3P => [ [ /eqP E1' /eqP E2' /eqP E3' ] | _ ] //; by rewrite E1' E2' E3' E in H.
      + by rewrite /= !eqxx.
  Qed.

  Definition T0 : Tab := {| t1 := fun _ _ => None; t2 := fun _ _ _ => None |}.

  Lemma good_T0 : good T0.
  Proof. by split. Qed.

  (* every term can be made ok by adding finitely many entries *)
  Lemma okt_build t : forall T, good T -> exists T', good T' /\ ext T T' /\ okt T' t.
  Proof using HS.
    elim: t => [ [] | g | g s IH | g s IH s' IH' ] T HT.
    - by exists T; split; [ | split; [ exact: ext_refl | ] ].
    - have [ T1 [ G1 [ X1 O1 ] ] ] := IH T HT.
      case: g => [ | c | k c | K c ].
      1-3: by exists T1; split; [ | split ].
      have [ T2 [ G2 [ X2 N2 ] ] ] := ensure1 K (ev T1 s) G1.
      exists T2; split; first done; split; first exact: ext_trans X1 X2.
      split; first exact: okt_ext X2 O1.
      by rewrite (ev_ext X2 O1).
    - have [ T1 [ G1 [ X1 O1 ] ] ] := IH T HT.
      have [ T2 [ G2 [ X2 O2 ] ] ] := IH' T1 G1.
      have O1' := okt_ext X2 O1.
      case: g => [ | | K c ].
      1-2: by exists T2; split; [ | split; [ exact: ext_trans X1 X2 | ] ].
      have [ T3 [ G3 [ X3 N3 ] ] ] := ensure1 K (ev T2 s) G2.
      have N3' : t1 T3 K (ev T3 s) <> None by rewrite (ev_ext X3 O1').
      have [ T4 [ G4 [ X4 N4 ] ] ] := ensure2 (ev T3 s') G3 N3'.
      have X34 := ext_trans X3 X4.
      exists T4; split; first done; split; first exact: ext_trans (ext_trans X1 X2) X34.
      split; first exact: okt_ext X34 O1'.
      split; first exact: okt_ext X34 O2.
      rewrite (ev_ext X4 (okt_ext X3 O1')) (ev_ext X4 (okt_ext X3 O2)); split => //.
      by case E: (t1 T3 K (ev T3 s)) N3' => [ w | ] // _; rewrite (X4.1 _ _ _ E).
  Qed.

  Lemma okt_list (l : list gterm) : exists T, good T /\ forall t, List.In t l -> okt T t.
  Proof using HS.
    elim: l => [ | t l [ T [ HT Hl ] ] ]; first by exists T0; split; [ exact: good_T0 | ].
    have [ T' [ G' [ X' O' ] ] ] := okt_build t HT.
    exists T'; split => // u [ <- // | Hu ]; exact: okt_ext X' (Hl u Hu).
  Qed.

  (** ** Every test succeeds *)

  Variable f : H10Z_PROBLEM.
  Hypothesis Hroot :
    dp_evalR (fun v => ((zc (pos2nat v))%:~R : rat)) (fun _ => 0) (projT2 f) = 0.

  (* the terms whose keys the rep instances of test N consult *)
  Definition reqs (N : nat) : list gterm :=
    List.flat_map (fun K =>
      List.flat_map (fun A => List.map (fun a => tapp2 (s_rep2 K (r_fz mem_v)) A a) (gterm_list N))
                    (gterm_list N)) (iota 1 N).

  Lemma test_sat N : qf_sat (projT2 (test D f N)).
  Proof using HS HWF Hroot.
    have [ T [ HT Hok ] ] := okt_list (reqs N).
    apply/test_spec; apply: (testf_write (rho := rho T)).
    - move=> u _; exact: rho_ring.
    - move=> u u' _ _; exact: rho_fun.
    - move=> phi /List.in_flat_map [ M [ HM /List.in_flat_map [ A [ HA /List.in_map_iff [ a [ <- Ha ] ] ] ] ] ].
      have Hring := rho_ring T.
      have Hc := coordOK_rho T.
      apply List.in_app_or in HM as [ HM | HM ];
        last apply List.in_map_iff in HM as (K & <- & HK).
      + case: HM => [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [] ] ] ] ] ] ].
        * exact/(inst_coord_iff Hring A a).
        * exact/(inst_P_iff D Hring A a (Hc _))/P_rho.
        * exact/(inst_add_iff Hring (Hc _) (Hc _) (Hc _))/AddSem_rho.
        * exact/(inst_chain_iff D Hring a (Hc A))/ChainSem_rho.
        * exact/(inst_sqrt2_iff Hring)/sqrt2_rho.
        * apply/(inst_root_iff Hring f A a); exact: Hroot.
      + have HK1 : (1 <= K)%N by move: HK => /In_mem; rewrite mem_iota => /andP [].
        apply/(inst_rep_iff D Hring K A a rat_Z0 Hc).
        have Hr : List.In (tapp2 (s_rep2 K (r_fz mem_v)) A a) (reqs N).
        { apply List.in_flat_map; exists K; split => //.
          apply List.in_flat_map; exists A; split => //.
          exact: (List.in_map (fun a => tapp2 (s_rep2 K (r_fz mem_v)) A a)). }
        have [ _ [ _ [ N1 N2 ] ] ] := Hok _ Hr.
        case E1: (t1 T K (ev T A)) N1 => [ w1 | ] // _.
        case E2: (t2 T K (ev T A) (ev T a)) N2 => [ w2 | ] // _.
        have S1 := HT.1 _ _ _ E1.
        have [ w1' [ E1' S2 ] ] := HT.2 _ _ _ _ E2.
        move: S2; rewrite E1 in E1'; case: E1' => <- S2.
        exact: RepSem_rho HK1 E1 E2 S1 S2.
    - move=> u _; exact: rho_Phi.
  Qed.

End standard_model.

Lemma dp_evalR_ext' {V P : Set} (φ φ' : V -> rat) (p : dio_polynomial V P) :
  (forall v, φ v = φ' v) -> dp_evalR φ (fun _ => 0) p = dp_evalR φ' (fun _ => 0) p.
Proof. move=> h; elim: p => [ c | v | i | [] p Hp q Hq ] //=; by rewrite ?h ?Hp ?Hq. Qed.

(** * Soundness of the finite tests *)

(* an integer zero of f makes every finite test succeed *)
Theorem tests_sound (D : FixedData) (HWF : FixedWF D) (HS : StdHyps D)
  n (f : dio_polynomial (pos n) (pos 0)) :
  H10Z (existT _ n f) -> forall N, qf_sat (projT2 (test D (existT _ n f) N)).
Proof.
  move=> /= [ Φ HΦ ] N.
  pose zc (i : nat) : int := Z_to_R (zcst Φ i).
  apply: (@test_sat D HWF HS zc (existT _ n f)) => /=.
  rewrite (@dp_evalR_ext' _ _ _ (fun v => Z_to_R (Φ v))).
  - by move=> v; rewrite /zc Z_to_R_intr zcst_pos.
  - by rewrite dp_evalR_rat HΦ /Z_to_R /= subrr.
Qed.
