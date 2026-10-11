(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2E, task P14b-iv-A: the fixed data with an ABSTRACT base point
   (PLAN.md, log 2026-10-10: O_rank is obtained from finite generation and
   the structure theorem, with an abstract generator G as P0).

   - [mkDataG P0 C S Hb c Kset Nh Ch]: as [mkData] (ExplicitData.v), but
     with [fd_P0 := P0]; [mkData_is_mkDataG].
   - the P0-independent conversions of PaperInputs.v for [mkDataG]
     ([mkDataG_WF], [HeightBound_O_height_G], [HeightThm_O_height_G],
     [HeightThm_hei_enlarge_G], [PP1_mkDataG], [PatternBody_spec_G],
     [PrimePattern_Kset_G]);
   - [HCov_thm_G]: the field HCov for [mkDataG]. HCov.v's final section
     [integer_tests] is stated for [mkData] and uses the explicit point
     only through [mkData_P0_on_curve]; it is copied here verbatim with
     that call replaced by a hypothesis [hP0 : on_curve P0]. The generic
     lemmas of HCov.v ([kernel_countF], [crt_h], [kern_red*],
     [kern_FormalZ*], [val_LocZw], [zpar]-facts) are reused.
   - the height constants [NhG P0], [ChG P0] (HeightLower.v's [HL_Nh],
     [HL_Ch], which depend only on P0, [HL_P0]);
   - Section [assembly_G]: for an abstract point P0 on the curve which is
     nontorsion, [FixedWF_G], [StdHyps_G], all fields of OrdHyps except
     O_rank ([O_F1_G], [O_F2_G], [O_height_G], [O_HS_G], [O_HL_G],
     [O_PP2_G]) and [OrdHyps_G : rank_one_stmt P0 -> OrdHyps D].
   - [rank_one_stmt P0]: the field O_rank, which only involves fd_m = 2
     and fd_P0 ([O_rank_of_rank_one]). What P14b-iv-B must deliver is
     [exists G, on_curve G /\ nontorsion G /\ rank_one_stmt G].

   No axioms. *)

From Stdlib Require Import ZArith Lia List.

From HB Require Import structures.
From mathcomp Require Import boot order algebra fingroup cyclic.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData ExplicitData
                 RatVal OrdHeights PoleParity HeightLower KernelReduction FormalLog.
From Undecidability.H10.Rational
  Require Import PaperInputs OrdinaryFacts OrdPlaces OrdBridges GroupLaw HCov.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

(** * 1. The data with an abstract base point *)

Definition mkDataG (P0 : qe rat * qe rat) (C : i4 -> rat) (S : seq nat) (Hb c : nat)
  (Kset : seq nat) (Nh Ch : nat) : FixedData :=
  {| fd_m := m0; fd_P0 := P0; fd_C := C; fd_S := S; fd_Hb := Hb; fd_c := c;
     fd_Kset := Kset; fd_SE := SE0; fd_PhiL := PhiL0; fd_Nh := Nh; fd_Ch := Ch |}.

Lemma mkData_is_mkDataG C S Hb c Kset Nh Ch :
  mkData C S Hb c Kset Nh Ch = mkDataG Q0 C S Hb c Kset Nh Ch.
Proof. reflexivity. Qed.

(** * 2. The multiples of a point, without FixedData; O_rank and nontorsion *)

Definition mulGn (P0 : qe rat * qe rat) (k : nat) : pt rat := iter k (ec_add (Some P0)) None.

Definition mulG (P0 : qe rat * qe rat) (n : int) : pt rat :=
  match n with
  | Posz k => mulGn P0 k
  | Negz k => pt_neg (mulGn P0 k.+1)
  end.

(* P0 is nontorsion; literally the premise of KernelReduction.E2_of_nontorsion *)
Definition nontorsion (P0 : qe rat * qe rat) : Prop :=
  forall n : int, n != 0 -> mulG P0 n <> None.

(* the field O_rank for fd_m = 2: 2 E(F) is contained in Z (2 P0).
   With E(F) = Z G (+) E[2] and P0 := G this is true. *)
Definition rank_one_stmt (P0 : qe rat * qe rat) : Prop :=
  forall Q1 Q2 : qe rat * qe rat,
    on_curve Q1 -> ADDrel (Some Q1) (Some Q1) (Some Q2) ->
    exists n : int, mulG P0 (n * (2%N)%:Z) = Some Q2.

(* the field O_rank of OrdHyps, verbatim, for a FixedData D *)
Definition O_rank_stmt (D : FixedData) : Prop :=
  forall Q : nat -> qe rat * qe rat,
    on_curve (Q 1%N) ->
    (forall k, (1 <= k)%N -> (k < fd_m D)%N -> ADDrel (Some (Q k)) (Some (Q 1%N)) (Some (Q k.+1))) ->
    exists n : int, mulP D n = Some (Q (fd_m D)).

Section mulG_facts.

  Variables (P0 : qe rat * qe rat) (C : i4 -> rat) (S : seq nat) (Hb c : nat)
            (Kset : seq nat) (Nh Ch : nat).
  Local Abbreviation D := (mkDataG P0 C S Hb c Kset Nh Ch).

  Lemma mulQ_mkDataG (n : int) : mulQ D n = mulG P0 n.
  Proof. by case: n. Qed.

  Lemma mulP_mkDataG (n : int) : mulP D n = mulG P0 (n * (2%N)%:Z).
  Proof. exact: mulQ_mkDataG. Qed.

  Lemma nontorsion_mkDataG : nontorsion P0 -> forall n : int, n != 0 -> mulQ D n <> None.
  Proof. by move=> H n Hn; rewrite mulQ_mkDataG; exact: H. Qed.

  (* O_rank only depends on P0 (and fd_m = 2) *)
  Lemma O_rank_of_rank_one : rank_one_stmt P0 -> O_rank_stmt D.
  Proof.
    move=> H Q HQ Hch.
    have [n Hn] := H (Q 1%N) (Q 2%N) HQ (Hch 1%N isT isT).
    by exists n; rewrite mulP_mkDataG.
  Qed.

End mulG_facts.

(** * 3. The P0-independent conversions of PaperInputs.v *)

Section mkDataG_conv.

  Variables (P0 : qe rat * qe rat) (C : i4 -> rat) (S : seq nat) (Hb c : nat)
            (Kset : seq nat) (Nh Ch : nat).
  Local Abbreviation D := (mkDataG P0 C S Hb c Kset Nh Ch).

  Lemma mkDataG_WF :
    (forall i j, C i = C j -> i = j) -> all prime S -> (0 < Hb)%N -> (0 < c)%N ->
    all (fun k => 0 < k)%N Kset -> (0 < Nh)%N ->
    FixedWF D.
  Proof.
    move=> HC HS HHb Hc HK HNh; constructor;
      first [ exact: m0_pos | exact: PhiL0_nonempty | exact: PhiL0_wf | exact: SE0_prime
            | (by move=> k hk; exact: (allP HK)) | assumption ].
  Qed.

  Lemma MSC_mkDataG S' s : MS D S' s = MSC C S' s.
  Proof. by []. Qed.

  Lemma HeightBound_O_height_G : HeightBound C S Hb c -> O_height_stmt D.
  Proof. by move=> H s Hs; rewrite MSC_mkDataG; exact: H. Qed.

  Lemma HeightBound_hei_enlarge_G : FixedWF D -> HeightBound C S Hb c -> hei_enlarge_ord D.
  Proof. by move=> HWF H; apply: (hei_enlarge_thm HWF); exact: HeightBound_O_height_G. Qed.

  Lemma PP1_mkDataG : PP1_L0 -> forall b : int, Phi_holdsR (fd_PhiL D) (b%:~R : rat).
  Proof. by move=> H b; apply/Phi_holds_iff; exact: H. Qed.

  Lemma memC_mkDataG (W : PatWit) A j :
    memC C A (pw_u1 W) (pw_u2 W) (pw_v W) j = pw_mem D W A j.
  Proof. by case: j. Qed.

End mkDataG_conv.

Lemma HeightThm_O_height_G (C : i4 -> rat) (S : seq nat) (Hb c : nat) :
  HeightBound C S Hb c ->
  forall P0 Kset Nh Ch, O_height_stmt (mkDataG P0 C S Hb c Kset Nh Ch).
Proof. by move=> H P0 Kset Nh Ch; exact: HeightBound_O_height_G. Qed.

Lemma HeightThm_hei_enlarge_G (C : i4 -> rat) (S : seq nat) (Hb c : nat) :
  HeightBound C S Hb c ->
  forall P0 Kset Nh Ch, FixedWF (mkDataG P0 C S Hb c Kset Nh Ch) ->
    hei_enlarge_ord (mkDataG P0 C S Hb c Kset Nh Ch).
Proof. by move=> H P0 Kset Nh Ch HWF; exact: HeightBound_hei_enlarge_G. Qed.

Lemma PatternBody_spec_G (C : i4 -> rat) (Kset : seq nat) :
  PatternBody C Kset ->
  forall P0 S Hb c Nh Ch (A : int) (Y : nat),
    exists W : PatWit, PatternSpec (mkDataG P0 C S Hb c Kset Nh Ch) A Y W.
Proof.
  move=> HP P0 S Hb c Nh Ch A Y.
  (* PatternSpec only involves fd_C and fd_Kset, shared with mkData *)
  have [W HW] := PatternBody_spec HP S Hb c Nh Ch A Y.
  exists W; case: HW => H1 H2 H3 H4 H5; split => //.
Qed.

Lemma PrimePattern_Kset_G : PrimePattern ->
  forall C : i4 -> rat, (forall i j, C i = C j -> i = j) ->
  exists Kset : seq nat, all (fun k => 0 < k)%N Kset /\
    forall P0 S Hb c Nh Ch (A : int) (Y : nat),
      exists W : PatWit, PatternSpec (mkDataG P0 C S Hb c Kset Nh Ch) A Y W.
Proof.
  move=> HP C HC; have [Kset [HK HB]] := HP C HC.
  by exists Kset; split => //; exact: PatternBody_spec_G.
Qed.

(** * 4. HCov for mkDataG

    Copy of HCov.v, Section [integer_tests] and [HCov_thm], with [mkData]
    replaced by [mkDataG P0] and [mkData_P0_on_curve] by [hP0]. *)

Section integer_tests_G.

  Variables (P0 : qe rat * qe rat) (C : i4 -> rat) (S : seq nat) (Hb c : nat)
            (Kset : seq nat) (Nh Ch : nat).
  Local Abbreviation D := (mkDataG P0 C S Hb c Kset Nh Ch).

  Hypothesis hP0 : on_curve P0.
  Hypothesis HF1 : O_F1_stmt D.
  Hypothesis HF2 : O_F2_stmt D.

  Lemma mulP_mkG (n : int) : mulP D n = mulQ D (n * (2%N)%:Z).
  Proof. by []. Qed.

  Lemma zpar_mulP0_G (sg : bool) : zpar sg (mulP D 0) = 0.
  Proof. by rewrite mulP_mkG mul0r. Qed.

  (* Cor pri:integer-tests at one place sqrt2 |-> s B above r *)
  Theorem integer_tests_G (K r : nat) (B : int) (s : sgn) :
    (1 <= K)%N -> prime r -> (K.+1 < r)%N -> (7 < r)%N ->
    (exists wB : int, B ^+ 2 - 2 = r%:Z * wB) ->
    (gcdn (cntE (Z.of_nat r) (int_to_Z (sgnz s * B))) (cntE (Z.of_nat r) (- int_to_Z (sgnz s * B))) %| 4)%N ->
    ~~ (r %| cntE (Z.of_nat r) (int_to_Z (sgnz s * B)) * cntE (Z.of_nat r) (- int_to_Z (sgnz s * B)))%N ->
    exists h j0 : int, h != 0 /\ j0 != 0 /\ forall a : int, RepConds D K r%:Z B s h j0 a.
  Proof.
    move=> HK Hr Hrk Hr7 HB Hg Hnd.
    have r2 : r != 2%N by apply/eqP => E; move: Hr7; rewrite E.
    have r7 : r != 7%N by apply/eqP => E; move: Hr7; rewrite E.
    set cc := sgnz s * B.
    set v := ovP (wsplit r B s).
    have Hv : is_place_above v r := wsplit_place Hr r2 HB s.
    have cpl : 1 <= v (tcq cc) := wsplit_root Hr r2 HB s.
    have crt : (r%:Z %| cc ^+ 2 - 2)%Z := c_root_of HB s.
    set v' := fun x => v (qe_conj x).
    have Hv' : is_place_above v' r := conj_place Hv.
    have cpl' : 1 <= v' (tcq (- cc)) by rewrite /v' conj_tcq (vbN Hv) ?tcq_neq0.
    have crt' : (r%:Z %| (- cc) ^+ 2 - 2)%Z by rewrite sqrrN.
    have hP0' : on_curve (fd_P0 D) := hP0.
    set d1 := cntE (Z.of_nat r) (int_to_Z cc) in Hg Hnd.
    set d2 := cntE (Z.of_nat r) (- int_to_Z cc) in Hg Hnd.
    have K1 : forall n : int, (d1 %| `|n|)%N -> kern v (mulQ D n).
    { exact: (kernel_countF Hr r2 r7 Hv crt cpl hP0'). }
    have K2 : forall n : int, (d2 %| `|n|)%N -> kern v' (mulQ D n).
    { move=> n Hn; apply: (kernel_countF Hr r2 r7 Hv' crt' cpl' hP0'); by rewrite iz_opp. }
    have d1p : (0 < d1)%N by [].
    have d2p : (0 < d2)%N by [].
    have nd1 : ~~ (r %| d1)%N by apply: contra Hnd => H; apply: dvdn_mulr.
    have nd2 : ~~ (r %| d2)%N by apply: contra Hnd => H; apply: dvdn_mull.
    have [ h [ nh [ Dh Dh4 ] ] ] := crt_h K Hr d1p d2p Hg nd1.
    have D2h4 : (d2%:Z %| h - 4)%Z.
    { apply: dvdz_trans Dh4; rewrite PoszM; apply: dvdz_mulr; exact: dvdzz. }
    have RKh4 : (r%:Z ^+ K %| h - 4)%Z.
    { have E : (r ^ K)%N%:Z = r%:Z ^+ K by rewrite -!natz natrX.
      apply: dvdz_trans Dh4; rewrite PoszM E; apply: dvdz_mull; exact: dvdzz. }
    have Kv : forall n : int, (d1%:Z %| n)%Z -> kern v (mulP D n).
    { move=> n Hn; rewrite mulP_mkG; apply: K1; rewrite abszM; apply: dvdn_mulr; by move: Hn; rewrite dvdzE. }
    have Kv' : forall n : int, (d2%:Z %| n)%Z -> kern v' (mulP D n).
    { move=> n Hn; rewrite mulP_mkG; apply: K2; rewrite abszM; apply: dvdn_mulr; by move: Hn; rewrite dvdzE. }
    have r_SE : r \notin fd_SE D by rewrite /= !inE negb_or r2 r7.
    exists h, d2%:Z; split => //; split; first by rewrite eqz_nat -lt0n.
    move=> a.
    have Dha : (d1%:Z %| h * a)%Z by apply: dvdz_mulr.
    have Dh4a : (d2%:Z %| (h - 4) * a)%Z by apply: dvdz_mulr.
    have Hcond : h * a = 0 \/ vqr r h%:~R <= vqr r (h * a)%:~R.
    { case: (eqVneq a 0) => [ -> | na ]; first by left; rewrite mulr0.
      right; rewrite !vqr_int abszM lognM ?absz_gt0 //= lez_nat; exact: leq_addr. }
    have [ Hell Hlog ] := HF2 HK Hr r_SE Hrk Hv nh (kern_red (Kv _ Dha)) (kern_red (Kv _ Dh)) Hcond.
    have Eq : qe_of ((h * a)%:~R / h%:~R) = a%:~R :> qe rat.
    { have nh' : (h%:~R : rat) != 0 by rewrite intr_eq0.
      by rewrite intrM mulrAC divff // mul1r qe_intE. }
    move: Hlog; cbv zeta; rewrite Eq => Hlog.
    have nd2' : d2%:Z != 0 by rewrite eqz_nat -lt0n.
    have L7 : LocZ K r%:Z B s (zpar true (mulP D ((h - 4) * a)) / zpar true (mulP D d2%:Z)).
    { set z1 := zpar true (mulP D ((h - 4) * a)); set z2 := zpar true (mulP D d2%:Z).
      apply: (@val_LocZw r B s Hr r2 HB); case: (eqVneq (z1 / z2) 0) => [ -> | nal ]; first by left.
      right.
      have nz1 : z1 != 0 by apply: contraNneq nal => ->; rewrite mul0r.
      have nz2 : z2 != 0 by apply: contraNneq nal => ->; rewrite invr0 mulr0.
      have [ E0 | E1 ] := HF1 Hr r_SE Hv nd2' (kern_red_conj (Kv' _ Dh4a))
                                 (kern_red_conj (Kv' _ (dvdzz _))).
      - by move: nz1; rewrite /z1 E0 zpar_mulP0_G eqxx.
      - have nn : (h - 4) * a != 0 by apply: contraNneq nz1 => E; rewrite /z1 E zpar_mulP0_G.
        have [ ni Ei ] := vb_inv Hv nz2.
        rewrite -/v (proj1 Hv _ _ nz1 ni) Ei.
        have -> : v z1 - v z2 = vqr r ((h - 4) * a)%:~R - vqr r (d2%:Z)%:~R by exact: E1.
        rewrite !vqr_int /= (logn_ndvd nd2) subr0 lez_nat.
        have n4 : h - 4 != 0 by apply: contraNneq nn => ->; rewrite mul0r.
        have na : a != 0 by apply: contraNneq nn => ->; rewrite mulr0.
        rewrite abszM lognM ?absz_gt0 //; apply: leq_trans (leq_addr _ _).
        rewrite -pfactor_dvdn ?absz_gt0 //.
        by move: RKh4; rewrite dvdzE abszX. }
    split; first exact: (@kern_FormalZ r B s Hr r2 HB _ (Kv _ Dh)).
    split; first exact: (@kern_FormalZ r B s Hr r2 HB _ (Kv _ Dha)).
    split; first exact: Hell.
    split; first exact: (@val_LocZw r B s Hr r2 HB K _ Hlog).
    split; first exact: (@kern_FormalZ_conj r B s Hr r2 HB _ (Kv' _ (dvdzz _))).
    split; first exact: (@kern_FormalZ_conj r B s Hr r2 HB _ (Kv' _ Dh4a)).
    exact: L7.
  Qed.

End integer_tests_G.

(* the field HCov of StdHyps for mkDataG (copy of HCov.HCov_thm) *)
Theorem HCov_thm_G (P0 : qe rat * qe rat) (C : i4 -> rat) (S : seq nat) (Hb c : nat)
  (Kset : seq nat) (Nh Ch : nat) :
  let D := mkDataG P0 C S Hb c Kset Nh Ch in
  on_curve P0 -> O_F1_stmt D -> O_F2_stmt D ->
  (forall (A : int) (Y : nat), exists W : PatWit, PatternSpec D A Y W) ->
  forall (K : nat) (A : int), (1 <= K)%N -> exists W : RepWit1, RepSpec D K A W.
Proof.
  move=> D hP0 HF1 HF2 HP K A HK.
  have [ W HW ] := HP A K.+1.
  have [ B HB ] := pattern_B HW.
  have Hj : forall j, exists hj : (int * int) * (int * int),
      (hj.1.1 != 0 /\ hj.1.2 != 0 /\ forall a, RepConds D K (pw_r W j)%:Z (B j) sg_p hj.1.1 hj.1.2 a) /\
      (hj.2.1 != 0 /\ hj.2.2 != 0 /\ forall a, RepConds D K (pw_r W j)%:Z (B j) sg_m hj.2.1 hj.2.2 a).
  { move=> j.
    have Hr := ps_prime HW j.
    have [ wB HwB ] := HB j.
    have T : forall s : sgn, exists h j0 : int,
        h != 0 /\ j0 != 0 /\ forall a : int, RepConds D K (pw_r W j)%:Z (B j) s h j0 a.
    { move=> s; have [ Hg Hnd ] := pattern_prime_orders_sgn Hr s HwB.
      exact: (integer_tests_G hP0 HF1 HF2 HK (pattern_prime_prime Hr) (pattern_prime_gtY Hr)
                              (pattern_prime_gt7 Hr) (HB j) Hg Hnd). }
    have [ hp [ jp Hp ] ] := T sg_p; have [ hm [ jm Hm ] ] := T sg_m.
    by exists ((hp, jp), (hm, jm)). }
  have [ f Hf ] := mem13_choice Hj.
  exists (pw_ext W B (fun j s => if s is sg_p then (f j).1.1 else (f j).2.1)
                     (fun j s => if s is sg_p then (f j).1.2 else (f j).2.2)).
  apply: (RepSpec_of_pattern HW (leqnn _) HB).
  move=> j [] /=; [ exact: (proj1 (Hf j)) | exact: (proj2 (Hf j)) ].
Qed.

(** * 5. The height constants: they depend only on P0 (HeightLower.HL_P0) *)

Definition NhG (P0 : qe rat * qe rat) : nat := HL_Nh (mkDataG P0 (fun _ => 0) [::] 0 0 [::] 0 0).
Definition ChG (P0 : qe rat * qe rat) : nat := HL_Ch (mkDataG P0 (fun _ => 0) [::] 0 0 [::] 0 0).

Lemma NhG_ChG (P0 : qe rat * qe rat) C S Hb c Kset Nh Ch :
  HL_Nh (mkDataG P0 C S Hb c Kset Nh Ch) = NhG P0 /\
  HL_Ch (mkDataG P0 C S Hb c Kset Nh Ch) = ChG P0.
Proof. exact: HL_P0. Qed.

(** * 6. Assembly for an abstract point *)

Section assembly_G.

  Variable P0 : qe rat * qe rat.
  Hypothesis HP0 : on_curve P0.
  Hypothesis Hnt : nontorsion P0.

  Variables (C : i4 -> rat) (S : seq nat) (Hb c : nat) (Kset : seq nat).
  Hypothesis HC : forall i j, C i = C j -> i = j.
  Hypothesis HS : all prime S.
  Hypothesis HHb : (0 < Hb)%N.
  Hypothesis Hc : (0 < c)%N.
  Hypothesis HK : all (fun k => 0 < k)%N Kset.
  Hypothesis HH : HeightBound C S Hb c.
  Hypothesis HPat : PatternBody C Kset.
  Hypothesis HPP1 : PP1_L0.

  Local Abbreviation D := (mkDataG P0 C S Hb c Kset (NhG P0) (ChG P0)).

  Let mulQ_on_h : forall D : FixedData, on_curve (fd_P0 D) -> forall n : int, onp (mulQ D n) :=
    fun D0 H n => @mulQ_on D0 H n.
  Let mulQ_add_h : forall D : FixedData, on_curve (fd_P0 D) ->
      forall n n' : int, mulQ D (n + n') = ec_add (mulQ D n) (mulQ D n') :=
    fun D0 H => @mulQ_add D0 H.

  Let HP0D : on_curve (fd_P0 D) := HP0.

  Lemma E1_G : forall n n' : int, ADDrel (mulQ D n) (mulQ D n') (mulQ D (n + n')).
  Proof. exact: (E1_thm HP0D). Qed.

  Lemma E2_G : forall n : int, n != 0 ->
    exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y).
  Proof.
    have Hnt' : forall n : int, n != 0 -> mulQ D n <> None.
    { move=> n Hn; rewrite mulQ_mkDataG; exact: Hnt. }
    exact: (E2_of_nontorsion mulQ_on_h mulQ_add_h HP0D Hnt').
  Qed.

  Lemma NhG_D : fd_Nh D = HL_Nh D.
  Proof. by rewrite /= (proj1 (NhG_ChG P0 C S Hb c Kset (NhG P0) (ChG P0))). Qed.

  Lemma ChG_D : fd_Ch D = HL_Ch D.
  Proof. by rewrite /= (proj2 (NhG_ChG P0 C S Hb c Kset (NhG P0) (ChG P0))). Qed.

  Lemma NhG_pos : (0 < NhG P0)%N.
  Proof. have := HL_Nh_pos E2_G; by rewrite -NhG_D. Qed.

  Theorem FixedWF_G : FixedWF D.
  Proof using All. exact: (mkDataG_WF P0 (ChG P0) HC HS HHb Hc HK NhG_pos). Qed.

  Lemma O_F1_G : O_F1_stmt D.
  Proof.
    have H := O_F1_of_E2 mulQ_on_h mulQ_add_h HP0D m0_pos E2_G.
    move=> sg p Hp _; exact (H sg p Hp).
  Qed.

  Lemma O_F2_G : O_F2_stmt D.
  Proof. exact: (O_F2_of_E2 HP0D m0_pos E2_G). Qed.

  Lemma O_height_G : O_height_stmt D.
  Proof. exact: HeightBound_O_height_G. Qed.

  Lemma hei_enlarge_G : hei_enlarge_ord D.
  Proof using All. exact: (HeightBound_hei_enlarge_G FixedWF_G HH). Qed.

  Lemma O_HS_G : forall x1 x2 x3 : rat, (htb (x1 + x2 + x3) <= htb x1 + htb x2 + htb x3 + 2)%N.
  Proof. exact: O_HS_thm. Qed.

  Lemma O_HL_G : forall (n : int) (x0 x1 x2 : rat), n != 0 -> x2 != 0 ->
      (exists y, mulP D n = Some (QE x0 x1 / qe_of x2, y)) ->
      ((absz n) ^ 2 <= fd_Nh D * (htb x0 + htb x1 + htb x2 + fd_Ch D))%N.
  Proof. exact: (O_HL_field E2_G NhG_D ChG_D). Qed.

  Lemma O_PP2_G : forall b : rat, b != 0 -> Phi_holdsR (fd_PhiL D) b ->
      forall q : nat, prime q -> q \notin S1 D -> vqr q b < 0 -> ~~ odd (absz (vqr q b)).
  Proof. exact: (PP2_thm FixedWF_G). Qed.

  Lemma HPatD : forall (A : int) (Y : nat), exists W : PatWit, PatternSpec D A Y W.
  Proof. exact: PatternBody_spec_G. Qed.

  Lemma HCov_G : forall (K : nat) (A : int), (1 <= K)%N -> exists W : RepWit1, RepSpec D K A W.
  Proof. exact: (HCov_thm_G HP0 O_F1_G O_F2_G HPatD). Qed.

  Lemma PP1_D : forall b : int, Phi_holdsR (fd_PhiL D) (b%:~R : rat).
  Proof. exact: PP1_mkDataG. Qed.

  Theorem StdHyps_G : StdHyps D.
  Proof using All. exact: (Build_StdHyps E1_G E2_G HCov_G (PP1_D)). Qed.

  Theorem OrdHyps_of_O_rank_G : O_rank_stmt D -> OrdHyps D.
  Proof using All.
    move=> Hr; exact: (Build_OrdHyps Hr O_F1_G O_F2_G O_height_G O_HS_G O_HL_G O_PP2_G).
  Qed.

  Theorem OrdHyps_G : rank_one_stmt P0 -> OrdHyps D.
  Proof using All. move=> H; apply: OrdHyps_of_O_rank_G; exact: O_rank_of_rank_one. Qed.

End assembly_G.

(** * 7. What P14b-iv-B must deliver *)

Definition generator_stmt : Prop :=
  exists G : qe rat * qe rat, on_curve G /\ nontorsion G /\ rank_one_stmt G.

(* everything about the data, from the generator statement and the three paper inputs *)
Theorem inputs_to_dataG : generator_stmt -> HeightThm -> PrimePattern -> PP1_L0 ->
  exists D : FixedData, FixedWF D /\ StdHyps D /\ OrdHyps D /\ hei_enlarge_ord D.
Proof.
  move=> [G [HG [Hnt Hr]]] [C [S [Hb [c [HC [HS [HHb [Hc HH]]]]]]]] HP HPP.
  have [Kset [HK HB]] := HP C HC.
  exists (mkDataG G C S Hb c Kset (NhG G) (ChG G)).
  split; first by apply: FixedWF_G.
  split; first by apply: StdHyps_G.
  split; first by apply: OrdHyps_G.
  by apply: hei_enlarge_G.
Qed.
