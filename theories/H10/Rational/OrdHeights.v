(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2C, part 3: the ORDINARY statements behind the height fields of
   Ambient.v: trHT0, trHS (= OrdHyps.O_HS, red:all-ring-height), trH2
   (= radical_divides_ord, red:radical-divides), trH3 (= hei_enlarge_ord,
   Cor hei:enlarge-exceptions, from the height bound O_height of Thm
   hei:height taken as a hypothesis), and the ordinary content of trH1
   about the contact radical [MK_ord] (positive, squarefree, its primes
   are good and have odd contact) that does not depend on Thm hei:height.

   Heights are the bit heights [htb] of FixedData.v; the ambient [ht]
   transfers  x |-> (htb x)%:R.  Main results:
   - [ord_HT0]           isZ (htb x) /\ 0 <= htb x                (trHT0)
   - [O_HS_thm]          the field O_HS of OrdHyps                 (trHS)
   - [ord_HS]            its cast version in rat
   - [radical_divides_thm]  radical_divides_ord D                  (trH2)
   - [ord_H2]            the ambient-shaped version, with witness
   - [hei_enlarge_thm]   O_height -> hei_enlarge_ord D             (trH3)
   - [ord_H3]            the ambient-shaped version in (u, v)
   - [MK_ord_gt0], [MK_ord_prime_dvd], [MK_ord_logn], [MK_ord_good],
     [MK_ord_odd_contact]: the ordinary content of trH1 without Thm
     hei:height.

   No axioms. *)

From Stdlib Require Import ZArith Lia List.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential Signature FixedData RatVal OrdinaryFacts.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

(** * Heights are nonnegative integers *)

(* ordinary version of trHT0 *)
Lemma ord_HT0 (x : rat) : isZo (htb x)%:R /\ 0 <= (htb x)%:R :> rat.
Proof. by split; [ exact: isZo_nat | exact: ler0n ]. Qed.

(** * The bit height and its defining inequality *)

Definition Hq (x : rat) : nat := maxn `|numq x| `|denq x|.

Lemma Hq_gt0 x : (0 < Hq x)%N.
Proof. by rewrite /Hq leq_max !absz_gt0 denq_neq0 orbT. Qed.

Lemma Hq_num x : (`|numq x| <= Hq x)%N.
Proof. by rewrite /Hq leq_max leqnn. Qed.

Lemma Hq_den x : (`|denq x| <= Hq x)%N.
Proof. by rewrite /Hq leq_max leqnn orbT. Qed.

Lemma htb_spec x : (Hq x <= Nat.pow 2 (htb x))%coq_nat.
Proof.
  apply Nat.log2_up_le_pow2; last by [].
  by have := Hq_gt0 x => /ssrnat.leP.
Qed.

Lemma htb_le x k : (Hq x <= Nat.pow 2 k)%coq_nat -> (htb x <= k)%coq_nat.
Proof.
  apply Nat.log2_up_le_pow2.
  by have := Hq_gt0 x => /ssrnat.leP.
Qed.

(* reduction of a fraction only decreases numerator and denominator *)
Lemma rat_frac_le (N D : int) : D != 0 ->
  (`|numq (N%:~R / D%:~R : rat)| <= `|N|)%N /\ (`|denq (N%:~R / D%:~R : rat)| <= `|D|)%N.
Proof.
  move=> HD.
  set y := (N%:~R / D%:~R : rat).
  have E : numq y * D = N * denq y.
  { apply: (@intr_inj rat); rewrite !intrM.
    have := divq_num_den y; rewrite /y => /eqP.
    rewrite eqr_div ?intr_eq0 ?denq_neq0 // => /eqP ->; by rewrite mulrC. }
  have En : (`|numq y| * `|D| = `|N| * `|denq y|)%N by rewrite -!abszM E.
  have Hdd : (`|denq y| %| `|D|)%N.
  { have Hcop : coprime `|denq y| `|numq y| by rewrite coprime_sym coprime_num_den.
    by rewrite -(Gauss_dvdr _ Hcop) En dvdn_mull. }
  have HD0 : (0 < `|D|)%N by rewrite absz_gt0.
  split; last exact: dvdn_leq.
  move: Hdd => /dvdnP [ k Hk ].
  have Hk0 : (0 < k)%N by move: HD0; rewrite Hk muln_gt0 => /andP [].
  have Hd0 : (0 < `|denq y|)%N by rewrite absz_gt0 denq_neq0.
  have : (`|numq y| * k = `|N|)%N.
  { apply/eqP; by rewrite -(eqn_pmul2r Hd0) -mulnA -Hk En. }
  move=> <-; by rewrite leq_pmulr.
Qed.

Lemma absz_triangle (a b : int) : (absz (a + b)%R <= absz a + absz b)%N.
Proof. by rewrite -lez_nat PoszD !abszE ler_normD. Qed.

(* red:all-ring-height in bits: H(x+y+z) <= 3 H(x) H(y) H(z) <= 2^2 2^h(x) 2^h(y) 2^h(z) *)
Lemma Hq_sum3 (x1 x2 x3 : rat) :
  (Hq (x1 + x2 + x3) <= 3 * (Hq x1 * Hq x2 * Hq x3))%N.
Proof.
  set n1 := numq x1; set n2 := numq x2; set n3 := numq x3.
  set d1 := denq x1; set d2 := denq x2; set d3 := denq x3.
  have Hd1 : d1 != 0 := denq_neq0 x1.
  have Hd2 : d2 != 0 := denq_neq0 x2.
  have Hd3 : d3 != 0 := denq_neq0 x3.
  have Hd : d1 * d2 * d3 != 0 by rewrite !mulf_neq0.
  pose N := n1 * d2 * d3 + n2 * d1 * d3 + n3 * d1 * d2.
  have E : x1 + x2 + x3 = N%:~R / (d1 * d2 * d3)%:~R.
  { rewrite /N !intrD !intrM -[x1 in LHS]divq_num_den -[x2 in LHS]divq_num_den.
    rewrite -[x3 in LHS]divq_num_den -/n1 -/n2 -/n3 -/d1 -/d2 -/d3.
    have H1 : d1%:~R != 0 :> rat by rewrite intr_eq0.
    have H2 : d2%:~R != 0 :> rat by rewrite intr_eq0.
    have H3 : d3%:~R != 0 :> rat by rewrite intr_eq0.
    field; by rewrite !mulf_neq0. }
  have [ HN HD ] := rat_frac_le N Hd.
  rewrite -E in HN HD.
  have B1 := Hq_num x1; have B2 := Hq_num x2; have B3 := Hq_num x3.
  have C1 := Hq_den x1; have C2 := Hq_den x2; have C3 := Hq_den x3.
  rewrite -/n1 -/n2 -/n3 in B1 B2 B3; rewrite -/d1 -/d2 -/d3 in C1 C2 C3.
  set P := (Hq x1 * Hq x2 * Hq x3)%N.
  have L1 : (absz (n1 * d2 * d3)%R <= P)%N by rewrite !abszM !leq_mul.
  have L2 : (absz (n2 * d1 * d3)%R <= P)%N.
  { have -> : n2 * d1 * d3 = d1 * n2 * d3 by rewrite [n2 * d1]mulrC.
    by rewrite !abszM !leq_mul. }
  have L3 : (absz (n3 * d1 * d2)%R <= P)%N.
  { have -> : n3 * d1 * d2 = d1 * d2 * n3 by ring.
    by rewrite !abszM !leq_mul. }
  have LN : (absz N <= 3 * P)%N.
  { apply: leq_trans (absz_triangle _ _) _.
    apply: leq_trans (leq_add (absz_triangle _ _) (leqnn _)) _.
    by rewrite (mulSn 2) (mulSn 1) mul1n addnA !leq_add. }
  have LD : (absz (d1 * d2 * d3)%R <= 3 * P)%N.
  { apply: (leq_trans _ (leq_pmull P (isT : (0 < 3)%N))).
    by rewrite !abszM !leq_mul. }
  rewrite /Hq geq_max; apply/andP; split; [ exact: leq_trans HN LN | exact: leq_trans HD LD ].
Qed.

(* OrdHyps.O_HS, i.e. the ordinary version of trHS *)
Theorem O_HS_thm (x1 x2 x3 : rat) :
  (htb (x1 + x2 + x3) <= htb x1 + htb x2 + htb x3 + 2)%N.
Proof.
  apply/ssrnat.leP; rewrite -!plusE.
  apply: htb_le.
  have H := Hq_sum3 x1 x2 x3; move/ssrnat.leP: H; rewrite -!multE => H.
  have S1 := htb_spec x1; have S2 := htb_spec x2; have S3 := htb_spec x3.
  rewrite !Nat.pow_add_r.
  have M : (Hq x1 * Hq x2 * Hq x3 <= Nat.pow 2 (htb x1) * Nat.pow 2 (htb x2) * Nat.pow 2 (htb x3))%coq_nat.
  { apply Nat.mul_le_mono; [ apply Nat.mul_le_mono | ]; assumption. }
  have E4 : Nat.pow 2 2 = 4%N by [].
  rewrite E4; move: M; rewrite -!multE => M; lia.
Qed.

(* the cast version, as the ambient field trHS reads it in sQ = rat *)
Lemma ord_HS (x1 x2 x3 : rat) :
  (htb (x1 + x2 + x3))%:R <= (htb x1)%:R + (htb x2)%:R + (htb x3)%:R + 2%:R :> rat.
Proof. by rewrite -!natrD ler_nat O_HS_thm. Qed.

(** * Products of distinct primes *)

Section prod_primes.

  Variable P : pred nat.

  Lemma prod_primes_gt0 (l : seq nat) : all prime l -> (0 < \prod_(p <- l | P p) p)%N.
  Proof.
    elim: l => [ | p l IH ] /=; first by rewrite big_nil.
    move=> /andP [ Hp Hl ]; rewrite big_cons; case: (P p); last exact: IH.
    by rewrite muln_gt0 prime_gt0 // IH.
  Qed.

  Lemma prod_primes_dvd (l : seq nat) (q : nat) : all prime l -> prime q ->
    (q %| \prod_(p <- l | P p) p)%N = (q \in l) && P q.
  Proof.
    move=> Hl Hq; elim: l Hl => [ | p l IH ] /=.
    - move=> _; rewrite big_nil dvdn1; apply/negbTE; apply: contraTneq Hq => ->; by [].
    - move=> /andP [ Hp Hl ]; rewrite big_cons inE.
      case HP : (P p).
      + rewrite Euclid_dvdM // dvdn_prime2 // IH //.
        by case: (eqVneq q p) => [ -> | ] /=; rewrite ?HP.
      + rewrite IH //.
        by case: (eqVneq q p) => [ -> | ] //=; rewrite HP !andbF.
  Qed.

  (* squarefree *)
  Lemma prod_primes_logn (l : seq nat) (q : nat) : uniq l -> all prime l -> prime q ->
    logn q (\prod_(p <- l | P p) p) = ((q \in l) && P q : nat).
  Proof.
    move=> Hu Hl Hq; elim: l Hu Hl => [ | p l IH ] /=.
    - by rewrite big_nil logn1.
    - move=> /andP [ Hpl Hu ] /andP [ Hp Hl ]; rewrite big_cons inE.
      case HP : (P p).
      + rewrite lognM; [ exact: prime_gt0 | exact: prod_primes_gt0 | ].
        rewrite logn_prime // IH //.
        case: (eqVneq q p) => [ -> | Hqp ] /=; first by rewrite (negbTE Hpl) HP.
        by rewrite add0n.
      + rewrite IH //; case: (eqVneq q p) => [ -> | ] //=.
        by rewrite (negbTE Hpl) HP.
  Qed.

  (* a product of distinct primes whose K-th powers divide n: its K-th power divides n *)
  Lemma prod_primes_radical (l : seq nat) (K n : nat) : uniq l -> all prime l ->
    (forall q, q \in l -> P q -> (q ^ K %| n)%N) -> ((\prod_(p <- l | P p) p) ^ K %| n)%N.
  Proof.
    elim: l => [ | p l IH ] /=.
    - by move=> _ _ _; rewrite big_nil exp1n dvd1n.
    - move=> /andP [ Hpl Hu ] /andP [ Hp Hl ] H; rewrite big_cons.
      have IH' := IH Hu Hl (fun q Hq HPq => H q ltac:(by rewrite inE Hq orbT) HPq).
      case HP : (P p); last exact: IH'.
      have Hcop : coprime (p ^ K) ((\prod_(q <- l | P q) q) ^ K).
      { apply: coprimeXl; apply: coprimeXr.
        by rewrite prime_coprime // prod_primes_dvd // (negbTE Hpl). }
      rewrite expnMn Gauss_dvd // IH' andbT.
      by apply: H => //; rewrite inE eqxx.
  Qed.

  (* a duplicate-free sublist gives a divisor of the product *)
  Lemma prod_subset_dvd (l1 l2 : seq nat) : uniq l1 -> uniq l2 -> {subset l1 <= l2} ->
    (\prod_(p <- l1) p %| \prod_(p <- l2) p)%N.
  Proof.
    elim: l1 l2 => [ | a l1 IH ] l2 /=; first by rewrite big_nil dvd1n.
    move=> /andP [ Hal Hu1 ] Hu2 Hs.
    have Ha : a \in l2 by apply: Hs; rewrite inE eqxx.
    rewrite big_cons [X in (_ %| X)%N](big_rem a) //=.
    apply: dvdn_mul => //; apply: IH => //; first exact: rem_uniq.
    move=> y Hy; rewrite mem_rem_uniq // inE; apply/andP; split.
    - by apply: contraNneq Hal => <-.
    - by apply: Hs; rewrite inE Hy orbT.
  Qed.

End prod_primes.

Lemma all_prime_primes (n : nat) : all prime (primes n).
Proof. apply/allP => q; by rewrite mem_primes => /andP []. Qed.

(** * The contact radical [MK_ord]: ordinary content of trH1 *)

Section contact_radical.

  Variable D : FixedData.

  Lemma MS_gt0 (S' : seq nat) (s : rat) : (0 < MS D S' s)%N.
  Proof. exact: prod_primes_gt0 (all_prime_primes _). Qed.

  Lemma MS_prime_dvd (S' : seq nat) (s : rat) (q : nat) : prime q ->
    (q %| MS D S' s)%N = [&& q \in primes (contact_support D s), q \notin S' & odd_contact D q s].
  Proof. move=> Hq; by rewrite /MS prod_primes_dvd ?all_prime_primes. Qed.

  Lemma MS_logn (S' : seq nat) (s : rat) (q : nat) : prime q ->
    logn q (MS D S' s) = ([&& q \in primes (contact_support D s), q \notin S' & odd_contact D q s] : nat).
  Proof. move=> Hq; by rewrite /MS prod_primes_logn ?primes_uniq ?all_prime_primes. Qed.

  (* trH1, first two conjuncts: MK K s is a positive integer *)
  Lemma MK_ord_gt0 (K : nat) (s : rat) : (0 < MK_ord D K s)%N.
  Proof. exact: MS_gt0. Qed.

  Lemma ord_H1_int (K : nat) (s : rat) : isZo (MK_ord D K s)%:R /\ 1 <= (MK_ord D K s)%:R :> rat.
  Proof. split; [ exact: isZo_nat | by rewrite ler1n MK_ord_gt0 ]. Qed.

  Lemma MK_ord_prime_dvd (K : nat) (s : rat) (q : nat) : prime q ->
    (q %| MK_ord D K s)%N = [&& q \in primes (contact_support D s), q \notin SK D K & odd_contact D q s].
  Proof. exact: MS_prime_dvd. Qed.

  (* MK is squarefree *)
  Lemma MK_ord_logn (K : nat) (s : rat) (q : nat) : prime q ->
    logn q (MK_ord D K s) = (q %| MK_ord D K s)%N.
  Proof. by move=> Hq; rewrite MK_ord_prime_dvd // /MK_ord MS_logn. Qed.

  (* trH1, the primes counted by MK are good ... *)
  Lemma MK_ord_good (K : nat) (s : rat) (q : nat) : prime q -> (q %| MK_ord D K s)%N ->
    good D K q.
  Proof.
    move=> Hq; rewrite MK_ord_prime_dvd // => /and3P [ _ HSK _ ].
    move: HSK; rewrite /SK mem_undup mem_cat negb_or mem_filter Hq mem_iota add0n /=.
    move=> /andP [ HS Hlt ]; rewrite /good HS andbT.
    by rewrite ltnNge -ltnS.
  Qed.

  (* ... and have odd contact order (in the reduced coordinates num s, den s) *)
  Lemma MK_ord_odd_contact (K : nat) (s : rat) (q : nat) : prime q -> (q %| MK_ord D K s)%N ->
    odd_contact D q s.
  Proof. move=> Hq; by rewrite MK_ord_prime_dvd // => /and3P []. Qed.

  (* the valuation of MK at a prime is 0 or 1 *)
  Lemma vqr_MK (K : nat) (s : rat) (q : nat) : prime q ->
    vqr q (MK_ord D K s)%:R = ((q %| MK_ord D K s)%N : nat)%:Z.
  Proof. by move=> Hq; rewrite natr_intr vqr_int /= MK_ord_logn. Qed.

End contact_radical.

(** * red:radical-divides (trH2) *)

(* FixedData.radical_divides_ord, the ordinary version of trH2 *)
Theorem radical_divides_thm (D : FixedData) : radical_divides_ord D.
Proof.
  move=> K s delta Hd H.
  apply: prod_primes_radical; [ exact: primes_uniq | exact: all_prime_primes | ].
  move=> q Hq /andP [ HSK Hodd ].
  have Hqp : prime q by move: Hq; rewrite mem_primes => /andP [].
  apply: H => //; by rewrite MK_ord_prime_dvd // Hq HSK Hodd.
Qed.

(* the ambient-shaped version of trH2, with the witness delta / MK^K *)
Lemma ord_H2 (D : FixedData) (K : nat) (s delta : rat) : isZo delta -> delta != 0 ->
  (forall q : rat, primeo q -> 0 < vqo q (MK_ord D K s)%:R -> K%:Z <= vqo q delta) ->
  let z := delta / ((MK_ord D K s)%:R ^+ K) in isZo z /\ delta = (MK_ord D K s)%:R ^+ K * z.
Proof.
  move=> Hz Hd H z.
  set M := MK_ord D K s.
  have HM0 : (MK_ord D K s)%:R ^+ K != 0 :> rat by rewrite expf_neq0 // pnatr_eq0 -lt0n MK_ord_gt0.
  split; last by rewrite /z mulrC mulfVK.
  have En := isZo_numq Hz.
  have Hn0 : numq delta != 0 by rewrite numq_eq0.
  have Hdvd : (M ^ K %| `|numq delta|)%N.
  { apply: radical_divides_thm => // q Hq HqM.
    rewrite -(vqr_dvd_int Hq) // -En -(vqo_nat q).
    apply: H; first exact/ord_PR.
    by rewrite vqo_nat vqr_MK // HqM. }
  have : ((M ^ K)%N%:Z %| numq delta)%Z by rewrite dvdzE.
  move=> /dvdzP [ k Hk ].
  exists k; rewrite /z En Hk intrM natr_intr -/M.
  have -> : ((M ^ K)%N%:Z)%:~R = (M%:R ^+ K : rat) by rewrite -natr_intr natrX.
  by rewrite mulfK // -/M.
Qed.

(** * Cor hei:enlarge-exceptions (trH3), from Thm hei:height *)

Section enlarge.

  Variable D : FixedData.
  Hypothesis HWF : FixedWF D.

  Lemma Sfix_prime (p : nat) : p \in Sfix D -> prime p.
  Proof using HWF.
    have primes_mem : forall n x, x \in primes n -> prime x.
    { by move=> n x; rewrite mem_primes => /andP []. }
    rewrite /Sfix /S1 /Sdet => H.
    rewrite !mem_cat !inE in H.
    repeat match goal with H : is_true (_ || _) |- _ => case/orP: H => H end.
    all: first [ by move/eqP: H => ->
               | exact: (allP (wf_S HWF) p H)
               | exact: (allP (wf_SE HWF) p H)
               | exact: primes_mem H
               | by move: H => /flattenP [ l /mapP [ k _ -> ] ] /primes_mem
               | by move: H => /flattenP [ l /mapP [ y _ -> ] ];
                    rewrite /rat_support mem_cat => /orP [] /primes_mem
               | by [] ].
  Qed.

  Lemma SK_prime (K p : nat) : p \in SK D K -> prime p.
  Proof using HWF.
    rewrite /SK mem_undup mem_cat => /orP [ /Sfix_prime // | ].
    by rewrite mem_filter => /andP [].
  Qed.

  Lemma S_sub_SK (K p : nat) : p \in fd_S D -> p \in SK D K.
  Proof. by move=> Hp; rewrite /SK mem_undup !mem_cat Hp. Qed.

  (* the product of the primes of S_K outside S *)
  Definition PiK (K : nat) : nat := \prod_(p <- SK D K | p \notin fd_S D) p.

  Lemma PiK_gt0 K : (0 < PiK K)%N.
  Proof using HWF.
    rewrite /PiK big_seq_cond prodn_cond_gt0 // => p /andP [ Hp _ ].
    exact/prime_gt0/(SK_prime Hp).
  Qed.

  (* M_S(s) = A * M_{S_K}(s), with A a divisor of PiK *)
  Lemma MS_split (K : nat) (s : rat) : exists A : nat,
    MS D (fd_S D) s = (A * MK_ord D K s)%N /\ (A <= PiK K)%N.
  Proof using HWF.
    set l := primes (contact_support D s).
    exists (\prod_(q <- l | ((q \notin fd_S D) && odd_contact D q s) && (q \in SK D K)) q).
    split.
    - rewrite /MS /MK_ord /MS -/l (bigID (fun q => q \in SK D K)); congr muln.
      apply: eq_bigl => q; rewrite [in RHS]andbC.
      case HS : (q \in SK D K); first by rewrite !andbF.
      rewrite !andbT.
      have -> : q \notin fd_S D by apply: contraFN HS => /S_sub_SK.
      by [].
    - apply: dvdn_leq; first exact: PiK_gt0.
      rewrite /PiK -[X in (X %| _)%N]big_filter -[X in (_ %| X)%N]big_filter.
      apply: prod_subset_dvd.
      + apply: filter_uniq; exact: primes_uniq.
      + apply: filter_uniq; exact: undup_uniq.
      + move=> q; rewrite !mem_filter => /andP [ /andP [ /andP [ H1 _ ] H2 ] _ ].
        by rewrite H1 H2.
  Qed.

  (* FixedData.hei_enlarge_ord, the ordinary version of trH3, from O_height *)
  Theorem hei_enlarge_thm :
    (forall s : rat, (forall i, s != fd_C D i) ->
       (htb s <= fd_Hb D * (MS D (fd_S D) s) ^ fd_c D)%N) ->
    hei_enlarge_ord D.
  Proof using HWF.
    move=> Hh K s Hs.
    apply: leq_trans (Hh s Hs) _.
    have [ A [ EA HA ] ] := MS_split K s.
    rewrite EA /HK -mulnA leq_mul2l; apply/orP; right.
    rewrite -expnMn; case: (fd_c D) => [ | c ]; first by rewrite !expn0.
    by rewrite leq_exp2r // leq_mul2r HA orbT.
  Qed.

  (* fd_L i u v <> 0 means u / v <> C_i *)
  Lemma fd_L_neq (i : i4) (u v : rat) : v != 0 -> fd_L D i u v != 0 -> u / v != fd_C D i.
  Proof.
    move=> Hv; apply: contraNneq => E.
    have Eu : u = fd_C D i * v by rewrite -E mulfVK.
    apply/eqP; rewrite /fd_L Eu mulrA [_%:~R * fd_C D i]mulrC -numqE; ring.
  Qed.

  (* the ambient-shaped version of trH3, in homogeneous coordinates (u, v) *)
  Lemma ord_H3 : hei_enlarge_ord D ->
    forall (K : nat) (u v : rat), v != 0 -> (forall i, fd_L D i u v != 0) ->
      (htb (u / v))%:R <= (HK D K)%:R * (MK_ord D K (u / v))%:R ^+ fd_c D :> rat.
  Proof.
    move=> He K u v Hv HL.
    rewrite -natrX -natrM ler_nat; apply: He => i; exact: fd_L_neq.
  Qed.

End enlarge.
