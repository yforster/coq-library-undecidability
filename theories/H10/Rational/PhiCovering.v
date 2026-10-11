(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The covering properties of the explicit Phi lists (PLAN.md, task P18;
   ASSEMBLY.md Sec. 1.3, "Caveat (trust)").

   The paper (03-parity.tex, Sec. 3.2) proves Prop par:pole-parity (1),
   integer completeness of Phi, for ANY finite nonempty lists M, D_m in
   Q^x with the two covering properties
     (par:b-prime-choices)  for every b in Q^x some m in M makes
         b' = m b > 0, b' in Q_2^{x2}, b' in the unit nonsquare class
         of Q_3^x (even 3-adic valuation, nonsquare unit part);
     (par:d-choices)  for every m in M, with S(m) = {2,3} u Supp(m), and
         every b <> 0 some m_d in D_m makes d = m_d b > 0 and
         d in Q_q^{x2} for all q in S(m).
   These are the only properties of the lists that the proof uses.

   PROVED here (no axioms):
   - [locsq q x] (x in Q_q^{x2}) and [unit_nonsq3 x], defined by the
     textbook description of local square classes (x = y^2 a/c with a, c
     integers prime to q and a = z^2 c mod q, resp. a = c mod 8 for
     q = 2), Sec. 5;
   - [CoversM L], [CoversD L]: the two covering properties, Sec. 7;
   - [PhiL0_CoversM : CoversM PhiL0], [PhiL0_CoversD : CoversD PhiL0]
     (Sec. 8), from finite checks by [vm_compute]: a bit-vector signature
     ([sigZ]: sign; per prime: parity of v_q and the unit characters,
     u mod 4 and u mod 8 at 2, the quadratic character at odd q) whose
     vanishing is lifted to the definitions of [locsq]/[unit_nonsq3] by
     residue tables for q in {2,3,5,...,23} (Sec. 3); and a check that
     every combination of bits of b is completed to the target by some
     list entry ([covers], Sec. 4). No multiplicativity of the
     signature and no primality is needed: b = n/d and m b = (m n)/d is
     handled by the decompositions of m, n, d separately;
   - [PP1_paper] (Sec. 9): the paper's Prop par:pole-parity (1) for all
     lists with these properties, and [PP1_paper_L0 : PP1_paper -> PP1_L0].
     So [PP1_L0] is the paper's statement specialized to lists whose
     covering properties are verified.

   NOT formalized: that [locsq q x] is equivalent to "x is a square in
   Q_q" (Hensel's lemma; only the definitions are used, no q-adic
   numbers). *)

From Stdlib Require Import ZArith Lia List.

From Undecidability.H10.Rational
  Require Import RatUtil PosExistential FixedData ExplicitData PaperInputs.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope Z_scope with ZZ.
Local Open Scope ring_scope.

(** * 1. Congruences on binary integers *)

Section Cong.

  Local Open Scope Z_scope.

  Definition cong (M x y : Z) : Prop := (M | x - y).

  Lemma cong_refl M x : cong M x x.
  Proof. exists 0; lia. Qed.

  Lemma cong_add M x x' y y' : cong M x x' -> cong M y y' -> cong M (x + y) (x' + y').
  Proof. move=> [a Ha] [b Hb]; exists (a + b); lia. Qed.

  Lemma cong_sub M x x' y y' : cong M x x' -> cong M y y' -> cong M (x - y) (x' - y').
  Proof. move=> [a Ha] [b Hb]; exists (a - b); lia. Qed.

  Lemma cong_mul M x x' y y' : cong M x x' -> cong M y y' -> cong M (x * y) (x' * y').
  Proof.
    move=> [a Ha] [b Hb]; exists (a * y + x' * b).
    have -> : x * y - x' * y' = (x - x') * y + x' * (y - y') by lia.
    rewrite Ha Hb; lia.
  Qed.

  Lemma cong_mod M x : M <> 0 -> cong M x (x mod M).
  Proof. move=> HM; exists (x / M); have := Z.div_mod x M HM; lia. Qed.

  Lemma cong_modE M x y : M <> 0 -> cong M x y -> x mod M = y mod M.
  Proof.
    move=> HM [k Hk]; have -> : x = y + k * M by lia.
    exact: Z_mod_plus_full.
  Qed.

  Lemma cong_div M N x y : (N | M) -> cong M x y -> cong N x y.
  Proof. move=> HNM HM; exact: Z.divide_trans HNM HM. Qed.

End Cong.

(** * 2. Valuation and unit part of a nonzero binary integer *)

Section VU.

  Local Open Scope Z_scope.

  Fixpoint vu_aux (f : nat) (q z : Z) : nat * Z :=
    match f with
    | O => (O, z)
    | S f => if z mod q =? 0 then let p := vu_aux f q (z / q) in (S (fst p), snd p) else (O, z)
    end.

  (* the fuel bounds the valuation, as q >= 2 *)
  Definition vu (q z : Z) : nat * Z := vu_aux (S (Z.to_nat (Z.log2 (Z.abs z)))) q z.

  Lemma vu_aux_S f q z : vu_aux (S f) q z =
    if (z mod q =? 0) then (S (fst (vu_aux f q (z / q))), snd (vu_aux f q (z / q))) else (O, z).
  Proof. by []. Qed.

  Lemma vu_aux_eq f q z : q <> 0 ->
    z = q ^ Z.of_nat (fst (vu_aux f q z)) * snd (vu_aux f q z).
  Proof.
    move=> Hq; elim: f z => [ | f IH ] z; first by rewrite /=; case: z.
    rewrite vu_aux_S; case: (Z.eqb_spec (z mod q) 0) => H; cbn [fst snd]; last by rewrite /=; case: (z).
    rewrite Nat2Z.inj_succ (Z.pow_succ_r _ _ (Nat2Z.is_nonneg _)).
    have Hz : z = q * (z / q) by apply: Z_div_exact_full_2.
    rewrite {1}Hz {1}(IH (z / q)); lia.
  Qed.

  Lemma vu_aux_unit f q z : 2 <= q -> z <> 0 -> Z.abs z < 2 ^ Z.of_nat f ->
    snd (vu_aux f q z) mod q <> 0.
  Proof.
    move=> Hq; elim: f z => [ | f IH ] z Hz.
    - rewrite /= => H; lia.
    - rewrite vu_aux_S; case: (Z.eqb_spec (z mod q) 0) => H Hlt; cbn [fst snd]; last done.
      have Hzq : z = q * (z / q) by apply: Z_div_exact_full_2; lia.
      apply: IH.
      + move=> H0; rewrite H0 in Hzq; lia.
      + move: Hlt; rewrite Nat2Z.inj_succ (Z.pow_succ_r _ _ (Nat2Z.is_nonneg _)).
        rewrite {1}Hzq Z.abs_mul (Z.abs_eq q); first lia.
        have := Z.abs_nonneg (z / q); nia.
  Qed.

  Lemma vu_eq q z : q <> 0 -> z = q ^ Z.of_nat (fst (vu q z)) * snd (vu q z).
  Proof. exact: vu_aux_eq. Qed.

  Lemma vu_unit q z : 2 <= q -> z <> 0 -> snd (vu q z) mod q <> 0.
  Proof.
    move=> Hq Hz; apply: vu_aux_unit => //.
    have Ha : 0 < Z.abs z by lia.
    have [_ H] := Z.log2_spec _ Ha.
    rewrite Nat2Z.inj_succ Z2Nat.id //; exact: Z.log2_nonneg.
  Qed.

End VU.

(** * 3. Local square-class signatures of binary integers

    For a prime q and a nonzero integer z = q^v u with q not dividing u,
    [csig q z] lists the coordinates of the class of z in
    Q_q^x / Q_q^{x2} as bits (the group law is [xorl]):
    - the parity of v;
    - for q = 2: the two characters [u = 3 mod 4] and [u = +-3 mod 8]
      of (Z/8)^x; for odd q: [u is a nonresidue mod q].
    [sigZ S z] prepends the sign. Only the direction "these bits
    vanish => z is a local square" (and its unit nonsquare variant at
    3) is used below; it is proved from the definitions, by lifting
    finite computations on residues. *)

Section Sig.

  Local Open Scope Z_scope.

  Definition rng (M : Z) : list Z := map Z.of_nat (List.seq 0 (Z.to_nat M)).

  Lemma in_rng M r : 0 <= r < M -> In r (rng M).
  Proof.
    move=> Hr; apply/in_map_iff; exists (Z.to_nat r); split; first by rewrite Z2Nat.id; lia.
    apply/List.in_seq; lia.
  Qed.

  Definition qr (q u : Z) : bool := List.existsb (fun y => (y * y - u) mod q =? 0) (rng q).

  Definition cu (q u : Z) : list bool :=
    if q =? 2 then [:: u mod 4 =? 3; (u mod 8 =? 3) || (u mod 8 =? 5)] else [:: negb (qr q u)].

  Definition csig (q z : Z) : list bool := Nat.odd (fst (vu q z)) :: cu q (snd (vu q z)).

  #[global] Arguments csig : simpl never.

  Definition sigZ (S : list Z) (z : Z) : list bool := (z <? 0) :: flat_map (fun q => csig q z) S.

  Fixpoint xorl (l1 l2 : list bool) : list bool :=
    match l1, l2 with
    | b1 :: l1, b2 :: l2 => xorb b1 b2 :: xorl l1 l2
    | _, _ => [::]
    end.

  (* the modulus on which the unit characters depend *)
  Definition Mq (q : Z) : Z := if q =? 2 then 8 else q.

  Definition unitb (q r : Z) : bool := negb (r mod q =? 0).

  (* the target unit bits of a local square *)
  Definition ct (q : Z) : list bool := if q =? 2 then [:: false; false] else [:: false].

  Definition sqb (q a c : Z) : bool :=
    if q =? 2 then (a - c) mod 8 =? 0
    else List.existsb (fun z => (a - z * z * c) mod q =? 0) (rng q).

  (* the finite check behind "bits vanish => local square", for q:
     units r0 r1 r2 mod M with vanishing combined bits have r0 r1 a unit
     and r0 r1 / r2 a square mod q (resp. 1 mod 8) *)
  Definition utab (q : Z) : list (Z * list bool) :=
    List.map (fun r => (r, cu q r)) (List.filter (unitb q) (rng (Mq q))).

  Definition rc_sq (q : Z) : bool :=
    let T := utab q in
    List.forallb (fun p0 => List.forallb (fun p1 => List.forallb (fun p2 =>
      implb (xorl p0.2 (xorl p1.2 p2.2) == ct q)%B
            (unitb q (p0.1 * p1.1) && sqb q (p0.1 * p1.1) p2.1)) T) T) T.

  (* the same at 3, for the unit nonsquare class *)
  Definition rc_ns3 : bool :=
    let T := utab 3 in
    List.forallb (fun p0 => List.forallb (fun p1 => List.forallb (fun p2 =>
      implb (xorl p0.2 (xorl p1.2 p2.2) == [:: true])%B
            (unitb 3 (p0.1 * p1.1) &&
             List.forallb (fun z => negb ((p0.1 * p1.1 - z * z * p2.1) mod 3 =? 0)) (rng 3))) T) T) T.

  (* the primes occurring in S(m) for the lists of ExplicitData *)
  Definition P8 : list Z := [:: 2; 3; 5; 7; 11; 13; 17; 19; 23].

  Lemma rc_sq_P8 : List.forallb rc_sq P8 = true.
  Proof. by vm_compute. Qed.

  Lemma rc_ns3_true : rc_ns3 = true.
  Proof. by vm_compute. Qed.

  (** Lifting the finite checks from residues to all units. *)

  Lemma existsb_ext' A (f g : A -> bool) l : (forall x, f x = g x) ->
    List.existsb f l = List.existsb g l.
  Proof. by move=> H; elim: l => [ | x l IH ] //=; rewrite H IH. Qed.

  Lemma Mq_pos q : 0 < q -> 0 < Mq q.
  Proof. by rewrite /Mq; case: (Z.eqb_spec q 2); lia. Qed.

  Lemma Mq_div q : (q | Mq q).
  Proof.
    rewrite /Mq; case: (Z.eqb_spec q 2) => [ -> | _ ]; first by exists 4.
    exact: Z.divide_refl.
  Qed.

  Lemma cong_q q x y : 0 < q -> cong (Mq q) x y -> x mod q = y mod q.
  Proof. move=> Hq H; apply: cong_modE; first lia; exact: cong_div (Mq_div q) H. Qed.

  Lemma cu_cong q u u' : 0 < q -> cong (Mq q) u u' -> cu q u = cu q u'.
  Proof.
    move=> Hq H; rewrite /cu; case: (Z.eqb_spec q 2) => [ Hq2 | Hq2 ].
    - move: H; rewrite /Mq Hq2 /= => H.
      have H8 : u mod 8 = u' mod 8 by apply: cong_modE.
      have H4 : u mod 4 = u' mod 4.
      { apply: cong_modE => //; apply: cong_div H; by exists 2. }
      by rewrite H4 H8.
    - move: H; rewrite /Mq; case: (Z.eqb_spec q 2) => // _ H.
      rewrite /qr; congr [:: negb _]; apply: existsb_ext' => y.
      f_equal; apply: cong_modE; first lia.
      apply: cong_sub; [ exact: cong_refl | exact: H ].
  Qed.

  Lemma unitb_cong q u u' : 0 < q -> cong (Mq q) u u' -> unitb q u = unitb q u'.
  Proof. by move=> Hq H; rewrite /unitb (cong_q Hq H). Qed.

  Lemma unitb_spec q u : q <> 0 -> unitb q u = true <-> ~ (q | u).
  Proof.
    move=> Hq; rewrite /unitb -(Z.mod_divide _ _ Hq).
    by case: (Z.eqb_spec (u mod q) 0).
  Qed.

  Lemma sqb_cong q a a' c c' : 0 < q -> cong (Mq q) a a' -> cong (Mq q) c c' ->
    sqb q a c = sqb q a' c'.
  Proof.
    move=> Hq Ha Hc; rewrite /sqb; case: (Z.eqb_spec q 2) => [ Hq2 | Hq2 ].
    - move: Ha Hc; rewrite /Mq Hq2 /= => Ha Hc.
      by rewrite (cong_modE _ (cong_sub Ha Hc)).
    - move: Ha Hc; rewrite /Mq; case: (Z.eqb_spec q 2) => // _ Ha Hc.
      apply: existsb_ext' => z; rewrite (@cong_modE q _ (a' - z * z * c')) //; first lia.
      apply: cong_sub => //; apply: cong_mul => //; exact: cong_refl.
  Qed.

  Lemma utab_in q u : 0 < q -> unitb q u -> In (u mod Mq q, cu q u) (utab q).
  Proof.
    move=> Hq Hu; have HM := Mq_pos Hq.
    have Hc : cong (Mq q) u (u mod Mq q) by apply: cong_mod; lia.
    apply/in_map_iff; exists (u mod Mq q); split; first by rewrite -(cu_cong Hq Hc).
    apply/filter_In; split; last by rewrite -(unitb_cong Hq Hc).
    apply: in_rng; exact: Z.mod_pos_bound.
  Qed.

  Lemma P8_pos q : In q P8 -> 2 <= q.
  Proof. by rewrite /P8 /=; intuition; subst; lia. Qed.

  Lemma comp_unit_sq q u0 u1 u2 : In q P8 ->
    unitb q u0 -> unitb q u1 -> unitb q u2 ->
    xorl (cu q u0) (xorl (cu q u1) (cu q u2)) = ct q ->
    unitb q (u0 * u1) && sqb q (u0 * u1) u2.
  Proof.
    move=> HP H0 H1 H2 Hx; have Hq : 0 < q by have := P8_pos HP; lia.
    have Hrc : rc_sq q by apply: (proj1 (List.forallb_forall _ _) rc_sq_P8).
    move: Hrc; rewrite /rc_sq => /List.forallb_forall /(_ _ (utab_in Hq H0)).
    move=> /List.forallb_forall /(_ _ (utab_in Hq H1)).
    move=> /List.forallb_forall /(_ _ (utab_in Hq H2)); cbn [fst snd].
    rewrite Hx eqxx /= => /andP [Hu Hs].
    set M := Mq q.
    have HM : M <> 0 by have := Mq_pos Hq; rewrite /M; lia.
    have C0 := cong_mod u0 HM; have C1 := cong_mod u1 HM; have C2 := cong_mod u2 HM.
    have C01 : cong M (u0 * u1) (u0 mod M * (u1 mod M)) by apply: cong_mul.
    by rewrite (unitb_cong Hq C01) Hu (sqb_cong Hq C01 C2) Hs.
  Qed.

  Lemma comp_unit_ns3 u0 u1 u2 :
    unitb 3 u0 -> unitb 3 u1 -> unitb 3 u2 ->
    xorl (cu 3 u0) (xorl (cu 3 u1) (cu 3 u2)) = [:: true] ->
    unitb 3 (u0 * u1) /\ forall z, (u0 * u1 - z * z * u2) mod 3 <> 0.
  Proof.
    move=> H0 H1 H2 Hx; have Hq : 0 < 3 by lia.
    move: rc_ns3_true; rewrite /rc_ns3 => /List.forallb_forall /(_ _ (utab_in Hq H0)).
    move=> /List.forallb_forall /(_ _ (utab_in Hq H1)).
    move=> /List.forallb_forall /(_ _ (utab_in Hq H2)); cbn [fst snd].
    rewrite Hx eqxx => /andP [Hu Hs0]; have Hs := proj1 (List.forallb_forall _ _) Hs0.
    have H3 : 3 <> 0 by lia.
    have C0 := cong_mod u0 H3; have C1 := cong_mod u1 H3.
    have C2 := cong_mod u2 H3.
    have C01 : cong 3 (u0 * u1) (u0 mod 3 * (u1 mod 3)) by apply: cong_mul.
    split; first by rewrite (@unitb_cong 3 _ _ Hq C01).
    move=> z; have Cz := cong_mod z H3.
    have Hz := Hs (z mod 3) (in_rng (Z.mod_pos_bound z 3 Hq)).
    rewrite (cong_modE H3 (cong_sub C01 (cong_mul (cong_mul Cz Cz) C2))).
    by case: (Z.eqb_spec ((u0 mod 3 * (u1 mod 3) - z mod 3 * (z mod 3) * (u2 mod 3)) mod 3) 0) Hz.
  Qed.

End Sig.

(** * 4. Bit vectors *)

Section Bits.

  Lemma length_cu q u : length (cu q u) = (if (q =? 2)%ZZ then 2 else 1)%N.
  Proof. by rewrite /cu; case: (q =? 2)%ZZ. Qed.

  Lemma length_csig q z : length (csig q z) = (if (q =? 2)%ZZ then 3 else 2)%N.
  Proof. by rewrite /csig /= length_cu; case: (q =? 2)%ZZ. Qed.

  Lemma length_xorl a b : length a = length b -> length (xorl a b) = length a.
  Proof. by elim: a b => [ | x a IH ] [ | y b ] //= [ /IH -> ]. Qed.

  Lemma xorl_app a1 a2 b1 b2 : length a1 = length b1 ->
    xorl (a1 ++ a2) (b1 ++ b2) = xorl a1 b1 ++ xorl a2 b2.
  Proof. by elim: a1 b1 => [ | x a IH ] [ | y b ] //= [ /IH -> ]. Qed.

  Lemma xorl_flat (f g : Z -> list bool) S : (forall q, length (f q) = length (g q)) ->
    xorl (flat_map f S) (flat_map g S) = flat_map (fun q => xorl (f q) (g q)) S.
  Proof. by move=> H; elim: S => [ | q S IH ] //=; rewrite xorl_app // IH. Qed.

  Lemma app_inv_len (a1 a2 b1 b2 : list bool) : length a1 = length b1 ->
    a1 ++ a2 = b1 ++ b2 -> a1 = b1 /\ a2 = b2.
  Proof.
    elim: a1 b1 => [ | x a IH ] [ | y b ] //= [ Hl ] [ -> Happ ].
    by have [ -> -> ] := IH _ Hl Happ.
  Qed.

  Lemma flat_eq (f g : Z -> list bool) S : (forall q, length (f q) = length (g q)) ->
    flat_map f S = flat_map g S -> forall q, In q S -> f q = g q.
  Proof.
    move=> H; elim: S => [ | q S IH ] //= Heq q' [ <- | Hq' ].
    - by have [ -> _ ] := app_inv_len (H q) Heq.
    - by have [ _ /IH ] := app_inv_len (H q) Heq; apply.
  Qed.

  Fixpoint bvecs (n : nat) : list (list bool) :=
    match n with
    | O => [:: [::]]
    | S n => flat_map (fun l => [:: true :: l; false :: l]) (bvecs n)
    end.

  Lemma bvecs_in l : In l (bvecs (length l)).
  Proof.
    elim: l => [ | b l IH ] /=; first by left.
    apply/in_flat_map; exists l; split => //; by case: b; [ left | right; left ].
  Qed.

  Lemma length_sigZ S z : length (sigZ S z) = length (sigZ S 1).
  Proof.
    rewrite /sigZ /=; congr (_.+1); elim: S => [ | q S IH ] //=.
    by rewrite !length_app IH !length_cu.
  Qed.

  (* the computational covering check: every combination of bits g is
     completed to the target by the signature of some list entry *)
  Definition covers (S : list Z) (t : Z -> list bool) (Ms : list Z) : bool :=
    List.forallb (fun m => negb (m =? 0)%ZZ) Ms &&
    let sigs := List.map (fun m => (m, sigZ S m)) Ms in
    List.forallb (fun g => List.existsb (fun ms => xorl ms.2 g == false :: flat_map t S)%B sigs)
                 (bvecs (length (sigZ S 1))).

  Lemma covers_spec S t Ms : covers S t Ms ->
    (forall m, In m Ms -> m <> 0%ZZ) /\
    forall g, length g = length (sigZ S 1) ->
      exists m, In m Ms /\ xorl (sigZ S m) g = false :: flat_map t S.
  Proof.
    move=> /andP [ /List.forallb_forall H0 /List.forallb_forall H ]; split.
    - by move=> m /H0; case: (Z.eqb_spec m 0).
    - move=> g Hg; move: (H g); rewrite -Hg => /(_ (bvecs_in g)) /List.existsb_exists.
      move=> [ [ m s ] [ /in_map_iff [ m' [ [ <- <- ] Hm ] ] /eqP /= Hs ] ].
      by exists m'.
  Qed.

  Lemma covers_core S t Ms : covers S t Ms ->
    (forall q, length (t q) = (if (q =? 2)%ZZ then 3 else 2)%N) ->
    forall n d : Z, n <> 0%ZZ -> d <> 0%ZZ ->
      exists m, In m Ms /\ m <> 0%ZZ /\
        xorb (m <? 0)%ZZ (xorb (n <? 0)%ZZ (d <? 0)%ZZ) = false /\
        forall q, In q S -> xorl (csig q m) (xorl (csig q n) (csig q d)) = t q.
  Proof.
    move=> /covers_spec [ Hnz Hcov ] Ht n d Hn Hd.
    have Hl : forall q z z', length (csig q z) = length (csig q z') by move=> q z z'; rewrite !length_csig.
    have [ m [ Hm Hx ] ] := Hcov (xorl (sigZ S n) (sigZ S d))
      (etrans (length_xorl (etrans (length_sigZ S n) (esym (length_sigZ S d)))) (length_sigZ S n)).
    exists m; split => //; split; first exact: Hnz.
    have Hl1 : forall q, length (csig q n) = length (csig q d) by move=> q; exact: Hl.
    have Hl2 : forall q, length (csig q m) = length (xorl (csig q n) (csig q d)).
    { by move=> q; rewrite length_xorl //; exact: Hl. }
    move: Hx; rewrite /sigZ; cbn [xorl].
    rewrite (@xorl_flat (fun q => csig q n) (fun q => csig q d) S Hl1).
    rewrite (@xorl_flat (fun q => csig q m) (fun q => xorl (csig q n) (csig q d)) S Hl2).
    move=> [ Hs Hf ]; split => //.
    apply: (flat_eq _ Hf) => q; cbv beta.
    rewrite Ht /= !length_xorl ?length_cu //; by case: (q =? 2)%ZZ.
  Qed.

End Bits.

(** * 5. Local square classes of rational numbers

    The textbook description of Q_q^x / Q_q^{x2} (Hensel's lemma; e.g.
    Serre, A Course in Arithmetic, Ch. II, Thm. 3 and 4): x in Q^x is a
    square in Q_q iff x = y^2 w with y in Q^x and w a q-adic unit which
    is a square mod q (q odd), resp. 1 mod 8 (q = 2). A q-adic unit in Q
    is written a / c with integers a, c prime to q; "a / c is a square
    mod q" is "a = z^2 c mod q", and "a / c = 1 mod 8" is "a = c mod 8".
    The predicates below take this description as the definition: no
    q-adic numbers are used, and the textbook equivalence is not
    formalized. *)

Definition qunit (q : nat) (a : Z) : Prop := ~ (Z.of_nat q | a)%ZZ.

Definition sqmod (q : nat) (a c : Z) : Prop :=
  if q == 2%N then (8 | a - c)%ZZ else exists z : Z, (Z.of_nat q | a - z * z * c)%ZZ.

(* x in Q_q^{x2} *)
Definition locsq (q : nat) (x : rat) : Prop :=
  exists (y : rat) (a c : Z),
    y != 0 /\ qunit q a /\ qunit q c /\ x = y ^+ 2 * (zr a / zr c) /\ sqmod q a c.

(* x in the unit nonsquare class of Q_3^x: even valuation, nonsquare unit part *)
Definition unit_nonsq3 (x : rat) : Prop :=
  exists (y : rat) (a c : Z),
    y != 0 /\ qunit 3 a /\ qunit 3 c /\ x = y ^+ 2 * (zr a / zr c) /\
    forall z : Z, ~ (3 | a - z * z * c)%ZZ.

Section RatSig.

  Lemma zr_gt0 (z : Z) : (0 < z)%ZZ -> 0 < zr z.
  Proof.
    move=> Hz; rewrite zr.unlock /Z_to_rat.
    have -> : Z.to_nat (- z) = 0%N by lia.
    rewrite subr0 ltr0n lt0n; apply/eqP; lia.
  Qed.

  Lemma zr_lt0 (z : Z) : (z < 0)%ZZ -> zr z < 0.
  Proof.
    move=> Hz; have -> : z = (- (- z))%ZZ by lia.
    by rewrite zr_opp oppr_lt0; apply: zr_gt0; lia.
  Qed.

  Lemma div_negneg (A D : Z) : (A < 0)%ZZ -> (D < 0)%ZZ -> 0 < zr A / zr D.
  Proof.
    move=> HA HD; rewrite -mulrNN -invrN -!zr_opp.
    by apply: divr_gt0; apply: zr_gt0; lia.
  Qed.

  Lemma pos_of_bits (N0 N1 D : Z) : N0 <> 0%ZZ -> N1 <> 0%ZZ -> D <> 0%ZZ ->
    xorb (N0 <? 0)%ZZ (xorb (N1 <? 0)%ZZ (D <? 0)%ZZ) = false ->
    0 < zr (N0 * N1) / zr D.
  Proof.
    move=> H0 H1 H2.
    case: (Z.ltb_spec N0 0); case: (Z.ltb_spec N1 0); case: (Z.ltb_spec D 0) => //= HD HN1 HN0 _;
      try (apply: div_negneg; nia); apply: divr_gt0; apply: zr_gt0; nia.
  Qed.

  Lemma frac_eq (A B P Q U W : Z) : B <> 0%ZZ -> Q <> 0%ZZ -> W <> 0%ZZ ->
    (A * (Q * Q * W) = P * P * U * B)%ZZ ->
    zr A / zr B = (zr P / zr Q) ^+ 2 * (zr U / zr W).
  Proof.
    move=> HB HQ HW E.
    have HB' := zr_neq0 HB; have HQ' := zr_neq0 HQ; have HW' := zr_neq0 HW.
    rewrite expr2 !mulf_div; apply/eqP; rewrite eqr_div ?mulf_neq0 //.
    by rewrite -!zr_mul E.
  Qed.

  Lemma rep_even (q : Z) (v0 v1 v2 : nat) (u0 u1 u2 : Z) : (2 <= q)%ZZ -> u2 <> 0%ZZ ->
    xorb (Nat.odd v0) (xorb (Nat.odd v1) (Nat.odd v2)) = false ->
    exists y : rat, y != 0 /\
      zr (q ^ Z.of_nat v0 * u0 * (q ^ Z.of_nat v1 * u1)) / zr (q ^ Z.of_nat v2 * u2)
      = y ^+ 2 * (zr (u0 * u1) / zr u2).
  Proof.
    move=> Hq Hu2 Hpar.
    have : Nat.odd (Nat.add (Nat.add v0 v1) v2) = false.
    { move: Hpar; rewrite !Nat.odd_add; by case: (Nat.odd v0); case: (Nat.odd v1); case: (Nat.odd v2). }
    rewrite -Nat.negb_even => /negbFE /Nat.even_spec [ h Hh ].
    have Hqp : forall k : nat, (q ^ Z.of_nat k <> 0)%ZZ by move=> k; apply: Z.pow_nonzero; lia.
    exists (zr (q ^ Z.of_nat h) / zr (q ^ Z.of_nat v2)); split.
    { by rewrite mulf_neq0 ?invr_eq0 ?zr_neq0. }
    apply: frac_eq => //; first by apply Z.neq_mul_0; split.
    have Hpp : (q ^ Z.of_nat h * q ^ Z.of_nat h =
                q ^ Z.of_nat v0 * q ^ Z.of_nat v1 * q ^ Z.of_nat v2)%ZZ.
    { rewrite -!Z.pow_add_r; try lia; congr (q ^ _)%ZZ; lia. }
    rewrite Hpp; lia.
  Qed.

  Lemma vu_parts (q z : Z) : (2 <= q)%ZZ -> z <> 0%ZZ ->
    z = (q ^ Z.of_nat (fst (vu q z)) * snd (vu q z))%ZZ /\ unitb q (snd (vu q z)).
  Proof.
    move=> Hq Hz; split; first by apply: vu_eq; lia.
    by rewrite /unitb; case: (Z.eqb_spec (snd (vu q z) mod q) 0) (vu_unit Hq Hz).
  Qed.

  Lemma loc_sq_of_bits (q N0 N1 D : Z) : In q P8 -> N0 <> 0%ZZ -> N1 <> 0%ZZ -> D <> 0%ZZ ->
    xorl (csig q N0) (xorl (csig q N1) (csig q D)) = false :: ct q ->
    locsq (Z.to_nat q) (zr (N0 * N1) / zr D).
  Proof.
    move=> HP H0 H1 H2; have Hq := P8_pos HP.
    have [ E0 U0 ] := vu_parts Hq H0; have [ E1 U1 ] := vu_parts Hq H1.
    have [ E2 U2 ] := vu_parts Hq H2.
    rewrite /csig; cbn [xorl] => [[ Hpar Hcu ]].
    have /andP [ U01 Hs ] := comp_unit_sq HP U0 U1 U2 Hcu.
    have Hq0 : q <> 0%ZZ by lia.
    have Hu2 : snd (vu q D) <> 0%ZZ by move=> H; move: U2; rewrite H /unitb Zmod_0_l.
    have [ y [ Hy Hx ] ] := @rep_even q _ _ _ (snd (vu q N0)) (snd (vu q N1)) _ Hq Hu2 Hpar.
    have Hqn : Z.of_nat (Z.to_nat q) = q by lia.
    exists y, (snd (vu q N0) * snd (vu q N1))%ZZ, (snd (vu q D)); split => //.
    split; first by rewrite /qunit Hqn -unitb_spec.
    split; first by rewrite /qunit Hqn -unitb_spec.
    split; first by rewrite {1}E0 {1}E1 {1}E2.
    move: Hs; rewrite /sqmod /sqb; case: (Z.eqb_spec q 2) => [ -> | Hq2 ].
    - by move=> /Z.eqb_eq /Z.mod_divide; apply.
    - have -> : (Z.to_nat q == 2%N) = false by apply/eqP; lia.
      move=> /List.existsb_exists [ z [ _ /Z.eqb_eq /Z.mod_divide Hz ] ].
      by exists z; rewrite Hqn; apply: Hz.
  Qed.

  Lemma ns3_of_bits (N0 N1 D : Z) : N0 <> 0%ZZ -> N1 <> 0%ZZ -> D <> 0%ZZ ->
    xorl (csig 3 N0) (xorl (csig 3 N1) (csig 3 D)) = [:: false; true] ->
    unit_nonsq3 (zr (N0 * N1) / zr D).
  Proof.
    move=> H0 H1 H2; have Hq : (2 <= 3)%ZZ by lia.
    have [ E0 U0 ] := vu_parts Hq H0; have [ E1 U1 ] := vu_parts Hq H1.
    have [ E2 U2 ] := vu_parts Hq H2.
    rewrite /csig; cbn [xorl] => [[ Hpar Hcu ]].
    have [ U01 Hs ] := comp_unit_ns3 U0 U1 U2 (ltac:(by rewrite /cu /= Hcu)).
    have Hu2 : snd (vu 3 D) <> 0%ZZ by move=> H; move: U2; rewrite H /unitb Zmod_0_l.
    have [ y [ Hy Hx ] ] := @rep_even 3 _ _ _ (snd (vu 3 N0)) (snd (vu 3 N1)) _ Hq Hu2 Hpar.
    exists y, (snd (vu 3 N0) * snd (vu 3 N1))%ZZ, (snd (vu 3 D)); split => //.
    split; first by rewrite /qunit -unitb_spec.
    split; first by rewrite /qunit -unitb_spec.
    split; first by rewrite {1}E0 {1}E1 {1}E2.
    have H3 : (3 <> 0)%ZZ by lia.
    move=> z Hd; apply: (Hs z); exact: (proj2 (Z.mod_divide _ _ H3) Hd).
  Qed.

End RatSig.

(** * 6. From integer bits to rationals *)

Section CoverRat.

  Lemma zr_iz (i : int) : zr (int_to_Z i) = i%:~R.
  Proof. by rewrite zr.unlock Z_to_rat_int. Qed.

  Lemma rat_frac (b : rat) : b != 0 ->
    exists n d : Z, n <> 0%ZZ /\ d <> 0%ZZ /\ b = zr n / zr d.
  Proof.
    move=> Hb; exists (int_to_Z (numq b)), (int_to_Z (denq b)).
    have Hnz : forall i : int, i != 0 -> int_to_Z i <> 0%ZZ.
    { move=> i Hi H; move: (zr_iz i); rewrite H zr0 => /esym /eqP.
      by rewrite intr_eq0 (negbTE Hi). }
    split; first by apply: Hnz; rewrite numq_eq0.
    split; first by apply: Hnz; exact: denq_neq0.
    by rewrite !zr_iz divq_num_den.
  Qed.

  Lemma covers_rat S t Ms : covers S t Ms ->
    (forall q, length (t q) = (if (q =? 2)%ZZ then 3 else 2)%N) ->
    forall b : rat, b != 0 -> exists m n d : Z,
      In m Ms /\ m <> 0%ZZ /\ n <> 0%ZZ /\ d <> 0%ZZ /\ zr m * b = zr (m * n) / zr d /\
      xorb (m <? 0)%ZZ (xorb (n <? 0)%ZZ (d <? 0)%ZZ) = false /\
      forall q, In q S -> xorl (csig q m) (xorl (csig q n) (csig q d)) = t q.
  Proof.
    move=> Hc Ht b Hb; have [ n [ d [ Hn [ Hd Hbnd ] ] ] ] := rat_frac Hb.
    have [ m [ Hm [ Hm0 [ Hs Hq ] ] ] ] := covers_core Hc Ht Hn Hd.
    exists m, n, d; do 4 (split => //).
    by rewrite Hbnd zr_mul mulrA.
  Qed.

End CoverRat.

(** * 7. The covering properties of the paper (03-parity.tex, Sec. 3.2)

    (par:b-prime-choices): for every b in Q^x some m in M makes
      b' = m b > 0,  b' in Q_2^{x2},  b' in the unit nonsquare class of Q_3^x.
    (par:d-choices): for each m in M, with S(m) = {2,3} u Supp(m), for
      any b <> 0 some m_d in D_m makes
      d = m_d b > 0,  d in Q_q^{x2}  (q in S(m)).
    The list L of pairs (m, D_m) is the representation of FixedData
    ([fd_PhiL], [Phi_math]). *)

Definition S_of (m : rat) : seq nat := [:: 2%N, 3%N & rat_support m].

Definition CoversM (L : seq (rat * seq rat)) : Prop :=
  forall b : rat, b != 0 -> exists mm Dm, List.In (mm, Dm) L /\
    0 < mm * b /\ locsq 2 (mm * b) /\ unit_nonsq3 (mm * b).

Definition CoversD (L : seq (rat * seq rat)) : Prop :=
  forall mm Dm, List.In (mm, Dm) L -> forall b : rat, b != 0 ->
    exists md, List.In md Dm /\ 0 < md * b /\ forall q, q \in S_of mm -> locsq q (md * b).

(** * 8. The covering properties of PhiL0, by computation *)

Section PhiL0Cov.

  Definition tM (q : Z) : list bool := if (q =? 3)%ZZ then [:: false; true] else false :: ct q.
  Definition tD (q : Z) : list bool := false :: ct q.

  Lemma length_tM q : length (tM q) = (if (q =? 2)%ZZ then 3 else 2)%N.
  Proof. by rewrite /tM /ct; case: (Z.eqb_spec q 3) => [ -> | ] //; case: (q =? 2)%ZZ. Qed.

  Lemma length_tD q : length (tD q) = (if (q =? 2)%ZZ then 3 else 2)%N.
  Proof. by rewrite /tD /ct; case: (q =? 2)%ZZ. Qed.

  Lemma MZ_covers : covers [:: 2; 3]%ZZ tM MZ.
  Proof. by vm_compute. Qed.

  Lemma DZ_covers : List.forallb (fun kJ => covers (Sm_of kJ.1) tD (DZ kJ)) Klist.
  Proof. by vm_compute. Qed.

  Lemma Sm_of_P8 : List.forallb (fun kJ => List.forallb (fun q => List.existsb (Z.eqb q) P8)
                                                       (Sm_of kJ.1)) Klist.
  Proof. by vm_compute. Qed.

  (* Supp(u k) is contained in Sm_of k *)
  Lemma supp_check : List.forallb (fun kJ => List.forallb (fun u =>
      all (fun p => List.existsb (Z.eqb (Z.of_nat p)) (Sm_of kJ.1)) (primes (Z.abs_nat (u * kJ.1))))
      unit23) Klist.
  Proof. by vm_compute. Qed.

  Lemma rat_support_zr (z : Z) : rat_support (zr z) = primes (Z.abs_nat z).
  Proof.
    have -> : zr z = (((Z.to_nat z)%:Z - (Z.to_nat (- z))%:Z)%R)%:~R.
    { by rewrite zr.unlock /Z_to_rat intrB -!pmulrn. }
    rewrite /rat_support numq_int denq_int /= cats0.
    congr primes; case: z => [ | p | p ] /=; rewrite ?addn0 // sub0r abszN //.
  Qed.

  Lemma map_List (A B : Type) (f : A -> B) (l : list A) : map f l = List.map f l.
  Proof. by elim: l => [ | x l IH ] //=; rewrite IH. Qed.

  Lemma in_P8 q : List.existsb (Z.eqb q) P8 -> In q P8.
  Proof. by move=> /List.existsb_exists [ x [ Hx /Z.eqb_eq -> ] ]. Qed.

  Theorem PhiL0_CoversM : CoversM PhiL0.
  Proof.
    move=> b Hb.
    have [ m [ n [ d [ Hm [ Hm0 [ Hn [ Hd [ Heq [ Hs Hq ] ] ] ] ] ] ] ] ] :=
      covers_rat MZ_covers length_tM Hb.
    have HM : List.map fst PhiL0Z = MZ by vm_compute.
    have Hm' : In m (List.map fst PhiL0Z) by rewrite HM.
    have [ [ m' Dz ] [ Hmm HIn ] ] := proj1 (in_map_iff _ _ _) Hm'.
    simpl in Hmm; subst m'.
    exists (zr m), (map zr Dz); split.
    { by rewrite /PhiL0 (map_List _ PhiL0Z); apply/in_map_iff; exists (m, Dz). }
    rewrite Heq; split; first exact: pos_of_bits.
    split.
    - have H2 : In 2%ZZ P8 by left.
      exact: (loc_sq_of_bits H2 Hm0 Hn Hd (Hq 2%ZZ (or_introl erefl))).
    - exact: (ns3_of_bits Hm0 Hn Hd (Hq 3%ZZ (or_intror (or_introl erefl)))).
  Qed.

  Theorem PhiL0_CoversD : CoversD PhiL0.
  Proof.
    move=> mm Dm; rewrite /PhiL0 (map_List _ PhiL0Z) => HIn.
    have [ [ mz Dz ] [ Hpair HIn' ] ] := proj1 (in_map_iff _ _ _) HIn.
    case: Hpair => <- <-.
    have [ [ k J ] [ HkJ Hu' ] ] := proj1 (in_flat_map _ _ _) HIn'.
    rewrite map_List in Hu'.
    have [ u [ Hu Hu23 ] ] := proj1 (in_map_iff _ _ _) Hu'.
    case: Hu => <- <- b Hb.
    have Hc := proj1 (List.forallb_forall _ _) DZ_covers _ HkJ.
    have [ md [ n [ d [ Hm [ Hm0 [ Hn [ Hd [ Heq [ Hs Hq ] ] ] ] ] ] ] ] ] := covers_rat Hc length_tD Hb.
    exists (zr md); split; first by rewrite map_List; apply: in_map.
    rewrite Heq; split; first exact: pos_of_bits.
    have HP := proj1 (List.forallb_forall _ _) Sm_of_P8 _ HkJ.
    have HS := proj1 (List.forallb_forall _ _) supp_check _ HkJ.
    have HS' := proj1 (List.forallb_forall _ _) HS _ Hu23.
    move=> q Hq'.
    have Hk : In (Z.of_nat q) (Sm_of k).
    { move: Hq'; rewrite /S_of !inE rat_support_zr => /orP [ /eqP -> | /orP [ /eqP -> | Hp ] ].
      - by rewrite /Sm_of; case: (k =? 1)%ZZ; left.
      - by rewrite /Sm_of; case: (k =? 1)%ZZ; right; left.
      - move: HS' => /allP /(_ _ Hp) /List.existsb_exists [ x [ Hx /Z.eqb_eq -> ] ] //. }
    have Hq8 : In (Z.of_nat q) P8.
    { apply: in_P8; exact: (proj1 (List.forallb_forall _ _) HP _ Hk). }
    rewrite -(Nat2Z.id q); apply: loc_sq_of_bits => //; exact: Hq.
  Qed.

End PhiL0Cov.

(** * 9. PP1_L0 as an instance of the paper's Prop par:pole-parity (1)

    The paper (03-parity.tex, Sec. 3.1-3.2) defines Phi from arbitrary
    finite nonempty lists M, D_m in Q^x and proves integer completeness
    (Prop par:pole-parity, part 1: Q |= Phi(b) for every b in Z) for any
    lists with the covering properties (par:b-prime-choices) and
    (par:d-choices): "The normalizations ... are used only to select
    entries m, m_d for an integer input" (proof via Lemmas
    par:cross-squares, par:descent, par:global-point,
    par:simultaneous-matrices). [PP1_paper] is that claim; [Phi_math] is
    the meaning of the formula Phi ([Phi_holds_iff]). *)

Definition PP1_paper : Prop :=
  forall L : seq (rat * seq rat),
    L <> [::] ->
    (forall mm Dm, List.In (mm, Dm) L -> mm != 0 /\ Dm <> [::] /\ forall md, List.In md Dm -> md != 0) ->
    CoversM L -> CoversD L ->
    forall b : int, Phi_math L (b%:~R : rat).

Theorem PP1_paper_L0 : PP1_paper -> PP1_L0.
Proof.
  move=> H; apply: H; [ exact: PhiL0_nonempty | exact: PhiL0_wf | exact: PhiL0_CoversM | exact: PhiL0_CoversD ].
Qed.
