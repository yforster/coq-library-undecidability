(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The elementary 2-Selmer set of E_l : y^2 = x (x - l) (x + 3l) and the
   two hypotheses of Phase 3 (PLAN.md, task Q1; design in PP1_DESIGN.md,
   Sec. 1.4 and 2.4).

   CONTENTS.
   1. The 2-coverings C_d and the ELEMENTARY 2-Selmer set [in_Sel2 l d]
      of E_l, over int/rat/nat only (no p-adic numbers, no cohomology).
   2. Square classes of pairs and F_2-spans ([sqc], [psq], [in_span2],
      [in_span3]); the classes of the 2-torsion points.
   3. The hypothesis [TwoConverseSel2_El] (a Definition, never an Axiom;
      it is meant to appear as a premise).
   4. Sanity lemmas, PROVED (no axioms), guarding against a mis-statement
      of the Selmer set:
      - [Sel2_O], [Sel2_T0], [Sel2_Tl], [Sel2_T3]: the classes of O and of
        the three 2-torsion points are Selmer classes;
      - [Sel2_point]: the Kummer image of every rational affine point
        (x, y) with x <> 0, x <> l is a Selmer class (x = -3l allowed);
      - [Sel2_int_sol]: more generally every d whose covering C_d has an
        integral (hence rational) point with z0 <> 0 is a Selmer class.
      NOT proved (remark): closure of [in_Sel2 l] under componentwise
      multiplication [pmul] (Sel_2 is a group); it follows from the
      equivalence with the classical Sel_2 described below.
   5. The bridge to [FixedData.El_point] ([TwoConverse_El_point]).

   ---------------------------------------------------------------------
   1. CONVENTIONS.

   The curve is E_l : y^2 = (x - e1)(x - e2)(x - e3) with
       e1 = 0,  e2 = l,  e3 = -3l,
   (the curve of [FixedData.El_point]: y^2 = x (x - l) (x + 3l)), l a
   nonzero integer (nonsingular iff l <> 0). Kummer coordinates are
       kappa(x, y) = (x - e1, x - e2) = (x, x - l)   in (Q^x / Q^x2)^2,
   with the usual replacements at the 2-torsion points (Silverman X.1.4):
       kappa(O)       = (1, 1),
       kappa(0, 0)    = ((e1-e2)(e1-e3), e1 - e2) = (-3 l^2, -l) ~ (-3, -l),
       kappa(l, 0)    = (e2 - e1, (e2-e1)(e2-e3)) = (l, 4 l^2)    ~ (l, 1),
       kappa(-3l, 0)  = (e3 - e1, e3 - e2)        = (-3l, -4l)    ~ (-3l, -l).
   The paper (03-parity.tex, proof of par:descent) uses the coordinates
   (x + 3l, x - l); the two are related by x = (x + 3l)(x - l) modulo
   squares, so the paper's tau_1 = (l, 1), tau_2 = (3, -l) are our
   (l, 1) and (-3l, -l), and the paper's gamma = (beta, 1) is our
   (beta, 1) as well.

   The 2-covering attached to d = (d1, d2) (d1, d2 nonzero integers) is
   the projective curve in P^3 (Silverman X.1.4, homogenized)
       C_d :  d1 z1^2 - d2 z2^2      = (e2 - e1) z0^2 =   l  z0^2,
              d1 z1^2 - d1 d2 z3^2   = (e3 - e1) z0^2 = -3l  z0^2,
   with map to E_l given by x = d1 z1^2 / z0^2 (then x - l = d2 z2^2/z0^2,
   x + 3l = d1 d2 z3^2 / z0^2, y = d1 d2 z1 z2 z3 / z0^3); the points with
   z0 = 0 lie over O. Classical fact (Silverman X.1.4 over a field K of
   characteristic 0, applied to K = Q, Q_p, R): d is in the image of
   E(K)/2E(K) -> (K^x/K^x2)^2 iff C_d(K) is nonempty.

   LOCAL CONDITIONS, elementary form.
   - At a prime p: [locsol l p d] := for every k there are integers
     z0..z3, NOT ALL DIVISIBLE BY p, solving both equations modulo p^k.
     Equivalent to C_d(Q_p) <> {} (classical, NOT proved here): "=>" by
     compactness of P^3(Q_p) (Koenig's lemma on the finitely branching
     tree of primitive solutions modulo p^k, solutions mod p^(k+1) reduce
     to solutions mod p^k); "<=" by scaling a Q_p-point to primitive
     Z_p-coordinates and truncating. Neither smoothness nor Hensel's
     lemma is needed for this equivalence.
   - At infinity: [locsol_inf l d] := there is a rational x with
         x = 0      or  sign x       = sign d1,
         x - l = 0  or  sign (x - l) = sign d2,
         x + 3l = 0 or  sign (x + 3l) = sign (d1 d2).
     This is equivalent to C_d(R) <> {}: a real affine point of C_d is
     exactly a real x satisfying these three conditions (each of
     x - e_i = c u^2 is solvable in real u iff x - e_i = 0 or has the sign
     of c), and the real solution set is a union of the roots (rational)
     and open intervals (containing rationals); the points at infinity
     exist iff d1, d2 > 0, and then every large x works.
   - [in_Sel2 l d] := d1 <> 0 /\ d2 <> 0 /\ locsol_inf l d /\
                      forall p prime, locsol l p d.
   By Silverman X.4.2 (definition of Sel^(2)(E/Q) by local Kummer
   conditions, here via X.1.4 locally) and the two equivalences above,
   [in_Sel2 l d] holds iff the class of d in (Q^x/Q^x2)^2 lies in the
   classical 2-Selmer group Sel_2(E_l/Q). [in_Sel2] depends only on the
   square classes of d1, d2 (rescale z1, z2, z3); this is a consequence of
   the equivalence and is not proved here. No squarefree representatives
   are needed: all statements below compare classes through [sqc]/[psq].

   ---------------------------------------------------------------------
   2. THE HYPOTHESIS [TwoConverseSel2_El] (PP1_DESIGN.md Sec. 1.4).

   For admissible l (l > 0 squarefree, l = 3 mod 4, l = 2 mod 3: the
   curves of Lemma par:descent; the narrow form is preferred as a trusted
   input), and (g1, g2) with
     (i)   in_Sel2 l (g1, g2),
     (ii)  every Selmer class is in the F_2-span of the torsion classes
           tau_l = (l, 1), tau_3 = (-3l, -l) and (g1, g2),
     (iii) (g1, g2) is not in the span of tau_l, tau_3,
   there are rational x, y with y^2 = x (x - l)(x + 3l), x <> 0, and
   x in g1 Q^x2, x - l in g2 Q^x2.

   Under (i)-(iii), since the torsion classes are Selmer classes
   ([Sel2_Tl], [Sel2_T3]) and, for admissible l, tau_l, tau_3 are
   independent (l is not a square as l = 3 mod 4, and -l < 0), the
   Selmer set has EXACTLY 8 classes, spanned by the torsion classes and
   (g1, g2) (that is the formulation of the task statement); (ii)+(iii)
   is the decidable-on-representatives way of saying it.

   Derivation (to be checked by a reviewer; standard, half a page). Let
   r = rank E_l(Q). Write Sel_2 for the classical 2-Selmer group, which
   is the set described by [in_Sel2] (above).
   a. The 2-descent exact sequence (Silverman X.4.2)
        0 -> E(Q)/2E(Q) -> Sel_2(E/Q) -> Sha(E/Q)[2] -> 0
      and E(Q)/2E(Q) = (Z/2)^(r+2) (full rational 2-torsion) give
        dim Sel_2 = r + 2 + dim Sha[2] = 3, i.e. r + dim Sha[2] = 1.
   b. 0 -> E(Q) (x) Q_2/Z_2 -> Sel_{2^oo} -> Sha[2^oo] -> 0 and
      Sha[2^oo] = (Q_2/Z_2)^t + finite give
        s_2(E_l) = corank Sel_{2^oo} = r + t <= r + dim Sha[2] = 1.
   c. Companion Theorem 1.1 ([PointwiseTwoConverse], "A pointwise
      2-converse for elliptic curves with rational two-torsion", OpenAI,
      Oct 7 2026, thm:main: E(Q)[2] <> 0 and s_2(E) in {0,1} imply
      ord_{s=1} L = rank = s_2 and Sha(E/Q) finite) gives Sha finite.
      (Alternatively Theorem 1.1 of [UnrestrictedTwoConverse].)
   d. Cassels-Tate (Cassels 1962; Poonen-Stoll 1999, Sec. 1, Cor. 9):
      the pairing on the finite group Sha[2^oo] is perfect and
      alternating (principal polarization from the rational divisor (O)),
      hence dim Sha[2] is even, hence 0, so r = 1 and
      Sel_2 = E(Q)/2E(Q).
   e. So (g1, g2) = kappa(T) for a rational point T; T is not O or
      2-torsion by (iii), so T = (x, y) affine with x not in {0, l, -3l}
      and kappa(T) = (x, x - l) modulo squares.
   (If tau_l, tau_3 were dependent the same steps work with "<= 3"; for
   admissible l this does not occur.)
   So [TwoConverseSel2_El] is a consequence of companion Theorem 1.1 TOGETHER
   WITH Cassels-Tate, the two Selmer exact sequences, the structure of
   cofinitely generated Z_2-modules, and the identification of the
   elementary Selmer set with Sel_2 (Silverman X.1.4, X.4.2, compactness
   of Z_p). It is NOT "just the companion theorem".

   RISK on record (PP1_DESIGN.md Sec. 4.3 (c), PLAN.md): the companion
   proof uses, in exactly this case (full rational 2-torsion, corank one),
   its Lemma pw:split-witness, whose mod-8 congruence pw:split-mod8 was
   questioned for the Goldfeld manuscript (borism/openai-math-slop#1).

   ---------------------------------------------------------------------
   (Until Phase 4 this file also defined a hypothesis for Dirichlet's
   theorem on primes in arithmetic progressions. The only case needed,
   Dirichlet's theorem for quadratic characters, is now proved in
   PrimePatterns.v, and the definition was removed.)

   No axioms. *)

From Stdlib Require Import Ring Field.

From Undecidability.H10.Rational Require Import FixedData.

From mathcomp Require Import boot order algebra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** * 0. Ring and field tactics for int and rat (local) *)

Lemma TC_int_rt : ring_theory (0 : int) 1 +%R *%R (fun x y => x - y) -%R (@eq int).
Proof.
  split; [ exact: add0r | exact: addrC | exact: addrA | exact: mul1r | exact: mulrC
         | exact: mulrA | exact: mulrDl | done | exact: subrr ].
Qed.

Lemma TC_rat_rt : ring_theory (0 : rat) 1 +%R *%R (fun x y => x - y) -%R (@eq rat).
Proof.
  split; [ exact: add0r | exact: addrC | exact: addrA | exact: mul1r | exact: mulrC
         | exact: mulrA | exact: mulrDl | done | exact: subrr ].
Qed.

Lemma TC_rat_ft : field_theory (0 : rat) 1 +%R *%R (fun x y => x - y) -%R
                    (fun x y => x / y) GRing.inv (@eq rat).
Proof. split; [ exact: TC_rat_rt | by [] | done | move=> p Hp; apply: mulVf; exact/eqP ]. Qed.

Add Ring TC_int_ring : TC_int_rt.
Add Field TC_rat_field : TC_rat_ft.

(** * 1. The coverings C_d and the elementary 2-Selmer set *)

(* a * zi^2 - b * zj^2 - e * z0^2 *)
Definition qform (a b e z0 zi zj : int) : int := a * zi ^+ 2 - b * zj ^+ 2 - e * z0 ^+ 2.

Section Sel2.

  Variable l : int.

  (* C_d :  d1 z1^2 - d2 z2^2 = l z0^2,   d1 z1^2 - d1 d2 z3^2 = -3l z0^2 *)
  Definition eqn1 (d : int * int) (z0 z1 z2 z3 : int) : int := qform d.1 d.2 l z0 z1 z2.
  Definition eqn2 (d : int * int) (z0 z1 z2 z3 : int) : int :=
    qform d.1 (d.1 * d.2) (- (3 * l)) z0 z1 z3.

  (* not all coordinates divisible by p *)
  Definition primitive (p : nat) (z0 z1 z2 z3 : int) : bool :=
    ~~ [&& (p%:Z %| z0)%Z, (p%:Z %| z1)%Z, (p%:Z %| z2)%Z & (p%:Z %| z3)%Z].

  (* C_d has a primitive solution modulo p^k for every k  (<-> C_d(Q_p) <> {}) *)
  Definition locsol (p : nat) (d : int * int) : Prop :=
    forall k : nat, exists z0 z1 z2 z3 : int,
      primitive p z0 z1 z2 z3 /\
      ((p ^ k)%:Z %| eqn1 d z0 z1 z2 z3)%Z /\ ((p ^ k)%:Z %| eqn2 d z0 z1 z2 z3)%Z.

  (* C_d(R) <> {}: a rational x with x - e_i zero or of the sign of the
     corresponding coefficient d1, d2, d1 d2 *)
  Definition locsol_inf (d : int * int) : Prop :=
    exists x : rat,
      (x = 0 \/ 0 < x * d.1%:~R) /\
      (x - l%:~R = 0 \/ 0 < (x - l%:~R) * d.2%:~R) /\
      (x + 3 * l%:~R = 0 \/ 0 < (x + 3 * l%:~R) * (d.1 * d.2)%:~R).

  (* the elementary 2-Selmer set of E_l (<-> classical Sel_2(E_l/Q)) *)
  Definition in_Sel2 (d : int * int) : Prop :=
    d.1 != 0 /\ d.2 != 0 /\ locsol_inf d /\ forall p : nat, prime p -> locsol p d.

  (** classes of O and of the 2-torsion points (0,0), (l,0), (-3l,0) *)
  Definition tors_O  : int * int := (1, 1).
  Definition tors_T0 : int * int := (-3, - l).
  Definition tors_Tl : int * int := (l, 1).
  Definition tors_T3 : int * int := (- (3 * l), - l).

End Sel2.

(** * 2. Square classes and F_2-spans *)

(* x in g Q^x2 *)
Definition sqc (x : rat) (g : int) : Prop := exists s : rat, s != 0 /\ x = g%:~R * s ^+ 2.

(* equality of square classes of pairs *)
Definition psq (d e : int * int) : Prop := sqc d.1%:~R e.1 /\ sqc d.2%:~R e.2.

Definition pmul (a b : int * int) : int * int := (a.1 * b.1, a.2 * b.2).
Definition ppow (i : bool) (a : int * int) : int * int := if i then a else (1, 1).

Definition in_span2 (a b d : int * int) : Prop :=
  exists i j : bool, psq d (pmul (ppow i a) (ppow j b)).

Definition in_span3 (a b c d : int * int) : Prop :=
  exists i j k : bool, psq d (pmul (ppow i a) (pmul (ppow j b) (ppow k c))).

(** * 3. The hypothesis *)

(* squarefree: no square n^2 > 1 divides l *)
Definition sqfree_int (l : int) : Prop := forall n : nat, (1 < n)%N -> ~~ (n * n %| `|l|)%N.

(* the curves of Lemma par:descent *)
Definition admissible_l (l : int) : Prop :=
  0 < l /\ sqfree_int l /\ (l %% 4)%Z = 3 /\ (l %% 3)%Z = 2.

(* Elementary consequence of companion Theorem 1.1 + Cassels-Tate + the
   classical Selmer sequences (see the header, Sec. 2): an 8-element
   2-Selmer set spanned by the torsion classes and (g1,g2) is realized
   by a rational point of class (g1,g2). *)
Definition TwoConverseSel2_El : Prop :=
  forall l : int, admissible_l l ->
  forall g1 g2 : int, in_Sel2 l (g1, g2) ->
  (forall d, in_Sel2 l d -> in_span3 (tors_Tl l) (tors_T3 l) (g1, g2) d) ->
  ~ in_span2 (tors_Tl l) (tors_T3 l) (g1, g2) ->
  exists x y : rat, y ^+ 2 = x * (x - l%:~R) * (x + 3 * l%:~R) /\
                    x != 0 /\ sqc x g1 /\ sqc (x - l%:~R) g2.

(** * 4. Sanity lemmas *)

Section sanity.

  Variable l : int.

  (* reduction to a primitive exact solution *)
  Lemma prim_exact (p : nat) (d : int * int) (z0 z1 z2 z3 : int) : prime p ->
    ~~ [&& z0 == 0, z1 == 0, z2 == 0 & z3 == 0] ->
    eqn1 l d z0 z1 z2 z3 = 0 -> eqn2 l d z0 z1 z2 z3 = 0 ->
    exists w0 w1 w2 w3, primitive p w0 w1 w2 w3 /\
      eqn1 l d w0 w1 w2 w3 = 0 /\ eqn2 l d w0 w1 w2 w3 = 0.
  Proof.
    move=> pp.
    have [n] := ubnP (`|z0| + `|z1| + `|z2| + `|z3|)%N.
    elim: n z0 z1 z2 z3 => // n IH z0 z1 z2 z3 Hlt Hnz E1 E2.
    case Hp : (primitive p z0 z1 z2 z3); first by exists z0, z1, z2, z3.
    move: Hlt Hnz E1 E2; move: Hp; rewrite /primitive => /negbFE /and4P [/dvdzP [w0 ->] /dvdzP [w1 ->]
                                                   /dvdzP [w2 ->] /dvdzP [w3 ->]] Hlt Hnz E1 E2.
    have Hp0 : (p%:Z) != 0 by rewrite eqz_nat; apply/eqP => H0; move: pp; rewrite H0.
    have Hp2 : (1 < p)%N by exact: prime_gt1.
    have Hw : ~~ [&& w0 == 0, w1 == 0, w2 == 0 & w3 == 0].
    { apply: contra Hnz => /and4P [/eqP -> /eqP -> /eqP -> /eqP ->]; by rewrite !mul0r eqxx. }
    have Es (a b e z0' zi zj : int) :
      qform a b e (z0' * p%:Z) (zi * p%:Z) (zj * p%:Z) = qform a b e z0' zi zj * (p%:Z ^+ 2).
    { rewrite /qform !expr2; ring. }
    apply: (IH w0 w1 w2 w3) => //.
    - move: Hlt; rewrite !abszM /= ltnS.
      rewrite -!mulnDl => H; apply: (leq_trans _ H).
      set s := (_ + _ + _ + _)%N.
      have Hs : (0 < s)%N.
      { by rewrite /s lt0n !addn_eq0 !absz_eq0 -!andbA. }
      by rewrite /= -{1}[s]muln1 ltn_pmul2l.
    - by move: E1; rewrite /eqn1 Es => /eqP; rewrite mulf_eq0 expf_eq0 (negbTE Hp0) andbF orbF => /eqP.
    - by move: E2; rewrite /eqn2 Es => /eqP; rewrite mulf_eq0 expf_eq0 (negbTE Hp0) andbF orbF => /eqP.
  Qed.

  (* c u^2 is zero or has the sign of c *)
  Lemma sq_case (c u : rat) : c != 0 -> c * u ^+ 2 = 0 \/ 0 < c * u ^+ 2 * c.
  Proof.
    move=> Hc; have [-> | Hu] := eqVneq u 0; first by left; rewrite expr0n mulr0.
    right; have -> : c * u ^+ 2 * c = (c * u) ^+ 2 by rewrite !expr2; ring.
    by rewrite lt0r sqr_ge0 andbT sqrf_eq0 mulf_neq0.
  Qed.

  Lemma sq_case' (x c u : rat) : c != 0 -> x = c * u ^+ 2 -> x = 0 \/ 0 < x * c.
  Proof. by move=> Hc ->; exact: sq_case. Qed.

  Lemma TC_intr0 (a : int) : (a%:~R : rat) = 0 -> a = 0.
  Proof. by move/eqP; rewrite intr_eq0 => /eqP. Qed.

  (* an integral point of C_d with z0 <> 0 makes d a Selmer class *)
  Lemma Sel2_int_sol (d : int * int) (z0 z1 z2 z3 : int) :
    d.1 != 0 -> d.2 != 0 -> z0 != 0 ->
    eqn1 l d z0 z1 z2 z3 = 0 -> eqn2 l d z0 z1 z2 z3 = 0 -> in_Sel2 l d.
  Proof.
    case: d => d1 d2 /= Hd1 Hd2 Hz0 E1 E2.
    split; [ done | split; [ done | split ] ].
    - (* at infinity *)
      have Q1 : (d1%:~R * z1%:~R ^+ 2 - d2%:~R * z2%:~R ^+ 2 - l%:~R * z0%:~R ^+ 2 : rat) = 0.
      { move/eqP: E1; rewrite -(intr_eq0 rat) /eqn1 /qform !rmorphB !rmorphM !expr2.
        by move/eqP. }
      have Q2 : (d1%:~R * z1%:~R ^+ 2 - (d1 * d2)%:~R * z3%:~R ^+ 2 + 3 * l%:~R * z0%:~R ^+ 2 : rat) = 0.
      { move/eqP: E2; rewrite -(intr_eq0 rat) /eqn2 /qform !rmorphB !rmorphM rmorphN rmorphM.
        rewrite rmorph_nat mulNr opprK !expr2.
        by move/eqP. }
      have Hz0r : (z0%:~R : rat) != 0 by rewrite intr_eq0.
      have Hd1r : (d1%:~R : rat) != 0 by rewrite intr_eq0.
      have Hd2r : (d2%:~R : rat) != 0 by rewrite intr_eq0.
      have Hd12r : ((d1 * d2)%:~R : rat) != 0 by rewrite intr_eq0 mulf_neq0.
      set x := d1%:~R * (z1%:~R / z0%:~R) ^+ 2 : rat.
      exists x; split; [ | split ].
      + exact: (sq_case' Hd1r).
      + apply: (sq_case' Hd2r (u := z2%:~R / z0%:~R)).
        have Hl : (l%:~R : rat) = (d1%:~R * z1%:~R ^+ 2 - d2%:~R * z2%:~R ^+ 2) / z0%:~R ^+ 2.
        { have -> : (d1%:~R * z1%:~R ^+ 2 - d2%:~R * z2%:~R ^+ 2 : rat) = l%:~R * z0%:~R ^+ 2.
          { apply/eqP; rewrite -subr_eq0; apply/eqP; rewrite -Q1; ring. }
          by rewrite mulfK // expf_neq0. }
        rewrite /x Hl; field; try exact/eqP.
      + apply: (sq_case' Hd12r (u := z3%:~R / z0%:~R)).
        have Hl : (3 * l%:~R : rat) = ((d1 * d2)%:~R * z3%:~R ^+ 2 - d1%:~R * z1%:~R ^+ 2) / z0%:~R ^+ 2.
        { have -> : ((d1 * d2)%:~R * z3%:~R ^+ 2 - d1%:~R * z1%:~R ^+ 2 : rat) = 3 * l%:~R * z0%:~R ^+ 2.
          { apply/eqP; rewrite -subr_eq0; apply/eqP; rewrite -[RHS]oppr0 -Q2; ring. }
          by rewrite mulfK // expf_neq0. }
        rewrite /x Hl; field; try exact/eqP.
    - (* at every prime *)
      move=> p pp k.
      have Hnz : ~~ [&& z0 == 0, z1 == 0, z2 == 0 & z3 == 0] by rewrite (negbTE Hz0).
      have [w0 [w1 [w2 [w3 [Hw [F1 F2]]]]]] := prim_exact pp Hnz E1 E2.
      by exists w0, w1, w2, w3; rewrite F1 F2 !dvdz0.
  Qed.

  (* clearing denominators *)
  Lemma clear_den (u1 u2 u3 : rat) : exists m z1 z2 z3 : int, m != 0 /\
    u1 * m%:~R = z1%:~R /\ u2 * m%:~R = z2%:~R /\ u3 * m%:~R = z3%:~R.
  Proof.
    exists (denq u1 * denq u2 * denq u3), (numq u1 * denq u2 * denq u3),
           (denq u1 * numq u2 * denq u3), (denq u1 * denq u2 * numq u3).
    split; first by rewrite !mulf_neq0 ?denq_neq0.
    rewrite !intrM !numqE; split; [ | split ]; ring.
  Qed.

  (* a rational solution of the affine covering makes d a Selmer class *)
  Lemma Sel2_rat_sol (d1 d2 : int) (u1 u2 u3 : rat) :
    d1 != 0 -> d2 != 0 ->
    d1%:~R * u1 ^+ 2 - d2%:~R * u2 ^+ 2 = l%:~R ->
    d1%:~R * u1 ^+ 2 - (d1 * d2)%:~R * u3 ^+ 2 = - (3 * l%:~R) ->
    in_Sel2 l (d1, d2).
  Proof.
    move=> Hd1 Hd2 R1 R2.
    have [m [z1 [z2 [z3 [Hm [H1 [H2 H3]]]]]]] := clear_den u1 u2 u3.
    apply: (Sel2_int_sol (z0 := m) (z1 := z1) (z2 := z2) (z3 := z3)) => //.
    - apply: TC_intr0; rewrite /eqn1 /qform !intrB !expr2 !intrM /= -H1 -H2 -R1.
      rewrite !expr2; ring.
    - apply: TC_intr0; rewrite /eqn2 /qform !intrB !expr2 !intrM intrN intrM /= -H1 -H3 rmorph_nat.
      have -> : (3%:R * l%:~R : rat) = d1%:~R * d2%:~R * u3 ^+ 2 - d1%:~R * u1 ^+ 2.
      { by rewrite -intrM -[LHS]opprK -R2 opprB. }
      rewrite !expr2; ring.
  Qed.

  (** (d) the trivial class (O; points at infinity of C_(1,1)) *)
  Lemma Sel2_O : in_Sel2 l tors_O.
  Proof.
    rewrite /tors_O; split; [ done | split; [ done | split ] ].
    - rewrite /locsol_inf /= mulr1 rmorph1; setoid_rewrite mulr1.
      have H3 : (0 : rat) < 3 by [].
      have [Hl | Hl | ->] := ltrgtP l 0.
      + have Hlr : (l%:~R : rat) < 0 by rewrite ltrz0.
        have H3l : (0 : rat) < - (3 * l%:~R) by rewrite oppr_gt0 pmulr_rlt0.
        exists (- (3 * l%:~R)); split; [ right | split; [ right | left ] ]; try done.
        * by rewrite addr_gt0 // oppr_gt0.
        * exact: addNr.
      + have Hlr : (0 : rat) < l%:~R by rewrite ltr0z.
        exists (l%:~R); split; [ right | split; [ left | right ] ]; try done.
        * exact: subrr.
        * by rewrite addr_gt0 // mulr_gt0.
      + exists 0; rewrite rmorph0; split; [ left | split; left ]; by rewrite ?subrr ?mulr0 ?addr0.
    - move=> p pp k; exists 0, 1, 1, 1.
      split; [ | split ].
      + apply/negP => /and4P [_ H _ _]; move: H; rewrite dvdz1 /= => /eqP H1.
        by move: pp; rewrite H1.
      + by rewrite /eqn1 /qform /= !expr2 !mulr0 !mul1r !subr0 subrr dvdz0.
      + by rewrite /eqn2 /qform /= !expr2 !mulr0 !mul1r !subr0 subrr dvdz0.
  Qed.

  (** (a) the three 2-torsion classes *)
  Ltac tors_tac Hl :=
    rewrite /= ?oppr_eq0 ?mulf_eq0 ?negb_or ?Hl //;
    rewrite /eqn1 /eqn2 /qform /= !expr2 ?mulrS ?mulr0n; ring.

  Lemma Sel2_T0 : l != 0 -> in_Sel2 l (tors_T0 l).
  Proof.
    move=> Hl; apply: (Sel2_int_sol (z0 := 1) (z1 := 0) (z2 := 1) (z3 := 1)); tors_tac Hl.
  Qed.

  Lemma Sel2_Tl : l != 0 -> in_Sel2 l (tors_Tl l).
  Proof.
    move=> Hl; apply: (Sel2_int_sol (z0 := 1) (z1 := 1) (z2 := 0) (z3 := 2)); tors_tac Hl.
  Qed.

  Lemma Sel2_T3 : l != 0 -> in_Sel2 l (tors_T3 l).
  Proof.
    move=> Hl; apply: (Sel2_int_sol (z0 := 1) (z1 := 1) (z2 := 2) (z3 := 0)); tors_tac Hl.
  Qed.

  (** (b) the Kummer image of a rational point (x, y), x <> 0, l *)
  Lemma Sel2_point (x y : rat) (d1 d2 : int) :
    y ^+ 2 = x * (x - l%:~R) * (x + 3 * l%:~R) ->
    d1 != 0 -> d2 != 0 -> sqc x d1 -> sqc (x - l%:~R) d2 ->
    in_Sel2 l (d1, d2).
  Proof.
    move=> Hy Hd1 Hd2 [s1 [Hs1 Hx]] [s2 [Hs2 Hxl]].
    have Hd1r : (d1%:~R : rat) != 0 by rewrite intr_eq0.
    have Hd2r : (d2%:~R : rat) != 0 by rewrite intr_eq0.
    have Hl : (l%:~R : rat) = d1%:~R * s1 ^+ 2 - d2%:~R * s2 ^+ 2.
    { by rewrite -Hx -Hxl opprB addrC subrK. }
    apply: (Sel2_rat_sol (u1 := s1) (u2 := s2) (u3 := y / (d1%:~R * d2%:~R * s1 * s2))) => //.
    rewrite intrM expr_div_n Hy Hx Hl.
    field; rewrite ?Hd1r ?Hd2r ?Hs1 ?Hs2 //; try (repeat split; apply/eqP; done).
  Qed.

End sanity.

(** * 5. Bridge to [El_point] *)

Lemma sqc_El_point (l : int) (g1 g2 : int) :
  (exists x y : rat, y ^+ 2 = x * (x - l%:~R) * (x + 3 * l%:~R) /\
                     x != 0 /\ sqc x g1 /\ sqc (x - l%:~R) g2) ->
  forall b' : rat, sqc b' g1 -> El_point (l%:~R : rat) b'.
Proof.
  move=> [x [y [Hy [Hx0 [[s [Hs Hxs]] _]]]]] b' [t [Ht Hb']].
  exists x, y, (s / t); split; [ by rewrite mulf_neq0 ?invr_eq0 | split; last exact: Hy ].
  rewrite Hxs Hb' expr_div_n; field; try exact/eqP.
Qed.

(* the conclusion of [TwoConverseSel2_El] in the form used by [Phi_math] *)
Lemma TwoConverse_El_point : TwoConverseSel2_El ->
  forall l : int, admissible_l l ->
  forall g1 g2 : int, in_Sel2 l (g1, g2) ->
  (forall d, in_Sel2 l d -> in_span3 (tors_Tl l) (tors_T3 l) (g1, g2) d) ->
  ~ in_span2 (tors_Tl l) (tors_T3 l) (g1, g2) ->
  forall b' : rat, sqc b' g1 -> El_point (l%:~R : rat) b'.
Proof. move=> H l Hl g1 g2 H1 H2 H3; exact: sqc_El_point (H l Hl g1 g2 H1 H2 H3). Qed.
