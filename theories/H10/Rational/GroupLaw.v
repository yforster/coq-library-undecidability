(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* The group law of the chord-tangent addition (PLAN P6, Phase 2D).

   Proves the hypothesis [E1] of [StdHyps] (FixedData.v) as a theorem,
   [E1_thm], under the sole premise that [fd_P0 D] lies on the curve.

   STRATEGY.
   1. Generic part (Section [wlaw]): an arbitrary [fieldType] K with
      2 <> 0, and the curve  y^2 = x^3 + A2 x^2 + A4 x + A6  with the
      nonsingularity condition "f(x) = 0 -> f'(x) <> 0". The extra
      coefficients A2, A6 are a device for the proofs: a polynomial
      identity which holds on the curve becomes a pure rational-function
      identity (MathComp [field]) after solving the curve equations of
      the points involved LINEARLY for A2 (Lagrange interpolation through
      three points), A4 (two points) or A6 (one point). Nothing about
      A2, A6 is used later: the curve of the paper is A2 = A6 = 0.
   2. Every sum of two affine points is [wsum l x1 y1 x2] for a slope l
      (chord or tangent). The workhorse [sum_eq] reduces an equality of
      two such sums with slopes n/d, n'/d' to two polynomial identities
      in n, d, n', d' that are free of these denominators, so [field]
      only ever sees "simple" denominators (differences of coordinates
      of the free points, 2, y).
   3. Group laws: closure, commutativity, inverses, negation of sums,
      the cancellation law (P + Q) - Q = P (by direct computation, using
      nonsingularity in one degenerate case), left cancellation.
   4. Associativity by a case analysis which needs only FOUR polynomial
      identities (Friedl-style; all other cases are reduced to these by
      commutativity and cancellation):
        (I)   generic: P, Q, R with distinct x, all sums by chords;
        (II)  P + Q = R (tangent at R), with P rewritten as R - Q so that
              no nested denominators occur;
        (III) 2 (P + Q) = 2 P for a 2-torsion point Q;
        (IV)  2P + R = P + (P + R), all by chords except 2P.
      The case 2(2P) = P + (P + 2P) is reduced to (IV) for the triple
      (2P, 2P, -P), with the 5-torsion subcase done by cancellation.
   5. Transport: [qe F] is a field when 2 is not a square in F
      ([QF F h], a copy of the ring structure with a field instance);
      [ec_add] and [on_curve] on [qe F] are [wadd] and [won] for
      A2 = A6 = 0, A4 = aE. [ADDrel] holds for [ec_add] and is
      functional. The multiples [mulQ] form a homomorphism Z -> E, hence
      [E1_thm].

   No axioms. *)

From HB Require Import structures.
From mathcomp Require Import boot order algebra.

From Undecidability.H10.Rational Require Import FixedData.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset Default Proof Using.

Local Open Scope ring_scope.

(** * 1. The generic chord-tangent law *)

Section wlaw.

  Variable K : fieldType.
  Variables A2 A4 A6 : K.

  Definition fc (x : K) : K := x ^+ 3 + A2 * x ^+ 2 + A4 * x + A6.
  Definition fd (x : K) : K := 3%:R * x ^+ 2 + 2%:R * A2 * x + A4.

  Definition won (p : K * K) : Prop := p.2 ^+ 2 = fc p.1.
  Definition won_pt (P : option (K * K)) : Prop := if P is Some p then won p else True.

  (* the sum of (x1, y1) and a point with abscissa x2 on the line of slope l *)
  Definition wsum (l x1 y1 x2 : K) : K * K :=
    (l ^+ 2 - A2 - x1 - x2, l * (x1 - (l ^+ 2 - A2 - x1 - x2)) - y1).

  Definition wadd (P Q : option (K * K)) : option (K * K) :=
    match P, Q with
    | None, _ => Q
    | _, None => P
    | Some (x1, y1), Some (x2, y2) =>
        if x1 == x2 then
          if y1 == - y2 then None else Some (wsum (fd x1 / (2%:R * y1)) x1 y1 x1)
        else Some (wsum ((y2 - y1) / (x2 - x1)) x1 y1 x2)
    end.

  Definition wneg (P : option (K * K)) : option (K * K) :=
    if P is Some (x, y) then Some (x, - y) else None.

  Hypothesis two0 : 2%:R != 0 :> K.
  Hypothesis nonsing : forall x, fc x = 0 -> fd x != 0.

  Ltac nz1 := solve [ done | rewrite oppr_eq0; done | rewrite -opprB oppr_eq0; done
                    | apply: mulf_neq0; nz1 | apply: expf_neq0; nz1 ].
  Ltac nzs := try nz1.

  (** ** Elementary facts *)

  Lemma y_opp0 (y : K) : y = - y -> y = 0.
  Proof.
    move=> e; have : 2%:R * y = 0 by rewrite mulr_natl mulr2n {1}e addNr.
    by move/eqP; rewrite mulf_eq0 (negbTE two0) /= => /eqP.
  Qed.

  Lemma y_sq (y1 y2 : K) : y1 ^+ 2 = y2 ^+ 2 -> y1 = y2 \/ y1 = - y2.
  Proof. by move/eqP; rewrite eqf_sqr => /orP [] /eqP; [ left | right ]. Qed.

  Lemma won_x (x y1 y2 : K) : won (x, y1) -> won (x, y2) -> y1 = y2 \/ y1 = - y2.
  Proof. by rewrite /won /= => h1 h2; apply: y_sq; rewrite h1 h2. Qed.

  Lemma won_neg (x y : K) : won (x, y) -> won (x, - y).
  Proof. by rewrite /won /= sqrrN. Qed.

  Lemma wneg_on P : won_pt P -> won_pt (wneg P).
  Proof. by case: P => [ [ x y ] | ] //= /won_neg. Qed.

  Lemma wnegK P : wneg (wneg P) = P.
  Proof. by case: P => [ [ x y ] | ] //=; rewrite opprK. Qed.

  Lemma wadd0P P : wadd None P = P. Proof. by []. Qed.
  Lemma waddP0 P : wadd P None = P. Proof. by case: P => [ [] | ]. Qed.

  Lemma wadd_ch x1 y1 x2 y2 : x1 != x2 ->
    wadd (Some (x1, y1)) (Some (x2, y2)) = Some (wsum ((y2 - y1) / (x2 - x1)) x1 y1 x2).
  Proof. by move=> h /=; rewrite (negbTE h). Qed.

  Lemma wadd_tg x1 y1 : y1 != 0 ->
    wadd (Some (x1, y1)) (Some (x1, y1)) = Some (wsum (fd x1 / (2%:R * y1)) x1 y1 x1).
  Proof.
    move=> h /=; rewrite eqxx ifF //; apply/negP => /eqP /y_opp0 e.
    by move: h; rewrite e eqxx.
  Qed.

  Lemma wadd_op x1 y1 x2 y2 : x1 = x2 -> y1 = - y2 -> wadd (Some (x1, y1)) (Some (x2, y2)) = None.
  Proof. by move=> -> -> /=; rewrite !eqxx. Qed.

  Lemma waddN P : wadd P (wneg P) = None.
  Proof. by case: P => [ [ x y ] | ] //; apply: wadd_op; rewrite ?opprK. Qed.

  Lemma waddNl P : wadd (wneg P) P = None.
  Proof. by case: P => [ [ x y ] | ] //; apply: wadd_op. Qed.

  (* the three cases for two affine points on the curve *)
  Lemma wcases x1 y1 x2 y2 : won (x1, y1) -> won (x2, y2) ->
       (x1 = x2 /\ y1 = - y2)
    \/ (x1 = x2 /\ y1 = y2 /\ y1 != 0)
    \/ x1 != x2.
  Proof.
    move=> h1 h2; case: (eqVneq x1 x2) => [ ex | ]; last by right; right.
    subst x2; case: (won_x h1 h2) => [ ey | ey ]; last by left.
    subst y2; case: (eqVneq y1 0) => [ e0 | ]; last by right; left.
    by left; rewrite e0 oppr0.
  Qed.

  (** ** Negation of a sum *)

  Lemma wsumN l x1 y1 x2 :
    (wsum (- l) x1 (- y1) x2) = ((wsum l x1 y1 x2).1, - (wsum l x1 y1 x2).2).
  Proof. by rewrite /wsum /=; congr pair; ring. Qed.

  Lemma wneg_add P Q : wneg (wadd P Q) = wadd (wneg P) (wneg Q).
  Proof.
    case: P => [ [ x1 y1 ] | ] //; case: Q => [ [ x2 y2 ] | ] //=.
    case: (eqVneq x1 x2) => [ ex | ne ] /=.
    - subst x2; have -> : (- y1 == - - y2) = (y1 == - y2) by rewrite eqr_opp.
      case: (y1 == - y2) => //.
      have -> : fd x1 / (2%:R * - y1) = - (fd x1 / (2%:R * y1)).
      { by rewrite mulrN invrN mulrN. }
      by rewrite wsumN.
    - have -> : (- y2 - - y1) / (x2 - x1) = - ((y2 - y1) / (x2 - x1)).
      { by rewrite -mulNr; congr (_ * _); ring. }
      by rewrite wsumN.
  Qed.

  (** ** Commutativity *)

  Lemma wadd_comm P Q : won_pt P -> won_pt Q -> wadd P Q = wadd Q P.
  Proof.
    case: P => [ [ x1 y1 ] | ]; last by move=> _ _; rewrite waddP0.
    case: Q => [ [ x2 y2 ] | ] h1 h2; last by [].
    case: (wcases h1 h2) => [ [ ex ey ] | [ [ ex [ ey ny ] ] | ne ] ].
    - by rewrite !wadd_op // ey opprK.
    - by subst.
    - rewrite !wadd_ch // 1?eq_sym //; congr Some; rewrite /wsum /=.
      have -> : (y1 - y2) / (x1 - x2) = (y2 - y1) / (x2 - x1).
      { by rewrite -[x1 - x2]opprB -[y1 - y2]opprB invrN mulrNN. }
      congr pair; first by ring.
      set l := (y2 - y1) / (x2 - x1).
      have hl : l * (x2 - x1) = y2 - y1.
      { by rewrite /l mulfVK // subr_eq0 eq_sym. }
      clearbody l; have -> : y2 = l * (x2 - x1) + y1 by rewrite hl subrK.
      ring.
  Qed.

  (** ** Linear-combination helpers *)

  Lemma eq_from1 (a b c d k : K) : a = b -> c - d = k * (a - b) -> c = d.
  Proof. by move=> -> h; apply/eqP; rewrite -subr_eq0 h subrr mulr0. Qed.

  Lemma eq_from3 (a1 b1 a2 b2 a3 b3 k1 k2 k3 c d : K) : a1 = b1 -> a2 = b2 -> a3 = b3 ->
    c - d = k1 * (a1 - b1) + k2 * (a2 - b2) + k3 * (a3 - b3) -> c = d.
  Proof.
    move=> -> -> -> h; apply/eqP; rewrite -subr_eq0 h !subrr !mulr0 !addr0 //.
  Qed.

  (** ** Closure *)

  Lemma eA6_of x1 y1 : won (x1, y1) -> A6 = y1 ^+ 2 - x1 ^+ 3 - A2 * x1 ^+ 2 - A4 * x1.
  Proof. rewrite /won /fc /= => ->; ring. Qed.

  Lemma eA4_of x1 y1 x2 y2 : won (x1, y1) -> won (x2, y2) -> x1 != x2 ->
    A4 = ((y1 ^+ 2 - x1 ^+ 3 - A2 * x1 ^+ 2) - (y2 ^+ 2 - x2 ^+ 3 - A2 * x2 ^+ 2)) / (x1 - x2).
  Proof.
    rewrite /won /fc /= => -> -> ne; have h : x1 - x2 != 0 by rewrite subr_eq0.
    field by nzs.
  Qed.

  Lemma wsum_on_ch x1 y1 x2 y2 : won (x1, y1) -> won (x2, y2) -> x1 != x2 ->
    won (wsum ((y2 - y1) / (x2 - x1)) x1 y1 x2).
  Proof.
    move=> h1 h2 ne; have h : x1 - x2 != 0 by rewrite subr_eq0.
    rewrite /won /fc /wsum /= (eA6_of h1) (eA4_of h1 h2 ne).
    field by nzs.
  Qed.

  Lemma wsum_on_tg x1 y1 : won (x1, y1) -> y1 != 0 ->
    won (wsum (fd x1 / (2%:R * y1)) x1 y1 x1).
  Proof.
    move=> h1 ny; rewrite /won /fc /fd /wsum /= (eA6_of h1).
    field by nzs.
  Qed.

  Lemma wadd_on P Q : won_pt P -> won_pt Q -> won_pt (wadd P Q).
  Proof.
    case: P => [ [ x1 y1 ] | ] //; case: Q => [ [ x2 y2 ] | ] // h1 h2.
    case: (wcases h1 h2) => [ [ ex ey ] | [ [ ex [ ey ny ] ] | ne ] ].
    - by rewrite wadd_op.
    - by subst; rewrite wadd_tg //; apply: wsum_on_tg.
    - by rewrite wadd_ch //; apply: wsum_on_ch.
  Qed.

  (** ** The secant identity *)

  Lemma secant x1 y1 x2 y2 : won (x1, y1) -> won (x2, y2) -> x1 != x2 ->
    (y2 - y1) / (x2 - x1) * (y1 + y2) = x1 ^+ 2 + x1 * x2 + x2 ^+ 2 + A2 * (x1 + x2) + A4.
  Proof.
    move=> h1 h2 ne; have h : x1 - x2 != 0 by rewrite subr_eq0.
    apply: (mulIf h).
    have -> : (y2 - y1) / (x2 - x1) * (y1 + y2) * (x1 - x2) = y1 ^+ 2 - y2 ^+ 2.
    { field by nzs. }
    move: h1 h2; rewrite /won /fc /= => -> ->; ring.
  Qed.

  (** ** Cancellation  (P + Q) - Q = P *)

  (* generic case: the line through S = P + Q and -Q has slope -l *)
  Lemma canc_gen l x1 y1 x2 y2 xs ys : y2 = y1 + l * (x2 - x1) ->
    wsum l x1 y1 x2 = (xs, ys) -> x2 != xs ->
    wsum ((- y2 - ys) / (x2 - xs)) xs ys x2 = (x1, y1).
  Proof.
    move=> ey [ exs eys ] ne; have h : x2 - xs != 0 by rewrite subr_eq0.
    have -> : (- y2 - ys) / (x2 - xs) = - l.
    { apply: (mulIf h); rewrite mulfVK //; rewrite -eys -exs ey; ring. }
    rewrite /wsum; congr pair; rewrite -?eys -exs; ring.
  Qed.

  (* degenerate case: S = -Q, the line is tangent at Q *)
  Lemma canc_deg l x1 y1 x2 y2 xs ys : y2 = y1 + l * (x2 - x1) ->
    wsum l x1 y1 x2 = (xs, ys) -> xs = x2 -> y2 != 0 -> l * (2%:R * y2) = fd x2 ->
    wadd (Some (xs, ys)) (Some (x2, - y2)) = Some (x1, y1).
  Proof.
    move=> ey [ exs eys ] ex ny hfd.
    have eys' : ys = - y2 by rewrite -eys exs ex ey; ring.
    have exs' : l ^+ 2 - A2 - x1 - x2 = x2 by rewrite exs ex.
    rewrite ex eys' wadd_tg ?oppr_eq0 //; congr Some.
    have -> : fd x2 / (2%:R * - y2) = - l.
    { rewrite -hfd; field by nzs. }
    have hl2 : l ^+ 2 = x1 + x2 + x2 + A2 by apply: (eq_from1 (k := 1) exs'); ring.
    rewrite /wsum sqrrN hl2; congr pair; first by ring.
    rewrite ey; ring.
  Qed.

  Lemma wadd_cancel P Q : won_pt P -> won_pt Q -> wadd (wadd P Q) (wneg Q) = P.
  Proof.
    case: P => [ [ x1 y1 ] | ]; last by move=> _ _; rewrite wadd0P waddN.
    case: Q => [ [ x2 y2 ] | ] h1 h2; last by rewrite !waddP0.
    case: (wcases h1 h2) => [ [ ex ey ] | [ [ ex [ ey ny ] ] | ne ] ].
    - by rewrite wadd_op //= ex ey.
    - subst x2 y2; rewrite wadd_tg // [wneg _]/=.
      set l := fd x1 / (2%:R * y1).
      have hl : l * (2%:R * y1) = fd x1 by rewrite /l divfK // mulf_neq0.
      case eS : (wsum l x1 y1 x1) => [ xs ys ].
      case: (eqVneq xs x1) => [ ex | ne ].
      + apply: (canc_deg _ eS) => //; ring.
      + rewrite wadd_ch //; congr Some; apply: (canc_gen _ eS); last by rewrite eq_sym.
        by ring.
    - rewrite wadd_ch // [wneg _]/=.
      have hsec := secant h1 h2 ne.
      set l := (y2 - y1) / (x2 - x1) in hsec *.
      have hl : y2 = y1 + l * (x2 - x1).
      { by rewrite /l divfK ?subrKC // subr_eq0 eq_sym. }
      clearbody l.
      case eS : (wsum l x1 y1 x2) => [ xs ys ].
      case: (eqVneq xs x2) => [ ex | nx ].
      + have exs : l ^+ 2 - A2 - x1 - x2 = x2 by move: eS => [ -> _ ].
        have hfd : l * (2%:R * y2) = fd x2.
        { apply: (eq_from3 hsec hl exs (k1 := 1) (k2 := l) (k3 := x2 - x1)); rewrite /fd; ring. }
        have ny : y2 != 0.
        { apply/eqP => e0; move: h2 => /= h2.
          have hf : fc x2 = 0 by rewrite -h2 e0 expr2 mulr0.
          by move: (nonsing hf); rewrite -hfd e0 !mulr0 eqxx. }
        exact: (canc_deg hl eS).
      + rewrite wadd_ch //; congr Some; apply: (canc_gen hl eS); by rewrite eq_sym.
  Qed.

  (** ** Consequences of cancellation *)

  Lemma wadd_cancel' P Q : won_pt P -> won_pt Q -> wadd (wadd P (wneg Q)) Q = P.
  Proof.
    move=> hP hQ; have := wadd_cancel hP (wneg_on hQ); by rewrite wnegK.
  Qed.

  Lemma wadd_KN P Q : won_pt P -> won_pt Q -> wadd P (wadd (wneg P) Q) = Q.
  Proof.
    move=> hP hQ; have hN := wneg_on hP.
    rewrite (wadd_comm hP (wadd_on hN hQ)) (wadd_comm hN hQ).
    exact: wadd_cancel'.
  Qed.

  Lemma wadd_NK P Q : won_pt P -> won_pt Q -> wadd (wneg P) (wadd P Q) = Q.
  Proof.
    move=> hP hQ; have := wadd_KN (wneg_on hP) hQ; by rewrite wnegK.
  Qed.

  Lemma wadd_linj X A B : won_pt X -> won_pt A -> won_pt B -> wadd X A = wadd X B -> A = B.
  Proof.
    move=> hX hA hB E; by rewrite -(wadd_NK hX hA) E wadd_NK.
  Qed.

  (** ** Equality of two sums given by slopes n/d and n'/d' *)

  Lemma sum_eq (n d n' d' xa ya xb xc yc xd : K) : d != 0 -> d' != 0 ->
    n ^+ 2 * d' ^+ 2 - n' ^+ 2 * d ^+ 2 = (xa + xb - xc - xd) * (d ^+ 2 * d' ^+ 2) ->
    n * d' * (xa * d ^+ 2 - n ^+ 2 + (A2 + xa + xb) * d ^+ 2)
      - n' * d * (xc * d ^+ 2 - n ^+ 2 + (A2 + xa + xb) * d ^+ 2) = (ya - yc) * (d ^+ 3 * d') ->
    wsum (n / d) xa ya xb = wsum (n' / d') xc yc xd.
  Proof.
    move=> nd nd' c1 c2.
    have ex : (n / d) ^+ 2 - A2 - xa - xb = (n' / d') ^+ 2 - A2 - xc - xd.
    { apply/eqP; rewrite -subr_eq0; apply/eqP.
      have -> : (n / d) ^+ 2 - A2 - xa - xb - ((n' / d') ^+ 2 - A2 - xc - xd)
                = ((n ^+ 2 * d' ^+ 2 - n' ^+ 2 * d ^+ 2) - (xa + xb - xc - xd) * (d ^+ 2 * d' ^+ 2))
                  / (d ^+ 2 * d' ^+ 2) by field by nzs.
      by rewrite c1 subrr mul0r. }
    rewrite /wsum -ex; congr pair.
    apply/eqP; rewrite -subr_eq0; apply/eqP.
    have -> : n / d * (xa - ((n / d) ^+ 2 - A2 - xa - xb)) - ya - (n' / d' * (xc - ((n / d) ^+ 2 - A2 - xa - xb)) - yc)
              = ((n * d' * (xa * d ^+ 2 - n ^+ 2 + (A2 + xa + xb) * d ^+ 2)
                  - n' * d * (xc * d ^+ 2 - n ^+ 2 + (A2 + xa + xb) * d ^+ 2)) - (ya - yc) * (d ^+ 3 * d'))
                / (d ^+ 3 * d') by field by nzs.
    by rewrite c2 subrr mul0r.
  Qed.

  (** ** The four polynomial identities of associativity *)

  (* (I) the generic case *)
  Lemma assoc_I x1 y1 x2 y2 x3 y3 xs ys xt yt :
    won (x1, y1) -> won (x2, y2) -> won (x3, y3) -> x1 != x2 -> x2 != x3 -> x1 != x3 ->
    wsum ((y2 - y1) / (x2 - x1)) x1 y1 x2 = (xs, ys) ->
    wsum ((y3 - y2) / (x3 - x2)) x2 y2 x3 = (xt, yt) ->
    xs != x3 -> x1 != xt ->
    wsum ((y3 - ys) / (x3 - xs)) xs ys x3 = wsum ((yt - y1) / (xt - x1)) x1 y1 xt.
  Proof.
    move=> h1 h2 h3 n12 n23 n13 [ exs eys ] [ ext eyt ] nS nT.
    have d12 : x1 - x2 != 0 by rewrite subr_eq0.
    have d23 : x2 - x3 != 0 by rewrite subr_eq0.
    have d13 : x1 - x3 != 0 by rewrite subr_eq0.
    have eA2 : A2 = ((y1 ^+ 2 - x1 ^+ 3) * (x2 - x3) - (y2 ^+ 2 - x2 ^+ 3) * (x1 - x3)
                     + (y3 ^+ 2 - x3 ^+ 3) * (x1 - x2)) / ((x1 - x2) * (x1 - x3) * (x2 - x3)).
    { move: h1 h2 h3; rewrite /won /fc /= => -> -> ->; field by nzs. }
    apply: sum_eq; [ by rewrite subr_eq0 eq_sym | by rewrite subr_eq0 eq_sym | | ];
      subst xs ys xt yt; rewrite eA2; field by nzs.
  Qed.

  (* (II) R = P + Q, written with S := R and P = S - Q *)
  Lemma assoc_II xs ys x2 y2 x1 y1 xt yt :
    won (xs, ys) -> won (x2, y2) -> xs != x2 -> ys != 0 ->
    wsum ((- y2 - ys) / (x2 - xs)) xs ys x2 = (x1, y1) ->
    wsum ((ys - y2) / (xs - x2)) x2 y2 xs = (xt, yt) ->
    x1 != xt ->
    wsum (fd xs / (2%:R * ys)) xs ys xs = wsum ((yt - y1) / (xt - x1)) x1 y1 xt.
  Proof.
    move=> hs h2 ns2 nys [ ex1 ey1 ] [ ext eyt ] nT.
    have d : xs - x2 != 0 by rewrite subr_eq0.
    have eA4 := eA4_of hs h2 ns2.
    apply: sum_eq; [ by rewrite mulf_neq0 | by rewrite subr_eq0 eq_sym | | ];
      subst x1 y1 xt yt; rewrite /fd eA4; field by nzs.
  Qed.

  (* (III) 2 (P + Q) = 2 P for a 2-torsion point Q *)
  Lemma assoc_III x1 y1 x2 xr yr :
    won (x1, y1) -> won (x2, 0) -> x1 != x2 -> y1 != 0 ->
    wsum ((0 - y1) / (x2 - x1)) x1 y1 x2 = (xr, yr) -> yr != 0 ->
    wsum (fd xr / (2%:R * yr)) xr yr xr = wsum (fd x1 / (2%:R * y1)) x1 y1 x1.
  Proof.
    move=> h1 h2 n12 ny1 [ exr eyr ] nyr.
    have d : x1 - x2 != 0 by rewrite subr_eq0.
    have eA4 := eA4_of h1 h2 n12.
    apply: sum_eq; [ by rewrite mulf_neq0 | by rewrite mulf_neq0 | | ];
      subst xr yr; rewrite /fd eA4; field by nzs.
  Qed.

  (* (IV) 2P + R = P + (P + R) *)
  Lemma assoc_IV x1 y1 x3 y3 xs ys xt yt :
    won (x1, y1) -> won (x3, y3) -> y1 != 0 -> x1 != x3 ->
    wsum (fd x1 / (2%:R * y1)) x1 y1 x1 = (xs, ys) ->
    wsum ((y3 - y1) / (x3 - x1)) x1 y1 x3 = (xt, yt) ->
    xs != x3 -> x1 != xt ->
    wsum ((y3 - ys) / (x3 - xs)) xs ys x3 = wsum ((yt - y1) / (xt - x1)) x1 y1 xt.
  Proof.
    move=> h1 h3 ny1 n13 [ exs eys ] [ ext eyt ] nS nT.
    have d : x1 - x3 != 0 by rewrite subr_eq0.
    have eA4 := eA4_of h1 h3 n13.
    apply: sum_eq; [ by rewrite subr_eq0 eq_sym | by rewrite subr_eq0 eq_sym | | ];
      subst xs ys xt yt; rewrite /fd eA4; field by nzs.
  Qed.

  (** ** Associativity *)

  Lemma Some_neq_x x1 y1 x2 y2 : won (x1, y1) -> won (x2, y2) ->
    Some (x2, y2) <> Some (x1, y1) -> Some (x2, y2) <> wneg (Some (x1, y1)) -> x1 != x2.
  Proof.
    move=> h1 h2 n1 n2; apply/eqP => ex; subst x2.
    by case: (won_x h1 h2) => ey; [ apply: n1 | apply: n2 ]; rewrite /= ey ?opprK.
  Qed.

  Lemma Some_eq_x x1 y1 x2 y2 : won (x1, y1) -> won (x2, y2) -> x1 = x2 ->
    Some (x2, y2) <> wneg (Some (x1, y1)) -> Some (x2, y2) = Some (x1, y1).
  Proof.
    move=> h1 h2 ex n2; subst x2.
    case: (won_x h1 h2) => ey; first by rewrite ey.
    by case: n2; rewrite /= ey opprK.
  Qed.

  (* 2-torsion: P = -P *)
  Lemma y0_neg x1 y1 : y1 = 0 -> Some (x1, y1) = wneg (Some (x1, y1)).
  Proof. by move=> ->; rewrite /= oppr0. Qed.

  Lemma y_neq0 x1 y1 : Some (x1, y1) <> wneg (Some (x1, y1)) -> y1 != 0.
  Proof. by move=> n; apply/eqP => e; apply: n; apply: y0_neg. Qed.

  (* the case Q = P, except R = 2P *)
  Lemma assoc_tanP_nonV P R : won_pt P -> won_pt R -> R <> wadd P P ->
    wadd (wadd P P) R = wadd P (wadd P R).
  Proof.
    move=> hP hR nV.
    have hN := wneg_on hP; have hPP := wadd_on hP hP; have hPR := wadd_on hP hR.
    case: (eqVneq (wadd P P) (wneg R)) => [ hSR | /eqP nSR ].
    { have eR : R = wneg (wadd P P) by rewrite hSR wnegK.
      have eT : wadd P R = wneg P.
      { by rewrite eR -{1}(wnegK P) -wneg_add wadd_NK. }
      by rewrite eT hSR waddNl waddN. }
    case: (eqVneq P (wneg (wadd P R))) => [ hPT | /eqP nPT ].
    { have eT : wadd P R = wneg P by rewrite {2}hPT wnegK.
      have eR : R = wneg (wadd P P) by rewrite -(wadd_NK hP hR) eT -wneg_add.
      by rewrite eT waddN eR waddN. }
    case: P hP hN hPP hPR nV nSR nPT => [ [ x1 y1 ] | ] hP hN hPP hPR nV nSR nPT; last by [].
    case: R hR hPP hPR nV nSR nPT => [ [ x3 y3 ] | ] hR hPP hPR nV nSR nPT; last by rewrite !waddP0.
    case: (eqVneq y1 0) => [ y0 | ny1 ].
    { have e : y1 = - y1 by rewrite y0 oppr0.
      rewrite (wadd_op erefl e) wadd0P.
      by rewrite {1}(y0_neg x1 y0) wadd_NK. }
    case: (eqVneq (Some (x3, y3)) (Some (x1, y1))) => [ e | /eqP n1 ].
    { by case: e => -> ->; apply: wadd_comm. }
    case: (eqVneq (Some (x3, y3)) (wneg (Some (x1, y1)))) => [ e | /eqP n2 ].
    { by rewrite e wadd_cancel // waddN waddP0. }
    have n13 := Some_neq_x hP hR n1 n2.
    move: hPP hPR nV nSR nPT; rewrite (wadd_tg _ ny1) (wadd_ch _ _ n13).
    case eS : (wsum _ x1 y1 x1) => [ xs ys ]; case eT : (wsum _ x1 y1 x3) => [ xt yt ].
    move=> hS hT nV nSR nPT.
    case: (eqVneq xs x3) => [ e | nS ].
    { by case: nV; symmetry; apply: Some_eq_x => //; rewrite e. }
    case: (eqVneq x1 xt) => [ e | nT ].
    { have E := Some_eq_x hT hP (esym e) nPT.
      have : wadd (Some (x1, y1)) (Some (x3, y3)) = wadd (Some (x1, y1)) None.
      { by rewrite waddP0 wadd_ch // eT E. }
      by move/(wadd_linj hP hR (I : won_pt None)). }
    rewrite !wadd_ch //; congr Some.
    exact: (assoc_IV hP hR ny1 n13 eS eT).
  Qed.

  Lemma assoc_tanP P R : won_pt P -> won_pt R -> wadd (wadd P P) R = wadd P (wadd P R).
  Proof.
    move=> hP hR.
    case: (eqVneq R (wadd P P)) => [ eR | /eqP nV ]; last exact: assoc_tanP_nonV.
    subst R; set S := wadd P P.
    have hS : won_pt S := wadd_on hP hP; have hN := wneg_on hP.
    have hSS := wadd_on hS hS.
    case: (eqVneq (wneg P) (wadd S S)) => [ e5 | /eqP n5 ].
    { have eT : wadd P S = wneg S.
      { have E : wneg (wadd P S) = S by rewrite wneg_add e5 wadd_cancel.
        by rewrite -[wadd P S]wnegK E. }
      by rewrite eT /S wneg_add wadd_KN. }
    have A := assoc_tanP_nonV hS hN n5.
    rewrite /S wadd_cancel // -/S in A.
    rewrite (wadd_comm hP hS) -A (wadd_comm hSS hN) wadd_KN //.
  Qed.

  (* the case S = R of the main proof, by identity (II) *)
  Lemma assoc_SR x1 y1 x2 y2 x3 y3 :
    won (x1, y1) -> won (x2, y2) -> won (x3, y3) -> x1 != x2 -> x2 != x3 -> y3 != 0 ->
    wadd (Some (x1, y1)) (Some (x2, y2)) = Some (x3, y3) ->
    (forall xt yt, wadd (Some (x2, y2)) (Some (x3, y3)) = Some (xt, yt) -> x1 != xt) ->
    wadd (wadd (Some (x1, y1)) (Some (x2, y2))) (Some (x3, y3))
    = wadd (Some (x1, y1)) (wadd (Some (x2, y2)) (Some (x3, y3))).
  Proof.
    move=> h1 h2 h3 n12 n23 ny3 eS nT.
    have eP := @wadd_cancel (Some (x1, y1)) (Some (x2, y2)) h1 h2; rewrite eS [wneg _]/= wadd_ch 1?eq_sym // in eP.
    move/Some_inj: eP => eP.
    rewrite eS wadd_tg // (wadd_ch _ _ n23).
    case eT : (wsum _ x2 y2 x3) => [ xt yt ].
    have nT' : x1 != xt by apply: nT; rewrite wadd_ch // eT.
    rewrite wadd_ch //; congr Some.
    have n32 : x3 != x2 by rewrite eq_sym.
    exact: (assoc_II h3 h2 n32 ny3 eP eT nT').
  Qed.

  Theorem wadd_assoc P Q R : won_pt P -> won_pt Q -> won_pt R ->
    wadd (wadd P Q) R = wadd P (wadd Q R).
  Proof.
    case: P => [ [ x1 y1 ] | ] hP; last by [].
    case: Q => [ [ x2 y2 ] | ] hQ; last by rewrite waddP0.
    case: R => [ [ x3 y3 ] | ] hR; last by rewrite !waddP0.
    set P := Some (x1, y1) in hP *; set Q := Some (x2, y2) in hQ *; set R := Some (x3, y3) in hR *.
    have hNP := wneg_on hP; have hNQ := wneg_on hQ.
    have hPQ := wadd_on hP hQ; have hQR := wadd_on hQ hR; have hQP := wadd_on hQ hP.
    have hRQ := wadd_on hR hQ.
    case: (eqVneq Q (wneg P)) => [ e | /eqP n1 ].
    { by rewrite e waddN wadd0P wadd_KN. }
    case: (eqVneq R (wneg Q)) => [ e | /eqP n2 ].
    { by rewrite e wadd_cancel // waddN waddP0. }
    case: (eqVneq R P) => [ e | /eqP n3 ].
    { by rewrite e (wadd_comm hQ hP) (wadd_comm hPQ hP). }
    case: (eqVneq R (wneg P)) => [ e | /eqP n4 ].
    { by rewrite e (wadd_comm hP hQ) wadd_cancel // (wadd_comm hQ hNP) wadd_KN. }
    case: (eqVneq Q P) => [ e | /eqP n5 ].
    { by rewrite e assoc_tanP. }
    case: (eqVneq R Q) => [ e | /eqP n6 ].
    { rewrite e (wadd_comm hPQ hQ) (wadd_comm hP hQ) -assoc_tanP // wadd_comm //.
      exact: wadd_on. }
    case: (eqVneq (wadd P Q) (wneg R)) => [ e | /eqP n7 ].
    { have eR : R = wneg (wadd P Q) by rewrite e wnegK.
      have eT : wadd Q R = wneg P.
      { by rewrite eR -{1}(wnegK Q) -wneg_add (wadd_comm hP hQ) wadd_NK. }
      by rewrite e waddNl eT waddN. }
    case: (eqVneq P (wneg (wadd Q R))) => [ e | /eqP n8 ].
    { have eS : wadd P Q = wneg R.
      { by rewrite e -{2}(wnegK Q) -wneg_add (wadd_comm hQ hR) wadd_cancel. }
      by rewrite eS waddNl e waddNl. }
    have n12 : x1 != x2 := Some_neq_x hP hQ n5 n1.
    have n23 : x2 != x3 := Some_neq_x hQ hR n6 n2.
    have n13 : x1 != x3 := Some_neq_x hP hR n3 n4.
    have eS := wadd_ch y1 y2 n12; have eT := wadd_ch y2 y3 n23.
    case eS' : (wsum _ x1 y1 x2) eS => [ xs ys ] eS.
    case eT' : (wsum _ x2 y2 x3) eT => [ xt yt ] eT.
    rewrite -/P -/Q -/R in eS eT.
    have hS : won (xs, ys) by move: hPQ; rewrite eS.
    have hT : won (xt, yt) by move: hQR; rewrite eT.
    rewrite eS in n7; rewrite eT in n8.
    case: (eqVneq xs x3) => [ exs | nxs ]; case: (eqVneq x1 xt) => [ ext | nxt ].
    - (* S = R and P = T: Q is 2-torsion, identity (III) *)
      have ESR := Some_eq_x hR hS (esym exs) n7.
      have EPT := Some_eq_x hT hP (esym ext) n8.
      have c1 : wadd R (wneg Q) = P by rewrite /R -ESR -eS wadd_cancel.
      have c2 : wadd R Q = P by rewrite (wadd_comm hR hQ) eT -EPT.
      have := wadd_linj hR hNQ hQ (etrans c1 (esym c2)).
      move=> [] /esym /y_opp0 y20.
      have ny3 : y3 != 0.
      { apply: y_neq0 => E; apply: n7; rewrite ESR; exact: E. }
      have ny1 : y1 != 0.
      { apply: y_neq0 => E; apply: n8; rewrite -EPT; exact: E. }
      rewrite eS ESR (wadd_tg _ ny3) eT -EPT (wadd_tg _ ny1); congr Some.
      subst y2; move: ESR => [ exs2 eys2 ]; rewrite exs2 eys2 in eS'.
      exact: (assoc_III hP hQ n12 ny1 eS' ny3).
    - (* S = R: identity (II) *)
      have ESR := Some_eq_x hR hS (esym exs) n7.
      have ny3 : y3 != 0.
      { apply: y_neq0 => E; apply: n7; rewrite ESR; exact: E. }
      apply: (assoc_SR hP hQ hR n12 n23 ny3); first by rewrite eS ESR.
      by move=> xt' yt'; rewrite eT => -[ <- _ ].
    - (* P = T: identity (II) for the mirrored triple *)
      have EPT := Some_eq_x hT hP (esym ext) n8.
      have ny1 : y1 != 0.
      { apply: y_neq0 => E; apply: n8; rewrite -EPT; exact: E. }
      have A : wadd (wadd R Q) P = wadd R (wadd Q P).
      { apply: (assoc_SR hR hQ hP _ _ ny1); rewrite 1?eq_sym //.
        - by rewrite (wadd_comm hR hQ) eT -EPT.
        - by move=> xt' yt'; rewrite (wadd_comm hQ hP) eS => -[ <- _ ]; rewrite eq_sym. }
      rewrite (wadd_comm hPQ hR) (wadd_comm hP hQ) -A (wadd_comm hRQ hP) (wadd_comm hR hQ) //.
    - (* generic: identity (I) *)
      rewrite eS eT !wadd_ch // 1?eq_sym //; congr Some.
      exact: (assoc_I hP hQ hR n12 n23 n13 eS' eT').
  Qed.

  (** ** Multiples *)

  Definition wmuln (P0 : option (K * K)) (k : nat) : option (K * K) := iter k (wadd P0) None.

  Definition wmul (P0 : option (K * K)) (n : int) : option (K * K) :=
    match n with
    | Posz k => wmuln P0 k
    | Negz k => wneg (wmuln P0 k.+1)
    end.

  Section multiples.

    Variable P0 : option (K * K).
    Hypothesis hP0 : won_pt P0.

    Lemma wmuln_on k : won_pt (wmuln P0 k).
    Proof. by elim: k => [ | k IHk ] //=; apply: wadd_on. Qed.

    Lemma wmul_on n : won_pt (wmul P0 n).
    Proof. by case: n => k; [ exact: wmuln_on | apply: wneg_on; exact: wmuln_on ]. Qed.

    Lemma wmuln_add j k : wmuln P0 (j + k) = wadd (wmuln P0 j) (wmuln P0 k).
    Proof.
      elim: j => [ | j IHj ] //; rewrite addSn /= IHj wadd_assoc //; exact: wmuln_on.
    Qed.

    Lemma wmul_succ n : wmul P0 (n + 1) = wadd (wmul P0 n) P0.
    Proof.
      case: n => k.
      - by rewrite -PoszD addn1 /= wadd_comm //; apply: wmuln_on.
      - have -> : Negz k + 1 = - k%:Z by rewrite NegzE -addn1 PoszD opprD addrNK.
        case: k => [ | k ]; first by rewrite oppr0 /= waddP0 waddNl.
        have -> : - (k.+1)%:Z = Negz k by [].
        rewrite /wmul [wmuln P0 k.+2]/wmuln iterS -/(wmuln P0 k.+1).
        rewrite wneg_add (wadd_comm (wneg_on hP0) (wneg_on (wmuln_on k.+1))).
        by rewrite wadd_cancel' //; apply: wneg_on; apply: wmuln_on.
    Qed.

    Lemma wmul_pred n : wmul P0 (n - 1) = wadd (wmul P0 n) (wneg P0).
    Proof.
      by rewrite -{2}(subrK 1 n) wmul_succ wadd_cancel //; apply: wmul_on.
    Qed.

    Theorem wmul_add n m : wmul P0 (n + m) = wadd (wmul P0 n) (wmul P0 m).
    Proof.
      case: m => k.
      - elim: k => [ | k IHk ]; first by rewrite addr0 /= waddP0.
        rewrite -addn1 PoszD addrA wmul_succ IHk (wadd_assoc (wmul_on n) (wmul_on k) hP0).
        by rewrite -wmul_succ.
      - elim: k => [ | k IHk ].
        + have -> : Negz 0 = - 1 by [].
          by rewrite wmul_pred /= waddP0.
        + have -> : Negz k.+1 = Negz k - 1 by rewrite !NegzE -addn1 PoszD opprD.
          rewrite addrA wmul_pred IHk (wadd_assoc (wmul_on n) (wmul_on (Negz k)) (wneg_on hP0)).
          by rewrite -wmul_pred.
    Qed.

  End multiples.

End wlaw.

(** * 2. The curve y^2 = x^3 + a x and the relation ADDrel, generically *)

Section wlaw0.

  Variable K : fieldType.
  Variable a : K.
  Hypothesis two0 : 2%:R != 0 :> K.
  Hypothesis a0 : a != 0.

  Lemma nonsing0 : forall x : K, fc 0 a 0 x = 0 -> fd 0 a x != 0.
  Proof.
    move=> x; rewrite /fc /fd => H0; apply/eqP => H0'.
    have H : x ^+ 3 + a * x = 0 by rewrite -H0; ring.
    have H' : 3%:R * x ^+ 2 + a = 0 by rewrite -H0'; ring.
    have ex : x * (x ^+ 2 + a) = 0 by rewrite -H; ring.
    move/eqP: ex; rewrite mulf_eq0 => /orP [ /eqP x0 | /eqP x2 ].
    - by move: H'; rewrite x0 expr2 !mulr0 !add0r => E; move: a0; rewrite E eqxx.
    - have : 2%:R * a = 0.
      { have -> : 2%:R * a = - (3%:R * x ^+ 2 + a) + 3%:R * (x ^+ 2 + a) by ring.
        by rewrite H' x2 oppr0 mulr0 addr0. }
      by move/eqP; rewrite mulf_eq0 (negbTE two0) (negbTE a0).
  Qed.

  (* the body of ADDrel (FixedData.v) for a generic coefficient a *)
  Definition ADDw (p1 p2 p3 : option (K * K)) : Prop :=
    match p1, p2 with
    | None, _ => p3 = p2
    | _, None => p3 = p1
    | Some (x1, y1), Some (x2, y2) =>
           (x1 = x2 /\ y1 = - y2 /\ p3 = None)
        \/ exists x3 y3, p3 = Some (x3, y3) /\
           (   (x1 <> x2
                /\ (x3 + x1 + x2) * (x2 - x1) ^+ 2 = (y2 - y1) ^+ 2
                /\ (y3 + y1) * (x2 - x1) = (y2 - y1) * (x1 - x3))
            \/ (x1 = x2 /\ y1 = y2 /\ y1 <> 0
                /\ (x3 + 2%:R * x1) * (2%:R * y1) ^+ 2 = (3%:R * x1 ^+ 2 + a) ^+ 2
                /\ (y3 + y1) * (2%:R * y1) = (3%:R * x1 ^+ 2 + a) * (x1 - x3)))
    end.

  Lemma ADDw_spec P Q : won_pt 0 a 0 P -> won_pt 0 a 0 Q -> ADDw P Q (wadd 0 a P Q).
  Proof.
    case: P => [ [ x1 y1 ] | ] //; case: Q => [ [ x2 y2 ] | ] // h1 h2.
    case: (wcases h1 h2) => [ [ ex ey ] | [ [ ex [ ey ny ] ] | ne ] ].
    - by left; rewrite wadd_op.
    - subst x2 y2; right; rewrite wadd_tg //.
      eexists; eexists; split; first by [].
      right; do 3 (split; first by [] || exact/eqP).
      have d : 2%:R * y1 != 0 by rewrite mulf_neq0.
      rewrite /fd /wsum /=; split; field by rewrite ?mulf_neq0.
    - right; rewrite wadd_ch //.
      eexists; eexists; split; first by [].
      left; split; first exact/eqP.
      have d : x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
      rewrite /wsum /=; split; field by rewrite ?mulf_neq0.
  Qed.

  Lemma ADDw_fun P Q R R' : ADDw P Q R -> ADDw P Q R' -> R = R'.
  Proof.
    case: P => [ [ x1 y1 ] | ] /=; last by move=> -> ->.
    case: Q => [ [ x2 y2 ] | ] /=; last by move=> -> ->.
    have y0 (u v : K) : u = - v -> u = v -> u <> 0 -> False.
    { move=> E1 E2 nu; apply: nu; apply: (y_opp0 two0); by rewrite {2}E2. }
    move=> [ [ e1 [ e2 -> ] ] | [ x3 [ y3 [ -> H ] ] ] ]
           [ [ e1' [ e2' -> ] ] | [ x3' [ y3' [ -> H' ] ] ] ] //.
    - case: H' => [ [ ne _ ] | [ _ [ ey [ ny _ ] ] ] ] //.
      by case: (y0 _ _ e2 ey ny).
    - case: H => [ [ ne _ ] | [ _ [ ey [ ny _ ] ] ] ] //.
      by case: (y0 _ _ e2' ey ny).
    - case: H => [ [ ne [ c1 c2 ] ] | [ e [ ey [ ny [ t1 t2 ] ] ] ] ];
      case: H' => [ [ ne' [ c1' c2' ] ] | [ e' [ ey' [ ny' [ t1' t2' ] ] ] ] ] //.
      + have nd : x2 - x1 != 0 by rewrite subr_eq0 eq_sym; apply/eqP.
        have ex : x3 = x3'.
        { have := mulIf (mulf_neq0 nd nd); rewrite -expr2 => /(_ _ _ (etrans c1 (esym c1'))).
          by move/addIr/addIr. }
        subst x3'; have := mulIf nd (etrans c2 (esym c2')); by move/addIr => ->.
      + have nd : 2%:R * y1 != 0 by apply: mulf_neq0 => //; apply/eqP.
        have ex : x3 = x3'.
        { have := mulIf (mulf_neq0 nd nd); rewrite -expr2 => /(_ _ _ (etrans t1 (esym t1'))).
          by move/addIr. }
        subst x3'; have := mulIf nd (etrans t2 (esym t2')); by move/addIr => ->.
  Qed.

End wlaw0.

(** * 3. qe F is a field when 2 is not a square in F *)

Section qe_field.

  Variable F : fieldType.
  Hypothesis HZ0 : forall z : F, z * z <> 2%:R.

  Lemma qe_neq0_unit (x : qe F) : x != 0 -> x \is a GRing.unit.
  Proof.
    case: x => a b Hx; rewrite qe_unitE /qe_norm /=; apply/eqP => N.
    case: (eqVneq b 0) => Hb.
    - subst b; move: N; rewrite expr0n /= mulr0 subr0 => /eqP; rewrite sqrf_eq0 => /eqP Ha.
      by move: Hx; rewrite Ha eqxx.
    - apply: (@HZ0 (a / b)).
      have E : a ^+ 2 = 2%:R * b ^+ 2 by apply/eqP; rewrite -subr_eq0; apply/eqP.
      rewrite -[_ * _]/((a / b) * (a / b)) -mulrA [b^-1 * _]mulrC !mulrA -expr2 E.
      by field.
  Qed.

End qe_field.

(* [qe F] with its field structure; the ring structure is that of [qe F] *)
Definition QF (F : fieldType) (h : forall z : F, z * z <> 2%:R) : Type := qe F.

HB.instance Definition _ (F : fieldType) (h : forall z : F, z * z <> 2%:R) :=
  GRing.ComUnitRing.on (@QF F h).
HB.instance Definition _ (F : fieldType) (h : forall z : F, z * z <> 2%:R) :=
  GRing.ComUnitRing_isField.Build (@QF F h) (@qe_neq0_unit F h).

(** * 4. Transport to [ec_add], [on_curve], [ADDrel] on [qe F] *)

Section transport.

  Variable F : fieldType.
  Variable h : forall z : F, z * z <> 2%:R.

  Local Abbreviation KF := (@QF F h).

  Lemma two0_F : 2%:R != 0 :> F.
  Proof. apply/eqP => E; apply: (@h 0); by rewrite mulr0 E. Qed.

  Lemma two0_QF : 2%:R != 0 :> KF.
  Proof.
    apply/eqP; rewrite (qe_natE F 2) qe0E => -[] /eqP; by rewrite (negbTE two0_F).
  Qed.

  (* 11243 and 7950 are coprime: 6557 * 11243 = 9273 * 7950 + 1 *)
  Lemma aE_neq0_QF : (aE : KF) != 0.
  Proof.
    apply/eqP; rewrite /aE qe0E => -[] /eqP; rewrite oppr_eq0 => /eqP E1 E2.
    have H : (1 : F) = 6557%:R * 11243%:R - 9273%:R * 7950%:R by ring.
    have G (c d u v : F) : (1 : F) = c * u - d * v -> u = 0 -> v = 0 -> False.
    { move=> e eu ev; move: e; rewrite eu ev !mulr0 subrr => /eqP; by rewrite oner_eq0. }
    exact: (G _ _ _ _ H E1 E2).
  Qed.

  Lemma nonsing_QF : forall x : KF, fc (K := KF) 0 aE 0 x = 0 -> fd (K := KF) 0 aE x != 0.
  Proof. exact: (nonsing0 two0_QF aE_neq0_QF). Qed.

  Lemma ec_add_w (P Q : pt F) : ec_add P Q = wadd (K := KF) 0 aE P Q.
  Proof.
    case: P => [ [ x1 y1 ] | ] //; case: Q => [ [ x2 y2 ] | ] //=.
    case: (x1 == x2) => //; first case: (y1 == - y2) => //.
    - by rewrite /wsum /fd; congr (Some (_, _)); ring.
    - by rewrite /wsum; congr (Some (_, _)); ring.
  Qed.

  Lemma on_curve_w (p : qe F * qe F) : on_curve p <-> won (K := KF) 0 aE 0 p.
  Proof.
    rewrite /on_curve /won /fc; case: p => x y /=.
    have -> : x ^+ 3 + 0 * x ^+ 2 + aE * x + 0 = x ^+ 3 + aE * x :> KF by ring.
    by rewrite expr2.
  Qed.

  Lemma ADDrel_w (P Q R : pt F) : ADDrel P Q R <-> ADDw (K := KF) aE P Q R.
  Proof. by []. Qed.

  Lemma pt_neg_w (P : pt F) : pt_neg P = wneg (K := KF) P.
  Proof. by case: P => [ [] | ]. Qed.

  Definition on_curve_pt (P : pt F) : Prop := if P is Some p then on_curve p else True.

  Lemma on_curve_pt_w (P : pt F) : on_curve_pt P <-> won_pt (K := KF) 0 aE 0 P.
  Proof. by case: P => [ p | ] //=; apply: on_curve_w. Qed.

  (** ** The group laws for [ec_add] *)

  Theorem ec_add_on (P Q : pt F) : on_curve_pt P -> on_curve_pt Q -> on_curve_pt (ec_add P Q).
  Proof. rewrite !on_curve_pt_w ec_add_w; exact: (wadd_on two0_QF). Qed.

  Theorem ADDrel_ec_add (P Q : pt F) : on_curve_pt P -> on_curve_pt Q -> ADDrel P Q (ec_add P Q).
  Proof. rewrite !on_curve_pt_w ec_add_w ADDrel_w; exact: (ADDw_spec two0_QF). Qed.

  Theorem ec_add_spec (p q : qe F * qe F) : on_curve p -> on_curve q ->
    ADDrel (Some p) (Some q) (ec_add (Some p) (Some q)).
  Proof. move=> hp hq; exact: (@ADDrel_ec_add (Some p) (Some q) hp hq). Qed.

  Theorem ADDrel_fun_F (P Q R R' : pt F) : ADDrel P Q R -> ADDrel P Q R' -> R = R'.
  Proof. rewrite !ADDrel_w; exact: (ADDw_fun two0_QF). Qed.

  (* the relation is the graph of the function on the curve *)
  Theorem ADDrel_iff (P Q R : pt F) : on_curve_pt P -> on_curve_pt Q ->
    ADDrel P Q R <-> R = ec_add P Q.
  Proof.
    move=> hP hQ; split => [ H | -> ]; last exact: ADDrel_ec_add.
    exact: (ADDrel_fun_F H (ADDrel_ec_add hP hQ)).
  Qed.

  Theorem ec_add0P (P : pt F) : ec_add None P = P.
  Proof. by []. Qed.

  Theorem ec_addP0 (P : pt F) : ec_add P None = P.
  Proof. by case: P => [ [] | ]. Qed.

  Theorem pt_neg_on (P : pt F) : on_curve_pt P -> on_curve_pt (pt_neg P).
  Proof. rewrite !on_curve_pt_w pt_neg_w; exact: wneg_on. Qed.

  Theorem ec_addN (P : pt F) : ec_add P (pt_neg P) = None.
  Proof. rewrite ec_add_w pt_neg_w; exact: (waddN (K := KF) 0 aE P). Qed.

  Theorem ec_add_comm (P Q : pt F) : on_curve_pt P -> on_curve_pt Q -> ec_add P Q = ec_add Q P.
  Proof. rewrite !on_curve_pt_w !ec_add_w; exact: wadd_comm. Qed.

  Theorem ec_add_assoc (P Q R : pt F) : on_curve_pt P -> on_curve_pt Q -> on_curve_pt R ->
    ec_add (ec_add P Q) R = ec_add P (ec_add Q R).
  Proof.
    rewrite !on_curve_pt_w !ec_add_w; exact: (wadd_assoc two0_QF nonsing_QF).
  Qed.

End transport.

(** * 5. The multiples of P0 over F = Q(sqrt2): E1 *)

(* sqrt2 is irrational (as Theory.rat_Z0) *)
Lemma rat_sq2 (x : rat) : x * x <> 2%:R.
Proof.
  move=> H.
  have Hx : x != 0.
  { apply/eqP => E; move: H; rewrite E mulr0 => /eqP; by rewrite eq_sym pnatr_eq0. }
  have E : numq x * numq x = 2%:Z * (denq x * denq x).
  { apply: (@intr_inj rat); rewrite !intrM !numqE mulrACA H. by []. }
  have En : (`|numq x| * `|numq x| = 2 * (`|denq x| * `|denq x|))%N.
  { by rewrite -!abszM E abszM. }
  have Hn : (0 < `|numq x|)%N by rewrite absz_gt0 numq_eq0.
  have Hd : (0 < `|denq x|)%N by rewrite absz_gt0 denq_neq0.
  move: (congr1 (logn 2) En).
  rewrite lognM // lognM ?muln_gt0 ?Hd // lognM // (@logn_prime 2 2) //=.
  move/(congr1 odd); rewrite !oddD !addbb /=.
  done.
Qed.

Section E1.

  Local Abbreviation KQ := (@QF rat rat_sq2).

  Variable D : FixedData.

  Lemma mulQn_w k : mulQn D k = wmuln (K := KQ) 0 aE (Some (fd_P0 D)) k.
  Proof.
    rewrite /mulQn /wmuln; elim: k => [ | k IHk ] //; rewrite !iterS IHk; exact: ec_add_w.
  Qed.

  Lemma mulQ_w n : mulQ D n = wmul (K := KQ) 0 aE (Some (fd_P0 D)) n.
  Proof. case: n => k; first exact: mulQn_w. by rewrite /mulQ /wmul mulQn_w (pt_neg_w rat_sq2). Qed.

  Hypothesis hP0 : on_curve (fd_P0 D).

  Lemma hP0w : won_pt (K := KQ) 0 aE 0 (Some (fd_P0 D)).
  Proof. exact: (proj1 (on_curve_w rat_sq2 (fd_P0 D)) hP0). Qed.

  Lemma mulQ_on n : on_curve_pt (mulQ D n).
  Proof.
    rewrite on_curve_pt_w mulQ_w; exact: (wmul_on (two0_QF rat_sq2) hP0w).
  Qed.

  (* n P0 + n' P0 = (n + n') P0 *)
  Theorem mulQ_add (n n' : int) : mulQ D (n + n') = ec_add (mulQ D n) (mulQ D n').
  Proof.
    rewrite !mulQ_w (ec_add_w rat_sq2).
    have E := wmul_add (two0_QF rat_sq2) (@nonsing_QF _ rat_sq2) hP0w n n'.
    exact: E.
  Qed.

  (* the field E1 of StdHyps (FixedData.v), as a theorem *)
  Theorem E1_thm : forall n n' : int, ADDrel (mulQ D n) (mulQ D n') (mulQ D (n + n')).
  Proof. move=> n n'; rewrite mulQ_add; apply: (ADDrel_ec_add rat_sq2); exact: mulQ_on. Qed.

End E1.

(* the premise of E1_thm follows from the field E2 of StdHyps (at n = 1) *)
Lemma P0_on_curve_of_E2 (D : FixedData) :
  (forall n : int, n != 0 ->
     exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y)) ->
  on_curve (fd_P0 D).
Proof.
  move=> /(_ 1 isT) [ x [ y [ E [ _ [ _ H ] ] ] ] ].
  have e : mulQ D 1 = Some (fd_P0 D) by exact: ec_addP0.
  by rewrite e in E; case: E => ->.
Qed.

Corollary E1_of_E2 (D : FixedData) :
  (forall n : int, n != 0 ->
     exists x y, mulQ D n = Some (x, y) /\ x != 0 /\ y != 0 /\ on_curve (x, y)) ->
  forall n n' : int, ADDrel (mulQ D n) (mulQ D n') (mulQ D (n + n')).
Proof. move=> H; exact: (E1_thm (P0_on_curve_of_E2 H)). Qed.
