(**************************************************************)
(*   Part of the formalization of the preprint                *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026), contributed to the Rocq library of undecidable   *)
(*   problems.                                                *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Tier 2 interface: the term signature of the Skolemized theory T
   (DESIGN.md, Section 3.1) and quantifier-free formulas over terms.

   This file is pure syntax (Stdlib only, no MathComp). It lives in a
   separate file so that the term-model interfaces (Ambient.v,
   SignatureS.v, AmbientS.v) can be stated before the theory T itself
   (Theory.v) is defined.

   Nothing here is assumed. *)

From Stdlib Require Import ZArith List.

Import ListNotations.

Set Implicit Arguments.

(** * Index types *)

(* the three summands u_1, u_2, u_3 of a contact representation *)
Inductive i3 : Set := I1 | I2 | I3.

(* the four finite points of the contact set C \ {oo} *)
Inductive i4 : Set := B1 | B2 | B3 | B4.

Definition all_i3 : list i3 := [I1; I2; I3].
Definition all_i4 : list i4 := [B1; B2; B3; B4].

(* the 13 members  v,  L_b(u_i, v)  (i in 1..3, b in C \ {oo})
   of the contact list red:contact-list / pri:coverage-list *)
Inductive mem13 : Set :=
  | mem_v
  | mem_L (i : i3) (b : i4).

Definition all_mem13 : list mem13 :=
  mem_v :: flat_map (fun i => map (mem_L i) all_i4) all_i3.

(* the sign s in {+,-} selecting a residue branch  sqrt2 |-> s B_r *)
Inductive sgn : Set := sg_p | sg_m.

Definition all_sgn : list sgn := [sg_p; sg_m].

(* the six coordinate functions x0 x1 x2 y0 y1 y2 of
   red:coordinate-functions; also used for the coordinates
   w0 .. w5 of the chain points of ax_chain *)
Inductive coord : Set := cx0 | cx1 | cx2 | cy0 | cy1 | cy2.

(* the components (X0, X1, Y0, Y1, iota, kappa) of a localization
   witness (DESIGN 3.2, macro LOC) *)
Inductive wcomp : Set := wX0 | wX1 | wY0 | wY1 | wiota | wkappa.

(* unary localization witnesses: FORMAL h, FORMALs j0 *)
Inductive tag1 : Set := tg_fh | tg_fj0.

(* binary localization witnesses: FORMAL (h a), red:primary-test,
   FORMALs ((h-4) a), red:alternate-test *)
Inductive tag2 : Set := tg_fha | tg_prim | tg_fh4a | tg_alt.

(** * Function symbols (DESIGN 3.1) *)

(* unary Skolem functions of the representation axiom Rep_K, argument A *)
Inductive rep1 : Set :=
  | r_u1 | r_u2 | r_v
  | r_r (j : mem13)                (* the prime-like element r of member j *)
  | r_B (j : mem13)                (* B_r *)
  | r_wB (j : mem13)               (* B_r^2 - 2 = r * wB *)
  | r_iota' (j : mem13)            (* (2 B_r) iota' - 1 = r kappa'   (fidelity) *)
  | r_kappa' (j : mem13)
  | r_h (j : mem13) (s : sgn)      (* h at branch s *)
  | r_j0 (j : mem13) (s : sgn)     (* j0 at branch s *)
  | r_W1 (j : mem13) (s : sgn) (tag : tag1) (c : wcomp).

(* binary Skolem functions of Rep_K, arguments (A, a) *)
Inductive rep2 : Set :=
  | r_fz (j : mem13)               (* "R/rR is a field" witnesses (fidelity) *)
  | r_fy (j : mem13)
  | r_fz' (j : mem13)
  | r_W2 (j : mem13) (s : sgn) (tag : tag2) (c : wcomp).

Inductive sym0 : Set :=
  | s_zero
  | s_one
  | s_int (z : Z)                  (* definitional expansion: the integer z *)
  | s_cst (i : nat).               (* the constants a_1 .. a_n (as s_cst 0 .. s_cst (n-1)) *)

Inductive sym1 : Set :=
  | s_neg                          (* ring negation *)
  | s_coord (c : coord)            (* x0 .. y2 *)
  | s_chain (k : nat) (c : coord)  (* coordinates of the chain point Q_k, 1 <= k <= m-1 *)
  | s_rep1 (K : nat) (c : rep1).

Inductive sym2 : Set :=
  | s_add
  | s_mul
  | s_rep2 (K : nat) (c : rep2).

(* ring symbols are interpreted by constraint (a); all others are
   uninterpreted and subject to functionality, constraint (b) *)
Definition ring_sym0 (g : sym0) : bool :=
  match g with s_cst _ => false | _ => true end.
Definition ring_sym1 (g : sym1) : bool :=
  match g with s_neg => true | _ => false end.
Definition ring_sym2 (g : sym2) : bool :=
  match g with s_add | s_mul => true | _ => false end.

(** * Terms over a type of variables *)

Inductive term (X : Type) : Type :=
  | tvar (x : X)
  | tapp0 (g : sym0)
  | tapp1 (g : sym1) (t : term X)
  | tapp2 (g : sym2) (s t : term X).

Arguments tapp0 {X}.

(* ground terms: no variables *)
Definition gterm := term Empty_set.

Fixpoint tsubst {X Y : Type} (σ : X -> term Y) (t : term X) : term Y :=
  match t with
  | tvar x => σ x
  | tapp0 g => tapp0 g
  | tapp1 g t => tapp1 g (tsubst σ t)
  | tapp2 g s t => tapp2 g (tsubst σ s) (tsubst σ t)
  end.

(** * Quantifier-free formulas in negation normal form over terms *)

Inductive fml (X : Type) : Type :=
  | f_eq (s t : term X)
  | f_ne (s t : term X)
  | f_and (A B : fml X)
  | f_or (A B : fml X)
  | f_tt
  | f_ff.

Arguments f_tt {X}.
Arguments f_ff {X}.

Definition gfml := fml Empty_set.

Fixpoint fml_subst {X Y : Type} (σ : X -> term Y) (A : fml X) : fml Y :=
  match A with
  | f_eq s t => f_eq (tsubst σ s) (tsubst σ t)
  | f_ne s t => f_ne (tsubst σ s) (tsubst σ t)
  | f_and A B => f_and (fml_subst σ A) (fml_subst σ B)
  | f_or A B => f_or (fml_subst σ A) (fml_subst σ B)
  | f_tt => f_tt
  | f_ff => f_ff
  end.

(* truth of a formula under a valuation of terms in an arbitrary type
   (only equality of values matters; the atoms are s = t and s <> t) *)
Fixpoint fml_holds {X R : Type} (val : term X -> R) (A : fml X) : Prop :=
  match A with
  | f_eq s t => val s = val t
  | f_ne s t => val s <> val t
  | f_and A B => fml_holds val A /\ fml_holds val B
  | f_or A B => fml_holds val A \/ fml_holds val B
  | f_tt => True
  | f_ff => False
  end.

(** * Decidable equality *)

Definition i3_eq_dec (x y : i3) : {x = y} + {x <> y}. Proof. decide equality. Defined.
Definition i4_eq_dec (x y : i4) : {x = y} + {x <> y}. Proof. decide equality. Defined.
Definition mem13_eq_dec (x y : mem13) : {x = y} + {x <> y}.
Proof. decide equality; auto using i3_eq_dec, i4_eq_dec. Defined.
Definition sgn_eq_dec (x y : sgn) : {x = y} + {x <> y}. Proof. decide equality. Defined.
Definition coord_eq_dec (x y : coord) : {x = y} + {x <> y}. Proof. decide equality. Defined.
Definition wcomp_eq_dec (x y : wcomp) : {x = y} + {x <> y}. Proof. decide equality. Defined.
Definition tag1_eq_dec (x y : tag1) : {x = y} + {x <> y}. Proof. decide equality. Defined.
Definition tag2_eq_dec (x y : tag2) : {x = y} + {x <> y}. Proof. decide equality. Defined.

Definition rep1_eq_dec (x y : rep1) : {x = y} + {x <> y}.
Proof.
  decide equality;
    auto using mem13_eq_dec, sgn_eq_dec, tag1_eq_dec, wcomp_eq_dec.
Defined.

Definition rep2_eq_dec (x y : rep2) : {x = y} + {x <> y}.
Proof.
  decide equality;
    auto using mem13_eq_dec, sgn_eq_dec, tag2_eq_dec, wcomp_eq_dec.
Defined.

Definition sym0_eq_dec (x y : sym0) : {x = y} + {x <> y}.
Proof. decide equality; auto using Z.eq_dec, PeanoNat.Nat.eq_dec. Defined.

Definition sym1_eq_dec (x y : sym1) : {x = y} + {x <> y}.
Proof. decide equality; auto using coord_eq_dec, rep1_eq_dec, PeanoNat.Nat.eq_dec. Defined.

Definition sym2_eq_dec (x y : sym2) : {x = y} + {x <> y}.
Proof. decide equality; auto using rep2_eq_dec, PeanoNat.Nat.eq_dec. Defined.

Definition term_eq_dec {X : Type} (HX : forall x y : X, {x = y} + {x <> y})
  (s t : term X) : {s = t} + {s <> t}.
Proof. decide equality; auto using sym0_eq_dec, sym1_eq_dec, sym2_eq_dec. Defined.

Definition gterm_eq_dec : forall s t : gterm, {s = t} + {s <> t} :=
  term_eq_dec (fun x : Empty_set => match x with end).

(** * Small facts *)

Lemma all_mem13_spec j : In j all_mem13.
Proof. destruct j as [ | [] [] ]; simpl; tauto. Qed.

Lemma all_i4_spec b : In b all_i4.
Proof. destruct b; simpl; tauto. Qed.

Lemma all_i3_spec i : In i all_i3.
Proof. destruct i; simpl; tauto. Qed.

Lemma all_sgn_spec s : In s all_sgn.
Proof. destruct s; simpl; tauto. Qed.

Lemma all_mem13_length : length all_mem13 = 13.
Proof. reflexivity. Qed.

Lemma fml_holds_subst {X Y R : Type} (val : term Y -> R) (σ : X -> term Y) (A : fml X) :
  fml_holds val (fml_subst σ A) <-> fml_holds (fun t => val (tsubst σ t)) A.
Proof. induction A; simpl; tauto. Qed.
