(**************************************************************)
(*   Formalization of the preprint                            *)
(*   "Hilbert's tenth problem over the rational numbers"      *)
(*   (2026)                                                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Phase 2B input: nonprincipal ultrafilters on nat, as Prop-level
   predicates on Prop-valued sets  S : nat -> Prop.

   THE ONLY NON-LOGICAL AXIOM OF THE DEVELOPMENT is [ultrafilter_exists]
   below: there is a nonprincipal ultrafilter on nat. It is a consequence
   of the Boolean prime ideal theorem (ultrafilter lemma), stated in
   Prop: it asserts the existence of a predicate, it provides no function
   and no computational content, and it is used only to prove Prop-level
   statements (e.g. [Compactness D], which is itself a Prop). Everything
   else (ultrapower construction, its field laws) takes the ultrafilter as
   a Section variable, see Ultrapower.v. *)

(* an ultrafilter on nat, sets being Prop-valued predicates *)
Record ultrafilter (U : (nat -> Prop) -> Prop) : Prop := {
  uf_full : U (fun _ => True);
  uf_proper : ~ U (fun _ => False);
  uf_mono : forall A B : nat -> Prop, (forall n, A n -> B n) -> U A -> U B;
  uf_inter : forall A B : nat -> Prop, U A -> U B -> U (fun n => A n /\ B n);
  uf_total : forall A : nat -> Prop, U A \/ U (fun n => ~ A n)
}.

Arguments uf_full {U}.
Arguments uf_proper {U}.
Arguments uf_mono {U}.
Arguments uf_inter {U}.
Arguments uf_total {U}.

(* no finite set is in U *)
Definition nonprincipal (U : (nat -> Prop) -> Prop) : Prop :=
  forall A : nat -> Prop, (exists k, forall n, A n -> n < k) -> ~ U A.

Definition nonprincipal_ultrafilter (U : (nat -> Prop) -> Prop) : Prop :=
  ultrafilter U /\ nonprincipal U.

(** The ultrafilter lemma for nat (Prop-level consequence of BPI). *)
Axiom ultrafilter_exists : exists U : (nat -> Prop) -> Prop, nonprincipal_ultrafilter U.

(** Basic consequences, for an arbitrary ultrafilter. *)

Section ultrafilter_facts.

  Variables (U : (nat -> Prop) -> Prop) (HU : ultrafilter U).

  Lemma uf_all (A : nat -> Prop) : (forall n, A n) -> U A.
  Proof using HU. intros H; apply (uf_mono HU (fun _ => True)); [ intros n _; apply H | apply (uf_full HU) ]. Qed.

  Lemma uf_ae1 (A B : nat -> Prop) : U A -> (forall n, A n -> B n) -> U B.
  Proof using HU. intros HA H; exact (uf_mono HU _ _ H HA). Qed.

  Lemma uf_ae2 (A B C : nat -> Prop) : U A -> U B -> (forall n, A n -> B n -> C n) -> U C.
  Proof using HU.
    intros HA HB H; apply (uf_mono HU (fun n => A n /\ B n)); [ | apply (uf_inter HU); assumption ].
    intros n [ ? ? ]; auto.
  Qed.

  Lemma uf_ae3 (A B C D : nat -> Prop) :
    U A -> U B -> U C -> (forall n, A n -> B n -> C n -> D n) -> U D.
  Proof using HU.
    intros HA HB HC H; apply (uf_ae2 (fun n => A n /\ B n) C); [ | exact HC | ].
    - apply (uf_inter HU); assumption.
    - intros n [ ? ? ]; auto.
  Qed.

  (* exactly one of A and its complement *)
  Lemma uf_not_both (A : nat -> Prop) : U A -> U (fun n => ~ A n) -> False.
  Proof using HU. intros H1 H2; apply (uf_proper HU); apply (uf_ae2 _ _ _ H1 H2); intros n a na; exact (na a). Qed.

  Lemma uf_compl (A : nat -> Prop) : ~ U A -> U (fun n => ~ A n).
  Proof using HU. intros H; destruct (uf_total HU A) as [ H' | H' ]; [ contradiction | exact H' ]. Qed.

  Lemma uf_compl_iff (A : nat -> Prop) : ~ U A <-> U (fun n => ~ A n).
  Proof using HU. split; [ apply uf_compl | intros H H'; exact (uf_not_both A H' H) ]. Qed.

  Lemma uf_or (A B : nat -> Prop) : U (fun n => A n \/ B n) -> U A \/ U B.
  Proof using HU.
    intros H; destruct (uf_total HU A) as [ HA | HA ]; [ left; exact HA | right ].
    apply (uf_ae2 _ _ _ H HA); intros n [ a | b ] na; [ contradiction | exact b ].
  Qed.

End ultrafilter_facts.

Arguments uf_all {U}.
Arguments uf_ae1 {U}.
Arguments uf_ae2 {U}.
Arguments uf_ae3 {U}.
Arguments uf_not_both {U}.
Arguments uf_compl {U}.
Arguments uf_compl_iff {U}.
Arguments uf_or {U}.
