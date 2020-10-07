From Undecidability.L Require Import L Datatypes.Lists.

Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Vector List.

Require Import Undecidability.TM.Util.TM_facts.

Import L.L TM.TM.
Require Import List.
Import ListNotations.


Definition encTM {Σ : Type} (s b : Σ) (l : list bool) :=
  @midtape Σ [] b (map (fun (x : bool) => (if x then s else b)) l).

Import VectorNotations.


Definition TM_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : TM Σ (k + 1 + n),
  forall v : Vector.t (list bool) k, 
  (forall m, R v m <-> exists q t, TM.eval M (start M) ((Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n) q t
                                /\ nth_error (Vector.to_list t) k = Some (encTM s b m)) /\
  (forall q t, TM.eval M (start M) ((Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n) q t ->
          exists m, nth_error (Vector.to_list t) k = Some (encTM s b m)).


Definition TM_computable_rel {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : pTM Σ unit (k + 1 + n),
    Realise M (fun t '(_, t') =>
                                       forall v, t = (Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n ->
                                            exists m, nth_error (Vector.to_list t') k = Some (encTM s b m) /\ R v m) /\
    exists f,
      TerminatesIn (projT1 M) (fun t i => exists v m, R v m /\ t = (Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n /\ i >= f k v).

      
Definition encL (l : list bool) := list_enc l.

Definition L_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists s, forall v : Vector.t (list bool) k, 
      (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encL n)) s v) (encL m)) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encL n)) s v) o -> exists m, o = encL m).