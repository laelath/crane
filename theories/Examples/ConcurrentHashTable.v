(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Concurrent hash table built on STM and vector effects.

   Flavor-independent implementation. Import a flavor file ([Monads.STM]
   or [Monads.STMBDE]) before extraction to supply the C++ inline customs.
   The [CHT.max] function needs a flavor-specific inline custom:
   - Std: [Crane Extract Inlined Constant CHT.max => "std::max(%a0, %a1)".]
   - BDE: [Crane Extract Inlined Constant CHT.max => "bsl::max(%a0, %a1)".]
*)
From Stdlib Require Import List Bool Nat.
From Crane Require Extraction.
From Crane Require Import Monads.ITree Monads.IODefs Monads.STMDefs.
From Crane Require Import Utils.WithPost.
From ITree Require Import Eq Props.HasPost.

Import ListNotations.
Set Implicit Arguments.

(*
Axiom nat_of_int : int -> nat.
Crane Extract Inlined Constant nat_of_int => "static_cast<unsigned int>(%a0)".
*)

Module CHT.

Section key_val.

Context {K V : Type}.

Definition const_type : unit -> Type :=
  fun _ => list (K * V).

#[local] Notation TVar := (TVar const_type).
#[local] Notation stmE := (stmE const_type).



Fixpoint assoc_lookup (eqb : K -> K -> bool) (k : K) (xs : list (K * V))
  : option V :=
  match xs with
  | [] => None
  | (k', v) :: tl => if eqb k k' then Some v else assoc_lookup eqb k tl
  end.

Fixpoint assoc_insert_or_replace
         (eqb : K -> K -> bool) (k : K) (v : V) (xs : list (K * V))
  : list (K * V) :=
  match xs with
  | [] => [(k, v)]
  | (k', v') :: tl =>
      if eqb k k' then (k, v) :: tl
      else (k', v') :: assoc_insert_or_replace eqb k v tl
  end.

Fixpoint assoc_remove
         (eqb : K -> K -> bool) (k : K) (xs : list (K * V))
  : (option V * list (K * V)) :=
  match xs with
  | [] => (None, xs)
  | (k', v') :: tl =>
      if eqb k k'
      then (Some v', tl)
      else let q := assoc_remove eqb k tl in (fst q, (k', v') :: (snd q))
  end.

Record CHT := {
  cht_eqb     : K -> K -> bool;
  cht_hash    : K -> nat;
  cht_buckets : list (TVar (list (K * V)));
  cht_fallback : TVar (list (K * V));
}.

(* Total bucket selection *)
Definition bucket_of (t : CHT) (k : K)
  :  TVar (list (K * V)) :=
  let i := modulo (t.(cht_hash) k) (length t.(cht_buckets)) in
  nth i t.(cht_buckets) t.(cht_fallback).

Section STM.

(* Get *)
Definition stm_get (t : CHT) (k : K) : itree stmE (option V) :=
  let b := bucket_of t k in
  xs <- readTVar b ;;
  Ret (assoc_lookup t.(cht_eqb) k xs).

(* Put / upsert *)
Definition stm_put (t : CHT) (k : K) (v : V) : itree stmE unit :=
  let b := bucket_of t k in
  xs <- readTVar b ;;
  let xs' := assoc_insert_or_replace t.(cht_eqb) k v xs in
  writeTVar b xs' ;;
  Ret tt.

(* Delete; returns previous value if any *)
Definition stm_delete (t : CHT) (k : K) : itree stmE (option V) :=
  let b := bucket_of t k in
  xs <- readTVar b ;;
  let p := assoc_remove t.(cht_eqb) k xs in
  match fst p with
  | None => Ret (fst p)
  | _ =>
    writeTVar b (snd p) ;;
    Ret (fst p)
  end.

(* Update with a function of the old option; returns the new value *)
Definition stm_update
           (t : CHT) (k : K) (f : option V -> V) : itree stmE V :=
  let b := bucket_of t k in
  xs <- readTVar b ;;
  let ov := assoc_lookup t.(cht_eqb) k xs in
  let v  := f ov in
  let xs' := assoc_insert_or_replace t.(cht_eqb) k v xs in
  writeTVar b xs' ;;
  Ret v.

Definition stm_get_or (t : CHT) (k : K) (dflt : V) : itree stmE V :=
  v <- stm_get t k ;;
  match v with
  | Some x => Ret x
  | None => Ret dflt
  end.

(*
Definition max : int -> int -> int := fun a b =>
  if ltb a b then b else a.
*)

End STM.

#[local] Notation runStmE := (runStmE const_type).

Definition runStmIOE := runStmE +' ioE.

(* Build N empty buckets *)
Definition mk_buckets (num : nat) : itree runStmIOE (list (TVar (list (K * V)))) :=
  (fix f buckets n :=
    match n with
    | 0 => Ret buckets
    | S n' =>
        b <- atomically (newTVar tt []) ;;
        f (b :: buckets) n'
    end) [] num.

Lemma mk_buckets_length : forall n, has_post (mk_buckets n) (fun buckets => length buckets = n).
Proof.
  intros.
  unfold mk_buckets.
  apply has_post_subrel with (P := fun buckets => length buckets = n + length ([] : list (TVar (const_type tt)))).
  { intros. rewrite plus_n_O. apply H. }
  generalize ([] : list (TVar (const_type tt))).
  induction n.
  - intros. apply eutt_Ret. reflexivity.
  - intros.
    apply has_post_bind_weak.
    intros.
    cbn. rewrite plus_n_Sm.
    apply IHn.
Qed.

(* Create a new table with at least one bucket; stores eqb/hash in the record *)
Definition new_hash
           (eqb : K -> K -> bool) (hash : K -> nat) (requested : nat)
  : itree runStmIOE CHT :=
  let n := max requested 1 in
  buckets <- mk_buckets (n - 1) ;;
  fallback <- atomically (newTVar tt []) ;;
  Ret {| cht_eqb := eqb; cht_hash := hash;
         cht_buckets := fallback :: buckets;
         cht_fallback := fallback |}.

Definition put  (t : CHT) (k : K) (v : V) : itree runStmIOE unit :=
  atomically (stm_put t k v).

Definition get  (t : CHT) (k : K) : itree runStmIOE (option V) :=
  atomically (stm_get t k).

Definition hash_delete (t : CHT) (k : K) : itree runStmIOE (option V) :=
  atomically (stm_delete t k).

Definition hash_update
           (t : CHT) (k : K) (f : option V -> V) : itree runStmIOE V :=
  atomically (stm_update t k f).

Definition get_or (t : CHT) (k : K) (dflt : V) : itree runStmIOE V :=
  atomically (stm_get_or t k dflt).

End key_val.

End CHT.
