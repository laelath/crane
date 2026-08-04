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

Import ListNotations.
Set Implicit Arguments.

(*
Axiom nat_of_int : int -> nat.
Crane Extract Inlined Constant nat_of_int => "static_cast<unsigned int>(%a0)".
*)

From ITree Require Import Eq Props.HasPost.
From Paco Require Import paco.

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
  cht_nbuckets: nat;
  cht_buckets : list (TVar (list (K * V)));
  cht_fallback : TVar (list (K * V));
  cht_buckets_wf : length cht_buckets = cht_nbuckets
}.

(* Total bucket selection *)
Definition bucket_of (t : CHT) (k : K)
  :  TVar (list (K * V)) :=
  let i := modulo (t.(cht_hash) k) t.(cht_nbuckets) in
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

Lemma has_post_subrel : forall {E R} (t : itree E R) (P Q : R -> Prop),
  (forall x, P x -> Q x) ->
  has_post t P ->
  has_post t Q.
Proof.
  intros.
  eapply eutt_subrel, H0.
  intros ??.
  apply H.
Qed.

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



Lemma has_post_eta {E R} {P : R -> Prop} (t : itree E R) : has_post t P -> has_post (go (observe t)) P.
Proof.
  intros.
  rewrite <- itree_eta.
  assumption.
Qed.

Lemma has_post_inv_Ret {E R} {P : R -> Prop} (r : R) : has_post ((Ret r) : itree E R) P -> P r.
Proof.
  intros.
  apply eqit_inv_Ret in H.
  apply H.
Qed.

Lemma has_post_inv_Tau {E R} {P : R -> Prop} (t : itree E R) : has_post (Tau t) P -> has_post t P.
Proof.
  intros.
  apply eqit_inv_Tau in H.
  apply H.
Qed.

Lemma has_post_inv_Vis {E R} {P : R -> Prop} {X} (e : E X) (k : X -> itree E R) : has_post (Vis e k) P -> forall x, has_post (k x) P.
Proof.
  intros.
  eapply eqit_inv_Vis in H.
  apply H.
Qed.

CoFixpoint with_post {E R} {P : R -> Prop} (t : itree E R) (pf : has_post t P) : itree E {x:R | P x} :=
  let ot := observe t in
  let pf' := has_post_eta pf in
  (match ot return ot = observe t -> _ with
  | RetF r => fun Heqot => Ret (exist P r (has_post_inv_Ret (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot)))
  | TauF t => fun Heqot => Tau (@with_post E R P t (has_post_inv_Tau (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot)))
  | VisF e k => fun Heqot => Vis e (fun x => @with_post E R P (k x) (has_post_inv_Vis (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot) x))
  end) eq_refl.

Arguments with_post : clear implicits.
Arguments with_post {E R P} (t pf).

Notation with_post_ P t pf :=
  (let ot := observe t in
  let pf' := has_post_eta pf in
  (match ot return ot = observe t -> _ with
  | RetF r => fun Heqot => Ret (exist P r (has_post_inv_Ret (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot)))
  | TauF t => fun Heqot => Tau (@with_post _ _ P t (has_post_inv_Tau (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot)))
  | VisF e k => fun Heqot => Vis e (fun x => @with_post _ _ P (k x) (has_post_inv_Vis (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot) x))
  end) eq_refl).



Lemma unfold_with_post {E R} (P : R -> Prop) (t : itree E R) (pf : has_post t P) :
  with_post t pf ≅ with_post_ P t pf.
Proof.
  apply observing_sub_eqit; constructor; reflexivity.
Qed.


Lemma with_post_proj1 {E R} {P : R -> Prop} (t : itree E R) (pf : has_post t P) :
  ITree.map (@proj1_sig R P) (with_post t pf) ≅ t.
Proof.
  revert t pf.
  unfold ITree.map.
  ginit.
  gcofix CIH.
  intros.
  rewrite unfold_with_post.
  gstep.
  generalize (observe t).
  red in pf.
Abort.


(* Create a new table with at least one bucket; stores eqb/hash in the record *)
Definition new_hash
           (eqb : K -> K -> bool) (hash : K -> nat) (requested : nat)
  : itree runStmIOE CHT :=
  let n := max requested 1 in
  '(exist _ buckets Hbuckets) <- with_post (mk_buckets n) (mk_buckets_length n) ;;
  _.
(*
  fallback <- get bs 0 ;;
  Ret {| cht_eqb := eqb; cht_hash := hash;
         cht_buckets := bs; cht_nbuckets := n; cht_fallback := b |}.
*)

Definition put  {K V} (t : CHT K V) (k : K) (v : V) : itree ioE unit :=
  atomically (stm_put t k v).

Definition get  {K V} (t : CHT K V) (k : K) : itree ioE (option V) :=
  atomically (stm_get t k).

Definition hash_delete {K V} (t : CHT K V) (k : K) : itree ioE (option V) :=
  atomically (stm_delete t k).

Definition hash_update {K V}
           (t : CHT K V) (k : K) (f : option V -> V) : itree ioE V :=
  atomically (stm_update t k f).

Definition get_or {K V} (t : CHT K V) (k : K) (dflt : V) : itree ioE V :=
  atomically (stm_get_or t k dflt).

End key_val.

End CHT.
