(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO Monads.STM.

From Stdlib Require Import List Arith Classes.EquivDec.

Import ListNotations.
Set Implicit Arguments.
Set Primitive Projections.

Module stmtest.

(* === Tests === *)

Inductive Ty :=
| Nat : Ty
| List : Ty -> Ty.

Definition D : Ty -> Type :=
  fix _denote (t : Ty) :=
    match t with
    | Nat => nat
    | List t => list (_denote t)
    end.

(*
Definition Ty_dec (x y : Ty) : {x = y} + {x <> y}.
  decide equality.
Defined.

#[global] Instance EqDec_Ty : EqDec Ty eq := Ty_dec.
*)

Crane Extract Skip Ty.
Crane Extract Skip Ty_rect.
Crane Extract Skip Ty_rec.
Crane Extract Skip D.
(*
Crane Extract Skip Ty_dec.
Crane Extract Skip EqDec_Ty.
*)



Definition ioStmE := ioE +' runStmE D.

Crane Extract Skip ioStmE.

(* 1) Basic: test creating a TVar, reading and writing *)
Definition basic_read (x : nat) : itree ioStmE nat :=
  c <- atomically (newTVar Nat x) ;;
  atomically (readTVar c).

Definition basic_write (x : nat) : itree ioStmE nat :=
  c <- atomically (newTVar Nat 0) ;;
  atomically (writeTVar c x) ;;
  atomically (readTVar c).

(* 2) Increment test: testing reading and writing in one transaction *)
Definition increment (x : nat) : itree ioStmE nat :=
  c <- atomically (newTVar Nat x) ;;
  atomically (modifyTVar c S) ;;
  atomically (readTVar c).

(* 3) Test that a transaction can read its own writes *)
Definition write_read (x : nat) : itree ioStmE nat :=
  c <- atomically (newTVar Nat 0) ;;
  atomically (
    writeTVar c x ;;
    readTVar c
  ).

(* 4) A small queue modeled as list nat inside a TVar *)

(* push at tail *)
Definition stm_enqueue {K} {V : K -> Type} (q : TVar V (list nat)) (x : nat) : itree (stmE V) unit :=
  xs <- readTVar q ;;
  writeTVar q (xs ++ [x]).

(* pop from head; retry if empty *)
Definition stm_dequeue {K} {V : K -> Type} (q : TVar V (list nat)) : itree (stmE V) nat :=
  xs <- readTVar q ;;
  match xs with
  | []      => retry
  | y :: ys => writeTVar q ys ;; Ret y
  end.

(* tryDequeue with default, using orElse to avoid blocking *)
(*
Definition stm_tryDequeue {K} {V : K -> Type} (q : TVar V (list nat)) : itree (stmE V) (option nat) :=
  orElse (v <- stm_dequeue q ;; Ret (Some v)) (Ret None).
*)

(* smoke test: enqueue then dequeue must return the enqueued element *)
Definition io_queue_roundtrip (x y : nat) : itree ioStmE nat :=
  q <- atomically (newTVar (List Nat) []) ;;
  atomically (stm_enqueue q x ;; stm_enqueue q y) ;;
  atomically (stm_dequeue q).

(* 5) orElse + retry behavior *)
(* First branch retries on empty; second returns a constant 42 *)
(*
Definition stm_orElse_retry_example (_ : unit) : itree stmE nat :=
  q <- newTVar ([] : list nat) ;;
  orElse (stm_dequeue q) (Ret 42).

Definition io_orElse_retry_example : itree ioE nat :=
  atomically (stm_orElse_retry_example tt).
*)

End stmtest.

Crane Extraction "stm" stmtest.
