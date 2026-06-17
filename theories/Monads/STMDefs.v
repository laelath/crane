(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared STM effect definitions (flavor-independent).

   Contains the effect inductives ([tvarE], [stmVecE], [stmControlE]),
   composed effect ([stmE]), axioms, and smart constructors that are
   identical across library flavors. Flavor files ([STM.v], [STMBDE.v])
   re-export this module and add flavor-specific C++ extraction mappings.
*)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Monads.ITree.

From ITree Require Import Basics.Basics.

Open Scope itree_scope.



Variant TVar {K} (V : K -> Type) : Type -> Type :=
| mk_tvar : forall (n : nat) (k : K), TVar V (V k).



Inductive tvarE {K : Type} (V : K -> Type) : Type -> Type :=
| NewTVar : forall (k : K), V k -> tvarE V (TVar V (V k))
| ReadTVar : forall {A}, TVar V A -> tvarE V A
| WriteTVar : forall {A}, TVar V A -> A -> tvarE V unit.

Arguments NewTVar {K} {V}.
Arguments ReadTVar {K} {V} {A}.
Arguments WriteTVar {K} {V} {A}.



Inductive stmControlE : Type -> Type :=
| Retry : stmControlE void.

Crane Extract Inductive stmControlE => ""
  [ "stm::retry()" ].

Definition stmE {K} (V : K -> Type) : Type -> Type := stmControlE +' tvarE V.
Crane Extract Skip stmE.

Definition retry {K} {V : K -> Type} {A} : itree (stmE V) A :=
  trigger (inl1 Retry) >>= fun (x : void) => match x with end.

(* not entirely sure why this is required *)
(*
#[global] Instance tvarE_sub_stmE {K} (V : K -> Type) : tvarE V -< stmE V := inr1.
#[global] Instance stmControlE_sub_stmE {K} (V : K -> Type) : stmControlE -< stmE V := inl1.
Crane Extract Skip tvarE_sub_stmE.
Crane Extract Skip stmControlE_sub_stmE.
*)



Variant runStmE {K} (V : K -> Type) : Type -> Type :=
| Atomically : forall {A} (t : itree (stmE V) A), runStmE V A.

Arguments Atomically {K} {V} {A} (t).

Definition atomically {K} {V : K -> Type} {E} `{runStmE V -< E} {A} (t : itree (stmE V) A) : itree E A :=
  trigger (Atomically t).

Crane Extract Inductive runStmE => ""
  [ "stm::atomically([&] { return %a0; })" ].



(*
Definition orElse {A} {K} {V : K -> Type} `{EqDec K eq} (t1 t2 : itree (stmControlE +' tvarE V) A) : itree (stmE V) A :=
  (cofix _orElse (m : halist (pkey K nat) (pkey_type V)) t :=
    match observe t with
    | RetF a =>
        commit_log V m ;;
        Ret a
    | TauF t => Tau (_orElse m t)
    | VisF (inr1 e) k => '(x, m) <- handle_tvar_log m e ;; Tau (_orElse m (k x))
    | VisF (inl1 Retry) _ => t2
    end) HMap.empty t1.
*)



Definition newTVar {K V} (k : K) (a : V k) : itree (stmE V) (TVar V (V k)) := trigger (inr1 (NewTVar k a)).
Definition readTVar {K} {V : K -> Type} {A} (v : TVar V A) : itree (stmE V) A := trigger (inr1 (ReadTVar v)).
Definition writeTVar {K} {V : K -> Type} {A} (v : TVar V A) (a : A) : itree (stmE V) unit := trigger (inr1 (WriteTVar v a)).

Definition check {K} {V : K -> Type} (b : bool) : itree (stmE V) unit :=
  if b then Ret tt else retry.

Definition modifyTVar {K} {V : K -> Type} {A : Type} (a : TVar V A) (f : A -> A) : itree (stmE V) unit :=
  val <- readTVar a ;;
  writeTVar a (f val) ;;
  Ret tt.

Crane Extract Inlined Constant atomically => "stm::atomically([&] { return %a0; })".
(*Crane Extract Inlined Constant orElse => "stm::orElse<%t0>(%a0, %a1)".*)
Crane Extract Inlined Constant retry => "stm::retry<%t2>()".
Crane Extract Inlined Constant newTVar => "stm::newTVar(%a1)".
