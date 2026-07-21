From Crane Require Import Monads.ITree.

From ITree Require Import Basics.Basics Basics.CategoryOps.

#[local] Open Scope itree_scope.

Variant atomicE E : Type -> Type :=
| Atomic : forall {A} (t : itree E A), atomicE E A.

Arguments Atomic {E} {A} (_).

Definition h_atomic {E F} `{E -< F} : atomicE E ~> itree F :=
  fun _ e =>
    match e with
    | Atomic t => translate subevent t
    end.

Definition run_atomic {E F} `{E -< F} : itree (atomicE E +' F) ~> itree F :=
  interp (case_ h_atomic (id_ _)).

Arguments run_atomic {E F H T} (t).
