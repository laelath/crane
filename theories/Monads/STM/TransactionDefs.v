(* represents transactions as subcomputations that can potentially fail *)

From Crane Require Import Monads.STMDefs Monads.ITree.

From ITree Require Import Basics.Basics Basics.CategoryOps.

Variant transactionE E : Type -> Type :=
| Transaction : forall {A}, itree E A -> transactionE E (option A).

Arguments Transaction {E} {A} (_).

Definition h_atomically {K} {V : K -> Type} {E} `{transactionE (stmE V) -< E} : runStmE V ~> itree E :=
  fun _ e =>
    match e with
    | Atomically t =>
        ITree.iter (fun _ =>
                      oa <- trigger (Transaction t) ;;
                      match oa with
                      | None => Ret (inl tt)
                      | Some a => Ret (inr a)
                      end) tt
    end.


Definition run_atomically {K} {V : K -> Type} {E A} (t0 : itree (runStmE V +' E) A):
  itree (transactionE (stmE V) +' E) A :=
  interp (bimap h_atomically (id_ _)) t0.
