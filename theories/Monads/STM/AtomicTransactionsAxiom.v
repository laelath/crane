From Crane.Monads Require Import ITree STMDefsAxiom STM.Atomic STM.TransactionDefs STM.ForkDefs STM.WriteLog.
From Crane.Utils Require Import HMap HAList.

From Stdlib Require Import List Classes.EquivDec.

Import ListNotations.

From ITree Require Import Basics.Basics Basics.CategoryOps Events.FailFacts.

Import Basics.Monads.

Axiom tid : Type.
Axiom tid_eq_dec : forall (i1 i2 : tid), i1 = i2 \/ i1 <> i2.

Variant transactionImplE E : Type -> Type :=
| NewTransactionID : transactionImplE E tid
| TransactionEvent : forall X, E X -> tid -> transactionImplE E X
| AbortTransaction : tid -> transactionImplE E unit
| CommitTransaction : tid -> transactionImplE E unit.

Definition embed_transaction_events (t : tid) : stmE ~> failT (itree (transactionImplE tvarE)) :=
  fun _ e =>
    match e with
    | inl1 Retry => Ret None
    | inr1 e => v <- trigger (TransactionEvent _ _ e t);; Ret (Some v)
    end.

(* Implements transactions by executing them atomically (blocks all other threads from executing until it is finished) *)
Definition h_atomic_transactions : transactionE stmE ~> atomicE (transactionImplE tvarE) :=
  fun _ e =>
    match e with
    | Transaction t =>
        Atomic (i <- trigger (NewTransactionID _) ;;
                res <- interp (embed_transaction_events i) t ;;
                match res with
                | Some a =>
                    trigger (CommitTransaction _ i) ;;
                    Ret (Some a)
                | None =>
                    trigger (AbortTransaction _ i) ;;
                    Ret None
                end)
    end.

Definition atomic_transactions {E} `{atomicE (transactionImplE tvarE) -< E} : transactionE stmE ~> itree E :=
  fun _ e => trigger (h_atomic_transactions _ e).

Definition run_atomic_transactions
  (t1 : itree (transactionE stmE +' forkE) unit):
  itree void1 (halist (pkey K nat) (pkey_type V) * unit) :=
  let t2 := interp (case_ (C := IFun) (bif := sum1) (c := itree (forkE +' atomicE (tvarE V) +' tvarE V))
                          atomic_transactions
                          (fun _ e => trigger e))
                   t1 in
  let t3 : itree (tvarE V) unit := run_atomic (schedule_rr [t2]) in
  let t4 : stateT _ _ _ := interp (handle_tvars _ _) t3 in
  t4 HMap.empty.
