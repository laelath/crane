From Crane.Monads Require Import ITree STMDefs2 STM.Atomic STM.TransactionDefs STM.ForkDefs STM.WriteLog.
From Crane.Utils Require Import HMap HAList.

From Stdlib Require Import List Classes.EquivDec.

Import ListNotations.

From ITree Require Import Basics.Basics Basics.CategoryOps Events.FailFacts.

Import Basics.Monads.

(* TODO: generalize to any HMap *)
(* Implements transactions by executing them atomically (blocks all other threads from executing until it is finished) *)
Definition h_atomic_transactions : transactionE stmE ~> atomicE tvarE :=
  fun _ e =>
    match e with
    | Transaction t =>
        let m : stateT (halist (pkey K nat) (pkey_type V)) (failT (itree (tvarE V))) _ :=
          interp h_stm_write_log t in
        Atomic (res <- m [] ;;
                match res with
                | Some (m, a) =>
                    commit_log _ m ;;
                    Ret (Some a)
                | None => Ret None
                end)
    end.

Definition atomic_transactions {K} {V : K -> Type} `{EqDec K eq} {E} `{atomicE (tvarE V) -< E}: transactionE (stmE V) ~> itree E :=
  fun _ e => trigger (h_atomic_transactions _ e).

Definition run_atomic_transactions {K} `{EqDec K eq} {V : K -> Type}
  (t1 : itree (transactionE (stmE V) +' forkE) unit):
  itree void1 (halist (pkey K nat) (pkey_type V) * unit) :=
  let t2 := interp (case_ (C := IFun) (bif := sum1) (c := itree (forkE +' atomicE (tvarE V) +' tvarE V))
                          atomic_transactions
                          (fun _ e => trigger e))
                   t1 in
  let t3 : itree (tvarE V) unit := run_atomic (schedule_rr [t2]) in
  let t4 : stateT _ _ _ := interp (handle_tvars _ _) t3 in
  t4 HMap.empty.
