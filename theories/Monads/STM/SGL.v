(* implements the single global lock STM algorithm *)
From Crane Require Import Monads.ITree Monads.STMDefs Monads.STM.TransactionDefs Monads.STM.WriteLog Monads.STM.ForkDefs.
From Crane.Utils Require Import HMap HAList.

From Stdlib Require Import Arith.PeanoNat Bool.Bool Classes.EquivDec List.

Import ListNotations.

From ITree Require Import Basics.Basics Basics.CategoryOps Events.State Events.FailFacts.

Import Basics.Monads.

Variant lockE : Type -> Type :=
| TryLock : lockE bool
| Unlock : lockE unit.

Definition spinlock {E} `{lockE -< E} : itree E unit :=
  ITree.iter (fun n => b <- trigger TryLock ;; if (b : bool) then Ret (inr tt) else Ret (inl (S n))) 0.

(* TODO: generalize to any HMap *)
(* implements transactions through a single global lock that is acquired before transaction execution *)
Definition single_global_lock {K} {V : K -> Type} `{EqDec K eq} {E} `{lockE -< E} `{tvarE V -< E}:
  transactionE (stmE V) ~> itree E :=
  fun _ e =>
    match e with
    | Transaction t =>
        spinlock ;;
        let m : stateT (halist (pkey K nat) (pkey_type V)) (failT (itree E)) _ :=
          interp h_stm_write_log t in
        res <- m [] ;;
        match res with
        | Some (m, a) =>
            commit_log _ m ;;
            trigger Unlock ;;
            Ret (Some a)
        | None =>
            trigger Unlock ;;
            Ret None
        end
    end.

Definition h_lock {E} : lockE ~> stateT bool (itree E) :=
  fun _ e l =>
    match e with
    | TryLock => Ret (true, negb l)
    | Unlock => Ret (false, tt)
    end.

Definition h_trigger {E F} `{E -< F}: Handler E F :=
  fun _ e => trigger e.

Definition run_single_lock_fork {K} `{EqDec K eq} {V : K -> Type}
  (t1 : itree (transactionE (stmE V) +' forkE) unit):
  itree void1 (halist (pkey K nat) (pkey_type V) * (bool * unit)) :=
  let t2 : itree (forkE +' lockE +' tvarE V) unit :=
    interp (case_ single_global_lock h_trigger) t1 in
  let t3 := schedule_rr [t2] in
  let t4 : stateT bool (itree (tvarE V)) unit := interp (case_ h_lock pure_state) t3 in
  let t5 : stateT _ (itree void1) _ := interp (handle_tvars _ _) (t4 false) in
  t5 HMap.empty.

