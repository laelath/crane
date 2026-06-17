From Crane Require Import Monads.ITree Monads.STM.Schedule.

From Stdlib Require Import List.

Import ListNotations.

From ExtLib Require Import Structures.Monad.

From ITree Require Import Basics.CategoryOps.

Open Scope itree_scope.

Variant atomicE E : Type -> Type :=
| Atomic : forall {A} (t : itree E A), atomicE E A.

Arguments Atomic {E} {A} (_).

Variant forkE : Type -> Type :=
| Fork : forkE bool.

Definition fork {E} `{forkE -< E} (t1 t2 : itree E unit) : itree E unit :=
  b <- trigger Fork ;;
  if (b : bool) then t1 else t2.

(* arranged so that a scheduleE handler that always returns 0 will be a round-robin scheduler *)
CoFixpoint schedule {E F} `{F -< E} (l : list (itree (atomicE F +' forkE +' E) unit)) : itree (scheduleE +' E) unit :=
  match l with
  | [] => Ret tt
  | _ =>
    Vis (subevent _ (Schedule (length l)))
        (fun n =>
          let l1 := firstn (proj1_sig n) l in
          let l2 := skipn (S (proj1_sig n)) l in
          let t := signth l n in
          match observe t with
          | RetF _ => schedule (l1 ++ l2)
          | TauF t => schedule (l1 ++ l2 ++ [t])
          | VisF (inl1 e) k =>
              match e, k with
              | Atomic t, k => a <- translate subevent t ;; schedule (l1 ++ l2 ++ [k a])
              end
          | VisF (inr1 (inl1 e)) k =>
              match e, k with
              | Fork, k => schedule (l1 ++ l2 ++ [k true; k false])
              end
          | VisF (inr1 (inr1 e)) k => Vis (subevent _ e) (fun x => schedule (l1 ++ l2 ++ [k x]))
          end)
  end.

Definition schedule_rr {E F} `{F -< E} (l : list (itree (atomicE F +' forkE +' E) unit)) : itree E unit :=
  interp (case_ h_rr (id_ _)) (schedule l).
