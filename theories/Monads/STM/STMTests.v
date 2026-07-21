From Crane.Monads Require Import STMDefs.
From Crane.Monads.STM Require Import
     ForkDefs
     TransactionDefs
     AtomicTransactions
     SGL
     TL2.

From ITree Require Import ITree Basics.Basics.
Import ITreeNotations.


From Stdlib Require Import Classes.EquivDec.

Section example.

  #[global] Instance EqDec_unit : EqDec unit eq :=
    fun x y => match x, y with tt, tt => left eq_refl end.

  Definition nats (_ : unit) : Type := nat.

  Definition fib_trans (x0 x1 : TVar nats nat): itree (stmE nats) unit :=
    v0 <- readTVar x0 ;;
    v1 <- readTVar x1 ;;
    writeTVar x0 v1 ;;
    writeTVar x1 (v0 + v1).

  Definition fib (n : nat) : itree (runStmE nats +' forkE) unit :=
    '(x, y) <- atomically (
      x <- newTVar tt 0 ;;
      y <- newTVar tt 1 ;;
      Ret (x, y)) ;;
    (fix fib_ n :=
      match n with
      | 0 => Ret tt
      | S n => fork (atomically (fib_trans x y)) (fib_ n)
      end) n.

  Variant result (E : Type -> Type) (A : Type) :=
  | Val : A -> result E A
  | NotYet : result E A
  | Event : forall {X}, E X -> result E A.

  Arguments Val {E A} (a).
  Arguments NotYet {E A}.
  Arguments Event {E A} {X} (e).

  Definition force {E A} (n : nat) (t : itree E A) : result E A :=
    match observe (burn n t) with
    | RetF a => Val a
    | TauF _ => NotYet
    | VisF e _ => Event e
    end.

  Definition unwrap {E A} : option A -> itree E A :=
    fun o => match o with None => ITree.spin | Some a => Ret a end.

  Compute (force 200 (run_atomic_transactions (run_atomically (fib 8)))).
  Compute (force 1000 (run_single_lock_fork (run_atomically (fib 8)))).
  Compute (force 1874 (run_tl2_fork (run_atomically (fib 8)))).

  Definition read_test : itree (runStmE nats +' forkE) unit :=
    x <- atomically (newTVar tt 21) ;;
    atomically (readTVar x) ;;
    Ret tt.

  Definition write_test : itree (runStmE nats +' forkE) unit :=
    x <- atomically (newTVar tt 22) ;;
    atomically (writeTVar x 23).

  Definition inc_test : itree (runStmE nats +' forkE) unit :=
    x <- atomically (newTVar tt 0) ;;
    atomically (v <- readTVar x ;; writeTVar x (S v)).

  Compute (force 1000 (run_tl2_fork (run_atomically read_test))).
  Compute (force 1000 (run_tl2_fork (run_atomically write_test))).
  Compute (force 1000 (run_tl2_fork (run_atomically inc_test))).

  Definition takeMVar {K} {V : K -> Type} {A} (t : TVar V (option A)) : itree (stmE V) A :=
    v <- readTVar t ;;
    match v with
    | None => retry
    | Some a => writeTVar t None ;; Ret a
    end.

  Definition putMVar {K} {V : K -> Type} {A} (t : TVar V (option A)) (a : A) : itree (stmE V) unit :=
    v <- readTVar t ;;
    match v with
    | None => writeTVar t (Some a)
    | Some _ => retry
    end.

  Inductive Ty :=
  | Nat : Ty
  | Opt : Ty -> Ty.

  Definition Ty_dec (x y : Ty) : {x = y} + {x <> y}.
    decide equality.
  Defined.

  #[global] Instance EqDec_Types : EqDec Ty eq := Ty_dec.

  Fixpoint D (type : Ty) : Type :=
    match type with
    | Nat => nat
    | Opt t => option (D t)
    end.

  Definition message_passing : itree (runStmE D +' forkE) unit :=
    mv <- atomically (newTVar (Opt Nat) None) ;;
    done <- atomically (newTVar Nat 0) ;;
    fork (v1 <- atomically (takeMVar mv) ;; v2 <- atomically (takeMVar mv) ;; atomically (putMVar mv (v1 + v2)))
         (atomically (putMVar mv 3) ;; atomically (putMVar mv 4) ;; atomically (V := D) (r <- takeMVar mv ;; writeTVar done r)).

  Definition message_passing_simple : itree (runStmE D +' forkE) unit :=
    mv <- atomically (newTVar (Opt Nat) None) ;;
    done <- atomically (newTVar Nat 0) ;;
    fork (v1 <- atomically (takeMVar mv) ;; atomically (putMVar mv (v1 * v1)))
         (atomically (putMVar mv 3) ;; atomically (V := D) (r <- takeMVar mv ;; writeTVar done r)).

  Definition message_passing_simpler : itree (runStmE D +' forkE) unit :=
    mv <- atomically (newTVar (Opt Nat) None) ;;
    done <- atomically (newTVar Nat 0) ;;
    fork (v1 <- atomically (takeMVar mv) ;; atomically (writeTVar done (v1 * v1)))
         (atomically (putMVar mv 3)).

  Compute (force 100 (run_atomic_transactions (run_atomically message_passing_simpler))).
  Compute (force 100 (run_atomic_transactions (run_atomically message_passing_simple))).
  Compute (force 200 (run_atomic_transactions (run_atomically message_passing))).
  Compute (force 200 (run_single_lock_fork (run_atomically message_passing_simpler))).
  Compute (force 200 (run_single_lock_fork (run_atomically message_passing_simple))).
  Compute (force 300 (run_single_lock_fork (run_atomically message_passing))).
  Compute (force 1000 (run_tl2_fork (run_atomically message_passing_simpler))).
  Compute (force 1000 (run_tl2_fork (run_atomically message_passing_simple))).
  Compute (force 1000 (run_tl2_fork (run_atomically message_passing))).

  (* TODO: tests with orElse *)

End example.


