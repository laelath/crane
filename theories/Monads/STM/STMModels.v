From Crane.Monads Require Import STMDefs.
From Crane.Monads.STM Require Import
     ForkDefs
     TransactionDefs
     AtomicTransactions
     SGL
     TL2.


From Stdlib Require Import Classes.EquivDec.

(*
So we want opacity, but that requires reasoning about histories and talking intrinsically about
what is allowed, I do not like this because
*)

(*
Have a simulation where the adversary is making plays with the transactional memory implementation,
and you are responding with plays from an idealized transactional memory rules.
The simulation has plays to spawn arbitrary transactions (sounds kinda sketchy if you are always allowed to do this, probably need to limit it to only when the adversary does it?)
The simulation would be terminated by a state relation that the simulation is indexed by
Simulation is a relation on a list of live transactions from the implementation(?) and a corresponding list of transactions from the idealized model(?) and a starting state.
*)

From Stdlib Require Import List Relations.Relation_Definitions.
Import ListNotations.

From ITree Require Import ITree Basics.Basics Eq Events.State.
Import Basics.Monads.

From Coinduction Require Import all.

From RelationAlgebra Require Import lattice monoid prop rel.

#[local] Open Scope itree_scope.

(* Universe conflict when trying to include CTree.Eq and ITree.Events.FailFacts *)
(*
#[local] Unset Universe Checking.
From CTree Require Import CTree Eq.
*)


Section transaction_sim.

Context {E F : Type -> Type} {Si Sm : Type}.

Context (i : E ~> stateT Sm (itree void1)).
(* i is the specification handler for shared state events *)

Context (h : transactionE E ~> itree F).
(* h takes transactions with state events E and translates them into events F
   that are interleaved with other transactions. *)

Context (g : F ~> stateT Si (itree void1)).
(* g translates F events into operations on the implementation state. *)

Context (HS : Si -> Sm -> Prop).
(* relation between implementation and model states. *)

Variant transaction_event :=
| TransEvDone (s : Si)
| TransEvRet {R} (r : R)
| TransEvStep
| TransEvNew {R} (t : itree E (option R))
.

Variant transaction_impl :=
| TransImpl {R} (t : itree F (option R)).

Variant trans_impl_move : transaction_event -> (Si * list transaction_impl) -> (Si * list transaction_impl) -> Prop :=
| TransMoveDone (s : Si) :
    trans_impl_move (TransEvDone s) (s, []) (s, [])
| TransMoveRet {R} (r : R) (t : itree F (option R)) s ts1 ts2 :
    t ≅ Ret (Some r) ->
    trans_impl_move (TransEvRet r) (s, ts1 ++ [TransImpl t] ++ ts2) (s, ts1 ++ ts2)
| TransMoveAbort {R} (t : itree F (option R)) s ts1 ts2 :
    t ≅ Ret None ->
    trans_impl_move TransEvStep (s, ts1 ++ [TransImpl t] ++ ts2) (s, ts1 ++ ts2)
| TransMoveStep {R} (t t' : itree F (option R)) s ts1 ts2 :
    t ≅ Tau t' ->
    trans_impl_move TransEvStep (s, ts1 ++ [TransImpl t] ++ ts2) (s, ts1 ++ [TransImpl t'] ++ ts2)
| TransMoveVis {R T} (t : itree F (option R)) (r : T) (e : F T) (k : T -> itree F (option R)) s s' ts1 ts2 :
    t ≅ Vis e k ->
    g _ e s ≅ Ret (s', r) ->
    trans_impl_move TransEvStep (s, ts1 ++ [TransImpl t] ++ ts2) (s', ts1 ++ [TransImpl (k r)] ++ ts2)
| TransMoveNewTransaction {R} (t : itree E (option R)) (s : Si) (ts : list transaction_impl) :
    trans_impl_move (TransEvNew t) (s, ts) (s, TransImpl (h _ (Transaction t)) :: ts)
.

Variant transaction_state : Type :=
| Pending {R} (p : itree E (option R))
| Committed {R} (r : R).

Inductive trans_move : (Sm * list transaction_state) -> (Sm * list transaction_state) -> Prop :=
| CommitTransaction {R} (t : itree E (option R)) (r : R) (s1 s2 : Sm) (ts1 ts2 : list transaction_state) :
    interp_state i t s1 ≈ Ret (s2, Some r) ->
    trans_move (s1, ts1 ++ [Pending t] ++ ts2) (s2, ts1 ++ [Committed r] ++ ts2)
| AbortTransaction (s : Sm) (t : transaction_state) (ts1 ts2 : list transaction_state) :
    trans_move (s, ts1 ++ [t] ++ ts2) (s, ts1 ++ ts2).

Variant trans_response (sim : (Sm * list transaction_state) -> Prop) : transaction_event -> (Sm * list transaction_state) -> Prop :=
| TransResDone (s1 : Si) (s2 : Sm) : HS s1 s2 -> trans_response sim (TransEvDone s1) (s2, [])
| TransResStep s ts : trans_response sim TransEvStep (s, ts)
| TransResRet {R} (r : R) (s : Sm) (ts1 ts2 : list transaction_state) : sim (s, ts1 ++ ts2) -> trans_response sim (TransEvRet r) (s, ts1 ++ [Committed r] ++ ts2).

Program Definition transactionalb : mon ((Si * list transaction_impl) -> (Sm * list transaction_state) -> Prop) :=
  {| body R s1 s2 := forall ev s1', trans_impl_move ev s1 s1' -> exists s2', trans_move ^* s2 s2' /\ trans_response (R s1') ev s2' |}.

End transaction_sim.



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

  Compute (force 178 (run_atomic_transactions (run_atomically (fib 8)))).
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
  Compute (force 100 (run_atomic_transactions (run_atomically message_passing))).
  Compute (force 200 (run_single_lock_fork (run_atomically message_passing_simpler))).
  Compute (force 200 (run_single_lock_fork (run_atomically message_passing_simple))).
  Compute (force 300 (run_single_lock_fork (run_atomically message_passing))).
  Compute (force 1000 (run_tl2_fork (run_atomically message_passing_simpler))).
  Compute (force 1000 (run_tl2_fork (run_atomically message_passing_simple))).
  Compute (force 1000 (run_tl2_fork (run_atomically message_passing))).

  (* TODO: tests with orElse *)

End example.



