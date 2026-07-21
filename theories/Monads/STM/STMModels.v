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

From RelationAlgebra Require Import lattice monoid prop rel srel.

#[local] Open Scope itree_scope.

Section transaction_sim.

Context {E F : Type -> Type} {Si Sm X : Type}.

Context (i : E ~> stateT Sm (itree G)).
(* i is the specification handler for shared state events *)

Context (h : transactionE E ~> itree F).
(* h takes transactions with state events E and translates them into events F
   that are interleaved with other transactions. *)

Context (g : F ~> stateT Si (itree H)).
(* g translates F events into operations on the implementation state. *)

Context (HS : Si -> Sm -> Prop).
(* relation between implementation and model states. *)

Variant transaction_event :=
| TransEvDone (s : Si)
| TransEvRet {R} (r : R)
| TransEvStep
| TransEvError
| TransEvNew {R} (t : itree E (option R))
.

Variant transaction_impl :=
| TI {R} (t : itree F (option R)).

Variant transaction_move : transaction_event -> hrel (Si * list transaction_impl) (Si * list transaction_impl) :=
| TransMoveDone (s : Si) :
    transaction_move (TransEvDone s) (s, []) (s, [])
| TransMoveRet {R} (r : R) (t : itree F (option R)) s ts1 ts2 :
    t ≅ Ret (Some r) ->
    transaction_move (TransEvRet r) (s, ts1 ++ [TI t] ++ ts2) (s, ts1 ++ ts2)
| TransMoveAbort {R} (t : itree F (option R)) s ts1 ts2 :
    t ≅ Ret None ->
    transaction_move TransEvStep (s, ts1 ++ [TI t] ++ ts2) (s, ts1 ++ ts2)
| TransMoveStep {R} (t t' : itree F (option R)) s ts1 ts2 :
    t ≅ Tau t' ->
    transaction_move TransEvStep (s, ts1 ++ [TI t] ++ ts2) (s, ts1 ++ [TI t'] ++ ts2)
| TransMoveVis {R T} (t : itree F (option R)) (r : T) (e : F T) (k : T -> itree F (option R)) s s' ts1 ts2 :
    t ≅ Vis e k ->
    g _ e s ≈ Ret (s', r) ->
    transaction_move TransEvStep (s, ts1 ++ [TI t] ++ ts2) (s', ts1 ++ [TI (k r)] ++ ts2)
| TransMoveVis {R T} (t : itree F (option R)) (r : T) (e : F T) (k : T -> itree F (option R)) s s' ts1 ts2 :
    t ≅ Vis e k ->
    g _ e s ≈ Vis e' k' ->
    transaction_move TransEvError (s, ts1 ++ [TI t] ++ ts2) (s', ts1 ++ [TI (k r)] ++ ts2)
| TransMoveNewTransaction {R} (t : itree E (option R)) (s : Si) (ts : list transaction_impl) :
    transaction_move (TransEvNew t) (s, ts) (s, TI (h _ (Transaction t)) :: ts)
.

Variant transaction_state : Type :=
| Pending {R} (p : itree E (option R))
| Committed {R} (r : R).

Inductive trans_move : hrel (Sm * list transaction_state) (Sm * list transaction_state) :=
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
  {| body R s1 s2 := forall ev s1', transaction_move ev s1 s1' -> exists s2', trans_move ^* s2 s2' /\ trans_response (R s1') ev s2' |}.
Next Obligation.
  apply H1 in H2 as [s2' [Hmoves Hresponse]].
  exists s2'.
  split; [assumption|].
  destruct Hresponse; constructor; auto.
Defined.

End transaction_sim.

