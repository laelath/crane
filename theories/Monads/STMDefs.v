(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared STM effect definitions (flavor-independent).

   Contains the effect inductives ([tvarE], [stmVecE], [stmControlE]),
   composed effect ([stmE]), axioms, and smart constructors that are
   identical across library flavors. Flavor files ([STM.v], [STMBDE.v])
   re-export this module and add flavor-specific C++ extraction mappings.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Extraction.
From Crane Require Import Monads.ITree Monads.IODefs External.VectorDefs.

From ITree Require Import Basics.

From Stdlib Require Import List.
Import ListNotations.

Open Scope itree_scope.

Axiom TVar : Type -> Type.
Axiom tvar_eqb : forall {A}, TVar A -> TVar A -> bool.
Axiom tvar_eqb_eq : forall {A} (t1 t2 : TVar A), t1 = t2 <-> tvar_eqb t1 t2 = true.

Inductive tvarE : Type -> Type :=
| NewTVar : forall {A}, A -> tvarE (TVar A)
| ReadTVar : forall {A}, TVar A -> tvarE A
| WriteTVar : forall {A}, TVar A -> A -> tvarE unit
| TVarEq : forall {A B} (t1 : TVar A) (t2 : TVar B),
    tvarE ({existT TVar A t1 = existT TVar B t2} + {existT TVar A t1 <> existT TVar B t2}).

Inductive stmControlE : Type -> Type :=
| Retry : stmControlE void.

Definition retry {E} `{stmControlE -< E} {A} : itree E A :=
  trigger Retry >>= fun (x : void) => match x with end.

Crane Extract Inductive stmControlE => ""
  [ "stm::retry<%t0>()" ].

Definition stmE := tvarE +' stmControlE.
Crane Extract Skip stmE.

(* Need to decide how to model parallelism,
    could be implicitly through holding onto a vector of scheduled ctrees and at each step choosing one to step.
      This requires an explicit "commit the values of all these tvars as one action" event
    or could be done with explicit yields, trusting the specification to not miss observable intermediate states (and sources of non-termination).
      this allows the implementation to sequence writes of single tvars
    I am for now electing to use explicit yielding.
 *)
(* start with an empty log, and then perform log operations when intercepting tvarE events *)

Variant atomicE : Type -> Type :=
| BeginAtomic : atomicE unit
| EndAtomic : atomicE unit.

Variant transactionE : Type -> Type :=
| BeginTransaction : transactionE unit
| CommitTransaction : transactionE unit
| AbortTransaction : transactionE unit.

Variant TVarEntry : Type := | TVarEnt {A} (t : TVar A) (v1 v2 : A).
Definition tvar_log : Type := list TVarEntry.

Definition read_tvar_log {E} `{tvarE -< E} {A} (t : TVar A) : tvar_log -> itree E (tvar_log * A) :=
  fix _read_tvar_log l :=
    match l with
    | [] => v <- trigger (ReadTVar t) ;; Ret ([TVarEnt t v v], v)
    | (TVarEnt t' v1 v2 :: l') => 
        same_tvar <- trigger (TVarEq t' t) ;;
        match same_tvar with
        | left p =>
            match p in (_ = s0) return (itree E (tvar_log * projT1 s0)) with
            | eq_refl => Ret (l, v2)
            end
        | right _ =>
            '(l'', v) <- _read_tvar_log l' ;;
            Ret (TVarEnt t' v1 v2 :: l'', v)
        end
    end.

Definition write_tvar_log {E} `{tvarE -< E} {A} (t : TVar A) (v : A) : tvar_log -> itree E tvar_log :=
  fix _write_tvar_log l :=
    match l with
    | [] => v' <- trigger (ReadTVar t) ;; Ret (TVarEnt t v' v :: l)
    | (TVarEnt t' v1 v2 :: l') => 
        same_tvar <- trigger (TVarEq t t') ;;
        match same_tvar with 
        | left p =>
            Ret (TVarEnt t' v1 (match p in (_ = s0) return (projT1 s0) with eq_refl => v end) :: l')
        | right _ =>
            l'' <- _write_tvar_log l' ;;
            Ret (TVarEnt t' v1 v2 :: l'')
        end
    end.

(*
Fixpoint verify_log {E} `{tvarE -< E} (l : tvar_log) : itree E bool :=
  match l with
  | [] => Ret true
  | (TVarEnt t v1 _ :: l') =>
    v1' <- trigger (ReadTVar t) ;;
    if eqb v1 v1'
    then verify_log l'
    else Ret false
  end.
*)

Fixpoint commit_log {E} `{tvarE -< E} (l : tvar_log) : itree E unit :=
  match l with
  | [] => Ret tt
  | (TVarEnt t _ v2 :: l') =>
    trigger (WriteTVar t v2) ;;
    commit_log l'
  end.

Definition atomically {E} `{tvarE -< E} `{atomicE -< E} {A} (t0 : itree stmE A) : itree E A :=
  trigger BeginAtomic ;;
  (cofix _atomic l t :=
    match observe t with
    | RetF a =>
        commit_log l ;;
        trigger EndAtomic ;;
        Ret a
    | TauF t => Tau (_atomic l t)
    | VisF (inr1 Retry) _ =>
        (* TODO: stall until a write to one of the TVars? (would require directly denoting into a state monad of ctrees) *)
        Vis (subevent _ EndAtomic) (fun _ => trigger BeginAtomic ;; _atomic [] t0)
    | VisF (inl1 e) k =>
        match e in (tvarE T) return ((T -> itree stmE A) -> itree E A) with
        | NewTVar v => fun k => Vis (subevent _ (NewTVar v)) (fun t => _atomic l (k t))
        | ReadTVar t => fun k => '(l', v) <- read_tvar_log t l ;; Tau (_atomic l' (k v))
        | WriteTVar t v => fun k => l' <- write_tvar_log t v l ;; Tau (_atomic l (k tt))
        | TVarEq t1 t2 => fun k => Vis (subevent _ (TVarEq t1 t2)) (fun x => _atomic l (k x))
        end k
    end) [] t0.

Definition orElse {A} (t1 t2 : itree stmE A) : itree stmE A :=
  (cofix _orElse l t :=
    match observe t with
    | RetF a =>
        commit_log l ;;
        Ret a
    | TauF t => Tau (_orElse l t)
    | VisF (inr1 Retry) _ => t2
    | VisF (inl1 e) k =>
        match e in (tvarE T) return ((T -> itree stmE A) -> itree stmE A) with
        | NewTVar v => fun k => Vis (subevent _ (NewTVar v)) (fun t => _orElse l (k t))
        | ReadTVar t => fun k => '(l', v) <- read_tvar_log t l ;; Tau (_orElse l' (k v))
        | WriteTVar t v => fun k => l' <- write_tvar_log t v l ;; Tau (_orElse l (k tt))
        | TVarEq t1 t2 => fun k => Vis (subevent _ (TVarEq t1 t2)) (fun x => _orElse l (k x))
        end k
    end) [] t1.

Definition atomically_trans {E} `{tvarE -< E} `{transactionE -< E} {A} (t0 : itree (transactionE +' stmE) A) : itree E A :=
  trigger BeginTransaction ;;
  (cofix _atomic t :=
    match observe t with
    | RetF a =>
        trigger CommitTransaction ;;
        Ret a
    | TauF t => Tau (_atomic t)
    | VisF (inl1 e) k => Vis (subevent _ e) (fun x => _atomic (k x))
    | VisF (inr1 (inr1 Retry)) _ =>
        (* abort a transaction, and then start a new one.
           should tell the scheduler to put this back into the thread pool
        *)
        Vis (subevent _ AbortTransaction)
            (fun _ => trigger (BeginTransaction) ;; _atomic t0)
    | VisF (inr1 (inl1 e)) k => Vis (subevent _ e) (fun x => _atomic (k x))
    end) t0.

Definition orElse_trans {E} `{tvarE -< E} `{transactionE -< E} {A} (t1 t2 : itree (transactionE +' stmE) A) : itree (transactionE +' stmE) A :=
  trigger BeginTransaction ;;
  (cofix _orElse t :=
    match observe t with
    | RetF a =>
        trigger CommitTransaction ;;
        Ret a
    | TauF t => Tau (_orElse t)
    | VisF (inl1 e) k => Vis (subevent _ e) (fun x => _orElse (k x))
    | VisF (inr1 (inr1 Retry)) _ => trigger AbortTransaction ;; t2
    | VisF (inr1 (inl1 e)) k => Vis (subevent _ e) (fun x => _orElse (k x))
    end) t1.

Definition newTVar {E} `{tvarE -< E} {A} (a : A) : itree E (TVar A) := embed (NewTVar a).
Definition readTVar {E} `{tvarE -< E} {A} (v : TVar A) : itree E A := embed (ReadTVar v).
Definition writeTVar {E} `{tvarE -< E} {A} (v : TVar A) (a : A) : itree E unit := embed (WriteTVar v a).

Crane Extract Inlined Constant atomically => "stm::atomically([&] { return %a0; })".
Crane Extract Inlined Constant orElse => "stm::orElse<%t0>(%a0, %a1)".
Crane Extract Inlined Constant retry => "stm::retry<%t0>()".
Crane Extract Inlined Constant newTVar => "stm::newTVar(%a0)".

Definition check (b : bool) : itree stmE unit :=
  if b then Ret tt else retry.

Definition modifyTVar {A : Type} (a : TVar A) (f : A -> A) : itree stmE unit :=
  val <- readTVar a ;;
  writeTVar a (f val) ;;
  Ret tt.
