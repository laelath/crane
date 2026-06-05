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
From Crane Require Import Monads.ITree Monads.IODefs External.VectorDefs Utils.HMap Utils.HAList.

From ITree Require Import Basics.Basics Basics.CategoryOps Basics.CategoryKleisli Indexed.Function Indexed.Sum Core.Subevent Interp.Interp.



Import Basics.Monads.

From ExtLib Require Import Structures.Monad Structures.Reducible.

From Stdlib Require Import List Classes.EquivDec.
Import ListNotations.

Open Scope itree_scope.

Variant TVar {K} (V : K -> Type) : Type -> Type :=
| mk_tvar : forall (n : nat) (k : K), TVar V (V k).

Definition tvar_key {K A} (V : K -> Type) (x : TVar V A) : K :=
  match x with mk_tvar _ _ k => k end.

(*
Axiom TVar : Type -> Type.
Axiom tvar_eq_dec : forall {A B} (t1 : TVar A) (t2 : TVar B),
  {existT _ _ t1 = existT _ _ t2} + {existT _ _ t1 <> existT _ _ t2}.
*)


Inductive tvarE {K : Type} (V : K -> Type) : Type -> Type :=
| NewTVar : forall (k : K), V k -> tvarE V (TVar V (V k))
| ReadTVar : forall {A}, TVar V A -> tvarE V A
| WriteTVar : forall {A}, TVar V A -> A -> tvarE V unit.

(*
| BeginTransaction : tvarE V unit
| CommitTransaction : tvarE V unit
| AbortTransaction : tvarE V unit.
*)

Arguments NewTVar {K} {V}.
Arguments ReadTVar {K} {V} {A}.
Arguments WriteTVar {K} {V} {A}.
(*
Arguments BeginTransaction {K} {V}.
Arguments CommitTransaction {K} {V}.
Arguments AbortTransaction {K} {V}.
*)

Inductive stmControlE : Type -> Type :=
| Retry : stmControlE void.

Definition retry {E} `{stmControlE -< E} {A} : itree E A :=
  trigger Retry >>= fun (x : void) => match x with end.

Crane Extract Inductive stmControlE => ""
  [ "stm::retry<%t0>()" ].

Definition stmE {K} (V : K -> Type) : Type -> Type := stmControlE +' tvarE V.
Crane Extract Skip stmE.

(* not entirely sure why this is required *)
#[global] Instance tvarE_sub_stmE {K} (V : K -> Type) : tvarE V -< stmE V := inr1.
#[global] Instance stmControlE_sub_stmE {K} (V : K -> Type) : stmControlE -< stmE V := inl1.

(* Need to decide how to model parallelism,
    could be implicitly through holding onto a vector of scheduled ctrees and at each step choosing one to step.
      This requires an explicit "commit the values of all these tvars as one action" event
    or could be done with explicit yields, trusting the specification to not miss observable intermediate states (and sources of non-termination).
      this allows the implementation to sequence writes of single tvars
    I am for now electing to use explicit yielding.
 *)
(* start with an empty log, and then perform log operations when intercepting tvarE events *)

(*
Definition atomically {E} {K} {V : K -> Type} `{tvarE V -< E} {A} (t0 : itree (stmE V) A) : itree E A :=
  trigger BeginTransaction ;;
  (cofix _atomic t :=
    match observe t with
    | RetF a =>
        trigger CommitTransaction ;;
        Ret a
    | TauF t => Tau (_atomic t)
    | VisF (inr1 e) k => Vis (subevent _ e) (fun x => _atomic (k x))
    | VisF (inl1 Retry) _ =>
        (* abort a transaction, and then start a new one.
           should tell the scheduler to put this back into the thread pool
        *)
        Vis (subevent _ AbortTransaction)
            (fun _ => trigger (BeginTransaction) ;; _atomic t0)
    end) t0.

Definition orElse {A} {K} {V : K -> Type} (t1 t2 : itree (stmE V) A) : itree (stmE V) A :=
  trigger BeginTransaction ;;
  (cofix _orElse t :=
    match observe t with
    | RetF a =>
        trigger CommitTransaction ;;
        Ret a
    | TauF t => Tau (_orElse t)
    | VisF (inr1 e) k => Vis (inr1 e) (fun x => _orElse (k x))
    | VisF (inl1 Retry) _ => trigger AbortTransaction ;; t2
    end) t1.
*)






Definition pkey (J K : Type) := (J * K)%type.
Definition pkey_type {J K} (V : K -> Type) (pk : pkey J K) := V (snd pk).
Definition nat_key := pkey nat.
Definition nat_key_type {K} (V : K -> Type) (nk : nat_key K) := V (snd nk).

Definition commit_log {K} (V : K -> Type) {M} `{Foldable M (sigT (nat_key_type V))} {E} `{H : tvarE V -< E} : M -> itree E unit :=
  fold (fun '(existT _ (n, k) v) acc => Vis (subevent (H := H) _ (WriteTVar (mk_tvar V n k) v)) (fun _ => acc)) (Ret tt).


Definition handle_tvar_log {K} {V : K -> Type} {M} `{HMap (nat_key K) (nat_key_type V) M} {E} `{H : tvarE V -< E}
  (m : M) : forall {A}, tvarE V A -> itree E (A * M) :=
  fun _ t =>
    match t with
    | NewTVar _ _ => ITree.spin (* error for now, need to figure out how to deal with these *)
    | ReadTVar tv =>
        (let '(mk_tvar _ n k) in TVar _ T := tv return TVar V T -> itree E (T * M) in
          match lookup (n, k) m with
          | Some v => fun _ => Ret (v, m)
          | None => fun tv => Vis (subevent (H := H) _ (ReadTVar tv)) (fun v => Ret (v, m))
          end) tv
    | WriteTVar (mk_tvar _ n k) v => Ret (tt, add (n, k) v m)
    end.

Variant atomicE E : Type -> Type :=
| Atomic : forall {A} (t : itree E A), atomicE E A.

Arguments Atomic {E} {A} (_).

Variant runStmE {K} (V : K -> Type) : Type -> Type :=
| Atomically : forall {A} (t : itree (stmE V) A), runStmE V A.

Arguments Atomically {K} {V} {A} (t).

Definition atomically {K} {V : K -> Type} {E} `{runStmE V -< E} {A} (t : itree (stmE V) A) : itree E A :=
  trigger (Atomically t).

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



From ITree Require Import Events.FailFacts.



Definition h_stm_write_log {K} {V : K -> Type} {M} `{HMap (nat_key K) (nat_key_type V) M} {E} `{tvarE V -< E}:
  stmE V ~> stateT M (failT (itree E)) :=
  fun _ e m =>
    match e with
    | inl1 Retry => Ret None
    | inr1 e =>
        '(a, m) <- handle_tvar_log m e ;;
        Ret (Some (m, a))
    end.

(* assumes that we can atomically execute transacitons, ** NOT (in general) TRUE ** *)
Definition atomic_transactions {K} {V : K -> Type} `{EqDec K eq}: transactionE (stmE V) ~> atomicE (tvarE V) :=
  fun _ e =>
    match e with
    | Transaction t =>
        let m : stateT (halist (pkey nat K) (pkey_type V)) (failT (itree (tvarE V))) _ :=
          interp h_stm_write_log t in
        Atomic (oma <- m [] ;;
                match oma with
                | Some (m, a) =>
                    commit_log _ m ;;
                    Ret (Some a)
                | None => Ret None
                end)
    end.

Definition orElse {A} {K} {V : K -> Type} `{EqDec K eq} (t1 t2 : itree (stmE V) A) : itree (stmE V) A :=
  (cofix _orElse (m : halist (nat_key K) (nat_key_type V)) t :=
    match observe t with
    | RetF a =>
        commit_log V m ;;
        Ret a
    | TauF t => Tau (_orElse m t)
    | VisF (inr1 e) k => '(x, m) <- handle_tvar_log m e ;; Tau (_orElse m (k x))
    | VisF (inl1 Retry) _ => t2
    end) HMap.empty t1.



Variant tl2E {K} (V : K -> Type) : Type -> Type :=
| GetVersionClock : tl2E V nat
| IncVersionClock : tl2E V nat
| NewTVarTL2 : forall (k : K), V k -> tl2E V (TVar V (V k))
| ReadTVarTL2 : forall {A}, TVar V A -> tl2E V (A * nat * bool)
| WriteTVarTL2 : forall {A}, TVar V A -> A -> nat -> tl2E V unit
| TryLockTVar : forall {A}, TVar V A -> tl2E V bool
| UnlockTVar : forall {A}, TVar V A -> tl2E V unit.

Arguments GetVersionClock {K} {V}.
Arguments IncVersionClock {K} {V}.
Arguments NewTVarTL2 {K} (V) (_ _).
Arguments ReadTVarTL2 {K} {V} {A} (_).
Arguments WriteTVarTL2 {K} {V} {A} (_ _ _).
Arguments TryLockTVar {K} {V} {A} (_).
Arguments UnlockTVar {K} {V} {A} (_).

From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From ExtLib Require Import Data.List.



Definition handle_tvar_log_tl2 {K} {V : K -> Type} {M} `{HMap (nat_key K) (nat_key_type V) M} {E} `{H : tl2E V -< E}
  (rv : nat) : stmE V ~> stateT (list (pkey nat K) * M) (failT (itree E)) :=
  fun _ t '(s_r, m_w) =>
    match t with
    | inl1 Retry => Ret None
    | inr1 e =>
      match e with
      | NewTVar _ _ => ITree.spin (* error for now, need to figure out how to deal with these *)
      | ReadTVar tv =>
          (let '(mk_tvar _ n k) in TVar _ T := tv return TVar V T -> itree E (option ((list (pkey nat K) * M) * T)) in
            match lookup (n, k) m_w with
            | Some v => fun _ => Ret (Some ((s_r, m_w), v))
            | None => fun tv =>
                '(v, ver, l) <- Vis (subevent (H := H) _ (ReadTVarTL2 tv)) (fun x => Ret x);;
                if l || (rv <? ver)
                then Ret None
                else Ret (Some (((n, k) :: s_r, m_w), v))
            end) tv
      | WriteTVar (mk_tvar _ n k) v => Ret (Some ((s_r, add (n, k) v m_w), tt))
      end
    end.

Definition write_tl2 {K} (V : K -> Type) {E} `{tl2E V -< E} (n : nat) (k : K) (v : V k) (wv : nat): itree E unit :=
  trigger (WriteTVarTL2 (mk_tvar V n k) v wv).

Definition tl2 {K} {V : K -> Type} `{EqDec K eq} {E} `{tl2E V -< E} : transactionE (stmE V) ~> itree E :=
  fun A e =>
    match e with
    | Transaction t0 =>
        (* sample global version-clock *)
        rv <- trigger GetVersionClock ;;
        (* run through a speculative execution *)
        let m : stateT (_ * halist (pkey nat K) (pkey_type V)) (failT (itree E)) _ :=
          interp (handle_tvar_log_tl2 rv) t0 in
        res <- m ([], []) ;;
        match res with
        | None => Ret None
        | Some ((s_r, m_w), a) =>
            (* lock the write-set *)
            have_locks <- fold (fun '(existT _ (n, k) _) t =>
                                  lock <- trigger (TryLockTVar (mk_tvar V n k)) ;;
                                  if (lock : bool) then t else Ret false)
                               (Ret true) m_w ;;
            if negb have_locks
            then Ret None
            else
            (* increment the global version-clock *)
            wv <- trigger IncVersionClock ;;
            (* validate the read-set *)
            validated <- fold (fun '(n, k) t =>
                                '(_, ver, l) <- trigger (ReadTVarTL2 (mk_tvar V n k)) ;;
                                if l || (rv <? ver)
                                then Ret false
                                else t)
                              (Ret true) s_r ;;
            if negb validated
            then Ret None
            else
            (* commit and release the locks *)
            fold (fun '(existT _ p v) t =>
                          trigger (WriteTVarTL2 (mk_tvar V (fst p) (snd p)) v wv) ;;
                          trigger (UnlockTVar (mk_tvar V (fst p) (snd p))) ;;
                          t)
                 (Ret tt) m_w ;;
            Ret (Some a)
        end
    end.

Definition handle_tvars {E} {K} `{EqDec K eq} (V : K -> Type) :
  tvarE V ~> stateT (halist (nat_key K) (nat_key_type V)) (itree E) :=
  fun _ t m =>
    match t with
    | NewTVar k v =>
        let n := S (fold (fun '(existT _ (n, _) _) acc => max n acc) 0 m) in
        Ret (add (n, k) v m, mk_tvar V n k)
    | ReadTVar x =>
        let '(mk_tvar _ n k) := x in
        match lookup (n, k) m with
        | Some v => Ret (m, v)
        | None => ITree.spin (* error *)
        end
    | WriteTVar x v =>
        (let '(mk_tvar _ n k) := x in
         fun (v : V k) => Ret (add (n, k) v m, tt)) v
    end.

Variant forkE : Type -> Type :=
| Fork : forkE bool.

Definition fork {E} `{forkE -< E} (t1 t2 : itree E unit) : itree E unit :=
  b <- trigger Fork ;;
  if (b : bool) then t1 else t2.

Variant scheduleE : Type -> Type :=
| Schedule (n : nat) : scheduleE {m : nat | m < n}.

Fixpoint signth {A} (l : list A) (n : {m : nat | m < length l}) : A :=
  match l, n with
  | [], exist _ m H => False_rect _ (PeanoNat.Nat.nlt_0_r m H)
  | (v :: l), exist _ m H =>
    match m with
    | 0 => fun _ => v
    | S m => fun H : S m < S (length l) => signth l (exist _ m (PeanoNat.lt_S_n _ _ H))
    end H
  end.

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

Definition h_rr {E} : scheduleE ~> itree E :=
  fun _ e =>
    match e with
    | Schedule n =>
        match n with
        | 0 => ITree.spin (* error *)
        | S m => Ret (exist _ 0 (PeanoNat.Nat.lt_0_succ m))
        end
    end.

Definition schedule_rr {E F} `{F -< E} (l : list (itree (atomicE F +' forkE +' E) unit)) : itree E unit :=
  interp (case_ h_rr (id_ _)) (schedule l).

Definition newTVar {E K V} `{tvarE V -< E} (k : K) (a : V k) : itree E (TVar V (V k)) := embed (NewTVar k a).
Definition readTVar {E K} {V : K -> Type} `{tvarE V -< E} {A} (v : TVar V A) : itree E A := embed (ReadTVar v).
Definition writeTVar {E K} {V : K -> Type} `{tvarE V -< E} {A} (v : TVar V A) (a : A) : itree E unit := embed (WriteTVar v a).

Definition check {K} {V : K -> Type} (b : bool) : itree (stmE V) unit :=
  if b then Ret tt else retry.

Definition modifyTVar {K} {V : K -> Type} {A : Type} (a : TVar V A) (f : A -> A) : itree (stmE V) unit :=
  val <- readTVar a ;;
  writeTVar a (f val) ;;
  Ret tt.

Section example.

  #[global] Instance EqDec_unit : EqDec unit eq :=
    fun x y => match x, y with tt, tt => left eq_refl end.

  Definition nats (_ : unit) : Type := nat.

  Definition fib_trans (x0 x1 : TVar nats nat): itree (stmE nats) unit :=
    v0 <- readTVar x0 ;;
    v1 <- readTVar x1 ;;
    writeTVar x0 v1 ;;
    writeTVar x1 (v0 + v1).

  Definition fib (n : nat) : itree (runStmE nats +' forkE +' tvarE nats) unit :=
    x <- newTVar tt 0 ;;
    y <- newTVar tt 1 ;;
    (fix fib_ n :=
      match n with
      | 0 => Ret tt
      | S n => fork (atomically (fib_trans x y)) (fib_ n)
      end) n.



  Definition run_atomically {K} {V : K -> Type} {E A} (t0 : itree (runStmE V +' E) A):
    itree (transactionE (stmE V) +' E) A :=
    interp (bimap h_atomically (id_ _)) t0.


  Definition run_atomic_transactions {K} `{EqDec K eq} {V : K -> Type}
    (t1 : itree (transactionE (stmE V) +' forkE +' tvarE V) unit)
    : itree void1 (halist (nat_key K) (nat_key_type V) * unit) :=
    let t2 := translate (bimap atomic_transactions (id_ (forkE +' tvarE V))) t1 in
    let s : stateT _ _ _ := interp (handle_tvars V) (schedule_rr [t2]) in
    s HMap.empty.

  Definition force {E A} (n : nat) (t : itree E A) : option A :=
    match observe (burn n t) with
    | RetF a => Some a
    | _ => None
    end.

  Definition unwrap {E A} : option A -> itree E A :=
    fun o => match o with None => ITree.spin | Some a => Ret a end.

  Compute (force 1000 (run_atomic_transactions (run_atomically (fib 8)))).

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

  Inductive Types :=
  | Nat : Types
  | Opt : Types -> Types.

  Definition decide_types (x y : Types) : {x = y} + {x <> y}.
    decide equality.
  Defined.

  #[global] Instance EqDec_Types : EqDec Types eq := decide_types.

  Fixpoint Types_Type (type : Types) : Type :=
    match type with
    | Nat => nat
    | Opt t => option (Types_Type t)
    end.

  Definition message_passing : itree (runStmE Types_Type +' forkE +' tvarE Types_Type) unit :=
    mv <- newTVar (Opt Nat) None ;;
    done <- newTVar Nat 0 ;;
    fork (v1 <- atomically (takeMVar mv) ;; v2 <- atomically (takeMVar mv) ;; atomically (putMVar mv (v1 + v2)))
         (atomically (putMVar mv 3) ;; atomically (putMVar mv 4) ;; atomically (r <- takeMVar mv ;; writeTVar done r)).

  Compute (force 100 (run_atomic_transactions (run_atomically message_passing))).

  (* TODO: tests with orElse *)

End example.



Crane Extract Inlined Constant atomically => "stm::atomically([&] { return %a0; })".
Crane Extract Inlined Constant orElse => "stm::orElse<%t0>(%a0, %a1)".
Crane Extract Inlined Constant retry => "stm::retry<%t0>()".
Crane Extract Inlined Constant newTVar => "stm::newTVar(%a1)".
