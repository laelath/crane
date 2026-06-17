From Corelib Require Import PrimString.
From Crane Require Import Monads.ITree Monads.STMDefs Monads.STM.ForkDefs.

From Stdlib Require Import Arith.PeanoNat Bool.Bool Classes.EquivDec List.

Import ListNotations.

From ExtLib Require Import Data.List Structures.Reducible.

From ITree Require Import Basics.Basics Basics.CategoryOps Events.State Events.FailFacts.

Import Basics.Monads.

From Crane.Utils Require Import HMap HAList Mergesort.

Definition pkey (K J : Type) := (K * J)%type.
Definition pkey_type {K J} (V : K -> Type) (pk : pkey K J) := V (fst pk).

Definition commit_log {K} (V : K -> Type) {M} `{Foldable M (sigT (pkey_type V))} {E} `{H : tvarE V -< E} : M -> itree E unit :=
  fold (fun '(existT _ (k, n) v) acc => Vis (subevent (H := H) _ (WriteTVar (mk_tvar V n k) v)) (fun _ => acc)) (Ret tt).

Definition handle_tvar_log {K} {V : K -> Type} {M} `{HMap (pkey K nat) (pkey_type V) M} {E} `{H : tvarE V -< E}
  (m : M) : forall {A}, tvarE V A -> itree E (A * M) :=
  fun _ t =>
    match t with
    | NewTVar k v => Vis (subevent (H := H) _ (NewTVar k v)) (fun tv => Ret (tv, m))
    | ReadTVar tv =>
        (let '(mk_tvar _ n k) in TVar _ T := tv return TVar V T -> itree E (T * M) in
          match lookup (k, n) m with
          | Some v => fun _ => Ret (v, m)
          | None => fun tv => Vis (subevent (H := H) _ (ReadTVar tv)) (fun v => Ret (v, m))
          end) tv
    | WriteTVar (mk_tvar _ n k) v => Ret (tt, add (k, n) v m)
    end.



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



Definition h_stm_write_log {K} {V : K -> Type} {M} `{HMap (pkey K nat) (pkey_type V) M} {E} `{tvarE V -< E}:
  stmE V ~> stateT M (failT (itree E)) :=
  fun _ e m =>
    match e with
    | inl1 Retry => Ret None
    | inr1 e =>
        '(a, m) <- handle_tvar_log m e ;;
        Ret (Some (m, a))
    end.

(* TODO: generalize to any HMap *)
(* Implements transactions by executing them atomically (blocks all other threads from executing until it is finished) *)
Definition atomic_transactions {K} {V : K -> Type} `{EqDec K eq}: transactionE (stmE V) ~> atomicE (tvarE V) :=
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




Variant tl2E {K} (V : K -> Type) : Type -> Type :=
| GetVersionClock : tl2E V nat
| IncVersionClock : tl2E V nat
| NewTVarTL2 : forall (k : K), V k -> tl2E V (TVar V (V k))
| ReadTVarTL2 : forall {A}, TVar V A -> tl2E V (A * nat * bool)
| WriteTVarTL2 : forall {A}, TVar V A -> A -> nat -> bool -> tl2E V unit
| TryLockTVar : forall {A}, TVar V A -> tl2E V bool
| UnlockTVar : forall {A}, TVar V A -> tl2E V unit.

Arguments GetVersionClock {K} {V}.
Arguments IncVersionClock {K} {V}.
Arguments NewTVarTL2 {K} {V} (_ _).
Arguments ReadTVarTL2 {K} {V} {A} (_).
Arguments WriteTVarTL2 {K} {V} {A} (_ _ _ _).
Arguments TryLockTVar {K} {V} {A} (_).
Arguments UnlockTVar {K} {V} {A} (_).



(* a blocking spinlock *)
Definition spinlock_tvar {K} {V : K -> Type} {E} `{tl2E V -< E} {A} (x : TVar V A) : itree E unit :=
  ITree.iter (fun _ => b <- trigger (TryLockTVar x) ;; if (b : bool) then Ret (inr tt) else Ret (inl tt)) tt.



Variant errorE : Type -> Type :=
| Error (msg : string) : errorE void.

Definition error {E A} `{errorE -< E} (msg : string) : itree E A :=
  Vis (subevent _ (Error msg)) (fun (x : void) => match x with end).



Definition handle_tvar_log_tl2 {K} {V : K -> Type} {M} `{HMap (pkey K nat) (pkey_type V) M} {E} `{H : tl2E V -< E}
  (rv : nat) : stmE V ~> stateT (list (pkey K nat) * M) (failT (itree E)) :=
  fun _ t '(s_r, m_w) =>
    match t with
    | inl1 Retry => Ret None
    | inr1 e =>
      match e with
      | NewTVar k v => Vis (subevent (H := H) _ (NewTVarTL2 k v)) (fun tv => Ret (Some ((s_r, m_w), tv)))
      | ReadTVar tv =>
          (let '(mk_tvar _ n k) in TVar _ T := tv return TVar V T -> itree E (option ((list (pkey K nat) * M) * T)) in
            match lookup (k, n) m_w with
            | Some v => fun _ => Ret (Some ((s_r, m_w), v))
            | None => fun tv =>
                '(v, ver, l) <- Vis (subevent (H := H) _ (ReadTVarTL2 tv)) (fun x => Ret x);;
                if l || (rv <? ver)
                then Ret None
                else Ret (Some (((k, n) :: s_r, m_w), v))
            end) tv
      | WriteTVar (mk_tvar _ n k) v => Ret (Some ((s_r, add (k, n) v m_w), tt))
      end
    end.

Definition write_tl2 {K} (V : K -> Type) {E} `{tl2E V -< E} (n : nat) (k : K) (v : V k) (wv : nat) (l : bool): itree E unit :=
  trigger (WriteTVarTL2 (mk_tvar V n k) v wv l).



Definition is_none {A} (o : option A) : bool := match o with None => true | Some _ => false end.

Definition to_list {M A} `{Foldable M A} : M -> list A := fold cons [].

(* Implements transactions with the Transactional Locking II algorithm *)
Definition tl2 {K} {V : K -> Type} {M}
  `{HMap (pkey K nat) (pkey_type V) M} `{Foldable M (sigT (@pkey_type K nat V))} {E} `{tl2E V -< E} `{errorE -< E}:
  transactionE (stmE V) ~> itree E :=
  fun A e =>
    match e with
    | Transaction t0 =>
        (* sample global version-clock *)
        rv <- trigger GetVersionClock ;;
        (* run through a speculative execution *)
        let m : stateT (_ * M) (failT (itree E)) _ :=
          interp (handle_tvar_log_tl2 rv) t0 in
        res <- m ([], HMap.empty) ;;
        match res with
        | None => Ret None (* transaction retried or read a failure state *)
        | Some ((s_r, m_w), a) =>
            (* lock the write-set *)
            (* sorts the locks so that we avoid deadlocks *)
            let locks := Mergesort.sort (fun x y => Nat.leb (snd (projT1 x)) (snd (projT1 y))) (to_list m_w) in
            fold (fun '(existT _ (k, n) _) (acc : itree E unit) =>
                    spinlock_tvar (mk_tvar V n k) ;; acc)
                 (Ret tt)
                 locks ;;
            (* increment the global version-clock *)
            wv <- trigger IncVersionClock ;;
            (* validate the read-set *)
            validated <- fold (fun '(k, n) t =>
                                '(_, ver, l) <- trigger (ReadTVarTL2 (mk_tvar V n k)) ;;
                                (* check that if the lock is held, it is because we locked it and that it hasn't been written to *)
                                if (l && is_none (lookup (k, n) m_w)) || (rv <? ver)
                                then Ret false
                                else t)
                              (Ret true) s_r ;;
            if negb validated
            then
              (* release the write locks *)
              fold (fun '(existT _ (k, n) _) acc => trigger (UnlockTVar (mk_tvar V n k)) ;; acc)
                    (Ret tt) m_w ;;
              Ret None
            else
              (* commit and release the locks *)
              fold (fun '(existT _ p v) t =>
                            (* write also sets the lock bit to unlocked *)
                            trigger (WriteTVarTL2 (mk_tvar V (snd p) (fst p)) v wv false) ;;
                            t)
                  (Ret tt) m_w ;;
              Ret (Some a)
        end
    end.



Definition h_tl2 {E} `{errorE -< E} {K} {V : K -> Type} M
  `{HMap (pkey K nat) (fun p => (V (fst p) * nat * bool)%type) M}
  `{Foldable M (sigT (fun p : K * nat => (V (fst p) * nat * bool)%type))}:
  tl2E V ~> stateT (nat * M) (itree E) :=
  fun _ e '(vc, m) =>
    match e with
    | GetVersionClock => Ret (vc, m, vc)
    | IncVersionClock => Ret (S vc, m, S vc)
    | NewTVarTL2 k v =>
        let n := S (fold (fun '(existT _ (_, n) _) acc => max n acc) 0 m) in
        Ret (vc, add (k, n) (v, vc, false) m, mk_tvar V n k)
    | ReadTVarTL2 x =>
        let '(mk_tvar _ n k) := x in
        match lookup (k, n) m with
        | Some v => Ret (vc, m, v)
        | None => error "ReadTVarTL2 lookup failed" (* error *)
        end
    | WriteTVarTL2 x v wv l =>
        (let '(mk_tvar _ n k) := x in
         fun (v : V k) => Ret (vc, add (k, n) (v, wv, l) m, tt)) v
    | TryLockTVar x =>
        let '(mk_tvar _ n k) := x in
        match lookup (k, n) m with
        | Some (v, wv, l) =>
            if (l : bool)
            then Ret (vc, m, false)
            else Ret (vc, add (k, n) (v, wv, true) m, true)
        | None => error "h_tl2 TryLockTVar lookup failed" (* error *)
        end
    | UnlockTVar (mk_tvar _ n k) =>
        match lookup (k, n) m with
        | Some (v, wv, l) =>
          Ret (vc, add (k, n) (v, wv, false) m, tt)
        | None => error "h_tl2 UnlockTVar lookup failed"
        end
    end.

Definition handle_tvars {E} {K} (V : K -> Type) M
  `{HMap (pkey K nat) (pkey_type V) M} `{Foldable M (sigT (@pkey_type K nat V))}:
  tvarE V ~> stateT M (itree E) :=
  fun _ t m =>
    match t with
    | NewTVar k v =>
        let n := S (fold (fun '(existT _ (_, n) _) acc => max n acc) 0 m) in
        Ret (add (k, n) v m, mk_tvar V n k)
    | ReadTVar x =>
        let '(mk_tvar _ n k) := x in
        match lookup (k, n) m with
        | Some v => Ret (m, v)
        | None => ITree.spin (* error *)
        end
    | WriteTVar x v =>
        (let '(mk_tvar _ n k) := x in
         fun (v : V k) => Ret (add (k, n) v m, tt)) v
    end.

Definition h_tvars_tl2 {K} (V : K -> Type):
  tvarE V ~> itree (tl2E V) :=
  fun _ e =>
    match e with
    | NewTVar k v => ITree.trigger (NewTVarTL2 k v)
    | ReadTVar x =>
        '(v, _, _) <- trigger (ReadTVarTL2 x) ;;
        Ret v
    | WriteTVar x v => ITree.spin (* error *)
    end.



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



  Definition run_atomically {K} {V : K -> Type} {E A} (t0 : itree (runStmE V +' E) A):
    itree (transactionE (stmE V) +' E) A :=
    interp (bimap h_atomically (id_ _)) t0.

  Definition run_atomic_transactions {K} `{EqDec K eq} {V : K -> Type}
    (t1 : itree (transactionE (stmE V) +' forkE) unit):
    itree void1 (halist (pkey K nat) (pkey_type V) * unit) :=
    let t2 : itree (atomicE (tvarE V) +' forkE +' tvarE V) unit := translate (bimap atomic_transactions subevent) t1 in
    let t3 : stateT _ _ _ := interp (handle_tvars _ _) (schedule_rr [t2]) in
    t3 HMap.empty.



  Definition h_trigger {E F} `{E -< F}: Handler E F :=
    fun _ e => trigger e.

  Definition run_single_lock {K} `{EqDec K eq} {V : K -> Type}
    (t1 : itree (transactionE (stmE V) +' forkE) unit):
    itree void1 (halist (pkey K nat) (pkey_type V) * (bool * unit)) :=
    let t2 : itree (atomicE void1 +' forkE +' lockE +' tvarE V) unit :=
      interp (case_ single_global_lock h_trigger) t1 in
    let t3 := schedule_rr [t2] in
    let t4 : stateT bool (itree (tvarE V)) unit := interp (case_ h_lock pure_state) t3 in
    let t5 : stateT _ (itree void1) _ := interp (handle_tvars _ _) (t4 false) in
    t5 HMap.empty.



  Definition run_tl2 {K} `{EqDec K eq} {V : K -> Type}
    (t1 : itree (transactionE (stmE V) +' forkE) unit)
    : itree errorE (nat * halist (pkey K nat) (fun p => (V (fst p) * nat * bool)%type) * unit) :=
    let t2 : itree (atomicE void1 +' forkE +' tl2E V +' errorE) unit :=
      interp (case_ tl2 h_trigger) t1 in
    let t3 : itree (tl2E V +' errorE) unit := schedule_rr [t2] in
    let t4 : stateT _ (itree errorE) _ :=
      interp (case_ (h_tl2 _) pure_state) t3 in
    t4 (0, HMap.empty).



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
  Compute (force 1000 (run_single_lock (run_atomically (fib 8)))).
  Compute (force 1874 (run_tl2 (run_atomically (fib 8)))).

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

  Compute (force 1000 (run_tl2 (run_atomically read_test))).
  Compute (force 1000 (run_tl2 (run_atomically write_test))).
  Compute (force 1000 (run_tl2 (run_atomically inc_test))).

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
  Compute (force 200 (run_single_lock (run_atomically message_passing_simpler))).
  Compute (force 200 (run_single_lock (run_atomically message_passing_simple))).
  Compute (force 300 (run_single_lock (run_atomically message_passing))).
  Compute (force 1000 (run_tl2 (run_atomically message_passing_simpler))).
  Compute (force 1000 (run_tl2 (run_atomically message_passing_simple))).
  Compute (force 1000 (run_tl2 (run_atomically message_passing))).

  (* TODO: tests with orElse *)

End example.



