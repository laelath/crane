
From Corelib Require Import PrimString.
From Crane.Monads Require Import ITree STMDefs STM.TransactionDefs STM.ForkDefs.
From Crane.Utils Require Import HMap HAList Mergesort.

From Stdlib Require Import Arith.PeanoNat Bool.Bool Classes.EquivDec List.

Import ListNotations.

From ExtLib Require Import Data.List Structures.Reducible.

From ITree Require Import Basics.Basics Basics.CategoryOps Events.State Events.FailFacts.

Import Basics.Monads.


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



Definition h_tvars_tl2 {K} (V : K -> Type) {E} `{tl2E V -< E} `{errorE -< E}:
  tvarE V ~> itree E :=
  fun _ e =>
    match e with
    | NewTVar k v => trigger (NewTVarTL2 k v)
    | ReadTVar x =>
        '(v, _, _) <- trigger (ReadTVarTL2 x) ;;
        Ret v
    | WriteTVar x v => error "h_tvars_tl2 write to a tvar outside a transaction"
    end.

Definition h_trigger {E F} `{E -< F}: Handler E F :=
  fun _ e => trigger e.

Definition run_tl2_fork {K} `{EqDec K eq} {V : K -> Type}
  (t1 : itree (transactionE (stmE V) +' forkE) unit)
  : itree errorE (nat * halist (pkey K nat) (fun p => (V (fst p) * nat * bool)%type) * unit) :=
  let t2 : itree (atomicE void1 +' forkE +' tl2E V +' errorE) unit :=
    interp (case_ tl2 h_trigger) t1 in
  let t3 : itree (tl2E V +' errorE) unit := schedule_rr [t2] in
  let t4 : stateT _ (itree errorE) _ :=
    interp (case_ (h_tl2 _) pure_state) t3 in
  t4 (0, HMap.empty).
