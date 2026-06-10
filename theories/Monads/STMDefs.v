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

From ITree Require Import
  Basics.Basics
  Basics.CategoryOps
  Basics.CategoryKleisli
  Core.Subevent
  Events.FailFacts
  Events.State
  Indexed.Function
  Indexed.Sum
  Interp.Interp.



Import Basics.Monads.

From ExtLib Require Import Data.List Structures.Monad Structures.Reducible.

From Stdlib Require Import List Classes.EquivDec Arith.PeanoNat Bool.Bool.

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






Definition h_stm_write_log {K} {V : K -> Type} {M} `{HMap (pkey K nat) (pkey_type V) M} {E} `{tvarE V -< E}:
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
        let m : stateT (halist (pkey K nat) (pkey_type V)) (failT (itree (tvarE V))) _ :=
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
  (cofix _orElse (m : halist (pkey K nat) (pkey_type V)) t :=
    match observe t with
    | RetF a =>
        commit_log V m ;;
        Ret a
    | TauF t => Tau (_orElse m t)
    | VisF (inr1 e) k => '(x, m) <- handle_tvar_log m e ;; Tau (_orElse m (k x))
    | VisF (inl1 Retry) _ => t2
    end) HMap.empty t1.



Variant lockE : Type -> Type :=
| TryLock : lockE bool
| Unlock : lockE unit.

Definition spinlock {E} `{lockE -< E} : itree E unit :=
  ITree.iter (fun _ => b <- trigger TryLock ;; if (b : bool) then Ret (inr tt) else Ret (inl tt)) tt.

Definition single_global_lock {K} {V : K -> Type} {M}
  `{HMap (pkey K nat) (pkey_type V) M} {E} `{lockE -< E}:
  transactionE (stmE V) ~> itree E.
Abort.



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
Definition spinlockTVar {K} {V : K -> Type} {E} `{tl2E V -< E} {A} (x : TVar V A) : itree E unit :=
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

From Crane Require Mergesort.

Definition toList {M A} `{Foldable M A} : M -> list A := fold cons [].

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
            let locks := Mergesort.sort (fun x y => Nat.leb (snd (projT1 x)) (snd (projT1 y))) (toList m_w) in
            fold (fun '(existT _ (k, n) _) (acc : itree E unit) =>
                    spinlockTVar (mk_tvar V n k) ;; acc)
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



Variant forkE : Type -> Type :=
| Fork : forkE bool.

Definition fork {E} `{forkE -< E} (t1 t2 : itree E unit) : itree E unit :=
  b <- trigger Fork ;;
  if (b : bool) then t1 else t2.

Inductive parE E : Type -> Type :=
| Par : forall {A B} (t1 : itree (parE E +' E) A) (t2 : itree (parE E +' E) B), parE E (A * B).

Definition par {E F} `{parE F -< E} {A B} (t1 : itree (parE F +' F) A) (t2 : itree (parE F +' F) B) : itree E (A * B) :=
  trigger (Par _ t1 t2).

(* Scheduler implementations should be such that 0 getting chosen infinitely often will ensure that every thread gets scheduled *)
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

Inductive par_tree E R :=
| Split {A B} (b : bool) (t1 : par_tree E A) (t2 : par_tree E B) (k : A * B -> itree (parE E +' E) R) : par_tree E R
| LeftDone {A B} (a : A) (t2 : par_tree E B) (k : A * B -> itree (parE E +' E) R) : par_tree E R
| RightDone {A B} (t1 : par_tree E A) (b : B) (k : A * B -> itree (parE E +' E) R) : par_tree E R
| Leaf (t : itree (parE E +' E) R) : par_tree E R.

Inductive par_tree_ctx E R : Type -> Type :=
| MT : par_tree_ctx E R R
| SplitR {A B T} (b : bool) (t1 : par_tree E A) (k : A * B -> itree (parE E +' E) T) (pk : par_tree_ctx E R T) : par_tree_ctx E R B
| SplitL {A B T} (b : bool) (t2 : par_tree E B) (k : A * B -> itree (parE E +' E) T) (pk : par_tree_ctx E R T) : par_tree_ctx E R A
| LeftDoneCtx {A B T} (a : A) (k : A * B -> itree (parE E +' E) T) (pk : par_tree_ctx E R T) : par_tree_ctx E R B
| RightDoneCtx {A B T} (b : B) (k : A * B -> itree (parE E +' E) T) (pk : par_tree_ctx E R T) : par_tree_ctx E R A.



Fixpoint plug_par_tree_ctx {E R T} (pk : par_tree_ctx E R T) (pt : par_tree E T) : par_tree E R :=
  match pk, pt with
  | MT _ _, pt => pt
  | SplitR _ _ b t1 k pk, pt => plug_par_tree_ctx pk (Split _ _ b t1 pt k)
  | SplitL _ _ b t2 k pk, pt => plug_par_tree_ctx pk (Split _ _ b pt t2 k)
  | LeftDoneCtx _ _ a k pk, pt => plug_par_tree_ctx pk (LeftDone _ _ a pt k)
  | RightDoneCtx _ _ b k pk, pt => plug_par_tree_ctx pk (RightDone _ _ pt b k)
  end.



(* needs to randomly select a leaf from the par tree, then observe it and put it back *)
CoFixpoint schedule_par {E R} (pt : par_tree E R) : itree (scheduleE +' E) R :=
  let fix find_leaf {T} (pt : par_tree E T) (pk : par_tree_ctx E R T)
    : itree (scheduleE +' E) (sigT (fun T => (par_tree_ctx E R T * itree (parE E +' E) T)%type)) :=
    match pt with
    | Split _ _ b t1 t2 k =>
        Vis (inl1 (Schedule 2))
            (fun (n : {m : nat | m < 2}) =>
              let '(exist _ n _) := n in
              (* use the boolean to ensure that both branches get scheduled for rr scheduler *)
              if xorb (n =? 0) b
              then find_leaf t1 (SplitL _ _ true t2 k pk)
              else find_leaf t2 (SplitR _ _ false t1 k pk))
    | LeftDone _ _ a t2 k => find_leaf t2 (LeftDoneCtx _ _ a k pk)
    | RightDone _ _ t1 b k => find_leaf t1 (RightDoneCtx _ _ b k pk)
    | Leaf _ _ t => Ret (existT _ _ (pk, t))
    end in
  '(existT _ _ (pk, t)) <- find_leaf pt (MT _ _) ;;
  match observe t with
  | RetF v =>
      match pk, v with
      | MT _ _, a => Ret a
      | SplitR _ _ _ t1 k pk, b => Tau (schedule_par (plug_par_tree_ctx pk (RightDone _ _ t1 b k)))
      | SplitL _ _ _ t2 k pk, a => Tau (schedule_par (plug_par_tree_ctx pk (LeftDone _ _ a t2 k)))
      | LeftDoneCtx _ _ a k pk, b => Tau (schedule_par (plug_par_tree_ctx pk (Leaf _ _ (k (a, b)))))
      | RightDoneCtx _ _ b k pk, a => Tau (schedule_par (plug_par_tree_ctx pk (Leaf _ _ (k (a, b)))))
      end
  | TauF t => Tau (schedule_par (plug_par_tree_ctx pk (Leaf _ _ t)))
  | VisF (inl1 e) k =>
      match e, k with
      | Par _ t1 t2, k => Tau (schedule_par (plug_par_tree_ctx pk (Split _ _ false (Leaf _ _ t1) (Leaf _ _ t2) k)))
      end
  | VisF (inr1 e) k => Vis (inr1 e) (fun x => schedule_par (plug_par_tree_ctx pk (Leaf _ _ (k x))))
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

Definition schedule_par_rr {E R} (pt : par_tree E R) : itree E R :=
  interp (case_ h_rr (id_ _)) (schedule_par pt).

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
    let s : stateT _ _ _ := interp (handle_tvars _ _) (schedule_rr [t2]) in
    s HMap.empty.



  Definition run_tl2 {K} `{EqDec K eq} {V : K -> Type}
    (t1 : itree (transactionE (stmE V) +' forkE) unit)
    : itree errorE (nat * halist (pkey K nat) (fun p => (V (fst p) * nat * bool)%type) * unit) :=
    let t2 := interp (@case_ _ IFun sum1 _ _ _ (itree (atomicE void1 +' forkE +' tl2E V +' errorE))
                             tl2 (fun _ e => trigger e))
                     t1 in
    let t3 : itree (tl2E V +' errorE) unit := schedule_rr [t2] in
    let s : stateT _ (itree errorE) _ :=
      interp (case_ (h_tl2 _) pure_state) t3 in
    s (0, HMap.empty).



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

  Definition message_passing : itree (runStmE Types_Type +' forkE) unit :=
    mv <- atomically (newTVar (Opt Nat) None) ;;
    done <- atomically (newTVar Nat 0) ;;
    fork (v1 <- atomically (takeMVar mv) ;; v2 <- atomically (takeMVar mv) ;; atomically (putMVar mv (v1 + v2)))
         (atomically (putMVar mv 3) ;; atomically (putMVar mv 4) ;; atomically (r <- takeMVar mv ;; writeTVar done r)).

  Definition message_passing_simple : itree (runStmE Types_Type +' forkE) unit :=
    mv <- atomically (newTVar (Opt Nat) None) ;;
    done <- atomically (newTVar Nat 0) ;;
    fork (v1 <- atomically (takeMVar mv) ;; atomically (putMVar mv (v1 * v1)))
         (atomically (putMVar mv 3) ;; atomically (r <- takeMVar mv ;; writeTVar done r)).

  Definition message_passing_simpler : itree (runStmE Types_Type +' forkE) unit :=
    mv <- atomically (newTVar (Opt Nat) None) ;;
    done <- atomically (newTVar Nat 0) ;;
    fork (v1 <- atomically (takeMVar mv) ;; atomically (writeTVar done (v1 * v1)))
         (atomically (putMVar mv 3)).

  Compute (force 100 (run_atomic_transactions (run_atomically message_passing))).
  Compute (force 100 (run_atomic_transactions (run_atomically message_passing_simple))).
  Compute (force 1000 (run_tl2 (run_atomically message_passing_simple))).
  Compute (force 1000 (run_tl2 (run_atomically message_passing_simpler))).
  Compute (force 1000 (run_tl2 (run_atomically message_passing))).

  (* TODO: tests with orElse *)

End example.



Crane Extract Inlined Constant atomically => "stm::atomically([&] { return %a0; })".
Crane Extract Inlined Constant orElse => "stm::orElse<%t0>(%a0, %a1)".
Crane Extract Inlined Constant retry => "stm::retry<%t0>()".
Crane Extract Inlined Constant newTVar => "stm::newTVar(%a1)".
