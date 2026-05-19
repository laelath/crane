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

From ExtLib Require Import Data.Monads.StateMonad.

From Stdlib Require Import List.
Import ListNotations.

Open Scope itree_scope.

Axiom TVar : Type -> Type.
Axiom tvar_eq_dec : forall {A B} (t1 : TVar A) (t2 : TVar B),
  {existT _ _ t1 = existT _ _ t2} + {existT _ _ t1 <> existT _ _ t2}.

Inductive tvarE : Type -> Type :=
| NewTVar : forall {A}, A -> tvarE (TVar A)
| ReadTVar : forall {A}, TVar A -> tvarE A
| WriteTVar : forall {A}, TVar A -> A -> tvarE unit
| BeginTransaction : tvarE unit
| CommitTransaction : tvarE unit
| AbortTransaction : tvarE unit.

Inductive stmControlE : Type -> Type :=
| Retry : stmControlE void.

Definition retry {E} `{stmControlE -< E} {A} : itree E A :=
  trigger Retry >>= fun (x : void) => match x with end.

Crane Extract Inductive stmControlE => ""
  [ "stm::retry<%t0>()" ].

Definition stmE := stmControlE +' tvarE.
Crane Extract Skip stmE.

(* Need to decide how to model parallelism,
    could be implicitly through holding onto a vector of scheduled ctrees and at each step choosing one to step.
      This requires an explicit "commit the values of all these tvars as one action" event
    or could be done with explicit yields, trusting the specification to not miss observable intermediate states (and sources of non-termination).
      this allows the implementation to sequence writes of single tvars
    I am for now electing to use explicit yielding.
 *)
(* start with an empty log, and then perform log operations when intercepting tvarE events *)

Definition atomically {E} `{tvarE -< E} {A} (t0 : itree stmE A) : itree E A :=
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

Definition orElse {A} (t1 t2 : itree stmE A) : itree stmE A :=
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


From ExtLib Require Import Structures.Reducible.

Section HMaps.

  Context (K : Type) (V : K -> Type).
  Context (map : Type).

  Class HMap : Type :=
  { empty  : map
  ; add    : forall (k : K), V k -> map -> map
  ; remove : K -> map -> map
  ; lookup : forall (k : K), map -> option (V k)
  ; union  : map -> map -> map
  }.

  Class HMapOk (M : HMap) : Type :=
  { mapsto : forall (k : K), V k -> map -> Prop
  ; mapsto_empty : forall k v, ~mapsto k v empty
  ; mapsto_lookup : forall k v m, lookup k m = Some v <-> mapsto k v m
  ; mapsto_add_eq : forall m k v, mapsto k v (add k v m)
  ; mapsto_add_neq : forall m k v k', k <> k' -> forall v', (mapsto k' v' m <-> mapsto k' v' (add k v m))
  ; mapsto_remove_eq : forall m k v, ~ mapsto k v (remove k m)
  ; mapsto_remove_neq : forall m k k', k <> k' -> forall v', (mapsto k' v' m <-> mapsto k' v' (remove k m))
  }.

  Context `{M : HMap}.

  Definition contains (k : K) (m : map) : bool :=
    match lookup k m with
    | None => false
    | Some _ => true
    end.

  Definition singleton (k : K) (v : V k) : map :=
    add k v empty.

  Context {F : Foldable map (sigT V)}.

  Definition combine (f : forall (k : K), V k -> V k -> V k) (m1 m2 : map) : map :=
    fold (fun k_v acc =>
      let '(existT _ k v) := k_v in
      match lookup k acc with
      | None => add k v acc
      | Some v' => add k (f k v v') acc
      end) m2 m1.

  Definition filter (f : forall (k : K), V k -> bool) (m : map) : map :=
    fold (fun k_v acc =>
      let '(existT _ k v) := k_v in
      if f k v
      then add k v acc
      else acc) empty m.

End HMaps.

Arguments empty {_} {_} {_} {_}.
Arguments add {K V} {map} {HMap} _ _ _.
Arguments remove {K V} {map} {HMap} _ _.
Arguments lookup {K V} {map} {HMap} _ _.
Arguments union {K V} {map} {HMap} _ _.
Arguments contains {K V} {map} {M} _ _.
Arguments singleton {K V} {map} {M} _ _.
Arguments combine {K V} {map} {M} _ _ _ _.
Arguments HMapOk {K V} {map} _.



From Stdlib Require Import Classes.EquivDec.

Section HAList.
  Context (K : Type) (V : K -> Type).

  Definition halist := list {k : K & V k}.

  Context `{Eq : EqDec K eq}.

  Definition halist_remove (k : K) (m : halist) : halist :=
    List.filter (fun k_v => negb (proj1_sig (bool_of_sumbool (projT1 k_v == k)))) m.

  Definition halist_add (k : K) (v : V k) (m : halist) : halist :=
    existT _ k v :: halist_remove k m.

  Fixpoint halist_lookup (k : K) (l : halist) : option (V k) :=
    match l with
    | [] => None
    | (existT _ k' v :: l') =>
      match k' == k with
      | left e => Some (eq_rect k' V v k e)
      | right _ => halist_lookup k l'
      end
    end.

  Section fold.
    Context {T : Type} (f : forall (k : K), V k -> T -> T).

    Fixpoint fold_halist (acc : T) (map : halist) : T :=
      match map with
      | [] => acc
      | (existT _ k v :: m) => fold_halist (f k v acc) m
      end.
  End fold.

  Definition halist_union (m1 m2 : halist) : halist :=
    fold_halist halist_add m2 m1.

  #[global] Instance HMap_halist : HMap K V halist :=
  { empty  := nil
  ; add    := @halist_add
  ; remove := @halist_remove
  ; lookup := @halist_lookup
  ; union  := @halist_union
  }.

  Section proofs.
    Definition mapsto_halist (k : K) (v : V k) (m : halist) : Prop :=
      halist_lookup k m = Some v.

    Theorem mapsto_empty_halist : forall (k : K) (v : V k), ~ mapsto_halist k v empty.
    Proof.
      intros ?? H.
      inversion H.
    Qed.

    Theorem mapsto_lookup_halist : forall (k : K) (v : V k) (m : halist),
      lookup k m = Some v <-> mapsto_halist k v m.
    Proof.
      reflexivity.
    Qed.

    Theorem mapsto_remove_eq_halist : forall m k v, ~ mapsto_halist k v (halist_remove k m).
    Proof.
      intros m k v.
      unfold mapsto_halist.
      induction m.
      - apply mapsto_empty_halist.
      - destruct a. cbn.
        destruct (x == k); [apply IHm|].
        cbn.
        destruct (x == k); [|apply IHm].
        contradiction.
    Qed.

    Theorem mapsto_remove_neq_halist : forall m k k', k <> k' ->
      forall v', (mapsto_halist k' v' m <-> mapsto_halist k' v' (halist_remove k m)).
    Proof.
      intros ??? Hneq ?.
      unfold mapsto_halist.
      induction m.
      - reflexivity.
      - destruct a.
        cbn.
        destruct (x == k) as [Heqk | Hneqk].
        + cbn. rewrite <- IHm.
          revert v.
          rewrite Heqk.
          destruct (k == k') as [Heqk' | _]; [exfalso; apply Hneq, Heqk'|reflexivity].
        + cbn. destruct (x == k') as [? | ?]; [reflexivity|apply IHm].
    Qed.

    Theorem mapsto_add_eq_halist : forall m k v, mapsto_halist k v (halist_add k v m).
    Proof.
      intros.
      unfold mapsto_halist.
      cbn.
      destruct (k == k) as [Heq | Hneq].
      - rewrite <- Eqdep_dec.eq_rect_eq_dec; [reflexivity|assumption].
      - exfalso. apply Hneq. reflexivity.
    Qed.

    Theorem mapsto_add_neq_halist : forall m k v k', k <> k' ->
      forall v', (mapsto_halist k' v' m <-> mapsto_halist k' v' (halist_add k v m)).
    Proof.
      intros ???? Hneq ?.
      unfold mapsto_halist.
      cbn.
      destruct (k == k') as [Heq | _].
      - exfalso. apply Hneq, Heq.
      - apply mapsto_remove_neq_halist, Hneq.
    Qed.

    #[global] Instance HMapOk_halist : HMapOk HMap_halist :=
      {| mapsto := mapsto_halist
       ; mapsto_empty := mapsto_empty_halist
       ; mapsto_lookup := mapsto_lookup_halist
       ; mapsto_add_eq := mapsto_add_eq_halist
       ; mapsto_add_neq := mapsto_add_neq_halist
       ; mapsto_remove_eq := mapsto_remove_eq_halist
       ; mapsto_remove_neq := mapsto_remove_neq_halist
      |}.
    
  End proofs.

  #[global] Instance Foldable_halist : Foldable halist {k : K & V k} :=
    fun _ f => fold_halist (fun k v => f (existT _ k v)).

End HAList.



(*Definition handle_tvars {E} : tvarE ~> stateT _ (itree E).*)

Variant TVarEntry : Type := | TVarEnt {A} (t : TVar A) (v1 v2 : A).
Definition tvar_log : Type := list TVarEntry.

Definition read_tvar_log {E} `{tvarE -< E} {A} (t : TVar A) : tvar_log -> itree E (tvar_log * A) :=
  fix _read_tvar_log l :=
    match l with
    | [] => v <- trigger (ReadTVar t) ;; Ret ([TVarEnt t v v], v)
    | (TVarEnt t' v1 v2 :: l') =>
        match tvar_eq_dec t' t with
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
        match tvar_eq_dec t t' with 
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
