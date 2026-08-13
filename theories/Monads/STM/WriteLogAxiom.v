From Crane Require Import Monads.ITree Monads.STMDefsAxiom Utils.HMap.

From ExtLib Require Import Structures.Reducible.

From ITree Require Import Basics.Basics Events.FailFacts.

Import Basics.Monads.

From Stdlib Require Import List.
Import ListNotations.

Definition commit_log {M} `{Foldable M (sigT (fun X => TVar X * X)%type)} {E} `{H : tvarE -< E} : M -> itree E unit :=
  fold (fun '(existT _ X (x, v)) acc => Vis (subevent (H := H) _ (WriteTVar x v)) (fun _ => acc)) (Ret tt).

Variant tvar_log_entry : Type :=
| tvar_log_new {A} (x : TVar A) (a : A)
| tvar_log_write {A} (x : TVar A) (a : A).

Definition tvar_log : Type := list tvar_log_entry.

Fixpoint log_write (l : tvar_log) {A} (x : TVar A) (v : A) : tvar_log :=
  match l with
  | [] => _
  | tvar_log_new y a :: l' => _
  | tvar_log_write y a :: l' => _
  end.

Definition handle_tvar_log {M} {E} `{H : tvarE -< E}
  (m : M) : forall {A}, tvarE A -> itree E (A * M) :=
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

Definition h_stm_write_log {K} {V : K -> Type} {M} `{HMap (pkey K nat) (pkey_type V) M} {E} `{tvarE V -< E}:
  stmE V ~> stateT M (failT (itree E)) :=
  fun _ e m =>
    match e with
    | inl1 Retry => Ret None
    | inr1 e =>
        '(a, m) <- handle_tvar_log m e ;;
        Ret (Some (m, a))
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
