From Crane Require Import Monads.ITree Monads.STMDefs Utils.HMap.

From ExtLib Require Import Structures.Reducible.

From ITree Require Import Basics.Basics Events.FailFacts.

Import Basics.Monads.

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

