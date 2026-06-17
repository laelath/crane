From Crane Require Import Monads.ITree Monads.STM.Schedule.

From Stdlib Require Import Arith.PeanoNat Bool.Bool Classes.EquivDec.

From ITree Require Import Basics.CategoryOps.


Inductive parE E : Type -> Type :=
| Par : forall {A B} (t1 : itree (parE E +' E) A) (t2 : itree (parE E +' E) B), parE E (A * B).

Definition par {E F} `{parE F -< E} {A B} (t1 : itree (parE F +' F) A) (t2 : itree (parE F +' F) B) : itree E (A * B) :=
  trigger (Par _ t1 t2).

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



Definition schedule_par_rr {E R} (pt : par_tree E R) : itree E R :=
  interp (case_ h_rr (id_ _)) (schedule_par pt).
