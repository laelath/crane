From Crane Require Import Monads.ITree.

From Stdlib Require Import Arith.PeanoNat List.

Import ListNotations.

From ITree Require Import Basics.Basics.

Open Scope itree_scope.

(* Scheduler implementations should be such that 0 getting chosen infinitely often will ensure that every thread gets scheduled *)
Variant scheduleE : Type -> Type :=
| Schedule (n : nat) : scheduleE {m : nat | m < n}.

Definition h_rr {E} : scheduleE ~> itree E :=
  fun _ e =>
    match e with
    | Schedule n =>
        match n with
        | 0 => ITree.spin (* error *)
        | S m => Ret (exist _ 0 (PeanoNat.Nat.lt_0_succ m))
        end
    end.

Fixpoint signth {A} (l : list A) (n : {m : nat | m < length l}) : A :=
  match l, n with
  | [], exist _ m H => False_rect _ (PeanoNat.Nat.nlt_0_r m H)
  | (v :: l), exist _ m H =>
    match m with
    | 0 => fun _ => v
    | S m => fun H : S m < S (length l) => signth l (exist _ m (PeanoNat.lt_S_n _ _ H))
    end H
  end.

