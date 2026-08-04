(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared STM effect definitions (flavor-independent).

   Contains the effect inductives ([tvarE], [stmVecE], [stmControlE]),
   composed effect ([stmE]), axioms, and smart constructors that are
   identical across library flavors. Flavor files ([STM.v], [STMBDE.v])
   re-export this module and add flavor-specific C++ extraction mappings.
*)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Monads.ITree.

From ITree Require Import Basics.Basics.

Open Scope itree_scope.

Axiom TVar : Type -> Type.

Inductive tvarE : Type -> Type :=
| NewTVar : forall {A}, A -> tvarE (TVar A)
| ReadTVar : forall {A}, TVar A -> tvarE A
| WriteTVar : forall {A}, TVar A -> A -> tvarE unit.


Inductive stmControlE : Type -> Type :=
| Retry : stmControlE void.

Crane Extract Inductive stmControlE => ""
  [ "stm::retry()" ].

Definition stmE : Type -> Type := stmControlE +' tvarE.
Crane Extract Skip stmE.

Definition retry {A} : itree stmE A :=
  trigger (inl1 Retry) >>= fun (x : void) => match x with end.

(* not entirely sure why this is required *)
(*
#[global] Instance tvarE_sub_stmE {K} (V : K -> Type) : tvarE V -< stmE V := inr1.
#[global] Instance stmControlE_sub_stmE {K} (V : K -> Type) : stmControlE -< stmE V := inl1.
Crane Extract Skip tvarE_sub_stmE.
Crane Extract Skip stmControlE_sub_stmE.
*)



Variant runStmE : Type -> Type :=
| Atomically : forall {A} (t : itree stmE A), runStmE A.

Definition atomically {E} `{runStmE -< E} {A} (t : itree stmE A) : itree E A :=
  trigger (Atomically t).

Crane Extract Inductive runStmE => ""
  [ "stm::atomically([&] { return %a0; })" ].



(*
Definition orElse {A} {K} {V : K -> Type} `{EqDec K eq} (t1 t2 : itree (stmControlE +' tvarE V) A) : itree (stmE V) A :=
  (cofix _orElse (m : halist (pkey K nat) (pkey_type V)) t :=
    match observe t with
    | RetF a =>
        commit_log V m ;;
        Ret a
    | TauF t => Tau (_orElse m t)
    | VisF (inr1 e) k => '(x, m) <- handle_tvar_log m e ;; Tau (_orElse m (k x))
    | VisF (inl1 Retry) _ => t2
    end) HMap.empty t1.
*)



Definition newTVar {A} (a : A) : itree stmE (TVar A) := trigger (inr1 (NewTVar a)).
Definition readTVar {A} (v : TVar A) : itree stmE A := trigger (inr1 (ReadTVar v)).
Definition writeTVar {A} (v : TVar A) (a : A) : itree stmE unit := trigger (inr1 (WriteTVar v a)).

Definition check (b : bool) : itree stmE unit :=
  if b then Ret tt else retry.

Definition modifyTVar {A} (a : TVar A) (f : A -> A) : itree stmE unit :=
  val <- readTVar a ;;
  writeTVar a (f val) ;;
  Ret tt.

Crane Extract Inlined Constant atomically => "stm::atomically([&] { return %a0; })".
(*Crane Extract Inlined Constant orElse => "stm::orElse<%t0>(%a0, %a1)".*)
Crane Extract Inlined Constant retry => "stm::retry<%t2>()".
Crane Extract Inlined Constant newTVar => "stm::newTVar(%a1)".



From ITree Require Import Basics.Basics.

Import Basics.Monads.

Variant h_tvarE_spec : forall A, tvarE A -> (TVar ~> option) -> A -> (TVar ~> option) -> Prop :=
| h_NewTVar {A} (a : A) (x : TVar A) s1 s2 :
    s1 _ x = None ->
    s2 _ x = Some a ->
    (* s2 is the same as s1 except for x *) True ->
    h_tvarE_spec (TVar A) (NewTVar a) s1 x s2
| h_ReadTVar {A} (x : TVar A) (a : A) s :
    s _ x = Some a ->
    h_tvarE_spec A (ReadTVar x) s a s
| h_WriteTVar {A} (x : TVar A) (a b : A) s1 s2 :
    s1 _ x = Some b ->
    s2 _ x = Some a ->
    (* s2 is the same as s1 except for x *) True ->
    h_tvarE_spec unit (WriteTVar x a) s1 tt s2.

Variant interp_state_specF {E F S} (h : forall A, E A -> S -> A -> S -> Prop) {A}
  (sim : itree (E +' F) A -> S -> itree F (S * A) -> Prop):
  itree' (E +' F) A -> S -> itree' F (S * A) -> Prop :=
| InterpStateSpecRet a s : interp_state_specF h sim (RetF a) s (RetF (s, a))
| InterpStateSpecTau t1 s t2 :
    sim t1 s t2 ->
    interp_state_specF h sim (TauF t1) s (TauF t2)
| InterpStateSpecVis {X} (e : F X) k1 s k2 :
    (forall x, sim (k1 x) s (k2 x)) ->
    interp_state_specF h sim (VisF (inr1 e) k1) s (VisF e k2)
| InterpStateSpecState {X} (e : E X) k1 s1 s2 r t2 :
    h _ e s1 r s2 ->
    sim (k1 r) s2 t2 ->
    interp_state_specF h sim (VisF (inl1 e) k1) s1 (TauF t2).

Definition interp_state_spec_ {E F S} h {A} sim (t1 : itree (E +' F) A) (s : S) t2 :=
  interp_state_specF h sim (observe t1) s (observe t2).


From Stdlib Require Import Basics.
From Coinduction Require Import all.
From Paco Require Import paco.
From ITree Require Import Eq Eq.Shallow.

Program Definition interp_state_specb {E F S} (h : forall A, E A -> S -> A -> S -> Prop) {A} :
  mon (itree (E +' F) A -> S -> itree F (S * A) -> Prop) :=
  {| body := interp_state_spec_ h |}.
Next Obligation.
  intros x y H t1 s t2 SR.
  red in H.
  red. red in SR.
  genobs_clear t1 ot1.
  genobs_clear t2 ot2.
  inversion SR; subst.
  - constructor.
  - constructor. auto.
  - constructor. auto.
  - econstructor; eauto.
Defined.



Definition interp_state_spec {E F S} (h : forall A, E A -> S -> A -> S -> Prop) {A} :=
  gfp (@interp_state_specb _ F _ h A).



#[global] Instance interp_state_spec_cong_eqit_chain {E F S A} h (C : Chain (@interp_state_specb E F S h A)):
  Proper (eq_itree eq ==> eq ==> eq_itree eq ==> flip impl) (elem C).
Proof.
  eapply (tower (P := fun R => Proper (eq_itree eq ==> eq ==> eq_itree eq ==> flip impl) R)).
  { intros T HT t1 t1' EQ1 s s' Hs t2 t2' EQ2 H sim Tsim.
    apply (HT sim Tsim t1 t1' EQ1 s s' Hs t2 t2' EQ2).
    exact (H sim Tsim). }
  clear C. intros C.
  intros HC t1 t1' EQ1 s s' Hs t2 t2' EQ2 HI.
  subst s'.
  cbn in HI |- *. unfold interp_state_spec_ in HI |- *.
  genobs t1' ot1'.
  genobs t2' ot2'.
  inversion HI; subst; clear HI.
  - (* Ret *)
    rewrite (simpobs H) in EQ1.
    apply eqitree_inv_Ret_r in EQ1 as ->.
    rewrite (simpobs H1) in EQ2.
    apply eqitree_inv_Ret_r in EQ2 as ->.
    constructor.
  - (* Tau *)
    rewrite (simpobs H0) in EQ1.
    apply eqitree_inv_Tau_r in EQ1 as [? [-> ?]].
    rewrite (simpobs H2) in EQ2.
    apply eqitree_inv_Tau_r in EQ2 as [? [-> ?]].
    constructor.
    rewrite H1, H3.
    assumption.
  - (* Vis, right (non-handled) effect *)
    rewrite (simpobs H0) in EQ1.
    apply eqitree_inv_Vis_r in EQ1 as [? [-> ?]].
    rewrite (simpobs H2) in EQ2.
    apply eqitree_inv_Vis_r in EQ2 as [? [-> ?]].
    constructor.
    intros.
    rewrite H1, H3.
    apply H.
  - (* Vis, left (handled/state) effect *)
    rewrite (simpobs H1) in EQ1.
    apply eqitree_inv_Vis_r in EQ1 as [? [-> ?]].
    rewrite (simpobs H3) in EQ2.
    apply eqitree_inv_Tau_r in EQ2 as [? [-> ?]].
    econstructor; [eassumption|].
    rewrite H2, H4.
    assumption.
Qed.

#[global] Instance interp_state_spec_cong_eqit {E F S A} h :
  Proper (eq_itree eq ==> eq ==> eq_itree eq ==> flip impl) (@interp_state_spec E F S h A).
Proof.
  unfold interp_state_spec.
  apply gfp_prop, interp_state_spec_cong_eqit_chain.
Qed.
