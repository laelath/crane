From ITree Require Import ITree Eq Props.HasPost.

#[local] Open Scope itree_scope.

Lemma has_post_eta {E R} {P : R -> Prop} (t : itree E R) : has_post t P -> has_post (go (observe t)) P.
Proof.
  intros.
  rewrite <- itree_eta.
  assumption.
Qed.

Lemma has_post_inv_Ret {E R} {P : R -> Prop} (r : R) : has_post ((Ret r) : itree E R) P -> P r.
Proof.
  intros.
  apply eqit_inv_Ret in H.
  apply H.
Qed.

Lemma has_post_inv_Tau {E R} {P : R -> Prop} (t : itree E R) : has_post (Tau t) P -> has_post t P.
Proof.
  intros.
  apply eqit_inv_Tau in H.
  apply H.
Qed.

Lemma has_post_inv_Vis {E R} {P : R -> Prop} {X} (e : E X) (k : X -> itree E R) : has_post (Vis e k) P -> forall x, has_post (k x) P.
Proof.
  intros.
  eapply eqit_inv_Vis in H.
  apply H.
Qed.

CoFixpoint with_post {E R} {P : R -> Prop} (t : itree E R) (pf : has_post t P) : itree E {x:R | P x} :=
  let ot := observe t in
  let pf' := has_post_eta _ pf in
  (match ot return ot = observe t -> _ with
  | RetF r => fun Heqot => Ret (exist P r (has_post_inv_Ret _ (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot)))
  | TauF t => fun Heqot => Tau (@with_post E R P t (has_post_inv_Tau _ (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot)))
  | VisF e k => fun Heqot => Vis e (fun x => @with_post E R P (k x) (has_post_inv_Vis _ _ (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot) x))
  end) eq_refl.

Arguments with_post : clear implicits.
Arguments with_post {E R P} (t pf).

Notation with_post_ P t pf :=
  (let ot := observe t in
   let pf' := has_post_eta _ pf in
   (match ot return ot = observe t -> _ with
    | RetF r => fun Heqot => Ret (exist P r (has_post_inv_Ret _ (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot)))
    | TauF t => fun Heqot => Tau (@with_post _ _ P t (has_post_inv_Tau _ (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot)))
    | VisF e k => fun Heqot => Vis e (fun x => @with_post _ _ P (k x) (has_post_inv_Vis _ _ (eq_ind_r (fun ot => has_post (go ot) P) pf' Heqot) x))
    end) eq_refl).



Lemma unfold_with_post {E R} (P : R -> Prop) (t : itree E R) (pf : has_post t P) :
  with_post t pf ≅ with_post_ P t pf.
Proof.
  apply observing_sub_eqit; constructor; reflexivity.
Qed.


Lemma with_post_proj1 {E R} {P : R -> Prop} (t : itree E R) (pf : has_post t P) :
  ITree.map (@proj1_sig R P) (with_post t pf) ≅ t.
Proof.
Abort.

Lemma has_post_subrel : forall {E R} (t : itree E R) (P Q : R -> Prop),
  (forall x, P x -> Q x) ->
  has_post t P ->
  has_post t Q.
Proof.
  intros.
  eapply eutt_subrel, H0.
  intros ??.
  apply H.
Qed.
