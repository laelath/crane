From ITree Require Import ITree Basics.Basics Core.Subevent.

Variant errorE X : Type -> Type :=
| Error (x : X) : errorE X void.

Arguments Error {X} (x).

Definition error {E X A} `{errorE X -< E} (x : X) : itree E A :=
  Vis (subevent _ (Error x)) (fun (x : void) => match x with end).


