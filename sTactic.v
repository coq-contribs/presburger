(************************************************************************)
(*                                                                      *)
(*                  sTactic.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(** Some simple tactics *)

Theorem Contradict1 : forall a b : Prop, b -> (a -> ~ b) -> ~ a.
intuition.
Qed.

Theorem Contradict2 : forall a b : Prop, b -> ~ b -> a.
intuition.
Qed.

Theorem Contradict3 : forall a : Prop, a -> ~ ~ a.
auto.
Qed.
(** Contradict is used to contradict an hypothesis H
  -if we have H:~A |- B the result is |- A
  -if we have H:~A |- ~B the result is H:B |- A
*)

Ltac Contradict name :=
  (apply (fun a : Prop => Contradict1 a _ name); clear name; intros name) ||
    (apply (fun a : Prop => Contradict2 a _ name); clear name);
   try apply Contradict3.

(** Same as Case but keeps an equality *)

Ltac CaseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.
(* Same as Case but cleans the case variable  *)

(** Same as Case but clear the variable *)
Ltac Casec name := case name; clear name.
(* Same as Elim but cleans the elim variable  *)

(** Same as Elim but keeps an equality *)
Ltac Elimc name := elim name; clear name.