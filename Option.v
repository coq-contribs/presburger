(************************************************************************)
(*                                                                      *)
(*                        Option.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(** Usual option type *)

Inductive Option (A : Set) : Set :=
  | Some : forall x : A, Option A
  | None : Option A.