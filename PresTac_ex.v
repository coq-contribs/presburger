(************************************************************************)
(*                                                                      *)
(*                    PresTac_ex.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
Require Import PresTac.

(** Examples of application of the tactic *)
Theorem OddEven :
 forall x : BinInt.Z,
 (exists y : BinInt.Z, x = (y + y)%Z) \/
 (exists y : BinInt.Z, x = (y + y + 1)%Z).
prestac.
Qed.

Theorem NOddEven :
 forall x : BinInt.Z,
 ~
 ((exists y : BinInt.Z, x = (y + y)%Z) /\
  (exists y : BinInt.Z, x = (y + y + 1)%Z)).
prestac.
Qed.