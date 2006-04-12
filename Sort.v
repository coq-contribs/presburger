(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(************************************************************************)
(*                                                                      *)
(*                          Sort.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
Require Import List.
Require Import Normal.
Require Import Nat.
Require Import ZArithRing.
Require Import sTactic.
Require Import Factor.
Require Import GroundN.

(** Sort 
   -Take a formula [f] that is supposed Cnf1 (conjunction of atomic formula)
   -Return for list [(l1,l2,l3,l4)]
   -- [l1] is the list of atomic formulae where the variable 0 does not occur    
   -- [l2] is the list of equalities
   -- [l3] is the list of inequalities
   -- [l4] is the list of congruence
 *)
 
Fixpoint sortAnd (f : form) :
 list form * (list (nat * form) * (list (nat * form) * list (nat * form))) :=
  match f with
  | ANd f1 f2 =>
      match sortAnd f1 with
      | (l1, (l2, (l3, l4))) =>
          match sortAnd f2 with
          | (l'1, (l'2, (l'3, l'4))) =>
              (l1 ++ l'1, (l2 ++ l'2, (l3 ++ l'3, l4 ++ l'4)))
          end
      end
  | Form.Eq e1 e2 =>
      match factorExp f with
      | (O, f1) => (f1 :: nil, (nil, (nil, nil)))
      | (S i, f1) => (nil, ((S i, f1) :: nil, (nil, nil)))
      end
  | Neg (Form.Eq e1 e2) =>
      match factorExp f with
      | (O, f1) => (f1 :: nil, (nil, (nil, nil)))
      | (S i, f1) => (nil, (nil, ((S i, f1) :: nil, nil)))
      end
  | Cong O e1 e2 =>
      match factorExp (Form.Eq e1 e2) with
      | (O, f1) => (f1 :: nil, (nil, (nil, nil)))
      | (S i, f1) => (nil, ((S i, f1) :: nil, (nil, nil)))
      end
  | Cong (S n) e1 e2 =>
      match factorExp f with
      | (O, f1) => (f1 :: nil, (nil, (nil, nil)))
      | (S i, f1) => (nil, (nil, (nil, (S i, f1) :: nil)))
      end
  | _ => (f :: nil, (nil, (nil, nil)))
  end.
 
Theorem sortAnd_correct :
 forall l f,
 Cnf1 f ->
 match sortAnd f with
 | (l1, (l2, (l3, l4))) =>
     (form2Prop l f <->
      form2Prop (tail l) (buildConj l1) /\
      formL2Prop (nth 0 l 0%Z) (tail l) l2 /\
      formL2Prop (nth 0 l 0%Z) (tail l) l3 /\
      formL2Prop (nth 0 l 0%Z) (tail l) l4) /\
     Cnf1 (buildConj l1) /\ listEqP l2 /\ listNEqP l3 /\ listCongP l4
 end.
intros l f H; elim H; auto.
intros a H1; elim H1; auto.
simpl in |- *; split; try (intuition; fail); auto.
simpl in |- *; split; try (intuition; fail); auto.
intros a1 b1; generalize (factorExp_correct l (Form.Eq a1 b1)); simpl in |- *.
case (factorVar0 a1); case (factorVar0 b1); simpl in |- *.
intros n1 e1 n2 e2; CaseEq (n1 - n2); CaseEq (n2 - n1).
replace (nth 0 l 0 * Z_of_nat 0 + exp2Z (tail l) e1)%Z with
 (exp2Z (tail l) e1);
 [ split; auto; simpl in |- *; intuition | simpl in |- *; ring ].
split; auto; simpl in |- *; intuition.
split; auto; simpl in |- *; intuition.
split; auto; simpl in |- *; intuition.
intros a1 b1; generalize (factorExp_correct l (Neg (Form.Eq a1 b1)));
 simpl in |- *.
case (factorVar0 a1); case (factorVar0 b1); simpl in |- *.
intros n1 e1 n2 e2; CaseEq (n1 - n2); CaseEq (n2 - n1).
replace (nth 0 l 0 * Z_of_nat 0 + exp2Z (tail l) e1)%Z with
 (exp2Z (tail l) e1);
 [ split; auto; simpl in |- *; intuition | simpl in |- *; ring ].
split; auto; simpl in |- *; intuition.
split; auto; simpl in |- *; intuition.
split; auto; simpl in |- *; intuition.
intros i a1 b1; generalize (factorExp_correct l (Cong i a1 b1));
 simpl in |- *.
case (factorVar0 a1); case (factorVar0 b1); simpl in |- *.
intros n1 e1 n2 e2; CaseEq (n1 - n2); CaseEq (n2 - n1).
case i; simpl in |- *.
replace (nth 0 l 0 * 0 + exp2Z (tail l) e1)%Z with (exp2Z (tail l) e1);
 [ idtac | simpl in |- *; ring ].
intros H0 H2 H3; split; auto.
apply iff_trans with (congZ 0 (exp2Z (tail l) e2) (exp2Z (tail l) e1)); auto.
apply
 iff_trans with (1 := congZ_O_Eq (exp2Z (tail l) e2) (exp2Z (tail l) e1));
 intuition.
replace (nth 0 l 0 * 0 + exp2Z (tail l) e1)%Z with (exp2Z (tail l) e1);
 [ split; auto; simpl in |- *; intuition | simpl in |- *; ring ].
case i.
intros n H2 H3 H4; split; [ idtac | simpl in |- *; auto with arith ].
cut
 (congZ 0 (exp2Z l a1) (exp2Z l b1) <->
  exp2Z (tail l) e1 = (nth 0 l 0 * Z_of_nat (S n) + exp2Z (tail l) e2)%Z).
simpl in |- *; intuition.
apply iff_trans with (1 := H4); apply congZ_O_Eq.
simpl in |- *; intuition; auto with arith.
case i.
intros H0 n H2 H3; split; [ idtac | simpl in |- *; auto with arith ].
cut
 (congZ 0 (exp2Z l a1) (exp2Z l b1) <->
  exp2Z (tail l) e2 = (nth 0 l 0 * Z_of_nat (S n) + exp2Z (tail l) e1)%Z).
simpl in |- *; intuition.
apply iff_trans with (1 := H3); apply congZ_O_Eq.
simpl in |- *; intuition; auto with arith.
intros n H0 n0 H2 H3; absurd (n1 <= n2).
apply lt_not_le.
apply lt_O_minus_lt; rewrite H2; auto with arith.
apply lt_le_weak; apply lt_O_minus_lt; rewrite H0; auto with arith.
simpl in |- *.
intros a b H0 H1 H2 H3.
generalize H1 H3; clear H1 H3; case (sortAnd a).
intros l11 p; case p; clear p.
intros l12 p; case p; clear p.
intros l13 l14; case (sortAnd b).
intros l21 p; case p; clear p.
intros l22 p; case p; clear p.
intros l23 l24.
intros (H4, H5).
intros (H'4, H'5).
split.
generalize (buildConj_append (tail l) l11 l21);
 generalize (formL2Prop_append (nth 0 l 0%Z) (tail l) l12 l22);
 generalize (formL2Prop_append (nth 0 l 0%Z) (tail l) l13 l23);
 generalize (formL2Prop_append (nth 0 l 0%Z) (tail l) l14 l24); 
 intuition.
case H5; intros H6 (H7, (H8, H9)); auto.
case H'5; intros H'6 (H'7, (H'8, H'9)); auto.
Qed.
 
 
Theorem sortAnd_groundN :
 forall n f,
 Cnf1 f ->
 groundNForm n f ->
 match sortAnd f with
 | (l1, (l2, (l3, l4))) =>
     groundNL (pred n) l1 /\
     groundNL2 (pred n) l2 /\ groundNL2 (pred n) l3 /\ groundNL2 (pred n) l4
 end.
intros n f H; generalize n; elim H; clear H f n; simpl in |- *; auto.
intros a H; elim H; clear H a; unfold sortAnd in |- *; lazy beta in |- *;
 auto.
intros a b n H; generalize (factorExp_groundN (Form.Eq a b));
 case (factorExp (Form.Eq a b)).
intros n0 f; case n0; simpl in |- *; auto.
intros a b n H; generalize (factorExp_groundN (Neg (Form.Eq a b)));
 case (factorExp (Neg (Form.Eq a b))).
intros n0 f; case n0; simpl in |- *; auto.
intros n1 H0; repeat split; auto.
intros i; case i; auto.
intros a b n H; cut (groundNForm n (Form.Eq a b));
 [ intros H1 | inversion H; auto ].
generalize (factorExp_groundN (Form.Eq a b)); case (factorExp (Form.Eq a b)).
intros n0 f; case n0; simpl in |- *; auto.
apply GNEq with (n := n0) (m := m); auto.
intros i1 a b n H; generalize (factorExp_groundN (Cong (S i1) a b));
 case (factorExp (Cong (S i1) a b)).
intros n0 f; case n0; simpl in |- *; auto.
intros n1 H0; repeat split; auto.
intros a b H H0 H1 H2 n H3.
inversion H3.
generalize (H0 n0 H9) (H2 m H10).
case (sortAnd a); simpl in |- *.
intros l1 p0; case p0; clear p0.
intros l2 p0; case p0; clear p0.
intros l3 l4.
case (sortAnd b); simpl in |- *.
intros l'1 p0; case p0; clear p0.
intros l'2 p0; case p0; clear p0.
intros l'3 l'4; auto.
intros (Z1, (Z2, (Z3, Z4))) (Z'1, (Z'2, (Z'3, Z'4))); repeat split; auto.
apply groundNL_app; auto.
apply groundNL_le with (n := pred n0); auto with arith.
apply groundNL_le with (n := pred m); auto with arith.
apply groundNL2_app; auto.
apply groundNL2_le with (n := pred n0); auto with arith.
apply groundNL2_le with (n := pred m); auto with arith.
apply groundNL2_app; auto.
apply groundNL2_le with (n := pred n0); auto with arith.
apply groundNL2_le with (n := pred m); auto with arith.
apply groundNL2_app; auto.
apply groundNL2_le with (n := pred n0); auto with arith.
apply groundNL2_le with (n := pred m); auto with arith.
Qed.