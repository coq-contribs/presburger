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
(*                        Factor.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(** Factorize expression *)
Require Import List.
Require Import Normal.
Require Import Nat.
Require Import ZArithRing.
Require Import sTactic.
Require Import GroundN.
 
 
(** Factor the variable of index 0 and decrement of 1 the other
    variables 
   - Take an expression
   - Return [(n,e')]  where
   --  [n] is the number of occurrences of (Var O)
   -- [e'] is the same expression than [e] but all
     the variables have an index decremented of 1 and
     [(Var O)] is canceled
*)
Fixpoint factorVar0 (e : exp) : nat * exp :=
  match e with
  | Var O => (1, Num 0)
  | Var (S i) => (0, Var i)
  | Num i => (0, Num i)
  | Plus e1 e2 =>
      match factorVar0 e1 with
      | (m1, e3) =>
          match factorVar0 e2 with
          | (m2, e4) => (m1 + m2, Plus e3 e4)
          end
      end
  end.
 
Theorem factorVar0_correct :
 forall l (e : exp),
 match factorVar0 e with
 | (n, e1) => exp2Z l e = (nth 0 l 0 * Z_of_nat n + exp2Z (tail l) e1)%Z
 end.
intros l e; elim e; simpl in |- *; auto.
intros n; case l; simpl in |- *; intros; ring.
intros n; case n; simpl in |- *; auto; try ring.
intros n1; case n1; case l; simpl in |- *; intros; ring.
intros e0 H e1 H0; generalize H H0; case (factorVar0 e0);
 case (factorVar0 e1); simpl in |- *.
intros n e2 n0 e3 H1 H2; rewrite H1; rewrite H2; rewrite Znat.inj_plus; ring.
Qed.
 
Theorem factorVar0_groundN :
 forall (e : exp) p,
 match factorVar0 e with
 | (n, e1) => groundNExp p e -> groundNExp (pred p) e1
 end.
intros e; elim e; simpl in |- *; auto.
intros n p; case n; simpl in |- *; auto.
intros n0 H; inversion H; auto with arith.
intros e1; case (factorVar0 e1); simpl in |- *.
intros n e'1 H e2; case (factorVar0 e2); simpl in |- *.
intros n0 e0 H0 p H1.
inversion H1; auto with arith.
apply GNPlus with (n := pred n1) (m := pred m); auto with arith.
Qed.

(** Factor the variable of index 0 and decrement of 1 the other
    variables 
   - Take an expression
   - Return [(n,e')]  where
   --  [n] is the number of occurrences of (Var O)
   -- [e'] is the same expression than [e] but all
     the variables have an index decremented of 1 and
     [(Var O)] is canceled
*)
Definition factorExp f :=
  match f with
  | Form.Eq a b =>
      match factorVar0 a with
      | (m1, a1) =>
          match factorVar0 b with
          | (m2, b1) =>
              match m1 - m2 with
              | O => (m2 - m1, Form.Eq a1 b1)
              | S i => (S i, Form.Eq b1 a1)
              end
          end
      end
  | Neg (Form.Eq a b) =>
      match factorVar0 a with
      | (m1, a1) =>
          match factorVar0 b with
          | (m2, b1) =>
              match m1 - m2 with
              | O => (m2 - m1, Neg (Form.Eq a1 b1))
              | S i => (S i, Neg (Form.Eq b1 a1))
              end
          end
      end
  | Cong n a b =>
      match factorVar0 a with
      | (m1, a1) =>
          match factorVar0 b with
          | (m2, b1) =>
              match m1 - m2 with
              | O => (m2 - m1, Cong n a1 b1)
              | S i => (S i, Cong n b1 a1)
              end
          end
      end
  | _ => (0, f)
  end.
 
Theorem factorExp_correct :
 forall l (f : form),
 match factorExp f with
 | (n, Form.Eq a b) =>
     form2Prop l f <->
     exp2Z (tail l) a = (nth 0 l 0 * Z_of_nat n + exp2Z (tail l) b)%Z
 | (n, Neg (Form.Eq a b)) =>
     form2Prop l f <->
     exp2Z (tail l) a <> (nth 0 l 0 * Z_of_nat n + exp2Z (tail l) b)%Z
 | (n, Cong i a b) =>
     form2Prop l f <->
     congZ i (exp2Z (tail l) a) (nth 0 l 0%Z * Z_of_nat n + exp2Z (tail l) b)
 | (n, f1) => n = 0 /\ f1 = f
 end.
intros l f; elim f; simpl in |- *; auto.
intros f0; case f0; simpl in |- *; auto.
intros e e0; generalize (factorVar0_correct l e) (factorVar0_correct l e0);
 case (factorVar0 e); case (factorVar0 e0); simpl in |- *; 
 auto.
intros n e1 n0 e2 H H0; CaseEq (n0 - n).
intuition.
intros; intuition.
intros e e0; generalize (factorVar0_correct l e) (factorVar0_correct l e0);
 case (factorVar0 e); case (factorVar0 e0); simpl in |- *; 
 auto.
intros n e1 n0 e2 H H0; CaseEq (n0 - n).
intros H2; rewrite H; rewrite H0; rewrite Znat.inj_minus1.
split; intros H3.
apply
 trans_equal
  with
    (nth 0 l 0 * Z_of_nat n + exp2Z (tail l) e1 +
     nth 0 l 0 * (0 - Z_of_nat n0))%Z.
rewrite <- H3; ring.
ring.
rewrite H3; ring.
apply minus_O_le; auto.
intros n1 H1; rewrite <- H1.
rewrite H; rewrite H0; rewrite Znat.inj_minus1.
split; intros H3.
apply
 trans_equal
  with
    (nth 0 l 0 * Z_of_nat n0 + exp2Z (tail l) e2 +
     nth 0 l 0 * (0 - Z_of_nat n))%Z.
rewrite H3; ring.
ring.
rewrite H3; ring.
apply lt_le_weak; apply lt_O_minus_lt; rewrite H1; auto with arith.
intros i e e0; generalize (factorVar0_correct l e) (factorVar0_correct l e0);
 case (factorVar0 e); case (factorVar0 e0); simpl in |- *; 
 auto.
intros n e1 n0 e2 H H0; CaseEq (n0 - n).
intros H2; rewrite H; rewrite H0; rewrite Znat.inj_minus1.
split; intros (m1, H3).
exists m1.
apply
 trans_equal
  with
    (nth 0 l 0 * Z_of_nat n + exp2Z (tail l) e1 + m1 * Z_of_nat i +
     nth 0 l 0 * (0 - Z_of_nat n0))%Z; [ rewrite <- H3 | idtac ]; 
 ring.
exists m1.
rewrite H3; ring.
apply minus_O_le; auto.
intros n1 H1; rewrite <- H1.
rewrite H; rewrite H0; rewrite Znat.inj_minus1.
split; intros (m1, H3).
exists (- m1)%Z.
apply
 trans_equal
  with
    (nth 0 l 0 * Z_of_nat n0 + exp2Z (tail l) e2 + - m1 * Z_of_nat i +
     nth 0 l 0 * (0 - Z_of_nat n))%Z; [ rewrite H3 | idtac ]; 
 ring.
exists (- m1)%Z.
rewrite H3; ring.
apply lt_le_weak; apply lt_O_minus_lt; rewrite H1; auto with arith.
Qed.
 
Theorem factorExp_groundN :
 forall e : form,
 Cnf2 e ->
 forall p,
 match factorExp e with
 | (n, e1) => groundNForm p e -> groundNForm (pred p) e1
 end.
intros e H; elim H; simpl in |- *; auto; clear H e.
intros a1 b1 p; generalize (factorVar0_groundN a1); case (factorVar0 a1);
 generalize (factorVar0_groundN b1); case (factorVar0 b1).
intros n e H n0 e0 H0; case (n0 - n); auto.
intros H1; inversion H1; auto.
apply GNEq with (n := pred n1) (m := pred m); auto with arith.
intros n1 H1.
inversion H1; auto.
apply GNEq with (n := pred m) (m := pred n2); auto with arith.
intros a1 b1 p; generalize (factorVar0_groundN a1); case (factorVar0 a1);
 generalize (factorVar0_groundN b1); case (factorVar0 b1).
intros n e H n0 e0 H0; case (n0 - n); auto.
intros H1; inversion H1; auto.
apply GNNeg.
inversion H4.
apply GNEq with (n := pred n2) (m := pred m); auto with arith.
intros n1 H1.
inversion H1; auto.
apply GNNeg.
inversion H4.
apply GNEq with (n := pred m) (m := pred n3); auto with arith.
intros i a1 b1 p; generalize (factorVar0_groundN a1); case (factorVar0 a1);
 generalize (factorVar0_groundN b1); case (factorVar0 b1).
intros n e H n0 e0 H0; case (n0 - n); auto.
intros H1; inversion H1; auto.
apply GNCong with (n := pred n1) (m := pred m); auto with arith.
intros n1 H1.
inversion H1; auto.
apply GNCong with (n := pred m) (m := pred n2); auto with arith.
Qed.