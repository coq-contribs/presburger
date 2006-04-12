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
(*                       GroundN.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(** * Ground formulae *)
Require Import Form.
Require Import sTactic.
Require Import Nat.
 
(** Definition of  ground expression at level [n]:
      -no variable has index greater than [n]
*)
Inductive groundNExp : nat -> exp -> Prop :=
  | GNNum : forall i n : nat, groundNExp n (Num i)
  | GNVar : forall i n : nat, i < n -> groundNExp n (Var i)
  | GNPlus :
      forall a b n m p,
      n <= p ->
      m <= p -> groundNExp n a -> groundNExp m b -> groundNExp p (Plus a b).
 
(** Check if an expresssion [e] has level [n]
*)
Fixpoint fgroundNExp (n : nat) (e : exp) {struct e} : bool :=
  match e with
  | Num _ => true
  | Var i => ltdec i n
  | Plus a b =>
      match fgroundNExp n a with
      | true => fgroundNExp n b
      | false => false
      end
  end.
Hint Constructors groundNExp.

(** Definition of  ground formula at level [n]:
      -no variable has index greater than [n]
*)

Inductive groundNForm : nat -> form -> Prop :=
  | GNTrue : forall n : nat, groundNForm n TRue
  | GNFalse : forall n : nat, groundNForm n FAlse
  | GNNeg : forall a n, groundNForm n a -> groundNForm n (Neg a)
  | GNAnd :
      forall a b n m p,
      n <= p ->
      m <= p -> groundNForm n a -> groundNForm m b -> groundNForm p (ANd a b)
  | GNOr :
      forall a b n m p,
      n <= p ->
      m <= p -> groundNForm n a -> groundNForm m b -> groundNForm p (Or a b)
  | GNImp :
      forall a b n m p,
      n <= p ->
      m <= p -> groundNForm n a -> groundNForm m b -> groundNForm p (Imp a b)
  | GNEq :
      forall a b n m p,
      n <= p ->
      m <= p ->
      groundNExp n a -> groundNExp m b -> groundNForm p (Form.Eq a b)
  | GNCong :
      forall i a b n m p,
      n <= p ->
      m <= p ->
      groundNExp n a -> groundNExp m b -> groundNForm p (Cong i a b)
  | GNForall : forall f m, groundNForm (S m) f -> groundNForm m (Forall f)
  | GNExists : forall f m, groundNForm (S m) f -> groundNForm m (Exists f).
Hint Constructors groundForm.

(** Check if an formula [f] has level [n]
*)
 
Fixpoint fgroundNForm (n : nat) (f : form) {struct f} : bool :=
  match f with
  | TRue => true
  | FAlse => true
  | Neg a => fgroundNForm n a
  | ANd a b =>
      match fgroundNForm n a with
      | true => fgroundNForm n b
      | false => false
      end
  | Or a b =>
      match fgroundNForm n a with
      | true => fgroundNForm n b
      | false => false
      end
  | Imp a b =>
      match fgroundNForm n a with
      | true => fgroundNForm n b
      | false => false
      end
  | Form.Eq a b =>
      match fgroundNExp n a with
      | true => fgroundNExp n b
      | false => false
      end
  | Cong i a b =>
      match fgroundNExp n a with
      | true => fgroundNExp n b
      | false => false
      end
  | Forall a => fgroundNForm (S n) a
  | Exists a => fgroundNForm (S n) a
  end.
Hint Constructors groundExp.
Hint Constructors groundNForm.
 
(** Same as groundN but for list *)
Inductive groundNL : nat -> list form -> Prop :=
  | GNNil : forall n : nat, groundNL n nil
  | GNVCons :
      forall a l n, groundNForm n a -> groundNL n l -> groundNL n (a :: l).
 
(** Same as groundN but for list of pair*)
Inductive groundNL2 : nat -> list (nat * form) -> Prop :=
  | GNNil2 : forall n : nat, groundNL2 n nil
  | GNVCons2 :
      forall a l n m,
      groundNForm n a -> groundNL2 n l -> groundNL2 n ((m, a) :: l).
Hint Constructors groundNL.
Hint Constructors groundNL2.
 
(** Some properties of groundN and groundNL *)
Theorem groundNL_app :
 forall n l1 l2, groundNL n l1 -> groundNL n l2 -> groundNL n (l1 ++ l2).
intros n l1 l2 H; generalize l2; elim H; simpl in |- *; auto.
Qed.
Hint Resolve groundNL_app.
 
Theorem groundNL2_app :
 forall n l1 l2, groundNL2 n l1 -> groundNL2 n l2 -> groundNL2 n (l1 ++ l2).
intros n l1 l2 H; generalize l2; elim H; simpl in |- *; auto.
Qed.
Hint Resolve groundNL2_app.
 
Theorem groundNExp_le :
 forall a n m, groundNExp n a -> n <= m -> groundNExp m a.
intros a n m H; generalize m; elim H; clear H n m; simpl in |- *; auto.
intros i n H m H0; apply GNVar.
apply lt_le_trans with (1 := H); auto.
intros a0 b n m p H H0 H1 H2 H3 H4 m0 H5.
apply GNPlus with (n := p) (m := p); auto.
Qed.
 
Theorem groundNForm_le :
 forall a n m, groundNForm n a -> n <= m -> groundNForm m a.
intros a n m H; generalize m; elim H; clear H n m; simpl in |- *; auto.
intros a0 b n m p H H0 H1 H2 H3 H4 m0 H5.
apply GNAnd with (n := p) (m := p); auto.
intros a0 b n m p H H0 H1 H2 H3 H4 m0 H5.
apply GNOr with (n := p) (m := p); auto.
intros a0 b n m p H H0 H1 H2 H3 H4 m0 H5.
apply GNImp with (n := p) (m := p); auto.
intros a0 b n m p H H0 H1 H2 m0 H3.
apply GNEq with (n := p) (m := p); auto.
apply groundNExp_le with (n := n); auto.
apply groundNExp_le with (n := m); auto.
intros i a0 b n m p H H0 H1 H2 m0 H3.
apply GNCong with (n := p) (m := p); auto.
apply groundNExp_le with (n := n); auto.
apply groundNExp_le with (n := m); auto.
intros f m H H0 m0 H1.
apply GNForall; auto with arith.
intros f m H H0 m0 H1.
apply GNExists; auto with arith.
Qed.
 
Theorem groundNL_le : forall a n m, groundNL n a -> n <= m -> groundNL m a.
intros a n m H; generalize m; elim H; clear H n m; simpl in |- *; auto.
intros a0 l n H H0 H1 m H2.
apply GNVCons; auto.
apply groundNForm_le with (n := n); auto.
Qed.
 
Theorem groundNL2_le : forall a n m, groundNL2 n a -> n <= m -> groundNL2 m a.
intros a n m H; generalize m; elim H; clear H n m; simpl in |- *; auto.
intros a0 l n m H H0 H1 m1 H2.
apply GNVCons2; auto.
apply groundNForm_le with (n := n); auto.
Qed.
 
Theorem scal_groundN :
 forall n a b, groundNExp n a -> groundNExp n (scal b a).
intros n a b H; elim b; simpl in |- *; auto.
intros n0; case n0; auto.
intros n1 H0; apply GNPlus with (n := n) (m := n); auto.
Qed.
Require Import Max.
 
 
Theorem shiftExp_groundN :
 forall n a th i o,
 groundNExp n a -> groundNExp (max (th + i) (n + o)) (shiftExp th i o a).
intros n a th i o H; generalize th i o; elim H; simpl in |- *; auto.
intros i0 n0 H0 th0 i1 o0; generalize (ltdec_correct i0 th0);
 case (ltdec i0 th0); auto.
intros H1; apply groundNExp_le with (S (i0 + i1)); auto with arith.
apply le_trans with (th0 + i1); auto with arith.
intros H1; apply groundNExp_le with (S (i0 + o0)); auto with arith.
apply le_trans with (n0 + o0); auto with arith.
intros a0 b n0 m p H0 H1 H2 H3 H4 H5 th0 i0 o0.
apply
 GNPlus with (n := max (th0 + i0) (n0 + o0)) (m := max (th0 + i0) (m + o0));
 auto with arith.
case (max_Or (th0 + i0) (n0 + o0)); intros H6; rewrite H6; auto with arith.
apply le_trans with (p + o0); auto with arith.
case (max_Or (th0 + i0) (m + o0)); intros H6; rewrite H6; auto with arith.
apply le_trans with (p + o0); auto with arith.
Qed.
 
Theorem shiftForm_groundN :
 forall n a th i o,
 noBinder a ->
 groundNForm n a -> groundNForm (max (th + i) (n + o)) (shiftForm th i o a).
intros n a th i o H; generalize th i o; elim H; simpl in |- *; auto.
intros a0 H0 H1 th0 i0 o0 H2.
inversion H2; auto.
intros a0 b H0 H1 H2 H3 th0 i0 o0 H4.
inversion H4.
apply
 GNAnd with (n := max (th0 + i0) (n + o0)) (m := max (th0 + i0) (n + o0));
 auto.
apply H1.
apply groundNForm_le with (1 := H10); auto.
apply H3.
apply groundNForm_le with (1 := H11); auto.
intros a0 b H0 H1 H2 H3 th0 i0 o0 H4.
inversion H4.
apply GNOr with (n := max (th0 + i0) (n + o0)) (m := max (th0 + i0) (n + o0));
 auto.
apply H1.
apply groundNForm_le with (1 := H10); auto.
apply H3.
apply groundNForm_le with (1 := H11); auto.
intros a0 b H0 H1 H2 H3 th0 i0 o0 H4.
inversion H4.
apply
 GNImp with (n := max (th0 + i0) (n + o0)) (m := max (th0 + i0) (n + o0));
 auto.
apply H1.
apply groundNForm_le with (1 := H10); auto.
apply H3.
apply groundNForm_le with (1 := H11); auto.
intros a0 b th0 i0 o0 H0.
inversion H0.
apply GNEq with (n := max (th0 + i0) (n + o0)) (m := max (th0 + i0) (n + o0));
 auto.
apply shiftExp_groundN; auto.
apply groundNExp_le with (1 := H6); auto.
apply shiftExp_groundN; auto.
apply groundNExp_le with (1 := H7); auto.
intros i1 a0 b th0 i0 o0 H0.
inversion H0.
apply
 GNCong with (n := max (th0 + i0) (n + o0)) (m := max (th0 + i0) (n + o0));
 auto.
apply shiftExp_groundN; auto.
apply groundNExp_le with (1 := H7); auto.
apply shiftExp_groundN; auto.
apply groundNExp_le with (1 := H8); auto.
Qed.
 
Theorem fgrounNExp_correct :
 forall n e,
 match fgroundNExp n e with
 | true => groundNExp n e
 | false => ~ groundNExp n e
 end.
intros n e; elim e; simpl in |- *; auto.
intros i; generalize (ltdec_correct i n); case (ltdec i n); auto.
intros H; Contradict H; inversion H; auto with arith.
intros e1; case (fgroundNExp n e1).
intros H e2; case (fgroundNExp n e2); auto.
intros H0; (apply GNPlus with (n := n) (m := n); auto).
intros H0; Contradict H0; inversion H0; auto.
apply groundNExp_le with (1 := H7); auto.
intros H e2 H0; Contradict H; inversion H; auto.
apply groundNExp_le with (1 := H6); auto.
Qed.
 
Theorem fgrounNForm_correct :
 forall f n,
 match fgroundNForm n f with
 | true => groundNForm n f
 | false => ~ groundNForm n f
 end.
intros f; elim f; clear f; simpl in |- *; auto.
intros f H n; generalize (H (S n)); case (fgroundNForm (S n) f); auto.
intros H0; Contradict H0; inversion H0; auto.
intros f H n; generalize (H (S n)); case (fgroundNForm (S n) f); auto.
intros H0; Contradict H0; inversion H0; auto.
intros f H f0 H0 n; generalize (H n); case (fgroundNForm n f); auto.
generalize (H0 n); case (fgroundNForm n f0); auto.
intros H1 H2; apply GNAnd with (n := n) (m := n); auto.
intros H1 H2; Contradict H1; inversion H1.
apply groundNForm_le with (1 := H9); auto.
intros H1; Contradict H1; inversion H1.
apply groundNForm_le with (1 := H7); auto.
intros f H f0 H0 n; generalize (H n); case (fgroundNForm n f); auto.
generalize (H0 n); case (fgroundNForm n f0); auto.
intros H1 H2; apply GNOr with (n := n) (m := n); auto.
intros H1 H2; Contradict H1; inversion H1.
apply groundNForm_le with (1 := H9); auto.
intros H1; Contradict H1; inversion H1.
apply groundNForm_le with (1 := H7); auto.
intros f H f0 H0 n; generalize (H n); case (fgroundNForm n f); auto.
generalize (H0 n); case (fgroundNForm n f0); auto.
intros H1 H2; apply GNImp with (n := n) (m := n); auto.
intros H1 H2; Contradict H1; inversion H1.
apply groundNForm_le with (1 := H9); auto.
intros H1; Contradict H1; inversion H1.
apply groundNForm_le with (1 := H7); auto.
intros f H n; generalize (H n); case (fgroundNForm n f); auto.
intros H1; Contradict H1; inversion H1; auto.
intros e e0 n; generalize (fgrounNExp_correct n e); case (fgroundNExp n e).
intros H1; generalize (fgrounNExp_correct n e0); case (fgroundNExp n e0);
 auto.
intros H; (apply GNEq with (n := n) (m := n); auto).
intros H; Contradict H; inversion H.
apply groundNExp_le with (1 := H7); auto.
intros H; Contradict H; inversion H.
apply groundNExp_le with (1 := H5); auto.
intros i e e0 n; generalize (fgrounNExp_correct n e); case (fgroundNExp n e).
intros H1; generalize (fgrounNExp_correct n e0); case (fgroundNExp n e0);
 auto.
intros H; (apply GNCong with (n := n) (m := n); auto).
intros H; Contradict H; inversion H.
apply groundNExp_le with (1 := H8); auto.
intros H; Contradict H; inversion H.
apply groundNExp_le with (1 := H6); auto.
Qed.