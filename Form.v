(************************************************************************)
(*                                                                      *)
(*                          Form.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(** * Definition of the datastructure *)
Require Export Cong.
Require Export List.
Require Export ZArith.
Require Export Bool.
Require Import ROmega.
Require Export Classical_Prop.
Require Import Zdivides.
Require Import ZArithRing.
Require Export Nat.
 
(** Expresssion 
   - Numbers
   - Variables
     -- deBrujn indices are used for variables and binders
   - Addition *)
Inductive exp : Set :=
  | Num : nat -> exp
  | Var : nat -> exp
  | Plus : exp -> exp -> exp.
 
(** Formulae :
   - Quantifiers (Forall, Exists)
   - Connectors (And,Or,Impl,Neg)
   - Constants (True,False)
   - Expressions (Eq,Cong)
 *)
Inductive form : Set :=
  | Forall : form -> form
  | Exists : form -> form
  | ANd : form -> form -> form
  | Or : form -> form -> form
  | Imp : form -> form -> form
  | Neg : form -> form
  | TRue : form
  | FAlse : form
  | Eq : exp -> exp -> form
  | Cong : nat -> exp -> exp -> form.

(** Define n.e as e+(n-1).e *)
Fixpoint scal (n : nat) : exp -> exp :=
  fun e =>
  match n with
  | O => Num 0
  | S O => e
  | S n => Plus e (scal n e)
  end.

(** The semantic of expressions:
     - the list l gives the value of the variables (deBrujn indices)
*)
Fixpoint exp2Z (l : list Z) (a : exp) {struct a} : Z :=
  match a with
  | Plus b c => (exp2Z l b + exp2Z l c)%Z
  | Num n => Z_of_nat n
  | Var n => nth n l 0%Z
  end.

(** i.a has the expected semantics *)
Theorem scal_correct :
 forall i a l, exp2Z l (scal i a) = (Z_of_nat i * exp2Z l a)%Z.
intros i a l; elim i; auto.
intros n H; apply trans_equal with (exp2Z l a + exp2Z l (scal n a))%Z.
simpl in |- *; auto.
case n; try ring.
intros n1; simpl in |- *; ring.
rewrite H; rewrite Znat.inj_S; unfold Zsucc in |- *; ring.
Qed.

 
(** The semantic of formulae *) 
Fixpoint form2Prop (l : list Z) (a : form) {struct a} : Prop :=
  match a with
  | Forall b => forall x : Z, form2Prop (x :: l) b
  | Exists b => exists x : Z, form2Prop (x :: l) b
  | ANd b c => form2Prop l b /\ form2Prop l c
  | Or b c => form2Prop l b \/ form2Prop l c
  | Imp b c => form2Prop l b -> form2Prop l c
  | Neg b => ~ form2Prop l b
  | TRue => True
  | FAlse => False
  | Form.Eq b c => exp2Z l b = exp2Z l c
  | Cong i b c => congZ i (exp2Z l b) (exp2Z l c)
  end.

(** A little example *)
Eval compute in (form2Prop nil (Exists (Form.Eq (Var 0) (Num 0)))).


(** Build a conjunction from a list of formulae **)
Fixpoint buildConj (l : list form) : form :=
  match l with
  | nil => TRue
  | e :: nil => e
  | e :: l1 => ANd e (buildConj l1)
  end.
(** Property of buildConj *)
Theorem buildConj_append :
 forall l l1 l2,
 form2Prop l (buildConj (l1 ++ l2)) <->
 form2Prop l (buildConj l1) /\ form2Prop l (buildConj l2).
intros l l1; elim l1; auto.
simpl in |- *; intuition.
intros a l1' Rec l2.
apply iff_trans with (form2Prop l a /\ form2Prop l (buildConj (l1' ++ l2))).
simpl in |- *; case (l1' ++ l2); simpl in |- *; intuition.
apply
 iff_trans
  with
    (form2Prop l a /\
     form2Prop l (buildConj l1') /\ form2Prop l (buildConj l2)).
simpl in |- *; generalize (Rec l2); intuition.
simpl in |- *; case l1'; simpl in |- *; intuition.
Qed.

 
(** Properties of form2Prop *)
Theorem form2Prop_cons :
 forall a l l1,
 form2Prop l1 a ->
 form2Prop l1 (buildConj l) -> form2Prop l1 (buildConj (a :: l)).
intros a l l1 H; simpl in |- *; case l; simpl in |- *; auto.
Qed.
Hint Resolve form2Prop_cons.
 
Theorem form2Prop_app :
 forall l l1 l2,
 form2Prop l (buildConj l1) ->
 form2Prop l (buildConj l2) -> form2Prop l (buildConj (l1 ++ l2)).
intros l l1; elim l1; auto.
intros a l0 H l2 H0 H1;
 change (form2Prop l (buildConj (a :: l0 ++ l2))) in |- *; 
 auto.
apply form2Prop_cons; auto.
generalize H0; case l0; simpl in |- *; auto; intuition.
apply H; auto; generalize H0; case l0; simpl in |- *; auto; intuition.
Qed.
Hint Resolve form2Prop_app.
 
Theorem form2Prop_cons_inv :
 forall a l l1,
 form2Prop l1 (buildConj (a :: l)) ->
 form2Prop l1 a /\ form2Prop l1 (buildConj l).
intros a l l1; simpl in |- *; case l; simpl in |- *; auto.
Qed.
 
Theorem form2Prop_app_inv :
 forall l l1 l2,
 form2Prop l (buildConj (l1 ++ l2)) ->
 form2Prop l (buildConj l1) /\ form2Prop l (buildConj l2).
intros l l1; elim l1; auto.
simpl in |- *; auto.
intros a l0 H l2 H0.
case (form2Prop_cons_inv a (l0 ++ l2) l); auto.
intros H1 H2; case (H l2); auto.
Qed.

 
(** Same as form2Prop but for a list of formulae *)

Fixpoint formL2Prop (c : Z) (l : list Z) (l1 : list (nat * form)) {struct l1} 
   : Prop :=
  match l1 with
  | (n, Form.Eq a b) :: l2 =>
      exp2Z l a = (c * Z_of_nat n + exp2Z l b)%Z /\ formL2Prop c l l2
  | (n, Neg (Form.Eq a b)) :: l2 =>
      exp2Z l a <> (c * Z_of_nat n + exp2Z l b)%Z /\ formL2Prop c l l2
  | (n, Cong i a b) :: l2 =>
      congZ i (exp2Z l a) (c * Z_of_nat n + exp2Z l b) /\ formL2Prop c l l2
  | nil => True
  | _ => False
  end.

(** Property of formL2Prop *)

Theorem formL2Prop_append :
 forall a l l1 l2,
 formL2Prop a l (l1 ++ l2) <-> formL2Prop a l l1 /\ formL2Prop a l l2.
intros a l l1; elim l1; auto.
simpl in |- *; intuition.
intros b l1' Rec l2; simpl in |- *; case b; intros n f; case f;
 try (intuition; fail).
intros f0; case f0; try (intuition; fail).
intros e1 e2; generalize (Rec l2); intuition.
intros e1 e2; generalize (Rec l2); intuition.
intros i e1 e2; generalize (Rec l2); intuition.
Qed.

(** Ground expression  i.e. it contains no variable *)
Inductive groundExp : exp -> Prop :=
  | GNum : forall i : nat, groundExp (Num i)
  | GPlus :
      forall a b : exp, groundExp a -> groundExp b -> groundExp (Plus a b).
 
(** Ground formula i.e. it contains no variable *)
Inductive groundForm : form -> Prop :=
  | GTrue : groundForm TRue
  | GFalse : groundForm FAlse
  | GNeg : forall a : form, groundForm a -> groundForm (Neg a)
  | GAnd :
      forall a b : form, groundForm a -> groundForm b -> groundForm (ANd a b)
  | GOr :
      forall a b : form, groundForm a -> groundForm b -> groundForm (Or a b)
  | GImp :
      forall a b : form, groundForm a -> groundForm b -> groundForm (Imp a b)
  | GEq :
      forall a b : exp,
      groundExp a -> groundExp b -> groundForm (Form.Eq a b)
  | GCong :
      forall (i : nat) (a b : exp),
      groundExp a -> groundExp b -> groundForm (Cong i a b).
 
(** A ground expression can be evaluated in an empty context *)
Theorem exp2Z_ground :
 forall (l : list Z) (e : exp), groundExp e -> exp2Z nil e = exp2Z l e.
intros l e H; elim H; simpl in |- *; auto.
intros a b H0 H1 H2 H3; rewrite H1; rewrite H3; auto.
Qed.
 
(** An algorithm to decide ground formulae 
    - Take a formula that is known to be ground
    - Returns a boolean
*)
Fixpoint decideGround (a : form) : bool :=
  match a with
  | Forall b => false
  | Exists b => false
  | ANd b c => decideGround b && decideGround c
  | Or b c => decideGround b || decideGround c
  | Imp b c => implb (decideGround b) (decideGround c)
  | Neg b => negb (decideGround b)
  | TRue => true
  | FAlse => false
  | Form.Eq b c => Z_eq_bool (exp2Z nil b) (exp2Z nil c)
  | Cong i b c =>
      match congZ_dec i (exp2Z nil b) (exp2Z nil c) with
      | left _ => true
      | _ => false
      end
  end.

(** decideGround is correct and complete on ground formulae *)
Theorem decideCorrect :
 forall f : form,
 groundForm f ->
 match decideGround f with
 | true => form2Prop nil f
 | false => ~ form2Prop nil f
 end.
intros f H; elim H; simpl in |- *; try (intros; discriminate); auto.
intros a H0; case (decideGround a); simpl in |- *; try (intros; discriminate);
 auto.
intros a b H0; case (decideGround a); simpl in |- *;
 try (intros; discriminate); auto.
intros H1 H2; case (decideGround b); simpl in |- *;
 try (intros; discriminate); auto.
intros H3 (H4, H5); case H3; auto.
intros H1 H2; case (decideGround b); simpl in |- *;
 try (intros; discriminate); auto.
intros H3 (H4, H5); case H1; auto.
intros H3 (H4, H5); case H3; auto.
intros a b H0; case (decideGround a); simpl in |- *;
 try (intros; discriminate); auto.
intros H1 H2; case (decideGround b); simpl in |- *;
 try (intros; discriminate); auto.
intros H3 [H4| H4]; [ case H1 | case H3 ]; auto.
intros a b H0; case (decideGround a); simpl in |- *;
 try (intros; discriminate); auto.
intros H1 H2; case (decideGround b); simpl in |- *;
 try (intros; discriminate); auto.
intros H1 H2; case (decideGround b); simpl in |- *;
 try (intros; discriminate); auto.
intros H3 H4; case H1; auto.
intros a b Ha Hb; generalize (Z_eq_bool_correct (exp2Z nil a) (exp2Z nil b));
 case (Z_eq_bool (exp2Z nil a) (exp2Z nil b)); auto.
intros i a b Ha Hb; case (congZ_dec i (exp2Z nil a) (exp2Z nil b)); auto.
Qed.
 
(** shift deBrujn indices for expressions
   - Variables under [th] are lifted of [i]
   - Variables over [th] are lifted of [o]
*)
Fixpoint shiftExp (th i o : nat) (a : exp) {struct a} : exp :=
  match a with
  | Plus b c => Plus (shiftExp th i o b) (shiftExp th i o c)
  | Num n => Num n
  | Var n =>
      match ltdec n th with
      | true => Var (n + i)
      | false => Var (n + o)
      end
  end.
 
(** shift deBrujn indices for formulae
   - Variables under [th] are lifted of [i]
   - Variables over [th] are lifted of [o]
*)
Fixpoint shiftForm (th i o : nat) (a : form) {struct a} : form :=
  match a with
  | Forall b => Forall b
  | Exists b => Exists b
  | ANd b c => ANd (shiftForm th i o b) (shiftForm th i o c)
  | Or b c => Or (shiftForm th i o b) (shiftForm th i o c)
  | Imp b c => Imp (shiftForm th i o b) (shiftForm th i o c)
  | Neg b => Neg (shiftForm th i o b)
  | TRue => TRue
  | FAlse => FAlse
  | Form.Eq b c => Form.Eq (shiftExp th i o b) (shiftExp th i o c)
  | Cong i1 b c => Cong i1 (shiftExp th i o b) (shiftExp th i o c)
  end.
 
(** A formula with noBinder  *)
Inductive noBinder : form -> Prop :=
  | nBTrue : noBinder TRue
  | nBFalse : noBinder FAlse
  | nBNeg : forall a : form, noBinder a -> noBinder (Neg a)
  | nBAnd : forall a b : form, noBinder a -> noBinder b -> noBinder (ANd a b)
  | nBOr : forall a b : form, noBinder a -> noBinder b -> noBinder (Or a b)
  | nBImp : forall a b : form, noBinder a -> noBinder b -> noBinder (Imp a b)
  | nBEq : forall a b : exp, noBinder (Form.Eq a b)
  | nBCong : forall (i : nat) (a b : exp), noBinder (Cong i a b).
Hint Constructors noBinder.

 
(** A list of pairs of integer and equations *)
Inductive listEqP : list (nat * form) -> Prop :=
  | listEqPnil : listEqP nil
  | listEqPcons :
      forall n a b l, 0 < n -> listEqP l -> listEqP ((n, Form.Eq a b) :: l).

(** A list of pairs of integer and inequations *)
Inductive listNEqP : list (nat * form) -> Prop :=
  | listNEqPnil : listNEqP nil
  | listNEqPcons :
      forall n a b l,
      0 < n -> listNEqP l -> listNEqP ((n, Neg (Form.Eq a b)) :: l).

(** A list of pairs of integer and congruence *)
Inductive listCongP : list (nat * form) -> Prop :=
  | listCongPnil : listCongP nil
  | listCongPcons :
      forall n i a b l,
      0 < i -> 0 < n -> listCongP l -> listCongP ((n, Cong i a b) :: l).

Hint Constructors listEqP.
Hint Constructors listCongP.
Hint Constructors listNEqP.

(** Some properties of lists *)
Theorem listEq_app :
 forall l1 l2, listEqP l1 -> listEqP l2 -> listEqP (l1 ++ l2).
intros l1 l2 H1 H2; elim H1; simpl in |- *; auto.
Qed.
 
Theorem listNeq_app :
 forall l1 l2, listNEqP l1 -> listNEqP l2 -> listNEqP (l1 ++ l2).
intros l1 l2 H1 H2; elim H1; simpl in |- *; auto.
Qed.
 
Theorem listCong_app :
 forall l1 l2, listCongP l1 -> listCongP l2 -> listCongP (l1 ++ l2).
intros l1 l2 H1 H2; elim H1; simpl in |- *; auto.
Qed.
Hint Resolve listEq_app listNeq_app listCong_app.