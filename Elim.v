(************************************************************************)
(*                                                                      *)
(*                          Elim.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
Require Import List.
Require Import Normal.
Require Import Nat.
Require Import ZArithRing.
Require Import sTactic.
Require Import Sort.
Require Import Process.
Require Import GroundN.

(** Elim one quantifier *) 
Fixpoint elimQuant (f : form) : form :=
  match f with
  | Or f1 f2 => Or (elimQuant f1) (elimQuant f2)
  | _ => buildConj (processList (sortAnd f))
  end.
 
Theorem elimQuant_correct :
 forall l f,
 Cnf f ->
 ((exists a : _, form2Prop (a :: l) f) <-> form2Prop l (elimQuant f)) /\
 Cnf (elimQuant f).
intros l f H; elim H; clear H f; simpl in |- *.
2: intros a b H (H1, H2) H3 (H4, H5); split; auto.
2: split.
2: intros (m6, [H6| H6]);
    [ case H1; intros H7 H8; left | case H4; intros H7 H8; right ]; 
    apply H7; exists m6; auto.
2: intros [H6| H6]; [ case H1 | case H4 ]; intros H7 H8; case H8; auto;
    intros m9 H9; exists m9; auto.
intros a H; replace (elimQuant a) with (buildConj (processList (sortAnd a)));
 [ idtac | inversion H; auto; inversion H0; auto ].
split.
split.
intros (c, H1).
generalize (sortAnd_correct (c :: l) a H).
case (sortAnd a).
intros l1 p; case p; clear p.
intros l2 p; case p; clear p.
intros l3 l4.
intros (H2, (Z1, (Z2, (Z3, Z4)))); case H2; auto; clear H2; intros H2 H3;
 case H2; auto.
intros H4 (H5, (H6, H7)).
simpl in H4, H5, H6, H7.
case (processList_correct l l1 l2 l3 l4); auto.
intros (H8, H9) H10; apply H8.
exists c; auto.
CaseEq (sortAnd a).
intros l1 p; case p; clear p.
intros l2 p; case p; clear p.
intros l3 l4.
intros Z1; case (processList_correct l l1 l2 l3 l4); auto.
generalize (sortAnd_correct l a H); rewrite Z1; intuition.
generalize (sortAnd_correct l a H); rewrite Z1; intuition.
generalize (sortAnd_correct l a H); rewrite Z1; intuition.
generalize (sortAnd_correct l a H); rewrite Z1; intuition.
intros H0 H1 H2.
case H0.
intros H3 H4; case H4; auto.
intros m5 (H5, (H6, (H7, H8))); exists m5.
generalize (sortAnd_correct (m5 :: l) a H); rewrite Z1.
simpl in |- *; intuition.
generalize (sortAnd_correct l a H).
case (sortAnd a).
intros l1 p; case p; clear p.
intros l2 p; case p; clear p.
intros l3 l4.
intros (H1, (H2, (H3, (H4, H5)))).
case (processList_correct l l1 l2 l3 l4); auto.
Qed.
 
Theorem groundNL_groundNForm :
 forall a n, groundNL n a -> groundNForm n (buildConj a).
intros a n H; elim H; simpl in |- *; auto.
intros a0 l; case l; auto.
intros f l0 n0 H0 H1 H2; (apply GNAnd with (n := n0) (m := n0); auto).
Qed.
 
Theorem elimQuant_groundN :
 forall n f, Cnf f -> groundNForm n f -> groundNForm (pred n) (elimQuant f).
intros n f H; generalize n; elim H; clear H f n; simpl in |- *; auto.
intros a H1; elim H1; simpl in |- *; auto.
intros a1 H2; elim H2; unfold elimQuant in |- *; lazy beta in |- *; auto.
intros a0 b n H0; cut (Cnf1 (Form.Eq a0 b)); auto; intros H3.
generalize (sortAnd_correct nil (Form.Eq a0 b) H3);
 generalize (sortAnd_groundN n (Form.Eq a0 b) H3 H0);
 case (sortAnd (Form.Eq a0 b)).
intros l1 p; case p; clear p.
intros l2 p; case p; clear p.
intros l3 l4 (H4, (H5, (H6, H7))) (H8, (H9, (H10, (H11, H12)))).
apply groundNL_groundNForm; auto.
apply processList_groundN; auto.
intros a0 b n H0; cut (Cnf1 (Neg (Form.Eq a0 b))); auto; intros H3.
generalize (sortAnd_correct nil (Neg (Form.Eq a0 b)) H3);
 generalize (sortAnd_groundN n (Neg (Form.Eq a0 b)) H3 H0);
 case (sortAnd (Neg (Form.Eq a0 b))).
intros l1 p; case p; clear p.
intros l2 p; case p; clear p.
intros l3 l4 (H4, (H5, (H6, H7))) (H8, (H9, (H10, (H11, H12)))).
apply groundNL_groundNForm; auto.
apply processList_groundN; auto.
intros i a0 b n H0; cut (Cnf1 (Cong i a0 b)); auto; intros H3.
generalize (sortAnd_correct nil (Cong i a0 b) H3);
 generalize (sortAnd_groundN n (Cong i a0 b) H3 H0);
 case (sortAnd (Cong i a0 b)).
intros l1 p; case p; clear p.
intros l2 p; case p; clear p.
intros l3 l4 (H4, (H5, (H6, H7))) (H8, (H9, (H10, (H11, H12)))).
apply groundNL_groundNForm; auto.
apply processList_groundN; auto.
intros a0 b H H0 H2 H3 n H4.
inversion H4.
generalize (sortAnd_correct nil a0 H);
 generalize (sortAnd_groundN n0 a0 H H10); case (sortAnd a0).
intros l1 p0; case p0; clear p0.
intros l2 p0; case p0; clear p0.
intros l3 l4 (H13, (H14, (H15, H16))) (H17, (H18, (H19, (H20, H21)))).
generalize (sortAnd_correct nil b H2);
 generalize (sortAnd_groundN m b H2 H11); case (sortAnd b).
intros l'1 p0; case p0; clear p0.
intros l'2 p0; case p0; clear p0.
intros l'3 l'4 (H'13, (H'14, (H'15, H'16)))
 (H'17, (H'18, (H'19, (H'20, H'21)))).
apply groundNL_groundNForm; auto.
apply processList_groundN; auto.
apply groundNL_app.
apply groundNL_le with (n := pred n0); auto with arith.
apply groundNL_le with (n := pred m); auto with arith.
apply groundNL2_app.
apply groundNL2_le with (n := pred n0); auto with arith.
apply groundNL2_le with (n := pred m); auto with arith.
apply groundNL2_app.
apply groundNL2_le with (n := pred n0); auto with arith.
apply groundNL2_le with (n := pred m); auto with arith.
apply groundNL2_app.
apply groundNL2_le with (n := pred n0); auto with arith.
apply groundNL2_le with (n := pred m); auto with arith.
intros a b H H0 H1 H2 n H3; inversion H3; auto.
apply GNOr with (n := pred n0) (m := pred m); auto with arith.
Qed.
 
(** Elim all quantifiers  *) 
Fixpoint elimQuants (f : form) : form :=
  match f with
  | Exists f1 => elimQuant (elimQuants f1)
  | Neg (Exists f1) => cnf (Neg (elimQuant (elimQuants f1)))
  | _ => f
  end.
 
Theorem cnf_noBinder : forall f, Cnf f -> noBinder f.
intros f H; elim H; simpl in |- *; auto.
intros a H1; elim H1; simpl in |- *; auto.
intros a1 H2; elim H2; simpl in |- *; auto.
Qed.
 
Theorem elimQuants_correct :
 forall l f,
 Normal f ->
 (form2Prop l f <-> form2Prop l (elimQuants f)) /\ Cnf (elimQuants f).
intros l f H; generalize l; elim H; clear H l f; simpl in |- *; auto.
intros a H H0 l; split.
case (elimQuant_correct l (elimQuants a)); auto.
case (H0 l); auto.
intros H1 H2; apply iff_trans with (2 := H1).
split; intros (m3, H3); exists m3; case (H0 (m3 :: l)); intuition.
case (elimQuant_correct l (elimQuants a)); auto.
case (H0 l); auto.
intros a H H0 l; split.
generalize (cnf_correct (Neg (elimQuant (elimQuants a)))); simpl in |- *.
intros H1; apply iff_sym; apply iff_trans with (1 := H1 l).
cut
 (ex (fun x : Z => form2Prop (x :: l) a) <->
  form2Prop l (elimQuant (elimQuants a))).
intros (H2, H3); split; intros H4; Contradict H4; auto.
case (elimQuant_correct l (elimQuants a)); auto.
case (H0 l); auto.
intros H2 H3; apply iff_trans with (2 := H2).
split; intros (m4, H4); exists m4; case (H0 (m4 :: l)); intuition.
apply cnf_cnf.
apply noBinder_Neg.
apply cnf_noBinder.
case (elimQuant_correct l (elimQuants a)); auto.
case (H0 l); auto.
intros a H l; replace (elimQuants a) with a; auto.
intuition.
elim H; simpl in |- *; auto.
intros a0 H0; elim H0; simpl in |- *; auto.
intros a1 H1; elim H1; simpl in |- *; auto.
Qed.
Hint Constructors groundForm.
 
Theorem elimQuants_groundN :
 forall n f, Normal f -> groundNForm n f -> groundNForm n (elimQuants f).
intros n f H; generalize n; elim H; simpl in |- *; auto.
intros a H0 H1 n0 H2; replace n0 with (pred (S n0));
 [ apply elimQuant_groundN | idtac ]; auto.
case (elimQuants_correct nil a); simpl in |- *; auto.
apply H1; inversion H2; auto.
intros a H0 H1 n0 H2.
apply cnf_groundN; auto.
apply GNNeg; auto.
replace n0 with (pred (S n0)); auto.
apply elimQuant_groundN; auto.
case (elimQuants_correct nil a); simpl in |- *; auto.
apply H1; auto.
simpl in H2; inversion H2.
simpl in H5; inversion H5; auto.
intros a H1; elim H1; simpl in |- *; auto.
intros a1 H2; elim H2; simpl in |- *; auto.
intros a3 H3; elim H3; simpl in |- *; auto.
Qed.
 
Theorem groundNForm_Cnf_groundForm_aux :
 forall f, Cnf f -> groundNForm 0 f -> groundForm f.
intros f H; elim H; simpl in |- *; auto; clear H f.
intros f H; elim H; simpl in |- *; auto; clear H f.
intros f H; elim H; simpl in |- *; auto; clear H f.
intros a b H; inversion H.
apply GEq.
cut (n = 0).
elim H5; auto.
intros i n0 H7 H8; Contradict H7; rewrite H8; auto with arith.
intros a1 b1 n0 m0 p0 H7 H8 H9 H10 H11 H12 H13; cut (n0 = 0);
 [ cut (m0 = 0) | idtac ]; auto.
rewrite H13 in H8; inversion H8; auto.
rewrite H13 in H7; inversion H7; auto.
inversion H2; auto.
inversion H2; auto.
clear H7; cut (m = 0).
elim H6; auto.
intros i n0 H7 H8; Contradict H7; rewrite H8; auto with arith.
intros a1 b1 n0 m0 p0 H7 H8 H9 H10 H11 H12 H13; cut (n0 = 0);
 [ cut (m0 = 0) | idtac ]; auto.
rewrite H13 in H8; inversion H8; auto.
rewrite H13 in H7; inversion H7; auto.
inversion H3; auto.
intros a b H; inversion H.
apply GNeg.
inversion H2; auto.
apply GEq.
cut (n0 = 0).
elim H8; auto.
intros i n1 H10 H11; Contradict H10; rewrite H11; auto with arith.
intros a2 b1 n1 m0 p0 H10 H11 H12 H13 H14 H15 H16; cut (n1 = 0);
 [ cut (m0 = 0) | idtac ]; auto.
rewrite H16 in H11; inversion H11; auto.
rewrite H16 in H10; inversion H10; auto.
inversion H5; auto.
cut (m = 0).
elim H9; auto.
intros i n1 H10 H11; Contradict H10; rewrite H11; auto with arith.
intros a2 b1 n1 m0 p0 H10 H11 H12 H13 H14 H15 H16; cut (n1 = 0);
 [ cut (m0 = 0) | idtac ]; auto.
rewrite H16 in H11; inversion H11; auto.
rewrite H16 in H10; inversion H10; auto.
inversion H6; auto.
intros i a b H; inversion H.
apply GCong.
cut (n = 0).
elim H6; auto.
intros i1 n1 H10 H11; Contradict H10; rewrite H11; auto with arith.
intros a2 b1 n1 m0 p0 H10 H11 H12 H13 H14 H15 H16; cut (n1 = 0);
 [ cut (m0 = 0) | idtac ]; auto.
rewrite H16 in H11; inversion H11; auto.
rewrite H16 in H10; inversion H10; auto.
inversion H3; auto.
cut (m = 0).
elim H7; auto.
intros i1 n1 H10 H11; Contradict H10; rewrite H11; auto with arith.
intros a2 b1 n1 m0 p0 H10 H11 H12 H13 H14 H15 H16; cut (n1 = 0);
 [ cut (m0 = 0) | idtac ]; auto.
rewrite H16 in H11; inversion H11; auto.
rewrite H16 in H10; inversion H10; auto.
inversion H5; auto.
intros a b H H0 H1 H2 H3; inversion H3.
generalize H9 H10; inversion H6; inversion H7; auto.
intros a b H H0 H1 H2 H3; inversion H3.
generalize H9 H10; inversion H6; inversion H7; auto.
Qed.
 
(** Presbuger: first Normal Form, then Elim Quant and finally Decide *)
Definition presburger f := decideGround (elimQuants (normalForm f)).
 
Theorem presburger_correct :
 forall f,
 groundNForm 0 f ->
 match presburger f with
 | true => form2Prop nil f
 | false => ~ form2Prop nil f
 end.
intros f H; CaseEq (presburger f); intros H1.
case (normalForm_correct f nil); intros H2 H3; apply H2; clear H2 H3.
generalize (normal_normal f); intros Z1.
case (elimQuants_correct nil (normalForm f) Z1); intros (H2, H3) H4; apply H3;
 clear H2 H3.
cut (groundForm (elimQuants (normalForm f))); [ intros Z2 | idtac ].
generalize (decideCorrect (elimQuants (normalForm f)) Z2); auto.
unfold presburger in H1; rewrite H1; auto.
apply groundNForm_Cnf_groundForm_aux; auto.
apply elimQuants_groundN; auto.
apply normalForm_groundN; auto.
cut (~ form2Prop nil (normalForm f)); [ intros Z0; Contradict Z0 | idtac ].
generalize (normal_normal f); intros Z1.
case (normalForm_correct f nil); intros H2 H3; apply H3; clear H2 H3; auto.
cut (~ form2Prop nil (elimQuants (normalForm f)));
 [ intros Z0; Contradict Z0 | idtac ].
generalize (normal_normal f); intros Z1.
case (elimQuants_correct nil (normalForm f) Z1); intros (H2, H3) H4; auto.
generalize (normal_normal f); intros Z1.
case (elimQuants_correct nil (normalForm f) Z1); intros (H2, H3) H4; auto.
cut (groundForm (elimQuants (normalForm f))); [ intros Z2 | idtac ].
generalize (decideCorrect (elimQuants (normalForm f)) Z2); auto.
unfold presburger in H1; rewrite H1; auto.
apply groundNForm_Cnf_groundForm_aux; auto.
apply elimQuants_groundN; auto.
apply normalForm_groundN; auto.
Qed.

(** An example *)
Eval compute in
  (presburger
     (Forall
        (Or (Exists (Form.Eq (Var 1) (Plus (Var 0) (Var 0))))
           (Exists (Form.Eq (Var 1) (Plus (Plus (Var 0) (Var 0)) (Num 1))))))).

(** Using it to do proofs using reflexion *) 
Theorem OddEven :
 forall x : Z,
 (exists y : Z, x = (y + y)%Z) \/ (exists y : Z, x = (y + y + 1)%Z).
exact
 (presburger_correct _
    (fgrounNForm_correct
       (Forall
          (Or (Exists (Form.Eq (Var 1) (Plus (Var 0) (Var 0))))
             (Exists (Form.Eq (Var 1) (Plus (Plus (Var 0) (Var 0)) (Num 1))))))
       0)).
Qed.
 
Theorem NOddEven :
 forall x : Z,
 ~ ((exists y : Z, x = (y + y)%Z) /\ (exists y : Z, x = (y + y + 1)%Z)).
exact
 (presburger_correct _
    (fgrounNForm_correct
       (Forall
          (Neg
             (ANd (Exists (Form.Eq (Var 1) (Plus (Var 0) (Var 0))))
                (Exists
                   (Form.Eq (Var 1) (Plus (Plus (Var 0) (Var 0)) (Num 1)))))))
       0)).
Qed.