(************************************************************************)
(*                                                                      *)
(*                      ReduceEq.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(** Reduce with an equality *)
Require Import List.
Require Import Normal.
Require Import Nat.
Require Import ZArithRing.
Require Import sTactic.
Require Import GroundN.

(** Reduce an equality with an equality 
    - [a1=b1+m1.x /\ a2=b2+m2.x] gives [a1=b1+m1.x /\ n2.a2+n1.b1=n2.b2+n1.a1]
*) 
Fixpoint reduceEqEq (m1 : nat) (a1 b1 : exp) (l : list (nat * form))
 {struct l} : list form :=
  match l with
  | (m2, Form.Eq a2 b2) :: l1 =>
      match lcm m1 m2 with
      | m3 =>
          match div m3 m1 with
          | n1 =>
              match div m3 m2 with
              | n2 =>
                  Form.Eq (Plus (scal n1 b1) (scal n2 a2))
                    (Plus (scal n1 a1) (scal n2 b2))
                  :: reduceEqEq m1 a1 b1 l1
              end
          end
      end
  | _ => nil
  end.
 
Theorem reduceEqEq_correct :
 forall m1 a b l l1,
 0 < m1 ->
 listEqP l1 ->
 (exp2Z (tail l) a = (nth 0 l 0 * Z_of_nat m1 + exp2Z (tail l) b)%Z /\
  formL2Prop (nth 0 l 0%Z) (tail l) l1 <->
  exp2Z (tail l) a = (nth 0 l 0 * Z_of_nat m1 + exp2Z (tail l) b)%Z /\
  form2Prop (tail l) (buildConj (reduceEqEq m1 a b l1))) /\
 Cnf1 (buildConj (reduceEqEq m1 a b l1)).
intros m1 a b l l1 H H0; elim H0; clear H0 l1; simpl in |- *; auto.
intuition.
intros n a0 b0 l0 H0 H1; case (reduceEqEq m1 a b l0).
simpl in |- *; repeat rewrite scal_correct.
intros (H2, H2'); split; auto; split.
intros (H3, (H4, H5)); split; auto.
rewrite H3; rewrite H4.
apply
 trans_equal
  with
    (Z_of_nat (div (lcm m1 n) m1) * exp2Z (tail l) b +
     (Z_of_nat (div (lcm m1 n) n) * (nth 0 l 0 * Z_of_nat n) +
      Z_of_nat (div (lcm m1 n) n) * exp2Z (tail l) b0))%Z.
ring; auto.
replace (Z_of_nat (div (lcm m1 n) n) * (nth 0 l 0 * Z_of_nat n))%Z with
 (Z_of_nat (div (lcm m1 n) m1) * (nth 0 l 0 * Z_of_nat m1))%Z.
ring; auto.
cut (forall a b c, (a * (b * c))%Z = (a * c * b)%Z);
 [ intros H6; repeat rewrite H6 | intros; ring ].
repeat rewrite <- Znat.inj_mult;
 repeat rewrite (fun y z => mult_comm (div y z));
 repeat rewrite <- divides_div; auto.
apply divides_lcm2; auto.
apply divides_lcm1; auto.
intros (H3, H4); split; [ idtac | split ]; auto.
apply Zeq_mult_simpl with (c := Z_of_nat (div (lcm m1 n) n)).
apply Compare.not_eq_sym; apply Zorder.Zlt_not_eq.
replace 0%Z with (Z_of_nat 0); [ apply Znat.inj_lt | simpl in |- *; auto ].
cut (lcm m1 n = n * div (lcm m1 n) n :>nat).
case (div (lcm m1 n) n); auto with arith.
rewrite mult_comm; simpl in |- *; intros H5; Contradict H5.
apply Compare.not_eq_sym; apply lt_O_neq; apply lcm_lt_O; auto.
apply divides_div; auto.
apply divides_lcm2; auto.
rewrite (fun a l => Zmult_comm (exp2Z l a)).
apply
 Zplus_reg_l with (n := (Z_of_nat (div (lcm m1 n) m1) * exp2Z (tail l) b)%Z).
rewrite H4.
rewrite H3.
replace
 ((nth 0 l 0 * Z_of_nat n + exp2Z (tail l) b0) * Z_of_nat (div (lcm m1 n) n))%Z
 with
 (exp2Z (tail l) b0 * Z_of_nat (div (lcm m1 n) n) +
  Z_of_nat n * Z_of_nat (div (lcm m1 n) n) * nth 0 l 0)%Z;
 [ rewrite <- Znat.inj_mult; rewrite <- divides_div; auto | ring ].
replace
 (Z_of_nat (div (lcm m1 n) m1) * (nth 0 l 0 * Z_of_nat m1 + exp2Z (tail l) b))%Z
 with
 (exp2Z (tail l) b * Z_of_nat (div (lcm m1 n) m1) +
  Z_of_nat m1 * Z_of_nat (div (lcm m1 n) m1) * nth 0 l 0)%Z;
 [ rewrite <- Znat.inj_mult; rewrite <- divides_div; auto | ring ].
ring.
apply divides_lcm1; auto.
apply divides_lcm2; auto.
intuition.
intros f l1 (H2, H2'); split; auto.
split.
intros (H3, (H4, H5)); split; auto.
change
  (form2Prop (tail l)
     (Form.Eq
        (Plus (scal (div (lcm m1 n) m1) b) (scal (div (lcm m1 n) n) a0))
        (Plus (scal (div (lcm m1 n) m1) a) (scal (div (lcm m1 n) n) b0))) /\
   form2Prop (tail l) (buildConj (f :: l1))) in |- *.
split; [ idtac | intuition ].
simpl in |- *; repeat rewrite scal_correct.
rewrite H3; rewrite H4.
replace
 (Z_of_nat (div (lcm m1 n) n) * (nth 0 l 0 * Z_of_nat n + exp2Z (tail l) b0))%Z
 with
 (Z_of_nat n * Z_of_nat (div (lcm m1 n) n) * nth 0 l 0 +
  Z_of_nat (div (lcm m1 n) n) * exp2Z (tail l) b0)%Z;
 [ rewrite <- Znat.inj_mult; rewrite <- divides_div; auto | ring ].
replace
 (Z_of_nat (div (lcm m1 n) m1) * (nth 0 l 0 * Z_of_nat m1 + exp2Z (tail l) b))%Z
 with
 (Z_of_nat m1 * Z_of_nat (div (lcm m1 n) m1) * nth 0 l 0 +
  Z_of_nat (div (lcm m1 n) m1) * exp2Z (tail l) b)%Z;
 [ rewrite <- Znat.inj_mult; rewrite <- divides_div; auto | ring ].
ring; auto.
apply divides_lcm1; auto.
apply divides_lcm2; auto.
intros (H3, H4); split; auto; split.
cut
 (form2Prop (tail l)
    (Form.Eq (Plus (scal (div (lcm m1 n) m1) b) (scal (div (lcm m1 n) n) a0))
       (Plus (scal (div (lcm m1 n) m1) a) (scal (div (lcm m1 n) n) b0))));
 [ simpl in |- *; repeat rewrite scal_correct; intros H5
 | generalize H4; simpl in |- *; intros (H5, H6); auto ].
apply Zeq_mult_simpl with (c := Z_of_nat (div (lcm m1 n) n)).
apply Compare.not_eq_sym; apply Zorder.Zlt_not_eq.
replace 0%Z with (Z_of_nat 0); [ apply Znat.inj_lt | simpl in |- *; auto ].
cut (lcm m1 n = n * div (lcm m1 n) n :>nat).
case (div (lcm m1 n) n); auto with arith.
rewrite mult_comm; simpl in |- *; intros H6; Contradict H6.
apply Compare.not_eq_sym; apply lt_O_neq; apply lcm_lt_O; auto.
apply divides_div; auto.
apply divides_lcm2; auto.
rewrite (fun a l => Zmult_comm (exp2Z l a)).
apply
 Zplus_reg_l with (n := (Z_of_nat (div (lcm m1 n) m1) * exp2Z (tail l) b)%Z).
rewrite H5.
rewrite H3.
replace
 ((nth 0 l 0 * Z_of_nat n + exp2Z (tail l) b0) * Z_of_nat (div (lcm m1 n) n))%Z
 with
 (exp2Z (tail l) b0 * Z_of_nat (div (lcm m1 n) n) +
  Z_of_nat n * Z_of_nat (div (lcm m1 n) n) * nth 0 l 0)%Z;
 [ rewrite <- Znat.inj_mult; rewrite <- divides_div; auto | ring ].
replace
 (Z_of_nat (div (lcm m1 n) m1) * (nth 0 l 0 * Z_of_nat m1 + exp2Z (tail l) b))%Z
 with
 (exp2Z (tail l) b * Z_of_nat (div (lcm m1 n) m1) +
  Z_of_nat m1 * Z_of_nat (div (lcm m1 n) m1) * nth 0 l 0)%Z;
 [ rewrite <- Znat.inj_mult; rewrite <- divides_div; auto | ring ].
ring.
apply divides_lcm1; auto.
apply divides_lcm2; auto.
cut (form2Prop (tail l) (buildConj (f :: l1)));
 [ intuition | generalize H4; simpl in |- *; intros (H5, H6); auto ].
Qed.

 
Theorem reduceEqEq_groundN :
 forall n m1 a b l,
 listEqP l ->
 groundNL2 n l ->
 groundNExp n a -> groundNExp n b -> groundNL n (reduceEqEq m1 a b l).
intros n m1 a b l H; generalize n m1 a b; elim H; clear H n m1 a b;
 simpl in |- *; auto.
intros n a b l0 H H0 H1 n0 m1 a0 b0 H2 H3 H4.
apply GNVCons; auto.
inversion H2.
inversion H8.
apply GNEq with (n := n0) (m := n0); auto.
apply GNPlus with (n := n0) (m := n2); auto.
apply scal_groundN; auto.
apply scal_groundN; auto.
apply GNPlus with (n := n0) (m := m0); auto.
apply scal_groundN; auto.
apply scal_groundN; auto.
apply H1 with (n := n0); auto.
inversion H2; auto.
Qed.

(** Reduce an inequality with an equality 
    - [a1=b1+m1.x /\ ~(a2=b2+m2.x)] gives [a1=b1+m1.x /\ ~(n2.a2+n1.b1=n2.b2+n1.a1)]
*) 
Fixpoint reduceEqNEq (m1 : nat) (a1 b1 : exp) (l : list (nat * form))
 {struct l} : list form :=
  match l with
  | (m2, Neg (Form.Eq a2 b2)) :: l1 =>
      match lcm m1 m2 with
      | m3 =>
          match div m3 m1 with
          | n1 =>
              match div m3 m2 with
              | n2 =>
                  Neg
                    (Form.Eq (Plus (scal n1 b1) (scal n2 a2))
                       (Plus (scal n1 a1) (scal n2 b2)))
                  :: reduceEqNEq m1 a1 b1 l1
              end
          end
      end
  | _ => nil
  end.
 
Theorem reduceEqNEq_correct :
 forall m1 a b l l1,
 0 < m1 ->
 listNEqP l1 ->
 (exp2Z (tail l) a = (nth 0 l 0 * Z_of_nat m1 + exp2Z (tail l) b)%Z /\
  formL2Prop (nth 0 l 0%Z) (tail l) l1 <->
  exp2Z (tail l) a = (nth 0 l 0 * Z_of_nat m1 + exp2Z (tail l) b)%Z /\
  form2Prop (tail l) (buildConj (reduceEqNEq m1 a b l1))) /\
 Cnf1 (buildConj (reduceEqNEq m1 a b l1)).
intros m1 a b l l1 H H0; elim H0; clear H0 l1; simpl in |- *; auto.
intuition.
intros n a0 b0 l0 H0 H1; case (reduceEqNEq m1 a b l0).
simpl in |- *; repeat rewrite scal_correct.
intros (H2, H2'); split; auto; split.
intros (H3, (H4, H5)); split; auto.
rewrite H3; Contradict H4.
apply Zeq_mult_simpl with (c := Z_of_nat (div (lcm m1 n) n)).
apply Compare.not_eq_sym; apply Zorder.Zlt_not_eq.
replace 0%Z with (Z_of_nat 0); [ apply Znat.inj_lt | simpl in |- *; auto ].
cut (lcm m1 n = n * div (lcm m1 n) n :>nat).
case (div (lcm m1 n) n); auto with arith.
rewrite mult_comm; simpl in |- *; intros H6; Contradict H6.
apply Compare.not_eq_sym; apply lt_O_neq; apply lcm_lt_O; auto.
apply divides_div; auto.
apply divides_lcm2; auto.
rewrite (fun a l => Zmult_comm (exp2Z l a)).
apply
 Zplus_reg_l with (n := (Z_of_nat (div (lcm m1 n) m1) * exp2Z (tail l) b)%Z).
rewrite H4.
replace
 (Z_of_nat (div (lcm m1 n) m1) * (nth 0 l 0 * Z_of_nat m1 + exp2Z (tail l) b))%Z
 with
 (Z_of_nat m1 * Z_of_nat (div (lcm m1 n) m1) * nth 0 l 0 +
  Z_of_nat (div (lcm m1 n) m1) * exp2Z (tail l) b)%Z;
 [ rewrite <- Znat.inj_mult; rewrite <- divides_div; auto | ring ].
replace
 ((nth 0 l 0 * Z_of_nat n + exp2Z (tail l) b0) * Z_of_nat (div (lcm m1 n) n))%Z
 with
 (Z_of_nat n * Z_of_nat (div (lcm m1 n) n) * nth 0 l 0 +
  Z_of_nat (div (lcm m1 n) n) * exp2Z (tail l) b0)%Z;
 [ rewrite <- Znat.inj_mult; rewrite <- divides_div; auto | ring ].
ring; auto.
apply divides_lcm2; auto.
apply divides_lcm1; auto.
intros (H3, H4); split; [ idtac | split ]; auto; [ idtac | intuition ].
Contradict H4.
rewrite H3; rewrite H4.
cut (forall a b c d, (a * (b * c + d))%Z = (a * c * b + a * d)%Z);
 [ intros H6; repeat rewrite H6 | intros; ring ].
repeat rewrite <- Znat.inj_mult;
 repeat rewrite (fun y z => mult_comm (div y z));
 repeat rewrite <- divides_div; auto.
ring.
apply divides_lcm1; auto.
apply divides_lcm2; auto.
intros f l1 (H2, H2'); split; auto; split.
intros (H3, (H4, H5)); split; auto.
change
  (form2Prop (tail l)
     (Neg
        (Form.Eq
           (Plus (scal (div (lcm m1 n) m1) b) (scal (div (lcm m1 n) n) a0))
           (Plus (scal (div (lcm m1 n) m1) a) (scal (div (lcm m1 n) n) b0)))) /\
   form2Prop (tail l) (buildConj (f :: l1))) in |- *; 
 split; try (intuition; fail).
simpl in |- *; repeat rewrite scal_correct; rewrite H3; red in |- *;
 Contradict H4.
apply Zeq_mult_simpl with (c := Z_of_nat (div (lcm m1 n) n)).
apply Compare.not_eq_sym; apply Zorder.Zlt_not_eq.
replace 0%Z with (Z_of_nat 0); [ apply Znat.inj_lt | simpl in |- *; auto ].
cut (lcm m1 n = n * div (lcm m1 n) n :>nat).
case (div (lcm m1 n) n); auto with arith.
rewrite mult_comm; simpl in |- *; intros H6; Contradict H6.
apply Compare.not_eq_sym; apply lt_O_neq; apply lcm_lt_O; auto.
apply divides_div; auto.
apply divides_lcm2; auto.
rewrite (fun a l => Zmult_comm (exp2Z l a)).
apply
 Zplus_reg_l with (n := (Z_of_nat (div (lcm m1 n) m1) * exp2Z (tail l) b)%Z).
rewrite H4.
replace
 (Z_of_nat (div (lcm m1 n) m1) * (nth 0 l 0 * Z_of_nat m1 + exp2Z (tail l) b))%Z
 with
 (Z_of_nat m1 * Z_of_nat (div (lcm m1 n) m1) * nth 0 l 0 +
  Z_of_nat (div (lcm m1 n) m1) * exp2Z (tail l) b)%Z;
 [ rewrite <- Znat.inj_mult; rewrite <- divides_div; auto | ring ].
replace
 ((nth 0 l 0 * Z_of_nat n + exp2Z (tail l) b0) * Z_of_nat (div (lcm m1 n) n))%Z
 with
 (Z_of_nat n * Z_of_nat (div (lcm m1 n) n) * nth 0 l 0 +
  Z_of_nat (div (lcm m1 n) n) * exp2Z (tail l) b0)%Z;
 [ rewrite <- Znat.inj_mult; rewrite <- divides_div; auto | ring ].
ring; auto.
apply divides_lcm2; auto.
apply divides_lcm1; auto.
intros (H3, H4); split; [ idtac | split ]; auto; [ idtac | intuition ].
cut
 (form2Prop (tail l)
    (Neg
       (Form.Eq
          (Plus (scal (div (lcm m1 n) m1) b) (scal (div (lcm m1 n) n) a0))
          (Plus (scal (div (lcm m1 n) m1) a) (scal (div (lcm m1 n) n) b0)))));
 [ simpl in |- *; repeat rewrite scal_correct; intros H5
 | generalize H4; simpl in |- *; intros (H5, H6); auto ].
Contradict H5.
rewrite H5; rewrite H3.
cut (forall a b c d, (a * (b * c + d))%Z = (a * c * b + a * d)%Z);
 [ intros H6; repeat rewrite H6 | intros; ring ].
repeat rewrite <- Znat.inj_mult;
 repeat rewrite (fun y z => mult_comm (div y z));
 repeat rewrite <- divides_div; auto.
ring.
apply divides_lcm1; auto.
apply divides_lcm2; auto.
cut (form2Prop (tail l) (buildConj (f :: l1)));
 [ intuition | generalize H4; simpl in |- *; intros (H7, H8); auto ].
Qed.
 
Theorem reduceEqNEq_groundN :
 forall n m1 a b l,
 listNEqP l ->
 groundNL2 n l ->
 groundNExp n a -> groundNExp n b -> groundNL n (reduceEqNEq m1 a b l).
intros n m1 a b l H; generalize n m1 a b; elim H; clear H n m1 a b;
 simpl in |- *; auto.
intros n a b l0 H H0 H1 n0 m1 a0 b0 H2 H3 H4.
apply GNVCons; auto.
apply GNNeg.
inversion H2.
inversion H8.
inversion H13.
apply GNEq with (n := n0) (m := n0); auto.
apply GNPlus with (n := n0) (m := n3); auto.
apply scal_groundN; auto.
apply scal_groundN; auto.
apply GNPlus with (n := n0) (m := m0); auto.
apply scal_groundN; auto.
apply scal_groundN; auto.
apply H1 with (n := n0); auto.
inversion H2; auto.
Qed.

(** Reduce a congruence with an equality 
    - [a1=b1+m1.x /\ a2=b2+m2.x [i2]] gives [a1=b1+m1.x /\ n2.a2+n1.b1=n2.b2+n1.a1 [n2*n]]
*) 
 
Fixpoint reduceEqCong (m1 : nat) (a1 b1 : exp) (l : list (nat * form))
 {struct l} : list form :=
  match l with
  | (m2, Cong n a2 b2) :: l1 =>
      match lcm m1 m2 with
      | m3 =>
          match div m3 m1 with
          | n1 =>
              match div m3 m2 with
              | n2 =>
                  Cong (n2 * n) (Plus (scal n1 b1) (scal n2 a2))
                    (Plus (scal n1 a1) (scal n2 b2))
                  :: reduceEqCong m1 a1 b1 l1
              end
          end
      end
  | _ => nil
  end.
 
Theorem reduceEqCong_correct :
 forall m1 a b l l1,
 0 < m1 ->
 listCongP l1 ->
 (exp2Z (tail l) a = (nth 0 l 0 * Z_of_nat m1 + exp2Z (tail l) b)%Z /\
  formL2Prop (nth 0 l 0%Z) (tail l) l1 <->
  exp2Z (tail l) a = (nth 0 l 0 * Z_of_nat m1 + exp2Z (tail l) b)%Z /\
  form2Prop (tail l) (buildConj (reduceEqCong m1 a b l1))) /\
 Cnf1 (buildConj (reduceEqCong m1 a b l1)).
intros m1 a b l l1 H H0; elim H0; clear H0 l1; simpl in |- *; auto.
intuition.
intros n i a0 b0 l0 HH H0 H1; case (reduceEqCong m1 a b l0).
simpl in |- *; repeat rewrite scal_correct.
intros (H2, H2'); split; auto; split.
intros (H3, ((m2, H4), H5)); split; auto.
rewrite H3; rewrite H4.
exists m2.
cut (forall a b c d, (a * (b * c + d))%Z = (a * c * b + a * d)%Z);
 [ intros H6; repeat rewrite H6 | intros; ring ].
cut (forall a b c d e, (a * (b * c + d + e))%Z = (a * c * b + a * (d + e))%Z);
 [ intros H7; repeat rewrite H7 | intros; ring ].
repeat rewrite <- Znat.inj_mult;
 repeat rewrite (fun y z => mult_comm (div y z));
 repeat rewrite <- divides_div; auto.
rewrite Znat.inj_mult.
ring; auto.
apply divides_lcm1; auto.
apply divides_lcm2; auto.
intros (H3, (m4, H4)); split; auto; split; auto.
exists m4.
apply Zeq_mult_simpl with (c := Z_of_nat (div (lcm m1 n) n)).
apply Compare.not_eq_sym; apply Zorder.Zlt_not_eq.
replace 0%Z with (Z_of_nat 0); [ apply Znat.inj_lt | simpl in |- *; auto ].
cut (lcm m1 n = n * div (lcm m1 n) n :>nat).
case (div (lcm m1 n) n); auto with arith.
rewrite mult_comm; simpl in |- *; intros H6; Contradict H6.
apply Compare.not_eq_sym; apply lt_O_neq; apply lcm_lt_O; auto.
apply divides_div; auto.
apply divides_lcm2; auto.
rewrite (fun a l => Zmult_comm (exp2Z (tail l) a)).
apply
 Zplus_reg_l with (n := (Z_of_nat (div (lcm m1 n) m1) * exp2Z (tail l) b)%Z).
rewrite H4.
rewrite H3.
rewrite Znat.inj_mult.
cut (forall a b c d, (a * (b * c + d))%Z = (a * c * b + a * d)%Z);
 [ intros H6; repeat rewrite H6 | intros; ring ].
cut (forall a b c d e, ((b * c + d + e) * a)%Z = (a * c * b + a * (d + e))%Z);
 [ intros H7; repeat rewrite H7 | intros; ring ].
repeat rewrite <- Znat.inj_mult;
 repeat rewrite (fun y z => mult_comm (div y z));
 repeat rewrite <- divides_div; auto.
rewrite Znat.inj_mult.
ring; auto.
apply divides_lcm2; auto.
apply divides_lcm1; auto.
intuition.
intros f l1 (H2, H2'); split; auto; split.
intros (H3, ((m4, H4), H5)); split; auto.
change
  (form2Prop (tail l)
     (Cong (div (lcm m1 n) n * i)
        (Plus (scal (div (lcm m1 n) m1) b) (scal (div (lcm m1 n) n) a0))
        (Plus (scal (div (lcm m1 n) m1) a) (scal (div (lcm m1 n) n) b0))) /\
   form2Prop (tail l) (buildConj (f :: l1))) in |- *; 
 split; try (intuition; fail).
simpl in |- *; repeat rewrite scal_correct; rewrite H3.
exists m4.
rewrite H4.
cut (forall a b c d, (a * (b * c + d))%Z = (a * c * b + a * d)%Z);
 [ intros H6; repeat rewrite H6 | intros; ring ].
cut (forall a b c d e, (a * (b * c + d + e))%Z = (a * c * b + a * (d + e))%Z);
 [ intros H7; repeat rewrite H7 | intros; ring ].
repeat rewrite <- Znat.inj_mult;
 repeat rewrite (fun y z => mult_comm (div y z));
 repeat rewrite <- divides_div; auto.
rewrite Znat.inj_mult.
ring; auto.
apply divides_lcm1; auto.
apply divides_lcm2; auto.
intros (H3, H4); split; [ idtac | split ]; auto; [ idtac | intuition ].
cut
 (form2Prop (tail l)
    (Cong (div (lcm m1 n) n * i)
       (Plus (scal (div (lcm m1 n) m1) b) (scal (div (lcm m1 n) n) a0))
       (Plus (scal (div (lcm m1 n) m1) a) (scal (div (lcm m1 n) n) b0))));
 [ simpl in |- *; repeat rewrite scal_correct; intros (m5, H5)
 | generalize H4; simpl in |- *; intros (H5, H6); auto ].
exists m5.
apply Zeq_mult_simpl with (c := Z_of_nat (div (lcm m1 n) n)).
apply Compare.not_eq_sym; apply Zorder.Zlt_not_eq.
replace 0%Z with (Z_of_nat 0); [ apply Znat.inj_lt | simpl in |- *; auto ].
cut (lcm m1 n = n * div (lcm m1 n) n :>nat).
case (div (lcm m1 n) n); auto with arith.
rewrite mult_comm; simpl in |- *; intros H6; Contradict H6.
apply Compare.not_eq_sym; apply lt_O_neq; apply lcm_lt_O; auto.
apply divides_div; auto.
apply divides_lcm2; auto.
rewrite (fun a l => Zmult_comm (exp2Z (tail l) a)).
apply
 Zplus_reg_l with (n := (Z_of_nat (div (lcm m1 n) m1) * exp2Z (tail l) b)%Z).
rewrite H5; rewrite H3.
cut (forall a b c d, (a * (b * c + d))%Z = (a * c * b + a * d)%Z);
 [ intros H6; repeat rewrite H6 | intros; ring ].
cut (forall a b c d e, ((b * c + d + e) * a)%Z = (a * c * b + a * (d + e))%Z);
 [ intros H7; repeat rewrite H7 | intros; ring ].
repeat rewrite <- Znat.inj_mult;
 repeat rewrite (fun y z => mult_comm (div y z));
 repeat rewrite <- divides_div; auto.
rewrite Znat.inj_mult.
ring; auto.
apply divides_lcm2; auto.
apply divides_lcm1; auto.
simpl in H4.
intuition.
Qed.
 
Theorem reduceEqCong_groundN :
 forall n m1 a b l,
 listCongP l ->
 groundNL2 n l ->
 groundNExp n a -> groundNExp n b -> groundNL n (reduceEqCong m1 a b l).
intros n m1 a b l H; generalize n m1 a b; elim H; clear H n m1 a b;
 simpl in |- *; auto.
intros n i a b l0 H H0 H1 H2 n0 m1 a0 b0 H3 H4 H5.
apply GNVCons; auto.
inversion H3.
inversion H9.
apply GNCong with (n := n0) (m := n0); auto.
apply GNPlus with (n := n0) (m := n2); auto.
apply scal_groundN; auto.
apply scal_groundN; auto.
apply GNPlus with (n := n0) (m := m0); auto.
apply scal_groundN; auto.
apply scal_groundN; auto.
apply H2 with (n := n0); auto.
inversion H3; auto.
Qed.