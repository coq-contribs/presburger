(************************************************************************)
(*                                                                      *)
(*                          Lift.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(** * Lift Quantifiers *)
Require Export Form.
 
Inductive prenex : form -> Prop :=
  | pExists : forall a : form, prenex a -> prenex (Exists a)
  | pForall : forall a : form, prenex a -> prenex (Forall a)
  | pNoBinder : forall a : form, noBinder a -> prenex a.
Hint Constructors prenex.
 
(** * Lift If
  - [((x:?)(P x) -> Q)] gives [(Ex [x:?] ((P x) -> Q)) )]
  - [(Ex [x:?](P x) -> Q)] gives [(x:?) ((P x) -> Q) )]
  - [Q->(x:?)(P x)] gives [(x:?) Q-> (P x)]
  - [Q->(Ex[x:?](P x)] gives [(Ex [x:?] Q->(P x)]
 *)
Fixpoint lift_if1 (n m : nat) (f1 f2 : form) {struct f2} : form :=
  match f2 with
  | Forall b => Forall (lift_if1 n (S m) f1 b)
  | Exists b => Exists (lift_if1 n (S m) f1 b)
  | _ => Imp (shiftForm n m m f1) (shiftForm m 0 n f2)
  end.
 
Fixpoint lift_if2 (n : nat) (f1 : form) {struct f1} : 
 form -> form :=
  fun f2 : form =>
  match f1 with
  | Forall b => Exists (lift_if2 (S n) b f2)
  | Exists b => Forall (lift_if2 (S n) b f2)
  | _ => lift_if1 n 0 f1 f2
  end.
 
Definition lift_if (f1 f2 : form) := lift_if2 0 f1 f2.
 
Theorem noBinder_shift :
 forall (f : form) (th i o : nat),
 noBinder f -> noBinder (shiftForm th i o f).
intros f th i o H; generalize th i o; elim H; simpl in |- *; auto.
Qed.
Hint Resolve noBinder_shift.
 
Theorem lift_if1_noBinder :
 forall (n m : nat) (f1 f2 : form),
 noBinder f2 ->
 lift_if1 n m f1 f2 = Imp (shiftForm n m m f1) (shiftForm m 0 n f2).
intros n m f1 f2 H; elim H; simpl in |- *; auto.
Qed.
 
Theorem lift_if1_prenex :
 forall (n m : nat) (f1 f2 : form),
 noBinder f1 -> prenex f2 -> prenex (lift_if1 n m f1 f2).
intros n m f1 f2 H1 H2; generalize n m; elim H2; simpl in |- *; auto.
intros a H3; elim H3; simpl in |- *; auto.
Qed.
Hint Resolve lift_if1_prenex.
Require Import GroundN.
Require Import ArithRing.
Require Import Max.
 
Theorem lift_if1_groundN :
 forall f1 f2 n m p,
 prenex f2 ->
 noBinder f1 ->
 groundNForm (p + n) f1 ->
 groundNForm (p + m) f2 -> groundNForm (p + (m + n)) (lift_if1 n m f1 f2).
intros f1 f2 n m p H H1; generalize m p; elim H; clear H m p;
 unfold lift_if1 in |- *; lazy beta in |- *; fold lift_if1 in |- *; 
 auto.
intros a H H0 m p H2 H3.
apply GNExists; auto.
replace (S (p + (m + n))) with (p + (S m + n)).
apply H0; auto.
replace (p + S m) with (S (p + m)).
inversion H3; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
intros a H H0 m p H2 H3.
apply GNForall; auto.
replace (S (p + (m + n))) with (p + (S m + n)).
apply H0; auto.
replace (p + S m) with (S (p + m)).
inversion H3; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
intros a H; elim H; unfold lift_if1 in |- *; lazy beta in |- *;
 fold lift_if1 in |- *; auto; intros;
 apply GNImp with (n := p + (m + n)) (m := p + (m + n)); 
 auto with arith;
 try
  (replace (p + (m + n)) with (max (n + m) (p + n + m));
    [ apply shiftForm_groundN; auto
    | replace (p + (m + n)) with (p + n + m); auto with arith; ring ]);
 try
  (replace (p + (m + n)) with (max (m + 0) (p + m + n));
    [ apply shiftForm_groundN; auto; replace (p + (m + n)) with (m + (p + n));
       auto with arith
    | replace (p + (m + n)) with (p + n + m); auto with arith; ring ]);
 try (replace (p + m + n) with (m + (n + p)); auto with arith; try ring).
Qed.
 
Theorem lift_if2_prenex :
 forall (n : nat) (f1 f2 : form),
 prenex f1 -> prenex f2 -> prenex (lift_if2 n f1 f2).
intros n f1 f2 H; generalize n f2; elim H; simpl in |- *; clear n f2 H; auto.
intros a H; elim H; clear H a; simpl in |- *; auto.
Qed.
Hint Resolve lift_if2_prenex.
 
Theorem lift_if2_groundN :
 forall f1 f2 n p,
 prenex f1 ->
 prenex f2 ->
 groundNForm (p + n) f1 ->
 groundNForm p f2 -> groundNForm (p + n) (lift_if2 n f1 f2).
intros f1 f2 n p H H1; generalize n p; elim H; clear H n p;
 unfold lift_if2 in |- *; lazy beta in |- *; fold lift_if2 in |- *.
intros a H0 H2 n p H3 H4.
apply GNForall; auto.
replace (S (p + n)) with (p + S n); auto with arith.
apply H2; auto.
replace (p + S n) with (S (p + n)); auto with arith.
inversion H3; auto.
intros a H0 H2 n p H3 H4.
apply GNExists; auto.
replace (S (p + n)) with (p + S n); auto with arith.
apply H2; auto.
replace (p + S n) with (S (p + n)); auto with arith.
inversion H3; auto.
intros a H; elim H; unfold lift_if2 in |- *; lazy beta in |- *;
 fold lift_if2 in |- *; auto; intros; replace (p + n) with (p + (0 + n));
 try apply lift_if1_groundN; auto with arith; rewrite plus_comm;
 simpl in |- *; auto.
Qed.
 
Theorem lift_if_prenex :
 forall f1 f2 : form, prenex f1 -> prenex f2 -> prenex (lift_if f1 f2).
intros; unfold lift_if in |- *; auto.
Qed.
Hint Resolve lift_if_prenex.
 
Theorem lift_if_groundN :
 forall f1 f2 p,
 prenex f1 ->
 prenex f2 ->
 groundNForm p f1 -> groundNForm p f2 -> groundNForm p (lift_if f1 f2).
intros f1 f2 p H H0 H1 H2; unfold lift_if in |- *.
replace p with (p + 0); auto with arith.
apply lift_if2_groundN; auto with arith; rewrite plus_comm; simpl in |- *;
 auto with arith.
Qed.
 
Definition iso_list (th i o : nat) (l1 l2 : list Z) :=
  forall n : nat,
  (n < th -> nth n l1 0%Z = nth (n + i) l2 0%Z) /\
  (th <= n -> nth n l1 0%Z = nth (n + o) l2 0%Z).
 
Theorem iso_shiftExp :
 forall (l1 l2 : list Z) (th i o : nat),
 iso_list th i o l1 l2 ->
 forall e : exp, exp2Z l1 e = exp2Z l2 (shiftExp th i o e).
intros l1 l2 th i o H e; elim e; simpl in |- *; auto.
intros n; generalize (H n); generalize (ltdec_correct n th);
 case (ltdec n th); intros H1 H2; case H2; auto.
intros e0 H0 e1 H1; rewrite H0; rewrite H1; auto.
Qed.
Hint Resolve iso_shiftExp.
 
Theorem iso_shiftForm :
 forall (th i o : nat) (l1 l2 : list Z),
 iso_list th i o l1 l2 ->
 forall f : form,
 noBinder f -> (form2Prop l1 f <-> form2Prop l2 (shiftForm th i o f)).
intros th i o l1 l2 H f H0; elim H0; simpl in |- *; auto; intros;
 repeat rewrite <- (iso_shiftExp l1); intuition; auto.
Qed.
 
Definition iso_list3 (n m : nat) (l1 l2 l3 : list Z) :=
  forall p : nat,
  ((p < m -> nth p l3 0%Z = nth p l2 0%Z) /\
   (m <= p -> nth (p + n) l3 0%Z = nth p l2 0%Z)) /\
  nth (p + m) l3 0%Z = nth p l1 0%Z.
 
Theorem iso_iso3_1 :
 forall l1 l2 l3 n m, iso_list3 n m l1 l2 l3 -> iso_list n m m l1 l3.
intros l1 l2 l3 n m H; red in |- *; intros p.
case (H p); intros H0 H1; intuition.
Qed.
 
Theorem iso_iso3_2 :
 forall l1 l2 l3 n m, iso_list3 n m l1 l2 l3 -> iso_list m 0 n l2 l3.
intros l1 l2 l3 n m H; red in |- *; intros p.
case (H p); intros H0 H1; rewrite plus_comm; simpl in |- *; intuition.
Qed.
 
Theorem iso3_1 :
 forall (n m : nat) (x : Z) l1 l2 l3,
 iso_list3 n m l1 l2 l3 -> iso_list3 n (S m) l1 (x :: l2) (x :: l3).
intros n m x l1 l2 l3 H; red in |- *; intros p; repeat split; try intros H1.
generalize H1; clear H1; case p; simpl in |- *; auto.
intros p' H1.
cut (p' < m); [ intros H2 | apply lt_S_n; auto ].
case (H p'); intros (H3, H4) H5; auto.
generalize H1; clear H1; case p; simpl in |- *; auto.
intros H1; inversion H1.
intros p' H1.
cut (m <= p'); [ intros H2 | apply le_S_n; auto ].
case (H p'); intros (H3, H4) H5; auto.
replace (p + S m) with (S (p + m)); simpl in |- *; [ idtac | auto ].
case (H p); intros (H3, H4) H5; auto.
Qed.
Hint Resolve iso3_1.
 
Theorem iso_lift_i1 :
 forall f1 f2 : form,
 noBinder f1 ->
 prenex f2 ->
 forall (n m : nat) (l1 l2 l3 : list Z),
 iso_list3 n m l1 l2 l3 ->
 (form2Prop l1 f1 -> form2Prop l2 f2 <-> form2Prop l3 (lift_if1 n m f1 f2)).
intros f1 f2 H H0; elim H0.
simpl in |- *; intros a H1 H2 n m l1 l2 l3 H3; split.
intros H4.
case (classic (form2Prop l1 f1)); intros H5.
case (H4 H5); clear H4; intros x H4; exists x.
case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
exists 0%Z.
case (H2 n (S m) l1 (0%Z :: l2) (0%Z :: l3)); auto.
intros H6 H7; apply H6; auto.
intros H8; case H5; auto.
intros H4 H5; case H4; clear H4; intros x H4; exists x.
case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
simpl in |- *; intros a H1 H2 n m l1 l2 l3 H3; split.
intros H4 x.
case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
intros H4 H5 x.
case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
intros a H1 n m l1 l2 l3 H2.
rewrite lift_if1_noBinder; simpl in |- *; auto.
case (iso_shiftForm n m m l1 l3) with (f := f1); auto.
apply iso_iso3_1 with (l2 := l2); auto.
case (iso_shiftForm m 0 n l2 l3) with (f := a); auto.
apply iso_iso3_2 with (l1 := l1); auto.
intuition.
Qed.
 
Theorem iso3_2 :
 forall (n : nat) (x : Z) l1 l2 l3,
 iso_list3 n 0 l1 l2 l3 -> iso_list3 (S n) 0 (x :: l1) l2 (x :: l3).
intros n x l1 l2 l3 H; red in |- *; intros p; repeat split; try intros H1.
inversion H1.
replace (p + S n) with (S (p + n));
 [ simpl in |- * | repeat rewrite (plus_comm p); simpl in |- *; auto ].
case (H p); intros (H2, H3) H4; auto.
case p; simpl in |- *; auto.
intros p'; case (H p'); intros (H1, H2) H3; auto.
Qed.
Hint Resolve iso3_2.
 
Theorem iso_lift_i2 :
 forall f1 f2 : form,
 prenex f1 ->
 prenex f2 ->
 forall (n : nat) (l1 l2 l3 : list Z),
 iso_list3 n 0 l1 l2 l3 ->
 (form2Prop l1 f1 -> form2Prop l2 f2 <-> form2Prop l3 (lift_if2 n f1 f2)).
intros f1 f2 H H1; elim H; clear H; simpl in |- *; auto.
intros a H H0 n l1 l2 l3 H2; split.
intros H3 x.
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros H4 H5; auto.
apply H4; auto.
intros H6; apply H3; exists x; auto.
intros H3 H4; case H4; clear H4; intros x H4.
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros a H H0 n l1 l2 l3 H2; split.
intros H3.
case (classic (forall x : Z, form2Prop (x :: l1) a)); intros H4.
exists 0%Z.
case (H0 (S n) (0%Z :: l1) l2 (0%Z :: l3)); auto.
case (classic (ex (fun x : Z => form2Prop (x :: l3) (lift_if2 (S n) a f2))));
 intros H5; auto.
elim H4; intros x.
case (classic (form2Prop (x :: l1) a)); intros H6; auto.
case H5; exists x.
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros H7 H8; apply H7; intros H9; case H6; auto.
intros H3 H4; case H3; clear H3; intros x H3.
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros a H; elim H; clear H; unfold lift_if2 in |- *; intros;
 apply iso_lift_i1; auto.
Qed.
 
Theorem correct_lift_if :
 forall f1 f2 : form,
 prenex f1 ->
 prenex f2 ->
 forall l : list Z,
 form2Prop l f1 -> form2Prop l f2 <-> form2Prop l (lift_if f1 f2).
intros f1 f2 H H0 l; unfold lift_if in |- *; apply iso_lift_i2; auto.
red in |- *; repeat split; (repeat rewrite (plus_comm p); simpl in |- *);
 auto.
Qed.

(** * Lift And
  - [((x:?)(P x) /\ Q)] gives [(x:?) ((P x) /\ Q)) )]
  - [(Ex [x:?](P x) /\ Q)] gives [(Ex [x:?] ((P x) -> Q) )]
  - [Q/\(x:?)(P x)] gives [(x:?) Q/\ (P x)]
  - [Q/\(Ex[x:?](P x)] gives [(Ex [x:?] Q/\(P x)]
 *)
 
Fixpoint lift_andor1 (op : form -> form -> form) (n m : nat) 
 (f1 f2 : form) {struct f2} : form :=
  match f2 with
  | Forall b => Forall (lift_andor1 op n (S m) f1 b)
  | Exists b => Exists (lift_andor1 op n (S m) f1 b)
  | _ => op (shiftForm n m m f1) (shiftForm m 0 n f2)
  end.
 
Fixpoint lift_andor2 (op : form -> form -> form) (n : nat) 
 (f1 : form) {struct f1} : form -> form :=
  fun f2 : form =>
  match f1 with
  | Forall b => Forall (lift_andor2 op (S n) b f2)
  | Exists b => Exists (lift_andor2 op (S n) b f2)
  | _ => lift_andor1 op n 0 f1 f2
  end.
 
Definition lift_andor (op : form -> form -> form) (f1 f2 : form) :=
  lift_andor2 op 0 f1 f2.
 
Theorem lift_andor1_noBinder :
 forall op (n m : nat) (f1 f2 : form),
 noBinder f2 ->
 lift_andor1 op n m f1 f2 = op (shiftForm n m m f1) (shiftForm m 0 n f2).
intros op n m f1 f2 H; elim H; simpl in |- *; auto.
Qed.
 
Theorem lift_andor1_prenex :
 forall op,
 (forall f1 f2, noBinder f1 -> noBinder f2 -> noBinder (op f1 f2)) ->
 forall (n m : nat) (f1 f2 : form),
 noBinder f1 -> prenex f2 -> prenex (lift_andor1 op n m f1 f2).
intros op H n m f1 f2 H1 H2; generalize n m; elim H2; simpl in |- *; auto.
intros a H3; elim H3; simpl in |- *; auto.
Qed.
Hint Resolve lift_andor1_prenex.
 
Theorem lift_andor2_prenex :
 forall op,
 (forall f1 f2, noBinder f1 -> noBinder f2 -> noBinder (op f1 f2)) ->
 forall (n : nat) (f1 f2 : form),
 prenex f1 -> prenex f2 -> prenex (lift_andor2 op n f1 f2).
intros op Rec n f1 f2 H; generalize n f2; elim H; simpl in |- *; clear n f2 H;
 auto.
intros a H; elim H; clear H a; simpl in |- *; auto.
Qed.
Hint Resolve lift_andor2_prenex.
 
Theorem lift_andor_prenex :
 forall op,
 (forall f1 f2, noBinder f1 -> noBinder f2 -> noBinder (op f1 f2)) ->
 forall f1 f2 : form, prenex f1 -> prenex f2 -> prenex (lift_andor op f1 f2).
intros; unfold lift_andor in |- *; auto.
Qed.
Hint Resolve lift_andor_prenex.
 
Theorem lift_andor1_and_groundN :
 forall f1 f2 n m p,
 prenex f2 ->
 noBinder f1 ->
 groundNForm (p + n) f1 ->
 groundNForm (p + m) f2 ->
 groundNForm (p + (m + n)) (lift_andor1 ANd n m f1 f2).
intros f1 f2 n m p H H1; generalize m p; elim H; clear H m p;
 unfold lift_andor1 in |- *; lazy beta in |- *; fold lift_andor1 in |- *;
 auto.
intros a H H0 m p H2 H3.
apply GNExists; auto.
replace (S (p + (m + n))) with (p + (S m + n)).
apply H0; auto.
replace (p + S m) with (S (p + m)).
inversion H3; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
intros a H H0 m p H2 H3.
apply GNForall; auto.
replace (S (p + (m + n))) with (p + (S m + n)).
apply H0; auto.
replace (p + S m) with (S (p + m)).
inversion H3; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
intros a H; elim H; unfold lift_andor1 in |- *; lazy beta in |- *;
 fold lift_andor1 in |- *; auto; intros;
 apply GNAnd with (n := p + (m + n)) (m := p + (m + n)); 
 auto with arith;
 try
  (replace (p + (m + n)) with (max (n + m) (p + n + m));
    [ apply shiftForm_groundN; auto
    | replace (p + (m + n)) with (p + n + m); auto with arith; ring ]);
 try
  (replace (p + (m + n)) with (max (m + 0) (p + m + n));
    [ apply shiftForm_groundN; auto; replace (p + (m + n)) with (m + (p + n));
       auto with arith
    | replace (p + (m + n)) with (p + n + m); auto with arith; ring ]);
 try (replace (p + m + n) with (m + (n + p)); auto with arith; try ring).
Qed.
 
Theorem lift_andor1_or_groundN :
 forall f1 f2 n m p,
 prenex f2 ->
 noBinder f1 ->
 groundNForm (p + n) f1 ->
 groundNForm (p + m) f2 ->
 groundNForm (p + (m + n)) (lift_andor1 Or n m f1 f2).
intros f1 f2 n m p H H1; generalize m p; elim H; clear H m p;
 unfold lift_andor1 in |- *; lazy beta in |- *; fold lift_andor1 in |- *;
 auto.
intros a H H0 m p H2 H3.
apply GNExists; auto.
replace (S (p + (m + n))) with (p + (S m + n)).
apply H0; auto.
replace (p + S m) with (S (p + m)).
inversion H3; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
intros a H H0 m p H2 H3.
apply GNForall; auto.
replace (S (p + (m + n))) with (p + (S m + n)).
apply H0; auto.
replace (p + S m) with (S (p + m)).
inversion H3; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
repeat rewrite (plus_comm p); simpl in |- *; auto.
intros a H; elim H; unfold lift_andor1 in |- *; lazy beta in |- *;
 fold lift_andor1 in |- *; auto; intros;
 apply GNOr with (n := p + (m + n)) (m := p + (m + n)); 
 auto with arith;
 try
  (replace (p + (m + n)) with (max (n + m) (p + n + m));
    [ apply shiftForm_groundN; auto
    | replace (p + (m + n)) with (p + n + m); auto with arith; ring ]);
 try
  (replace (p + (m + n)) with (max (m + 0) (p + m + n));
    [ apply shiftForm_groundN; auto; replace (p + (m + n)) with (m + (p + n));
       auto with arith
    | replace (p + (m + n)) with (p + n + m); auto with arith; ring ]);
 try (replace (p + m + n) with (m + (n + p)); auto with arith; try ring).
Qed.
 
Theorem lift_andor2_and_groundN :
 forall f1 f2 n p,
 prenex f1 ->
 prenex f2 ->
 groundNForm (p + n) f1 ->
 groundNForm p f2 -> groundNForm (p + n) (lift_andor2 ANd n f1 f2).
intros f1 f2 n p H H1; generalize n p; elim H; clear H n p;
 unfold lift_andor2 in |- *; lazy beta in |- *; fold lift_andor2 in |- *.
intros a H0 H2 n p H3 H4.
apply GNExists; auto.
replace (S (p + n)) with (p + S n); auto with arith.
apply H2; auto.
replace (p + S n) with (S (p + n)); auto with arith.
inversion H3; auto.
intros a H0 H2 n p H3 H4.
apply GNForall; auto.
replace (S (p + n)) with (p + S n); auto with arith.
apply H2; auto.
replace (p + S n) with (S (p + n)); auto with arith.
inversion H3; auto.
intros a H; elim H; unfold lift_andor2 in |- *; lazy beta in |- *;
 fold lift_andor2 in |- *; auto; intros; replace (p + n) with (p + (0 + n));
 try apply lift_andor1_and_groundN; auto with arith; 
 rewrite plus_comm; simpl in |- *; auto.
Qed.
 
Theorem lift_andor2_or_groundN :
 forall f1 f2 n p,
 prenex f1 ->
 prenex f2 ->
 groundNForm (p + n) f1 ->
 groundNForm p f2 -> groundNForm (p + n) (lift_andor2 Or n f1 f2).
intros f1 f2 n p H H1; generalize n p; elim H; clear H n p;
 unfold lift_andor2 in |- *; lazy beta in |- *; fold lift_andor2 in |- *.
intros a H0 H2 n p H3 H4.
apply GNExists; auto.
replace (S (p + n)) with (p + S n); auto with arith.
apply H2; auto.
replace (p + S n) with (S (p + n)); auto with arith.
inversion H3; auto.
intros a H0 H2 n p H3 H4.
apply GNForall; auto.
replace (S (p + n)) with (p + S n); auto with arith.
apply H2; auto.
replace (p + S n) with (S (p + n)); auto with arith.
inversion H3; auto.
intros a H; elim H; unfold lift_andor2 in |- *; lazy beta in |- *;
 fold lift_andor2 in |- *; auto; intros; replace (p + n) with (p + (0 + n));
 try apply lift_andor1_or_groundN; auto with arith; 
 rewrite plus_comm; simpl in |- *; auto.
Qed.
 
Theorem lift_andor_and_groundN :
 forall f1 f2 p,
 prenex f1 ->
 prenex f2 ->
 groundNForm p f1 -> groundNForm p f2 -> groundNForm p (lift_andor ANd f1 f2).
intros f1 f2 p H H0 H1 H2; unfold lift_andor in |- *.
replace p with (p + 0); auto with arith.
apply lift_andor2_and_groundN; auto with arith; rewrite plus_comm;
 simpl in |- *; auto with arith.
Qed.
 
Theorem lift_andor_or_groundN :
 forall f1 f2 p,
 prenex f1 ->
 prenex f2 ->
 groundNForm p f1 -> groundNForm p f2 -> groundNForm p (lift_andor Or f1 f2).
intros f1 f2 p H H0 H1 H2; unfold lift_andor in |- *.
replace p with (p + 0); auto with arith.
apply lift_andor2_or_groundN; auto with arith; rewrite plus_comm;
 simpl in |- *; auto with arith.
Qed.
 
Theorem iso_lift_andor_and1 :
 forall f1 f2 : form,
 noBinder f1 ->
 prenex f2 ->
 forall (n m : nat) (l1 l2 l3 : list Z),
 iso_list3 n m l1 l2 l3 ->
 (form2Prop l1 f1 /\ form2Prop l2 f2 <->
  form2Prop l3 (lift_andor1 ANd n m f1 f2)).
intros f1 f2 H H0; elim H0.
simpl in |- *; intros a H1 H2 n m l1 l2 l3 H3; split.
intros (H4, (x, H5)); exists x.
case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
intros (x, H4).
case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
intros H5 H6; (split; [ idtac | exists x ]); case H6; auto.
simpl in |- *; intros a H1 H2 n m l1 l2 l3 H3; split.
intros (H4, H5) x.
case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
intros H4; split.
case (H2 n (S m) l1 (0%Z :: l2) (0%Z :: l3)); auto.
intros H5 H6; case H6; auto.
intros x; case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
intros H5 H6; case H6; auto.
intros a H1 n m l1 l2 l3 H2.
rewrite lift_andor1_noBinder; simpl in |- *; auto.
case (iso_shiftForm n m m l1 l3) with (f := f1); auto.
apply iso_iso3_1 with (l2 := l2); auto.
case (iso_shiftForm m 0 n l2 l3) with (f := a); auto.
apply iso_iso3_2 with (l1 := l1); auto.
intuition.
Qed.
 
Theorem iso_lift_andor_or1 :
 forall f1 f2 : form,
 noBinder f1 ->
 prenex f2 ->
 forall (n m : nat) (l1 l2 l3 : list Z),
 iso_list3 n m l1 l2 l3 ->
 (form2Prop l1 f1 \/ form2Prop l2 f2 <->
  form2Prop l3 (lift_andor1 Or n m f1 f2)).
intros f1 f2 H H0; elim H0.
simpl in |- *; intros a H1 H2 n m l1 l2 l3 H3; split.
intros [H4| (x, H4)].
case (H2 n (S m) l1 (0%Z :: l2) (0%Z :: l3)); auto.
intros H5 H6; exists 0%Z; auto.
exists x.
case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
intros (x, H4).
case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
intros H5 H6; case H6; auto; intros H7.
right; exists x; auto.
simpl in |- *; intros a H1 H2 n m l1 l2 l3 H3; split.
intros [H4| H4] x; case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
intros H4; case (classic (form2Prop l1 f1)); intros H5; auto.
right; intros x.
case (H2 n (S m) l1 (x :: l2) (x :: l3)); auto.
intros H6 H7; case H7; auto.
intros H8; case H5; auto.
intros a H1 n m l1 l2 l3 H2.
rewrite lift_andor1_noBinder; simpl in |- *; auto.
case (iso_shiftForm n m m l1 l3) with (f := f1); auto.
apply iso_iso3_1 with (l2 := l2); auto.
case (iso_shiftForm m 0 n l2 l3) with (f := a); auto.
apply iso_iso3_2 with (l1 := l1); auto.
intuition.
Qed.
 
Theorem iso_lift_andor_and2 :
 forall f1 f2 : form,
 prenex f1 ->
 prenex f2 ->
 forall (n : nat) (l1 l2 l3 : list Z),
 iso_list3 n 0 l1 l2 l3 ->
 (form2Prop l1 f1 /\ form2Prop l2 f2 <->
  form2Prop l3 (lift_andor2 ANd n f1 f2)).
intros f1 f2 H H1; elim H; clear H; simpl in |- *; auto.
intros a H H0 n l1 l2 l3 H2; split.
intros ((x, H3), H4); exists x.
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros (x, H3); split; [ exists x | idtac ].
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros H4 H5; case H5; auto.
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros H4 H5; case H5; auto.
intros a H H0 n l1 l2 l3 H2; split.
intros (H3, H4) x.
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros H3; (split; [ intros | idtac ]).
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros H4 H5; case H5; auto.
case (H0 (S n) (0%Z :: l1) l2 (0%Z :: l3)); auto.
intros H4 H5; case H5; auto.
intros a H; elim H; clear H; unfold lift_andor2 in |- *; intros;
 apply iso_lift_andor_and1; auto.
Qed.
 
Theorem iso_lift_andor_or2 :
 forall f1 f2 : form,
 prenex f1 ->
 prenex f2 ->
 forall (n : nat) (l1 l2 l3 : list Z),
 iso_list3 n 0 l1 l2 l3 ->
 (form2Prop l1 f1 \/ form2Prop l2 f2 <->
  form2Prop l3 (lift_andor2 Or n f1 f2)).
intros f1 f2 H H1; elim H; clear H; simpl in |- *; auto.
intros a H H0 n l1 l2 l3 H2; split.
intros [(x, H3)| H4]; [ exists x | exists 0%Z ].
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
case (H0 (S n) (0%Z :: l1) l2 (0%Z :: l3)); auto.
intros (x, H3).
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros H4 H5; case H5; auto.
intros H6; left; exists x; auto.
intros a H H0 n l1 l2 l3 H2; split.
intros [H3| H3] x; case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros H3; case (classic (form2Prop l2 f2)); auto; left; intros x.
case (H0 (S n) (x :: l1) l2 (x :: l3)); auto.
intros H5 H6; case H6; auto.
intros H7; case H4; auto.
intros a H; elim H; clear H; unfold lift_andor2 in |- *; intros;
 apply iso_lift_andor_or1; auto.
Qed.
 
Theorem correct_lift_andor_and :
 forall f1 f2 : form,
 prenex f1 ->
 prenex f2 ->
 forall l : list Z,
 form2Prop l f1 /\ form2Prop l f2 <-> form2Prop l (lift_andor ANd f1 f2).
intros f1 f2 H H0 l; unfold lift_andor in |- *; apply iso_lift_andor_and2;
 auto.
red in |- *; repeat split; (repeat rewrite (plus_comm p); simpl in |- *);
 auto.
Qed.
 
Theorem correct_lift_andor_or :
 forall f1 f2 : form,
 prenex f1 ->
 prenex f2 ->
 forall l : list Z,
 form2Prop l f1 \/ form2Prop l f2 <-> form2Prop l (lift_andor Or f1 f2).
intros f1 f2 H H0 l; unfold lift_andor in |- *; apply iso_lift_andor_or2;
 auto.
red in |- *; repeat split; (repeat rewrite (plus_comm p); simpl in |- *);
 auto.
Qed.
 
(** * Lift Neg
  - [~((x:?)(P x))] gives  [(Ex [x:?] ~(P x))]
  - [~([x:?](P x))] gives [(x:?) ~(P x)]
 *)

Fixpoint lift_neg (f : form) : form :=
  match f with
  | Forall b => Exists (lift_neg b)
  | Exists b => Forall (lift_neg b)
  | b => Neg b
  end.
 
Theorem lift_neg_prenex : forall f : form, prenex f -> prenex (lift_neg f).
intros f H; elim H; simpl in |- *; auto.
intros a H1; elim H1; simpl in |- *; auto.
Qed.
Hint Resolve lift_neg_prenex.
 
Theorem lift_neg_groundN :
 forall f p, prenex f -> groundNForm p f -> groundNForm p (lift_neg f).
intros f p H; generalize p; elim H; clear H p; unfold lift_neg in |- *;
 lazy beta in |- *; fold lift_neg in |- *.
intros a H H0 p H1; inversion H1; auto.
intros a H H0 p H1; inversion H1; auto.
intros a H; elim H; simpl in |- *; auto.
Qed.
 
Theorem correct_lift_neg :
 forall f : form,
 prenex f -> forall l : list Z, ~ form2Prop l f <-> form2Prop l (lift_neg f).
intros f H; elim H; simpl in |- *; auto.
intros a H0 H1 l; split.
intros H2 x.
case (H1 (x :: l)); auto.
intros H3 H4; apply H3; auto; red in |- *; intros; case H2; exists x; auto.
intros H2; red in |- *; intros (x, H3).
case (H1 (x :: l)); auto.
intros H4 H5; apply H5; auto.
intros a H0 H1 l; split.
intros H2; case (classic (ex (fun x : Z => form2Prop (x :: l) (lift_neg a))));
 intros H3; auto.
elim H2; intros x.
case (classic (form2Prop (x :: l) a)); intros H4; auto.
case H3; exists x.
case (H1 (x :: l)); auto.
intros (x, H2); red in |- *; intros H3.
case (H1 (x :: l)); auto.
intros H4 H5; apply H5; auto.
intros a H1; elim H1; simpl in |- *; auto; intuition.
Qed.
 
(** Lift quantifier *)
Fixpoint lift_quant (f : form) : form :=
  match f with
  | Forall f1 => Forall (lift_quant f1)
  | Exists f1 => Exists (lift_quant f1)
  | Imp f1 f2 => lift_if (lift_quant f1) (lift_quant f2)
  | ANd f1 f2 => lift_andor ANd (lift_quant f1) (lift_quant f2)
  | Or f1 f2 => lift_andor Or (lift_quant f1) (lift_quant f2)
  | Neg f1 => lift_neg (lift_quant f1)
  | f1 => f1
  end.
 
Theorem lift_quant_prenex : forall f : form, prenex (lift_quant f).
intros f; elim f; simpl in |- *; auto.
Qed.
Hint Resolve lift_quant_prenex.
 
Theorem lift_quant_groundN :
 forall f p, groundNForm p f -> groundNForm p (lift_quant f).
intros f; elim f; clear f; unfold lift_quant in |- *; lazy beta in |- *;
 fold lift_quant in |- *; auto.
intros f H p H0; inversion H0; auto.
intros f H p H0; inversion H0; auto.
intros f H f0 H0 p H1; inversion H1; apply lift_andor_and_groundN; auto.
apply groundNForm_le with (2 := H4); auto.
apply groundNForm_le with (2 := H5); auto.
intros f H f0 H0 p H1; inversion H1; apply lift_andor_or_groundN; auto.
apply groundNForm_le with (2 := H4); auto.
apply groundNForm_le with (2 := H5); auto.
intros f H f0 H0 p H1; inversion H1; apply lift_if_groundN; auto.
apply groundNForm_le with (2 := H4); auto.
apply groundNForm_le with (2 := H5); auto.
intros f H p H0; inversion H0; apply lift_neg_groundN; auto.
Qed.
 
Theorem correct_lift_quant :
 forall (f : form) (l : list Z), form2Prop l f <-> form2Prop l (lift_quant f).
intros f; elim f; simpl in |- *; auto; try (intuition; fail).
intros f0 H l; split; intros H0 x; case (H (x :: l)); auto.
intros f0 H l; split; intros (x, H0); exists x; case (H (x :: l)); auto.
intros f1 H f2 H0 l; case (H l); intros H1 H2; case (H0 l); intros H3 H4;
 case (correct_lift_andor_and (lift_quant f1) (lift_quant f2)) with (l := l);
 intuition.
intros f1 H f2 H0 l; case (H l); intros H1 H2; case (H0 l); intros H3 H4;
 case (correct_lift_andor_or (lift_quant f1) (lift_quant f2)) with (l := l);
 intuition.
intros f1 H f2 H0 l; case (H l); intros H1 H2; case (H0 l); intros H3 H4;
 case (correct_lift_if (lift_quant f1) (lift_quant f2)) with (l := l);
 intuition.
intros f1 H l; case (H l); intros H1 H2;
 case (correct_lift_neg (lift_quant f1)) with (l := l); 
 intuition.
Qed.