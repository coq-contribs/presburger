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
(*                       Process.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
Require Import List.
Require Import Normal.
Require Import Nat.
Require Import ZArithRing.
Require Import sTactic.
Require Import ReduceEq.
Require Import ReduceCong.
 
Fixpoint maxL (l : list Z) (l1 : list (nat * form)) {struct l1} : Z :=
  match l1 with
  | nil => 0%Z
  | (n1, Neg (Form.Eq a b)) :: l2 =>
      Zmax (maxL l l2) (Zsucc (exp2Z l a - exp2Z l b))
  | _ => 0%Z
  end.
 
Theorem maxPos : forall l l1, (0 <= maxL l l1)%Z.
intros l l1; elim l1; simpl in |- *; auto with zarith.
intros a; case a; simpl in |- *; auto with arith.
intros n; intros f; case f; simpl in |- *; auto with zarith.
intros f0; case f0; simpl in |- *; auto with zarith.
intros; apply Zle_trans with (maxL l l0); auto.
apply Zmax1; auto.
Qed.
 
Theorem onlyNeg_correct_aux :
 forall l l1,
 listNEqP l1 -> forall a, (maxL l l1 <= a)%Z -> formL2Prop a l l1.
intros l l1 H; elim H; simpl in |- *; auto.
intros n a b l0 H0 H1 H2 a0 H3; split; auto.
2: apply H2.
2: apply Zle_trans with (2 := H3).
2: apply Zmax1.
red in |- *; intros H4;
 absurd (Zmax (maxL l l0) (Zsucc (exp2Z l a - exp2Z l b)) <= a0)%Z; 
 auto.
apply Zlt_not_le.
replace (Zsucc (a0 * Z_of_nat n + exp2Z l b - exp2Z l b)) with
 (Zsucc (a0 * Z_of_nat n)); [ idtac | unfold Zsucc in |- *; ring ].
apply Zlt_le_trans with (Zsucc (a0 * Z_of_nat n)).
apply Zle_lt_succ.
pattern a0 at 1 in |- *; replace a0 with (a0 * Z_of_nat 1)%Z;
 [ idtac | simpl in |- *; ring ].
apply Zmult_le_compat_l; auto with zarith arith.
apply Znat.inj_le; auto with arith.
apply Zle_trans with (maxL l l0).
apply maxPos.
apply Zle_trans with (2 := H3).
apply Zmax1.
replace (exp2Z l a - exp2Z l b)%Z with (a0 * Z_of_nat n)%Z.
apply Zmax2.
rewrite H4; ring.
Qed.
 
Theorem onlyNeg_correct :
 forall l l1, listNEqP l1 -> exists a : _, formL2Prop a l l1.
intros l l1 H; exists (maxL l l1).
apply onlyNeg_correct_aux; auto with zarith.
Qed.
 
Fixpoint maxC (l1 : list (nat * form)) : nat :=
  match l1 with
  | nil => 1
  | (n1, Cong i a b) :: l2 => lcm i (maxC l2)
  | _ => 1
  end.
 
Theorem maxCPos : forall l, listCongP l -> 1 <= maxC l.
intros l H; elim H; simpl in |- *; auto.
intros n i a b l0 H0 H1 H2 H3; (apply le_trans with i; auto with arith).
case (divides_lcm1 i (maxC l0)); auto with arith.
intros m1 H4; rewrite H4; pattern i at 1 in |- *; replace i with (i * 1);
 [ idtac | ring ].
cut (0 < lcm i (maxC l0)).
rewrite H4; case m1; auto with arith.
intros H5; Contradict H5; rewrite mult_comm; simpl in |- *; auto with arith.
apply lcm_lt_O; auto.
Qed.
 
Theorem onlyNeg_correct_aux1 :
 forall a b l l1,
 listCongP l1 ->
 formL2Prop a l l1 -> formL2Prop (a + b * Z_of_nat (maxC l1)) l l1.
intros a b l l1 H; generalize a b; elim H; simpl in |- *; clear H a b l1;
 auto.
intros n i a b l0 H H0 H1 H2 a0 b0 ((m3, H3), H4).
split.
exists (m3 - Z_of_nat n * (b0 * Z_of_nat (div (lcm i (maxC l0)) i)))%Z.
rewrite H3.
cut
 (forall a b c d e,
  ((a - e * (b * Z_of_nat c)) * d)%Z = (a * d - e * (d * Z_of_nat c * b))%Z);
 [ intros H5; rewrite H5 | intros; ring ].
rewrite <- Znat.inj_mult; rewrite <- divides_div; auto.
ring.
apply divides_lcm1; auto.
generalize (maxCPos _ H1); auto with arith.
replace (b0 * Z_of_nat (lcm i (maxC l0)))%Z with
 (b0 * Z_of_nat (div (lcm i (maxC l0)) (maxC l0)) * Z_of_nat (maxC l0))%Z;
 auto.
cut (forall a b c, (a * b * c)%Z = (c * b * a)%Z);
 [ intros H5; rewrite H5 | intros; ring ].
rewrite <- Znat.inj_mult; rewrite <- divides_div; auto.
ring.
generalize (maxCPos _ H1); auto with arith.
apply divides_lcm2; auto.
generalize (maxCPos _ H1); auto with arith.
Qed.
 
Theorem onlyNeg_correct_aux2 :
 forall a b l l1,
 listCongP l1 ->
 formL2Prop a l l1 -> exists c : _, (b <= c)%Z /\ formL2Prop c l l1.
intros a b l l1 H H0; (case (Zle_or_lt b a); intros H1).
exists a; auto with zarith.
exists (a + (b - a) * Z_of_nat (maxC l1))%Z.
split.
pattern b at 1 in |- *; replace b with (a + (b - a) * Z_of_nat 1)%Z;
 [ idtac | simpl in |- *; ring ].
apply Zplus_le_compat_l.
apply Zmult_le_compat_l.
apply Znat.inj_le; apply maxCPos; auto.
apply Zlt_le_weak; unfold Zminus in |- *; apply Zlt_left_lt; auto.
apply onlyNeg_correct_aux1; auto.
Qed.
 
Theorem oneCongNeq_correct :
 forall l l1 l2,
 listNEqP l1 ->
 listCongP l2 ->
 ((exists c : _, formL2Prop c l l1 /\ formL2Prop c l l2) <->
  (exists c : _, formL2Prop c l l2)).
intros l l1 l2 H H1; split.
intros (c, (H2, H3)); exists c; auto.
intros (d, H2).
case (onlyNeg_correct_aux2 d (maxL l l1) l l2); auto.
intros c (H3, H4); exists c; split; auto.
apply onlyNeg_correct_aux; auto.
Qed.

(** Process the list produced by Sort and generate the appropriate reduction *) 
Definition processList
  (ls : list form *
        (list (nat * form) * (list (nat * form) * list (nat * form)))) :
  list form :=
  match ls with
  | (l1, ((m1, Form.Eq a1 b1) :: l2, (l3, l4))) =>
      Cong m1 a1 b1
      :: l1 ++
         reduceEqEq m1 a1 b1 l2 ++
         reduceEqNEq m1 a1 b1 l3 ++ reduceEqCong m1 a1 b1 l4
  | (l1, (nil, (l3, (m1, Cong i1 a1 b1) :: l4))) =>
      match reduceCongCong i1 m1 a1 b1 l4 with
      | (i2, (m2, (a2, (b2, l5)))) => Cong (gcd i2 m2) a2 b2 :: l1 ++ l5
      end
  | (l1, (l2, (l3, l4))) => l1
  end.
 
Theorem processList_correct :
 forall l l1 l2 l3 l4,
 Cnf1 (buildConj l1) ->
 listEqP l2 ->
 listNEqP l3 ->
 listCongP l4 ->
 ((exists a : _,
     form2Prop l (buildConj l1) /\
     formL2Prop a l l2 /\ formL2Prop a l l3 /\ formL2Prop a l l4) <->
  form2Prop l (buildConj (processList (l1, (l2, (l3, l4)))))) /\
 Cnf1 (buildConj (processList (l1, (l2, (l3, l4))))).
intros l l1 l2 l3 l4 H H0 H1 H2; inversion H0.
inversion H2; simpl in |- *.
split; auto; split.
intros (m5, (H5, H6)); auto.
case (onlyNeg_correct l l3); auto with arith.
intros a H5 H6; exists a; auto.
split.
split.
intros (c, (H8, (H9, (H10, (H11, H12))))).
generalize (reduceCongCong_correct i n a b (c :: l) l0 H4 H5 H6);
 case (reduceCongCong i n a b l0).
intros n1 p; case p; clear p.
intros n2 p; case p; clear p.
intros a1 p; case p; clear p.
intros b1 ll.
intros (H13, (H14, (H'14, H''14))); simpl in H13, H14.
case H13; clear H13; intros H13 H15; case H13; clear H13 H15; auto.
intros H15 H16; apply form2Prop_cons; auto.
case H15; intros m17 H17.
simpl in |- *;
 exists
  (c * Z_of_nat (div n2 (gcd n1 n2)) + m17 * Z_of_nat (div n1 (gcd n1 n2)))%Z.
rewrite H17.
cut
 (forall a b c d e, ((a * b + c * d) * e)%Z = (a * (e * b) + c * (e * d))%Z);
 [ intros H18; rewrite H18 | intros; ring ].
repeat rewrite <- Znat.inj_mult; repeat rewrite <- divides_div; auto.
ring.
apply gcd_lt_zero; auto.
apply divides_gcd1; auto.
apply gcd_lt_zero; auto.
apply divides_gcd2; auto.
CaseEq (reduceCongCong i n a b l0).
intros n1 p; case p; clear p.
intros n2 p; case p; clear p.
intros a1 p; case p; clear p.
intros b1 ll.
intros H8 H9.
generalize (form2Prop_cons_inv _ _ _ H9); intros ((m10, H10), H11).
case (gcd_bezout n1 n2); intros z1 (z2, H12).
rewrite <- H12 in H10.
generalize (reduceCongCong_correct i n a b ((m10 * z2)%Z :: l) l0 H4 H5 H6).
rewrite H8; simpl in |- *.
intros ((H13, H14), (H15, (H16, H17))); case H14; clear H13 H14.
split.
exists (m10 * z1)%Z; rewrite H10; ring.
case (form2Prop_app_inv _ _ _ H11); auto.
intros H13 H14.
case (oneCongNeq_correct l l3 ((n, Cong i a b) :: l0)); auto.
intros H18 H19; case H19; clear H18 H19; auto.
exists (m10 * z2)%Z; simpl in |- *; auto.
simpl in |- *; intros m5 (H18, (H19, H20)); exists m5; repeat split; auto.
case (form2Prop_app_inv _ _ _ H11); auto.
CaseEq (reduceCongCong i n a b l0).
intros n1 p; case p; clear p.
intros n2 p; case p; clear p.
intros a1 p; case p; clear p.
intros b1 ll.
intros H8; apply Cnf1_cons; auto.
apply Cnf1_app; auto.
generalize (reduceCongCong_correct i n a b (0%Z :: l) l0 H4 H5 H6).
rewrite H8; intuition.
unfold processList in |- *; lazy beta in |- *.
split.
split.
intros (m6, (H6, (H7, (H8, H'8)))).
simpl in H7; case H7; intros H9 H10.
apply form2Prop_cons.
simpl in |- *; exists m6; rewrite H9; ring.
apply form2Prop_app; auto.
apply form2Prop_app; auto.
case (reduceEqEq_correct n a b (m6 :: l) l0); simpl in |- *; auto.
intuition.
apply form2Prop_app; auto.
case (reduceEqNEq_correct n a b (m6 :: l) l3); simpl in |- *; auto.
intuition.
case (reduceEqCong_correct n a b (m6 :: l) l4); simpl in |- *; auto.
intuition.
intros H6.
case (form2Prop_cons_inv _ _ _ H6); auto.
intros H7 H8.
simpl in H7; case H7; clear H7; intros m7 H7.
exists m7; repeat split; auto.
case (form2Prop_app_inv _ _ _ H8); auto.
rewrite H7; ring.
case (reduceEqEq_correct n a b (m7 :: l) l0); simpl in |- *; auto.
case (form2Prop_app_inv _ _ _ H8); auto.
intros H9 H10.
case (form2Prop_app_inv _ _ _ H10); auto.
rewrite Zplus_comm; intuition.
case (reduceEqNEq_correct n a b (m7 :: l) l3); simpl in |- *; auto.
case (form2Prop_app_inv _ _ _ H8); auto.
intros H9 H10.
case (form2Prop_app_inv _ _ _ H10); auto.
intros H11 H12.
case (form2Prop_app_inv _ _ _ H12); auto.
rewrite Zplus_comm; intuition.
case (reduceEqCong_correct n a b (m7 :: l) l4); simpl in |- *; auto.
case (form2Prop_app_inv _ _ _ H8); auto.
intros H9 H10.
case (form2Prop_app_inv _ _ _ H10); auto.
intros H11 H12.
case (form2Prop_app_inv _ _ _ H12); auto.
rewrite Zplus_comm; intuition.
case (reduceEqEq_correct n a b l l0); auto.
case (reduceEqNEq_correct n a b l l3); auto.
case (reduceEqCong_correct n a b l l4); auto.
Qed.
Require Import GroundN.
 
Theorem processList_groundN :
 forall n l1 l2 l3 l4,
 listEqP l2 ->
 listNEqP l3 ->
 listCongP l4 ->
 groundNL n l1 ->
 groundNL2 n l2 ->
 groundNL2 n l3 ->
 groundNL2 n l4 -> groundNL n (processList (l1, (l2, (l3, l4)))).
intros n l1 l2 l3 l4 H; inversion H; simpl in |- *.
intros H1 H2; inversion H2; auto.
intros H7 H8 H9 H10; inversion H10.
inversion H14.
cut (groundNExp n a);
 [ intros H25 | apply groundNExp_le with (n := n2); auto ].
cut (groundNExp n b);
 [ intros H26 | apply groundNExp_le with (n := m0); auto ].
generalize (reduceCongCong_groundN i n n0 a b l H5 H16 H25 H26);
 case (reduceCongCong i n0 a b l).
intros i3 p0; case p0; clear p0.
intros m3 p0; case p0; clear p0.
intros a3 p0; case p0; clear p0.
intros b3 l5 (H27, (H28, H29)).
apply GNVCons; auto.
apply GNCong with (n := n) (m := n); auto.
intros H3 H4 H5 H6 H7 H8.
inversion H6.
inversion H12.
apply GNVCons; auto.
apply GNCong with (n := n2) (m := m0); auto.
apply groundNL_app; auto.
apply groundNL_app; auto.
apply reduceEqEq_groundN; auto.
apply groundNExp_le with (n := n2); auto.
apply groundNExp_le with (n := m0); auto.
apply groundNL_app; auto.
apply reduceEqNEq_groundN; auto.
apply groundNExp_le with (n := n2); auto.
apply groundNExp_le with (n := m0); auto.
apply reduceEqCong_groundN; auto.
apply groundNExp_le with (n := n2); auto.
apply groundNExp_le with (n := m0); auto.
Qed.