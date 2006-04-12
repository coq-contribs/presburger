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
(*                    ReduceCong.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
Require Import List.
Require Import Normal.
Require Import Nat.
Require Import ZArithRing.
Require Import sTactic.
Require Import GroundN.
 
(** Reduce a congruence with another congruence *)
Fixpoint reduceCongCong1 (i m1 m2 : nat) (a1 a2 b1 b2 : exp) 
 (n : nat) {struct n} : nat * (exp * (exp * form)) :=
  match minus2 m1 m2 with
  | (O, O) => (m1, (a1, (b1, Cong i (Plus a2 b1) (Plus b2 a1))))
  | (O, m3) =>
      match n with
      | O => (m1, (a1, (b1, Cong i (Plus a2 b1) (Plus b2 a1))))
      | S n1 => reduceCongCong1 i m1 m3 a1 (Plus a2 b1) b1 (Plus b2 a1) n1
      end
  | (m3, _) =>
      match n with
      | O => (m1, (a1, (b1, Cong i (Plus a2 b1) (Plus b2 a1))))
      | S n1 => reduceCongCong1 i m2 m3 a2 (Plus a1 b2) b2 (Plus b1 a2) n1
      end
  end.
 
Theorem reduceCongCong1_correct :
 forall i n m1 m2 a1 a2 b1 b2 l,
 0 < m1 ->
 m1 <= n ->
 0 < m2 ->
 m2 <= n ->
 match reduceCongCong1 i m1 m2 a1 a2 b1 b2 n with
 | (m3, (a3, (b3, c3))) =>
     (congZ i (exp2Z (tail l) a1)
        (nth 0 l 0%Z * Z_of_nat m1 + exp2Z (tail l) b1) /\
      congZ i (exp2Z (tail l) a2)
        (nth 0 l 0%Z * Z_of_nat m2 + exp2Z (tail l) b2) <->
      congZ i (exp2Z (tail l) a3)
        (nth 0 l 0%Z * Z_of_nat m3 + exp2Z (tail l) b3) /\
      form2Prop (tail l) c3) /\ Cnf2 c3 /\ 0 < m3
 end.
intros i n; elim n; simpl in |- *.
intros m1 m2 a1 a2 b1 b2 l H H1; Contradict H; inversion H1; auto with arith.
intros n1 Rec m1 m2 a1 a22 b1 b2 l H1 H2 H3 H4.
generalize (minus2_correct m1 m2); case (minus2 m1 m2).
intros n0 n2; case n0; case n2; simpl in |- *.
intros (H6, H7); replace m1 with m2.
split; auto; split; intros (H8, H9); split; auto.
case H8; intros m10 H10; case H9; intros m11 H11; exists (m11 - m10)%Z;
 rewrite H10; rewrite H11; ring.
case H8; intros m10 H10; case H9; intros m11 H11; exists (m11 + m10)%Z;
 apply Zplus_reg_l with (n := exp2Z (tail l) b1);
 rewrite (Zplus_comm (exp2Z (tail l) b1)); rewrite H11; 
 rewrite H10; ring.
apply le_antisym; apply minus_O_le; auto.
intros n3 (H5, H6).
cut (S n3 <= n1); [ intros Z1 | idtac ].
cut (m1 <= n1); [ intros Z2 | idtac ].
cut (0 < S n3); [ intros Z3 | auto with arith ].
generalize (Rec m1 (S n3) a1 (Plus a22 b1) b1 (Plus b2 a1) l H1 Z2 Z3 Z1).
case (reduceCongCong1 i m1 (S n3) a1 (Plus a22 b1) b1 (Plus b2 a1) n1).
intros n4 p; case p.
intros e p0; case p0.
intros e0 f.
intros (H7, (HH1, HH2)); split; auto; split; intros (H8, H9).
cut
 (congZ i (exp2Z (tail l) (Plus a22 b1))
    (nth 0 l 0%Z * Z_of_nat (S n3) + exp2Z (tail l) (Plus b2 a1)));
 [ intros H10; intuition | idtac ].
case H8; intros m10 H10.
case H9; intros m11 H11.
exists (m11 - m10)%Z; rewrite H6; simpl in |- *; rewrite H10; rewrite H11;
 rewrite Znat.inj_minus1; try ring.
apply minus_O_le; auto.
case H7; intros HH H10; case H10; clear HH H10; auto.
intros H10 H11; split; auto.
case H10; intros m12 H12; case H11; rewrite H6; simpl in |- *;
 rewrite Znat.inj_minus1; try intros m13 H13.
exists (m12 + m13)%Z.
apply Zplus_reg_l with (n := exp2Z (tail l) b1);
 rewrite (Zplus_comm (exp2Z (tail l) b1)); rewrite H13; 
 rewrite H12; ring.
apply minus_O_le; auto.
apply lt_n_Sm_le; apply lt_le_trans with m2; auto.
apply lt_O_minus_lt; rewrite <- H6; auto with arith.
rewrite H6.
apply lt_n_Sm_le; apply lt_le_trans with m2; auto with arith.
apply lt_minus; auto.
apply minus_O_le; auto.
intros n3 (H5, H6).
cut (S n3 <= n1); [ intros Z1 | idtac ].
cut (m2 <= n1); [ intros Z2 | idtac ].
cut (0 < S n3); [ intros Z3 | auto with arith ].
generalize (Rec m2 (S n3) a22 (Plus a1 b2) b2 (Plus b1 a22) l H3 Z2 Z3 Z1).
case (reduceCongCong1 i m2 (S n3) a22 (Plus a1 b2) b2 (Plus b1 a22) n1).
intros n4 p; case p.
intros e p0; case p0.
intros e0 f.
intros (H7, (E, HH2)); split; auto; split; intros (H8, H9).
cut
 (congZ i (exp2Z (tail l) (Plus a1 b2))
    (nth 0 l 0%Z * Z_of_nat (S n3) + exp2Z (tail l) (Plus b1 a22)));
 [ intros H10; intuition | idtac ].
case H9; intros m11 H11.
case H8; intros m10 H10.
exists (m10 - m11)%Z; rewrite H5; simpl in |- *; rewrite H10; rewrite H11;
 rewrite Znat.inj_minus1; try ring.
apply minus_O_le; auto.
case H7; intros HH H10; case H10; clear HH H10; auto.
intros H10 H11; split; auto.
case H10; intros m12 H12; case H11; rewrite H5; simpl in |- *;
 rewrite Znat.inj_minus1; try intros m13 H13.
exists (m12 + m13)%Z.
apply Zplus_reg_l with (n := exp2Z (tail l) b2);
 rewrite (Zplus_comm (exp2Z (tail l) b2)); rewrite H13; 
 rewrite H12; ring.
apply minus_O_le; auto.
apply lt_n_Sm_le; apply lt_le_trans with m1; auto.
apply lt_O_minus_lt; rewrite <- H5; auto with arith.
rewrite H5.
apply lt_n_Sm_le; apply lt_le_trans with m1; auto with arith.
apply lt_minus; auto.
apply minus_O_le; auto.
intros n3 n4 (H5, H6); absurd (m1 <= m2); auto.
apply lt_not_le; apply lt_O_minus_lt; rewrite <- H5; auto with arith.
apply lt_le_weak; apply lt_O_minus_lt; rewrite <- H6; auto with arith.
Qed.
 
Theorem reduceCongCong1_groundN :
 forall p i n m1 m2 a1 a2 b1 b2,
 groundNExp n a1 ->
 groundNExp n a2 ->
 groundNExp n b1 ->
 groundNExp n b2 ->
 match reduceCongCong1 i m1 m2 a1 a2 b1 b2 p with
 | (m3, (a3, (b3, c3))) =>
     groundNExp n a3 /\ groundNExp n b3 /\ groundNForm n c3
 end.
intros p; elim p; simpl in |- *.
intros i n m1 m2 a1 a2 b1 b2 H H0 H1 H2; case (minus2 m1 m2).
intros n0 n1; case n0; case n1; simpl in |- *; repeat split; auto.
apply GNCong with (n := n) (m := n); auto;
 apply GNPlus with (n := n) (m := n); auto.
apply GNCong with (n := n) (m := n); auto;
 apply GNPlus with (n := n) (m := n); auto.
apply GNCong with (n := n) (m := n); auto;
 apply GNPlus with (n := n) (m := n); auto.
apply GNCong with (n := n) (m := n); auto;
 apply GNPlus with (n := n) (m := n); auto.
intros n H i n0 m1 m2 a1 a2 b1 b2 H0 H1 H2 H3; case (minus2 m1 m2).
intros n1 n2; case n1; case n2; simpl in |- *; repeat split; auto.
apply GNCong with (n := n0) (m := n0); auto;
 apply GNPlus with (n := n0) (m := n0); auto.
intros n3.
cut (groundNExp n0 (Plus a2 b1)); [ intros H4 | auto ].
cut (groundNExp n0 (Plus b2 a1)); [ intros H5 | auto ].
generalize (H i n0 m1 (S n3) _ _ _ _ H0 H4 H2 H5);
 case (reduceCongCong1 i m1 (S n3) a1 (Plus a2 b1) b1 (Plus b2 a1) n).
intros n4 p0; case p0; clear p0.
intros a3 p0; case p0; clear p0; auto.
apply GNPlus with (n := n0) (m := n0); auto.
apply GNPlus with (n := n0) (m := n0); auto.
intros n3.
cut (groundNExp n0 (Plus a1 b2)); [ intros H4 | auto ].
cut (groundNExp n0 (Plus b1 a2)); [ intros H5 | auto ].
generalize (H i n0 m2 (S n3) _ _ _ _ H1 H4 H3 H5);
 case (reduceCongCong1 i m2 (S n3) a2 (Plus a1 b2) b2 (Plus b1 a2) n).
intros n4 p0; case p0; clear p0.
intros a3 p0; case p0; clear p0; auto.
apply GNPlus with (n := n0) (m := n0); auto.
apply GNPlus with (n := n0) (m := n0); auto.
intros n3 n'3.
cut (groundNExp n0 (Plus a1 b2)); [ intros H4 | auto ].
cut (groundNExp n0 (Plus b1 a2)); [ intros H5 | auto ].
generalize (H i n0 m2 (S n'3) _ _ _ _ H1 H4 H3 H5);
 case (reduceCongCong1 i m2 (S n'3) a2 (Plus a1 b2) b2 (Plus b1 a2) n).
intros n4 p0; case p0; clear p0.
intros a3 p0; case p0; clear p0; auto.
apply GNPlus with (n := n0) (m := n0); auto.
apply GNPlus with (n := n0) (m := n0); auto.
Qed.

(** Iteration *) 
Fixpoint reduceCongCong (i1 m1 : nat) (a1 b1 : exp) 
 (l : list (nat * form)) {struct l} :
 nat * (nat * (exp * (exp * list form))) :=
  match l with
  | (m2, Cong i2 a2 b2) :: l1 =>
      match lcm i1 i2 with
      | i3 =>
          match div i3 i1 with
          | n1 =>
              match div i3 i2 with
              | n2 =>
                  match
                    reduceCongCong1 i3 (n1 * m1) (n2 * m2) 
                      (scal n1 a1) (scal n2 a2) (scal n1 b1) 
                      (scal n2 b2) (n1 * m1 + n2 * m2)
                  with
                  | (m4, (a4, (b4, f4))) =>
                      match reduceCongCong i3 m4 a4 b4 l1 with
                      | (i5, (m5, (a5, (b5, l5)))) =>
                          (i5, (m5, (a5, (b5, f4 :: l5))))
                      end
                  end
              end
          end
      end
  | _ => (i1, (m1, (a1, (b1, nil))))
  end.
 
Theorem reduceCongCong_correct :
 forall i m1 a b l l1,
 0 < i ->
 0 < m1 ->
 listCongP l1 ->
 match reduceCongCong i m1 a b l1 with
 | (i3, (m3, (a3, (b3, l3)))) =>
     (congZ i (exp2Z (tail l) a)
        (nth 0 l 0%Z * Z_of_nat m1 + exp2Z (tail l) b) /\
      formL2Prop (nth 0 l 0%Z) (tail l) l1 <->
      congZ i3 (exp2Z (tail l) a3)
        (nth 0 l 0%Z * Z_of_nat m3 + exp2Z (tail l) b3) /\
      form2Prop (tail l) (buildConj l3)) /\
     Cnf1 (buildConj l3) /\ 0 < i3 /\ 0 < m3
 end.
intros i m1 a b l l1 HH H H1; generalize i m1 a b l HH H; elim H1;
 simpl in |- *; clear HH H i m1 a b l H1.
intuition.
intros m2 i2 a2 b2 l HH0 H H1 Rec.
intros i1 m1 a1 b1 l2 HH1 H2.
cut (0 < div (lcm i1 i2) i1 * m1); [ intros Z1 | apply mult_lt_ZERO; auto ].
2: apply div_lt_ZERO; auto.
2: apply lcm_lt_O; auto.
2: rewrite mult_comm; apply divides_div; auto.
2: apply divides_lcm1; auto.
cut
 (div (lcm i1 i2) i1 * m1 <=
  div (lcm i1 i2) i1 * m1 + div (lcm i1 i2) i2 * m2);
 [ intros Z2 | auto with arith ].
cut (0 < div (lcm i1 i2) i2 * m2); [ intros Z3 | apply mult_lt_ZERO; auto ].
2: apply div_lt_ZERO; auto.
2: apply lcm_lt_O; auto.
2: rewrite mult_comm; apply divides_div; auto.
2: apply divides_lcm2; auto.
cut
 (div (lcm i1 i2) i2 * m2 <=
  div (lcm i1 i2) i1 * m1 + div (lcm i1 i2) i2 * m2);
 [ intros Z4 | auto with arith ].
generalize
 (reduceCongCong1_correct (lcm i1 i2)
    (div (lcm i1 i2) i1 * m1 + div (lcm i1 i2) i2 * m2)
    (div (lcm i1 i2) i1 * m1) (div (lcm i1 i2) i2 * m2)
    (scal (div (lcm i1 i2) i1) a1) (scal (div (lcm i1 i2) i2) a2)
    (scal (div (lcm i1 i2) i1) b1) (scal (div (lcm i1 i2) i2) b2) l2 Z1 Z2 Z3
    Z4).
case
 (reduceCongCong1 (lcm i1 i2) (div (lcm i1 i2) i1 * m1)
    (div (lcm i1 i2) i2 * m2) (scal (div (lcm i1 i2) i1) a1)
    (scal (div (lcm i1 i2) i2) a2) (scal (div (lcm i1 i2) i1) b1)
    (scal (div (lcm i1 i2) i2) b2)
    (div (lcm i1 i2) i1 * m1 + div (lcm i1 i2) i2 * m2)).
intros m3 p; case p; clear p.
intros a3 p; case p; clear p.
intros b3 f (H3, (Z5', Z5)).
cut (0 < lcm i1 i2); [ intros Z6 | apply lcm_lt_O; auto ].
generalize (Rec (lcm i1 i2) m3 a3 b3 l2 Z6 Z5); clear Rec.
case (reduceCongCong (lcm i1 i2) m3 a3 b3 l).
intros i4 p; case p; clear p.
intros m4 p; case p; clear p.
intros a4 p; case p; clear p.
intros b4 l0 (H4, (H'4, (H''4, H'''4))).
split; auto.
split.
intros (H5, (H6, H7)).
case H3; intros H8; case H8; clear H3 H8.
split.
repeat rewrite scal_correct.
case H5; intros m8 H8; exists m8; repeat rewrite scal_correct;
 repeat rewrite Znat.inj_mult; rewrite H8.
cut
 (forall a b c d e : Z, (a * (b + c + d * e))%Z = (a * (b + c) + e * a * d)%Z);
 [ intros H9; rewrite H9; rewrite <- Znat.inj_mult; rewrite <- divides_div;
    auto
 | intros; ring ].
ring.
apply divides_lcm1; auto.
case H6; intros m8 H8; exists m8; repeat rewrite scal_correct;
 repeat rewrite Znat.inj_mult; rewrite H8.
cut
 (forall a b c d e : Z, (a * (b + c + d * e))%Z = (a * (b + c) + e * a * d)%Z);
 [ intros H9; rewrite H9; rewrite <- Znat.inj_mult; rewrite <- divides_div;
    auto
 | intros; ring ].
ring.
apply divides_lcm2; auto.
intros H8 H9 H10; clear H10; split.
intuition.
cut (form2Prop (tail l2) (buildConj l0)); [ idtac | intuition ].
case l0; simpl in |- *; auto.
intros (H5, H6).
cut (form2Prop (tail l2) f);
 [ intros HZ1 | generalize H6; case l0; simpl in |- *; intuition ].
cut (form2Prop (tail l2) (buildConj l0));
 [ intros HZ2; clear H6 | generalize H6; case l0; simpl in |- *; intuition ].
case H3.
intros H6 H7; case H7; clear H6 H7.
split; auto.
case H4; intros H6 H7; case H7; clear H6 H7; auto.
repeat rewrite scal_correct; intros H6 H7.
split.
case H6; clear H6; intros m6 H6.
exists m6.
apply Zeq_mult_simpl with (c := Z_of_nat (div (lcm i1 i2) i1)).
apply Compare.not_eq_sym; apply Zorder.Zlt_not_eq.
replace 0%Z with (Z_of_nat 0); [ apply Znat.inj_lt | simpl in |- *; auto ].
apply div_lt_ZERO; auto; rewrite mult_comm; apply divides_div; auto.
apply divides_lcm1; auto.
rewrite (Zmult_comm (exp2Z (tail l2) a1)); rewrite H6.
cut
 (forall a b c d e : Z, ((a + b + c * d) * e)%Z = ((a + b) * e + d * e * c)%Z);
 [ intros H8; rewrite H8 | intros; ring ].
repeat rewrite <- Znat.inj_mult; rewrite <- divides_div;
 repeat rewrite Znat.inj_mult; try ring; auto.
apply divides_lcm1; auto.
split.
case H7; clear H7; intros m7 H7.
exists m7.
apply Zeq_mult_simpl with (c := Z_of_nat (div (lcm i1 i2) i2)).
apply Compare.not_eq_sym; apply Zorder.Zlt_not_eq.
replace 0%Z with (Z_of_nat 0); [ apply Znat.inj_lt | simpl in |- *; auto ].
apply div_lt_ZERO; auto; rewrite mult_comm; apply divides_div; auto.
apply divides_lcm2; auto.
rewrite (Zmult_comm (exp2Z (tail l2) a2)); rewrite H7.
cut
 (forall a b c d e : Z, ((a + b + c * d) * e)%Z = ((a + b) * e + d * e * c)%Z);
 [ intros H8; rewrite H8 | intros; ring ].
repeat rewrite <- Znat.inj_mult; rewrite <- divides_div;
 repeat rewrite Znat.inj_mult; try ring; auto.
apply divides_lcm2; auto.
intuition.
Qed.
 
Theorem reduceCongCong_groundN :
 forall i n m1 a b l,
 listCongP l ->
 groundNL2 n l ->
 groundNExp n a ->
 groundNExp n b ->
 match reduceCongCong i m1 a b l with
 | (i3, (m3, (a3, (b3, l3)))) =>
     groundNExp n a3 /\ groundNExp n b3 /\ groundNL n l3
 end.
intros i n m1 a b l H; generalize i n m1 a b; elim H; simpl in |- *; auto;
 clear H i n m1 a b.
intros n i a b l0 H H0 H1 H2 i0 n0 m1 a0 b0 H3 H4 H5.
cut (groundNExp n0 (scal (div (lcm i0 i) i0) a0)); [ intros H6 | idtac ].
cut (groundNExp n0 (scal (div (lcm i0 i) i) a)); [ intros H7 | idtac ].
cut (groundNExp n0 (scal (div (lcm i0 i) i0) b0)); [ intros H8 | idtac ].
cut (groundNExp n0 (scal (div (lcm i0 i) i) b)); [ intros H9 | idtac ].
generalize
 (reduceCongCong1_groundN (div (lcm i0 i) i0 * m1 + div (lcm i0 i) i * n)
    (lcm i0 i) n0 (div (lcm i0 i) i0 * m1) (div (lcm i0 i) i * n) _ _ _ _ H6
    H7 H8 H9);
 case
  (reduceCongCong1 (lcm i0 i) (div (lcm i0 i) i0 * m1) 
     (div (lcm i0 i) i * n) (scal (div (lcm i0 i) i0) a0)
     (scal (div (lcm i0 i) i) a) (scal (div (lcm i0 i) i0) b0)
     (scal (div (lcm i0 i) i) b)
     (div (lcm i0 i) i0 * m1 + div (lcm i0 i) i * n)).
intros m3 p; case p; clear p.
intros a3 p; case p; clear p; intros b3 l3.
intros (H10, (H11, H12)).
inversion H3.
generalize (H2 (lcm i0 i) n0 m3 a3 b3 H18 H10 H11);
 case (reduceCongCong (lcm i0 i) m3 a3 b3 l0).
intros i4 p; case p; clear p.
intros m4 p; case p; clear p.
intros a4 p; case p; clear p.
intros b4 l4 (H19, (H20, H21)); auto.
inversion H3.
inversion H12.
apply groundNExp_le with (n := m0); auto.
apply scal_groundN; auto.
apply scal_groundN; auto.
inversion H3.
inversion H10.
apply groundNExp_le with (n := n2); auto.
apply scal_groundN; auto.
apply scal_groundN; auto.
Qed.