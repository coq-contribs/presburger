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
(*                           Nat.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(** Some extra properties of natural numbers *)
Require Import Arith.
Require Import ZArith.
Require Import ZArithRing.
Require Import sTactic.
Require Import Max.

Theorem le_ind2 :
 forall P : nat -> nat -> Prop,
 (forall m : nat, 0 <= m -> P 0 m) ->
 (forall m n : nat, n <= m -> P n m -> P (S n) (S m)) ->
 forall m n : nat, n <= m -> P n m.
intros P H H0 m n; generalize m; elim n; clear n m; auto with arith.
intros n H1 m; case m; auto with arith.
intros H2; Contradict H2; auto with arith.
Qed.
 
Theorem minus_O : forall n m : nat, n <= m -> n - m = 0.
intros n m H; elim H using le_ind2; auto.
Qed.

Theorem minus_O_le : forall n m : nat, n - m = 0 -> n <= m.
intros n; elim n; simpl in |- *; auto with arith.
intros n1 Rec m; case m; simpl in |- *; try (intros H; rewrite H);
 auto with arith.
Qed.

(** Check if [i] is strictly less than [o] *)
Fixpoint ltdec (i o : nat) {struct o} : bool :=
  match i, o with
  | O, O => false
  | O, S o1 => true
  | S i1, S o1 => ltdec i1 o1
  | S i1, O => false
  end.
 
Theorem ltdec_correct :
 forall i o : nat, match ltdec i o with
                   | true => i < o
                   | false => o <= i
                   end.
intros i; elim i; simpl in |- *; auto.
intros o; case o; simpl in |- *; auto with arith.
intros i1 H o; case o; simpl in |- *; auto with arith.
intros o1; generalize (H o1); case (ltdec i1 o1); auto with arith.
Qed.

Theorem pred_le : forall a b, a <= b -> pred a <= pred b.
intros a b; case a; case b; simpl in |- *; auto with arith.
Qed.
Hint Resolve pred_le: arith.

 
Fixpoint minus2 (m1 m2 : nat) {struct m2} : nat * nat :=
  match m1, m2 with
  | S m3, S m4 => minus2 m3 m4
  | _, _ => (m1, m2)
  end.
 
Theorem minus2_correct :
 forall m1 m2 : nat,
 match minus2 m1 m2 with
 | (m3, m4) => m3 = m1 - m2 /\ m4 = m2 - m1
 end.
intros m1 m2; generalize m1; elim m2; clear m1 m2; simpl in |- *;
 auto with arith.
intros m1; case m1; simpl in |- *; auto.
intros m2 Rec m1; case m1; simpl in |- *; auto.
Qed.
 
(** Definition of the gcd of two numbers *)
Fixpoint gcd1 (m1 m2 n : nat) {struct n} : nat :=
  match minus2 m1 m2 with
  | (O, O) => m1
  | (O, m3) => match n with
               | O => m3
               | S n1 => gcd1 m1 m3 n1
               end
  | (m3, _) => match n with
               | O => m3
               | S n1 => gcd1 m3 m2 n1
               end
  end.

Definition gcd m1 m2 := gcd1 m1 m2 (m1 + m2).
 
Theorem gcd1_bezout0 : forall n m : nat, gcd1 m 0 n = m.
intros n; elim n; simpl in |- *.
intros m; case m; simpl in |- *; auto.
intros n1 Rec m; case m; simpl in |- *; auto.
Qed.
 
Theorem gcd1_bezout1 : forall n m : nat, gcd1 0 m n = m.
intros n; elim n; simpl in |- *.
intros m; case m; simpl in |- *; auto.
intros n1 Rec m; case m; simpl in |- *; auto.
Qed.
 
Theorem gcd1_bezout :
 forall n m1 m2 : nat,
 m1 <= n ->
 m2 <= n ->
 exists x1 : Z,
   (exists x2 : Z,
      (Z_of_nat m1 * x1 + Z_of_nat m2 * x2)%Z = Z_of_nat (gcd1 m1 m2 n)).
intros n; elim n; simpl in |- *.
intros m1 m2 H1 H2; inversion H1; inversion H2; simpl in |- *; exists 0%Z;
 exists 0%Z; auto.
intros n0 H m1 m2 H0 H1; generalize (minus2_correct m1 m2);
 case (minus2 m1 m2).
intros n1 n2; case n1; case n2; auto.
intros H2; exists 1%Z; exists 0%Z; ring.
intros m3 (H2, H3).
cut (m1 < m2); [ intros H4 | idtac ].
generalize H0 H3 H4; case m1; clear H2 H0 H3 H4 m1.
intros H0 H3 H4; exists 0%Z; exists 1%Z; rewrite gcd1_bezout1.
replace (S m3) with m2; [ ring | rewrite H3; case m2; simpl in |- *; auto ].
intros n3 H0 H3 H4.
case (H (S n3) (S m3)); auto.
apply gt_S_le; red in |- *.
apply lt_le_trans with m2; auto with arith.
rewrite H3; auto.
generalize H1 H4; case m2; simpl in |- *; auto with arith.
intros n4 H2 H5; apply le_trans with n4; auto with arith.
intros x (y, H2).
exists (x - y)%Z; exists y; rewrite <- H2; rewrite H3.
rewrite Znat.inj_minus1; try ring.
apply lt_le_weak; auto.
apply lt_O_minus_lt; rewrite <- H3; auto with arith.
intros m3 (H2, H3).
cut (m2 < m1); [ intros H4 | idtac ].
generalize H1 H2 H4; case m2; clear H1 H2 H3 H4 m2.
intros H1 H3 H4; exists 1%Z; exists 0%Z; rewrite gcd1_bezout0.
replace (S m3) with m1; [ ring | rewrite H3; case m1; simpl in |- *; auto ].
intros n3 H1 H3 H4.
case (H (S m3) (S n3)); auto.
apply gt_S_le; red in |- *.
apply lt_le_trans with m1; auto with arith.
rewrite H3; generalize H4; case m1; simpl in |- *; auto with arith.
intros H2; Contradict H2; auto with arith.
apply gt_S_le; red in |- *.
apply lt_le_trans with m1; auto with arith.
intros x (y, H2).
exists x; exists (y - x)%Z; rewrite <- H2; rewrite H3.
rewrite Znat.inj_minus1; try ring.
apply lt_le_weak; auto.
apply lt_O_minus_lt; rewrite <- H2; auto with arith.
intros n3 n4 (H2, H3).
case (le_or_lt m1 m2); intros H4.
Contradict H2; rewrite minus_O; auto.
Contradict H3; rewrite minus_O; auto with arith.
Qed.
 
Theorem gcd1_O : forall n m, gcd1 0 m n = m /\ gcd1 m 0 n = m.
intros n; elim n.
intros m; case m; simpl in |- *; auto.
intros n1 Rec m; case m; simpl in |- *; auto.
Qed.
 
Theorem gcd_O1 : forall m, gcd 0 m = m.
intros m; case (gcd1_O m m); simpl in |- *; auto.
Qed.
 
Theorem gcd_O2 : forall m, gcd m 0 = m.
intros m; case (gcd1_O (m + 0) m); simpl in |- *; auto.
Qed.

(** Bezout equality *) 
Theorem gcd_bezout :
 forall m1 m2 : nat,
 exists x1 : Z,
   (exists x2 : Z,
      (Z_of_nat m1 * x1 + Z_of_nat m2 * x2)%Z = Z_of_nat (gcd m1 m2)).
intros m1 m2; unfold gcd in |- *; apply gcd1_bezout; auto with arith.
Qed.
 
(** Division of two numbers *)
Fixpoint div1 (m1 m2 n : nat) {struct n} : nat :=
  match minus2 m1 m2 with
  | (O, O) => 1
  | (O, _) => 0
  | (m3, _) => match n with
               | O => 0
               | S n1 => S (div1 m3 m2 n1)
               end
  end.

Definition div m1 m2 := div1 m1 m2 m1.
 
 
Theorem div1_correct :
 forall n m1 m2 : nat,
 m1 <= n -> 0 < m2 -> m2 * div1 m1 m2 n <= m1 /\ m1 < m2 * S (div1 m1 m2 n).
intros n; elim n; simpl in |- *; auto.
intros m1 m2 H H0; inversion H; auto.
generalize H0; case m2; simpl in |- *; auto with arith.
intros; rewrite mult_comm; simpl in |- *; auto with arith.
intros n0 H m1 m2 H0 H1; generalize (minus2_correct m1 m2);
 case (minus2 m1 m2).
intros n1 n2; case n1; case n2; simpl in |- *.
intros (H2, H3); replace m1 with m2; auto with arith.
rewrite mult_1_r; split; auto with arith.
rewrite mult_comm; simpl in |- *; apply le_lt_trans with (m2 + 0);
 auto with arith.
apply le_antisym; apply minus_O_le; auto.
intros n3 (H2, H3); rewrite <- mult_n_O; rewrite mult_1_r; simpl in |- *;
 split; auto with arith.
apply lt_O_minus_lt; rewrite <- H3; auto with arith.
intros n3 (H2, H3); case (H (S n3) m2); auto with arith.
apply gt_S_le; red in |- *.
apply lt_le_trans with m1; auto with arith.
rewrite H2; apply lt_minus; auto.
apply minus_O_le; auto.
intros H4 H5; split; auto.
rewrite <- mult_n_Sm.
apply le_trans with (S n3 + m2); auto with arith.
rewrite H2.
rewrite plus_comm; rewrite <- le_plus_minus; auto with arith.
apply minus_O_le; auto with arith.
rewrite <- mult_n_Sm.
apply le_lt_trans with (S n3 + m2); auto with arith.
rewrite H2.
rewrite plus_comm; rewrite <- le_plus_minus; auto with arith.
apply minus_O_le; auto with arith.
intros n3 n4 (H2, H3).
case (le_or_lt m1 m2); intros H4.
Contradict H2; rewrite minus_O; auto.
Contradict H3; rewrite minus_O; auto with arith.
Qed.
 
Theorem div_correct :
 forall m1 m2 : nat,
 0 < m2 -> m2 * div m1 m2 <= m1 /\ m1 < m2 * S (div m1 m2).
intros m1 m2 H; unfold div in |- *; apply div1_correct; auto.
Qed.
 
Definition divides m1 m2 := exists m3 : _, m2 = m1 * m3.
 
Theorem divides_refl : forall m, divides m m.
intros; exists 1; simpl in |- *; auto; ring.
Qed.
 
Theorem divides_trans :
 forall m1 m2 m3, divides m1 m2 -> divides m2 m3 -> divides m1 m3.
intros m1 m2 m3 (m1', H1) (m2', H2); exists (m1' * m2'); rewrite H2;
 rewrite H1; ring.
Qed.
 
Theorem divides_add :
 forall m1 m2 m3, divides m1 m2 -> divides m1 m3 -> divides m1 (m2 + m3).
intros m1 m2 m3 (m1', H1) (m2', H2); exists (m1' + m2'); rewrite H2;
 rewrite H1; ring.
Qed.
 
Theorem divides_minus :
 forall m1 m2 m3, divides m1 m2 -> divides m1 m3 -> divides m1 (m2 - m3).
intros m1 m2 m3 (m1', H1) (m2', H2); exists (m1' - m2'); rewrite H2;
 rewrite H1. auto with arith.
Qed.
Hint Resolve divides_refl divides_add divides_minus.
 
Theorem divides_gcd_aux :
 forall n m1 m2,
 0 < m1 ->
 m1 <= n ->
 0 < m2 -> m2 <= n -> divides (gcd1 m1 m2 n) m2 /\ divides (gcd1 m1 m2 n) m1.
intros n; elim n; simpl in |- *.
intros m1 m2 H H0; Contradict H0; auto with arith.
intros n' Rec; intros m1 m2 H1 H2 H3 H4; generalize (minus2_correct m1 m2);
 case (minus2 m1 m2).
intros n0; case n0; clear n0.
intros n1; case n1; clear n1.
intros (H5, H6); replace m1 with m2; auto.
apply le_antisym; apply minus_O_le; auto.
intros n1 (H5, H6); case (Rec m1 (S n1)); auto with arith.
apply lt_n_Sm_le; apply lt_le_trans with m2; auto.
apply lt_O_minus_lt; rewrite <- H6; auto with arith.
apply lt_n_Sm_le; apply lt_le_trans with m2; auto.
rewrite H6.
apply lt_minus; auto.
apply minus_O_le; auto.
intros H7 H8; split; auto.
replace m2 with (m1 + S n1); auto with arith.
rewrite H6.
apply sym_equal; apply le_plus_minus.
apply minus_O_le; auto.
intros n1 n2; case n2; clear n2.
intros (H5, H6); case (Rec (S n1) m2); auto with arith.
apply lt_n_Sm_le; apply lt_le_trans with m1; auto.
rewrite H5.
apply lt_minus; auto.
apply minus_O_le; auto.
apply lt_n_Sm_le; apply lt_le_trans with m1; auto.
apply lt_O_minus_lt; rewrite <- H5; auto with arith.
intros H7 H8; split; auto.
replace m1 with (m2 + S n1); auto with arith.
rewrite H5.
apply sym_equal; apply le_plus_minus.
apply minus_O_le; auto.
intros n2 (H5, H6).
case (le_or_lt m1 m2); intros H7.
Contradict H5; rewrite minus_O; auto.
Contradict H6; rewrite minus_O; auto with arith.
Qed.
 
Theorem divides_gcd1 : forall m1 m2, divides (gcd m1 m2) m1.
intros m1 m2; case m1.
rewrite gcd_O1; exists 0; simpl in |- *; auto.
intros m1'; case m2; simpl in |- *.
rewrite gcd_O2; exists 1; ring.
intros m2'; case (divides_gcd_aux (S m1' + S m2') (S m1') (S m2'));
 auto with arith.
Qed.
 
Theorem divides_gcd2 : forall m1 m2, divides (gcd m1 m2) m2.
intros m1 m2; case m1.
rewrite gcd_O1; exists 1; ring.
intros m1'; case m2; simpl in |- *.
rewrite gcd_O2; exists 0; ring.
intros m2'; case (divides_gcd_aux (S m1' + S m2') (S m1') (S m2'));
 auto with arith.
Qed.
 
Theorem divides_gcd1_aux :
 forall n m1 m2 m3,
 0 < m1 ->
 m1 <= n ->
 0 < m2 ->
 m2 <= n -> divides m3 m1 -> divides m3 m2 -> divides m3 (gcd1 m1 m2 n).
intros n; elim n; simpl in |- *.
intros m1 m2 m3 H H0; Contradict H0; auto with arith.
intros n' Rec m1 m2 m3 H1 H2 H3 H4 H5 H6.
generalize (minus2_correct m1 m2); case (minus2 m1 m2).
intros n0; case n0; clear n0; auto.
intros n1; case n1; clear n1; auto.
intros n1 (H7, H8); apply Rec; auto with arith.
apply lt_n_Sm_le; apply lt_le_trans with m2; auto.
apply lt_O_minus_lt; rewrite <- H8; auto with arith.
apply lt_n_Sm_le; apply lt_le_trans with m2; auto.
rewrite H8.
apply lt_minus; auto.
apply minus_O_le; auto.
rewrite H8; auto.
intros n1 n2; case n2; clear n2; auto.
intros (H7, H8); apply Rec; auto with arith.
apply lt_n_Sm_le; apply lt_le_trans with m1; auto.
rewrite H7.
apply lt_minus; auto.
apply minus_O_le; auto.
apply lt_n_Sm_le; apply lt_le_trans with m1; auto.
apply lt_O_minus_lt; rewrite <- H7; auto with arith.
rewrite H7; auto.
intros n2 (H7, H8).
case (le_or_lt m1 m2); intros H9.
Contradict H7; rewrite minus_O; auto.
Contradict H8; rewrite minus_O; auto with arith.
Qed.
 
Theorem divides_gcd3 :
 forall m1 m2 m3, divides m3 m1 -> divides m3 m2 -> divides m3 (gcd m1 m2).
intros m1 m2 m3; case m1.
rewrite gcd_O1; auto.
intros m1'; case m2; simpl in |- *.
rewrite gcd_O2; auto.
intros m2' H; apply (divides_gcd1_aux (S m1' + S m2') (S m1') (S m2'));
 auto with arith.
Qed.
 
Theorem mult_inv : forall m1 m2 m3, S m1 * m2 = S m1 * m3 -> m2 = m3.
intros m1 m2 m3 H; apply le_antisym; apply mult_S_le_reg_l with (n := m1);
 rewrite H; auto with arith.
Qed.
 
Theorem divides_id : forall m1 m2, divides m1 m2 -> divides m2 m1 -> m2 = m1.
intros m1 m2 (m3, H) (m4, H0).
generalize H H0; clear H H0; case m1; clear m1.
case m2; simpl in |- *; auto; intros; discriminate.
intros m1 H H0.
cut (m3 * m4 = 1); [ intros H1 | idtac ].
cut (m3 = 1); [ intros H2 | idtac ].
rewrite H; rewrite H2; ring.
generalize H1; case m3; case m4; simpl in |- *; auto.
intros n1; rewrite mult_comm; simpl in |- *; intros H2; discriminate.
intros n n0; case n0; simpl in |- *; auto.
intros n1; rewrite <- plus_n_Sm; simpl in |- *; intros; discriminate.
apply mult_inv with (m1 := m1).
pattern (S m1) at 2 in |- *; rewrite H0; rewrite H; ring.
Qed.
 
Theorem gcd_sym : forall m1 m2, gcd m1 m2 = gcd m2 m1.
intros m1 m2; apply divides_id; auto.
apply divides_gcd3; auto.
apply divides_gcd2; auto.
apply divides_gcd1; auto.
apply divides_gcd3; auto.
apply divides_gcd2; auto.
apply divides_gcd1; auto.
Qed.

(** Definition of the lcm of two numbers *) 
Definition lcm m1 m2 := div (m1 * m2) (gcd m1 m2).
 
Theorem divides_div :
 forall m1 m2, 0 < m1 -> divides m1 m2 -> m2 = m1 * div m2 m1.
intros m1 m2 H0 (m3, H).
case (div_correct m2 m1); auto.
intros H1 H2; auto.
apply le_antisym; auto.
case (le_or_lt m3 (div m2 m1)); intros H3.
pattern m2 at 1 in |- *; rewrite H; auto with arith.
Contradict H2; auto with arith.
apply le_not_lt.
pattern m2 at 2 in |- *; rewrite H; auto with arith.
Qed.
 
Theorem gcd_lt_zero : forall m1 m2, 0 < m1 -> 0 < m2 -> 0 < gcd m1 m2.
intros m1 m2 H H0.
generalize (divides_gcd1 m1 m2).
case (gcd m1 m2); simpl in |- *; auto with arith.
intros (m3, H1).
Contradict H; rewrite H1; simpl in |- *; auto with arith.
Qed.
 
Theorem mult_inv1 :
 forall m1 m2 m3 : nat, 0 < m1 -> m1 * m2 = m1 * m3 -> m2 = m3.
intros m1 m2 m3; case m1.
intros H; Contradict H; auto with arith.
intros n H H0; apply mult_inv with (m1 := n); auto.
Qed.
 
Theorem divides_lcm1 :
 forall m1 m2, 0 < m1 -> 0 < m2 -> divides m1 (lcm m1 m2).
intros m1 m2 H H0.
generalize (divides_gcd1 m1 m2); intros (m3, H1).
generalize (divides_gcd2 m1 m2); intros (m4, H2).
exists m4.
apply mult_inv1 with (m1 := gcd m1 m2).
apply gcd_lt_zero; auto.
unfold lcm in |- *; simpl in |- *.
rewrite <- divides_div.
pattern m2 at 1 in |- *; rewrite H2; ring.
apply gcd_lt_zero; auto.
apply divides_trans with (m2 := m1); auto.
apply divides_gcd1.
exists m2; ring.
Qed.
 
Theorem lcm_sym : forall a b, lcm a b = lcm b a.
intros a b; unfold lcm in |- *.
rewrite (mult_comm a); rewrite gcd_sym; auto.
Qed.
 
Theorem divides_lcm2 :
 forall m1 m2, 0 < m1 -> 0 < m2 -> divides m2 (lcm m1 m2).
intros m1 m2 H H0; rewrite lcm_sym; apply divides_lcm1; auto.
Qed.
 
Theorem divides_lcm3 :
 forall m1 m2 m3,
 0 < m1 -> 0 < m2 -> divides m1 m3 -> divides m2 m3 -> divides (lcm m1 m2) m3.
intros m1 m2 m3; case m3.
intros H H0 H1 H2; exists 0; ring.
clear m3; intros m3 H1 H2 H3 H4.
generalize (divides_gcd1 m1 m2); intros (m6, H5).
generalize (divides_gcd2 m1 m2); intros (m7, H6).
apply divides_trans with (gcd (lcm m1 m2) (S m3)); auto.
2: apply divides_gcd2.
generalize (divides_gcd1 (lcm m1 m2) (S m3)); intros (m8, H7).
pattern (lcm m1 m2) at 1 in |- *; rewrite H7.
replace m8 with 1; [ exists 1; ring | idtac ].
cut (divides (gcd m1 m2 * m8) (gcd m1 m2)); [ intros (m9, H8) | idtac ].
cut (1 = m8 * m9).
case m9.
rewrite mult_comm; simpl in |- *; intros; discriminate.
intros n1; case m8; simpl in |- *; auto.
intros n2; case n2; simpl in |- *; auto.
intros n3; rewrite <- plus_n_Sm; simpl in |- *; intros; discriminate.
apply mult_inv1 with (m1 := gcd m1 m2).
apply gcd_lt_zero; auto.
pattern (gcd m1 m2) at 1 in |- *; rewrite H8; ring.
apply divides_gcd3.
cut (divides m2 (gcd (lcm m1 m2) (S m3))); [ intros (m9, H8) | idtac ].
exists m9.
apply mult_inv1 with (m1 := m2); auto.
apply trans_equal with (gcd m1 m2 * (m2 * m9 * m8)); [ idtac | ring ].
rewrite <- H8; rewrite <- H7.
rewrite (mult_comm m2); unfold lcm in |- *; apply divides_div; auto.
apply gcd_lt_zero; auto.
apply divides_trans with m1; auto.
apply divides_gcd1.
exists m2; ring.
apply divides_gcd3; auto.
apply divides_lcm2; auto.
cut (divides m1 (gcd (lcm m1 m2) (S m3))); [ intros (m9, H8) | idtac ].
exists m9.
apply mult_inv1 with (m1 := m1); auto.
apply trans_equal with (gcd m1 m2 * (m1 * m9 * m8)); [ idtac | ring ].
rewrite <- H8; rewrite <- H7.
unfold lcm in |- *; apply divides_div; auto.
apply gcd_lt_zero; auto.
apply divides_trans with m1; auto.
apply divides_gcd1.
exists m2; ring.
apply divides_gcd3; auto.
apply divides_lcm1; auto.
Qed.

Theorem lcm_lt_O : forall a b, 0 < a -> 0 < b -> 0 < lcm a b.
intros a b H H1; case (le_or_lt (lcm a b) 0); auto; intros H2.
cut (lcm a b = 0); [ intros H3 | inversion H2; auto ].
absurd (0 < a * b); auto with arith.
rewrite (divides_div (gcd a b) (a * b)); auto.
change (~ 0 < gcd a b * lcm a b) in |- *.
rewrite H3; rewrite mult_comm; simpl in |- *; auto with arith.
apply gcd_lt_zero; auto.
apply divides_trans with a; auto.
apply divides_gcd1; auto.
exists b; ring; auto.
generalize H H1; case a; simpl in |- *.
intros H6; Contradict H6; auto with arith.
intros n; case n; simpl in |- *; auto with arith.
Qed.

Theorem mult_lt_ZERO : forall a b, 0 < a -> 0 < b -> 0 < a * b.
intros a; case a.
intros b H; Contradict H; auto with arith.
intros a1 b H; case b; simpl in |- *; auto with arith.
intros H1; Contradict H1; auto with arith.
Qed.
 
Theorem div_lt_ZERO :
 forall a b, 0 < a -> 0 < b -> a = div a b * b -> 0 < div a b.
intros a b H H0; case (div a b); simpl in |- *; auto with arith.
intros H1; Contradict H; rewrite H1; auto with arith.
Qed.

Theorem max_Or : forall a b, max a b = a \/ max a b = b.
intros a; elim a; simpl in |- *; auto.
intros n H b; case b; simpl in |- *; auto.
intros n0; case (H n0); intros H1; rewrite H1; auto.
Qed.
