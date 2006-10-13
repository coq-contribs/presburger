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
(*                          Cong.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(** * Congruence *)
Require Export ZArith.
Require Import Zdivides.
Require Import ZArithRing.
Require Import sTactic.

(** Useful lemmae *)

Theorem Zabs_absolu : forall z : Z, Zabs z = Z_of_nat (Zabs_nat z).
intros z; case z; simpl in |- *; auto; intros p; apply POS_inject.
Qed.
 
Theorem Zlt_ZERO_minus : forall a b : Z, (a < b)%Z -> (0 < b - a)%Z.
intros; unfold Zminus in |- *; apply Zlt_left_lt; auto.
Qed.
 
Theorem lt_inj : forall a b : nat, (Z_of_nat a < Z_of_nat b)%Z -> a < b.
intros a b H; case (le_or_lt b a); auto; intros H0.
Contradict H; apply Zle_not_lt; apply Znat.inj_le; auto with zarith arith.
Qed.
 
(** Definition of the congruence *)
Definition congZ (i : nat) (a b : Z) :=
  exists c : Z, a = (b + c * Z_of_nat i)%Z.
 

(** Some basic properties of the congruence *)
Theorem congZ_id : forall (i : nat) (a : Z), congZ i a a.
intros i a; exists 0%Z; simpl in |- *; ring.
Qed.
Hint Resolve congZ_id.
 
Theorem congZ_sym : forall (a b : Z) (i : nat), congZ i a b -> congZ i b a.
intros a b i (x, H); exists (- x)%Z; rewrite H; ring.
Qed.
 
Theorem congZ_trans :
 forall (a b c : Z) (i : nat), congZ i a b -> congZ i b c -> congZ i a c.
intros a b c i (x, H) (y, H1); exists (x + y)%Z; rewrite H; rewrite H1; ring.
Qed.
 
Theorem congZ_plus :
 forall (a b c d : Z) (i : nat),
 congZ i a b -> congZ i c d -> congZ i (a + c) (b + d).
intros a b c d i (x, H) (y, H1); exists (x + y)%Z; rewrite H; rewrite H1;
 ring.
Qed.
 
Theorem congZ_minus :
 forall (a b c d : Z) (i : nat),
 congZ i a b -> congZ i c d -> congZ i (a - c) (b - d).
intros a b c d i (x, H) (y, H1); exists (x - y)%Z; rewrite H; rewrite H1;
 ring.
Qed.
 
Theorem congZ_mult :
 forall (a b : Z) (i j : nat),
 congZ i a b -> congZ (i * j) (a * Z_of_nat j) (b * Z_of_nat j).
intros a b i j (x, H); exists x; rewrite H; rewrite Znat.inj_mult; ring.
Qed.

Definition fcong (i : nat) (a b : Z) :=
  match i with
  | O => 0
  | S i1 =>
      let ab := (a - b)%Z in
      match (ab - Z_of_nat i * Zquotient ab (Z_of_nat i))%Z with
      | Zneg p1 => Zabs_nat (Z_of_nat i + Zneg p1)
      | p => Zabs_nat p
      end
  end.
 
 
Theorem fcong_correct :
 forall (i : nat) (a b : Z),
 i <> 0 -> congZ i a (b + Z_of_nat (fcong i a b)) /\ fcong i a b < i.
intros i a b; unfold fcong in |- *; case i; auto.
intros H; elim H; auto.
intros n H.
case (ZquotientProp (a - b) (Z_of_nat (S n))); auto with arith.
simpl in |- *; red in |- *; intros; discriminate.
intros x (H1, H2).
replace (a - b - Z_of_nat (S n) * Zquotient (a - b) (Z_of_nat (S n)))%Z with
 x; [ idtac | pattern (a - b)%Z at 1 in |- *; rewrite H1; ring ].
generalize H1 H2; case x; clear H1 H2 x.
intros H1 (H2, H3); split; simpl in |- *.
exists (Zquotient (a - b) (Z_of_nat (S n))).
apply trans_equal with (b + (a - b))%Z.
ring.
pattern (a - b)%Z at 1 in |- *; rewrite H1; ring; auto with arith.
auto with arith.
intros p H1 (H2, H3); split; auto.
exists (Zquotient (a - b) (Z_of_nat (S n))).
apply trans_equal with (b + (a - b))%Z.
ring.
pattern (a - b)%Z at 1 in |- *; rewrite H1; ring_simplify;
  eapply Zplus_eq_compat; [reflexivity | simpl; apply POS_inject].
case (le_or_lt (S n) (Zabs_nat (Zpos p))); intros H4; auto.
Contradict H3; simpl in |- *.
apply Zle_not_lt.
repeat rewrite POS_inject.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ; apply Znat.inj_le;
 auto with zarith arith.
intros p H1 (H2, H3); split; auto.
exists (Zquotient (a - b) (Z_of_nat (S n)) - 1)%Z.
apply trans_equal with (b + (a - b))%Z.
ring.
replace (Z_of_nat (Zabs_nat (Z_of_nat (S n) + Zneg p))) with
 (Z_of_nat (S n) + Zneg p)%Z.
pattern (a - b)%Z at 1 in |- *; rewrite H1; ring.
rewrite <- Zabs_absolu; auto.
apply sym_equal; apply Zabs_eq.
change (0 <= Z_of_nat (S n) - Zpos p)%Z in |- *.
apply Zlt_le_weak; apply Zlt_ZERO_minus.
rewrite <- (Zabs_eq (Z_of_nat (S n))); auto with zarith arith.
apply lt_inj.
rewrite <- Zabs_absolu; auto.
rewrite Zabs_eq.
pattern (Z_of_nat (S n)) at 2 in |- *;
 replace (Z_of_nat (S n)) with (Z_of_nat (S n) + 0)%Z; 
 auto with zarith.
change (0 <= Z_of_nat (S n) - Zpos p)%Z in |- *.
apply Zlt_le_weak; apply Zlt_ZERO_minus.
rewrite <- (Zabs_eq (Z_of_nat (S n))); auto with zarith arith.
Qed.
 
Theorem neg_cong :
 forall (i : nat) (a b : Z),
 i <> 0 ->
 ~ congZ i a b -> exists x : _, 0 < x /\ x < i /\ congZ i a (b + Z_of_nat x).
intros i a b H H0; exists (fcong i a b).
case (fcong_correct i a b); auto; intros H1 H2.
repeat split; auto.
generalize H1; case (fcong i a b); simpl in |- *; auto with arith.
replace (b + 0)%Z with b; auto with zarith.
intros H3; case H0; auto.
Qed.

(** Congruence is decidable *) 
Definition congZ_dec :
  forall (i : nat) (a b : Z), {congZ i a b} + {~ congZ i a b}.
intros i a b; case i.
generalize (Z_eq_bool_correct a b); case (Z_eq_bool a b).
intros H; left; exists 0%Z; rewrite H; ring.
intros H; right; red in |- *; intros (x, H0); case H; rewrite H0; ring.
intros n; case (ZdividesP (a - b) (Z_of_nat (S n))).
intros H; left; case H; intros x H1.
exists x; replace a with (b + (a - b))%Z; [ rewrite H1 | idtac ]; ring.
intros H; right; red in |- *; intros (x, H0); case H.
exists x; rewrite H0; ring.
Defined.

Theorem congZ_O_Eq : forall a b, congZ 0 a b <-> a = b.
intros a b; split.
intros (m1, H1); rewrite H1; ring.
intros H1; rewrite H1; exists 0%Z; ring.
Qed.
