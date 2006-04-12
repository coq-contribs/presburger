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
(*                        Normal.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(** * Turn a formula in normal form *)
Require Export Form.
Require Import ZArithRing.
Require Export Zdivides.
Require Import Lift.
Require Import sTactic.
Require Import GroundN.
(** A Cnf2 formula is either
  - Constant (True,False)
  - An equation
  - An inequation
  - A congruence*)
 
Inductive Cnf2 : form -> Prop :=
  | Cnf2True : Cnf2 TRue
  | Cnf2False : Cnf2 FAlse
  | Cnf2Eq : forall a b : exp, Cnf2 (Form.Eq a b)
  | Cnf2NEq : forall a b : exp, Cnf2 (Neg (Form.Eq a b))
  | Cnf2Cong : forall (i : nat) (a b : exp), Cnf2 (Cong i a b).
Hint Constructors Cnf2.
(** A Pneg formula is either
  - Cnf2
  - A conjunction
  - A disjunction*)
 
Inductive PNeg : form -> Prop :=
  | PNegCnf2 : forall a : form, Cnf2 a -> PNeg a
  | PNegAnd : forall a b : form, PNeg a -> PNeg b -> PNeg (ANd a b)
  | PNegOr : forall a b : form, PNeg a -> PNeg b -> PNeg (Or a b).
Hint Constructors PNeg.
(** A Cn1 formula is either
  - Cnf2
  - A conjunction*)
 
Inductive Cnf1 : form -> Prop :=
  | Cnf1Cnf2 : forall a : form, Cnf2 a -> Cnf1 a
  | Cnf1And : forall a b : form, Cnf1 a -> Cnf1 b -> Cnf1 (ANd a b).
Hint Constructors Cnf1.
 
Theorem Cnf1_app :
 forall l1 l2,
 Cnf1 (buildConj l1) -> Cnf1 (buildConj l2) -> Cnf1 (buildConj (l1 ++ l2)).
intros l1 l2; elim l1; simpl in |- *; auto.
intros a l; case l.
case l2; auto.
simpl in |- *; auto.
intros f l0 H H0 H1.
replace ((f :: l0) ++ l2) with (f :: l0 ++ l2); [ idtac | simpl in |- * ];
 auto.
change (Cnf1 (ANd a (buildConj ((f :: l0) ++ l2)))) in |- *.
inversion H0; auto.
inversion H2; auto.
Qed.
Hint Resolve Cnf1_app.
 
Theorem Cnf1_cons :
 forall a l, Cnf2 a -> Cnf1 (buildConj l) -> Cnf1 (buildConj (a :: l)).
intros a l; simpl in |- *; case l; auto.
Qed.
Hint Resolve Cnf1_cons.
(** A Cnf formula that is a disjunction of Cn1*)
 
Inductive Cnf : form -> Prop :=
  | CnfCnf1 : forall a : form, Cnf1 a -> Cnf a
  | CnfOr : forall a b : form, Cnf a -> Cnf b -> Cnf (Or a b).
Hint Constructors Cnf.
(** A normal formula starts with existential and negation and then is Cnf *)
 
Inductive Normal : form -> Prop :=
  | nExists : forall a : form, Normal a -> Normal (Exists a)
  | nNExists : forall a : form, Normal a -> Normal (Neg (Exists a))
  | nCnf : forall a : form, Cnf a -> Normal a.
Hint Constructors Normal.
(** Expand negation of congruence
  - [~(a = b [n]) == (a=b+1 [n])\/...\/(a=b+n-1 [n])]*)
 
Fixpoint econg (i : nat) (a b : exp) (n : nat) {struct n} : form :=
  match n with
  | O => FAlse
  | S O => Cong i a (Plus b (Num n))
  | S n1 => Or (Cong i a (Plus b (Num n))) (econg i a b n1)
  end.
 
Definition expand_cong i a b :=
  match i with
  | O => Neg (Form.Eq a b)
  | S O => FAlse
  | S i1 => econg i a b i1
  end.
 
Theorem econg_correct :
 forall (n : nat) i a b l,
 form2Prop l (econg i a b n) <->
 (exists x : nat, 1 <= x /\ x <= n /\ form2Prop l (Cong i a (Plus b (Num x)))).
intros n; elim n; simpl in |- *; auto.
intros i a b l; split.
intros H; case H.
intros (x, (H1, (H2, H3))).
generalize H1; inversion H2.
intros H4; inversion H4; auto.
intros i1; case i1.
intros H i a b l; simpl in |- *; split.
intros H0; exists 1; repeat split; auto.
intros (x, (H1, (H2, H3))).
generalize H1 H3; inversion H2; simpl in |- *; auto.
inversion H4; auto.
intros H6; inversion H6.
intros n0 H i a b l; split.
unfold form2Prop in |- *; lazy beta in |- *; fold form2Prop in |- *.
intros H1; case H1.
intros H0; exists (S (S n0)); repeat split; auto with arith.
intros H0; case (H i a b l); auto.
intros H2 H3; case (H2 H0); intros x (H4, (H5, H6)).
exists x; repeat split; auto with arith.
unfold form2Prop in |- *; lazy beta in |- *; fold form2Prop in |- *.
intros (x, (H1, (H2, H3))).
generalize H3; inversion H2; auto.
intros H5; right.
case (H i a b l); auto.
intros H6 H7; apply H7.
exists x; repeat split; auto with zarith.
Qed.
 
Theorem econg_groundN :
 forall n p i a b,
 groundNExp p a -> groundNExp p b -> groundNForm p (econg i a b n).
intros n; elim n; simpl in |- *; auto.
intros n0; case n0; auto.
intros H p i a b H0 H1.
apply GNCong with (n := p) (m := p); auto.
apply GNPlus with (n := p) (m := p); auto.
intros n1 H p i a b H0 H1.
apply GNOr with (n := p) (m := p); auto.
apply GNCong with (n := p) (m := p); auto.
apply GNPlus with (n := p) (m := p); auto.
Qed.
 
Theorem econg_pneg : forall i a b n, PNeg (econg i a b n).
intros i a b n; elim n; simpl in |- *; auto.
intros i1; case i1; auto.
Qed.
 
Theorem expand_cong_pneg : forall i a b, PNeg (expand_cong i a b).
intros i; case i; simpl in |- *; auto.
intros i1; case i1; auto.
intros; apply econg_pneg; auto.
Qed.
 
Theorem expand_cong_correct :
 forall i a b l,
 form2Prop l (Neg (Cong i a b)) <-> form2Prop l (expand_cong i a b).
intros i a b l; case i; simpl in |- *.
simpl in |- *; split; intros H; red in |- *; intros H1; case H.
rewrite H1; auto.
case H1; intros x H2; rewrite H2; simpl in |- *; ring.
intros i1; case i1; auto.
simpl in |- *; split; intros H; auto.
case H; exists (exp2Z l a - exp2Z l b)%Z; simpl in |- *; ring.
intros n.
apply
 iff_trans
  with
    (exists x : nat,
       1 <= x /\ x <= S n /\ form2Prop l (Cong (S (S n)) a (Plus b (Num x)))).
2: apply iff_sym; apply econg_correct.
split.
intros H; case neg_cong with (2 := H); auto.
simpl in |- *; intros x (H1, (H2, H3)); exists x; repeat split;
 auto with arith.
simpl in |- *; intros (x, (H1, (H2, H3))); red in |- *; intros H4.
cut (congZ (S (S n)) 0 (Z_of_nat x)).
intros (y, H5).
2: replace 0%Z with (exp2Z l b - exp2Z l b)%Z; [ idtac | ring ].
2: replace (Z_of_nat x) with (exp2Z l b + Z_of_nat x - exp2Z l b)%Z;
    [ idtac | ring ].
2: apply congZ_minus; auto.
2: apply congZ_trans with (2 := H3).
2: apply congZ_sym; auto.
generalize H5; case y.
intros H; Contradict H; apply Zorder.Zlt_not_eq.
simpl in |- *.
replace (Z_of_nat x + 0)%Z with (Z_of_nat x);
 [ replace 0%Z with (Z_of_nat 0); try apply Znat.inj_lt;
    auto with zarith arith
 | ring ].
intros p H; Contradict H; apply Zorder.Zlt_not_eq.
replace 0%Z with (0 + 0)%Z; [ apply Zplus_le_lt_compat | ring ];
 auto with zarith arith.
intros p H; Contradict H; apply Compare.not_eq_sym; apply Zorder.Zlt_not_eq.
replace 0%Z with
 (Zpos p * Z_of_nat (S (S n)) + Zneg p * Z_of_nat (S (S n)))%Z;
 [ apply Zplus_lt_compat_r
 | replace (Zneg p) with (- Zpos p)%Z; [ ring | simpl in |- * ] ];
 auto with zarith arith.
apply Zlt_le_trans with (1 * Z_of_nat (S (S n)))%Z; auto with zarith arith.
change (Z_of_nat x < Z_of_nat (S (S n)))%Z in |- *; apply Znat.inj_lt;
 auto with arith.
apply Zmult_le_compat_r; auto with zarith arith.
case p; red in |- *; simpl in |- *; intros; red in |- *; discriminate.
Qed.
 
Theorem expand_groundN :
 forall i p a b,
 groundNExp p a -> groundNExp p b -> groundNForm p (expand_cong i a b).
intros i; case i; simpl in |- *; auto.
intros p a b H H0; apply GNNeg.
apply GNEq with (n := p) (m := p); auto.
intros n; case n; auto.
intros n0 p a b H H0; apply econg_groundN; auto.
Qed.
(** * Push negation 
  - [~(a\/b)] gives [~a /\ ~b] 
  - [~(a/\b)] gives [~a \/ ~b] *)
 
Fixpoint push_neg (b : bool) (f : form) {struct f} : form :=
  match b, f with
  | true, Imp f1 f2 => Or (push_neg false f1) (push_neg true f2)
  | true, Or f1 f2 => Or (push_neg true f1) (push_neg true f2)
  | true, ANd f1 f2 => ANd (push_neg true f1) (push_neg true f2)
  | true, Neg f1 => push_neg false f1
  | true, _ => f
  | false, Imp f1 f2 => ANd (push_neg true f1) (push_neg false f2)
  | false, Or f1 f2 => ANd (push_neg false f1) (push_neg false f2)
  | false, ANd f1 f2 => Or (push_neg false f1) (push_neg false f2)
  | false, Neg f1 => push_neg true f1
  | false, FAlse => TRue
  | false, TRue => FAlse
  | false, Cong i e1 e2 => expand_cong i e1 e2
  | false, _ => Neg f
  end.
 
Theorem push_neg_pneg : forall f, noBinder f -> forall b, PNeg (push_neg b f).
intros f H; elim H; simpl in |- *; auto.
intros b; case b; auto.
intros b; case b; auto.
intros a H1 Rec b; case b; simpl in |- *; auto.
intros a b H0 H1 H2 H3 b0; case b0; simpl in |- *; auto.
intros a b H0 H1 H2 H3 b0; case b0; simpl in |- *; auto.
intros a b H0 H1 H2 H3 b0; case b0; simpl in |- *; auto.
intros a b b0; case b0; simpl in |- *; auto.
intros i a b b0; case b0; simpl in |- *; auto.
apply expand_cong_pneg.
Qed.
 
Theorem push_neg_correct :
 forall f b l,
 form2Prop l (push_neg b f) <->
 match b with
 | true => form2Prop l f
 | false => ~ form2Prop l f
 end.
intros f; elim f; simpl in |- *; auto.
intros f0 H b l.
case b; intuition.
intros f0 H b l; case b; simpl in |- *; split; auto.
intros f0 H f1 H0 b l; case b; simpl in |- *.
generalize (H0 true l); generalize (H true l); intuition.
simpl in |- *; generalize (H0 false l); generalize (H false l); intuition.
case (classic (form2Prop l (push_neg false f0))); auto; right; intuition.
intros f0 H f1 H0 b l; case b; simpl in |- *; auto.
simpl in |- *; generalize (H0 true l); generalize (H true l); intuition.
simpl in |- *; generalize (H0 false l); generalize (H false l); intuition.
intros f0 H f1 H0 b l; case b; simpl in |- *; split.
intros [H1| H1] H2; auto.
simpl in |- *; generalize (H false l); intuition.
simpl in |- *; generalize (H0 true l); intuition.
intros H1; case (classic (form2Prop l f1)); intros H2; auto.
right; generalize (H0 true l); intuition.
case (classic (form2Prop l f0)); auto; intuition.
simpl in |- *; generalize (H false l); intuition.
simpl in |- *; generalize (H0 false l); generalize (H true l); intuition.
case (classic (form2Prop l f1)); auto.
intros H1 H2; case H2; auto.
case (classic (form2Prop l f0)); auto.
simpl in |- *; generalize (H0 false l); generalize (H true l); intuition.
intros H1 H2 H3; case H3; intros H4; case H1; auto.
intros f0 H b l; case b; simpl in |- *.
simpl in |- *; generalize (H false l); intuition.
case (classic (form2Prop l f0)).
simpl in |- *; generalize (H true l); intuition.
simpl in |- *; generalize (H true l); intuition.
intros b; case b; intuition.
intros b; case b; simpl in |- *; intuition.
intros e e0 b; case b; simpl in |- *; intuition.
intros n e e0 b; case b.
simpl in |- *; intuition.
intros l; generalize (expand_cong_correct n e e0 l); simpl in |- *; intuition.
Qed.
 
Theorem push_neg_groundN :
 forall f b n, groundNForm n f -> groundNForm n (push_neg b f).
intros f; elim f; simpl in |- *; auto.
intros f0 H b n H0; case b; simpl in |- *; auto.
intros f0 H b n H0; case b; simpl in |- *; auto.
intros f0 H f1 H0 b n H1; case b; simpl in |- *; auto.
inversion H1; auto.
apply GNAnd with (n := n0) (m := m); auto.
inversion H1; auto.
apply GNOr with (n := n0) (m := m); auto.
intros f0 H f1 H0 b n H1; case b.
inversion H1; auto.
apply GNOr with (n := n0) (m := m); auto.
inversion H1; auto.
apply GNAnd with (n := n0) (m := m); auto.
intros f0 H f1 H0 b n H1; case b.
inversion H1; auto.
apply GNOr with (n := n0) (m := m); auto.
inversion H1; auto.
apply GNAnd with (n := n0) (m := m); auto.
intros f0 H b n H0; case b; auto.
inversion H0; auto.
inversion H0; auto.
intros b n H; case b; auto.
intros b n H; case b; auto.
intros e e0 b n H; case b; auto.
intros n e e0 b n0 H; case b; auto.
inversion H; auto.
apply expand_groundN; auto.
apply groundNExp_le with (1 := H6); auto.
apply groundNExp_le with (1 := H7); auto.
Qed.
(** * Push conjunction under disjunction
  - [c/\(a\/b)] gives [(c/\a)\/(c/\b)] 
  - [(a\/b)/\c] gives [(a/\c) \/ (b/\c)] *)
 
Fixpoint push_and_rules1 (f1 : form) : form -> form :=
  fun f2 =>
  match f1 with
  | Or f3 f4 => Or (push_and_rules1 f3 f2) (push_and_rules1 f4 f2)
  | _ => ANd f1 f2
  end.
 
Fixpoint push_and_rules (f1 f2 : form) {struct f2} : form :=
  match f2 with
  | Or f3 f4 => Or (push_and_rules f1 f3) (push_and_rules f1 f4)
  | _ => push_and_rules1 f1 f2
  end.
 
Fixpoint push_and (f : form) : form :=
  match f with
  | Or f1 f2 => Or (push_and f1) (push_and f2)
  | ANd f1 f2 => push_and_rules (push_and f1) (push_and f2)
  | _ => f
  end.
 
Theorem push_and_rules1_cnf :
 forall f1 f2, Cnf f1 -> Cnf1 f2 -> Cnf (push_and_rules1 f1 f2).
intros f1 f2 H; generalize f2; elim H; clear f2 H f1; simpl in |- *; auto.
intros f1 H; elim H; clear H f1; simpl in |- *; auto.
intros f1 H; elim H; clear H f1; simpl in |- *; auto.
Qed.
 
Theorem push_and_rules1_correct :
 forall f1 f2 l,
 form2Prop l (push_and_rules1 f1 f2) <-> form2Prop l (ANd f1 f2).
intros f1; elim f1; simpl in |- *; try intuition eauto; fail.
intros f H f0 H0 f2 l.
generalize (H0 f2 l); generalize (H f2 l); intuition.
Qed.
 
Theorem push_and_rules1_groundN :
 forall f1 f2 n,
 groundNForm n f1 ->
 groundNForm n f2 -> groundNForm n (push_and_rules1 f1 f2).
intros f1; elim f1; simpl in |- *; auto;
 try (intros; apply GNAnd with (n := n) (m := n); auto; fail).
intros f H f0 H0 f2 n H1 H2.
inversion H1.
apply GNOr with (n := n) (m := n); auto.
apply H; auto.
apply groundNForm_le with (n := n0); auto.
apply H0; auto.
apply groundNForm_le with (n := m); auto.
intros n e e0 f2 n0 H H0.
inversion H.
apply GNAnd with (n := n0) (m := n0); auto.
Qed.
 
Theorem push_and_rules_cnf :
 forall f1 f2, Cnf f1 -> Cnf f2 -> Cnf (push_and_rules f1 f2).
intros f1 f2 H H1; elim H1; clear H1 f2; simpl in |- *; auto.
intros f2 H1; elim H1; simpl in |- *; clear H1 f2; auto.
intros f2 H1; elim H1; simpl in |- *; clear H1 f2; auto; intros;
 try apply push_and_rules1_cnf; auto.
intros a b H0 H1 H2 H3; apply push_and_rules1_cnf; auto.
Qed.
 
Theorem push_and_rules_correct :
 forall f1 f2 l,
 form2Prop l (push_and_rules f1 f2) <-> form2Prop l (ANd f1 f2).
intros f1 f2; generalize f1; elim f2; clear f1 f2;
 unfold push_and_rules in |- *; lazy beta in |- *;
 fold push_and_rules in |- *; try (intros; apply push_and_rules1_correct);
 auto.
intros f H f0 H0 f1 l.
generalize (H0 f1 l); generalize (H f1 l); simpl in |- *; intuition.
Qed.
 
Theorem push_and_rules_groundN :
 forall f2 f1 n,
 groundNForm n f1 -> groundNForm n f2 -> groundNForm n (push_and_rules f1 f2).
intros f1; elim f1; simpl in |- *; auto;
 try (intros; apply push_and_rules1_groundN; auto; fail).
intros f H f0 H0 f2 n H1 H2.
inversion H2.
apply GNOr with (n := n) (m := n); auto.
apply H; auto.
apply groundNForm_le with (n := n0); auto.
apply H0; auto.
apply groundNForm_le with (n := m); auto.
Qed.
 
Theorem push_and_cnf : forall f, PNeg f -> Cnf (push_and f).
intros f H; elim H; clear H f; simpl in |- *; auto.
intros f H; elim H; clear H f; simpl in |- *; auto.
intros a b H H0 H1 H2; apply push_and_rules_cnf; auto.
Qed.
 
Theorem push_and_correct :
 forall f l, form2Prop l (push_and f) <-> form2Prop l f.
intros f; elim f; simpl in |- *; try intuition eauto; fail.
intros f0 H f1 H0 l; generalize (H0 l); generalize (H l);
 generalize (push_and_rules_correct (push_and f0) (push_and f1) l);
 simpl in |- *; intuition.
intros f0 H f1 H0 l; generalize (H0 l); generalize (H l);
 generalize (push_and_rules_correct (push_and f0) (push_and f1) l);
 simpl in |- *; intuition.
Qed.
 
Theorem push_and_groundN :
 forall f n, groundNForm n f -> groundNForm n (push_and f).
intros f; elim f; simpl in |- *; auto.
intros f0 H f1 H0 n H1; inversion H1; (apply push_and_rules_groundN; auto).
apply H.
apply groundNForm_le with (1 := H7); auto.
apply H0.
apply groundNForm_le with (1 := H8); auto.
intros f0 H f1 H0 n H1; inversion H1.
apply GNOr with (n := n0) (m := m); auto.
Qed.
(** Build cnf formulae *)
 
Definition cnf f := push_and (push_neg true f).
 
Theorem cnf_cnf : forall f, noBinder f -> Cnf (cnf f).
intros f H; unfold cnf in |- *; (apply push_and_cnf; auto).
apply push_neg_pneg; auto.
Qed.
 
Theorem cnf_correct : forall f l, form2Prop l (cnf f) <-> form2Prop l f.
intros f l; apply iff_trans with (form2Prop l (push_neg true f)).
unfold cnf in |- *; apply push_and_correct; auto.
apply (push_neg_correct f true).
Qed.
 
Theorem cnf_groundN : forall f n, groundNForm n f -> groundNForm n (cnf f).
intros f n H; unfold cnf in |- *.
apply push_and_groundN; auto.
apply push_neg_groundN; auto.
Qed.
(** Expand forall 
  - [(x:?)(P x)] gives [~(Ex [x:?] (P x))] *)
 
Fixpoint expand_forall (b : bool) (f : form) {struct f} : form :=
  match b, f with
  | true, Forall f1 => Neg (Exists (expand_forall false f1))
  | true, Exists f1 => Exists (expand_forall true f1)
  | true, _ => cnf f
  | false, Forall f1 => Exists (expand_forall false f1)
  | false, Exists f1 => Neg (Exists (expand_forall true f1))
  | false, _ => cnf (Neg f)
  end.
 
Theorem noBinder_Neg : forall a : form, noBinder a -> noBinder (Neg a).
intros a H; elim H; simpl in |- *; auto.
Qed.
Hint Resolve noBinder_Neg.
 
Theorem expand_forall_normal :
 forall f b, prenex f -> Normal (expand_forall b f).
intros f b H; generalize b; elim H; clear H f b; simpl in |- *; auto.
intros a H H0 b; case b; auto.
intros a H H0 b; case b; auto.
intros f H; elim H; clear H f; simpl in |- *; auto.
intros b; case b; simpl in |- *; auto.
intros b; case b; simpl in |- *; auto.
intros a H H0 b; case b; simpl in |- *; apply nCnf; apply cnf_cnf; auto.
intros a b H H0 H1 H2 b0; case b0; simpl in |- *; auto; apply nCnf;
 apply cnf_cnf; auto.
intros a b H H0 H1 H2 b0; case b0; simpl in |- *; auto; apply nCnf;
 apply cnf_cnf; auto.
intros a b H H0 H1 H2 b0; case b0; simpl in |- *; auto; apply nCnf;
 apply cnf_cnf; auto.
intros a b b0; case b0; simpl in |- *; auto; apply nCnf; apply cnf_cnf; auto.
intros i a b b0; case b0; simpl in |- *; auto; apply nCnf; apply cnf_cnf;
 auto.
Qed.
 
Theorem expand_forall_correct :
 forall f b l,
 form2Prop l (expand_forall b f) <->
 match b with
 | true => form2Prop l f
 | false => ~ form2Prop l f
 end.
intros f; elim f; simpl in |- *.
intros f0 H b l; case b; simpl in |- *; split.
intros H0 x; case (classic (form2Prop (x :: l) f0)); auto; intros H1; case H0;
 exists x.
case (H false (x :: l)); auto.
intros H0; red in |- *; intros (x, H1).
case (H false (x :: l)); intuition.
intros (x, H0); red in |- *; intros H1.
case (H false (x :: l)); intuition.
intros H0;
 case
  (classic (ex (fun x : Z => form2Prop (x :: l) (expand_forall false f0))));
 auto; intros H1.
case H0; intros x; case (classic (form2Prop (x :: l) f0)); auto; intros H2.
case H1; exists x; generalize (H false (x :: l)); intuition.
intros f0 H b l; case b; simpl in |- *; split.
intros (x, H0); exists x; generalize (H true (x :: l)); intuition.
intros (x, H0); exists x; generalize (H true (x :: l)); intuition.
intros H0; red in |- *; intros (x, H1); case H0; exists x;
 generalize (H true (x :: l)); intuition.
intros H0; red in |- *; intros (x, H1); case H0; exists x;
 generalize (H true (x :: l)); intuition.
intros f0 H f1 H0 b l; case b.
apply (cnf_correct (ANd f0 f1) l).
generalize (cnf_correct (Neg (ANd f0 f1)) l); simpl in |- *; intuition.
intros f0 H f1 H0 b l; case b.
apply (cnf_correct (Or f0 f1) l).
generalize (cnf_correct (Neg (Or f0 f1)) l); simpl in |- *; intuition.
intros f0 H f1 H0 b l; case b.
apply (cnf_correct (Imp f0 f1) l).
generalize (cnf_correct (Neg (Imp f0 f1)) l); simpl in |- *; intuition.
intros f0 H b l; case b.
apply (cnf_correct (Neg f0) l).
generalize (cnf_correct (Neg (Neg f0)) l); simpl in |- *; intuition.
intros b l; case b; intuition.
intros b l; case b; simpl in |- *; intuition.
intros e e0 b l; case b.
apply (cnf_correct (Form.Eq e e0) l).
generalize (cnf_correct (Form.Eq e e0) l); simpl in |- *; intuition.
intros n e e0 b l; case b.
apply (cnf_correct (cnf (Cong n e e0)) l).
generalize (cnf_correct (Neg (Cong n e e0)) l); simpl in |- *; intuition.
Qed.
 
Theorem expand_forall_groundN :
 forall f b n, groundNForm n f -> groundNForm n (expand_forall b f).
intros f; elim f; simpl in |- *; auto;
 try (intros; case b; auto; apply cnf_groundN; auto).
intros f0 H b n H0; inversion H0; case b; auto.
intros f0 H b n H0; inversion H0; case b; auto.
Qed.
(** Build a normal form formula *)
 
Definition normalForm f := expand_forall true (lift_quant f).
(** An example *)
Eval compute in
  (normalForm
     (Forall
        (Or (Exists (Form.Eq (Var 1) (Plus (Var 0) (Var 0))))
           (Exists (Form.Eq (Var 1) (Plus (Plus (Var 0) (Var 0)) (Num 0))))))).
(** Normal is normal *)
 
Theorem normal_normal : forall f, Normal (normalForm f).
intros f; unfold normalForm in |- *.
apply expand_forall_normal.
apply lift_quant_prenex.
Qed.
(** normal does not change the semantic *)
 
Theorem normalForm_correct :
 forall f l, form2Prop l (normalForm f) <-> form2Prop l f.
intros f l; apply iff_trans with (form2Prop l (lift_quant f)).
apply (expand_forall_correct (lift_quant f) true l).
apply iff_sym; apply correct_lift_quant.
Qed.
(** normal preserves the ground level *)
 
Theorem normalForm_groundN :
 forall f n, groundNForm n f -> groundNForm n (normalForm f).
intros f n H; unfold normalForm in |- *; apply expand_forall_groundN.
apply lift_quant_groundN; auto.
Qed.