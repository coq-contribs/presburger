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
(*                      Zdivides.v                                      *)
(*                                                                      *)
(*    Laurent.Thery @sophia.inria.fr        March 2002                  *)
(************************************************************************)
(** Extra properties over Z *)
Require Import Arith.
Require Import Compare.
Require Import Omega.
Require Import Zpower.
Require Import Zcomplements.
Require Import Reals.
Require Import sTactic.
Require Import Option.
Require Import ZArith.
Require Import ZArithRing.
Require Import Option.
Require Import Inverse_Image.
Require Import Wf_nat.

(** Useful lemmae *)

Theorem POS_inject : forall x : positive, Zpos x = Z_of_nat (nat_of_P x) :>Z.
intros x; elim x; simpl in |- *; auto.
intros p H; rewrite ZL6.
apply f_equal with (f := Zpos).
apply nat_of_P_inj.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ; unfold nat_of_P in |- *;
 simpl in |- *.
rewrite ZL6; auto.
intros p H; unfold nat_of_P in |- *; simpl in |- *.
rewrite ZL6; simpl in |- *.
rewrite Znat.inj_plus; repeat rewrite <- H.
rewrite BinInt.Zpos_xO; ring.
Qed.

Theorem Zabs_Zopp : forall z : Z, Zabs (- z) = Zabs z.
intros z; case z; simpl in |- *; auto.
Qed.


Theorem Zabs_Zmult : forall z1 z2 : Z, Zabs (z1 * z2) = (Zabs z1 * Zabs z2)%Z.
intros z1 z2; case z1; case z2; simpl in |- *; auto.
Qed.
 
Theorem Zle_Zabs : forall z : Z, (0 <= Zabs z)%Z.
intros z; case z; simpl in |- *; auto with zarith.
Qed.
Hint Resolve Zle_Zabs: zarith.

Theorem Zeq_mult_simpl :
 forall a b c : Z, c <> 0%Z -> (a * c)%Z = (b * c)%Z -> a = b.
intros a b c H H0.
case (Zle_or_lt c 0); intros Zl1.
apply Zle_antisym; apply Zmult_le_reg_r with (p := (- c)%Z); try apply Zlt_gt;
 auto with zarith; repeat rewrite <- Zopp_mult_distr_r; 
 rewrite H0; auto with zarith.
apply Zle_antisym; apply Zmult_le_reg_r with (p := c); try apply Zlt_gt;
 auto with zarith; rewrite H0; auto with zarith.
Qed.

Fixpoint pos_eq_bool (a b : positive) {struct b} : bool :=
  match a, b with
  | xH, xH => true
  | xI a', xI b' => pos_eq_bool a' b'
  | xO a', xO b' => pos_eq_bool a' b'
  | _, _ => false
  end.
 
Theorem pos_eq_bool_correct :
 forall p q : positive,
 match pos_eq_bool p q with
 | true => p = q
 | false => p <> q
 end.
intros p q; generalize p; elim q; simpl in |- *; auto; clear p q.
intros p Rec q; case q; simpl in |- *;
 try (intros; red in |- *; intros; discriminate; fail).
intros q'; generalize (Rec q'); case (pos_eq_bool q' p); simpl in |- *; auto.
intros H1; rewrite H1; auto.
intros H1; Contradict H1; injection H1; auto.
intros p Rec q; case q; simpl in |- *;
 try (intros; red in |- *; intros; discriminate; fail).
intros q'; generalize (Rec q'); case (pos_eq_bool q' p); simpl in |- *; auto.
intros H1; rewrite H1; auto.
intros H1; Contradict H1; injection H1; auto.
intros q; case q; simpl in |- *;
 try (intros; red in |- *; intros; discriminate; fail); 
 auto.
Qed.
 
Theorem Z_O_1 : (0 < 1)%Z.
red in |- *; simpl in |- *; auto; intros; red in |- *; intros; discriminate.
Qed.
Hint Resolve Z_O_1: zarith.
 
Definition Z_eq_bool a b :=
  match a, b with
  | Z0, Z0 => true
  | Zpos a', Zpos b' => pos_eq_bool a' b'
  | Zneg a', Zneg b' => pos_eq_bool a' b'
  | _, _ => false
  end.
 
Theorem Z_eq_bool_correct :
 forall p q : Z,
 match Z_eq_bool p q with
 | true => p = q
 | false => p <> q
 end.
intros p q; case p; case q; simpl in |- *; auto;
 try (intros; red in |- *; intros; discriminate; fail).
intros p' q'; generalize (pos_eq_bool_correct q' p');
 case (pos_eq_bool q' p'); simpl in |- *; auto.
intros H1; rewrite H1; auto.
intros H1; Contradict H1; injection H1; auto.
intros p' q'; generalize (pos_eq_bool_correct q' p');
 case (pos_eq_bool q' p'); simpl in |- *; auto.
intros H1; rewrite H1; auto.
intros H1; Contradict H1; injection H1; auto.
Qed.

Theorem Zabs_eq_case :
 forall z1 z2 : Z, Zabs z1 = Zabs z2 -> z1 = z2 \/ z1 = (- z2)%Z.
intros z1 z2; case z1; case z2; simpl in |- *; auto;
 try (intros; discriminate); intros p1 p2 H1; injection H1;
 (intros H2; rewrite H2); auto.
Qed.
 
Theorem Zabs_intro : forall P (z : Z), P (- z)%Z -> P z -> P (Zabs z).
intros P z; case z; simpl in |- *; auto.
Qed.
 
Theorem Zle_NEG_POS : forall p, (Zneg p <= Zpos p)%Z.
intros p; red in |- *; simpl in |- *; red in |- *; intros H; discriminate.
Qed.
Hint Resolve Zle_NEG_POS: zarith.
 
Theorem Zabs_tri : forall z1 z2 : Z, (Zabs (z1 + z2) <= Zabs z1 + Zabs z2)%Z.
intros z1 z2; case z1; case z2; try (simpl in |- *; auto with zarith; fail).
intros p1 p2;
 apply
  Zabs_intro with (P := fun x => (x <= Zabs (Zpos p2) + Zabs (Zneg p1))%Z);
 try rewrite Zopp_plus_distr; auto with zarith.
apply Zplus_le_compat; simpl in |- *; auto with zarith.
apply Zplus_le_compat; simpl in |- *; auto with zarith.
intros p1 p2;
 apply
  Zabs_intro with (P := fun x => (x <= Zabs (Zpos p2) + Zabs (Zneg p1))%Z);
 try rewrite Zopp_plus_distr; auto with zarith.
apply Zplus_le_compat; simpl in |- *; auto with zarith.
apply Zplus_le_compat; simpl in |- *; auto with zarith.
Qed.
Hint Resolve Zabs_tri: zarith.

(** Maximum of two relative numbers *)
Definition Zmax a b := match (a ?= b)%Z with
                       | Datatypes.Lt => b
                       | _ => a
                       end.
 

(** Some basic properties of Zmax *)
Theorem Zmax1 : forall a b, (a <= Zmax a b)%Z.
intros a b; unfold Zmax in |- *; CaseEq (a ?= b)%Z; simpl in |- *;
 auto with zarith.
unfold Zle in |- *; intros H; rewrite H; red in |- *; intros; discriminate.
Qed.
 
Theorem Zmax2 : forall a b, (b <= Zmax a b)%Z.
intros a b; unfold Zmax in |- *; CaseEq (a ?= b)%Z; simpl in |- *;
 auto with zarith.
intros H;
 (case (Zle_or_lt b a); auto; unfold Zlt in |- *; rewrite H; intros;
   discriminate).
intros H;
 (case (Zle_or_lt b a); auto; unfold Zlt in |- *; rewrite H; intros;
   discriminate).
Qed.

 
(** Division over positive 
  - Take two positives [p], [q]
  - Return a pair of optional positive for the quotient and the rest
    -- Optional positive are used to represent ZERO
    --- (Some x) is (POS x) while None is ZERO
*)
Fixpoint Pdiv (p : positive) :
 positive -> Option positive * Option positive :=
  fun q =>
  match p with
  | xH =>
      match q with
      | xH => (Some _ 1%positive, None _)
      | xO r => (None _, Some _ p)
      | xI r => (None _, Some _ p)
      end
  | xI p' =>
      match Pdiv p' q with
      | (None, None) =>
          match (1 - Zpos q)%Z with
          | Z0 => (Some _ 1%positive, None _)
          | Zpos r' => (Some _ 1%positive, Some _ r')
          | Zneg r' => (None _, Some _ 1%positive)
          end
      | (None, Some r1) =>
          match (Zpos (xI r1) - Zpos q)%Z with
          | Z0 => (Some _ 1%positive, None _)
          | Zpos r' => (Some _ 1%positive, Some _ r')
          | Zneg r' => (None _, Some _ (xI r1))
          end
      | (Some q1, None) =>
          match (1 - Zpos q)%Z with
          | Z0 => (Some _ (xI q1), None _)
          | Zpos r' => (Some _ (xI q1), Some _ r')
          | Zneg r' => (Some _ (xO q1), Some _ 1%positive)
          end
      | (Some q1, Some r1) =>
          match (Zpos (xI r1) - Zpos q)%Z with
          | Z0 => (Some _ (xI q1), None _)
          | Zpos r' => (Some _ (xI q1), Some _ r')
          | Zneg r' => (Some _ (xO q1), Some _ (xI r1))
          end
      end
  | xO p' =>
      match Pdiv p' q with
      | (None, None) => (None _, None _)
      | (None, Some r1) =>
          match (Zpos (xO r1) - Zpos q)%Z with
          | Z0 => (Some _ 1%positive, None _)
          | Zpos r' => (Some _ 1%positive, Some _ r')
          | Zneg r' => (None _, Some _ (xO r1))
          end
      | (Some q1, None) => (Some _ (xO q1), None _)
      | (Some q1, Some r1) =>
          match (Zpos (xO r1) - Zpos q)%Z with
          | Z0 => (Some _ (xI q1), None _)
          | Zpos r' => (Some _ (xI q1), Some _ r')
          | Zneg r' => (Some _ (xO q1), Some _ (xO r1))
          end
      end
  end.
 
(** Turn an optional positive into a natural numbers *)
Definition oZ h := match h with
                   | None => 0
                   | Some p => nat_of_P p
                   end.
 
(** Auxillary lemma *)
Theorem ptonat_def1 : forall p q, 1 < Pmult_nat p (S (S q)).
intros p; elim p; simpl in |- *; auto with arith.
Qed.
Hint Resolve ptonat_def1: arith.
 
(** Pdiv is correct *)
Theorem Pdiv_correct :
 forall p q,
 nat_of_P p = oZ (fst (Pdiv p q)) * nat_of_P q + oZ (snd (Pdiv p q)) /\
 oZ (snd (Pdiv p q)) < nat_of_P q.
intros p q; elim p; simpl in |- *; auto.
3: case q; simpl in |- *; try intros q1; split; auto; unfold nat_of_P in |- *;
    simpl in |- *; auto with arith.
intros p'; simpl in |- *; case (Pdiv p' q); simpl in |- *;
 intros q1 r1 (H1, H2); split.
unfold nat_of_P in |- *; simpl in |- *.
rewrite ZL6; rewrite H1.
case q1; case r1; simpl in |- *.
intros r2 q2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xI r2) q Datatypes.Eq); simpl in |- *; auto.
intros H3; rewrite <- (Pcompare_Eq_eq _ _ H3); simpl in |- *;
 unfold nat_of_P in |- *; simpl in |- *.
apply f_equal with (f := S); repeat rewrite (fun x y => mult_comm x (S y));
 repeat rewrite ZL6; unfold nat_of_P in |- *; simpl in |- *; 
 ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *; repeat rewrite (fun x y => plus_comm x (S y));
 simpl in |- *; apply f_equal with (f := S); ring.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4.
apply
 trans_equal with (nat_of_P q + nat_of_P h + Pmult_nat q2 2 * Pmult_nat q 1);
 [ rewrite <- nat_of_P_plus_morphism; rewrite H5; simpl in |- *;
    repeat rewrite ZL6; unfold nat_of_P in |- *; apply f_equal with (f := S)
 | unfold nat_of_P in |- * ]; ring.
intros r2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare 1 q Datatypes.Eq); simpl in |- *; auto.
intros H3; rewrite <- (Pcompare_Eq_eq _ _ H3); simpl in |- *;
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 apply f_equal with (f := S); unfold nat_of_P; ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 repeat rewrite (fun x y => plus_comm x (S y)); simpl in |- *;
 apply f_equal with (f := S); unfold nat_of_P; ring.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply
  trans_equal with (nat_of_P q + nat_of_P h + Pmult_nat r2 2 * Pmult_nat q 1);
 [ rewrite <- nat_of_P_plus_morphism; rewrite H5; simpl in |- *;
    repeat rewrite ZL6; unfold nat_of_P in |- *; apply f_equal with (f := S)
 | unfold nat_of_P in |- * ]; ring.
intros r2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xI r2) q Datatypes.Eq); simpl in |- *; auto.
intros H3; rewrite <- (Pcompare_Eq_eq _ _ H3); simpl in |- *;
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *; apply f_equal with (f := S); 
 ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *; apply f_equal with (f := S); 
 ring.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply trans_equal with (nat_of_P q + nat_of_P h);
 [ rewrite <- (nat_of_P_plus_morphism q); rewrite H5; unfold nat_of_P in |- *;
    simpl in |- *; repeat rewrite ZL6; unfold nat_of_P in |- *;
    apply f_equal with (f := S)
 | unfold nat_of_P in |- * ]; ring.
case q; simpl in |- *; auto.
generalize H2; case q1; case r1; simpl in |- *; auto.
intros r2 q2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xI r2) q Datatypes.Eq); simpl in |- *; auto.
intros; apply lt_O_nat_of_P; auto.
intros H H0; apply nat_of_P_lt_Lt_compare_morphism; auto.
intros H3 H7; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply plus_lt_reg_l with (p := nat_of_P q);
 rewrite <- (nat_of_P_plus_morphism q); rewrite H5; 
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *;
 apply le_lt_trans with (Pmult_nat r2 1 + Pmult_nat q 1); 
 auto with arith.
intros r2 HH; case q; simpl in |- *; auto.
intros p2; case p2; unfold nat_of_P in |- *; simpl in |- *; auto with arith.
intros p2; case p2; unfold nat_of_P in |- *; simpl in |- *; auto with arith.
intros r2 HH. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xI r2) q Datatypes.Eq); simpl in |- *.
intros; apply lt_O_nat_of_P; auto.
intros H3; apply nat_of_P_lt_Lt_compare_morphism; auto.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply plus_lt_reg_l with (p := nat_of_P q);
 rewrite <- (nat_of_P_plus_morphism q); rewrite H5; 
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *;
 apply le_lt_trans with (Pmult_nat r2 1 + Pmult_nat q 1); 
 auto with arith.
intros HH; case q; simpl in |- *; auto.
intros p2; case p2; unfold nat_of_P in |- *; simpl in |- *; auto with arith.
intros p2; case p2; unfold nat_of_P in |- *; simpl in |- *; auto with arith.
intros p'; simpl in |- *; case (Pdiv p' q); simpl in |- *;
 intros q1 r1 (H1, H2); split.
unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6; rewrite H1.
case q1; case r1; simpl in |- *; auto.
intros r2 q2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xO r2) q Datatypes.Eq); simpl in |- *; auto.
intros H3; rewrite <- (Pcompare_Eq_eq _ _ H3); simpl in |- *;
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *; ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *; ring.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply
  trans_equal with (nat_of_P q + nat_of_P h + Pmult_nat q2 2 * Pmult_nat q 1);
 [ rewrite <- (nat_of_P_plus_morphism q); rewrite H5; unfold nat_of_P in |- *;
    simpl in |- *; repeat rewrite ZL6; unfold nat_of_P in |- *
 | unfold nat_of_P in |- * ]; ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *; ring.
intros r2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xO r2) q Datatypes.Eq); simpl in |- *; auto.
intros H3; rewrite <- (Pcompare_Eq_eq _ _ H3); simpl in |- *;
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *; ring.
intros H3; unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *; ring.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply trans_equal with (nat_of_P q + nat_of_P h);
 [ rewrite <- (nat_of_P_plus_morphism q); rewrite H5; unfold nat_of_P in |- *;
    simpl in |- *; repeat rewrite ZL6; unfold nat_of_P in |- *
 | unfold nat_of_P in |- * ]; ring.
generalize H2; case q1; case r1; simpl in |- *.
intros r2 q2. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xO r2) q Datatypes.Eq); simpl in |- *; auto.
intros; apply lt_O_nat_of_P; auto.
intros H H0; apply nat_of_P_lt_Lt_compare_morphism; auto.
intros H3 H7; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply plus_lt_reg_l with (p := nat_of_P q);
 rewrite <- (nat_of_P_plus_morphism q); rewrite H5; 
 unfold nat_of_P in |- *; simpl in |- *; unfold nat_of_P in |- *;
 simpl in |- *; repeat rewrite ZL6; unfold nat_of_P in |- *;
 apply lt_trans with (Pmult_nat r2 1 + Pmult_nat q 1); 
 auto with arith.
intros; apply lt_O_nat_of_P; auto.
intros r2 HH. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare (xO r2) q Datatypes.Eq); simpl in |- *.
intros; apply lt_O_nat_of_P; auto.
intros H3; apply nat_of_P_lt_Lt_compare_morphism; auto.
intros H3; case (Pminus_mask_Gt _ _ H3); intros h (H4, (H5, H6));
 unfold Pminus in |- *; rewrite H4;
 apply plus_lt_reg_l with (p := nat_of_P q);
 rewrite <- (nat_of_P_plus_morphism q); rewrite H5; 
 unfold nat_of_P in |- *; simpl in |- *; repeat rewrite ZL6;
 unfold nat_of_P in |- *;
 apply lt_trans with (Pmult_nat r2 1 + Pmult_nat q 1); 
 auto with arith.
auto.
Qed.

(**  Turn an optional positive into a relative number *)
Definition oZ1 (x : Option positive) :=
  match x with
  | None => 0%Z
  | Some z => Zpos z
  end.
 
(** Definition of the quotient
   - Take two relative numbers [n], [m] 
   - Return the quotient ([ZERO] if [m=ZERO]) *)
Definition Zquotient (n m : Z) :=
  match n, m with
  | Z0, _ => 0%Z
  | _, Z0 => 0%Z
  | Zpos x, Zpos y => match Pdiv x y with
                      | (x, _) => oZ1 x
                      end
  | Zneg x, Zneg y => match Pdiv x y with
                      | (x, _) => oZ1 x
                      end
  | Zpos x, Zneg y => match Pdiv x y with
                      | (x, _) => (- oZ1 x)%Z
                      end
  | Zneg x, Zpos y => match Pdiv x y with
                      | (x, _) => (- oZ1 x)%Z
                      end
  end.
 
(** Useful lemmae for oZ1 and oZ *)
 
Theorem inj_oZ1 : forall z, oZ1 z = Z_of_nat (oZ z).
intros z; case z; simpl in |- *; try (exact POS_inject; auto); auto.
Qed.
 
Theorem Zero_le_oZ : forall z, 0 <= oZ z.
intros z; case z; simpl in |- *; auto with arith.
Qed.
Hint Resolve Zero_le_oZ: arith.
 
 
(** Zquotient is correct *)
Theorem ZquotientProp :
 forall m n : Z,
 n <> 0%Z ->
 ex
   (fun r : Z =>
    m = (Zquotient m n * n + r)%Z /\
    (Zabs (Zquotient m n * n) <= Zabs m)%Z /\ (Zabs r < Zabs n)%Z).
intros m n; unfold Zquotient in |- *; case n; simpl in |- *.
intros H; case H; auto.
intros n' Hn'; case m; simpl in |- *; auto.
exists 0%Z; repeat split; simpl in |- *; auto with zarith.
intros m'; generalize (Pdiv_correct m' n'); case (Pdiv m' n'); simpl in |- *;
 auto.
intros q r (H1, H2); exists (oZ1 r); repeat (split; auto with zarith).
rewrite (POS_inject m'); auto.
rewrite H1.
rewrite Znat.inj_plus; rewrite Znat.inj_mult.
rewrite (POS_inject n'); auto.
repeat rewrite inj_oZ1; auto.
rewrite inj_oZ1; rewrite Zabs_eq; auto with zarith.
rewrite (POS_inject m'); auto with zarith.
rewrite (POS_inject n'); auto with zarith.
rewrite inj_oZ1; rewrite Zabs_eq; auto with zarith.
rewrite (POS_inject n'); auto with zarith.
intros m'; generalize (Pdiv_correct m' n'); case (Pdiv m' n'); simpl in |- *;
 auto.
intros q r (H1, H2); exists (- oZ1 r)%Z; repeat (split; auto with zarith).
replace (Zneg m') with (- Zpos m')%Z; [ idtac | simpl in |- *; auto ].
rewrite (POS_inject m'); auto.
rewrite H1.
rewrite Znat.inj_plus; rewrite Znat.inj_mult.
rewrite (POS_inject n'); auto.
repeat rewrite inj_oZ1; auto with zarith.
ring.
rewrite <- Zopp_mult_distr_l; rewrite Zabs_Zopp.
rewrite inj_oZ1; rewrite Zabs_eq; auto with zarith.
rewrite (POS_inject m'); auto with zarith.
rewrite (POS_inject n'); auto with zarith.
rewrite Zabs_Zopp.
rewrite inj_oZ1; rewrite Zabs_eq; auto with zarith.
rewrite (POS_inject n'); auto with zarith.
intros n' Hn'; case m; simpl in |- *; auto.
exists 0%Z; repeat split; simpl in |- *; auto with zarith.
intros m'; generalize (Pdiv_correct m' n'); case (Pdiv m' n'); simpl in |- *;
 auto.
intros q r (H1, H2); exists (oZ1 r); repeat (split; auto with zarith).
replace (Zneg n') with (- Zpos n')%Z; [ idtac | simpl in |- *; auto ].
rewrite (POS_inject m'); auto.
rewrite H1.
rewrite Znat.inj_plus; rewrite Znat.inj_mult.
rewrite (POS_inject n'); auto.
repeat rewrite inj_oZ1; auto with zarith.
ring.
replace (Zneg n') with (- Zpos n')%Z; [ idtac | simpl in |- *; auto ].
rewrite Zmult_opp_opp.
rewrite inj_oZ1; rewrite Zabs_eq; auto with zarith.
rewrite (POS_inject n'); auto with zarith.
rewrite (POS_inject m'); auto with zarith.
rewrite inj_oZ1; rewrite Zabs_eq; auto with zarith.
rewrite (POS_inject n'); auto with zarith.
intros m'; generalize (Pdiv_correct m' n'); case (Pdiv m' n'); simpl in |- *;
 auto.
intros q r (H1, H2); exists (- oZ1 r)%Z; repeat (split; auto with zarith).
replace (Zneg m') with (- Zpos m')%Z; [ idtac | simpl in |- *; auto ].
rewrite (POS_inject m'); auto.
replace (Zneg n') with (- Zpos n')%Z; [ idtac | simpl in |- *; auto ].
rewrite H1.
rewrite Znat.inj_plus; rewrite Znat.inj_mult.
rewrite (POS_inject n'); auto.
repeat rewrite inj_oZ1; auto with zarith.
ring.
replace (Zneg n') with (- Zpos n')%Z; [ idtac | simpl in |- *; auto ].
rewrite <- Zopp_mult_distr_r; rewrite Zabs_Zopp.
rewrite inj_oZ1; rewrite Zabs_eq; auto with zarith.
rewrite (POS_inject m'); auto with zarith.
rewrite (POS_inject n'); auto with zarith.
rewrite Zabs_Zopp.
rewrite inj_oZ1; rewrite Zabs_eq; auto with zarith.
rewrite (POS_inject n'); auto with zarith.
Qed.

(** The quotient of two positive numbers is positive *) 
Theorem ZquotientPos :
 forall z1 z2 : Z, (0 <= z1)%Z -> (0 <= z2)%Z -> (0 <= Zquotient z1 z2)%Z.
intros z1 z2 H H0; case (Z_eq_dec z2 0); intros Z1.
rewrite Z1; red in |- *; case z1; simpl in |- *; auto; intros; red in |- *;
 intros; discriminate.
case (ZquotientProp z1 z2); auto; intros r (H1, (H2, H3)).
case (Zle_or_lt 0 (Zquotient z1 z2)); auto; intros Z2.
Contradict H3; apply Zle_not_lt.
replace r with (z1 - Zquotient z1 z2 * z2)%Z;
 [ idtac | pattern z1 at 1 in |- *; rewrite H1; ring ].
repeat rewrite Zabs_eq; auto.
pattern z2 at 1 in |- *; replace z2 with (0 + 1 * z2)%Z; [ idtac | ring ].
unfold Zminus in |- *; apply Zle_trans with (z1 + 1 * z2)%Z; auto with zarith.
apply Zplus_le_compat_l.
rewrite Zopp_mult_distr_l.
apply Zmult_le_compat_r; auto with zarith.
unfold Zminus in |- *; rewrite Zopp_mult_distr_l; auto with zarith.
Qed.
 
(** Definition of m divides n ([(Zdivides n m)]) *)
Definition Zdivides (n m : Z) := exists q : Z, n = (m * q)%Z.
 
 
(** Some properties of Zdivides *) 
Theorem ZdividesZquotient :
 forall n m : Z, m <> 0%Z -> Zdivides n m -> n = (Zquotient n m * m)%Z.
intros n m H' H'0.
case H'0; intros z1 Hz1.
case (ZquotientProp n m); auto; intros z2 (Hz2, (Hz3, Hz4)).
cut (z2 = 0%Z);
 [ intros H1; pattern n at 1 in |- *; rewrite Hz2; rewrite H1; ring | idtac ].
cut (z2 = ((z1 - Zquotient n m) * m)%Z); [ intros H2 | idtac ].
case (Z_eq_dec (z1 - Zquotient n m) 0); intros H3.
rewrite H2; rewrite H3; ring.
Contradict Hz4.
replace (Zabs m) with (1 * Zabs m)%Z; [ idtac | ring ].
apply Zle_not_lt; rewrite H2.
rewrite Zabs_Zmult; apply Zmult_le_compat_r; auto with zarith.
generalize H3; case (z1 - Zquotient n m)%Z;
 try (intros H1; case H1; auto; fail); simpl in |- *; 
 intros p; case p; simpl in |- *; auto; intros; red in |- *; 
 simpl in |- *; auto; red in |- *; intros; discriminate.
rewrite Zmult_minus_distr_r; rewrite (Zmult_comm z1); rewrite <- Hz1;
 (pattern n at 1 in |- *; rewrite Hz2); ring.
Qed.
 
Theorem ZdividesZquotientInv :
 forall n m : Z, n = (Zquotient n m * m)%Z -> Zdivides n m.
intros n m H'; red in |- *.
exists (Zquotient n m); auto.
pattern n at 1 in |- *; rewrite H'; auto with zarith.
Qed.
 
Theorem ZdividesMult :
 forall n m p : Z, Zdivides n m -> Zdivides (p * n) (p * m).
intros n m p H'; red in H'.
elim H'; intros q E.
red in |- *.
exists q.
rewrite E.
auto with zarith.
Qed.
 
 
Theorem ZdividesDiv :
 forall n m p : Z, p <> 0%Z -> Zdivides (p * n) (p * m) -> Zdivides n m.
intros n m p H' H'0.
case H'0; intros q E.
exists q.
apply Zeq_mult_simpl with (c := p); auto.
rewrite (Zmult_comm n); rewrite E; ring.
Qed.
 
(* Zdivides is decidable *) 
Definition ZdividesP : forall n m : Z, {Zdivides n m} + {~ Zdivides n m}.
intros n m; case m.
case n.
left; red in |- *; exists 0%Z; auto with zarith.
intros p; right; red in |- *; intros H; case H; simpl in |- *; intros f H1;
 discriminate.
intros p; right; red in |- *; intros H; case H; simpl in |- *; intros f H1;
 discriminate.
intros p; generalize (Z_eq_bool_correct (Zquotient n (Zpos p) * Zpos p) n);
 case (Z_eq_bool (Zquotient n (Zpos p) * Zpos p) n); 
 intros H1.
left; apply ZdividesZquotientInv; auto.
right; Contradict H1; apply sym_equal; apply ZdividesZquotient; auto.
red in |- *; intros; discriminate.
intros p; generalize (Z_eq_bool_correct (Zquotient n (Zneg p) * Zneg p) n);
 case (Z_eq_bool (Zquotient n (Zneg p) * Zneg p) n); 
 intros H1.
left; apply ZdividesZquotientInv; auto.
right; Contradict H1; apply sym_equal; apply ZdividesZquotient; auto.
red in |- *; intros; discriminate.
Defined.
Eval compute in (ZdividesP 4 2).
 
Theorem Zquotient1 : forall m : Z, Zquotient m 1 = m.
intros m.
case (ZquotientProp m 1); auto.
red in |- *; intros; discriminate.
intros z (H1, (H2, H3)).
pattern m at 2 in |- *; rewrite H1; replace z with 0%Z; try ring.
generalize H3; case z; simpl in |- *; auto; intros p; case p;
 unfold Zlt in |- *; simpl in |- *; intros; discriminate.
Qed.
 
Theorem Zdivides1 : forall m : Z, Zdivides m 1.
intros m; exists m; auto with zarith.
Qed.
 

(* Unicity of the quotient *) 
Theorem ZquotientUnique :
 forall m n q r : Z,
 n <> 0%Z ->
 m = (q * n + r)%Z ->
 (Zabs (q * n) <= Zabs m)%Z -> (Zabs r < Zabs n)%Z -> q = Zquotient m n.
intros m n q r H' H'0 H'1 H'2.
case (ZquotientProp m n); auto; intros z (H0, (H1, H2)).
case (Zle_or_lt (Zabs q) (Zabs (Zquotient m n))); intros Zl1; auto with arith.
case (Zle_lt_or_eq _ _ Zl1); clear Zl1; intros Zl1; auto with arith.
Contradict H1; apply Zlt_not_le.
pattern m at 1 in |- *; rewrite H'0.
apply Zle_lt_trans with (Zabs (q * n) + Zabs r)%Z; auto with zarith.
apply Zlt_le_trans with (Zabs (q * n) + Zabs n)%Z; auto with zarith.
repeat rewrite Zabs_Zmult.
replace (Zabs q * Zabs n + Zabs n)%Z with (Zsucc (Zabs q) * Zabs n)%Z;
 [ auto with zarith | unfold Zsucc in |- *; ring ].
case (Zabs_eq_case _ _ Zl1); auto.
intros H;
 (cut (Zquotient m n = 0%Z);
   [ intros H3; rewrite H; repeat rewrite H3; simpl in |- *; auto | idtac ]).
cut (Zabs (Zquotient m n) < 1)%Z.
case (Zquotient m n); simpl in |- *; auto; intros p; case p;
 unfold Zlt in |- *; simpl in |- *; intros; discriminate.
apply Zgt_lt; apply Zmult_gt_reg_r with (p := Zabs n); apply Zlt_gt;
 auto with zarith.
case (Zle_lt_or_eq 0 (Zabs n)); auto with zarith.
intros H3; case H'; auto.
generalize H3; case n; simpl in |- *; auto; intros; discriminate.
rewrite <- Zabs_Zmult.
replace (1 * Zabs n)%Z with (Zabs n); [ idtac | ring ].
apply Zle_lt_trans with (1 := H1).
apply Zgt_lt; apply Zmult_gt_reg_r with (p := (1 + 1)%Z); apply Zlt_gt;
 auto with zarith.
replace (Zabs m * (1 + 1))%Z with (Zabs (m + m)).
replace (Zabs n * (1 + 1))%Z with (Zabs n + Zabs n)%Z; [ idtac | ring ].
pattern m at 1 in |- *; rewrite H'0; rewrite H0; rewrite H.
replace (- Zquotient m n * n + r + (Zquotient m n * n + z))%Z with (r + z)%Z;
 [ idtac | ring ].
apply Zle_lt_trans with (Zabs r + Zabs z)%Z; auto with zarith.
rewrite <- (Zabs_eq (1 + 1)); auto with zarith.
rewrite <- Zabs_Zmult; apply f_equal with (f := Zabs); auto with zarith.
Contradict H'1; apply Zlt_not_le.
pattern m at 1 in |- *; rewrite H0.
apply Zle_lt_trans with (Zabs (Zquotient m n * n) + Zabs z)%Z;
 auto with zarith.
apply Zlt_le_trans with (Zabs (Zquotient m n * n) + Zabs n)%Z;
 auto with zarith.
repeat rewrite Zabs_Zmult.
replace (Zabs (Zquotient m n) * Zabs n + Zabs n)%Z with
 (Zsucc (Zabs (Zquotient m n)) * Zabs n)%Z;
 [ auto with zarith | unfold Zsucc in |- *; ring ].
Qed.
 
Theorem ZquotientZopp :
 forall m n : Z, Zquotient (- m) n = (- Zquotient m n)%Z.
intros m n; case (Z_eq_dec n 0); intros Z1.
rewrite Z1; unfold Zquotient in |- *; case n; case m; simpl in |- *; auto.
case (ZquotientProp m n); auto; intros r1 (H'2, (H'3, H'4)); auto with zarith.
apply sym_equal;
 apply ZquotientUnique with (q := (- Zquotient m n)%Z) (r := (- r1)%Z); 
 auto.
pattern m at 1 in |- *; rewrite H'2; ring.
rewrite <- Zopp_mult_distr_l; repeat rewrite Zabs_Zopp; auto.
rewrite Zabs_Zopp; auto.
Qed.

(** Monotonictiy of the quotient *) 
Theorem ZquotientMonotone :
 forall n m q : Z,
 (Zabs n <= Zabs m)%Z -> (Zabs (Zquotient n q) <= Zabs (Zquotient m q))%Z.
intros n m q H; case (Zle_lt_or_eq _ _ H); intros Z0.
case (Z_eq_dec q 0); intros Z1.
rewrite Z1; unfold Zquotient in |- *; case n; case m; simpl in |- *;
 auto with zarith.
case (Zle_or_lt (Zabs (Zquotient n q)) (Zabs (Zquotient m q))); auto;
 intros H'1.
case (ZquotientProp m q); auto; intros r1 (H'2, (H'3, H'4)); auto with zarith.
case (ZquotientProp n q); auto; intros r2 (H'5, (H'6, H'7)); auto with zarith.
Contradict H'6.
apply Zlt_not_le.
apply Zlt_le_trans with (1 := Z0).
rewrite H'2.
apply Zle_trans with (Zabs (Zquotient m q * q) + Zabs r1)%Z; auto with zarith.
apply Zle_trans with (Zabs (Zquotient m q * q) + Zabs q)%Z; auto with zarith.
repeat rewrite Zabs_Zmult.
replace (Zabs (Zquotient m q) * Zabs q + Zabs q)%Z with
 (Zsucc (Zabs (Zquotient m q)) * Zabs q)%Z;
 [ idtac | unfold Zsucc in |- *; ring ].
cut (0 < Zabs q)%Z; auto with zarith.
case (Zle_lt_or_eq 0 (Zabs q)); auto with zarith.
intros H'6; case Z1; auto.
generalize H'6; case q; simpl in |- *; auto; intros; discriminate.
case (Zabs_eq_case _ _ Z0); intros Z1; rewrite Z1; auto with zarith.
rewrite ZquotientZopp; rewrite Zabs_Zopp; auto with zarith.
Qed.
 
Theorem ZDividesLe :
 forall n m : Z, n <> 0%Z -> Zdivides n m -> (Zabs m <= Zabs n)%Z.
intros n m H' H'0; case H'0; intros q E; rewrite E.
rewrite Zabs_Zmult.
pattern (Zabs m) at 1 in |- *; replace (Zabs m) with (Zabs m * 1)%Z;
 [ idtac | ring ].
apply Zmult_le_compat_l; auto with zarith.
generalize E H'; case q; simpl in |- *; auto;
 try (intros H1 H2; case H2; rewrite H1; ring; fail); 
 intros p; case p; unfold Zle in |- *; simpl in |- *; 
 intros; red in |- *; discriminate.
Qed.
 
Theorem Zquotient_mult_comp :
 forall m n p : Z, p <> 0%Z -> Zquotient (m * p) (n * p) = Zquotient m n.
intros m n p Z1; case (Z_eq_dec n 0); intros Z2.
rewrite Z2; unfold Zquotient in |- *; case (m * p)%Z; case m; simpl in |- *;
 auto.
case (ZquotientProp m n); auto; intros r (H1, (H2, H3)).
apply sym_equal; apply ZquotientUnique with (r := (r * p)%Z);
 auto with zarith.
red in |- *; intros H; case (Zmult_integral _ _ H); intros H4;
 try (case Z1; auto; fail); case Z2; auto.
pattern m at 1 in |- *; rewrite H1; ring.
rewrite Zmult_assoc.
repeat rewrite (fun x => Zabs_Zmult x p); auto with zarith.
repeat rewrite Zabs_Zmult; auto with zarith.
apply Zmult_gt_0_lt_compat_r; auto with zarith.
apply Zlt_gt; generalize Z1; case p; simpl in |- *;
 try (intros H4; case H4; auto; fail); unfold Zlt in |- *; 
 simpl in |- *; auto; intros; red in |- *; intros; 
 discriminate.
Qed.
 
Theorem ZDivides_add :
 forall n m p : Z, Zdivides n p -> Zdivides m p -> Zdivides (n + m) p.
intros n m p H' H'0.
case H'; intros z1 Hz1.
case H'0; intros z2 Hz2.
exists (z1 + z2)%Z; rewrite Hz1; rewrite Hz2; ring.
Qed.
 
Theorem NDivides_minus :
 forall n m p : Z, Zdivides n p -> Zdivides m p -> Zdivides (n - m) p.
intros n m p H' H'0.
case H'; intros z1 Hz1.
case H'0; intros z2 Hz2.
exists (z1 - z2)%Z; rewrite Hz1; rewrite Hz2; ring.
Qed.
 
Theorem ZDivides_mult :
 forall n m p q : Z, Zdivides n p -> Zdivides m q -> Zdivides (n * m) (p * q).
intros n m p q H' H'0.
case H'; intros z1 Hz1.
case H'0; intros z2 Hz2.
exists (z1 * z2)%Z; rewrite Hz1; rewrite Hz2; ring.
Qed.
 
Theorem ZdividesTrans :
 forall n m p : Z, Zdivides n m -> Zdivides m p -> Zdivides n p.
intros n m p H' H'0.
case H'; intros z1 Hz1.
case H'0; intros z2 Hz2.
exists (z1 * z2)%Z; rewrite Hz1; rewrite Hz2; ring.
Qed.
