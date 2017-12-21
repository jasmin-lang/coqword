(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
(* ------- *) Require Import Arith ZArith Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.

Import GRing.Theory.

(* -------------------------------------------------------------------- *)
Definition int_to_Z (z : int) : Z :=
  match z with
  | Posz n =>  (Z.of_nat n   )
  | Negz n => -(Z.of_nat n.+1)
  end.

Definition Z_to_int (z : Z) : int :=
  match z with
  | 0       => 0%:Z
  | Z.pos p => (Pos.to_nat p)%:Z
  | Z.neg p => - (Pos.to_nat p)%:Z
  end.

Lemma Z_to_intK : cancel Z_to_int int_to_Z.
Proof.
case=> [//|p|p] /=; first by rewrite positive_nat_Z.
have /ltP := Pos2Nat.is_pos p; case E: Pos.to_nat => [|n] // _.
by rewrite -NegzE /= (SuccNat2Pos.inv _ _ E).
Qed.

(* -------------------------------------------------------------------- *)
Lemma ZeqbP x y : reflect (x = y) (Z.eqb x y).
Proof. by apply: (iffP idP) => /Z.eqb_eq. Qed.

Definition Z_eqMixin := EqMixin ZeqbP.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.

(* -------------------------------------------------------------------- *)
Definition Z_choiceMixin := CanChoiceMixin Z_to_intK.
Canonical Z_choiceType := Eval hnf in ChoiceType Z Z_choiceMixin.

Definition Z_countMixin := CanCountMixin Z_to_intK.
Canonical Z_counType := Eval hnf in CountType Z Z_countMixin.

(* -------------------------------------------------------------------- *)
Definition Z_zmodMixin :=
  ZmodMixin Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.
Canonical Z_zmodType := Eval hnf in ZmodType Z Z_zmodMixin.

(* -------------------------------------------------------------------- *)
Definition Z_comRingMixin :=
  ComRingMixin
    Z.mul_assoc Z.mul_comm Z.mul_1_l Z.mul_add_distr_r (erefl true).
Canonical Z_ringType := Eval hnf in RingType Z Z_comRingMixin.
Canonical Z_comRingType := Eval hnf in ComRingType Z Z.mul_comm.

(* -------------------------------------------------------------------- *)
Module ZUnitRing.
Definition unitZ := [qualify a n : Z | (n == 1) || (n == -1)].
Definition invZ n : Z := n.

Lemma mulVZ : {in unitZ, left_inverse 1%R invZ *%R}.
Proof. by move=> n /pred2P[] ->. Qed.

Lemma unitZPl (m n : Z) : (n * m = 1)%R -> m \is a unitZ.
Proof. by rewrite mulrC => /Z.mul_eq_1 [] ->. Qed.

Lemma  invZ_out : {in [predC unitZ], invZ =1 id}.
Proof. exact. Qed.

Lemma idomain_axiomZ (m n : Z) : (m * n = 0)%R -> (m == 0) || (n == 0).
Proof. by move/Z.mul_eq_0 => [] ->; rewrite eqxx ?orbT. Qed.

Definition comUnitMixin := ComUnitRingMixin mulVZ unitZPl invZ_out.
End ZUnitRing.

Canonical Z_unitRingType :=
  Eval hnf in UnitRingType Z ZUnitRing.comUnitMixin.
Canonical Z_comUnitRing :=
  Eval hnf in [comUnitRingType of Z].
Canonical Z_iDomain :=
  Eval hnf in IdomainType Z ZUnitRing.idomain_axiomZ.

(* -------------------------------------------------------------------- *)
Lemma lezP x y : reflect (x <= y) (x <=? y).
Proof. by apply: (iffP idP) => /Z.leb_le. Qed.

Lemma ltzP x y : reflect (x < y) (x <? y).
Proof. by apply: (iffP idP) => /Z.ltb_lt. Qed.

Definition ltezP := (
  (fun x y => rwP (lezP x y)),
  (fun x y => rwP (ltzP x y))).

(* --------------------------------------------------------------------- *)
Module ZNumDomain.
Lemma leZ_norm_add (x y : Z) :
  Z.abs (x + y)%R <=? (Z.abs x + Z.abs y)%R.
Proof. by rewrite -!ltezP; apply/Z.abs_triangle. Qed.

Lemma ltZ_add (x y : Z) : 
  0 <? x -> 0 <? y -> 0 <? (x + y)%R.
Proof. by rewrite -!ltezP; apply/Z.add_pos_pos. Qed.

Lemma eq0_normZ (x : Z) : Z.abs x = 0 -> x = 0.
Proof. by move/Z.abs_0_iff. Qed.

Lemma leZ_total (x y : Z) : (x <=? y) || (y <=? x).
Proof. by apply/orP; rewrite -!ltezP; apply/Z.le_ge_cases. Qed.

Lemma normZM : {morph Z.abs : x y / (x * y)%R}.
Proof. by move=> x y; rewrite Z.abs_mul. Qed.

Lemma leZ_def (x y : Z) : (x <=? y) = (Z.abs (y - x)%R == (y - x)%R).
Proof.
apply/idP/eqP; rewrite -!ltezP.
* by move=> h; rewrite Z.abs_eq // Z.le_0_sub.
* by move/Z.abs_eq_iff; rewrite Z.le_0_sub.
Qed.

Lemma ltZ_def (x y : Z) : (x <? y) = (y != x) && (x <=? y).
Proof.
apply/idP/andP; rewrite -!ltezP.
* by move/Z.le_neq => [? /eqP]; rewrite eq_sym.
* by rewrite eq_sym; case=> /eqP ? ?; apply/Z.le_neq.
Qed.

Definition Z_numMixin :=
  NumMixin leZ_norm_add ltZ_add eq0_normZ (in2W leZ_total)
           normZM leZ_def ltZ_def.
End ZNumDomain.

Canonical Z_numType := Eval hnf in NumDomainType Z ZNumDomain.Z_numMixin.
Canonical Z_realDomainType := RealDomainType Z (ZNumDomain.leZ_total 0).
