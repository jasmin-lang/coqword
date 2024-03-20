(* Copyright 2017-2021, École Polytechnique, France                     *)
(*                                                                      *)
(* Permission is hereby granted, free of charge, to any person          *)
(* obtaining a copy of this software and associated documentation       *)
(* files (the "Software"), to deal in the Software without restriction, *)
(* including without limitation the rights to use, copy, modify, merge, *)
(* publish, distribute, sublicense, and/or sell copies of the Software, *)
(* and to permit persons to whom the Software is furnished to do so,    *)
(* subject to the following conditions:                                 *)
(*                                                                      *)
(* The above copyright notice and this permission notice shall be       *)
(* included in all copies or substantial portions of the Software.      *)
(*                                                                      *)
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,      *)
(* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF   *)
(* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND                *)
(* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS  *)
(* BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN   *)
(* ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN    *)
(* CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE     *)
(* SOFTWARE.                                                            *)

(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint intdiv.
From Coq Require Import Arith ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.

Import GRing.Theory Num.Theory Order.POrderTheory.

Local Notation "m ^ n" := (expn m n) : nat_scope.

Notation rmorph := (rmorphM, rmorphB, rmorphD, rmorphN, rmorph1, rmorph0).

(* -------------------------------------------------------------------- *)
Section PosInd.
Context (P : positive -> Prop).

Lemma posind : P 1%positive -> (forall p, P p -> P (p + 1)) -> forall p, P p.
Proof.
move=> h1 ih p; rewrite -[p]Pos2Nat.id; elim: (Pos.to_nat p) => //.
by move=> [|n] // ihSn; rewrite -addn1 Nat2Pos.inj_add //; apply/ih.
Qed.
End PosInd.

(* -------------------------------------------------------------------- *)
Lemma addP m n : (m + n)%coq_nat = (m + n)%nat.
Proof. by []. Qed.

Lemma mulP m n : (m * n)%coq_nat = (m * n)%nat.
Proof. by []. Qed.

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

Lemma int_to_ZK : cancel int_to_Z Z_to_int.
Proof. by case=> [[|n]|n] //=; rewrite Pos.of_nat_succ Nat2Pos.id. Qed.

(* -------------------------------------------------------------------- *)
Lemma ZeqbP x y : reflect (x = y) (Z.eqb x y).
Proof. by apply: (iffP idP) => /Z.eqb_eq. Qed.

HB.instance Definition _ := hasDecEq.Build Z ZeqbP.

(* -------------------------------------------------------------------- *)
HB.instance Definition _ := Countable.copy Z (can_type Z_to_intK).

(* -------------------------------------------------------------------- *)
HB.instance Definition _ := GRing.isZmodule.Build Z
  Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.

(* -------------------------------------------------------------------- *)
HB.instance Definition _ := GRing.Zmodule_isComRing.Build Z
  Z.mul_assoc Z.mul_comm Z.mul_1_l Z.mul_add_distr_r (erefl true).

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

End ZUnitRing.

HB.instance Definition _ := GRing.ComRing_hasMulInverse.Build Z
  ZUnitRing.mulVZ ZUnitRing.unitZPl ZUnitRing.invZ_out.

HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build Z
  ZUnitRing.idomain_axiomZ.

(* -------------------------------------------------------------------- *)
Lemma leZP x y : reflect (x <= y) (x <=? y).
Proof. by apply: (iffP idP) => /Z.leb_le. Qed.

Lemma ltZP x y : reflect (x < y) (x <? y).
Proof. by apply: (iffP idP) => /Z.ltb_lt. Qed.

Definition lteZP := (
  (fun x y => rwP (leZP x y)),
  (fun x y => rwP (ltZP x y))).

(* --------------------------------------------------------------------- *)
Module ZNumDomain.
Lemma leZ_anti (x : Z) : 0 <=? x -> x <=? 0 -> x = 0.
Proof. by move=> ??; apply: Zle_bool_antisym. Qed.

Lemma leZ_mul (x y : Z) : 0 <=? x -> 0 <=? y -> 0 <=? (x * y)%R.
Proof. by rewrite -!lteZP; apply: Z.mul_nonneg_nonneg. Qed.

Lemma leZ_add (x y : Z) : 
  0 <=? x -> 0 <=? y -> 0 <=? (x + y)%R.
Proof. by rewrite -!lteZP; apply: Z.add_nonneg_nonneg. Qed.

Lemma subZ_ge0 (y x : Z) : (0 <=? (x - y)%R) = (y <=? x).
Proof.
by apply/leZP/leZP; [exact: Zle_0_minus_le | exact: Zle_minus_le_0].
Qed.

Lemma normZN x : Z.abs (- x) = Z.abs x.
Proof. exact: Z.abs_opp. Qed.

Lemma geZ0_norm x : 0 <=? x -> Z.abs x = x.
Proof. by rewrite -!lteZP; apply: Z.abs_eq. Qed.

Lemma leZ_norm_add (x y : Z) :
  Z.abs (x + y)%R <=? (Z.abs x + Z.abs y)%R.
Proof. by rewrite -!lteZP; apply/Z.abs_triangle. Qed.

Lemma eq0_normZ (x : Z) : Z.abs x = 0 -> x = 0.
Proof. by move/Z.abs_0_iff. Qed.

Lemma leZ_total (x y : Z) : (x <=? y) || (y <=? x).
Proof. by apply/orP; rewrite -!lteZP; apply/Z.le_ge_cases. Qed.

Lemma ltZ_def (x y : Z) : (x <? y) = (y != x) && (x <=? y).
Proof.
apply/idP/andP; rewrite -!lteZP.
* by move/Z.le_neq => [? /eqP]; rewrite eq_sym.
* by rewrite eq_sym; case=> /eqP ? ?; apply/Z.le_neq.
Qed.

Definition Z_realLeMixin := Num.IntegralDomain_isLeReal.Build Z
  leZ_add leZ_mul leZ_anti subZ_ge0 (leZ_total 0) normZN geZ0_norm ltZ_def.
End ZNumDomain.

HB.instance Definition _ := ZNumDomain.Z_realLeMixin.

(* -------------------------------------------------------------------- *)
Lemma ltzE {z1 z2 : Z} : (z1 <? z2)%Z = (z1 < z2)%R.
Proof. by []. Qed.

Lemma ltzP {z1 z2 : Z} : reflect (z1 < z2)%Z (z1 < z2)%R.
Proof. by rewrite -ltzE; apply: (iffP idP) => /Z.ltb_lt. Qed.

Lemma lezE {z1 z2 : Z} : (z1 <=? z2)%Z = (z1 <= z2)%R.
Proof. by []. Qed.

Lemma lezP {z1 z2 : Z} : reflect (z1 <= z2)%Z (z1 <= z2)%R.
Proof. by rewrite -lezE; apply: (iffP idP) => /Z.leb_le. Qed.

(* -------------------------------------------------------------------- *)
Lemma addZE (x y : Z) : (x + y)%Z = (x + y)%R.
Proof. by []. Qed.

Lemma oppZE (x : Z) : (- x)%Z = (- x)%R.
Proof. by []. Qed.

Lemma subZE (x y : Z) : (x - y)%Z = (x - y)%R.
Proof. by []. Qed.

Lemma mulZE (x y : Z) : (x * y)%Z = (x * y)%R.
Proof. by []. Qed.

Lemma expZE (x : Z) n : (x ^ Z.of_nat n)%Z = x ^+ n.
Proof.
elim: n => // n ih; rewrite exprS Nat2Z.inj_succ.
by rewrite Z.pow_succ_r ?ih //; apply/Nat2Z.is_nonneg.
Qed.

(* ==================================================================== *)
Lemma Z_to_int_is_additive : additive Z_to_int.
Proof.
have h x y: Z_to_int (Z.pos_sub x y) = ((Pos.to_nat x)%:Z - (Pos.to_nat y)%:Z)%R.
+ rewrite Z.pos_sub_spec; case E: (_ ?= _)%positive => /=.
  - by move/Pos.compare_eq: E => ->; rewrite addrN.
  - move/Pos.compare_lt_iff: E => E; rewrite Pos2Nat.inj_sub //.
    rewrite -subzn ?opprB //; apply/leP.
    by apply/Pos2Nat.inj_le/Pos.lt_le_incl.
  - move/Pos.compare_gt_iff: E => E; rewrite Pos2Nat.inj_sub //.
    rewrite -subzn ?opprB //; apply/leP.
    by apply/Pos2Nat.inj_le/Pos.lt_le_incl.
case=> [|x|x] [|y|y] //=.
+ by rewrite sub0r.
+ by rewrite opprK add0r.
+ by rewrite subr0.
+ by apply/h.
+ by rewrite opprK -PoszD Pos2Nat.inj_add.
+ by rewrite subr0.
+ by rewrite -opprD -PoszD Pos2Nat.inj_add.
+ by rewrite opprK [RHS]addrC; apply/h.
Qed.

HB.instance Definition _ := GRing.isAdditive.Build Z int Z_to_int
  Z_to_int_is_additive.

(* -------------------------------------------------------------------- *)
Lemma Z_to_int_is_multiplicative : multiplicative Z_to_int.
Proof.
split=> // -[|x|x] y /=; first by rewrite mul0r.
- elim/posind: x => [|p ih]; first by rewrite !mul1r.
  rewrite Pos2Z.inj_add addZE mulrDl mul1r raddfD /=.
  by rewrite ih Pos2Nat.inj_add /= addP PoszD mulrDl mul1r.
- elim/posind: x => [|p ih]; first by rewrite !mulN1r raddfN.
  rewrite -Pos2Z.add_neg_neg addZE mulrDl mulN1r.
  rewrite raddfB /= ih Pos2Nat.inj_add addP PoszD.
  by rewrite opprD mulrDl mulN1r.
Qed.

HB.instance Definition _ := GRing.isMultiplicative.Build Z int Z_to_int
  Z_to_int_is_multiplicative.

(* -------------------------------------------------------------------- *)
Lemma int_to_Z_is_additive : additive int_to_Z.
Proof. by apply/(can2_additive _ int_to_ZK)/Z_to_intK. Qed.

HB.instance Definition _ := GRing.isAdditive.Build int Z int_to_Z
  int_to_Z_is_additive.

(* -------------------------------------------------------------------- *)
Lemma int_to_Z_is_multiplicative : multiplicative int_to_Z.
Proof. by apply/(can2_rmorphism _ int_to_ZK)/Z_to_intK. Qed.

HB.instance Definition _ := GRing.isMultiplicative.Build int Z int_to_Z
  int_to_Z_is_multiplicative.

(* -------------------------------------------------------------------- *)
Lemma Z_to_int_of_natE k : Z_to_int (Z.of_nat k) = k%:Z.
Proof. by apply/(can_inj int_to_ZK); rewrite Z_to_intK. Qed.

(* -------------------------------------------------------------------- *)
Lemma int_of_Z_PoszE k : int_to_Z k%:Z = Z.of_nat k.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Coercion int_to_Z : int >-> Z.
Coercion Z_to_int : Z >-> int.

(* -------------------------------------------------------------------- *)
Delimit Scope int_scope with I.

Lemma leZE {x y : Z} : reflect (x <= y) (x <= y :> int).
Proof.
have h z: exists n : nat, Pos.to_nat z == n.+1.
- by case: (Pos2Nat.is_succ z)=> zS ->; exists zS.
case: x y => [|x|x] [|y|y] //=; try by constructor.
+ rewrite oppr_ge0 lez0_nat gtn_eqF; first by constructor.
  by apply/ltP/Pos2Nat.is_pos.
+ rewrite lez0_nat gtn_eqF; first by constructor.
  by apply/ltP/Pos2Nat.is_pos.
+ by rewrite lez_nat; apply: (iffP leP) => /Pos2Nat.inj_le.
+ by rewrite (eqP (xchooseP (h y))); constructor.
+ by rewrite oppr_le0; constructor.
+ by rewrite (eqP (xchooseP (h x))); constructor.
+ rewrite lerNr opprK; apply: (iffP idP).
  - by move/leP/Pos2Nat.inj_le/Pos2Z.neg_le_neg.
  rewrite -!Pos2Z.opp_pos -Z.opp_le_mono => {}h.
  by rewrite lez_nat -(rwP leP) -Pos2Nat.inj_le.
Qed.

Lemma ltZE (x y : Z) : reflect (x < y) (x < y :> int).
Proof. apply: (iffP idP).
+ rewrite lt_neqAle -(rwP andP) -(rwP leZE) => -[neq lt].
  apply/Z.le_neq; split=> // /(congr1 Z_to_int).
  by move/eqP; rewrite (negbTE neq).
+ move/Z.le_neq => [le neq]; rewrite lt_neqAle; apply/andP.
  rewrite -(rwP leZE); split=> //; apply/eqP.
  by move/(congr1 int_to_Z); rewrite !Z_to_intK.
Qed.

Definition lteZE :=
  (fun x y => rwP (@leZE x y), fun x y => rwP (@ltZE x y)).

Lemma divZE (a b : Z) : (0 < b)%R -> a / b = (a %/ b)%I.
Proof.
move/ltzP/(@ltZE 0) => h; have /(congr1 int_to_Z) := divz_eq a b.
rewrite mulrC !rmorph /= !Z_to_intK => /Zdiv_unique -> //.
rewrite !lteZE !rmorph /= !int_to_ZK subr_ge0 ltrBlDr.
rewrite (rwP andP) lez_floor ?gt_eqF //=.
by rewrite addrC -[X in (_ + X)%R]mul1r -mulrDl ltz_ceil.
Qed.

Lemma modZE (a b : Z) : (0 < b)%R -> a mod b = (a %% b)%I.
Proof.
move=> gt0_b; rewrite /modz Zmod_eq_full; last first.
+ by apply/eqP; rewrite gt_eqF.
+ by rewrite rmorphB !rmorphM /= !Z_to_intK divZE.
Qed.

Lemma divnZE (a b : nat) :
  b != 0%nat -> Z.of_nat (a %/ b) = (Z.of_nat a / Z.of_nat b)%Z.
Proof.
move=> nz_b; apply/(can_inj Z_to_intK); rewrite Z_to_int_of_natE.
rewrite -divz_nat divZE; last by case: b nz_b.
by rewrite int_to_ZK !Z_to_int_of_natE.
Qed.

Lemma modnZE (a b : nat) :
  b != 0%nat -> Z.of_nat (a %% b) = (Z.of_nat a mod Z.of_nat b)%Z.
Proof.
move=> nz_b; apply/(can_inj Z_to_intK); rewrite Z_to_int_of_natE.
rewrite -modz_nat modZE; last by case: b nz_b.
by rewrite int_to_ZK !Z_to_int_of_natE.
Qed.

(* ==================================================================== *)
Module Z2Nat.

(* -------------------------------------------------------------------- *)
Lemma z2n0 : Z.to_nat 0 = 0%nat.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma z2nD z1 z2 : (0 <= z1)%R -> (0 <= z2)%R ->
  Z.to_nat (z1 + z2) = (Z.to_nat z1 + Z.to_nat z2)%nat.
Proof.
by move=> ge0_z1 ge0_z2; apply/Z2Nat.inj_add; apply/lezP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma z2nM z1 z2 : (0 <= z1)%R -> (0 <= z2)%R ->
  Z.to_nat (z1 * z2) = (Z.to_nat z1 * Z.to_nat z2)%nat.
Proof.
by move=> ge0_z1 ge0_z2; apply/Z2Nat.inj_mul; apply/lezP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma z2n_sum {T : Type} (P : ssrbool.pred T) (F : T -> Z) r :
     (forall x, P x -> (0 <= F x)%R)
  -> Z.to_nat (\sum_(x <- r | P x) F x)%R =
       \sum_(x <- r | P x) Z.to_nat (F x).
Proof.
move=> ge0_F; elim: r => [|x r ih]; first by rewrite !big_nil z2n0.
rewrite !big_cons; case: ifPn => // Px.
by rewrite z2nD ?ih //; [apply/ge0_F | apply/sumr_ge0].
Qed.

(* -------------------------------------------------------------------- *)
Lemma z2nX (z : Z) n :
  (0 <= z)%R -> Z.to_nat (z ^+ n)%R = (Z.to_nat z ^ n)%nat.
Proof.
move=> ge0_z; elim: n => // n ih; rewrite exprS.
by rewrite z2nM ?exprn_ge0 // ih expnS.
Qed.

(* -------------------------------------------------------------------- *)
Lemma z2n_natmul (z : Z) n :
  (0 <= z)%R -> Z.to_nat (z *+ n) = (Z.to_nat z * n)%nat.
Proof.
move=> ge0_z; elim: n; first by rewrite muln0.
move=> n ih; rewrite mulrS.
by rewrite z2nD ?mulrn_wge0 // ih mulnS.
Qed.

(* -------------------------------------------------------------------- *)
Lemma z2nr n : Z.to_nat (n%:R) = n.
Proof. by rewrite z2n_natmul // mul1n. Qed.

End Z2Nat.

(* ==================================================================== *)
Module Nat2Z.
Lemma n2z0 : Z.of_nat 0 = 0%R.
Proof. by []. Qed.

Lemma n2z1 : Z.of_nat 1 = 1%R.
Proof. by []. Qed.

Lemma n2zD n m : Z.of_nat (n + m) = (Z.of_nat n + Z.of_nat m)%R.
Proof. by rewrite -addZE Nat2Z.inj_add. Qed.

Lemma n2zB n m : (m <= n)%nat ->
  Z.of_nat (n - m) = (Z.of_nat n - Z.of_nat m)%R.
Proof.
by move=> le; rewrite -subZE Nat2Z.inj_sub //; apply/leP.
Qed.

Lemma n2zM n m : Z.of_nat (n * m) = (Z.of_nat n * Z.of_nat m)%R.
Proof. by rewrite -mulZE Nat2Z.inj_mul. Qed.

Lemma n2zX n m : Z.of_nat (n ^ m) = (Z.of_nat n ^+ m)%R.
Proof. by elim: m => // m ih; rewrite exprS -ih -n2zM -expnS. Qed.
End Nat2Z.

(* -------------------------------------------------------------------- *)
Lemma oddZE (z : Z) : (0 <= z)%R -> Z.odd z = odd (Z.to_nat z).
Proof.
move=> ge0_z; have : injective nat_of_bool by move=> [] [].
apply; rewrite -modn2; apply/Nat2Z.inj; rewrite modnZE //.
by rewrite Z2Nat.id ?(rwP lezP) // Zmod_odd; case: ifP.
Qed.
