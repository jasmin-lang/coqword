(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
(* ------- *) Require Import Arith ZArith Omega ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Open Scope Z_scope.
Local Open Scope ring_scope.
Local Open Scope nat_scope.

Import GRing.Theory Num.Theory.

Local Notation "m ^ n" := (expn m n) : nat_scope.

(* -------------------------------------------------------------------- *)
Section WordDef.
Context (nbits : nat).

Definition modulus := two_power_nat nbits.

(* -------------------------------------------------------------------- *)
Lemma two_power_natE n : two_power_nat n = 2%:R ^+ n.
Proof. by elim: n => // n ih; rewrite two_power_nat_S exprS ih. Qed.

Lemma modulusE : modulus = 2%:R^+nbits.
Proof. by apply/two_power_natE. Qed.

Lemma modulus_gt0 : (0 < modulus)%R.
Proof.
rewrite modulusE; elim: nbits => [|n ih].
+ by rewrite expr0. + by rewrite exprS mulr_gt0.
Qed.

Lemma Ztonat_modulus : Z.to_nat modulus = 2 ^ nbits.
Proof. by rewrite modulusE Z2Nat.z2nX. Qed.

Lemma Zofnat_modulus : modulus = Z.of_nat (2 ^ nbits).
Proof. by rewrite -Ztonat_modulus Z2Nat.id. Qed.

Lemma prednK_modulus n : (2 ^ n).-1.+1 = 2 ^ n.
Proof. by rewrite prednK // expn_gt0. Qed.

(* -------------------------------------------------------------------- *)
Notation isword z := (0 <= z < modulus)%R.

Record word := mkWord { toword :> Z; _ : isword toword; }.

Canonical word_subType := Eval hnf in [subType for toword].
Definition word_eqMixin := [eqMixin of word by <:].
Canonical word_eqType := Eval hnf in EqType word word_eqMixin.
Definition word_choiceMixin := [choiceMixin of word by <:].
Canonical word_choiceType := Eval hnf in ChoiceType word word_choiceMixin.
Definition word_countMixin := [countMixin of word by <:].
Canonical word_countType := Eval hnf in CountType word word_countMixin.
End WordDef.

(* -------------------------------------------------------------------- *)
Notation "n .-word" := (word n)
  (at level 2, format "n .-word") : type_scope.

(* -------------------------------------------------------------------- *)
Section WordRing.
Context (n : nat).

Notation isword z := (0 <= z < modulus n)%R.

(* -------------------------------------------------------------------- *)
Lemma mkword_proof (z : Z) : isword (z mod (modulus n))%Z.
Proof.
apply/andP; rewrite -(rwP ltzP) -(rwP lezP).
by apply/Z_mod_lt/Z.lt_gt/ltzP/modulus_gt0.
Qed.

Definition mkword (z : Z) := mkWord (mkword_proof z).

(* -------------------------------------------------------------------- *)
Definition urepr (w : word n) : Z := val w.

(* -------------------------------------------------------------------- *)
Lemma urepr_ge0 (w : word n) : (0 <= urepr w)%R.
Proof. by case: w => w; rewrite /urepr /= => /andP[]. Qed.

(* -------------------------------------------------------------------- *)
Lemma urepr_ltmod (w : word n) : (urepr w < modulus n)%R.
Proof. by case: w => w; rewrite /urepr /= => /andP[]. Qed.

(* -------------------------------------------------------------------- *)
Lemma urepr_isword (w : word n) : isword (urepr w).
Proof. by rewrite urepr_ge0 urepr_ltmod. Qed.

(* -------------------------------------------------------------------- *)
Lemma ureprK : cancel urepr mkword.
Proof.
move=> w; rewrite (rwP eqP) -val_eqE /=; rewrite Z.mod_small //.
by rewrite !(rwP lezP, rwP ltzP) (rwP andP) urepr_isword.
Qed.

(* -------------------------------------------------------------------- *)
Lemma mkwordK (z : Z) : urepr (mkword z) = (z mod modulus n)%Z.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma isword_ofnatZP (k : nat) :
  reflect (0 <= Z.of_nat k < modulus n)%Z (k < 2 ^ n).
Proof. apply: (iffP idP) => lt.
+ split; first by apply/Nat2Z.is_nonneg.
  by move/ltP/Nat2Z.inj_lt: lt; rewrite -Ztonat_modulus Z2Nat.id.
+ case: lt => [_ lt]; apply/ltP/Nat2Z.inj_lt.
  by rewrite -Ztonat_modulus Z2Nat.id.
Qed.

(* -------------------------------------------------------------------- *)
Lemma isword_tonatZP (k : Z) :
  (0 <= k < modulus n)%Z -> Z.to_nat k < 2 ^ n.
Proof.
case=> le lt; apply/ltP/Nat2Z.inj_lt.
by rewrite Z2Nat.id // -Zofnat_modulus.
Qed.

(* -------------------------------------------------------------------- *)
Lemma isword_tonatZWP (k : Z) :
  (0 <= k < modulus n)%Z -> Z.to_nat k <= 2 ^ n.
Proof. by move=> h; apply/ltnW/isword_tonatZP. Qed.

(* -------------------------------------------------------------------- *)
Lemma iswordZP (k : Z) :
  reflect (0 <= k < modulus n)%Z (isword k).
Proof.
by apply: (iffP idP); rewrite !(rwP ltzP, rwP lezP) (rwP andP).
Qed.

(* -------------------------------------------------------------------- *)
Lemma isword0 : isword 0%Z.
Proof.
rewrite lerr /= modulusE; elim: n => [|k ih].
+ by rewrite expr0 ltr01. + by rewrite exprS mulr_gt0.
Qed.

Definition word0 := mkWord isword0.

(* -------------------------------------------------------------------- *)
Lemma isword_word (w : n.-word) : isword (w : Z).
Proof. by apply/(valP w). Qed.

Hint Resolve 0 isword_word.

(* -------------------------------------------------------------------- *)
Lemma word_eqE (w1 w2 : n.-word) :
  (w1 == w2) = (urepr w1 == urepr w2)%Z.
Proof. by rewrite -val_eqE. Qed.

(* -------------------------------------------------------------------- *)
Definition add_word (w1 w2 : n.-word) :=
  mkword (urepr w1 + urepr w2)%Z.

Definition sub_word (w1 w2 : n.-word) :=
  mkword (urepr w2 - urepr w2)%Z.

Definition opp_word (w : n.-word) :=
  mkword (- urepr w)%Z.

(* -------------------------------------------------------------------- *)
Lemma isword_geZ0 (w : Z) : isword w -> (0 <= w)%Z.
Proof. by case/andP=> [/lezP]. Qed.

Hint Extern 0 (0 <= _)%Z => by apply/isword_geZ0; assumption.

Lemma word_geZ0 (w : n.-word) : (0 <= w)%Z.
Proof. by apply/isword_geZ0. Qed.

Hint Resolve 0 word_geZ0.

(* -------------------------------------------------------------------- *)
Notation mword n := 'I_(2^n).-1.+1.

Definition zmod_of_word (w : n.-word) : mword n :=
  inZp (Z.to_nat w).

Definition word_of_zmod (w : mword n) : n.-word :=
  mkword (Z.of_nat w).

(* -------------------------------------------------------------------- *)
Lemma zmod_of_wordK : cancel zmod_of_word word_of_zmod.
Proof.
rewrite /zmod_of_word /word_of_zmod => -[w /= h].
rewrite (rwP eqP) -val_eqE /= modn_small.
+ rewrite prednK_modulus -(rwP ltP) Nat2Z.inj_lt.
  rewrite Z2Nat.id //; case/andP: h => _ /ltzP.
  by rewrite /modulus two_power_nat_equiv Nat2Z.n2zX expZE.
+ rewrite Z2Nat.id; first by case/andP: h => /lezP.
  by rewrite Zmod_small // !(rwP lezP, rwP ltzP) (rwP andP).
Qed.

(* -------------------------------------------------------------------- *)
Lemma word_of_zmodK : cancel word_of_zmod zmod_of_word.
Proof.
rewrite /zmod_of_word /word_of_zmod => -[k /= lt].
apply/eqP; rewrite -val_eqE /= prednK_modulus.
rewrite prednK_modulus in lt; rewrite Zmod_small.
+ by apply/isword_ofnatZP.
+ by rewrite modn_small Nat2Z.id.
Qed.

(* -------------------------------------------------------------------- *)
Lemma word0_zmodE : word0 = word_of_zmod 0%R.
Proof. by rewrite (rwP eqP) word_eqE. Qed.

(* -------------------------------------------------------------------- *)
Lemma add_word_zmodE (x y : n.-word) :
  add_word x y = word_of_zmod (zmod_of_word x + zmod_of_word y)%R.
Proof.
rewrite (rwP eqP) word_eqE /=; case: x y => [x hx] [y hy].
rewrite /add_word /urepr /= prednK_modulus; apply/eqP.
rewrite [Z.to_nat x %% _]modn_small 1?[Z.to_nat y %% _]modn_small.
+ by apply/isword_tonatZP/iswordZP.
+ by apply/isword_tonatZP/iswordZP.
rewrite modnZE ?expn_eq0 // -Zofnat_modulus.
by rewrite Zmod_mod Nat2Z.n2zD !Z2Nat.id.
Qed.

(* -------------------------------------------------------------------- *)
Lemma opp_word_zmodE (x : n.-word) :
  opp_word x = word_of_zmod (- zmod_of_word x)%R.
Proof.
rewrite (rwP eqP) word_eqE /=; case: x => [x hx].
rewrite /opp_word /urepr /= prednK_modulus; apply/eqP.
rewrite modnZE ?expn_eq0 // -Zofnat_modulus Zmod_mod.
rewrite modn_small; first by apply/isword_tonatZP/iswordZP.
rewrite Nat2Z.n2zB ?isword_tonatZWP //; first by apply/iswordZP.
rewrite Z2Nat.id // -subZE -Zofnat_modulus Zminus_mod.
rewrite Z_mod_same_full Z.sub_0_l [(x mod _)%Z]Zmod_small //.
by apply/iswordZP.
Qed.

(* -------------------------------------------------------------------- *)
Definition word_zmodE := (word0_zmodE, add_word_zmodE, opp_word_zmodE).

(* -------------------------------------------------------------------- *)
Lemma add_wordC : commutative add_word.
Proof. by move=> x y; rewrite !word_zmodE addrC. Qed.

Lemma add_wordA : associative add_word.
Proof. by move=> x y z; rewrite !word_zmodE !word_of_zmodK addrA. Qed.

Lemma add_word0w : left_id word0 add_word.
Proof.
by move=> x; rewrite !word_zmodE !word_of_zmodK add0r zmod_of_wordK.
Qed.

Lemma add_wordNw : left_inverse word0 opp_word add_word.
Proof.
by move=> x; rewrite !word_zmodE @word_of_zmodK addNr.
Qed.

Definition word_zmodMixin :=
  ZmodMixin add_wordA add_wordC add_word0w add_wordNw.

Canonical word_zmodType :=
  Eval hnf in ZmodType n.-word word_zmodMixin.

(* -------------------------------------------------------------------- *)
Notation wbits := (n.-tuple bool).

Definition wbit (w : n.-word) (n : nat) : bool :=
  Z.testbit w (Z.of_nat n).

Lemma wbitE w k : wbit w k = odd (Z.to_nat w %/ (2 ^ k)).
Proof.
have ->: Z.to_nat w %/ (2 ^ k) = Z.to_nat (w / (2 ^ k)).
+ rewrite int_of_Z_PoszE; apply/Nat2Z.inj; rewrite Z2Nat.id.
  * by apply/Z.div_pos => //; apply/Z.pow_pos_nonneg/Nat2Z.is_nonneg.
  by rewrite divnZE ?expn_eq0 // Z2Nat.id // Nat2Z.n2zX expZE.
rewrite /wbit Z.testbit_odd Z.shiftr_div_pow2.
+ by apply/Nat2Z.is_nonneg.
rewrite int_of_Z_PoszE oddZE // divZE.
+ by apply/ltzP/Z.pow_pos_nonneg/Nat2Z.is_nonneg.
+ apply/lezP/leZE; rewrite int_to_ZK /= divz_ge0.
  * by apply/(@ltZE 0)/Z.pow_pos_nonneg/Nat2Z.is_nonneg.
  * by apply/(@leZE 0).
Qed.

Definition w2t (w : n.-word) : wbits :=
  [tuple wbit w k | k < n].

Definition t2w_def (t : wbits) : Z :=
  (\sum_(i < n) 2%:R^+i * (tnth t i)%:R)%R.

Lemma le2Xn_sumbits k (F : nat -> bool) :
  \sum_(i < k) 2 ^ i * F i < 2 ^ k.
Proof.
elim: k => [|k ih]; [by rewrite big_ord0 | rewrite big_ord_recr /=].
rewrite expnS mul2n -addnn -addSn leq_add //.
by rewrite -[X in _ <= X]muln1 leq_mul2l leq_b1 orbT.
Qed.

Local Lemma ge0_bit k b : (0 <= 2%:R ^+ k * b%:R :> Z)%R.
Proof. by rewrite mulr_ge0 // ?exprn_ge0 // ler0n. Qed.

Local Lemma t2w_proof (t : wbits) : isword (t2w_def t).
Proof.
rewrite /t2w_def sumr_ge0 /= => [i _|]; first by rewrite ge0_bit.
rewrite /t2w_def modulusE; elim: n t => [|l ih] t.
  by rewrite big_ord0 ltr01.
rewrite big_ord_recr /= exprS mulr_natl [_ ^+ _ *+ 2]mulr2n.
apply/ltr_le_add/ler_pimulr; first last.
+ by rewrite lern1 leq_b1. + by rewrite exprn_ge0.
pose u := [tuple nth false t i | i < l].
rewrite (eq_bigr (fun i : 'I_l => 2%:R ^+ i * (tnth u i)%:R)%R) //.
by move=> i _; rewrite tnth_map (tnth_nth false) tnth_ord_tuple.
Qed.

Definition t2w (t : wbits) : n.-word := mkWord (t2w_proof t).

(* -------------------------------------------------------------------- *)
Lemma Ztonat_bit k b :
  Z.to_nat (2%:R ^+ k * b%:R) = (2 ^ k * b)%nat.
Proof.
rewrite Z2Nat.z2nM ?multE ?(rwP leZP) ?(exprn_ge0,ler0n) //.
by rewrite Z2Nat.z2nX // !Z2Nat.z2nr.
Qed.

(* -------------------------------------------------------------------- *)
Lemma Ztonat_t2w w :
  Z.to_nat (t2w_def w) = \sum_(i < n) 2 ^ i * tnth w i.
Proof.
rewrite /t2w_def Z2Nat.z2n_sum => /= [i _|]; first by apply/ge0_bit.
by apply/eq_bigr=> i _; rewrite Ztonat_bit.
Qed.

(* -------------------------------------------------------------------- *)
Lemma t2wK : cancel t2w w2t.
Proof.
move=> w; apply/eq_from_tnth => k; rewrite /w2t /t2w.
rewrite tnth_map tnth_ord_tuple wbitE /t2w_def /=.
rewrite Ztonat_t2w; pose F i := 2 ^ i * nth false w i.
rewrite (eq_bigr (F \o val)); first by move=> i; rewrite (tnth_nth false).
rewrite (bigD1 k) //= -(big_mkord [pred i | i != val k]).
rewrite divnDl ?dvdn_mulr // [F k]/F mulKn ?expn_gt0 //.
rewrite odd_add -tnth_nth oddb (bigID [pred i| i < k]) /=.
rewrite divnDr ?dvdn_sum // 1?divn_small; first move=> i /andP[_ ge_in].
+ by rewrite dvdn_mulr // dvdn_exp2l // leqNgt.
+ rewrite (eq_bigl (fun i => i < k)) ?big_mkord.
  * move=> i /=; rewrite andbC andb_idr //.
    by move=> /gtn_eqF /negbT; rewrite eq_sym.
  by rewrite -big_ord_widen ?[k <= _]ltnW ?le2Xn_sumbits.
rewrite add0n (eq_bigl (fun i => k < i)).
+ by move=> i /=; rewrite -leqNgt ltn_neqAle eq_sym.
rewrite (eq_bigr (fun i => 2 ^ k * (2 ^ (i - k) * nth false w i))).
+ by move=> i lt_ni; rewrite mulnA -expnD subnKC 1?ltnW.
rewrite -big_distrr /= mulKn ?expn_gt0 //.
rewrite (big_morph odd odd_add (erefl _)) big1 ?addbF //.
by move=> i lt_ni; rewrite -(subnSK lt_ni) expnS -mulnA odd_mul.
Qed.

End WordRing.

(* -------------------------------------------------------------------- *)
Section WordBits.
Context (n : nat).

Notation isword z := (0 <= z < modulus n)%R.

Lemma wand_subproof (w1 w2 : n.-word) : isword (Z.land w1 w2).
Proof. Admitted.

Lemma wor_subproof (w1 w2 : n.-word) : isword (Z.lor w1 w2).
Proof. Admitted.

Definition wand (w1 w2 : n.-word) := mkWord (wand_subproof w1 w2).
Definition wor  (w1 w2 : n.-word) := mkWord (wor_subproof  w1 w2).

End WordBits.
