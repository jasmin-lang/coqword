(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra zmodp.
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
Section WordBaseTheory.
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
(* FIXME: notation? *)
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

(* -------------------------------------------------------------------- *)
Lemma word_eqE (w1 w2 : n.-word) :
  (w1 == w2) = (urepr w1 == urepr w2)%Z.
Proof. by rewrite -val_eqE. Qed.

(* -------------------------------------------------------------------- *)
Lemma isword_geZ0 (w : Z) : isword w -> (0 <= w)%Z.
Proof. by case/andP=> [/lezP]. Qed.

Lemma word_geZ0 (w : n.-word) : (0 <= w)%Z.
Proof. by apply/isword_geZ0/isword_word. Qed.

(* -------------------------------------------------------------------- *)
Definition wsize (w : n.-word) := n.
End WordBaseTheory.

(* -------------------------------------------------------------------- *)
Hint Resolve 0 isword_word.
Hint Extern  0 (0 <= _)%Z => by apply/isword_geZ0; eassumption.
Hint Resolve 0 word_geZ0.

Arguments word0 [n].

(* ==================================================================== *)
Section WordZmod.
Context (n : nat).

Notation mkword := (@mkword n).

(* -------------------------------------------------------------------- *)
Definition add_word (w1 w2 : n.-word) :=
  mkword (urepr w1 + urepr w2)%Z.

Definition sub_word (w1 w2 : n.-word) :=
  mkword (urepr w2 - urepr w2)%Z.

Definition opp_word (w : n.-word) :=
  mkword (- urepr w)%Z.

Definition mul_word (w1 w2 : n.-word) :=
  mkword (urepr w1 * urepr w2).

(* -------------------------------------------------------------------- *)
Notation mword n := 'I_(2^n).-1.+1.

Definition ord_of_word (w : n.-word) : mword n :=
  inZp (Z.to_nat w).

Definition word_of_ord (w : mword n) : n.-word :=
  mkword (Z.of_nat w).

(* -------------------------------------------------------------------- *)
Lemma ord_of_wordK : cancel ord_of_word word_of_ord.
Proof.
rewrite /ord_of_word /word_of_ord => -[w /= h].
rewrite (rwP eqP) -val_eqE /= modn_small.
+ rewrite prednK_modulus -(rwP ltP) Nat2Z.inj_lt.
  rewrite Z2Nat.id //; case/andP: h => _ /ltzP.
  by rewrite /modulus two_power_nat_equiv Nat2Z.n2zX expZE.
+ rewrite Z2Nat.id; first by case/andP: h => /lezP.
  by rewrite Zmod_small // !(rwP lezP, rwP ltzP) (rwP andP).
Qed.

(* -------------------------------------------------------------------- *)
Lemma word_of_ordK : cancel word_of_ord ord_of_word.
Proof.
rewrite /ord_of_word /word_of_ord => -[k /= lt].
apply/eqP; rewrite -val_eqE /= prednK_modulus.
rewrite prednK_modulus in lt; rewrite Zmod_small.
+ by apply/isword_ofnatZP.
+ by rewrite modn_small Nat2Z.id.
Qed.

(* -------------------------------------------------------------------- *)
Lemma word0_ordE : word0 = word_of_ord 0%R.
Proof. by rewrite (rwP eqP) word_eqE. Qed.

(* -------------------------------------------------------------------- *)
Lemma add_word_ordE (x y : n.-word) :
  add_word x y = word_of_ord (ord_of_word x + ord_of_word y)%R.
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
Lemma opp_word_ordE (x : n.-word) :
  opp_word x = word_of_ord (- ord_of_word x)%R.
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
Definition word_ordE := (word0_ordE, add_word_ordE, opp_word_ordE).

(* -------------------------------------------------------------------- *)
Lemma addwC : commutative add_word.
Proof. by move=> x y; rewrite !word_ordE addrC. Qed.

Lemma addwA : associative add_word.
Proof. by move=> x y z; rewrite !word_ordE !word_of_ordK addrA. Qed.

Lemma add0w : left_id word0 add_word.
Proof.
by move=> x; rewrite !word_ordE !word_of_ordK add0r ord_of_wordK.
Qed.

Lemma addNw : left_inverse word0 opp_word add_word.
Proof.
by move=> x; rewrite !word_ordE @word_of_ordK addNr.
Qed.

Definition word_ordMixin :=
  ZmodMixin addwA addwC add0w addNw.

Canonical word_ordType :=
  Eval hnf in ZmodType n.-word word_ordMixin.

(* -------------------------------------------------------------------- *)
Lemma ord_of_word_is_additive : additive ord_of_word.
Proof.
move=> /= x y; rewrite [in LHS]/GRing.add [in LHS]/GRing.opp /=.
by rewrite !word_ordE /= !word_of_ordK.
Qed.

Canonical ord_of_word_additive :=
  Additive ord_of_word_is_additive.

Canonical word_of_ord_additive :=
  Additive (can2_additive ord_of_wordK word_of_ordK).
End WordZmod.

(* ==================================================================== *)
Section WordRing.
Context (n : nat).

(* -------------------------------------------------------------------- *)
Notation isword z := (0 <= z < modulus n.+1)%R.

(* -------------------------------------------------------------------- *)
Notation mword n := 'Z_(2^n).

Lemma word_Fcast : (2^n.+1).-1.+1 = (Zp_trunc (2^n.+1)).+2.
Proof.
rewrite prednK_modulus Zp_cast // expnS.
by rewrite leq_pmulr // expn_gt0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma isword1 : isword 1%Z.
Proof.
rewrite ler01 /= modulusE exprS (@ltr_le_trans _ 2%:R) //.
by rewrite ler_pmulr // exprn_ege1.
Qed.

Definition word1 := mkWord isword1.

(* -------------------------------------------------------------------- *)
Definition zmod_of_word (w : n.+1.-word) : mword n.+1 :=
  cast_ord word_Fcast (ord_of_word w).

Definition word_of_zmod (w : mword n.+1) : n.+1.-word :=
  word_of_ord (cast_ord (esym word_Fcast) w).

(* -------------------------------------------------------------------- *)
Lemma zmod_of_wordK : cancel zmod_of_word word_of_zmod.
Proof.
move=> w; rewrite /zmod_of_word /word_of_zmod.
by rewrite cast_ordK ord_of_wordK.
Qed.

(* -------------------------------------------------------------------- *)
Lemma word_of_zmodK : cancel word_of_zmod zmod_of_word.
Proof.
move=> w; rewrite /zmod_of_word /word_of_zmod.
by rewrite word_of_ordK cast_ordKV.
Qed.

(* -------------------------------------------------------------------- *)
Lemma zmod_of_word_is_additive : additive zmod_of_word.
Proof.
move=> /= x y; rewrite {1}/zmod_of_word raddfB /=.
by apply/eqP; rewrite -val_eqE /= -word_Fcast.
Qed.

Canonical zmod_of_word_additive :=
  Additive zmod_of_word_is_additive.

Canonical word_of_zmod_additive :=
  Additive (can2_additive zmod_of_wordK word_of_zmodK).

(* -------------------------------------------------------------------- *)
Lemma word0_zmodE : word0 = word_of_zmod 0%R.
Proof. by rewrite word0_ordE. Qed.

(* -------------------------------------------------------------------- *)
Lemma word1_zmodE : word1 = word_of_zmod 1%R.
Proof. by rewrite (rwP eqP) -val_eqE /= Zmod_small. Qed.

(* -------------------------------------------------------------------- *)
Lemma add_word_zmodE (x y : n.+1.-word) :
  add_word x y = word_of_zmod (zmod_of_word x + zmod_of_word y)%R.
Proof.
rewrite add_word_ordE /word_of_zmod; congr word_of_ord.
by apply/eqP; rewrite -val_eqE /= word_Fcast.
Qed.

(* -------------------------------------------------------------------- *)
Lemma opp_word_zmodE (x : n.+1.-word) :
  opp_word x = word_of_zmod (- zmod_of_word x)%R.
Proof.
rewrite opp_word_ordE /word_of_zmod; congr word_of_ord.
by apply/eqP; rewrite -val_eqE /= word_Fcast.
Qed.

(* -------------------------------------------------------------------- *)
Lemma mul_word_zmodE (x y : n.+1.-word) :
  mul_word x y = word_of_zmod (zmod_of_word x * zmod_of_word y)%R.
Proof.
rewrite (rwP eqP) word_eqE /=; case: x y => [x hx] [y hy].
rewrite /mul_word /urepr /= prednK_modulus; apply/eqP.
rewrite [Z.to_nat x %% _]modn_small 1?[Z.to_nat y %% _]modn_small.
+ by apply/isword_tonatZP/iswordZP.
+ by apply/isword_tonatZP/iswordZP.
rewrite -word_Fcast prednK_modulus modnZE ?expn_eq0 //.
by rewrite -Zofnat_modulus Zmod_mod Nat2Z.n2zM !Z2Nat.id.
Qed.

(* -------------------------------------------------------------------- *)
Definition word_zmodE :=
  (word0_zmodE, word1_zmodE, add_word_zmodE, opp_word_zmodE, mul_word_zmodE).

(* -------------------------------------------------------------------- *)
Lemma mulwC : commutative (@mul_word n.+1).
Proof. by move=> x y; rewrite !word_zmodE mulrC. Qed.

Lemma mulwA : associative (@mul_word n.+1).
Proof. by move=> x y z; rewrite !word_zmodE !word_of_zmodK mulrA. Qed.

Lemma mul1w : left_id word1 (@mul_word n.+1).
Proof.
by move=> x; rewrite !word_zmodE !word_of_zmodK mul1r zmod_of_wordK.
Qed.

Lemma mulwDl : left_distributive (@mul_word n.+1) +%R.
Proof.
by move=> x w1 w2; rewrite !word_zmodE raddfD /= mulrDl [LHS]raddfD.
Qed.

Lemma onew_neq0 : word1 != 0%R.
Proof. by rewrite -val_eqE. Qed.

(* -------------------------------------------------------------------- *)
Definition word_ringMixin :=
  ComRingMixin mulwA mulwC mul1w mulwDl onew_neq0.

Canonical word_ringType :=
  Eval hnf in RingType n.+1.-word word_ringMixin.
Canonical word_comRingType :=
  Eval hnf in ComRingType n.+1.-word mulwC.

(* -------------------------------------------------------------------- *)
Lemma zmod_of_word_is_rmorphism : rmorphism zmod_of_word.
Proof.
split; first by apply/zmod_of_word_is_additive.
split=> /= [x y|]; rewrite ?[in LHS]/GRing.mul ?[in LHS]/GRing.one /=.
+ by rewrite !word_zmodE /= !word_of_zmodK.
+ by rewrite !word_zmodE /= !word_of_zmodK.
Qed.

Canonical zmod_of_word_rmorphism :=
  RMorphism zmod_of_word_is_rmorphism.

Canonical word_of_zmod_rmorphism :=
  RMorphism (can2_rmorphism zmod_of_wordK word_of_zmodK).
End WordRing.

(* ==================================================================== *)
Section WordBits.
Context (n : nat).

(* -------------------------------------------------------------------- *)
Notation isword z := (0 <= z < modulus n)%R.

(* -------------------------------------------------------------------- *)
Notation wbits := (n.-tuple bool).

Lemma le2Xn_sumbits k (F : nat -> bool) :
  \sum_(i < k) 2 ^ i * F i < 2 ^ k.
Proof.
elim: k => [|k ih]; [by rewrite big_ord0 | rewrite big_ord_recr /=].
rewrite expnS mul2n -addnn -addSn leq_add //.
by rewrite -[X in _ <= X]muln1 leq_mul2l leq_b1 orbT.
Qed.

Lemma le2Xn_sumbitsZ k (F : nat -> bool) :
  (\sum_(i < k) 2%:R ^ i * (F i)%:R < 2%:R ^+ k :> Z)%R.
Proof.
elim: k => [|k ih]; [by rewrite big_ord0 | rewrite big_ord_recr /=].
rewrite exprS mulr_natl [X in (_ < X)%R]mulr2n ltr_le_add //.
by case: (F k); rewrite !Monoid.simpm // exprn_ge0.
Qed.

Local Lemma ge0_bit k b : (0 <= 2%:R ^+ k * b%:R :> Z)%R.
Proof. by rewrite mulr_ge0 // ?exprn_ge0 // ler0n. Qed.

Definition wbit (z : Z) (n : nat) : bool :=
  nosimpl (Z.testbit z (Z.of_nat n)).

Lemma wbitE (z : Z) k :
  (0 <= z)%R -> wbit z k = odd (Z.to_nat z %/ (2 ^ k)).
Proof.
move=> ge0_z; have ->: Z.to_nat z %/ (2 ^ k) = Z.to_nat (z / (2 ^ k)).
+ rewrite int_of_Z_PoszE; apply/Nat2Z.inj; rewrite Z2Nat.id.
  * apply/Z.div_pos; first by apply/leZP.
    by apply/Z.pow_pos_nonneg/Nat2Z.is_nonneg.
  rewrite divnZE ?expn_eq0 // Z2Nat.id ?(rwP (leZP _ _)) //.
  by rewrite Nat2Z.n2zX expZE.
rewrite /wbit Z.testbit_odd Z.shiftr_div_pow2.
+ by apply/Nat2Z.is_nonneg.
rewrite int_of_Z_PoszE oddZE // divZE.
+ by apply/ltzP/Z.pow_pos_nonneg/Nat2Z.is_nonneg.
+ apply/lezP/leZE; rewrite int_to_ZK /= divz_ge0.
  * by apply/(@ltZE 0)/Z.pow_pos_nonneg/Nat2Z.is_nonneg.
  * by apply/(@leZE 0)/leZP.
Qed.

Definition w2t (w : n.-word) : wbits :=
  [tuple wbit w k | k < n].

Definition t2w_def (t : wbits) : Z :=
  (\sum_(i < n) 2%:R^+i * (tnth t i)%:R)%R.

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
+ by apply/sumr_ge0 => i _; apply/ge0_bit.
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

(* -------------------------------------------------------------------- *)
Lemma wbit_word_ovf (w : n.-word) i : (i >= n) -> wbit w i = false.
Proof.
case: (w =P 0)%R => [->|]; first by rewrite /wbit Z.bits_0.
move=> /eqP nz_w le_ni; rewrite /wbit Z.bits_above_log2 //.
rewrite -Z.log2_lt_pow2; last first.
+ by rewrite Z.le_neq; split=> //; apply/eqP; rewrite eq_sym nz_w.
apply/ltzP/(@ltr_le_trans _ (2 ^ Z.of_nat n)%Z); last first.
+ by apply/lezP/Z.pow_le_mono_r/inj_le/leP.
by rewrite -two_power_nat_equiv; case/andP: (isword_word w).
Qed.

(* -------------------------------------------------------------------- *)
Lemma z2sumE (z : Z) :
     (0 <= z)%R
  -> (forall i, i >= n -> ~~ wbit z i)
  -> z = (\sum_(i < n) 2%:R ^+ i * (wbit z i)%:R)%R.
Proof.
rewrite /wbit; elim: n z => [|m ih] z ge0_z hbit.
+ rewrite big_ord0; apply/Z.bits_inj_0 => i; case: (ltrP i 0).
  * by move=> lt0_i; rewrite Z.testbit_neg_r // (rwP ltzP).
  by case/lezP/Z_of_nat_complete => k ->; apply/negbTE/hbit.
rewrite [LHS](Z_div_mod_eq _ 2) // -Z.bit0_mod {1}[(z/2)%Z]ih.
+ by apply/lezP/Z_div_pos/lezP.
+ move=> i le_mi; rewrite Z.div2_bits; first by apply/Zle_0_nat.
  by rewrite -Nat2Z.inj_succ hbit.
rewrite big_ord_recl expr0 mul1r addrC; congr +%R; last first.
+ by rewrite /= /Z.b2z; case: ifP.
rewrite mulZE mulr_sumr; apply/eq_bigr => i _.
rewrite exprS mulrA; congr *%R; rewrite Z.div2_bits.
+ by apply/Zle_0_nat. + by rewrite -Nat2Z.inj_succ.
Qed.

(* -------------------------------------------------------------------- *)
Lemma w2sumE (w : n.-word) :
  w = (\sum_(i < n) 2%:R ^+ i * (wbit w i)%:R)%R :> Z.
Proof.
apply/z2sumE => //; first by case/andP: (isword_word w).
by move=> i le_ni; rewrite wbit_word_ovf.
Qed.

(* -------------------------------------------------------------------- *)
Lemma eq_from_wbit (w1 w2 : n.-word) :
  reflect
    (forall i : 'I_n, wbit w1 i = wbit w2 i)
    (w1 == w2).
Proof.
apply: (iffP eqP) => [->//|heq]; apply/val_eqP => /=.
rewrite [_ w1]w2sumE [_ w2]w2sumE; apply/eqP/eq_bigr.
by move=> /= i _; rewrite heq.
Qed.

End WordBits.

(* ==================================================================== *)
Notation lsb w := (wbit (toword w) 0).
Notation msb w := (wbit (toword w) (wsize w).-1).

(* ==================================================================== *)
Section SignedRepr.
Context (n : nat).

Definition srepr (w : n.-word) :=
  (if msb w then (val w - modulus n.-1)%R else val w)%Z.
End SignedRepr.

(* ==================================================================== *)
Section Word0Extend.
Context (n : nat).

Lemma w0extend_subproof (p : nat) (w : n.-word) :
  (0 <= val w < modulus (n + p))%R.
Proof.
case/andP: (isword_word w) => -> h /=; rewrite modulusE.
rewrite exprD (ltr_le_trans h) // modulusE ler_pemulr //.
+ by apply/exprn_ge0. + by apply/exprn_ege1.
Qed.

Definition w0extend :=
  nosimpl (fun p w => mkWord (w0extend_subproof p w)).

Definition wbit_w0extend (p : nat) (w : n.-word) i :
  wbit (w0extend p w) i = if i < n then wbit w i else false.
Proof. by case: ifPn => //; rewrite -leqNgt; apply/wbit_word_ovf. Qed.
End Word0Extend.

(* -------------------------------------------------------------------- *)
Section WordLogicals.
Context (n : nat).

Notation isword z := (0 <= z < modulus n)%R.

(* -------------------------------------------------------------------- *)
Lemma wand_subproof (w1 w2 : n.-word) : isword (Z.land w1 w2).
Proof.
have h: (0 <= Z.land w1 w2)%R by apply/lezP/Z.land_nonneg; left.
apply/andP; split => //; rewrite [Z.land _ _](@z2sumE n)//.
+ move=> i le_ni; rewrite /wbit Z.land_spec.
  by rewrite -!/(wbit _ _) !wbit_word_ovf.
+ by rewrite modulusE le2Xn_sumbitsZ.
Qed.

Lemma wor_subproof (w1 w2 : n.-word) : isword (Z.lor w1 w2).
Proof.
have h: (0 <= Z.lor w1 w2)%R by apply/lezP/Z.lor_nonneg; split.
apply/andP; split => //; rewrite [Z.lor _ _](@z2sumE n)//.
+ move=> i le_ni; rewrite /wbit Z.lor_spec.
  by rewrite -!/(wbit _ _) !wbit_word_ovf.
+ by rewrite modulusE le2Xn_sumbitsZ.
Qed.

Lemma wxor_subproof (w1 w2 : n.-word) : isword (Z.lxor w1 w2).
Proof.
have h: (0 <= Z.lxor w1 w2)%R by apply/lezP/Z.lxor_nonneg; split.
apply/andP; split => //; rewrite [Z.lxor _ _](@z2sumE n)//.
+ move=> i le_ni; rewrite /wbit Z.lxor_spec.
  by rewrite -!/(wbit _ _) !wbit_word_ovf.
+ by rewrite modulusE le2Xn_sumbitsZ.
Qed.

Definition wand := nosimpl (fun w1 w2 => mkWord (wand_subproof w1 w2)).
Definition wor  := nosimpl (fun w1 w2 => mkWord (wor_subproof  w1 w2)).
Definition wxor := nosimpl (fun w1 w2 => mkWord (wxor_subproof w1 w2)).

(* -------------------------------------------------------------------- *)
Lemma wandE (w1 w2 : n.-word) i :
  wbit (wand w1 w2) i = wbit w1 i && wbit w2 i.
Proof. by apply/Z.land_spec. Qed.

Lemma worE (w1 w2 : n.-word) i :
  wbit (wor w1 w2) i = wbit w1 i || wbit w2 i.
Proof. by apply/Z.lor_spec. Qed.

Lemma wxorE (w1 w2 : n.-word) i :
  wbit (wxor w1 w2) i = wbit w1 i (+) wbit w2 i.
Proof. by rewrite /wbit Z.lxor_spec /=; do 2! case: Z.testbit. Qed.

End WordLogicals.

(* ==================================================================== *)
Section WordLogicalsTh.
Context (n : nat).

(* -------------------------------------------------------------------- *)
Lemma wand_w0extend (p : nat) (w1 w2 : n.-word) :
  w0extend p (wand w1 w2) = wand (w0extend p w1) (w0extend p w2).
Proof. by apply/eqP/eq_from_wbit => i. Qed.

(* -------------------------------------------------------------------- *)
Lemma wor_w0extend (p : nat) (w1 w2 : n.-word) :
  w0extend p (wor w1 w2) = wor (w0extend p w1) (w0extend p w2).
Proof. by apply/eqP/eq_from_wbit => i. Qed.

(* -------------------------------------------------------------------- *)
Lemma wxor_w0extend (p : nat) (w1 w2 : n.-word) :
  w0extend p (wxor w1 w2) = wxor (w0extend p w1) (w0extend p w2).
Proof. by apply/eqP/eq_from_wbit => i. Qed.
End WordLogicalsTh.
