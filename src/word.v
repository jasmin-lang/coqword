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
Lemma kwordK (z : Z) : urepr (mkword z) = (z mod modulus n)%Z.
Proof. by []. Qed.

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
+ rewrite prednK ?expn_gt0 // -(rwP ltP) Nat2Z.inj_lt.
  rewrite Z2Nat.id //; case/andP: h => _ /ltzP.
  by rewrite /modulus two_power_nat_equiv Nat2Z.n2zX expZE.
+ rewrite Z2Nat.id; first by case/andP: h => /lezP.
  by rewrite Zmod_small // !(rwP lezP, rwP ltzP) (rwP andP).
Qed.

(* -------------------------------------------------------------------- *)
Notation wbits := (n.-tuple bool).

Definition wbit (w : n.-word) (n : nat) : bool :=
  Z.testbit w (Z.of_nat n).

Lemma wbitE w k : wbit w k = odd (Z.to_nat w %/ (2 ^ k)).
Proof.
case: w => -[] // => [|p] h; rewrite /wbit {h}/=.
+ by rewrite div0n /= Z.testbit_0_l.
apply/esym; elim: k p => [|k ih] [p|p|] //=.
+ by rewrite expn0 divn1 Pos2Nat.inj_xI mulP /= mul2n odd_double.
+ by rewrite expn0 divn1 Pos2Nat.inj_xO mulP mul2n odd_double.
+ admit.
+ admit.
+ admit.
Admitted.

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
