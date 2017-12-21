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
Parameter (nbits : nat).

Definition modulus := two_power_nat nbits.

(* -------------------------------------------------------------------- *)
Lemma two_power_natE n : two_power_nat n = 2%:R ^+ n.
Proof. by elim: n => // n ih; rewrite two_power_nat_S exprS ih. Qed.

Lemma modulusE : modulus = 2%:R^+nbits.
Proof. by apply/two_power_natE. Qed.

(* -------------------------------------------------------------------- *)
Record word := mkWord {
  toword :> Z; _ : (0 <= toword)%R && (toword < modulus)%R;
}.

Canonical word_subType := Eval hnf in [subType for toword].
Definition word_eqMixin := Eval hnf in [eqMixin of word by <:].
Canonical word_eqType := Eval hnf in EqType word word_eqMixin.

(* -------------------------------------------------------------------- *)
Notation wbits := (nbits.-tuple bool).

Definition wbit (w : word) (n : nat) : bool :=
  odd (Z.to_nat w %/ (2 ^ n)).

Definition w2t (w : word) : wbits :=
  [tuple wbit w n | n < nbits].

Definition t2w_def (t : wbits) : Z :=
  (\sum_(i < nbits) 2%:R^+i * (tnth t i)%:R)%R.

Lemma le2Xn_sumbits n (F : nat -> bool) :
  \sum_(i < n) 2 ^ i * F i < 2 ^ n.
Proof.
elim: n => [|n ih]; [by rewrite big_ord0 | rewrite big_ord_recr /=].
rewrite expnS mul2n -addnn -addSn leq_add //.
by rewrite -[X in _ <= X]muln1 leq_mul2l leq_b1 orbT.
Qed.

Local Lemma ge0_bit n b : (0 <= 2%:R ^+ n * b%:R :> Z)%R.
Proof. by rewrite mulr_ge0 // ?exprn_ge0 // ler0n. Qed.

Local Lemma t2w_proof (t : wbits) :
  (0 <= t2w_def t)%R && (t2w_def t < modulus)%R.
Proof.
(* FIXME: use le2Xn_sumbits *)
rewrite /t2w_def sumr_ge0 /= => [i _|]; first by rewrite ge0_bit.
rewrite /t2w_def modulusE; elim: nbits t => [|n ih] t.
  by rewrite big_ord0 ltr01.
rewrite big_ord_recr /= exprS mulr_natl [_ ^+ _ *+ 2]mulr2n.
apply/ltr_le_add/ler_pimulr; first last.
+ by rewrite lern1 leq_b1. + by rewrite exprn_ge0.
pose u := [tuple nth false t i | i < n].
rewrite (eq_bigr (fun i : 'I_n => 2%:R ^+ i * (tnth u i)%:R)%R) //.
by move=> i _; rewrite tnth_map (tnth_nth false) tnth_ord_tuple.
Qed.

Definition t2w (t : wbits) : word := mkWord (t2w_proof t).

(* -------------------------------------------------------------------- *)
Lemma Ztonat_bit n b :
  Z.to_nat (2%:R ^+ n * b%:R) = (2 ^ n * b)%nat.
Proof.
rewrite Z2Nat.z2nM ?multE ?(rwP leZP) ?(exprn_ge0,ler0n) //.
by rewrite Z2Nat.z2nX // !Z2Nat.z2nr.
Qed.

(* -------------------------------------------------------------------- *)
Lemma Ztonat_t2w w :
  Z.to_nat (t2w_def w) = \sum_(i < nbits) 2 ^ i * tnth w i.
Proof.
rewrite /t2w_def Z2Nat.z2n_sum => /= [i _|]; first by apply/ge0_bit.
by apply/eq_bigr=> i _; rewrite Ztonat_bit.
Qed.

(* -------------------------------------------------------------------- *)
Lemma t2wK : cancel t2w w2t.
Proof.
move=> w; apply/eq_from_tnth => n; rewrite /w2t /t2w.
rewrite tnth_map tnth_ord_tuple /wbit /t2w_def /=.
rewrite Ztonat_t2w; pose F i := 2 ^ i * nth false w i.
rewrite (eq_bigr (F \o val)); first by move=> i; rewrite (tnth_nth false).
rewrite (bigD1 n) //= -(big_mkord [pred i | i != val n]).
rewrite divnDl ?dvdn_mulr // [F n]/F mulKn ?expn_gt0 //.
rewrite odd_add -tnth_nth oddb (bigID [pred i| i < n]) /=.
rewrite divnDr ?dvdn_sum // 1?divn_small; first move=> i /andP[_ ge_in].
+ by rewrite dvdn_mulr // dvdn_exp2l // leqNgt.
+ rewrite (eq_bigl (fun i => i < n)) ?big_mkord.
  * move=> i /=; rewrite andbC andb_idr //.
    by move=> /gtn_eqF /negbT; rewrite eq_sym.
  by rewrite -big_ord_widen ?[n <= _]ltnW ?le2Xn_sumbits.
rewrite add0n (eq_bigl (fun i => n < i)).
+ by move=> i /=; rewrite -leqNgt ltn_neqAle eq_sym.
rewrite (eq_bigr (fun i => 2 ^ n * (2 ^ (i - n) * nth false w i))).
+ by move=> i lt_ni; rewrite mulnA -expnD subnKC 1?ltnW.
rewrite -big_distrr /= mulKn ?expn_gt0 //.
rewrite (big_morph odd odd_add (erefl _)) big1 ?addbF //.
by move=> i lt_ni; rewrite -(subnSK lt_ni) expnS -mulnA odd_mul.
Qed.
