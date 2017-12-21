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
Lemma two_power_natE n : two_power_nat n = 2%:R^+n.
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

Local Lemma ge0_bit n b : (0 <= 2%:R ^+ n * b%:R :> Z)%R.
Proof. by rewrite mulr_ge0 // ?exprn_ge0 // ler0n. Qed.

Local Lemma t2w_proof (t : wbits) :
  (0 <= t2w_def t)%R && (t2w_def t < modulus)%R.
Proof.
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



