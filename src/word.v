(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
(* ------- *) Require Import Arith ZArith Omega ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope ring_scope.

Import GRing.Theory.

(* -------------------------------------------------------------------- *)
Parameter (nbits : nat).

Definition modulus := two_power_nat nbits.

(* -------------------------------------------------------------------- *)
Record word := mkWord {
  toword :> Z; _ : (0 <= toword) && (toword < modulus);
}.

Canonical word_subType := Eval hnf in [subType for toword].
Definition word_eqMixin := Eval hnf in [eqMixin of word by <:].
Canonical word_eqType := Eval hnf in EqType word word_eqMixin.
