(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra zmodp.
(* ------- *) Require Import Arith ZArith Omega ssrZ.
Require Psatz.

Ltac elim_div :=
   unfold Z.div, Zmod;
     match goal with
       |  H : context[ Z.div_eucl ?X ?Y ] |-  _ =>
          generalize (Z_div_mod_full X Y) ; destruct (Z.div_eucl X Y)
       |  |-  context[ Z.div_eucl ?X ?Y ] =>
          generalize (Z_div_mod_full X Y) ; destruct (Z.div_eucl X Y)
     end; unfold Remainder.

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

Lemma modulusZE : modulus = (2 ^ nbits)%Z.
Proof. by rewrite /modulus two_power_nat_equiv. Qed.

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
Lemma modulus0 : modulus 0 = 1.
Proof. by rewrite modulusE expr0. Qed.

(* -------------------------------------------------------------------- *)
Lemma modulusS n : modulus n.+1 = (modulus n *+ 2)%R.
Proof. by rewrite [in LHS]modulusE exprS mulr_natl -modulusE. Qed.

(* -------------------------------------------------------------------- *)
Lemma modulusD n p : modulus (n + p) = (modulus n * modulus p)%R.
Proof. by rewrite !modulusE exprD. Qed.

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
Lemma urepr_word (w : n.-word) : urepr w = w :> Z.
Proof. by []. Qed.

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
Lemma mkword_valK (z : Z) : mkword z = (z mod modulus n)%Z :> Z.
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
Lemma word_eqP (w1 w2 : n.-word) :
  reflect (w1 = w2) (toword w1 == toword w2).
Proof. exact/val_eqP. Qed.

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
Lemma mkword_val_small {n : nat} (z : Z) :
  (0 <= z < 2%:R ^+ n.+1)%R -> mkword n.+1 z = z :> Z.
Proof.
move=> rg; rewrite /= Zmod_small // modulusE.
by rewrite !(rwP lezP, rwP ltzP) (rwP andP).
Qed.

Lemma mkword_val0 {n : nat} : mkword n.+1 0 = 0%Z :> Z.
Proof. by rewrite mkword_val_small ?lerr //= exprn_gt0. Qed.

Lemma mkword_val1 {n : nat} : mkword n.+1 1 = 1%Z :> Z.
Proof.
rewrite mkword_val_small // (@ltr_le_trans _ 2%:R) //.
by rewrite exprS ler_pemulr // exprn_ege1.
Qed.

(* ==================================================================== *)
Lemma mkword0E {n : nat} : mkword n 0 = 0%R :> word n.
Proof. by apply/val_eqP. Qed.

Lemma mkword1E {n : nat} : mkword n.+1 1 = 1%R :> word n.+1.
Proof. by apply/word_eqP; rewrite mkword_val1. Qed.

(* ==================================================================== *)
Lemma mkwordN1E {n : nat} : mkword n.+1 (-1)%Z = -1%R :> word n.+1.
Proof. by apply/val_eqP. Qed.

(* ==================================================================== *)
Lemma addwE {n} (w1 w2 : n.-word) :
  urepr (w1 + w2)%R = ((urepr w1 + urepr w2)%R mod modulus n)%Z.
Proof. by []. Qed.

Lemma subwE {n} (w1 w2 : n.-word) :
  urepr (w1 - w2)%R = ((urepr w1 - urepr w2)%R mod modulus n)%Z.
Proof.
rewrite addwE {1}/GRing.opp /= /opp_word mkwordK.
by rewrite -!(addZE, oppZE) Zplus_mod_idemp_r.
Qed.

Lemma subw_modE {n} (w1 w2 : n.-word) :
  (urepr (w1 - w2)%R =
    urepr w1 - urepr w2 + (modulus n) *+ (urepr w1 < urepr w2)%R)%R.
Proof.
case: (w2 =P 0%R) => [->|/eqP nz_w2].
+ by rewrite !subr0 ltrNge urepr_ge0 addr0.
have /= {nz_w2} gt0_w2: (0%R < val w2)%R.
+ rewrite ltr_neqAle urepr_ge0 andbT eq_sym.
  apply/contra_neq: nz_w2; pose z : n.-word := 0%R.
  by rewrite [X in val _ = X](_ : _ = val z) // => /val_inj.
rewrite /GRing.opp /GRing.add /= /add_word /opp_word /urepr /=.
rewrite Zplus_mod_idemp_r !(oppZE, addZE).
case: ltrP; rewrite (addr0, mulr1n); last first.
+ move=> le_w2_w1; rewrite Z.mod_small //; split.
  * by rewrite (rwP lezP) subr_ge0.
  * rewrite (rwP ltzP) ltr_subl_addr.
    by rewrite (ltr_trans (urepr_ltmod _)) ?ltr_addl.
+ move=> lt_w1_w2; rewrite -(@Z_mod_plus_full _ 1) Z.mul_1_l.
  rewrite Z.mod_small //; rewrite !(rwP lezP, rwP ltzP); split.
  * rewrite addZE addrAC subr_ge0; apply/ltrW.
    rewrite (ltr_le_trans (urepr_ltmod _)) //.
    by rewrite ler_addr urepr_ge0.
  * by rewrite addZE -ltr_subr_addl opprB ltr_addl subr_gt0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma word_sz_eq0 {n} (w : n.-word) : n = 0 -> w = 0%R.
Proof.
move=> n_eq0; move: (isword_word w); rewrite [X in modulus X]n_eq0.
rewrite modulus0 -(rwP andP) -!(rwP lezP, rwP ltzP) !lteZE.
rewrite int_to_ZK -[1%:Z]add0r ltz_addr1.
rewrite (rwP andP) -eqr_le => /eqP /(can_inj Z_to_intK).
by move/(@val_inj _ _ _ word0) => <-.
Qed.

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

Lemma wbit0 i : wbit 0 i = false.
Proof. by rewrite /wbit Z.testbit_0_l. Qed.

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

(* -------------------------------------------------------------------- *)
Lemma wbitwE (w : n.-word) (i : nat) : wbit w i  = nth false (w2t w) i.
Proof.
rewrite /w2t; case: (ltnP i n) => [lt_in|ge_in].
+ by rewrite -(tnth_nth _ _ (Ordinal lt_in)) tnth_map tnth_ord_tuple.
+ by rewrite nth_default ?size_tuple // wbit_word_ovf.
Qed.
End WordBits.

(* -------------------------------------------------------------------- *)
Lemma wbit_t2wE {n} (w : n.-tuple bool) k :
  wbit (t2w w) k = nth false w k.
Proof. by rewrite wbitwE t2wK. Qed.

(* -------------------------------------------------------------------- *)
Lemma wbit_t2wFE {n} (F : nat -> bool) k :
  wbit (t2w [tuple F i | i < n]) k = (k < n) && F k.
Proof.
rewrite wbit_t2wE; case: ltnP; rewrite [_ && _]/=.
+ move=> lt_kn; rewrite -(tnth_nth _ _ (Ordinal lt_kn)).
  by rewrite tnth_map tnth_ord_tuple.
+ move=> le_nk; rewrite nth_default //.
  by rewrite size_map val_ord_tuple size_enum_ord.
Qed.

(* -------------------------------------------------------------------- *)
Lemma wbit_mkword {n} (z : Z) (i : 'I_n) :
  wbit (mkword n z) i = wbit z i.
Proof.
rewrite /wbit [toword _]mkwordK modulusZE.
by rewrite Z.mod_pow2_bits_low //; apply/inj_lt/ltP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma wbitb (b : bool) i : wbit b%:R i = b && (i == 0).
Proof. by case: b i => -[|i]. Qed.

(* -------------------------------------------------------------------- *)
Lemma wbitD w1 w2 i :
     (forall j, ~~ wbit w1 j || ~~ wbit w2 j)
  -> (wbit (w1 + w2)%R i = wbit w1 i || wbit w2 i).
Proof.
move=> hex; rewrite /wbit -addZE Z.add_nocarry_lxor.
  apply/Z.bits_inj_0 => j; rewrite Z.land_spec.
  case: (ltrP j 0) => [/ltzP lt0_j|ge0_j].
    by rewrite !Z.testbit_neg_r.
  rewrite -[j]Z2Nat.id ?(rwP lezP) // -!/(wbit _ _).
  by apply/negbTE; rewrite negb_and hex.
rewrite Z.lxor_spec -!/(wbit _ _); move: (hex i).
by case: (wbit w1); case: (wbit w2).
Qed.

(* -------------------------------------------------------------------- *)
Lemma wbit2XM w j i : (0 <= w)%R ->
  wbit (2%:R ^+ j * w)%R i = (j <= i) && wbit w (i - j).
Proof.
move=> ge0_w; rewrite /wbit mulrC -expZE -mulZE; case: leqP => /=.
+ move=> le_ji; rewrite -{1}(subnK le_ji) Nat2Z.n2zD.
  by rewrite addrC Z.mul_pow2_bits_add //; apply/Zle_0_nat.
+ by move=> lt_ij; rewrite Z.mul_pow2_bits_low //; apply/inj_lt/ltP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma wbit2XMb (b : bool) j i :
  wbit (2%:R ^+ j * b%:R) i = b && (i == j).
Proof.
rewrite wbit2XM ?ler0n // wbitb subn_eq0.
by rewrite eqn_leq andbCA !andbA andbAC.
Qed.

(* -------------------------------------------------------------------- *)
Lemma wbit_sum {p} (F : 'I_p -> Z) k :
     (forall i j : 'I_p, i != j -> forall k, 
        ~~ wbit (F i) k || ~~ wbit (F j) k)
  -> wbit (\sum_(i < p) F i)%R k = \big[orb/false]_(i < p) wbit (F i) k.
Proof.
elim: p F k => /= [|p ih] F k hex; first by rewrite !big_ord0 wbit0.
rewrite !big_ord_recl wbitD ?ih //; last first.
  move=> i j ne_ij; apply/hex.
  by rewrite (eqtype.inj_eq (@lift_inj _ _)).
move=> j; rewrite (ih _ j) // => [i1 i2 ne_i1_i2|].
  by apply/hex; rewrite (eqtype.inj_eq (@lift_inj _ _)).
case/boolP: (wbit _ j) => //= w0j; rewrite big_has.
apply/hasPn=> /= i _; have := hex ord0 (lift ord0 i) _ j.
by rewrite w0j /= => ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma wbit_sum2XM {n p} (F : 'I_p -> n.-word) (q : 'I_p) (r : 'I_n) :
    wbit (\sum_(i < p) 2%:R ^+ (n * i) * urepr (F i))%R (q * n + r)
  = wbit (F q) r.
Proof.
rewrite wbit_sum => [i j ne_ij k|].
  rewrite !wbit2XM ?urepr_ge0 //; do 2! case: andP => //=.
  wlog: i j ne_ij / (i < j)%nat => [wlog|lt_ij].
    case: (ltnP i j); first by apply/wlog.
    rewrite leq_eqVlt eq_sym val_eqE (negbTE ne_ij) /=.
    by move=> lt_ji h1 h2; apply/wlog: h2 h1; rewrite 1?eq_sym.
  case=> [le_nMj_k hw1] [le_nMi_k hw2].
  have ltni: k - n * i < n; first apply/contraLR: hw2.
    move=> hw2; rewrite wbit_word_ovf 1?leqNgt //.
  have := ltni; rewrite -subSn // leq_subLR.
  rewrite addnC -mulnS => /(leq_ltn_trans le_nMj_k).
  rewrite ltn_pmul2l; last by rewrite ltnS leqNgt lt_ij.
  by apply/(leq_ltn_trans _ ltni).
rewrite (bigD1 q) //= wbit2XM ?urepr_ge0 //= mulnC.
rewrite leq_addr /= addnC addnK big1 ?orbF //.
move=> i ne_iq; rewrite wbit2XM ?urepr_ge0 // ![n*_]mulnC.
case: leqP => //= le; rewrite wbit_word_ovf //.
case: (n =P 0) => [{1}->//|/eqP nz_n].
rewrite -val_eqE /= in ne_iq; have lt_iq: i < q.
  have: i * n < q.+1 * n.
    by apply/(leq_ltn_trans le); rewrite mulSn ltn_add2r.
  by rewrite ltn_pmul2r ?lt0n // ltnS leq_eqVlt (negbTE ne_iq).
rewrite -addnBA; first by rewrite leq_mul2r (ltnW lt_iq) orbT.
rewrite -mulnBl (@leq_trans (r + n)) ?leq_addl //.
by rewrite leq_add2l leq_pmull // subn_gt0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma wbit_mod2Xn (w : Z) (m k : nat) :
  (0 <= w)%R -> (k < m)%nat ->
    wbit (w mod modulus m) k = wbit w k.
Proof.
move=> ge0_x lt_km; rewrite /wbit modulusZE Z.mod_pow2_bits_low //.
by rewrite int_of_Z_PoszE; apply/inj_lt/ltP.
Qed.

(* ==================================================================== *)
Notation lsb w := (wbit (toword w) 0).
Notation msb w := (wbit (toword w) (wsize w).-1).

(* ==================================================================== *)
Lemma lsbE n (w: n.-word) :
  lsb w = Z.odd w.
Proof. exact: Z.bit0_odd. Qed.

Lemma msbE n (w: n.-word) :
  msb w = (modulus n.-1 <= w)%R.
Proof.
case: n w => [|n] /= w; rewrite /wsize /=.
+ have /andP[_] := isword_word w; rewrite ltrNge => /negbTE->.
  by rewrite wbitwE // nth_default // size_tuple.
apply/esym; rewrite [in LHS]w2sumE big_ord_recr /=.
case: (wbit _); rewrite !Monoid.simpm modulusE.
+ by rewrite ler_addr; apply/sumr_ge0 => i _; apply/ge0_bit.
+ by apply/negbTE; rewrite -ltrNge le2Xn_sumbitsZ.
Qed.

(* ==================================================================== *)
Section SignedRepr.
Context (n : nat).

Definition srepr (w : n.-word) :=
  (if msb w then (val w - modulus n)%R else val w)%Z.

Lemma sreprK : cancel srepr (mkword n).
Proof.
rewrite /srepr => w; case: ifP => _; last exact/ureprK.
apply/val_eqP/eqP; case: w => w /=.
rewrite -mulrN1 mulrC -mulZE -addZE Z_mod_plus_full.
move/andP; rewrite -!(rwP ltzP, rwP lezP) => h.
by rewrite Z.mod_small.
Qed.
End SignedRepr.

Lemma srepr_inj {n} : injective (@srepr n).
Proof.
case: n => [|n].
+ by move=> w1 w2; rewrite [w1]word_sz_eq0 // [w2]word_sz_eq0.
move=> w1 w2; rewrite /srepr !msbE /=; do! case: ifPn.
+ by move=> _ _ /addIr /val_inj.
+ rewrite -ltrNge => /= h2 h1 /eqP; rewrite ltr_eqF //.
  by rewrite (@ltr_le_trans _ 0) ?urepr_ge0 // subr_lt0 urepr_ltmod.
+ rewrite -ltrNge => /= h2 h1 /eqP; rewrite gtr_eqF //.
  by rewrite (@ltr_le_trans _ 0) ?urepr_ge0 // subr_lt0 urepr_ltmod.
+ by move=> _ _ /val_inj.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sreprE {n} (w : n.-word) : srepr w =
  if (urepr w < modulus n.-1)%R then urepr w else (urepr w - modulus n)%R.
Proof.
case: n w => [|n] /= w.
+ have /andP[_] := isword_word w; rewrite modulusE expr0 => h.
  by rewrite h /srepr msbE {1}modulusE expr0 lerNgt h.
+ by rewrite /srepr msbE /= lerNgt if_neg; case: ifP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma wltuE {n} (w1 w2: n.-word) :
  (urepr w1 < urepr w2)%R = (urepr (w1 - w2) != (urepr w1 - urepr w2))%R.
Proof.
apply/esym; case: ltrP; last first.
+ move=> ge; apply/negbTE; rewrite negbK subwE Zmod_small //.
  split; first by apply/lezP; rewrite subr_ge0.
  apply/ltzP; rewrite -[modulus n]subr0 ltr_le_sub //.
  * by rewrite urepr_ltmod. * by rewrite urepr_ge0.
+ move=> lt; rewrite subwE -(@Z_mod_plus _ 1).
  * by apply/Z.lt_gt/ltzP/modulus_gt0.
  rewrite !(addZE, mulZE) mul1r Zmod_small; first split.
  * apply/lezP; rewrite addrC -opprB subr_ge0.
    rewrite ler_subl_addr ler_paddr //.
    * by rewrite urepr_ge0. * by rewrite ltrW ?urepr_ltmod.
  * by apply/ltzP; rewrite gtr_addr subr_lt0.
  * apply/eqP; rewrite -[X in _=X]addr0 => /addrI.
    by move/eqP; rewrite gtr_eqF.
Qed.

(* ==================================================================== *)
Section WSplit.
Context (n : nat).

Notation isword n z := (0 <= z < modulus n)%R.

Lemma wsplit1_subproof (w : n.*2.-word) :
  isword n (Z.div_eucl w (modulus n)).1.
Proof.
rewrite [_.1](_ : _ = (w / modulus n)%Z) //; apply/andP; split.
+ by apply/lezP/Z_div_pos.
+ apply/ltzP/Zdiv_lt_upper_bound => //; rewrite modulusE.
  rewrite mulZE -exprD addnn -modulusE (rwP ltzP).
  by case/andP: (isword_word w).
Qed.

Lemma wsplit2_subproof (w : n.*2.-word) :
  isword n (Z.div_eucl w (modulus n)).2.
Proof. by rewrite [_.2](_ : _ = (w mod modulus n)%Z) ?mkword_proof. Qed.

Definition wsplit (w : n.*2.-word) :=
  let w' := Z.div_eucl w (modulus n) in
  (@mkWord n w'.1 (wsplit1_subproof w),
   @mkWord n w'.2 (wsplit2_subproof w)).
End WSplit.

(* ==================================================================== *)
Section WMul.
Context (n : nat).

Notation isword n z := (0 <= z < modulus n)%R.

Lemma wumul_subproof (w1 w2 : n.-word) : isword n.*2 (urepr w1 * urepr w2).
Proof.
rewrite mulr_ge0 ?urepr_ge0 //= modulusE -addnn exprD.
by apply/ltr_pmul; rewrite -?modulusE ?(urepr_ge0, urepr_ltmod).
Qed.

Definition wumul (w1 w2 : n.-word) : n.*2.-word :=
  mkWord (wumul_subproof w1 w2).

Definition wumul2 (w1 w2 : n.-word) : n.-word * n.-word:=
  wsplit (wumul w1 w2).

Definition wsmul (w1 w2 : n.-word) : n.-word :=
  mkword n (srepr w1 * srepr w2)%R.
End WMul.

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

(* ==================================================================== *)
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

Lemma wN1E i : wbit (mkword n (-1)) i = (i < n).
Proof.
rewrite /wbit /= /modulus two_power_nat_equiv.
have hi := Nat2Z.is_nonneg i.
have hn := Nat2Z.is_nonneg n.
have Hn : (0 < 2 ^ Z.of_nat n)%Z.
+ exact: Z.pow_pos_nonneg.
replace (-1 mod 2 ^ Z.of_nat n)%Z with (Z.ones (Z.of_nat n)); first last.
+ rewrite Z.ones_equiv; elim_div; intuition; cut (z = -1)%Z; Psatz.nia.
case: ltP => h.
+ apply: Z.ones_spec_low; Psatz.lia.
apply: Z.ones_spec_high; Psatz.lia.
Qed.

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

(* ==================================================================== *)
Section WordShift.
Context (n : nat).

Definition lsl (w : n.-word) k := mkword n (Z.shiftl (urepr w) (Z.of_nat k)).
Definition lsr (w : n.-word) k := mkword n (Z.shiftr (urepr w) (Z.of_nat k)).
Definition asr (w : n.-word) k := mkword n (Z.shiftr (srepr w) (Z.of_nat k)).

Notation asl := lsl (only parsing).

Definition rotl (w : n.-word) k :=
  t2w [tuple wbit w ((i + (n - k %% n)) %% n) | i < n].

Definition rotr (w : n.-word) k :=
  t2w [tuple wbit w ((i + k) %% n) | i < n].

Lemma lslE (w : n.-word) k :
  lsl w k = t2w [tuple (k <= i) && wbit w (i - k) | i < n].
Proof.
apply/eqP/eq_from_wbit => i; rewrite [in RHS]wbit_t2wE.
rewrite -tnth_nth tnth_map tnth_ord_tuple.
rewrite /lsl mkword_valK wbit_mod2Xn ?{1}/wbit //.
+ by apply/leZP; rewrite Z.shiftl_nonneg.
rewrite Z.shiftl_spec; first by apply/Zle_0_nat.
case: leqP => /= => [le_ki|lt_ik].
+ by rewrite subZE -Nat2Z.n2zB.
+ by rewrite Z.testbit_neg_r // Z.lt_sub_0; apply/inj_lt/ltP.
Qed.

Lemma lsrE (w : n.-word) k :
  lsr w k = t2w [tuple wbit w (i + k) | i < n].
Proof.
apply/eqP/eq_from_wbit => i; rewrite [in RHS]wbit_t2wE.
rewrite -tnth_nth tnth_map tnth_ord_tuple.
rewrite /lsr mkword_valK wbit_mod2Xn ?{1}/wbit //.
+ by apply/leZP; rewrite Z.shiftr_nonneg.
rewrite Z.shiftr_spec; first by apply/Zle_0_nat.
by rewrite addZE -Nat2Z.n2zD -/(wbit _ _).
Qed.

Lemma wbit_lsl (w : n.-word) i j :
  wbit (lsl w i) (i + j) = (i + j < n) && wbit w j.
Proof. 
rewrite lslE; pose F k := (i <= k) && wbit w (k - i).
by rewrite (wbit_t2wFE F) {}/F leq_addr /= addnC addnK.
Qed.

Lemma wbit_lsl_lo (w : n.-word) i j :
  j < i -> wbit (lsl w i) j = false.
Proof.
move=> lt_ji; rewrite lslE; pose F k := (i <= k) && wbit w (k - i).
by rewrite (wbit_t2wFE F) {}/F [i <= j]leqNgt lt_ji andbF.
Qed.

Lemma wbit_lsr (w : n.-word) i j :
  wbit (lsr w i) j = wbit w (i + j).
Proof.
rewrite lsrE; pose F k := wbit w (k + i).
rewrite (wbit_t2wFE F) {}/F addnC andb_idl //.
apply/contraLR; rewrite -leqNgt => le_nj.
by rewrite wbit_word_ovf // (leq_trans le_nj) // leq_addl.
Qed.

Lemma wbit_lsr_hi (w : n.-word) i j :
  j < i -> wbit (lsr w i) (n - j.+1) = false.
Proof.
move=> lt_ij; rewrite wbit_lsr wbit_word_ovf //; case: (ltnP j n).
+ by move=> lt_jn; rewrite addnBA // -addnC -addnBA ?leq_addr.
+ move=> le_nj; rewrite (leq_trans le_nj) 1?ltnW //.
  by rewrite (leq_trans lt_ij) // leq_addr.
Qed.

Lemma asrE (w : n.-word) k : asr w k =
  t2w [tuple if i + k < n then wbit w (i + k) else msb w | i < n].
Proof.
apply/eqP/eq_from_wbit => i; rewrite [in RHS]wbit_t2wE.
rewrite -tnth_nth tnth_map tnth_ord_tuple.
rewrite /asr mkword_valK sreprE msbE lerNgt; case: ifPn => /=.
+ move=> _; rewrite wbit_mod2Xn ?{1}/wbit //.
  * by apply/leZP; rewrite Z.shiftr_nonneg.
  rewrite Z.shiftr_spec; first by apply/Zle_0_nat.
  rewrite addZE -Nat2Z.n2zD; case: ifPn => //; rewrite -leqNgt.
  by move=> ovf; rewrite -/(wbit _ _) wbit_word_ovf.
rewrite -lerNgt => le; rewrite -(@Z_mod_plus_full _ 1).
rewrite !(addZE, mulZE) mul1r wbit_mod2Xn ?{1}/wbit //.
+ rewrite -ler_subl_addr sub0r /Z.shiftr /=.
  set x := (urepr _ - _)%R; have gex: (-modulus n <= x)%R.
  * by rewrite -ler_subl_addr opprK addrC subrr urepr_ge0.
  case: k => //=; elim=> /= [|k ih].
  * rewrite Z.div2_div -(rwP lezP); apply/Z.div_le_lower_bound => //.
    by apply/lezP; rewrite mulZE (ler_trans _ gex) // ler_nemull.
  * rewrite Pos.iter_succ Z.div2_div -(rwP lezP).
    apply/Z.div_le_lower_bound/lezP => //; rewrite mulZE.
    by rewrite (ler_trans _ ih) // ler_nemull.
rewrite -(@Z.mod_pow2_bits_low _ n) /=; first by apply/inj_lt/ltP.
have h: (2 ^ n = modulus n)%Z by rewrite /modulus two_power_nat_equiv.
rewrite h -Zplus_mod_idemp_r Z_mod_same_full Z.add_0_r.
rewrite -[X in (_ mod X)%Z]h Z.mod_pow2_bits_low.
+ by apply/inj_lt/ltP.
rewrite Z.shiftr_spec; first by apply/Zle_0_nat.
rewrite addZE -Nat2Z.n2zD; case: ifPn.
+ move=> lt_iDk_n; rewrite -(@Z.mod_pow2_bits_low _ n) /=.
  * by apply/inj_lt/ltP.
  rewrite h; rewrite -mulrN1 mulrC -addZE -mulZE.
  rewrite Z_mod_plus_full Zmod_small // !(rwP lezP, rwP ltzP).
  by rewrite (rwP andP) isword_word.
+ rewrite -leqNgt; move=> le_n_iDk; have: (1 <= modulus n - urepr w)%R.
  * rewrite ler_subr_addl; apply/leZP/leZE; rewrite rmorphD.
    by rewrite lez_addr1; apply/ltZE/ltZP/urepr_ltmod.
  rewrite ler_eqVlt => /orP[/eqP|lt].
  * move/(congr1 -%R); rewrite opprB => <-.
    by rewrite Z.bits_opp ?Z.bits_0 //; apply/Zle_0_nat.
  apply/Z.bits_above_log2_neg.
  * by apply/ltzP; rewrite subr_lt0 urepr_ltmod.
  * apply/Z.log2_lt_pow2; apply/ltzP.
    - rewrite -Z.sub_1_r !(subZE, addZE, oppZE).
      by rewrite ltr_subr_addl addr0 opprB.
    - apply/(@ltr_le_trans _ (modulus n)); last first.
      + by rewrite -h; apply/lezP/Z.pow_le_mono_r/inj_le/leP.
      rewrite -Z.sub_1_r !(subZE, oppZE) opprB -addrA -opprD.
      by rewrite ltr_subl_addr ltr_addl ltr_paddl // urepr_ge0.
Qed.

Lemma wbit_asr_hi (w : n.-word) i j :
  (j < i)%nat -> wbit (asr w i) (n - j.+1) = msb w.
Proof.
pose F k := if k + i < n then wbit w (k + i) else msb w.
move=> lt_ji; rewrite asrE (wbit_t2wFE F) {}/F addnC; case: (ltnP j n).
+ move=> lt_jn; rewrite {1}subnS prednK 1?subn_gt0 //.
  rewrite leq_subLR leq_addl /= addnBA // addnC -addnBA //.
  by rewrite ltnNge leq_addr.
+ move=> le_nj; have: n - j.+1 = 0.
    by apply/eqP; rewrite subn_eq0 (leq_trans le_nj).
  move=> -> /=; rewrite addn0 andbC ltnNge ltnW /=.
    by apply/(leq_ltn_trans le_nj).
  rewrite andb_idr // msbE; case: n w => //=.
  move=> w; case/andP: (isword_word w) => _.
  by rewrite ltrNge => /negbTE ->.
Qed.
End WordShift.

(* -------------------------------------------------------------------- *)
Section SubWord.
Context {n : nat}.

Definition subword (i l : nat) (w : n.-word) := mkword l (lsr w i).

Lemma subwordE i l w : subword i l w =
  t2w [tuple wbit w (j + i) | j < l].
Proof.
apply/eqP/eq_from_wbit => j; rewrite /subword lsrE.
rewrite wbit_mkword !wbitwE !t2wK; case: (ltnP j n).
  move=> lt_jn; rewrite -{1}[val j]/(val (Ordinal lt_jn)).
  by rewrite -!tnth_nth !tnth_map !tnth_ord_tuple.
move=> le_nj; rewrite nth_default ?size_tuple // -tnth_nth.
rewrite tnth_map tnth_ord_tuple wbit_word_ovf //.
by rewrite (leq_trans le_nj) // leq_addr.
Qed.

Fixpoint wcat_r (s : seq n.-word) : Z :=
  if s is w :: s then
    Z.lor (urepr w) (Z.shiftl (wcat_r s) n)
  else 0%Z.

Lemma wcat_rE (s : seq n.-word) : wcat_r s =
  (\sum_(i < size s) 2%:R ^+ (n * i) * urepr s`_i)%R.
Proof.
pose F (s : seq n.-word) i := (2%:R ^+ (n * i) * urepr s`_i)%R.
elim: s => /= [|w s ih]; first by rewrite big_ord0.
rewrite big_ord_recl /= muln0 expr0 mul1r.
rewrite Z.shiftl_mul_pow2 //; first by apply/Zle_0_nat.
rewrite (eq_bigr (fun i : 'I__ => 2%:R ^+ n * (F s i))%R).
  by move=> i _; rewrite {}/F mulnS exprD mulrA.
rewrite -mulr_sumr -ih mulrC -!(modulusE, modulusZE).
move=> [: h]; rewrite -Z.lxor_lor; first abstract: h.
  apply/Z.bits_inj_0 => k; rewrite Z.land_spec.
  case: (ltrP k 0) => [lt0_k|ge0_k].
    by rewrite Z.testbit_neg_r // (rwP ltzP).
  have ->: k = Z.of_nat (Z.to_nat k).
    by rewrite Z2Nat.id // (rwP lezP).
  case: (ltnP (Z.to_nat k) n) => [lt_kn|ge_kn]; last first.
    by rewrite -/(wbit _ _) wbit_word_ovf.
  rewrite andbC modulusZE -Z.shiftl_mul_pow2.
    by apply/Zle_0_nat.
  by rewrite Z.shiftl_spec_low //; apply/inj_lt/ltP.
by rewrite -Z.add_nocarry_lxor.
Qed.

Lemma wcat_subproof {p} (s : p.-tuple n.-word) :
  (0 <= wcat_r s < modulus (n * p))%R.
Proof.
rewrite wcat_rE sumr_ge0 /=.
  by move=> i _; rewrite mulr_ge0 ?(urepr_ge0, exprn_ge0).
case: s => /= s /eqP <-; elim: s => /= [|w s ih].
  by rewrite big_ord0 muln0 modulusE expr0.
rewrite big_ord_recl /= muln0 expr0 mul1r.
pose F i := (2%:R ^+ n * (2%:R ^+ (n * i) * urepr s`_i))%R.
rewrite (eq_bigr (F \o val)) /= => [i _|].
  by rewrite mulnS exprD /F mulrA.
rewrite mulnS modulusD {}/F -mulr_sumr -modulusE.
set z := (X in (_ + _ * X < _)%R).
apply/(@ltr_le_trans _ (modulus n + modulus n * z)).
  by rewrite ltr_add2r urepr_ltmod.
rewrite -[X in (X + _ <= _)%R]mulr1 -mulrDr ler_wpmul2l //.
by rewrite -(rwP lezP) -addZE Z.add_1_l; apply/Zlt_le_succ/ltzP.
Qed.

Definition wcat {p} (s : p.-tuple n.-word) :=
  mkWord (wcat_subproof s).

Lemma wcat_wbitE {p} (s : p.-tuple n.-word) i :
  wbit (wcat s) i = wbit (s`_(i %/ n))%R (i %% n).
Proof.
case: (n =P 0) => [z_n|/eqP nz_n].
  rewrite [wcat s]word_sz_eq0; first by rewrite z_n.
  by rewrite [(s`__)%R]word_sz_eq0 // !wbit0.
case: (ltnP i (n * p)); last first.
  move=> h; rewrite wbit_word_ovf // nth_default ?wbit0 //.
  by rewrite leq_divRL ?lt0n // size_tuple mulnC.
move=> lt_i_nMp; have lt_iDn_p: i %/ n < p.
  by rewrite ltn_divLR ?lt0n // mulnC.
have lt_iEn_n: i %% n < n by rewrite ltn_mod lt0n.
rewrite /wcat /= wcat_rE {1}(@divn_eq i n) size_tuple.
pose oi := Ordinal lt_iDn_p; pose oj := Ordinal lt_iEn_n.
by rewrite (wbit_sum2XM _ oi oj).
Qed.

Lemma wcatE {p} (s : p.-tuple n.-word) :
  wcat s = t2w [tuple wbit (s`_(i %/ n))%R (i %% n) | i < n * p].
Proof.
apply/eqP/eq_from_wbit => i; rewrite wcat_wbitE wbit_t2wE.
by rewrite -tnth_nth tnth_map tnth_ord_tuple.
Qed.
End SubWord.

Lemma wcat_subwordK {n p} (w : (n * p).-word) :
  wcat [tuple subword (i * n) n w | i < p] = w.
Proof.
case: (n =P 0) => [n_eq0|/eqP nz_n].
  by rewrite [w]word_sz_eq0 ?[wcat _]word_sz_eq0 ?n_eq0.
apply/eqP/eq_from_wbit => i; rewrite wcat_wbitE.
have hD: i %/ n < p by rewrite ltn_divLR ?lt0n // [p*_]mulnC.
rewrite -(tnth_nth _ _ (Ordinal hD)) tnth_map tnth_ord_tuple.
rewrite subwordE wbit_t2wE; have hE: i %% n < n.
  by rewrite ltn_mod lt0n.
rewrite -(tnth_nth _ _ (Ordinal hE)) tnth_map.
by rewrite tnth_ord_tuple /= addnC -divn_eq.
Qed.
