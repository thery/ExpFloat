Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
Require Import tableINVERSE tableLOGINV algoP1.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Log1.

Let p := 53%Z.
Let emax := 1024%Z.
Let emin := (3 - emax - p)%Z.

Compute emin.

Let beta := radix2.

Hypothesis Hp2: Z.lt 1 p.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).

Lemma uE : u = pow (- p).
Proof. by rewrite /u /= /Z.pow_pos /=; lra. Qed.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Local Notation float := (float radix2).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format radix2 fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation fastTwoSum := (fastTwoSum rnd).
Local Notation RN := (round beta fexp rnd).
Local Notation p1 := (p1 rnd).

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Variable getRange : R -> R * Z.

Hypothesis getRangeCorrect : 
  forall f,  format f -> alpha <= f <= omega -> 
    sqrt 2 / 2 < (getRange f).1 < sqrt 2 /\ 
    f = ((getRange f).1) * pow (getRange f).2.

Lemma getRange_bound f : 
  format f -> alpha <= f <= omega -> (- 1074 <= (getRange f).2 <= 1024)%Z.
Proof.
move=> aF aB.
have sqrt2B : 1.4 < sqrt 2 < 1.5 by split; interval.
have [tN eB] := getRangeCorrect aF aB.
set t := (_).1 in eB tN; set e := (_).2 in eB *.
suff:  (- 1075 < e < 1025)%Z by lia.
suff : -1075 < IZR e < 1025 by case; split; apply/lt_IZR.
suff:  Rpower 2 (- 1075) < Rpower 2 (IZR e) < Rpower 2 (1025).
  have: IZR e <= - 1075 -> Rpower 2 (IZR e) <= Rpower 2 (- 1075).
    by apply: Rle_Rpower; lra.
  have: 1025 <= IZR e -> Rpower 2 1025 <= Rpower 2 (IZR e).
    by apply: Rle_Rpower; lra.
  by lra.
have -> : Rpower 2 (IZR e) = pow e by rewrite pow_Rpower.
suff : t * Rpower 2 (-1075) < t * pow e < t * Rpower 2 1025 by nra.
suff : sqrt 2 * Rpower 2 (-1075) < t * pow e < sqrt 2 / 2 * Rpower 2 1025.
  have : 0 < Rpower 2 (- 1075).
    by rewrite -pow_Rpower //; apply: bpow_gt_0.
  suff : 0 < Rpower 2 (1025) by nra.
  by rewrite -pow_Rpower //; apply: bpow_gt_0.
rewrite -eB; rewrite /alpha /omega in aB.
split; interval with (i_prec 40).
Qed.

Definition getIndex (f : R) : nat := Z.to_nat (Zfloor (pow 8 * f)).

Lemma getIndexCorrect (f : R) : 
  alpha <= f -> Z.of_nat (getIndex f) = Zfloor (pow 8 * f).
Proof.
move=> aLf; rewrite Z2Nat.id // -(Zfloor_IZR 0).
apply: Zfloor_le.
have : 0 <= pow 8 by apply: bpow_ge_0.
have : 0 < alpha by apply: alpha_gt_0.
nra.
Qed.

Lemma fastTwoSum_0 : fastTwoSum 0 0 = DWR 0 0.
Proof. by rewrite /fastTwoSum !(Rsimp01, round_0). Qed. 

Definition fastSum (a bh bl : R) := 
  let: DWR h t := fastTwoSum a bh in DWR h (RN (t + bl)).

Lemma fastSum_0 : fastSum 0 0 0 = DWR 0 0.
Proof. by rewrite /fastSum fastTwoSum_0 Rsimp01 round_0. Qed. 

Definition log1 x := 
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RN (r * t  - 1) in
  let th := RN (IZR e * LOG2H + l1) in 
  let tl := RN (IZR e * LOG2L + l2) in
  let: DWR h l := fastSum th z tl in 
  let: DWR ph pl := p1 z in 
  let: DWR h l := fastSum h ph (RN (l * pl)) in 
  if (e =? 0%Z)%Z then fastTwoSum h l else DWR h l.

Lemma log1_1 :  log1 1 = DWR 0 0.
Proof.
have sqrt2B : 1.4 < sqrt 2 < 1.5 by split; interval.
have F1 : format 1 by apply: format1.
have aL1 : alpha <= 1 by rewrite /alpha; interval.
rewrite /log1; case: getRange (getRangeCorrect F1 aL1) => t e.
rewrite /fst /snd => [] [H1 H2].
have eE : e = 0%Z.
  case: e H2 => // e1.
    suff: pow 1 <= pow (Z.pos e1) by rewrite pow1E [IZR beta]/=; nra.
    by apply: bpow_le; lia.
    suff: pow (Z.neg e1) <= pow (- 1).
      by rewrite (bpow_opp _ 1) pow1E [IZR beta]/=; nra.
    by apply: bpow_le; lia.
have tE : t = 1 by rewrite eE pow0E in H2; lra.
set i := getIndex t.
have iE : i = 256%N.
  by rewrite {}/i /getIndex tE Rmult_1_r /= /Z.pow_pos /= Zfloor_IZR.
rewrite iE ![nth _ _ _]/= tE eE !Rsimp01.
have -> : 0x1.00%xR = 1 by lra.
by rewrite /= !(Rsimp01, Rminus_eq_0, round_0, p1_0, fastTwoSum_0).
Qed.

Lemma th_prop (e : Z) p : 
  p \in LOGINV -> 
  let th := RN (IZR e * LOG2H + p.1) in 
  [/\ is_imul th (pow -42),
      th = IZR e * LOG2H + p.1, 

      
(* This is lemma 4*)

Lemma hl_logB x : 
  alpha <= x -> format x ->
  let: DWR h l := log1 x in 
  [/\ Rabs l <= Rpower 2 (- 23.89) * Rabs h,
      Rabs (h + l - ln x) <= (Rpower 2  (- 67.0544)) * Rabs (ln x) &
      ~ (sqrt 2 / 2 < x < sqrt 2) -> 
      Rabs (h + l - ln x) <= (Rpower 2  (- 73.527)) * Rabs (ln x)].
Proof.
move=> aLx Fx.
have sqrt2B : 1.4 < sqrt 2 < 1.5 by split; interval.
have [x_eq1|x_neq1] := Req_dec x 1.
  by rewrite x_eq1 log1_1 !Rsimp01; split; [lra | interval | move=> _; interval].
Admitted.
  
End Log1.

