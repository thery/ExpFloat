Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Interval Require Import Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim algoLog1 algoMul1.
Require Import Fast2Sum_robust_flt algoQ1 tableT1 tableT2 algoExp1.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Prelim.

Let p := 53%Z.
Let emax := 1024%Z.
Let emin := (3 - emax - p)%Z.

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
Context ( valid_rnd : Valid_rnd rnd ).

Local Notation float := (float radix2).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format radix2 fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation fastTwoSum := (fastTwoSum rnd).
Local Notation exactMul := (exactMul rnd).
Local Notation fastSum := (fastSum rnd).
Local Notation q1 := (q1 rnd).
Local Notation exp1 := (exp1 rnd).

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

End Prelim.

Section algoPhase1.

Let p := 53%Z.
Let emax := 1024%Z.
Let emin := (3 - emax - p)%Z.

Let beta := radix2.

Hypothesis Hp2: Z.lt 1 p.
Local Notation pow e := (bpow beta e).

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).

Variable rnd : R -> Z.
Context ( valid_rnd : Valid_rnd rnd ).

Local Notation float := (float radix2).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format radix2 fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation fastTwoSum := (fastTwoSum rnd).
Local Notation exactMul := (exactMul rnd).
Local Notation fastSum := (fastSum rnd).
Local Notation log1 := (log1 rnd).
Local Notation mul1 := (mul1 rnd).
Local Notation q1 := (q1 rnd).
Variable choice : Z -> bool.
Local Notation exp1 := (exp1 rnd choice).

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Local Notation ulp := (ulp beta fexp).


(* Algo Phase 1 *)

Definition Nan := omega + 1.
Local Notation " x <? y " := (Rlt_bool x y).
Local Notation FAIL := None.
Local Notation R_UP := (round beta fexp Zceil).
Local Notation R_DN := (round beta fexp Zfloor).

Definition hsqrt2 := 0x1.6a09e667f3bccp-1.

Lemma hsqrt2E : hsqrt2 = R_DN (sqrt 2 / 2).
Proof.
have hsE : hsqrt2 = Float beta 6369051672525772 (-53).
  rewrite /hsqrt2 /Q2R /F2R /= /Z.pow_pos /=.
  by lra.
rewrite hsE.
apply/sym_equal/round_DN_eq => //; first by apply: FLT_exp_valid.
  by apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _.
rewrite -hsE; split.
  rewrite /F2R /= /Z.pow_pos /=.
  by interval with (i_prec 100).
have maghsE : mag beta hsqrt2 = 0%Z :> Z.
  apply: mag_unique.
  rewrite /F2R /= /Z.pow_pos /=.
  by split; interval.
have uhsE : ulp hsqrt2 = pow (- 53).
  rewrite ulp_neq_0.
    by congr (pow _); rewrite /cexp /fexp maghsE.
  by rewrite /hsqrt2 /F2R /= /Z.pow_pos /=; lra.
by rewrite succ_eq_pos ?uhsE; interval with (i_prec 100).
Qed.

Lemma hsqrt2F : format hsqrt2.
Proof.
by rewrite hsqrt2E; apply: generic_format_round; apply: FLT_exp_valid.
Qed.

Definition sqrt2 := 0x1.6a09e667f3bcdp+0.

Lemma sqrt2E : sqrt2 = R_UP (sqrt 2).
Proof.
have sE : sqrt2 = Float beta 6369051672525773 (-52).
  rewrite /sqrt2 /Q2R /F2R /= /Z.pow_pos /=.
  by lra.
rewrite sE.
apply/sym_equal/round_UP_eq => //; first by apply: FLT_exp_valid.
  by apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _.
rewrite -sE; split; last first.
  by rewrite /F2R /= /Z.pow_pos /=; interval with (i_prec 100).
have magsE : mag beta sqrt2 = 1%Z :> Z.
  apply: mag_unique.
  rewrite /F2R /= /Z.pow_pos /=.
  by split; interval.
have usE : ulp sqrt2 = pow (- 52).
  rewrite ulp_neq_0.
    by congr (pow _); rewrite /cexp /fexp magsE.
  by rewrite /sqrt2 /F2R /= /Z.pow_pos /=; lra.
rewrite pred_eq_pos; last by interval.
rewrite /pred_pos magsE.
case: Req_bool_spec => [|_].
  suff : pow (1 - 1) < sqrt2 by lra.
  by interval.
by rewrite usE; interval with (i_prec 100).
Qed.

Lemma sqrt2F : format sqrt2.
Proof.
by rewrite sqrt2E; apply: generic_format_round; apply: FLT_exp_valid.
Qed.

Definition e1 := 0x1.5b4a6bd3fff4ap-58.

Lemma e1E : e1 = R_UP (Rpower 2 (- 57.560)).
Proof.                    
have e1E : e1 = Float beta 6109602743582538 (- 110).
  rewrite /e1 /Q2R /F2R /= /Z.pow_pos /=.
  by lra.
apply/sym_equal/round_UP_eq => //; first by apply: FLT_exp_valid.
  rewrite e1E.
  by apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _.
split; last by interval with (i_prec 100).
have mage1E : mag beta e1 = (-57)%Z :> Z.
  apply: mag_unique.
  rewrite /F2R /= /Z.pow_pos /=.
  by split; interval.
have ue1E : ulp e1 = pow (- 110).
  rewrite ulp_neq_0.
    by congr (pow _); rewrite /cexp /fexp mage1E.
  by rewrite /e1 /F2R /= /Z.pow_pos /=; lra.
rewrite pred_eq_pos; last by interval.
rewrite /pred_pos mage1E.
case: Req_bool_spec => [|_].
  suff : pow (- 57 - 1) < e1 by lra.
  by interval.
by rewrite ue1E; interval with (i_prec 70).
Qed.

Lemma e1F : format e1.
Proof.
by rewrite e1E; apply: generic_format_round; apply: FLT_exp_valid.
Qed.

Definition e2 := 0x1.27b3b3b4bb6dfp-63.

Lemma e2E : e2 = R_UP (Rpower 2 (- 62.792)).
Proof.                    
have e2E : e2 = Float beta 5202043908896479 (- 115).
  rewrite /e2 /Q2R /F2R /= /Z.pow_pos /=.
  by lra.
apply/sym_equal/round_UP_eq => //; first by apply: FLT_exp_valid.
  rewrite e2E.
  by apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _.
split; last by interval with (i_prec 100).
have mage1E : mag beta e2 = (- 62)%Z :> Z.
  apply: mag_unique.
  rewrite /F2R /= /Z.pow_pos /=.
  by split; interval.
have ue2E : ulp e2 = pow (- 115).
  rewrite ulp_neq_0.
    by congr (pow _); rewrite /cexp /fexp mage1E.
  by rewrite /e2 /F2R /= /Z.pow_pos /=; lra.
rewrite pred_eq_pos; last by interval.
rewrite /pred_pos mage1E.
case: Req_bool_spec => [|_].
  suff : pow (- 62 - 1) < e2 by lra.
  by interval.
by rewrite ue2E; interval with (i_prec 60).
Qed.

Lemma e2F : format e2.
Proof.
by rewrite e2E; apply: generic_format_round; apply: FLT_exp_valid.
Qed.

Local Notation " x =? y " := (Req_bool x y).

Definition phase1 (x y : R) := 
  let l := log1 x in 
  let r := mul1 l y in 
  let 'DWR eh el := exp1 r in 
  let e := 
    if (0x1.6a09e667f3bccp-1 <? x) && (x <? 0x1.6a09e667f3bcdp+0) then 
      0x1.5b4a6bd3fff4ap-58 else 0x1.27b3b3b4bb6dfp-63 in 
  let u := RND (eh + RND (el - e * eh)) in 
  let v := RND (eh + RND (el + e * eh)) in
  if (u =? v) then some u else FAIL.
    
End algoPhase1.

