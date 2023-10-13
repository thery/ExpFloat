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
Local Notation log1 := (log1 rnd).
Local Notation mul1 := (mul1 rnd).
Local Notation q1 := (q1 rnd).
Variable choice : Z -> bool.
Local Notation exp1 := (exp1 rnd choice).

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Local Notation ulp := (ulp beta fexp).
Local Notation R_UP := (round beta fexp Zceil).
Local Notation R_DN := (round beta fexp Zfloor).

Definition hsqrt2 := 0x1.6a09e667f3bccp-1.

Lemma hsqrt2sqrt : sqrt 2 / 2 = / sqrt 2.
Proof.
have {2}<- : (sqrt 2) ^ 2 = 2 by apply: pow2_sqrt; interval.
by field; interval.
Qed.

Lemma hsqrt2E : hsqrt2 = R_DN (sqrt 2 / 2).
Proof.
have hsE : hsqrt2 = Float beta 6369051672525772 (-53).
  rewrite /hsqrt2 /Q2R /F2R /= /Z.pow_pos /=.
  by lra.
rewrite hsE.
apply/sym_equal/round_DN_eq => //.
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
apply/sym_equal/round_UP_eq => //.
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
apply/sym_equal/round_UP_eq => //.
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
apply/sym_equal/round_UP_eq.
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

Variables x y : R.
Hypothesis xB : alpha <= x <= omega.
Hypothesis xF : format x.
Hypothesis yF : format y.

Definition lh := let 'DWR lh _  := log1 x in lh.
Definition ll := let 'DWR _  ll := log1 x in ll.

Definition rh := let 'DWR rh _  := mul1 (DWR lh ll) y in rh.
Definition rl := let 'DWR _  rl := mul1 (DWR lh ll) y in rl.

Definition rhF : format rh.
Proof. by apply: generic_format_round. Qed.

Definition rlF : format rl.
Proof. by apply: generic_format_round. Qed.

Definition eh := if exp1 (DWR rh rl) is some (DWR eh _) then eh else 0.
Definition el := if exp1 (DWR rh rl) is some (DWR _ el) then el else 0.

Lemma sqrt2NF : ~ format (sqrt 2).
Proof.
move=> sqrt2F.
have [cexp_pos|cexp_neg] := Z_le_dec 0 (cexp (sqrt 2)).
  case: (@sqrt2_irr (Ztrunc (scaled_mantissa radix2 fexp (sqrt 2)) * 
                       2 ^ (cexp (sqrt 2))) 1).
  by rewrite [RHS]sqrt2F /F2R /= Rsimp01 mult_IZR /= (IZR_Zpower beta).
case: (@sqrt2_irr (Ztrunc (scaled_mantissa radix2 fexp (sqrt 2))) 
                  (2 ^ (- cexp (sqrt 2)))).
rewrite [RHS]sqrt2F /F2R /= (IZR_Zpower beta); last by lia.
by rewrite bpow_opp /Rdiv Rinv_inv.
Qed.

Lemma hsqrt2NF : ~ format (sqrt 2 / 2).
Proof.
move=> hsqrt2F.
have [cexp_pos|cexp_neg] := Z_le_dec 0 (cexp (sqrt 2 / 2) + 1).
  case: (@sqrt2_irr (Ztrunc (scaled_mantissa radix2 fexp (sqrt 2 / 2)) * 
                       2 ^ (cexp (sqrt 2 / 2) + 1)) 1).
  have {3}-> : sqrt 2 = (sqrt 2 / 2) * 2 by lra.                    
  rewrite [in RHS]hsqrt2F /F2R /= Rsimp01 mult_IZR /= (IZR_Zpower beta) //.
  rewrite bpow_plus pow1E -[IZR beta]/2.
  by set u := pow _; set v := IZR _; lra.
case: (@sqrt2_irr (Ztrunc (scaled_mantissa radix2 fexp (sqrt 2 / 2))) 
                  (2 ^ (- (cexp (sqrt 2 / 2) + 1)))).
have {3}-> : sqrt 2 = (sqrt 2 / 2) * 2 by lra.
rewrite [in RHS]hsqrt2F /F2R /= (IZR_Zpower beta); last by lia.
rewrite bpow_opp /Rdiv Rinv_inv.
rewrite bpow_plus pow1E -[IZR beta]/2.
by set u := pow _; set v := IZR _; lra.
Qed.

Definition e := 
  if (Rlt_bool hsqrt2 x) && (Rlt_bool x sqrt2) then e1 else e2.

Lemma eI : sqrt 2 / 2 < x < sqrt 2 -> e = R_UP(Rpower 2  (- 57.560)).
Proof.
move=> xB1.
have xRB : R_DN (sqrt 2 / 2) <= x <= R_UP (sqrt 2).
  split.
    have <- : R_DN x = x by apply: round_generic.
    by apply: round_le; lra.
  have <- : R_UP x = x by apply: round_generic.
  by apply: round_le; lra.
have DN_UP_hsqrt2 : R_DN (sqrt 2 / 2) < sqrt 2 / 2 < R_UP (sqrt 2 / 2).
  by apply/round_DN_UP_lt/hsqrt2NF.
have DN_UP_sqrt2 : R_DN (sqrt 2) < sqrt 2 < R_UP (sqrt 2).
  by apply/round_DN_UP_lt/sqrt2NF.
rewrite /e hsqrt2E sqrt2E; case: Rlt_bool_spec => /= H; last by lra.
case: Rlt_bool_spec => /= H1; last by lra.
by apply: e1E.
Qed.

Lemma eNI : x <= sqrt 2 / 2 \/ sqrt 2 <= x -> e = R_UP(Rpower 2  (- 62.792)).
Proof.
case => xB1.
  have xRB : x <= R_DN (sqrt 2 / 2).
    have <- : R_DN x = x by apply: round_generic.
    by apply: round_le; lra.
  have DN_UP_hsqrt2 : R_DN (sqrt 2 / 2) < sqrt 2 / 2 < R_UP (sqrt 2 / 2).
    by apply/round_DN_UP_lt/hsqrt2NF.
  rewrite /e hsqrt2E sqrt2E; case: Rlt_bool_spec => /= H; first by lra.
  by rewrite e2E.
have xRB : R_UP (sqrt 2) <= x.
  have <- : R_UP x = x by apply: round_generic.
  by apply: round_le; lra.
have DN_UP_sqrt2 : R_DN (sqrt 2) < sqrt 2 < R_UP (sqrt 2).
  by apply/round_DN_UP_lt/sqrt2NF.
rewrite /e hsqrt2E sqrt2E; case: Rlt_bool_spec => /= H; last by rewrite e2E.
by case: Rlt_bool_spec => /= H1; [lra | rewrite e2E].
Qed.

Definition mu := 
  if (Rlt_bool hsqrt2 x) && (Rlt_bool x sqrt2) then Rpower 2 (- 57.5605)
  else Rpower 2 (- 62.7924).

Lemma muI : sqrt 2 / 2 < x < sqrt 2 -> mu = Rpower 2 (- 57.5605).
Proof.
move=> xB1.
have xRB : R_DN (sqrt 2 / 2) <= x <= R_UP (sqrt 2).
  split.
    have <- : R_DN x = x by apply: round_generic.
    by apply: round_le; lra.
  have <- : R_UP x = x by apply: round_generic.
  by apply: round_le; lra.
have DN_UP_hsqrt2 : R_DN (sqrt 2 / 2) < sqrt 2 / 2 < R_UP (sqrt 2 / 2).
  by apply/round_DN_UP_lt/hsqrt2NF.
have DN_UP_sqrt2 : R_DN (sqrt 2) < sqrt 2 < R_UP (sqrt 2).
  by apply/round_DN_UP_lt/sqrt2NF.
rewrite /mu hsqrt2E sqrt2E; case: Rlt_bool_spec => /= H; last by lra.
by case: Rlt_bool_spec => //; lra.
Qed.

Lemma muNI : x <= sqrt 2 / 2 \/ sqrt 2 <= x -> mu = Rpower 2 (- 62.7924).
Proof.
case => xB1.
  have xRB : x <= R_DN (sqrt 2 / 2).
    have <- : R_DN x = x by apply: round_generic.
    by apply: round_le; lra.
  have DN_UP_hsqrt2 : R_DN (sqrt 2 / 2) < sqrt 2 / 2 < R_UP (sqrt 2 / 2).
    by apply/round_DN_UP_lt/hsqrt2NF.
  by rewrite /mu hsqrt2E sqrt2E; case: Rlt_bool_spec => //= H; lra.
have xRB : R_UP (sqrt 2) <= x.
  have <- : R_UP x = x by apply: round_generic.
  by apply: round_le; lra.
have DN_UP_sqrt2 : R_DN (sqrt 2) < sqrt 2 < R_UP (sqrt 2).
  by apply/round_DN_UP_lt/sqrt2NF.
rewrite /mu hsqrt2E sqrt2E; case: Rlt_bool_spec => //= H.
by case: Rlt_bool_spec => //= H1; lra.
Qed.

Definition tau := 
  if (Rlt_bool hsqrt2 x) && (Rlt_bool x sqrt2) then Rpower 2 (- 57.5604) 
  else Rpower 2 (- 62.7923).

Lemma tauI : sqrt 2 / 2 < x < sqrt 2 -> tau = Rpower 2 (- 57.5604).
Proof.
move=> xB1.
have xRB : R_DN (sqrt 2 / 2) <= x <= R_UP (sqrt 2).
  split.
    have <- : R_DN x = x by apply: round_generic.
    by apply: round_le; lra.
  have <- : R_UP x = x by apply: round_generic.
  by apply: round_le; lra.
have DN_UP_hsqrt2 : R_DN (sqrt 2 / 2) < sqrt 2 / 2 < R_UP (sqrt 2 / 2).
  by apply/round_DN_UP_lt/hsqrt2NF.
have DN_UP_sqrt2 : R_DN (sqrt 2) < sqrt 2 < R_UP (sqrt 2).
  by apply/round_DN_UP_lt/sqrt2NF.
rewrite /tau hsqrt2E sqrt2E; case: Rlt_bool_spec => //= H; last by lra.
by case: Rlt_bool_spec => //= H1; lra.
Qed.

Lemma tauNI : x <= sqrt 2 / 2 \/ sqrt 2 <= x -> tau = Rpower 2 (- 62.7923).
Proof.
case => xB1.
  have xRB : x <= R_DN (sqrt 2 / 2).
    have <- : R_DN x = x by apply: round_generic.
    by apply: round_le; lra.
  have DN_UP_hsqrt2 : R_DN (sqrt 2 / 2) < sqrt 2 / 2 < R_UP (sqrt 2 / 2).
    by apply/round_DN_UP_lt/hsqrt2NF.
  by rewrite /tau hsqrt2E sqrt2E; case: Rlt_bool_spec => //= H; lra.
have xRB : R_UP (sqrt 2) <= x.
  have <- : R_UP x = x by apply: round_generic.
  by apply: round_le; lra.
have DN_UP_sqrt2 : R_DN (sqrt 2) < sqrt 2 < R_UP (sqrt 2).
  by apply/round_DN_UP_lt/sqrt2NF.
rewrite /tau hsqrt2E sqrt2E; case: Rlt_bool_spec => //= H.
by case: Rlt_bool_spec => /= H1; lra.
Qed.

Definition eln := 
  if (Rlt_bool hsqrt2 x) && (Rlt_bool x sqrt2) then Rpower 2 (- 67.0544)
  else Rpower 2 (- 73.527).

Lemma elnB : 0 < eln < 1.
Proof.
by rewrite /eln; (do 2 case: Rlt_bool) => /=; split; interval.
Qed.

Lemma elnI : sqrt 2 / 2 < x < sqrt 2 -> eln = Rpower 2 (- 67.0544).
Proof.
move=> xB1.
have xRB : R_DN (sqrt 2 / 2) <= x <= R_UP (sqrt 2).
  split.
    have <- : R_DN x = x by apply: round_generic.
    by apply: round_le; lra.
  have <- : R_UP x = x by apply: round_generic.
  by apply: round_le; lra.
have DN_UP_hsqrt2 : R_DN (sqrt 2 / 2) < sqrt 2 / 2 < R_UP (sqrt 2 / 2).
  by apply/round_DN_UP_lt/hsqrt2NF.
have DN_UP_sqrt2 : R_DN (sqrt 2) < sqrt 2 < R_UP (sqrt 2).
  by apply/round_DN_UP_lt/sqrt2NF.
rewrite /eln hsqrt2E sqrt2E; case: Rlt_bool_spec => /= H; last by lra.
by case: Rlt_bool_spec => //; lra.
Qed.

Lemma elnNI : x <= sqrt 2 / 2 \/ sqrt 2 <= x -> eln = Rpower 2 (- 73.527).
Proof.
case => xB1.
  have xRB : x <= R_DN (sqrt 2 / 2).
    have <- : R_DN x = x by apply: round_generic.
    by apply: round_le; lra.
  have DN_UP_hsqrt2 : R_DN (sqrt 2 / 2) < sqrt 2 / 2 < R_UP (sqrt 2 / 2).
    by apply/round_DN_UP_lt/hsqrt2NF.
  by rewrite /eln hsqrt2E sqrt2E; case: Rlt_bool_spec => //= H; lra.
have xRB : R_UP (sqrt 2) <= x.
  have <- : R_UP x = x by apply: round_generic.
  by apply: round_le; lra.
have DN_UP_sqrt2 : R_DN (sqrt 2) < sqrt 2 < R_UP (sqrt 2).
  by apply/round_DN_UP_lt/sqrt2NF.
rewrite /eln hsqrt2E sqrt2E; case: Rlt_bool_spec => //= H.
by case: Rlt_bool_spec => //= H1; lra.
Qed.

Lemma hllnxB : Rabs (lh + ll - ln x) <= eln * Rabs (ln x).
Proof.
have [llB lhllB lhllB1] : 
        [/\ Rabs ll <= Rpower 2 (-23.89) * Rabs lh, 
            Rabs (lh + ll - ln x) <= Rpower 2 (-67.0544) * Rabs (ln x) & 
            ~ / sqrt 2 < x < sqrt 2 -> 
            Rabs (lh + ll - ln x) <= Rpower 2 (-73.527) * Rabs (ln x)].
  have := @err_lem4 (refl_equal _) rnd valid_rnd x xF xB.
  by rewrite /lh /ll; case: log1.
have [xLhs|hsLx] := Rle_lt_dec x (/ sqrt 2).
  rewrite elnNI; first by apply: lhllB1; lra.
  by rewrite hsqrt2sqrt; lra.
have [sLx|xLs] := Rle_lt_dec (sqrt 2) x.
  rewrite elnNI; first by apply: lhllB1; lra.
  by rewrite hsqrt2sqrt; lra.
rewrite elnI //.
by rewrite hsqrt2sqrt; lra.
Qed.

Definition u' := RND (eh + RND (el - e * eh)).
Definition v' := RND (eh + RND (el + e * eh)).

Lemma ylnxLB : 
    ~ r1 < rh < r2 ->
    Rabs rh * (1 - pow (- 52))  * (1 - Rpower 2 (-23.89)) / (1 + eln) <= 
             Rabs (y * ln x).
Proof.
move=> rhB.
have rhB1 : - r1 <= Rabs rh.
  have [] := Rle_lt_dec rh r1; last first.
    have [] := Rle_lt_dec r2 rh; last by lra.
    by rewrite /r1 /r2 => rhBB _; interval.
  by rewrite /r1; split_Rabs; lra.
have elnB := elnB.
have lnxB :  Rabs (lh + ll) / (1  + eln) <= Rabs (ln x).
  apply/Rcomplements.Rle_div_l; first by lra.
  by have hllnxB := hllnxB; split_Rabs; nra.
have [llB _ _] : 
        [/\ Rabs ll <= Rpower 2 (-23.89) * Rabs lh, 
            Rabs (lh + ll - ln x) <= Rpower 2 (-67.0544) * Rabs (ln x) & 
            ~ / sqrt 2 < x < sqrt 2 -> 
            Rabs (lh + ll - ln x) <= Rpower 2 (-73.527) * Rabs (ln x)].
  have := @err_lem4 (refl_equal _) rnd valid_rnd x xF xB.
  by rewrite /lh /ll; case: log1.
have ylhB : Rabs rh * (1 - pow (- 52)) <= Rabs (y * lh).
  have -> : rh = RND (y * lh) by [].
  have [ex [exB ->]]: exists eps : R, 
     Rabs eps < pow (- p + 1) /\ RND (y * lh) = (y * lh) * (1 + eps).
    have:= @relative_error_ex _ _ _ (emin + p); apply => //.
      by rewrite /fexp => k kL; lia.
    have [//|ylhLe] := Rle_lt_dec (pow (emin + p)) (Rabs (y * lh)).
    have : Rabs (RND (y * lh)) <= pow (emin + p).
      apply: Rabs_round_le => //.
      by rewrite -[bpow _ _]/(pow _); lra.
    have -> : RND (y * lh) = rh by [].
    have : pow (emin + p) < Rabs rh.
      apply: Rlt_le_trans rhB1.
      by interval.
    by lra.
  rewrite Rabs_mult [Rabs (1 + _)]Rabs_pos_eq; last by interval.
  have exMB : 0 <= (1 + ex) * (1 - pow (-52)) <= 1.
    by split; interval with (i_prec 70).
  suff : 0 <= Rabs (y * lh) by nra.
  by apply: Rabs_pos.
apply: Rle_trans (_ : Rabs (y * lh) * (1 - Rpower 2 (-23.89)) / (1 + eln) <= _).
  apply: Rmult_le_compat_r; first by apply: Rinv_0_le_compat; lra.
  by apply: Rmult_le_compat_r; first by interval.
rewrite !Rabs_mult [_ / _]Rmult_assoc Rmult_assoc.
apply: Rmult_le_compat_l; first apply: Rabs_pos.
rewrite -Rmult_assoc.
apply: Rle_trans _ lnxB.
apply: Rmult_le_compat_r; first by apply: Rinv_0_le_compat; lra.
by split_Rabs; nra.
Qed.

Lemma ylnxUB : 
    ~ r1 < rh < r2 ->
     Rabs (y * ln x) <=
     Rabs rh * (1 + pow (- 52))  * (1 + Rpower 2 (-23.89)) / (1 - eln).
Proof.
move=> rhB.
have rhB1 : - r1 <= Rabs rh.
  have [] := Rle_lt_dec rh r1; last first.
    have [] := Rle_lt_dec r2 rh; last by lra.
    by rewrite /r1 /r2 => rhBB _; interval.
  by rewrite /r1; split_Rabs; lra.
have elnB := elnB.
have lnxB : Rabs (ln x) <= Rabs (lh + ll) / (1 - eln).
  apply/Rcomplements.Rle_div_r; first by lra.
  by have hllnxB := hllnxB; split_Rabs; nra.
have [llB _ _] : 
        [/\ Rabs ll <= Rpower 2 (-23.89) * Rabs lh, 
            Rabs (lh + ll - ln x) <= Rpower 2 (-67.0544) * Rabs (ln x) & 
            ~ / sqrt 2 < x < sqrt 2 -> 
            Rabs (lh + ll - ln x) <= Rpower 2 (-73.527) * Rabs (ln x)].
  have := @err_lem4 (refl_equal _) rnd valid_rnd x xF xB.
  by rewrite /lh /ll; case: log1.
have ylhB : Rabs (y * lh) <= Rabs rh * (1 + pow (- 52)).
  have rhE : rh = RND (y * lh) by [].
  rewrite rhE in rhB1 *.
  have F1 : Rabs (RND (y * lh) - (y * lh)) <= ulp (RND (y * lh)).
    by apply: error_le_ulp_round.
  have F2 :=  @ulp_FLT_le beta emin p (RND (y * lh)).
  have F3 : Rabs (RND (y * lh) - (y * lh)) <= Rabs (RND (y * lh)) * pow (1 - p).
    suff : pow (emin + p - 1) <= Rabs (RND (y * lh)) by lra.
    apply: Rle_trans rhB1.
    interval.
  have F4 : Rabs (y * lh) - Rabs (RND (y * lh)) <= 
       Rabs (RND (y * lh) - (y * lh)) by clear; split_Rabs; lra.
  clear -F3 F4.
  rewrite [(1 - p)%Z]/= in F3.
  by split_Rabs; lra.
apply: Rle_trans (_ : Rabs (y * lh) * (1 + Rpower 2 (-23.89)) / (1 - eln) <= _)
       ; last first.
  apply: Rmult_le_compat_r; first by apply: Rinv_0_le_compat; lra.
  by apply: Rmult_le_compat_r; first by interval.
rewrite !Rabs_mult [_ / _]Rmult_assoc Rmult_assoc.
apply: Rmult_le_compat_l; first apply: Rabs_pos.
rewrite -Rmult_assoc.
apply: Rle_trans lnxB _.
apply: Rmult_le_compat_r; first by apply: Rinv_0_le_compat; lra.
by split_Rabs; nra.
Qed.


Lemma ylnx_neg :  rh < r0 -> y * ln x <= 0.
Proof.
have [lh0|lh_neq0] := Req_dec lh 0.  
  by rewrite /rh lh0 /= Rmult_0_r round_0; rewrite /r0;lra.
move=> rhB.
case:(Rle_lt_dec (y * ln x) 0) =>// ylnx_pos.
have lnx_neq0 : ln x <> 0 by nra.
suff : 0 <= rh by rewrite /r0 in rhB; lra.
rewrite /rh /=.
have->:  0 = RND 0 by rewrite round_0.
apply/round_le.
suff : 0 <= lh * ln x  by nra.
apply/(Rmult_le_reg_r (Rsqr (/ ln x))).
 by apply/Rlt_0_sqr/Rinv_neq_0_compat.
rewrite Rmult_0_l /Rsqr Rmult_assoc -(Rmult_assoc (ln x)) Rinv_r // 
    Rmult_1_l.
have->: lh * /ln x = lh/ln x by [].
have [llB HH1 HH2] : 
        [/\ Rabs ll <= Rpower 2 (-23.89) * Rabs lh, 
            Rabs (lh + ll - ln x) <= Rpower 2 (-67.0544) * Rabs (ln x) & 
            ~ / sqrt 2 < x < sqrt 2 -> 
            Rabs (lh + ll - ln x) <= Rpower 2 (-73.527) * Rabs (ln x)].
  have := @err_lem4 (refl_equal _) rnd valid_rnd x xF xB.
  by rewrite /lh /ll; case: log1.
have elnB: Rpower 2 (-73.527) <= eln <=  Rpower 2 (-67.0544).
  by rewrite /eln; case:(_ && _); split; try interval;lra.
have hlb1: 0 < 1 - Rpower 2  (-23.89) by interval.
have hlb2: 0 < 1 - Rpower 2 (-67.0544) by interval.
have: Rabs ( (1 + ll / lh) * (lh / ln x)  - 1) <= eln.
  apply/(Rmult_le_reg_r (Rabs (ln x))); first by apply/Rabs_pos_lt.
  rewrite -Rabs_mult Rmult_minus_distr_r Rmult_1_l.
  have->: (1 + ll/lh)*(lh/ln x)* ln x - ln x = (lh + ll - ln x) by field; lra.
  by apply/hllnxB.
set lllh := ll/lh;set lhln:= lh/(ln x).
have:  Rabs (lllh) <= Rpower 2 (-23.89).
  rewrite /lllh Rabs_mult Rabs_inv; apply/(Rmult_le_reg_r (Rabs lh)); first by split_Rabs; lra.
  by rewrite Rmult_assoc Rinv_l ?Rmult_1_r; last by split_Rabs; lra.
move/Rabs_le_inv=> [lllh1 lllh2].
move/Rabs_le_inv=> *.
nra.
Qed.

Lemma xy_alphaB : rh < r0 -> Rpower x y < alpha / 2.
Proof.
move=> rhB.
rewrite /Rpower.
have -> : alpha / 2 = pow (emin - 1).
  by rewrite bpow_plus powN1 /alpha /=; lra.
rewrite pow_Rpower //; apply: exp_increasing.
have ylnx_neg:= (ylnx_neg rhB).
have F : ~ r1 < rh < r2.
  have : r0 < r1 by interval.
  by lra.
have G := ylnxLB F.
move:G.
rewrite - Rabs_Ropp Rabs_pos_eq; last by rewrite /r0 in rhB; lra.
rewrite -Rabs_Ropp Rabs_pos_eq;last by lra.
rewrite /Rdiv !Rmult_assoc Ropp_mult_distr_l_reverse.
move/Ropp_le_cancel.
move=>hh.
apply/(Rle_lt_trans _  
 (rh * ((1 - pow (-52)) * ((1 - Rpower 2 (-23.89)) * / (1 + eln))))); 
   first lra.
have {}rhB : rh <= pred beta fexp r0.
  apply/pred_ge_gt=>//; last by apply/format_r0.
  by apply/generic_format_round.
rewrite pr0fE1 /pr0 in rhB.
have elnB : Rpower 2 (-73.527) <= eln <= Rpower 2 (-67.0544).
  by rewrite /eln; case: (_ && _) => /=; split; try lra; interval.
interval with (i_prec 70).
Qed.

Hypothesis  basic_rnd : (rnd = (Znearest choice) \/ 
                         rnd = Ztrunc \/ rnd = Zaway \/ 
                         rnd = Zfloor \/ rnd = Zceil).
(* Appendix A-L *)
Lemma r1B_phase1_thm1 : rh  < r1 -> u' = v' -> u' = RND (Rpower x y).
Proof.
move=> rhB.
have alphaF: format alpha by apply/generic_format_bpow; rewrite /fexp; lia.
have alpha_pos: 0 < alpha by rewrite /alpha; move: (bpow_gt_0 beta (-1074)); lra.
have apha_pos' : 0 < pow emin by rewrite /emin.
have alpha_2 : alpha / 2 = pow (emin - 1).
  by rewrite bpow_plus powN1 /alpha /=; lra.
have eB : e2 <= e <= e1 by rewrite /e ; case:(_ && _); rewrite /e1 /e2; lra.
rewrite /e1 /e2 in eB.
move=> uv'E; suff h: u' <= RND (Rpower x y) <= v' by lra.
case: (Rlt_le_dec rh r0)=> rhr0.
  have xy_alphaB:= xy_alphaB rhr0.
  have ehE: eh = alpha.
    rewrite /eh /exp1 Rlt_bool_false; last by rewrite /r0 in rhr0; lra.
    rewrite Rlt_bool_true; last by exact:rhr0.
    by rewrite /alpha /beta.
  have elE: el = -alpha.
    rewrite /el /exp1 Rlt_bool_false; last by rewrite /r0 in rhr0; lra.
    rewrite Rlt_bool_true; last by exact:rhr0.
    by rewrite /alpha /beta.
  have uemin: ulp (pow (emin)) = pow (emin).
    rewrite ulp_neq_0  /cexp /fexp.
      by rewrite mag_bpow Z.max_r //.
    by lra.
   have succ0:  succ beta fexp 0 = pow emin.
     by rewrite succ_0 ulp_FLT_0.
  have RND_DN_xy: round beta fexp Zfloor (Rpower x y) = 0.
    apply/round_DN_eq.
      by apply/generic_format_0.
    rewrite succ0; split.
      by rewrite /Rpower; apply/Rlt_le/exp_pos.
    apply/(Rlt_trans _ (pow (emin - 1))); first lra.
    by apply/bpow_lt; lia.
  have RND_UP_xy: round beta fexp Zceil (Rpower x y) = pow emin.
    apply/round_UP_eq.
      by apply/generic_format_bpow; rewrite /fexp; lia.
    rewrite -succ0  pred_succ; last apply/generic_format_0; split.
      by rewrite /Rpower; apply/exp_pos.
    apply/(Rle_trans _ (pow (emin - 1))); first lra.
    by rewrite succ0; apply/bpow_le; lia.
  rewrite /u' /v' ehE elE.
  have h1: -alpha < (- alpha + e * alpha)< 0 by  nra.
  have h2: - 2* alpha < (- alpha - e * alpha) < -alpha by nra.
  have h3: pred beta fexp 0 = - pow emin by rewrite pred_0 ulp_FLT_0.
  split.
    apply/(Rle_trans _ (RND 0) ).
      apply/round_le.
      suff: RND (- alpha - e * alpha) <= - alpha by lra.
      rewrite -[X in _ <= X](round_generic beta fexp).
        by apply/round_le; lra.
      by apply/generic_format_opp.
    by apply/round_le/Rlt_le/exp_pos.
  case: basic_rnd=>[rndE|].
    have->: RND (Rpower x y) = 0.
      rewrite rndE.
      rewrite round_N_eq_DN=>//.
      by rewrite   RND_DN_xy   RND_UP_xy -/alpha; lra.
    have ->: 0 = RND 0 by rewrite round_0.
    apply/round_le.
    suff : -alpha <= RND (- alpha + e * alpha) by lra.
    have {1}-> : -alpha = RND (- alpha) 
      by rewrite round_generic // ;apply/generic_format_opp.
    by apply/round_le; lra.
  move=> rndE.
  suff : u' <> v' by lra.
  rewrite /u' /v'.
  have hepf: round beta fexp Zfloor  (- alpha + e * alpha) = -alpha.
    apply/round_DN_eq; first by apply/generic_format_opp.
    rewrite succ_opp pred_bpow /fexp Z.max_r ; try lra; last lia.
    suff->: (pow (-1074) = pow emin)  by lra.
    by congr bpow; lia.
  have hepc: round beta fexp Zceil  (- alpha + e * alpha) = 0.
    apply/round_UP_eq; first by apply/generic_format_0.
    rewrite pred_0 ulp_FLT_0.
    have ->: pow emin = alpha by [].
    by lra.
  have h4: 2 * alpha = pow (emin + 1).
    have-> : 2 = pow 1 by [].
    by rewrite -bpow_plus; congr bpow; lia.
  have hemf: round beta fexp Zfloor  (- alpha - e * alpha) = - (2*alpha).
    apply/round_DN_eq.
      rewrite h4; apply/generic_format_opp/generic_format_bpow;
      by rewrite /fexp ; lia.
    rewrite succ_opp  h4 pred_bpow /fexp Z.max_r ; try lra; last lia.
    rewrite -h4; have<-: alpha = pow emin by [].
    lra.
  have hemc: round beta fexp Zceil  (- alpha -  e * alpha) = - alpha.
    apply/round_UP_eq; first by apply/generic_format_opp.
    rewrite pred_opp succ_eq_pos.
      split; try lra.
      suff: ulp alpha = alpha by lra.
      by have ->: alpha = pow emin  by [].
    by apply/bpow_ge_0.
  case: rndE=> [->|]; rewrite elE ehE.
    rewrite !(round_generic _ _ _ (alpha + _)) !round_ZR_UP; try lra.
      by rewrite   hepc Rplus_0_r.
    rewrite   hemc.
    have->:  (alpha + - alpha) = 0 by lra.
    by apply/generic_format_0.
  case=> [->|].
    rewrite !(round_generic _ _ _ (alpha + _)) !round_AW_DN; try lra.
      rewrite   hepf.
      have->:  (alpha + - alpha) = 0 by lra.
      by apply/generic_format_0.
    rewrite   hemf.
    have->:  (alpha + - (2 * alpha)) = - alpha  by lra.
    by apply/generic_format_opp.
  case => [->|].
    rewrite hepf hemf !round_generic; first lra.
      have->:(alpha + - alpha) = 0 by lra.
      by apply/generic_format_0.
    have->:  (alpha + - (2 * alpha)) = - alpha by lra.
    by apply/generic_format_opp. 
  move ->.
  rewrite hepc hemc !round_generic; first lra.
    by rewrite Rplus_0_r.
  have->: (alpha + - alpha) = 0 by lra.
  by apply/generic_format_0.
Admitted.

Lemma ulp_omega : ulp omega = pow (emax - p).
Proof.
rewrite ulp_neq_0; last by interval.
congr (pow _); rewrite /cexp /fexp.
rewrite (mag_unique_pos beta _ emax); first lia.
by split; interval with (i_prec 100).
Qed.

Lemma xy_omega : r3 < rh -> omega + ulp (omega) < Rpower x y.
Proof.
move=> r3B.
have -> : omega + ulp (omega) = pow 1024.
  by rewrite ulp_omega /omega bpow_plus /emax; lra.
have ylnxLB : Rabs rh * (1 - pow (- 52)) * (1 - Rpower 2 (-23.89)) / (1 + eln) 
                <= Rabs (y * ln x).
  by apply: ylnxLB; rewrite /r2 /r3 in r3B *; lra.
have r3_43B : r3 + pow (- 43) <= rh.
  have <- : succ beta fexp r3 = r3 + pow (- 43).
    rewrite succ_eq_pos; last by rewrite /r3; interval.
    rewrite ulp_neq_0; last by rewrite /r3; interval.
    congr (_ + pow _).
    rewrite /cexp /fexp.
    rewrite (mag_unique_pos beta _ 10); first lia.
    by split; rewrite /r3; interval.
  apply: succ_le_lt => //; first by apply: format_r3.
  by apply: rhF.
  apply: Rlt_le_trans (_ : exp (709.782712893384) <= _).
    by rewrite /omega /p /emax; interval with (i_prec 100).
  apply: exp_le.
  rewrite -[y * ln x]Rabs_pos_eq.
    apply: Rle_trans ylnxLB.
    have elnB : Rpower 2 (-73.527) <= eln <= Rpower 2 (-67.0544).
      by rewrite /eln; case: (_ && _) => /=; split; try lra; interval.
    rewrite Rabs_pos_eq.
    clear r3B.
    by interval with (i_prec 100).
  by interval.
have [//|ylnx_neg] := Rle_lt_dec 0 (y * ln x).
suff : rh <= 0 by rewrite /r3 in r3B *; lra.
have <- : RND 0 = 0 by apply: round_0.
apply: round_le => //.
have [llB HH1 HH2] : 
      [/\ Rabs ll <= Rpower 2 (-23.89) * Rabs lh, 
          Rabs (lh + ll - ln x) <= Rpower 2 (-67.0544) * Rabs (ln x) & 
          ~ / sqrt 2 < x < sqrt 2 -> 
          Rabs (lh + ll - ln x) <= Rpower 2 (-73.527) * Rabs (ln x)].
  have := @err_lem4 (refl_equal _) rnd valid_rnd x xF xB.
  by rewrite /lh /ll; case: log1.
have [->|lh_neq0] := Req_dec lh 0; first by lra.
have lnx_neq0 : ln x <> 0 by nra.
have F1 : Rabs ((lh + ll)/ ln x - 1) <= Rpower 2 (-67.0544).
  have -> : (lh + ll) / ln x - 1 = (lh + ll - ln x) / ln x by field; lra.
  rewrite Rabs_mult Rabs_inv.
  apply/Rcomplements.Rle_div_l => //.
  by split_Rabs; lra.

have F2 : 1 - Rpower 2 (-67.0544) <= (lh + ll) / ln x <= 1 + Rpower 2 (-67.0544).
  by clear -F1; split_Rabs; lra.
have F3 : (lh + ll) / ln x = (1 + ll / lh) * (lh / ln x).
  by field; lra.
rewrite F3 in F2.
have F4 : Rabs (ll / lh) <= Rpower 2 (-23.89).
  rewrite Rabs_mult Rabs_inv.
  apply/Rcomplements.Rle_div_l => //.
  by clear -lh_neq0; split_Rabs; lra.
have F5 : 1 - Rpower 2 (-23.89) <= 1 + ll / lh <= 1 + Rpower 2 (-23.89).
  by clear -F4; split_Rabs; lra.
have F6 : (1 - Rpower 2 (-67.0544)) / (1 + ll / lh) <= (lh / ln x) <= 
          (1 + Rpower 2 (-67.0544)) / (1 + ll / lh).
  split.
    apply/Rcomplements.Rle_div_l; last by lra.
    case: F5 => FF1 FF2.
    apply: Rlt_gt.
    apply: Rlt_le_trans FF1.
    by interval.
  apply/(Rcomplements.Rle_div_r (lh / ln x)); last by lra.
  case: F5 => FF1 FF2.
  apply: Rlt_gt.
  apply: Rlt_le_trans FF1.
  by interval.
have F7 : (1 - Rpower 2 (-67.0544)) / (1 + Rpower 2 (-23.89)) <= (lh / ln x) <= 
          (1 + Rpower 2 (-67.0544)) / (1 - Rpower 2 (-23.89)).
  case: F6 => FF1 FF2.
  split.
    apply: Rle_trans _ FF1.
    apply: Rmult_le_compat_l; first by interval.
    apply: Rinv_le.
      case: F5 => FF3 FF4.
      apply: Rlt_gt.
      apply: Rlt_le_trans FF3.
      by interval.
    by lra.
  apply: Rle_trans FF2 _.
  apply: Rmult_le_compat_l; first by interval.
  apply: Rinv_le.
    by interval.
  by lra.
have -> : y * lh = y * ln x * (lh / ln x) by field.
suff : 0 <= lh / ln x by clear -ylnx_neg; nra.
apply: Rle_trans (_ : (1 - Rpower 2 (-67.0544)) / (1 + Rpower 2 (-23.89)) <= _).
  by interval.
by lra.
Qed.

(* Appendix A-M *)
Lemma r2B_phase1_thm1 : r2 < rh -> u' = v' -> u' = RND (Rpower x y).
Proof.
move=> rhB.
Admitted.

(* Appendix A-N *)
Lemma r1r2B_phase1_thm1 : r1 <= rh <= r2 -> u' = v' -> u' = RND (Rpower x y).
Proof.
move=> rhB u'Ev'.
have yhB : Rabs (y * lh) <= 709.7827.
  case: (Rle_lt_dec  (Rabs (y * lh)) 709.7827) => // {}yhB.
  suff : r2 < Rabs rh by rewrite  /r1 /r2 in rhB *; split_Rabs; lra.
  apply: Rlt_le_trans (_ : 709.78269 <= _); first by interval.
  apply: Rle_trans (_ : 709.7827 * (1 - pow (- 52)) <= _).
    have -> : 709.7827 = 7097827 / 10000 by lra.
    by interval.
  apply: Rle_trans (_ : Rabs (y * lh) * (1 - pow (- 52)) <= _).
    apply: Rmult_le_compat_r; first by interval.
    by lra.
  apply: relative_error_eps_le => //.
  case: (@format_decomp_prod _ y lh) => // [||m1 [e1 [yhE m1B]]//] //.
  - by apply/generic_format_FLX_FLT/yF.
  - suff /generic_format_FLX_FLT : format lh by [].
    have := @log1_format_h (refl_equal _) _ valid_rnd _ xF.
    by rewrite /lh; case: log1.
  have -> : (3 - 1024 - 53 + 53 - 1 = (-917) - 2 * 53 + 1)%Z by lia.
  apply: is_imul_bound_pow yhE m1B.
  apply: Rle_trans (_ : 709.7827 <= _); first by rewrite /= /Z.pow_pos /=; lra.
  by lra.
have [llB lhllB lhllB1] : 
        [/\ Rabs ll <= Rpower 2 (-23.89) * Rabs lh, 
            Rabs (lh + ll - ln x) <= Rpower 2 (-67.0544) * Rabs (ln x) & 
            ~ / sqrt 2 < x < sqrt 2 -> 
            Rabs (lh + ll - ln x) <= Rpower 2 (-73.527) * Rabs (ln x)].
  have := @err_lem4 (refl_equal _) rnd valid_rnd x xF xB.
  by rewrite /lh /ll; case: log1.
have [ylhB|ylhB] := Rle_lt_dec (pow (- 969)) (Rabs (y * lh)).
  have [rhB1 rlB rlrhB rhrlB [rhrllnB rhrllnB1]] :
        [/\ pow (-970) <= Rabs rh <= 709.79,
            Rabs rl <= Rpower 2 (-14.4187), 
            Rabs (rl / rh) <= Rpower 2 (-23.8899), 
            Rabs (rh + rl) <= 709.79 & 
            Rabs (rh + rl - y * ln x) <= Rpower 2 (-57.580)
            /\ (~ / sqrt 2 < x < sqrt 2 -> Rabs (rh + rl - y * ln x) <= 
            Rpower 2 (-63.799))].
    move: yhB ylhB.
    have := @err_lem5 (refl_equal _) rnd valid_rnd x y xF xB yF.
    rewrite /rh /rl /lh /ll; case: log1 => xh xl; case: mul1 => xh1 xl1 H H1 H2.
    by apply: H.
  have rhF := rhF.
  have rlF := rlF.
  have rhB2 : pow (-970) <= Rabs rh by lra. 
    have [ehelB ehelB1 ehB] :
      [/\    
        Rabs ((eh + el) / exp (rh + rl) - 1) < Rpower 2 (- 63.78597), 
        Rabs (el / eh) <= Rpower 2 (- 49.2999) &
        pow (- 991) <= eh
      ].
    have := @exp1_good_range rnd choice rh rl rhB. 
    have := @err_lem7 (refl_equal _) rnd valid_rnd choice 
               rh rl _ _ rhF rlF rhB2 rhB rlrhB rlB.
    by rewrite /eh /el; case: exp1 => //[] [xh xl] /(_ xh xl (refl_equal _)).
  have elB1 : Rabs el <= Rpower 2 (- 49.2999) * Rabs eh.
    apply/Rcomplements.Rle_div_l; first by interval.
    by rewrite /Rdiv -Rabs_inv -Rabs_mult.
  set r := rh + rl in rhrlB rhrllnB rhrllnB1 ehelB.
  have ehelrB : Rabs (eh + el - exp r) < Rpower 2 (- 63.78597) *  exp r.
    apply/Rcomplements.Rlt_div_l; first by apply: exp_pos.
    rewrite -{2}[exp r]Rabs_pos_eq; last by apply/Rlt_le/exp_pos.
    rewrite /Rdiv -Rabs_inv -Rabs_mult.
    suff <- : (eh + el) / exp r - 1 = (eh + el - exp r) * / exp r by [].
    field; suff : 0 < exp r by lra.
    by apply: exp_pos.
  set s := r - y * ln x in rhrllnB rhrllnB1.
  have  exxyB : Rabs (exp r - Rpower x y) <= Rabs (exp (- s) - 1) * exp r.
    suff : Rabs (exp r - Rpower x y) = Rabs (exp (- s) - 1) * exp r by lra.
    rewrite -{2}[exp r]Rabs_pos_eq; last by apply/Rlt_le/exp_pos.
    rewrite -Rabs_mult -Rabs_Ropp Ropp_minus_distr; congr Rabs.
    have -> : (exp (-s) - 1) * exp r = exp (-s + r) - exp r.
      by rewrite exp_plus; lra.
    have -> : -s + r = y * ln x by rewrite /s; lra.
    by [].
  have  ehelxyB :
     Rabs (eh + el - Rpower x y) <=
       (Rpower 2 (- 63.78597 ) + Rabs (exp (- s) - 1)) * exp r.
    have -> : eh + el - Rpower x y = (eh + el - exp r) + (exp r - Rpower x y).
      by lra.
    have -> : (Rpower 2 (-63.78597) + Rabs (exp (- s) - 1)) * exp r =
              Rpower 2 (-63.78597) * exp r + Rabs (exp (- s) - 1) * exp r.
      by lra.
    by boundDMI => //; lra.
  have ehelxyB1 : Rabs (eh + el - Rpower x y) <= Rpower 2 (- 57.5605) * exp r.
    apply: Rle_trans ehelxyB _.
    apply: Rmult_le_compat_r; first by apply/Rlt_le/exp_pos.
    have F : Rabs (exp (- s) - 1) <= Rabs (exp (Rpower 2 (-57.580)) - 1).
      clear -rhrllnB .
      set  B := Rpower 2 (- 57.580) in rhrllnB *.
      have eB : exp (- B) - 1 <= exp (- s) - 1 <= exp B - 1.
        suff: exp (- B) <= exp (- s) <= exp B by lra.
        split; first by apply: exp_le; split_Rabs; lra.
        by apply: exp_le; split_Rabs; lra.
      have F2 : Rabs (exp (- B) - 1) < Rabs (exp B - 1).
        by rewrite /B; interval with (i_prec 150).
      clear - eB F2; split_Rabs; lra.
    apply: Rle_trans (_ : Rpower 2 (-63.78597) + Rabs (exp (Rpower 2 (-57.580)) - 1) <= _).
      lra.
    by interval with (i_prec 100).
  have ehelxyB2 : ~ / sqrt 2 < x < sqrt 2 -> 
                    Rabs (eh + el - Rpower x y) <= Rpower 2 (- 62.7924) * exp r.
    move=> /rhrllnB1 {}rhrllnB.
    apply: Rle_trans ehelxyB _.
    apply: Rmult_le_compat_r; first by apply/Rlt_le/exp_pos.
    have F : Rabs (exp (- s) - 1) <= Rabs (exp (Rpower 2 (-63.799)) - 1).
      clear -rhrllnB .
      set  B := Rpower 2 (- 63.799) in rhrllnB *.
      have eB : exp (- B) - 1 <= exp (- s) - 1 <= exp B - 1.
        suff: exp (- B) <= exp (- s) <= exp B by lra.
        split; first by apply: exp_le; split_Rabs; lra.
        by apply: exp_le; split_Rabs; lra.
      have F2 : Rabs (exp (- B) - 1) < Rabs (exp B - 1).
        by rewrite /B; interval with (i_prec 150).
      clear - eB F2; split_Rabs; lra.
    apply: Rle_trans (_ : Rpower 2 (-63.78597) +
                          Rabs (exp (Rpower 2 (- 63.799)) - 1) <= _).
      lra.
    by interval with (i_prec 100).
  have ehelxyB3 : Rabs (eh + el - Rpower x y) <= mu * exp r.
    have [xB1|xB1]:= Rle_lt_dec x (sqrt 2 / 2).
      rewrite muNI; last by lra.
      by apply: ehelxyB2; rewrite -hsqrt2sqrt; lra.
    have [xB2|xB2]:= Rle_lt_dec (sqrt 2) x.
      rewrite muNI; last by lra.
      by apply: ehelxyB2; rewrite -hsqrt2sqrt; lra.
    rewrite muI; last by lra.
    by apply: ehelxyB1; lra.
  have erB : exp r < (1 + Rpower 2 (- 49.2999)) / (1 - Rpower 2 (- 63.78597)) *
                     Rabs eh.
    apply: Rlt_le_trans
       (_ : / (1 - Rpower 2 (- 63.78597 )) * Rabs (eh + el) <= _).
      clear -ehelB.
      rewrite Rmult_comm.
      apply/Rcomplements.Rlt_div_r; first by interval.
      suff : Rabs ((eh + el) - exp r) < Rpower 2 (-63.78597) * exp r.
        by split_Rabs; lra.
      apply/Rcomplements.Rlt_div_l; first by apply: exp_pos.
      rewrite -{2}[exp r]Rabs_pos_eq; last by apply/Rlt_le/exp_pos.
      rewrite /Rdiv -Rabs_inv -Rabs_mult.
      suff <- : (eh + el) / exp r - 1 = (eh + el - exp r) * / exp r by [].
      field.
      suff : 0 < exp r by lra.
      by apply: exp_pos.
    rewrite [_/_]Rmult_comm Rmult_assoc.
    apply: Rmult_le_compat_l; first by interval.
    by clear -elB1; split_Rabs; lra.
  have ehelxyB4 : Rabs ((eh + el) - Rpower x y) <= Rpower 2 (- 57.5604) * eh.
    apply: Rle_trans ehelxyB1 _.
    apply: Rle_trans (_ : Rpower 2 (-57.5605) * 
                          (1 + Rpower 2 (-49.2999)) / (1 - Rpower 2 (-63.78597)) 
                          * Rabs eh <= _).
      rewrite !Rmult_assoc; apply: Rmult_le_compat_l; first by interval.
      by rewrite -Rmult_assoc; lra.
    rewrite Rabs_pos_eq; last by interval.
    by apply: Rmult_le_compat_r; interval.
  have ehelxyB5 : ~ / sqrt 2 < x < sqrt 2 -> 
                Rabs ((eh + el) - Rpower x y) <= Rpower 2 (- 62.7923) * eh.
    move=> /ehelxyB2 {}ehelxyB1.
    apply: Rle_trans ehelxyB1 _.
    apply: Rle_trans (_ : Rpower 2 (- 62.7924) * 
                          (1 + Rpower 2 (-49.2999)) / (1 - Rpower 2 (-63.78597)) 
                          * Rabs eh <= _).
      rewrite !Rmult_assoc; apply: Rmult_le_compat_l; first by interval.
      by rewrite -Rmult_assoc; lra.
    rewrite Rabs_pos_eq; last by interval.
    by apply: Rmult_le_compat_r; interval.
  have ehelxyB6 : Rabs ((eh + el) - Rpower x y) <= tau * eh.
    have [xB1|xB1]:= Rle_lt_dec x (sqrt 2 / 2).
      rewrite tauNI; last by lra.
      by apply: ehelxyB5; rewrite -hsqrt2sqrt; lra.
    have [xB2|xB2]:= Rle_lt_dec (sqrt 2) x.
      rewrite tauNI; last by lra.
      by apply: ehelxyB5; rewrite -hsqrt2sqrt; lra.
    rewrite tauI; last by lra.
    by apply: ehelxyB4; lra.
  pose u1' := el - e * eh.
  pose v1' := el + e * eh.
  have eB : tau + pow (- 83) <= e <= 2 * tau.
    have [xB1|xB1]:= Rle_lt_dec x (sqrt 2 / 2).
      rewrite eNI ?tauNI -?e2E; try by lra.
      by interval.
    have [xB2|xB2]:= Rle_lt_dec (sqrt 2) x.
      rewrite tauNI; last by lra.
      rewrite eNI ?tauNI -?e2E; try by lra.
      by interval.
    rewrite eI ?tauI -?e1E; try by lra.
    by interval with (i_prec 100).
  suff : u' <= RND (Rpower x y) <= v' by lra.
  split.
    apply: Rle_trans (_ : RND (eh + el - tau * eh) <= _); last first.
      apply: round_le.
      by clear -ehelxyB6; split_Rabs; lra.
    apply: round_le.
    suff : RND (u1') <= el - tau * eh by rewrite /u1'; lra.
    apply: Rle_trans (_ : u1' + ulp u1' <= _).
      suff : Rabs (RND u1' - u1') <= ulp u1'.
        by clear; split_Rabs; lra.
      by apply: error_le_ulp.
    suff : ulp u1' <= (e - tau) * eh by rewrite /u1'; lra.
    apply: Rle_trans (_ : pow (- 83) * eh <= _); last first.
      apply: Rmult_le_compat_r; first by interval.
      by lra.
    have u1'B : Rabs u1' <= Rpower 2 (- 49.2905) * eh.
      apply: Rle_trans (_ : Rabs el + e * eh <= _).
        suff : 0 <= e * eh.
          by rewrite /u1'; clear; split_Rabs; lra.
        by rewrite /e; do 2 case: Rlt_bool => //=; interval.
      apply: Rle_trans (_ : (Rpower 2 (- 49.2999) + 2 * tau) * eh <= _); 
          last first.
        apply: Rmult_le_compat_r; first by interval.
        by rewrite /tau; do 2 case: Rlt_bool => //=; interval.
      have -> : (Rpower 2 (-49.2999) + 2 * tau) * eh = 
                 Rpower 2 (-49.2999) * eh + 2 * tau * eh by lra.
      apply: Rplus_le_compat.
        by rewrite -[eh]Rabs_pos_eq; [lra|interval].
      by apply: Rmult_le_compat_r; [interval | lra].
    have [pLu1'|u1'Lp] := Rle_dec (pow (emin + p - 1)) (Rabs u1'). 
      apply: Rle_trans (_ : Rabs u1' * pow (1 - p) <= _).
        by apply: ulp_FLT_le.
      apply: Rle_trans (_ : Rpower 2 (-49.2905) * eh * pow (1 - p) <= _).
        by apply: Rmult_le_compat_r; first by interval.
      rewrite Rmult_comm -Rmult_assoc.
      apply: Rmult_le_compat_r; first by interval.
      by interval.
    rewrite ulp_subnormal //; first by interval with (i_prec 100).
    rewrite [(_ + _)%Z]/=; rewrite [(_ - _)%Z]/= in u1'Lp.
    apply: Rle_lt_trans (_ : pow (- 1022) < _); first by lra.
    by apply: bpow_lt; lia.
  apply: Rle_trans (_ : RND (eh + el + tau * eh) <= _).
    apply: round_le.
    by clear -ehelxyB6; split_Rabs; lra.
  apply: round_le.
  suff : el + tau * eh <= RND (v1') by rewrite /v1'; lra.
  apply: Rle_trans (_ : v1' - ulp v1' <= _); last first.
    suff : Rabs (RND v1' - v1') <= ulp v1'.
      by clear; split_Rabs; lra.
    by apply: error_le_ulp.
  suff : ulp v1' <= (e - tau) * eh by rewrite /v1'; lra.
  apply: Rle_trans (_ : pow (- 83) * eh <= _); last first.
    apply: Rmult_le_compat_r; first by interval.
    by lra.
  have v1'B : Rabs v1' <= Rpower 2 (- 49.2905) * eh.
    apply: Rle_trans (_ : Rabs el + e * eh <= _).
      suff : 0 <= e * eh.
        by rewrite /v1'; clear; split_Rabs; lra.
      by rewrite /e; do 2 case: Rlt_bool => //=; interval.
    apply: Rle_trans (_ : (Rpower 2 (- 49.2999) + 2 * tau) * eh <= _); 
        last first.
      apply: Rmult_le_compat_r; first by interval.
      by rewrite /tau; do 2 case: Rlt_bool => //=; interval.
    have -> : (Rpower 2 (-49.2999) + 2 * tau) * eh = 
                Rpower 2 (-49.2999) * eh + 2 * tau * eh by lra.
    apply: Rplus_le_compat.
      by rewrite -[eh]Rabs_pos_eq; [lra|interval].
    by apply: Rmult_le_compat_r; [interval | lra].
  have [pLv1'|v1'Lp] := Rle_dec (pow (emin + p - 1)) (Rabs v1'). 
    apply: Rle_trans (_ : Rabs v1' * pow (1 - p) <= _).
      by apply: ulp_FLT_le.
    apply: Rle_trans (_ : Rpower 2 (-49.2905) * eh * pow (1 - p) <= _).
      by apply: Rmult_le_compat_r; first by interval.
    rewrite Rmult_comm -Rmult_assoc.
    apply: Rmult_le_compat_r; first by interval.
    by interval.
  rewrite ulp_subnormal //; first by interval with (i_prec 100).
  rewrite [(_ + _)%Z]/=; rewrite [(_ - _)%Z]/= in v1'Lp.
  apply: Rle_lt_trans (_ : pow (- 1022) < _); first by lra.
  by apply: bpow_lt; lia.
have rhB1 : Rabs rh <= pow (- 969).
  apply: Rabs_round_le => //.
  by apply: Rlt_le.
have rlB : Rabs rl <= pow (- 992).
  rewrite /rl [Rabs _]/=.
  set s := y * lh - rh.
  have sB : Rabs (RND s) <= pow (- 1022).
    apply: Rabs_round_le => //.
    have -> : Rabs s = Rabs (rh - y * lh).
      by clear; rewrite /s; split_Rabs; lra.
    apply: Rle_trans (_ : ulp (y * lh) <= _); first by apply: error_le_ulp.
    by apply: bound_ulp.
  have yll : Rabs (y * ll) < Rpower 2 (- 992.89).
    rewrite Rabs_mult.
    apply: Rle_lt_trans (_ : Rabs y * (Rpower 2 (-23.89) * Rabs lh) < _).
      by apply: Rmult_le_compat_l => //; apply: Rabs_pos.
    rewrite Rmult_comm Rmult_assoc -Rabs_mult [lh * _]Rmult_comm.
    have -> : -992.89 = (- 23.89) + (-969) by lra.
    rewrite Rpower_plus.
    apply: Rmult_lt_compat_l => //; first by interval.
    by rewrite -pow_Rpower.
  have ylsB : Rabs (y * ll + RND s) <= Rpower 2 (- 992.88).
    apply: Rle_trans (_ : Rpower 2 (- 992.89) + pow (- 1022) <= _);
        last by interval.
    by boundDMI; first by lra.
  rewrite -[round _ _ _ _]/(RND _) -[round _ _ _ s]/(RND _).
  apply: Rle_trans (_ : Rpower 2 (- 992.88) * (1 + pow (- 52)) <= _);
      last by interval.
  have [pLy|yLp] := 
      Rle_dec (bpow beta (emin + p - 1)) (Rabs (y * ll + RND s)). 
    apply: Rle_trans (_ : Rabs (y * ll + RND s) * (1 + pow (- 52)) <= _).
      by apply/Rlt_le/relative_error_FLT_alt.
    by apply: Rmult_le_compat_r; first by interval.
  apply: Rle_trans (_ : pow (emin + p - 1) <= _); last by interval.
  apply: Rabs_round_le  => //.
  by rewrite -[bpow _ _]/(pow _); lra.
pose k := Znearest choice (RND (rh * INVLN2)).
have k_eq0 : k = 0%Z.
  apply: Znearest_imp.
  apply: Rle_lt_trans (_ : pow (- 2) < _); last by interval.
  rewrite !Rsimp01.
  apply: Rabs_round_le => //.
  rewrite Rabs_mult.
  set xx := Rabs _ in rhB1 *.
  by interval.
pose zh := RND (rh - IZR k * LN2H).
have zhE : zh = rh.
  by rewrite /zh k_eq0 !Rsimp01 round_generic //; apply: rhF.
pose zl := RND (rl - IZR k * LN2L).
have zlE : zl = rl.
  by rewrite /zl k_eq0 !Rsimp01 round_generic //; apply: rlF.
pose z := RND (zh + zl).
have zE : z = RND (rh + rl) by rewrite /z zhE zlE.
have zB : Rabs z <= Rpower 2 (- 968.9).
  rewrite zE.
  have [pLy|yLp] := 
      Rle_dec (bpow beta (emin + p - 1)) (Rabs (rh + rl)). 
    apply: Rle_trans (_ : Rabs (rh + rl) * (1 + pow (- 52)) <= _).
      by apply/Rlt_le/relative_error_FLT_alt.
    by interval.
  apply: Rle_trans (_ : pow (emin + p - 1) <= _); last by interval.
  apply: Rabs_round_le  => //.
  by rewrite -[bpow _ _]/(pow _); lra.
pose e := (k / 2 ^ 12)%Z.
have eE : e = 0%Z by rewrite /e k_eq0.
pose i2 := ((k - e * 2 ^ 12) / 2 ^ 6)%Z.
have i2E : i2 = 0%Z by rewrite /i2 k_eq0 eE.
pose i1 := ((k - e * 2 ^ 12 - i2 * 2 ^ 6))%Z.
have i1E : i1 = 0%Z by rewrite /i1 k_eq0 eE i2E.
pose h2 := (nth (0,0) T1 (Z.to_nat i2)).1.
have h2E : h2 = 1 by rewrite /h2 i2E.
pose l2 := (nth (0,0) T1 (Z.to_nat i2)).2.
have l2E : l2 = 0 by rewrite /l2 i2E.
pose h1 := (nth (0,0) T2 (Z.to_nat i1)).1.
have h1E : h1 = 1 by rewrite /h1 i1E.
pose l1 := (nth (0,0) T2 (Z.to_nat i1)).2.
have l1E : l1 = 0 by rewrite /l1 i1E.
pose ph := let 'DWR ph s := exactMul h1 h2 in ph.
have phE : ph = 1.
  rewrite /ph h1E h2E /exactMul /= ?Rsimp01.
  by apply: round_generic; apply: format1.
pose s := let 'DWR ph s := exactMul h1 h2 in s.
have sE : s = 0.
  rewrite /s h1E h2E /exactMul /= ?Rsimp01.
  rewrite [round _ _ _ 1]round_generic ?Rsimp01.
    by apply: round_0.
  by apply: format1.
pose t := RND (l1 * h2 + s).
have tE : t = 0 by rewrite /t l1E h2E sE !Rsimp01 round_0.
pose pl := RND (h1 * l2 + t).
have plE : pl = 0 by rewrite /pl h1E l2E tE !Rsimp01 round_0.
pose qh := let 'DWR qh ql := q1 z in qh.
pose ql := let 'DWR qh ql := q1 z in ql.
pose h := let 'DWR h s := exactMul ph qh in h.
have hE : h = qh.
  by rewrite /h phE /= !Rsimp01 round_generic //; apply: generic_format_round.
pose s' := let 'DWR h s := exactMul ph qh in s.
have s'E : s' = 0.
  rewrite /s' /= phE !Rsimp01 [round _ _ _ qh] round_generic.
    by rewrite !Rsimp01 round_0.
  by apply: generic_format_round.
pose t' := RND (pl * qh + s').
have t'E : t' = 0 by rewrite /t' s'E plE !Rsimp01 round_0.
pose l' := RND (ph * ql + t').
have l'E : l' = ql.
  rewrite /l' t'E phE !Rsimp01 round_generic //.
  by apply: generic_format_round.
have ehE : eh = qh.
  rewrite /eh /exp1 -/k.
  case: Rlt_bool_spec => [|_].
    have : rh <= 0x1.62e4316ea5df9p9%xR by rewrite /r1 /r2 in rhB; lra.
    by lra.
  case: Rlt_bool_spec => [|_].
    have : (-0x1.74910ee4e8a27p9)%xR  <= rh by rewrite /r1 /r2 in rhB; lra.
    by lra.
  case: Rlt_bool_spec => [|_].
    have : (-0x1.577453f1799a6p9)%xR <= rh <= rh by rewrite /r1 /r2 in rhB; lra.
    by lra.
  rewrite [false || _]/=.
  case: Rlt_bool_spec => [|_].
    have : rh <= 0x1.62e42e709a95bp9%xR by rewrite /r1 /r2 in rhB; lra.
    by lra.
  case E : nth => [xx yy].
  have -> : xx = h2 by rewrite /h2; case: nth E => /= ? ? [].
  have -> : yy = l2 by rewrite /l2; case: nth E => /= ? ? [].
  case E1 : nth => [xx1 yy1].
  have -> : xx1 = h1 by rewrite /h1; case: nth E1 => /= ? ? [].
  have -> : yy1 = l1 by rewrite /l1; case: nth E1 => /= ? ? [].
  case E2 : exactMul => [xx2 yy2].
  have -> : xx2 = ph by rewrite /ph; case: exactMul E2 => /= ? ? [].
  have -> : yy2 = s by rewrite /s; case: exactMul E2 => /= ? ? [].
  case E3 : q1 => [xx3 yy3].
  have -> : xx3 = qh by rewrite /qh; case: q1 E3 => /= ? ? [].
  have -> : yy3 = ql by rewrite /ql; case: q1 E3 => /= ? ? [].
  case E4 : exactMul => [xx4 yy4].
  have -> : xx4 = h by rewrite /h; case: exactMul E4 => /= ? ? [].
  rewrite k_eq0 pow0E !Rsimp01 round_generic //.
  by apply: generic_format_round.
have elE : el = ql.
  rewrite /el /exp1 -/k.
  case: Rlt_bool_spec => [|_].
    have : rh <= 0x1.62e4316ea5df9p9%xR by rewrite /r1 /r2 in rhB; lra.
    by lra.
  case: Rlt_bool_spec => [|_].
    have : (-0x1.74910ee4e8a27p9)%xR  <= rh by rewrite /r1 /r2 in rhB; lra.
    by lra.
  case: Rlt_bool_spec => [|_].
    have : (-0x1.577453f1799a6p9)%xR <= rh <= rh by rewrite /r1 /r2 in rhB; lra.
    by lra.
  rewrite [false || _]/=.
  case: Rlt_bool_spec => [|_].
    have : rh <= 0x1.62e42e709a95bp9%xR by rewrite /r1 /r2 in rhB; lra.
    by lra.
  case E : nth => [xx yy].
  have -> : xx = h2 by rewrite /h2; case: nth E => /= ? ? [].
  have -> : yy = l2 by rewrite /l2; case: nth E => /= ? ? [].
  case E1 : nth => [xx1 yy1].
  have -> : xx1 = h1 by rewrite /h1; case: nth E1 => /= ? ? [].
  have -> : yy1 = l1 by rewrite /l1; case: nth E1 => /= ? ? [].
  case E2 : exactMul => [xx2 yy2].
  have -> : xx2 = ph by rewrite /ph; case: exactMul E2 => /= ? ? [].
  have -> : yy2 = s by rewrite /s; case: exactMul E2 => /= ? ? [].
  case E3 : q1 => [xx3 yy3].
  have -> : xx3 = qh by rewrite /qh; case: q1 E3 => /= ? ? [].
  have -> : yy3 = ql by rewrite /ql; case: q1 E3 => /= ? ? [].
  case E4 : exactMul => [xx4 yy4].
  have -> : yy4 = s' by rewrite /s'; case: exactMul E4 => /= ? ? [].
  rewrite k_eq0 pow0E !Rsimp01 round_generic //.
  by apply: generic_format_round.
Admitted.

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

Hypothesis  basic_rnd : (rnd = (Znearest choice) \/ 
                         rnd = Ztrunc \/ rnd = Zaway \/ 
                         rnd = Zfloor \/ rnd = Zceil).

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Local Notation ulp := (ulp beta fexp).


(* Algo Phase 1 *)

Local Notation " x <? y " := (Rlt_bool x y).
Local Notation FAIL := None.
Local Notation R_UP := (round beta fexp Zceil).
Local Notation R_DN := (round beta fexp Zfloor).
Local Notation " x =? y " := (Req_bool x y).

Definition phase1 (x y : R) := 
  let l := log1 x in 
  let r := mul1 l y in 
  if exp1 r is some (DWR eh el) then
    let e := 
      if (0x1.6a09e667f3bccp-1 <? x) && (x <? 0x1.6a09e667f3bcdp+0) then 
        0x1.5b4a6bd3fff4ap-58 else 0x1.27b3b3b4bb6dfp-63 in 
    let u := RND (eh + RND (el - e * eh)) in 
    let v := RND (eh + RND (el + e * eh)) in
      if (u =? v) then some u else FAIL
  else FAIL.

(* This is theorem 1 *)

Lemma phase1_thn1 x y r :
  format x -> format y -> alpha <= x <= omega -> 
  phase1 x y = some r -> r = RND (Rpower x y). 
Proof.
move=> xB yB x_pos; rewrite /phase1.
case E : log1 => [lh ll].
have lhE : lh = algoPhase1.lh rnd x.
  by rewrite /algoPhase1.lh; case: log1 E => ? ? [].
have llE : ll = algoPhase1.ll rnd x.
  by rewrite /algoPhase1.ll; case: log1 E => ? ? [].
case E1 : mul1 => [rh rl].
have rhE : rh = algoPhase1.rh rnd x y.
  by rewrite /algoPhase1.rh -llE -lhE; case: mul1 E1 => ? ? [].
have rlE : rl = algoPhase1.rl rnd x y.
  by rewrite /algoPhase1.rl -llE -lhE; case: mul1 E1 => ? ? [].
case E2 : exp1 => [[eh el]|]; last by discriminate.
have ehE : eh = algoPhase1.eh rnd choice x y.
  rewrite /algoPhase1.eh -rhE -rlE; case: exp1 E2 => [[xh xl]|];
    last by discriminate.
  by case.
have elE : el = algoPhase1.el rnd choice x y.
  rewrite /algoPhase1.el -rhE -rlE; case: exp1 E2 => [[xh xl]|];
    last by discriminate.
  by case.
set e := if _ && _ then _ else _.
have eE : e = algoPhase1.e x by [].
case: Req_bool_spec => //.
set u' := RND _; set v' := RND _ => u'Ev' [<-].
have u'E : u' = algoPhase1.u' rnd choice x y.
  by rewrite /algoPhase1.u' -ehE -elE -eE.
have v'E : v' = algoPhase1.v' rnd choice x y.
  by rewrite /algoPhase1.v' -ehE -elE -eE.
have [r1Lrh|rhLr1] := Rle_dec r1 rh; last first.
  rewrite u'E.
  apply: r1B_phase1_thm1 => //.
    by rewrite -rhE; lra.
  by rewrite -u'E -v'E.
have [rhLr2|r2Lrh] := Rle_dec rh r2.
  rewrite u'E.
  apply: r1r2B_phase1_thm1 => //.
    by rewrite -rhE; lra.
  by rewrite -u'E -v'E.
rewrite u'E.
apply: r2B_phase1_thm1 => //.
  by rewrite -rhE; lra.
by rewrite -u'E -v'E.
Qed.

End algoPhase1.

