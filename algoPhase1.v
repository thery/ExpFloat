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

Definition eh := let 'DWR eh _  := exp1 (DWR rh rl) in eh.
Definition el := let 'DWR _  el := exp1 (DWR rh rl) in el.

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

Definition u' := RND (eh + RND (el - e * eh)).
Definition v' := RND (eh + RND (el + e * eh)).

(* Appendix A-L *)
Lemma r1B_phase1_thm1 : rh < r1 -> u' = v' -> u' = RND (Rpower x y).
Proof.
Admitted.

(* Appendix A-M *)
Lemma r2B_phase1_thm1 : r2 < rh -> u' = v' -> u' = RND (Rpower x y).
Proof.
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
have [ylhB|ylhB] := Rle_lt_dec (pow (- 969)) (Rabs (y * lh)).
  have [llB lhllB lhllB1] : 
          [/\ Rabs ll <= Rpower 2 (-23.89) * Rabs lh, 
              Rabs (lh + ll - ln x) <= Rpower 2 (-67.0544) * Rabs (ln x) & 
              ~ / sqrt 2 < x < sqrt 2 -> 
              Rabs (lh + ll - ln x) <= Rpower 2 (-73.527) * Rabs (ln x)].
    have := @err_lem4 (refl_equal _) rnd valid_rnd x xF xB.
    by rewrite /lh /ll; case: log1.
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
  have rhF : format rh by admit.
  have rlF : format rl by admit.
  have rhB2 : pow (-970) <= Rabs rh by lra. 
    have [ehelB ehelB1 ehB] :
      [/\    
        Rabs ((eh + el) / exp (rh + rl) - 1) < Rpower 2 (- 63.78597), 
        Rabs (el / eh) <= Rpower 2 (- 49.2999) &
        pow (- 991) <= eh
      ].
    have := @err_lem7 (refl_equal _) rnd valid_rnd choice 
               rh rl rhF rlF rhB2 rhB rlrhB rlB.
    by rewrite /eh /el; case: exp1 => xh xl.
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
    suff : Rabs el <= Rpower 2 (- 49.2999) * Rabs eh.
      by clear; split_Rabs; lra.
    apply/Rcomplements.Rle_div_l; first by interval.
    by rewrite /Rdiv -Rabs_inv -Rabs_mult.
  have ehelxyB3 : Rabs ((eh + el) - Rpower x y) <= Rpower 2 (- 57.5604) * eh.
    apply: Rle_trans ehelxyB1 _.
    apply: Rle_trans (_ : Rpower 2 (-57.5605) * 
                          (1 + Rpower 2 (-49.2999)) / (1 - Rpower 2 (-63.78597)) 
                          * Rabs eh <= _).
      rewrite !Rmult_assoc; apply: Rmult_le_compat_l; first by interval.
      by rewrite -Rmult_assoc; lra.
    rewrite Rabs_pos_eq; last by interval.
    by apply: Rmult_le_compat_r; interval.
  have ehelxyB4 : ~ / sqrt 2 < x < sqrt 2 -> 
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

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Local Notation ulp := (ulp beta fexp).


(* Algo Phase 1 *)

Definition Nan := omega + 1.
Local Notation " x <? y " := (Rlt_bool x y).
Local Notation FAIL := None.
Local Notation R_UP := (round beta fexp Zceil).
Local Notation R_DN := (round beta fexp Zfloor).
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
case E2 : exp1 => [eh el].
have ehE : eh = algoPhase1.eh rnd choice x y.
  by rewrite /algoPhase1.eh -rhE -rlE; case: exp1 E2 => ? ? [].
have elE : el = algoPhase1.el rnd choice x y.
  by rewrite /algoPhase1.el -rhE -rlE; case: exp1 E2 => ? ? [].
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

