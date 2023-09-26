Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Interval Require Import Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim algoLog1 algoMul1.
Require Import Fast2Sum_robust_flt algoQ1.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section algoExp1.

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
Context { valid_rnd : Valid_rnd rnd }.

Local Notation float := (float radix2).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format radix2 fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation fastTwoSum := (fastTwoSum rnd).
Local Notation exactMul := (exactMul rnd).
Local Notation fastSum := (fastSum rnd).

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Local Notation ulp := (ulp beta fexp).

Definition INVLN2 := 0x1.71547652b82fep+12.

Lemma format_INVLN2 : format INVLN2.
Proof.
have -> : INVLN2 = Float beta 6497320848556798 (- 40).
  by rewrite /F2R /INVLN2 /=; lra.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma INVLN2B : Rabs (INVLN2 - pow 12 / ln 2) < Rpower 2 (- 43.447).
Proof. by interval with (i_prec 70). Qed. 

Definition LN2H := 0x1.62e42fefa39efp-13.

Lemma format_LN2H : format LN2H.
Proof.
have -> : LN2H = Float beta 6243314768165359 (- 65).
  by rewrite /F2R /LN2H /=; lra.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Definition LN2L := 0x1.abc9e3b39803fp-68.

Lemma format_LN2L : format LN2L.
Proof.
have -> : LN2L = Float beta 7525737178955839 (- 120).
  by rewrite /F2R /LN2L /=; lra.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma LN2HLB : Rabs (LN2H + LN2L - ln 2 * pow (- 12)) < Rpower 2 (- 122.43).
Proof. by rewrite /LN2H /LN2L; interval with (i_prec 150). Qed.

Lemma imul_INVLN2 : is_imul INVLN2 (pow (- 40)).
Proof.
have -> : INVLN2 = Float beta 6497320848556798 (- 40).
  by rewrite /F2R /INVLN2 /=; lra.
by exists 6497320848556798%Z; rewrite /F2R /INVLN2 /=; lra.
Qed.

Lemma imul_LN2H : is_imul LN2H (pow (- 65)).
Proof.
have -> : LN2H = Float beta 6243314768165359 (- 65).
  by rewrite /F2R /LN2H /=; lra.
by exists 6243314768165359%Z; rewrite /F2R /INVLN2 /=; lra.
Qed.

Lemma imul_LN2L : is_imul LN2L (pow (- 120)).
Proof.
have -> : LN2L = Float beta 7525737178955839 (- 120).
  by rewrite /F2R /LN2L /=; lra.
by exists 7525737178955839%Z; rewrite /F2R /INVLN2 /=; lra.
Qed.

Variables rh rl : R.
Hypothesis rhF : format rh.
Hypothesis rlF : format rl.
Hypothesis rhB : pow (- 970) <= Rabs rh <= 709.79.
Hypothesis rlB : Rabs rl <= Rpower 2 (-14.4187).
Hypothesis rhDrlB : Rabs (rl / rh) <= Rpower 2 (- 23.8899).
Hypothesis rhlB : Rabs (rh + rl) <= 709.79.

Definition k := ZnearestE (RND (rh * INVLN2)).

Lemma Zfloor_opp k : Zfloor (- k) = (- Zceil k)%Z.
Proof. by rewrite /Zceil /Zfloor; lia. Qed.

Lemma Zceil_opp k : Zceil (- k) = (- Zfloor k)%Z.
Proof. by rewrite /Zceil /Zfloor Ropp_involutive; lia. Qed.

Lemma Znearest_le c r1 r2 : 
  r1 <= r2 -> (Znearest c r1 <= Znearest c r2)%Z.
Proof. by case: (valid_rnd_N c) => H _; exact: H. Qed.

Lemma Znearest_IZR c k : Znearest c (IZR k) = k.
Proof. by case: (valid_rnd_N c) => _ H; exact: H. Qed.

Lemma ZnearestE_opp r : ZnearestE (- r) = (- ZnearestE r)%Z.
Proof.
have [<-|zNE] := Req_dec (IZR (Zfloor r)) r.
  by rewrite -opp_IZR ![ZnearestE (IZR _)]Znearest_IZR.
rewrite [in RHS]/ZnearestE; case: Rcompare_spec => H.
- have rE : /2 < - r - IZR (Zfloor (- r)).
    rewrite Zfloor_opp Zceil_floor_neq // opp_IZR plus_IZR; lra.
  rewrite /ZnearestE; case: Rcompare_spec; try lra.
  by rewrite Zceil_opp; lia.
- have rE : - r = IZR (Zfloor (- r)) + / 2.
   by rewrite Zfloor_opp Zceil_floor_neq // opp_IZR plus_IZR; lra.
  rewrite /Znearest; case: Rcompare_spec; (try by lra) => _.
  rewrite Zfloor_opp Zceil_floor_neq; last by lra.
  by rewrite Z.even_opp Z.even_add Zceil_opp /=; case: Z.even => /=; lia.
have rE : - r - IZR (Zfloor (- r)) < /2.
  by rewrite Zfloor_opp Zceil_floor_neq // opp_IZR plus_IZR; lra.
  rewrite /ZnearestE; case: Rcompare_spec; try lra.
by rewrite Zfloor_opp.
Qed.

Lemma ZnearestE_le_abs r1 r2 : 
  Rabs r1 <= r2 -> (Z.abs (ZnearestE r1) <= ZnearestE r2)%Z.
Proof.
have [r1_pos|r1_neg] := Rle_dec 0 r1.
  rewrite Rabs_pos_eq // Z.abs_eq; last first.
    rewrite -(Znearest_IZR (fun x => ~~ Z.even x) 0).
    by apply: Znearest_le.
  by apply: Znearest_le.
rewrite Rabs_left; last by lra.
rewrite Z.abs_neq; last first.
  rewrite -(Znearest_IZR (fun x => ~~ Z.even x) 0).
  by apply: Znearest_le; lra.
rewrite -ZnearestE_opp.
by apply: Znearest_le; lra.
Qed.

Lemma kB : (Z.abs k <= 4194347)%Z.
Proof.
have ->: 4194347%Z = ZnearestE 4194347.07.
  rewrite /ZnearestE.
  have -> : Zfloor 4194347.07 = 4194347%Z.
    by apply: Zfloor_imp; rewrite plus_IZR; lra.
  by case: Rcompare_spec => //; lra.
apply: ZnearestE_le_abs.
apply: Rle_trans (_ : Rabs (rh * INVLN2) * (1 + pow (- 52)) <= _).
  apply/Rlt_le/relative_error_FLT_alt => //.
  rewrite Rabs_mult [Rabs INVLN2]Rabs_pos_eq; last by interval.
  apply: Rle_trans (_ : pow (-970) * INVLN2 <= _); first by interval.
  by apply: Rmult_le_compat; try lra; interval.
apply: Rle_trans (_ : (709.79 * (pow 12/ ln 2 + Rpower 2 (- 43.447))) *
                         (1 + pow (-52)) <= _).
  apply: Rmult_le_compat_r; first by interval.
  boundDMI; first by lra.
  by interval with (i_prec 100).
by interval.
Qed.

Lemma kn2rhrlB: 
   Rabs (IZR k * ln 2 * pow (- 12) - (rh + rl)) <= Rpower 2 (- 12.906174).
Proof.
suff HF : Rabs (IZR k - (rh + rl) * pow 12 / ln 2) <= 0.7698196.
  have -> : IZR k * ln 2 * pow (- 12) - (rh + rl) = 
            (ln 2 * pow (-12)) * (IZR k - (rh + rl) * pow 12 / ln 2).
    have -> : (- 12 = (- (12)))%Z by lia.
    by rewrite bpow_opp; field; split; interval.
  rewrite Rabs_mult.
  apply: Rle_trans (_ : Rabs (ln 2 * pow (-12)) * 0.7698196 <= _).
    by apply: Rmult_le_compat_l => //; interval.
  by interval.
pose D1 := IZR k - RND(rh * INVLN2).
pose D2 := RND(rh * INVLN2) - rh * INVLN2.
pose D3 := (rh + rl) * (INVLN2 - pow 12 / ln 2).
pose D4 := rl * INVLN2.
have -> : IZR k - (rh + rl) * pow 12 / ln 2 = D1 + D2 + D3 - D4.
  by rewrite [_ / ln 2]Rmult_assoc /D1 /D2 /D3 /D4; field; interval.
apply: Rle_trans (_ : 1/2 + pow (-30) + Rpower 2 (- 33.975) + 
                      0.2698195 <= _); last by interval.
boundDMI; [boundDMI; [boundDMI|]|].
- rewrite /D1 /k.
  suff : Rabs (RND (rh * INVLN2) - IZR (ZnearestE (RND (rh * INVLN2))))
                <= / 2.
    by split_Rabs; lra.
  by apply: Znearest_half.
- apply: Rle_trans  (_ : ulp (rh * INVLN2) <= _).
    by apply/error_le_ulp.
  have Rrh_pos: 0 < Rabs rh by move: (bpow_gt_0 beta (- 970)); lra.
  rewrite ulp_neq_0; last by rewrite /INVLN2; split_Rabs; nra.
  have h : Rabs (rh * INVLN2) <= 709.79 *  INVLN2.
    rewrite Rabs_mult.
    by rewrite (Rabs_pos_eq INVLN2); try rewrite /INVLN2;lra.
  have : 709.79 * INVLN2 < pow (23).
    by rewrite /INVLN2 ; interval.
  rewrite /cexp /fexp Z.max_l => *.
    apply/bpow_le.
    suff: (mag beta (rh * INVLN2) <= 23) %Z by lia.
    apply/mag_le_bpow;  try lra.
    by rewrite /INVLN2; split_Rabs; nra.
  suff : (emin + p <=  mag beta (rh * INVLN2))%Z by lia.
  apply/mag_ge_bpow.
  rewrite Rabs_mult (Rabs_pos_eq INVLN2); try interval.
  rewrite /INVLN2.
  apply: Rle_trans (_ : pow (-970) <= _); last by lra. 
  by apply/bpow_le; lia.
- apply: Rle_trans (_ : 709.79 * Rpower 2 (- 43.447) <= _); last by interval.
  boundDMI; first by lra.
  by interval with (i_prec 70).
rewrite Rabs_Ropp /D4.
apply: Rle_trans (_ : Rpower 2 (- 14.4187) * Rabs INVLN2 <= _).
  by boundDMI; lra.
by rewrite [Rabs INVLN2]Rabs_pos_eq; interval.
Qed.

Lemma rhBkln2h_format : format (rh - IZR k * LN2H).
Proof.
have rhBkln2hB : Rabs (rh - IZR k * LN2H) <= omega.
  apply: Rle_trans (_ : Rabs rh + Rabs (IZR k * LN2H) <= _).
    by clear; split_Rabs; lra.
  apply: Rle_trans (_ : Rabs 709.79 + 4194347 * LN2H <= _); last by interval.
  apply: Rplus_le_compat.
    by rewrite [Rabs 709.79]Rabs_pos_eq; lra.
  rewrite Rabs_mult [Rabs LN2H]Rabs_pos_eq; last by interval.
  apply: Rmult_le_compat_r; first by interval.
  by rewrite Rabs_Zabs; apply/IZR_le/kB.
have rhBkln2h_imul : is_imul (rh - IZR k * LN2H) alpha.
  apply: is_imul_pow_le (_ : is_imul _ (pow (- 1022))) _; last by lia.
  apply: is_imul_minus.
    have -> : (- 1022 = - 970 - p + 1)%Z by lia.
    apply: is_imul_bound_pow_format => //.
    by rewrite -[bpow _ _]/(pow _); lra.
  apply: is_imul_pow_le (_ : is_imul _ (pow (- 65))) _; last by lia.
  exists (6243314768165359 * k)%Z.
  by rewrite mult_IZR /LN2H /F2R /= /Z.pow_pos /=; lra.
Admitted.

Definition zl := RND (rl - IZR k * LN2L).

Lemma zl_err : Rabs (zl - (rl - IZR k * LN2L)) <= pow (- 67).
Proof.
have rlkln2lB : Rabs (rl - IZR k * LN2L) <= Rpower 2 (- 14.418).
  apply: Rle_trans (_ : Rabs rl + Rabs (IZR k * LN2L) <= _).
    by clear; split_Rabs; lra.
  apply: Rle_trans (_ : Rpower 2 (- 14.4187) + 4194347 * LN2L <= _);
     last by interval.
  apply: Rplus_le_compat; first by lra.
  rewrite Rabs_mult [Rabs LN2L]Rabs_pos_eq; last by interval.
  apply: Rmult_le_compat_r; first by interval.
  by rewrite Rabs_Zabs; apply/IZR_le/kB.
apply: Rle_trans (error_le_ulp _ _ _ _) _.
apply: bound_ulp => //.
apply: Rle_lt_trans rlkln2lB _.
by interval.
Qed.

Definition e := (k / 2 ^ 12)%Z.
Definition i1 := ((k - e * 2 ^ 12) / 2 ^ 6)%Z.
Definition i2 := ((k - e * 2 ^ 12 - i1 * 2 ^ 6))%Z.

Lemma eE : (k = e * 2 ^ 12 + i1 * 2 ^ 6 + i2)%Z.
Proof.
rewrite /i2 /i1 /e -!Zmod_eq_full; try by lia.
rewrite -Zplus_assoc [(_ * 2 ^ 6)%Z]Z.mul_comm -Z_div_mod_eq_full.
by rewrite [(_ * 2 ^ 12)%Z]Z.mul_comm -Z_div_mod_eq_full.
Qed.

Lemma i1B : (0 <= i1 <= 63)%Z.
Proof.
rewrite /i1 /e -Zmod_eq_full; last by lia.
have km12B : (0 <= k mod (2 ^ 12) < 2 ^12)%Z by apply: Z.mod_pos_bound.
split; first by apply: Z.div_pos; lia.
have -> : (63 = (2 ^ 12 - 1) / 2 ^ 6)%Z by [].
by apply: Z_div_le; lia.
Qed.

Lemma i2B : (0 <= i2 <= 63)%Z.
Proof.
suff : (0 <= i2 < 2 ^ 6)%Z by lia.
rewrite /i2 /i1 /e -Zmod_eq_full; last by lia.
by apply: Z.mod_pos_bound.
Qed.

Definition h1 := round beta fexp ZnearestE (Rpower 2 (IZR i1 / pow 12)).
Definition e1 := (h1 - Rpower 2 (IZR i1 / pow 12)).

Lemma h1F : format h1.
Proof. by apply: generic_format_round. Qed.

Lemma h1B : 1 <= h1 < 2.
Proof.
have Blow : 1 <= (Rpower 2 (IZR i1 / pow 12)).
  have <- : Rpower 2 0 = 1 by rewrite Rpower_O; lra.
  apply: Rle_Rpower; first by lra.
  apply: Rcomplements.Rdiv_le_0_compat; last by apply: bpow_gt_0.
  by apply/IZR_le; have := i1B; lia.
have Bhigh : Rpower 2 (IZR i1 / pow 12) < 2.
  have {2}<- : Rpower 2 1 = 2 by rewrite Rpower_1; lra.
  apply: Rpower_lt; first by lra.
  apply/Rcomplements.Rlt_div_l; first by interval.
  rewrite Rsimp01 -IZR_Zpower //.
  apply/IZR_lt.
  by rewrite /beta /= /Z.pow_pos /=; have := i1B; lia.
split.
  have-> : 1 = pow 0 by [].
  suff: pow (1 - 1) <= h1 <= pow 1 by rewrite -[(1 - 1)%Z]/0%Z; lra.
  by apply: round_bounded_large_pos.
rewrite [h1]round_FLT_FLX; last first.
  rewrite Rabs_pos_eq; last by lra.
  by apply: Rle_trans Blow; interval.
apply: RN_lt_pos; try by (lia || lra).
rewrite -{4}[2]/(pow 1).
rewrite ulp_bpow [FLX_exp _ _]/=.
apply: Rle_lt_trans (_ : Rpower 2 0.5 < _); last by interval.
apply: Rle_Rpower; first by lra.
apply/Rcomplements.Rle_div_l; first by interval.
have -> : 0.5 * pow 12 = pow 11 by rewrite /= /Z.pow_pos /=; lra.
rewrite -IZR_Zpower //.
apply/IZR_le.
by rewrite /= /Z.pow_pos /=; have := i1B; lia.
Qed.

Lemma h1E : h1 = Rpower 2 (IZR i1 / pow 12) + e1.
Proof. by rewrite /e1; lra. Qed.

Lemma e1B : Rabs e1 <= pow (- 53).
Proof.
apply: Rle_trans (_ : /2 * ulp (Rpower 2 (IZR i1 / pow 12)) <= _).
  by apply: error_le_half_ulp.
suff : ulp (Rpower 2 (IZR i1 / pow 12)) <= pow (-52).
  by rewrite ![pow _]/= /Z.pow_pos /=; lra.
apply: bound_ulp => //.
rewrite Rabs_pos_eq; last by apply/Rlt_le/exp_pos.
rewrite pow_Rpower //.
apply: Rpower_lt; first by lra.
apply/Rcomplements.Rlt_div_l; first by interval.
rewrite -IZR_Zpower // -mult_IZR.
apply/IZR_lt.
by have := i1B; rewrite /=; lia.
Qed.

Definition l1 := round beta fexp ZnearestE (Rpower 2 (IZR i1 / pow 12) - h1).

Lemma l1E : l1 = round beta fexp ZnearestE (- e1).
Proof. by rewrite /l1 /e1; congr round; lra. Qed.

Lemma l1B : Rabs l1 <= pow (- 53).
Proof.
rewrite l1E; apply: Rabs_round_le => //.
by rewrite Rabs_Ropp; apply: e1B.
Qed.

End algoExp1.

