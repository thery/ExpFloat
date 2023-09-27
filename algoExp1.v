Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Interval Require Import Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim algoLog1 algoMul1.
Require Import Fast2Sum_robust_flt algoQ1 tableT1 tableT2.

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

Variable choice : Z -> bool.
Definition k := Znearest choice (RND (rh * INVLN2)).

Lemma Znearest_le c r1 r2 : 
  r1 <= r2 -> (Znearest c r1 <= Znearest c r2)%Z.
Proof. by case: (valid_rnd_N c) => H _; exact: H. Qed.

Lemma Znearest_IZR c k : Znearest c (IZR k) = k.
Proof. by case: (valid_rnd_N c) => _ H; exact: H. Qed.

Lemma kB : (Z.abs k <= 4194347)%Z.
Proof.
have F1: Rabs (RND (rh * INVLN2)) <= 4194347.07.
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
have [rhi_neg|rhi_pos] := Rle_lt_dec (rh * INVLN2) 0.
  have rrhi_neg : RND (rh * INVLN2) <= 0.
    have <- : RND 0 = 0 by rewrite round_0.
    by apply: round_le.  
  rewrite Z.abs_neq; last first.
    have <- : Znearest choice 0 = 0%Z by rewrite Znearest_IZR.
    by apply: Znearest_le.
  suff: (- 4194347 <= k)%Z by lia.
  have <- : Znearest choice (- 4194347.07) = (- 4194347)%Z.
    by apply: Znearest_imp; interval.
  apply: Znearest_le.
  by clear -F1 rrhi_neg; split_Rabs; lra.
have rrhi_pos : 0 <= RND (rh * INVLN2).
  have <- : RND 0 = 0 by rewrite round_0.
  by apply: round_le; lra.
rewrite Z.abs_eq; last first.
  have <- : Znearest choice 0 = 0%Z by rewrite Znearest_IZR.
  by apply: Znearest_le.
have <- : Znearest choice (4194347.07) = 4194347%Z.
  by apply: Znearest_imp; interval.
apply: Znearest_le.
by clear -F1 rrhi_pos; split_Rabs; lra.
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
  suff : Rabs (RND (rh * INVLN2) - IZR (Znearest choice (RND (rh * INVLN2))))
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
  apply: Rle_trans (_ : Rabs 709.79 + 4194347 * LN2H <= _); 
   last by interval.
  apply: Rplus_le_compat.
    by rewrite [Rabs 709.79]Rabs_pos_eq; lra.
  rewrite Rabs_mult [Rabs LN2H]Rabs_pos_eq; last by interval.
  apply: Rmult_le_compat_r; first by interval.
  by rewrite Rabs_Zabs; apply/IZR_le/kB.
have rhBkln2h_imul_1022: (is_imul (rh - IZR k * LN2H)(pow (- 1022))).
  apply: is_imul_minus.
    have -> : (- 1022 = - 970 - p + 1)%Z by lia.
    apply: is_imul_bound_pow_format => //.
    by rewrite -[bpow _ _]/(pow _); lra.
  apply: is_imul_pow_le (_ : is_imul _ (pow (- 65))) _; last by lia.
  exists (6243314768165359 * k)%Z.
  by rewrite mult_IZR /LN2H /F2R /= /Z.pow_pos /=; lra.
have rhBkln2h_imul : is_imul (rh - IZR k * LN2H) alpha.
  by apply: is_imul_pow_le (_ : is_imul _ (pow (- 1022))) _; last by lia.

have rhBkln2hB13 : Rabs (rh - IZR k * LN2H) <= Rpower 2 (-13.528766) by admit.
case:(Rle_lt_dec (bpow radix2 (-13)) (Rabs rh))=>hrh13.
  
  have imul_rh65: is_imul rh (pow (-65)).
    have->: (-65 = -13 - 53 + 1)%Z by lia.
    by apply/is_imul_bound_pow_format.    
  case:imul_LN2H => mln2h mE.
  have [m rhkln2E]: is_imul (rh - IZR k * LN2H)  (pow (-65)).
    apply/is_imul_minus=>//.
    by rewrite mE;exists (k * mln2h)%Z; rewrite -Rmult_assoc mult_IZR.
  apply/generic_format_FLT/(FLT_spec _ _ _ _ (Float beta  m (-65))); rewrite /F2R/=.
  +  have ->: IZR (Z.pow_pos 2 65) = bpow beta 65 by [].
     by rewrite -bpow_opp.
  + apply/lt_IZR; have ->: IZR (Z.pow_pos 2 53) = bpow beta 53 by [].
    apply/(Rmult_lt_reg_r (pow (-65))); first by apply/bpow_gt_0.
    rewrite abs_IZR -bpow_plus -(Rabs_pos_eq (pow (-65))); last by apply/bpow_ge_0.
    rewrite -Rabs_mult -rhkln2E; ring_simplify (53 + -65)%Z.
    apply/(Rle_lt_trans _ (Rpower 2 (-13.528766)))=>//.
    by rewrite pow_Rpower; last lia; apply/Rpower_lt; lra.
  by lia.

Admitted.

Definition zh := RND (rh - IZR k * LN2H).

Lemma zhF : format zh.
Proof. by apply: generic_format_round. Qed.

Lemma zhE : zh = rh - IZR k * LN2H.
Proof. by apply/round_generic/rhBkln2h_format. Qed.

Definition zl := RND (rl - IZR k * LN2L).

Lemma zlF : format zl.
Proof. by apply: generic_format_round. Qed.

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

Definition z := RND (zh + zl).

Lemma zF : format z.
Proof. by apply: generic_format_round. Qed.

Lemma zB: Rabs z <= Rpower 2  (- 12.905).
Admitted.

Definition e := (k / 2 ^ 12)%Z.
Definition i1 := ((k - e * 2 ^ 12) / 2 ^ 6)%Z.
Definition ni1 := Z.to_nat i1.
Definition i2 := ((k - e * 2 ^ 12 - i1 * 2 ^ 6))%Z.
Definition ni2 := Z.to_nat i2.

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

Lemma ni1B : (0 <= ni1 <= 63)%N.
Proof.
by apply/andP; split; apply/leP; have := i1B; rewrite /ni1; lia.
Qed.

Lemma INR_ni1E : INR ni1 = IZR i1.
Proof. by rewrite INR_IZR_INZ Z2Nat.id //; have := i1B; lia. Qed. 

Lemma i2B : (0 <= i2 <= 63)%Z.
Proof.
suff : (0 <= i2 < 2 ^ 6)%Z by lia.
rewrite /i2 /i1 /e -Zmod_eq_full; last by lia.
by apply: Z.mod_pos_bound.
Qed.

Lemma ni2B : (0 <= ni2 <= 63)%N.
Proof.
by apply/andP; split; apply/leP; have := i2B; rewrite /ni2; lia.
Qed.

Lemma INR_ni2E : INR ni2 = IZR i2.
Proof. by rewrite INR_IZR_INZ Z2Nat.id //; have := i2B; lia. Qed. 

Definition h1 := (nth (0,0) T2 ni1).1.
Definition e1 := (h1 - Rpower 2 (IZR i1 / pow 12)).

Lemma h1F : format h1.
Proof. by apply: format_T2_h1 => //; case/andP: ni1B. Qed.

Lemma h1B : 1 <= h1 < 2.
Proof. by apply: T2_h1B; case/andP: ni1B. Qed.

Lemma e1B : Rabs e1 <= pow (- 53).
Proof.
by rewrite /e1 -INR_ni1E; apply: T2_e1B; have/andP[] := ni1B.
Qed.

Lemma imul_h1 : is_imul h1 (pow (- 52)).
Proof.
have -> : (- 52 = 0 - p + 1)%Z by lia.
apply: is_imul_bound_pow_format h1F.
by have h1B := h1B; rewrite pow0E Rabs_pos_eq; lra.
Qed.

Definition l1 := (nth (0,0) T2 ni1).2.

Lemma l1F : format l1.
Proof. by apply: format_T2_l1 => //; case/andP: ni1B. Qed.

Lemma l1B : Rabs l1 <= pow (- 53).
Proof.
have [->|l1_neq0] := Req_dec l1 0; first by interval.
suff : pow (- 58) <= Rabs l1 <= pow (- 53) by lra.
by apply: T2_l1B => //; have/andP[] := ni1B.
Qed.

Lemma imul_l1 : is_imul l1 (pow (- 110)).
Proof.
have [->|l1_neq0] := Req_dec l1 0; first by exists 0%Z; lra.
have -> : (- 110 = - 58 - p + 1)%Z by lia.
apply: is_imul_bound_pow_format l1F.
rewrite -[bpow _ _]/(pow _).
suff : pow (- 58) <= Rabs l1 <= pow (- 53) by lra.
by apply: T2_l1B => //; have/andP[] := ni1B.
Qed.

Lemma rel_error_h1l1 : 
  Rabs ((h1 + l1) / Rpower 2 (IZR i1 /pow 12) - 1) < Rpower 2 (- 107.000244).
Proof.
rewrite -INR_ni1E /h1 /l1.
case: nth (@T2_rel_error_h1l1 ni1) => h l /=.
by apply; have/andP[] := ni1B.
Qed.

Definition h2 :=  (nth (0,0) T1 ni2).1.
Definition e2 := (h2 - Rpower 2 (IZR i2 / pow 6)).

Lemma h2F : format h2.
Proof. by apply: format_T1_h2 => //; case/andP: ni2B. Qed.

Lemma h2B : 1 <= h2 < 2.
Proof. by apply: T1_h2B; case/andP: ni2B. Qed.

Lemma h2E : h2 = Rpower 2 (IZR i2 / pow 6) + e2.
Proof. by rewrite /e2; lra. Qed.

Lemma imul_h2 : is_imul h2 (pow (- 52)).
Proof.
have -> : (- 52 = 0 - p + 1)%Z by lia.
apply: is_imul_bound_pow_format h2F.
by have h2B := h2B; rewrite pow0E Rabs_pos_eq; lra.
Qed.

Lemma e2B : Rabs e2 <= pow (- 53).
Proof.
by rewrite /e2 -INR_ni2E; apply: T1_e2B; have/andP[] := ni2B.
Qed.

Definition l2 := (nth (0,0) T1 ni2).2.

Lemma l2F : format l2.
Proof. by apply: format_T1_l2 => //; case/andP: ni2B. Qed.

Lemma l2B : Rabs l2 <= pow (- 53).
Proof.
have [->|l2_neq0] := Req_dec l2 0; first by interval.
suff : pow (- 59) <= Rabs l2 <= pow (- 53) by lra.
by apply: T1_l2B => //; have/andP[] := ni2B.
Qed.

Lemma rel_error_h2l2 : 
  Rabs ((h2 + l2) / Rpower 2 (IZR i2 /pow 6) - 1) < Rpower 2 (- 107.015625).
Proof.
rewrite -INR_ni2E /h2 /l2.
case: nth (@T1_rel_error_h2l2 ni2) => h l /=.
by apply; have/andP[] := ni2B.
Qed.

Lemma imul_l2 : is_imul l2 (pow (- 111)).
Proof.
have [->|l2_neq0] := Req_dec l2 0; first by exists 0%Z; lra.
have -> : (- 111 = - 59 - p + 1)%Z by lia.
apply: is_imul_bound_pow_format l2F.
apply: Rle_trans (_ : Rpower 2 (- 58.98) <= _); first by interval.
suff : Rpower 2 (- 58.98) <= Rabs l2 <= pow (- 53) by lra.
by apply: T1_l2B => //; have/andP[] := ni2B.
Qed.

Lemma h1h2B : 1 <= h1 * h2 < 2.
Proof.
split; first by have := h1B; have := h2B; nra.
apply: Rle_lt_trans (_ : Rpower 2 (0.015381) * Rpower 2 (0.984376) < _); 
   last by interval.
apply: Rmult_le_compat.
- have := h1B; lra.
- have := h2B; lra.
- by apply: T2_h1B1; case/andP : ni1B.
by apply: T1_h2B1; case/andP : ni2B.
Qed.

End algoExp1.

