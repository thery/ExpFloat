Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim algoLog1.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Mul1.

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
Local Notation fastTwoSum := (fastTwoSum rnd).
Local Notation RND := (round beta fexp rnd).
Local Notation log1 := (log1 rnd).
Local Notation exactMul := (exactMul rnd).
Local Notation ulp := (ulp beta fexp).

Lemma ulp_subnormal f : 
  format f -> pow emin <= Rabs f < pow (emin + p) -> ulp f = pow emin.
Proof.
move=> Ff fB.
have f_neq_0 : f <> 0.
  suff : 0 < Rabs f by split_Rabs; lra.
  suff : 0 < pow emin by lra.
  by apply: bpow_gt_0.
rewrite ulp_neq_0; last by lra.
rewrite /cexp /fexp Z.max_r //.
suff : (mag beta f <= emin + p)%Z by lia.
apply: mag_le_bpow; first by lra.
by lra.
Qed.

Lemma ulp_norm f : 
  format f -> pow (emin + p) <= Rabs f -> ulp f = pow (mag beta f - p).
Proof.
move=> Ff fB.
have f_neq_0 : f <> 0.
  suff : 0 < Rabs f by split_Rabs; lra.
  suff : 0 < pow (emin + p) by lra.
  by apply: bpow_gt_0.
rewrite ulp_neq_0; last by lra.
rewrite /cexp /fexp Z.max_l //.
suff : (emin + p <= mag beta f)%Z by lia.
apply: mag_ge_bpow.
apply: Rle_trans fB.
apply: bpow_le; lia.
Qed.

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Lemma error_round_general f : 
  exists d, exists e,
  [/\ 
    RND f = f * (1 + d) + e,
    e * d = 0,
    Rabs e <= alpha &
    Rabs d <= pow (- 52)].
Proof.
have [->|f_neq0] := Req_dec f 0.
  by exists 0; exists 0; rewrite round_0 !Rsimp01; 
     split => //; apply: bpow_ge_0.
have [pLf|fLp] := Rle_lt_dec (pow (emin + p)) (Rabs f); last first.
  exists 0; exists (RND f - f); split; rewrite ?Rsimp01 //.
  - by lra.
  - apply: Rle_trans (_ : ulp f <= _); first by apply: error_le_ulp.
    rewrite /alpha -[(- 1074)%Z]/emin.
    rewrite ulp_neq_0 // /cexp /fexp Z.max_r; first by lra.
    suff : (mag beta f <= emin + p)%Z by lia.
    apply: mag_le_bpow; first by lra.
    by lra.
  by apply: bpow_ge_0.
exists ((RND f - f) / f); exists 0; split.
- by field.
- by lra.
- by rewrite Rabs_R0; apply: bpow_ge_0.
rewrite Rabs_div //.
apply/Rle_div_l; first by clear -f_neq0; split_Rabs; lra.
apply: Rlt_le.
apply: relative_error_FLT => //.
apply: Rle_trans pLf.
by apply: bpow_le; lia.
Qed.

Definition mul1 x y := 
  let: DWR h l := x in
  let: DWR rh s := exactMul y h in
  let rl := RND (y * l + s) in DWR rh rl.

Lemma format_decomp_prod x1 x2 : 
  generic_format beta (FLX_exp p) x1 -> 
  generic_format beta (FLX_exp p) x2 -> 
  exists m1, exists e1, x1 * x2 = IZR m1 * pow e1 /\
                        Rabs (IZR m1) < pow (2 * p).
Proof.
move=> x1F x2F.
exists ((Ztrunc (scaled_mantissa beta (FLX_exp p) x1)) * 
        (Ztrunc (scaled_mantissa beta (FLX_exp p)  x2)))%Z.
exists (Generic_fmt.cexp beta (FLX_exp p) x1 + 
        Generic_fmt.cexp beta (FLX_exp p) x2)%Z.
split.
  rewrite [in LHS]x1F [in LHS]x2F /F2R /=.
  rewrite mult_IZR bpow_plus.
  set xx1 := Ztrunc _.
  set xx2 := Ztrunc _.
  set yy1 := Generic_fmt.cexp _ _ _.
  set yy2 := Generic_fmt.cexp _ _ _.
  rewrite -[bpow _ yy1]/(pow _).
  rewrite -[bpow _ yy2]/(pow _).
  lra.
rewrite mult_IZR.
have -> : (2 * p = p + p)%Z by lia.
rewrite bpow_plus Rabs_mult.
apply: Rmult_lt_compat; try by apply: Rabs_pos.
  rewrite -scaled_mantissa_generic //.
  have [x1_eq0|x1_neq0] := Req_dec x1 0.
    by rewrite x1_eq0 scaled_mantissa_0 Rabs_R0; apply: bpow_gt_0.
  suff : bpow beta (p - 1) <= Rabs (scaled_mantissa beta (FLX_exp p) x1) <=
          bpow beta p - 1 by lra.
  by apply: mant_bound_le.
rewrite -scaled_mantissa_generic //.
have [x2_eq0|x2_neq0] := Req_dec x2 0.
  by rewrite x2_eq0 scaled_mantissa_0 Rabs_R0; apply: bpow_gt_0.
suff : bpow beta (p - 1) <= Rabs (scaled_mantissa beta (FLX_exp p) x2) <=
        bpow beta p - 1 by lra.
by apply: mant_bound_le.
Qed.

Lemma is_imul_bound_pow e1 e2 p1 x1 m1 : 
   pow e1 <= Rabs x1 -> 
   x1 = IZR m1 * pow e2 -> Rabs (IZR m1) < pow p1 ->
   is_imul x1 (pow (e1 - p1 + 1)).
Proof.
move=> x1B x1E m1B.
exists (m1 * (2 ^ (e2 - (e1 - p1 + 1))))%Z.
  rewrite mult_IZR (IZR_Zpower beta).
    rewrite Rmult_assoc -bpow_plus x1E.
    by congr (_ * pow _); lia.   
suff: (e1 < p1 + e2)%Z by lia.
apply: (lt_bpow beta).
rewrite bpow_plus.
suff : Rabs x1 < pow p1 * pow e2 by lra.
have pe2_gt0 : 0 < pow e2 by apply: bpow_gt_0.
by rewrite x1E Rabs_mult [Rabs (pow _)]Rabs_pos_eq //; nra.
Qed.

Ltac boundDMI := 
  (apply: Rle_trans (Rabs_triang _ _) _ ;
   apply: Rplus_le_compat) ||
  (rewrite Rabs_mult;
   apply: Rmult_le_compat; (try by apply: Rabs_pos)) ||
  (rewrite Rabs_inv; apply: Rinv_le).

(* This is lemma 5 *)
Lemma err_lem5 x y : 
  format x -> alpha <= x <= omega -> format y ->
  let: DWR h l := log1 x in
  let: DWR rh rl := mul1 (DWR h l) y in
  pow (- 969) <= Rabs (y * h) <= 709.7827 ->
  [/\ pow (- 970) <= Rabs rh <= 709.79,
      Rabs rl <= Rpower 2 (-14.4187),
      Rabs (rl / rh) <= Rpower 2 (- 23.8899) /\ Rabs (rh + rl) <= 709.79,
      Rabs (h + l - ln x) <= Rpower 2 (- 67.0544 ) * Rabs (ln x) & 
      Rabs (rh + rl - y * ln x) <= Rpower 2 (- 57.580) /\
      (~(/ sqrt 2 < x < sqrt 2) -> 
       Rabs (rh + rl - y * ln x) <= Rpower 2 (- 63.799))].
Proof.
move=> xF xB yF.
have := @err_lem4 (refl_equal _) _ valid_rnd _ xF xB.
case log1E : log1 => [h l].
case mul1E : mul1 => [rh rl] [lB hlE hE] yhB.
have h_neq0 : h <> 0.
  move=> hE1; rewrite hE1 !Rsimp01 in yhB.
  have: 0 < pow (- 969) by interval.
  by lra.
have y_neq0 : y <> 0.
  move=> yE1; rewrite yE1 !Rsimp01 in yhB.
  have: 0 < pow (- 969) by interval.
  by lra.
pose lambda := l / h.
have lambdaE : l = lambda * h by rewrite /lambda; field.
have lambdaB : Rabs lambda <= Rpower 2 (- 23.89).
  rewrite lambdaE Rabs_mult in lB.
  suff : 0 < Rabs h by nra.
  by split_Rabs; lra.
have hl_neq0 : h + l <> 0.
  move=> hl_eq0.
  have lE1 : l = - h by lra.
  rewrite lE1 Rabs_Ropp in lB.
  have F : 0 < Rabs h by split_Rabs; lra.
  suff : Rpower 2 (- 23.89) < 1 by nra.
  by interval.
pose eps1 := (ln x) / (h + l) - 1.
have eps1E : ln x = (h + l) * (1 + eps1) by rewrite /eps1; field.
have eps1E1 : ln x = h * (1 + lambda) * (1 + eps1).
  by rewrite eps1E lambdaE; lra.
have eps1B : Rabs eps1 <= / (1 -  Rpower 2 (- 67.0544)) - 1.
  move: hlE.
  rewrite eps1E.
  have -> : h + l - (h + l) * (1 + eps1) = - ((h + l) * eps1) by lra.
  rewrite Rabs_Ropp !Rabs_mult => hB.
  have hB1 : Rabs eps1 <= Rpower 2 (-67.0544) * Rabs (1 + eps1).
    suff : 0 < Rabs (h + l) by nra.
    by clear -hl_neq0; split_Rabs; lra.
  have hB2 : Rabs eps1 <= Rpower 2 (- 67.0544) + Rpower 2 (- 67.0544) * Rabs eps1.
    apply: Rle_trans hB1 _.
    suff : Rabs (1 + eps1) <= 1 + Rabs eps1.
      suff: 0 < Rpower 2 (- 67.0544) by nra.
      by interval.
    by clear; split_Rabs; lra.
  suff : Rabs eps1 + 1 <= / (1 - Rpower 2 (- 67.0544)) by lra.
  rewrite -[X in _ <=X]Rdiv_1_l.
  apply/Rle_div_r; first by interval.
  by lra.
have eps1B1 : ~ / sqrt 2 < x < sqrt 2 -> 
               Rabs eps1 <= / (1 -  Rpower 2 (- 73.527)) - 1.
  move=> /hE.
  rewrite eps1E.
  have -> : h + l - (h + l) * (1 + eps1) = - ((h + l) * eps1) by lra.
  rewrite Rabs_Ropp !Rabs_mult => hB.
  have hB1 : Rabs eps1 <= Rpower 2 (- 73.527) * Rabs (1 + eps1).
    suff : 0 < Rabs (h + l) by nra.
    by clear -hl_neq0; split_Rabs; lra.
  have hB2 : Rabs eps1 <= Rpower 2 (- 73.527) + Rpower 2 (- 73.527) * Rabs eps1.
    apply: Rle_trans hB1 _.
    suff : Rabs (1 + eps1) <= 1 + Rabs eps1.
      suff: 0 < Rpower 2 (- 73.527) by nra.
      by interval.
    by clear; split_Rabs; lra.
  suff : Rabs eps1 + 1 <= / (1 - Rpower 2 (- 73.527)) by lra.
  rewrite -[X in _ <=X]Rdiv_1_l.
  apply/Rle_div_r; first by interval.
  by lra.
set A := pow _ in yhB; set B := 709.7827 in yhB.
have hF : format h.
  have := @log1_format_h (refl_equal _) _ valid_rnd _ xF.
  by rewrite log1E. 
have hl : is_imul (y * h) alpha.
  have -> : alpha = pow (- 969 - 2 * p + 1) by [].
  case: (@format_decomp_prod y h) => [||m1 [e1 [yhE m1B]]].
  - by apply: generic_format_FLX_FLT yF.
  - suff /generic_format_FLX_FLT : format h by [].
    have := @log1_format_h (refl_equal _) _ valid_rnd _ xF.
    by rewrite log1E.
  apply: is_imul_bound_pow yhE m1B.
  by rewrite -/A; lra.
move: mul1E; rewrite /mul1 /exactMul.
rewrite -[round _ _ _ _]/(RND _) -[round _ _ _ (_ - _)]/(RND _) => [] [rhE rlE].
set s := RND(_ - _) in rlE.
have sE : s = y * h - RND (y * h).
  apply: round_generic.
  rewrite -Ropp_minus_distr.
  apply: generic_format_opp.
  by apply: format_err_mul.
pose d1 := s / (y * h).
have d1E : s = d1 * (y * h) by rewrite /d1; field; lra.
have d1B : Rabs d1 < pow (- 52).
  rewrite Rabs_div; last by clear - y_neq0 h_neq0; nra.
  apply/Rlt_div_l.
    by clear - y_neq0 h_neq0; split_Rabs; nra.
  rewrite sE -Rabs_Ropp Ropp_minus_distr.
  case: hl => m1 m1E.
  pose x1 := Float beta m1 emin.
  have yhE1 : y * h = x1 by rewrite m1E /F2R /=.
  rewrite yhE1.
  apply: relative_error_FLT_F2R_emin => //.
  by rewrite -yhE1; clear -h_neq0 y_neq0; nra.
have rhE1 : rh = (y * h) * (1 - d1).
  by rewrite -rhE; lra.
have rhB : pow (- 970) <= Rabs (rh) <= 709.79.
  split.
    apply: Rle_trans (_ : A * (1 - pow (- 52)) <= _); first by interval.
    rewrite rhE1 Rabs_mult.
    apply: Rmult_le_compat; try by interval.
      by lra.
    by clear -d1B; split_Rabs; lra.
  apply: Rle_trans (_ : B * (1 + pow (- 52)) <= _); last by interval.
  rewrite rhE1 Rabs_mult.
  apply: Rmult_le_compat; try by interval.
    by lra.
  by clear -d1B; split_Rabs; lra.
have ylsB : Rabs (y * l + s) <= pow (- 13).
  have -> : y * l + s = (y * h) * (lambda + d1).
    by rewrite lambdaE d1E; lra.
  rewrite Rabs_mult.
  apply: Rle_trans (_ : B * (Rabs lambda + Rabs d1) <= _); last by interval.
  apply: Rmult_le_compat; try by apply: Rabs_pos.
    by lra.
  by clear; split_Rabs; lra.
have [d2 [e2 [d2e2E d2e2_eq0 e2B d2B]]] := error_round_general (y * l + s).
rewrite rlE in d2e2E.
have rlE1 : rl = (y * h) * (lambda + d1 ) * (1 + d2 ) + e2.
  by rewrite d2e2E lambdaE d1E; lra.
have rlB : Rabs rl <= Rpower 2 (- 14.4187).
  rewrite rlE1.
  apply: Rle_trans (_ : 
     B * (Rpower 2 (- 23.89) + pow (- 52)) * (1 + pow (- 52)) + alpha <= _);
      last by interval.
  boundDMI; last by lra.
  boundDMI; last first.
    boundDMI; first by rewrite Rabs_pos_eq; lra.
    by lra.
  boundDMI; first by lra.
  by boundDMI; lra.  
have rhrlB : Rabs (rl / rh) <= Rpower 2 (- 23.8899).
  have -> : rl / rh = 
        (lambda + d1) * (1 + d2 ) * /(1 - d1) + e2 / (y * h) * /(1 - d1). 
    rewrite rlE1 rhE1; field; repeat split => //.
    by interval.
  apply: Rle_trans (_ : 
    (Rpower 2 (- 23.89) + pow (- 52)) * (1 + pow (- 52)) * 
       / (1 - pow (- 52)) + 
      pow (- 1074 + 969) * /(1 - pow (- 52)) <= _); last by interval.
  do !boundDMI; try (interval || lra).
  - apply: Rle_trans (_ : Rabs 1 - Rabs d1 <= _).
      by rewrite Rabs_pos_eq; lra.
    by clear; split_Rabs; lra.
  - rewrite bpow_plus; boundDMI.
      by rewrite -[pow _]/alpha; lra.
  - have -> : (969 = - - 969)%Z by lia.
    rewrite bpow_opp -/A.
    boundDMI; first by interval.
    by lra.
  apply: Rle_trans (_ : Rabs 1 - Rabs d1 <= _).
    by rewrite Rabs_pos_eq; lra.
  by clear; split_Rabs; lra.
have rhrlE : rh + rl = (y * h) * (1 + lambda * (1 + d2) + d1 * d2) + e2.
  by lra.
have rhrlB1 : Rabs (rh + rl) <= 709.79.
  apply: Rle_trans (_ : 
    709.7827 * (1 + Rpower 2 (- 23.89) * (1 + pow (- 52)) + pow (- 104)) +
    alpha <= _); last by interval.
  rewrite rhrlE.
  boundDMI; last by lra.
  boundDMI; first by rewrite -/B; lra.
  boundDMI.
    boundDMI; first by rewrite Rabs_pos_eq; lra.
    boundDMI; first by lra.
    boundDMI; first by rewrite Rabs_pos_eq; lra.
    by lra.
  have ->: (- 104 = - 52 + - 52)%Z by lia.
  rewrite bpow_plus.
  by boundDMI; lra.
have ylnxE : y * ln x = (y * h) * (1 + lambda) * (1 + eps1).
  by rewrite eps1E1; lra.
have rhrlylnxE : rh + rl - y * ln x = 
                 y * h  * (- (1 + lambda) * eps1 + (lambda + d1 ) * d2) + e2.
  by lra.
pose C := B * ((1 + Rpower 2 (- 23.89)) * Rabs eps1 +
               (Rpower 2 (- 23.89) + pow (- 52)) * pow (- 52)) + alpha.
have rhrlylnxB : Rabs (rh + rl - y * ln x) <= C.
  rewrite rhrlylnxE.
  boundDMI; last by lra.
  boundDMI; first by lra.
  boundDMI.
    boundDMI; last by lra.
    rewrite Rabs_Ropp.
    boundDMI; first by rewrite Rabs_pos_eq; lra.
    by lra.
  boundDMI; last by lra.
  by boundDMI; lra.
split => //; split.
  apply: Rle_trans rhrlylnxB _.
  rewrite /C /alpha /B.
  by interval with (i_prec 100).
move=> xInsqrt.
have {}eps1B := eps1B1 xInsqrt.
apply: Rle_trans rhrlylnxB _.
rewrite /C /alpha /B.
by interval with (i_prec 100).
Qed.

End Mul1.
