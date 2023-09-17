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

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Definition mul1 x y := 
  let: DWR h l := x in
  let: DWR r_h s := exactMul y h in
  let r_l := RND (y * l + s) in DWR r_h r_l.

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

(* This is lemma 5 *)
Lemma err_lem5 x y : 
  format x -> alpha <= x <= omega -> format y ->
  let: DWR h l := log1 x in
  let: DWR r_h r_l := mul1 (DWR h l) y in
  pow (- 969) <= Rabs (y * h) <= 709.7827 ->
  [/\ pow (- 970) <= Rabs r_h <= 709.79,
      Rabs r_l <= Rpower 2 (-14.4187),
      Rabs (r_l / r_h) <= Rpower 2 (- 23.8899) /\ Rabs (r_h + r_l) <= 709.79,
      Rabs (h + l - ln x) <= Rpower 2 (- 67.0544 ) * Rabs (ln x) & 
      Rabs (r_h + r_l - y * ln x) <= Rpower 2 (- 67.0544) /\
      ~(/ sqrt 2 < x < sqrt 2) -> 
      Rabs (r_h + r_l - y * ln x) <= Rpower 2 (- 63.799)].
Proof.
move=> xF xB yF.
have := @err_lem4 (refl_equal _) _ valid_rnd _ xF xB.
case log1E : log1 => [h l].
case mul1E : mul1 => [r_h r_l] [lB hlE hE] yhB.
have h_neq0 : h <> 0.
  move=> hE1; rewrite hE1 !Rsimp01 in yhB.
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
have hl : is_imul (y * h) alpha.
  have -> : alpha = pow (- 969 - 2 * p + 1) by [].
  case: (@format_decomp_prod y h) => [||m1 [e1 [yhE m1B]]].
  - by apply: generic_format_FLX_FLT yF.
  - suff /generic_format_FLX_FLT : format h by [].
    have := @log1_format_h (refl_equal _) _ valid_rnd _ xF.
    by rewrite log1E.
  apply: is_imul_bound_pow yhE m1B.
  by rewrite -/A; lra.
Admitted.

End Mul1.
