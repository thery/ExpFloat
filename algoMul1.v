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

(* This is lemma 5 *)
Lemma err_lem5 x y : 
  format x -> alpha <= x <= omega ->
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
move=> fF fB.
have := @err_lem4 (refl_equal _) _ valid_rnd _ fF fB.
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
Admitted.

End Mul1.
