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
  [/\ pow (- 970) <= Rabs r_h <= 709.79,
      Rabs r_l <= Rpower 2 (-14.4187),
      Rabs (r_l / r_h) <= Rpower 2 (- 23.8899) /\ Rabs (r_h + r_l) <= 709.79,
      Rabs (h + l - ln x) <= Rpower 2 (- 67.0544 ) * Rabs (ln x) & 
      Rabs (r_h + r_l - y * ln x) <= Rpower 2 (- 67.0544) /\
      ~(/ sqrt 2 < x < sqrt 2) -> 
      Rabs (r_h + r_l - y * ln x) <= Rpower 2 (- 63.799)].
Proof.
Admitted.

End Mul1.
