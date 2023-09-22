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

End algoExp1.

