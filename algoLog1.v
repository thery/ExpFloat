Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore algoP1.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Exp.

Let p := 53%Z.
Let emax := 1024%Z.
Let emin := (3 - emax - p)%Z.

Compute emin.

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
Local Notation RN := (round beta fexp rnd).

Definition LOG2H : float := Float _ 3048493539143 (- 42).

Lemma LOG2HE : F2R LOG2H = 3048493539143 * (pow (- 42)).
Proof. by rewrite /LOG2H /F2R /= /Z.pow_pos. Qed.

Lemma format_LOG2H : format LOG2H.
Proof.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma imul_LOG2H : is_imul LOG2H (pow (- 42)).
Proof. by exists 3048493539143%Z. Qed.

Lemma error_LOG2H : Rabs (LOG2H - ln 2) < pow (-44).
Proof.
by rewrite LOG2HE !pow_Rpower //; interval with (i_prec 54).
Qed.

Definition LOG2L : float := Float _ 544487923021427 (- 93).

Lemma LOG2LE : F2R LOG2L = 544487923021427 * (pow (- 93)).
Proof. by rewrite /LOG2L /F2R /= /Z.pow_pos. Qed.

Lemma format_LOG2L : format LOG2L.
Proof.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma imul_LOG2L : is_imul LOG2L (pow (- 93)).
Proof. by exists 544487923021427%Z. Qed.

Lemma error_LOG2L : Rabs (LOG2H + LOG2L - ln 2) < pow (- 102).
Proof.
by rewrite LOG2HE LOG2LE !pow_Rpower //; interval with (i_prec 120).
Qed.

Definition err8 e := Rabs (IZR e * LOG2H + IZR e * LOG2L - IZR e * ln 2).

Lemma err8_0 : err8 0 = 0.
Proof. by rewrite /err8 !Rsimp01. Qed.

Lemma err8_bound e : (- 1074 <= e <= 1024)%Z -> err8 e <= Rpower 2 (- 91.949).
Proof.
move=> e8B.
have {e8B}e8B1 : - 1074 <= IZR e <= 1024.
  have [e8L e8R] := e8B.
  by split; apply: IZR_le; lia.
pose v := LOG2H + LOG2L - ln 2.
have vB : - Rpower 2 (- 102.018) < v < 0.
  by rewrite /v LOG2HE LOG2LE !pow_Rpower; split; interval with (i_prec 150).
have -> : err8 e = Rabs (IZR e * v).
  by congr (Rabs _); rewrite /v; lra.
by interval with (i_prec 150).
Qed.

End Exp.

