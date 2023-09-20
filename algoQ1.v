Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Interval Require Import Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim algoLog1 algoMul1.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section algoQ1.

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

Definition Q0 := 1.
Definition Q1 := 1.
Definition Q2 := 0.5.
Definition Q3 := 0x1.5555555997996p-3.
Definition Q4 := 0x1.5555555849d8dp-5.

Definition Qf0 : float := 
  Float _ 1 0.

Definition Qf1 : float := 
  Float _ 1 0.

Definition Qf2 : float := 
  Float _ 1 (-1).

Definition Qf3 : float := 
  Float _ 6004799507626390 (-55).

Definition Qf4 : float := 
  Float _ 6004799506259341 (-57).

Fact Qf0E : F2R Qf0 = Q0.
Proof. by rewrite /Q0 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_Q0 : format Q0.
Proof.
rewrite -Qf0E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Qf1E : F2R Qf1 = Q1.
Proof. by rewrite /Q1 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_Q1 : format Q1.
Proof.
rewrite -Qf1E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Qf2E : F2R Qf2 = Q2.
Proof. by rewrite /Q2 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_Q2 : format Q2.
Proof.
rewrite -Qf2E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Qf3E : F2R Qf3 = Q3.
Proof. by rewrite /Q3 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_Q3 : format Q3.
Proof.
rewrite -Qf3E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Qf4E : F2R Qf4 = Q4.
Proof. by rewrite /Q4 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_Q4 : format Q4.
Proof.
rewrite -Qf4E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Definition Q z :=
  Q0 + Q1 * z + Q2 * z ^ 2 + Q3 * z ^ 3 + Q4 * z ^ 4.

Lemma Q_abs_error z :
  Rabs z <= Rpower 2 (- 12.905) -> 
  Rabs (exp z - Q z) <= Rpower 2 (- 74.34).
Proof.
move=> *; rewrite /Q /Q0 /Q1 /Q2 /Q3 /Q4.
interval with (i_prec 90, i_bisect z, i_taylor z).
Qed.


Lemma error_exactMul (a b : R) :
  format a -> format b ->
  let: DWR h l := exactMul a b in Rabs ((h + l) - (a * b)) < alpha.
Proof.
Admitted.

(* L'algo q_1 *)

Definition q1 (z : R) :=
  let q := RND (Q4 * z + Q3) in
  let q := RND (q * z + Q2) in
  let: h0 := RND (q * z + Q1) in
  let: DWR h1 l1 := exactMul z h0 in fastSum Q0 h1 l1.

Lemma err_lem6 z :
  format z ->
  let: DWR qh ql := q1 z in 
  Rabs z <= Rpower 2 (- 12.905) ->
  Rabs ((qh - ql) / exp z - 1) < Rpower 2 (- 64.902632) /\ 
  Rabs ql <= Rpower 2 (- 51.999).
Proof.
move=> Fz; case Eq : q1 => [qh ql].
move: Eq; rewrite /q1.
set q := RND (Q4 * _ + _); set q' := RND (q * _ + _).
set h0 := RND (q' * _ + _).
case Em : exactMul => [h1 l1].
move=> Ef zB.
have Q4B1 : Rpower 2 (- 4.59) < Q4 by interval.
have Q4B : 0 < Q4 < Rpower 2 (- 4.58) by split; interval.
have Q3B1 : Rpower 2 (- 2.59) < Q3 by interval.
have Q3B : 0 < Q3 < Rpower 2 (- 2.58) by split; interval.
have Q4zQ3B : pow (emin + p - 1) <= (Q4 * z + Q3).
  apply: Rle_trans (_: Q3 - Q4 * Rabs z <= _); last by split_Rabs; nra.
  apply: Rle_trans (_: 
    Rpower 2 (-2.59) - Rpower 2 (-4.58) * Rpower 2 (-12.905) <= _); last first.
    boundDMI; first by lra.
    boundDMI.
    apply: Rmult_le_compat; (try by interval).
    by lra.
  by interval.
have qB : Rabs q <= Rpower 2 (- 2.579).
  have FB : pow (emin + p - 1) <= Rabs (Q4 * z + Q3).
    rewrite Rabs_pos_eq //.
    by apply: Rle_trans (bpow_ge_0 _ _) Q4zQ3B.
  apply: Rle_trans (_ : (Q4 * Rpower 2 (-12.905) + Q3) *
      (1 + pow (- 52)) <= _); last by interval.
  apply: Rle_trans (_ : Rabs (Q4 * z + Q3) * (1 + pow (- 52)) <= _).
    suff: Rabs (q - (Q4 * z + Q3)) < pow (- 52) * Rabs (Q4 * z + Q3).
      by split_Rabs; lra.
    by apply: relative_error_FLT.
  apply: Rmult_le_compat_r; try (by apply: Rabs_pos); first by interval.
  boundDMI; last by rewrite Rabs_pos_eq; lra.
  boundDMI; last by lra.
  by rewrite Rabs_pos_eq; lra.
pose Q := Q4 * z + Q3.
have qB1 : pow (emin + p - 1) <= q.
  rewrite -[q]Rabs_pos_eq; last first.
    rewrite -[0](round_0 beta fexp) //.
    apply: round_le.
    by apply: Rle_trans (bpow_ge_0 _ _) Q4zQ3B. 
  apply: format_Rabs_round_le => //.
  apply: generic_format_bpow => //.
  by rewrite Rabs_pos_eq //; apply: Rle_trans (bpow_ge_0 _ _) Q4zQ3B.
have q_pos : 0 < q by apply: Rlt_le_trans (bpow_gt_0 _ _) qB1.
have qQB : Rabs (q - Q) <= pow (- 55).
  apply: Rle_trans (_ : ulp q <= _); first by apply: error_le_ulp_round.
  rewrite ulp_neq_0; last by lra.
  rewrite /cexp /fexp Z.max_l.
    apply: bpow_le.
    suff : (mag beta q <= - 2)%Z by lia.
    apply: mag_le_bpow; first by lra.
    apply: Rle_lt_trans qB _.
    by interval.
  suff : (emin + p <= mag beta q)%Z by lia.
  apply: mag_ge_bpow.
  by rewrite Rabs_pos_eq; lra.
have qzQ2B : pow (emin + p - 1) <= (q * z + Q2).
  apply: Rle_trans (_: Q2 - q * Rabs z <= _); last by split_Rabs; nra.
  apply: Rle_trans (_: 
    /2 - Rpower 2  (- 2.579) * Rpower 2 (-12.905) <= _); last first.
    boundDMI; first by rewrite /Q2; lra.
    boundDMI.
    apply: Rmult_le_compat; (try by interval); last by lra.
    by rewrite -[q]Rabs_pos_eq; lra.
  by interval.
have q'B : Rabs q' <= 0.50003.
  have FB : pow (emin + p - 1) <= Rabs (q * z + Q2).
    rewrite Rabs_pos_eq //.
    by apply: Rle_trans (bpow_ge_0 _ _) qzQ2B.
  apply: Rle_trans (_ : 
   (Rpower 2 (-2.579) * Rpower 2 (-12.905) + /2) *
      (1 + pow (- 52)) <= _); last by interval.
  apply: Rle_trans (_ : Rabs (q * z + Q2) * (1 + pow (- 52)) <= _).
    suff: Rabs (q' - (q * z + Q2)) < pow (- 52) * Rabs (q * z + Q2).
      by split_Rabs; lra.
    by apply: relative_error_FLT.
  apply: Rmult_le_compat_r; try (by apply: Rabs_pos); first by interval.
  boundDMI; last by rewrite Rabs_pos_eq /Q2; lra.
  boundDMI; last by lra.
  by lra.
pose Q' := Q4 * z ^ 2 + Q3 * z + Q2.
have q'B1 : pow (emin + p - 1) <= q'.
  rewrite -[q']Rabs_pos_eq; last first.
    rewrite -[0](round_0 beta fexp) //.
    apply: round_le.
    by apply: Rle_trans (bpow_ge_0 _ _) qzQ2B. 
  apply: format_Rabs_round_le => //.
  apply: generic_format_bpow => //.
  by rewrite Rabs_pos_eq //; apply: Rle_trans (bpow_ge_0 _ _) qzQ2B.
have q'_pos : 0 < q' by apply: Rlt_le_trans (bpow_gt_0 _ _) q'B1.
have q'Q'B : Rabs (q' - Q') <= Rpower 2 (- 52.999952).
  apply:  Rle_trans 
     (_ : pow (- 53) + pow (- 55) * Rpower 2 (- 12.905) <= _); 
     last by interval.
  apply: Rle_trans (_ : ulp q' + Rabs (q - Q) * Rabs z <= _).
    have -> : q' - Q' = (q' - (q * z + Q2)) + (q - Q) * z.
      by rewrite /Q' /Q; lra.
    boundDMI; last by rewrite Rabs_mult; lra.
    by apply: error_le_ulp_round.
  boundDMI; last first.
    by apply: Rmult_le_compat; try (by apply: Rabs_pos; lra); lra.
  rewrite ulp_neq_0; last by lra.
  rewrite /cexp /fexp Z.max_l.
    apply: bpow_le.
    suff : (mag beta q' <= 0)%Z by lia.
    apply: mag_le_bpow; first by lra.
    apply: Rle_lt_trans q'B _.
    by interval.
  suff : (emin + p <= mag beta q')%Z by lia.
  apply: mag_ge_bpow.
  by rewrite Rabs_pos_eq; lra.
have q'zQ1B1 : pow (emin + p - 1) <= q' * z + Q1.
  apply: Rle_trans (_: Q1 - q' * Rabs z <= _); last by split_Rabs; nra.
  apply: Rle_trans (_: 
    1 - 0.50003 * Rpower 2 (-12.905) <= _); last first.
    boundDMI; first by rewrite /Q1; lra.
    boundDMI.
    apply: Rmult_le_compat; (try by interval); last by lra.
    by rewrite -[q']Rabs_pos_eq; lra.
  by clear; interval.
have h0B1 : pow (emin + p - 1) <= h0.
  rewrite -[h0]Rabs_pos_eq; last first.
    rewrite -[0](round_0 beta fexp) //.
    apply: round_le.
    by apply: Rle_trans (bpow_ge_0 _ _) q'zQ1B1. 
  apply: format_Rabs_round_le => //.
  apply: generic_format_bpow => //.
  by rewrite Rabs_pos_eq //; apply: Rle_trans (bpow_ge_0 _ _) q'zQ1B1.
have h0_pos : 0 < h0 by apply: Rlt_le_trans (bpow_gt_0 _ _) h0B1.
have h0B : Rabs h0 <= 1.0001.
  apply: Rle_trans (_ : 
          (0.50003 * Rpower 2 (- 12.905) + 1) * (1 + pow (- 52)) <= _);
      last by interval.
  apply: Rle_trans (_ : Rabs (q' * z + Q1) * (1 + pow (- 52)) <= _).
    suff: Rabs (h0 - (q' * z + Q1)) < pow (- 52) * Rabs (q' * z + Q1).
      by split_Rabs; lra.
    apply: relative_error_FLT => //.
    by rewrite Rabs_pos_eq //; apply: Rle_trans (bpow_ge_0 _ _) q'zQ1B1.
  apply: Rmult_le_compat_r; try (by apply: Rabs_pos); first by interval.
  boundDMI; last by rewrite Rabs_pos_eq /Q1; lra.
  boundDMI; last by lra.
  by lra.
pose H0 := Q1 + Q' * z.
have h0H0B : Rabs (h0 - H0) <= Rpower 2 (- 51.999905).
  apply:  Rle_trans 
     (_ : pow (- 52) + Rpower 2 (- 52.999952) * Rpower 2 (- 12.905) <= _); 
     last by interval.
  apply: Rle_trans (_ : ulp h0 + Rabs (q' - Q') * Rabs z <= _).
    have -> : h0 - H0 = (h0 - (q' * z + Q1)) + (q' - Q') * z.
      by rewrite /H0 /Q' /Q1 /Q; lra.
    boundDMI; last by rewrite Rabs_mult; lra.
    by apply: error_le_ulp_round.
  boundDMI; last first.
    by apply: Rmult_le_compat; try (by apply: Rabs_pos; lra); lra.
  rewrite ulp_neq_0; last by lra.
  rewrite /cexp /fexp Z.max_l.
    apply: bpow_le.
    suff : (mag beta h0 <= 1)%Z by lia.
    apply: mag_le_bpow; first by lra.
    apply: Rle_lt_trans h0B _.
    by interval.
  suff : (emin + p <= mag beta h0)%Z by lia.
  apply: mag_ge_bpow.
  by rewrite Rabs_pos_eq; lra.
have h1l1E : Rabs (h1 + l1) <= Rabs (z * h0) + alpha.
  suff : let 'DWR h l := exactMul z h0 in Rabs (h + l - z * h0) < alpha.
    by rewrite Em; clear; split_Rabs; lra.
  apply: error_exactMul => //.
  by apply: generic_format_round.
Admitted.

End algoQ1.

