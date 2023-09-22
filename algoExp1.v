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

End algoExp1.

