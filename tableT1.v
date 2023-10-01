Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Interval Require Import Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section tableT1.

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

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Local Notation ulp := (ulp beta fexp).

Lemma F2R_conv1 x y :  
  IZR x * / 4503599627370496 / IZR (Z.pow_pos 2 y) = 
  F2R (Float beta x (- 52 - Zpos y)).
Proof.
rewrite /F2R [Fnum _]/= -[Fexp _]/(- (52) - Z.pos y)%Z.
by rewrite bpow_plus !bpow_opp -Rmult_assoc.
Qed.

Lemma F2R_conv2 x y :  
  IZR x * / 281474976710656 / IZR (Z.pow_pos 2 y) = 
  F2R (Float beta x (- 48 - Zpos y)).
Proof.
rewrite /F2R [Fnum _]/= -[Fexp _]/(- (48) - Z.pos y)%Z.
by rewrite bpow_plus !bpow_opp -Rmult_assoc.
Qed.

Lemma F2R_conv3 x :  
  IZR x * / 4503599627370496 = F2R (Float beta x (- 52)).
Proof. by rewrite /F2R [Fnum _]/= -[Fexp _]/(- (52))%Z !bpow_opp. Qed.

Lemma F2R_conv4 x :  
  IZR x * / 281474976710656 = F2R (Float beta x (- 48)).
Proof. by rewrite /F2R [Fnum _]/= -[Fexp _]/(- (48))%Z !bpow_opp. Qed.

Definition T1 :=
 [::
    (              0x1p+0,                 0x0p+0);
    (0x1.02c9a3e778061p+0, -0x1.19083535b085dp-56);
    (0x1.059b0d3158574p+0,  0x1.d73e2a475b465p-55);
    (0x1.0874518759bc8p+0,  0x1.186be4bb284ffp-57);
    (0x1.0b5586cf9890fp+0,  0x1.8a62e4adc610bp-54);
    (0x1.0e3ec32d3d1a2p+0,  0x1.03a1727c57b53p-59);
    (0x1.11301d0125b51p+0, -0x1.6c51039449b3ap-54);
    ( 0x1.1429aaea92dep+0, -0x1.32fbf9af1369ep-54);
    (0x1.172b83c7d517bp+0, -0x1.19041b9d78a76p-55);
    (0x1.1a35beb6fcb75p+0,  0x1.e5b4c7b4968e4p-55);
    (0x1.1d4873168b9aap+0,  0x1.e016e00a2643cp-54);
    (0x1.2063b88628cd6p+0,  0x1.dc775814a8495p-55);
    (0x1.2387a6e756238p+0,  0x1.9b07eb6c70573p-54);
    (0x1.26b4565e27cddp+0,  0x1.2bd339940e9d9p-55);
    (0x1.29e9df51fdee1p+0,  0x1.612e8afad1255p-55);
    (0x1.2d285a6e4030bp+0,  0x1.0024754db41d5p-54);
    (0x1.306fe0a31b715p+0,  0x1.6f46ad23182e4p-55);
    (0x1.33c08b26416ffp+0,  0x1.32721843659a6p-54);
    (0x1.371a7373aa9cbp+0, -0x1.63aeabf42eae2p-54);
    (0x1.3a7db34e59ff7p+0, -0x1.5e436d661f5e3p-56);
    (0x1.3dea64c123422p+0,  0x1.ada0911f09ebcp-55);
    (0x1.4160a21f72e2ap+0, -0x1.ef3691c309278p-58);
    (0x1.44e086061892dp+0,   0x1.89b7a04ef80dp-59);
    ( 0x1.486a2b5c13cdp+0,   0x1.3c1a3b69062fp-56);
    (0x1.4bfdad5362a27p+0,  0x1.d4397afec42e2p-56);
    (0x1.4f9b2769d2ca7p+0, -0x1.4b309d25957e3p-54);
    (0x1.5342b569d4f82p+0, -0x1.07abe1db13cadp-55);
    (0x1.56f4736b527dap+0,  0x1.9bb2c011d93adp-54);
    (0x1.5ab07dd485429p+0,  0x1.6324c054647adp-54);
    (0x1.5e76f15ad2148p+0,  0x1.ba6f93080e65ep-54);
    (0x1.6247eb03a5585p+0, -0x1.383c17e40b497p-54);
    (0x1.6623882552225p+0, -0x1.bb60987591c34p-54);
    (0x1.6a09e667f3bcdp+0, -0x1.bdd3413b26456p-54);
    (0x1.6dfb23c651a2fp+0, -0x1.bbe3a683c88abp-57);
    (0x1.71f75e8ec5f74p+0, -0x1.16e4786887a99p-55);
    (0x1.75feb564267c9p+0, -0x1.0245957316dd3p-54);
    (0x1.7a11473eb0187p+0, -0x1.41577ee04992fp-55);
    (0x1.7e2f336cf4e62p+0,  0x1.05d02ba15797ep-56);
    (0x1.82589994cce13p+0, -0x1.d4c1dd41532d8p-54);
    (0x1.868d99b4492edp+0, -0x1.fc6f89bd4f6bap-54);
    (0x1.8ace5422aa0dbp+0,  0x1.6e9f156864b27p-54);
    (0x1.8f1ae99157736p+0,  0x1.5cc13a2e3976cp-55);
    (0x1.93737b0cdc5e5p+0, -0x1.75fc781b57ebcp-57);
    ( 0x1.97d829fde4e5p+0, -0x1.d185b7c1b85d1p-54);
    ( 0x1.9c49182a3f09p+0,  0x1.c7c46b071f2bep-56);
    (0x1.a0c667b5de565p+0, -0x1.359495d1cd533p-54);
    (0x1.a5503b23e255dp+0, -0x1.d2f6edb8d41e1p-54);
    (0x1.a9e6b5579fdbfp+0,  0x1.0fac90ef7fd31p-54);
    (0x1.ae89f995ad3adp+0,  0x1.7a1cd345dcc81p-54);
    (0x1.b33a2b84f15fbp+0, -0x1.2805e3084d708p-57);
    (0x1.b7f76f2fb5e47p+0, -0x1.5584f7e54ac3bp-56);
    (0x1.bcc1e904bc1d2p+0,  0x1.23dd07a2d9e84p-55);
    (0x1.c199bdd85529cp+0,  0x1.11065895048ddp-55);
    (0x1.c67f12e57d14bp+0,  0x1.2884dff483cadp-54);
    (0x1.cb720dcef9069p+0,  0x1.503cbd1e949dbp-56);
    (0x1.d072d4a07897cp+0, -0x1.cbc3743797a9cp-54);
    (0x1.d5818dcfba487p+0,  0x1.2ed02d75b3707p-55);
    (0x1.da9e603db3285p+0,  0x1.c2300696db532p-54);
    (0x1.dfc97337b9b5fp+0, -0x1.1a5cd4f184b5cp-54);
    (0x1.e502ee78b3ff6p+0,  0x1.39e8980a9cc8fp-55);
    (0x1.ea4afa2a490dap+0, -0x1.e9c23179c2893p-54);
    (0x1.efa1bee615a27p+0,   0x1.dc7f486a4b6bp-54);
    ( 0x1.f50765b6e454p+0,  0x1.9d3e12dd8a18bp-54);
    (0x1.fa7c1819e90d8p+0,  0x1.74853f3a5931ep-55)
 ].

Definition F2R_conv := (F2R_conv1, F2R_conv2, F2R_conv3, F2R_conv4).

Lemma format_T1_h2 i : 
  (i <= 63)%N ->
   let h2 := (nth (0,0) T1 i).1 in format h2.
Proof.
case: i => [/= _|]; first by apply: format1.
by do 63
(case => [/= _|]; first by 
      rewrite /Q2R /= F2R_conv;
      apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _ => //).
Qed.

Lemma format_T1_l2 i : 
  (i <= 63)%N ->
   let l2 := (nth (0,0) T1 i).2 in format l2.
Proof.
case: i => [/= _|]; first by apply: generic_format_0.
by do 63
(case => [/= _|]; first by 
      rewrite /Q2R /= F2R_conv;
      apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _ => //).
Qed.

Lemma T1_h2B i : (i <= 63)%N ->
   let h2 := (nth (0,0) T1 i).1 in 1 <= h2 < 2.
Proof.
case: i => [/= _|]; first by split; (lra || interval).
by do 63 (case => [/=|]; first by
      split; (lra || interval)).
Qed.

Lemma T1_h2B1 i : (i <= 63)%N ->
   let h2 := (nth (0,0) T1 i).1 in h2 <= Rpower 2 0.984376.
Proof.
case: i => [/= _|]; first by (lra || interval).
by do 63 (case => [/= _|]; first by (lra || interval)).
Qed.

Lemma T1_h2B2 i : (1 <= i <= 63)%N ->
   let h2 := (nth (0,0) T1 i).1 in 
   Rpower 2 (1 / 2 ^ 6) * (1 - pow (- 53)) <= h2.
Proof.
case: i => [//|].
by do 63 (case => [/= _|]; first by (lra || interval with (i_prec 70))).
Qed.

Lemma T1_l2B i : (i <= 63)%N ->
   let l2 := (nth (0,0) T1 i).2 in 
   (l2 <> 0 -> Rpower 2 (- 58.98) <= Rabs l2 <= pow (- 53)).
Proof.
case: i => [/= H0|]; first by (split; lra || interval).
by do 63 (case => [/= _ _|]; first by (split; lra || interval)).
Qed.

Lemma T1_e2B i :
  (i <= 63)%N ->
   let h2 := (nth (0,0) T1 i).1 in 
   Rabs (h2 - Rpower 2 (INR i / pow 6)) <= pow (- 53).
Proof.
case: i => [/= _|]; first by interval.
by do 63 (case=> [/= _|]; first by interval with (i_prec 70)).
Qed.

Lemma T1_rel_error_h2l2 i : 
  (i <= 63)%N ->
   let: (h2, l2) := nth (0,0) T1 i in 
  Rabs ((h2 + l2) / Rpower 2 (INR i /pow 6) - 1) < Rpower 2 (- 107.57149).
Proof.
case: i => [/= _|]; first by interval with (i_prec 70).
by do 63 (case => [/= _|]; first by (interval with (i_prec 150))).
Qed.

End tableT1.

