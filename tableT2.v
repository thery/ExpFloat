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

Section tableT2.

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

Definition T2 :=
 [::
    (              0x1p+0,                 0x0p+0);
    (0x1.000b175effdc7p+0,  0x1.ae8e38c59c72ap-54);
    (0x1.00162f3904052p+0, -0x1.7b5d0d58ea8f4p-58);
    (0x1.0021478e11ce6p+0,  0x1.4115cb6b16a8ep-54);
    (0x1.002c605e2e8cfp+0, -0x1.d7c96f201bb2fp-55);
    (0x1.003779a95f959p+0,  0x1.84711d4c35e9fp-54);
    (0x1.0042936faa3d8p+0, -0x1.0484245243777p-55);
    ( 0x1.004dadb113dap+0, -0x1.4b237da2025f9p-54);
    (0x1.0058c86da1c0ap+0, -0x1.5e00e62d6b30dp-56);
    (0x1.0063e3a559473p+0,  0x1.a1d6cedbb9481p-54);
    (0x1.006eff583fc3dp+0, -0x1.4acf197a00142p-54);
    (0x1.007a1b865a8cap+0, -0x1.eaf2ea42391a5p-57);
    (0x1.0085382faef83p+0,  0x1.da93f90835f75p-56);
    (0x1.00905554425d4p+0, -0x1.6a79084ab093cp-55);
    (0x1.009b72f41a12bp+0,  0x1.86364f8fbe8f8p-54);
    (0x1.00a6910f3b6fdp+0, -0x1.82e8e14e3110ep-55);
    (0x1.00b1afa5abcbfp+0, -0x1.4f6b2a7609f71p-55);
    (0x1.00bcceb7707ecp+0, -0x1.e1a258ea8f71bp-56);
    (0x1.00c7ee448ee02p+0,  0x1.4362ca5bc26f1p-56);
    (0x1.00d30e4d0c483p+0,  0x1.095a56c919d02p-54);
    (0x1.00de2ed0ee0f5p+0, -0x1.406ac4e81a645p-57);
    ( 0x1.00e94fd0398ep+0,  0x1.b5a6902767e09p-54);
    (0x1.00f4714af41d3p+0, -0x1.91b2060859321p-54);
    (0x1.00ff93412315cp+0,  0x1.427068ab22306p-55);
    (0x1.010ab5b2cbd11p+0,  0x1.c1d0660524e08p-54);
    (0x1.0115d89ff3a8bp+0, -0x1.e7bdfb3204be8p-54);
    (0x1.0120fc089ff63p+0,  0x1.843aa8b9cbbc6p-55);
    (0x1.012c1fecd613bp+0, -0x1.34104ee7edae9p-56);
    (0x1.0137444c9b5b5p+0, -0x1.2b6aeb6176892p-56);
    (0x1.01426927f5278p+0,  0x1.a8cd33b8a1bb3p-56);
    (0x1.014d8e7ee8d2fp+0,  0x1.2edc08e5da99ap-56);
    (0x1.0158b4517bb88p+0,  0x1.57ba2dc7e0c73p-55);
    (0x1.0163da9fb3335p+0,  0x1.b61299ab8cdb7p-54);
    (0x1.016f0169949edp+0, -0x1.90565902c5f44p-54);
    (0x1.017a28af25567p+0,  0x1.70fc41c5c2d53p-55);
    (0x1.018550706ab62p+0,  0x1.4b9a6e145d76cp-54);
    (0x1.019078ad6a19fp+0, -0x1.008eff5142bf9p-56);
    (0x1.019ba16628de2p+0, -0x1.77669f033c7dep-54);
    (0x1.01a6ca9aac5f3p+0, -0x1.09bb78eeead0ap-54);
    (0x1.01b1f44af9f9ep+0,  0x1.371231477ece5p-54);
    (0x1.01bd1e77170b4p+0,  0x1.5e7626621eb5bp-56);
    (0x1.01c8491f08f08p+0, -0x1.bc72b100828a5p-54);
    ( 0x1.01d37442d507p+0, -0x1.ce39cbbab8bbep-57);
    (0x1.01de9fe280ac8p+0,  0x1.16996709da2e2p-55);
    (0x1.01e9cbfe113efp+0, -0x1.c11f5239bf535p-55);
    (0x1.01f4f8958c1c6p+0,  0x1.e1d4eb5edc6b3p-55);
    (0x1.020025a8f6a35p+0, -0x1.afb99946ee3fp-54);
    (0x1.020b533856324p+0, -0x1.8f06d8a148a32p-54);
    (0x1.02168143b0281p+0, -0x1.2bf310fc54eb6p-55);
    (0x1.0221afcb09e3ep+0, -0x1.c95a035eb4175p-54);
    (0x1.022cdece68c4fp+0, -0x1.491793e46834dp-54);
    (0x1.02380e4dd22adp+0, -0x1.3e8d0d9c49091p-56);
    (0x1.02433e494b755p+0, -0x1.314aa16278aa3p-54);
    (0x1.024e6ec0da046p+0,  0x1.48daf888e9651p-55);
    (0x1.02599fb483385p+0,  0x1.56dc8046821f4p-55);
    (0x1.0264d1244c719p+0,  0x1.45b42356b9d47p-54);
    (0x1.027003103b10ep+0, -0x1.082ef51b61d7ep-56);
    (0x1.027b357854772p+0,  0x1.2106ed0920a34p-56);
    (0x1.0286685c9e059p+0, -0x1.fd4cf26ea5d0fp-54);
    (0x1.02919bbd1d1d8p+0, -0x1.09f8775e78084p-54);
    (0x1.029ccf99d720ap+0,  0x1.64cbba902ca27p-58);
    (0x1.02a803f2d170dp+0,  0x1.4383ef231d207p-54);
    (0x1.02b338c811703p+0,  0x1.4a47a505b3a47p-54);
    (0x1.02be6e199c811p+0,  0x1.e47120223467fp-54)
 ].

Definition F2R_conv := (F2R_conv1, F2R_conv2, F2R_conv3, F2R_conv4).

Lemma format_T2_h1 i : 
  (i <= 63)%N ->
   let h1 := (nth (0,0) T2 i).1 in format h1.
Proof.
case: i => [/= _|]; first by apply: format1_FLT.
by do 63
(case => [/= _|]; first by 
      rewrite /Q2R /= F2R_conv;
      apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _ => //).
Qed.

Lemma format_T2_l1 i : 
  (i <= 63)%N ->
   let l1 := (nth (0,0) T2 i).2 in format l1.
Proof.
case: i => [/= _|]; first by apply: generic_format_0.
by do 63
(case => [/= _|]; first by 
      rewrite /Q2R /= F2R_conv;
      apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _ => //).
Qed.

Lemma T2_h1B i : (i <= 63)%N ->
   let h1 := (nth (0,0) T2 i).1 in 1 <= h1 < 2.
Proof.
case: i => [/= _|]; first by split; (lra || interval).
by do 63 (case => [/=|]; first by
      split; (lra || interval)).
Qed.

Lemma T2_h1B1 i : (i <= 63)%N ->
   let h1 := (nth (0,0) T2 i).1 in h1 <= Rpower 2 (0.015381).
Proof.
case: i => [/= _|]; first by (lra || interval).
by do 63 (case => [/= _|]; first by (lra || interval)).
Qed.

Lemma T2_h1B2 i : (1 <= i <= 63)%N ->
   let h1 := (nth (0,0) T2 i).1 in 
   Rpower 2 (1 / 2 ^ 12) * (1 - pow (- 53)) <= h1.
Proof.
case: i => [//|].
by do 63 (case => [/= _|]; first by (lra || interval with (i_prec 70))).
Qed.


Lemma T2_l1B i : (i <= 63)%N ->
   let l1 := (nth (0,0) T2 i).2 in 
   (l1 <> 0 -> pow (- 58) <= Rabs l1 <= pow (- 53)).
Proof.
case: i => [/= H0|]; first by (split; lra || interval).
by do 63 (case => [/= _ _|]; first by (split; lra || interval)).
Qed.

Lemma T2_e1B i :
  (i <= 63)%N ->
   let h1 := (nth (0,0) T2 i).1 in 
   Rabs (h1 - Rpower 2 (INR i / pow 12)) <= pow (- 53).
Proof.
case: i => [/= _|]; first by interval.
by do 63 (case=> [/= _|]; first by interval with (i_prec 70)).
Qed.

Lemma T2_rel_error_h1l1 i : 
  (i <= 63)%N ->
   let: (h1, l1) := nth (0,0) T2 i in 
  Rabs ((h1 + l1) / Rpower 2 (INR i /pow 12) - 1) < Rpower 2 (- 107.0228).
Proof.
case: i => [/= _|]; first by interval with (i_prec 70).
by do 63 (case => [/= _|]; first by (interval with (i_prec 150))).
Qed.

End tableT2.

