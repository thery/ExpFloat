Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Plot Tactic.
Require Import Nmore Rmore Fmore Rstruct.

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

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Local Notation float := (float radix2).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format radix2 fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RN := (round beta fexp rnd).

(* Some sanity check *)
Let alpha := pow (- 1074).
Let alphaF : float := Float _ 1 emin.

Lemma alphaFE : F2R alphaF = alpha.
Proof.
by rewrite /alpha /alphaF /F2R /Q2R /= /Z.pow_pos /=; lra.
Qed.

Lemma format_alpha : format alpha.
Proof.
rewrite -alphaFE.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma alpha_gt_0 : 0 < alpha.
Proof.
rewrite /alpha !bpow_powerRZ !powerRZ_Rpower.
  by rewrite -[IZR beta]/2; interval with (i_prec 54).
by apply: IZR_lt.
Qed.

Lemma alpha_LB x : format x -> 0 < x -> alpha <= x.
Proof.
move=> fX xP.
have [f xE H1f H2f] : FLT_format beta emin p x by apply: FLT_format_generic.
rewrite xE -alphaFE.
rewrite /F2R -[bpow radix2 _]/(pow _).
rewrite -[Fexp alphaF]/emin -[Fnum alphaF]/1%Z.
apply: Rmult_le_compat; [lra| apply: bpow_ge_0 | idtac | apply: bpow_le] => //.
apply: IZR_le.
rewrite xE /F2R in xP.
have F1 : 0 < pow (Fexp f) by apply: bpow_gt_0.
have F2 : 0 < IZR (Fnum f) by nra.
suff: (0 < Fnum f)%Z by lia.
by apply: lt_IZR.
Qed.

Let omega := (1 - pow (-p)) * pow emax.
Let omegaF : float := Float _ (2 ^ p - 1) (emax - p).

Lemma omegaFE : F2R omegaF = omega.
Proof.
by rewrite /omega /omegaF /F2R /Q2R /= /Z.pow_pos /=; lra.
Qed.

Lemma omega_gt_alpha : alpha < omega.
Proof.
rewrite /omega /alpha !bpow_powerRZ !powerRZ_Rpower; try by apply: IZR_lt.
rewrite -[IZR beta]/2 -[IZR (- p)]/(-53) -[IZR emax]/1024.
interval with (i_prec 54).
Qed.

Lemma omega_gt_0 : 0 < omega.
Proof. by apply: Rlt_trans alpha_gt_0 omega_gt_alpha. Qed.

Lemma format_omega : format omega.
Proof.
rewrite -omegaFE.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma format1 : format 1.
Proof.
have -> : 1 = F2R (Float radix2 1 0) by rewrite /F2R /=; lra.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma ln_pow1022_le x : 
  format x -> 1 < x <= omega -> pow (- 1022) <= ln x <= omega.
Proof.
move=> Fx [x_gt_1 x_le_omega] ; split; last first.
  apply: Rle_trans (_ : ln omega <= _).
    by apply: ln_le; lra.
  rewrite /omega !bpow_powerRZ !powerRZ_Rpower.
  - rewrite -[IZR beta]/2 -[IZR (- p)]/(-53) -[IZR emax]/1024.
    interval with (i_prec 54).
  - by apply: IZR_lt.
  by apply: IZR_lt.
have sE : succ radix2 fexp 1 = 1 + Rpower 2 (-52).
  rewrite /succ /=.
  (case: Rle_bool_spec; try lra) => _.
  rewrite ulp_neq_0 //= /Generic_fmt.cexp mag_1 /fexp.
  rewrite -[Z.max _ _]/(-52)%Z.
  by rewrite bpow_powerRZ powerRZ_Rpower; last by apply: IZR_lt.
apply: Rle_trans (_ : ln (succ radix2 fexp 1) <= _).
  rewrite sE.
  by interval with (i_prec 54).
apply: ln_le; last by apply: succ_le_lt => //; apply: format1.
suff : 0 < Rpower 2 (- 52) by rewrite sE; lra.
rewrite -powerRZ_Rpower; last by lra.
apply: powerRZ_lt; lra.
Qed.

Lemma ln_pow1022_ge x : 
  format x -> alpha <= x < 1 -> - omega <= ln x <= - pow (- 1022).
Proof.
move=> Fx [x_ge_alpha x_lt_1] ; split.
  apply: Rle_trans (_ : ln alpha <= _); last first.
    apply: ln_le => //.
    by apply: alpha_gt_0.
  rewrite /alpha /omega !bpow_powerRZ !powerRZ_Rpower; try by apply: IZR_lt.
  rewrite -[IZR beta]/2 -[IZR (- p)]/(-53) -[IZR emax]/1024.
  interval with (i_prec 54).
have sE : pred radix2 fexp 1 = 1 - Rpower 2 (-53).
  rewrite /pred /= /succ.
  (case: Rle_bool_spec; try lra) => _.
  have -> : (- - (1) = 1)%R by lra.
  rewrite /pred_pos mag_1 /=.
  (case: Req_bool_spec; try lra) => _.
  rewrite /Z.pow_pos /=.
  rewrite -powerRZ_Rpower; last by apply: IZR_lt.
  by rewrite /powerRZ /=; lra.
apply: Rle_trans (_ : ln (pred radix2 fexp 1) <= _); last first.
  rewrite sE.
  rewrite bpow_powerRZ powerRZ_Rpower; last by apply: IZR_lt.
  rewrite -[IZR beta]/2.
  by interval with (i_prec 54).
apply: ln_le.
 by apply: Rlt_le_trans alpha_gt_0 x_ge_alpha.
rewrite -[x](@succ_pred_pos radix2 fexp) //; last first.
  by apply: Rlt_le_trans alpha_gt_0 _.
apply: succ_le_lt.
- by apply: generic_format_pred.
- by apply/generic_format_pred/format1.
apply: pred_lt => //.
by apply: format1.
Qed.

Definition RNF x : float :=
    {|
	Fnum := rnd (scaled_mantissa beta fexp x);
    Fexp := Generic_fmt.cexp beta fexp x
    |}.

Lemma RNFE x : RN x = F2R (RNF x).
Proof. by []. Qed.

Local Notation ulp := (ulp beta fexp).

Inductive dwfloat := DWFloat (xh : float) (xl : float).

Coercion F2R : float >-> R.

Definition exactMul (a b : float) : dwfloat := 
  let h := RNF (a * b) in 
  let l := RNF(a * b - h) in 
  DWFloat h l.
  
Definition fastTwoSum (a b : float) :=
  let s := RNF (a + b) in
  let z := RNF (s - a) in
  DWFloat s (RNF (b - z)).

Check fastTwoSum.

Definition twoSum (a : float) (b : dwfloat) :=  
  let: DWFloat bh bl := b in 
  let: DWFloat h t := fastTwoSum a bh in 
  let: l := RNF (t + bl) in DWFloat h l.

Check twoSum.

Definition P3 :=
  0.333333333333333481363069950020872056484222412109375.
Definition P4 := - 0.250000000000000166533453693773481063544750213623046875.
Definition P5 :=   0.1999999999569951614208918044823803938925266265869140625.
Definition P6 := - 0.16666666662262275000472300234832800924777984619140625.
Definition P7 :=   0.142861026799963208855359653171035461127758026123046875.
Definition P8 := - 0.125003701310396342361030974643654190003871917724609375.

Definition Pf3 : float := 
  Float _ 6004799503160664 (-54).

Definition Pf4 : float := 
  Float _ (-4503599627370499) (-54).
Definition Pf5 : float := 
  Float _ (7205759402243381) (-55).
Definition Pf6 : float := 
  Float _ (-6004799501573812) (-55).
Definition Pf7 : float := 
  Float _ (5147110936496646) (-55).
Definition Pf8 : float := 
  Float _ (-4503732981131470) (-55).

Fact Pf3E : F2R Pf3 = P3.
Proof.
by rewrite /P3 /F2R /Q2R /= /Z.pow_pos /=; field.
Qed.

Lemma format_P3 : format P3.
Proof.
rewrite -Pf3E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Pf4E : F2R Pf4 = P4.
Proof.
by rewrite /P4 /F2R /Q2R /= /Z.pow_pos /=; field.
Qed.

Lemma format_P4 : format P4.
Proof.
rewrite -Pf4E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Pf5E : F2R Pf5 = P5.
Proof.
by rewrite /P5 /F2R /Q2R /= /Z.pow_pos /=; field.
Qed.

Lemma format_P5 : format P5.
Proof.
rewrite -Pf5E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Pf6E : F2R Pf6 = P6.
Proof.
by rewrite /P6 /F2R /Q2R /= /Z.pow_pos /=; field.
Qed.

Lemma format_P6 : format P6.
Proof.
rewrite -Pf6E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Pf7E : F2R Pf7 = P7.
Proof.
by rewrite /P7 /F2R /Q2R /= /Z.pow_pos /=; field.
Qed.

Lemma format_P7 : format P7.
Proof.
rewrite -Pf7E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Pf8E : F2R Pf8 = P8.
Proof.
by rewrite /P8 /F2R /Q2R /= /Z.pow_pos /=; field.
Qed.

Lemma format_P8 : format P8.
Proof.
rewrite -Pf8E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Definition P z :=
    z - z ^ 2 / 2 + P3 * z ^ 3 
    + P4 * z ^ 4 + P5 * z ^ 5 + P6 * z ^ 6 + P7 * z ^ 7 + P8 * z ^ 8. 

Definition Pz z :=
    1 - z / 2 + P3 * z ^ 2 
  + P4 * z ^ 3 + P5 * z ^ 4 + P6 * z ^ 5 + P7 * z ^ 6 + P8 * z ^ 7. 

Lemma PzE z : P z = z * Pz z.
Proof. by rewrite /Pz /P; lra. Qed.

Lemma Pz_pos z :
  Rabs z < 33 * (Rpower 2 (-13)) -> 0 <= Pz z.
Proof.
by move=> *; rewrite /Pz /P3 /P4 /P5 /P6 /P7 /P8; interval.
Qed.

Lemma P_abs_error z :
  Rabs z < 33 * (Rpower 2 (-13)) ->
  Rabs (ln (1 + z) - P z) <= Rpower 2 (- (81.63)).
Proof.
move=> *; rewrite /P /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 90, i_bisect z, i_taylor z, i_degree 8).
Qed.

Lemma derive_ln_1px x : 
  -1 < x -> is_derive (fun x => ln (1 + x)) x (1 / (1 + x)).
Proof. by move=> *; auto_derive; lra. Qed.

Lemma ln_bound_pos e x : 
  0 < e < 1 -> 0 <= x < e -> 
  1 / (1 + e) * x <= ln (1 + x) <=  x * (1 / (1 - e)).
Proof.
move=> Be Bx.
case: (MVT_cor4 (fun x => ln (1 + x)) (fun x => 1 / (1 + x)) 
         0 e _ x) => [||c].
- by move=> c Hc; apply: derive_ln_1px; split_Rabs; lra.
- by split_Rabs; lra.
rewrite !(ln_1, Rsimp01) => [] [-> H2c].
suff: / (1 + e) <= / (1 + c) <= / (1 - e) by nra.
split; apply: Rinv_le_contravar; split_Rabs; nra.
Qed.

Lemma Pz_bound_pos e x : 
  0 < e < 33 * (Rpower 2 (-13)) -> 0 < x < e -> 
  Pz x * (1 - e) <= P x / ln (1 + x) <=  Pz x * (1 + e).
Proof.
move=> Be Bx.
have pow_gt1 : 33 * (Rpower 2 (-13)) < 1 by interval.
have Pz_ge0 : 0 <= Pz x by apply: Pz_pos; split_Rabs; lra.
suff: (1 - e) <= x / ln (1 + x) <= (1 + e) by rewrite PzE; nra.
have Hf : 1 / (1 + e) * x <= ln (1 + x) <=  x * (1 / (1 - e)).
  by apply: ln_bound_pos; lra.
have ln_gt0 : 0 < ln (1 + x) by rewrite -ln_1; apply: ln_increasing; lra.
split.
  apply/Rle_div_r => //.
  by rewrite Rmult_comm; apply/Rle_div_r; lra.
apply/Rle_div_l => //.
by rewrite Rmult_comm; apply/Rle_div_l; lra.
Qed.

Lemma ln_bound_neg e x : 
  0 < e < 1 -> -e < x <= 0 -> 
  1 / (1 - e) * x <= ln (1 + x) <=  x * (1 / (1 + e)).
Proof.
move=> Be Bx.
case: (MVT_cor4 (fun x => ln (1 + x)) (fun x => 1 / (1 + x)) 
         0 e _ x) => [||c].
- by move=> c Hc; apply: derive_ln_1px; split_Rabs; lra.
- by split_Rabs; lra.
rewrite !(ln_1, Rsimp01) => [] [-> H2c].
suff: / (1 + e) <= / (1 + c) <= / (1 - e) by nra.
split; apply: Rinv_le_contravar; split_Rabs; nra.
Qed.

Lemma Pz_bound_neg e x : 
  0 < e < 33 * (Rpower 2 (-13)) -> -e < x < 0 -> 
  Pz x * (1 - e) <= P x / ln (1 + x) <=  Pz x * (1 + e).
Proof.
move=> Be Bx.
have pow_gt1 : 33 * (Rpower 2 (-13)) < 1 by interval.
have Pz_ge0 : 0 <= Pz x by apply: Pz_pos; split_Rabs; lra.
suff: (1 - e) <= x / ln (1 + x) <= (1 + e) by rewrite PzE; nra.
have Hf : 1 / (1 - e) * x <= ln (1 + x) <=  x * (1 / (1 + e)).
  by apply: ln_bound_neg; lra.
have ln_gt0 : ln (1 + x) < 0 by rewrite -ln_1; apply: ln_increasing; lra.
have-> : x / ln (1 + x) = (- x) / (- ln (1 + x)) by field; lra.
split.
  apply/Rle_div_r; try lra.
  by rewrite Rmult_comm; apply/Rle_div_r; lra.
apply/Rle_div_l; try lra.
by rewrite Rmult_comm; apply/Rle_div_l; lra.
Qed.

Lemma PPz1_bound_pos x : 
let e := Rpower 2 (-80) in 
   0 < x < e ->  - (Rpower 2 (-(72.423))) <  1 - Pz x * (1 + e).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz2_bound_pos x : 
let e := Rpower 2 (-80) in 
   0 < x < e ->  1 - Pz x * (1 + e) < (Rpower 2 (-(72.423))).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz3_bound_pos x : 
let e := Rpower 2 (-80) in 
   0 < x < e ->  1 - Pz x * (1 - e) < (Rpower 2 (-(72.423))).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz4_bound_pos x : 
let e := Rpower 2 (-80) in 
   0 < x < e ->  - (Rpower 2 (-(72.423))) <  1 - Pz x * (1 - e).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz1_bound_neg x : 
let e := Rpower 2 (-80) in 
   -e < x < 0 ->  - (Rpower 2 (-(72.423))) <  1 - Pz x * (1 + e).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz2_bound_neg x : 
let e := Rpower 2 (-80) in 
   -e < x < 0 ->  1 - Pz x * (1 + e) < (Rpower 2 (-(72.423))).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz3_bound_neg x : 
let e := Rpower 2 (-80) in 
   -e < x < 0 ->  1 - Pz x * (1 - e) < (Rpower 2 (-(72.423))).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz4_bound_neg x : 
let e := Rpower 2 (-80) in 
   -e < x < 0 ->  - (Rpower 2 (-(72.423))) <  1 - Pz x * (1 - e).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.


Lemma PPz_bound_pos x : 
let e := Rpower 2 (-80) in 
   0 < x < e ->  
   Rabs (1 - P x / ln (1 + x)) < Rpower 2 (-(72.423)).
Proof.
move=>e He.
have Pz_ge0 : 0 <= Pz x.
  apply: Pz_pos.
  by rewrite /e in He; interval.
have H1e : 0 < 1 - e
  by rewrite /e in He; interval.
have :  Pz x * (1 - e) <= P x / ln (1 + x) <=  Pz x * (1 + e).
  apply: Pz_bound_pos => //.
  by rewrite /e; split; interval.
have := PPz1_bound_pos He.
have := PPz2_bound_pos He.
have := PPz3_bound_pos He.
have := PPz4_bound_pos He.
by rewrite /e; split_Rabs; lra.
Qed.

Lemma PPz_bound_neg x : 
let e := Rpower 2 (-80) in 
   -e < x < 0 ->  
   Rabs (1 - P x / ln (1 + x)) < Rpower 2 (-(72.423)).
Proof.
move=>e He.
have Pz_ge0 : 0 <= Pz x.
  apply: Pz_pos.
  by rewrite /e in He; interval.
have H1e : 0 < 1 - e
  by rewrite /e in He; interval.
have :  Pz x * (1 - e) <= P x / ln (1 + x) <=  Pz x * (1 + e).
  apply: Pz_bound_neg => //.
  by rewrite /e; split; interval.
have := PPz1_bound_neg He.
have := PPz2_bound_neg He.
have := PPz3_bound_neg He.
have := PPz4_bound_neg He.
by rewrite /e; split_Rabs; lra.
Qed.

Lemma PPz_bound x : 
   Rabs x < Rpower 2 (-80) ->  
   Rabs ((ln(1 + x) - P x) / ln (1 + x)) < Rpower 2 (-(72.423)).
Proof.
move=> He.
have [H1 | [->|H1]] : 
  0 < x < Rpower 2 (-80) \/ x = 0 \/ - Rpower 2 (-80) < x < 0.
- by split_Rabs; lra.
- have-> : (ln (1 + x) - P x) / ln (1 + x) = 1 - P x / ln (1 + x).
    field.
    suff : 0 < ln (1 + x) by lra.
    by rewrite -ln_1; apply: ln_increasing; lra.
  by apply: PPz_bound_pos.
- rewrite !(ln_1, Rsimp01); interval.
have-> : (ln (1 + x) - P x) / ln (1 + x) = 1 - P x / ln (1 + x).
  field.
  suff : ln (1 + x) < 0 by lra.
  rewrite -ln_1; apply: ln_increasing; try lra.
  interval.
by apply: PPz_bound_neg.
Qed.

Lemma P_rel_error_pos z :
  Rpower 2 (-80) <= z <  33 * Rpower 2 (-13) ->
  Rabs ((ln (1 + z) - P z) /
   (ln (1 + z))) < Rpower 2 (-(72.423)).
Proof.
intros.
interval with (i_prec 200, i_depth 50,
   i_bisect z, i_taylor z, i_degree 20).
Qed.

Lemma P_rel_error_neg z :
  - 33 * Rpower 2 (-13) < z <= - Rpower 2 (-80) ->
  Rabs ((ln (1 + z) - P z) /
   (ln (1 + z))) < Rpower 2 (-(72.423)).
Proof.
intros.
interval with (i_prec 200, i_depth 50,
   i_bisect z, i_taylor z, i_degree 20).
Qed.

Lemma P_rel_error z :
  Rabs z < 33 * Rpower 2 (-13)  ->
  Rabs ((ln (1 + z) - P z) /
   (ln (1 + z))) < Rpower 2 (-(72.423)).
Proof.
move=> H.
have [H1 | H1 ]: Rpower 2 (-80) <= Rabs z \/ Rabs z < Rpower 2 (-80) 
  by lra.
  rewrite /Rabs in H H1.
  move: H H1; case: Rcase_abs => H2 H H1.
    by apply: P_rel_error_neg; lra.
  by apply: P_rel_error_pos; lra.
by apply: PPz_bound.
Qed.

(* L'algo p_1 *)

Definition p1 (z : float) :=
  let: DWFloat wh wl := exactMul z z in 
  let: t := RNF (Pf8 * z + Pf7) in
  let: u := RNF (Pf6 * z + Pf5) in
  let: v := RNF (Pf4 * z + Pf3) in
  let: u := RNF (t * wh + u) in 
  let: v := RNF (u * wh + v) in 
  let: u := RNF (v * wh) in 
  DWFloat (RNF (- 0.5 * wh))
          (RNF (u * z - 0.5 * wl)).

End Exp.
