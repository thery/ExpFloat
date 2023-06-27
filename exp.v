Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore.

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

Definition wellFormed d :=
  let: DWFloat xh xl := d in RN(xh + xl) = xh.

Definition exactMul (a b : float) : dwfloat := 
  let h := RNF (a * b) in 
  let l := RNF(a * b - h) in 
  DWFloat h l.
  
Lemma exactMul_correct (a b : float) :
  format a -> format b -> is_imul (a * b) (pow emin) ->
  let: DWFloat h l := exactMul a b in 
  h + l = a * b.
Proof.
move=> Fa Fb Mab /=.
rewrite -!RNFE -Ropp_minus_distr round_opp.
rewrite [X in -X]round_generic //; first by lra.
by apply: MULTmore.exactMul.
Qed.

Lemma exactMul_wf (a b : float) : 
  format a -> format b -> is_imul (a * b) (pow emin) ->
  wellFormed (exactMul a b).
Proof. by move=> Fa Fb Mab /=; rewrite /= -!RNFE exactMul_correct. Qed.

Definition fastTwoSum (a b : float) :=
  let s := RNF (a + b) in
  let z := RNF (s - a) in
  DWFloat s (RNF (b - z)).

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
  Rabs z <= 33 * (Rpower 2 (-13)) ->
  Rabs (ln (1 + z) - P z) <= Rpower 2 (- 81.63).
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
let e := Rpower 2 (- 80) in 
   0 < x < e ->  - (Rpower 2 (- 72.423)) <  1 - Pz x * (1 + e).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz2_bound_pos x : 
let e := Rpower 2 (-80) in 
   0 < x < e ->  1 - Pz x * (1 + e) < (Rpower 2 (- 72.423)).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz3_bound_pos x : 
let e := Rpower 2 (-80) in 
   0 < x < e ->  1 - Pz x * (1 - e) < (Rpower 2 (- 72.423)).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz4_bound_pos x : 
let e := Rpower 2 (-80) in 
   0 < x < e ->  - (Rpower 2 (- 72.423)) <  1 - Pz x * (1 - e).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz1_bound_neg x : 
let e := Rpower 2 (-80) in 
   -e < x < 0 ->  - (Rpower 2 (- 72.423)) <  1 - Pz x * (1 + e).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz2_bound_neg x : 
let e := Rpower 2 (-80) in 
   -e < x < 0 ->  1 - Pz x * (1 + e) < (Rpower 2 (- 72.423)).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz3_bound_neg x : 
let e := Rpower 2 (-80) in 
   -e < x < 0 ->  1 - Pz x * (1 - e) < (Rpower 2 (- 72.423)).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.

Lemma PPz4_bound_neg x : 
let e := Rpower 2 (-80) in 
   -e < x < 0 ->  - (Rpower 2 (- 72.423)) <  1 - Pz x * (1 - e).
Proof.
move=> e *; rewrite /e /Pz /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 80).
Qed.


Lemma PPz_bound_pos x : 
let e := Rpower 2 (-80) in 
   0 < x < e ->  
   Rabs (1 - P x / ln (1 + x)) < Rpower 2 (- 72.423).
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
   Rabs (1 - P x / ln (1 + x)) < Rpower 2 (- 72.423).
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
   Rabs ((ln(1 + x) - P x) / ln (1 + x)) < Rpower 2 (- 72.423).
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
  Rpower 2 (-80) <= z <=  33 * Rpower 2 (-13) ->
  Rabs ((ln (1 + z) - P z) /
   (ln (1 + z))) < Rpower 2 (- 72.423).
Proof.
(*
intros.
interval with (i_prec 200, i_depth 50,
   i_bisect z, i_taylor z, i_degree 20).
Qed.
*)
Admitted.

Lemma P_rel_error_neg z :
  - 33 * Rpower 2 (-13) <= z <= - Rpower 2 (-80) ->
  Rabs ((ln (1 + z) - P z) /
   (ln (1 + z))) < Rpower 2 (- 72.423).
Proof.
(*
intros.
interval with (i_prec 200, i_depth 50,
   i_bisect z, i_taylor z, i_degree 20).
Qed.
*)
Admitted.

Lemma P_rel_error z :
  Rabs z <= 33 * Rpower 2 (-13)  ->
  Rabs ((ln (1 + z) - P z) /
   (ln (1 + z))) < Rpower 2 (- 72.423).
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

Lemma pow_Rpower z : pow z = Rpower 2 (IZR z).
Proof.
by rewrite bpow_powerRZ powerRZ_Rpower //; apply: IZR_lt.
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

Lemma is_imul_pow_round x y : is_imul x (pow y) -> is_imul (RN x) (pow y).
Proof.
move=> [k ->].
rewrite /round /mant /F2R /=.
set e1 := cexp _; set m1 := rnd _.
have [e1L|yLe1] := Zle_or_lt e1 y.
  exists k.
  rewrite /m1.
  have -> : IZR k * pow y * pow (- e1) = IZR (k * beta ^ (y - e1)).
    rewrite Rmult_assoc -bpow_plus -IZR_Zpower; last by lia.
    by rewrite -mult_IZR.
  rewrite Zrnd_IZR.
  rewrite mult_IZR IZR_Zpower; last by lia.
  by rewrite Rmult_assoc -bpow_plus; congr (_ * pow _); lia.
exists ((rnd (IZR k * pow (y - e1))%R) * beta ^ (e1 - y))%Z.
rewrite mult_IZR IZR_Zpower; try lia.
rewrite /m1 Rmult_assoc -bpow_plus.
rewrite  Rmult_assoc -bpow_plus.
congr (_ * pow _); lia.
Qed.

Lemma powN1 : pow (-1) = 0.5.
Proof. by rewrite /= /Z.pow_pos /=; lra. Qed.

Lemma is_imul_format_half x y : 
  format x -> is_imul x (pow y) -> (emin + p <= y)%Z -> format (0.5 * x).
Proof.
move=> Fx Mxy eminLy.
case:(Req_dec x 0)=> [->| xn0].
  by rewrite Rmult_0_r;apply/generic_format_0.
have ->: 0.5 * x = (x * (pow (-1))) by rewrite Rmult_comm powN1.
apply: mult_bpow_exact_FLT => //.
have := is_imul_pow_mag xn0 Mxy; rewrite /beta; lia.
Qed.

Lemma is_imul_format_round_gt_0 x y : 
  0 < x -> is_imul x (pow y) -> (emin <= y)%Z -> 0 < RN x.
Proof.
move=> x_gt_0 Mx eminpLy.
pose f := Float beta 1 emin.
have Ff : format (Float beta 1 emin).
  apply: generic_format_FLT.
  by apply: FLT_spec (refl_equal _) _ _.
have fE : F2R f = pow emin by rewrite /f /F2R /= /Z.pow_pos /=; lra.
suff : RN f <= RN x.
  rewrite round_generic // /F2R /= /Z.pow_pos //=; lra.
apply: round_le.
rewrite fE.
apply: Rle_trans (_ : pow y <= _); first by apply: bpow_le; lia.
have [k kE] := Mx; rewrite kE in x_gt_0 *.
have F2 : 0 < pow y by apply: bpow_gt_0.
have F3 : (0 < k)%Z by apply: lt_IZR; nra.
have/IZR_le : (1 <= k)%Z by lia.
nra.
Qed.

Lemma relative_error_is_min_eps x y :
  (emin <= y)%Z -> is_imul x (pow y) ->
  exists eps : R, Rabs eps < 2 * u /\ RN x = x * (1 + eps).
Proof.
move=> eLy [z ->].
pose x1 := Float beta (z * beta ^ (y - emin))%Z emin.
have <- : F2R x1 = IZR z * pow y.
  rewrite /F2R mult_IZR IZR_Zpower; last by lia.
  rewrite Rmult_assoc -bpow_plus [Fexp _]/=.
  congr (_ * pow _); lia.
have -> : 2 * u = pow (- p + 1).
  rewrite bpow_plus pow1E  -[IZR beta]/2 uE; lra.
by apply: relative_error_FLT_F2R_emin_ex.
Qed.

Lemma relative_error_is_min_eps_bound x y eps :
  (emin <= y)%Z -> is_imul x (pow y) -> x <> 0 ->
  RN x = x * (1 + eps) -> Rabs eps < 2 * u.
Proof.
move=> eLy Mxy x_neq_0 HRN.
have [eps1 [Heps1 H1eps1]] := relative_error_is_min_eps eLy Mxy.
by have <- : eps1 = eps by nra.
Qed.

Lemma absolute_rel_error_p1 (z : float) :
  format z -> 
  Rabs z <= 33 * Rpower 2 (-13) ->
  is_imul z (Rpower 2 (-61)) ->
  let: DWFloat ph pl := p1 z in 
  (Rabs((ph + pl) - (ln (1 + z) - z)) < Rpower 2 (-75.492) /\ 
   Rabs ph < Rpower 2 (-16.9) /\
   Rabs pl < Rpower 2 (-25.446)) /\ 
  (F2R z <> 0%R ->   Rabs z < 32 * Rpower 2 (-13) ->
    Rabs ((z + ph + pl) / ln (1 + z) -1) < Rpower 2 (- 67.441)).
Proof.
move=> Fz zB Mz /=.
rewrite -!RNFE.
rewrite -pow_Rpower in Mz.
set wh := RN (z * z).
set wl := RN (z * z - wh).
set t := RN (Pf8 * z + Pf7).
set u := RN (Pf6 * z + Pf5).
set v := RN (Pf4 * z + Pf3).
set u' := RN (t * wh + u).
set v' := RN (u' * wh + v).
set u'' := RN (v' * wh).
set ph := RN (-0.5 * wh).
set pl := RN (u'' * z - 0.5 * wl).
have Fwh : format wh by apply: generic_format_round.
have [z_eq0 | z_neq0] := Req_dec z 0.
  have wh_eq0 : wh = 0 by rewrite /wh z_eq0 Rmult_0_l round_0.
  have wl_eq0 : wl = 0 by rewrite /wl z_eq0 wh_eq0 !(round_0, Rsimp01).
  have -> : ph = 0 by rewrite /ph wh_eq0 !(round_0, Rsimp01).
  have -> : pl = 0 by rewrite /pl z_eq0 wl_eq0 !(round_0, Rsimp01).
  split; last by lra.
  by rewrite z_eq0 !(Rsimp01, ln_1); repeat split; interval.
have wh_gt_0 : 0 < wh.
  have G1 : is_imul (z * z) (pow (-122)).
    have -> : pow (-122) = pow (-61) * pow (-61) by rewrite -bpow_plus.
    by apply: is_imul_mul.
  by apply: is_imul_format_round_gt_0 _ G1 _ => //=; nra.
have F1 : wh + wl = z * z.
  apply: exactMul_correct => //.
  have [k ->] := Mz.
  exists (k * k * 2 ^ 952)%Z.
  rewrite 2!mult_IZR.
  suff : pow (-61) * pow (-61) = IZR (2 ^ 952) * pow emin by nra.
  by rewrite -!bpow_plus (IZR_Zpower beta) // -bpow_plus.
have F2 : z ^ 2 <= 33 ^ 2 * Rpower 2 (-26).
  have -> : Rpower 2 (-26) = (Rpower 2 (-13)) ^ 2.
    by rewrite pow2_mult -Rpower_plus; congr (Rpower _ _); lra.
  rewrite -Rpow_mult_distr.
  by apply: pow_maj_Rabs.
have F3 : z ^ 2 < Rpower 2 (- 15.91).
  by apply: Rle_lt_trans F2 _; interval.
have F4 : ulp(z ^ 2) <= Rpower 2 (-68).
  apply: Rle_trans (_ : ulp (33 ^ 2 * Rpower 2 (-26)) <= _).
    apply: ulp_le => //.
    by rewrite !Rabs_pos_eq //; nra.
  rewrite ulp_neq_0 /cexp /fexp; last first.
    interval.
  have -> : (mag beta (33 ^ 2 * Rpower 2 (-26)) = (-15) :> Z)%Z.
    apply: mag_unique_pos.
    by rewrite !pow_Rpower /=; split; interval.
  by rewrite pow_Rpower /emin /Z.max /=; lra.
have F5 : Rabs wh <= Rpower 2 (-15.91) + Rpower 2 (-68).
  apply: Rle_trans (_ : z ^ 2 + ulp (z ^2) <= _); last by lra.
  rewrite Rabs_pos_eq; last first.
    rewrite -(round_0 beta fexp).
    by apply: round_le; nra.
  suff : Rabs (RN (z ^ 2) - z ^ 2) <= ulp(z ^ 2).
    by rewrite /wh -pow2_mult; split_Rabs; lra.
  by apply: error_le_ulp.
rewrite Rabs_pos_eq in F5; last by lra.
have F6 : Rabs wl <= Rpower 2 (-68).
  apply: Rle_trans F4.
  have -> : wl = - (wh - z ^ 2) by lra.
  rewrite Rabs_Ropp.
  rewrite /wh -pow2_mult.
  by apply: error_le_ulp.
have F7 : is_imul wh (pow (- 122)).
  apply: is_imul_pow_round.
  have -> : pow (-122) = pow (-61) * pow (-61) by rewrite -bpow_plus.
  by apply: is_imul_mul.
have F8 : is_imul wl (pow (- 122)).
  have -> : wl = z * z - wh by lra.
  apply: is_imul_minus => //.
  have -> : pow (-122) = pow (-61) * pow (-61) by rewrite -bpow_plus.
  by apply: is_imul_mul.
have F9 : ph = -0.5 * wh.
  rewrite /ph round_generic //.
  have-> : -0.5 = -(0.5) by lra.
  rewrite -!Ropp_mult_distr_l.
  apply: generic_format_opp.
  by apply: is_imul_format_half Fwh F7 _; lia.
have F10 : is_imul (z ^ 2) (pow (-122)).
  have -> : pow (-122) = pow (-61) * pow (-61) by rewrite -bpow_plus.
  by rewrite pow2_mult; apply: is_imul_mul.
have F11 : is_imul (z ^ 2) (pow (-123)).
  by apply: is_imul_pow_le F10 _; lia.
have F12 : is_imul (z ^ 2 - wh) (pow (-123)).
  by apply: is_imul_pow_le (is_imul_minus F10 F7) _; lia.
have F13 : is_imul (0.5 * wh) (pow (-123)).
  have-> : pow (-123) = pow (-1) * pow (-122) by rewrite -bpow_plus.
  by rewrite powN1; apply: is_imul_mul => //; exists 1%Z; lra.
have F14 : is_imul (0.5 * wl) (pow (-123)).
  have-> : pow (-123) = pow (-1) * pow (-122) by rewrite -bpow_plus.
  by rewrite powN1; apply: is_imul_mul => //; exists 1%Z; lra.
pose e1 := t - (P8 * z + P7).
have e1E : t = P8 * z + P7 + e1 by rewrite /e1;lra.
have [F15_1 F15_2 F15_3 F15_4] : 
  [/\ 
    Rabs e1 <= pow (- 55),
    t <= Rpower 2 (- 2.8022) + Rpower 2 (-55),
    0 < t < Rpower 2 (- 2.802) & 
    is_imul t (pow (-116))].
  have G1 : 0 < P8 * z + P7 < Rpower 2 (- 2.8022).
    by split; rewrite /P8 /P7; interval.
  have G2 : ulp (Rpower 2 (- 2.8022)) = pow (-55).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (-55 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have G3 : Rabs e1 <= pow (- 55).
    rewrite -G2 /e1.
    apply: Rle_trans (_ : ulp (P8 * z + P7) <= _); last first.
      by apply: ulp_le; rewrite {zB F6}//; split_Rabs; lra.
    rewrite /t Pf8E Pf7E.
    by apply: error_le_ulp.
  have G4 : t <= Rpower 2 (- 2.8022) + Rpower 2 (-55).
    apply: Rle_trans (_ : Rabs e1 + P8 * z + P7 <= _).
      by rewrite {zB F6}// /e1; split_Rabs; lra.
    by rewrite pow_Rpower in G3; lra.
  have G5 : t < Rpower 2 (- 2.802).
    apply: Rle_lt_trans G4 _.
    by interval. 
  have G6 : is_imul (P8 * z + P7) (pow (-116)).
    apply: is_imul_add.
      have -> : pow (-116) = pow (-55) * pow (-61).
        by rewrite -bpow_plus; congr (pow _); lia.
      apply: is_imul_mul => //.
      exists (-4503732981131470)%Z.
      by rewrite /P8 /= /Z.pow_pos /=; lra.
    exists (11868429770568140608450203318484992)%Z.
    by rewrite /P7 /= /Z.pow_pos /=; lra.
  have G7 : is_imul t (pow (-116)).
    by apply: is_imul_pow_round; rewrite Pf8E Pf7E.
  suff G8 : 0 < t by [].
  rewrite /t Pf8E Pf7E.
  by apply: is_imul_format_round_gt_0 _ G6 _ => //=; nra.
pose e2 := u - (P6 * z + P5).
have e2E : u = P6 * z + P5 + e2 by rewrite /e2;lra.
have [F16_1 F16_2 F16_3 F16_4] : 
  [/\ 
    Rabs e2 <= pow (- 55),
    0 < u < Rpower 2 (- 2.317),
    u <= Rpower 2 (-2.31709) + Rpower 2 (-55) & 
    is_imul u (pow (-116))].
  have G1 : 0 < P6 * z + P5 < Rpower 2 (- 2.31709).
    by split; rewrite /P6 /P5; interval.
  have G2 : ulp (Rpower 2 (- 2.31709)) = pow (-55).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (-55 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have G3 : Rabs e2 <= pow (- 55).
    rewrite -G2 /e2.
    apply: Rle_trans (_ : ulp (P6 * z + P5) <= _); last first.
      by apply: ulp_le; rewrite {zB F6 F15_1}//; split_Rabs; lra.
    rewrite /u Pf6E Pf5E.
    by apply: error_le_ulp.
  have G4 : u <= Rpower 2 (-2.31709) + Rpower 2 (-55).
    apply: Rle_trans (_ : Rabs e2 + P6 * z + P5 <= _).
      by rewrite {zB F6 F15_1 G3}// /e2; split_Rabs; lra.
    by rewrite pow_Rpower in G3; lra.
  have G5 : u < Rpower 2 (- 2.317).
    apply: Rle_lt_trans G4 _.
    by interval. 
  have G6 : is_imul (P6 * z + P5) (pow (-116)).
    apply: is_imul_add.
      have -> : pow (-116) = pow (-55) * pow (-61).
        by rewrite -bpow_plus; congr (pow _); lia.
      apply: is_imul_mul => //.
      exists (-6004799501573812)%Z.
      by rewrite /P6 /= /Z.pow_pos /=; lra.
    exists (16615349943738746199199974751731712)%Z.
    by rewrite /P5 /= /Z.pow_pos /=; lra.
  have G7 : is_imul u (pow (-116)).
    by apply: is_imul_pow_round; rewrite Pf6E Pf5E.
  suff G8 : 0 < u by [].
  rewrite /u Pf6E Pf5E.
  by apply: is_imul_format_round_gt_0 _ G6 _ => //=; nra.
pose e3 := v - (P4 * z + P3).
have e3E : v = P4 * z + P3 + e3 by rewrite /e3;lra.
have [F17_1 F17_2 F17_3 F17_4] : 
  [/\ 
    Rabs e3 <= pow (- 54),
    v <= Rpower 2 (- 1.5806) + Rpower 2 (-54),
    0 < v < Rpower 2 (- 1.580) & 
    is_imul v (pow (-115))].
  have G1 : 0 < P4 * z + P3 < Rpower 2 (- 1.5806).
    by split; rewrite /P4 /P3; interval.
  have G2 : ulp (Rpower 2 (- 1.5806)) = pow (-54).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (-54 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have G3 : Rabs e3 <= pow (- 54).
    rewrite -G2 /e3.
    apply: Rle_trans (_ : ulp (P4 * z + P3) <= _); last first.
      by apply: ulp_le; rewrite {zB F6 F15_1 F16_1}//; split_Rabs; lra.
    rewrite /v Pf4E Pf3E.
    by apply: error_le_ulp.
  have G4 : v <= Rpower 2 (- 1.5806) + Rpower 2 (-54).
    apply: Rle_trans (_ : Rabs e3 + P4 * z + P3 <= _).
      by rewrite /e3; rewrite {zB F6 F15_1 F16_1 G3}//; split_Rabs; lra.
    by rewrite pow_Rpower in G3; lra.
  have G5 : v < Rpower 2 (- 1.580).
    apply: Rle_lt_trans G4 _.
    by interval. 
  have G6 : is_imul (P4 * z + P3) (pow (-115)).
    apply: is_imul_add.
      have -> : pow (-115) = pow (-54) * pow (-61).
        by rewrite -bpow_plus; congr (pow _); lia.
      apply: is_imul_mul => //.
      exists (-4503599627370499)%Z.
      by rewrite /P4 /= /Z.pow_pos /=; lra.
    exists (13846124956092879824996014781104128)%Z.
    by rewrite /P3 /= /Z.pow_pos /=; lra.
  have G7 : is_imul v (pow (-115)).
    by apply: is_imul_pow_round; rewrite Pf4E Pf3E.
  suff G8 : 0 < v by [].
  rewrite /v Pf4E Pf3E.
  by apply: is_imul_format_round_gt_0 _ G6 _ => //=; nra.
pose e4 := u' - (t * wh + u).
have e4E : u' = t * wh + u + e4 by rewrite /e4; lra.
have [F18_1 F18_2 F18_3 F18_4] : 
  [/\ 
    Rabs e4 <= pow (- 55),
    u' <= Rpower 2 (-2.31707) + Rpower 2 (-55), 
    0 < u' < Rpower 2 (- 2.31706) & 
    is_imul u' (pow (-238))].
  have G1 : 0 < t * wh + u < Rpower 2 (- 2.31707).
    split; first by nra.
    apply: Rle_lt_trans
      (_ :  Rpower 2 (-2.802) * (Rpower 2 (-15.91) + Rpower 2 (-68)) + 
            (Rpower 2 (- 2.31709) + Rpower 2 (- 55)) < _); last by interval.
    by nra.
  have G2 : ulp (Rpower 2 (-2.31707)) = pow (-55).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (-55 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have G3 : Rabs e4 <= pow (- 55).
    rewrite -G2 /e4.
    apply: Rle_trans (_ : ulp (t * wh + u) <= _); last first.
      by apply: ulp_le; rewrite {zB F6 F15_1 F16_1 F17_1}//; split_Rabs; lra.
    by apply: error_le_ulp.    
  have G4 : u' <= Rpower 2 (-2.31707) + Rpower 2 (-55).
    apply: Rle_trans (_ : Rabs e4 + t * wh + u <= _).
      by rewrite /e4; rewrite {zB F6 F15_1 F16_1 F17_1 G3}//;
         split_Rabs; lra.
    by rewrite pow_Rpower in G3; lra.
  have G5 : u' < Rpower 2 (-2.31706).
    apply: Rle_lt_trans G4 _.
    by interval. 
  have G6 : is_imul (t * wh + u) (pow (-238)).
    apply: is_imul_add; last first.
      by apply: is_imul_pow_le F16_4 _; lia.
    have -> : pow (-238) = pow (-116) * pow (-122).
      by rewrite -bpow_plus; congr (pow _); lia.
    by apply: is_imul_mul.
  have G7 : is_imul u'  (pow (-238)).
    by apply: is_imul_pow_round.
  suff G8 : 0 < u' by [].
  by apply: is_imul_format_round_gt_0 _ G6 _ => //=; nra.
pose e5 := v' - (u' * wh + v).
have e5E : v' = u' * wh + v + e5 by rewrite /e5; lra.
have [F19_1 F19_2 F19_3 F19_4] : 
  [/\ 
    Rabs e5 <= pow (- 54),
    v' <= Rpower 2 (- 1.58058) + Rpower 2 (-54), 
    0 < v' < Rpower 2 (- 1.5805) & 
    is_imul v' (pow (- 360))].
  have G1 : 0 < u' * wh + v < Rpower 2 (- 1.58058).
    split; first by nra.
    apply: Rle_lt_trans
      (_ :  Rpower 2 (- 2.31706) * (Rpower 2 (-15.91) + Rpower 2 (-68)) + 
            (Rpower 2 (- 1.5806) + Rpower 2 (- 54)) < _); last by interval.
    by nra.
  have G2 : ulp (Rpower 2 (- 1.58058)) = pow (-54).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (- 54 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have G3 : Rabs e5 <= pow (- 54).
    rewrite -G2 /e5.
    apply: Rle_trans (_ : ulp (u' * wh + v) <= _); last first.
      by apply: ulp_le; rewrite {zB F6 F15_1 F16_1 F17_1 F18_1}//;
         split_Rabs; lra.
    by apply: error_le_ulp.
  have G4 : v' <= Rpower 2 (- 1.58058) + Rpower 2 (-54).
    apply: Rle_trans (_ : Rabs e5 + u' * wh + v <= _).
      by rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 G3}// /e5; split_Rabs; lra.
    by rewrite pow_Rpower in G3; lra.
  have G5 : v' < Rpower 2 (-1.5805).
    apply: Rle_lt_trans G4 _.
    by interval. 
  have G6 : is_imul (u' * wh + v) (pow (- 360)).
    apply: is_imul_add; last first.
      by apply: is_imul_pow_le F17_4 _; lia.
    have -> : pow (- 360) = pow (- 238) * pow (-122).
      by rewrite -bpow_plus; congr (pow _); lia.
    by apply: is_imul_mul.
  have G7 : is_imul v'  (pow (- 360)).
    by apply: is_imul_pow_round.
  suff G8 : 0 < v' by [].
  by apply: is_imul_format_round_gt_0 _ G6 _ => //=; nra.
pose e6 := u'' - (v' * wh).
have e6E : u'' = v' * wh + e6 by rewrite /e6; lra.
have [F20_1 F20_2 F20_3 F20_4] : 
  [/\ 
    Rabs e6 <= pow (- 70),
    u'' <= Rpower 2 (- 17.49057) + Rpower 2 (- 70),
    0 < u'' < Rpower 2 (- 17.4905) & 
    is_imul u'' (pow (- 482))].
  have G1 : 0 < v' * wh < Rpower 2 (- 17.49057).
    split; first by nra.
    apply: Rle_lt_trans
      (_ :  (Rpower 2 (- 1.58058) + Rpower 2 (- 54)) *
            (Rpower 2 (- 15.91) + Rpower 2 (- 68)) < _); last by interval.
    by apply: Rmult_le_compat; lra.
  have G2 : ulp (Rpower 2 (- 17.49057)) = pow (- 70).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (- 70 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have G3 : Rabs e6 <= pow (- 70).
    rewrite -G2 /e6.
    apply: Rle_trans (_ : ulp (v' * wh) <= _); last first.
      by apply: ulp_le; rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1}//;
         split_Rabs; lra.
    by apply: error_le_ulp.
  have G4 : u'' <= Rpower 2 (- 17.49057) + Rpower 2 (- 70).
    apply: Rle_trans (_ : Rabs e6 + v' * wh <= _).
      by rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1 G3}// /e6; 
         split_Rabs; lra.
    by rewrite pow_Rpower in G3; lra.
  have G5 : u'' < Rpower 2 (- 17.4905).
    apply: Rle_lt_trans G4 _.
    by interval. 
  have G6 : is_imul (v' * wh) (pow (- 482)).
    have -> : pow (- 482) = pow (- 360) * pow (-122).
      by rewrite -bpow_plus; congr (pow _); lia.
    by apply: is_imul_mul.
  have G7 : is_imul u'' (pow (- 482)).
    by apply: is_imul_pow_round.
  suff G8 : 0 < u'' by [].
  by apply: is_imul_format_round_gt_0 _ G6 _ => //=; nra.
pose e7 := pl - (u'' * z - 0.5 * wl).
have e7E : pl = u'' * z - 0.5 * wl + e7 by rewrite /e7; lra.
have [F21_1 F21_2 F21_3] : 
  [/\ 
    Rabs e7 <= pow (- 78),
    Rabs pl < Rpower 2 (- 25.446) & 
    is_imul pl (pow (- 543))].
  have G1 : Rabs (u'' * z - 0.5 * wl) < Rpower 2 (- 25.4461).
    apply: Rle_lt_trans
      (_ :  (Rpower 2 (- 17.49057) + Rpower 2 (- 70)) *
            (33  * Rpower 2 (- 13)) + Rpower 2 (- 69) < _); last by interval.
    apply: Rle_trans
      (_ :  (u'' * Rabs z + 0.5 * Rabs wl <= _)).
      by rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1}//; split_Rabs; nra.
    apply: Rplus_le_compat; last first.
      suff -> : Rpower 2 (-69) = 0.5 * Rpower 2 (- 68) by lra.
      have -> : 0.5 = Rpower 2 (-1).
        by rewrite -pow_Rpower /= /Z.pow_pos /=; lra.
      by rewrite -Rpower_plus; congr (Rpower _ _); lra.
    apply: Rmult_le_compat; try lra.
    rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1}//; split_Rabs; lra.
  have G2 : ulp (Rpower 2 (- 25.4461)) = pow (- 78).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (- 78 + p)%Z); try lra.
    - rewrite Z.max_l; last by lia.
      congr bpow; lia.
    - by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
    by interval.
  have G3 : Rabs e7 <= pow (- 78).
    rewrite -G2 /e7.
    apply: Rle_trans (_ : ulp (u'' * z - 0.5 * wl) <= _); last first.
      by apply: ulp_le; 
         rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1 F20_1 G2}// /e6;
         split_Rabs; lra.
    by apply: error_le_ulp.
  have G4 : Rabs pl < Rpower 2 (- 25.446).
    apply: Rle_lt_trans (_ : Rpower 2 (- 25.4461) + Rpower 2 (- 78) < _).
      apply: Rle_trans (_ : Rabs e7 + Rabs (u'' * z - 0.5 * wl) <= _).
        by  rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1 F20_1 G2}// /e7;
            split_Rabs; lra.
      by rewrite pow_Rpower in G3; lra.
    by interval. 
  have G5 : is_imul (u'' * z - 0.5 * wl) (pow (- 543)).
    apply: is_imul_minus.
      have -> : pow (- 543) = pow (- 482) * pow (- 61).
        by rewrite -bpow_plus; congr (pow _); lia.
      by apply: is_imul_mul.
    have -> : pow (- 543) = pow (- 1) * pow (- 542).
      by rewrite -bpow_plus; congr (pow _); lia.
    apply: is_imul_mul.
      by exists 1%Z; rewrite /= /Z.pow_pos /=; lra.
    by apply: is_imul_pow_le F8 _; lia.
  have G6 : is_imul pl (pow (- 543)).
    by apply: is_imul_pow_round.
  by [].
set E := Rabs (ph + pl - (P z - z)).
pose Q := P3 + P4 * z + P5 * z ^ 2 + P6 * z ^ 3 +
         P7 * z ^ 4 + P8 * z ^ 5.
have PzE : P z - z = - 0.5 * z ^ 2 + z ^ 3 * Q by rewrite /P /Q; lra.
pose tR := P5 + P6 * z + P7 * z ^ 2 + P8 * z ^ 3.
have QE : Q = P3 + P4 * z + tR * z ^ 2 by rewrite /Q /tR; lra.
have F22 : E = Rabs (u'' * z + e7 - z ^ 3 * Q).
  congr (Rabs _); rewrite PzE.
  suff : ph + pl + 0.5 * z ^ 2 = u'' * z + e7 by lra.
  by rewrite pow2_mult -F1 e7E F9; lra.
pose E1 := Rabs (u'' - z ^ 2 * Q); pose tE0 := Rabs e7.
have F23 : E <= E1 * Rabs z + tE0.
  rewrite /tE0 /E1 F22.
  rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1 F20_1 F21_1 F21_2 }//.
  by split_Rabs; nra.
pose E3 := Rabs (v' - Q); pose tE1 := Rabs (- v' * wl + e6).
have F24 : E1 <= E3 * z ^ 2 + tE1.
  rewrite /tE1 /E1 /E3.
  have -> : u'' = v' * z ^ 2 - v' * wl + e6 by rewrite e6E pow2_mult -F1; lra.
  rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1 F20_1 F21_1 F21_2 F22 F23 }//.
  by split_Rabs; nra.
pose E5 := Rabs (u' - tR); pose tE3 := Rabs (- u' * wl + e3 + e5).
have F25 : E3 <= E5 * z ^ 2 + tE3.
  rewrite /E3 /E5 /tE3.
  have -> : v' - Q = (u' - tR) * z ^ 2  - u' * wl + e3 + e5.
    have -> : v' = u' * (z ^ 2 - wl) + (P4 * z + P3 + e3 ) + e5.
      by rewrite pow2_mult -F1; lra.
    by lra.
  rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1 F20_1 F21_1 F21_2 F22 F23 }//.
  by split_Rabs; nra.
pose tE7 := Rabs e1; pose tE5 := Rabs (- t * wl + e2 + e4).
have F26 : E5 <= tE7 * z ^2 + tE5.
  rewrite /E5 /tE7 /tE5.
  have-> : u' - tR = e1 * z ^ 2 - t * wl + e2 + e4 by rewrite /tR; nra.
  rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1 F20_1 F21_1 F21_2 F22 F23 }//.
  by split_Rabs; nra.
have F27 : E <= Rpower 2 (- 75.513).
  apply: Rle_trans 
      (_ : tE0 + tE1 * Rabs z + tE3 * Rabs z ^ 3 + 
                 tE5 * Rabs z ^ 5 + tE7 * Rabs z ^ 7 <= _).
    apply: Rle_trans F23 _.
    suff : E1 <= tE1 + tE3 * Rabs z ^ 2 + tE5 * Rabs z ^ 4 + tE7 * Rabs z ^ 6.
      have : 0 <= Rabs z by apply: Rabs_pos.
      by nra.
    rewrite pow2_abs.
    have -> : Rabs z ^ 4 = z ^ 4.
      have-> : (Rabs z) ^ 4 = (Rabs z ^ 2) ^ 2 by lra.
      rewrite pow2_abs; lra.
    have -> : Rabs z ^ 6 = z ^ 6.
      have-> : (Rabs z) ^ 6 = (Rabs z ^ 2) ^ 3 by lra.
      rewrite pow2_abs; lra.
    apply: Rle_trans F24 _.
    suff : E3 <= tE3 + tE5 * z ^ 2 + tE7 * z ^ 4.
      by nra.
    by nra.
  have G1 : tE0 <= pow (- 78) by rewrite /tE0; lra.
  have G2 : tE1 < Rpower 2 (- 68.775).
    apply: Rle_lt_trans 
      (_ : (Rpower 2 (- 1.58058) + pow (-54)) * pow (-68) + pow (-70) < _);
        last first.
      by rewrite !pow_Rpower; interval.
    apply: Rle_trans (_ : Rabs v' * Rabs wl + Rabs e6 <= _).
      rewrite /tE1.
      rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1 F20_1 F21_1 F21_2 F22 F23 }//.
      by split_Rabs; nra.
    have-> : Rabs v' = v' by rewrite Rabs_pos_eq; lra.
    apply: Rplus_le_compat => //.
    apply: Rmult_le_compat; first by lra.
    - by apply: Rabs_pos; lra.
    - by rewrite pow_Rpower.
    by rewrite pow_Rpower.
  have G3 : tE3 < Rpower 2 (- 52.999).
    apply: Rle_lt_trans 
      (_ : (Rpower 2 (- 2.31707) + pow (-55)) * pow (-68) + 
            pow (-54) + pow (-54) < _);
        last first.
      by rewrite !pow_Rpower; interval.
    apply: Rle_trans (_ : u' * Rabs wl + Rabs e3  + Rabs e5 <= _).
      rewrite /tE3.
      rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1 F20_1 F21_1 F21_2 F22 F23 }//.
      by split_Rabs; nra.
    apply: Rplus_le_compat => //.
    apply: Rplus_le_compat => //.
    apply: Rmult_le_compat => //; first by lra.
    - by apply: Rabs_pos; lra.
    - by rewrite pow_Rpower.
    by rewrite pow_Rpower.
  have G4 : tE5 < Rpower 2 (- 53.999).
    apply: Rle_lt_trans 
      (_ : (Rpower 2 (- 2.8022) + pow (-55)) * pow (-68) + 
            pow (-55) + pow (-55) < _);
        last first.
      by rewrite !pow_Rpower; interval.
    apply: Rle_trans (_ : t * Rabs wl + Rabs e2 + Rabs e4 <= _).
      rewrite /tE5.
      rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1 F20_1 F21_1 F21_2 F22 F23 }//.
      by split_Rabs; nra.
    apply: Rplus_le_compat => //.
    apply: Rplus_le_compat => //.
    apply: Rmult_le_compat => //; first by lra.
    - by apply: Rabs_pos; lra.
    - by rewrite pow_Rpower.
    by rewrite pow_Rpower.
  have G5 : tE7 <= Rpower 2 (- 55) by rewrite /tE7 -pow_Rpower.
  have G6 : (Rabs z) ^ 3 <= 33 ^ 3 * (Rpower 2 (-13)) ^ 3.
    rewrite -Rpow_mult_distr.
    apply: pow_incr; split; last by lra.
    by apply: Rabs_pos.
  have G7 : (Rabs z) ^ 5 <= 33 ^ 5 * (Rpower 2 (-13)) ^ 5.
    rewrite -Rpow_mult_distr.
    apply: pow_incr; split; last by lra.
    by apply: Rabs_pos.
  have G8 : (Rabs z) ^ 7 <= 33 ^ 7 * (Rpower 2 (-13)) ^ 7.
    rewrite -Rpow_mult_distr.
    apply: pow_incr; split; last by lra.
    by apply: Rabs_pos.
  apply: Rle_trans.
    apply: Rplus_le_compat; last first.
      apply: Rmult_le_compat G5 G8; first by apply: Rabs_pos.
      by apply/pow_le/Rabs_pos.
    apply: Rplus_le_compat; last first.
      apply: Rmult_le_compat (Rlt_le _ _ G4) G7; first by apply: Rabs_pos.
      by apply/pow_le/Rabs_pos.
    apply: Rplus_le_compat; last first.
      apply: Rmult_le_compat (Rlt_le _ _ G3) G6; first by apply: Rabs_pos.
      by apply/pow_le/Rabs_pos.
    apply: Rplus_le_compat; last first.
      apply: Rmult_le_compat (Rlt_le _ _ G2) zB; first by apply: Rabs_pos.
      by apply: Rabs_pos.
    by apply: G1.
  by interval.
repeat split => //.
- apply: Rle_lt_trans (_ : E + Rabs (ln (1 + z) - P z) < _).
    rewrite /E.
    rewrite {zB F6 F15_1 F16_1 F17_1 F18_1 F19_1 F20_1 F21_1 F21_2 F22 F23 }//.
    by split_Rabs; nra.
  apply: Rle_lt_trans (_ : Rpower 2 (- 75.513) + Rpower 2 (- 81.63) < _); 
       last by interval.
  apply: Rplus_le_compat => //. 
  by apply: P_abs_error.
- rewrite F9 Rabs_mult Rabs_left; try lra.
  apply: Rle_lt_trans (_ : 0.5 * (33 ^ 2 * pow (-13) ^ 2) < _); last by interval.
  pose f := Float beta (33 ^ 2) (- 26).
  have Ff : format (33 ^ 2 * (pow (-13)) ^ 2).
    apply: generic_format_FLT.
    apply: FLT_spec (_ : _ = F2R f) _ _; try by rewrite /=; lia.
    by rewrite /F2R /= /Z.pow_pos /=; lra.
  have : wh <= RN (33 ^ 2 * pow (-13) ^ 2).
    apply: round_le.
    rewrite -pow2_mult -Rpow_mult_distr.
    apply: pow_maj_Rabs.
    by rewrite pow_Rpower.
  rewrite round_generic // Rabs_pos_eq; last by lra.
  by lra.
move=> z_neq zB1.
pose u_ := Exp.u.
pose d0 := (wh - z ^ 2) / (z ^ 2).
have d0E : wh = z ^ 2 * (1 + d0) by rewrite /d0; field; lra.
have d0L2u : Rabs d0 < 2 * u_.
  apply: relative_error_is_min_eps_bound _ F11 _ _.
  - by rewrite /emin; lia.
  - by apply: pow_nonzero; lra.
  by rewrite [in LHS]pow2_mult.
have H1 : Rpower 2 (- 2.8125) < P8 * z + P7  < Rpower 2 (- 2.8022).
  rewrite /P8 /P7; split; interval.
pose d1 := e1 / (P8 * z + P7).
have d1E : t = (P8 * z + P7) * (1 + d1).
  rewrite /d1 /e1; field; interval.
have d1B : Rabs d1 < 1.76 * u_.
  rewrite /d1 [u_]uE pow_Rpower [IZR (- p)]/=.
  by interval.
have H2 : Rpower 2 (- 2.3268) < P6 * z + P5  < Rpower 2 (- 2.3170).
  rewrite /P6 /P5; split; interval.
pose d2 := e2 / (P6 * z + P5).
have d2E : u = (P6 * z + P5) * (1 + d2).
  rewrite /d2 /e2; field; interval.
have d2B : Rabs d2 < 1.255 * u_.
  rewrite /d2 [u_]uE pow_Rpower [IZR (- p)]/=.
  by interval.
pose d3 := e3 / (P4 * z + P3).
have d3E : v = (P4 * z + P3) * (1 + d3).
  rewrite /d3 /e3; field; interval.
have d3B : Rabs d3 < 1.505 * u_.
  rewrite /d3 [u_]uE pow_Rpower [IZR (- p)]/=.
  by interval.
have twhuB : 0 < t * wh + u < Rpower 2 (- 2.31707).
  split; first by nra.
  apply: Rle_lt_trans
      (_ :  Rpower 2 (-2.802) * (Rpower 2 (-15.91) + Rpower 2 (-68)) + 
            (Rpower 2 (- 2.31709) + Rpower 2 (- 55)) < _); last by interval.
  by nra.
pose d4 := e4 / (t * wh + u).
have d4E : u' = (t * wh + u) * (1 + d4).
  rewrite /d4 /e4; field; lra.
have d4B : Rabs d4 < 1.255 * u_.
  have G1 : u <= t * wh + u by clear -wh_gt_0 F15_3; nra.
  rewrite /d4 [u_]uE pow_Rpower [IZR (- p)]/=.
  rewrite Rabs_mult Rabs_inv [X in _ * / X]Rabs_pos_eq; last by lra.
  apply/Rlt_div_l; first by lra.
  suff X1 : Rpower 2 (- 2.3269) < t * wh + u.
    set vv := t * wh + u in X1 *.
    apply: Rle_lt_trans F18_1 _.
    interval.
  apply: Rlt_le_trans (_ : u <= _); last by lra.
  rewrite /e2 in F16_1.
  clear -H2 F16_1.
  apply: Rle_lt_trans (_ : Rpower 2 (-2.3268) - pow (-55) < _).
    by interval.
  by split_Rabs; lra.
(* 
Similarly,
we know that u′ wh + v < 2−1.58058 ; since u′ > 0
and wh ≥ 0, we have also u′ wh + v ≥ v =
◦(P4 z + P3 ) > 2−1.5894 − 2−54 > 2−1.5895 , which
gives λ5 < 2 · 2−2 /2−1.5895 < 1.505.
*)
have H3 : Rpower 2 (- 1.5894) < P4 * z + P3 < Rpower 2 (- 1.5806).
  by rewrite /P4 /P3; split; interval.
pose d5 := e5 / (u' * wh + v).
have d5E : v' = (u' * wh + v) * (1 + d5).
  rewrite /d5 /e5; field.
  clear - F17_3 F18_3 wh_gt_0.
  by nra.
have d5B : Rabs d5 < 1.505 * u_.
  have G1 : v <= u' * wh + v by clear -wh_gt_0 F17_3 F18_3; nra.
  rewrite /d5 [u_]uE pow_Rpower [IZR (- p)]/=.
  rewrite Rabs_mult Rabs_inv [X in _ * / X]Rabs_pos_eq; last by lra.
  apply/Rlt_div_l; first by lra.
  suff X1 : Rpower 2 (- 1.5895) < u' * wh + v.
    set vv := u' * wh + v in X1 *.
    apply: Rle_lt_trans F19_1 _.
    interval.
  apply: Rlt_le_trans (_ : v <= _); last by lra.
  rewrite /e3 in F17_1.
  clear -H3 F17_1.
  apply: Rle_lt_trans (_ : Rpower 2 (-1.5894) - pow (-54) < _).
    by interval.
  by split_Rabs; lra.
pose A := P8 * z + P7. 
pose B := P6 * z + P5.
pose C := P4 * z + P3.
have tE : t = A * (1 + d1) by rewrite /A; lra.
have uE : u = B * (1 + d2) by rewrite /B; lra.
have vE : v = C * (1 + d3) by rewrite /C; lra.
have u'E : u' = A * z ^ 2 * (1 + d0 ) * (1 + d1 ) * (1 + d4 ) + 
                B * (1 + d2) * (1 + d4).
    rewrite /A / B; clear -d0E d1E d2E d4E.
    by nra.
have v'E : v' =  A * z ^ 4 * (1 + d0) ^ 2 * (1 + d1) * (1 + d4) * (1 + d5) +
                 B * z ^ 2 * (1 + d0) * (1 + d2) * (1 + d4) * (1 + d5) +
                 C * (1 + d3) * (1 + d5).
    rewrite /A /B /C; clear -d0E d1E d2E d3E d4E d5E u'E.
    ring[d0E d1E d2E d3E d4E d5E].
pose d6 := e6 / (v' * wh).
have d6E : u'' = (v' * wh) * (1 + d6).
  rewrite /d6 /e6; field.
  clear -F19_3 wh_gt_0.
  by nra.
have d6B : Rabs d6 < 2 * u_.
  have G6 : is_imul (v' * wh) (pow (- 482)).
    have -> : pow (- 482) = pow (- 360) * pow (-122).
      by rewrite -bpow_plus; congr (pow _); lia.
    by apply: is_imul_mul.
  apply: relative_error_is_min_eps_bound G6 _ d6E; first by rewrite /emin /=.
  by clear - F19_3 wh_gt_0; nra.
pose t7 := (1 + d0) ^ 3 * (1 + d1) * (1 + d4) * (1 + d5) * (1 + d6) - 1.
pose t6 := (1 + d0) ^ 2 * (1 + d2) * (1 + d4) * (1 + d5) * (1 + d6) - 1.
pose t4 := (1 + d0) * (1 + d3) * (1 + d5) * (1 + d6) - 1.
have u''E : u'' = A * z ^ 6 * (1 + t7) + 
                  B * z ^ 4 * (1 + t6) +
                  C * z ^ 2 * (1 + t4).
    rewrite /A /B /C /t7 /t6 /t4.
    clear -d0E d1E d2E d3E d4E d5E d6E.
    ring[d0E d1E d2E d3E d4E d5E d6E].
pose d7 := e7 / (u'' * z - 0.5 * wl).
have d7E : pl = (u'' * z - 0.5 * wl) * (1 + d7).
  have [uzwl_eq0 | uzwl_neq0] := Req_dec (u'' * z - 0.5 * wl) 0.
    by rewrite /pl uzwl_eq0 round_0; lra.
  by rewrite /d7 /e7; field.
have d7B : Rabs d7 < 2 * u_.
  have [uzwl_eq0 | uzwl_neq0] := Req_dec (u'' * z - 0.5 * wl) 0.
    rewrite /d7 /e7 /pl uzwl_eq0 round_0 !Rsimp01.
    suff : 0 < u_ by lra.
    by apply: u_gt_0.
  have G5 : is_imul (u'' * z - 0.5 * wl) (pow (- 543)).
    apply: is_imul_minus.
      have -> : pow (- 543) = pow (- 482) * pow (- 61).
        by rewrite -bpow_plus; congr (pow _); lia.
      by apply: is_imul_mul.
      have -> : pow (- 543) = pow (- 1) * pow (- 542).
      by rewrite -bpow_plus; congr (pow _); lia.
    apply: is_imul_mul.
      by exists 1%Z; rewrite /= /Z.pow_pos /=; lra.
    by apply: is_imul_pow_le F8 _; lia.
  by apply: relative_error_is_min_eps_bound G5 _ d7E.
have phplE : 
     ph + pl = - 0.5 * z ^ 2 + 0.5 * d0 * d7 * z ^ 2 + u'' * z * (1 + d7).
  have whE : wh = z ^ 2 - wl by lra.
  have wlE : wl = - z ^ 2 * d0 by lra.
  by rewrite d7E F9 whE wlE; lra.
pose t8 := (1 + t7) * (1 + d7) - 1.
pose t7' := (1 + t6) * (1 + d7) - 1.
pose t5 := (1 + t4) * (1 + d7) -1.
have u''zd7E  : u'' * z * (1 + d7) = z ^ 3 * Q + t8 * A * z ^ 7 + 
                                     t7' * B * z ^ 5 + t5 * C * z ^ 3.
  rewrite /Q u''E /t8 /t7 /t7' /t6 /t5 /t4 /A /B /C.
  by lra.
have phplE' : ph + pl = P z - z + 0.5 * d0 * d7 * z ^ 2 + t5 * C * z ^ 3 +
                        t7' * B * z ^ 5 + t8 * A * z ^ 7.
  rewrite phplE /P u''E /t8 /t7 /t7' /t6 /t5 /t4 /A /B /C.
  by lra.
have Q_pos : 0 < 1 - 0.5 * z + z ^ 2 * Q.
  by rewrite /Q /P3 /P4 /P5 /P6 /P7 /P8; interval.
pose nphi := 0.5 * d0 * d7 * z + t5 * C * z ^ 2 + t7' * B * z ^ 4 + 
                  t8 * A * z ^ 6.
pose dphi := 1 - 0.5 * z + z ^ 2 * Q.
pose phi := Rabs nphi / dphi.
have Herr : phi = Rabs (z + ph + pl - P z) / Rabs (P z).
  have -> : z + ph + pl - P z = z * nphi.
    by rewrite /nphi Rplus_assoc phplE'; lra.
  have -> : P z = z * dphi by rewrite /dphi /P /Q; lra.
  rewrite ![Rabs (z * _)]Rabs_mult [Rabs dphi]Rabs_pos_eq; last first.
    by rewrite /dphi /Q /P3 /P4 /P5 /P6 /P7 /P8; interval.
  rewrite /phi; field; split.
    by rewrite /dphi /Q /P3 /P4 /P5 /P6 /P7 /P8; interval.
  by apply: Rabs_no_R0; lra.
have d0d7B : Rabs (0.5 * d0 * d7) < pow (- 105).
  rewrite pow_Rpower 2!Rabs_mult.
  have -> : Rpower 2 (-105) = 0.5 * (2 * u_) * (2 * u_).
    have <- : pow (- 1) = 0.5 by rewrite (bpow_opp _ 1) bpow_1 /=; lra.
    rewrite pow_Rpower.
    have -> : 2 * u_ = Rpower 2 (- 52).
      have {1}-> : 2 = Rpower 2 1 by rewrite Rpower_1; lra.
      rewrite [u_]/(Fmore.u _ _).
      have -> : / 2 = Rpower 2 (- 1) by rewrite Rpower_Ropp Rpower_1; lra.
      by rewrite pow_Rpower -!Rpower_plus /=; congr (Rpower _ _); lra.
    by rewrite -!Rpower_plus; congr (Rpower _ _); lra.
  rewrite Rabs_pos_eq; last by lra.
  rewrite [X in X < _]Rmult_assoc [X in _ < X]Rmult_assoc.
   apply: Rmult_lt_compat_l; first by lra.
  by apply: Rmult_lt_compat => //; apply: Rabs_pos.
pose B1 := pow (- 105).
pose B2 := Rpower 2 (- 51.413).
pose B3 := Rpower 2 (- 51.828).
pose B4 := Rpower 2 (- 51.735).
pose B5 := Rpower 2 (- 51.998).
pose B6 := Rpower 2 (- 51.947).
pose B7 := Rpower 2 (- 52.139).
pose Bz z := B1 * Rabs z +       B2 * (Rabs z) ^ 2 + B3 * (Rabs z) ^ 3 + 
           B4 * (Rabs z) ^ 4 + B5 * (Rabs z) ^ 5 + B6 * (Rabs z) ^ 6 + 
           B7 * (Rabs z) ^ 7.
have u_E : u_ = pow (- 53).
  by rewrite [u_]/(Fmore.u _ _) /= /Z.pow_pos /=; lra.
have V1 : 1 - 2 * pow (- 53) < 1 + d0 < 1 + 2 * pow (- 53).
  by clear -d0L2u u_E; split_Rabs; lra.
have V2 : 1 - 1.255 * pow (- 53) < 1 + d2 < 1 + 1.255 * pow (- 53).
  by clear -d2B u_E; split_Rabs; lra.
have V3 : 1 - 1.505 * pow (- 53) < 1 + d3 < 1 + 1.505 * pow (- 53).
  by clear -d3B u_E; split_Rabs; lra.
have V4 : 1 - 1.255 * pow (- 53) < 1 + d4 < 1 + 1.255 * pow (- 53).
  by clear -d4B u_E; split_Rabs; lra.
have V5 : 1 - 1.505 * pow (- 53) < 1 + d5 < 1 + 1.505 * pow (- 53).
  by clear -d5B u_E; split_Rabs; lra.
have V6 : 1 - 2 * pow (- 53) < 1 + d6 < 1 + 2 * pow (- 53).
  by clear -d6B u_E; split_Rabs; lra.
have V7 : 1 - 2 * pow (- 53) < 1 + d7 < 1 + 2 * pow (- 53).
  by clear -d7B u_E; split_Rabs; lra.
have K1 : Rabs (0.5 * d0 * d7) < B1.
  by apply: d0d7B.
have K2 : Rabs (t5 * P3) <= B2.
  rewrite /B2 /P3 /t5 /t4.
  interval with (i_prec 65).
have K3 : Rabs (t5 * P4) <= B3.
  rewrite /B3 /P4 /t5 /t4.
  interval with (i_prec 65).
have K4 : Rabs (t7' * P5) <= B4.
  rewrite /t7' /t6 /P5 /B4.
  interval with (i_prec 100).
have K5 : Rabs (t7' * P6) <= B5.
  rewrite /t7' /t6 /P6 /B5.
  interval with (i_prec 100).
have K6 : Rabs (t8 * P7) <= B6.
  rewrite /t8 /t7 /P7 /B6.
  interval with (i_prec 100).
have K7 : Rabs (t8 * P8) <= B7.
  rewrite /t8 /t7 /P8 /B7.
  interval with (i_prec 100).
have K8 : Rabs nphi <= Bz z.
  rewrite /nphi /Bz /A /B /C.
  clear - K1 K2 K3 K4 K5 K6 K7.
  rewrite [in X in _ <= X]Rplus_assoc.
  apply: Rle_trans (Rabs_triang _ _) _.
    apply: Rplus_le_compat; last first.
    rewrite Rplus_comm Rmult_plus_distr_l Rmult_plus_distr_r.
    apply: Rle_trans (Rabs_triang _ _) _.
      apply: Rplus_le_compat.
      rewrite Rabs_mult RPow_abs.
      by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
    rewrite 2!Rmult_assoc -[in X in Rabs (_ * (_ * (X * _)))  <= _](pow_1 z).
    rewrite -pow_add -Rmult_assoc.
    rewrite Rabs_mult RPow_abs.
    by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
  rewrite [in X in _ <= X]Rplus_assoc.
  apply: Rle_trans (Rabs_triang _ _) _.
    apply: Rplus_le_compat; last first.
    rewrite Rplus_comm Rmult_plus_distr_l Rmult_plus_distr_r.
    apply: Rle_trans (Rabs_triang _ _) _.
      apply: Rplus_le_compat.
      rewrite Rabs_mult RPow_abs.
      by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
    rewrite 2!Rmult_assoc -[in X in Rabs (_ * (_ * (X * _)))  <= _](pow_1 z).
    rewrite -pow_add -Rmult_assoc.
    rewrite Rabs_mult RPow_abs.
    by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
  rewrite [in X in _ <= X]Rplus_assoc.
  apply: Rle_trans (Rabs_triang _ _) _.
    apply: Rplus_le_compat; last first.
    rewrite Rplus_comm Rmult_plus_distr_l Rmult_plus_distr_r.
    apply: Rle_trans (Rabs_triang _ _) _.
      apply: Rplus_le_compat.
      rewrite Rabs_mult RPow_abs.
      by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
    rewrite 2!Rmult_assoc -[in X in Rabs (_ * (_ * (X * _)))  <= _](pow_1 z).
    rewrite -pow_add -Rmult_assoc.
    rewrite Rabs_mult RPow_abs.
    by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
  rewrite Rabs_mult.
  apply: Rmult_le_compat_r => //; first by apply: Rabs_pos.
  by lra.
pose Cz z := 1 - 0.5 * Rabs z + Rabs z ^ 2 *
          (P3 + P4 * Rabs z + P5 * Rabs z ^ 2 + P6 * 
          Rabs z ^ 3 + P7 * Rabs z ^ 4 + P8 * Rabs z ^ 5).
have CzLdphi : Cz z <= dphi.
  rewrite /Cz /dphi.
  apply: Rplus_le_compat.
    by clear - K8; split_Rabs;lra.
  rewrite {1}RPow_abs Rabs_pos_eq; last by clear - K8; nra.
  apply: Rmult_le_compat_l; first by clear - K8; nra.
  rewrite /Q.
  do !apply: Rplus_le_compat; try lra.
  - by rewrite /P4; clear; split_Rabs; lra.
  - by clear; rewrite RPow_abs Rabs_pos_eq; nra.
  -  by rewrite /P6; clear; split_Rabs; nra.
  - by clear; rewrite RPow_abs Rabs_pos_eq; nra.
  rewrite /P8; clear; split_Rabs; last by nra.
  suff : z ^ 5 <= 0 by nra.
  suff : z ^ 3 <= 0 by nra.
  by nra.
have phiB : phi < Rpower 2 (- 67.31693).
  apply: Rle_lt_trans 
     (_ :  Bz (33 * pow (-13)) / Cz (33 * pow (-13)) < _); last first.
    rewrite /Bz /Cz /B1 /B2 /B3 /B4 /B5 /B6 /B7 /P3 /P4 /P5 /P6 /P7 /P8.
    by interval.
  rewrite /phi.
  have CzB : 0 < Cz (33 * pow (-13)) <= Cz z.
    rewrite /Bz /Cz /B1 /B2 /B3 /B4 /B5 /B6 /B7 /P3 /P4 /P5 /P6 /P7 /P8.
    split; interval.
  apply: Rle_trans (_ : Bz z / Cz z <= _).
    apply: Rmult_le_compat; first apply: Rabs_pos.
    - by apply: Rinv_0_le_compat; lra.
    - by lra.
    by apply: Rinv_le_contravar; lra.
  apply: Rmult_le_compat.
    rewrite /Bz /B1 /B2 /B3 /B4 /B5 /B6 /B7.
    by interval with (i_prec 100).
  - by apply: Rinv_0_le_compat; lra.
  - rewrite /Bz /Cz /B1 /B2 /B3 /B4 /B5 /B6 /B7 /P3 /P4 /P5 /P6 /P7 /P8.
    interval.
  by apply: Rinv_le_contravar; lra.
rewrite Herr in phiB.
have ln1zB : Rabs ((ln (1 + z) - P z) / ln (1 + z)) < Rpower 2 (-72.423).
  apply: P_rel_error; lra.
have HB1 : Rabs ((z + ph + pl) / ln (1 + z) -1) <= Rpower 2 (67.2756).
  apply: Rle_trans (_ : (1 + Rpower 2 (- 67.31693 )) * (1 + Rpower 2 (- 72.423)) 
                        - 1 <= _); last by interval.
  pose P1 z := 
       1 - z / 2 + P3 * z ^ 2 + P4 * z ^ 3 + P5 * z ^ 4 + 
       P6 * z ^ 5 + P7 * z ^ 6 + P8 * z ^ 7.
  have P1E : P z = z * P1 z by rewrite /P /P1; lra.
  have P1_gt_0 : 0 < P1 z.
    by rewrite /P1 /P3 /P4 /P5 /P6 /P7 /P8; interval.
  have Pz_neq_0 : P z <> 0.
    by rewrite P1E; clear -P1_gt_0 z_neq0; nra.
  have -> :  (z + ph + pl) / ln (1 + z) = 
               ((z + ph + pl) / P z) *  (P z / ln (1 + z)).
    field; split => //.
    apply: ln_neq_0; first by lra.
    by interval.
  have HB : Rabs ((z + ph + pl) / P z - 1) <= (Rpower 2 (-67.31693)) /\ 
         Rabs (P z / ln (1 + z) - 1) <= (Rpower 2 (-72.423)).
    split.
      rewrite /Rdiv -Rabs_inv -Rabs_mult in phiB.
      have <- : (z + ph + pl - P z) * / P z = (z + ph + pl) / P z  - 1.
        by field.
      by lra.
      have <- : - ((ln (1 + z) - P z) / ln (1 + z)) = P z / ln (1 + z) - 1.
        field.
        apply: ln_neq_0; first by lra.
        by interval.
      by rewrite Rabs_Ropp; lra.
  clear -HB.
  by split_Rabs; nra.
suff d0d6B : Rabs d0 + Rabs d6 <= 3.505 * u_.
  pose B2' := Rpower 2 (- 51.4949).
  pose B3'  := Rpower 2 (- 51.9099).
  pose Bz' z := B1 * Rabs z +       B2' * (Rabs z) ^ 2 + B3' * (Rabs z) ^ 3 + 
           B4 * (Rabs z) ^ 4 + B5 * (Rabs z) ^ 5 + B6 * (Rabs z) ^ 6 + 
           B7 * (Rabs z) ^ 7.
  pose d0d6 := (1 + d0) * (1 + d6).
  have Vd0d6 : 1 - 3.505 * u_ - 4 * u_ ^ 2  <= d0d6 <= 
                 1 + 3.505 * u_ + 4 * u_ ^ 2 . 
      rewrite /d0d6 .
      clear -V1 V6 d0d6B u_E.
      rewrite u_E in d0d6B *.
      by split_Rabs; nra.
  have K2' : Rabs (t5 * P3) <= B2'.
    rewrite /B2' /P3 /t5 /t4.
    have -> : (1 + d0) * (1 + d3) * (1 + d5) * (1 + d6) = 
         (d0d6) * (1 + d3) * (1 + d5) by rewrite /d0d6; lra.
    by interval with (i_prec 100).
  have K3' : Rabs (t5 * P4) <= B3'.
    rewrite /B3' /P4 /t5 /t4.
    have -> : (1 + d0) * (1 + d3) * (1 + d5) * (1 + d6) = 
         (d0d6) * (1 + d3) * (1 + d5) by rewrite /d0d6; lra.
    by interval with (i_prec 100).
  have K8' : Rabs nphi <= Bz' z.
    rewrite /nphi /Bz' /A /B /C.
    clear - K1 K2' K3' K4 K5 K6 K7.
    rewrite [in X in _ <= X]Rplus_assoc.
    apply: Rle_trans (Rabs_triang _ _) _.
      apply: Rplus_le_compat; last first.
      rewrite Rplus_comm Rmult_plus_distr_l Rmult_plus_distr_r.
      apply: Rle_trans (Rabs_triang _ _) _.
        apply: Rplus_le_compat.
        rewrite Rabs_mult RPow_abs.
        by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
      rewrite 2!Rmult_assoc -[in X in Rabs (_ * (_ * (X * _)))  <= _](pow_1 z).
      rewrite -pow_add -Rmult_assoc.
      rewrite Rabs_mult RPow_abs.
      by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
    rewrite [in X in _ <= X]Rplus_assoc.
    apply: Rle_trans (Rabs_triang _ _) _.
      apply: Rplus_le_compat; last first.
      rewrite Rplus_comm Rmult_plus_distr_l Rmult_plus_distr_r.
      apply: Rle_trans (Rabs_triang _ _) _.
        apply: Rplus_le_compat.
        rewrite Rabs_mult RPow_abs.
        by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
      rewrite 2!Rmult_assoc -[in X in Rabs (_ * (_ * (X * _)))  <= _](pow_1 z).
      rewrite -pow_add -Rmult_assoc.
      rewrite Rabs_mult RPow_abs.
      by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
    rewrite [in X in _ <= X]Rplus_assoc.
    apply: Rle_trans (Rabs_triang _ _) _.
      apply: Rplus_le_compat; last first.
      rewrite Rplus_comm Rmult_plus_distr_l Rmult_plus_distr_r.
      apply: Rle_trans (Rabs_triang _ _) _.
        apply: Rplus_le_compat.
        rewrite Rabs_mult RPow_abs.
        by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
      rewrite 2!Rmult_assoc -[in X in Rabs (_ * (_ * (X * _)))  <= _](pow_1 z).
      rewrite -pow_add -Rmult_assoc.
      rewrite Rabs_mult RPow_abs.
      by apply: Rmult_le_compat_r => //; apply: Rabs_pos.
    rewrite Rabs_mult.
    apply: Rmult_le_compat_r => //; first by apply: Rabs_pos.
    by lra.
  have phiB' : phi < Rpower 2 (- 67.4878).
    apply: Rle_lt_trans 
       (_ :  Bz' (32.0001 * pow (-13)) / Cz (32.1 * pow (-13)) < _); last first.
      rewrite /Bz' /Cz /B1 /B2' /B3' /B4 /B5 /B6 /B7 /P3 /P4 /P5 /P6 /P7 /P8.
      by interval with (i_prec 100).
    rewrite /phi.
    have CzB : 0 < Cz (32.1 * pow (-13)) <= Cz z.
      rewrite /Cz /P3 /P4 /P5 /P6 /P7 /P8.
      by split; interval with (i_prec 100).
    apply: Rle_trans (_ : Bz' z / Cz z <= _).
      apply: Rmult_le_compat; first apply: Rabs_pos.
      - by apply: Rinv_0_le_compat; lra.
      - by lra.
      by apply: Rinv_le_contravar; lra.
    apply: Rmult_le_compat.
    - rewrite /Bz' /B1 /B2' /B3' /B4 /B5 /B6 /B7.
      by interval with (i_prec 100).
    - by apply: Rinv_0_le_compat; lra.
    - rewrite /Bz' /Cz /B1 /B2' /B3' /B4 /B5 /B6 /B7 /P3 /P4 /P5 /P6 /P7 /P8.
      clear -zB1.
      interval with (i_prec 100).
    by apply: Rinv_le_contravar; lra.
  rewrite Herr in phiB'.
  have HB1' : Rabs ((z + ph + pl) / ln (1 + z) -1) < Rpower 2 (-67.441).
    apply: Rle_lt_trans (_ : (1 + Rpower 2 (- 67.4878)) * (1 + Rpower 2 (- 72.423)) 
                        - 1 < _); last by interval with (i_prec 100).
    pose P1 z := 
         1 - z / 2 + P3 * z ^ 2 + P4 * z ^ 3 + P5 * z ^ 4 + 
         P6 * z ^ 5 + P7 * z ^ 6 + P8 * z ^ 7.
    have P1E : P z = z * P1 z by rewrite /P /P1; lra.
    have P1_gt_0 : 0 < P1 z.
      by rewrite /P1 /P3 /P4 /P5 /P6 /P7 /P8; interval.
    have Pz_neq_0 : P z <> 0.
      by rewrite P1E; clear -P1_gt_0 z_neq0; nra.
    have -> :  (z + ph + pl) / ln (1 + z) = 
               ((z + ph + pl) / P z) *  (P z / ln (1 + z)).
      field; split => //.
      apply: ln_neq_0; first by lra.
      by interval.
    have HB' : Rabs ((z + ph + pl) / P z - 1) <= (Rpower 2 (- 67.4878)) /\ 
         Rabs (P z / ln (1 + z) - 1) <= (Rpower 2 (-72.423)).
      split.
        rewrite /Rdiv -Rabs_inv -Rabs_mult in phiB'.
        have <- : (z + ph + pl - P z) * / P z = (z + ph + pl) / P z  - 1.
          by field.
        by lra.
        have <- : - ((ln (1 + z) - P z) / ln (1 + z)) = P z / ln (1 + z) - 1.
          field.
          apply: ln_neq_0; first by lra.
          by interval.
        by rewrite Rabs_Ropp; lra.
    clear -HB'.
    by split_Rabs; nra.
  by [].
Qed.

End Exp.


