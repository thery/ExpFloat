Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section algoP1.

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

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Local Notation ulp := (ulp beta fexp).


Definition P3 :=   0x1.5555555555558p-2.
Definition P4 := - 0x1.0000000000003p-2.
Definition P5 :=   0x1.999999981f535p-3.
Definition P6 := - 0x1.55555553d1eb4p-3.
Definition P7 :=   0x1.2494526fd4a06p-3.
Definition P8 := - 0x1.0001f0c80e8cep-3.

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
Proof. by rewrite /P3 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_P3 : format P3.
Proof.
rewrite -Pf3E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Pf4E : F2R Pf4 = P4.
Proof. by rewrite /P4 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_P4 : format P4.
Proof.
rewrite -Pf4E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Pf5E : F2R Pf5 = P5.
Proof. by rewrite /P5 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_P5 : format P5.
Proof.
rewrite -Pf5E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Pf6E : F2R Pf6 = P6.
Proof. by rewrite /P6 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_P6 : format P6.
Proof.
rewrite -Pf6E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Pf7E : F2R Pf7 = P7.
Proof. by rewrite /P7 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_P7 : format P7.
Proof.
rewrite -Pf7E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Pf8E : F2R Pf8 = P8.
Proof. by rewrite /P8 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

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

Lemma Pz_pos z : Rabs z < 33 * (Rpower 2 (-13)) -> 0 <= Pz z.
Proof. by move=> *; rewrite /Pz /P3 /P4 /P5 /P6 /P7 /P8; interval. Qed.

Lemma P_abs_error z :
  Rabs z <= 33 * (Rpower 2 (-13)) -> 
  Rabs (ln (1 + z) - P z) <= Rpower 2 (- 81.63).
Proof.
move=> *; rewrite /P /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 90, i_bisect z, i_taylor z, i_degree 8).
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
move=> *.
interval with (i_prec 200, i_depth 50, i_bisect z, i_taylor z, i_degree 20).
Qed.

Lemma P_rel_error_neg z :
  - 33 * Rpower 2 (-13) <= z <= - Rpower 2 (-80) ->
  Rabs ((ln (1 + z) - P z) / (ln (1 + z))) < Rpower 2 (- 72.423).
Proof.
move=> *.
interval with (i_prec 200, i_depth 50, i_bisect z, i_taylor z, i_degree 20).
Qed.

Lemma P_rel_error z :
  Rabs z <= 33 * Rpower 2 (-13)  ->
  Rabs ((ln (1 + z) - P z) / (ln (1 + z))) < Rpower 2 (- 72.423).
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

Notation exactMul := (exactMul rnd).

(* L'algo p_1 *)

Definition p1 (z : R) :=
  let: DWR wh wl := exactMul z z in 
  let: t := RN (P8 * z + P7) in
  let: u := RN (P6 * z + P5) in
  let: v := RN (P4 * z + P3) in
  let: u := RN (t * wh + u) in 
  let: v := RN (u * wh + v) in 
  let: u := RN (v * wh) in 
  DWR (RN (- 0.5 * wh)) (RN (u * z - 0.5 * wl)).

Lemma p1_0 : p1 0 = DWR 0 0. 
Proof. by rewrite /p1 !(Rsimp01, exactMul0l, round_0). Qed.

Lemma absolute_rel_error_main (z : R) :
  format z -> 
  Rabs z <= 33 * Rpower 2 (-13) ->
  is_imul z (Rpower 2 (-61)) ->
  let: DWR ph pl := p1 z in 
  [/\
  Rabs((ph + pl) - (ln (1 + z) - z)) < Rpower 2 (-75.492), 
  (z <> 0%R ->  
    ((Rabs ((z + ph + pl) / ln (1 + z) -1) < Rpower 2 (- 67.2756)) /\
     (Rabs z < 32 * Rpower 2 (-13) ->
        Rabs ((z + ph + pl) / ln (1 + z) -1) < Rpower 2 (- 67.441)))
  ),
  (is_imul ph (pow (- 123)) /\ Rabs ph < Rpower 2 (-16.9)) &
  (is_imul pl (pow (- 543)) /\ Rabs pl < Rpower 2 (-25.446))].
Proof.
move=> Fz zB Mz /=.
rewrite -pow_Rpower // in Mz.
set wh := RN (z * z).
set wl := RN (z * z - wh).
set t := RN (P8 * z + P7).
set u := RN (P6 * z + P5).
set v := RN (P4 * z + P3).
set u' := RN (t * wh + u).
set v' := RN (u' * wh + v).
set u'' := RN (v' * wh).
set ph := RN (-0.5 * wh).
set pl := RN (u'' * z - 0.5 * wl).
have Fwh : format wh by apply: generic_format_round.
have wh_ge_0 : 0 <= wh.
  have G1 : is_imul (z * z) (pow (-122)).
    have -> : pow (-122) = pow (-61) * pow (-61) by rewrite -bpow_plus.
    by apply: is_imul_mul.
  by apply: is_imul_format_round_ge_0 _ G1 _ => //=; nra.
have wh_wl_zz : wh + wl = z * z.
  apply: exactMul_correct => //.
  have [k ->] := Mz.
  exists (k * k * 2 ^ 952)%Z.
  rewrite 2!mult_IZR  -[bpow _ _]/(pow _) -[bpow radix2 _]/(pow _) -/emin.
  suff : pow (-61) * pow (-61) = IZR (2 ^ 952) * pow emin by nra.
  by rewrite -!bpow_plus (IZR_Zpower beta) // -bpow_plus.
have zzLe : z ^ 2 <= 33 ^ 2 * Rpower 2 (-26).
  have -> : Rpower 2 (-26) = (Rpower 2 (-13)) ^ 2.
    by rewrite pow2_mult -Rpower_plus; congr (Rpower _ _); lra.
  rewrite -Rpow_mult_distr.
  by apply: pow_maj_Rabs.
have zzLt : z ^ 2 < Rpower 2 (- 15.91).
  by apply: Rle_lt_trans zzLe _; interval.
have uzzLe : ulp(z ^ 2) <= Rpower 2 (-68).
  apply: Rle_trans (_ : ulp (33 ^ 2 * Rpower 2 (-26)) <= _).
    apply: ulp_le => //.
    by rewrite !Rabs_pos_eq //; nra.
  rewrite ulp_neq_0 /cexp /fexp; last first.
    interval.
  have -> : (mag beta (33 ^ 2 * Rpower 2 (-26)) = (-15) :> Z)%Z.
    apply: mag_unique_pos.
    by rewrite !pow_Rpower /=; split; interval.
  by rewrite pow_Rpower /emin /Z.max /= //; lra.
have whLe : Rabs wh <= Rpower 2 (-15.91) + Rpower 2 (-68).
  apply: Rle_trans (_ : z ^ 2 + ulp (z ^2) <= _); last by lra.
  rewrite Rabs_pos_eq; last first.
    rewrite -(round_0 beta fexp).
    by apply: round_le; nra.
  suff : Rabs (RN (z ^ 2) - z ^ 2) <= ulp(z ^ 2).
    by rewrite /wh -pow2_mult; split_Rabs; lra.
  by apply: error_le_ulp.
rewrite Rabs_pos_eq in whLe; last by lra.
have wlLe : Rabs wl <= Rpower 2 (-68).
  apply: Rle_trans uzzLe.
  have -> : wl = - (wh - z ^ 2) by lra.
  rewrite Rabs_Ropp.
  rewrite /wh -pow2_mult.
  by apply: error_le_ulp.
have imul_wh : is_imul wh (pow (- 122)).
  apply: is_imul_pow_round.
  have -> : pow (-122) = pow (-61) * pow (-61) by rewrite -bpow_plus.
  by apply: is_imul_mul.
have imul_wl : is_imul wl (pow (- 122)).
  have -> : wl = z * z - wh by lra.
  apply: is_imul_minus => //.
  have -> : pow (-122) = pow (-61) * pow (-61) by rewrite -bpow_plus.
  by apply: is_imul_mul.
have phE : ph = -0.5 * wh.
  rewrite /ph round_generic //.
  have-> : -0.5 = -(0.5) by lra.
  rewrite -!Ropp_mult_distr_l.
  apply: generic_format_opp.
  by apply: is_imul_format_half Fwh imul_wh _; lia.
have imul_zz122 : is_imul (z ^ 2) (pow (-122)).
  have -> : pow (-122) = pow (-61) * pow (-61) by rewrite -bpow_plus.
  by rewrite pow2_mult; apply: is_imul_mul.
have imul_zz123 : is_imul (z ^ 2) (pow (-123)).
  by apply: is_imul_pow_le imul_zz122 _; lia.
have imul_zzBwh : is_imul (z ^ 2 - wh) (pow (-123)).
  by apply: is_imul_pow_le (is_imul_minus imul_zz122 imul_wh) _; lia.
have imul_half_wh : is_imul (0.5 * wh) (pow (-123)).
  have-> : pow (-123) = pow (-1) * pow (-122) by rewrite -bpow_plus.
  by rewrite powN1; apply: is_imul_mul => //; exists 1%Z; lra.
have imul_half_wl : is_imul (0.5 * wl) (pow (-123)).
  have-> : pow (-123) = pow (-1) * pow (-122) by rewrite -bpow_plus.
  by rewrite powN1; apply: is_imul_mul => //; exists 1%Z; lra.
pose e1 := t - (P8 * z + P7).
have e1E : t = P8 * z + P7 + e1 by rewrite /e1;lra.
have [e1Le tLe tB imul_t] : 
  [/\ 
    Rabs e1 <= pow (- 55),
    t <= Rpower 2 (- 2.8022) + Rpower 2 (-55),
    0 < t < Rpower 2 (- 2.802) & 
    is_imul t (pow (-116))].
  have P8zP7B : 0 < P8 * z + P7 < Rpower 2 (- 2.8022).
    by split; rewrite /P8 /P7; interval.
  have u28022 : ulp (Rpower 2 (- 2.8022)) = pow (-55).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (-55 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have e1Le : Rabs e1 <= pow (- 55).
    rewrite -u28022 /e1.
    apply: Rle_trans (_ : ulp (P8 * z + P7) <= _); last first.
      by apply: ulp_le; clear -P8zP7B; split_Rabs; lra.
    by apply: error_le_ulp.
  have tLe : t <= Rpower 2 (- 2.8022) + Rpower 2 (-55).
    apply: Rle_trans (_ : Rabs e1 + P8 * z + P7 <= _).
      by rewrite /e1; clear -e1E P8zP7B; split_Rabs; lra.
    by rewrite pow_Rpower // in e1Le; lra.
  have tLt : t < Rpower 2 (- 2.802) by interval. 
  have imul_P8zP7 : is_imul (P8 * z + P7) (pow (-116)).
    apply: is_imul_add.
      have -> : pow (-116) = pow (-55) * pow (-61).
        by rewrite -bpow_plus; congr (pow _); lia.
      apply: is_imul_mul => //.
      exists (-4503732981131470)%Z.
      by rewrite /P8 /= /Z.pow_pos /=; lra.
    exists (11868429770568140608450203318484992)%Z.
    by rewrite /P7 /= /Z.pow_pos /=; lra.
  have imul_t : is_imul t (pow (-116)).
    by apply: is_imul_pow_round.
  suff t_gt0 : 0 < t by [].
  by apply: is_imul_format_round_gt_0 _ imul_P8zP7 _ => //=; nra.
pose e2 := u - (P6 * z + P5).
have e2E : u = P6 * z + P5 + e2 by rewrite /e2;lra.
have [e2Le uB uLw imul_u] : 
  [/\ 
    Rabs e2 <= pow (- 55),
    0 < u < Rpower 2 (- 2.317),
    u <= Rpower 2 (-2.31709) + Rpower 2 (-55) & 
    is_imul u (pow (-116))].
  have P6zP5B : 0 < P6 * z + P5 < Rpower 2 (- 2.31709).
    by split; rewrite /P6 /P5; interval.
  have u131709 : ulp (Rpower 2 (- 2.31709)) = pow (-55).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (-55 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have e2Le : Rabs e2 <= pow (- 55).
    rewrite -u131709 /e2.
    apply: Rle_trans (_ : ulp (P6 * z + P5) <= _); last first.
      by apply: ulp_le; clear -P6zP5B; split_Rabs; lra.
    by apply: error_le_ulp.
  have uLe : u <= Rpower 2 (-2.31709) + Rpower 2 (-55).
    apply: Rle_trans (_ : Rabs e2 + P6 * z + P5 <= _).
      by rewrite /e2; clear e2E P6zP5B; split_Rabs; lra.
    by rewrite pow_Rpower // in e2Le; lra.
  have uLt : u < Rpower 2 (- 2.317) by interval. 
  have imul_P6zP5 : is_imul (P6 * z + P5) (pow (-116)).
    apply: is_imul_add.
      have -> : pow (-116) = pow (-55) * pow (-61).
        by rewrite -bpow_plus; congr (pow _); lia.
      apply: is_imul_mul => //.
      exists (-6004799501573812)%Z.
      by rewrite /P6 /= /Z.pow_pos /=; lra.
    exists (16615349943738746199199974751731712)%Z.
    by rewrite /P5 /= /Z.pow_pos /=; lra.
  have imul_u : is_imul u (pow (-116)) by apply: is_imul_pow_round.
  suff u_gt0 : 0 < u by [].
  by apply: is_imul_format_round_gt_0 _ imul_P6zP5 _ => //=; nra.
pose e3 := v - (P4 * z + P3).
have e3E : v = P4 * z + P3 + e3 by rewrite /e3;lra.
have [e3Le vLe vB imul_v] : 
  [/\ 
    Rabs e3 <= pow (- 54),
    v <= Rpower 2 (- 1.5806) + Rpower 2 (-54),
    0 < v < Rpower 2 (- 1.580) & 
    is_imul v (pow (-115))].
  have P4zP3B: 0 < P4 * z + P3 < Rpower 2 (- 1.5806).
    by split; rewrite /P4 /P3; interval.
  have u15806 : ulp (Rpower 2 (- 1.5806)) = pow (-54).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (-54 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have e3Le : Rabs e3 <= pow (- 54).
    rewrite -u15806 /e3.
    apply: Rle_trans (_ : ulp (P4 * z + P3) <= _); last first.
      by apply: ulp_le; clear -P4zP3B; split_Rabs; lra.
    by apply: error_le_ulp.
  have vLe : v <= Rpower 2 (- 1.5806) + Rpower 2 (-54).
    apply: Rle_trans (_ : Rabs e3 + P4 * z + P3 <= _).
      by rewrite /e3; clear -P4zP3B; split_Rabs; lra.
    by rewrite pow_Rpower // in e3Le; lra.
  have vLt : v < Rpower 2 (- 1.580) by interval. 
  have imul_P4zP3 : is_imul (P4 * z + P3) (pow (-115)).
    apply: is_imul_add.
      have -> : pow (-115) = pow (-54) * pow (-61).
        by rewrite -bpow_plus; congr (pow _); lia.
      apply: is_imul_mul => //.
      exists (-4503599627370499)%Z.
      by rewrite /P4 /= /Z.pow_pos /=; lra.
    exists (13846124956092879824996014781104128)%Z.
    by rewrite /P3 /= /Z.pow_pos /=; lra.
  have imul_v : is_imul v (pow (-115)) by apply: is_imul_pow_round.
  suff v_gt0 : 0 < v by [].
  by apply: is_imul_format_round_gt_0 _ imul_P4zP3 _ => //=; nra.
pose e4 := u' - (t * wh + u).
have e4E : u' = t * wh + u + e4 by rewrite /e4; lra.
have [e4Le u'Le u'B imul_u'] : 
  [/\ 
    Rabs e4 <= pow (- 55),
    u' <= Rpower 2 (-2.31707) + Rpower 2 (-55), 
    0 < u' < Rpower 2 (- 2.31706) & 
    is_imul u' (pow (-238))].
  have twhuB : 0 < t * wh + u < Rpower 2 (- 2.31707).
    split; first by nra.
    apply: Rle_lt_trans
      (_ :  Rpower 2 (-2.802) * (Rpower 2 (-15.91) + Rpower 2 (-68)) + 
            (Rpower 2 (- 2.31709) + Rpower 2 (- 55)) < _); last by interval.
    by nra.
  have u231707 : ulp (Rpower 2 (-2.31707)) = pow (-55).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (-55 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have e4Le : Rabs e4 <= pow (- 55).
    rewrite -u231707 /e4.
    apply: Rle_trans (_ : ulp (t * wh + u) <= _); last first.
      by apply: ulp_le; clear -twhuB; split_Rabs; lra.
    by apply: error_le_ulp.    
  have u'Le : u' <= Rpower 2 (-2.31707) + Rpower 2 (-55).
    apply: Rle_trans (_ : Rabs e4 + t * wh + u <= _).
      by rewrite /e4; clear -twhuB; split_Rabs; lra.
    by rewrite pow_Rpower // in e4Le; lra.
  have u'Lt : u' < Rpower 2 (-2.31706) by interval. 
  have imul_twhu : is_imul (t * wh + u) (pow (-238)).
    apply: is_imul_add; last first.
      by apply: is_imul_pow_le imul_u _; lia.
    have -> : pow (-238) = pow (-116) * pow (-122).
      by rewrite -bpow_plus; congr (pow _); lia.
    by apply: is_imul_mul.
  have imul_u' : is_imul u'  (pow (-238)).
    by apply: is_imul_pow_round.
  suff u'_gt0 : 0 < u' by [].
  by apply: is_imul_format_round_gt_0 _ imul_twhu _ => //=; nra.
pose e5 := v' - (u' * wh + v).
have e5E : v' = u' * wh + v + e5 by rewrite /e5; lra.
have [e5Le v'Le v'B imul_v'] : 
  [/\ 
    Rabs e5 <= pow (- 54),
    v' <= Rpower 2 (- 1.58058) + Rpower 2 (-54), 
    0 < v' < Rpower 2 (- 1.5805) & 
    is_imul v' (pow (- 360))].
  have u'whvB : 0 < u' * wh + v < Rpower 2 (- 1.58058).
    split; first by nra.
    apply: Rle_lt_trans
      (_ :  Rpower 2 (- 2.31706) * (Rpower 2 (-15.91) + Rpower 2 (-68)) + 
            (Rpower 2 (- 1.5806) + Rpower 2 (- 54)) < _); last by interval.
    by nra.
  have u158058 : ulp (Rpower 2 (- 1.58058)) = pow (-54).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (- 54 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have e5Le : Rabs e5 <= pow (- 54).
    rewrite -u158058 /e5.
    apply: Rle_trans (_ : ulp (u' * wh + v) <= _); last first.
      by apply: ulp_le; clear -u'whvB; split_Rabs; lra.
    by apply: error_le_ulp.
  have v'Le : v' <= Rpower 2 (- 1.58058) + Rpower 2 (-54).
    apply: Rle_trans (_ : Rabs e5 + u' * wh + v <= _).
      by rewrite /e5;  clear -u'whvB; split_Rabs; lra.
    by rewrite pow_Rpower // in e5Le; lra.
  have v'Lt : v' < Rpower 2 (-1.5805) by interval. 
  have imul_u'whv : is_imul (u' * wh + v) (pow (- 360)).
    apply: is_imul_add; last first.
      by apply: is_imul_pow_le imul_v _; lia.
    have -> : pow (- 360) = pow (- 238) * pow (-122).
      by rewrite -bpow_plus; congr (pow _); lia.
    by apply: is_imul_mul.
  have imul_v' : is_imul v'  (pow (- 360)).
    by apply: is_imul_pow_round.
  suff v'_gt0 : 0 < v' by [].
  by apply: is_imul_format_round_gt_0 _ imul_u'whv _ => //=; nra.
pose e6 := u'' - (v' * wh).
have e6E : u'' = v' * wh + e6 by rewrite /e6; lra.
have [e6Le u''Le u''B imul_u''] : 
  [/\ 
    Rabs e6 <= pow (- 70),
    u'' <= Rpower 2 (- 17.49057) + Rpower 2 (- 70),
    0 <= u'' < Rpower 2 (- 17.4905) & 
    is_imul u'' (pow (- 482))].
  have v'whB : 0 <= v' * wh < Rpower 2 (- 17.49057).
    split; first by nra.
    apply: Rle_lt_trans
      (_ :  (Rpower 2 (- 1.58058) + Rpower 2 (- 54)) *
            (Rpower 2 (- 15.91) + Rpower 2 (- 68)) < _); last by interval.
    by apply: Rmult_le_compat; lra.
  have u1749057 : ulp (Rpower 2 (- 17.49057)) = pow (- 70).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (- 70 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
  have e6Le : Rabs e6 <= pow (- 70).
    rewrite -u1749057 /e6.
    apply: Rle_trans (_ : ulp (v' * wh) <= _); last first.
      by apply: ulp_le; clear -v'whB; split_Rabs; lra.
    by apply: error_le_ulp.
  have u''Le : u'' <= Rpower 2 (- 17.49057) + Rpower 2 (- 70).
    apply: Rle_trans (_ : Rabs e6 + v' * wh <= _).
      by rewrite /e6; clear -v'whB; split_Rabs; lra.
    by rewrite pow_Rpower // in e6Le; lra.
  have u''Lt : u'' < Rpower 2 (- 17.4905) by interval. 
  have imul_v'wh : is_imul (v' * wh) (pow (- 482)).
    have -> : pow (- 482) = pow (- 360) * pow (-122).
      by rewrite -bpow_plus; congr (pow _); lia.
    by apply: is_imul_mul.
  have imul_u'' : is_imul u'' (pow (- 482)).
    by apply: is_imul_pow_round.
  suff u''_ge0 : 0 <= u'' by [].
  by apply: is_imul_format_round_ge_0 _ imul_v'wh _ => //=; nra.
pose e7 := pl - (u'' * z - 0.5 * wl).
have e7E : pl = u'' * z - 0.5 * wl + e7 by rewrite /e7; lra.
have [e7Le plB imul_pl] : 
  [/\ 
    Rabs e7 <= pow (- 78),
    Rabs pl < Rpower 2 (- 25.446) & 
    is_imul pl (pow (- 543))].
  have u''zhwlLt : Rabs (u'' * z - 0.5 * wl) < Rpower 2 (- 25.4461).
    apply: Rle_lt_trans
      (_ :  (Rpower 2 (- 17.49057) + Rpower 2 (- 70)) *
            (33  * Rpower 2 (- 13)) + Rpower 2 (- 69) < _); last by interval.
    apply: Rle_trans
      (_ :  (u'' * Rabs z + 0.5 * Rabs wl <= _)).
      by  clear -u''B; split_Rabs; nra.
    apply: Rplus_le_compat; last first.
      suff -> : Rpower 2 (-69) = 0.5 * Rpower 2 (- 68) by lra.
      have -> : 0.5 = Rpower 2 (-1).
        by rewrite -pow_Rpower //= /Z.pow_pos /=; lra.
      by rewrite -Rpower_plus; congr (Rpower _ _); lra.
    apply: Rmult_le_compat; try lra.
    by apply: Rabs_pos.
  have u254461 : ulp (Rpower 2 (- 25.4461)) = pow (- 78).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (- 78 + p)%Z); try lra.
    - rewrite Z.max_l; last by lia.
      congr bpow; lia.
    - by rewrite !pow_Rpower /p/=;split; [apply: Rle_Rpower|apply: Rpower_lt];
       lra.
    by interval.
  have e7Le : Rabs e7 <= pow (- 78).
    rewrite -u254461 /e7.
    apply: Rle_trans (_ : ulp (u'' * z - 0.5 * wl) <= _); last first.
      by apply: ulp_le; clear -u''zhwlLt; split_Rabs; lra.
    by apply: error_le_ulp.
  have plLt : Rabs pl < Rpower 2 (- 25.446).
    apply: Rle_lt_trans (_ : Rpower 2 (- 25.4461) + Rpower 2 (- 78) < _).
      apply: Rle_trans (_ : Rabs e7 + Rabs (u'' * z - 0.5 * wl) <= _).
        by rewrite /e7; clear -u''B; split_Rabs; lra.
      by rewrite pow_Rpower // in e7Le; lra.
    by interval. 
  have imul_u''zhwl : is_imul (u'' * z - 0.5 * wl) (pow (- 543)).
    apply: is_imul_minus.
      have -> : pow (- 543) = pow (- 482) * pow (- 61).
        by rewrite -bpow_plus; congr (pow _); lia.
      by apply: is_imul_mul.
    have -> : pow (- 543) = pow (- 1) * pow (- 542).
      by rewrite -bpow_plus; congr (pow _); lia.
    apply: is_imul_mul.
      by exists 1%Z; rewrite /= /Z.pow_pos /=; lra.
    by apply: is_imul_pow_le imul_wl _; lia.
  suff imul_pl : is_imul pl (pow (- 543)) by [].
  by apply: is_imul_pow_round.
set E := Rabs (ph + pl - (P z - z)).
pose Q := P3 + P4 * z + P5 * z ^ 2 + P6 * z ^ 3 +
         P7 * z ^ 4 + P8 * z ^ 5.
have PzE : P z - z = - 0.5 * z ^ 2 + z ^ 3 * Q by rewrite /P /Q; lra.
pose tR := P5 + P6 * z + P7 * z ^ 2 + P8 * z ^ 3.
have QE : Q = P3 + P4 * z + tR * z ^ 2 by rewrite /Q /tR; lra.
have F22 : E = Rabs (u'' * z + e7 - z ^ 3 * Q).
  congr (Rabs _); rewrite PzE.
  suff : ph + pl + 0.5 * z ^ 2 = u'' * z + e7 by lra.
  by rewrite pow2_mult -wh_wl_zz e7E phE; lra.
pose E1 := Rabs (u'' - z ^ 2 * Q); pose tE0 := Rabs e7.
have ELe : E <= E1 * Rabs z + tE0.
  rewrite /tE0 /E1 F22.
  by clear; split_Rabs; nra.
pose E3 := Rabs (v' - Q); pose tE1 := Rabs (- v' * wl + e6).
have E1LE2zzE1 : E1 <= E3 * z ^ 2 + tE1.
  rewrite /tE1 /E1 /E3.
  have -> : u'' = v' * z ^ 2 - v' * wl + e6.
    by rewrite e6E pow2_mult -wh_wl_zz; lra.
  by clear; split_Rabs; nra.
pose E5 := Rabs (u' - tR); pose tE3 := Rabs (- u' * wl + e3 + e5).
have E3LE5zzE3 : E3 <= E5 * z ^ 2 + tE3.
  rewrite /E3 /E5 /tE3.
  have -> : v' - Q = (u' - tR) * z ^ 2  - u' * wl + e3 + e5.
    have -> : v' = u' * (z ^ 2 - wl) + (P4 * z + P3 + e3 ) + e5.
      by rewrite pow2_mult -wh_wl_zz; lra.
    by lra.
  by clear; split_Rabs; nra.
pose tE7 := Rabs e1; pose tE5 := Rabs (- t * wl + e2 + e4).
have E5LE7zzE5 : E5 <= tE7 * z ^2 + tE5.
  rewrite /E5 /tE7 /tE5.
  have-> : u' - tR = e1 * z ^ 2 - t * wl + e2 + e4 by rewrite /tR; nra.
  by clear; split_Rabs; nra.
have ELe75513 : E <= Rpower 2 (- 75.513).
  apply: Rle_trans 
      (_ : tE0 + tE1 * Rabs z + tE3 * Rabs z ^ 3 + 
                 tE5 * Rabs z ^ 5 + tE7 * Rabs z ^ 7 <= _).
    apply: Rle_trans ELe _.
    suff : E1 <= tE1 + tE3 * Rabs z ^ 2 + tE5 * Rabs z ^ 4 + tE7 * Rabs z ^ 6.
      have : 0 <= Rabs z by apply: Rabs_pos.
      by nra.
    rewrite pow2_abs.
    have -> : Rabs z ^ 4 = z ^ 4.
      have-> : (Rabs z) ^ 4 = (Rabs z ^ 2) ^ 2 by lra.
      by rewrite pow2_abs; lra.
    have -> : Rabs z ^ 6 = z ^ 6.
      have-> : (Rabs z) ^ 6 = (Rabs z ^ 2) ^ 3 by lra.
      by rewrite pow2_abs; lra.
    apply: Rle_trans E1LE2zzE1 _.
    suff : E3 <= tE3 + tE5 * z ^ 2 + tE7 * z ^ 4 by nra.
    by nra.
  have E0Le : tE0 <= pow (- 78) by rewrite /tE0; lra.
  have E1Lt : tE1 < Rpower 2 (- 68.775).
    apply: Rle_lt_trans 
      (_ : (Rpower 2 (- 1.58058) + pow (-54)) * pow (-68) + pow (-70) < _);
        last first.
      by rewrite !pow_Rpower //; interval.
    apply: Rle_trans (_ : Rabs v' * Rabs wl + Rabs e6 <= _).
      by rewrite /tE1; clear; split_Rabs; nra.
    have-> : Rabs v' = v' by rewrite Rabs_pos_eq; lra.
    apply: Rplus_le_compat => //.
    apply: Rmult_le_compat; first by lra.
    - by apply: Rabs_pos; lra.
    - by rewrite pow_Rpower.
    by rewrite pow_Rpower.
  have E3Lt : tE3 < Rpower 2 (- 52.999).
    apply: Rle_lt_trans 
      (_ : (Rpower 2 (- 2.31707) + pow (-55)) * pow (-68) + 
            pow (-54) + pow (-54) < _);
        last first.
      by rewrite !pow_Rpower //; interval.
    apply: Rle_trans (_ : u' * Rabs wl + Rabs e3  + Rabs e5 <= _).
      by rewrite /tE3; clear -u'B; split_Rabs; nra.
    apply: Rplus_le_compat => //.
    apply: Rplus_le_compat => //.
    apply: Rmult_le_compat => //; first by lra.
    - by apply: Rabs_pos; lra.
    - by rewrite pow_Rpower.
    by rewrite pow_Rpower.
  have E5Lt : tE5 < Rpower 2 (- 53.999).
    apply: Rle_lt_trans 
      (_ : (Rpower 2 (- 2.8022) + pow (-55)) * pow (-68) + 
            pow (-55) + pow (-55) < _);
        last first.
      by rewrite !pow_Rpower //; interval.
    apply: Rle_trans (_ : t * Rabs wl + Rabs e2 + Rabs e4 <= _).
      by rewrite /tE5; clear -tB; split_Rabs; nra.
    apply: Rplus_le_compat => //.
    apply: Rplus_le_compat => //.
    apply: Rmult_le_compat => //; first by lra.
    - by apply: Rabs_pos; lra.
    - by rewrite pow_Rpower.
    by rewrite pow_Rpower.
  have E7Le : tE7 <= Rpower 2 (- 55) by rewrite /tE7 -pow_Rpower.
  have z3Le : (Rabs z) ^ 3 <= 33 ^ 3 * (Rpower 2 (-13)) ^ 3.
    rewrite -Rpow_mult_distr.
    apply: pow_incr; split; last by lra.
    by apply: Rabs_pos.
  have z5Le : (Rabs z) ^ 5 <= 33 ^ 5 * (Rpower 2 (-13)) ^ 5.
    rewrite -Rpow_mult_distr.
    apply: pow_incr; split; last by lra.
    by apply: Rabs_pos.
  have z7Le : (Rabs z) ^ 7 <= 33 ^ 7 * (Rpower 2 (-13)) ^ 7.
    rewrite -Rpow_mult_distr.
    apply: pow_incr; split; last by lra.
    by apply: Rabs_pos.
  apply: Rle_trans.
    apply: Rplus_le_compat; last first.
      apply: Rmult_le_compat E7Le z7Le; first by apply: Rabs_pos.
      by apply/pow_le/Rabs_pos.
    apply: Rplus_le_compat; last first.
      apply: Rmult_le_compat (Rlt_le _ _ E5Lt) z5Le; first by apply: Rabs_pos.
      by apply/pow_le/Rabs_pos.
    apply: Rplus_le_compat; last first.
      apply: Rmult_le_compat (Rlt_le _ _ E3Lt) z3Le; first by apply: Rabs_pos.
      by apply/pow_le/Rabs_pos.
    apply: Rplus_le_compat; last first.
      apply: Rmult_le_compat (Rlt_le _ _ E1Lt) zB; first by apply: Rabs_pos.
      by apply: Rabs_pos.
    by apply: E0Le.
  by interval.
have phB : Rabs ph < Rpower 2 (-16.9).
  rewrite phE Rabs_mult Rabs_left; try lra.
  apply: Rle_lt_trans (_ : 0.5 * (33 ^ 2 * pow (-13) ^ 2) < _); last first.
    by interval.
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
split => //; first 2 last.
- split=> //.
  rewrite phE.
  have -> : -0.5 * wh = -(0.5 * wh) by lra.
  by apply: is_imul_opp.
- apply: Rle_lt_trans (_ : E + Rabs (ln (1 + z) - P z) < _).
    by rewrite /E; clear; split_Rabs; nra.
  apply: Rle_lt_trans (_ : Rpower 2 (- 75.513) + Rpower 2 (- 81.63) < _); 
      last by interval.
  apply: Rplus_le_compat => //.
  by apply: P_abs_error.
move=> z_neq0.
have {wh_ge_0}wh_gt_0 : 0 < wh.
  have G1 : is_imul (z * z) (pow (-122)).
    have -> : pow (-122) = pow (-61) * pow (-61) by rewrite -bpow_plus.
    by apply: is_imul_mul.
  by apply: is_imul_format_round_gt_0 _ G1 _ => //=; nra.
pose u_ := algoP1.u.
pose d0 := (wh - z ^ 2) / (z ^ 2).
have d0E : wh = z ^ 2 * (1 + d0) by rewrite /d0; field; lra.
have d0L2u : Rabs d0 < 2 * u_.
  apply: relative_error_is_min_eps_bound _ imul_zz123 _ _ => //.
    by rewrite /d0 => ->; rewrite Rsimp01.
  by rewrite [in LHS]pow2_mult.
have P8zP7B : Rpower 2 (- 2.8125) < P8 * z + P7  < Rpower 2 (- 2.8022).
  by rewrite /P8 /P7; split; interval.
pose d1 := e1 / (P8 * z + P7).
have d1E : t = (P8 * z + P7) * (1 + d1).
  rewrite /d1 /e1; field; interval.
have d1B : Rabs d1 < 1.76 * u_.
  rewrite /d1 [u_]uE pow_Rpower // [IZR (- p)]/=.
  by interval.
have P6zP5B : Rpower 2 (- 2.3268) < P6 * z + P5  < Rpower 2 (- 2.3170).
  by rewrite /P6 /P5; split; interval.
pose d2 := e2 / (P6 * z + P5).
have d2E : u = (P6 * z + P5) * (1 + d2).
  rewrite /d2 /e2; field; interval.
have d2B : Rabs d2 < 1.255 * u_.
  rewrite /d2 [u_]uE pow_Rpower // [IZR (- p)]/=.
  by interval.
pose d3 := e3 / (P4 * z + P3).
have d3E : v = (P4 * z + P3) * (1 + d3).
  by rewrite /d3 /e3; field; interval.
have d3B : Rabs d3 < 1.505 * u_.
  rewrite /d3 [u_]uE pow_Rpower // [IZR (- p)]/=.
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
  have G1 : u <= t * wh + u by clear -wh_gt_0 tB; nra.
  rewrite /d4 [u_]uE pow_Rpower // [IZR (- p)]/=.
  rewrite Rabs_mult Rabs_inv [X in _ * / X]Rabs_pos_eq; last by lra.
  apply/Rlt_div_l; first by lra.
  suff X1 : Rpower 2 (- 2.3269) < t * wh + u.
    set vv := t * wh + u in X1 *.
    apply: Rle_lt_trans e4Le _.
    by interval.
  apply: Rlt_le_trans (_ : u <= _); last by lra.
  rewrite /e2 in e2Le.
  clear -P6zP5B e2Le.
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
have P4zP3B : Rpower 2 (- 1.5894) < P4 * z + P3 < Rpower 2 (- 1.5806).
  by rewrite /P4 /P3; split; interval.
pose d5 := e5 / (u' * wh + v).
have d5E : v' = (u' * wh + v) * (1 + d5).
  rewrite /d5 /e5; field.
  clear -vB u'B wh_gt_0.
  by nra.
have d5B : Rabs d5 < 1.505 * u_.
  have vLu'whv : v <= u' * wh + v by clear -wh_gt_0 vB u'B; nra.
  rewrite /d5 [u_]uE pow_Rpower // [IZR (- p)]/=.
  rewrite Rabs_mult Rabs_inv [X in _ * / X]Rabs_pos_eq; last by lra.
  apply/Rlt_div_l; first by lra.
  suff X1 : Rpower 2 (- 1.5895) < u' * wh + v.
    set vv := u' * wh + v in X1 *.
    apply: Rle_lt_trans e5Le _.
    by interval.
  apply: Rlt_le_trans (_ : v <= _); last by lra.
  rewrite /e3 in e3Le.
  clear -P4zP3B e3Le.
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
  have [wh_eq0|wh_neq0] := Req_dec wh 0.
    by rewrite /d6 /u'' wh_eq0 !Rsimp01 round_0.
  rewrite /d6 /e6; field.
  by clear -v'B wh_neq0; nra.
have d6B : Rabs d6 < 2 * u_.
  have imul_v'wh : is_imul (v' * wh) (pow (- 482)).
    have -> : pow (- 482) = pow (- 360) * pow (-122).
      by rewrite -bpow_plus; congr (pow _); lia.
    by apply: is_imul_mul.
  apply: relative_error_is_min_eps_bound imul_v'wh _ d6E => //.
  by rewrite /d6 /e6 => ->; rewrite !Rsimp01.
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
  have imul_u''zhwl : is_imul (u'' * z - 0.5 * wl) (pow (- 543)).
    apply: is_imul_minus.
      have -> : pow (- 543) = pow (- 482) * pow (- 61).
        by rewrite -bpow_plus; congr (pow _); lia.
      by apply: is_imul_mul.
      have -> : pow (- 543) = pow (- 1) * pow (- 542).
      by rewrite -bpow_plus; congr (pow _); lia.
    apply: is_imul_mul.
      by exists 1%Z; rewrite /= /Z.pow_pos /=; lra.
    by apply: is_imul_pow_le imul_wl _; lia.
  by apply: relative_error_is_min_eps_bound imul_u''zhwl _ d7E.
have phplE : 
     ph + pl = - 0.5 * z ^ 2 + 0.5 * d0 * d7 * z ^ 2 + u'' * z * (1 + d7).
  have whE : wh = z ^ 2 - wl by lra.
  have wlE : wl = - z ^ 2 * d0 by lra.
  by rewrite d7E phE whE wlE; lra.
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
  rewrite pow_Rpower // 2!Rabs_mult.
  have -> : Rpower 2 (-105) = 0.5 * (2 * u_) * (2 * u_).
    have <- : pow (- 1) = 0.5 by rewrite (bpow_opp _ 1) bpow_1 /=; lra.
    rewrite pow_Rpower //.
    have -> : 2 * u_ = Rpower 2 (- 52).
      have {1}-> : 2 = Rpower 2 1 by rewrite Rpower_1; lra.
      rewrite [u_]/(Fmore.u _ _).
      have -> : / 2 = Rpower 2 (- 1) by rewrite Rpower_Ropp Rpower_1; lra.
      by rewrite pow_Rpower // -!Rpower_plus /=; congr (Rpower _ _); lra.
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
have Od0B : 1 - 2 * pow (- 53) < 1 + d0 < 1 + 2 * pow (- 53).
  by clear -d0L2u u_E; split_Rabs; lra.
have Od2B : 1 - 1.255 * pow (- 53) < 1 + d2 < 1 + 1.255 * pow (- 53).
  by clear -d2B u_E; split_Rabs; lra.
have Od3B : 1 - 1.505 * pow (- 53) < 1 + d3 < 1 + 1.505 * pow (- 53).
  by clear -d3B u_E; split_Rabs; lra.
have Od4B : 1 - 1.255 * pow (- 53) < 1 + d4 < 1 + 1.255 * pow (- 53).
  by clear -d4B u_E; split_Rabs; lra.
have Od5B : 1 - 1.505 * pow (- 53) < 1 + d5 < 1 + 1.505 * pow (- 53).
  by clear -d5B u_E; split_Rabs; lra.
have Od6B : 1 - 2 * pow (- 53) < 1 + d6 < 1 + 2 * pow (- 53).
  by clear -d6B u_E; split_Rabs; lra.
have Od7B : 1 - 2 * pow (- 53) < 1 + d7 < 1 + 2 * pow (- 53).
  by clear -d7B u_E; split_Rabs; lra.
have B1Gt : Rabs (0.5 * d0 * d7) < B1.
  by apply: d0d7B.
have B2Gt : Rabs (t5 * P3) <= B2.
  by rewrite /B2 /P3 /t5 /t4; interval with (i_prec 65).
have B3Gt : Rabs (t5 * P4) <= B3.
  by rewrite /B3 /P4 /t5 /t4; interval with (i_prec 65).
have B4Gt : Rabs (t7' * P5) <= B4.
  by rewrite /t7' /t6 /P5 /B4; interval with (i_prec 100).
have B5Gt : Rabs (t7' * P6) <= B5.
  by rewrite /t7' /t6 /P6 /B5; interval with (i_prec 100).
have B6Gt : Rabs (t8 * P7) <= B6.
  by rewrite /t8 /t7 /P7 /B6; interval with (i_prec 100).
have B7Gt : Rabs (t8 * P8) <= B7.
  by rewrite /t8 /t7 /P8 /B7; interval with (i_prec 100).
have BzGe : Rabs nphi <= Bz z.
  rewrite /nphi /Bz /A /B /C.
  clear - B1Gt B2Gt B3Gt B4Gt B5Gt B6Gt B7Gt.
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
    by clear - BzGe; split_Rabs;lra.
  rewrite {1}RPow_abs Rabs_pos_eq; last by clear -BzGe; nra.
  apply: Rmult_le_compat_l; first by clear -BzGe; nra.
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
     (_ :  Bz (33 * pow (-13)) / (8989057312882642 / 9007199254740992) < _); last first.
    rewrite /Bz /Cz /B1 /B2 /B3 /B4 /B5 /B6 /B7 /P3 /P4 /P5 /P6 /P7 /P8.
    by interval.
  rewrite /phi.
  have CzB : 0 < 8989057312882642 / 9007199254740992 <= Cz z.
    rewrite /Bz /Cz /B1 /B2 /B3 /B4 /B5 /B6 /B7 /P3 /P4 /P5 /P6 /P7 /P8.
    split; interval with (i_prec 100).
    apply: Rle_trans (_ : Bz z / Cz z <= _).
    apply: Rmult_le_compat; first apply: Rabs_pos.
    - by apply: Rinv_0_le_compat; lra.
    - by lra.
    by apply: Rinv_le_contravar; lra.
  apply: Rmult_le_compat.
    rewrite /Bz /B1 /B2 /B3 /B4 /B5 /B6 /B7.
    by interval with (i_prec 100).
  - by apply: Rinv_0_le_compat; lra.
  - rewrite /Bz /B1 /B2 /B3 /B4 /B5 /B6 /B7 /P3 /P4 /P5 /P6 /P7 /P8.
    rewrite !pow_Rpower //.
    clear  -zB.
    by do ! apply: Rplus_le_compat; apply: Rmult_le_compat_l; try interval;
       rewrite [in X in _ <= X]Rabs_pos_eq ?pow_Rpower; try interval; try lra;
       apply: pow_incr; split; try lra; apply: Rabs_pos.
  by apply: Rinv_le_contravar; lra.
rewrite Herr in phiB.
have ln1zB : Rabs ((ln (1 + z) - P z) / ln (1 + z)) < Rpower 2 (-72.423).
  apply: P_rel_error; lra.
have HB1 : Rabs ((z + ph + pl) / ln (1 + z) -1) < Rpower 2 (- 67.2756).
  apply: Rle_lt_trans (_ : (1 + Rpower 2 (- 67.31693 )) * 
                           (1 + Rpower 2 (- 72.423)) 
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
split => //.
move=> zB1.
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
      clear -Od0B Od6B d0d6B u_E.
      rewrite u_E in d0d6B *.
      by split_Rabs; nra.
  have t5P3LB2 : Rabs (t5 * P3) <= B2'.
    rewrite /B2' /P3 /t5 /t4.
    have -> : (1 + d0) * (1 + d3) * (1 + d5) * (1 + d6) = 
         (d0d6) * (1 + d3) * (1 + d5) by rewrite /d0d6; lra.
    by interval with (i_prec 100).
  have t5P3LB3 : Rabs (t5 * P4) <= B3'.
    rewrite /B3' /P4 /t5 /t4.
    have -> : (1 + d0) * (1 + d3) * (1 + d5) * (1 + d6) = 
         (d0d6) * (1 + d3) * (1 + d5) by rewrite /d0d6; lra.
    by interval with (i_prec 100).
  have nphiLBz : Rabs nphi <= Bz' z.
    rewrite /nphi /Bz' /A /B /C.
    clear - B1Gt t5P3LB2 t5P3LB3 B4Gt B5Gt B6Gt B7Gt.
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
  (* Here we use the interval tactic to establish this bound 
     in the paper there is a monotony argument *)
  have phiB' : phi < Rpower 2 (- 67.4878).
    apply: Rle_lt_trans 
       (_ :  Bz' (32 * pow (-13)) / Cz (32.1 * pow (-13)) < _); last first.
      rewrite /Bz' /Cz /B1 /B2' /B3' /B4 /B5 /B6 /B7 /P3 /P4 /P5 /P6 /P7 /P8.
      by interval with (i_prec 100).
    rewrite /phi.
    have CzB : 0 < Cz (32.1 * pow (-13)) <= Cz z.
      rewrite /Bz' /Cz /B1 /B2' /B3' /B4 /B5 /B6 /B7 /P3 /P4 /P5 /P6 /P7 /P8.
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
    - rewrite /Bz' /B1 /B2' /B3' /B4 /B5 /B6 /B7 /P3 /P4 /P5 /P6 /P7 /P8.
      rewrite !pow_Rpower //.
      clear  -zB1.
      by do ! apply: Rplus_le_compat; apply: Rmult_le_compat_l; try interval;
       rewrite [in X in _ <= X]Rabs_pos_eq ?pow_Rpower; try interval; try lra;
       apply: pow_incr; split; try lra; apply: Rabs_pos.
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
have vGt : Rpower 2 (- 1.5894) < v.
  apply: Rlt_le_trans (_ : P4 * 33 * pow (-13) + P3 - pow (- 54) <= _).
    by rewrite /P4 /P3; interval.
  rewrite -pow_Rpower // -[bpow _ _]/(pow _) in zB. 
  clear - e3Le zB.
  rewrite /e3 /P4 in e3Le *.
  by split_Rabs; nra.
pose v0 := Rpower 2 (- 1.5894) * (1 - pow (-52)).
have v0Lv' : v0 <= v'.
  apply: Rle_trans (_ : RN v <= _); last first.
    apply: round_le.
    by clear -u'B wh_gt_0; nra.
  rewrite round_generic; last by apply: generic_format_round.
  rewrite /v0.
  apply: Rle_trans (_ :Rpower 2 (-1.5894) <= _); last by lra.
  by interval with (i_prec 100).
pose v1 := Rpower 2 (-1.5805).
have v'Lv1 : v' < v1 by rewrite /v1; lra.
pose sf := (1 - mag beta z)%Z.
have sf_gt0 : (0 <= sf)%Z.
  rewrite /sf -mag_abs.
  suff : (mag beta (Rabs z) <= mag beta 1)%Z by rewrite mag_1; lia.
  apply: mag_le.
  clear -z_neq0; split_Rabs; lra.
  by interval.
pose z1 := z * pow sf.
have z1B : 1 <= Rabs z1 < 2.
  rewrite Rabs_mult [Rabs (pow sf)]Rabs_pos_eq; last by apply: bpow_ge_0.
  suff zBsf : pow (- sf) <= Rabs z < pow (1 - sf).
    have -> : 1 = pow (- sf) * pow sf.
      by rewrite -bpow_plus -(pow0E beta); congr (pow _); lia.
    have -> : 2 = pow (1 - sf) * pow sf.
      rewrite -[2](pow1E beta) -bpow_plus; congr (pow _); lia.
    split.
      apply: Rmult_le_compat_r; first by apply: bpow_ge_0.
      by lra.
    apply: Rmult_lt_compat_r; first by apply: bpow_gt_0.
    by lra.
  split.
    have -> : (- sf = mag beta z - 1)%Z by rewrite /sf; lia.
    by apply: bpow_mag_le; lra.
  have -> : (1 - sf = mag beta z)%Z by rewrite /sf; lia.
  by apply: bpow_mag_gt; lra.
pose wh1 := wh * (pow sf) ^ 2.
have wh1E : wh1 = RN (z1 ^ 2).
  rewrite Rpow_mult_distr -pow2M round_bpow_flt; last first .
    have z2_neq_0 : z ^ 2 <> 0 by clear -z_neq0; nra.
    rewrite /p /emin /emax -/beta.
    have magzzB : (-121 <= mag beta (z ^ 2))%Z.
      by have := is_imul_pow_mag z2_neq_0 imul_zz122; lia.
    have magzGe : (-60 <= mag beta z)%Z.
      have := is_imul_pow_mag z_neq0 Mz; rewrite -/beta; lia.
    by lia.
  by rewrite pow2M /wh1 /wh !pow2_mult.
have d0'E : wh1 = z1 ^ 2 * (1 + d0).
  by rewrite /wh1 d0E /z1; lra. 
pose u1'' := u'' *  (pow sf) ^ 2.
(* 
pose v1' := v' * pow sf.
*)
have d6'E : u1'' = (v' * wh1) * (1 + d6).
  by rewrite /u1'' /wh1 d6E; lra.
have u1''E : u1'' = RN (v' * wh1).
  rewrite /wh1.
  have -> : v' * (wh * pow sf ^ 2) = v' *  wh * (pow (2 * sf)).
    by rewrite pow2M; lra.
  rewrite round_bpow_flt -/beta.
    by rewrite pow2M // /u1'' /u''; lra.
  have v'wh_neq_0 : v' * wh <> 0.
    by clear -wh_gt_0 v'B; nra.
  have imul_v'wh : is_imul (v' * wh) (pow (- 482)).
    have -> : pow (- 482) = pow (- 360) * pow (-122).
      by rewrite -bpow_plus; congr (pow _); lia.
    by apply: is_imul_mul.
  have magv'whGe : (-481 <= mag beta (v' * wh))%Z.
    by have := is_imul_pow_mag v'wh_neq_0 imul_v'wh; lia.
  rewrite /emin /p /emax.
  by lia.
have z12B : 1 <= z1 ^ 2 < 4 by clear -z1B; split_Rabs; nra.
have wh1B : 1 <= wh1 <= 4.
  split.
    have -> : 1 = RN 1.
      rewrite -(pow0E beta) round_generic //.
      by apply: generic_format_FLT_bpow; first by rewrite /emin; lia.
    rewrite wh1E.
    by apply: round_le; lra.
  have -> : 4 = RN (pow 2).
    rewrite round_generic //.
    by apply: generic_format_FLT_bpow; first by rewrite /emin; lia.
  rewrite wh1E.
  apply: round_le.
  have -> : pow 2 = 4 by [].
  by lra.
have v1'wh1B : v' <= v' * wh1 <= 4 * v'.
  suff : 0 <= v' by clear -wh1B; nra.
  by lra.
have Fz1 : format z1 by rewrite /z1; apply: mult_bpow_pos_exact_FLT.
have Faz1 : format (Rabs z1) by apply: generic_format_abs.
have f2 : format 2.
  rewrite -(pow1E beta).
  by apply: generic_format_FLT_bpow; rewrite /emin; lia.
have f4 : format 4.
  rewrite -[4]/(pow 2).
  by apply: generic_format_FLT_bpow; rewrite /emin; lia.
have u_E1 : u_ = / 9007199254740992.
  by rewrite u_E /= /Z.pow_pos /=; lra.
have wh1L4 : wh1 < 4.
  have pred2E : pred beta fexp 2 = 2 - 2 * u_.
    rewrite -[in LHS](pow1E beta) pred_bpow pow1E u_E1.
    by rewrite /Z.pow_pos /=; lra.
  have F2M2 : format (2 - 2 * u_).
    by rewrite -pred2E; apply: generic_format_pred.
  have z1R2M2u : Rabs z1 <= 2 - 2 * u_.
    have L2 : Rabs z1 <= pred beta fexp 2.
      by apply: pred_ge_gt => //; lra.
    by lra.
  have z12B' : z1 ^ 2 <= 4 - 4 * u_.
    have pred4E : pred beta fexp 4 = 4 - 4 * u_.
      rewrite -{1}[4]/(pow 2) pred_bpow [pow 2]/(4).
      rewrite u_E1 /= /Z.pow_pos /IPR /=.
      by lra.
    have F4M4 : format (4 - 4 * u_).
      by rewrite -pred4E; apply: generic_format_pred.
    apply: Rle_trans (_ : 4 - 8 * u_ + 4 * u_^2 <= _); last first.
      by rewrite u_E1; lra.
    have -> : z1 ^ 2 = (Rabs z1) ^ 2 by rewrite pow2_abs.
    have : 0 <= Rabs z1 by apply: Rabs_pos.
    by clear -z1R2M2u; nra.
  have pred4E : pred beta fexp 4 = 4 - 4 * u_.
    rewrite -{1}[4]/(pow 2)  pred_bpow.
    by rewrite u_E1 /= /Z.pow_pos /=; lra.
  have F4M4 : format (4 - 4 * u_).
    by rewrite -pred4E; apply: generic_format_pred.
  apply: Rle_lt_trans (@pred_lt_id beta fexp _ _); last by lra.
  rewrite -(@round_generic beta fexp _ _ (pred beta fexp 4)) //.
    rewrite wh1E.
    apply: round_le.
    by rewrite pred4E; lra.
  by apply: generic_format_pred.
have [wh1_12|wh1_24] : (1 <= wh1 < 2) \/ (2 <= wh1 < 4) by lra.
  have [v'wh_N2N1 | v'wh_N1N0] : (pow (-2) <= v' * wh1 < pow (-1)) \/ 
                                 (pow (-1) <= v' * wh1 < 1).
    suff: pow (-2) <= v' * wh1 < 1 by lra.
      split.
        apply: Rle_trans (_ : v0 * wh1 <= _).
          by rewrite /v0; interval.
        have : 0 <= v0 by rewrite /v0; interval.
        by clear - wh1_12 v0Lv'; nra.
      apply: Rle_lt_trans (_ : v1 * 2 < _).
        have : 0 <= v1 by rewrite /v1; interval.
        have : 0 <= v' by rewrite /v1; interval.        
        by clear - wh1_12 v'Lv1; nra.
      by rewrite /v1; interval.
    suff : Rabs d6 < 1.505 * u_ by lra.
    apply: Rle_lt_trans (_ : u_ / (2 * v0) < _); last first.
      by rewrite u_E1 /v0; interval.
    apply: Rle_trans (_ : 2 * u_ * pow (-2) / (v' * wh1) <= _); last first.
      have -> : 2 * u_ * pow (-2) / (v' * wh1) = u_ / (2 * wh1 * v').
        by rewrite -[pow (-2)]/(/4); field; split; lra.
      apply: Rmult_le_compat_l; first by rewrite u_E1; lra.
      apply: Rinv_le; first by rewrite /v0; interval.
      apply: Rmult_le_compat; try lra.
      by rewrite /v0; interval.
    apply/Rle_div_r; first by lra.
    rewrite -[v' * wh1]Rabs_pos_eq; last by lra.
    rewrite -Rabs_mult.
    have -> : d6 * (v' * wh1) = (v' * wh1) * (1 + d6) - (v' * wh1) by lra.
    rewrite -d6'E u1''E.
    suff <- : ulp (v' * wh1) = 2 * u_ * pow (-2).
      by apply: error_le_ulp.
    rewrite ulp_neq_0; last by lra.
    rewrite /cexp /fexp [in LHS]/=.
    have -> : mag beta (v' * wh1) = (-1)%Z :> Z.
      apply: mag_unique_pos.
      by rewrite [(-1 -1)%Z]/=; lra.
    by rewrite /p /emin u_E1 /= /Z.pow_pos /=; lra.
  suff : Rabs d0 < 1.505 * u_ by lra.
  apply: Rle_lt_trans (_ : 1.34 * u_ < _); last by lra.
  apply: Rle_trans (_ : 4 * u_ * (1 + 2 * u_) * v1 <= _ ); last first.
    by rewrite /v1 u_E1; interval.
  apply: Rle_trans (_ : (2 * u_) * (2 * v') * (1 + 2 * u_) <= _); last first.
    have -> : 2 * u_ * (2 * v') * (1 + 2 * u_) = 4 * u_ * (1 + 2 * u_) * v'.
      by lra.
    apply: Rmult_le_compat_l; first by rewrite u_E1; interval.
    by lra.
  apply: Rle_trans (_ : (2 * u_) / z1 ^ 2 <= _).
    apply/Rle_div_r; first by lra.
    rewrite -[z1 ^ 2]Rabs_pos_eq; last by lra.
    rewrite -Rabs_mult. 
    have -> : d0 * (z1 ^ 2) = (z1 ^ 2) * (1 + d0) - (z1 ^ 2) by lra.
    rewrite -d0'E wh1E.
    suff <- : ulp (z1 ^ 2) = 2 * u_.
      by apply: error_le_ulp.
    rewrite ulp_neq_0; last by lra.
    rewrite /cexp /fexp [in LHS]/=.
    have -> : mag beta (z1 ^ 2) = 1%Z :> Z.
      apply: mag_unique_pos.
      rewrite [(1 -1)%Z]/= pow0E pow1E [IZR beta]/=.
      split; first by lra.
      suff : 2 <= z1 ^ 2 -> 2 <= wh1 by lra.
      move=> z1B'.
      have <- : RN (pow 1) = 2 by rewrite round_generic.
      rewrite wh1E.
      by apply: round_le; rewrite pow1E [IZR beta] /=; lra.
    by rewrite u_E1 /= /Z.pow_pos /=; lra.
  apply/Rle_div_l; first by lra.
  suff : 1 <= (2 * v') * (z1 ^ 2 * (1 + 2 * u_)).
    have : 0 < 2 * u_ by rewrite u_E1; lra.
    by clear; nra.
  apply: Rle_trans (_ : (2 * v') * (z1 ^ 2 * (1 + d0)) <= _); last first.
    apply: Rmult_le_compat_l; first by lra.
    apply: Rmult_le_compat_l; first by lra.
    by lra.
  rewrite -d0'E.
  by rewrite /= /Z.pow_pos /= in v'wh_N1N0; lra.
have [v'wh_N1N1 | v'wh_N1N0] : (pow (-1) <= v' * wh1 < 1) \/ 
                                 (1 <= v' * wh1 < pow 1).
    suff: pow (-1) <= v' * wh1 < pow 1 by lra.
      split.
        apply: Rle_trans (_ : v0 * wh1 <= _).
          by rewrite /v0; interval.
        have : 0 <= v0 by rewrite /v0; interval.
        by clear - wh1_24 v0Lv'; nra.
      apply: Rle_lt_trans (_ : v1 * 4 < _).
        have : 0 <= v1 by rewrite /v1; interval.
        have : 0 <= v' by rewrite /v1; interval.        
        by clear - wh1_24 v'Lv1; nra.
      by rewrite /v1; interval.
    suff : Rabs d6 < 1.505 * u_ by lra.
    apply: Rle_lt_trans (_ : u_ / (2 * v0) < _); last first.
      by rewrite u_E1 /v0; interval.
    apply: Rle_trans (_ : 2 * u_ * pow (-1) / (v' * wh1) <= _); last first.
      have -> : 2 * u_ * pow (-1) / (v' * wh1) = u_ / (wh1 * v').
        by rewrite -[pow (-1)]/(/2); field; split; lra.
      apply: Rmult_le_compat_l; first by rewrite u_E1; lra.
      apply: Rinv_le; first by rewrite /v0; interval.
      apply: Rmult_le_compat; try lra.
      by rewrite /v0; interval.
    apply/Rle_div_r; first by lra.
    rewrite -[v' * wh1]Rabs_pos_eq; last by lra.
    rewrite -Rabs_mult.
    have -> : d6 * (v' * wh1) = (v' * wh1) * (1 + d6) - (v' * wh1) by lra.
    rewrite -d6'E u1''E.
    suff <- : ulp (v' * wh1) = 2 * u_ * pow (-1).
      by apply: error_le_ulp.
    rewrite ulp_neq_0; last by lra.
    rewrite /cexp /fexp [in LHS]/=.
    have -> : mag beta (v' * wh1) = 0%Z :> Z.
      apply: mag_unique_pos.
      by rewrite [(0 -1)%Z]/= pow0E; lra.
    by rewrite /p /emin u_E1 /= /Z.pow_pos /=; lra.
suff : Rabs d0 < 1.505 * u_ by lra.
have [z1B'|z1B'] : 
  (z1 ^ 2 <= pred beta fexp 2) \/ (pred beta fexp 2 <= z1 ^ 2) by lra.
  suff : wh1 < 2 by lra.
  apply: Rle_lt_trans (@pred_lt_id beta fexp _ _); last by lra.
  rewrite -[X in _ <= X](@round_generic beta fexp rnd) //.
    by rewrite wh1E; apply: round_le; lra.
  by apply: generic_format_pred.
have [z1B''|z1B''] : (z1 ^ 2 <= 2) \/ (2 <= z1 ^ 2) by lra.
  have wh1L2 : wh1 <= 2.
    rewrite -[X in _ <= X](@round_generic beta fexp rnd) //.
    by rewrite wh1E; apply: round_le; lra.
  have wh1_eq2 : wh1 = 2 by lra.
  have -> : d0 = 2 / z1 ^ 2 - 1.
    rewrite -wh1_eq2 d0'E; field.
    move=> z1IE; rewrite z1IE pow_ne_zero in z12B; last by lia.
    by lra.
  have pred2E : pred beta fexp 2 = 2 - 2 * u_.
    rewrite -[in LHS](pow1E beta) pred_bpow pow1E u_E1.
    by rewrite /Z.pow_pos /=; lra.
  rewrite pred2E in z1B'.
  set xx := z1 ^ 2 in z1B' z1B'' *.
  rewrite u_E1 in z1B' z1B'' *.
  by interval with (i_prec 100).
apply: Rle_lt_trans (_ : 1.34 * u_ < _); last by lra.
apply: Rle_trans (_ : 4 * u_ * (1 + 2 * u_) * v1 <= _ ); last first.
  by rewrite /v1 u_E1; interval.
apply: Rle_trans (_ : (2 * u_) * (2 * v') * (1 + 2 * u_) <= _); last first.
  have -> : 2 * u_ * (2 * v') * (1 + 2 * u_) = 4 * u_ * (1 + 2 * u_) * v'.
    by lra.
  apply: Rmult_le_compat_l; first by rewrite u_E1; interval.
  by lra.
apply: Rle_trans (_ : (4 * u_) / z1 ^ 2 <= _).
  apply/Rle_div_r; first by lra.
  rewrite -[z1 ^ 2]Rabs_pos_eq; last by lra.
  rewrite -Rabs_mult. 
  have -> : d0 * (z1 ^ 2) = (z1 ^ 2) * (1 + d0) - (z1 ^ 2) by lra.
  rewrite -d0'E wh1E.
  suff <- : ulp (z1 ^ 2) = 4 * u_.
    by apply: error_le_ulp.
  rewrite ulp_neq_0; last by lra.
  rewrite /cexp /fexp [in LHS]/=.
  have -> : mag beta (z1 ^ 2) = 2%Z :> Z.
    apply: mag_unique_pos.
    rewrite -[pow (2 - 1)]/2 -[pow 2]/4.
    by lra.
  by rewrite /= u_E1 /Z.pow_pos /=; lra.
apply/Rle_div_l; first by lra.
  suff : 1 <=  v' * (z1 ^ 2 * (1 + 2 * u_)).
  have : 0 < u_ by rewrite u_E1; lra.
  by clear; nra.
apply: Rle_trans (_ : v' * (z1 ^ 2 * (1 + d0)) <= _); last first.
  apply: Rmult_le_compat_l; first by lra.
  apply: Rmult_le_compat_l; first by lra.
  by lra.
rewrite -d0'E.
by rewrite /= /Z.pow_pos /= in v'wh_N1N0; lra.
Qed.

Lemma imul_ph_p1 z :
  format z -> 
  Rabs z <= 33 * Rpower 2 (-13) ->
  is_imul z (Rpower 2 (-61)) ->
  let: DWR ph pl := p1 z in 
  is_imul ph (pow (- 123)).
Proof.
move=> Fz zB Mz.
by have [_ _ [H _] _] := absolute_rel_error_main Fz zB Mz.
Qed.

Lemma ph_bound_p1 z :
  format z -> 
  Rabs z <= 33 * Rpower 2 (-13) ->
  is_imul z (Rpower 2 (-61)) ->
  let: DWR ph pl := p1 z in 
  Rabs ph < Rpower 2 (-16.9).
Proof.
move=> Fz zB Mz.
by have [_ _ [_ H] _] := absolute_rel_error_main Fz zB Mz.
Qed.

Lemma imul_pl_p1 z :
  format z -> 
  Rabs z <= 33 * Rpower 2 (-13) ->
  is_imul z (Rpower 2 (-61)) ->
  let: DWR ph pl := p1 z in 
  is_imul pl (pow (- 543)).
Proof.
move=> Fz zB Mz.
by have [_ _ _ [H _]] := absolute_rel_error_main Fz zB Mz.
Qed.

Lemma pl_bound_p1 z :
  format z -> 
  Rabs z <= 33 * Rpower 2 (-13) ->
  is_imul z (Rpower 2 (-61)) ->
  let: DWR ph pl := p1 z in 
  Rabs pl < Rpower 2 (-25.446).
Proof.
move=> Fz zB Mz.
by have [_ _ _ [_ H]] := absolute_rel_error_main Fz zB Mz.
Qed.

Lemma absolute_error_p1 z :
  format z -> 
  Rabs z <= 33 * Rpower 2 (-13) ->
  is_imul z (Rpower 2 (-61)) ->
  let: DWR ph pl := p1 z in 
  Rabs((ph + pl) - (ln (1 + z) - z)) < Rpower 2 (-75.492).
Proof.
move=> Fz zB Mz.
by have [H _ _ _] := absolute_rel_error_main Fz zB Mz.
Qed.

Lemma rel_error_p1 z :
  z <> 0 ->  
  format z -> 
  Rabs z <= 33 * Rpower 2 (-13) ->
  is_imul z (Rpower 2 (-61)) ->
  let: DWR ph pl := p1 z in 
  Rabs ((z + ph + pl) / ln (1 + z) -1) < Rpower 2 (- 67.2756).
Proof.
move=> z_neq0 Fz zB Mz.
have [_ H _ _] := absolute_rel_error_main Fz zB Mz.
by have [H1 _] := H z_neq0.
Qed.

Lemma rel_error_32_p1 z :
  z <> 0 ->  
  format z -> 
  Rabs z < 32 * Rpower 2 (-13) ->
  is_imul z (Rpower 2 (-61)) ->
  let: DWR ph pl := p1 z in 
  Rabs ((z + ph + pl) / ln (1 + z) -1) < Rpower 2 (- 67.441).
Proof.
move=> z_neq0 Fz zB Mz.
have zB1 : Rabs z <= 33 * Rpower 2 (-13) by interval.
have [_ H _ _] := absolute_rel_error_main Fz zB1 Mz.
have [_ H1] := H z_neq0.
by apply: H1.
Qed.

End algoP1.

