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

Section Prelim.

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
have sE : succ radix2 fexp 1 = 1 + pow (-52).
  rewrite /succ /=.
  (case: Rle_bool_spec; try lra) => _.
  by rewrite ulp_neq_0 //= /Generic_fmt.cexp mag_1 /fexp.
apply: Rle_trans (_ : ln (succ radix2 fexp 1) <= _).
  rewrite sE.
  by interval with (i_prec 54).
apply: ln_le; last by apply: succ_le_lt => //; apply: format1.
suff : 0 < pow (- 52) by rewrite sE; lra.
by apply: bpow_gt_0.
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
have sE : pred radix2 fexp 1 = 1 - pow (-53).
  rewrite /pred /= /succ.
  (case: Rle_bool_spec; try lra) => _.
  have -> : (- - (1) = 1)%R by lra.
  rewrite /pred_pos mag_1 /=.
  by case: Req_bool_spec; lra.
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

Local Notation ulp := (ulp beta fexp).

Coercion F2R : float >-> R.

Inductive dwR := DWR (xh : R) (xl : R).

Definition formatDw (d : dwR) :=
  let: (DWR xh xl) := d in 
  [/\ format xh, format xl & RN (xh + xl) = xh].

Definition exactMul (a b : R) : dwR := 
  let h := RN (a * b) in 
  let l := RN (a * b - h) in DWR h l.
  
Lemma exactMul0l b : exactMul 0 b = DWR 0 0.
Proof. by rewrite /exactMul !(Rsimp01, round_0). Qed.

Lemma exactMul0r a : exactMul a 0 = DWR 0 0.
Proof. by rewrite /exactMul !(Rsimp01, round_0). Qed.

Lemma exactMul_correct (a b : R) :
  format a -> format b -> is_imul (a * b) (pow emin) ->
  let: DWR h l := exactMul a b in h + l = a * b.
Proof.
move=> Fa Fb Mab /=.
rewrite -Ropp_minus_distr round_opp.
rewrite [X in -X]round_generic //; first by lra.
by apply: format_err_mul.
Qed.

Lemma format_exactMul (a b : float) : 
  format a -> format b -> is_imul (a * b) (pow emin) -> formatDw (exactMul a b).
Proof. 
move=> Fa Fb Mab /=; split; try by apply: generic_format_round.
by rewrite exactMul_correct.
Qed.

Definition fastTwoSum (a b : R) :=
  let s := RN (a + b) in
  let z := RN (s - a) in DWR s (RN (b - z)).

Definition twoSum (a : R) (b : dwR) :=  
  let: DWR bh bl := b in 
  let: DWR h t := fastTwoSum a bh in 
  let: l := RN (t + bl) in DWR h l.

Check twoSum.

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

Lemma pow_Rpower z : pow z = Rpower 2 (IZR z).
Proof. by rewrite bpow_powerRZ powerRZ_Rpower //; apply: IZR_lt. Qed.

Lemma powN1 : pow (-1) = 0.5.
Proof. by rewrite /= /Z.pow_pos /=; lra. Qed.

Theorem cexp_bpow_flt  x e (xne0: x <> R0)
           (emin_le : (emin <= Z.min (mag beta x + e - p) (mag beta x - p))%Z) :
           cexp (x * pow e) = (cexp x + e)%Z.
Proof. 
rewrite /cexp mag_mult_bpow //.
rewrite /fexp.
rewrite !Z.max_l ; first ring.
apply:(Z.min_glb_r (mag beta x + e - p) )=>//.
apply:(Z.min_glb_l _  (mag beta x - p) )=>//.
Qed.

Theorem mant_bpow_flt x e (emin_le: (emin <= Z.min (mag beta x + e - p)
                          (mag beta x - p))%Z) : mant (x * pow e) = mant x.
Proof.
case: (Req_dec x 0) => [->|Zx]; first by rewrite Rmult_0_l.
rewrite /scaled_mantissa /cexp /fexp.
rewrite mag_mult_bpow //.
rewrite !Rmult_assoc.
apply: Rmult_eq_compat_l.
rewrite -bpow_plus.
congr bpow.
rewrite !Z.max_l ; first ring.
apply:(Z.min_glb_r (mag beta x + e - p) )=>//.
apply:(Z.min_glb_l _  (mag beta x - p) )=>//.
Qed.

Theorem round_bpow_flt  x e (emin_le: (emin <= Z.min (mag beta x + e - p)
    (mag beta x - p))%Z) :
    RN  (x * pow e) = (RN x * pow e)%R.
Proof.
case: (Req_dec x 0) => [->|Zx] ; first by rewrite Rmult_0_l round_0 Rmult_0_l.
by rewrite /round /F2R /= mant_bpow_flt //  cexp_bpow_flt // bpow_plus
Rmult_assoc.
Qed.

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

Lemma is_imul_format_round_ge_0 x y : 
  0 <= x -> is_imul x (pow y) -> (emin <= y)%Z -> 0 <= RN x.
Proof.
move=> x_ge_0 Mx eminpLy.
have [->|x_gt_0] := Req_dec x 0; first by rewrite round_0; lra.
by apply: Rlt_le; apply: is_imul_format_round_gt_0 Mx _ => //; lra.
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
  (emin <= y)%Z -> is_imul x (pow y) -> (x = 0 -> eps = 0) ->
  RN x = x * (1 + eps) -> Rabs eps < 2 * u.
Proof.
move=> eLy Mxy Heps HRN.
have [x_eq0|x_neq0] := Req_dec x 0.
  rewrite Heps // Rabs_R0.
  by have := u_gt_0; lra.
have [eps1 [Heps1 H1eps1]] := relative_error_is_min_eps eLy Mxy.
by have <- : eps1 = eps by nra.
Qed.

End Prelim.

