Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error Plus_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore Fast2Sum_robust_flt.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Prelim.

Variable beta : radix.
Variables emin p : Z.
Hypothesis Hp2: Z.lt 1 p.

Let p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Defined.

Variable rnd : R -> Z.
Hypothesis valid_rnd : Valid_rnd rnd.

Variable fexp : Z -> Z.
Hypothesis valid_fexp : Valid_exp fexp.

Local Notation format := (generic_format beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation cexp := (cexp beta fexp).
Local Notation pow e := (bpow beta e).

Lemma round_le_l x y : format x -> x <= y -> x <= RND y.
Proof.
move=> xF xLy.
have <- : RND x = x by apply: round_generic.
by apply: round_le.
Qed.

Lemma round_le_r x y : format y -> x <= y -> RND x <= y.
Proof.
move=> yF xLy.
have <- : RND y = y by apply: round_generic.
by apply: round_le.
Qed.

Lemma Rabs_round_le_l f x : format f -> f <= Rabs x -> f <= Rabs (RND x).
Proof.
move=> fF.
have [x_pos|x_neg] := Rle_lt_dec 0 x.
  rewrite !Rabs_pos_eq //; last first.
    by apply : round_le_l => //; apply: generic_format_0.
  by apply: round_le_l.
rewrite !Rabs_left1; try lra; last first.
  by apply : round_le_r; [apply: generic_format_0 | lra].
suff : x <= - f -> RND x <= - f by lra.
by apply/round_le_r/generic_format_opp.
Qed.

Lemma Rabs_round_le_r f x : format f -> Rabs x <= f -> Rabs (RND x) <= f.
Proof.
move=> eLm.
have [x_pos|x_neg] := Rle_lt_dec 0 x.
  rewrite !Rabs_pos_eq //; last first.
    by apply : round_le_l => //; apply: generic_format_0.
  by apply: round_le_r.
rewrite !Rabs_left1; try lra; last first.
  by apply : round_le_r; [apply: generic_format_0 | lra].
suff : - f <= x ->  - f <= RND x by lra.
by apply/round_le_l/generic_format_opp.
Qed.

Local Notation ulp := (ulp beta fexp).

Lemma format_pos_le_ex_add_ulp f1 f2 :
  Monotone_exp fexp -> format f1 -> format f2 -> 0 < f1 <= f2 ->
  exists k, f2 = f1 + IZR k * ulp f1.
Proof.
move=> Mfexp Hf1 Hf2 f1Lf2.
red in Hf1.
have cf1Lcf2 : (cexp f1 <= cexp f2)%Z.
  have [cf2Lcf1|//] := Z_lt_le_dec (cexp f2) (cexp f1).
  suff : f2 < f1 by lra.
  by apply: lt_cexp_pos cf2Lcf1 => //; lra.
rewrite ulp_neq_0; last by lra.
rewrite {1}Hf1 {1}Hf2 /F2R /=.
set x1 := Ztrunc _; set x2 := Ztrunc _.
exists (x1 * beta ^ (cexp f2 - cexp f1) - x2)%Z.
rewrite minus_IZR mult_IZR IZR_Zpower; last by lia.
rewrite Rmult_minus_distr_r Rmult_assoc -bpow_plus -[bpow _ _]/(pow _).
rewrite -[bpow _ (cexp f1)]/(pow _).
rewrite -[bpow _ (_ + _)]/(pow _).
have -> : (cexp f2 - cexp f1 + cexp f1 = cexp f2)%Z by lia.
by lra.
Qed.

Local Notation R_UP := (round beta fexp Zceil).

Lemma round_up_lt x1 y1 : x1 < y1 -> x1 < R_UP y1.
Proof.
move=> x1Ly1.
apply: Rlt_le_trans x1Ly1 _.
case:(@round_DN_UP_le beta y1 fexp);lra.
Qed.

Local Notation R_DN := (round beta fexp Zfloor).

Lemma round_down_gt x1 y1 : x1 < y1 -> R_DN x1 < y1.
Proof.
move=> x1Ly1.
apply: Rle_lt_trans _ x1Ly1.
case:(@round_DN_UP_le beta  x1 fexp);lra.
Qed.

End Prelim.

Section FltPrelim.

Variable beta : radix.
Variables emin p : Z.
Hypothesis Hp2: Z.lt 1 p.
Hypothesis emin_neg : (emin < - p - 1)%Z.

Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Variable rnd : R -> Z.
Hypothesis valid_rnd : Valid_rnd rnd.

Local Notation FLT := (FLT_exp emin p).
Local Notation format := (generic_format beta FLT).
Local Notation RND := (round beta FLT rnd).
Local Notation pow e := (bpow beta e).
Local Notation float := (float beta).
Local Notation cexp := (cexp beta FLT).
Local Notation mant := (scaled_mantissa beta FLT).

Lemma format1_FLT : format 1.
Proof.
have -> : 1 = F2R (Float beta 1 0) by rewrite /F2R /=; lra.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; last by lia.
have -> : (1 = beta ^ 0)%Z by [].
by apply: Zpower_lt; lia. 
Qed.

Lemma pow_Rpower z : pow z = Rpower (IZR beta) (IZR z).
Proof. 
rewrite bpow_powerRZ powerRZ_Rpower //.
apply: IZR_lt.
apply: radix_gt_0.
Qed.

Lemma Rabs_round_ge_bpow x e :
  (emin <= e)%Z -> pow e <= Rabs x -> pow e <= Rabs (RND x).
Proof.
move=> eLm eLx.
by apply/Rabs_round_le_l => //; apply: generic_format_FLT_bpow.
Qed.

Lemma Rabs_round_le_bpow x e : 
  (emin <= e)%Z -> Rabs x <= pow e -> Rabs (RND x) <= pow e.
Proof.
move=> eLm eLx.
by apply/Rabs_round_le_r => //; apply: generic_format_FLT_bpow.
Qed.

Lemma relative_error_FLT_alt x : 
  pow (emin + p - 1) <= Rabs x -> Rabs (RND x) < Rabs x * (1 + pow (1 - p)).
Proof.
move=> pLx.
suff : Rabs (RND x - x) < pow (- p + 1) * Rabs x.
  have -> : (1 - p = -p + 1)%Z by lia.
  by split_Rabs; lra.
by apply: relative_error_FLT => //; apply: p_gt_0.
Qed.

Let alpha := pow emin.

Lemma alphaF : format alpha.
Proof. by apply: generic_format_bpow; rewrite /FLT; lia. Qed.

Lemma alpha_gt_0 : 0 < alpha.
Proof.
rewrite /alpha !bpow_powerRZ !powerRZ_Rpower; last by apply/IZR_lt/radix_gt_0.
by apply: exp_pos.
Qed.

Lemma alpha_lB x (Fx : format x) (xneq0 : x <> 0) : alpha <= Rabs x.
Proof.
move: Fx; rewrite /generic_format /F2R /= /cexp.
set mx := Ztrunc _=> xE.
have mx_neq0: (mx <> 0)%Z by move => mx0 ; apply xneq0; rewrite xE mx0; lra.
apply: Rle_trans  (_ : pow (FLT (mag beta x)) <= _).
  by rewrite /alpha /FLT; apply/bpow_le; lia.
rewrite [X in _ <= Rabs X]xE.
rewrite Rabs_mult -[X in X <= _]Rmult_1_l.
apply: Rmult_le_compat; first by lra.
- by apply: bpow_ge_0. 
- by rewrite -abs_IZR; apply/IZR_le; lia.
by rewrite Rabs_pos_eq; [lra | apply: bpow_ge_0].
Qed.

Lemma alpha_LB x : format x -> 0 < x -> alpha <= x.
Proof.
move=> fX xP.
suff : alpha <= Rabs x by split_Rabs; lra.
by apply: alpha_lB => //; lra.
Qed.

(* Some sanity check *)
Let emax := (3 - emin - p)%Z.

Let omega := (1 - pow (- p)) * pow emax.
Let omegaF : float := Float _ (beta ^ p - 1) (emax - p).

Lemma omegaFE : F2R omegaF = omega.
Proof.
rewrite /omega /omegaF /F2R /= minus_IZR IZR_Zpower; last by lia.
rewrite Rmult_minus_distr_r -bpow_plus Rsimp01.
have -> : (p + (emax - p) = emax)%Z by lia.
by rewrite [pow (emax - _)]bpow_plus; lra.
Qed.

Lemma omega_gt_alpha : alpha < omega.
Proof.
rewrite /omega /alpha /emax.
have {1}-> : emin = ((2 * emin - 3 + p) + (3 - emin - p))%Z by lia.
rewrite bpow_plus.
apply: Rmult_lt_compat_r; first by apply: bpow_gt_0.
apply: Rlt_le_trans (_ : pow (2 * (- p - 1) - 3 + p) <= _).
  by apply: bpow_lt; first by lia.
have -> : (2 * (- p - 1) - 3 + p = - p - 5)%Z by lia.
suff : pow (- p) + pow (- p - 5) <= 1 by lra.
rewrite bpow_plus.
have -> : pow (- p) + pow (- p) * pow (- (5)) = pow (- p) * (1 + pow (- (5))).
  by lra.
have {2}-> : 1 = pow (- p) * pow p.
  rewrite -bpow_plus; have -> : (- p + p = 0)%Z by lia.
  by [].
apply: Rmult_le_compat_l; first by apply: bpow_ge_0.
apply: Rle_trans (_ : pow 1 <= _); last by apply: bpow_le; lia.
have -> : pow 1 = IZR beta by rewrite bpow_1.
apply: Rle_trans (_ : 2 <= _).
  have : pow (- (5)) <= pow 0 by apply: bpow_le.
  have -> : pow 0 = 1 by [].
  by lra.
apply/IZR_le.
by have := radix_gt_1 beta; lia.
Qed.

Lemma omega_gt_0 : 0 < omega.
Proof. by apply: Rlt_trans alpha_gt_0 omega_gt_alpha. Qed.

Lemma format_omega : format omega.
Proof.
rewrite -omegaFE.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=.
  rewrite Z.abs_eq; first lia.
  have : (beta ^ 0 <= beta ^ p)%Z by apply: Zpower_le; lia.
  by rewrite /=; lia.
by rewrite /emax; lia.
Qed.

Local Notation ulp := (ulp beta FLT).

Lemma ulp_subnormal f : Rabs f < pow (emin + p) -> ulp f = pow emin.
Proof.
  move=> fB.
have [->|f_neq0]:= Req_dec f 0; first by rewrite ulp_FLT_0.
rewrite ulp_neq_0; last by lra.
rewrite /cexp /FLT Z.max_r //.
suff : (mag beta f <= emin + p)%Z by lia.
apply: mag_le_bpow; first by lra.
by lra.
Qed.

Lemma ulp_norm f : pow (emin + p) <= Rabs f -> ulp f = pow (mag beta f - p).
Proof.
move=> fB.
have f_neq_0 : f <> 0.
  suff : 0 < Rabs f by split_Rabs; lra.
  suff : 0 < pow (emin + p) by lra.
  by apply: bpow_gt_0.
rewrite ulp_neq_0; last by lra.
rewrite /cexp /FLT Z.max_l //.
suff : (emin + p <= mag beta f)%Z by lia.
apply: mag_ge_bpow.
apply: Rle_trans fB.
apply: bpow_le; lia.
Qed.

Lemma ulp_omega : ulp omega = pow (emax - p).
Proof.
have beta_ge_2 : 2 <= IZR beta.
  by apply/IZR_le; have := radix_gt_1 beta; lia.
rewrite ulp_neq_0; last by have := omega_gt_0; lra.
congr (pow _); rewrite /cexp /FLT.
rewrite (mag_unique_pos beta _ emax); first lia.
split; rewrite /omega.
  have -> : (1 - pow (- p)) * pow emax = 
            (IZR beta * (1 - pow (- p))) * pow (emax - 1).
    have -> : pow emax = pow 1 * pow (emax - 1).
      by rewrite -bpow_plus; congr (pow _); lia.
    rewrite -Rmult_assoc; congr (_ * _).
    by rewrite pow1E; lra.
  rewrite -{1}[pow (_ - 1)]Rmult_1_l; apply: Rmult_le_compat_r.
    by apply: bpow_ge_0.
  apply: Rle_trans (_ : IZR beta * (1 - pow (- 1)) <= _).
    suff -> : IZR beta * (1 - pow (- 1)) = IZR beta - 1 by lra.
    have -> : pow (-1) = / IZR beta by rewrite /= /Z.pow_pos /= Zmult_1_r.
    by field; lra.
  apply: Rmult_le_compat_l; first by lra.
  suff : pow (- p) <= pow (- 1) by lra.
  apply: bpow_le; lia.
rewrite -{2}[pow emax]Rmult_1_l; apply: Rmult_lt_compat_r.
  by apply: bpow_gt_0.
suff : 0 < pow (- p) by lra.
by apply: bpow_gt_0.
Qed.

Lemma succ_bpow_FLT (e : Z) : 
 (emin <= e + 1 - p)%Z -> succ beta FLT (pow e) = pow e + pow (e + 1 - p).
Proof.
move=> eminB.
rewrite succ_eq_pos; last by apply: bpow_ge_0.
rewrite ulp_bpow.
have -> : (FLT (e + 1) = e + 1 - p)%Z by rewrite /FLT; lia.
by [].
Qed.

Lemma relative_error_eps_le x :
  is_imul x (pow (emin + p - 1)) ->
  Rabs x * (1 - pow (- p + 1)) <=  Rabs (RND x).
Proof.
move=> xB.
have [->|x_neq0] := Req_dec x 0; first by rewrite !(round_0, Rsimp01); lra.
have F1 :  Rabs (RND x - x) < pow (- p + 1) * Rabs x.
  apply: relative_error_FLT => //; first by lia.
  by apply: is_imul_pow_le_abs.
by split_Rabs; nra.
Qed.

Lemma relative_error_eps_ge x :
  is_imul x  (pow (emin + p - 1)) ->
  Rabs (RND x) <= Rabs x * (1 + pow (- p + 1)).
Proof.
move=> xB.
have [->|x_neq0] := Req_dec x 0; first by rewrite !(round_0, Rsimp01); lra.
have F1 :  Rabs (RND x - x) < pow (- p + 1) * Rabs x.
  apply: relative_error_FLT => //; first by lia.
  by apply: is_imul_pow_le_abs.
by split_Rabs; nra.
Qed.

Lemma is_imul_bound_pow_format e x :
  pow e <= Rabs x -> format x -> is_imul x (pow (e - p + 1)).
Proof.
move=> eLx x_F.
have [->|x_neq0] := Req_dec x 0;  first by exists 0%Z; lra.
apply/(is_imul_format_mag_pow x_F)=>//.
apply/(Z.le_trans _ (mag beta x - p)%Z); last by  (rewrite /FLT; lia).
suff: (e + 1 <= mag beta x )%Z by lia.
apply/mag_ge_bpow.
by have->: (e + 1 -1 = e)%Z by lia.
Qed.

Theorem cexp_bpow_FLT  x e (xne0: x <> R0)
           (emin_le : (emin <= Z.min (mag beta x + e - p) (mag beta x - p))%Z) :
           cexp (x * pow e) = (cexp x + e)%Z.
Proof. 
rewrite /cexp mag_mult_bpow //.
rewrite /FLT.
rewrite !Z.max_l ; first ring.
apply:(Z.min_glb_r (mag beta x + e - p) )=>//.
apply:(Z.min_glb_l _  (mag beta x - p) )=>//.
Qed.

Theorem mant_bpow_FLT x e (emin_le: (emin <= Z.min (mag beta x + e - p)
                          (mag beta x - p))%Z) : mant (x * pow e) = mant x.
Proof.
case: (Req_dec x 0) => [->|Zx]; first by rewrite Rmult_0_l.
rewrite /scaled_mantissa /cexp /FLT.
rewrite mag_mult_bpow //.
rewrite !Rmult_assoc.
apply: Rmult_eq_compat_l.
rewrite -bpow_plus.
congr bpow.
rewrite !Z.max_l ; first ring.
apply:(Z.min_glb_r (mag beta x + e - p) )=>//.
apply:(Z.min_glb_l _  (mag beta x - p) )=>//.
Qed.

Theorem round_bpow_FLT x e (emin_le: (emin <= Z.min (mag beta x + e - p)
    (mag beta x - p))%Z) :
    RND (x * pow e) = (RND x * pow e)%R.
Proof.
case: (Req_dec x 0) => [->|Zx] ; first by rewrite Rmult_0_l round_0 Rmult_0_l.
by rewrite /round /F2R /= mant_bpow_FLT // 
           cexp_bpow_FLT // bpow_plus Rmult_assoc.
Qed.

(* This proof should be reworked *)
Lemma imul_format z e b : 
  (emin <= e)%Z -> is_imul z (pow e) -> Rabs z <= b -> b <= (pow (p + e))
  -> format z.
Proof.
move=> emLe [k ->] zB bB.
have {b zB bB}zLp : Rabs (IZR k * pow e) <= pow (p + e) by lra.
have {}zLp : Rabs (IZR k) <= pow p.
  apply: (Rmult_le_reg_r (pow e)); first by apply: bpow_gt_0.
  rewrite -bpow_plus -[pow e]Rabs_pos_eq; first by rewrite -Rabs_mult.
  by apply: bpow_ge_0.
have [E|D] := Req_dec (Rabs (IZR k)) (pow p).
  have[->|->] : IZR k = pow p \/ IZR k = - pow p by split_Rabs; lra.
    by rewrite -bpow_plus; apply: generic_format_FLT_bpow; lia.
  rewrite -Ropp_mult_distr_l; apply: generic_format_opp.
  by rewrite -bpow_plus; apply: generic_format_FLT_bpow; lia.
have -> : IZR k * pow e = Float beta k e by [].
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => //=.
apply/lt_IZR.
by rewrite abs_IZR IZR_Zpower; [lra|lia].
Qed.

Lemma is_imul_format_round_gt_0 x y : 
  0 < x -> is_imul x (pow y) -> (emin <= y)%Z -> 0 < RND x.
Proof.
move=> x_gt_0 Mx eminpLy.
pose f := Float beta 1 emin.
have Ff : format (Float beta 1 emin).
  apply: generic_format_FLT.
  apply: FLT_spec (refl_equal _) _ _ => //=; last by lia.
  have -> : (1 = beta ^ 0)%Z by [].
  by apply: Zpower_lt; lia.
apply: Rlt_le_trans alpha_gt_0 _.
apply: round_le_l; first by apply: alphaF.
apply: Rle_trans (_ : pow y <= _); first by apply: bpow_le; lia.
have [k kE] := Mx; rewrite kE in x_gt_0 *.
have F2 : 0 < pow y by apply: bpow_gt_0.
have F3 : (0 < k)%Z by apply: lt_IZR; nra.
have/IZR_le : (1 <= k)%Z by lia.
nra.
Qed.

Lemma is_imul_format_round_ge_0 x y : 
  0 <= x -> is_imul x (pow y) -> (emin <= y)%Z -> 0 <= RND x.
Proof.
move=> x_ge_0 Mx eminpLy.
have [->|x_gt_0] := Req_dec x 0; first by rewrite round_0; lra.
by apply: Rlt_le; apply: is_imul_format_round_gt_0 Mx _ => //; lra.
Qed.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).

Lemma relative_error_is_min_eps x y :
  (emin <= y)%Z -> is_imul x (pow y) ->
  exists eps : R, Rabs eps < 2 * u /\ RND x = x * (1 + eps).
Proof.
move=> eLy [z ->].
pose x1 := Float beta (z * beta ^ (y - emin))%Z emin.
have <- : F2R x1 = IZR z * pow y.
  rewrite /F2R mult_IZR IZR_Zpower; last by lia.
  rewrite Rmult_assoc -bpow_plus [Fexp _]/=.
  congr (_ * pow _); lia.
have -> : 2 * u = pow (- p + 1).
  have -> : (- p + 1 = 1 - p)%Z by lia.
  by rewrite /u; lra.
by apply: relative_error_FLT_F2R_emin_ex; lia.
Qed.

Lemma relative_error_is_min_eps_bound x y eps :
  (emin <= y)%Z -> is_imul x (pow y) -> (x = 0 -> eps = 0) ->
  RND x = x * (1 + eps) -> Rabs eps < 2 * u.
Proof.
move=> eLy Mxy Heps HRN.
have [x_eq0|x_neq0] := Req_dec x 0.
  rewrite Heps // Rabs_R0.
  by have := u_gt_0; lra.
have [eps1 [Heps1 H1eps1]] := relative_error_is_min_eps eLy Mxy.
by have <- : eps1 = eps by nra.
Qed.


Inductive dwR := DWR (xh : R) (xl : R).

Definition formatDw (d : dwR) :=
  let: (DWR xh xl) := d in 
  [/\ format xh, format xl & RND (xh + xl) = xh].

Definition exactMul (a b : R) : dwR := 
  let h := RND (a * b) in 
  let l := RND (a * b - h) in DWR h l.
  
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

(* Lemma 0 *)
Lemma error_exactMul a b (Fa : format a) (Fb : format b) :
 let: DWR h l := exactMul a b in Rabs (h + l - (a * b)) < alpha.
Proof.
rewrite /=.
have alphaE : alpha = pow emin by []. 
have alpha_pos : 0 < alpha  by apply/bpow_gt_0.
case:(Rle_lt_dec (pow (emin + 2 * p - 1))  (Rabs (a * b))) => abB.
  set h := RND (a * b).
  rewrite round_generic; last first.
    have->: a * b - h = - (RND (a * b) - (a * b)) by rewrite /h; lra.
    by apply/generic_format_opp/mult_error_FLT.
  by rewrite Rabs_0; lra.
case: (Req_dec a 0) => [->|aneq_0].
  rewrite !(Rsimp01 , round_0); apply/bpow_gt_0.
case: (Req_dec b 0) => [->|bneq_0].
  rewrite !(Rsimp01 , round_0); apply/bpow_gt_0.
have abn0: a * b <>  0 by nra.
set h := RND _.
set l' := a * b - h.
case:(Req_dec l' 0)=>[l'0|l'neq_0].
  rewrite l'0  ; rewrite /l' in l'0.
  by rewrite !(Rsimp01 , round_0) Rabs_0; lra.
have -> :  h + RND l' - a * b = RND l' - l' by rewrite /l'; lra.
apply/(Rlt_le_trans _ (ulp (l'))); first by apply/error_lt_ulp. 
have: Rabs l' < ulp (a * b).
  by rewrite /l' -(Rabs_Ropp) Ropp_minus_distr; apply/error_lt_ulp.
have:  ulp (a * b) <= ulp (pow (emin + 2 * p - 1)).
  apply/ulp_le.
  rewrite (Rabs_pos_eq (pow _)); try lra.
  by apply/bpow_ge_0.
rewrite ulp_bpow {2}/FLT Z.max_l; last lia.
have -> : (emin + 2 * p - 1 + 1 - p = emin + p)%Z by lia.
move=> *.
have l'B: Rabs l' <  pow (emin + p) by lra.
by rewrite ulp_FLT_small; lra.
Qed.

Definition fastTwoSum (a b : R) :=
  let s := RND (a + b) in
  let z := RND (s - a) in DWR s (RND (b - z)).

Lemma fastTwoSum_0 : fastTwoSum 0 0 = DWR 0 0.
Proof. by rewrite /fastTwoSum !(Rsimp01, round_0). Qed. 


Lemma fastTwoSum_0l f : format f -> fastTwoSum 0 f = DWR f 0.
Proof.
move=> Ff; rewrite /fastTwoSum !Rsimp01 round_generic //.
by rewrite (round_generic _ _ _ f) // !Rsimp01 round_0.
Qed.

Lemma fastTwoSum_0r f : format f -> fastTwoSum f 0 = DWR f 0.
Proof.
by move=> Ff; rewrite /fastTwoSum !Rsimp01 round_generic // !(Rsimp01, round_0).
Qed.

Definition twoSum (a : R) (b : dwR) :=  
  let: DWR bh bl := b in 
  let: DWR h t := fastTwoSum a bh in 
  let: l := RND (t + bl) in DWR h l.

Check twoSum.

Definition fastSum (a bh bl : R) := 
  let: DWR h t := fastTwoSum a bh in DWR h (RND (t + bl)).

Lemma error_le_ulp_add x : Rabs (RND x) <= Rabs x + ulp x.
Proof.
have : Rabs (RND x - x) <= ulp x by apply: error_le_ulp.
split_Rabs; lra.
Qed.

Lemma fastSum_0 : fastSum 0 0 0 = DWR 0 0.
Proof. by rewrite /fastSum fastTwoSum_0 Rsimp01 round_0. Qed. 

Lemma bound_ulp_FLT f e : 
  (emin <= e)%Z -> Rabs f < pow (e + p) -> ulp f <= pow e.
Proof.
move=> epLe.
have [-> fLe |f_neq0 fLe] := Req_dec f 0.
  rewrite ulp_FLT_0.
  by apply: bpow_le; lia.
rewrite ulp_neq_0 // /cexp /FLT.
apply: bpow_le.
have magfE : (mag beta f <= (e + p))%Z by apply: mag_le_bpow => //; lia.
by lia.
Qed.

Lemma error_round_delta_eps_FLT f : 
  exists d, exists e,
  [/\ 
    RND f = f * (1 + d) + e,
    e * d = 0,
    Rabs e <= alpha &
    Rabs d <= pow (- p + 1)].
Proof.
have [->|f_neq0] := Req_dec f 0.
  by exists 0; exists 0; rewrite round_0 !Rsimp01; 
     split => //; apply: bpow_ge_0.
have [pLf|fLp] := Rle_lt_dec (pow (emin + p)) (Rabs f); last first.
  exists 0; exists (RND f - f); split; rewrite ?Rsimp01 //.
  - by lra.
  - apply: Rle_trans (_ : ulp f <= _); first by apply: error_le_ulp.
    rewrite ulp_neq_0 // /cexp /FLT Z.max_r; first by rewrite /alpha; lra.
    suff : (mag beta f <= emin + p)%Z by lia.
    apply: mag_le_bpow; first by lra.
    by lra.
  by apply: bpow_ge_0.
exists ((RND f - f) / f); exists 0; split.
- by field.
- by lra.
- by rewrite Rabs_R0; apply: bpow_ge_0.
rewrite Rabs_div //.
apply/Rle_div_l; first by clear -f_neq0; split_Rabs; lra.
apply: Rlt_le.
apply: relative_error_FLT => //; first by apply: p_gt_0.
apply: Rle_trans pLf.
by apply: bpow_le; lia.
Qed.

Lemma format_decomp_prod x1 x2 : 
  generic_format beta (FLX_exp p) x1 -> 
  generic_format beta (FLX_exp p) x2 -> 
  exists m1, exists e1, x1 * x2 = IZR m1 * pow e1 /\
                        Rabs (IZR m1) < pow (2 * p).
Proof.
move=> x1F x2F.
exists ((Ztrunc (scaled_mantissa beta (FLX_exp p) x1)) * 
        (Ztrunc (scaled_mantissa beta (FLX_exp p)  x2)))%Z.
exists (Generic_fmt.cexp beta (FLX_exp p) x1 + 
        Generic_fmt.cexp beta (FLX_exp p) x2)%Z.
split.
  rewrite [in LHS]x1F [in LHS]x2F /F2R /=.
  rewrite mult_IZR bpow_plus.
  set xx1 := Ztrunc _.
  set xx2 := Ztrunc _.
  set yy1 := Generic_fmt.cexp _ _ _.
  set yy2 := Generic_fmt.cexp _ _ _.
  rewrite -[bpow _ yy1]/(pow _).
  rewrite -[bpow _ yy2]/(pow _).
  lra.
rewrite mult_IZR.
have -> : (2 * p = p + p)%Z by clear; lia.
rewrite bpow_plus Rabs_mult.
apply: Rmult_lt_compat; try by apply: Rabs_pos.
  rewrite -scaled_mantissa_generic //.
  have [x1_eq0|x1_neq0] := Req_dec x1 0.
    by rewrite x1_eq0 scaled_mantissa_0 Rabs_R0; apply: bpow_gt_0.
  suff : bpow beta (p - 1) <= Rabs (scaled_mantissa beta (FLX_exp p) x1) <=
          bpow beta p - 1 by lra.
  by apply: mant_bound_le.
rewrite -scaled_mantissa_generic //.
have [x2_eq0|x2_neq0] := Req_dec x2 0.
  by rewrite x2_eq0 scaled_mantissa_0 Rabs_R0; apply: bpow_gt_0.
suff : bpow beta (p - 1) <= Rabs (scaled_mantissa beta (FLX_exp p) x2) <=
        bpow beta p - 1 by lra.
by apply: mant_bound_le.
Qed.

End FltPrelim.

Section Flt2Prelim.

Let beta := radix2.
Variables emin p : Z.
Hypothesis Hp2: Z.lt 1 p.
Hypothesis emin_neg : (emin < - p - 1)%Z.

Local Instance p1_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Variable rnd : R -> Z.
Hypothesis valid_rnd : Valid_rnd rnd.

Local Notation FLT := (FLT_exp emin p).
Local Notation format := (generic_format beta FLT).
Local Notation RND := (round beta FLT rnd).
Local Notation pow e := (bpow beta e).
Local Notation float := (float beta).
Local Notation cexp := (cexp beta FLT).
Local Notation mant := (scaled_mantissa beta FLT).
Local Notation fastTwoSum := (fastTwoSum beta emin p rnd).
Local Notation fastSum := (fastSum beta emin p rnd).

Lemma fastTwoSum_correct a b : 
  format a -> format b -> (a <> 0 -> Rabs b <= Rabs a) ->
  let: DWR h l := fastTwoSum a b in 
  Rabs (h + l - (a + b)) <= pow (1 - 2 * p) * Rabs h.
Proof.
by move=> Fa Fb b_le_a; apply: FastTwoSum_bound_round.
Qed.

Lemma fastTwoSum_correct1 a b : 
  format a -> format b -> (a <> 0 -> Rabs b <= Rabs a) ->
  let: DWR h l := fastTwoSum a b in 
  Rabs (h + l - (a + b)) <= pow (1 - 2 * p) * Rabs (a + b).
Proof.
by move=> Fa Fb b_le_a ; apply: FastTwoSum_bound1.
Qed.

Local Notation ulp := (ulp beta FLT).

(* Lemma 1 *)
Lemma fastSum_correct a bh bl : 
  format a -> format bh -> format bl -> (a <> 0 -> Rabs bh <= Rabs a) ->
  let: DWR h l := fastSum a bh bl in 
  Rabs (h + l - (a + bh + bl)) <= pow (1 - 2 * p) * Rabs h + ulp l.
Proof.
move=> Fa Fbh Fbl bhLa.
rewrite /fastSum.
case: fastTwoSum (fastTwoSum_correct Fa Fbh) => h t F1.
have {}F1 := F1 bhLa.
apply : Rle_trans  (_ : Rabs (h + t - (a + bh)) + 
                        Rabs (RND (t + bl) - (t + bl)) <= _ ).
  by split_Rabs; lra.
apply: Rplus_le_compat => //.
by apply: error_le_ulp_round.
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

End Flt2Prelim.

Section Flt53Prelim.

Let beta := radix2.
Let p := 53%Z.
Let emax := 1024%Z.
Let emin := (3 - emax - p)%Z.

Hypothesis Hp2: Z.lt 1 p.

Local Instance p2_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Variable rnd : R -> Z.
Hypothesis valid_rnd : Valid_rnd rnd.

Local Notation FLT := (FLT_exp emin p).
Local Notation format := (generic_format beta FLT).
Local Notation RND := (round beta FLT rnd).
Local Notation pow e := (bpow beta e).
Local Notation float := (float radix2).
Local Notation cexp := (cexp beta FLT).
Local Notation mant := (scaled_mantissa beta FLT).

Open Scope R_scope.

Let alpha := pow emin.
Let omega := (1 - pow (- p)) * pow emax.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).

Lemma uE : u = pow (- p).
Proof. rewrite /u /= /Z.pow_pos /=; lra. Qed.

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
have sE : succ radix2 FLT 1 = 1 + pow (-52).
  rewrite /succ /=.
  (case: Rle_bool_spec; try lra) => _.
  by rewrite ulp_neq_0 //= /Generic_fmt.cexp mag_1 /FLT.
apply: Rle_trans (_ : ln (succ radix2 FLT 1) <= _).
  rewrite sE.
  by interval with (i_prec 54).
apply: ln_le; last first.
  by apply: succ_le_lt => //; apply: format1_FLT.
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
have sE : pred radix2 FLT 1 = 1 - pow (-53).
  rewrite /pred /= /succ.
  (case: Rle_bool_spec; try lra) => _.
  have -> : (- - (1) = 1)%R by lra.
  rewrite /pred_pos mag_1 /=.
  by case: Req_bool_spec; lra.
apply: Rle_trans (_ : ln (pred radix2 FLT 1) <= _); last first.
  rewrite sE.
  rewrite bpow_powerRZ powerRZ_Rpower; last by apply: IZR_lt.
  rewrite -[IZR beta]/2.
  by interval with (i_prec 54).
apply: ln_le.
  apply: Rlt_le_trans _ x_ge_alpha.
  by apply : alpha_gt_0.
rewrite -[x](@succ_pred_pos radix2 FLT) //; last first.
  by apply: Rlt_le_trans _ x_ge_alpha; apply: alpha_gt_0.
apply: succ_le_lt.
- by apply: generic_format_pred.
- by apply/generic_format_pred/format1_FLT.
apply: pred_lt => //.
by apply: format1_FLT.
Qed.

End Flt53Prelim.

