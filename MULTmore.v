Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Mult.

Variable p : Z.
Context { prec_gt_0_ : Prec_gt_0 p }.
Variable emin : Z.
Variable beta : radix.

Hypothesis Hp2: Z.lt 1 p.
Local Notation pow e := (bpow beta e).

Open Scope R_scope.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Local Notation float := (float beta).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RN := (round beta fexp rnd).

Definition is_imul x y := exists z : Z, x = IZR z * y.

Theorem is_imul_EM :
  forall x y,is_imul x y \/ ~is_imul x y.
Proof.
move=> x y.
case: (Req_dec y 0)=>[->|y_neq_0].
  case: (Req_dec x 0)=>[->|x_neq_0].
    by left; exists 0%Z; lra.
  right; move=> [z xE]; lra.
pose z := Zfloor(x/y).
case:(Req_dec (x/y) (IZR z))=> hz.
  by left; exists z; rewrite -hz; field.
right; move => [z0 xE].
apply/hz.
rewrite /z.
have->: x/y = IZR z0 by rewrite xE; field.
by rewrite Zfloor_IZR.
Qed.

Lemma is_imul_add x1 x2 y : 
  is_imul x1 y -> is_imul x2 y -> is_imul (x1 + x2) y.
Proof.
move=> [z1 ->] [z2 ->]; exists (z1 + z2)%Z.
by rewrite plus_IZR; lra.
Qed.

Lemma is_imul_opp x y : 
  is_imul x y -> is_imul (- x) y.
Proof.
move=> [z ->]; exists (-z)%Z.
by rewrite opp_IZR; lra.
Qed.

Lemma is_imul_minus x1 x2 y : 
  is_imul x1 y -> is_imul x2 y -> is_imul (x1 - x2) y.
Proof.
move=> [z1 ->] [z2 ->]; exists (z1 - z2)%Z.
by rewrite minus_IZR; lra.
Qed.

Lemma is_imul_mul x1 x2 y1 y2 : 
  is_imul x1 y1 -> is_imul x2 y2 -> is_imul (x1 * x2) (y1 * y2).
Proof.
move=> [z1 ->] [z2 ->]; exists (z1 * z2)%Z.
rewrite mult_IZR; lra.
Qed.

Lemma is_imul_pow_mag x y : x <> 0 -> is_imul x (pow y) -> (y <= (mag beta x) - 1)%Z.
Proof.
move=> x_neq_0 [k kE].
rewrite kE in x_neq_0 *.
have k_neq_0 : k <> 0%Z.
  move=> k_eq_0; case: x_neq_0.
  by rewrite k_eq_0; lra.
rewrite mag_mult_bpow; last by apply: not_0_IZR.
suff : (1 <= (mag beta (IZR k)))%Z by lia.
apply: mag_ge_bpow.
rewrite pow0E -abs_IZR.
apply: IZR_le; lia.
Qed.

Lemma is_imul_format_mag_pow x y : 
  format x -> (y <= fexp (mag beta x))%Z -> is_imul x (pow y).
Proof.
move=> Fx My.
have [-> | x_neq0] := Req_dec x 0; first by exists 0%Z; lra.
rewrite /generic_format /F2R /= in Fx.
rewrite Fx /cexp.
set m := Ztrunc _.
exists (m * (beta ^ (fexp (mag beta x) - y)))%Z.
rewrite mult_IZR IZR_Zpower; last by lia.
by rewrite Rmult_assoc -bpow_plus; congr (_ * pow _); lia.
Qed.

Lemma is_imul_pow_le x y1 y2 : 
  is_imul x (pow y1) -> (y2 <= y1)%Z -> is_imul x (pow y2).
Proof.
move=> [z ->] y2Ly1.
exists (z * beta ^ (y1 - y2))%Z.
rewrite mult_IZR IZR_Zpower; last by lia.
rewrite Rmult_assoc -bpow_plus; congr (_ * pow _); lia.
Qed.

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

Lemma format_err_mul (a b : R) :
  format a -> format b -> is_imul (a * b) (pow emin) ->
  format (RN (a * b) - a * b).
move=> Fa Fb [z zE].
have [rz rE]:( is_imul (RN (a*b)) (pow emin)).
   by apply/is_imul_pow_round;exists z.
have eE: (RN (a * b) - a * b) = IZR (rz -z) * pow emin by rewrite  minus_IZR; lra.
have [pLab|pGab] := Rle_lt_dec (pow (emin + 2 * p - 1)) (Rabs (a * b)).
  by apply: mult_error_FLT.
have F1 : Ulp.ulp beta fexp (pow (emin + 2 * p - 1)) = pow (emin + p).
  by rewrite ulp_bpow; congr (pow _); rewrite /fexp ; lia.
have [hut | hue] : Rabs (RN (a * b) - a * b) <= pow (emin + p).
    apply/(Rle_trans _ (ulp beta fexp (a * b))); first by apply/error_le_ulp.
    by rewrite -F1; apply/ulp_le; rewrite (Rabs_pos_eq (pow _)); try lra;
      apply/bpow_ge_0.
  apply/generic_format_FLT.
  apply/(FLT_spec _ _ _ _ ({| Fnum := rz - z; Fexp := emin |} : float)); 
     rewrite /F2R //=; last lia.
  apply/lt_IZR; move:hut; rewrite {1}eE.
  rewrite Rabs_mult abs_IZR IZR_Zpower; last lia.
  rewrite (Rabs_pos_eq (pow _)); last by apply/bpow_ge_0.
  by rewrite bpow_plus; move:(bpow_gt_0 beta emin); nra.
move: hue; rewrite -(Rabs_pos_eq (pow _)); last by apply/bpow_ge_0.
  by case/Rabs_eq_Rabs => ->; last apply/generic_format_opp;
    apply/generic_format_FLT_bpow; lia.
Qed.

Lemma imul_fexp_le (f : float) e : (e <= Fexp f)%Z -> is_imul f (pow e).
Proof.
case: f => mf ef /= eLef.
rewrite /F2R /=.
have ->: (ef = (ef - e) + e)%Z by lia.
rewrite bpow_plus.
exists (mf * (beta ^ (ef - e)))%Z.
rewrite mult_IZR IZR_Zpower; try lia.
by rewrite Rmult_assoc.
Qed.

Lemma imul_fexp_lt (f : float) e : 
  beta = radix2 -> Z.even (Fnum f) -> (e - 1 <= Fexp f)%Z -> is_imul f (pow e).
Proof.
move=> betaE.
case: f => mf ef /= even_f eLef.
rewrite /F2R /=.
have ->: (ef = -1 + (ef - (e - 1) + e))%Z by lia.
rewrite 2!bpow_plus betaE.
exists ((mf / 2) * (radix2 ^ (ef - (e - 1))))%Z.
rewrite mult_IZR IZR_Zpower; last by lia.
rewrite -!Rmult_assoc; congr (_ * _ * _).
have [hp ->] := Zeven_ex mf.
rewrite even_f Z.add_0_r Zmult_comm Z.div_mul //.
by rewrite mult_IZR /= /Z.pow_pos /=; lra.
Qed.

Lemma is_imul_pow_le_abs x y : is_imul x (pow y) -> x <> 0 -> pow y <= Rabs x.
Proof.
case=> [k ->] ke_neq0.
have powy_gt_0 : 0 < pow y by apply: bpow_gt_0.
rewrite Rabs_mult [Rabs (pow _)]Rabs_pos_eq; last by lra.
suff : 1 <= Rabs (IZR k) by nra.
rewrite -abs_IZR; apply: IZR_le.
suff : k <> 0%Z by lia.
by contradict ke_neq0; rewrite ke_neq0 Rsimp01.
Qed.

Lemma is_imul_bound_pow e1 e2 p1 x1 m1 : 
   pow e1 <= Rabs x1 -> 
   x1 = IZR m1 * pow e2 -> Rabs (IZR m1) < pow p1 ->
   is_imul x1 (pow (e1 - p1 + 1)).
Proof.
move=> x1B x1E m1B.
exists (m1 * (beta ^ (e2 - (e1 - p1 + 1))))%Z.
  rewrite mult_IZR (IZR_Zpower beta).
    rewrite Rmult_assoc -bpow_plus x1E.
    by congr (_ * pow _); lia.   
suff: (e1 < p1 + e2)%Z by lia.
apply: (lt_bpow beta).
rewrite bpow_plus.
suff : Rabs x1 < pow p1 * pow e2 by lra.
have pe2_gt0 : 0 < pow e2 by apply: bpow_gt_0.
by rewrite x1E Rabs_mult [Rabs (pow _)]Rabs_pos_eq //; nra.
Qed.

End Mult.
