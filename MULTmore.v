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

Lemma exactMul (a b : R) :
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

End Mult.


