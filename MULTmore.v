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

Lemma is_imul_minus x1 x2 y : 
  is_imul x1 y -> is_imul x2 y -> is_imul (x1 - x2) y.
Proof.
move=> [z1 ->] [z2 ->]; exists (z1 - z2)%Z.
by rewrite minus_IZR; lra.
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
have [->|ab_neq0] := Req_dec (a * b) 0.
  by rewrite !(round_0, Rsimp01); apply: generic_format_0.
have [pLab|pGab] := Rle_lt_dec (pow (emin + 2 * p - 1)) (Rabs (a * b)).
  by apply: mult_error_FLT.
have F1 : Ulp.ulp beta fexp (pow (emin + 2 * p - 1)) = pow (emin + p).
  rewrite ulp_bpow; congr (pow _).
  by rewrite /fexp Z.max_l; lia.
have F2 : Rabs (RN (a * b) - a * b) <= pow (emin + p).
  rewrite -F1.
  apply: Rle_trans (error_le_ulp _ _ _ _) _.
  apply: ulp_le.
  rewrite [X in _ <= X]Rabs_pos_eq //; first by lra.
  apply: bpow_ge_0.
have [zr Hzr] : 
     exists zr, RN (a * b) = F2R ({| Fnum := zr; Fexp := emin |} : float).
  have : format (RN (a * b)) by apply: generic_format_round.
  rewrite /generic_format [X in _ = X -> _]/F2R /=.
  set m := Ztrunc _; set e := cexp _ => H.
  exists (m * (beta ^ (e - emin)))%Z.
  rewrite H /F2R /= mult_IZR (IZR_Zpower beta).
    rewrite Rmult_assoc -bpow_plus. 
    by congr (_ * pow _); lia.
  by rewrite /e /cexp /fexp; lia.
have FF : RN (a * b) - a * b = F2R ({| Fnum := zr - z; Fexp := emin |} : float).
  by rewrite Hzr zE /F2R /= minus_IZR; lra.
have /Rle_lt_or_eq_dec [C1 | C2] := F2 ; last first.
  apply: generic_format_abs_inv.
  rewrite C2.
  apply: generic_format_FLT.
  by apply: FLT_format_bpow; lia.
have F : Rabs (IZR (zr - z)) < pow p.
  rewrite bpow_plus [_ * pow p]Rmult_comm in C1.
  rewrite FF /F2R /= Rabs_mult in C1.
  suff : 0 < pow emin by split_Rabs; nra.
  by apply: bpow_gt_0.
apply: generic_format_FLT.
apply: FLT_spec FF _ _ => /=; last by lia.
apply/lt_IZR.
rewrite abs_IZR.
rewrite -(IZR_Zpower beta) // in F.
by suff : (0 < p)%Z by lia.
Qed.

End Mult.


