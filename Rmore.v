From mathcomp Require Import all_ssreflect.
From Coquelicot Require Import Coquelicot.
Require Import Reals  Psatz.
From Flocq Require Import Core.Raux.

Open Scope R_scope.

Lemma Rabs_0 x : x = 0 -> Rabs x = 0.
Proof. by move->; rewrite Rabs_R0. Qed.

Lemma Rdiv_1_l x : 1 / x = / x.
Proof. by rewrite [_ / _]Rmult_1_l. Qed.

Lemma Rdiv_1_r x : x / 1 = x.
Proof. by rewrite /Rdiv Rinv_1 Rmult_1_r. Qed.

Lemma Rdiv_0_l x : 0 / x = 0.
Proof. by rewrite [_ / _]Rmult_0_l. Qed.

Lemma Rdiv_0_r x : x / 0 = 0.
Proof. by rewrite /Rdiv Rinv_0 Rmult_0_r. Qed.

Lemma Rmult_N1_l x : (-1 * x = -x).
Proof. by lra. Qed.

Lemma Rmult_N1_r x : (x * -1 = -x).
Proof. by lra. Qed.

Definition Rsimp01 := (Rmult_0_l, Rmult_0_r, Rmult_1_l, Rmult_1_r,
                       Rminus_0_l, Rminus_0_r, Rplus_0_l, Rplus_0_r, Ropp_0,
                       Rmult_N1_l, Rmult_N1_r,
                       Rinv_0, Rdiv_0_l, Rdiv_0_r, Rabs_R0,
                       Rinv_1, Rdiv_1_l, Rdiv_1_r, Rabs_R1,
                       Rminus_eq_0).

Ltac gsplit_Rabs := rewrite /Rabs; split_case_Rabs.

Lemma Rinv_0_le_compat r : 0 <= r -> 0 <= / r.
Proof.
move=> r_pos; have [->|r_neq] := Req_dec r 0; first by rewrite Rinv_0; lra.
suff: 0 < / r by lra.
by apply: Rinv_0_lt_compat; lra.
Qed.

Lemma sqrt_Rinv x (xpos: 0 < x) : sqrt (/ x) = / sqrt x.
Proof.
have ->: / x = / 1 * / x  by field; lra.
rewrite -/Rdiv sqrt_div ?Rinv_1 ?sqrt_1 ; lra.
Qed.

Lemma leq_sqrt x y : 0 <= y -> x * x <= y * y -> x <= y.
Proof. by nra. Qed.

Lemma ltr_sqrt x y : 0 <= y -> x * x < y * y -> x < y.
Proof. by nra. Qed.

Lemma eq_sqrt x y : 0 <= x -> 0 <= y -> x * x = y * y -> x = y.
Proof. by nra. Qed.

Lemma Rabs_sqr x : Rabs x * Rabs x = x * x.
Proof. by rewrite /Rabs; case: Rcase_abs; lra. Qed.

Lemma sqrt_triangle_sum3 x y z :
  0 <= z -> 
  sqrt ((x + z) * (x + z) + y * y) <= sqrt (x * x + y * y) + z.
Proof.
move=> z_pos.
apply: leq_sqrt.
  apply: Rplus_le_le_0_compat => //.
  by apply: sqrt_ge_0.
rewrite sqrt_sqrt; last by set v := (x + z); nra.
suff: y * y + (x + z) * (x + z) - (x * x + y * y) - z * z 
      <= 2 * z * sqrt (x * x + y * y).
    have : sqrt (x * x + y * y) * sqrt (x * x + y * y) = x * x + y * y.
      by rewrite sqrt_sqrt; nra.
    by nra.
apply: leq_sqrt.
  repeat apply: Rmult_le_pos; try lra.
  by apply: sqrt_ge_0.
have -> : forall t1 t2, (t1 * t2) * (t1 * t2) = (t1 * t1) * (t2 * t2).
  by move=> *; lra.
by rewrite sqrt_sqrt; nra.
Qed.

Lemma pow2_mult x : x ^ 2 = x * x.
Proof. lra. Qed.

Lemma pow_pos_lt x y k :
  0 <= x -> 0 <= y -> (0 < k)%nat -> x < y -> x ^ k < y ^ k.
Proof.
move=> x_pos y_pos k_pos.
elim: (k) k_pos => //= [] [|k1] /= IH _ xLy; first by lra.
have : x * x ^ k1 < y * y ^ k1 by apply: IH.
set u1 := x * _ ^ _; set u2 := y * _ ^ _ => Hu1.
suff : 0 <= u1 by nra.
by apply: (pow_le x k1.+1 x_pos).
Qed.

Lemma pow_pos_lt_inv x y k :
  0 <= x -> 0 <= y -> (0 < k)%nat -> x ^ k < y ^ k -> x < y.
Proof.
move=> x_pos y_pos k_pos xkLyk.
case: (Rle_dec y x) => yLx; last by lra.
have [xEy|xDy] := Req_dec x y; first by rewrite xEy in xkLyk; lra.
suff : y ^ k < x ^ k by lra.
by apply: pow_pos_lt => //; lra.
Qed.

Lemma pow_inv x y k : 0 <= x -> 0 <= y -> (0 < k)%nat -> x ^ k = y ^ k -> x = y.
Proof.
move=> x_pos y_pos k_pos.
have := pow_pos_lt x y k x_pos y_pos k_pos.
have := pow_pos_lt y x k y_pos x_pos k_pos.
lra.
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

(* sqrt 2 is irrational *)

Lemma sqrt2_irr x y : IZR x / IZR y <> sqrt 2.
Proof.
have s2G : 1 < sqrt 2.
  by rewrite -sqrt_1; apply: sqrt_lt_1_alt; lra.
elim/Zcomplements.Z_lt_abs_induction: x y => x IH y xyE.
have xxE : (x * x = 2 * y * y)%Z.
  apply: eq_IZR; rewrite !mult_IZR.
  have -> : 2 = sqrt 2 * sqrt 2.
    by have /sqrt_sqrt Hf : 0 <= 2 by lra.
  rewrite -xyE; field => yE.
  by rewrite yE Rdiv_0_r in xyE; lra.
have Ex : Z.even x.
  have := Z.even_mul x x.
  rewrite xxE.
  by rewrite -Zmult_assoc Z.even_mul /=; case: Z.even.
case: (Zaux.Zeven_ex x) => x1; rewrite Ex Zplus_0_r => xE.
have Ey : Z.even y.
  have := Z.even_mul y y.
  have -> : (y * y = 2 * x1 * x1)%Z by lia.
  by rewrite -Zmult_assoc Z.even_mul /=; case: Z.even.
case: (Zaux.Zeven_ex y) => y1; rewrite Ey Zplus_0_r => yE.
have [x_eq0|x_neq0] := Z.eq_dec x 0.
  have y_eq0 : y = 0%Z by lia.
  suff : sqrt 2 = 0 by lra.
  by rewrite -xyE x_eq0 y_eq0; lra.
have [y_eq0|y_neq0] := Z.eq_dec y 0.
  have x_eq0 : x = 0%Z by lia.
  suff : sqrt 2 = 0 by lra.
  by rewrite -xyE x_eq0 y_eq0; lra.
case: (IH x1 _ y1); first by lia.
rewrite -xyE xE yE !mult_IZR; field.
apply: not_0_IZR; lia.
Qed.
