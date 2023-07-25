(* Copyright (c)  Inria. All rights reserved. *)

Require Import Reals  Psatz.
From Flocq Require Import Core Relative Sterbenz Operations.
From mathcomp Require Import all_ssreflect.
From Coquelicot Require Import Coquelicot.
Require Import Rmore.
Set Implicit Arguments.

Section Float.

Variables  p: Z.
Variable beta: radix.
Hypothesis Hbeta2: (1 < beta)%Z.
Hypothesis Hp2: (1 < p)%Z.

Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.
Variable choice : Z -> bool.
Hypothesis choice_sym: forall x, choice x  = negb (choice (- (x + 1))).

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation ulp := (ulp beta fexp).

Open Scope R_scope.

(* About power                                                                *)

Lemma Rabs_pow x : Rabs (pow x) = pow x.
Proof. by rewrite Rabs_pos_eq //; apply: bpow_ge_0. Qed.

Lemma pow0E : pow 0 = 1.
Proof. by rewrite /= /Z.pow_pos; lra. Qed.

Lemma pow1E : pow 1 = IZR beta.
Proof. by rewrite /= /Z.pow_pos /= Zmult_1_r; lra. Qed.

Lemma pow2M r : pow (2 * r) = (pow r) ^ 2.
Proof.
have -> : (2 * r = r + r)%Z by lia.
by rewrite bpow_plus; lra.
Qed.

Lemma pow_neq_0 x : pow x <> 0.
Proof. by have := bpow_gt_0 beta x; lra. Qed.

(* About Format                                                               *)

Lemma format_pow x : format (pow x).
Proof.
apply: generic_format_FLX.
apply: (FLX_spec beta p _ (Float beta 1 x)).
  by rewrite  /F2R /=; lra.
by apply: (Zpower_lt _ 0); lia.
Qed.

Lemma FLX_format_Rabs_Fnum  (x : R) (fx : float beta):
  x = F2R fx -> Rabs (IZR (Fnum fx)) <= pow p -> format x.
Proof.
have [fn fe ->] := fx; rewrite /F2R /= =>h.
have [h1|h1] : Rabs (IZR (Fnum fx)) < pow p \/ Rabs (IZR (Fnum fx)) = pow p.
    by lra.
  apply:generic_format_F2R =>/not_0_IZR Mxyn0.
  rewrite /F2R /= /cexp /fexp mag_mult_bpow //.
  have mlpb := (mag_le_bpow beta _ p Mxyn0 h1).
  lia.
split_Rabs.
  rewrite -[IZR _]Ropp_involutive h1 -Ropp_mult_distr_l -bpow_plus.
  apply: generic_format_opp.
  by apply: generic_format_bpow; rewrite /fexp; lia.
rewrite h1 -bpow_plus.
by apply: generic_format_bpow; rewrite /fexp; lia.
Qed.

(* About beta                                                                 *)

Lemma beta_ge_2 : 2 <= IZR beta.
Proof. by apply: IZR_le; lia. Qed.

Lemma Rabs_beta : Rabs (IZR beta) = IZR beta.
Proof. by rewrite -pow1E Rabs_pow. Qed.

(* About cexp                                                                 *)

Lemma cexp_bpow : forall x e, x <> R0 -> cexp (x * pow e) = (cexp x + e)%Z.
Proof. by move=> x e xn0; rewrite /cexp mag_mult_bpow // /FLX_exp; lia. Qed.


(* About mantissa *)

Lemma mant_bound x : format x -> x <> 0 -> pow (p - 1) <= Rabs (mant x) < pow p.
Proof.
move=> Fx x_neq_0.
split; last first.
  have {2}-> : p = (mag beta x - cexp x)%Z by rewrite /cexp /fexp; lia.
  by apply: scaled_mantissa_lt_bpow.
have F_pos : 0 < pow (mag beta x - p) by apply: bpow_gt_0.
apply: Rmult_le_reg_l F_pos _.
have pow_p_gt0 := bpow_gt_0 beta p.
rewrite !bpow_plus !bpow_opp -!Rmult_assoc.
rewrite [_ */ _ * _]Rmult_assoc Rinv_l ?Rmult_1_r ; try lra.
have := bpow_mag_le beta x x_neq_0.
have := (Fx).
rewrite /generic_format /F2R /cexp {2}/fexp -scaled_mantissa_generic // => xE.
rewrite [in X in _ <= X]xE Rabs_mult Rabs_pow !bpow_plus !bpow_opp.
by lra.
Qed.

Lemma mant_bound_le x : format x -> x <> 0 -> 
  pow (p - 1) <= Rabs (mant x) <= pow p -1 .
Proof.
move=> Fx x_neq_0.
have [? Hlt] := mant_bound Fx x_neq_0; split => //.
rewrite (scaled_mantissa_generic beta fexp x Fx) in Hlt *.
rewrite -!(IZR_Zpower beta) ?Rabs_Zabs in Hlt *; try lia.
rewrite -minus_IZR; apply: IZR_le.
by have := lt_IZR _ _ Hlt; lia.
Qed.

Lemma mant_bpow x e : mant (x * pow e) = mant x.
Proof.
case: (Req_dec x 0) => [->|Zx]; first by rewrite Rmult_0_l.
rewrite /scaled_mantissa cexp_bpow // Rmult_assoc -bpow_plus.
by ring_simplify (e + - (cexp x + e))%Z.
Qed.

(* About u                                                                    *)

Definition u := /2 * pow (1 - p).

Lemma u_gt_0 : 0 < u.
Proof. by apply: Rmult_lt_0_compat; [lra | apply: bpow_gt_0]. Qed.

Lemma u_lt_1 : u < 1.
Proof.
rewrite /u.
suff: pow (1 - p) < pow 0 by rewrite pow0E; lra.
by apply: bpow_lt; lia.
Qed.

Lemma u_bound : 0 < u < 1.
Proof. by split; [apply: u_gt_0 | apply: u_lt_1]. Qed.

Fact ui2: u <= /2. 
Proof.
rewrite /u; suff: pow (1 - p) <= 1 by lra.
have-> : 1 = pow 0 by [].
apply: bpow_le; lia.
Qed.

(* About ulp *)

Lemma ulp1 : ulp 1 = 2 * u.
Proof. by rewrite /u ulp_neq_0 /cexp ?mag_1 /=; lra. Qed.

Lemma ulp_2u x : ulp x <= 2 * u * Rabs x.
Proof.
suff : ulp x <= Rabs x * pow (1 - p) by rewrite /u; lra.
by apply: ulp_FLX_le.
Qed.

Lemma Rabs_div_ulp_bound t : t <> 0 -> pow (p - 1) <= Rabs t / ulp t < pow p.
Proof.
move=> t_neq_0.
have ulp_gt_0 : 0 < ulp t by rewrite ulp_neq_0  //; apply: bpow_gt_0.
suff : ulp t * pow (p - 1) <= Rabs t < ulp t * pow p.
  move=> [H1 H2]; split; first by apply/Rle_div_r; lra.
  by apply/Rlt_div_l; lra.
rewrite ulp_neq_0 // /cexp -!bpow_plus /fexp.
have -> : (mag beta t - p + (p - 1) = mag beta t - 1)%Z by lia.
have -> : (mag beta t - p + p = mag beta t)%Z by lia.
by split; [apply: bpow_mag_le | exact: bpow_mag_gt].
Qed.

Lemma ulp_in_binade x z : 
  pow (z + p - 1) <= Rabs x < pow (z + p) -> ulp x = pow z.
Proof.
move=> xB.
have zp_gt0 := bpow_gt_0 beta (z + p - 1).
rewrite ulp_neq_0 /cexp /fexp; last by split_Rabs; lra.
suff -> : (mag beta x = z + p :> Z)%Z by congr (pow _); lia.
by apply: mag_unique.
Qed. 

Theorem ulp_FLX_gt x : x <> 0 -> Rabs x * pow (- p) < ulp x.
Proof.
move=> x_neq_0.
rewrite ulp_neq_0 //.
unfold cexp, FLX_exp.
unfold Zminus; rewrite bpow_plus.
apply Rmult_lt_compat_r; first by apply bpow_gt_0.
by apply: bpow_mag_gt.
Qed.

Lemma ulp_FLX_bound x : 
  x <> 0 -> ulp x * pow (p - 1) <=  Rabs x < ulp x * pow p.
Proof.
move=> x_neq_0.  
split.
  have xF1 := @ulp_FLX_le beta p p_gt_0 x.
  have -> : Rabs x = Rabs x * pow (1 - p) * pow (p - 1).
    rewrite Rmult_assoc -bpow_plus.
    have -> : (1 - p + (p - 1) = 0)%Z by lia.
    by rewrite pow0E; lra.
  by have := bpow_gt_0 beta (p - 1); nra.
have xF1 := @ulp_FLX_gt x x_neq_0.
have -> : Rabs x = Rabs x * pow (- p) * pow p.
  rewrite Rmult_assoc -bpow_plus.
  have -> : (- p + p = 0)%Z by lia.
  by rewrite pow0E; lra.
by have := bpow_gt_0 beta p; nra.
Qed.

Lemma ulp_FLX_bound_le x : ulp x * pow (p - 1) <= Rabs x <= ulp x * pow p.
Proof.
split.
  have xF1 := @ulp_FLX_le beta p p_gt_0 x.
  have -> : Rabs x = Rabs x * pow (1 - p) * pow (p - 1).
    rewrite Rmult_assoc -bpow_plus.
    have -> : (1 - p + (p - 1) = 0)%Z by lia.
    by rewrite pow0E; lra.
  by have := bpow_gt_0 beta (p - 1); nra.
have xF1 := @ulp_FLX_ge beta p p_gt_0 x.
have -> : Rabs x = Rabs x * pow (- p) * pow p.
  rewrite Rmult_assoc -bpow_plus.
  have -> : (- p + p = 0)%Z by lia.
  by rewrite pow0E; lra.
by have := bpow_gt_0 beta p; nra.
Qed.

Lemma lt_mag_ulp x y : 
  ulp x < ulp y -> Rabs x < pow (mag beta y - 1).
Proof.
move=> Hu.
have [->|x_neq0]:= Req_dec x 0; first by rewrite Rabs_R0; apply: bpow_gt_0.
have y_neq0 : y <> 0.
  move=> y_eq0.
  have uy_0 : ulp y = 0 by rewrite y_eq0 ulp_FLX_0.
  have := ulp_ge_0 beta fexp x.
  by rewrite uy_0 in Hu; lra.
suff pxLpy : (mag beta x < mag beta y)%Z.
  apply: Rlt_le_trans (bpow_mag_gt beta _) _.
  by apply: bpow_le; lia.
apply: (lt_bpow beta).
have : 0 < pow (- p) by apply: bpow_gt_0.
rewrite !ulp_neq_0 // /cexp /fexp !bpow_plus in Hu.
by nra.
Qed.

Lemma ulp_mag x y (x0 : x <> 0) (y0: y <> 0) :
  ulp x <= ulp y -> (mag beta x <= mag beta y)%Z.
Proof. by rewrite !ulp_neq_0 // /cexp /fexp => /le_bpow; lia. Qed.

Lemma ulp_gt_0 x : x <> 0 -> 0 < ulp x.
Proof.
move=> x_neq_0; rewrite ulp_neq_0 //.
by apply: bpow_gt_0.
Qed.

Lemma ulp_lt_le x y : ulp x < ulp y -> IZR beta * ulp x <= ulp y.
Proof.
have [->|x_neq_0] := Req_dec x 0; first by rewrite ulp_FLX_0; lra.
move=> uxLuy.
have y_neq_0 : y <> 0.
  move=> y_eq_0; move: uxLuy; rewrite y_eq_0 ulp_FLX_0.
  by rewrite ulp_neq_0; have := bpow_gt_0 beta (cexp x); nra.
move: uxLuy; rewrite -pow1E !ulp_neq_0 // -bpow_plus.
by move=> /lt_bpow H; apply: bpow_le; lia.
Qed.


(* About round to the nearest                                                 *)

Local Notation RN := (round beta fexp (Znearest choice)).

Lemma RN_1 : RN 1 = 1.
Proof.
apply: round_generic.
have<- :  F2R ({| Fnum := Z.pow beta (p - 1); Fexp := 1-p |} : float beta) = 1.
  rewrite /F2R IZR_Zpower; try lia.
  by rewrite /Fexp -bpow_plus -[1]/(pow 0); congr (pow _); lia.
apply: generic_format_canonical.
rewrite /canonical /Fexp /cexp mag_F2R_Zdigits; last first.
  by apply: Z.pow_nonzero; rewrite /=; lia.
rewrite Zdigits_Zpower; first by rewrite /fexp; lia.
by lia.
Qed.

Lemma RN_sym x: RN (- x) = - (RN x).
Proof.
suff : - RN (- x) = RN x by lra.
by rewrite round_N_opp Ropp_involutive /round  /Znearest -choice_sym.
Qed.

Lemma RN_abs x: RN (Rabs x) = Rabs (RN x).
Proof.
by split_Rabs; rewrite ?RN_sym //; [have : RN x <= RN 0 | have : RN 0 <= RN x];
  try (by apply: round_le; lra); rewrite round_0; lra.
Qed.

Lemma RN_lt_inv t v : RN t < RN v -> t < v.
Proof.
move=> htv.
have [|] := Rlt_le_dec t v =>// hvt.
have : RN v <= RN t by apply/round_le.
lra.
Qed.

Lemma RN_ge_0 x : 0 <= x -> 0 <= RN x.
Proof.
move=> x_pos.
have <- : RN 0 = 0 by rewrite round_0.
by apply: round_le.
Qed.

Lemma relative_error_le x : Rabs ((RN x - x)) <= u * Rabs x.
Proof.
have [->|x_neq0] := Req_dec x 0.
  by rewrite round_0 // Rminus_0_r Rabs_R0; lra.
apply: Rle_trans  (_ : /2 * ulp x <= _); first by apply: error_le_half_ulp.
by have := ulp_2u x; lra.
Qed.

Lemma relative_error_lt x : x <> 0 -> Rabs ((RN x - x)) < u * Rabs x.
Proof.
move=> x_neq_0.
have [He | Hne] := Req_dec (Rabs x) (pow (p - 1) * ulp x).
  suff -> : RN x = x.
    rewrite Rminus_eq_0 Rsimp01.
    by have := u_gt_0; split_Rabs; nra.
  suff: RN (Rabs x) = Rabs x.
    split_Rabs => //.
    rewrite -[RN x]Ropp_involutive -RN_sym; lra.
  apply: round_generic.
  rewrite He ulp_neq_0 // -bpow_plus.
  by apply: format_pow.
apply: Rle_lt_trans  (_ : /2 * ulp x < _); first by apply: error_le_half_ulp.
suff : ulp x <> 2 * u * Rabs x by have := ulp_2u x; lra.
contradict Hne; rewrite Hne /u.
have ->: 2 * (/ 2 * pow (1 - p)) = pow (1 - p) by lra.
rewrite -Rmult_assoc -bpow_plus.
have ->: (p -1 + (1 - p) = 0)%Z by lia.
by rewrite pow0E Rsimp01.
Qed.

Lemma RN_pow x : RN (pow x) = pow x.
Proof. by rewrite round_generic //; exact: format_pow. Qed.

Lemma RN_ulp_FLX_bound x : 
  ulp x * pow (p - 1) <=  Rabs (RN x) <= ulp x * pow p.
Proof.
have [->|x_neq_0] := Req_dec x 0.
  by rewrite ulp_FLX_0 round_0; split_Rabs; lra.
have F := ulp_FLX_bound_le x.
rewrite ulp_neq_0 // -!bpow_plus -RN_abs.
by split; rewrite -RN_pow; apply: round_le; rewrite bpow_plus -ulp_neq_0; lra.
Qed.

Lemma error_bound_ulp_u t : Rabs (RN t - t) <= /2 * ulp t <= u * Rabs t.
Proof.
split; first by apply: error_le_half_ulp.
have [->|t_neq0] := Req_dec t 0; first by rewrite ulp_FLX_0 Rabs_R0; lra.
rewrite Rmult_assoc.
apply: Rmult_le_compat_l; first by lra.
have -> : pow (1 - p) = / (pow (p - 1)).
  have -> : (1 - p = - (p - 1))%Z by lia.
  by rewrite bpow_opp.
rewrite Rmult_comm.
apply/Rle_div_r; first by apply: bpow_gt_0.
have [H _]:= Rabs_div_ulp_bound t_neq0.
rewrite Rmult_comm.
apply/Rle_div_r => //.
rewrite ulp_neq_0 //.
by apply: bpow_gt_0.
Qed.

Lemma RN_IZR_ex z : exists z', RN (IZR z) = IZR z'.
Proof.
have [zLb|bLz] := Z_lt_le_dec (Z.abs z) (beta ^ p).
  exists z.
  rewrite round_generic //.
  apply/generic_format_FLX/(FLX_spec _ _ _ (Float beta z 0)) => //.
  by rewrite /F2R  /=; lra.
by have [] := round_DN_or_UP beta fexp (Znearest choice) (IZR z);
    rewrite /round /F2R /= => ->;
      [exists  ((up (mant (IZR z)) - 1) * beta ^ ( cexp (IZR z)))%Z|
       exists  (-(up (- mant (IZR z)) - 1) * beta ^ ( cexp (IZR z)))%Z];
    rewrite mult_IZR IZR_Zpower // /cexp /fexp;
    (suff: (p <= mag beta (IZR z))%Z by lia);
    (apply/mag_ge_bpow/(Rle_trans _ (pow p)); first by apply/bpow_le; lia);
    (rewrite -abs_IZR -IZR_Zpower; [apply/IZR_le |]); lia.
Qed.

Lemma RN_E t : exists d, RN t = t * (1 + d) /\ Rabs d <= u.
Proof.
have [->|t_neq0] := Req_dec t 0.
  exists 0; split; first by rewrite round_0; lra.
  by have := u_gt_0; rewrite Rabs_R0; lra.
exists ((RN t - t) / t); split; first by field.
rewrite Rabs_div //.
apply/Rle_div_l; first by gsplit_Rabs; lra.
by case: (error_bound_ulp_u t); lra.
Qed.

Lemma RN_minus_ulp_le x y (fx : format x) (fy: format y):
  ulp (x - y) <= ulp x -> ulp (x - y) <= ulp y -> RN (x - y) = x - y.
Proof.
have [->|xy0 ulpx ulpy] := Req_dec (x- y) 0; first by rewrite round_0.
have ulpxy := ulp_gt_0 xy0.
have [->|x0] := Req_dec x 0.
  rewrite round_generic //.
  have->: 0 - y =  -y by lra.
  by apply/generic_format_opp.
have [->|y0] := Req_dec y 0; first by rewrite round_generic // Rminus_0_r.
rewrite round_generic //.
apply/generic_format_plus=> //; first by apply/generic_format_opp.
have ->: x + - y = x - y by lra.
apply: Rle_trans (_ : pow (mag beta (x - y)) <= _).
apply/Rlt_le/bpow_mag_gt.
apply/bpow_le.
apply/Z.min_glb; apply /ulp_mag=>//; first by lra.
by rewrite ulp_opp.
Qed.

Lemma RN_ulp_le x : 0 <= x -> ulp x <= ulp (RN x).
move => [xpos | <-]; last by rewrite round_0 ulp_FLX_0; lra.
case: (ulp_round_pos beta fexp  (Znearest choice) x xpos) =>[|->]; first by lra.
rewrite ulp_bpow ulp_neq_0; last by lra.
by rewrite /cexp /fexp; apply/bpow_le; lia.
Qed.

Lemma RN_same_sign x : 0 <= RN x * x.
Proof.
have [x_pos|x_neg] := Rle_lt_dec 0 x.
  have : RN 0 <= RN x by apply: round_le.
  by rewrite round_0; nra.
have : RN x <= RN 0 by apply: round_le; lra.
by rewrite round_0; nra.
Qed.

Lemma RN_nearest_lt_half_ulp f g : 
  format g -> 0 <= g -> g <= f < g + /2 * ulp g -> RN f = g.
Proof.
have [->|g_neq_0] := Req_dec g 0; first by rewrite ulp_FLX_0; lra.
have [->|g_neq_f] := Req_dec f g; first by move=> *; rewrite round_generic.
move=> Fg p_pos f_bound.
have ug_pos := ulp_gt_0 g_neq_0.
have F1 : succ beta fexp g = g + ulp g by apply: succ_eq_pos.
have F2 : round beta fexp Zfloor f = g.
  by apply: round_DN_eq => //; lra.
have F3 : round beta fexp Zceil f = succ beta fexp g.
  apply: round_UP_eq; first by apply: generic_format_succ.
  by rewrite pred_succ //; lra.
rewrite -F2.
apply: round_N_eq_DN; lra.
Qed.

Lemma RN_mult_pow x e :  RN (x * pow e) = RN x * pow e.
Proof.
have [->|Zx] := Req_dec x 0; first by rewrite Rmult_0_l round_0 Rmult_0_l.
rewrite /round/F2R /=  /mant /cexp mag_mult_bpow // 
        !Rmult_assoc -!bpow_plus/fexp.
by congr(IZR (Znearest _ (_ * pow _)) * pow _); lia.
Qed.

(* Lemma 4.2 *)
Fact RN_lt_pos x y (xpos : 0 <= x) (ypos : 0 < y): 
  x < y - /2 * ulp y -> RN x < y.
Proof.
move=> xlyyu.
apply: (Rle_lt_trans _ (x + /2 * ulp x)).
  case: (error_bound_ulp_u x); move/Rabs_le_inv; rewrite Rabs_pos_eq; lra.
apply: (Rle_lt_trans _ (x + /2 *  ulp y)); last lra.
suff: ulp x <= ulp y by lra.
apply: ulp_le; rewrite !Rabs_pos_eq;[|lra|lra].
suff: 0 <= ulp y by lra.
apply: ulp_ge_0.
Qed.

Definition iRN (z : Z) := Zfloor (RN (IZR z)).

Lemma iRNE (z : Z) : RN (IZR z) = IZR (iRN z).
Proof.
by rewrite /iRN; have [x ->] := RN_IZR_ex z; rewrite Zfloor_IZR.
Qed.

(* About round down                                                           *)

Local Notation RD := (round beta fexp Zfloor).

Lemma round_DN_UP_le (x : R) :
  round beta fexp Zfloor x <=  x <= round beta fexp Zceil x.
Proof.
case : (generic_format_EM beta fexp  x)=> Fx.
  rewrite !round_generic //; lra.
suff: RD x < x < round beta fexp Zceil x by lra.
by apply: round_DN_UP_lt.
Qed.

End Float.

(* About complex number                                                       *)

Definition generic_formatC beta fexp (c : C) :=
  generic_format beta fexp c.1 /\ generic_format beta fexp c.2.

Lemma generic_formatMCi beta fexp c :
  generic_formatC beta fexp c -> generic_formatC  beta fexp (Ci * c)%C.
Proof.
case: c => a b  [/= Fa Fb]; split; rewrite /= !Rsimp01 //.
by apply: generic_format_opp.
Qed.

(* round for complex number *)
Definition roundC beta fexp rnd (z : C) : C := 
   (round beta fexp rnd z.1, round beta fexp rnd z.2).

Lemma generic_formatC_roundC beta fexp rnd z :
  Valid_exp fexp -> Valid_rnd rnd ->
  generic_formatC beta fexp (roundC beta fexp rnd z).
Proof. 
by move=> Ve Vr; case: z => x y; split; apply: generic_format_round.
Qed.

Lemma roundC_generic beta fexp rnd z :
  Valid_rnd rnd ->
  generic_formatC beta fexp z -> roundC beta fexp rnd z = z.
Proof.
by move=> Hv; case: z => x y /= [Hi1 Hi2]; congr (_, _); 
      rewrite /= round_generic.
Qed.
