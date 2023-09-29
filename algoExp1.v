Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Interval Require Import Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim algoLog1 algoMul1.
Require Import Fast2Sum_robust_flt algoQ1 tableT1 tableT2.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section algoExp1.

Let p := 53%Z.
Let emax := 1024%Z.
Let emin := (3 - emax - p)%Z.

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
Context ( valid_rnd : Valid_rnd rnd ).

Local Notation float := (float radix2).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format radix2 fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation fastTwoSum := (fastTwoSum rnd).
Local Notation exactMul := (exactMul rnd).
Local Notation fastSum := (fastSum rnd).

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Local Notation ulp := (ulp beta fexp).

Definition INVLN2 := 0x1.71547652b82fep+12.

Lemma format_INVLN2 : format INVLN2.
Proof.
have -> : INVLN2 = Float beta 6497320848556798 (- 40).
  by rewrite /F2R /INVLN2 /=; lra.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma INVLN2B : Rabs (INVLN2 - pow 12 / ln 2) < Rpower 2 (- 43.447).
Proof. by interval with (i_prec 70). Qed. 

Definition LN2H := 0x1.62e42fefa39efp-13.

Lemma format_LN2H : format LN2H.
Proof.
have -> : LN2H = Float beta 6243314768165359 (- 65).
  by rewrite /F2R /LN2H /=; lra.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Definition LN2L := 0x1.abc9e3b39803fp-68.

Lemma format_LN2L : format LN2L.
Proof.
have -> : LN2L = Float beta 7525737178955839 (- 120).
  by rewrite /F2R /LN2L /=; lra.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma LN2HLB : Rabs (LN2H + LN2L - ln 2 * pow (- 12)) < Rpower 2 (- 122.43).
Proof. by rewrite /LN2H /LN2L; interval with (i_prec 150). Qed.

Lemma imul_INVLN2 : is_imul INVLN2 (pow (- 40)).
Proof.
have -> : INVLN2 = Float beta 6497320848556798 (- 40).
  by rewrite /F2R /INVLN2 /=; lra.
by exists 6497320848556798%Z; rewrite /F2R /INVLN2 /=; lra.
Qed.

Lemma imul_LN2H : is_imul LN2H (pow (- 65)).
Proof.
have -> : LN2H = Float beta 6243314768165359 (- 65).
  by rewrite /F2R /LN2H /=; lra.
by exists 6243314768165359%Z; rewrite /F2R /INVLN2 /=; lra.
Qed.

Lemma imul_LN2L : is_imul LN2L (pow (- 120)).
Proof.
have -> : LN2L = Float beta 7525737178955839 (- 120).
  by rewrite /F2R /LN2L /=; lra.
by exists 7525737178955839%Z; rewrite /F2R /INVLN2 /=; lra.
Qed.

Variables rh rl : R.
Hypothesis rhF : format rh.
Hypothesis rlF : format rl.
Hypothesis rhB : pow (- 970) <= Rabs rh <= 709.79.
Hypothesis rlB : Rabs rl <= Rpower 2 (-14.4187).
Hypothesis rhDrlB : Rabs (rl / rh) <= Rpower 2 (- 23.8899).
Hypothesis rhlB : Rabs (rh + rl) <= 709.79.

Variable choice : Z -> bool.
Definition k := Znearest choice (RND (rh * INVLN2)).

Lemma Znearest_le c r1 r2 : 
  r1 <= r2 -> (Znearest c r1 <= Znearest c r2)%Z.
Proof. by case: (valid_rnd_N c) => H _; exact: H. Qed.

Lemma Znearest_IZR c k : Znearest c (IZR k) = k.
Proof. by case: (valid_rnd_N c) => _ H; exact: H. Qed.

Lemma kB : (Z.abs k <= 4194347)%Z.
Proof.
have F1: Rabs (RND (rh * INVLN2)) <= 4194347.07.
  apply: Rle_trans (_ : Rabs (rh * INVLN2) * (1 + pow (- 52)) <= _).
    apply/Rlt_le/relative_error_FLT_alt => //.
    rewrite Rabs_mult [Rabs INVLN2]Rabs_pos_eq; last by interval.
    apply: Rle_trans (_ : pow (-970) * INVLN2 <= _); first by interval.
    by apply: Rmult_le_compat; try lra; interval.
  apply: Rle_trans (_ : (709.79 * (pow 12/ ln 2 + Rpower 2 (- 43.447))) *
                         (1 + pow (-52)) <= _).
    apply: Rmult_le_compat_r; first by interval.
    boundDMI; first by lra.
    by interval with (i_prec 100).
  by interval.
have [rhi_neg|rhi_pos] := Rle_lt_dec (rh * INVLN2) 0.
  have rrhi_neg : RND (rh * INVLN2) <= 0.
    have <- : RND 0 = 0 by rewrite round_0.
    by apply: round_le.  
  rewrite Z.abs_neq; last first.
    have <- : Znearest choice 0 = 0%Z by rewrite Znearest_IZR.
    by apply: Znearest_le.
  suff: (- 4194347 <= k)%Z by lia.
  have <- : Znearest choice (- 4194347.07) = (- 4194347)%Z.
    by apply: Znearest_imp; interval.
  apply: Znearest_le.
  by clear -F1 rrhi_neg; split_Rabs; lra.
have rrhi_pos : 0 <= RND (rh * INVLN2).
  have <- : RND 0 = 0 by rewrite round_0.
  by apply: round_le; lra.
rewrite Z.abs_eq; last first.
  have <- : Znearest choice 0 = 0%Z by rewrite Znearest_IZR.
  by apply: Znearest_le.
have <- : Znearest choice (4194347.07) = 4194347%Z.
  by apply: Znearest_imp; interval.
apply: Znearest_le.
by clear -F1 rrhi_pos; split_Rabs; lra.
Qed.

Definition D1 :=  IZR k - RND(rh * INVLN2).

Lemma D1_B:  Rabs D1 <= 1 / 2.
Proof.
rewrite /D1 /k.
suff : Rabs (RND (rh * INVLN2) - IZR (Znearest choice (RND (rh * INVLN2))))
                <= / 2.
  by split_Rabs; lra.
by apply: Znearest_half.
Qed.

Definition D2 := RND(rh * INVLN2) - rh * INVLN2.

Lemma D2_B : Rabs D2 <= pow (-30).
Proof.
apply: Rle_trans  (_ : ulp (rh * INVLN2) <= _).
  by apply/error_le_ulp.
have Rrh_pos: 0 < Rabs rh by move: (bpow_gt_0 beta (- 970)); lra.
rewrite ulp_neq_0; last by rewrite /INVLN2; split_Rabs; nra.
have h : Rabs (rh * INVLN2) <= 709.79 *  INVLN2.
  rewrite Rabs_mult.
  by rewrite (Rabs_pos_eq INVLN2); try rewrite /INVLN2;lra.
have : 709.79 * INVLN2 < pow (23).
  by rewrite /INVLN2 ; interval.
rewrite /cexp /fexp Z.max_l => *.
  apply/bpow_le.
  suff: (mag beta (rh * INVLN2) <= 23) %Z by lia.
  apply/mag_le_bpow;  try lra.
  by rewrite /INVLN2; split_Rabs; nra.
suff : (emin + p <=  mag beta (rh * INVLN2))%Z by lia.
apply/mag_ge_bpow.
rewrite Rabs_mult (Rabs_pos_eq INVLN2); try interval.
rewrite /INVLN2.
apply: Rle_trans (_ : pow (-970) <= _); last by lra. 
by apply/bpow_le; lia.
Qed.

Lemma kn2rhrlB: 
   Rabs (IZR k * ln 2 * pow (- 12) - (rh + rl)) <= Rpower 2 (- 12.906174).
Proof.
suff HF : Rabs (IZR k - (rh + rl) * pow 12 / ln 2) <= 0.7698196.
  have -> : IZR k * ln 2 * pow (- 12) - (rh + rl) = 
            (ln 2 * pow (-12)) * (IZR k - (rh + rl) * pow 12 / ln 2).
    have -> : (- 12 = (- (12)))%Z by lia.
    by rewrite bpow_opp; field; split; interval.
  rewrite Rabs_mult.
  apply: Rle_trans (_ : Rabs (ln 2 * pow (-12)) * 0.7698196 <= _).
    by apply: Rmult_le_compat_l => //; interval.
  by interval.
pose D1 := IZR k - RND(rh * INVLN2).
pose D2 := RND(rh * INVLN2) - rh * INVLN2.
pose D3 := (rh + rl) * (INVLN2 - pow 12 / ln 2).
pose D4 := rl * INVLN2.
have -> : IZR k - (rh + rl) * pow 12 / ln 2 = D1 + D2 + D3 - D4.
  by rewrite [_ / ln 2]Rmult_assoc /D1 /D2 /D3 /D4; field; interval.
apply: Rle_trans (_ : 1/2 + pow (-30) + Rpower 2 (- 33.975) + 
                      0.2698195 <= _); last by interval.
boundDMI; [boundDMI; [boundDMI|]|].
- by apply/D1_B.
- by apply/D2_B.
- apply: Rle_trans (_ : 709.79 * Rpower 2 (- 43.447) <= _); last by interval.
  boundDMI; first by lra.
  by interval with (i_prec 70).
rewrite Rabs_Ropp /D4.
apply: Rle_trans (_ : Rpower 2 (- 14.4187) * Rabs INVLN2 <= _).
  by boundDMI; lra.
by rewrite [Rabs INVLN2]Rabs_pos_eq; interval.
Qed.

Lemma  LN2H_2E: LN2H/2 = Float beta 6243314768165359 (- 66).
Proof.   by rewrite /F2R /LN2H /=; lra. Qed.


Lemma format_LN2H_2 : format (LN2H/2).
Proof.
rewrite LN2H_2E; apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.
Lemma mag_LNH2_2:  (mag beta  (LN2H/2) = -13:>Z)%Z.
Proof.
by rewrite (mag_unique_pos _ _ (-13)) //= /LN2H ; lra.
Qed.

Lemma  ulp_LN2H_2: ulp (LN2H/2) =  pow (-66).
Proof.
rewrite ulp_neq_0; last by interval.
congr bpow; rewrite /cexp mag_LNH2_2 /fexp; lia.
Qed.

Lemma pred_LN2H_2: 
    pred beta fexp (LN2H/2)=  Float beta 6243314768165358 (- 66).
Proof.
rewrite pred_eq_pos; try (rewrite /LN2H; lra).
rewrite /pred_pos Req_bool_false.
  by rewrite  ulp_LN2H_2   LN2H_2E /F2R/=;lra.
rewrite  mag_LNH2_2 LN2H_2E /F2R //=;lra.
Qed.

Lemma rhBkln2h_format : format (rh - IZR k * LN2H).
Proof.
have rhBkln2hB : Rabs (rh - IZR k * LN2H) <= omega.
  apply: Rle_trans (_ : Rabs rh + Rabs (IZR k * LN2H) <= _).
    by clear; split_Rabs; lra.
  apply: Rle_trans (_ : Rabs 709.79 + 4194347 * LN2H <= _); 
   last by interval.
  apply: Rplus_le_compat.
    by rewrite [Rabs 709.79]Rabs_pos_eq; lra.
  rewrite Rabs_mult [Rabs LN2H]Rabs_pos_eq; last by interval.
  apply: Rmult_le_compat_r; first by interval.
  by rewrite Rabs_Zabs; apply/IZR_le/kB.
have rhBkln2h_imul_1022: (is_imul (rh - IZR k * LN2H)(pow (- 1022))).
  apply: is_imul_minus.
    have -> : (- 1022 = - 970 - p + 1)%Z by lia.
    apply: is_imul_bound_pow_format => //.
    by rewrite -[bpow _ _]/(pow _); lra.
  apply: is_imul_pow_le (_ : is_imul _ (pow (- 65))) _; last by lia.
  exists (6243314768165359 * k)%Z.
  by rewrite mult_IZR /LN2H /F2R /= /Z.pow_pos /=; lra.
have rhBkln2h_imul : is_imul (rh - IZR k * LN2H) alpha.
  by apply: is_imul_pow_le (_ : is_imul _ (pow (- 1022))) _; last by lia.
have rhBkln2hB13 : Rabs (rh - IZR k * LN2H) <= Rpower 2 (-13.528766).
pose D3' := rh * (INVLN2 -/LN2H).
have D1_B:= D1_B; have D2_B := D2_B.
have E1:  ( IZR k  - rh/ LN2H) = D1 + D2 + D3' by rewrite /D1 /D2 /D3'; lra.
  have ->:  Rabs (rh - IZR k * LN2H) = Rabs (D1 + D2 + D3')* LN2H.
    rewrite -Rabs_Ropp  -{2}(Rabs_pos_eq LN2H); last by rewrite /LN2H;lra.
    by rewrite -Rabs_mult /D1 /D2 /D3'; congr Rabs; field; rewrite /LN2H;lra.
  apply/(Rle_trans _ ((Rabs D1 + Rabs D2 + Rabs D3')* LN2H)).
    apply/Rmult_le_compat_r;  first by rewrite /LN2H; lra.
    apply: Rle_trans (Rabs_triang _ _) _.
    by apply/Rplus_le_compat_r;apply: Rle_trans (Rabs_triang _ _) _ ; lra.
  have h: Rabs  (INVLN2 - / LN2H) < Rpower 2 (-41.694).
    by interval with (i_prec 70).
  have D3'B: Rabs D3' <= Rpower 2 (-32.222).
    rewrite /D3' Rabs_mult.
    apply/(Rle_trans _ ( 709.79 *  Rpower 2 (-41.694))).
      by apply/Rmult_le_compat=>//; try apply/Rabs_pos; lra.
    by interval.
  apply/(Rle_trans _ ((/2 + pow (-30) +  Rpower 2 (-32.222))*LN2H)).
    by apply/Rmult_le_compat_r;  rewrite /LN2H; lra.
  by interval.
case:(Rle_lt_dec (bpow radix2 (-13)) (Rabs rh))=>hrh13.
  have imul_rh65: is_imul rh (pow (-65)).
    have->: (-65 = -13 - 53 + 1)%Z by lia.
    by apply/is_imul_bound_pow_format.    
  case:imul_LN2H => mln2h mE.
  have [m rhkln2E]: is_imul (rh - IZR k * LN2H)  (pow (-65)).
    apply/is_imul_minus=>//.
    by rewrite mE;exists (k * mln2h)%Z; rewrite -Rmult_assoc mult_IZR.
  apply/generic_format_FLT/(FLT_spec _ _ _ _ (Float beta  m (-65))); rewrite /F2R/=.
  +  have ->: IZR (Z.pow_pos 2 65) = bpow beta 65 by [].
     by rewrite -bpow_opp.
  + apply/lt_IZR; have ->: IZR (Z.pow_pos 2 53) = bpow beta 53 by [].
    apply/(Rmult_lt_reg_r (pow (-65))); first by apply/bpow_gt_0.
    rewrite abs_IZR -bpow_plus -(Rabs_pos_eq (pow (-65))); last by apply/bpow_ge_0.
    rewrite -Rabs_mult -rhkln2E; ring_simplify (53 + -65)%Z.
    apply/(Rle_lt_trans _ (Rpower 2 (-13.528766)))=>//.
    by rewrite pow_Rpower; last lia; apply/Rpower_lt; lra.
  by lia.
have  powm1E: pow (-1) = /2  by [].
have rhINVLN2B: Rabs (rh *  INVLN2) < 0.73 by interval.
have u73: ulp (0.73) = pow (-p).
  rewrite ulp_neq_0 /cexp; last lra.
  rewrite (mag_unique_pos  _ _ 0)/fexp.
    by rewrite Z.max_l.
  have->: pow (0 -1) = /2 by [].
  by rewrite -powm1E pow0E; lra.
have ulpk: ulp  (rh * INVLN2) <= pow (-p).
  rewrite -u73; apply/ulp_le.
  by rewrite (Rabs_pos_eq (0.73));lra.
have hRNk: Rabs (RND (rh* INVLN2)) <= 0.75.
  have-> : (RND (rh* INVLN2)) = 
         ((RND (rh* INVLN2)) -  (rh* INVLN2))+
          (rh* INVLN2) by lra.
  apply: Rle_trans (Rabs_triang _ _) _.
  apply/(Rle_trans _   (ulp (rh * INVLN2) + 0.73)).
    apply/Rplus_le_compat.
      by  apply/error_le_ulp.
    by lra.
  apply/(Rle_trans _ (pow (-p) + 0.73)); try lra.
  by interval.
have kB: (-1 <= k <= 1)%Z.
  rewrite /k.
  have h: -0.75 <=  RND(rh * INVLN2) <= 0.75 by split_Rabs;lra.  
  have ->: (-1 =  Znearest choice(-0.75))%Z.
    rewrite (Znearest_imp choice _ (-1)%Z) //.
    by split_Rabs; lra.
  have ->: (1 =  Znearest choice 0.75)%Z.
    rewrite (Znearest_imp choice _ 1%Z) //.
    by split_Rabs; lra.
  by  split; apply/Znearest_le; lra.
have kE: (k = 0)%Z \/ (k = 1)%Z \/ (k = -1)%Z by lia.
case:kE=> [k0 |kE].
  by rewrite k0 Rmult_0_l Rminus_0_r.

have LN2H_2E:  
   round beta fexp Zceil (pred beta fexp (/ 2) * / INVLN2) = 
          LN2H / 2.
  rewrite -powm1E pred_bpow.
  apply/round_UP_eq.
    by apply/format_LN2H_2.
  by rewrite pred_LN2H_2 ; rewrite /INVLN2 /LN2H /F2R /=; lra.

(* k = 1 *)
case:kE=> [k1 |kE].
  rewrite k1 Rmult_1_l.
  case :(Rlt_le_dec rh 0)=>rh0.
    suff: (k <= 0)%Z by lia.
    rewrite /k -(Znearest_IZR  choice 0).
    apply/Znearest_le.
    have-> : 0 = RND 0 by rewrite round_0.
    by apply/round_le; rewrite /INVLN2 ;lra.
  apply/sterbenz=>//.
    by apply/format_LN2H.
  split; last interval.
  case: (Rlt_le_dec (RND (rh * INVLN2)) (/2))=>h.
    suff: (k <= 0)%Z by lia.
    rewrite /k (Znearest_imp _ _ 0); first  lia.
    rewrite Rminus_0_r Rabs_pos_eq //.
    have ->: 0 = RND 0 by rewrite round_0.
    by apply/round_le; rewrite /INVLN2; lra.
  case :(Rle_lt_dec (rh * INVLN2)  (pred beta fexp (/ 2))).
    move=>hle.
    have: RND(rh * INVLN2) <= RND(pred beta fexp (/ 2)) 
      by apply/round_le.
    rewrite (round_generic _ _ _ (pred _ _ _ )).
      move: h;
      have->: /2 = pow (-1) by [].
      rewrite pred_bpow; move:(bpow_gt_0 beta (fexp (-1))).
      by  lra.
    have->: /2 = pow (-1) by [].
    by apply/generic_format_pred/generic_format_bpow;
      rewrite /fexp; lia.
  have h2: 0 </ INVLN2 by interval.
  move/(Rmult_lt_compat_r (/INVLN2) _ _ h2).
  rewrite Rmult_assoc Rinv_r ?Rmult_1_r; last interval.
  move=> h3.
  have: round beta fexp Zceil (pred beta fexp (/ 2) * / INVLN2) <=
    round beta fexp Zceil rh.
    by apply/round_le; lra.
  rewrite (round_generic _ _ _ rh) //; lra.
(* k = -1 *)
case :(Req_dec rh 0)=>[->| rhn0].
  rewrite kE !Rsimp01.
  by apply/generic_format_opp/generic_format_opp/format_LN2H.
have ->: rh - IZR k * LN2H = LN2H - (-rh) by rewrite kE;lra.
apply/sterbenz.
+ by apply/format_LN2H.
+ by apply/generic_format_opp.
split; first by interval.
have rhneg: rh <= 0.
  case:(Rle_lt_dec rh 0)=>//=> rhpos.
  have h : 0 <=(rh * INVLN2) by rewrite /INVLN2; lra.
  have hR : 0 <=  (RND (rh * INVLN2)).
  have ->: 0 = RND 0 by rewrite round_0.
    by apply/round_le.
  suff : (0 <= k)%Z by lia.
  rewrite /k -(Znearest_IZR  choice 0).
  by apply/Znearest_le.
have rhb: - bpow radix2 (-13) < rh.
move: hrh13; rewrite -Rabs_Ropp Rabs_pos_eq /beta; lra.
have hneg:  RND (rh * INVLN2) <= 0.
  have ->: 0 =  RND 0 by rewrite round_0.
  apply/round_le; rewrite /INVLN2; lra.
have h: RND (rh * INVLN2) <= -/2.
  case: (Rle_lt_dec (RND (rh * INVLN2))(-/2))=>//=> h.
  suff: (k = 0)%Z by lia.
  rewrite /k; apply/Znearest_imp.
  by rewrite -Rabs_Ropp Rabs_pos_eq; lra.
have succE: - / 2 + pow (-54)= succ beta fexp (-/2).
    rewrite succ_opp -powm1E pred_bpow  /fexp Z.max_l; last lia.
    by ring_simplify; congr Rplus; congr bpow; lia.
have h4 : rh * INVLN2 < -/2 + pow(-54).

  case:(Rlt_le_dec (rh * INVLN2)  (- / 2 + pow (-54)))=>//h2.
  have:RND (- /2 + pow (-54)) <= RND(rh * INVLN2) by apply/round_le.
  rewrite round_generic; first by  move:(bpow_gt_0 beta (-54)); lra.
  rewrite succE; apply/generic_format_succ/generic_format_opp.
  rewrite -powm1E; apply/generic_format_bpow.
  rewrite /fexp; lia.

have {}h2: (/2 - pow (-54)) /INVLN2 < -rh. 
  apply/(Rmult_lt_reg_r INVLN2); first by interval.
  by rewrite Rmult_assoc Rinv_l ?Rmult_1_r; last interval; lra.
suff: LN2H/2 <= -rh by lra.
rewrite -LN2H_2E.
have->: -rh =  (round beta fexp Zceil (-rh)).
  by rewrite round_generic//; apply/generic_format_opp.
apply/round_le.
rewrite -powm1E pred_bpow.
have ->: (pow (-1) - pow (fexp (-1)))= (/ 2 - pow (-54)).
  by rewrite powm1E /fexp ; congr Rminus; congr bpow; 
     rewrite /fexp; lia.
lra.
Qed.


Definition zh := RND (rh - IZR k * LN2H).

Lemma zhF : format zh.
Proof. by apply: generic_format_round. Qed.

Lemma zhE : zh = rh - IZR k * LN2H.
Proof. by apply/round_generic/rhBkln2h_format. Qed.

Definition zl := RND (rl - IZR k * LN2L).

Lemma zlF : format zl.
Proof. by apply: generic_format_round. Qed.

Lemma zl_err : Rabs (zl - (rl - IZR k * LN2L)) <= pow (- 67).
Proof.
have rlkln2lB : Rabs (rl - IZR k * LN2L) <= Rpower 2 (- 14.418).
  apply: Rle_trans (_ : Rabs rl + Rabs (IZR k * LN2L) <= _).
    by clear; split_Rabs; lra.
  apply: Rle_trans (_ : Rpower 2 (- 14.4187) + 4194347 * LN2L <= _);
     last by interval.
  apply: Rplus_le_compat; first by lra.
  rewrite Rabs_mult [Rabs LN2L]Rabs_pos_eq; last by interval.
  apply: Rmult_le_compat_r; first by interval.
  by rewrite Rabs_Zabs; apply/IZR_le/kB.
apply: Rle_trans (error_le_ulp _ _ _ _) _.
apply: bound_ulp => //.
apply: Rle_lt_trans rlkln2lB _.
by interval.
Qed.

Definition z := RND (zh + zl).

Lemma zF : format z.
Proof. by apply: generic_format_round. Qed.

Lemma zB: Rabs z <= Rpower 2  (- 12.905).
Admitted.

Definition e := (k / 2 ^ 12)%Z.
Definition i1 := ((k - e * 2 ^ 12) / 2 ^ 6)%Z.
Definition ni1 := Z.to_nat i1.
Definition i2 := ((k - e * 2 ^ 12 - i1 * 2 ^ 6))%Z.
Definition ni2 := Z.to_nat i2.

Lemma eE : (k = e * 2 ^ 12 + i1 * 2 ^ 6 + i2)%Z.
Proof.
rewrite /i2 /i1 /e -!Zmod_eq_full; try by lia.
rewrite -Zplus_assoc [(_ * 2 ^ 6)%Z]Z.mul_comm -Z_div_mod_eq_full.
by rewrite [(_ * 2 ^ 12)%Z]Z.mul_comm -Z_div_mod_eq_full.
Qed.

Lemma i1B : (0 <= i1 <= 63)%Z.
Proof.
rewrite /i1 /e -Zmod_eq_full; last by lia.
have km12B : (0 <= k mod (2 ^ 12) < 2 ^12)%Z by apply: Z.mod_pos_bound.
split; first by apply: Z.div_pos; lia.
have -> : (63 = (2 ^ 12 - 1) / 2 ^ 6)%Z by [].
by apply: Z_div_le; lia.
Qed.

Lemma ni1B : (0 <= ni1 <= 63)%N.
Proof.
by apply/andP; split; apply/leP; have := i1B; rewrite /ni1; lia.
Qed.

Lemma INR_ni1E : INR ni1 = IZR i1.
Proof. by rewrite INR_IZR_INZ Z2Nat.id //; have := i1B; lia. Qed. 

Lemma i2B : (0 <= i2 <= 63)%Z.
Proof.
suff : (0 <= i2 < 2 ^ 6)%Z by lia.
rewrite /i2 /i1 /e -Zmod_eq_full; last by lia.
by apply: Z.mod_pos_bound.
Qed.

Lemma ni2B : (0 <= ni2 <= 63)%N.
Proof.
by apply/andP; split; apply/leP; have := i2B; rewrite /ni2; lia.
Qed.

Lemma INR_ni2E : INR ni2 = IZR i2.
Proof. by rewrite INR_IZR_INZ Z2Nat.id //; have := i2B; lia. Qed. 

Definition h1 := (nth (0,0) T2 ni1).1.
Definition e1 := (h1 - Rpower 2 (IZR i1 / pow 12)).

Lemma h1F : format h1.
Proof. by apply: format_T2_h1 => //; case/andP: ni1B. Qed.

Lemma h1B : 1 <= h1 < 2.
Proof. by apply: T2_h1B; case/andP: ni1B. Qed.

Lemma e1B : Rabs e1 <= pow (- 53).
Proof.
by rewrite /e1 -INR_ni1E; apply: T2_e1B; have/andP[] := ni1B.
Qed.

Lemma imul_h1 : is_imul h1 (pow (- 52)).
Proof.
have -> : (- 52 = 0 - p + 1)%Z by lia.
apply: is_imul_bound_pow_format h1F.
by have h1B := h1B; rewrite pow0E Rabs_pos_eq; lra.
Qed.

Definition l1 := (nth (0,0) T2 ni1).2.

Lemma l1F : format l1.
Proof. by apply: format_T2_l1 => //; case/andP: ni1B. Qed.

Lemma l1B : Rabs l1 <= pow (- 53).
Proof.
have [->|l1_neq0] := Req_dec l1 0; first by interval.
suff : pow (- 58) <= Rabs l1 <= pow (- 53) by lra.
by apply: T2_l1B => //; have/andP[] := ni1B.
Qed.

Lemma imul_l1 : is_imul l1 (pow (- 110)).
Proof.
have [->|l1_neq0] := Req_dec l1 0; first by exists 0%Z; lra.
have -> : (- 110 = - 58 - p + 1)%Z by lia.
apply: is_imul_bound_pow_format l1F.
rewrite -[bpow _ _]/(pow _).
suff : pow (- 58) <= Rabs l1 <= pow (- 53) by lra.
by apply: T2_l1B => //; have/andP[] := ni1B.
Qed.

Lemma rel_error_h1l1 : 
  Rabs ((h1 + l1) / Rpower 2 (IZR i1 /pow 12) - 1) < Rpower 2 (- 107.000244).
Proof.
rewrite -INR_ni1E /h1 /l1.
case: nth (@T2_rel_error_h1l1 ni1) => h l /=.
by apply; have/andP[] := ni1B.
Qed.

Definition h2 :=  (nth (0,0) T1 ni2).1.
Definition e2 := (h2 - Rpower 2 (IZR i2 / pow 6)).

Lemma h2F : format h2.
Proof. by apply: format_T1_h2 => //; case/andP: ni2B. Qed.

Lemma h2B : 1 <= h2 < 2.
Proof. by apply: T1_h2B; case/andP: ni2B. Qed.

Lemma h2E : h2 = Rpower 2 (IZR i2 / pow 6) + e2.
Proof. by rewrite /e2; lra. Qed.

Lemma imul_h2 : is_imul h2 (pow (- 52)).
Proof.
have -> : (- 52 = 0 - p + 1)%Z by lia.
apply: is_imul_bound_pow_format h2F.
by have h2B := h2B; rewrite pow0E Rabs_pos_eq; lra.
Qed.

Lemma e2B : Rabs e2 <= pow (- 53).
Proof.
by rewrite /e2 -INR_ni2E; apply: T1_e2B; have/andP[] := ni2B.
Qed.

Definition l2 := (nth (0,0) T1 ni2).2.

Lemma l2F : format l2.
Proof. by apply: format_T1_l2 => //; case/andP: ni2B. Qed.

Lemma l2B : Rabs l2 <= pow (- 53).
Proof.
have [->|l2_neq0] := Req_dec l2 0; first by interval.
suff : Rpower 2 (- 58.98) <= Rabs l2 <= pow (- 53) by lra.
by apply: T1_l2B => //; have/andP[] := ni2B.
Qed.

Lemma rel_error_h2l2 : 
  Rabs ((h2 + l2) / Rpower 2 (IZR i2 /pow 6) - 1) < Rpower 2 (- 107.015625).
Proof.
rewrite -INR_ni2E /h2 /l2.
case: nth (@T1_rel_error_h2l2 ni2) => h l /=.
by apply; have/andP[] := ni2B.
Qed.

Lemma imul_l2 : is_imul l2 (pow (- 111)).
Proof.
have [->|l2_neq0] := Req_dec l2 0; first by exists 0%Z; lra.
have -> : (- 111 = - 59 - p + 1)%Z by lia.
apply: is_imul_bound_pow_format l2F.
apply: Rle_trans (_ : Rpower 2 (- 58.98) <= _); first by interval.
suff : Rpower 2 (- 58.98) <= Rabs l2 <= pow (- 53) by lra.
by apply: T1_l2B => //; have/andP[] := ni2B.
Qed.

Lemma imul_h1h2 : is_imul (h1 * h2) (pow (- 104)).
Proof.
have -> : pow (- 104) = pow (- 52) * pow (- 52) by rewrite -bpow_plus.
  by apply: is_imul_mul imul_h1 imul_h2.
Qed.

Lemma h1B1 : h1 <= Rpower 2 (0.015381).
Proof. by apply: T2_h1B1; case/andP : ni1B. Qed.

Lemma h2B1 : h2 <= Rpower 2 (0.984376).
Proof. by apply: T1_h2B1; case/andP : ni2B.
Qed.

Lemma h1h2B1 : h1 * h2 <= Rpower 2 0.999757.
Proof.
have <- : 0.015381 + 0.984376 = 0.999757 by lra.
rewrite Rpower_plus.
apply: Rmult_le_compat h1B1 h2B1; first by have := h1B; lra.
by have := h2B; lra.
Qed.

Lemma h1h2B : 1 <= h1 * h2 < 2.
Proof.
split; first by have := h1B; have := h2B; nra.
by apply: Rle_lt_trans h1h2B1 _; interval.
Qed.

Definition ph := let 'DWR ph _ := exactMul h1 h2 in ph.

Lemma phE : ph = RND (h1 * h2).
Proof. by []. Qed.

Lemma imul_ph : is_imul ph (pow (- 104)).
Proof. by rewrite phE; apply: is_imul_pow_round imul_h1h2. Qed.

Definition s := let 'DWR _ s := exactMul h1 h2 in s.

Lemma sE : s = h1 * h2 - ph.
Proof.
have [h1F h2F] := (h1F, h2F).
have -> : s = RND (h1 * h2 - ph) by [].
apply: round_generic.
have -> : h1 * h2 - ph = - (ph - h1 * h2) by lra.
apply: generic_format_opp.
apply: format_err_mul => //.
apply: is_imul_pow_le (_ : _ <= (- 52) + (- 52))%Z => //.
rewrite bpow_plus.
by apply: is_imul_mul imul_h1 imul_h2.
Qed.

Lemma sB : Rabs s <= pow (- 52).
Proof.
apply: Rle_trans (_ : ulp (h1 * h2) <= _).
have -> : Rabs s = Rabs (ph - h1 * h2) by rewrite sE; split_Rabs; lra.
apply: error_le_ulp.
apply: bound_ulp => //.
rewrite -[bpow _ _]/2.
by have := h1h2B; split_Rabs; lra.
Qed.

Lemma imul_s : is_imul s (pow (- 104)).
Proof. by rewrite sE; apply: is_imul_minus imul_h1h2 imul_ph. Qed.

Lemma imul_l1h2s : is_imul (l1 * h2 + s) (pow (- 162)).
Proof.
apply: is_imul_add.
  have -> : pow (- 162) = pow (- 110) * pow (- 52) by rewrite -bpow_plus.
  by apply: is_imul_mul imul_l1 imul_h2.
by apply: is_imul_pow_le imul_s _.
Qed.

Definition t := RND (l1 * h2 + s).

Lemma imul_t : is_imul t (pow (- 162)).
Proof. by apply: is_imul_pow_round imul_l1h2s. Qed.

Lemma l1h2sB : Rabs (l1 * h2 + s) <= Rpower 2 (-51.007).
Proof.
apply: Rle_trans (_ : pow (- 53) * Rpower 2 0.984376 + pow (- 52) <= _);
    last by interval.
boundDMI; last by apply: sB.
boundDMI; first by apply: l1B.
rewrite Rabs_pos_eq; first by apply: h2B1.
have := h2B; lra.
Qed.

Lemma tB : Rabs t < Rpower 2 (- 51.00699).
Proof.
apply: Rle_lt_trans (_ : Rpower 2 (- 51.007) + pow (- 104) < _);
    last by interval.
apply: Rle_trans (_ : Rabs (l1 * h2 + s) + ulp (l1 * h2 + s) <= _).
  by apply: error_le_ulp_add.
apply: Rplus_le_compat l1h2sB _.
apply: bound_ulp => //.
by apply: Rle_lt_trans l1h2sB _; interval.
Qed.

Definition pl := RND (h1 * l2 + t).

Lemma imul_l2h1t : is_imul (h1 * l2 + t) (pow (- 163)).
Proof.
apply: is_imul_add.
  have -> : pow (- 163) = pow (- 52) * pow (- 111) by rewrite -bpow_plus.
  by apply: is_imul_mul imul_h1 imul_l2.
by apply: is_imul_pow_le imul_t _.
Qed.

Lemma imul_pl : is_imul pl (pow (- 163)).
Proof. by apply: is_imul_pow_round imul_l2h1t. Qed.

Lemma h1l2tB : Rabs (h1 * l2 + t) <= Rpower 2 (- 50.6805).
Proof.
apply: Rle_trans (_ : Rpower 2 0.015381  * pow (- 53) + Rpower 2 (- 51.00699) 
           <= _);
    last by interval.
boundDMI; last by apply/Rlt_le/tB.
boundDMI; last by apply: l2B.
rewrite Rabs_pos_eq; first by apply: h1B1.
have := h1B; lra.
Qed.

Lemma plB : Rabs pl < Rpower 2 (- 50.680499).
Proof.
apply: Rle_lt_trans (_ : Rpower 2 (- 50.6805) + pow (- 103) < _);
    last by interval.
apply: Rle_trans (_ : Rabs (h1 * l2 + t) + ulp (h1 * l2 + t) <= _).
  by apply: error_le_ulp_add.
apply: Rplus_le_compat h1l2tB _.
apply: bound_ulp => //.
by apply: Rle_lt_trans h1l2tB _; interval.
Qed.

Lemma phplB : 1 <= ph + pl < 2.
Proof.
suff : 1 <= ph + pl.
  split; first by lra.
  apply: Rle_lt_trans (_ : Rpower 2 0.999757 * (1 + pow (- 52)) +
                           Rpower 2 (- 50.680499) < _); last by interval.
  rewrite -[ph + pl]Rabs_pos_eq; last by lra.
  boundDMI; last by apply/Rlt_le/plB.
  apply: Rle_trans (_ : Rabs (h1 * h2) * (1 + pow (- 52)) <= _).
    apply: relative_error_eps_ge => //.
    by apply: is_imul_pow_le imul_h1h2 _.
  apply: Rmult_le_compat_r; first by interval.
  rewrite Rabs_pos_eq; last by have := h1h2B; lra.
  by apply: h1h2B1.
have [i1eq0|i1ne0] := Z.eq_dec i1 0.
  have h1E: h1 = 1 by rewrite /h1 /ni1 i1eq0.
  have [i2eq0|i2ne0] := Z.eq_dec i2 0.
    have h2E: h2 = 1 by rewrite /h2 /ni2 i2eq0.
    rewrite /pl /t sE phE h1E h2E !Rsimp01.
    rewrite /l1 /l2 /ni1 /ni2 i1eq0 i2eq0 /= !Rsimp01.
    suff -> : RND 1 = 1 by rewrite !Rsimp01 !round_0; lra.
    by apply: round_generic; apply: format1.
  have h2B : Rpower 2 (1 / 2 ^ 6) * (1 - pow (- 53)) <= h2.
    apply: T1_h2B2.
    have := ni2B; suff: ni2 <> 0%N by case : ni2.
    by have := i2B; rewrite /ni2; lia.
  apply: Rle_trans (_ : 1.0001 - Rpower 2 (- 50.680499) <= _); 
     first by interval.
  apply: Rle_trans (_ : ph - Rabs pl <= _); last by split_Rabs; lra.
  suff : 1.0001 <= ph by have := plB; lra.
  rewrite phE h1E Rsimp01 -[RND h2]Rabs_pos_eq; last first.
    have <- : RND 0 = 0 by apply: round_0.
    by apply: round_le; interval.
  apply: Rle_trans (_ : Rabs (h2) * (1 - pow (-52)) <= _).
    rewrite Rabs_pos_eq; first by interval.
    by apply: Rle_trans h2B; interval.
  apply: relative_error_eps_le => //.
  by apply: is_imul_pow_le imul_h2 _.
have h1B1 : Rpower 2 (1 / 2 ^ 12) * (1 - pow (- 53)) <= h1.
  apply: T2_h1B2.
  have := ni1B; suff: ni1 <> 0%N by case : ni1.
  by have := i1B; rewrite /ni1; lia.
apply: Rle_trans (_ : 1.0001 - Rpower 2 (- 50.680499) <= _); 
    first by interval.
apply: Rle_trans (_ : ph - Rabs pl <= _); last by split_Rabs; lra.
suff : 1.0001 <= ph by have := plB; lra.
rewrite phE -[RND _]Rabs_pos_eq; last first.
  have <- : RND 0 = 0 by apply: round_0.
    by apply: round_le; have := h1B; have := h2B; nra.
  apply: Rle_trans (_ : Rabs (h1 * h2) * (1 - pow (-52)) <= _).
  by have h2B := h2B; interval.
apply: relative_error_eps_le => //.
by apply: is_imul_pow_le imul_h1h2 _.
Qed. 

Lemma phplh1l1h2l2B :
  Rabs (ph + pl - (h1 + l1) * (h2 + l2)) <= Rpower 2 (- 102.299).
Proof.
pose e1 := ph - h1 * h2.
have phE1 : ph = h1 * h2 + e1 by rewrite /e1; lra.
pose e3 := pl - (h1 * l2 + t).
have plE1 : pl = h1 * l2 + t + e3 by rewrite /e3; lra.
pose e2 := t - (l1 * h2 + s).
have tE : t = l1 * h2 - e1 + e2 by rewrite /e2 /t sE /e1; lra.
have -> : ph + pl - (h1 + l1) * (h2 + l2) = e2 + e3 - l1 * l2.
    by rewrite /e2 /e3 sE /t; lra.
apply: Rle_trans (_ :
    pow (- 104) + pow (- 103) + pow (- 53) * pow (- 53) <= _);
    last by interval.
boundDMI; last first.
  rewrite Rabs_Ropp; boundDMI; first by apply: l1B.
  by apply: l2B.
boundDMI.
  apply: Rle_trans (_ : ulp (l1 * h2 + s) <= _).
    by apply: error_le_ulp.
  apply: bound_ulp => //.
  by apply: Rle_lt_trans l1h2sB _; interval.
apply: Rle_trans (_ : ulp (h1 * l2 + t) <= _).
  by apply: error_le_ulp.
apply: bound_ulp => //.
by apply: Rle_lt_trans h1l2tB _; interval.
Qed.

Lemma rel_error_phpl : 
  Rabs ((ph + pl) / ((h1 + l1) * (h2 + l2)) - 1) <= Rpower 2 (- 102.314869).
Proof.
have [i1eq0|i1ne0] := Z.eq_dec i1 0.
  have h1E : h1 = 1 by rewrite /h1 /ni1 i1eq0.
  have l1E : l1 = 0 by rewrite /l1 /ni1 i1eq0.
  have phE : ph = h2.
    by rewrite phE h1E Rsimp01; apply: round_generic h2F.
  have sE : s = 0 by rewrite sE phE h1E; lra.
  have tE : t = 0.
    by rewrite /t l1E sE !Rsimp01; apply: round_0.
  rewrite /pl phE h1E l1E tE !Rsimp01 round_generic; last by apply: l2F.
  have -> : (h2 + l2) / (h2 + l2) - 1 = 0.
    by field; have [Hx Hy] := (h2B, l2B); interval.
  by interval.
have [i2eq0|i2ne0] := Z.eq_dec i2 0.
  have h2E : h2 = 1 by rewrite /h2 /ni2 i2eq0.
  have l2E : l2 = 0 by rewrite /l2 /ni2 i2eq0.
  have phE : ph = h1.
    by rewrite phE h2E Rsimp01; apply: round_generic h1F.
  have sE : s = 0 by rewrite sE phE h2E; lra.
  have tE : t = l1.
    by rewrite /t h2E sE !Rsimp01; apply: round_generic l1F.
  rewrite /pl phE h2E l2E tE !Rsimp01 round_generic; last by apply: l1F.
  have -> : (h1 + l1) / (h1 + l1) - 1 = 0.
    by field; have [Hx Hy] := (h1B, l1B); interval.
  by interval.
suff h1l1h2l2B : 1.0110603 < (h1 + l1) * (h2 + l2).
  have -> : (ph + pl) / ((h1 + l1) * (h2 + l2)) - 1 = 
            ((ph + pl) - (h1 + l1) * (h2 + l2)) /
             ((h1 + l1) * (h2 + l2)).
    field.
    have [[[Hx Hy] Hz] Ht]:= (h2B, l2B, h1B, l1B).
    by split; interval.
  rewrite Rabs_mult Rabs_inv.
  rewrite [Rabs (_ * _)]Rabs_pos_eq; last by lra.
  apply: Rle_trans (_ : Rpower 2 (-102.299) / 1.0110603 <= _);
    last by interval.
  apply: Rmult_le_compat.
  - apply: Rabs_pos.
  - by set xx := _ * _ in h1l1h2l2B *; interval.
  - by apply: phplh1l1h2l2B.
  apply: Rinv_le; first by lra.
  by lra.
have h2B : Rpower 2 (1 / 2 ^ 6) * (1 - pow (- 53)) <= h2.
  apply: T1_h2B2.
  have := ni2B; suff: ni2 <> 0%N by case : ni2.
  by have := i2B; rewrite /ni2; lia.
have h1B1 : Rpower 2 (1 / 2 ^ 12) * (1 - pow (- 53)) <= h1.
  apply: T2_h1B2.
  have := ni1B; suff: ni1 <> 0%N by case : ni1.
  by have := i1B; rewrite /ni1; lia.
have l1B := l1B; have l2B := l2B.
apply: Rlt_le_trans (_ : (h1 - Rabs l1) * (h2 - Rabs l2) <= _); last first.
  apply: Rmult_le_compat; try by interval.
    by clear; split_Rabs; lra.
  by clear; split_Rabs; lra.
by interval.
Qed.

End algoExp1.

