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

Section Prelim.

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
Local Notation exactMul := (exactMul beta emin p rnd).
Local Notation fastSum := (fastSum beta emin p rnd).
Local Notation q1 := (q1 rnd).

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Local Notation ulp := (ulp beta fexp).

Definition INVLN2 := 0x1.71547652b82fep+12.

Lemma INVLN2F : format INVLN2.
Proof.
have -> : INVLN2 = Float beta 6497320848556798 (- 40).
  by rewrite /F2R /INVLN2 /=; lra.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma INVLN2B : Rabs (INVLN2 - pow 12 / ln 2) < Rpower 2 (- 43.447).
Proof. by interval with (i_prec 70). Qed. 

Definition LN2H := 0x1.62e42fefa39efp-13.

Lemma LN2HF : format LN2H.
Proof.
have -> : LN2H = Float beta 6243314768165359 (- 65).
  by rewrite /F2R /LN2H /=; lra.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Definition LN2L := 0x1.abc9e3b39803fp-68.

Lemma LN2LF : format LN2L.
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
    by apply: round_le_r => //; apply: generic_format_0.
  rewrite Z.abs_neq; last first.
    have <- : Znearest choice 0 = 0%Z by rewrite Znearest_IZR.
    by apply: Znearest_le.
  suff: (- 4194347 <= k)%Z by lia.
  have <- : Znearest choice (- 4194347.07) = (- 4194347)%Z.
    by apply: Znearest_imp; interval.
  apply: Znearest_le.
  by clear -F1 rrhi_neg; split_Rabs; lra.
have rrhi_pos : 0 <= RND (rh * INVLN2).
  by apply: round_le_l; [apply: generic_format_0 | lra].
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

Lemma LN2H_2F : format (LN2H/2).
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


Fact  rhBkln2hB13: Rabs (rh - IZR k * LN2H) <= Rpower 2 (-13.528766).
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
    apply: is_imul_bound_pow_format rhF => //.
    by rewrite -[bpow _ _]/(pow _); lra.
  apply: is_imul_pow_le (_ : is_imul _ (pow (- 65))) _; last by lia.
  exists (6243314768165359 * k)%Z.
  by rewrite mult_IZR /LN2H /F2R /= /Z.pow_pos /=; lra.
have rhBkln2h_imul : is_imul (rh - IZR k * LN2H) alpha.
  by apply: is_imul_pow_le (_ : is_imul _ (pow (- 1022))) _; last by lia.
have rhBkln2hB13 := rhBkln2hB13.
case:(Rle_lt_dec (bpow radix2 (-13)) (Rabs rh))=>hrh13.
  have imul_rh65 : is_imul rh (pow (-65)).
    have->: (-65 = -13 - 53 + 1)%Z by lia.
    by apply: (is_imul_bound_pow_format _ rhF).    
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
    by rewrite pow_Rpower; apply/Rpower_lt; lra.
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
    by apply/LN2H_2F.
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
    by apply/LN2HF.
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
  by apply/generic_format_opp/generic_format_opp/LN2HF.
have ->: rh - IZR k * LN2H = LN2H - (-rh) by rewrite kE;lra.
apply/sterbenz.
+ by apply/LN2HF.
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

Fact rlkln2lB : Rabs (rl - IZR k * LN2L) <= Rpower 2 (- 14.418).
  apply: Rle_trans (_ : Rabs rl + Rabs (IZR k * LN2L) <= _).
    by clear; split_Rabs; lra.
  apply: Rle_trans (_ : Rpower 2 (- 14.4187) + 4194347 * LN2L <= _);
     last by interval.
  apply: Rplus_le_compat; first by lra.
  rewrite Rabs_mult [Rabs LN2L]Rabs_pos_eq; last by interval.
  apply: Rmult_le_compat_r; first by interval.
  by rewrite Rabs_Zabs; apply/IZR_le/kB.
Qed.


Lemma zl_err : Rabs (zl - (rl - IZR k * LN2L)) <= pow (- 67).
Proof.
have rlkln2lB := rlkln2lB.
apply: Rle_trans (error_le_ulp _ _ _ _) _.
apply: bound_ulp_FLT => //.
apply: Rle_lt_trans rlkln2lB _.
by interval.
Qed.


Definition z := RND (zh + zl).

Lemma zF : format z.
Proof. by apply: generic_format_round. Qed.

Lemma zrhrlk2B : 
  Rabs (z - (rh + rl - IZR k * ln 2 * pow (-12))) < Rpower 2 (-64.67807).
Proof.
have h1: Rabs(zh + zl)  <=  Rpower 2 (- 12.9059). 
  apply/(Rle_trans _ (Rpower 2 (-13.528766) + Rpower 2 (-14.418) + pow (- 67))); 
    last by interval.
  rewrite Rplus_assoc; boundDMI; first by rewrite zhE; apply/rhBkln2hB13.
  have->:(zl = ( (rl - IZR k * LN2L) + (zl - (rl - IZR k * LN2L)))) by lra.
  by boundDMI;[apply/rlkln2lB|apply/zl_err].
have ulpz: ulp (zh + zl) <= pow (-65).
  have ->: pow (-65) = ulp( Rpower 2 (- 12.9059)).
    rewrite ulp_neq_0 /cexp /fexp; last interval.
    congr bpow; rewrite (mag_unique_pos _ _ (-12)); first lia.
    by rewrite !pow_Rpower; try lia; split;interval.
  apply/ulp_le; rewrite (Rabs_pos_eq (Rpower _ _)) //.
  by apply/Rlt_le/exp_pos.
apply/(Rle_lt_trans _ ( pow (-65) + pow (-67) + Rpower 2(-100.429))); 
      last by interval.
have->:  (z - (rh + rl - IZR k * ln 2 * pow (-12))) = 
          (z - (zh + zl)) + (zl - (rl - IZR k * LN2L)) -
          (IZR k * (LN2H + LN2L) - IZR k * ln 2 * pow (-12)).
  by rewrite zhE; lra.
boundDMI.
  boundDMI.
    apply/(Rle_trans _  (ulp (zh + zl)))=>//.
    by apply/error_le_ulp.
  by apply/zl_err.
rewrite Rabs_Ropp Rmult_assoc -Rmult_minus_distr_l.
apply/(Rle_trans _ ( 4194347 * Rpower 2 (-122.43 ))); last interval.
rewrite Rabs_mult; apply/Rmult_le_compat; try apply/Rabs_pos.
  by rewrite -abs_IZR; apply/IZR_le/kB.
apply/Rlt_le/LN2HLB.
Qed.

Lemma zB: Rabs z <= Rpower 2  (- 12.905).
Proof.
apply/(Rle_trans _ (Rpower 2 (-64.67806) + Rpower 2 (-12.906174))); last interval.
have->: z = z - (rh + rl - IZR k * (ln 2) * pow(-12))+ 
                 (rh + rl - IZR k* ln 2 * pow (-12)) by lra.
boundDMI; last by rewrite -Rabs_Ropp Ropp_minus_distr; apply/kn2rhrlB.
by apply: Rlt_le; apply: Rlt_le_trans zrhrlk2B _; interval.
Qed.

Lemma expzB : 
  Rabs (exp (rh + rl) / (Rpower 2 (IZR k / pow 12) * exp z) - 1) <= 
    Rpower 2 (-64.67806).
Proof.
pose eps := rh + rl - (IZR k * ln 2 * pow (- 12) + z).
have rhrlE : rh + rl = IZR k * ln 2 * pow (- 12) + z + eps.
  by rewrite /eps; lra.
have epsB : Rabs eps <= Rpower 2 (- 64.67807).
  rewrite -Rabs_Ropp.
  have -> : - eps = z - (rh + rl - IZR k * ln 2 * pow (-12)).
    by rewrite /eps; lra.
  by apply/Rlt_le/zrhrlk2B.
have erhrlE : exp (rh + rl) = 
   Rpower 2 (IZR k / pow 12) * exp z * exp eps.
  rewrite rhrlE 2!exp_plus.
  congr (exp _ * _ * _).
  have -> : (-12 = - (12))%Z by [].
  by rewrite bpow_opp; lra.
have -> : exp (rh + rl) / (Rpower 2 (IZR k / pow 12) * exp z) = exp eps.
  rewrite erhrlE.
  field; split.
    suff : 0 < exp z by lra.
    by apply: exp_pos.
  suff : 0 < Rpower 2 (IZR k / pow 12)  by lra.
  by apply: exp_pos.
by interval with (i_prec 100).
Qed.

Definition e := (k / 2 ^ 12)%Z.
Definition i2 := ((k - e * 2 ^ 12) / 2 ^ 6)%Z.
Definition ni2 := Z.to_nat i2.
Definition i1 := ((k - e * 2 ^ 12 - i2 * 2 ^ 6))%Z.
Definition ni1 := Z.to_nat i1.

Lemma kE : (k = e * 2 ^ 12 + i2 * 2 ^ 6 + i1)%Z.
Proof.
rewrite /i1 /i2 /e -!Zmod_eq_full; try by lia.
rewrite -Zplus_assoc [(_ * 2 ^ 6)%Z]Z.mul_comm -Z_div_mod_eq_full.
by rewrite [(_ * 2 ^ 12)%Z]Z.mul_comm -Z_div_mod_eq_full.
Qed.

Lemma i2B : (0 <= i2 <= 63)%Z.
Proof.
rewrite /i2 /e -Zmod_eq_full; last by lia.
have km12B : (0 <= k mod (2 ^ 12) < 2 ^12)%Z by apply: Z.mod_pos_bound.
split; first by apply: Z.div_pos; lia.
have -> : (63 = (2 ^ 12 - 1) / 2 ^ 6)%Z by [].
by apply: Z_div_le; lia.
Qed.

Lemma ni2B : (0 <= ni2 <= 63)%N.
Proof.
by apply/andP; split; apply/leP; have := i2B; rewrite /ni2; lia.
Qed.

Lemma INR_ni2E : INR ni2 = IZR i2.
Proof. by rewrite INR_IZR_INZ Z2Nat.id //; have := i2B; lia. Qed. 

Lemma i1B : (0 <= i1 <= 63)%Z.
Proof.
suff : (0 <= i1 < 2 ^ 6)%Z by lia.
rewrite /i1 /i2 /e -Zmod_eq_full; last by lia.
by apply: Z.mod_pos_bound.
Qed.

Lemma ni1B : (0 <= ni1 <= 63)%N.
Proof.
by apply/andP; split; apply/leP; have := i1B; rewrite /ni1; lia.
Qed.

Lemma INR_ni1E : INR ni1 = IZR i1.
Proof. by rewrite INR_IZR_INZ Z2Nat.id //; have := i1B; lia. Qed. 

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
  Rabs ((h1 + l1) / Rpower 2 (IZR i1 /pow 12) - 1) < Rpower 2 (- 107.0228).
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
  Rabs ((h2 + l2) / Rpower 2 (IZR i2 /pow 6) - 1) < Rpower 2 (- 107.57149).
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

Lemma phF : format ph.
Proof. by apply: generic_format_round. Qed.

Lemma phE : ph = RND (h1 * h2).
Proof. by []. Qed.

Lemma phB : 1 <= ph <= 2.
Proof.
split.
  apply: round_le_l => //; first by apply: format1_FLT.
  by have := h1h2B; lra.
apply: round_le_r.
  have <- : pow 1 = 2 by rewrite pow1E.
  by apply: generic_format_bpow.
by have := h1h2B; lra.
Qed.

Lemma imul_ph : is_imul ph (pow (- 52)).
Proof.
have -> : (- 52 = 0 - 53 + 1)%Z by lia.
apply: is_imul_bound_pow_format => //.
  by rewrite pow0E; have := phB; clear; split_Rabs; lra.
by apply: phF.
Qed.

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
apply: bound_ulp_FLT => //.
rewrite -[bpow _ _]/2.
by have := h1h2B; split_Rabs; lra.
Qed.

Lemma imul_s : is_imul s (pow (- 104)).
Proof. 
rewrite sE; apply: is_imul_minus imul_h1h2 _.
by apply: is_imul_pow_le imul_ph _.
Qed.

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
apply: bound_ulp_FLT => //.
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
apply: bound_ulp_FLT => //.
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
    by apply: round_generic; apply: format1_FLT.
  have h2B : Rpower 2 (1 / 2 ^ 6) * (1 - pow (- 53)) <= h2.
    apply: T1_h2B2.
    have := ni2B; suff: ni2 <> 0%N by case : ni2.
    by have := i2B; rewrite /ni2; lia.
  apply: Rle_trans (_ : 1.0001 - Rpower 2 (- 50.680499) <= _); 
     first by interval.
  apply: Rle_trans (_ : ph - Rabs pl <= _); last by split_Rabs; lra.
  suff : 1.0001 <= ph by have := plB; lra.
  rewrite phE h1E Rsimp01 -[RND h2]Rabs_pos_eq; last first.
    apply: round_le_l; first by apply: generic_format_0.
    by interval.
  apply: Rle_trans (_ : Rabs (h2) * (1 - pow (-52)) <= _).
    rewrite Rabs_pos_eq; first by interval.
    by apply: Rle_trans h2B; interval.
  apply: (relative_error_eps_le Hp2) => //.
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
  apply: round_le_l; first by apply: generic_format_0.
  have := h1B; have := h2B; nra.
apply: Rle_trans (_ : Rabs (h1 * h2) * (1 - pow (-52)) <= _).
  by have h2B := h2B; interval.
apply: (relative_error_eps_le Hp2) => //.
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
  apply: bound_ulp_FLT => //.
  by apply: Rle_lt_trans l1h2sB _; interval.
apply: Rle_trans (_ : ulp (h1 * l2 + t) <= _).
  by apply: error_le_ulp.
apply: bound_ulp_FLT => //.
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

Lemma rel_error_phpl_i1i2 : 
  Rabs ((ph + pl) / (Rpower 2 (IZR i2 / pow 6 + IZR i1 / pow 12)) - 1) <= 
  Rpower 2 (- 102.2248).
Proof.
have aI x y : 0 <= x -> 1 - x <= y <= 1 + x -> Rabs (y - 1) <= x.
  by move=> xP yB; split_Rabs; lra.
have bI x y : Rabs (y - 1) <= x -> 1 - x <= y <= 1 + x.
  by move=> xB; split_Rabs; lra.
have -> :  (ph + pl) / (Rpower 2 (IZR i2 / pow 6 + IZR i1 / pow 12)) = 
    ((ph + pl) / ((h1 + l1) * (h2 + l2))) * 
    ((h2 + l2) / Rpower 2 (IZR i2 /pow 6)) *
    ((h1 + l1) / Rpower 2 (IZR i1 /pow 12)).
  rewrite Rpower_plus.
  field.
  split.
    suff : 0 < Rpower 2 (IZR i1 / pow 12) by lra.
    by apply: exp_pos.
  split.
    suff : 0 < Rpower 2 (IZR i2 / pow 6) by lra.
    by apply: exp_pos.
  split.
    suff : 0 < h2 - Rabs l2 by clear; split_Rabs; lra.
    by have [Hx Hy]:= (h2B, l2B); interval with (i_prec 100).
  suff : 0 < h1 - Rabs l1 by clear; split_Rabs; lra.
  by have [Hx Hy] := (h1B, l1B); interval with (i_prec 100).
have := rel_error_phpl; set xx := (_ / _) => /bI Hxx.
have := rel_error_h2l2; set yy := (_ / _) =>  /Rlt_le /bI Hyy.
have := rel_error_h1l1; set zz := (_ / _) => /Rlt_le /bI Hzz.
apply: aI; first by apply/Rlt_le/exp_pos.
interval with (i_prec 200).
Qed.

Definition qh := let 'DWR qh _ := q1 z in qh.

Lemma qhF : format qh.
Proof. by apply: generic_format_round. Qed.

Definition ql := let 'DWR _ ql := q1 z in ql.

Lemma qlF : format ql.
Proof. by apply: generic_format_round. Qed.

Definition h := RND (ph * qh).

Lemma hF : format h.
Proof. by apply: generic_format_round. Qed.

Definition s' := RND (ph * qh - h).

Lemma s'F : format s'.
Proof. by apply: generic_format_round. Qed.

Definition t' := RND (pl * qh + s').

Lemma t'F : format t'.
Proof. by apply: generic_format_round. Qed.

Definition l := RND (ph * ql + t').

Lemma lF : format l.
Proof. by apply: generic_format_round. Qed.

Lemma qlB : Rabs ql <= Rpower 2 (- 51.999).
Proof.
rewrite /ql.
by case: q1 (@err_lem6 (refl_equal _) _ valid_rnd z zF) => h l /(_ zB); lra.
Qed.

Lemma qhqlB : Rabs ((qh + ql) / exp z - 1) < Rpower 2 (- 64.902632).
Proof.
rewrite /qh /ql.
by case: q1 (@err_lem6 (refl_equal _) _ valid_rnd z zF) => h l /(_ zB); lra.
Qed.

Lemma qhB : 0.99986 <= qh <= 1.000131.
Proof.
have zB := zB.
have qlB := qlB.
pose d := (qh + ql) / exp z - 1.
have qhE : qh = exp z * (1 + d) - ql.
  rewrite /d; field.
  suff : 0 < exp z by lra.
  by apply: exp_pos.
have dB : Rabs d <= Rpower 2 (- 64.902632).
  by apply/Rlt_le/qhqlB.
by rewrite qhE; split; interval.
Qed.

Lemma imul_qh : is_imul qh (pow (- 53)).
Proof.
have -> : (- 53 = -1 - 53 + 1)%Z by lia.
apply: is_imul_bound_pow_format.
  by rewrite powN1; have := qhB; split_Rabs; lra.
by apply: qhF.
Qed.

Lemma imul_phqh : is_imul (ph * qh) (pow (- 105)).
Proof.
have -> : (- 105 = - 52 + - 53)%Z by lia.
rewrite bpow_plus; apply: is_imul_mul; first by apply: imul_ph.
by apply: imul_qh.
Qed.

Lemma imul_h : is_imul h (pow (- 105)).
Proof.
apply: is_imul_pow_round.
by apply: imul_phqh.
Qed.

Lemma phqhhF : format (ph * qh - h).
Proof.
have -> : ph * qh - h = - (h - ph * qh) by lra.
apply/generic_format_opp/format_err_mul => //; first by apply: phF.
  by apply: qhF.
by apply: is_imul_pow_le imul_phqh _.
Qed.

Lemma s'E : s' = ph * qh - h.
Proof. by apply: round_generic phqhhF. Qed.

Lemma imul_s' : is_imul s' (pow (- 105)).
Proof.
rewrite s'E; apply: is_imul_minus; last by apply: imul_h.
by apply: imul_phqh.
Qed.

Lemma phqhB : ph * qh < 2.
Proof.
have h1h2_pos : 0 <= h1 * h2 by have := h1h2B; lra.
apply: Rle_lt_trans (_ : h1 * h2 * (1 + pow (- 52)) * qh < _).
  apply: Rmult_le_compat_r; first by have := qhB; lra.
  rewrite phE -{2}[h1 * h2]Rabs_pos_eq // -[RND _]Rabs_pos_eq; last first.
    by apply: round_le_l => //; apply: generic_format_0.
  apply: relative_error_eps_ge => //.
  by apply: is_imul_pow_le imul_h1h2 _.
apply: Rle_lt_trans 
       (_ : Rpower 2 (0.999757) * (1 + pow (- 52)) *  1.000131 < _); 
       last by interval.
apply: Rmult_le_compat.
- suff : 0 <= 1 + pow (-52) by nra.
  by interval.
- by have := qhB; lra.
- apply: Rmult_le_compat_r; first by interval.
  by apply: h1h2B1.
by have := qhB; lra.
Qed.

Lemma hB : 0.999859 <= h <= 2.
Proof.
split.
  apply: Rle_trans (_ : (1 * 0.99986) * (1 - pow (- 52)) <= _); 
     first by interval.
  apply: Rle_trans (_ : Rabs (ph * qh) * (1 - pow (-52)) <= _).
    apply: Rmult_le_compat_r; first by interval.
    rewrite Rabs_mult.
    apply: Rmult_le_compat; try by lra.
      by have := phB; split_Rabs; lra.
    by have := qhB; split_Rabs; lra.
  rewrite -[h]Rabs_pos_eq; last first.
    apply: round_le_l; first by apply: generic_format_0.
    by have := phB; have := qhB; nra.
  apply: (relative_error_eps_le Hp2) => //.
  by apply: is_imul_pow_le imul_phqh _.
apply: round_le_r.
  by rewrite -(pow1E beta); apply: generic_format_bpow.
by apply/Rlt_le/phqhB.
Qed.

Lemma s'B : Rabs s' <= pow (- 52).
Proof.
apply: Rle_trans (_ : ulp (ph * qh) <= _).
  rewrite s'E -Rabs_Ropp Ropp_minus_distr.
  by apply: error_le_ulp.
apply: bound_ulp_FLT => //.
rewrite Rabs_pos_eq; first by apply: phqhB.
by have := phB; have := qhB; nra.
Qed.

Lemma imul_plqhs' : is_imul (pl * qh + s') (pow (- 216)).
Proof.
apply: is_imul_add; last first.
  by apply: is_imul_pow_le imul_s' _.
have -> : pow (- 216) = pow (- 163) * pow (- 53) by rewrite -bpow_plus.
by apply: is_imul_mul imul_pl imul_qh.
Qed.

Lemma plqhs'B : Rabs (pl * qh + s') <= Rpower 2 (- 50.19424).
Proof.
apply: Rle_trans (_ : Rpower 2 (- 50.680499) * 1.000131 + pow (- 52) <= _);
    last by interval.
boundDMI; last by apply: s'B.
boundDMI; first by have := plB; lra.
by have := qhB; split_Rabs; lra.
Qed.

Definition e'2 := t' - (pl * qh + s').

Lemma t'E : t' = pl * qh + s' + e'2.
Proof. by rewrite /e'2; lra. Qed.

Lemma e'2B : Rabs e'2 <= pow (- 103).
Proof.
apply: Rle_trans (_ : ulp (pl * qh + s') <= _).
  by apply: error_le_ulp.
apply: bound_ulp_FLT => //.
by apply: Rle_lt_trans plqhs'B _; interval.
Qed.

Lemma t'B : Rabs t' <= Rpower 2 (- 50.194239).
Proof.
rewrite t'E.
apply: Rle_trans (_ : Rpower 2 (- 50.19424) + pow (- 103) <= _); 
    last by interval.
boundDMI => //; first by apply: plqhs'B.
apply: e'2B.
Qed.

Lemma phqlt'B : Rabs (ph * ql + t') <= Rpower 2 (- 49.541218).
Proof.
apply: Rle_trans (_ : 2 * Rpower 2 (- 51.999 ) + Rpower 2 (- 50.194239) <= _);
    last by interval.
boundDMI; last by apply: t'B.
boundDMI; first by have := phB; split_Rabs; lra.
by apply: qlB.
Qed.

Definition e'3 := l - (ph * ql + t').

Lemma lE : l = ph * ql + t' + e'3.
Proof. by rewrite /e'3; lra. Qed.

Lemma e'3B : Rabs e'3 <= pow (- 102).
Proof.
apply: Rle_trans (_ : ulp (ph * ql + t') <= _).
  by apply: error_le_ulp.
apply: bound_ulp_FLT => //.
by apply: Rle_lt_trans phqlt'B _; interval.
Qed.

Lemma lB : Rabs l <= Rpower 2 (- 49.5412179).
Proof.
rewrite lE.
apply: Rle_trans (_ : Rpower 2 (- 49.541218) + pow (- 102) <= _); 
    last by interval.
boundDMI => //; first by apply: phqlt'B.
by apply: e'3B.
Qed.

Lemma lhB : Rabs (l / h) <= Rpower 2 (- 49.541).
Proof.
rewrite Rabs_mult Rabs_inv.
by have hB := hB; have lB := lB; interval.
Qed.

Lemma abs_error_hl :
  Rabs (h + l - (ph + pl) * (qh + ql)) <= Rpower 2 (- 100.9129).
Proof.
apply: Rle_trans (_ : pow (- 103) + pow (- 102) + Rpower 2 (- 50.680499) *
                      Rpower 2 (- 51.999) <= _); last by interval.
have -> : h + l - (ph + pl) * (qh + ql) = e'2 + e'3 - pl * ql.
  by rewrite lE /e'2 /e'3 s'E; lra.
boundDMI.
  boundDMI; first by apply: e'2B.
  by apply: e'3B.
rewrite Rabs_Ropp.
boundDMI; first by apply/Rlt_le/plB.
by apply: qlB.
Qed.

Lemma rel_error_hl :
  Rabs ((h + l) / ((ph + pl) * (qh + ql)) - 1) <= Rpower 2 (- 100.912696).
Proof.
have phplqhqlB : Rpower 2 (- 0.000204) <= (ph + pl) * (qh + ql).
  apply: Rle_trans (_ : 0.999859 <= _); first by interval.
  have phB := phB; have plB := plB; have qhB := qhB; have qlB := qlB.
  have ql_pos : 0 <= Rabs ql by apply: Rabs_pos.
  have pl_pos : 0 <= Rabs pl by apply: Rabs_pos.
  set xx := Rabs pl in plB pl_pos; set yy := Rabs ql in qlB ql_pos.
  have plphB : 0.9999998 <= ph + pl.
    apply: Rle_trans (_ : ph - xx <= _); first by interval with (i_prec 100).
    by rewrite /xx; split_Rabs; lra.
  have qlqhB : 0.9998599 <= qh + ql.
    apply: Rle_trans (_ : qh - yy <= _); first by interval with (i_prec 100).
    by rewrite /yy; split_Rabs; lra.
  set uu := ph + pl in plphB *; set vv := qh + ql in qlqhB *.
  by interval.
have abs_error := abs_error_hl.
set uu := _ * _ in abs_error phplqhqlB *.
have -> : (h + l) / uu - 1 = (h + l - uu) / uu.
  by field; interval.
rewrite Rabs_mult Rabs_inv [Rabs uu]Rabs_pos_eq; last by interval.
apply/Rcomplements.Rle_div_l; first by interval.
apply: Rle_trans abs_error _.
have -> : -100.9129 = -100.912696 + -0.000204 by lra.
rewrite Rpower_plus.
by apply: Rmult_le_compat_l phplqhqlB; interval.
Qed.

Definition eh := RND (pow e * h).

Definition el := RND (pow e * l).

Definition r0 := -0x1.74910ee4e8a27p+9.
Definition pr0 := -0x1.74910ee4e8a28p+9.
Definition r1 := -0x1.577453f1799a6p+9.
Definition r2 := 0x1.62e42e709a95bp+9.
Definition r3 := 0x1.62e4316ea5df9p+9.

Definition r0f := Float beta (-6554261530774055) (- 43).
Definition pr0f := Float beta (-6554261530774056) (- 43).
Definition r1f := Float beta (-6042113805883814) (- 43).
Definition r2f := Float beta (6243314366523739) (- 43).
Definition r3f := Float beta (6243315169779193) (- 43).

Fact r0fE : F2R r0f = r0.
Proof. by rewrite /r0 /F2R /Q2R /= /Z.pow_pos /=; lra. Qed.

Lemma r0F : format r0.
Proof.
rewrite -r0fE.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact pr0fE : F2R pr0f = pr0.
Proof. by rewrite /pr0 /F2R /Q2R /= /Z.pow_pos /=; lra. Qed.

Lemma pr0F : format pr0.
Proof.
rewrite -pr0fE.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma pr0fE1 : pred beta fexp r0 = pr0.
Proof.
have -> : r0 = - (0x1.74910ee4e8a27p9) by rewrite /r0; lra.
rewrite pred_opp succ_eq_pos; last by lra.
rewrite ulp_neq_0; last by lra.
rewrite /cexp.
have -> : mag beta 0x1.74910ee4e8a27p9%xR = 10%Z :> Z.
  by apply: mag_unique_pos; split; interval.
by rewrite /= /Z.pow_pos /pr0 /=; lra.
Qed.

Fact r1fE : F2R r1f = r1.
Proof. rewrite /r1 /F2R /Q2R /= /Z.pow_pos /=; lra.
Qed.

Lemma r1F : format r1.
Proof.
rewrite -r1fE.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact r2fE : F2R r2f = r2.
Proof. by rewrite /r2 /F2R /Q2R /= /Z.pow_pos /=; lra. Qed.

Lemma r2F : format r2.
Proof.
rewrite -r2fE.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact r3fE : F2R r3f = r3.
Proof. by rewrite /r3 /F2R /Q2R /= /Z.pow_pos /=; lra. Qed.

Lemma format_r3 : format r3.
Proof.
rewrite -r3fE.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Definition e''' := (h + l) / ((ph + pl) * (qh + ql)) - 1.

Lemma hlE : h + l = (ph + pl) * (qh + ql) * (1 + e''').
Proof.
rewrite /e'''; field.
  have phB := phB; have plB := plB; have qhB := qhB; have qlB := qlB.
  have ql_pos : 0 <= Rabs ql by apply: Rabs_pos.
  have pl_pos : 0 <= Rabs pl by apply: Rabs_pos.
  set xx := Rabs pl in plB pl_pos; set yy := Rabs ql in qlB ql_pos.
  have plphB : 0.9999998 <= ph + pl.
    apply: Rle_trans (_ : ph - xx <= _); first by interval with (i_prec 100).
    by rewrite /xx; split_Rabs; lra.
  have qlqhB : 0.9998599 <= qh + ql.
    apply: Rle_trans (_ : qh - yy <= _); first by interval with (i_prec 100).
    by rewrite /yy; split_Rabs; lra.
  by split; lra.
Qed.

Lemma e'''B : Rabs e''' <= Rpower 2 (- 100.912696).
Proof. by apply: rel_error_hl. Qed.

Definition e' := (ph + pl) / (Rpower 2 (IZR i2 / pow 6 + IZR i1 / pow 12)) - 1.

Lemma phplE : ph + pl = Rpower 2 (IZR i2 / pow 6 + IZR i1 / pow 12) * (1 + e').
Proof.
rewrite /e'; field.
suff : 0 < Rpower 2 (IZR i2 / pow 6 + IZR i1 / pow 12) by lra.
by apply: exp_pos.
Qed.

Lemma e'B : Rabs e' <= Rpower 2 (- 102.2248).
Proof. apply: rel_error_phpl_i1i2. Qed.

Definition eps := exp (rh + rl) / (Rpower 2 (IZR k / pow 12) * exp z) - 1.

Lemma erhrlE : exp (rh + rl) = Rpower 2 (IZR k / pow 12) * exp z * (1 + eps).
Proof.
rewrite /eps; field.
split.
  suff : 0 < exp z by lra.
  by apply: exp_pos.
suff : 0 < Rpower 2 (IZR k / pow 12)  by lra.
by apply: exp_pos.
Qed.

Lemma epsB : Rabs eps <= Rpower 2 (- 64.67806).
Proof. by apply: expzB. Qed.

Definition e'' := (qh + ql) / exp z - 1.

Lemma qhqlE : qh + ql = exp z * (1 + e'').
Proof.
rewrite /e''; field.
suff : 0 < exp z by lra.
by apply: exp_pos.
Qed.

Lemma e''B : Rabs e'' <= Rpower 2 (- 64.902632).
Proof. by apply/Rlt_le/qhqlB. Qed.

Definition d := (pow e * (h + l)) / exp (rh + rl) - 1.

Lemma powehlE : pow e * (h + l) = exp (rh + rl) * (1 + d).
Proof.
rewrite /d; field.
suff : 0 < exp (rh + rl) by lra.
by apply: exp_pos.
Qed.

Lemma dE : d = (1 + e') * (1 + e'') * (1 + e''') / (1 + eps) - 1.
Proof.
rewrite /d hlE phplE qhqlE erhrlE.
rewrite pow_Rpower -[IZR beta]/2 // -!Rmult_assoc -Rpower_plus.
have -> : IZR e + (IZR i2 / pow 6 + IZR i1 / pow 12) = IZR k / pow 12.
  rewrite kE 2!plus_IZR 2!mult_IZR !(IZR_Zpower beta); try lia.
  have -> : pow 12 = pow 6 * pow 6 by rewrite -bpow_plus; congr bpow; lia.
  by field; interval.
field; split; first by have epsB := epsB; interval.
split.
  suff: 0 < exp z by lra.
  by apply: exp_pos.
suff : 0 < Rpower 2 (IZR k / pow 12) by lra.
by apply: exp_pos.
Qed.

Definition Phi := Rpower 2 (- 63.78598).

Lemma dB : Rabs d < Phi.
Proof.
rewrite dE.
have e'B := e'B.
have e''B := e''B.
have e'''B := e'''B.
have epsB := epsB.
by interval with (i_prec 90).
Qed.

Lemma rhrlLB : r1 <= rh <= r2 -> r1 + -0x1.72b0feb06bbe9p-15 <= rh + rl.
Proof.
move=> rhB1.
have [->|rh_neq0] := Req_dec rh 0; first by interval.
have rlhB:  Rabs rl <= Rpower 2 (-23.8899) * Rabs rh.
  apply/Rcomplements.Rle_div_l; first by split_Rabs; lra.
  by rewrite /Rdiv -Rabs_inv -Rabs_mult.
have [rh_pos|rh_neg] := Rle_lt_dec 0 rh; first by interval.
suff : (-0x1.72b0feb06bbe9p-15)%xR <= rl by lra.
rewrite [Rabs rh]Rabs_left in rlhB; last by lra.
have F : Rpower 2 (-23.8899) * r1 <= rl.
  have p_pos : 0 < Rpower 2 (-23.8899) by apply: exp_pos.
  by split_Rabs; nra.
pose R_UP := (round beta fexp Zceil).
have <- : R_UP rl = rl by apply: round_generic.
suff <- : R_UP (Rpower 2 (-23.8899) * r1) = -0x1.72b0feb06bbe9p-15.
  by apply: round_le.
pose f : float := Float beta (-6521271831935977) (- 67).
have fF : format f.
  by apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _.
have magfE : mag beta f = (- 14)%Z :> Z.
  apply: mag_unique.
  rewrite /F2R /= /Z.pow_pos /=.
  by split; interval.
have ufE : ulp f = pow (- 67).
  rewrite ulp_neq_0; last by rewrite /F2R /= /Z.pow_pos /=; lra.
  by congr (pow _); rewrite /cexp /fexp magfE; lia.
have fE : f = -0x1.72b0feb06bbe9p-15 :> R.
  by rewrite /F2R /= /Z.pow_pos /=; lra.
rewrite -fE.
apply: round_UP_eq => //; split; last first.
  by rewrite /F2R /= /Z.pow_pos /=; interval with (i_prec 70).
have foppE : f = - Float beta (6521271831935977) (- 67) :> R.
  by rewrite /F2R /= /Z.pow_pos /=; lra.
rewrite foppE pred_opp succ_eq_pos; last first.
  by rewrite /F2R /= /Z.pow_pos /=; lra.
rewrite -ulp_opp -foppE ufE.
by rewrite /F2R /= /Z.pow_pos /=; interval with (i_prec 100).
Qed.

Lemma powehlLB : r1 <= rh <= r2 -> pow (- 991) <= pow e * (h + l).
Proof.
move=> rhB1.
rewrite powehlE.
apply: Rle_trans (_ : exp (r1 + -0x1.72b0feb06bbe9p-15) * (1 - Phi) <= _).
  by interval with (i_prec 100).
apply: Rle_trans (_ : exp (r1 + -0x1.72b0feb06bbe9p-15) * (1 + d) <= _).
  apply: Rmult_le_compat_l; first by apply/Rlt_le/exp_pos.
  by have := dB; clear; split_Rabs; lra.
apply: Rmult_le_compat_r.
  apply: Rle_trans (_ : 1 - Phi <= _); first by interval.
  by have := dB; clear; split_Rabs; lra.
by apply/exp_le/rhrlLB.
Qed.

Lemma powehLB : r1 <= rh <= r2 -> pow (- 991) <= pow e * h.
Proof.
move=> rhB1.
have [rl_neg|rl_pos] := Rle_lt_dec l 0.
  apply: Rle_trans (_ : pow e * (h + l) <= _); first by apply: powehlLB.
  apply: Rmult_le_compat_l; last by lra.
  by apply: bpow_ge_0.
apply: Rle_trans (_ : pow e * (h + l) * (1 - Rpower 2 (- 49.541)) <= _);
    last first.
  rewrite Rmult_assoc; apply: Rmult_le_compat_l; first by apply: bpow_ge_0.
  have hB := hB.
  have lB : l <= Rpower 2 (-49.541) * h.
    apply/Rcomplements.Rle_div_l; first by lra.
    rewrite -[l / h]Rabs_pos_eq; first by apply: lhB.
    by apply: Rcomplements.Rdiv_le_0_compat; lra.
  suff : l * (1 - Rpower 2 (-49.541)) <= Rpower 2 (-49.541) * h by lra.
  apply: Rle_trans lB.
  suff: 0 <= Rpower 2 (-49.541) * l by lra.
  suff: 0 <= Rpower 2 (-49.541) by nra.
  by interval.
rewrite powehlE.
apply: Rle_trans (_ : exp (r1 + -0x1.72b0feb06bbe9p-15) 
           * (1 - Phi) * (1 - Rpower 2 (-49.541)) <= _).
  by interval with (i_prec 100).
apply: Rmult_le_compat_r; first by interval.
apply: Rle_trans (_ : exp (r1 + -0x1.72b0feb06bbe9p-15) * (1 + d) <= _).
  apply: Rmult_le_compat_l; first by apply/Rlt_le/exp_pos.
  by have := dB; clear; split_Rabs; lra.
apply: Rmult_le_compat_r.
  apply: Rle_trans (_ : 1 - Phi <= _); first by interval.
  by have := dB; clear; split_Rabs; lra.
by apply/exp_le/rhrlLB.
Qed.

Lemma rhrlUB : r1 <= rh <= r2 -> rh + rl <= r2 + 0x1.7f09093c9fe5bp-15.
Proof.
move=> rhB1.
have [->|rh_neq0] := Req_dec rh 0; first by interval.
have rlhB:  Rabs rl <= Rpower 2 (-23.8899) * Rabs rh.
  apply/Rcomplements.Rle_div_l; first by split_Rabs; lra.
  by rewrite /Rdiv -Rabs_inv -Rabs_mult.
have [rh_pos|rh_neg] := Rle_lt_dec 0 rh; last by interval.
suff :  rl <= 0x1.7f09093c9fe5bp-15 by lra.
rewrite [Rabs rh]Rabs_pos_eq in rlhB; last by lra.
have F : rl <= Rpower 2 (-23.8899) * r2.
  have p_pos : 0 < Rpower 2 (-23.8899) by apply: exp_pos.
  by split_Rabs; nra.
pose R_DN := (round beta fexp Zfloor).
have <- : R_DN rl = rl by apply: round_generic.
suff <- : R_DN (Rpower 2 (-23.8899) * r2) = 0x1.7f09093c9fe5bp-15%xR.
  by apply: round_le.
pose f : float := Float beta (6738428209790555) (- 67).
have fF : format f.
  by apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _.
have magfE : mag beta f = (- 14)%Z :> Z.
  apply: mag_unique.
  rewrite /F2R /= /Z.pow_pos /=.
  by split; interval.
have ufE : ulp f = pow (- 67).
  rewrite ulp_neq_0; last by rewrite /F2R /= /Z.pow_pos /=; lra.
  by congr (pow _); rewrite /cexp /fexp magfE; lia.
have fE : f = 0x1.7f09093c9fe5bp-15 :> R.
  by rewrite /F2R /Q2R /= /Z.pow_pos /=; lra.
rewrite -fE.
apply: round_DN_eq => //; split.
  by rewrite /F2R /= /Z.pow_pos /=; interval with (i_prec 70).
rewrite succ_eq_pos; last first.
  by rewrite /F2R /= /Z.pow_pos /=; lra.
rewrite ufE.
by rewrite /F2R /= /Z.pow_pos /=; interval with (i_prec 100).
Qed.

Lemma powehlUB : r1 <= rh <= r2 -> pow e * (h + l) <= omega.
Proof.
move=> rhB1.
rewrite powehlE.
apply: Rle_trans (_ : exp (r2 + 0x1.7f09093c9fe5bp-15) * (1 + Phi) <= _);
    last by interval with (i_prec 100).
apply: Rle_trans (_ : exp (r2 + 0x1.7f09093c9fe5bp-15) * (1 + d) <= _); 
    last first.
  apply: Rmult_le_compat_l; first by apply/Rlt_le/exp_pos.
  by have := dB; clear; split_Rabs; lra.
apply: Rmult_le_compat_r.
  apply: Rle_trans (_ : 1 - Phi <= _); first by interval.
  by have := dB; clear; split_Rabs; lra.
by apply/exp_le/rhrlUB.
Qed.

Lemma powehUB : r1 <= rh <= r2 -> pow e * h <= omega.
Proof.
move=> rhB1.
have [rl_pos|rl_neg] := Rle_lt_dec 0 l.
  apply: Rle_trans (_ : pow e * (h + l) <= _); last by apply: powehlUB.
  apply: Rmult_le_compat_l; last by lra.
  by apply: bpow_ge_0.
apply: Rle_trans (_ : pow e * (h + l) * 
            (1 + Rpower 2 (- 49.541)) / (1 - Rpower 2 (- 49.541)) <= _).
  rewrite /Rdiv !Rmult_assoc; apply: Rmult_le_compat_l.
    by apply: bpow_ge_0.
  have hB := hB.
  have lB : - l <= Rpower 2 (-49.541) * h.
    apply/Rcomplements.Rle_div_l; first by lra.
    have -> : - l / h = - (l / h) by lra.
    rewrite -Rabs_left; first by apply: lhB.
    suff : 0 < (- l) / h by lra.
    by apply: Rcomplements.Rdiv_lt_0_compat; lra.
  rewrite -!Rmult_assoc -[_ */ _]/(_ / _).
  suff : h * (1 - Rpower 2 (-49.541)) <= (h + l) * (1 + Rpower 2 (-49.541)).
    have p_pos : (1 - Rpower 2 (-49.541)) > 0 by interval.
    by move=> /Rcomplements.Rle_div_r => /(_ p_pos); lra.
  apply: Rle_trans (_ : h * (1 - Rpower 2 (-49.541)) *
                         (1 + Rpower 2 (-49.541)) <= _).
    rewrite Rmult_assoc.
    apply: Rmult_le_compat_l; first by lra.
    by interval.
  apply: Rmult_le_compat_r; first by interval.
  by lra.
rewrite powehlE.
apply: Rle_trans (_ : exp (r2 + 0x1.7f09093c9fe5bp-15) 
           * (1 + Phi) * (1 + Rpower 2 (-49.541)) 
              / (1 - Rpower 2 (-49.541)) <= _); last first.
  by interval with (i_prec 100).
apply: Rmult_le_compat_r; first by interval.
apply: Rmult_le_compat_r; first by interval.
apply: Rle_trans (_ : exp (r2 + 0x1.7f09093c9fe5bp-15) * (1 + d) <= _); 
    last first.
  apply: Rmult_le_compat_l; first by apply/Rlt_le/exp_pos.
  by have := dB; clear; split_Rabs; lra.
apply: Rmult_le_compat_r.
  apply: Rle_trans (_ : 1 - Phi <= _); first by interval.
  by have := dB; clear; split_Rabs; lra.
by apply/exp_le/rhrlUB.
Qed.

Lemma pehF : r1 <= rh <= r2 -> format (pow e * h).
Proof.
move=> rhB1.
rewrite Rmult_comm.
apply: mult_bpow_exact_FLT hF _.
rewrite -[radix2]/beta.
suff : (emin + p - e < mag beta h)%Z by lia.
apply: mag_gt_bpow.
rewrite bpow_plus bpow_opp.
apply/Rcomplements.Rle_div_l; first by apply: bpow_gt_0.
rewrite Rabs_pos_eq; last by have := hB; lra.
apply: Rle_trans (_ : pow (- 991) <= _); first by apply: bpow_le; lia.
by have := powehLB rhB1; rewrite Rmult_comm; lra.
Qed.

Lemma el_abs_error : Rabs (el - pow e * l) <= alpha.
Proof.
have [eLl|lLe] := Z_lt_le_dec  (emin + p - e)(mag beta l).
  rewrite /e'' /el round_generic ?Rsimp01 //; first by interval.
  rewrite Rmult_comm.
  apply: mult_bpow_exact_FLT lF _.
  by rewrite -[radix2]/beta; lia.
suff <- : ulp (pow e * l) = alpha by apply: error_le_ulp.
apply: ulp_subnormal => //.
rewrite Rabs_mult Rabs_pos_eq; last by apply: bpow_ge_0.
have -> : (3 - 1024 - 53 + 53 = e + (3 - 1024 - 53 + 53 - e))%Z by lia.
rewrite bpow_plus -[bpow _ _]/(pow _); apply: Rmult_lt_compat_l.
  by apply: bpow_gt_0.
apply: Rlt_le_trans (_ : pow (mag beta l) <= _).
  by apply: bpow_mag_gt.
by apply: bpow_le; lia.
Qed.

Lemma ehB : r1 <= rh <= r2 -> pow (- 991) <= eh.
Proof.
move=> rhB1.
apply: round_le_l; first by apply: generic_format_FLT_bpow.
by apply: powehLB.
Qed.

Lemma elehB : r1 <= rh <= r2 -> Rabs (el / eh) <= Rpower 2 (- 49.2999).
Proof.
move=> rhB1.
apply: Rle_trans (_ : Rpower 2 (-49.541) + alpha / pow (- 1022) <= _);
    last by interval with (i_prec 100).
have teh := pehF rhB1.
rewrite /eh round_generic //.
pose e'' := el - pow e * l.
have elE : el = pow e * l + e'' by rewrite /e''; lra.
have e''B : Rabs e'' <= alpha by apply: el_abs_error.
rewrite elE.
have -> : (pow e * l + e'') / (pow e * h) = l / h + e'' / (pow e * h).
  field; split; first by have hB := hB; interval.
  suff : 0 < pow e by lra.
  by apply: bpow_gt_0.
boundDMI; first by apply: lhB.
rewrite Rabs_mult Rabs_inv.
apply: Rmult_le_compat => //; first by apply: Rabs_pos.
  by apply/Rinv_0_le_compat/Rabs_pos.
apply: Rinv_le; first by interval.
have powehLB := powehLB rhB1.
by set xx := (_ * _) in powehLB *; interval.
Qed.

Definition mu := (eh + el) / (pow e * (h + l)) - 1.

Lemma ehelE : eh + el = (pow e * (h + l)) * (1 + mu).
Proof.
rewrite /mu; field; split => //.
  by have hB := hB; have lB := lB; interval.
suff : 0 < pow e by lra.
by apply: bpow_gt_0.
Qed.

Lemma muB : r1 <= rh <= r2 -> Rabs mu <= Rpower 2 (- 82.9).
Proof.
move=> rhB1; rewrite /mu.
have -> : (eh + el) / (pow e * (h + l)) - 1 = 
          (eh + el - pow e * (h + l)) / (pow e * (h + l)).
  field; split => //.
    by have hB := hB; have lB := lB; interval.
  suff : 0 < pow e by lra.
  by apply: bpow_gt_0.
have -> : eh + el - pow e * (h + l) = el - pow e * l.
  rewrite /eh round_generic //; first by lra.
  by apply: pehF.
rewrite Rabs_mult Rabs_inv.
apply: Rle_trans (_ : alpha / pow (- 991) <= _); 
  last by interval with (i_prec 100).
apply: Rmult_le_compat; first by apply: Rabs_pos.
- by apply/Rinv_0_le_compat/Rabs_pos.
- by apply: el_abs_error.
apply: Rinv_le; first by interval.
rewrite Rabs_pos_eq; first by apply: powehlLB.
apply: Rle_trans (_ : pow (-991) <= _); first by apply: bpow_ge_0.
by apply: powehlLB.
Qed.

Definition e_exp := (1 + d) * (1 + mu) - 1.

Lemma ehelE1 : r1 <= rh <= r2 -> eh + el = exp(rh + rl) * (1 + e_exp).
Proof.
by move=> rhB1; rewrite ehelE powehlE /e_exp; lra.
Qed.

Lemma e_expB : r1 <= rh <= r2 -> Rabs e_exp < Rpower 2 (- 63.78597).
Proof.
move=> rhB1; suff : 0 < Rpower 2 (- 63.78597) - Rabs e_exp by lra.
have dB := dB; have muB := muB rhB1.
interval with (i_prec 100).
Qed.

End Prelim.

Section algoExp1.

Let p := 53%Z.
Let emax := 1024%Z.
Let emin := (3 - emax - p)%Z.

Let beta := radix2.

Hypothesis Hp2: Z.lt 1 p.
Local Notation pow e := (bpow beta e).

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).

Variable rnd : R -> Z.
Context ( valid_rnd : Valid_rnd rnd ).

Local Notation float := (float radix2).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format radix2 fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation fastTwoSum := (fastTwoSum rnd).
Local Notation exactMul := (exactMul beta emin p rnd).
Local Notation fastSum := (fastSum beta emin p rnd).
Local Notation q1 := (q1 rnd).

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Local Notation ulp := (ulp beta fexp).

Variable choice : Z -> bool.

(* Algo Exp 1 *)

Local Notation " x <? y " := (Rlt_bool x y).

(* With the format FLT_exp there is no overflow so by contrast to the 
   paper we do not deal with it, so we always fail when rh > r2 *)

Definition exp1 r := 
let 'DWR rh rl := r in 
let r0 := -0x1.74910ee4e8a27p+9 in
let r1 := -0x1.577453f1799a6p+9 in
let r2 := 0x1.62e42e709a95bp+9 in
let r3 := 0x1.62e4316ea5df9p+9 in
if r3 <? rh then (* some (DWR omega omega) *) None else 
if rh <? r0 then some (DWR alpha (- alpha)) else 
if (rh <? r1) || (r2 <? rh) then None else
let INVLN2 := 0x1.71547652b82fep+12 in
let k := Znearest choice (RND (rh * INVLN2)) in 
let LN2H := 0x1.62e42fefa39efp-13 in 
let LN2L := 0x1.abc9e3b39803fp-68 in
let zh := RND (rh - IZR k * LN2H) in 
let zl := RND (rl - IZR k * LN2L) in
let z := RND (zh + zl) in 
let e := (k / 2 ^ 12)%Z in 
let i2 := ((k - e * 2 ^ 12) / 2 ^ 6)%Z in
let i1 := ((k - e * 2 ^ 12 - i2 * 2 ^ 6))%Z in
let '(h2, l2) := (nth (0,0) T1 (Z.to_nat i2)) in 
let '(h1, l1) := (nth (0,0) T2 (Z.to_nat i1)) in 
let 'DWR ph s := exactMul h1 h2 in 
let t := RND (l1 * h2 + s) in 
let pl := RND (h1 * l2 + t) in 
let 'DWR qh ql := q1 z in 
let 'DWR h s := exactMul ph qh in
let t := RND (pl * qh + s) in 
let l := RND (ph * ql + t) in 
some (DWR (RND (pow e * h)) (RND (pow e * l))).

Lemma exp1_good_range rh rl :
  -0x1.577453f1799a6p+9 <= rh <= 0x1.62e42e709a95bp+9 ->
  ~ (exp1 (DWR rh rl) = None).
Proof.
rewrite /exp1.
case: Rlt_bool_spec => //.
  rewrite -/r2 -/r3 => ?; suff: r2 < rh by lra.
  interval.
case: Rlt_bool_spec; first by lra.
case: Rlt_bool_spec; first by lra.
case: Rlt_bool_spec; first by lra.
case: nth => h3 l3 /=.
by case: nth => h4 l4.
Qed.

Lemma err_lem7 rh rl eh el :
  format rh -> format rl -> pow (- 970) <= Rabs rh ->
  -0x1.577453f1799a6p+9 <= rh <= 0x1.62e42e709a95bp+9 ->
  Rabs (rl / rh) <= Rpower 2 (- 23.8899) -> Rabs rl <= Rpower 2 (- 14.4187) ->
  exp1 (DWR rh rl) = some (DWR eh el) -> 
  [/\
    Rabs ((eh + el) / exp (rh + rl) - 1) < Rpower 2 (- 63.78597), 
    Rabs (el / eh) <= Rpower 2 (- 49.2999) &
    pow (- 991) <= eh].
Proof.
move=> rhF rlF rhB rhB1 rlrhB rlB.
case E: exp1 => [[xh xl]|]; last by discriminate.
case => xhE xlE.
rewrite {xh}xhE in E; rewrite {xl}xlE in E.
have rhB2 : pow (-970) <= Rabs rh <= 709.79.
  by split; [lra | interval].
have rhrlB : Rabs (rh + rl) <= 709.79 by interval.
have -> : eh = algoExp1.eh rnd rh rl choice.
  have := E.
  rewrite /exp1.
  case: Rlt_bool_spec => [|_]; first by lra.
  case: Rlt_bool_spec => [|_]; first by lra.
  case: Rlt_bool_spec => [|_]; first by lra.
  case: Rlt_bool_spec => [|_ /=]; first by lra.
  case E2 : nth => [h2 l2].
  case E1 : nth => [h1 l1].
  case=> <- _.
  congr (RND (_ * RND(RND (_ * _) * _))).
    rewrite /algoExp1.h1.
    by case: nth E1 => ? ? [].
  rewrite /algoExp1.h2.
  by case: nth E2 => ? ? [].
have -> : el = algoExp1.el rnd rh rl choice.
  have := E.
  rewrite /exp1.
  case: Rlt_bool_spec => [|_]; first by lra.
  case: Rlt_bool_spec => [|_]; first by lra.
  case: Rlt_bool_spec => [|_]; first by lra.
  case: Rlt_bool_spec => [|_ /=]; first by lra.
  case E2 : nth => [h2 l2].
  case E1 : nth => [h1 l1].
  case=> _ <-.
  have h1E : h1 = algoExp1.h1 rnd rh choice.
    rewrite /algoExp1.h1.
    by case: nth E1 => ? ? [].
  have h2E : h2 = algoExp1.h2 rnd rh choice.
    rewrite /algoExp1.h2.
    by case: nth E2 => ? ? [].
  congr (RND (_ * RND (RND (_ * _) * 
            RND _ + RND (RND (_ * _ + RND (_ * _ + RND (_ * _ - RND (_ * _)))) 
            * RND (_ + RND _) + RND _)))) => //.
  - rewrite /algoExp1.l2.
    by case: nth E2 => ? ? [].
  - rewrite /algoExp1.l1.
    by case: nth E1 => ? ? [].
  by congr (RND (_ * _) * _ - RND (RND (_ * _) * _)).
split.
- rewrite ehelE1 //; try lra.
  have -> : exp (rh + rl) * (1 + e_exp rnd rh rl choice) / exp (rh + rl) - 1 =
             e_exp rnd rh rl choice.
    field.
    have : 0 < exp (rh + rl) by apply: exp_pos.
    by lra.
  by apply: e_expB => //; lra.
- by apply: elehB => //; lra.
by apply: ehB.
Qed.

End algoExp1.

