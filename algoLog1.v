Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
Require Import tableINVERSE tableLOGINV algoP1.
Require Import Fast2Sum_robust_flt.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Log1.

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
Local Notation fastTwoSum := (fastTwoSum rnd).
Local Notation RND := (round beta fexp rnd).
Local Notation p1 := (p1 rnd).

Let alpha := pow (- 1074).
Let omega := (1 - pow (-p)) * pow emax.

Variable getRange : R -> R * Z.

Hypothesis getRangeCorrect : 
  forall f,  format f -> alpha <= f <= omega -> 
    / sqrt 2 < (getRange f).1 < sqrt 2 /\ 
    f = ((getRange f).1) * pow (getRange f).2.

Hypothesis getRangeFormat : 
  forall f,  format f -> alpha <= f <= omega -> format (getRange f).1. 

Lemma getRange_bound f : 
  format f -> alpha <= f <= omega -> (- 1074 <= (getRange f).2 <= 1024)%Z.
Proof.
move=> aF aB.
have sqrt2B : 1.4 < sqrt 2 < 1.5 by split; interval.
have sqrt2BI : 0.6 < / sqrt 2 < 0.8 by split; interval.
have [tN eB] := getRangeCorrect aF aB.
set t := (_).1 in eB tN; set e := (_).2 in eB *.
suff:  (- 1075 < e < 1025)%Z by lia.
suff:  pow (- 1075) < pow e < pow (1025).
  by move=> [? ?]; split; apply: (lt_bpow radix2).
suff : t * pow (- 1075) < t * pow e < t * pow 1025 by nra.
suff : sqrt 2 * pow (- 1075) < t * pow e < / sqrt 2 * pow 1025.
  have : 0 < pow (- 1075) by apply: bpow_gt_0.
  have : 0 < pow 1025 by apply: bpow_gt_0.
  by nra.
rewrite -eB; rewrite /alpha /omega in aB.
split; interval with (i_prec 40).
Qed.

Definition getIndex (f : R) : nat := Z.to_nat (Zfloor (pow 8 * f)).

Lemma getIndexCorrect (f : R) : 
  alpha <= f -> Z.of_nat (getIndex f) = Zfloor (pow 8 * f).
Proof.
move=> aLf; rewrite Z2Nat.id // -(Zfloor_IZR 0).
apply: Zfloor_le.
have : 0 <= pow 8 by apply: bpow_ge_0.
have : 0 < alpha by apply: alpha_gt_0.
nra.
Qed.

Lemma getIndexBound (t : R) : 
  / sqrt 2 < t < sqrt 2 -> (181 <= (getIndex t) <= 362)%N.
Proof.  
move=> tB.
rewrite /getIndex.
have powN8_gt0 : 0 < pow 8 by apply: bpow_gt_0.
have pow8t_ge0 : (0 <= Zfloor (pow 8 * t))%Z.
  rewrite -(Zfloor_IZR 0); apply: Zfloor_le.
  by interval with (i_prec 100).
apply/andP; split; apply/leP/Nat2Z.inj_le.
  suff <- : Zfloor (/ sqrt 2 * pow 8 ) = Z.of_nat 181.
    by rewrite Z2Nat.id //; apply: Zfloor_le ; nra.
  apply: Zfloor_imp; rewrite /= /Z.pow_pos /=.
  by split; interval.
suff <- : Zfloor (sqrt 2 * pow 8 ) = Z.of_nat 362.
  by rewrite Z2Nat.id //; apply: Zfloor_le; nra.
apply: Zfloor_imp; rewrite /= /Z.pow_pos /=.
by split; interval.
Qed.

Lemma fastTwoSum_0 : fastTwoSum 0 0 = DWR 0 0.
Proof. by rewrite /fastTwoSum !(Rsimp01, round_0). Qed. 

Local Notation ulp := (ulp beta fexp).

Definition fastSum (a bh bl : R) := 
  let: DWR h t := fastTwoSum a bh in DWR h (RND (t + bl)).

Lemma fastTwoSum_correct a b : 
  format a -> format b -> (a <> 0 -> Rabs b <= Rabs a) ->
  let: DWR h l := fastTwoSum a b in 
  Rabs (h + l - (a + b)) <= pow (- 105) * Rabs h.
Proof.
by move=> Fa Fb b_le_a; apply/FastTwoSum_bound_round.
Qed.

Lemma fastTwoSum_correct1 a b : 
  format a -> format b -> (a <> 0 -> Rabs b <= Rabs a) ->
  let: DWR h l := fastTwoSum a b in 
  Rabs (h + l - (a + b)) <= pow (- 105) * Rabs (a + b).
Proof.
by move=> Fa Fb b_le_a ; apply/FastTwoSum_bound1.
Qed.

Lemma error_le_ulp_add x : Rabs (RND x) <= Rabs x + ulp x.
Proof.
have : Rabs (RND x - x) <= ulp x by apply: error_le_ulp.
split_Rabs; lra.
Qed.

(* Lemma 1 *)
Lemma fastSum_correct a bh bl : 
  format a -> format bh -> format bl -> (a <> 0 -> Rabs bh <= Rabs a) ->
  let: DWR h l := fastSum a bh bl in 
  Rabs (h + l - (a + bh + bl)) <= pow (- 105) * Rabs h + ulp l.
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

Lemma fastSum_0 : fastSum 0 0 0 = DWR 0 0.
Proof. by rewrite /fastSum fastTwoSum_0 Rsimp01 round_0. Qed. 

Definition log1 x := 
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h l := fastSum th z tl in 
  let: DWR ph pl := p1 z in 
  let: DWR h l := fastSum h ph (RND (l + pl)) in 
  if (e =? 0%Z)%Z then fastTwoSum h l else DWR h l.

Lemma log1_1 :  log1 1 = DWR 0 0.
Proof.
have sqrt2B : 1.4 < sqrt 2 < 1.5 by split; interval.
have sqrt2BI : 0.6 < / sqrt 2 < 0.8 by split; interval.
have F1 : format 1 by apply: format1.
have aL1 : alpha <= 1 <= omega by rewrite /alpha; interval.
rewrite /log1; case: getRange (getRangeCorrect F1 aL1) => t e.
rewrite /fst /snd => [] [H1 H2].
have eE : e = 0%Z.
  case: e H2 => // e1.
    suff: pow 1 <= pow (Z.pos e1) by rewrite pow1E [IZR beta]/=; nra.
    by apply: bpow_le; lia.
    suff: pow (Z.neg e1) <= pow (- 1).
      by rewrite (bpow_opp _ 1) pow1E [IZR beta]/=; nra.
    by apply: bpow_le; lia.
have tE : t = 1 by rewrite eE pow0E in H2; lra.
set i := getIndex t.
have iE : i = 256%N.
  by rewrite {}/i /getIndex tE Rmult_1_r /= /Z.pow_pos /= Zfloor_IZR.
rewrite iE ![nth _ _ _]/= tE eE !Rsimp01.
have -> : 0x1.00%xR = 1 by lra.
by rewrite /= !(Rsimp01, round_0, p1_0, fastTwoSum_0).
Qed.

Lemma th_prop (e : Z) x : 
  x \in LOGINV -> (- 1074 <= e <= 1024)%Z ->
  let th := IZR e * LOG2H + x.1 in 
  [/\ is_imul th (pow (- 42)),
      format th, 
      e  = 0%Z -> th <> 0 -> 0.00587 < Rabs th < 0.347,
      e <> 0 %Z-> 0.346147 <= Rabs th &
      e <> 0 %Z-> 0.346 <= Rabs th <= 744.8].
Proof.
move=> xIL eB th.
have LOG2H_pos : 0 < LOG2H by interval.
have eRB : Rabs (IZR e) <= 1074.
  by split_Rabs; rewrite -?opp_IZR; apply: IZR_le; lia.
have imul_LOG2H := imul_LOG2H.
have [] := @l1_LOGINV (index x LOGINV); first by rewrite index_mem.
rewrite nth_index // => imul_x1 _ x1B _ _.
have imul_th : is_imul th (pow (-42)).
  apply: is_imul_add => //.
  exists (e * 3048493539143)%Z.
  by rewrite LOG2HE -[bpow _ _]/(pow _) mult_IZR; lra.
have thB : Rabs th <= 744.8.
  apply: Rle_trans (_ : 1074 * LOG2H + 0.347 <= _); last first.
    by rewrite LOG2HE; interval.
  apply: Rle_trans (Rabs_triang _ _) _.
  rewrite Rabs_mult [Rabs LOG2H]Rabs_pos_eq; last by lra.
  have [->|/x1B HH] := Req_dec x.1 0; first by rewrite !Rsimp01; nra.
  apply: Rplus_le_compat; first by nra.
  by apply: Rlt_le; case: HH.
have Fth : format th.
  by apply: imul_format imul_th thB _ => //; interval.
suff thB1 : e <> 0%Z -> 0.346147 <= Rabs th.
split => // [e_eq0 t_neq0|e_neq0].
- by rewrite /th e_eq0 !Rsimp01 in t_neq0 *; apply: x1B.
- split; last by lra.
- by have := thB1 e_neq0 => ?; lra.
move=> e_neq0.
apply: Rle_trans (_ : LOG2H - Rabs x.1 <= _).
  have [->|/x1B HH] := Req_dec x.1 0; first by rewrite LOG2HE; interval.
  by set u := Rabs _ in HH *; clear LOG2H_pos; interval.
apply: Rle_trans (_ : Rabs (IZR e * LOG2H) - Rabs x.1 <= _); last first.
  by rewrite /th; split_Rabs; lra.
suff : LOG2H <= Rabs (IZR e * LOG2H) by lra.
rewrite Rabs_mult [Rabs LOG2H]Rabs_pos_eq; last by lra.
suff C : IZR e <= -1 \/ 1 <= IZR e.
  suff : 1 <= Rabs (IZR e) by nra.
  clear x1B thB; split_Rabs; lra.
have [/IZR_le|/IZR_le]: (e <= -1)%Z \/ (1 <= e)%Z by lia.
  by left; lra.
by right; lra.
Qed.

Lemma bound_ulp f e : 
  (emin <= e)%Z -> Rabs f < pow (e + p) -> ulp f <= pow e.
Proof.
move=> epLe.
have [-> fLe |f_neq0 fLe] := Req_dec f 0.
  rewrite ulp_FLT_0.
  by apply: bpow_le; lia.
rewrite ulp_neq_0 // /cexp /fexp.
apply: bpow_le.
have magfE : (mag beta f <= (e + p))%Z by apply: mag_le_bpow => //; lia.
by lia.
Qed.

Lemma format_Rabs_round_le f g : format f -> f <= Rabs g -> f <= Rabs (RND g).
Proof.
move=> Ff fLg.
have [g_pos| g_neg] := Rle_dec g 0; last first.
  rewrite Rabs_pos_eq in fLg; last by lra.
  rewrite Rabs_pos_eq; last first.
    have -> : 0 = RND 0 by rewrite round_0.
    apply: round_le; lra.
  have -> : f = RND f by rewrite round_generic.
  apply: round_le; lra.
rewrite Rabs_left1 // in fLg.
rewrite Rabs_left1; last first.
  have -> : 0 = RND 0 by rewrite round_0.
  apply: round_le; lra.
suff : RND g <= - f by lra.
have -> : - f = RND (- f).
  by rewrite round_generic //; apply: generic_format_opp.
apply: round_le; lra.
Qed.

Lemma format_Rabs_round_ge f g : format f -> Rabs g <= f -> Rabs (RND g) <= f.
Proof.
move=> Ff fLg.
have [g_pos| g_neg] := Rle_dec g 0; last first.
  rewrite Rabs_pos_eq in fLg; last by lra.
  rewrite Rabs_pos_eq; last first.
    have -> : 0 = RND 0 by rewrite round_0.
    apply: round_le; lra.
  have -> : f = RND f by rewrite round_generic.
  apply: round_le; lra.
rewrite Rabs_left1 // in fLg.
rewrite Rabs_left1; last first.
  have -> : 0 = RND 0 by rewrite round_0.
  apply: round_le; lra.
suff : -f <= RND g by lra.
have -> : - f = RND (- f).
  by rewrite round_generic //; apply: generic_format_opp.
apply: round_le; lra.
Qed.

Lemma tl_prop (e : Z) x : 
  x \in LOGINV -> (- 1074 <= e <= 1024)%Z ->
  let tl := RND (IZR e * LOG2L + x.2) in 
  [/\ is_imul tl (pow (- 104)),
      e  = 0%Z -> tl <> 0 -> pow (- 52) <= Rabs tl <= pow (- 43), 
      e <> 0 %Z-> tl <> 0 -> pow (- 104) <= Rabs tl <= Rpower 2 (- 33.8) &
      let err1 := Rabs (tl - (IZR e * LOG2L + x.2)) in 
        (e = 0%Z -> err1 = 0) /\ err1 <= pow (- 86)].
Proof.
move=> xIL eB tl.
have LOG2L_pos : 0 < LOG2L by interval.
have eRB : Rabs (IZR e) <= 1074.
  by split_Rabs; rewrite -?opp_IZR; apply: IZR_le; lia.
have imul_LOG2L := imul_LOG2L.
rewrite -[bpow _ _]/(pow _)  in imul_LOG2L.
have [] := @l1_LOGINV (index x LOGINV); first by rewrite index_mem.
rewrite nth_index // => _ imul_x2 _ x2B.
rewrite -[bpow _ _]/(pow _)  in imul_x2.
have imul_tl : is_imul tl (pow (-104)).
  apply: is_imul_pow_round.
  apply: is_imul_add => //.
  rewrite -[pow (-104)]Rmult_1_l.
  apply: is_imul_mul; first by exists e; lra.
  by apply: is_imul_pow_le imul_LOG2L _.
have ulpeLx : ulp (IZR e * LOG2L + x.2) <= pow (- 86).
  apply: bound_ulp; first by lia.
  rewrite LOG2LE -[bpow _ _]/(pow _).
  have [-> |/x2B HH] := Req_dec x.2 0; first by interval.
  rewrite -![bpow _ _]/(pow _)  in HH.
  apply: Rle_lt_trans (Rabs_triang _ _) _.
  set uu := Rabs x.2 in HH *.
  interval.
have tlB1 : e = 0%Z -> tl <> 0 -> pow (-52) <= Rabs tl <= pow (-43).
  move=> e_eq0.
  rewrite /tl e_eq0 !Rsimp01.
  have [-> |/x2B HH] := Req_dec x.2 0; first by rewrite round_0; lra.
  move=> _.
  rewrite -![bpow _ _]/(pow _) in HH.
  rewrite -![bpow radix2 _]/(pow _) in HH.  
  set xx := x.2 in HH *.
  split.
    apply: format_Rabs_round_le; last by lra.
    by apply: generic_format_bpow => //; lia.
  apply: format_Rabs_round_ge; last by lra.
  by apply: generic_format_bpow => //; lia.
have tlB2 : e <> 0%Z -> tl <> 0 -> pow (-104) <= Rabs tl <= Rpower 2 (-33.8).
  move=> e_neq0 t_neq0.
  rewrite /tl.
  have elxB : pow (-104) <=  Rabs (IZR e * LOG2L + x.2) <= Rpower 2 (- 33.9).
    split.
      have imul_elx2 : is_imul (IZR e * LOG2L + x.2) (pow (- 104)).
        (* copy *)
        apply: is_imul_add => //.
        rewrite -[pow (-104)]Rmult_1_l.
        apply: is_imul_mul; first by exists e; lra.
        by apply: is_imul_pow_le imul_LOG2L _.
      have [elx_eq0|elx_neq0]:= Req_dec (IZR e * LOG2L + x.2) 0.
        by case: t_neq0; rewrite /tl elx_eq0 round_0.
      case: imul_elx2 elx_neq0 => k -> H.
      have pow_pos : 0 < pow (- 104) by apply: bpow_gt_0.
      have k_neq0 : IZR k <> 0 by nra.
      have k_zneq0 : (k <> 0)%Z by contradict k_neq0; rewrite k_neq0.
      rewrite Rabs_mult [Rabs (pow _)]Rabs_pos_eq; last by lra.
      suff : 1 <= Rabs (IZR k) by nra.
      by rewrite -abs_IZR; apply: IZR_le; lia.
    have [x2_eq0|x2_neq0]:= Req_dec x.2 0.
      rewrite x2_eq0 !Rsimp01.
      rewrite Rabs_mult LOG2LE.
      set xx := Rabs (IZR e) in eRB *.
      by interval.
    have {}x2B := x2B x2_neq0.
  apply: Rle_trans (Rabs_triang _ _) _.
  rewrite Rabs_mult.
    set xx := Rabs (IZR e) in eRB *.
    set yy := Rabs x.2 in x2B *.
    rewrite LOG2LE.
    by interval.
  split.
    apply: format_Rabs_round_le; first by apply: generic_format_bpow.
    lra.
  apply: Rle_trans (_ : Rpower 2 (-33.9) + ulp (IZR e * LOG2L + x.2) <= _); last first.
    by interval.
  apply: Rle_trans (_ : Rabs (IZR e * LOG2L + x.2) + ulp (IZR e * LOG2L + x.2) <= _); last first.
    lra.
  by apply: error_le_ulp_add.
split => // err1.
split.
  move=> e_eq0.
  rewrite /err1 /tl e_eq0 !Rsimp01.
  have [_ f_x2] := format_LOGINV (refl_equal _) xIL.
  by rewrite round_generic // !Rsimp01.
apply: Rle_trans (_ : ulp (IZR e * LOG2L + x.2) <= _) => //.
by apply: error_le_ulp.
Qed.

Lemma fastTwoSum_0l f : format f -> fastTwoSum 0 f = DWR f 0.
Proof.
move=> Ff; rewrite /fastTwoSum !Rsimp01 round_generic //.
by rewrite (round_generic _ _ _ f) // !Rsimp01 round_0.
Qed.

Lemma fastTwoSum_0r f : format f -> fastTwoSum f 0 = DWR f 0.
Proof.
by move=> Ff; rewrite /fastTwoSum !Rsimp01 round_generic // !(Rsimp01, round_0).
Qed.

Lemma err2_err3_h_l_bound x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t1 := fastTwoSum th z in 
  let l := RND (t1 + tl) in
  let err2 := Rabs ((h + t1) - (th + z)) in 
  let err3 := Rabs (l - (t1 + tl)) in
  [/\
     (e = 0%Z -> err2 <= Rpower 2 (- 106.5)) /\ 
     (e <> 0%Z -> err2 <= Rpower 2 (- 94.458)),
     (e = 0%Z -> err3 <= pow (- 95)) /\ 
     (e <> 0%Z -> err3 <= pow (- 86)) &
    [/\ is_imul h (pow (-61)), 
        Rabs h < 745, 
        e = 0%Z -> Rabs h < 0.352, 
        is_imul l (pow (- 104)) & 
      ((e = 0%Z -> Rabs l <= Rpower 2 (- 42.89)) /\
       (e <> 0%Z -> Rabs l <= Rpower 2 (- 33.78)))]].     
Proof.
move=> Fx aLxLo.
case: getRange (getRangeCorrect Fx aLxLo) (getRange_bound Fx aLxLo)
      (getRangeFormat Fx aLxLo)
   => t e [Ht He] eB Ft.
rewrite /fst in Ht Ft; rewrite /fst /snd in He; rewrite /snd in eB.
move=> i r.
have iB := getIndexBound Ht.
rewrite -/i in iB.
case E:  (nth (1, 1) LOGINV (i - 181)) => [l1 l2].
move=> z th tl.
have l1l2_in : (l1, l2) \in LOGINV.
  rewrite -E; apply: mem_nth.
  rewrite size_LOGINV.
  rewrite ltn_subLR; first by case/andP: iB.
  by case/andP: iB.
have  [H1 H2 H3 H4 H5]:= th_prop l1l2_in eB.
rewrite /fst in H1 H2 H3 H4 H5.
have [G1 G2 G3] := rt_float (refl_equal _) Ft Ht.
rewrite -[Z.to_nat _]/i in G1 G2 G3.
rewrite -[nth _ _ _]/r in G1 G2 G3.
have fast_cond : th <> 0 -> Rabs z <= Rabs th.
  move=> th_neq0.
  rewrite /th round_generic //.
  rewrite /z round_generic //.
  apply: Rle_trans G2 _.
  apply: Rle_trans (_ :  0.00587 <= _); first by interval.
  have [e_eq0|e_neq0] := Z.eq_dec e 0.
    have {}H3 := H3 e_eq0.
    case: H3; last by lra.
    by move=> HH; rewrite /th HH round_0 in th_neq0.
  have {}H4 := H4 e_neq0.
  by lra.
have [L1 L2 L3 [L4 L5]] := tl_prop l1l2_in eB.
  rewrite /snd -/tl in L1 L2 L3 L4 L5.
have [th_eq0|th_neq0] := Req_dec th 0.
  rewrite th_eq0 fastTwoSum_0l //; last first.
    by apply: generic_format_round.
  rewrite !(round_0, Rsimp01).
  split; try split; try by (move=> _; interval).
  - move=> _; rewrite round_generic //.
      by rewrite !Rsimp01; apply: bpow_ge_0.
    by apply: generic_format_round.
  - move=> _; rewrite round_generic //.
      by rewrite !Rsimp01; apply: bpow_ge_0.
    by apply: generic_format_round.
  - by apply: is_imul_pow_round.
  - rewrite /z round_generic //.
    by set xx := Rabs _ in G2 *; interval.
  - move=> e_eq0.
    rewrite /z round_generic //.
    by set xx := Rabs _ in G2 *; interval.
  - by apply: is_imul_pow_round.
  split.
    move=> e_eq0; rewrite round_generic //; last by apply: generic_format_round.
    have [->|tl_neq0] := Req_dec tl 0; first by interval.
    have := L2 e_eq0 tl_neq0.
    set xx := Rabs tl => ?; interval.
  move=> e_neq0; rewrite round_generic //; last by apply: generic_format_round.
  have [->|tl_neq0] := Req_dec tl 0; first by interval.
  have := L3 e_neq0 tl_neq0.
  by set xx := Rabs tl => ?; interval.
have imul_th : is_imul th (pow (- 42)).
  by apply: is_imul_pow_round.
have zE : z = r * t - 1 by rewrite /z round_generic.
rewrite -[bpow _ _ ]/(pow _) in G3.
rewrite -zE  in G1 G2 G3.
have imult_thz : is_imul (th + z) (pow (- 61)).
  apply: is_imul_add => //.
  by apply: is_imul_pow_le imul_th _.
have thzB1 : e <> 0%Z -> Rabs (th + z) < 744.9.
  move=> e_neq0.
  apply: Rle_lt_trans (Rabs_triang _ _) _.
  apply: Rle_lt_trans (_ : 744.8 + 33 * pow (- 13) < _); last first.
    by interval.
  apply: Rplus_le_compat => //.
  rewrite /th round_generic //.  
  by have := H5 e_neq0; lra.
have thzB2 : e = 0%Z -> Rabs (th + z) < 0.35103.
  move=> e_eq0.
  apply: Rle_lt_trans (Rabs_triang _ _) _.
  apply: Rle_lt_trans (_ : 0.347 + 33 * pow (- 13) < _); last first.
    by interval.
  apply: Rplus_le_compat => //.
  rewrite /th round_generic //.
  have ell1_neq0 : IZR e * LOG2H + l1 <> 0.
    contradict th_neq0.
    by rewrite /th th_neq0 round_0.
  by have := H3 e_eq0 ell1_neq0; lra.
case E1 : fastTwoSum => [h t1] l err2 err3.
have imul_h : is_imul h (pow (- 61)).
  have ->: h = RND (th + z) by case: E1.
  by apply: is_imul_pow_round.
have hB1 : e <> 0%Z -> Rabs h < 745.
  move=> e_neq0.
  have ->: h = RND (th + z) by case: E1.
  set y := th + z in thzB1 *.
  apply: Rle_lt_trans (_ : Rabs y + ulp y < _).
    by apply: error_le_ulp_add.
  have {}thzB1 := thzB1 e_neq0.
  have ulp_B : ulp y <= pow (10 - p).
    apply: bound_ulp => //.
    set yy := Rabs y in thzB1 *; interval.
  by set yy := Rabs y in thzB1 *; interval.
have hB2 : e = 0%Z -> Rabs h < 0.352.
  move=> e_eq0.
  have ->: h = RND (th + z) by case: E1.
  set y := th + z in thzB2 *.
  apply: Rle_lt_trans (_ : Rabs y + ulp y < _).
    by apply: error_le_ulp_add.
  have {}thzB2 := thzB2 e_eq0.
  have ulp_B : ulp y <= pow (-1 - p).
    apply: bound_ulp => //.
    set yy := Rabs y in thzB2 *; interval.
  by set yy := Rabs y in thzB2 *; interval.
have imul_hth : is_imul (h - th) (pow (-61)).
  apply: is_imul_minus => //.
  by apply: is_imul_pow_le imul_th _.
have hthB1 : e <> 0%Z -> Rabs (h - th) < 1490.
  move=> e_neq0.
  apply: Rle_lt_trans (Rabs_triang _ _) _.
  rewrite Rabs_Ropp.
  have -> : 1490 = 745 + 745 by lra.
  apply: Rplus_lt_compat; first by apply: hB1.
  rewrite /th round_generic //.
  by have := H5 e_neq0; lra.
have hthB2 : e = 0%Z -> Rabs (h - th) < 0.699.
  move=> e_eq0.
  apply: Rle_lt_trans (Rabs_triang _ _) _.
  rewrite Rabs_Ropp.
  apply: Rlt_le_trans (_ : 0.352 + 0.347 <= _); last by lra.
  apply: Rplus_lt_compat; first by apply: hB2.
  rewrite /th round_generic //.
  case: (H3 e_eq0); last by lra.
  contradict th_neq0.
  by rewrite /th th_neq0 round_0.
rewrite /fastTwoSum in E1.
rewrite -[FLT_exp _ _]/fexp in E1.
rewrite -![round _ _ _ _]/(RND _) in E1.
have XX : round radix2 fexp rnd (RND (th + z) - th) = RND (RND (th + z) - th).
  by [].
rewrite XX in E1.
have {}XX : round radix2 fexp rnd (z - RND (RND (th + z) - th)) = 
             RND(z - RND (RND (th + z) - th)).
  by [].
rewrite XX in E1.
case: (E1) => hE t1E.
rewrite hE in t1E.
have Fht : format (h - th).
  rewrite -hE.
  apply: sma_exact_abs_or0 => //.
  by apply: generic_format_round.
set s := h - th in imul_hth hthB1 hthB2 Fht.
have imul_t1 : is_imul t1 (pow (-61)).
  rewrite -t1E -/s.
  apply: is_imul_pow_round.
  rewrite [RND s]round_generic //.
  by apply: is_imul_minus.
have thzB3 : e <> 0%Z -> Rabs (th + z) < pow 10.
  move=> e_neq0.
  have := thzB1 e_neq0.
  by set xx := Rabs _ => ?; interval.
have thzB4 : e = 0%Z -> Rabs (th + z) < pow (-1).
  move=> e_eq0.
  have := thzB2 e_eq0.
  by set xx := Rabs _ => ?; interval.
have Fth : format th by apply: generic_format_round.
have t1B1 : e <> 0%Z -> Rabs t1 <= pow (- 43).
  move=> e_neq0.
  apply: Rle_trans (_ : ulp (th + z) <= _).
    rewrite -t1E -hE.
    by apply: sma_ulp.
  apply: bound_ulp => //.
  by apply: thzB3.
have t1B2 : e = 0%Z -> Rabs t1 <= pow (- 54).
  move=> e_eq0.
  apply: Rle_trans (_ : ulp (th + z) <= _).
    rewrite -t1E -hE.
    by apply: sma_ulp.
  apply: bound_ulp => //.
  by apply: thzB4.
have imul_t1tl : is_imul (t1 + tl) (pow (- 104)).
  apply: is_imul_add => //.
  by apply: is_imul_pow_le imul_t1 _.
have imul_l : is_imul l (pow (- 104)) by apply: is_imul_pow_round.
have t1tlB1 : e <> 0%Z -> Rabs (t1 + tl) <= Rpower 2 (- 33.79).
  move=> e_neq0.
  apply: Rle_trans (Rabs_triang _ _) _.
  apply: Rle_trans (_: pow (- 43) + Rpower 2 (- 33.8) <= _); last by interval.
  apply: Rplus_le_compat; first by apply: t1B1.
  have [->|tl_neq0] := Req_dec tl 0; first by interval.
  have := L3 e_neq0 tl_neq0.
  by case.
have t1tlB2 : e = 0%Z -> Rabs (t1 + tl) <= Rpower 2 (- 42.9).
  move=> e_eq0.
  apply: Rle_trans (Rabs_triang _ _) _.
  apply: Rle_trans (_: pow (- 54) + pow (- 43) <= _); last by interval.
  apply: Rplus_le_compat; first by apply: t1B2.
  have [->|tl_neq0] := Req_dec tl 0; first by interval.
  have := L2 e_eq0 tl_neq0.
  by case.
have ulp_t1tlB1 : e <> 0%Z -> ulp (t1 + tl) <= pow (-86).
  move=> e_neq0.
  apply: bound_ulp => //.
  have {}t1tlB1 := t1tlB1 e_neq0.
  by set xx := Rabs _ in t1tlB1 *; interval.
have ulp_t1tlB2 : e = 0%Z -> ulp (t1 + tl) <= pow (- 95).
  move=> e_eq0.
  apply: bound_ulp => //.
  have {}t1tlB2 := t1tlB2 e_eq0.
  by set xx := Rabs _ in t1tlB2 *; interval.
split => //; split => //.
- move=> e_eq0.
  apply: Rle_trans (_ : pow (- 105) * Rabs h <= _).
    rewrite /err2.
    have := @fastTwoSum_correct th z Fth G1.
    rewrite [fastTwoSum _ _]E1.
    by apply.
  have := hB2 e_eq0.
  by set xx := Rabs h => ?; interval.
- move=> e_neq0.
  apply: Rle_trans (_ : pow (- 105) * Rabs h <= _).
    rewrite /err2.
    have := @fastTwoSum_correct th z Fth G1.
    rewrite [fastTwoSum _ _]E1.
    by apply.
  have := hB1 e_neq0.
  by set xx := Rabs h => ?; interval.
- move=> e_eq0.
  apply: Rle_trans (_ : ulp (t1 + tl) <= _); first by apply: error_le_ulp.
  by apply: ulp_t1tlB2.
- move=> e_neq0.
  apply: Rle_trans (_ : ulp (t1 + tl) <= _); first by apply: error_le_ulp.
  by apply: ulp_t1tlB1.
- by have [/hB2|/hB1 //] := Z.eq_dec e 0; lra.
split.
  move=> e_eq0; rewrite /l; set xx := t1 + tl.
  apply: Rle_trans (_ : Rabs xx + ulp xx <= _).
    by apply: error_le_ulp_add.
  have {}t1tlB2 := t1tlB2 e_eq0.
  have {}ulp_t1tlB2 := ulp_t1tlB2 e_eq0.
  rewrite -/xx in t1tlB2 ulp_t1tlB2.
by interval.
move=> e_neq0; rewrite /l; set xx := t1 + tl.
apply: Rle_trans (_ : Rabs xx + ulp xx <= _).
  by apply: error_le_ulp_add.
have {}t1tlB1 := t1tlB1 e_neq0.
have {}ulp_t1tlB1 := ulp_t1tlB1 e_neq0.
rewrite -/xx in t1tlB1 ulp_t1tlB1.
by interval.
Qed.

Lemma err23_bound  x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t1 := fastTwoSum th z in 
  let l := RND (t1 + tl) in
  let err2 := Rabs ((h + t1) - (th + z)) in 
  let err3 := Rabs (l - (t1 + tl)) in
  let err23 := err2 + err3 in 
  (e = 0%Z -> err23 <= Rpower 2 (- 94.999)) /\ 
  (e <> 0%Z -> err23 <= Rpower 2 (- 85.995)).
Proof.
move=> Fx xB.
case E : getRange => [t e] i r.
case E1 : nth => [l1 l2] z th tl.
case E2 : fastTwoSum => [h t1] l err2 err3 err23.
have F1 := err2_err3_h_l_bound Fx xB.
lazy zeta in F1.
rewrite E E1 E2 in F1.
have {}[[err2B1 err2B2] [err3B1 err3B2] [lB1 lB2] imul_l] := F1.
rewrite -/th -/tl -/l -/err3 -/err2 in err2B1 err2B2 err3B1 err3B2 lB1 lB2 imul_l.
split => [e_eq0|e_neq0].
  have {}err2B1 := err2B1 e_eq0.
  have {}err3B1 := err3B1 e_eq0.
  by rewrite /err23; interval.
have {}err2B2 := err2B2 e_neq0.
have {}err3B2 := err3B2 e_neq0.
by rewrite /err23; interval.
Qed.

Lemma h_l_bound  x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t1 := fastTwoSum th z in 
  let l := RND (t1 + tl) in
  [/\ is_imul h (pow (-61)), Rabs h < 745,
      e = 0%Z -> Rabs h < 0.352, is_imul l (pow (- 104)) &
      ((e = 0%Z -> Rabs l <= Rpower 2 (- 42.89)) /\
       (e <> 0%Z -> Rabs l <= Rpower 2 (- 33.78)))].     
Proof.
move=> Fx xB.
case E : getRange => [t e] i r.
case E1 : nth => [l1 l2] z th tl.
case E2 : fastTwoSum => [h t1].
have F1 := err2_err3_h_l_bound Fx xB.
lazy zeta in F1.
rewrite E E1 E2 in F1.
by have {}[[err2B1 err2B2] [err3B1 err3B2] [lB1 lB2] imul_l] := F1.
Qed.

Lemma err5_lp_bound  x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t1 := fastTwoSum th z in 
  let l := RND (t1 + tl) in
  let: DWR ph pl := p1 z in
  let lp := l + pl in 
  let err5 := Rabs (RND lp - lp) in
  err5 <= pow (- 78) /\ Rabs (RND lp) < Rpower 2 (- 25.4409).
Proof.
move=> Fx xB.
case E : getRange => [t e] i r.
case E1 : nth => [l1 l2] z th tl.
case E2 : fastTwoSum => [h t1] l.
case E3 : p1 => [ph pl] lp err5.
have [imul_l hB imul_h] : 
  [/\ is_imul l (pow (-104)), Rabs h < 745 & is_imul h (pow (- 61))].
  have F1 := h_l_bound Fx xB.
  lazy zeta in F1.
  rewrite E E1 E2 in F1.
  by have [] := F1.
have Fz : format z by apply: generic_format_round.
have Ft : format t by have := getRangeFormat Fx xB; rewrite E.
have tB : / sqrt 2 < t < sqrt 2.
  by have [] := getRangeCorrect Fx xB; rewrite E.
have zB : Rabs z <= 33 * pow (- 13).
  have [] := rt_float _ Ft tB => //.
  rewrite -/r -/z => Frt1 rtB _.
  by rewrite /z round_generic.  
have imul_z : is_imul z (pow (- 61)).
  have [] := rt_float _ Ft tB  => // _ _ F1.
  by apply: is_imul_pow_round.
have imul_pl : is_imul pl (pow (- 543)).
  have := @imul_pl_p1 _ rnd _ z Fz zB.
  by rewrite E3; apply.
have imul_lp : is_imul lp (pow (- 543)).
  apply: is_imul_add => //.
  by apply: is_imul_pow_le imul_l _.
have lB : Rabs l <= Rpower 2 (-33.78).
  have F1 := h_l_bound Fx xB.
  lazy zeta in F1.
  rewrite E E1 E2 in F1.
  have {}[_ _ _ _ [H1 H2]] := F1.
  have [e_eq0|e_neq0] := Z.eq_dec e 0.
    have {}H1 := H1 e_eq0.
    rewrite -/l in H1.
    set xx := Rabs l in H1 *; interval.
  by have {}H2 := H2 e_neq0.
have plB : Rabs pl < Rpower 2 (-25.446).
  have := @pl_bound_p1 _ rnd _ z Fz zB.
  by rewrite E3; apply.
have lplB : Rabs (l + pl) < Rpower 2 (- 25.441).
  apply: Rle_lt_trans (Rabs_triang _ _) _.
  by set xx := Rabs l in lB *; set yy := Rabs pl in lB *; interval.
have ulplB : ulp (l + pl) <= pow (- 78).
  apply: bound_ulp => //.
  by set xx := Rabs (l + pl) in lplB *; interval.
have err5B : err5 <= pow (-78).
  apply: Rle_trans ulplB.
  by apply: error_le_ulp.
split => //.
apply: Rle_lt_trans (_ : Rabs (l + pl) + ulp (l + pl) < _).
  by apply: error_le_ulp_add.
by set xx := Rabs (l + pl) in lplB; interval.
Qed.

Lemma err5_bound x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t1 := fastTwoSum th z in 
  let l := RND (t1 + tl) in
  let: DWR ph pl := p1 z in
  let lp := l + pl in 
  let err5 := Rabs (RND lp - lp) in
  err5 <= pow (- 78).
Proof.
move=> Fx xB.
case E : getRange => [t e] i r.
case E1 : nth => [l1 l2] z th tl.
case E2 : fastTwoSum => [h t1] l.
case E3 : p1 => [ph pl] lp err5.
have F1 := err5_lp_bound Fx xB.
lazy zeta in F1.
by rewrite E E1 E2 E3 in F1; have [] := F1.
Qed.

Lemma lp_bound  x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t1 := fastTwoSum th z in 
  let l := RND (t1 + tl) in
  let: DWR ph pl := p1 z in
  let lp := l + pl in 
  let err5 := Rabs (RND lp - lp) in
  Rabs (RND lp) < Rpower 2 (- 25.4409).
Proof.
move=> Fx xB.
case E : getRange => [t e] i r.
case E1 : nth => [l1 l2] z th tl.
case E2 : fastTwoSum => [h t1] l.
case E3 : p1 => [ph pl] lp err5.
have F1 := err5_lp_bound Fx xB.
lazy zeta in F1.
by rewrite E E1 E2 E3 in F1; have [] := F1.
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

Lemma relative_error_eps_le x :
  is_imul x (pow (emin + p - 1)) ->
  Rabs x * (1 - pow (- p + 1)) <=  Rabs (RND x).
Proof.
move=> xB.
have [->|x_neq0] := Req_dec x 0; first by rewrite !(round_0, Rsimp01); lra.
have F1 :  Rabs (RND x - x) < pow (- p + 1) * Rabs x.
  apply: relative_error_FLT => //.
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
  apply: relative_error_FLT => //.
  by apply: is_imul_pow_le_abs.
by split_Rabs; nra.
Qed.

Lemma err4_err6_h'_l'_bound  x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t1 := fastTwoSum th z in 
  let l := RND (t1 + tl) in
  let: DWR ph pl := p1 z in
  let lp := l + pl in 
  let: DWR h' t' := fastTwoSum h ph in
  let l' := RND (t' + RND lp) in   
  let err4 := Rabs ((h' + t') - (h + ph)) in
  let err6 := Rabs (l' - (t' + RND lp)) in
  [/\ err4 + err6 <= Rpower 2 (- 77.9999),
      [/\ is_imul h' (pow (- 123)), Rabs h' <= 746 & e = 0%Z -> Rabs h' <= 0.353
       ] & 
      is_imul l' (pow (- 543)) /\ Rabs l' <= Rpower 2 (- 25.4407)].
Proof.
move=> Fx xB.
case E : getRange => [t e] i r.
case E1 : nth => [l1 l2] z th tl.
case E2 : fastTwoSum => [h t1] l.
case E3 : p1 => [ph pl] lp.
case E4 : fastTwoSum => [h' t'] l' err4 err6.
have [imul_l hB1 hB2 imul_h] : 
  [/\ is_imul l (pow (-104)), Rabs h < 745,
      e = 0%Z -> Rabs h < 0.352 & is_imul h (pow (- 61))].
  have F1 := h_l_bound Fx xB.
  lazy zeta in F1.
  rewrite E E1 E2 in F1.
  by have [] := F1.
have Fz : format z by apply: generic_format_round.
have Ft : format t by have := getRangeFormat Fx xB; rewrite E.
have tB : / sqrt 2 < t < sqrt 2.
  by have [] := getRangeCorrect Fx xB; rewrite E.
have iB := getIndexBound tB.
have l1l2_in : (l1, l2) \in LOGINV.
  rewrite -E1; apply: mem_nth.
  rewrite size_LOGINV.
  rewrite ltn_subLR; first by case/andP: iB.
  by case/andP: iB.
have zB : Rabs z <= 33 * pow (- 13).
  have [] := rt_float _ Ft tB => //.
  rewrite -/r -/z => Frt1 rtB _.
  by rewrite /z round_generic.  
have imul_z : is_imul z (pow (- 61)).
  have [] := rt_float _ Ft tB => //.
  rewrite -/r -/z => Frt1 rtB imul_rt.
  by rewrite /z round_generic.
have imul_ph : is_imul ph (pow (- 123)).
  have := @imul_ph_p1 _ rnd _ _ Fz zB.
  by rewrite E3; apply.
have phB : Rabs ph < Rpower 2 (-16.9).
  have := ph_bound_p1 _ Fz zB imul_z.
  by case: E3 => <- _; apply.
have imul_pl : is_imul pl (pow (- 543)).
  have := @imul_pl_p1 _ rnd _ z Fz zB.
  by rewrite E3; apply.
have imul_lp : is_imul lp (pow (- 543)).
  apply: is_imul_add => //.
  by apply: is_imul_pow_le imul_l _.
have rlpB : Rabs (RND lp) <= Rpower 2 (-25.4409).
  have := lp_bound Fx xB.
  by lazy zeta; rewrite E E1 E2 E3 -/lp; lra.
have [h_eq0|h_neq0] := Req_dec h 0.
  have h'E : h' = ph.
    rewrite h_eq0 fastTwoSum_0l // in E4; first by case: E4.
    case: E3 => <- _.
    by apply: generic_format_round.
  have t'E : t' = 0.
    rewrite h_eq0 fastTwoSum_0l // in E4; first by case: E4.
    case: E3 => <- _.
    by apply: generic_format_round.
  have l'E : l' = RND lp.
    by rewrite /l' t'E Rsimp01 round_generic //; apply: generic_format_round.
  rewrite /err4 /err6 h'E l'E t'E h_eq0 !Rsimp01.
  split => //; try split => //; first by interval.
  - by apply: Rle_trans (Rlt_le _ _ phB) _; interval.
  - by move=> _; apply: Rle_trans (Rlt_le _ _ phB) _; interval.
  - by apply: is_imul_pow_round.
  by apply: Rle_trans rlpB _; interval.
have eB := getRange_bound Fx xB; rewrite E /snd in eB.
have imul_th : is_imul th (pow (- 42)).
  apply: is_imul_pow_round.
  by have [] := th_prop l1l2_in eB.
have hE : h = RND (th + z) by case: E2.
have Fh : format h.
  by rewrite hE; apply: generic_format_round.
have Fph : format ph.
  by case: E3 => <- _; apply: generic_format_round.
have fast_cond : h <> 0 -> Rabs ph <= Rabs h.
  move=> _.
  have [th_eq0|th_neq0] := Req_dec th 0.
    have hE1 : h = z.
      rewrite th_eq0 fastTwoSum_0l // in E2.
      by case: E2.
    rewrite hE1.
    have zB1 : Rabs z <= 1 by set xx := Rabs z in zB *; interval.
    have z2B : z * z <= Rabs z.
       have -> : z * z = Rabs z * Rabs z by split_Rabs; lra.
       suff : 0 <= Rabs z by nra.
       by apply: Rabs_pos.
    apply: Rle_trans (_ : RND (z * z) <= _) => //.
      have phE : ph = - 0.5 * RND (z * z).
        case: E3 => <- _.
        rewrite -[round _ _ _]/RND round_generic //.
        have -> : -0.5 * RND (z * z) = - (0.5 * RND (z * z)) by lra.
        have imul_zz : is_imul ((z * z)) (pow (- 122)).
          have -> : (- 122 = (- 61) + (- 61))%Z by [].
          by rewrite bpow_plus; apply: is_imul_mul.
        have imul_rzz : is_imul (RND (z * z)) (pow (- 122)).
          by apply: is_imul_pow_round.
        apply: generic_format_opp.
        apply: is_imul_format_half imul_rzz _ => //.
        by apply: generic_format_round.
      have tphE : 2 * Rabs ph = RND (z * z).
        suff : 0 <= RND (z * z) by rewrite phE; split_Rabs; lra.
        have -> : 0 = RND 0 by rewrite round_0.
        by apply: round_le; nra.
      rewrite -tphE.
      by split_Rabs; lra.
    have-> : Rabs z = RND (Rabs z).
      rewrite round_generic //. 
      by apply: generic_format_abs.
    by apply: round_le.
  rewrite hE.
  apply: Rle_trans (_ :  Rabs (th + z) * (1 - pow (- p + 1)) <= _); last first.
    apply: relative_error_eps_le.
    apply: is_imul_pow_le (_ : is_imul _ (pow (- 61))) _ => //.
    apply: is_imul_add => //.
    by apply: is_imul_pow_le imul_th _.
  have pow1p_gt_0 : 0 < 1 - pow (- p + 1) by interval.
  apply: Rle_trans (_ :  (Rabs th - Rabs z) * (1 - pow (- p + 1)) <= _); last first.
    by split_Rabs; nra.
  apply: Rle_trans (_ : Rpower 2 (-16.9) <= _); first by lra.
  apply: Rle_trans (_ : (0.00587 - 33 * pow (- 13)) * (1 - pow (- p + 1)) <= _).
    by interval.
  suff : 0.00587 <= Rabs th  by nra.
  have  [H1 H2 H3 H4 H5]:= th_prop l1l2_in eB.
  rewrite /fst in H3 H5.
  rewrite /th round_generic //.
  have [e_eq0|e_neq0] := Z.eq_dec e 0.
    have {}H3 := H3 e_eq0.
    case: H3; last by lra.
    by move=> HH; rewrite /th HH round_0 in th_neq0.
  have {}H5 := H5 e_neq0.
  by lra.
have imulhph : is_imul (h + ph) (pow (- 123)).
  apply: is_imul_add => //.
  by apply: is_imul_pow_le imul_h _.
have hphB1 : Rabs (h + ph) <= 745 + Rpower 2 (- 16.9).
  by apply: Rle_trans (Rabs_triang _ _) _; lra.
have hphB2 : e = 0%Z -> Rabs (h + ph) <= 0.352 + Rpower 2 (- 16.9).
  move=> e_eq0.
  apply: Rle_trans (Rabs_triang _ _) _.
  have {}hB2 := hB2 e_eq0; lra.
have h'E: h' = RND (h + ph) by case: E4.
have imul_h' : is_imul h' (pow (- 123)).
  by rewrite h'E; apply: is_imul_pow_round.
have h'B1 : Rabs h' <= 746.
  apply: Rle_trans (_ : (Rabs (h + ph) + ulp (h + ph)) <= _).
    by rewrite h'E; apply: error_le_ulp_add.
  apply: Rle_trans (_ : (745 + Rpower 2 (-16.9)) + pow (10 - p) <= _); last first.
    by interval.
  apply: Rplus_le_compat => //.
  apply: bound_ulp => //.
  apply: Rle_lt_trans hphB1 _.
  by interval.
have h'B2 : e = 0%Z -> Rabs h' <= 0.353.
  move=> e_eq0.
  apply: Rle_trans (_ : (Rabs (h + ph) + ulp (h + ph)) <= _).
    by rewrite h'E; apply: error_le_ulp_add.
  apply: Rle_trans (_ : (0.352 + Rpower 2 (-16.9)) + pow (10 - p) <= _); last first.
    by interval.
  apply: Rplus_le_compat => //.
    by apply: hphB2.
  apply: bound_ulp => //.
  apply: Rle_lt_trans hphB1 _.
  by interval.  
have imul_h'h : is_imul (h' - h) (pow (- 123)).
  apply: is_imul_minus => //.
  by apply: is_imul_pow_le imul_h _.
have h'hB : Rabs (h' - h) <= 2 * 746.
  apply: Rle_trans (_ : Rabs h' + Rabs h <= _); last by lra.
  by split_Rabs; lra.
have Fht : format (h' - h).
  rewrite h'E.
  by apply: sma_exact_abs_or0.
have t'E : t' = RND (h + ph - h').
  case: E4 => _ <-.
  rewrite -[round _ _ _ (_ + _)]/(RND _).
  rewrite -[round _ _ _ (_ - _)]/(RND _).
  rewrite -[round _ _ _ (_ - h)]/(RND _).
  by rewrite -h'E [RND (_ - h)]round_generic //; congr (RND _); lra.
have imul_t' : is_imul t' (pow (- 123)).
  rewrite t'E; apply: is_imul_pow_round.
  by apply: is_imul_minus.
have t'B : Rabs t' <= pow (- 43).
  apply: Rle_trans (_ : ulp (h + ph) <= _).
    by case: E4 => _ <-; apply: sma_ulp.
  apply: bound_ulp => //.
  apply: Rle_lt_trans hphB1 _.
  by interval.
have err4B : err4 <= Rpower 2 (- 95.45).
  apply: Rle_trans (_ : pow (- 105) * Rabs h' <= _).
    by rewrite /err4; have := fastTwoSum_correct Fh Fph; rewrite E4; apply.
  apply: Rle_trans (_ : pow (- 105) * 746 <= _); last by interval.
  suff : 0 <= pow (- 105) by nra.
  by apply: bpow_ge_0.
have imul_t'rlp : is_imul (t' + RND lp) (pow (- 543)).
  apply: is_imul_add; first by apply: is_imul_pow_le imul_t' _.
  apply: is_imul_pow_round.
  by apply: is_imul_add => //; apply: is_imul_pow_le imul_l _.
have t'rlpB : Rabs (t' + RND lp) <= Rpower 2 (- 25.4408).
  apply: Rle_trans (Rabs_triang _ _) _.
  apply: Rle_trans (_ : pow (- 43) + Rpower 2 (- 25.4409) <= _); last by interval.
  by lra.
split => //.
- suff : err6 <= pow (- 78) by move=> ?; interval.
  rewrite /err6.
  apply: Rle_trans (_ : ulp (t' + RND lp) <= _); first by apply: error_le_ulp.
  apply: bound_ulp => //.
  apply: Rle_lt_trans t'rlpB _.
  by interval.
split => //.
  apply: is_imul_pow_round.
  apply: is_imul_add; first by apply: is_imul_pow_le imul_t' _.
  by apply: is_imul_pow_round.
apply: Rle_trans (_ : Rpower 2 (- 25.4408) * (1 + pow (- 52)) <= _); last first.
  by interval.
rewrite /l'.
apply: Rle_trans (_ : Rabs (t' + RND lp) * (1 + pow (- 52)) <= _).
  apply: relative_error_eps_ge.
  rewrite [(_ - 1)%Z]/=.
  apply: is_imul_add; first by apply: is_imul_pow_le imul_t' _.
  apply: is_imul_pow_round.
  by apply: is_imul_pow_le imul_lp _.
suff : 0 < (1 + pow (- 52)) by nra.
by interval.
Qed.

Lemma err4_err6_bound  x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t1 := fastTwoSum th z in 
  let l := RND (t1 + tl) in
  let: DWR ph pl := p1 z in
  let lp := l + pl in 
  let: DWR h' t' := fastTwoSum h ph in
  let l' := RND (t' + RND lp) in   
  let err4 := Rabs ((h' + t') - (h + ph)) in
  let err6 := Rabs (l' - (t' + RND lp)) in
  err4 + err6 <= Rpower 2 (- 77.9999).
Proof.
move=> Fx xB.
case E : getRange => [t e] i r.
case E1 : nth => [l1 l2] z th tl.
case E2 : fastTwoSum => [h t1] l.
case E3 : p1 => [ph pl] lp.
case E4 : fastTwoSum => [h' t'] l' err4 err6.
have := err4_err6_h'_l'_bound Fx xB.
by lazy zeta; rewrite E E1 E2 E3 E4; case.
Qed.

Lemma h'_l'_bound  x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t1 := fastTwoSum th z in 
  let l := RND (t1 + tl) in
  let: DWR ph pl := p1 z in
  let lp := l + pl in 
  let: DWR h' t' := fastTwoSum h ph in
  let l' := RND (t' + RND lp) in   
  [/\ is_imul h' (pow (- 123)), Rabs h' <= 746, e = 0%Z -> Rabs h' <= 0.353,
      is_imul l' (pow (- 543)) & Rabs l' <= Rpower 2 (- 25.4407)].
Proof.
move=> Fx xB.
case E : getRange => [t e] i r.
case E1 : nth => [l1 l2] z th tl.
case E2 : fastTwoSum => [h t1] l.
case E3 : p1 => [ph pl] lp.
case E4 : fastTwoSum => [h' t'] l'.
have := err4_err6_h'_l'_bound Fx xB.
lazy zeta; rewrite E E1 E2 E3 E4.
by case => ? [? ? ?] [? ?]; split.
Qed.

Lemma err9_bound  x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t1 := fastTwoSum th z in 
  let l := RND (t1 + tl) in
  let: DWR ph pl := p1 z in
  let lp := l + pl in 
  let: DWR h' t' := fastTwoSum h ph in
  let l' := RND (t' + RND lp) in   
  let: DWR h'' l'' := fastTwoSum h' l' in
  let err9 := Rabs ((h'' + l'') - (h' + l')) in 
  e = 0%Z -> i <> 255%N -> i <> 256%N -> err9 <= Rpower 2 (- 106.502).
Proof.
move=> Fx xB.
case E : getRange => [t e] i r.
case E1 : nth => [l1 l2] z th tl.
case E2 : fastTwoSum => [h t1] l.
case E3 : p1 => [ph pl] lp.
case E4 : fastTwoSum => [h' t'] l'.
case E5 : fastTwoSum => [h'' l''] err9 e_eq0 iD255 iD256.
have := h'_l'_bound Fx xB.
lazy zeta; rewrite E E1 E2 E3 E4 -/l' => [] [imul_h' h'B1 h'B2 imul_l' l'B].
have Fh' : format h' by case: E4 => <- _; apply: generic_format_round.
have Fl' : format l' by apply: generic_format_round.
have tB : / sqrt 2 < t < sqrt 2.
  by have [] := getRangeCorrect Fx xB; rewrite E.
have iB := getIndexBound tB.
have l1l2_in : (l1, l2) \in LOGINV.
  rewrite -E1; apply: mem_nth.
  rewrite size_LOGINV.
  rewrite ltn_subLR; first by case/andP: iB.
  by case/andP: iB.
have Fl1 : format l1 by have [] :=  format_LOGINV _ l1l2_in. 
have thE : th = l1 by rewrite /th e_eq0 !Rsimp01 round_generic.
have l1B : l1 <> 0 -> 0.00587 < Rabs l1 < 0.347.
  suff /l1_LOGINV[] : (i - 181 < size LOGINV)%N by rewrite E1.
  by rewrite ltn_subLR; case/andP: iB.
have {}/l1B l1B : l1 <> 0.
  have := iN255_N256_l1_neq_1 iB iD255 iD256.
  by lazy zeta; rewrite E1.
have thB : 0.00587 <= Rabs th by rewrite thE; lra.
have [h'_eq0|h'_neq0] := Req_dec h' 0.
  have h''El' : h'' = l'.
    by rewrite h'_eq0 fastTwoSum_0l // in E5; case: E5.   
  have l''E0 : l'' = 0.
    by rewrite h'_eq0 fastTwoSum_0l // in E5; case: E5.
  suff -> : err9 = 0 by interval. 
  by rewrite /err9 h''El' l''E0 h'_eq0 !Rsimp01.
have h''E : h'' = RND (h' + l') by case: E5 => <-.
have hE : h = RND (th + z) by case: E2 => <- _.
have Ft : format t by have := getRangeFormat Fx xB; rewrite E.
have zB : Rabs z <= 33 * pow (- 13).
  have [] := rt_float _ Ft tB => //.
  rewrite -/r -/z => Frt1 rtB _.
  by rewrite /z round_generic.  
have thzB : 587 / 100000  - 33 * pow (- 13) <= Rabs (th + z).
  apply: Rle_trans (_ : Rabs th - Rabs z <= _); last by clear; split_Rabs; lra.
  by lra.
have imul_z : is_imul z (pow (- 61)).
  have [] := rt_float _ Ft tB  => // _ _ F1.
  by apply: is_imul_pow_round.
have eB := getRange_bound Fx xB; rewrite E /snd in eB.
have imul_th : is_imul th (pow (- 42)).
  apply: is_imul_pow_round.
  by have [] := th_prop l1l2_in eB.
have hB : Rpower 2 (- 9.09) <= Rabs h.
  apply: Rle_trans (_ : Rabs (th + z) * (1 - pow (- 52)) <= _); last first.
    rewrite hE.
    apply: relative_error_eps_le.
    apply: is_imul_add; first by apply: is_imul_pow_le imul_th _.
    by apply: is_imul_pow_le imul_z _.
  apply: Rle_trans (_ : (587 / 100000 - 33 * pow (-13))
                        * (1 - pow (- 52)) <= _); first by interval.
  suff : 0 <= 1 - pow (-52) by nra.
  by interval.
have h'E : h' = RND (h + ph) by case: E4 => <- _.
have Fz : format z by apply: generic_format_round.
have phB : Rabs ph <= Rpower 2  (- 16.9).
  apply: Rlt_le; case: E3 => <- _.
  by have := ph_bound_p1 _ Fz zB imul_z; apply.
have hphB : Rpower 2 (-9.09)  - Rpower 2 (-16.9) <= Rabs (h + ph).
  apply: Rle_trans (_ : Rabs h - Rabs ph <= _); last by clear; split_Rabs; lra.
  by lra.
have imul_thz : is_imul (th + z) (pow (- 61)).
  apply: is_imul_add => //.
  by apply: is_imul_pow_le imul_th _.
have imul_h : is_imul h (pow (- 61)).
  by rewrite hE; apply: is_imul_pow_round.
have imul_ph : is_imul ph (pow (- 123)).
  have := @imul_ph_p1 _ rnd _ _ Fz zB.
  by rewrite E3; apply.
have h'B3 : Rpower 2 (- 9.1) <= Rabs h'.
  apply: Rle_trans (_ : Rabs (h + ph) * (1 - pow (- 52)) <= _); last first.
    rewrite h'E.
    apply: relative_error_eps_le.
    apply: is_imul_add; first by apply: is_imul_pow_le imul_h _.
    by apply: is_imul_pow_le imul_ph _.
  apply: Rle_trans (_ : (Rpower 2 (-9.09) - Rpower 2 (-16.9)) *
                                     (1 - pow (-52)) <= _); first by interval.
  suff : 0 <= 1 - pow (-52) by nra.
  by interval.  
have l'B1 :  Rabs l' <= Rpower 2 (- 25.4407). 
  have := h'_l'_bound Fx xB.
  by lazy zeta; rewrite E E1 E2 E3; case.
have l'Lh' : Rabs l' <= Rabs h'.
  apply: Rle_trans h'B3.
  apply: Rle_trans l'B1 _.
  by interval.
have l''E : l'' = RND (l' + h' - h'').
  case: E5 => _ <-.
  rewrite -[round _ _ _ _]/(RND _).
  rewrite -[round _ _ _ (_ + l')]/(RND _).
  rewrite -[round _ _ _ (_ - h')]/(RND _).
  rewrite [RND (_ - h')]round_generic //.
    by rewrite -h''E; congr (RND _); lra.
  by apply: sma_exact_abs_or0.
have {}h'B2 := h'B2 e_eq0.
apply: Rle_trans 
  (_ : pow (- 105) * (0.353 + Rpower 2 (- 25.4407)) * (1 + pow (- 52)) <= _);
    last by interval.
apply: Rle_trans (_ : pow (-105) * Rabs h'' <= _).
  have := fastTwoSum_correct Fh' Fl' (fun _ => l'Lh').
  rewrite -[round _ _ _ _]/(RND _).
  rewrite -[round _ _ _ (_ - _)]/(RND _).
  rewrite -[round _ _ _ (_ - h')]/(RND _).
  rewrite /err9 h''E.
  rewrite [RND (_ - h')]round_generic //; last by apply: sma_exact_abs_or0.
  rewrite -h''E l''E.
  have -> : l' - (h'' - h') =  l' + h' - h'' by lra.
  by apply.
suff : Rabs h'' <= (0.353 + Rpower 2 (-25.4407)) * (1 + pow (-52)).
  have: 0 < pow (-105) by apply: bpow_gt_0.
  by nra.
apply: Rle_trans (_ : Rabs (h' + l') * (1 + pow (-52)) <= _).
  rewrite h''E; apply: relative_error_eps_ge.
  apply: is_imul_add; first by apply: is_imul_pow_le imul_h' _.
  by apply: is_imul_pow_le imul_l' _.
suff : Rabs (h' + l') <= (0.353 + Rpower 2 (-25.4407)).
  have : 0 < (1 + pow (-52)) by interval.
  by nra.
apply: Rle_trans (Rabs_triang _ _) _.
by apply: Rplus_le_compat; lra.
Qed.

Lemma err_lem4_e_neq0_i x : 
  format x -> alpha <= x <= omega ->
  let: (t, e) := getRange x in
  e <> 0%Z ->
  let: DWR h l := log1 x in
  let elog := Rpower 2 (- 73.527) in
  Rabs l <= Rpower 2 (- 23.89) * Rabs h /\ 
  Rabs (h + l - ln x) <= elog * Rabs (ln x).
Proof.
move=> Fx xB; rewrite /log1 /fastSum.
case E : getRange => [t e] e_neq0.
have-> : (e =? 0)%Z = false by lia.
set i := getIndex _.
case E1 : nth => [l1 l2].
set r  := nth 1 INVERSE _.
set z  := RND (r * t  - 1).
set th := RND (IZR e * LOG2H + l1). 
set tl := RND (IZR e * LOG2L + l2).
case E2 : (fastTwoSum th z) => [h t1].
set l := RND (t1 + tl).
case E3 : p1 => [ph pl].
set lp := l + pl. 
case E4 : fastTwoSum => [h' t'].
set l' := RND (t' + RND lp).
have tB : / sqrt 2 < t < sqrt 2.
  by have [] := getRangeCorrect Fx xB; rewrite E.
have iB := getIndexBound tB; rewrite -/i in iB.
have eB := getRange_bound Fx xB; rewrite E /snd in eB.
have Ft : format t by have := getRangeFormat Fx xB; rewrite E.
have l1l2_in : (l1, l2) \in LOGINV.
  rewrite -E1; apply: mem_nth.
  rewrite size_LOGINV.
  rewrite ltn_subLR; first by case/andP: iB.
  by case/andP: iB. 
have x_neq1 : x <> 1.
  contradict e_neq0.
  have := getRangeCorrect Fx xB; rewrite E /fst /snd e_neq0 => [] [tB1 tE].
  (* Rework this*)
  suff :  ~(e <= -1 \/ 1 <= e)%Z by lia.
  case => [eLN1|eG1].
    have peLN1: pow e <= pow (- 1) by apply: bpow_le.
    have : ~ (1 <= t * pow (-1)).
      suff: t * pow (- 1) < 1 by lra.
      interval.
    rewrite tE; suff : 0 < t by nra.
    interval.
  have peG1: pow 1 <= pow e by apply: bpow_le.
  have : ~ (t * pow 1 <= 1).
    suff: 1 < t * pow 1 by lra.
    interval.
  rewrite tE; suff : 0 < t by nra.
  interval.
have l'B : Rabs l' <= Rpower 2 (- 25.4407).
  have := h'_l'_bound Fx xB.
  by lazy zeta; rewrite E E1 E2 E3; case; case: E4 => _ -> apply.
have thB : 0.346147 <= Rabs th.
  have  [_ H1 _ /(_ e_neq0) H2 _]:= th_prop l1l2_in eB.
  by rewrite /th round_generic.
have zB : Rabs z <= 33 * pow (- 13).
  have [] := rt_float _ Ft tB => //.
  rewrite -/r -/z => Frt1 rtB _.
  by rewrite /z round_generic.
have hB : 0.342118 <= Rabs h.
  apply: Rle_trans (_ : Rabs (th + z) * (1 - pow (- 52)) <= _); last first.
    have -> : h = RND (th + z) by case: E2=> -> _.
    apply: relative_error_eps_le.
    apply: is_imul_add.
      suff/is_imul_pow_le : is_imul th (pow (- 42)) by apply.
      apply: is_imul_pow_round.
      by have  [] := th_prop l1l2_in eB.
    suff /is_imul_pow_le : is_imul z (pow (- 61)) by apply.
    have [] := rt_float _ Ft tB  => // _ _ F1.
    by apply: is_imul_pow_round.
  have pP : 0 < 1 - pow (-52) by interval.
  apply: Rle_trans (_ : (Rabs th - Rabs z) * (1 - pow (-52)) <= _); last first.
    suff: Rabs th - Rabs z <= Rabs (th + z) by nra.
    clear; split_Rabs; lra.
  apply: Rle_trans (_ : (0.346147 - 33 * pow (-13)) * (1 - pow (-52)) <= _).
    have -> : 0.342118 = 342118 / 1000000 by lra.
    have -> : 0.346147 = 346147 / 1000000 by lra.
    by interval.
  by nra.
have Fz : format z by apply: generic_format_round.
  have imul_z : is_imul z (bpow radix2 (-61)).
  have [] := rt_float _ Ft tB  => // _ _ F1.
  by apply: is_imul_pow_round.
have h'B : 0.342 <= Rabs h'.
  apply: Rle_trans (_ : Rabs (h + ph) * (1 - pow (- 52)) <= _); last first.
    have -> : h' = RND (h + ph) by case: E4 => ->.
    apply: relative_error_eps_le.
    apply: is_imul_add.
      suff/is_imul_pow_le : is_imul h (pow (- 61)) by apply.
      have ->: h = RND (th + z) by case: E2.
      apply: is_imul_pow_round.
      apply: is_imul_add => //.
      suff/is_imul_pow_le : is_imul th (pow (- 42)) by apply.
      apply: is_imul_pow_round.
      by have [] := th_prop l1l2_in eB.
    suff /is_imul_pow_le : is_imul ph (pow (- 123)) by apply.
    have := @imul_ph_p1 _ rnd _ _ Fz zB.
    by rewrite E3; apply.
  have pP : 0 < 1 - pow (-52) by interval.
  apply: Rle_trans (_ : (Rabs h - Rabs ph) * (1 - pow (-52)) <= _); last first.
    suff: Rabs h - Rabs ph <= Rabs (h + ph) by nra.
    clear; split_Rabs; lra.
  apply: Rle_trans (_ : (0.342118 - Rpower 2 (- 16.9)) * (1 - pow (-52)) <= _).
    have -> : 0.342118 = 342118 / 1000000 by lra.
    by interval.
  have phB : Rabs ph < Rpower 2 (-16.9).
    have := ph_bound_p1 _ Fz zB imul_z.
    by case: E3 => <- _; apply.
  by nra.
have l'h'B : Rabs l' / Rabs h' <= Rpower 2 (- 23.89).
  by set xx := Rabs l' in l'B *; set yy := Rabs h' in h'B *; interval.
split; first by apply/Rle_div_l; lra.
have lxE : ln x = ln t + IZR e * ln 2.
  have [_ ->] := getRangeCorrect Fx xB; rewrite E /fst /snd.
  rewrite ln_mult; last 2 first.
  - by interval.
  - by apply: bpow_gt_0.
  by rewrite pow_Rpower // ln_Rpower.
have lxB : 0.34657 < Rabs (ln x).
  apply: Rlt_le_trans (_ : Rabs (IZR e * ln 2) - Rabs (ln t) <= _); last first.
    rewrite lxE; clear; split_Rabs; lra.
  rewrite Rabs_mult.
  suff: 1 <= Rabs (IZR e) by set xx := Rabs _ => ?; interval.
  by rewrite -abs_IZR; apply: IZR_le; lia.
pose err0 :=  Rabs((ph + pl) - (ln (1 + z) - z)).
pose err1 := Rabs (tl - (IZR e * LOG2L + l2)).
pose err2 := Rabs ((h + t1) - (th + z)). 
pose err3 := Rabs (l - (t1 + tl)).
pose err4 := Rabs ((h' + t') - (h + ph)).
pose err5 := Rabs (RND lp - lp).
pose err6 := Rabs (l' - (t' + RND lp)).
pose err7 := Rabs (l1 + l2 - (- ln r)).
pose err8 := Rabs (IZR e * LOG2H + IZR e * LOG2L - IZR e * ln 2).
apply: Rle_trans (_ : err0 + err1 + err2 + err3 + err4 + err5 + 
                      err6 + err7 + err8 <= _).
  have -> : ln x = ln (1 + z) - ln r + IZR e * ln 2.
    rewrite /z round_generic; last by have [] := rt_float _ Ft tB.
    have -> : 1 + (r * t - 1) = r * t by lra.
    rewrite lxE ln_mult //; first by lra.
      by apply: r_gt_0.
    by interval.
  rewrite /err0 /err1 /err2 /err3 /err4 /err4 /err5 /err6 /err7 /err8.
  rewrite /th round_generic; last by have [] := th_prop l1l2_in eB.
  have F x1 x2 x3 x4 x5 x6 x7 x8 x9 : 
    Rabs (x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9) <= 
      Rabs x1 + Rabs x2 + Rabs x3 + Rabs x4 + Rabs x5 + Rabs x6 + 
      Rabs x7 + Rabs x8 + Rabs x9.
    by do 8 (apply: Rle_trans (Rabs_triang _ _) _; 
          apply: Rplus_le_compat; last by lra); lra.
  apply: Rle_trans (F _ _ _ _ _ _ _ _ _); right.
  by congr (Rabs _); rewrite /lp; lra.
apply: Rle_trans (_ : Rpower 2 (-73.527) * 0.34657 <= _); last first.
  suff : 0 <= Rpower 2 (-73.527) by nra.
  by interval.
have err0B : err0 < Rpower 2 (-75.492).
  have := @absolute_error_p1 _ rnd _ _ Fz zB.
  by rewrite E3; apply.
have -> : err0 + err1 + err2 + err3 + err4 + err5 + err6 + err7 + err8 =
          err0 + err1 + (err2 + err3) + (err4 + err6) + err5 + err7 + err8.
   by lra.
apply: Rle_trans (_ : 
     Rpower 2 (- 75.492) + pow (- 86) + Rpower 2 (- 85.995) +
     Rpower 2 (- 77.9999) + pow (- 78) + pow (- 97) + 
     Rpower 2 (-  91.949) <= _); last first.
  have -> : 0.34657 = 34657 / 100000 by lra.
  by interval.
apply: Rplus_le_compat; last first.
  by apply: err8_bound eB.
apply: Rplus_le_compat; last first.
  have /l1_LOGINV : (i - 181 < size LOGINV)%N.
    by rewrite ltn_subLR; case/andP: iB.
  by rewrite E1; case.
apply: Rplus_le_compat; last first.
  have := err5_bound Fx xB.
  by lazy zeta; rewrite E E1 E2 E3.
apply: Rplus_le_compat; last first.
  have := err4_err6_bound Fx xB.
  by lazy zeta; rewrite E E1 E2 E3 E4.
apply: Rplus_le_compat; last first.
  have := err23_bound Fx xB.
  by lazy zeta; rewrite E E1 E2; case => _ /(_ e_neq0).
apply: Rplus_le_compat.
  apply: Rlt_le.
  by have := @absolute_error_p1 _ rnd _ _ Fz zB;rewrite E3; apply.
by have [_ _ _ [_ ?]] := tl_prop l1l2_in eB.
Qed.

Lemma Rabs_round_le x e : 
  (fexp (e + 1) <= e)%Z -> Rabs x <= pow e -> Rabs (RND x) <= pow e.
Proof.
move=> fH.
have [x_pos|x_neg] : 0 <= x \/ x <= 0 by lra.
  rewrite !Rabs_pos_eq //; last first.
    have <- : RND 0 = 0 by rewrite round_0.
    by apply: round_le.
  move=> xLp.
  have <- : RND (pow e)  = pow e.
    rewrite round_generic //.
    by apply: generic_format_bpow.
  by apply: round_le.
rewrite !Rabs_left1 //; last first.
  have <- : RND 0 = 0 by rewrite round_0.
  by apply: round_le.
move=> xLp.
suff: - pow e <= RND x by lra. 
have <- : RND (- pow e)  = - pow e.
  rewrite round_generic //.
  apply: generic_format_opp.
  by apply: generic_format_bpow.
by apply: round_le; lra.
Qed.

Lemma err_lem4_e_eq0_iD255_iD256 x : 
  format x -> alpha <= x <= omega ->
  let: (t, e) := getRange x in
  e = 0%Z ->
  let i  := getIndex t in
  i <> 255%N -> i <> 256%N ->
  let: DWR h l := log1 x in
  let elog := Rpower 2 (- 67.0544) in
  Rabs l <= Rpower 2 (- 44.89998) * Rabs h /\ 
  Rabs (h + l - ln x) <= elog * Rabs (ln x).
Proof.
move=> Fx xB; rewrite /log1 /fastSum.
case E : getRange => [t e] e_eq0.
set i := getIndex _ => iD255 iD256.
have-> : (e =? 0)%Z = true by lia.
case E1 : nth => [l1 l2].
set r  := nth 1 INVERSE _.
set z  := RND (r * t  - 1).
set th := RND (IZR e * LOG2H + l1). 
set tl := RND (IZR e * LOG2L + l2).
case E2 : (fastTwoSum th z) => [h t1].
set l := RND (t1 + tl).
case E3 : p1 => [ph pl].
set lp := l + pl. 
case E4 : fastTwoSum => [h' t'].
set l' := RND (t' + RND lp).
case E5 : fastTwoSum => [h'' l''].
have hE : h = RND (th + z) by case: E2 => <- _.
have tB : / sqrt 2 < t < sqrt 2.
  by have [] := getRangeCorrect Fx xB; rewrite E.
have iB := getIndexBound tB; rewrite -/i in iB.
have l1l2_in : (l1, l2) \in LOGINV.
  rewrite -E1; apply: mem_nth.
  rewrite size_LOGINV.
  rewrite ltn_subLR; first by case/andP: iB.
  by case/andP: iB. 
have Fl1 : format l1 by have [] :=  format_LOGINV _ l1l2_in. 
have thE : th = l1 by rewrite /th e_eq0 !Rsimp01 round_generic.
have l1B : l1 <> 0 -> 0.00587 < Rabs l1 < 0.347.
  suff /l1_LOGINV[] : (i - 181 < size LOGINV)%N by rewrite E1.
  by rewrite ltn_subLR; case/andP: iB.
have {}/l1B l1B : l1 <> 0.
  have := iN255_N256_l1_neq_1 iB iD255 iD256.
  by lazy zeta; rewrite E1.
have thB : 0.00587 <= Rabs th by rewrite thE; lra.
have h''E : h'' = RND (h' + l') by case: E5 => <-.
have Ft : format t by have := getRangeFormat Fx xB; rewrite E.
have zB : Rabs z <= 33 * pow (- 13).
  have [] := rt_float _ Ft tB => //.
  rewrite -/r -/z => Frt1 rtB _.
  by rewrite /z round_generic.  
have thzB : 587 / 100000  - 33 * pow (- 13) <= Rabs (th + z).
  apply: Rle_trans (_ : Rabs th - Rabs z <= _); last by clear; split_Rabs; lra.
  by lra.
have imul_z : is_imul z (pow (- 61)).
  have [] := rt_float _ Ft tB  => // _ _ F1.
  by apply: is_imul_pow_round.
have eB := getRange_bound Fx xB; rewrite E /snd in eB.
have imul_th : is_imul th (pow (- 42)).
  apply: is_imul_pow_round.
  by have [] := th_prop l1l2_in eB.
have hB : Rpower 2 (- 9.09) <= Rabs h.
  apply: Rle_trans (_ : Rabs (th + z) * (1 - pow (- 52)) <= _); last first.
    rewrite hE.
    apply: relative_error_eps_le => //.
    apply: is_imul_add; first by apply: is_imul_pow_le imul_th _.
    by apply: is_imul_pow_le imul_z _.
  apply: Rle_trans (_ : (587 / 100000 - 33 * pow (-13))
                        * (1 - pow (- 52)) <= _); first by interval.
  suff : 0 <= 1 - pow (-52) by nra.
  by interval.
have h'E : h' = RND (h + ph) by case: E4 => <- _.
have Fz : format z by apply: generic_format_round.
have phB : Rabs ph <= Rpower 2  (- 16.9).
  apply: Rlt_le; case: E3 => <- _.
  by have := ph_bound_p1 _ Fz zB imul_z; apply.
have hphB : Rpower 2 (-9.09)  - Rpower 2 (-16.9) <= Rabs (h + ph).
  apply: Rle_trans (_ : Rabs h - Rabs ph <= _); last by clear; split_Rabs; lra.
  by lra.
have imul_thz : is_imul (th + z) (pow (- 61)).
  apply: is_imul_add => //.
  by apply: is_imul_pow_le imul_th _.
have imul_h : is_imul h (pow (- 61)).
  by rewrite hE; apply: is_imul_pow_round.
have imul_ph : is_imul ph (pow (- 123)).
  have := @imul_ph_p1 _ rnd _ _ Fz zB.
  by rewrite E3; apply.
have h'B : Rpower 2 (- 9.1) <= Rabs h'.
  apply: Rle_trans (_ : Rabs (h + ph) * (1 - pow (- 52)) <= _); last first.
    rewrite h'E.
    apply: relative_error_eps_le.
    apply: is_imul_add; first by apply: is_imul_pow_le imul_h _. 
    by apply: is_imul_pow_le imul_ph _. 
  apply: Rle_trans (_ : (Rpower 2 (-9.09) - Rpower 2 (-16.9)) *
                                     (1 - pow (-52)) <= _); first by interval.
  suff : 0 <= 1 - pow (-52) by nra.
  by interval.  
have h''B : Rpower 2 (- 9.10002) <= Rabs h''.
  rewrite h''E.
  apply: Rle_trans (_ : Rabs (h' + l') * (1 - pow (- 52)) <= _); last first.
    have[->|h'l'_neq0] := Req_dec (h' + l') 0.
      by rewrite !(Rsimp01, round_0); lra.
    apply: relative_error_eps_le.
    apply: is_imul_add.
      suff/is_imul_pow_le : is_imul h' (pow (- 123)) by apply.
      rewrite h'E.
      apply: is_imul_pow_round.
      apply: is_imul_add => //.
      suff/is_imul_pow_le : is_imul h (pow (- 61)) by apply.
      by have := h_l_bound Fx xB; lazy zeta; rewrite E E1 E2; case.
    suff /is_imul_pow_le : is_imul l' (pow (- 543)) by apply.
    have := h'_l'_bound Fx xB.
    by lazy zeta; rewrite E E1 E2 E3 E4 => [] [].
  have l'B : Rabs l' <= Rpower 2 (- 25.4407).
    have := h'_l'_bound Fx xB.
    by lazy zeta; rewrite E E1 E2 E3; case; case: E4 => _ -> apply.
  have pP : 0 < 1 - pow (-52) by interval.
  apply: Rle_trans (_ : (Rabs h' - Rabs l') * (1 - pow (-52)) <= _); last first.
    suff: Rabs h' - Rabs l'  <= Rabs (h' + l') by nra.
    clear; split_Rabs; lra.
  apply: Rle_trans (_ : (Rpower 2 (- 9.1) - Rpower 2 (- 25.4407)) 
                                   * (1 - pow (-52)) <= _).
    by interval.
  by nra.
have Fh' : format h' by case: E4 => <- _; apply: generic_format_round.
have Fl' : format l' by apply: generic_format_round.
have l'B : Rabs l' <= Rpower 2 (- 25.4407).
  have := h'_l'_bound Fx xB.
  by lazy zeta; rewrite E E1 E2 E3; case; case: E4 => _ -> apply.
have l''E : l'' = RND (l' + h' - h'').
  case: E5 => _ <-.
  rewrite -[round _ _ _ _]/(RND _).
  rewrite -[round _ _ _ (_ + l')]/(RND _).
  rewrite -[round _ _ _ (_ - h')]/(RND _).
  rewrite [RND (_ - h')]round_generic //.
    by rewrite -h''E; congr (RND _); lra.
  apply: sma_exact_abs_or0 => //.
  move=> h'_neq0.
  apply: Rle_trans l'B _.
  by apply: Rle_trans h'B;  interval.
have l''B : Rabs l'' <= pow (- 54).
  rewrite l''E h''E.
  apply: Rabs_round_le => //.
  have -> : Rabs (l' + h' - RND (h' + l')) = Rabs (RND (h' + l') - (h' + l')).
    by clear; split_Rabs; lra.
  apply: Rle_trans (_ : ulp (h' + l') <= _); first by apply: error_le_ulp.
  apply: Rle_trans (_ : ulp(0.353 + Rpower 2 (- 25.4407)) <= _).
    apply: ulp_le.
    apply: Rle_trans (Rabs_triang _ _) _.
    rewrite [Rabs (_ + _)]Rabs_pos_eq; last by interval.
    apply: Rplus_le_compat => //.
    have := err4_err6_h'_l'_bound Fx xB.
    by lazy zeta; rewrite E E1 E2 E3 E4; case => _ [_ _ /(_ e_eq0) h'B1 _].
  apply: bound_ulp => //.
  by interval.
split.
  apply: Rle_trans l''B _.
  have -> : pow (- 54) = Rpower 2 (-44.89998) * Rpower 2 (- 9.10002).
    by rewrite -Rpower_plus pow_Rpower //; congr (Rpower _ _); lra.
  suff : 0 <= Rpower 2 (-44.89998) by nra.
  by interval.
have lxE : ln x = ln t + IZR e * ln 2.
  have [_ ->] := getRangeCorrect Fx xB; rewrite E /fst /snd.
  rewrite ln_mult; last 2 first.
  - by interval.
  - by apply: bpow_gt_0.
  by rewrite pow_Rpower // ln_Rpower.
have lxB : Rpower 2 (- 8.0029) < Rabs (ln x).
  have pN8 : 0 < pow (-8) by apply: bpow_gt_0.
  have p8 : 0 < pow 8 by apply: bpow_gt_0.
  have [H|[H|[H|H]]]: x < 1 - pow (- 8) \/ 1 - pow (- 8) <= x < 1 \/
         1 <= x < 1 + pow (- 8) \/ 1 + pow (- 8) <= x by lra.
  - by interval with (i_prec 100).
  - case: iD255.
    rewrite /i.
    have -> : t = x.
      by have [_ ->] := getRangeCorrect Fx xB; rewrite E e_eq0 /=; lra.
    rewrite /getIndex.
    suff : Zfloor (pow 8 * x) = 255%Z by lia.
    apply: Zfloor_imp.
    have -> : IZR 256 = pow 8 * 1 by rewrite /= /Z.pow_pos /=; lra.
    have -> : IZR 255 = pow 8 * (1 - pow (- 8)) by rewrite /= /Z.pow_pos /=; lra.
    have: 0 < pow 8 by apply: bpow_gt_0.
    by nra.
  - case: iD256.
    rewrite /i.
    have -> : t = x.
      by have [_ ->] := getRangeCorrect Fx xB; rewrite E e_eq0 /=; lra.
    rewrite /getIndex.
    suff : Zfloor (pow 8 * x) = 256%Z by lia.
    apply: Zfloor_imp.
    have -> : IZR 256 = pow 8 * 1 by rewrite /= /Z.pow_pos /=; lra.
    have -> : IZR 257 = pow 8 * (1 + pow (- 8)) by rewrite /= /Z.pow_pos /=; lra.
    have: 0 < pow 8 by apply: bpow_gt_0.
    by nra.
  by interval with (i_prec 100).
pose err0 :=  Rabs((ph + pl) - (ln (1 + z) - z)).
pose err1 := Rabs (tl - (IZR e * LOG2L + l2)).
pose err2 := Rabs ((h + t1) - (th + z)). 
pose err3 := Rabs (l - (t1 + tl)).
pose err4 := Rabs ((h' + t') - (h + ph)).
pose err5 := Rabs (RND lp - lp).
pose err6 := Rabs (l' - (t' + RND lp)).
pose err7 := Rabs (l1 + l2 - (- ln r)).
pose err8 := Rabs (IZR e * LOG2H + IZR e * LOG2L - IZR e * ln 2).
pose err9 := Rabs ((h'' + l'') - (h' + l')). 
 apply: Rle_trans (_ : err0 + err1 + err2 + err3 + err4 + err5 + 
                      err6 + err7 + err8 + err9 <= _).
  have -> : ln x = ln (1 + z) - ln r + IZR e * ln 2.
    rewrite /z round_generic; last by have [] := rt_float _ Ft tB.
    have -> : 1 + (r * t - 1) = r * t by lra.
    rewrite lxE ln_mult //; first by lra.
      by apply: r_gt_0.
    by interval.
  rewrite /err0 /err1 /err2 /err3 /err4 /err4 /err5 /err6 /err7 /err8 /err9.
  rewrite /th round_generic; last by have [] := th_prop l1l2_in eB.
  have F x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : 
    Rabs (x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) <= 
      Rabs x1 + Rabs x2 + Rabs x3 + Rabs x4 + Rabs x5 + Rabs x6 + 
      Rabs x7 + Rabs x8 + Rabs x9 + Rabs x10.
    by do 9 (apply: Rle_trans (Rabs_triang _ _) _; 
          apply: Rplus_le_compat; last by lra); lra.
  apply: Rle_trans (F _ _ _ _ _ _ _ _ _ _); right.
  by congr (Rabs _); rewrite /lp; lra.
apply: Rle_trans (_ : Rpower 2 (- 67.0544) * 
                      Rpower 2 (- 8.0029)  <= _); last first.
  suff : 0 <= Rpower 2 (- 67.0544) by nra.
  by interval.
have -> : err0 + err1 + err2 + err3 + err4 + err5 + err6 + err7 + err8 + err9 =
          err0 + err1 + (err2 + err3) + (err4 + err6) + err5 + err7 + err8 +
          err9.
   by lra.
apply: Rle_trans (_ : 
     Rpower 2 (- 75.492) + 0 + Rpower 2 (- 94.999) +
     Rpower 2 (- 77.9999) + pow (- 78) + pow (- 97) + 0 + 
     Rpower 2 (-  106.502) <= _); last first.
  by interval.
apply: Rplus_le_compat; last first.
  have := err9_bound Fx xB.
  lazy zeta; rewrite E E1 E2 E3 E4 E5 -/i; by apply.
apply: Rplus_le_compat; last first.
  suff : err8 = 0 by lra.
  by rewrite /err8 e_eq0; apply: err8_0 .
apply: Rplus_le_compat; last first.
  have /l1_LOGINV : (i - 181 < size LOGINV)%N.
    by rewrite ltn_subLR; case/andP: iB.
  by rewrite E1; case.
apply: Rplus_le_compat; last first.
  have := err5_bound Fx xB.
  by lazy zeta; rewrite E E1 E2 E3.
apply: Rplus_le_compat; last first.
  have := err4_err6_bound Fx xB.
  by lazy zeta; rewrite E E1 E2 E3 E4.
apply: Rplus_le_compat; last first.
  have := err23_bound Fx xB.
  by lazy zeta; rewrite E E1 E2; case => /(_ e_eq0).
apply: Rplus_le_compat.
  apply: Rlt_le.
  by have := @absolute_error_p1 _ rnd _ _ Fz zB;rewrite E3; apply.
have [_ _ _ [/(_ e_eq0) V _]] := tl_prop l1l2_in eB.
rewrite [err1]V; lra.
Qed.


Lemma err_lem4_e_eq0_iE255_iE256 x : 
  format x -> alpha <= x <= omega ->
  let: (t, e) := getRange x in
  e = 0%Z ->
  let i  := getIndex t in
  (i = 255%N \/ i = 256%N) ->
  let: DWR h l := log1 x in
  let elog := Rpower 2 (- 67.145) in
  Rabs l <= Rpower 2 (- 51.99) * Rabs h /\ 
  Rabs (h + l - ln x) <= elog * Rabs (ln x).
Proof.
move=> Fx xB; rewrite /log1 /fastSum.
case E : getRange => [t e] e_eq0.
set i := getIndex _ => iE255O256.
have-> : (e =? 0)%Z = true by lia.
case E1 : nth => [l1 l2].
set r  := nth 1 INVERSE _.
set z  := RND (r * t  - 1).
set th := RND (IZR e * LOG2H + l1). 
set tl := RND (IZR e * LOG2L + l2).
case E2 : (fastTwoSum th z) => [h t1].
set l := RND (t1 + tl).
case E3 : p1 => [ph pl].
set lp := l + pl. 
case E4 : fastTwoSum => [h' t'].
set l' := RND (t' + RND lp).
case E5 : fastTwoSum => [h'' l''].
have hE : h = RND (th + z) by case: E2 => <- _.
have tB : / sqrt 2 < t < sqrt 2.
  by have [] := getRangeCorrect Fx xB; rewrite E.
have iB := getIndexBound tB; rewrite -/i in iB.
have l1l2_in : (l1, l2) \in LOGINV.
  rewrite -E1; apply: mem_nth.
  rewrite size_LOGINV.
  rewrite ltn_subLR; first by case/andP: iB.
  by case/andP: iB.
have tEx : t = x.
  by have [_ ->] := getRangeCorrect Fx xB; rewrite E e_eq0 /=; lra.
have xB1 : 1 - pow (- 8) <= x < 1 + pow (- 8).
  rewrite -tEx.
  have [i255|i256] := iE255O256.
    suff: 1 - pow (- 8) <= t < 1 by lra.
    suff : 255 <= pow 8 * t < 255 + 1 by rewrite /= /Z.pow_pos /=; lra.
    suff Zx : Zfloor (pow 8 * t) = 255%Z.
      split; first by rewrite -Zx; apply: Zfloor_lb.
      by rewrite -Zx; apply: Zfloor_ub.
    apply: Z2Nat.inj => //.
    rewrite -[0%Z](Zfloor_IZR 0); apply: Zfloor_le.
    by interval with (i_prec 100).
  suff : 1 <= t < 1 + pow (- 8) by lra.
  suff : 256 <= pow 8 * t < 256 + 1 by rewrite /= /Z.pow_pos /=; lra.
  suff Zx : Zfloor (pow 8 * t) = 256%Z.
    split; first by rewrite -Zx; apply: Zfloor_lb.
    by rewrite -Zx; apply: Zfloor_ub.
  apply: Z2Nat.inj => //.
  rewrite -[0%Z](Zfloor_IZR 0); apply: Zfloor_le.
  by interval with (i_prec 100).
have rE1 : r = 1 by rewrite /r; case: iE255O256 => -> /=; lra.
have l1E0 : l1 = 0 by move: E1; case: iE255O256 => -> /= [].
have l2E0 : l2 = 0 by move: E1; case: iE255O256 => -> /= [].
have rB : - pow (- 8) <= z < pow (- 8).
  rewrite /z round_generic //; first by rewrite rE1 Rsimp01 tEx; lra.
  have Ft : format t by have := getRangeFormat Fx xB; rewrite E.
  by have [] := rt_float _ Ft tB.
have thE0 : th = 0 by rewrite /th e_eq0 l1E0 !Rsimp01 round_0.
have tlE0 : tl = 0 by rewrite /tl e_eq0 l2E0 !Rsimp01 round_0.
have Fz : format z by apply: generic_format_round.
have Ft : format t by have := getRangeFormat Fx xB; rewrite E.
have Frt : format (r * t - 1) by have [] := rt_float _ Ft tB.
have imul_z : is_imul z (pow (- 61)).
  by rewrite [z]round_generic //; have [] := rt_float _ Ft tB.
have hEz : h = z.
  have -> : h = RND (th + z) by case: E2 => <- _.
  by rewrite thE0 Rsimp01 round_generic.
have t1E0 : t1 = 0.
  by rewrite thE0 fastTwoSum_0l // in E2; case: E2.
have lE0 : l = 0 by rewrite /l tlE0 t1E0 !Rsimp01 round_0.
have [x_eq1|x_neq1] := Req_dec x 1.
  have zE0 : z = 0 by rewrite /z rE1 tEx x_eq1 !Rsimp01 round_0.
  have phE0 : ph = 0 by rewrite zE0 p1_0 in E3; case: E3.
  have plE0 : pl = 0 by rewrite zE0 p1_0 in E3; case: E3.
  have h'Eh : h' = h.
    rewrite phE0 fastTwoSum_0r // in E4; first by case: E4.
    by rewrite hEz.
  have t'E0 : t' = 0.
    rewrite phE0 fastTwoSum_0r // in E4; first by case: E4.
    by rewrite hEz.
  have h''Eh : h'' = h.
    rewrite h'Eh /l' t'E0 /lp lE0 plE0 !(Rsimp01, round_0) in E5.
    rewrite fastTwoSum_0r // in E5; first by case: E5.
    by rewrite hEz.
  have l''E0 : l'' = 0.
    rewrite h'Eh /l' t'E0 /lp lE0 plE0 !(Rsimp01, round_0) in E5.
    rewrite fastTwoSum_0r // in E5; first by case: E5.
    by rewrite hEz.
  by rewrite l''E0 h''Eh x_eq1 hEz zE0 ln_1 !Rsimp01; lra.
have z_gt0 : 0 < Rabs z.
  suff : z <> 0 by split_Rabs; lra.
  contradict x_neq1.
  rewrite /z round_generic // in x_neq1.
  by rewrite rE1 tEx in x_neq1; lra.
pose delta := (z + ph + pl) / ln x - 1.
have deltaE : z + ph + pl = ln x * (1 + delta).
  rewrite /delta; field.
  apply: ln_neq_0; [lra | interval].    
have zE : x = 1 + z.
  rewrite /z round_generic //.
  by rewrite ?rE1 ?tEx; lra.
have z_neq0 : z <> 0 by lra.
have zB0 : Rabs z <= pow (- 8) by split_Rabs; lra.
have zB' : Rabs z <= 32 * bpow radix2 (-13).
  suff -> : 32 * pow (- 13) = pow (- 8) by [].
  by rewrite -[32]/(pow 5) -bpow_plus.
have deltaB : Rabs delta < Rpower 2 (- 67.441).
  by rewrite /delta zE; have := @rel_error_32_p1 _ rnd _ z; rewrite E3; apply.
have zB1 : pow (- 61) <= Rabs z.
  by apply: is_imul_pow_le_abs => //; lra.
have z1B : pow (- 62) <= Rabs (ln (1 + z)).
  have F1 : z <= - pow (- 61) -> pow (- 62) <= Rabs (ln (1 + z)).
    by move=> ?; interval with (i_prec 100).
  have F2 : pow (- 61) <= z -> pow (- 62) <= Rabs (ln (1 + z)).
    by move=> ?; interval with (i_prec 100).
  by split_Rabs; lra.
have zphpl_neq_0 : z + ph + pl <> 0.
  suff: 0 < Rabs (z + ph + pl) by clear; split_Rabs; lra.
  have phplB : Rabs (ph + pl - (ln (1 + z) - z)) < Rpower 2 (-75.492).
    have := @absolute_error_p1 _ rnd _ z; rewrite E3; apply => //.
    by apply: Rle_trans zB' _; interval.
  apply: Rlt_le_trans (_ : Rabs (ln (1 + z)) - 
                            Rabs (ph + pl - (ln (1 + z) - z)) <= _); last first.
    clear; split_Rabs; lra.
  apply: Rlt_le_trans (_ : pow (-62) - Rpower 2 (-75.492) <= _); last by lra.
  by interval.
pose delta' := (h' + l') / (z + ph + pl) -1.
have delta'E : h' + l' = (z + ph + pl) * (1 + delta').
  by rewrite /delta'; field.
pose err0 :=  Rabs((ph + pl) - (ln (1 + z) - z)).
pose err1 := Rabs (tl - (IZR e * LOG2L + l2)).
pose err2 := Rabs ((h + t1) - (th + z)). 
pose err3 := Rabs (l - (t1 + tl)).
pose err4 := Rabs ((h' + t') - (h + ph)).
pose err5 := Rabs (RND lp - lp).
pose err6 := Rabs (l' - (t' + RND lp)).
pose err7 := Rabs (l1 + l2 - (- ln r)).
pose err8 := Rabs (IZR e * LOG2H + IZR e * LOG2L - IZR e * ln 2).
pose err9 := Rabs ((h'' + l'') - (h' + l')). 
have err23B : err2 + err3 <= Rpower 2 (- 94.999).
  have := err23_bound Fx xB.
  by lazy zeta; rewrite E E1 E2; case => /(_ e_eq0).
have zphplE : fastSum z ph pl = DWR h' l'.
  rewrite /fastSum -hEz E4 /l' /lp lE0 Rsimp01 [RND pl]round_generic //.
  by case: E3 => _ <-; apply: generic_format_round.
have phLz : Rabs ph <= Rabs z.
(* copy *)
  have zB2 : Rabs z <= 1 by set xx := Rabs z in zB' *; interval.
  have z2B : z * z <= Rabs z.
    have -> : z * z = Rabs z * Rabs z by split_Rabs; lra.
    suff : 0 <= Rabs z by clear -zB2; nra.
    by apply: Rabs_pos.
  apply: Rle_trans (_ : RND (z * z) <= _) => //.
    have phE : ph = - 0.5 * RND (z * z).
      case: E3 => <- _.
      rewrite -[round _ _ _]/RND round_generic //.
      have -> : -0.5 * RND (z * z) = - (0.5 * RND (z * z)) by lra.
      have imul_zz : is_imul ((z * z)) (pow (- 122)).
        have -> : (- 122 = (- 61) + (- 61))%Z by [].
        by rewrite bpow_plus; apply: is_imul_mul.
      have imul_rzz : is_imul (RND (z * z)) (pow (- 122)).
        by apply: is_imul_pow_round.
      apply: generic_format_opp.
      apply: is_imul_format_half imul_rzz _ => //.
      by apply: generic_format_round.
    have tphE : 2 * Rabs ph = RND (z * z).
      suff : 0 <= RND (z * z) by rewrite phE; split_Rabs; lra.
      have -> : 0 = RND 0 by rewrite round_0.
      by apply: round_le; nra.
    rewrite -tphE.
    by split_Rabs; lra.
  have-> : Rabs z = RND (Rabs z).
    rewrite round_generic //. 
    by apply: generic_format_abs.
  by apply: round_le.
have zB : Rabs z <= 33 * pow (- 13).
  have [] := rt_float _ Ft tB => //.
  rewrite -/r -/z => Frt1 rtB _.
  by rewrite /z round_generic.  
have imul_ph : is_imul ph (pow (- 123)).
  have := @imul_ph_p1 _ rnd _ _ Fz zB.
  by rewrite E3; apply.
have imul_zph : is_imul (z + ph) (pow (- 123)).
  apply: is_imul_add => //.
  by apply: is_imul_pow_le imul_z _.
have h'E : h' = RND (z + ph) by case: zphplE => ->.
have Fph : format ph by case: E3 => <- _; apply: generic_format_round.
have h'z_exact : RND (h' - z) = h' - z.
  apply: round_generic; rewrite h'E.
  by apply: sma_exact_abs_or0.
have lpE : lp = pl by rewrite /lp lE0 Rsimp01.
have l'E : l' = RND (RND (z + ph - h') + pl).
  rewrite /l'; congr (RND _).
  case: E4 => _ <-.
  rewrite -[round _ _ _ _]/(RND _).
  rewrite -[round _ _ _ (_ + ph)]/(RND _).
  rewrite -[round _ _ _ (_ - h)]/(RND _).
  rewrite hEz -h'E h'z_exact lpE [RND pl]round_generic //.
    by congr (RND _ + _); lra.
  by case: E3 => _ <-; apply: generic_format_round.
pose delta1' := if (Req_bool (z + ph) 0) then 0 else  h' / (z + ph) - 1.
have delta1'E : h' = (z + ph) * (1 + delta1').
  rewrite /delta1' h'E.
  have [->|zph_neq0] := Req_dec (z + ph) 0.
    rewrite round_0 Rsimp01; lra.
  by rewrite Req_bool_false //; field.
have delta1'B : Rabs delta1' < pow (- 52).
  rewrite /delta1' h'E.
  have [zph_eq0|zph_neq0] := Req_dec (z + ph) 0.
    by rewrite Req_bool_true // Rsimp01; interval.
  rewrite Req_bool_false //.
  set xx := z + ph in zph_neq0 imul_zph *. 
  have -> : Rabs (RND xx / xx - 1) = Rabs  (RND xx - xx) / Rabs xx.
    by rewrite -Rabs_div //; congr (Rabs _); field.
  apply/Rlt_div_l; first by clear -zph_neq0; split_Rabs; lra.
  apply: relative_error_FLT => //.
  apply: is_imul_pow_le_abs => //.
  by apply: is_imul_pow_le imul_zph _.
pose delta2' := if (Req_bool (z + ph - h') 0) then 0 
                else RND (z + ph - h') / (z + ph - h') - 1.
have delta2'E : RND (z + ph - h') = (z + ph - h') * (1 + delta2').
  rewrite /delta2'.
  have [->|zphh'_neq0] := Req_dec (z + ph - h') 0.
    by rewrite round_0 Rsimp01; lra.
  by rewrite Req_bool_false //; field.
have imul_zphh' : is_imul (z + ph - h') (pow (- 123)).
  apply: is_imul_minus => //.
  rewrite h'E.
  by apply: is_imul_pow_round.
have delta2'B : Rabs delta2' < pow (- 52).
  rewrite /delta2'.
  have [zphh'_eq0|zphh'_neq0] := Req_dec (z + ph - h') 0.
    by rewrite Req_bool_true // Rsimp01; interval.
  rewrite Req_bool_false //.
  set xx := z + ph - h' in zphh'_neq0 imul_zph *. 
  have -> : Rabs (RND xx / xx - 1) = Rabs  (RND xx - xx) / Rabs xx.
    by rewrite -Rabs_div //; congr (Rabs _); field.
  apply/Rlt_div_l; first by clear -zphh'_neq0; split_Rabs; lra.
  apply: relative_error_FLT => //.
  apply: is_imul_pow_le_abs => //.
  by apply: is_imul_pow_le imul_zphh' _.
pose delta3' := if (Req_bool (RND (z + ph - h') + pl) 0) then 0 
                else RND (RND (z + ph - h') + pl) / 
                     (RND (z + ph - h') + pl) - 1.
have delta3'E : RND (RND (z + ph - h') + pl) = 
                 (RND (z + ph - h') + pl) * (1 + delta3').
  rewrite /delta3'.
  have [->|zphh'pl_neq0] := Req_dec (RND (z + ph - h') + pl) 0.
    by rewrite round_0 Rsimp01; lra.
  by rewrite Req_bool_false //; field.
have imul_pl : is_imul pl (pow (- 543)).
  have := @imul_pl_p1 _ rnd _ z Fz zB.
  by rewrite E3; apply.
have imul_zphh'pl : is_imul (RND (z + ph - h') + pl) (pow (- 543)).
  apply: is_imul_add => //.
  apply: is_imul_pow_round => //.
  by apply: is_imul_pow_le imul_zphh' _.
have delta3'B : Rabs delta3' < pow (- 52).
  rewrite /delta3'.
  have [zphh'pl_eq0|zphh'pl_neq0] := Req_dec (RND (z + ph - h') + pl) 0.
    by rewrite Req_bool_true // Rsimp01; interval.
  rewrite Req_bool_false //.
  set xx := RND (z + ph - h') + pl in zphh'pl_neq0 imul_zph *. 
  have -> : Rabs (RND xx / xx - 1) = Rabs  (RND xx - xx) / Rabs xx.
    by rewrite -Rabs_div //; congr (Rabs _); field.
  apply/Rlt_div_l; first by clear -zphh'pl_neq0; split_Rabs; lra.
  apply: relative_error_FLT => //.
  apply: is_imul_pow_le_abs => //.
  by apply: is_imul_pow_le imul_zphh'pl _.
have  l'E1 : l'  = ((z + ph - h') * (1 + delta2') + pl) * (1 + delta3').
  by ring [l'E delta1'E delta2'E delta3'E].
have  h'l'E : h' + l' - (z + ph + pl) =
            - delta1' * (delta2' + delta3' + delta2' * delta3') * (z + ph) +
              delta3' * pl.
  by ring [l'E1 delta1'E delta2'E delta3'E].
have h'l'B :  Rabs ((h' + l') - (z + ph + pl)) <= (pow (-103) +  pow (-156)) *
                                             Rabs (z + ph) + pow (- 52) * Rabs pl.
  rewrite h'l'E.
  apply: Rle_trans (Rabs_triang _ _) _.
  apply: Rplus_le_compat; last first.
    rewrite Rabs_mult.
    suff : 0 <= Rabs pl by clear -delta3'B; nra.
    by apply: Rabs_pos.
  rewrite !Rabs_mult Rabs_Ropp.
  suff: Rabs delta1' * Rabs (delta2' + delta3' + delta2' * delta3') <=
           (pow (-103) + pow (-156)).
    have : 0 <= Rabs (z + ph) by apply: Rabs_pos.
    by clear; nra.
  have -> : pow (-103) + pow (-156) =
          pow (- 52) * (pow (- 52) + pow (- 52) + pow (- 52) * pow (-52)).
    by rewrite /= /Z.pow_pos /=; lra.
  apply: Rmult_le_compat => //; try apply: Rabs_pos; try lra.
  apply: Rle_trans (Rabs_triang _ _) _.
  apply: Rplus_le_compat.
    by apply: Rle_trans (Rabs_triang _ _) _; lra.
  rewrite Rabs_mult.
  by apply: Rmult_le_compat => //; try apply: Rabs_pos; lra.
pose delta0 := RND (z * z) / (z * z) - 1.
have delta0E : RND (z * z) = (z * z) * (1 + delta0).
  by rewrite /delta0; field.
have imul_zz : is_imul (z * z) (pow (- 122)).
  have -> : (-122 = - 61 + - 61)%Z by [].
  by rewrite bpow_plus; apply: is_imul_mul.
have delta0B : Rabs delta0 < pow (- 52).
  rewrite /delta0.
  have -> : Rabs (RND (z * z) / (z * z) - 1) = 
            Rabs  (RND (z * z) - z * z) / Rabs (z * z).
    rewrite -Rabs_div //; last by clear -z_neq0; nra.
    by congr (Rabs _); field.
  apply/Rlt_div_l; first by clear -z_neq0; split_Rabs; nra.
  apply: relative_error_FLT => //.
  apply: is_imul_pow_le_abs; last by clear -z_neq0; nra.
  by apply: is_imul_pow_le imul_zz _.
have phE : ph = - 0.5 * RND (z * z).
  case: E3 => <- _.
  rewrite -[round _ _ _]/RND round_generic //.
  have -> : -0.5 * RND (z * z) = - (0.5 * RND (z * z)) by lra.
  have imul_rzz : is_imul (RND (z * z)) (pow (- 122)).
    by apply: is_imul_pow_round.
  apply: generic_format_opp.
  apply: is_imul_format_half imul_rzz _ => //.
  by apply: generic_format_round.
have zphE : Rabs (z + ph) = Rabs (z - 0.5 * (z * z) * (1 + delta0)).
  by rewrite phE delta0E; congr (Rabs _); lra.
pose A := 1 - pow (- 9) * (1 + pow (- 52)).
pose B := 1 + pow (- 9) * (1 + pow (- 52)).
have zphhB : A <= Rabs (z + ph) / Rabs z <= B.
  rewrite zphE -Rabs_div //.
  have -> : (z - 0.5 * (z * z) * (1 + delta0)) / z = 1 - 0.5 * z * (1 + delta0).
    by field.
  split.
    apply: Rle_trans (_: 1 - Rabs (0.5 * z * (1 + delta0)) <= _); last first.
      by clear; split_Rabs; lra.
    rewrite 2!Rabs_mult /A [Rabs 0.5]Rabs_pos_eq; last by lra.
    have -> : pow (- 9) = 0.5 * pow (- 8) by rewrite -powN1 -bpow_plus.
    suff : Rabs z * Rabs (1 + delta0) <=  pow (-8) * (1 + pow (-52)).
      by lra.
    apply: Rmult_le_compat; try apply: Rabs_pos; try lra.
    apply: Rle_trans (Rabs_triang _ _) _.
    by rewrite Rabs_pos_eq; lra.
  apply: Rle_trans (_: 1 + Rabs (0.5 * z * (1 + delta0)) <= _).
    by clear; split_Rabs; lra.
  rewrite 2!Rabs_mult /B [Rabs 0.5]Rabs_pos_eq; last by lra.
  have -> : pow (- 9) = 0.5 * pow (- 8) by rewrite -powN1 -bpow_plus.
  suff : Rabs z * Rabs (1 + delta0) <=  pow (-8) * (1 + pow (-52)).
    by lra.
  apply: Rmult_le_compat; try apply: Rabs_pos; try lra.
  apply: Rle_trans (Rabs_triang _ _) _.
  by rewrite Rabs_pos_eq; lra.
have CC : 
  let wh := RND (z * z) in
  let wl := RND (z * z - wh) in
  let t := RND (P8 * z + P7) in
  let u := RND (P6 * z + P5) in
  let v := RND (P4 * z + P3) in
  let u' := RND (t * wh + u) in
  let v' := RND (u' * wh + v) in 
  let u'' := RND (v' * wh) in
  let e5 := v' - (u' * wh + v) in
    [/\ 
      [/\ wl = z * z - wh,  pl = RND (u'' * z - 0.5 * wl) &
      u'' = RND(v' * RND (z * z))],
      Rabs e5 <= pow (- 54),
      v' <= Rpower 2 (- 1.58058) + pow (- 54), 
      0 < v' < Rpower 2 (- 1.5805) & 
     is_imul v' (pow (- 360))].
  have := @e5_error_bound (refl_equal _ : 1 < 53)%Z _ valid_rnd _ Fz zB.
  by rewrite E3 /=; apply.
lazy zeta in CC.
set wh := RND (z * z) in CC.
set wl := RND (z * z - wh) in CC.
set xt := RND (P8 * z + P7) in CC.
set xu := RND (P6 * z + P5) in CC.
set v := RND (P4 * z + P3) in CC.
set u' := RND (xt * wh + xu) in CC.
set v' := RND (u' * wh + v) in CC.
set u'' := RND (v' * wh) in CC.
have imul_v' : is_imul v' (pow (- 360)) by case: CC.
have plE : pl = RND (u'' * z - 0.5 * wl) by case: CC; case.
have u''E : u'' = RND (v' * RND (z * z)) by [].
have v'B : 0 < v' <= Rpower 2 (- 1.5805).
  by case: CC; case; lra.
have p52 : 0 < pow (- 52) by apply: bpow_gt_0.
have wlE : wl = - delta0 * (z * z).
  have -> : wl = (z * z) - RND (z * z).
    by rewrite -/wh; case: CC; case; lra.
  by rewrite delta0E; lra.
have u''_pos : 0 <= u''.
  rewrite /u''.
  have <-: RND 0 = 0 by apply: round_0.
  apply: round_le.
  have : 0 <= v' by lra.
  suff: 0 <= wh by clear; nra.
  have <-: RND 0 = 0 by apply: round_0.
  apply: round_le.
  clear; nra.  
have u''B : u'' <= (Rpower 2 (- 1.580499)) * (z * z).
  apply: Rle_trans (_ : (Rpower 2 (-1.5805) *
                          (1 + pow (- 52)) * 
                          (1 + pow (- 52))) * (z * z) <= _); last first.
    have : 0 <= z * z by clear; nra.
    suff : Rpower 2 (-1.5805) * (1 + pow (-52)) * (1 + pow (-52)) <=
           Rpower 2 (-1.580499) by clear; nra.
    by interval.
  rewrite /u'' /wh.
  have [->|rzz_neq0] := Req_dec (RND (z * z)) 0.
    rewrite !(Rsimp01, round_0).
    have -> : 0 = 0 * 0 by lra.
    apply: Rmult_le_compat; try lra; try by apply: Rabs_pos.
      by interval.
    clear; nra.
  apply: Rle_trans (_ : (Rabs (v' * RND (z * z))) * (1 + pow (- 52)) <= _).
    rewrite -/u'' -(Rabs_pos_eq _ u''_pos) u''E.
    apply: relative_error_eps_ge.
    apply: is_imul_pow_le (_ : is_imul _ (pow (- 360 + - 122))) _ => //.
    rewrite bpow_plus; apply: is_imul_mul => //.
    apply: is_imul_pow_round.
    have -> : (- 122 = - 61 + - 61)%Z by [].
    by rewrite bpow_plus; apply: is_imul_mul => //.
  rewrite Rabs_mult.
  suff : Rabs v' * Rabs (RND (z * z)) <=
         Rpower 2 (-1.5805) *  ((z * z) * (1 + pow (-52))).
    by clear -p52; nra. 
  apply: Rmult_le_compat=> //; try by apply: Rabs_pos.
    by rewrite Rabs_pos_eq; lra.
  rewrite -{2}[z * z]Rabs_pos_eq; last by clear; nra.
  apply: relative_error_eps_ge.
  by apply: is_imul_pow_le (_ : is_imul _ (pow (- 61 + - 61))) _ => //.
have wlB :  Rabs wl <= pow (- 52) * (z * z).
  have zz_pos : 0 <= z * z by clear; nra.
  rewrite wlE Rabs_mult Rabs_Ropp [Rabs (z * z)]Rabs_pos_eq //.
  by clear -zz_pos delta0B; nra.
have imul_wh : is_imul wh (pow (- 122)).
  apply: is_imul_pow_round.
  have -> : pow (-122) = pow (-61) * pow (-61) by rewrite -bpow_plus.
  by apply: is_imul_mul.
have imul_half_wh : is_imul (0.5 * wh) (pow (-123)).
  have-> : pow (-123) = pow (-1) * pow (-122) by rewrite -bpow_plus.
  by rewrite powN1; apply: is_imul_mul => //; exists 1%Z; lra.
have imul_half_u'' : is_imul u'' (pow (-482)).
  apply: is_imul_pow_round.
  have -> : (-482 = - 360 + - 122)%Z by [].
  by rewrite bpow_plus; apply: is_imul_mul.
have imul_wl : is_imul wl (pow (- 122)).
  by apply: is_imul_pow_round; apply: is_imul_minus.
have imul_half_wl : is_imul (0.5 * wl) (pow (-123)).
  have-> : pow (-123) = pow (-1) * pow (-122) by rewrite -bpow_plus.
  by rewrite powN1; apply: is_imul_mul => //; exists 1%Z; lra.
have plB : Rabs pl <= (Rpower 2 (- 1.580499) * (Rabs z) ^ 3 + 
                        pow (- 53) * z^ 2) * (1 + pow (-52)).
  rewrite plE.
  apply: Rle_trans (_ : Rabs (u'' * z - 0.5 * wl) * (1 + pow (-52)) <= _).
    apply: relative_error_eps_ge.
    apply: is_imul_minus => //.
      apply: is_imul_pow_le (_ : is_imul _ (pow (- 482 + -61))) _ => //.
      by rewrite bpow_plus; apply: is_imul_mul.
    by apply: is_imul_pow_le imul_half_wl _.
  suff : Rabs (u'' * z - 0.5 * wl) <=
           (Rpower 2 (-1.580499) * Rabs z ^ 3 + pow (-53) * z ^ 2).
    by clear -p52; nra.
  apply: Rle_trans (_ : Rabs (u'' * z) + Rabs (0.5 * wl) <= _).
    by clear; split_Rabs; lra.
  apply: Rplus_le_compat.
    rewrite Rabs_mult.
    suff :  Rabs u'' <= Rpower 2 (-1.580499) * Rabs z ^ 2.
      suff: 0 <= Rabs z by clear; nra.
      by apply: Rabs_pos.
    rewrite Rabs_pos_eq //.
    suff -> : Rabs z ^ 2 = z ^ 2 by lra.
    by clear; split_Rabs; lra.
  rewrite Rabs_mult Rabs_pos_eq; last by lra.
  rewrite -powN1 -[bpow _ _]/(pow _).
  have -> : (- 53 = - 1 + - 52)%Z by [].
  rewrite bpow_plus.
  suff: 0 <= pow (-1) by clear - wlB; nra.
  by interval.
pose C := Rpower 2 (- 17.58049).
have plzB : Rabs pl / Rabs z <= C.
  apply: Rle_trans (_ :  (Rpower 2 (- 1.580499) * pow (-16) +
                                    pow (-53) * pow (- 8)) * 
                                    (1 + pow (- 52)) <= _); last first.
    by interval.
  apply: Rle_trans (_ : (Rpower 2 (-1.580499) * Rabs z ^ 3 + pow (-53) * z ^ 2) 
                              * (1 + pow (-52)) / Rabs z <= _).
    suff : 0 < / Rabs z by clear -plB; rewrite /Rdiv; nra.
    by apply: Rinv_0_lt_compat; clear -z_neq0; split_Rabs; lra.
  have -> : z ^ 2 = Rabs z ^ 2 by clear; split_Rabs; lra.
  have -> : (Rpower 2 (-1.580499) * Rabs z ^ 3 + pow (-53) * Rabs z ^ 2) *
              (1 + pow (-52)) / Rabs z = 
           (Rpower 2 (-1.580499) * Rabs z ^ 2 + pow (-53) * Rabs z) *
              (1 + pow (-52)) by field; clear -z_neq0; split_Rabs; lra.
  apply: Rmult_le_compat; try lra.
    apply: Rplus_le_le_0_compat.
      apply: Rmult_le_pos; first by interval.
      by clear; split_Rabs; nra.
    apply: Rmult_le_pos; first by interval.
    by apply: Rabs_pos.
  apply: Rplus_le_compat.
    apply: Rmult_le_compat; try lra; try by interval.
    have -> : (- 16 = - 8 + - 8)%Z by [].
    rewrite bpow_plus.
    by clear -rB; split_Rabs; nra.
  by apply: Rmult_le_compat; try (lra); interval.
have AC_pos : 0 < A - C by rewrite /A /C; interval.
have zphplB : (A - C) * Rabs z <= Rabs (z + ph + pl).
  have -> : (A - C) * Rabs z = A * Rabs z - C * Rabs z by lra.
  apply: Rle_trans (_ : Rabs (z + ph) - Rabs pl <= _); last first.
    by clear; split_Rabs; lra.
  apply: Rplus_le_compat.
    apply/Rle_div_r; first by clear -z_neq0; split_Rabs; lra.
    by lra.
  apply: Ropp_le_contravar.
  apply/Rle_div_l; first by clear -z_neq0; split_Rabs; lra.
  by lra.
have delta'B : Rabs delta' <= Rpower 2 (- 69.5776).
  rewrite /delta'.
  have -> : (h' + l') / (z + ph + pl) - 1 = 
            ((h' + l')  - (z + ph + pl)) / (z + ph + pl) by field.
  rewrite Rabs_div //.
  apply: Rle_trans (_ : 
        ((pow (-103) + pow (-156)) * Rabs (z + ph) + pow (-52) * Rabs pl ) /
        ((A - C) * Rabs z)  <= _).
    apply: Rmult_le_compat => //; first by apply: Rabs_pos.
      by apply/Rinv_0_le_compat/Rabs_pos.
    apply: Rinv_le => //.
    suff: 0 < Rabs z by clear -AC_pos; nra.
    by clear -z_neq0; split_Rabs; nra.
  have -> : ((pow (-103) + pow (-156)) * Rabs (z + ph) + pow (-52) * Rabs pl) 
                / ((A - C) * Rabs z) = 
            (pow (-103) + pow (-156))/ (A - C) * (Rabs (z + ph)/Rabs z) + 
            pow (-52) / (A - C) * (Rabs pl / Rabs z).
    by field; split; try lra.
  apply: Rle_trans (_ : 
    (pow (-103) + pow (-156)) / (A - C) * B + pow (-52) / (A - C) * C <= _); 
           last first.
    by rewrite /A /B /C; interval.
  apply: Rplus_le_compat.
    apply: Rmult_le_compat_l; last by lra.
    apply: Rmult_le_pos; first by interval.
    by apply: Rinv_0_le_compat; lra.
  apply: Rmult_le_compat_l; last by lra.
  apply: Rmult_le_pos; first by interval.
  by apply: Rinv_0_le_compat; lra.
pose lambda := (z + ph) / z.
have lambdaE : z + ph = lambda * z.
  by rewrite /lambda; field; lra.
have lambdaB : A <= Rabs lambda <= B.
  have-> : Rabs lambda = Rabs (z + ph) / Rabs z by rewrite Rabs_div; lra.
  by lra.
pose mu := pl / z.
have muE : pl = mu * z.
  by rewrite /mu; field; lra.
have muB : Rabs mu <= C.
  have-> : Rabs mu = Rabs pl / Rabs z by rewrite Rabs_div; lra.
  by lra.
have h'E1 : h' = lambda * z * (1 + delta1').
  by rewrite delta1'E /lambda; field.
have l'E2 : l' = (- lambda * z * delta1' * (1 + delta2') + mu * z) * 
              (1 + delta3').
  by rewrite l'E1 h'E1 /lambda /mu; field.
have h'zB : 0.998 <= Rabs h' / Rabs z.
  apply: Rle_trans (_ : A * (1 - pow (- 52)) <= _).
    by rewrite /A; interval.
  rewrite h'E1 2!Rabs_mult.
  have -> : Rabs lambda * Rabs z * Rabs (1 + delta1') / Rabs z = 
            Rabs lambda * Rabs (1 + delta1').
    by field; clear -z_neq0; split_Rabs; lra.
  apply: Rmult_le_compat; try (by lra); try by rewrite /A; interval.
  apply: Rle_trans (_ : Rabs 1 - Rabs delta1' <= _).
    by rewrite [Rabs 1]Rabs_pos_eq; lra.
  by clear; split_Rabs; lra.
have l'zB : Rabs l' / Rabs z <= Rpower 2 (- 17.5).
  apply: Rle_trans (_ : (B * pow (- 52) * (1 + pow (- 52)) + C) * 
                            (1 + pow (- 52)) <= _); last first.                            
    by rewrite /B /C; interval.
  rewrite l'E2.
  have -> : (- lambda * z * delta1' * (1 + delta2') + mu * z) = 
            z * (- lambda * delta1' * (1 + delta2') + mu) by lra.
  rewrite 2!Rabs_mult.
  have -> : Rabs z * Rabs (- lambda * delta1' * (1 + delta2') + mu) * 
             Rabs (1 + delta3') / Rabs z = 
            Rabs (- lambda * delta1' * (1 + delta2') + mu) * 
             Rabs (1 + delta3').
    by field; clear -z_neq0; split_Rabs; lra.
  apply: Rmult_le_compat; try by apply: Rabs_pos.
    apply: Rle_trans (Rabs_triang _ _) _.
    apply: Rplus_le_compat; last by lra.
    rewrite !Rabs_mult Rabs_Ropp.
  apply: Rmult_le_compat; try by apply: Rabs_pos.
  - by apply: Rmult_le_pos; apply: Rabs_pos.
  - by apply: Rmult_le_compat; try (by lra); apply: Rabs_pos.
  - apply: Rle_trans (_ : Rabs 1 + Rabs delta2' <= _).
      by clear; split_Rabs; lra.
    by rewrite [Rabs 1]Rabs_pos_eq; lra.
  apply: Rle_trans (_ : Rabs 1 + Rabs delta3' <= _).
    by clear; split_Rabs; lra.
  by rewrite [Rabs 1]Rabs_pos_eq; lra.
have l'Lh' : Rabs l' <= Rabs h'.
  have -> : Rabs l' = Rabs l' / Rabs z * Rabs z 
    by field; clear -z_neq0; split_Rabs; lra.
  have -> : Rabs h' = Rabs h' / Rabs z * Rabs z 
    by field; clear -z_neq0; split_Rabs; lra.
  apply: Rmult_le_compat_r; first by apply: Rabs_pos.
  apply: Rle_trans l'zB _.
  by apply: Rle_trans h'zB; interval.
have h'l'_neq0 : h' + l' <> 0.
  suff : 0 < Rabs (h' + l') by clear; split_Rabs; lra.
  apply: Rlt_le_trans (_ : Rabs h' - Rabs l' <= _); last first.
    by clear; split_Rabs; lra.
  suff : Rabs l' < Rabs h' by lra.
  have -> : Rabs l' = Rabs l' / Rabs z * Rabs z 
    by field; clear -z_neq0; split_Rabs; lra.
  have -> : Rabs h' = Rabs h' / Rabs z * Rabs z 
    by field; clear -z_neq0; split_Rabs; lra.
  apply: Rmult_lt_compat_r; first by clear -z_neq0; split_Rabs; lra.
  apply: Rle_lt_trans l'zB _.
  by apply: Rlt_le_trans h'zB; interval.
pose delta'' := (h''  + l'') / (h' + l') - 1.
have delta''E : h'' + l'' = (h' + l') * (1 + delta'').
  by rewrite /delta''; field.
have h''l''E : h'' + l'' = ln x * (1 + delta) * (1 + delta') * (1 + delta'').
  by rewrite delta''E delta'E deltaE.
have delta''B : Rabs delta'' <= pow (- 105).
  rewrite /delta''.
  have -> : (h'' + l'') / (h' + l') - 1 = (h'' + l'' - (h' + l')) / (h' + l').
    by field; lra.
  rewrite Rabs_div //.
  apply/Rle_div_l.
    by clear -h'l'_neq0; split_Rabs; lra.
  have := @fastTwoSum_correct1 h' l'.
  rewrite E5; apply => //.
    by rewrite h'E; apply: generic_format_round.
  by rewrite l'E; apply: generic_format_round.
have h''E : h''= RND (h' + l') by case: E5 => <-.
have l''E : l'' = RND (h' + l' - h'').
  case: E5 => <- <-.
  have -> : RND (RND (h' + l') - h') = RND (h' + l') - h'.
    rewrite round_generic //.
    apply: sma_exact_abs_or0 => //.
      by rewrite h'E; apply: generic_format_round.
    by rewrite l'E; apply: generic_format_round.
  by congr (RND _); rewrite -[round _ _ _ _]/(RND _); lra.
have := h'_l'_bound Fx xB.
lazy zeta; rewrite E E1 E2 E3 E4 -/l' => [] [imul_h' _ _ imul_l' _].
have imul_h'l' : is_imul (h' + l') (pow (- 543)).
  apply: is_imul_add => //.
  by apply: is_imul_pow_le imul_h' _.
have h''_neq0 : h'' <> 0.
  suff: pow (- 543) <= Rabs h''.
    by rewrite /= /Z.pow_pos /=; clear; split_Rabs; lra.
  rewrite h''E.
  apply: format_Rabs_round_le; first by apply: generic_format_bpow.
  by apply: is_imul_pow_le_abs.
pose delta1'' := (h' + l') / h'' - 1.
have delta1''E : h' + l' = h'' * (1 + delta1'').
  by rewrite /delta1''; field.
have delta1''B : Rabs delta1'' < pow (- 52).
  rewrite /delta1'' h''E in h''_neq0 *.
  set xx := h' + l' in h'l'_neq0 imul_h'l' h''_neq0 *.
  clear - valid_rnd h'l'_neq0 imul_h'l' h''_neq0.
  have -> : Rabs (xx / RND xx - 1) = Rabs  (RND xx - xx) / Rabs (RND xx).
    rewrite -Rabs_div // -Ropp_minus_distr Rabs_Ropp.
    by congr (Rabs _); field.
  apply/Rlt_div_l; first by split_Rabs; lra.
  rewrite round_FLT_FLX.
    by apply: relative_error_FLX_round.
  apply: is_imul_pow_le_abs => //.
  by apply: is_imul_pow_le imul_h'l' _.
pose delta2'' := if (Req_bool (h' + l' - h'') 0) 
                 then 0 else  l'' / (h' + l' - h'') - 1.
have delta2''E : l'' = (h' + l' - h'') * (1 + delta2'').
  rewrite /delta2'' l''E.
  have [->|h'l'h''_neq0] := Req_dec (h' + l' - h'') 0.
    rewrite round_0 Rsimp01; lra.
  by rewrite Req_bool_false //; field.
have imul_h'l'h'' : is_imul (h' + l' - h'') (pow (- 543)).
  apply: is_imul_minus => //.
  rewrite h''E.
  by apply: is_imul_pow_round.
have delta2''B : Rabs delta2'' < pow (- 52).
  rewrite /delta2'' l''E.
  have [h'l'h''_eq0|h'l'h''_neq0] := Req_dec (h' + l' - h'') 0.
    by rewrite Req_bool_true // Rsimp01; interval.
  rewrite Req_bool_false //.
  set xx := h' + l' - h'' in h'l'h''_neq0 imul_h'l'h'' *. 
  have -> : Rabs (RND xx / xx - 1) = Rabs  (RND xx - xx) / Rabs xx.
    by rewrite -Rabs_div //; congr (Rabs _); field.
  apply/Rlt_div_l; first by clear -h'l'h''_neq0; split_Rabs; lra.
  apply: relative_error_FLT => //.
  apply: is_imul_pow_le_abs => //.
  by apply: is_imul_pow_le imul_h'l'h'' _.
split.
  rewrite delta2''E delta1''E.
  have -> : Rabs ((h'' * (1 + delta1'') - h'') * (1 + delta2'')) = 
         Rabs (delta1'') * Rabs (1 + delta2'') * Rabs h''.
    by rewrite -!Rabs_mult; congr (Rabs _); lra.
  suff : Rabs delta1'' * Rabs (1 + delta2'') <= Rpower 2 (-51.99).
    have: 0 <= Rabs h'' by apply: Rabs_pos.
    by clear; nra.
  apply: Rle_trans (_ : pow (-52) * (1 + pow (- 52)) <= _).
    apply: Rmult_le_compat; try (by apply: Rabs_pos); try lra.
    by clear -delta2''B; split_Rabs; lra.
  by interval.
rewrite h''l''E.
have -> : Rabs (ln x * (1 + delta) * (1 + delta') * (1 + delta'') - ln x) =
          Rabs ((1 + delta) * (1 + delta') * (1 + delta'') - 1) * 
            Rabs (ln x).
  by rewrite -Rabs_mult; congr (Rabs _); lra.
suff : Rabs ((1 + delta) * (1 + delta') * (1 + delta'') - 1) <=
       Rpower 2 (-67.145).
  have: 0 <= Rabs (ln x) by apply: Rabs_pos.
  by clear; nra.
have -> : (1 + delta) * (1 + delta') * (1 + delta'') - 1 = 
           delta * (1 + delta') * (1 + delta'') + 
           delta' * (1 + delta'') +
           delta'' by lra.
by interval.
Qed.

(* This is lemma 4 *)
Lemma err_lem4 x : 
  format x -> alpha <= x <= omega ->
  let: DWR h l := log1 x in
  [/\ Rabs l <= Rpower 2 (- 23.89) * Rabs h,
      Rabs (h + l - ln x) <= Rpower 2 (- 67.0544 ) * Rabs (ln x) & 
     ~(/ sqrt 2 < x < sqrt 2) -> 
     Rabs (h + l - ln x) <= Rpower 2 (- 73.527) * Rabs (ln x)].
Proof.
move=> Fx xB.
case E : (getRange x) => [t e].
pose i := getIndex t.
have [e_eq0|e_neq0] := Z.eqb_spec e 0.
  have [tN eB] := getRangeCorrect Fx xB.
  rewrite E /fst /snd e_eq0 pow0E !Rsimp01 in tN eB.
  rewrite -eB in tN.
  have [iC|[iC1 iC2]]: 
    (i = 255%N \/ i = 256%N) \/ (i <> 255%N /\ i <> 256%N) by lia.
  have := err_lem4_e_eq0_iE255_iE256 Fx xB; rewrite E.
  move/(_ e_eq0 iC).
  case: log1 => h l [Hh Hl]; split => //.
    apply: Rle_trans Hh _.
    suff : Rpower 2 (-51.99) <= Rpower 2 (-23.89).
      have : 0 <= Rabs h by apply: Rabs_pos.
      by clear; nra.
    by interval.
  apply: Rle_trans Hl _.
  suff : Rpower 2 (-67.145) <= Rpower 2 (-67.0544).
    have : 0 <= Rabs (ln x) by apply: Rabs_pos.
    by clear; nra.
  by interval.
- have := err_lem4_e_eq0_iD255_iD256 Fx xB; rewrite E.
  move/(_ e_eq0 iC1 iC2).
  case: log1 => h l [Hh Hl]; split => //.
  apply: Rle_trans Hh _.
  suff : Rpower 2 (-44.89998) <= Rpower 2 (-23.89).
    have : 0 <= Rabs h by apply: Rabs_pos.
    by clear; nra.
  by interval.
have := err_lem4_e_neq0_i Fx xB; rewrite E.
move/(_ e_neq0).
case: log1 => h l [Hh Hl]; split => //.
apply: Rle_trans Hl _.
suff : Rpower 2 (-73.527) <= Rpower 2 (-67.0544).
  have : 0 <= Rabs (ln x) by apply: Rabs_pos.
  by clear; nra.
by interval.
Qed.

End Log1.
