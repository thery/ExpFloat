Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
Require Import tableINVERSE tableLOGINV algoP1.

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
    sqrt 2 / 2 < (getRange f).1 < sqrt 2 /\ 
    f = ((getRange f).1) * pow (getRange f).2.

Hypothesis getRangeFormat : 
  forall f,  format f -> alpha <= f <= omega -> format (getRange f).1. 

Lemma getRange_bound f : 
  format f -> alpha <= f <= omega -> (- 1074 <= (getRange f).2 <= 1024)%Z.
Proof.
move=> aF aB.
have sqrt2B : 1.4 < sqrt 2 < 1.5 by split; interval.
have [tN eB] := getRangeCorrect aF aB.
set t := (_).1 in eB tN; set e := (_).2 in eB *.
suff:  (- 1075 < e < 1025)%Z by lia.
suff : -1075 < IZR e < 1025 by case; split; apply/lt_IZR.
suff:  Rpower 2 (- 1075) < Rpower 2 (IZR e) < Rpower 2 (1025).
  have: IZR e <= - 1075 -> Rpower 2 (IZR e) <= Rpower 2 (- 1075).
    by apply: Rle_Rpower; lra.
  have: 1025 <= IZR e -> Rpower 2 1025 <= Rpower 2 (IZR e).
    by apply: Rle_Rpower; lra.
  by lra.
have -> : Rpower 2 (IZR e) = pow e by rewrite pow_Rpower.
suff : t * Rpower 2 (-1075) < t * pow e < t * Rpower 2 1025 by nra.
suff : sqrt 2 * Rpower 2 (-1075) < t * pow e < sqrt 2 / 2 * Rpower 2 1025.
  have : 0 < Rpower 2 (- 1075).
    by rewrite -pow_Rpower //; apply: bpow_gt_0.
  suff : 0 < Rpower 2 (1025) by nra.
  by rewrite -pow_Rpower //; apply: bpow_gt_0.
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

(* Check underflow *)
Lemma fastTwoSum_correct a b : 
  format a -> format b -> (a <> 0 -> Rabs b <= Rabs a) ->
  let: DWR h l := fastTwoSum a b in 
  Rabs (h + l - (a + b)) <= pow (- 105) * Rabs h.
Admitted.

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
by rewrite /= !(Rsimp01, Rminus_eq_0, round_0, p1_0, fastTwoSum_0).
Qed.

Lemma th_prop (e : Z) x : 
  x \in LOGINV -> (- 1074 <= e <= 1024)%Z ->
  let th := IZR e * LOG2H + x.1 in 
  [/\ is_imul th (pow (- 42)),
      format th, 
      e  = 0%Z -> th <> 0 -> 0.00587 < Rabs th < 0.347 & 
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
split => // [e_eq0 t_neq0|e_neq0].
  by rewrite /th e_eq0 !Rsimp01 in t_neq0 *; apply: x1B.
split => //.
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
  (emin + p <= e)%Z -> Rabs f < pow e -> ulp f <= pow (e - p).
Proof.
move=> epLe.
have [-> fLe |f_neq0 fLe] := Req_dec f 0.
  rewrite ulp_FLT_0.
  by apply: bpow_le; lia.
rewrite ulp_neq_0 // /cexp /fexp.
apply: bpow_le.
have magfE : (mag beta f <= e)%Z by apply: mag_le_bpow => //; lia.
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
  have -> : (- 86 = -33 - p)%Z by lia.
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
  set xx := IZR e * LOG2L + x.2.
  suff: Rabs (RND xx - xx) <= ulp xx by split_Rabs; lra.
  by apply: error_le_ulp.
split => // err1.
split.
  move=> e_eq0.
  rewrite /err1 /tl e_eq0 !Rsimp01.
  have [_ f_x2] := format_LOGINV xIL.
  by rewrite round_generic // Rminus_eq_0 !Rsimp01.
apply: Rle_trans (_ : ulp (IZR e * LOG2L + x.2) <= _) => //.
by apply: error_le_ulp.
Qed.

Lemma fastTwoSum_0l f : format f -> fastTwoSum 0 f = DWR f 0.
Proof.
move=> Ff; rewrite /fastTwoSum !Rsimp01 round_generic //.
congr DWR.
by rewrite (round_generic _ _ _ f) // Rminus_eq_0 round_0.
Qed.

Lemma fastTwoSum_0r f : format f -> fastTwoSum f 0 = DWR f 0.
Proof.
move=> Ff; rewrite /fastTwoSum !Rsimp01 round_generic //.
congr DWR.
by rewrite Rminus_eq_0 // round_0 Rsimp01 round_0.
Qed.

Lemma err2_bound  x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t := fastTwoSum th z in 
  let l := RND (t + tl) in
  let err2 := Rabs ((h + t) - (th + z)) in 
  (e = 0%Z -> err2 <= Rpower 2 (- 106.5)) /\ 
  (e <> 0%Z -> err2 <= Rpower 2 (- 94.458)).
Proof.
move=> Fx aLxLo.
case: getRange (getRangeCorrect Fx aLxLo) (getRange_bound Fx aLxLo)
      (getRangeFormat Fx aLxLo)
   => t e [Ht He] eB Ft.
rewrite /fst in Ht Ft; rewrite /fst /snd in He; rewrite /snd in eB.
move=> i r.
have sqrt2E : sqrt 2 / 2 = / sqrt 2.
  rewrite -{2}[2]pow2_sqrt; last by lra.
  by field; lra.
rewrite sqrt2E in Ht.
have iB := getIndexBound Ht.
rewrite -/i in iB.
case E:  (nth (1, 1) LOGINV (i - 181)) => [l1 l2].
move=> z th tl.
have l1l2_in : (l1, l2) \in LOGINV.
  rewrite -E; apply: mem_nth.
  rewrite size_LOGINV.
  rewrite ltn_subLR; first by case/andP: iB.
  by case/andP: iB.
have  [H1 H2 H3 H4]:= th_prop l1l2_in eB.
rewrite /fst in H1 H2 H3 H4.
have Ht1 : / sqrt 2 <= t < sqrt 2 by lra.
have [G1 G2 G3] := rt_float (refl_equal _) Ft Ht1.
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
have [th_eq0|th_neq0] := Req_dec th 0.
  rewrite th_eq0 fastTwoSum_0l //; last first.
    by apply: generic_format_round.
  rewrite !(Rminus_eq_0, round_0, Rsimp01) /=.
  by split => _; interval.
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
  by have := H4 e_neq0; lra.
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
case E1 : fastTwoSum => [h t1] l err2.
have imul_h : is_imul h (pow (- 61)).
  have ->: h = RND (th + z) by case: E1.
  by apply: is_imul_pow_round.
have hB1 : e <> 0%Z -> Rabs h < 745.
  move=> e_neq0.
  have ->: h = RND (th + z) by case: E1.
  set y := th + z in thzB1 *.
  apply: Rle_lt_trans (_ : Rabs y + ulp y < _).
    suff: Rabs (RND y - y) <= ulp y by split_Rabs; lra.
    by apply: error_le_ulp.
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
    suff: Rabs (RND y - y) <= ulp y by split_Rabs; lra.
    by apply: error_le_ulp.
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
  by have := H4 e_neq0; lra.
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
have Fht : format (h - th).
  have : |z
Qed.

Lemma err2_err3_e_eq0  x : 
  format x -> 
  alpha <= x <= omega ->
  let: (t, e) := getRange x in
  let i  := getIndex t in
  let r  := nth 1 INVERSE (i - 181) in
  let: (l1, l2) := nth (1,1) LOGINV (i - 181) in
  let z  := RND (r * t  - 1) in
  let th := RND (IZR e * LOG2H + l1) in 
  let tl := RND (IZR e * LOG2L + l2) in
  let: DWR h t := fastTwoSum th z in 
  let l := RND (t + tl) in
  let err2 := Rabs ((h + t) - (th + z)) in 
  let err3 := Rabs (l - (t + tl)) in
  e = 0%Z -> err2 + err3 <= Rpower 2 (- 94.999).
Proof.
move=> Fx aLxLo.
case: getRange (getRangeCorrect Fx aLxLo) => t e [Ht He].
rewrite /fst in Ht; rewrite /fst /snd in He.
move=> i r.
case E:  (nth (1, 1) LOGINV (i - 181)) => [l1 l2].
move=> z th tl.

  x m\in LOGINV -> (e = 0)%Z ->
  let th := IZR e * LOG2H + x.1 in 
  let tl := RND (IZR e * LOG2L + x.2) in 
(* This is lemma 4*)

Lemma hl_logB x : 
  alpha <= x -> format x ->
  let: DWR h l := log1 x in 
  [/\ Rabs l <= Rpower 2 (- 23.89) * Rabs h,
      Rabs (h + l - ln x) <= (Rpower 2  (- 67.0544)) * Rabs (ln x) &
      ~ (sqrt 2 / 2 < x < sqrt 2) -> 
      Rabs (h + l - ln x) <= (Rpower 2  (- 73.527)) * Rabs (ln x)].
Proof.
move=> aLx Fx.
have sqrt2B : 1.4 < sqrt 2 < 1.5 by split; interval.
have [x_eq1|x_neq1] := Req_dec x 1.
  by rewrite x_eq1 log1_1 !Rsimp01; split; [lra | interval | move=> _; interval].
Admitted.
  
End Log1.

