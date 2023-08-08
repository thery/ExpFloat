Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
Require Import tableINVERSE tableLOGINV algoP1 Fast2Sum_robust.

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
  by apply: error_le_ulp_add.
split => // err1.
split.
  move=> e_eq0.
  rewrite /err1 /tl e_eq0 !Rsimp01.
  have [_ f_x2] := format_LOGINV xIL.
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

Lemma err2_err3_l_bound  x : 
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
     (e <> 0%Z -> err3 <= pow (- 86)),
     (e = 0%Z -> Rabs l <= Rpower 2 (- 42.89)) /\
     (e <> 0%Z -> Rabs l <= Rpower 2 (- 33.78)) & 
     is_imul l (pow (- 104))].     
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
  - move=> e_eq0; rewrite round_generic //; last by apply: generic_format_round.
    have [->|tl_neq0] := Req_dec tl 0; first by interval.
    have := L2 e_eq0 tl_neq0.
    set xx := Rabs tl => ?; interval.
  - move=> e_neq0; rewrite round_generic //; last by apply: generic_format_round.
    have [->|tl_neq0] := Req_dec tl 0; first by interval.
    have := L3 e_neq0 tl_neq0.
    by set xx := Rabs tl => ?; interval.
  by rewrite round_generic //; apply: generic_format_round.
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
  have -> : (- 43 = 10 - p)%Z by [].
  apply: bound_ulp => //.
  by apply: thzB3.
have t1B2 : e = 0%Z -> Rabs t1 <= pow (- 54).
  move=> e_eq0.
  apply: Rle_trans (_ : ulp (th + z) <= _).
    rewrite -t1E -hE.
    by apply: sma_ulp.
  have -> : (- 54 = -1 - p)%Z by [].
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
  have -> : (-86 = -33 - p)%Z by [].
  apply: bound_ulp => //.
  have {}t1tlB1 := t1tlB1 e_neq0.
  by set xx := Rabs _ in t1tlB1 *; interval.
have ulp_t1tlB2 : e = 0%Z -> ulp (t1 + tl) <= pow (- 95).
  move=> e_eq0.
  have -> : (- 95 = - 42 - p)%Z by [].
  apply: bound_ulp => //.
  have {}t1tlB2 := t1tlB2 e_eq0.
  by set xx := Rabs _ in t1tlB2 *; interval.
split => //.
- split=>  // [e_eq0|e_neq0]; last first.
    apply: Rle_trans (_ : pow (- 105) * Rabs h <= _).
      rewrite /err2.
      have := @fastTwoSum_correct th z Fth G1.
      rewrite [fastTwoSum _ _]E1.
      by apply.
    have := hB1 e_neq0.
    by set xx := Rabs h => ?; interval.
  apply: Rle_trans (_ : pow (- 105) * Rabs h <= _).
    rewrite /err2.
    have := @fastTwoSum_correct th z Fth G1.
    rewrite [fastTwoSum _ _]E1.
    by apply.
  have := hB2 e_eq0.
  by set xx := Rabs h => ?; interval.
- split => [e_eq0|e_neq0]; last first.
    apply: Rle_trans (_ : ulp (t1 + tl) <= _); first by apply: error_le_ulp.
    by apply: ulp_t1tlB1.
  apply: Rle_trans (_ : ulp (t1 + tl) <= _); first by apply: error_le_ulp.
  by apply: ulp_t1tlB2.
rewrite /l; set xx := t1 + tl.
split => [e_eq0|e_neq0].
  apply: Rle_trans (_ : Rabs xx + ulp xx <= _).
    by apply: error_le_ulp_add.
  have {}t1tlB2 := t1tlB2 e_eq0.
  have {}ulp_t1tlB2 := ulp_t1tlB2 e_eq0.
  rewrite -/xx in t1tlB2 ulp_t1tlB2.
  by interval.
apply: Rle_trans (_ : Rabs xx + ulp xx <= _).
  by apply: error_le_ulp_add.
have {}t1tlB1 := t1tlB1 e_neq0.
have {}ulp_t1tlB1 := ulp_t1tlB1 e_neq0.
rewrite -/xx in t1tlB1 ulp_t1tlB1.
by interval.
Qed.

Lemma err23_l_bound  x : 
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
have F1 := err2_err3_l_bound Fx xB.
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

Lemma er_l_bound  x : 
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
have imul_l : is_imul l (pow (-104)).
  have F1 := err2_err3_l_bound Fx xB.
  lazy zeta in F1.
  rewrite E E1 E2 in F1.
  by have {}[_ _ _ imul_l] := F1.
have Fz : format z by apply: generic_format_round.
have Ft : format t by have := getRangeFormat Fx xB; rewrite E.
have tB : / sqrt 2 < t < sqrt 2.
  have<- : sqrt 2 / 2 = / sqrt 2.
    rewrite -{2}[2]pow2_sqrt; last by lra.
    by field; interval.
  by have [] := getRangeCorrect Fx xB; rewrite E.
have zB : Rabs z <= 33 * Rpower 2 (- 13).
  rewrite - pow_Rpower //.
  have [] := rt_float _ Ft tB => //.
  rewrite -/r -/z => Frt1 rtB _.
  by rewrite /z round_generic.  
have imul_z : is_imul z (Rpower 2 (-61)).
  have [] := rt_float _ Ft tB  => // _ _ F1.
  rewrite - pow_Rpower //.
  by apply: is_imul_pow_round.
have imul_pl : is_imul pl (pow (- 543)).
  have := @imul_pl_p1 _ rnd _ z Fz zB.
  by rewrite E3; apply.
have imul_lp : is_imul lp (pow (- 543)).
  apply: is_imul_add => //.
  by apply: is_imul_pow_le imul_l _.
have lB : Rabs l <= Rpower 2 (-33.78).
  have F1 := err2_err3_l_bound Fx xB.
  lazy zeta in F1.
  rewrite E E1 E2 in F1.
  have {}[_ _ [H1 H2] _] := F1.
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
  have -> : (- 78 = -25 - p)%Z by [].
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

Lemma relative_error_eps x :
  pow (emin + p - 1) <= Rabs x ->
  Rabs x * (1 - pow (- p + 1)) <=  Rabs (RND x).
Proof.
move=> xB.
have F1 :  Rabs (RND x - x) < pow (- p + 1) * Rabs x.
  by apply: relative_error_FLT.
by split_Rabs; nra.
Qed.

Lemma xxx_bound  x : 
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
  by interval.
have Fz : format z by apply: generic_format_round.
have Ft : format t by have := getRangeFormat Fx xB; rewrite E.
have tB : / sqrt 2 < t < sqrt 2.
  have<- : sqrt 2 / 2 = / sqrt 2.
    rewrite -{2}[2]pow2_sqrt; last by lra.
    by field; interval.
  by have [] := getRangeCorrect Fx xB; rewrite E.
have zB : Rabs z <= 33 * Rpower 2 (- 13).
  rewrite - pow_Rpower //.
  have [] := rt_float _ Ft tB => //.
  rewrite -/r -/z => Frt1 rtB _.
  by rewrite /z round_generic.  
have fast_cond : h <> 0 -> Rabs ph <= Rabs h.
  move=> _.
  have [th_eq0|th_neq0] := Req_dec th 0.
    have hE : h = z.
      rewrite th_eq0 fastTwoSum_0l // in E2.
      by case: E2.
    rewrite hE.
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
        have imul_z : is_imul (z) (pow (- 61)).
          apply: is_imul_pow_round.
          by have [] := rt_float _ Ft tB.
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
  have hE : h = RND (th + z) by case: E2.
Admitted.

End Log1.

