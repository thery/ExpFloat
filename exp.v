Require Import Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Plot Tactic.
Require Import Nmore Rmore Fmore Rstruct.

Delimit Scope R_scope with R.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Exp.

Variable p : Z.
Let beta := radix2.

Hypothesis Hp2: Z.lt 1 p.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).

Variable choice : Z -> bool.
Hypothesis choice_sym: forall x, choice x  = negb (choice (- (x + 1))).

Local Notation float := (float radix2).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RN := (round beta fexp (Znearest choice)).
Definition RNF x : float :=
    {|
	Fnum := Znearest choice (scaled_mantissa beta fexp x);
    Fexp := Generic_fmt.cexp beta fexp x
    |}.

Lemma RNFE x : RN x = F2R (RNF x).
Proof. by []. Qed.

Local Notation ulp := (ulp beta fexp).

Inductive dwfloat := DWFloat (xh : float) (xl : float).

Coercion F2R : float >-> R.

Definition exactMul (a b : float) : dwfloat := 
  let h := RNF (a * b) in 
  let l := RNF(a * b - h) in 
  DWFloat h l.

Check exactMul.

Definition fastTwoSum (a b : float) :=
  let s := RNF (a + b) in
  let z := RNF (s - a) in
  DWFloat s (RNF (b - z)).

Check fastTwoSum.

Definition twoSum (a : float) (b : dwfloat) :=  
  let: DWFloat bh bl := b in 
  let: DWFloat h t := fastTwoSum a bh in 
  let: l := RNF (t + bl) in DWFloat h l.

Check twoSum.

Definition P3 :=
  0.33333333333333348136306995002087205648422241210937.
Definition P4 := 0.25000000000000016653345369377348106354475021362305.
Definition P5 := 0.199999999956995161420891804482380393892526626586914.
Definition P6 := 0.166666666622622750004723002348328009247779846191406.
Definition P7 := 0.142861026799963208855359653171035461127758026123047.
Definition P8 := 0.12500370131039634236103097464365419000387191772461.

Definition P z :=
    z - z ^ 2 / 2 + P3 * z ^ 3 
  - P4 * z ^ 4 + P5 * z ^ 5 - P6 * z ^ 6 + P7 * z ^ 7 - P8 * z ^ 8. 

Definition Pz z :=
    1 - z / 2 + P3 * z ^ 2 
  - P4 * z ^ 3 + P5 * z ^ 4 - P6 * z ^ 5 + P7 * z ^ 6 - P8 * z ^ 7. 

Lemma PzE z : P z = z * Pz z.
Proof. by rewrite /Pz /P; lra. Qed.

Lemma Pz_pos z :
  Rabs z < 33 * (Rpower 2 (-13)) -> 0 <= Pz z.
Proof.
by move=> *; rewrite /Pz /P3 /P4 /P5 /P6 /P7 /P8; interval.
Qed.

Lemma P_abs_error z :
  Rabs z < 33 * (Rpower 2 (-13)) ->
  Rabs (ln (1 + z) - P z) <= Rpower 2 (- (81.63)).
Proof.
move=> *; rewrite /P /P3 /P4 /P5 /P6 /P7 /P8.
interval with (i_prec 90, i_bisect z, i_taylor z, i_degree 8).
Qed.

Definition p1 := ltac:(plot  (fun z => 
  (ln(1 + z) - (1 + Rpower 10 (- 4)) * z))
   (0.00)
   0.0001).

Plot p1.

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



 => [Hc Hv].
Search (ln 1).
lra.
auto_derive; try lra.
Qed.

Search derive_pt Derive.
Check MVT.
Search "MVT".
Check MVT_cor4.
Lemma foo x : (Rpower 10 (-100)) <= x <= (Rpower 10 (-4)) ->
  0 <= (x - ln(1 + x)).
intros.
interval with (i_prec 420, i_bisect x, i_taylor x, i_degree 40).
Qed.




Definition p1 := ltac:(plot  (fun z => 
  (1 -
   (z - z ^ 2 / 2 +
    0.33333333333333348136306995002087205648422241210937 * z ^ 3 -
    0.25000000000000016653345369377348106354475021362305 * z ^ 4 +
    0.199999999956995161420891804482380393892526626586914 * z ^ 5 -
    0.166666666622622750004723002348328009247779846191406 * z ^ 6 +
    0.142861026799963208855359653171035461127758026123047 * z ^ 7 -
    0.12500370131039634236103097464365419000387191772461 * z ^ 8) / 
    (ln (1 + z))))
   (0.000000005)
   0.0005
   (- Rpower 2 (-(72.423)))
   (Rpower 2 (-(72.423)))
    with  (i_prec 400, i_degree 50)).

Plot p1.




(*
Lemma P_abs_error z :
  Rabs z < 33 * Rpower 2 (-13) ->
  Rabs (ln (1 + z) -
   (z - z ^ 2 / 2 +
    0.33333333333333348136306995002087205648422241210937 * z ^ 3 -
    0.25000000000000016653345369377348106354475021362305 * z ^ 4 +
    0.199999999956995161420891804482380393892526626586914 * z ^ 5 -
    0.166666666622622750004723002348328009247779846191406 * z ^ 6 +
    0.142861026799963208855359653171035461127758026123047 * z ^ 7 -
    0.12500370131039634236103097464365419000387191772461 * z ^ 8)) 
     <= Rpower 2 (- (81.63)).
Proof.
intros.
interval with (i_prec 120, i_bisect z, i_taylor z, i_degree 10).
Qed.

Lemma P_rel_error z :
  Rabs z < 33 * Rpower 2 (-13) ->
  Rabs ((ln (1 + z) -
   (z - z ^ 2 / 2 +
    0.33333333333333348136306995002087205648422241210937 * z ^ 3 -
    0.25000000000000016653345369377348106354475021362305 * z ^ 4 +
    0.199999999956995161420891804482380393892526626586914 * z ^ 5 -
    0.166666666622622750004723002348328009247779846191406 * z ^ 6 +
    0.142861026799963208855359653171035461127758026123047 * z ^ 7 -
    0.12500370131039634236103097464365419000387191772461 * z ^ 8)) / 
    (ln (1 + z))) <= Rpower 2 (-(72.423)).
Proof.
intros.
Fail interval with (i_prec 120, i_bisect z, i_taylor z, i_degree 10).
Admitted.

Definition p1 := ltac:(plot  (fun z => 
  (1 -
   (z - z ^ 2 / 2 +
    0.33333333333333348136306995002087205648422241210937 * z ^ 3 -
    0.25000000000000016653345369377348106354475021362305 * z ^ 4 +
    0.199999999956995161420891804482380393892526626586914 * z ^ 5 -
    0.166666666622622750004723002348328009247779846191406 * z ^ 6 +
    0.142861026799963208855359653171035461127758026123047 * z ^ 7 -
    0.12500370131039634236103097464365419000387191772461 * z ^ 8) / 
    (ln (1 + z))))
   (0.0005)
   ( 33 * (Rpower 2 (-13)))
   (- Rpower 2 (-(72.423)))
   (Rpower 2 (-(72.423)))
    with  (i_prec 120, i_degree 10)).

Plot p1.



End Exp.

