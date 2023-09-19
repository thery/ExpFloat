Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim algoLog1.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section algoQ1.

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
Context { valid_rnd : Valid_rnd rnd }.

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

Definition Q0 := 1.
Definition Q1 := 1.
Definition Q2 := 0.5.
Definition Q3 := 0x1.5555555997996p-3.
Definition Q4 := 0x1.55555558489dcp-5.

Definition Qf0 : float := 
  Float _ 1 0.

Definition Qf1 : float := 
  Float _ 1 0.

Definition Qf2 : float := 
  Float _ 1 (-1).

Definition Qf3 : float := 
  Float _ 6004799507619127 (-55).

Definition Qf4 : float := 
  Float _ (6004799506254300) (-57).

Fact Qf0E : F2R Qf0 = Q0.
Proof. by rewrite /Q0 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_Q0 : format Q0.
Proof.
rewrite -Qf0E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Qf1E : F2R Qf1 = Q1.
Proof. by rewrite /Q1 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_Q1 : format Q1.
Proof.
rewrite -Qf1E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Qf2E : F2R Qf2 = Q2.
Proof. by rewrite /Q2 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_Q2 : format Q2.
Proof.
rewrite -Qf2E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Qf3E : F2R Qf3 = Q3.
Proof. rewrite /Q3 /F2R /Q2R /= /Z.pow_pos /=; field. Qed.

Lemma format_Q3 : format Q3.
Proof.
rewrite -Qf3E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Fact Qf4E : F2R Qf4 = Q4.
Proof. rewrite /Q4 /F2R /Q2R /= /Z.pow_pos /=. field. Qed.

Lemma format_Q4 : format Q4.
Proof.
rewrite -Qf4E.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Definition Q z :=
  Q0 + Q1 * z + Q2 * z ^ 2 + Q3 * z ^ 3 + Q4 * z ^ 4.

Lemma Q_abs_error z :
  Rabs z <= 0.000130273 -> 
  Rabs (exp z - Q z) <= Rpower 2 (- 74.346).
Proof.
move=> *; rewrite /Q /Q0 /Q1 /Q2 /Q3 /Q4.
interval with (i_prec 90, i_bisect z, i_taylor z).
Qed.

(* L'algo q_1 *)

Definition q1 (z : dwR) :=
  let: DWR zh zl := z in 
  let z := RND (zh + zl) in 
  let q := RND (Q4 * zh + Q3) in
  let q := RND (q * z + Q2) in
  let: DWR h0 l0 := fastTwoSum Q1 (RND (q * z)) in
  let: DWR h1 s := exactMul zh h0 in
  let t := RND(zl * h0 + s) in
  let l1 := RND(zh * l0 + t) in
  fastSum Q0 h1 l1.

Lemma err_lem6 z :
  let: DWR zh zl := z in 
  let: DWR qh ql := q1 z in 
  Rabs (zh + zl) <= 0.000130273 -> Rabs zl <= Rpower 2 (- 42.7260) ->
  Rabs ((qh - ql) / exp (zh + zl) - 1) < Rpower 2 (- 74.169053) /\ 
  Rabs ql <= Rpower 2 (- 42.7096).
Proof.
move: z => z1.
case Ez1 : z1 => [zh zl].
case Eq : q1 => [qh ql].
set Z := zh + zl => ZB zlB.
move: Eq.
rewrite /q1; set z := RND (zh + zl).
set q := RND (Q4 * _ + _); set q1 := RND (q * _ + _).
case Ef : fastTwoSum => [h0 l0].
case Em : exactMul => [h1 s].
set t := RND(zl * _ + _); set l1 := RND(zh * _ + _) => Es.
have zB : Rabs z < Rpower 2 (- 12.80).
  apply: Rle_lt_trans (_ : 0.000130273 * (1 + pow (- 52)) < _); last first.
    by interval.
    Search "rel" "err"  FLT_exp.
  Search (_ * (_ + _)).




Admitted.

End algoQ1.

