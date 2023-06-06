Require Import Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
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

Definition emult (a b : float) : dwfloat := 
  let h := RNF(F2R a * F2R b) in 
  let l := RNF(F2R a * F2R b - F2R h) in 
  DWFloat h l.

Check emult.

Definition fastTwoSum (a b : float) := 
 let s := RNF (F2R a + F2R b) in
 let z := RNF (F2R s - F2R a) in
 DWFloat s (RNF (F2R b - F2R z)).

Check fastTwoSum.


End Exp.

