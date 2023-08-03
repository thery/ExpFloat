Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore algoP1.

Locate Zfloor.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Exp.

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
Local Notation RN := (round beta fexp rnd).

Definition LOG2H : float := Float _ 3048493539143 (- 42).

Lemma LOG2HE : F2R LOG2H = 3048493539143 * (pow (- 42)).
Proof. by rewrite /LOG2H /F2R /= /Z.pow_pos. Qed.

Lemma format_LOG2H : format LOG2H.
Proof.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma imul_LOG2H : is_imul LOG2H (pow (- 42)).
Proof. by exists 3048493539143%Z. Qed.

Lemma error_LOG2H : Rabs (LOG2H - ln 2) < pow (-44).
Proof.
by rewrite LOG2HE !pow_Rpower //; interval with (i_prec 54).
Qed.

Definition LOG2L : float := Float _ 544487923021427 (- 93).

Lemma LOG2LE : F2R LOG2L = 544487923021427 * (pow (- 93)).
Proof. by rewrite /LOG2L /F2R /= /Z.pow_pos. Qed.

Lemma format_LOG2L : format LOG2L.
Proof.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => /=; lia.
Qed.

Lemma imul_LOG2L : is_imul LOG2L (pow (- 93)).
Proof. by exists 544487923021427%Z. Qed.

Lemma error_LOG2L : Rabs (LOG2H + LOG2L - ln 2) < pow (- 102).
Proof.
by rewrite LOG2HE LOG2LE !pow_Rpower //; interval with (i_prec 120).
Qed.

Definition err8 e := Rabs (IZR e * LOG2H + IZR e * LOG2L - IZR e * ln 2).

Lemma err8_0 : err8 0 = 0.
Proof. by rewrite /err8 !Rsimp01. Qed.

Lemma err8_bound e : (- 1074 <= e <= 1024)%Z -> err8 e <= Rpower 2 (- 91.949).
Proof.
move=> e8B.
have {e8B}e8B1 : - 1074 <= IZR e <= 1024.
  have [e8L e8R] := e8B.
  by split; apply: IZR_le; lia.
pose v := LOG2H + LOG2L - ln 2.
have vB : - Rpower 2 (- 102.018) < v < 0.
  by rewrite /v LOG2HE LOG2LE !pow_Rpower; split; interval with (i_prec 150).
have -> : err8 e = Rabs (IZR e * v).
  by congr (Rabs _); rewrite /v; lra.
by interval with (i_prec 150).
Qed.

Definition INVERSE : list R := 
  [:: 0x1.69p+0; 0x1.67p+0; 0x1.65p+0; 0x1.63p+0; 0x1.61p+0; 0x1.5fp+0;
      0x1.5ep+0; 0x1.5cp+0; 0x1.5ap+0; 0x1.58p+0; 0x1.56p+0; 0x1.54p+0; 
      0x1.53p+0; 0x1.51p+0; 0x1.4fp+0; 0x1.4ep+0; 0x1.4cp+0; 0x1.4ap+0;
      0x1.48p+0; 0x1.47p+0; 0x1.45p+0; 0x1.44p+0; 0x1.42p+0; 0x1.4p+0; 
      0x1.3fp+0; 0x1.3dp+0; 0x1.3cp+0; 0x1.3ap+0; 0x1.39p+0; 0x1.37p+0;
      0x1.36p+0; 0x1.34p+0; 0x1.33p+0; 0x1.32p+0; 0x1.3p+0;  0x1.2fp+0;
      0x1.2dp+0; 0x1.2cp+0; 0x1.2bp+0; 0x1.29p+0; 0x1.28p+0; 0x1.27p+0;
      0x1.25p+0; 0x1.24p+0; 0x1.23p+0; 0x1.21p+0; 0x1.2p+0; 0x1.1fp+0; 
      0x1.1ep+0; 0x1.1cp+0; 0x1.1bp+0; 0x1.1ap+0; 0x1.19p+0; 0x1.17p+0; 
      0x1.16p+0; 0x1.15p+0; 0x1.14p+0; 0x1.13p+0; 0x1.12p+0; 0x1.1p+0; 
      0x1.0fp+0; 0x1.0ep+0; 0x1.0dp+0; 0x1.0cp+0; 0x1.0bp+0; 0x1.0ap+0;
      0x1.09p+0; 0x1.08p+0; 0x1.07p+0; 0x1.06p+0; 0x1.05p+0; 0x1.04p+0;
      0x1.03p+0; 0x1.02p+0; 0x1.00p+0; 0x1.00p+0; 0x1.fdp-1; 0x1.fbp-1;
      0x1.f9p-1; 0x1.f7p-1; 0x1.f5p-1; 0x1.f3p-1; 0x1.f1p-1; 0x1.fp-1;
      0x1.eep-1; 0x1.ecp-1; 0x1.eap-1; 0x1.e8p-1; 0x1.e6p-1; 0x1.e5p-1;
      0x1.e3p-1; 0x1.e1p-1; 0x1.dfp-1; 0x1.ddp-1; 0x1.dcp-1; 0x1.dap-1;
      0x1.d8p-1; 0x1.d7p-1; 0x1.d5p-1; 0x1.d3p-1; 0x1.d2p-1; 0x1.dp-1;
      0x1.cep-1; 0x1.cdp-1; 0x1.cbp-1; 0x1.c9p-1; 0x1.c8p-1; 0x1.c6p-1;
      0x1.c5p-1; 0x1.c3p-1; 0x1.c2p-1; 0x1.cp-1; 0x1.bfp-1; 0x1.bdp-1;
      0x1.bcp-1; 0x1.bap-1; 0x1.b9p-1; 0x1.b7p-1; 0x1.b6p-1; 0x1.b4p-1;
      0x1.b3p-1; 0x1.b1p-1; 0x1.bp-1; 0x1.aep-1; 0x1.adp-1; 0x1.acp-1;
      0x1.aap-1; 0x1.a9p-1; 0x1.a7p-1; 0x1.a6p-1; 0x1.a5p-1; 0x1.a3p-1; 
      0x1.a2p-1; 0x1.a1p-1; 0x1.9fp-1; 0x1.9ep-1; 0x1.9dp-1; 0x1.9cp-1; 
      0x1.9ap-1; 0x1.99p-1; 0x1.98p-1; 0x1.96p-1; 0x1.95p-1; 0x1.94p-1; 
      0x1.93p-1; 0x1.91p-1; 0x1.9p-1; 0x1.8fp-1; 0x1.8ep-1; 0x1.8dp-1;
      0x1.8bp-1; 0x1.8ap-1; 0x1.89p-1; 0x1.88p-1; 0x1.87p-1; 0x1.86p-1;
      0x1.84p-1; 0x1.83p-1; 0x1.82p-1; 0x1.81p-1; 0x1.8p-1; 0x1.7fp-1;
      0x1.7ep-1; 0x1.7cp-1; 0x1.7bp-1; 0x1.7ap-1; 0x1.79p-1; 0x1.78p-1;
      0x1.77p-1; 0x1.76p-1; 0x1.75p-1; 0x1.74p-1; 0x1.73p-1; 0x1.72p-1;
      0x1.71p-1; 0x1.7p-1; 0x1.6fp-1; 0x1.6ep-1; 0x1.6dp-1; 0x1.6cp-1; 
      0x1.6bp-1; 0x1.6ap-1].

Definition FINVERSE : seq float := 
  [:: {| Fnum := 361; Fexp := -8 |}; {| Fnum := 359; Fexp := -8 |};
    {| Fnum := 357; Fexp := -8 |}; {| Fnum := 355; Fexp := -8 |};
    {| Fnum := 353; Fexp := -8 |}; {| Fnum := 351; Fexp := -8 |};
    {| Fnum := 350; Fexp := -8 |}; {| Fnum := 348; Fexp := -8 |};
    {| Fnum := 346; Fexp := -8 |}; {| Fnum := 344; Fexp := -8 |};
    {| Fnum := 342; Fexp := -8 |}; {| Fnum := 340; Fexp := -8 |};
    {| Fnum := 339; Fexp := -8 |}; {| Fnum := 337; Fexp := -8 |};
    {| Fnum := 335; Fexp := -8 |}; {| Fnum := 334; Fexp := -8 |};
    {| Fnum := 332; Fexp := -8 |}; {| Fnum := 330; Fexp := -8 |};
    {| Fnum := 328; Fexp := -8 |}; {| Fnum := 327; Fexp := -8 |};
    {| Fnum := 325; Fexp := -8 |}; {| Fnum := 324; Fexp := -8 |};
    {| Fnum := 322; Fexp := -8 |}; {| Fnum := 20; Fexp := -4 |};
    {| Fnum := 319; Fexp := -8 |}; {| Fnum := 317; Fexp := -8 |};
    {| Fnum := 316; Fexp := -8 |}; {| Fnum := 314; Fexp := -8 |};
    {| Fnum := 313; Fexp := -8 |}; {| Fnum := 311; Fexp := -8 |};
    {| Fnum := 310; Fexp := -8 |}; {| Fnum := 308; Fexp := -8 |};
    {| Fnum := 307; Fexp := -8 |}; {| Fnum := 306; Fexp := -8 |};
    {| Fnum := 19; Fexp := -4 |}; {| Fnum := 303; Fexp := -8 |};
    {| Fnum := 301; Fexp := -8 |}; {| Fnum := 300; Fexp := -8 |};
    {| Fnum := 299; Fexp := -8 |}; {| Fnum := 297; Fexp := -8 |};
    {| Fnum := 296; Fexp := -8 |}; {| Fnum := 295; Fexp := -8 |};
    {| Fnum := 293; Fexp := -8 |}; {| Fnum := 292; Fexp := -8 |};
    {| Fnum := 291; Fexp := -8 |}; {| Fnum := 289; Fexp := -8 |};
    {| Fnum := 18; Fexp := -4 |}; {| Fnum := 287; Fexp := -8 |};
    {| Fnum := 286; Fexp := -8 |}; {| Fnum := 284; Fexp := -8 |};
    {| Fnum := 283; Fexp := -8 |}; {| Fnum := 282; Fexp := -8 |};
    {| Fnum := 281; Fexp := -8 |}; {| Fnum := 279; Fexp := -8 |};
    {| Fnum := 278; Fexp := -8 |}; {| Fnum := 277; Fexp := -8 |};
    {| Fnum := 276; Fexp := -8 |}; {| Fnum := 275; Fexp := -8 |};
    {| Fnum := 274; Fexp := -8 |}; {| Fnum := 17; Fexp := -4 |};
    {| Fnum := 271; Fexp := -8 |}; {| Fnum := 270; Fexp := -8 |};
    {| Fnum := 269; Fexp := -8 |}; {| Fnum := 268; Fexp := -8 |};
    {| Fnum := 267; Fexp := -8 |}; {| Fnum := 266; Fexp := -8 |};
    {| Fnum := 265; Fexp := -8 |}; {| Fnum := 264; Fexp := -8 |};
    {| Fnum := 263; Fexp := -8 |}; {| Fnum := 262; Fexp := -8 |};
    {| Fnum := 261; Fexp := -8 |}; {| Fnum := 260; Fexp := -8 |};
    {| Fnum := 259; Fexp := -8 |}; {| Fnum := 258; Fexp := -8 |};
    {| Fnum := 256; Fexp := -8 |}; {| Fnum := 256; Fexp := -8 |};
    {| Fnum := 509; Fexp := -9 |}; {| Fnum := 507; Fexp := -9 |};
    {| Fnum := 505; Fexp := -9 |}; {| Fnum := 503; Fexp := -9 |};
    {| Fnum := 501; Fexp := -9 |}; {| Fnum := 499; Fexp := -9 |};
    {| Fnum := 497; Fexp := -9 |}; {| Fnum := 31; Fexp := -5 |};
    {| Fnum := 494; Fexp := -9 |}; {| Fnum := 492; Fexp := -9 |};
    {| Fnum := 490; Fexp := -9 |}; {| Fnum := 488; Fexp := -9 |};
    {| Fnum := 486; Fexp := -9 |}; {| Fnum := 485; Fexp := -9 |};
    {| Fnum := 483; Fexp := -9 |}; {| Fnum := 481; Fexp := -9 |};
    {| Fnum := 479; Fexp := -9 |}; {| Fnum := 477; Fexp := -9 |};
    {| Fnum := 476; Fexp := -9 |}; {| Fnum := 474; Fexp := -9 |};
    {| Fnum := 472; Fexp := -9 |}; {| Fnum := 471; Fexp := -9 |};
    {| Fnum := 469; Fexp := -9 |}; {| Fnum := 467; Fexp := -9 |};
    {| Fnum := 466; Fexp := -9 |}; {| Fnum := 29; Fexp := -5 |};
    {| Fnum := 462; Fexp := -9 |}; {| Fnum := 461; Fexp := -9 |};
    {| Fnum := 459; Fexp := -9 |}; {| Fnum := 457; Fexp := -9 |};
    {| Fnum := 456; Fexp := -9 |}; {| Fnum := 454; Fexp := -9 |};
    {| Fnum := 453; Fexp := -9 |}; {| Fnum := 451; Fexp := -9 |};
    {| Fnum := 450; Fexp := -9 |}; {| Fnum := 28; Fexp := -5 |};
    {| Fnum := 447; Fexp := -9 |}; {| Fnum := 445; Fexp := -9 |};
    {| Fnum := 444; Fexp := -9 |}; {| Fnum := 442; Fexp := -9 |};
    {| Fnum := 441; Fexp := -9 |}; {| Fnum := 439; Fexp := -9 |};
    {| Fnum := 438; Fexp := -9 |}; {| Fnum := 436; Fexp := -9 |};
    {| Fnum := 435; Fexp := -9 |}; {| Fnum := 433; Fexp := -9 |};
    {| Fnum := 27; Fexp := -5 |}; {| Fnum := 430; Fexp := -9 |};
    {| Fnum := 429; Fexp := -9 |}; {| Fnum := 428; Fexp := -9 |};
    {| Fnum := 426; Fexp := -9 |}; {| Fnum := 425; Fexp := -9 |};
    {| Fnum := 423; Fexp := -9 |}; {| Fnum := 422; Fexp := -9 |};
    {| Fnum := 421; Fexp := -9 |}; {| Fnum := 419; Fexp := -9 |};
    {| Fnum := 418; Fexp := -9 |}; {| Fnum := 417; Fexp := -9 |};
    {| Fnum := 415; Fexp := -9 |}; {| Fnum := 414; Fexp := -9 |};
    {| Fnum := 413; Fexp := -9 |}; {| Fnum := 412; Fexp := -9 |};
    {| Fnum := 410; Fexp := -9 |}; {| Fnum := 409; Fexp := -9 |};
    {| Fnum := 408; Fexp := -9 |}; {| Fnum := 406; Fexp := -9 |};
    {| Fnum := 405; Fexp := -9 |}; {| Fnum := 404; Fexp := -9 |};
    {| Fnum := 403; Fexp := -9 |}; {| Fnum := 401; Fexp := -9 |};
    {| Fnum := 25; Fexp := -5 |}; {| Fnum := 399; Fexp := -9 |};
    {| Fnum := 398; Fexp := -9 |}; {| Fnum := 397; Fexp := -9 |};
    {| Fnum := 395; Fexp := -9 |}; {| Fnum := 394; Fexp := -9 |};
    {| Fnum := 393; Fexp := -9 |}; {| Fnum := 392; Fexp := -9 |};
    {| Fnum := 391; Fexp := -9 |}; {| Fnum := 390; Fexp := -9 |};
    {| Fnum := 388; Fexp := -9 |}; {| Fnum := 387; Fexp := -9 |};
    {| Fnum := 386; Fexp := -9 |}; {| Fnum := 385; Fexp := -9 |};
    {| Fnum := 24; Fexp := -5 |}; {| Fnum := 383; Fexp := -9 |};
    {| Fnum := 382; Fexp := -9 |}; {| Fnum := 380; Fexp := -9 |};
    {| Fnum := 379; Fexp := -9 |}; {| Fnum := 378; Fexp := -9 |};
    {| Fnum := 377; Fexp := -9 |}; {| Fnum := 376; Fexp := -9 |};
    {| Fnum := 375; Fexp := -9 |}; {| Fnum := 374; Fexp := -9 |};
    {| Fnum := 373; Fexp := -9 |}; {| Fnum := 372; Fexp := -9 |};
    {| Fnum := 371; Fexp := -9 |}; {| Fnum := 370; Fexp := -9 |};
    {| Fnum := 369; Fexp := -9 |}; {| Fnum := 23; Fexp := -5 |};
    {| Fnum := 367; Fexp := -9 |}; {| Fnum := 366; Fexp := -9 |};
    {| Fnum := 365; Fexp := -9 |}; {| Fnum := 364; Fexp := -9 |};
    {| Fnum := 363; Fexp := -9 |}; {| Fnum := 362; Fexp := -9 |}].

Lemma map_FINVERSE : [seq F2R i | i <- FINVERSE] = INVERSE.
Proof.
rewrite /FINVERSE /INVERSE /F2R /= /Z.pow_pos //=.
repeat (congr cons); try lra.
Qed.

Lemma format_INVERSE x : x \in INVERSE -> format x.
Proof.
rewrite -map_FINVERSE.
do ! (rewrite in_cons => /orP[/eqP->|];
 first by apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _ => 
           /=; lia).
by [].
Qed.

(* This is lemma 3 *)

Local Notation ulp := (ulp beta fexp).

Lemma format_pos_le_ex_add_ulp f1 f2 :
  format f1 -> format f2 -> 0 < f1 <= f2 ->
  exists k, f2 = f1 + IZR k * ulp f1.
Proof.
move=> Hf1 Hf2 f1Lf2.
red in Hf1.
have cf1Lcf2 : (cexp f1 <= cexp f2)%Z.
  have [cf2Lcf1|//] := Z_lt_le_dec (cexp f2) (cexp f1).
  suff : f2 < f1 by lra.
  by apply: lt_cexp_pos cf2Lcf1; lra.
rewrite ulp_neq_0; last by lra.
rewrite {1}Hf1 {1}Hf2 /F2R /=
        -[(Generic_fmt.cexp radix2 fexp f2)]/(cexp f2)
        -[(Generic_fmt.cexp radix2 fexp f1)]/(cexp f1). 
set x1 := Ztrunc _; set x2 := Ztrunc _.
Search Z "pow".
exists (x1 * radix2 ^ (cexp f2 - cexp f1) - x2)%Z.
rewrite minus_IZR mult_IZR IZR_Zpower; last by lia.
rewrite Rmult_minus_distr_r Rmult_assoc -bpow_plus -[bpow _ _]/(pow _).
rewrite -[bpow _ (cexp f1)]/(pow _).
rewrite -[bpow _ (_ + _)]/(pow _).
have -> : (cexp f2 - cexp f1 + cexp f1 = cexp f2)%Z by lia.
by lra.
Qed.

Lemma imul_fexp_le (f : float) e : (e <= Fexp f)%Z -> is_imul f (pow e).
Proof.
case: f => mf ef /= eLef.
rewrite /F2R /=.
have ->: (ef = (ef - e) + e)%Z by lia.
rewrite bpow_plus.
exists (mf * (radix2 ^ (ef - e)))%Z.
rewrite mult_IZR IZR_Zpower; try lia.
by rewrite Rmult_assoc.
Qed.

Lemma imul_fexp_lt (f : float) e : 
  Z.even (Fnum f) -> (e - 1 <= Fexp f)%Z -> is_imul f (pow e).
Proof.
case: f => mf ef /= even_f eLef.
rewrite /F2R /=.
have ->: (ef = -1 + (ef - (e - 1) + e))%Z by lia.
rewrite 2!bpow_plus.
exists ((mf / 2) * (radix2 ^ (ef - (e - 1))))%Z.
rewrite mult_IZR IZR_Zpower; last by lia.
rewrite -!Rmult_assoc; congr (_ * _ * _).
have [hp ->] := Zeven_ex mf.
rewrite even_f Z.add_0_r Zmult_comm Z.div_mul //.
by rewrite mult_IZR /= /Z.pow_pos /=; lra.
Qed.

(* This proof should be reworked *)
Lemma imul_format z e b : 
  (emin <= e)%Z -> is_imul z (pow e) -> Rabs z <= b -> b <= (pow (p + e))
  -> format z.
Proof.
move=> emLe [k ->] zB bB.
have [E|D] := Req_dec (Rabs (IZR k * pow e)) b.
  have [E1|D1] := Req_dec b (pow (p + e)).
    rewrite E1 Rabs_mult bpow_plus [Rabs (pow _)]Rabs_pos_eq in E; last first.
      apply: bpow_ge_0.
    have: Rabs (IZR k) = pow p.
      have: 0 < pow e by apply: bpow_gt_0.
      by nra.
    clear zB E; split_Rabs.
      rewrite -[IZR _]Ropp_involutive H Ropp_mult_distr_l_reverse -bpow_plus.
      apply: generic_format_opp.
      apply: generic_format_bpow => //.
      by rewrite /fexp; lia.
    rewrite H -bpow_plus.
    apply: generic_format_bpow => //.
    by rewrite /fexp; lia.
  have ->: IZR k * pow e = F2R (Float radix2 k e) by rewrite /F2R /=.
  apply: generic_format_FLT.
  apply: FLT_spec (refl_equal _) _ _ => //=.
  have powe_gt_0 : 0 < pow e by apply: bpow_gt_0.
  rewrite Rabs_mult -abs_IZR Rabs_pos_eq in zB E; last by lra.
  apply/lt_IZR; rewrite IZR_Zpower_pos powerRZ_Rpower; last by lra.
  rewrite -(pow_Rpower _ 53) // -[bpow _ _]/(pow p).
  suff : IZR (Z.abs k) * pow e < pow (p + e) by rewrite bpow_plus; nra.
  by lra.  
have ->: IZR k * pow e = F2R (Float radix2 k e) by rewrite /F2R /=.
apply: generic_format_FLT.
apply: FLT_spec (refl_equal _) _ _ => //=.
have powe_gt_0 : 0 < pow e by apply: bpow_gt_0.
rewrite Rabs_mult -abs_IZR Rabs_pos_eq in zB D; last by lra.
apply/lt_IZR; rewrite IZR_Zpower_pos powerRZ_Rpower; last by lra.
rewrite -(pow_Rpower _ 53) // -[bpow _ _]/(pow p).
suff : IZR (Z.abs k) * pow e < pow (p + e) by rewrite bpow_plus; nra.
by lra.
Qed.

Lemma rt_float t : 
  format t -> / sqrt 2 <= t < sqrt 2 ->
  let i := Z.to_nat (Zfloor (pow 8 * t)) in 
  let r := nth 1 INVERSE (i - 181) in 
  let z := r * t - 1 in 
  [/\ format z, Rabs z <= 33 * pow (- 13) & is_imul z (pow (- 61))].
Proof.
move=> Ft tB i r z.
have t_gt0 : 0 < t by interval.
have pow8_gt0 : 0 < pow 8 by apply: bpow_gt_0.
have powN8_gt0 : 0 < pow (- 8) by apply: bpow_gt_0.
have pow8t_ge0 : (0 <= Zfloor (pow 8 * t))%Z.
  by rewrite -(Zfloor_IZR 0); apply: Zfloor_le; interval.
have iB : (181 <= i <= 362)%N.
  apply/andP; split; apply/leP/Nat2Z.inj_le.
    suff <- : Zfloor (/ sqrt 2 * pow 8 ) = Z.of_nat 181.
      by rewrite Z2Nat.id //; apply: Zfloor_le; nra.
    apply: Zfloor_imp; rewrite /= /Z.pow_pos /=.
    by split; interval.
  suff <- : Zfloor (sqrt 2 * pow 8 ) = Z.of_nat 362.
    by rewrite Z2Nat.id //; apply: Zfloor_le; nra.
  apply: Zfloor_imp; rewrite /= /Z.pow_pos /=.
  by split; interval.
pose ti := pow (- 8) * INR i; pose ti1 := pow (- 8) * INR i.+1. 
have ti_gt_0 : 0 < ti.
  apply: Rmult_lt_0_compat; try lra.
  apply/(lt_INR 0)/leP.
  apply: leq_trans (_ : 180 < _)%N => //.
  by case/andP: iB.
have tiB : ti <= t < ti1.
  rewrite /ti /ti1 !INR_IZR_INZ Nat2Z.inj_succ /Z.succ Z2Nat.id // plus_IZR.
  rewrite [X in _ <= X < _](_ : t = pow (-8) * (pow 8 * t)); last first.
    by rewrite -Rmult_assoc -bpow_plus Rsimp01.
  suff :  IZR (Zfloor (pow 8 * t)) <= (pow 8 * t) < 
              IZR (Zfloor (pow 8 * t)) + 1 by nra.
  split; first by apply: Zfloor_lb.
  by apply: Zfloor_ub.
have [iL255|iG256] := leqP i 255.
  have INRiB : 181 <= INR i <= 255.
    split.
      have->: 181 = INR 181 by rewrite /=; lra.
      by apply/le_INR/leP; case/andP: iB.
    have->: 255 = INR 255 by rewrite /=; lra.
    by apply/le_INR/leP.
  have Fti : format ti.
    have ZiB : (181 <= Z.of_nat i <= 255)%Z.
      split; first by apply/(Nat2Z.inj_le 181)/leP; case/andP: iB.
      by apply/(Nat2Z.inj_le _ 255)/leP.
    have -> : ti = (Float _ (Z.of_nat i * Z.pow_pos 2 45) (- 53) : float).
      by rewrite /ti /F2R /= /Z.pow_pos /= mult_IZR -INR_IZR_INZ; lra.
    apply: generic_format_FLT.
    apply: FLT_spec (refl_equal _) _ _ => /=; last by lia.
    by rewrite Z.abs_eq /Z.pow_pos /=; lia.
  have t_lt_1 : t < 1.
    apply: Rlt_le_trans (_ : ti1 <= _); first by lra.
    have -> : 1 = pow (- 8) * INR (255).+1 by rewrite /= /Z.pow_pos /=; lra.
    rewrite /ti1; suff : INR i.+1 <= INR 256 by nra.
    by apply/le_INR/leP.
  have ti1_le_1 : ti1 <= 1.
    suff : INR i.+1 <= 256.
      by rewrite /ti1 -[pow (-8)]/(/256); lra.
    have -> : 256 = INR 256 by rewrite /=; lra.
    by apply/(le_INR _ 256%N)/leP.
  pose ril := IZR (Zfloor (/ ti1 * pow 8)) * pow (- 8).
  pose riu := IZR (Zceil (/ ti * pow 8)) * pow (- 8).
  have riB : 1 <= ril < riu.
    split.
      rewrite /ril.
      have /IZR_le : (Zfloor (pow 8) <= Zfloor (/ ti1 * pow 8))%Z.
        apply: Zfloor_le.
        suff : / 1 <= / ti1 by nra.
        by apply: Rinv_le; lra.
      have -> : Zfloor (pow 8) = 256%Z.
        by apply: Zfloor_imp; rewrite /= /Z.pow_pos /=; lra.
      by rewrite -[pow (- 8)]/(/256); lra.
    rewrite /ril /riu.
    suff : IZR (Zfloor (/ ti1 * pow 8)) < IZR (Zceil (/ ti * pow 8)) by nra.
    have [Hf|Hnf] := Req_dec (IZR (Zfloor (/ ti * pow 8))) (/ ti * pow 8).
      rewrite - Hf Zceil_IZR Hf.
      apply: Rle_lt_trans (Zfloor_lb _) _.
      suff : /ti1 < /ti by nra.
      by apply: Rinv_lt; lra.
    rewrite (Zceil_floor_neq _ Hnf).
    rewrite plus_IZR.
    suff: IZR (Zfloor (/ ti1 * pow 8)) <= IZR (Zfloor (/ ti * pow 8)) by lra.
    apply/IZR_le/Zfloor_le.
    suff : /ti1 < /ti by nra.
    by apply: Rinv_lt; lra.
  pose kil := (Zfloor (/ ti1 * pow 8) - 256)%Z.
  have rilE : ril = 1 + IZR kil * pow (- 8).
    by rewrite /ril /kil minus_IZR -[pow (- 8)]/(/256); lra.
  pose kiu := (Zceil (/ ti * pow 8) - 256)%Z.
  have riuE : riu = 1 + IZR kiu * pow (- 8).
    by rewrite /riu /kiu minus_IZR -[pow (- 8)]/(/256); lra.
  have kiuBkilB : (1 <= kiu - kil <= 3)%Z.
    split.
      suff: (kil < kiu)%Z by lia.
      by apply/lt_IZR; nra.
    suff: (kiu - kil < 4)%Z by lia.
      apply/lt_IZR; rewrite minus_IZR.
    apply: Rle_lt_trans 
       (_ : pow 8 * pow 8 / (INR i * INR (i.+1)) + 2 < _); last first.
      by rewrite S_INR; interval.
    have -> : IZR kiu - IZR kil = 
          IZR (Zceil (/ ti * pow 8)) -IZR (Zfloor (/ ti1 * pow 8)).
      by rewrite /kiu /kil !minus_IZR; lra.
    apply: Rle_trans
       (_ : (/ ti * pow 8) - IZR (Zfloor (/ ti1 * pow 8)) + 1 <= _).
      have := Zceil_lb ((/ ti * pow 8)); lra.
    apply: Rle_trans
       (_ : (/ ti * pow 8) - (/ ti1 * pow 8) + 2 <= _).
      by have := Zfloor_ub ((/ ti1 * pow 8)); lra.
    suff : / ti - / ti1 <= pow 8 / (INR i * INR i.+1) by nra.
    rewrite /ti /ti1 S_INR -[pow (-8)]/(/256) -[pow 8]/256.
    right.
    by field; split; lra.
  have [j tE] : exists j, t = ti + IZR j * ulp ti.
    by apply: format_pos_le_ex_add_ulp => //; last by lra.
  have ulp_ti : ulp ti = pow (-53).
    rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (- 53 + p)%Z); try lra.
      rewrite Z.max_l; last by lia.
      congr bpow; lia.
    rewrite /ti !pow_Rpower /p //.
    by split; interval.
  rewrite ulp_ti in tE.
  pose jmax := (radix2 ^ 45 - 1)%Z.
  have jB : (0 <= j <= jmax)%Z.
    suff : (0 <= j < radix2 ^ 45)%Z by lia.
    split.
      apply/le_IZR.
      suff : 0 < pow (- 53) by nra.
      by apply: bpow_gt_0.
    apply/lt_IZR.
    rewrite IZR_Zpower //= /Z.pow_pos /=.
    have ti1E : ti1 = ti + pow (- 8) by rewrite /ti /ti1 S_INR; lra.
    have : t - ti < ti1 - ti by lra.
    rewrite tE ti1E /jmax /= /Z.pow_pos /=.
    by lra.
  have rjB : 0 <= IZR j <= IZR jmax.
    by split; apply: IZR_le; lia.
  have imul_r : is_imul r (pow (-8)).
    pose fr := nth (Float _ 0 0) FINVERSE (i - 181).
    have <- : F2R fr = r.
      rewrite /fr /r -map_FINVERSE (nth_map (Float _ 0 0)) //=.
      by rewrite ltn_subLR; case/andP: iB.
    apply: imul_fexp_le.
    have -> : fr = nth (Float _ 0 0) (take 75 FINVERSE) (i - 181).
      by rewrite nth_take // ltn_subLR //; case/andP: iB.
    case/andP: iB iL255.
    do 75 rewrite leq_eqVlt=> /orP[/eqP<-//|].
    by rewrite ltnNge; case (i <= 255)%N.
  have imul_z : is_imul z (pow (-61)).
    apply: is_imul_minus; last first.
      exists (radix2 ^ 61)%Z.
      by rewrite IZR_Zpower // -bpow_plus -(pow0E radix2); congr bpow; lia.
    rewrite -[(-61)%Z]/(-8 + - 53)%Z bpow_plus tE.
    apply: is_imul_mul => //.
    apply: is_imul_add; last by exists j.
    exists (Z.of_nat i * radix2 ^ (- 8 + 53))%Z.
    rewrite /ti mult_IZR IZR_Zpower // -INR_IZR_INZ.
    by rewrite Rmult_comm Rmult_assoc -bpow_plus.
  have F : Rabs z <= Rmax (Rabs (r * ti - 1))
                          (Rabs (r * (ti + IZR jmax * pow (- 53)) - 1)).
    apply/Rmax_Rle.
    have M a b c d : a <= b <= c -> Rabs (d * b - 1) <= Rabs (d * a - 1) \/ 
                                    Rabs (d * b - 1) <= Rabs (d * c - 1).
      move=> Ha.
      have [r_pos|r_neg] := Rle_lt_dec 0 d.
        have F : d * a <= d * b <= d * c by nra.
        by split_Rabs; lra.
      have F : d * c <= d * b <= d * a by nra.
      by split_Rabs; lra.
    apply: M.
    have: 0 <= pow (-53) by apply: bpow_ge_0.
    by nra.
  have [i187|/eqP iD187] := (i =P 187%N).
    have imul_r1 : is_imul r (pow (-7)).
      pose fr := nth (Float _ 0 0) FINVERSE (i - 181).
      have <- : F2R fr = r.
        rewrite /fr /r -map_FINVERSE (nth_map (Float _ 0 0)) //=.
        by rewrite ltn_subLR; case/andP: iB.
      rewrite /fr i187 [nth _ _ _ ]/=.
      by apply: imul_fexp_lt.
    have imul_z1 : is_imul z (pow (-60)).
      apply: is_imul_minus; last first.
        exists (radix2 ^ 60)%Z.
        by rewrite IZR_Zpower // -bpow_plus -(pow0E radix2); congr bpow; lia.
      rewrite -[(-60)%Z]/(-7 + - 53)%Z bpow_plus tE.
      apply: is_imul_mul => //.
      apply: is_imul_add; last by exists j.
      exists (Z.of_nat i * radix2 ^ (- 8 + 53))%Z.
      rewrite /ti mult_IZR IZR_Zpower // -INR_IZR_INZ.
      by rewrite Rmult_comm Rmult_assoc -bpow_plus.
    split => //.
      suff zB : Rabs z <= pow (-7).
        by apply: imul_format imul_z1 zB _ => //=; lra.
      apply: Rle_trans F _.
      rewrite /jmax [IZR (_ ^ _ - 1)]/= /ti /r i187.
      rewrite [nth _ _ _]/= INR_IZR_INZ [Z.of_nat _]/=.
      by apply: Rmax_lub; interval with (i_prec 100).
    apply: Rle_trans F _.
    rewrite /jmax [IZR (_ ^ _ - 1)]/= /ti /r i187.
    rewrite [nth _ _ _]/= INR_IZR_INZ [Z.of_nat _]/=.
    by apply: Rmax_lub; interval with (i_prec 100).
  have [i196|/eqP iD196] := (i =P 196%N).
    have imul_r1 : is_imul r (pow (-7)).
      pose fr := nth (Float _ 0 0) FINVERSE (i - 181).
      have <- : F2R fr = r.
        rewrite /fr /r -map_FINVERSE (nth_map (Float _ 0 0)) //=.
        by rewrite ltn_subLR; case/andP: iB.
      rewrite /fr i196 [nth _ _ _ ]/=.
      by apply: imul_fexp_lt.
    have imul_z1 : is_imul z (pow (-60)).
      apply: is_imul_minus; last first.
        exists (radix2 ^ 60)%Z.
        by rewrite IZR_Zpower // -bpow_plus -(pow0E radix2); congr bpow; lia.
      rewrite -[(-60)%Z]/(-7 + - 53)%Z bpow_plus tE.
      apply: is_imul_mul => //.
      apply: is_imul_add; last by exists j.
      exists (Z.of_nat i * radix2 ^ (- 8 + 53))%Z.
      rewrite /ti mult_IZR IZR_Zpower // -INR_IZR_INZ.
      by rewrite Rmult_comm Rmult_assoc -bpow_plus.
    split => //.
      suff zB : Rabs z <= pow (-7).
        by apply: imul_format imul_z1 zB _ => //=; lra.
      apply: Rle_trans F _.
      rewrite /jmax [IZR (_ ^ _ - 1)]/= /ti /r i196.
      rewrite [nth _ _ _]/= INR_IZR_INZ [Z.of_nat _]/=.
      by apply: Rmax_lub; interval with (i_prec 100).
    apply: Rle_trans F _.
    rewrite /jmax [IZR (_ ^ _ - 1)]/= /ti /r i196.
    rewrite [nth _ _ _]/= INR_IZR_INZ [Z.of_nat _]/=.
    by apply: Rmax_lub; interval with (i_prec 100).
  have [i199|/eqP iD199] := (i =P 199%N).
    have imul_r1 : is_imul r (pow (-7)).
      pose fr := nth (Float _ 0 0) FINVERSE (i - 181).
      have <- : F2R fr = r.
        rewrite /fr /r -map_FINVERSE (nth_map (Float _ 0 0)) //=.
        by rewrite ltn_subLR; case/andP: iB.
      rewrite /fr i199 [nth _ _ _ ]/=.
      by apply: imul_fexp_lt.
    have imul_z1 : is_imul z (pow (-60)).
      apply: is_imul_minus; last first.
        exists (radix2 ^ 60)%Z.
        by rewrite IZR_Zpower // -bpow_plus -(pow0E radix2); congr bpow; lia.
      rewrite -[(-60)%Z]/(-7 + - 53)%Z bpow_plus tE.
      apply: is_imul_mul => //.
      apply: is_imul_add; last by exists j.
      exists (Z.of_nat i * radix2 ^ (- 8 + 53))%Z.
      rewrite /ti mult_IZR IZR_Zpower // -INR_IZR_INZ.
      by rewrite Rmult_comm Rmult_assoc -bpow_plus.
    split => //.
      suff zB : Rabs z <= pow (-7).
        by apply: imul_format imul_z1 zB _ => //=; lra.
      apply: Rle_trans F _.
      rewrite /jmax [IZR (_ ^ _ - 1)]/= /ti /r i199.
      rewrite [nth _ _ _]/= INR_IZR_INZ [Z.of_nat _]/=.
      by apply: Rmax_lub; interval with (i_prec 100).
    apply: Rle_trans F _.
    rewrite /jmax [IZR (_ ^ _ - 1)]/= /ti /r i199.
    rewrite [nth _ _ _]/= INR_IZR_INZ [Z.of_nat _]/=.
    by apply: Rmax_lub; interval with (i_prec 100).
  suff zB : Rabs z <= pow (-8).
    split => //.
      by apply: imul_format imul_z zB _ => //=; lra.
    by apply: Rle_trans zB _; interval.
  apply: Rle_trans F _.
  rewrite /jmax [IZR (_ ^ _ - 1)]/= /ti /r.
  case/andP: iB iL255 iD187 iD196 iD199.
  do 75 (rewrite leq_eqVlt=> /orP[/eqP<-//|];
    try by rewrite [nth _ _ _]/= INR_IZR_INZ [Z.of_nat _]/=;
           move=> *; apply: Rmax_lub; interval with (i_prec 100)).
  by rewrite ltnNge; case: (i <= 255)%N.
have pow9_gt_0 : 0 < pow 9 by apply: bpow_gt_0.
have powN9_gt_0 : 0 < pow (- 9) by apply: bpow_gt_0.
have INRiB : 256 <= INR i <= 362.
  split.
    have->: 256 = INR 256 by rewrite /=; lra.
    by apply/le_INR/leP; case/andP: iB.
  have->: 362 = INR 362 by rewrite /=; lra.
  by apply/le_INR/leP; case/andP: iB.
have Fti : format ti.
  have ZiB : (256 <= Z.of_nat i <= 362)%Z.
    split; first by apply/(Nat2Z.inj_le 256)/leP; case/andP: iB.
    by apply/(Nat2Z.inj_le _ 362)/leP; case/andP: iB.
  have -> : ti = (Float _ (Z.of_nat i * Z.pow_pos 2 44) (- 52) : float).
    by rewrite /ti /F2R /= /Z.pow_pos /= mult_IZR -INR_IZR_INZ; lra.
  apply: generic_format_FLT.
  apply: FLT_spec (refl_equal _) _ _ => /=; last by lia.
  by rewrite Z.abs_eq /Z.pow_pos /=; lia.
  have t_ge_1 : 1 <= t.
    apply: Rle_trans (_ : ti <= _); last by lra.
    have -> : 1 = pow (- 8) * INR (256) by rewrite /= /Z.pow_pos /=; lra.
    rewrite /ti; suff : INR 256 <= INR i by nra.
  by apply/le_INR/leP.
have ti_ge_1 : 1 <= ti.
  have -> : 1 = pow (- 8) * INR (255).+1 by rewrite /= /Z.pow_pos /=; lra.
  rewrite /ti; suff : INR 256 <= INR i by nra.
  by apply/le_INR/leP.
pose ril := IZR (Zfloor (/ ti1 * pow 9)) * pow (- 9).
pose riu := IZR (Zceil (/ ti * pow 9)) * pow (- 9).
have riB : ril < riu <= 1.
  split.
    rewrite /ril /riu.
    suff : IZR (Zfloor (/ ti1 * pow 9)) < IZR (Zceil (/ ti * pow 9)) by nra.
    have [Hf|Hnf] := Req_dec (IZR (Zfloor (/ ti * pow 9))) (/ ti * pow 9).
      rewrite - Hf Zceil_IZR Hf.
      apply: Rle_lt_trans (Zfloor_lb _) _.
      suff : /ti1 < /ti by nra.
      by apply: Rinv_lt; lra.
    rewrite (Zceil_floor_neq _ Hnf).
    rewrite plus_IZR.
    suff: IZR (Zfloor (/ ti1 * pow 9)) <= IZR (Zfloor (/ ti * pow 9)) by lra.
    apply/IZR_le/Zfloor_le.
    suff : /ti1 < /ti by nra.
    by apply: Rinv_lt; lra.
  rewrite /riu.
  have /IZR_le : (Zceil (/ ti * pow 9) <= Zceil (pow 9))%Z.
    apply: Zceil_le.
    suff : / ti <= / 1 by nra.
    by apply: Rinv_le; lra.
  have -> : Zceil (pow 9) = 512%Z.
    by apply: Zceil_imp; rewrite /= /Z.pow_pos /=; lra.
  by rewrite -[pow (- 9)]/(/512); lra.
pose kil := (512 - Zfloor (/ ti1 * pow 9))%Z.
have rilE : ril = 1 - IZR kil * pow (- 9).
  by rewrite /ril /kil minus_IZR -[pow (- 9)]/(/512); lra.
pose kiu := (512 - Zceil (/ ti * pow 9))%Z.
have riuE : riu = 1 - IZR kiu * pow (- 9).
  by rewrite /riu /kiu minus_IZR -[pow (- 9)]/(/512); lra.
have kiuBkilB : (1 <= kil - kiu <= 3)%Z.
  split.
    suff: (kiu < kil)%Z by lia.
    by apply/lt_IZR; nra.
  suff: (kil - kiu < 4)%Z by lia.
  apply/lt_IZR; rewrite minus_IZR.
  apply: Rle_lt_trans 
      (_ : pow 8 * pow 9 / (INR i * INR (i.+1)) + 2 < _); last first.
    by rewrite S_INR; interval.
  have -> : IZR kil - IZR kiu = 
            IZR (Zceil (/ ti * pow 9)) - IZR (Zfloor (/ ti1 * pow 9)).
  rewrite /kiu /kil ![IZR (512 - _)]minus_IZR; lra.
    apply: Rle_trans
       (_ : (/ ti * pow 9) - IZR (Zfloor (/ ti1 * pow 9)) + 1 <= _).
    by have := Zceil_lb ((/ ti * pow 9)); lra.
  apply: Rle_trans
    (_ : (/ ti * pow 9) - (/ ti1 * pow 9) + 2 <= _).
    by have := Zfloor_ub ((/ ti1 * pow 9)); lra.
  suff : / ti - / ti1 <= pow 8 / (INR i * INR i.+1) by nra.
  rewrite /ti /ti1 S_INR -[pow (-8)]/(/256) -[pow 8]/256.
  right.
  by field; split; lra.
have [j tE] : exists j, t = ti + IZR j * ulp ti.
  by apply: format_pos_le_ex_add_ulp => //; last by lra.
have ulp_ti : ulp ti = pow (- 52).
  rewrite ulp_neq_0 /cexp /fexp  ?(mag_unique_pos _ _ (- 52 + p)%Z); try lra.
    rewrite Z.max_l; last by lia.
    by congr bpow; lia.
  rewrite /ti /= /Z.pow_pos /=.
  by lra.
rewrite ulp_ti in tE.
pose jmax := (radix2 ^ 44 - 1)%Z.
have jB : (0 <= j <= jmax)%Z.
  suff : (0 <= j < radix2 ^ 44)%Z by lia.
  split.
    apply/le_IZR.
    suff : 0 < pow (- 52) by nra.
    by apply: bpow_gt_0.
  apply/lt_IZR.
  rewrite IZR_Zpower //= /Z.pow_pos /=.
  have ti1E : ti1 = ti + pow (- 8) by rewrite /ti /ti1 S_INR; lra.
  have : t - ti < ti1 - ti by lra.
  rewrite tE ti1E /jmax /= /Z.pow_pos /=.
  by lra.
have rjB : 0 <= IZR j <= IZR jmax.
  by split; apply: IZR_le; lia.
have imul_r : is_imul r (pow (- 9)).
  pose fr := nth (Float _ 0 0) FINVERSE (i - 181).
  have <- : F2R fr = r.
    rewrite /fr /r -map_FINVERSE (nth_map (Float _ 0 0)) //=.
    by rewrite ltn_subLR; case/andP: iB.
  apply: imul_fexp_le.
  rewrite /fr.
  case/andP: iB; move: iG256.
  do 107 rewrite leq_eqVlt=> /orP[/eqP<-//|].
  by rewrite ltnNge; case (i <= 362)%N.
have imul_z : is_imul z (pow (-61)).
  apply: is_imul_minus; last first.
    exists (radix2 ^ 61)%Z.
    by rewrite IZR_Zpower // -bpow_plus -(pow0E radix2); congr bpow; lia.
  rewrite -[(-61)%Z]/(-9 + - 52)%Z bpow_plus tE.
  apply: is_imul_mul => //.
  apply: is_imul_add; last by exists j.
  exists (Z.of_nat i * radix2 ^ (- 9 + 53))%Z.
  rewrite /ti mult_IZR IZR_Zpower // -INR_IZR_INZ.
  by rewrite Rmult_comm Rmult_assoc -bpow_plus.
have F : Rabs z <= Rmax (Rabs (r * ti - 1))
                        (Rabs (r * (ti + IZR jmax * pow (- 52)) - 1)).
  apply/Rmax_Rle.
  have M a b c d : a <= b <= c -> Rabs (d * b - 1) <= Rabs (d * a - 1) \/ 
                                  Rabs (d * b - 1) <= Rabs (d * c - 1).
    move=> Ha.
    have [r_pos|r_neg] := Rle_lt_dec 0 d.
      have F : d * a <= d * b <= d * c by nra.
      by split_Rabs; lra.
    have F : d * c <= d * b <= d * a by nra.
    by split_Rabs; lra.
  apply: M.
  have: 0 <= pow (-52) by apply: bpow_ge_0.
  by nra.
suff zB : Rabs z <= pow (-8).
  split => //.
    by apply: imul_format imul_z zB _ => //=; lra.
  by apply: Rle_trans zB _; interval.
apply: Rle_trans F _.
rewrite /jmax [IZR (_ ^ _ - 1)]/= /ti /r.
case/andP: iB; move: iG256.
do 107 (rewrite leq_eqVlt=> /orP[/eqP<-//|];
  try by rewrite [nth _ _ _]/= INR_IZR_INZ [Z.of_nat _]/=;
         move=> *; apply: Rmax_lub; interval with (i_prec 100)).
by rewrite ltnNge; case: (i <= 362)%N.
Qed.

Lemma rt_inverse i : 
  (i < size INVERSE)%N ->  
  let r := nth 1 INVERSE i in r <> 1 -> 0.00587 < Rabs (ln r) < 0.347.
Proof.
rewrite [size _]/=.
do 74 (case: i => [_ r|i]; first by rewrite /r [nth _ _ _]/=; split; interval).
do 2 (case: i => [_ r|i]; first by rewrite /r [nth _ _ _]/=; case; lra).
do 106 (case: i => [_ r|i]; first by rewrite /r [nth _ _ _]/=; split; interval).
by [].
Qed.

Lemma ZnearestE_IZR z : ZnearestE (IZR z) = z.
Proof.
by case: (Znearest_DN_or_UP (fun x => ~~ Z.even x) (IZR z)); 
   rewrite ?(Zfloor_IZR, Zceil_IZR) => ->.
Qed.

Lemma l1_bound  i : 
  (i < size INVERSE)%N ->  
  let r := nth 1 INVERSE i in
  let l1 := IZR (ZnearestE ((- ln r) *  pow 42)) * pow (- 42) in
  [/\ is_imul l1 (pow (- 42)), 
      l1 <> 0 -> pow (-8) < Rabs l1 < pow (-1),
      format l1 &
      l1 <> - ln r -> pow (- 52) < Rabs (l1 - (- ln r)) < pow (- 43)].
Proof.
move=> Hs r l1.
have imul_l1 : is_imul l1 (pow (- 42)).
  by exists (ZnearestE (- ln r * pow 42)).
have l1_B : l1 <> 0 -> pow (-8) < Rabs l1 < pow (-1).
  move=> l1_neq0.
  have [r_eq1|r_neq1] := Req_dec r 1.
    by case: l1_neq0; rewrite /l1 r_eq1 ln_1 !Rsimp01 ZnearestE_IZR Rsimp01.
  rewrite /l1 -/r; set v := - ln r.
  have : (0.00587 < v < 0.347) \/ (- 0.347 < v < - 0.00587).
    have := rt_inverse Hs r_neq1.
    by rewrite -/r /v; split_Rabs; lra.
  by case; split; interval.
have Fl1 : format l1.
  have [->|l1_neq0] := Req_dec l1 0; first by apply: generic_format_0.
  apply: imul_format imul_l1 (_ : _ <= pow (- 1)) _ => //; first by lra.
  by apply: bpow_le.
split => //; move: Hs.
rewrite [size _]/= /l1 {l1 imul_l1 l1_B Fl1}/r.
do 74 (case: i => [_ |i]; first by rewrite [nth _ _ _]/=;
                                     split; interval with (i_prec 100)).
do 2 (case: i => [_|i]; first by 
   rewrite [nth _ _ _]/=; case; (have -> : 0x1.00%xR = 1 by lra);
   rewrite !(ln_1, ZnearestE_IZR, Rsimp01)).
do 106 (case: i => [_ |i]; first by rewrite [nth _ _ _]/=;
                                     split; interval with (i_prec 100)).
by [].
Qed.

Lemma ulp_FLT_FLX (x : R) :
  bpow beta (emin + p - 1) <= Rabs x ->
  Ulp.ulp beta (FLT_exp emin p) x =
  Ulp.ulp beta (FLX_exp p) x.
Proof.
move=> x_ge.
rewrite -[LHS]ulp_abs -[RHS]ulp_abs.
have x_gt_0 : 0 < Rabs x.
  by apply: Rlt_le_trans x_ge; apply: bpow_gt_0.
rewrite !ulp_neq_0; try by lra.
by rewrite cexp_FLT_FLX // Rabs_Rabsolu.
Qed.

Lemma err7_bound i (choice : Z -> bool) : 
  (i < size INVERSE)%N ->  
  let r := nth 1 INVERSE i in
  let l1 := IZR (ZnearestE ((- ln r) *  pow 42)) * pow (- 42) in
  let l2 := round beta fexp (Znearest choice) ((- ln r) - l1) in
  let err7 := Rabs (l1 + l2 - (- ln r)) in err7 <= pow (- 97).
Proof.
move=> iLs r l1 l2 err7.
have -> : err7 = Rabs (l2 - (- ln r - l1)).
  by rewrite /err7; split_Rabs; lra.
apply: Rle_trans  (_ : /2 * ulp (- ln r - l1) <= _).
  by apply: error_le_half_ulp.
suff: ulp (- ln r - l1) <= pow (- 96) by rewrite /= /Z.pow_pos /=; lra.
rewrite -ulp_abs.
have [->|l1_neqlr] := Req_dec l1  (- ln r).
  have -> : - ln r - - ln r = 0 by lra.
  by rewrite Rsimp01 ulp_FLT_0 /= /Z.pow_pos /=; lra.
have F1 : pow (- 52) < Rabs (l1 - (- ln r)) < pow (- 43).
  by case: (l1_bound iLs) => // _ _ _; apply.
rewrite ulp_neq_0; last by split_Rabs; lra.
apply: bpow_le.
have <- : (fexp (- 43) = - 96)%Z by [].
by apply: cexp_le_bpow; split_Rabs; lra.
Qed.

End Exp.

