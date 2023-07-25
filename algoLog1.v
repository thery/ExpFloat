Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore algoP1.

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

End Exp.

