(* Formalisation of the F2Sum part of "On the robustness of the @Sum andt Fast2Sum algo" *)

(* Copyright (c)  Inria. All rights reserved. *)
Require Import Reals  Psatz.
From Flocq Require Import Core Plus_error Mult_error Relative Sterbenz Operations.
From Flocq Require Import  Round.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rmore.

Set Implicit Arguments.

Section Main.
Definition  beta:= radix2.
Variable emin p : Z.
Hypothesis precisionNotZero : (1 < p)%Z.
Context { prec_gt_0_ : Prec_gt_0 p}.


Notation format := (generic_format beta (FLT_exp emin p)).
Notation pow e := (bpow beta e).


Local Notation fexp := (FLT_exp emin p).
Local Notation ce := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Open Scope Z_scope.

Theorem cexp_bpow_flt  x e (xne0: x <> R0) 
                 (emin_le : emin <= Z.min (mag beta x + e - p) (mag beta x - p)):
       ce (x * pow e) = (ce x) + e.
Proof. 
by rewrite /cexp mag_mult_bpow // /fexp; lia.
Qed.

Theorem mant_bpow_flt x e (emin_le: emin <= Z.min (mag beta x + e - p) (mag beta x - p)):
     mant (x * pow e) = mant x.
Proof.
case: (Req_dec x 0) => [->|Zx]; first by rewrite Rmult_0_l.
rewrite /scaled_mantissa cexp_bpow_flt // Rmult_assoc.
by congr Rmult; rewrite -bpow_plus; congr bpow; lia.
Qed.

Theorem FLT_mant_le  x (Fx: format x): Z.abs (Ztrunc (mant x)) <= beta^p - 1.
Proof.
suff :  (Z.abs (Ztrunc (mant x)) < beta ^ p)%Z by lia .
apply: lt_IZR; rewrite abs_IZR - scaled_mantissa_generic // IZR_Zpower; last lia.
apply:(Rlt_le_trans _ ( bpow beta (mag beta x - cexp beta fexp x))%R).
  exact : scaled_mantissa_lt_bpow.
by apply:bpow_le;rewrite /cexp /fexp; lia.
Qed.

Lemma cexp_le (x y: R)  (xne0 : x <> 0%R) : (Rabs x <= Rabs y)%R -> (ce x <= ce y)%Z.
Proof.
by move=> xycmp;apply/FLT_exp_monotone/mag_le_abs.
Qed.

Local Open Scope R_scope.

Theorem Hauser a b (Fa : format a)(Fb: format b) :
  Rabs  (a + b) <= pow (emin + p  )%Z-> format (a + b).
Proof.
move=> s_ub.
move:(Fa) (Fb); rewrite {1 2} /generic_format /F2R /=.
set ma := Ztrunc _.
set Ma:= IZR _.
set mb := Ztrunc _.
set Mb := IZR _.
pose ea :=  ((cexp beta fexp a) +p -1)%Z.
have ->: ((cexp beta  fexp a) = ea -p +1)%Z by lia.
pose eb :=  ((cexp beta fexp b) +p -1)%Z.
have ->: ((cexp beta fexp b) = eb -p +1)%Z by lia.
have ea_ge_Emin: (emin + p - 1 <= ea)%Z.
  by rewrite /ea /cexp /fexp; apply(Z.le_trans _ (emin + p -1)); lia. 
have eb_ge_Emin: (emin + p - 1 <= eb)%Z.
  by rewrite /eb /cexp /fexp; apply(Z.le_trans _ (emin + p -1)); lia.
have ->: (ea -p +1 = (ea - (emin+p -1)) + (emin ))%Z by ring.
rewrite bpow_plus -Rmult_assoc => aE.
have ->: (eb -p +1 = (eb - (emin+p -1)) + (emin ))%Z by ring.
rewrite bpow_plus -Rmult_assoc  => bE.
have : Rabs (a +b) = 
       Rabs (Ma * (pow (ea - (emin + p -1))) + Mb * (pow (eb - (emin + p -1) )))* pow (emin).
  rewrite aE bE  -Rmult_plus_distr_r Rabs_mult (Rabs_pos_eq (pow _)) //.
  by apply/bpow_ge_0.
move=> sE.
move : s_ub; rewrite sE.
rewrite (Zplus_comm emin p) (bpow_plus _  p).
 move/Rmult_le_reg_r.
move /(_ (bpow_gt_0 _ _)).
have  <-: (emin + p - 1 = (p + emin - 1))%Z by lia.
set K := Rabs _.
move=>Kp; apply/generic_format_abs_inv.
rewrite sE -/K.
pose k := Z.abs (ma*beta^(ea- (emin + p -1)) + mb * beta^(eb -(emin +p -1)))%Z.
have KE: K = IZR  k.
  rewrite /k abs_IZR plus_IZR !mult_IZR !(IZR_Zpower beta)//; lia.
case: Kp => Kp.
  pose f := Float beta k emin.
  have fE : K * pow emin = F2R f by rewrite KE /F2R.
  apply/generic_format_FLT.
  apply/(FLT_spec _ _ _ _ (Float beta k
 emin)); rewrite /F2R//=; last lia.
move:Kp.
rewrite KE -(IZR_Zpower beta); last lia.
move/lt_IZR.
by rewrite /k Z.abs_involutive.
rewrite Kp  -bpow_plus.
apply/generic_format_FLT_bpow.
lia.
Qed.


Section F2Sum.
Local Open Scope R_scope.
Section Pre.

Variable rnd : R-> Z.
Hypothesis valid_rnd: Valid_rnd rnd.
Local Notation rnd_p := (round beta fexp rnd).

Variables a b   : R.
Hypothesis Fa : format a.
Hypothesis Fb : format b.

Notation  s := (rnd_p (a + b)).
Notation  z := (rnd_p (s - a)).
Notation t := (rnd_p (b - z)).

(* Lemma 2.4 of "robustness 2sum and f2sum" *)
Lemma sma_exact_aux: (ce s  <=  Z.min (ce a) (ce b))%Z -> (s = a + b)%R.
Proof.
case: (Req_dec s 0).
  by move/round_plus_eq_0 -> =>//; rewrite round_0.
move=> sn0 sminab.
case : (Req_dec (a + b) 0)=>[->|abn0]; first by rewrite round_0.
have abminab: (ce (a + b) <= Z.min (ce a) (ce b))%Z.
  apply/(Z.le_trans _ (ce s))=>//.
  by apply/cexp_round_ge; lra.
pose cas := (ce a - ce (a + b))%Z.
pose cbs := (ce b - ce (a + b))%Z.
move:Fa Fb.
rewrite /generic_format /F2R /=.
set Ma:= Ztrunc _  => aE.
set Mb := Ztrunc _ => bE.
pose  ceab := ce (a+b).
have aE' : a = (IZR (Ma * beta ^ cas)) * (pow ceab).
  rewrite mult_IZR IZR_Zpower; last lia.
  by rewrite Rmult_assoc -bpow_plus /cas  -/ceab;ring_simplify (ce a - ceab  + ceab)%Z.
have bE' : b = (IZR (Mb * beta ^ cbs)) * (pow ceab).
  rewrite mult_IZR IZR_Zpower ; last lia.
  by rewrite Rmult_assoc -bpow_plus /cbs /ceab ; ring_simplify (ce b - ce (a+b) + ce (a+b))%Z.
(* pose f := Float beta ((Ma * beta ^ cas) + (Mb * beta ^ cbs))%Z (ceab). *)
(* rewrite round_generic //. *)
(* apply/(generic_format_F2R' beta fexp _ f). *)
(*   rewrite /f /F2R/=. *)
(*   rewrite [in RHS] aE' [in RHS] bE' plus_IZR /beta /=; lra. *)
(* by move=>_; rewrite /f /F2R/= ; lia. *)

case: (generic_format_EM beta fexp  (a+b))=> FEM.
  by rewrite round_generic.
have :  round beta fexp Zfloor (a + b)  < a + b < round beta fexp Zceil (a + b).
  by apply /round_DN_UP_lt.
rewrite {1 2}/round /F2R /=.
pose Mab := ((Ma * beta ^ cas) + (Mb * beta ^ cbs))%Z.
have {3 4}->: a+b= (IZR Mab) * pow (ce (a+b)) by rewrite /Mab plus_IZR -/ceab; lra.
move=> h0.
have[/lt_IZR h1 /lt_IZR h2]:
    IZR (Zfloor (mant (a + b))) < IZR Mab < IZR (Zceil (mant (a + b))) 
  by move: (bpow_gt_0 beta (ce (a + b))); nra.
rewrite Zceil_floor_neq in h2.
  lia.
move=>h;apply/FEM.
suff->: a+b = round beta fexp Zfloor (a + b).
  by apply/generic_format_round.
rewrite /round /F2R /= h.
rewrite /scaled_mantissa Rmult_assoc -bpow_plus Z.add_opp_diag_l /=; ring.
Qed.

End Pre.


(* Lemma 2.5 "robustness 2sum and f2sum" *)
Lemma sma_exact  a b (Fa: format a) (Fb : format b) rnd (valid_rnd :Valid_rnd rnd ) : 
  ((ce b ) <= (ce a))%Z ->
let s := round beta fexp rnd (a + b) in 
  format (s - a).
Proof.
move=> cb_le_ca /=.
wlog apos: a b Fa Fb  rnd  valid_rnd  cb_le_ca/ 0 <= a.
  move=> Hwlog.
  case: (Rle_lt_dec 0 a) =>[apos | aneg].
    by apply/Hwlog.
  rewrite/=.
  have -> : (a + b ) = - ((-a)+ (-b)) by ring.
  have RDOp: forall x y,  -x - y =-( x - (-y)) by move=>x y ; ring.
  case: (@round_DN_or_UP beta fexp rnd valid_rnd (- (- a + - b)))=> ->;
    [rewrite round_DN_opp | rewrite round_UP_opp];
     rewrite  RDOp;apply/generic_format_opp;
     apply/Hwlog=>//; try (by  apply/generic_format_opp); try lra;
    by  rewrite !cexp_opp.
case:apos=>[apos |<-]; 
  last by rewrite Rminus_0_r; apply/generic_format_round.
set  s := round _ _ _ _.
case:(Req_dec s 0)=> [s0|sn0].
  move: s0 ; rewrite /s; move/ round_plus_eq_0 -> =>//.
  by rewrite round_0 Rminus_0_l; apply/generic_format_opp.
have abn0: a+b <> 0 by move => ab0; apply/sn0; rewrite /s ab0 round_0.
set sma:= s - a.
move: (Fa) (Fb); rewrite {1 2}/generic_format/F2R/=.
set Ma := Ztrunc _; set Mb := Ztrunc _=>aE bE.
have Maub: (Z.abs Ma <= beta^p -1)%Z by apply/FLT_mant_le.
have Mbub: (Z.abs Mb <= beta^p -1)%Z by apply/FLT_mant_le.
have Mapos: (0 <=  Ma)%Z by apply/le_IZR; move: (bpow_gt_0 beta (ce a)); nra.
case:(Z.le_gt_cases (ce s) (ce b))=> hcecb.
  rewrite /sma /s sma_exact_aux //. 
    by have ->: a + b -a = b by ring.
  by rewrite  Z.min_r.
have cexp_Maxab: ce  (Rmax (Rabs a) (Rabs b)) = ce a.
  case/Zle_lt_or_eq:  cb_le_ca => cb_ca; last first.
      rewrite /Rmax;case :(Rle_dec _ _); rewrite cexp_abs; lia.
    rewrite Rmax_left ?cexp_abs //.
    move/lt_cexp:cb_ca; lra.
have /Rabs_le_inv abB: Rabs (a + b)  <= 2 * (Rmax (Rabs a) (Rabs b)).
  apply/(Rle_trans _ _ _ (Rabs_triang a b)).
  by rewrite double; apply/Rplus_le_compat; [apply/Rmax_l|apply/Rmax_r].
have F2ab : format ( 2 * Rmax (Rabs a) (Rabs b)).
  rewrite Rmult_comm; have ->: 2 =  pow 1 by [].
  apply/mult_bpow_pos_exact_FLT; last  lia.
  rewrite /Rmax.
  by case :(Rle_dec _ _)=>*;apply/generic_format_abs.
have sB: Rabs s <= (2 * Rmax (Rabs a) (Rabs b)).
  apply/Rabs_le; split.
    rewrite -[X in X <= _](round_generic beta fexp rnd).
      by apply/round_le; lra.
    by apply/generic_format_opp.
  rewrite -(round_generic _ _ _ _ F2ab).
   apply/round_le; lra.
have ces_le_ca: (ce s <= 1 + ce a)%Z.
  apply/(Z.le_trans _ (ce (2 * Rmax (Rabs a) (Rabs b)))).
    by  apply/cexp_le=>//; rewrite [X in _ <= X]Rabs_pos_eq //;lra.
  have->: 2 = pow 1 by [].
  rewrite Rmult_comm -cexp_Maxab.
  by rewrite /cexp /fexp mag_mult_bpow=>//; last lra; lia.
have abpos_or_ceq : 0 < a + b \/ ce a = ce b.
  case / Z_le_lt_eq_dec: cb_le_ca; last by right.
  move=>hce.
  have : Rabs b < Rabs a. 
    apply/(lt_cexp beta fexp _ _ _ hce); lra.
  rewrite (Rabs_pos_eq a); last lra.
  by move/Rabs_lt_inv; lra.
have  : format s by apply/generic_format_round.
rewrite {1}/generic_format/F2R/=.
set Ms := Ztrunc _.
move=> sE.
have Msub: (Z.abs Ms <= beta^p -1)%Z by apply/FLT_mant_le.

case/Zle_lt_or_eq:   ces_le_ca=>[ces_lt_ca | ces_eq_ca]; last first.

pose delta := (Zminus (ce a)  (ce b)).
  pose mu :=  (Ms * beta - Ma)%Z.
  have: (Z.abs mu <= Z.abs Mb + 1)%Z.
    suff :  (Z.abs mu < Z.abs Mb + 2)%Z by lia.
    apply/lt_IZR.
    rewrite plus_IZR !abs_IZR.
    have h1: (IZR Mb* pow (-delta) - 2 < IZR mu < IZR  Mb* pow (-delta) + 2)%R.
      have :   Rabs (s - (a + b)) <   ulp beta fexp s.
        by apply/error_lt_ulp_round=>//.
      rewrite ulp_neq_0 //.
      rewrite {1}sE aE bE.
      move/Rabs_lt_inv.
      have->: IZR Ms * pow (ce s) = 2 * (IZR Ms) * pow (ce a).
        by rewrite ces_eq_ca bpow_plus /= ; lra.
      have->:  2 * IZR Ms * pow (ce a) - (IZR Ma * pow (ce a) + IZR Mb * pow (ce b)) = 
              (IZR mu) * pow (ce a)  - IZR Mb * pow (ce b).
        by rewrite /mu plus_IZR mult_IZR opp_IZR /=; lra.
      have-> : pow (ce s ) = 2 * pow (ce a) by rewrite ces_eq_ca bpow_plus /=; lra.
      have ->: pow (ce b) = pow (-delta ) * pow (ce a).
        by rewrite -bpow_plus; congr bpow; rewrite /delta ; lia.
      rewrite -Rmult_assoc -Rmult_minus_distr_r.
      by have:= (bpow_gt_0 beta (ce a)); nra.
    apply/(Rlt_le_trans _ ((Rabs (IZR Mb) * pow (- delta)) + 2)); last first.
      apply/Rplus_le_compat_r; rewrite -[X in _ <= X]Rmult_1_r; apply/Rmult_le_compat_l.
        by apply/Rabs_pos.
      by have ->: 1 = pow 0 by []; apply/bpow_le; lia.
    apply/Rabs_lt.
    case : (Rle_lt_dec 0 (IZR Mb))=> Mb0.
      by rewrite Rabs_pos_eq //; move:(bpow_gt_0 beta (- delta)); nra.
    rewrite -Rabs_Ropp Rabs_pos_eq; last lra.
    by move:(bpow_gt_0 beta (- delta)); nra.
  move=> hmu.
  have smaE: sma = IZR mu * pow (ce a).
    by rewrite /mu minus_IZR mult_IZR /sma sE {1} aE ces_eq_ca 
       bpow_plus /=; lra.
  have: (Z.abs mu <=  beta ^ p)%Z by lia.
  case/Zle_lt_or_eq=> muB.
  pose fx := Float beta mu (ce a).

  apply/generic_format_FLT/(FLT_spec _ _ _ _ fx)=>//.
    by rewrite /F2R/= /cexp /fexp; lia.
  pose fx := Float beta (Z.sgn mu * beta ^ ( p -1))(1 + ce a). 
  apply/generic_format_FLT/(FLT_spec _ _ _ _ fx).
  - rewrite smaE /F2R /fx.
    set cea1:=  (1 + ce a)%Z.
    rewrite /=  -{1}(Z.abs_sgn mu) muB !mult_IZR !(IZR_Zpower beta); try  lia.
    rewrite Rmult_assoc bpow_plus !Rmult_assoc  -!bpow_plus /cea1.
    rewrite Rmult_comm Rmult_assoc -bpow_plus ; congr Rmult.
    congr bpow; lia.
  - rewrite /fx/F2R/=.
    suff -> :   (Z.abs (Z.sgn mu * 2 ^ (p - 1)) =  2^ (p - 1))%Z.
      by apply/(Zpower_lt beta); lia.
    lia.
  rewrite /fx; set ces := (1 + ce a)%Z.
  by rewrite /F2R/= /ces /cexp /fexp;lia.
have abE: a+b = 
       (IZR Ma * pow (ce a - ce s) + IZR Mb * pow (ce b - ce s)) * pow (ce s).
  rewrite {1}aE {1}bE Rmult_plus_distr_r !Rmult_assoc -!bpow_plus.
  congr Rplus ; congr Rmult; congr bpow; lia.
have :   Rabs (s - (a + b)) <   ulp beta fexp s.
        by apply/error_lt_ulp_round=>//.
rewrite ulp_neq_0 =>//.
move/Rabs_lt_inv=> s_e.
have : b - pow (ce s) < s - a < b + pow (ce s) by lra.
have ->: b = (IZR Mb * pow (ce b - ce s)) * pow (ce s).
rewrite [LHS]bE Rmult_assoc -bpow_plus; congr Rmult; congr bpow; lia.
rewrite  -[X in _ - X]Rmult_1_l -[X in _ + X]Rmult_1_l.
rewrite -Rmult_minus_distr_r -Rmult_plus_distr_r.
have smaE : s - a = IZR (Ms - Ma * 2 ^ (ce a - ce s)) * pow (ce s).
  have aE': a = IZR Ma * pow (ce a - ce s)* pow (ce s).
    by rewrite [LHS] aE Rmult_assoc -bpow_plus; congr Rmult ; 
       congr bpow; lia.

  rewrite [in LHS]sE [in LHS]aE'.
  rewrite minus_IZR mult_IZR (IZR_Zpower beta); last lia; lra.
rewrite smaE.
set K := (Ms - _)%Z.
move=> hK.
have : (IZR Mb * pow (ce b - ce s) - 1)  < IZR K <  
         (IZR Mb * pow (ce b - ce s) + 1).
by move:(bpow_gt_0 beta (ce s)); nra.
rewrite /sma smaE -/K.
move=> Hk.
pose fx := Float beta K (ce s). 
apply/generic_format_FLT/(FLT_spec _ _ _ _ fx); first 2 last.
- by rewrite /fx/F2R/= /cexp/fexp;lia.
- by rewrite /fx /F2R/=.  
rewrite /fx/F2R/=.
apply/lt_IZR; rewrite abs_IZR (IZR_Zpower beta); last lia.
apply/(Rle_lt_trans _ (Rabs (IZR Mb)/2 + 1)); last first.
  case:(Z_zerop Mb)=>[->|mb0].
    rewrite Rabs_R0/Rdiv  Rmult_0_l Rplus_0_l; have ->: 1 = pow 0 by [].
    apply/bpow_lt; lia.
  apply/(Rlt_le_trans _ (Rabs (IZR Mb) + 1)).
    suff: 0 < Rabs (IZR Mb) by lra.
    by apply/Rabs_pos_lt/IZR_neq.
  suff:   Rabs (IZR Mb)  <= pow p -1 by lra.
  rewrite -abs_IZR -IZR_Zpower; last lia.
  by rewrite -minus_IZR; apply/IZR_le.
apply/(Rle_trans _  ((Rabs (IZR Mb)) * pow (ce b - ce s) +1)); last first.
suff:  pow (ce b - ce s)<= /2 by move:(Rabs_pos (IZR Mb)); nra.
have ->: /2 = pow (-1) by [].
apply/bpow_le; lia.
apply/Rabs_le.
    case : (Rle_lt_dec 0 (IZR Mb))=> Mb0.
      by rewrite Rabs_pos_eq //; move:(bpow_gt_0 beta (ce b -ce s)); nra.
    rewrite -Rabs_Ropp Rabs_pos_eq; last lra.
    by move:(bpow_gt_0 beta (ce b -ce s)); nra.
Qed.

Lemma sma_exact_abs  a b (Fa: format a) (Fb : format b) rnd (valid_rnd :Valid_rnd rnd ) : 
  Rabs b <= Rabs a ->
let s := round beta fexp rnd (a + b) in 
  format (s - a).
Proof.
move=> bLa s.
have [b_eq0|b_neq0] := Req_dec b 0.
  rewrite /s b_eq0 !Rsimp01 round_generic // Rminus_eq_0.
  by apply: generic_format_0.
apply: sma_exact => //.
by apply: cexp_le.
Qed.

Lemma sma_exact_abs_or0  a b (Fa: format a) (Fb : format b) rnd (valid_rnd :Valid_rnd rnd ) : 
  (a = 0 \/ Rabs b <= Rabs a) ->
let s := round beta fexp rnd (a + b) in 
  format (s - a).
Proof.
move=> [a_eq0| bLa] s.
  by rewrite /s a_eq0 !Rsimp01 round_generic.
by apply: sma_exact_abs.
Qed.

End F2Sum.
End Main.




