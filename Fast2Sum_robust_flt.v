(* Formalisation of the F2Sum part of "On the robustness of the @Sum andt Fast2Sum algo" *)

(* Copyright (c)  Inria. All rights reserved. *)
Require Import Reals  Psatz.
From Flocq Require Import Core Plus_error Mult_error Relative Sterbenz Operations.
From Flocq Require Import  Round.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rmore MULTmore.

Set Implicit Arguments.

Section Main.
Definition  beta:= radix2.
Variable emin p : Z.
Hypothesis precisionNotZero : (1 < p)%Z.
Context { prec_gt_0_ : Prec_gt_0 p}.
Hypothesis eminB:(emin < - p - 1)%Z.



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

Lemma cexp_le (x y: R)  (xne0 : x <> 0%R) : 
    (Rabs x <= Rabs y)%R -> (ce x <= ce y)%Z.
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

Lemma round_bpow_flt  x e (emin_le: (emin <= Z.min (mag beta x + e - p)
    (mag beta x - p))%Z) :
    rnd_p (x * pow e) = (rnd_p x * pow e)%R.
Proof.
case: (Req_dec x 0) => [->|Zx] ; first by rewrite Rmult_0_l round_0 Rmult_0_l.
by rewrite /round /F2R /= mant_bpow_flt //  cexp_bpow_flt // bpow_plus
Rmult_assoc.
Qed.

Lemma round_bpow_flt_pos  x e  (emin_le: (emin <=  (mag beta x - p))%Z)
(epos: (0 <= e)%Z):
    rnd_p (x * pow e) = (rnd_p x * pow e)%R.
Proof.
case: (Req_dec x 0) => [->|Zx] ; first by rewrite Rmult_0_l round_0 Rmult_0_l.
rewrite /round /F2R /= mant_bpow_flt // ?cexp_bpow_flt // ?bpow_plus
?Rmult_assoc //; lia.
Qed.

Lemma format_mag_ge_emin a (a_neq0: a <> 0)(Fa: format a) : (emin +1 <= mag beta a)%Z.
Proof.
have:  (cexp beta fexp a < mag beta a)%Z.
apply /mag_generic_gt=>//.
rewrite /cexp/fexp; lia.
Qed.

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
Lemma sma_exact  a b (Fa: format a) (Fb : format b) 
     rnd (valid_rnd :Valid_rnd rnd ) : 
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
set Ma := Ztrunc _; set Mb := Ztrunc _=> aE bE.
have Maub: (Z.abs Ma <= beta^p -1)%Z by apply/FLT_mant_le.
have Mbub: (Z.abs Mb <= beta^p -1)%Z by apply/FLT_mant_le.
have Mapos: (0 <=  Ma)%Z by apply/le_IZR; 
   move: (bpow_gt_0 beta (ce a)); nra.
case:(Z.le_gt_cases (ce s) (ce b))=> hcecb.
  rewrite /sma /s sma_exact_aux //. 
    by have ->: a + b - a = b by ring.
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

Lemma sma_exact_abs_or0  a b (Fa: format a) (Fb : format b) 
                         rnd (valid_rnd :Valid_rnd rnd ) : 
  (a <> 0 -> Rabs b <= Rabs a) ->
let s := round beta fexp rnd (a + b) in 
  format (s - a).
Proof.
move=> Hab s.
have [a_eq0 | a_neq0] := Req_dec a 0.
  by rewrite /s a_eq0 !Rsimp01 round_generic.
by apply: sma_exact_abs => //;lra.
Qed.

Lemma format_Rabs_round_ge f g rnd (valid_rnd :Valid_rnd rnd )  : 
  format f -> Rabs g <= f -> Rabs (round beta fexp rnd g) <= f.
Proof.
move=> Ff fLg.
set RND := round beta fexp rnd.
have RF: round beta fexp  rnd f = f by rewrite round_generic.
have RFopp: round beta fexp  rnd (-f) = -f 
   by rewrite round_generic //; apply/generic_format_opp.
apply/Rabs_le; split;[rewrite -RFopp|rewrite -RF]; 
  apply/round_le; split_Rabs; lra.
Qed.

Lemma sma_ulp_round  a b (Fa: format a) (Fb : format b) rnd 
                    (valid_rnd: Valid_rnd rnd ) : 
  (a <> 0 -> Rabs b <= Rabs a) ->
let h := round beta fexp rnd (a + b) in 
let s := round beta fexp rnd (h - a) in 
let t := round beta fexp rnd (b - s) in 
Rabs t <= ulp beta fexp h.
Proof.
move=> bLa h s t.
rewrite /t [s]round_generic; last first.
  by apply: sma_exact_abs_or0.
rewrite /h.
set RND := round beta fexp rnd.
set xx := a + b.
have ->: b - (RND xx - a) =  (xx - RND xx) by rewrite /xx; lra.
have F1 : Rabs (xx - RND xx) <= ulp beta fexp (RND xx).
  rewrite -Rabs_Ropp Ropp_minus_distr.
  by apply: error_le_ulp_round.
apply: format_Rabs_round_ge => //.
by apply: generic_format_ulp.
Qed.

Lemma sma_ulp  a b (Fa: format a) (Fb : format b) rnd 
                   (valid_rnd: Valid_rnd rnd ) : 
  (a <> 0 -> Rabs b <= Rabs a) ->
let h := round beta fexp rnd (a + b) in 
let s := round beta fexp rnd (h - a) in 
let t := round beta fexp rnd (b - s) in 
Rabs t <= ulp beta fexp (a + b).
Proof.
move=> bLa h s t.
rewrite /t [s]round_generic; last first.
  by apply: sma_exact_abs_or0.
rewrite /h.
set RND := round beta fexp rnd.
set xx := a + b.
have ->: b - (RND xx - a) =  (xx - RND xx) by rewrite /xx; lra.
have F1 : Rabs (xx - RND xx) <= ulp beta fexp xx.
  rewrite -Rabs_Ropp Ropp_minus_distr.
  by apply: error_le_ulp.
apply: format_Rabs_round_ge => //.
by apply: generic_format_ulp.
Qed.

Section F2Sum_pre.

Variable rnd : R-> Z.
Hypothesis valid_rnd: Valid_rnd rnd.
Local Notation rnd_p := (round beta fexp rnd).


Variables a b   : R.
Hypothesis Fa : format a.
Hypothesis Fb : format b.

Notation  s := (rnd_p (a + b)).
Notation  z := (rnd_p (s - a)).
Notation t := (rnd_p (b - z)).


Notation ulp := (ulp beta fexp).
Notation u := (pow (-p)).


Lemma Fast2Sum_correct_aux:
  (a <> 0 -> (mag beta  b <= mag beta  a)%Z)->
   (mag beta a <= mag beta b + p)%Z ->
          pow (p - 1) <= a < pow p ->
          let h := round beta fexp rnd (a + b) in
          let z := round beta fexp rnd (h - a) in let l := round beta fexp rnd (b - z) in h + l = a + b.
Proof.
move=> magaleb magalebp aB.
case:(Req_dec b 0 )=>[-> /= | bneq0].
  rewrite Rplus_0_r (round_generic _ _ _ a)// Rminus_eq_0 !(round_0, Rminus_0_r).
  by lra.
have apos: 0 < a  by move: (bpow_gt_0 beta (p - 1)); lra.
have aneq0: a <> 0 by lra.
have {} magaleb : (mag beta b <= mag beta a)%Z by apply:magaleb.
have magaE: (mag beta a  = p :>Z)%Z by rewrite (mag_unique_pos beta _ p).
have cea0:  (ce a = 0)%Z by rewrite /cexp /fexp; lia.
have ulpa: ulp a = 1.
  rewrite ulp_neq_0;last lra.
  by rewrite cea0.
have clea : (ce b <= ce a)%Z.
  by rewrite /cexp/fexp; lia.
have pow0 : pow 0 = 1 by [].
have pow1: pow 1 = 2 by [].
have bB: Rabs b < pow p.
  apply/(Rlt_le_trans _ (pow (mag beta b))).
    by apply/bpow_mag_gt.
  apply/(Rle_trans _ (pow (mag beta a))).
    by apply/bpow_le.
  by rewrite (mag_unique_pos _ _ p) //; lra.
have aub: a <= pow p - 1.
  have ->: pow p - 1 = pred beta fexp (pow p).
    rewrite pred_bpow /fexp Zeq_minus//  Zmax_left ?pow0 //; lia.
  apply/pred_ge_gt =>//; last lra.
  apply/generic_format_bpow; rewrite /fexp; lia.
have bub: Rabs b <= pow p - 1.
  have ->: pow p - 1 = pred beta fexp (pow p).
    rewrite pred_bpow /fexp Zeq_minus//  Zmax_left ?pow0 //; lia.
  apply/pred_ge_gt =>//.
    by apply/generic_format_abs.
  by   apply/generic_format_bpow; rewrite /fexp; lia.
have abB : Rabs (a + b) <= pow (p + 1) - 2.
  apply/(Rle_trans _ _ _ (Rabs_triang _ _)).
  rewrite bpow_plus pow1 Rabs_pos_eq; lra.
have hrab: Rabs (round beta fexp rnd  (a + b)) <= (pow (p +1) - 2).
  apply/format_Rabs_round_ge=>//.
  have ->:  (pow (p + 1) - 2)= pred beta fexp (pow (p + 1)).
    rewrite pred_bpow ; congr Rminus.
    rewrite -pow1 /fexp; congr bpow; lia.
  apply/generic_format_pred/generic_format_bpow; rewrite /fexp;lia.  
move=> x.
have ulph: ulp x <= 2.
  have <- : ulp (pow (p+1) -2 ) = 2.
    rewrite ulp_neq_0 /cexp /fexp.
      rewrite (mag_unique_pos _ _  (p + 1)).
        rewrite  -pow1 Z.max_l; last lia.
        congr bpow; lia.
      split; try lra.
      rewrite (bpow_plus _ _ (-1)).
      have->: pow (-1) = /2 by [].
      suff: 4 <= pow (p  + 1) by lra.
      have ->: 4 = pow 2 by [].
      apply/bpow_le; lia.
    suff : 2 < pow (p + 1) by lra.
    rewrite -pow1; apply/bpow_lt; lia.
  apply/ulp_le; rewrite (Rabs_pos_eq (_ -_)).
    by rewrite /x.
  suff : 2 < pow (p + 1) by lra.
  rewrite -pow1; apply/bpow_lt; lia.

case:(Req_dec (a + b) 0)=> [ /= ab0 | abn0].
  rewrite  /x ab0 round_0 !Rsimp01 (round_generic _ _ _ (-a)).
    have->: b - - a =   a + b by lra.
    by rewrite ab0 round_0.
  by apply/generic_format_opp.
have hn0: x <> 0 by apply/round_plus_neq_0.
set e := (a + b) - x.
have eb: Rabs e < ulp  x.
  have->: Rabs e = Rabs (x - (a + b)).
    by rewrite -Rabs_Ropp /e ; congr Rabs; lra.
  rewrite /x; apply/error_lt_ulp_round=>//.
move=>z.
have z_exact: z = x -a.
  by rewrite /z round_generic //; apply/sma_exact.
move=> y.
have yE: y = round beta fexp rnd e by rewrite /y z_exact /e; congr round; lra.

pose k := (mag beta  a -  mag beta  b)%Z.
have kb: (0 <= k <= p)%Z by rewrite /k; lia.
case : (ex_shift beta fexp b (-k) Fb); first by rewrite /cexp /fexp  /k; lia.
move=>mb bE.
case: (ex_shift beta fexp a (-k) Fa); first by lia.
move=> ma aE.
have imul_a: is_imul  a (bpow beta (-k)).
  by exists ma.
have imul_b : is_imul  b (pow (-k)) by exists mb.
have imul_x: is_imul x (pow (-k)).
  by apply/is_imul_pow_round/is_imul_add.
have imul_e: is_imul e (pow (-k)).
  by apply/is_imul_minus=>//; apply/is_imul_add.
case: imul_e => m eE.
case: (Rlt_le_dec  (Rabs x) (pow p) ) => xb.
  have uhle1: (ulp x <= 1).
    rewrite  -pow0 ulp_neq_0 //.
    apply/bpow_le.
    have : (mag beta x <= p)%Z .
      apply/mag_le_bpow=>//; lia.
    by rewrite /cexp /fexp; lia.
  have eub: Rabs e < 1 by lra.
  rewrite  /y  round_generic.
    by rewrite z_exact; ring.
  have->: b - z = e by rewrite z_exact /e; lra.
  rewrite eE.
  pose fe := Float beta m (-k). 
  apply/generic_format_FLT/(FLT_spec _ _ _ _ fe).
  - by rewrite  /fe/F2R/=.
  - rewrite /fe/F2R/=.
    move: eub ; rewrite eE Rabs_mult (Rabs_pos_eq (pow _)); last by apply/bpow_ge_0.
    move/(Rmult_lt_compat_r (pow k) _ _ (bpow_gt_0 beta k)).
    rewrite Rmult_assoc -bpow_plus.
    have->: (-k + k = 0 )%Z by lia.
    rewrite pow0 Rmult_1_l Rmult_1_r -abs_IZR -(IZR_Zpower beta); last lia.
    move/lt_IZR.
    suff : (beta ^ k <= 2 ^ p)%Z by lia.
    by apply/Zpower_le; lia.
  by rewrite /fe/F2R/=; lia.
have ulpxE: ulp x = 2.
  suff : 2 <= ulp x by lra.
  rewrite ulp_neq_0 // /cexp /fexp.
  have hmagx: ( p +1 <= mag beta x)%Z.
    by apply/mag_ge_bpow; ring_simplify (p + 1 -1)%Z.
  by rewrite -pow1; apply/bpow_le;  lia.
have : (k <= p )%Z by lia.
case/Z_le_lt_eq_dec=>kp.
  rewrite yE round_generic;  first by rewrite /e ;  lra.
  rewrite eE.  
  pose fe := Float beta m (-k). 
  apply/generic_format_FLT/(FLT_spec _ _ _ _ fe).
  - by rewrite /F2R /=.
  - rewrite /fe/F2R/=.
    apply/(Z.lt_le_trans _ (2^(k+1))); last by apply/(Zpower_le beta); lia.
    move: eb; rewrite ulpxE eE.
    rewrite Rabs_mult (Rabs_pos_eq (pow _)); last by apply/bpow_ge_0.
    move/(Rmult_lt_compat_r (pow (k)) _  _(bpow_gt_0 beta k)).
    rewrite Rmult_assoc -bpow_plus;ring_simplify (-k + k)%Z.
    rewrite pow0 -pow1 Rmult_1_r -bpow_plus.
    rewrite -abs_IZR -IZR_Zpower; last lia.
    by move/lt_IZR; rewrite Zplus_comm.
  by rewrite /fe /F2R /=; lia.
(* k = p *)
have magb0: (mag beta b = 0 :>Z )%Z by lia.
have blub: /2 <= Rabs  b < 1.
  split.
    have ->: /2 = pow (-1) by [].
    have ->: (-1 = mag beta b - 1)%Z by lia.
    by apply/bpow_mag_le.
  by rewrite -pow0  -magb0; apply/bpow_mag_gt.
have abpos: 0 <= a + b.
  suff : 2 <= pow (p - 1) by split_Rabs;  lra.
  by rewrite -pow1; apply/bpow_le; lia.
have:  round beta fexp rnd 0 <= x by apply/round_le.
rewrite round_0.
case/Rle_lt_or_eq_dec=> xpos; last lra.
have bpos: 0 < b.
  case: (Rlt_le_dec 0 b)=> // hb0.
  have xa: x <= a .
    have ->: a =  round beta fexp rnd a.
      by rewrite round_generic.
    apply/round_le; lra.
  suff:  Rabs x <= Rabs a.
    by move/(ulp_le beta fexp); lra.
  by rewrite !Rabs_pos_eq ; lra.
rewrite Rabs_pos_eq in blub; last lra.
case: aub=> ha.
(* a < pow p -1 *)
  have Fpm1: format (pow p - 1).
    apply/generic_format_FLT/(FLT_spec _ _ _ _ (Float beta (2^p - 1) 0)); 
      rewrite /F2R /=; try lia.
    by rewrite /F2R /= minus_IZR (IZR_Zpower beta); last lia; lra.
  have aub: a <= pow p - 2.
    move: Fa ha; rewrite /generic_format /F2R /= cea0 pow0 Rmult_1_r=> ->.
    rewrite -IZR_Zpower -?minus_IZR; last lia.
    by move/lt_IZR=> h; apply/IZR_le; lia.
  have : a+b < pow p - 1 by lra.
  have : x <= round beta fexp rnd (pow p - 1).
    apply/round_le; lra.
  rewrite  (round_generic  _ _ _ (pow p -1)) //.
  move : ulpxE; rewrite ulp_neq_0 /cexp /fexp -?pow1; last lra.
  move/bpow_inj=>  h.
  have h': (mag beta x = p + 1 :>Z)%Z by lia.
  have: bpow beta  (mag beta x - 1) <= Rabs x.
    apply/bpow_mag_le;  lra.
  rewrite h' (Rabs_pos_eq x); try lra.
  ring_simplify(p + 1 - 1)%Z; lra.

(* a = pow p  - 1 *)
rewrite Rabs_pos_eq in xb; last lra.
have {} xE: x = pow p.
  suff : x <= pow p by lra.
  have ->: pow p = round beta fexp rnd (pow p).
    rewrite  round_generic //.
    apply/generic_format_bpow; rewrite /fexp; lia.
  apply/round_le; lra.
have zE: x - a = 1 by lra.
have he: e = b - 1 by rewrite /e ; lra.
rewrite /y round_generic ; first lra.
have h: (2^(p -1) <= mb < 2^p)%Z.
  move: blub; rewrite bE kp.
  have ->: /2 = pow (-1) by [].
  move=> [h1 h2].
  have h3: pow (p - 1) <= IZR mb .
    apply/(Rmult_le_reg_r (pow (-p))); first by apply /bpow_gt_0.
    by rewrite -bpow_plus; ring_simplify (p - 1 + - p)%Z.
  have h4: IZR mb < pow p.
    apply/(Rmult_lt_reg_r (pow (-p))); first by apply /bpow_gt_0.
    by rewrite -bpow_plus; ring_simplify (p  + - p)%Z.
  split;[apply/le_IZR|apply/lt_IZR]; rewrite (IZR_Zpower beta)//; lia.
have -> : b -z = e by rewrite z_exact /e ; ring.

rewrite he bE kp.
have ->: IZR mb * pow (-p)  - 1 = (IZR mb - pow p) * (pow (-p)).
  rewrite Rmult_minus_distr_r -bpow_plus.
  have ->: (p + -p = 0)%Z by ring.
  by rewrite pow0.
apply/generic_format_FLT/(FLT_spec _ _ _ _ (Float beta  (mb - 2 ^p) (-p))); 
    rewrite /F2R/=; try lia.
by rewrite   minus_IZR (IZR_Zpower beta);last lia; lra.
Qed.


End F2Sum_pre.


Definition round_direct (rnd: R -> Z):=
(forall x, round beta fexp rnd x = round beta fexp Zfloor x) \/
(forall x, round beta fexp rnd x = round beta fexp Zceil x).


Notation ulp := (ulp beta fexp).


Lemma fastTwoSum_correct_mag a b (Fa: format a) (Fb : format b) rnd 
                   (valid_rnd: Valid_rnd rnd ) (rndD: round_direct rnd) :
  (Rabs b <= Rabs a) -> (mag beta  a <=  mag beta b + p)%Z ->
let h := round beta fexp rnd (a + b) in 
let z := round beta fexp rnd (h - a) in 
let l := round beta fexp rnd (b - z) in 
 h + l = (a + b).
Proof.
move=> blea.
have pow0 : pow 0 = 1 by [].
have pow1: pow 1 = 2 by [].

(* case: (Req_dec a 0)=> [->|a_neq0]. *)
(*   by rewrite /= !(Rsimp01,(round_generic _ _ _ b), Rminus_eq_0,round_0). *)
wlog apos: a b Fa Fb  blea rnd valid_rnd rndD/ 0 <= a.
  move=> Hwlog.
  case: (Rle_lt_dec 0 a) =>[apos | aneg].
    by apply/Hwlog.
  move=> /= bleap.
  have apbE : (a + b ) = - ((-a) + (-b)) by ring.
  have E1: forall x y, - x -  y = - (x + y) by move=> *; ring.
  have E2: forall x y, x -  y = x + -y by move=> *; ring.
  have E3 : forall x y , - x + y = - (x - y ) by move=>*; ring.
  rewrite apbE.
  set ma := -a.
  set mb := -b.
  set Rm:= round _ _ _ _.
  have ->: b = - (-b) by ring.
  rewrite -/mb  (E2 _ a) -/ma E1 /Rm.
  case: rndD=> RNE; rewrite !RNE;
  rewrite  !(round_DN_opp , round_UP_opp) (E3 _ ma) 
     !(round_DN_opp, round_UP_opp) -E2 E1;
     congr Ropp ; rewrite -E2;
     apply/Hwlog=>//.
  + by apply/generic_format_opp.
  +  by apply/generic_format_opp.
  + by rewrite !Rabs_Ropp.
  + by right.
  + rewrite /ma ;lra.
  + by rewrite !mag_opp.
  + by apply/generic_format_opp.
  +  by apply/generic_format_opp.
  + by rewrite !Rabs_Ropp.
  + by left.
  + rewrite /ma ;lra.
  by rewrite !mag_opp.

case:apos=> [apos| <-]; last first.
  rewrite /=  Rplus_0_l Rminus_0_r !(round_generic _ _ _ b Fb) Rminus_eq_0
    round_0 =>*; ring.
case: (Req_dec b 0)=> [-> h1 /=   |bneq0].
  by rewrite /= !Rsimp01 (round_generic _ _ _ a) // !(Rminus_eq_0, round_0, Ropp_0); lra.
move=> maga_le_magb.
case:(Req_dec (a + b) 0)=> [ /= ab0 | abn0].
  rewrite  /=  ab0 round_0 !Rsimp01 (round_generic _ _ _ (-a)) ; last by apply/generic_format_opp.
  have->: b - - a =   a + b by lra.
  by rewrite ab0 round_0.
rewrite /=.
have hn0:  round beta fexp rnd (a + b) <> 0 by apply/round_plus_neq_0.
have abpos: 0 < a + b by split_Rabs; lra.

have  blea_mag:  (mag beta b <= mag beta  a)%Z by apply/mag_le_abs.

set x := round _ _ _ (a + b).
set z := (_ -a).
have xpos: 0 < x .
suff : 0 <= x by rewrite -/x in hn0;  lra.
have->: 0 = round beta fexp rnd 0 by rewrite round_0.
  by apply/round_le; lra.

have z_exact: format z.
  apply/sma_exact =>//.
  by rewrite /cexp;apply/FLT_exp_monotone;  lia.
rewrite (round_generic _ _ _ z)//.
case:(mag beta a)=> maga  aB.
have {} aB:  pow (maga - 1) <= a < pow maga .
by rewrite -(Rabs_pos_eq a) ; lra.
have magaE: maga = mag  beta a by rewrite (mag_unique_pos _ _ maga)=>//.
rewrite magaE in aB.


pose e :=  (a + b) - x .
have zE: z = b - e by  rewrite /z /e; lra.
set y := round _ _ _ _.
have yE: y = round beta fexp rnd e by rewrite /y; congr round ; lra.
have eb: Rabs e < ulp  x.
  have->: Rabs e = Rabs (x - (a + b)).
    by rewrite -Rabs_Ropp /e ; congr Rabs; lra.
  by rewrite /x; apply/error_lt_ulp_round.

pose t := (mag beta a - p)%Z.



pose k := (Z.min (mag beta a - mag beta b)%Z ( mag beta a - p  - emin)).

have emin_tk: (emin <= (t - k))%Z by rewrite /k /t; lia.
have a_is_mul_tk: is_imul a (pow (t - k)).
  by apply/(is_imul_format_mag_pow Fa); rewrite /fexp ; lia.

have b_is_mul_tk: is_imul b (pow (t - k)).
  by apply/(is_imul_format_mag_pow Fb); rewrite /fexp ; lia.
have x_is_mul_tk: is_imul x (pow (t - k)).
  by rewrite /x; apply/is_imul_pow_round/is_imul_add.
have e_is_mul_tk: is_imul e (pow (t - k)); rewrite /e.
  by apply/is_imul_minus=>//;  apply/is_imul_add.
case:(e_is_mul_tk) => m eE.
have aub : a < pow ( t + p).
  rewrite /t -{1}(Rabs_pos_eq a); last lra.
  apply/(Rlt_le_trans _ ( pow (mag beta a))).
    by apply/bpow_mag_gt.
  by apply/bpow_le; lia.
have bub : Rabs b < pow ( t +  p).
  rewrite /t ; apply/(Rlt_le_trans _ (pow (mag beta b))).
    by apply/bpow_mag_gt.
  by apply/bpow_le; lia.
have maga_lb: (emin + 1 <= mag beta a)%Z 
  by apply/format_mag_ge_emin =>//; lra.
have magb_lb: (emin + 1 <= mag beta b)%Z 
  by apply/format_mag_ge_emin =>//; lra.
have alepred: a <= pred beta fexp (pow (t + p)).
  apply/pred_ge_gt=>//.
apply/generic_format_FLT_bpow;lia.
have blepred: Rabs b <= pred beta fexp (pow (t + p)).
  apply/pred_ge_gt=>//.
    by apply/generic_format_abs.
  apply/generic_format_FLT_bpow; lia.
(* rewrite pred_bpow   in   blepred alepred. *)
case:(Z_lt_le_dec (t +1 ) emin)=> ht_emin.
  have xE: x = a + b .
    rewrite /x round_generic //.
    apply/Hauser=>//.
    apply/(Rle_trans  _ _ _ (Rabs_triang _ _)); rewrite Rabs_pos_eq ; last lra.
    apply(Rle_trans _ ( 2 * (pow (t + p)))).
      suff: 0 <  pow (fexp (t + p)) by lra.
      apply/bpow_gt_0.
    rewrite -pow1 -bpow_plus; apply/bpow_le; lia.
    rewrite /y /z  xE; ring_simplify (b - (a + b - a)); rewrite round_0; lra.

have h: a + Rabs b <= pred beta fexp   (pow ( 1 + (t + p))).
  rewrite pred_bpow bpow_plus pow1.
  suff: (pow (fexp (1 + (t + p)))) <= 2 * (pow (fexp (t + p)))  by 
rewrite pred_bpow   in   blepred alepred; lra.
  rewrite -pow1 -bpow_plus.
  apply/bpow_le; rewrite/fexp ;lia.
have h': a + b <= pred beta fexp (pow (1 + (t + p))) by split_Rabs; lra.
have : x <= round beta fexp rnd (pred beta fexp (pow (1 + (t + p)))).
  by apply/round_le.
rewrite round_generic; last first.
  apply/generic_format_pred/generic_format_bpow; rewrite /fexp; lia.
move=> xub.

have : ulp x <= pow (t + 1).
  apply/(Rle_trans _ (ulp  (pred beta fexp (pow (1 + (t + p)))))).
    apply/ulp_le; rewrite !Rabs_pos_eq;  lra.
  rewrite ulp_neq_0; last first.
    move:(bpow_gt_0 beta (t + p)); lra.
  apply/bpow_le.
   rewrite /cexp  (mag_unique_pos _ _ (1 + (t + p ))).
     rewrite /fexp; try lia.
  rewrite pred_bpow; split; last first.
    set ff:= fexp _ .
    suff: 0 < pow ff by lra.
    by apply/bpow_gt_0.
  rewrite (bpow_plus _ 1) pow1.
  ring_simplify  (1 + (t + p) - 1)%Z.
  suff : pow (fexp (1 + (t + p)))<=  pow (t + p) by lra.
  apply/bpow_le; rewrite /fexp; lia.
(* la *)

case=>uxt.
  have {} uxt : ulp x <= pow t.
    move:uxt; rewrite ulp_neq_0; last lra.
    move/lt_bpow=>hh.
    by apply/bpow_le; lia.
  have eub: Rabs e < pow t by lra.
  rewrite  /y  round_generic.
    by rewrite /z; ring.
  have->: b - z = e by rewrite /z  /e; lra.
  rewrite eE.
  have  kE: (k = mag beta a - Z.max ( mag beta b) ( (p + emin)))%Z  by lia.
  move: eub.
  rewrite eE Rabs_mult (Rabs_pos_eq  (pow _)); last by apply/bpow_ge_0.
  move/(Rmult_lt_compat_r (pow (k -t))_  _ (bpow_gt_0 beta (k - t))).
  rewrite Rmult_assoc -!bpow_plus.
  ring_simplify(t - k + (k - t))%Z.
  ring_simplify(t + (k - t))%Z.
  rewrite pow0 Rmult_1_r.
  case:(Z_lt_le_dec 0 k) =>hk.
    rewrite -abs_IZR -(IZR_Zpower beta); last lia.
    move/lt_IZR => /= hmk.
    pose fe := Float beta (m )  (t - k). 
    apply/generic_format_FLT/(FLT_spec _ _ _ _ fe); rewrite /F2R//=.
    apply/(Z.lt_le_trans _ ( 2 ^ k))=>//.
    apply/(Zpower_le beta); lia.
  move=> hh.
  have : Rabs (IZR m ) < 1 .
    apply/(Rlt_le_trans _ (pow k))=>//.
    rewrite -pow0; apply/bpow_le; lia.
  rewrite -abs_IZR; move/lt_IZR=> h0.
  have->: (m = 0)%Z by lia.
  by rewrite Rmult_0_l; apply/generic_format_0.
(* ulp x = pow (t + 1) *)
have : (k <= p)%Z by lia.
case/Zle_lt_or_eq=> kp.
move:eb; rewrite uxt=> eb.
  rewrite  /y  round_generic.
    by rewrite /z; ring.
  have->: b - z = e by rewrite /z  /e; lra.
  rewrite eE.
  have  kE: (k = mag beta a - Z.max ( mag beta b) ( (p + emin)))%Z  by lia.

  move: eb.
  rewrite eE Rabs_mult (Rabs_pos_eq  (pow _)); last by apply/bpow_ge_0.
  move/(Rmult_lt_compat_r (pow (k -t))_  _ (bpow_gt_0 beta (k - t))).
  rewrite Rmult_assoc -!bpow_plus.
  ring_simplify(t - k + (k - t))%Z.
  ring_simplify(t + 1 + (k - t))%Z.
  rewrite pow0 Rmult_1_r.
  case:(Z_lt_le_dec k 0) =>hk; last first.
    rewrite -abs_IZR -(IZR_Zpower beta); last lia.
    move/lt_IZR => /= .
    move=> mkb.
    pose fe := Float beta (m )  (t - k). 
    apply/generic_format_FLT/(FLT_spec _ _ _ _ fe); rewrite /F2R//=.
    apply/(Z.lt_le_trans _ ( 2 ^ (k + 1)))=>//.
    apply/(Zpower_le beta); lia.
  move=> hh.
  have : Rabs (IZR m ) <  1.
    apply/(Rlt_le_trans _ (pow (k + 1)))=>//.
    rewrite -pow0; apply/bpow_le; lia.
  rewrite -abs_IZR; move/lt_IZR=> h0.
  have->: (m = 0)%Z by lia.
  by rewrite Rmult_0_l; apply/generic_format_0.
(* k = p, ulp x = pow (t + 1) *)
have magbt: (mag beta b = t :>Z )%Z by lia.
have blub: /2* pow t <= Rabs  b < pow t.
  split.
    have ->: /2 * pow t = pow (t-1) .
      by rewrite   Rmult_comm (bpow_plus _ t);congr Rmult ; congr bpow.
    by rewrite -magbt; apply/bpow_mag_le.
  by rewrite  -magbt; apply/bpow_mag_gt.
have ua: ulp a = pow t.
rewrite ulp_neq_0 /t; last lra.
congr bpow; rewrite /cexp /fexp; lia.
case: (Rlt_le_dec 0 b)=> // hb0; last first.
  have xa: x <= a .
    have ->: a =  round beta fexp rnd a.
      by rewrite round_generic.
    apply/round_le; lra.
  suff: pow (t + 1) <= pow t by move/le_bpow; lia.
  rewrite -ua -uxt ; apply/ulp_le_pos; lra.
rewrite Rabs_pos_eq in blub; last lra.
case:   alepred=> ha.
  have :  a + b < succ beta fexp a.
    by rewrite succ_eq_pos; lra.
  move => hsucc.
  have:a <= pred beta fexp (pred beta fexp (pow ( t +  p))).
    by apply/pred_ge_gt  =>//; apply/generic_format_pred/generic_format_FLT_bpow; lia.
  move/(succ_le beta fexp _ _ Fa).
  rewrite succ_pred => [hh |].
    have : x <= pred beta fexp (pow (t + p)).
      rewrite -(round_generic beta fexp rnd (pred _ _ _ )).
        apply/round_le/(Rle_trans _ ( succ beta fexp a )); try lra.
        by apply/hh/generic_format_pred/generic_format_pred/generic_format_FLT_bpow; lia.
      by apply/generic_format_pred/generic_format_FLT_bpow; lia.
    rewrite pred_bpow => hg.
    suff : pow (t + p) <= x by move :(bpow_gt_0 beta (fexp (t + p))); lra.
    have : (mag beta x <= t + p)%Z.
      apply/mag_le_bpow=>//.
      by rewrite Rabs_pos_eq; move:(bpow_gt_0 beta (fexp ( t  + p))); lra.
    move => magx.
    move: uxt;rewrite ulp_neq_0; last lra.
    by rewrite /cexp /fexp; move/bpow_inj; lia.
  by apply/generic_format_pred/generic_format_FLT_bpow; lia.
have aE : a = (pow p - 1 ) * pow t.
  rewrite ha pred_bpow /fexp Z.max_l; last lia.
  by ring_simplify(t + p - p)%Z; rewrite bpow_plus; lra.
have xE: x = pow (t + p).
  apply/Rle_antisym.
    have -> :  pow (t + p) = round beta fexp rnd ( pow (t + p)).
      rewrite round_generic //.
       by apply/generic_format_FLT_bpow; lia.
    by apply/round_le; rewrite bpow_plus; lra.
  rewrite -(Rabs_pos_eq x); last lra.
  apply/(Rle_trans _ (pow (mag beta  x - 1))).
    apply/bpow_le.
    move:uxt; rewrite ulp_neq_0; last lra.
    by move/bpow_inj; rewrite /cexp /fexp; lia.
  by apply/bpow_mag_le.
have zE': z  = pow t by rewrite /z aE xE bpow_plus; lra.
 suff ->: y = e by rewrite /e; lra.
rewrite /y round_generic /z /e; first lra.
rewrite -/z zE'.
case:(  b_is_mul_tk)=> mb bE.
move:blub; rewrite bE=> blub.
have: / 2 * pow t * pow (k -t)  <= IZR mb * pow (t - k) * pow (k - t) < 
      pow t* pow (k -t) by move: (bpow_gt_0 beta (k -t)); nra.
rewrite !Rmult_assoc -!bpow_plus.
ring_simplify(t + (k - t))%Z;ring_simplify(t - k + (k - t))%Z; rewrite pow0 Rmult_1_r.
move => hmb.
pose fe := Float beta (mb - 2^k )  (t - k). 
apply/generic_format_FLT/(FLT_spec _ _ _ _ fe); rewrite /F2R//=.
  rewrite minus_IZR (IZR_Zpower beta); last lia.
  rewrite Rmult_minus_distr_r -bpow_plus; congr (Rminus _ (bpow beta _)).
  lia.
apply/lt_IZR.
rewrite abs_IZR minus_IZR !(IZR_Zpower beta); try lia.
apply/Rabs_lt; rewrite -kp.
by move:(bpow_gt_0 beta k); nra.
Qed.

Notation R_DN := (round beta fexp Zfloor).
Notation R_UP := (round beta fexp Zceil).
Notation u := (pow (-p)).

Lemma fastTwoSum_bound a b (Fa: format a) (Fb : format b) rnd 
                   (valid_rnd: Valid_rnd rnd )(rndD: round_direct rnd) :
  (a <> 0 -> Rabs b <= Rabs a) ->
let h := round beta fexp rnd (a + b) in 
let z := round beta fexp rnd (h - a) in 
let l := round beta fexp rnd (b - z) in 
  Rabs (h + l - (a + b)) <= pow (1 - 2 * p) * Rabs (a + b) /\ 
 Rabs (h + l - (a + b)) <= pow (1 - 2 * p) * Rabs h.
Proof.
move=> blea.
set ex:= (1 - _)%Z.
case: (Req_dec a 0)=> [->|a_neq0].
  rewrite /= !(Rsimp01,(round_generic _ _ _ b), Rminus_eq_0,round_0) //.
  by move:(bpow_gt_0 beta ex); split_Rabs; nra.
have {} blea :  Rabs b <= Rabs a by apply/blea.
case: (Req_dec b 0)=> [->|b_neq0].
  rewrite /= !(Rsimp01,(round_generic _ _ _ a), Rminus_eq_0,round_0) //.
  by move:(bpow_gt_0 beta ex); split_Rabs; nra.
rewrite /=.
have z_exact: format(round beta fexp rnd (a + b) - a).
  apply/sma_exact=>//.
  by rewrite /cexp;apply/FLT_exp_monotone/mag_le_abs=> //.
rewrite (round_generic _ _ _ _ z_exact).
have-> : (b - (round beta fexp rnd (a + b) - a)) = 
   a + b -  (round beta fexp rnd (a + b)) by lra.
clear z_exact.
wlog apos: a b Fa Fb  blea a_neq0 b_neq0  rnd valid_rnd rndD/ 0 <= a.
  move=> Hwlog.
  case: (Rle_lt_dec 0 a) =>[apos | aneg].
    by apply/Hwlog.
  have HwlogUP:  forall a b : R,
          format a ->
          format b ->
          Rabs b <= Rabs a ->
          a <> 0 ->
          b <> 0 ->
          0 <= a ->
          Rabs
            (round beta fexp Zceil(a + b) +
             round beta fexp Zceil(a + b - round beta fexp Zceil(a + b)) -
             (a + b)) <= pow ex * Rabs (a + b) /\
          Rabs
            (round beta fexp Zceil(a + b) +
             round beta fexp Zceil (a + b - round beta fexp Zceil (a + b)) -
             (a + b)) <= pow ex * Rabs (round beta fexp Zceil (a + b)).
    by move=>*; apply/Hwlog=>//; right.
  have HwlogDN:  forall a b : R,
          format a ->
          format b ->
          Rabs b <= Rabs a ->
          a <> 0 ->
          b <> 0 ->
          0 <= a ->
          Rabs
            (round beta fexp Zfloor(a + b) +
             round beta fexp Zfloor(a + b - round beta fexp Zfloor(a + b)) -
             (a + b)) <= pow ex * Rabs (a + b) /\
          Rabs
            (round beta fexp Zfloor(a + b) +
             round beta fexp Zfloor (a + b - round beta fexp Zfloor (a + b)) -
             (a + b)) <= pow ex * Rabs (round beta fexp Zfloor (a + b)).
    by move=>*; apply/Hwlog=>//; left.
  have Fma : format (-a) by apply/generic_format_opp.
  have Fmb : format (-b) by apply/generic_format_opp.
  have Rb_le_Ra: Rabs (-b) <= Rabs (-a) by rewrite !Rabs_Ropp.
  have ma_neq0 : (-a) <> 0 by lra.
  have mb_neq0 : (-b) <> 0 by lra.
  have ma_pos: 0 <= -a by lra.
  have hE1: forall x y , - x -- y = - (x - y) by move=>*;  lra.
  have hE2: forall x y , - x + - y = - (x + y) by move=>*;  lra.
  have hE3: forall x y , - x  - y = - (x + y) by move=>*;  lra.
  move: (HwlogUP (-a) ( -b) Fma Fmb Rb_le_Ra ma_neq0 mb_neq0 
       ma_pos).
  move: (HwlogDN (-a) ( -b) Fma Fmb Rb_le_Ra ma_neq0 mb_neq0 
       ma_pos).
  by case: rndD=> RNE; rewrite !RNE
     !(round_DN_opp,round_UP_opp, hE1, hE2, hE3, Rabs_Ropp).
have {} apos: 0 < a by lra.
case: (Z_lt_le_dec (mag beta b + p) (mag beta  a))=> hmagabp; last first.
  have->: (a + b - round beta fexp rnd (a + b))= 
     b - round beta fexp rnd  (round beta fexp rnd (a + b) -a).
    rewrite (round_generic _ _ _ (_ -a)); first lra.
    apply/sma_exact =>//.
    by rewrite /cexp;apply/FLT_exp_monotone/mag_le_abs. 
 rewrite fastTwoSum_correct_mag // Rminus_eq_0 Rabs_R0.
  by move: (bpow_ge_0 beta ex) (Rabs_pos (a + b)) 
     (Rabs_pos (round beta fexp rnd (a + b))); nra.
have pow0 : pow 0 = 1 by [].
have pow1: pow 1 = 2 by [].
have powm1: pow (-1) = /2 by [].
have maga_lb: (emin + 1 <= mag beta a)%Z by apply/format_mag_ge_emin.
have magb_lb: (emin + 1 <= mag beta b)%Z by apply/format_mag_ge_emin.
have uba: Rabs b < (ulp a) /2.
  rewrite ulp_neq_0;last lra.
  rewrite/Rdiv  -powm1 -bpow_plus.
  apply/(Rlt_le_trans _ (pow (mag beta b))).
    apply/bpow_mag_gt.
  by apply/bpow_le; rewrite /cexp/fexp; lia.
case: (mag beta a)=> maga aB.
have {} aB:  pow (maga - 1) <=  a < pow maga  by  rewrite -(Rabs_pos_eq a); lra.
have magaE: maga = mag beta a by rewrite (mag_unique_pos _ _ maga).
pose t := (mag beta a -p)%Z.
have tE: (t = (mag beta a -p))%Z by [].
have ua: ulp a = pow t.
  rewrite ulp_neq_0 /cexp  /fexp ; last lra.
  congr bpow;  lia.
have : a <= pred beta fexp (pow maga).
  apply/pred_ge_gt=>//; last lra.
  by apply/generic_format_bpow; rewrite/fexp; lia.
rewrite pred_bpow {1}/fexp Z.max_l magaE -/t; last lia.
move=> a_uB.
have magb_uB : (mag beta b <= t -1)%Z by lia.
have b_uB: Rabs b < (pow t)/2.
  apply/(Rlt_le_trans _ (pow (mag beta b))); first by apply/bpow_mag_gt.
  rewrite /Rdiv -powm1 -bpow_plus.
  by apply/bpow_le; lia.
set x := round _ _ _ (a + b).
have powt_pos: 0 < pow t by apply/bpow_gt_0.
have powex_pos:= (bpow_gt_0 beta ex).
have Rabpos:= (Rabs_pos (a +b)).
have ab_B:  a - (pow t)/2 < a+b < a + (pow t) /2.
  by split_Rabs; lra.
have abB_bpos : 0 < b -> a < a + b < a + pow t / 2 by lra.
have abB_bneg :  b < 0 ->  a - pow t / 2 < a + b < a  by lra.
case:(Z_lt_le_dec (t + 1) emin)=> ht_emin.
  have xE: x = a + b .
    rewrite /x round_generic //.
    apply/Hauser=>//.
    apply/(Rle_trans  _ _ _ (Rabs_triang _ _)); rewrite Rabs_pos_eq ; last lra.
    apply(Rle_trans _ ( 2 * (pow (t + p)))).
      have -> :  2 * pow (t + p) =   pow (t + p)+  pow (t + p) by lra.
      rewrite (Rabs_pos_eq a) in blea; last lra.
      have->: (t+p = maga)%Z by lia.
      lra.
    by rewrite -pow1 -bpow_plus; apply/bpow_le; lia.
  by rewrite xE !(Rminus_eq_0, round_0, Rplus_0_r) Rabs_R0; nra.
case:blea =>blea; last first.
  suff: (mag beta b = (mag beta a):>Z)%Z by lia.
  rewrite (mag_unique beta b maga)=>//.
  by rewrite  (Rabs_pos_eq a) in blea; lra.
have ab_pos: 0 < a + b by  split_Rabs; lra.
have hn0:  x <> 0  by rewrite /x; apply/round_plus_neq_0=>//; lra.
have xpos: 0 < x .
  suff : 0 <= x by rewrite -/x in hn0;  lra.
  have->: 0 = round beta fexp rnd 0 by rewrite round_0.
  by apply/round_le; lra.
have casexE: x = a \/ x = a + pow t \/ x = a - pow t \/ 
     (x = a - (pow t) /2 /\ a = pow (t + p - 1) /\ (b < 0)).
  case :(Rle_lt_dec b 0)=>bcmp0; last first.
    have  {} abB_bpos : a < a + b < a + pow t / 2 by lra.
    have : round beta fexp rnd a <= x by apply/round_le; lra.
    rewrite round_generic //.
    case =>hxa; last first.
      by left.
    right;left.
    have succa: a + pow t = succ beta fexp a by rewrite succ_eq_pos; lra.
    rewrite succa; apply/Rle_antisym.
      have : a  + b <= a + pow t by lra.
      move/(round_le beta fexp rnd).
      by rewrite -/x succa round_generic //; apply/generic_format_succ.
    by apply/succ_le_lt=>//; apply/generic_format_round.
  have {} abB_bneg : a - pow t / 2 < a + b < a by lra.
  have : x <= round beta fexp rnd a by apply/round_le; lra.
  rewrite round_generic //.
  case =>hxa; last first.
    by left.
  right;right.
  have: pow (t + p - 1 ) <= a.
    suff ->: (t + p -1 = maga - 1)%Z by lra.
    lia.
  case=> hpa.
    left.
    have magpreda: pow (maga - 1) <= pred beta fexp a < pow maga.
      split.
        apply/pred_ge_gt=>//.
          apply/generic_format_bpow; rewrite  /fexp; lia.
        suff->:  (maga - 1 = t + p -1)%Z by lra.
        lia.
      apply/(Rlt_trans _ a); first (by apply/pred_lt_id); lra.
    have preda: a - pow t = pred beta fexp a .
      suff: pred beta fexp a + pow t = a by lra.
      suff ->: pow t = ulp (pred beta fexp a).
        by rewrite pred_plus_ulp.
      rewrite -ua !ulp_neq_0 /cexp; try lra.
        by congr bpow; congr fexp; rewrite !(mag_unique_pos _ _ maga).
      move: (bpow_gt_0 beta (maga -1)); lra.
    rewrite preda; apply/Rle_antisym.
      by apply/pred_ge_gt=>//; apply/generic_format_round.
    have: a - pow t <= a + b by lra.
    move/(round_le beta fexp rnd).
    by rewrite -/x preda round_generic //; apply/generic_format_pred.
  right.
  suff: x = a - pow t/2 by lra.
  have preda: a - pow t / 2= pred beta fexp a .
    rewrite -hpa pred_bpow /fexp Z.max_l; last lia.
    congr Rminus; rewrite /Rdiv  -powm1 -bpow_plus; congr bpow; lia.
   rewrite preda; apply/Rle_antisym.
      by apply/pred_ge_gt=>//; apply/generic_format_round.
    have: a - pow t /2 <= a + b by lra.
    move/(round_le beta fexp rnd).
    by rewrite -/x preda round_generic //; apply/generic_format_pred.
case: casexE=>[xa|casexE].
  rewrite xa; ring_simplify(a + b -a).
  by rewrite (round_generic _ _ _ b) // Rminus_eq_0 Rabs_R0 (Rabs_pos_eq a); nra.
case: casexE=>[xa|casexE].
  have bpos: 0 < b.
    case (Rle_lt_dec b 0)=>b0=>//.
    have :  a + b < a by lra.
    move/Rlt_le/(round_le beta fexp rnd (a + b) a).
    by rewrite -/x round_generic //; lra.
  have h: - pow t < b - pow t <  -(pow t)/2 by lra.
  have magbpt: pow ( t - 1) <= Rabs (b -pow t) < pow t.
    rewrite -Rabs_Ropp Rabs_pos_eq; last lra.
    by rewrite bpow_plus powm1; lra.
  have ->:  (x + round beta fexp rnd (a + b - x) - (a + b))= 
    round beta fexp rnd (b - pow t) - (b -pow t).
    rewrite xa.
    ring_simplify(a + b - (a + pow t)); ring.
  case:(Z_lt_le_dec (emin + p) t)=> htemin; last first.
    have Fe: format (b - pow t).
      apply/Hauser=>//.
        apply/generic_format_opp/generic_format_bpow.
        by rewrite/fexp;lia.
      apply/(Rle_trans _ (pow t)).
        have->: b + -(pow t ) = b-pow t by lra.
        lra.
      by apply/bpow_le; lia.
    rewrite round_generic // Rminus_eq_0 Rabs_R0.
    move:(bpow_ge_0 beta ex) (Rabs_pos (a + b)) (Rabs_pos x); nra.
  split;apply/(Rle_trans _ (ulp ( b - pow t))); try apply/error_le_ulp.
    rewrite /ex; apply/(Rle_trans _ ((pow (t + p -1)) * ( pow (1 - 2 * p)))).
      rewrite -bpow_plus;ring_simplify (t + p - 1 + (1 - 2 * p))%Z.
      rewrite ulp_neq_0; last lra.
      rewrite /cexp /fexp; apply/bpow_le.
      rewrite (mag_unique  _ _ t)// ;lia.
    rewrite Rmult_comm; apply/Rmult_le_compat_l.
      by apply/bpow_ge_0.
    apply/(Rle_trans _ a).
      have->:  (t + p - 1 = maga - 1)%Z by lia.
      lra.
    by rewrite Rabs_pos_eq; lra.
  rewrite  ulp_neq_0; last by lra.
  rewrite Rabs_pos_eq; last lra.
  apply/(Rmult_le_reg_l (pow (-ex))); first by apply/bpow_gt_0.
  rewrite -Rmult_assoc -!bpow_plus.
  have->: (-ex + ex  = 0)%Z by ring.
  rewrite pow0 Rmult_1_l xa /ex /cexp /fexp (mag_unique  _ _ t)// Z.max_l; last lia.
  have -> :  (- (1 - 2 * p) + (t - p) =  maga - 1)%Z by lia.
  lra.
case: casexE=>[xa|casexE].
  have bpos:  b < 0.
    case (Rle_lt_dec 0 b)=>b0=>//.
    have : a <=  a + b   by lra.
    move/(round_le beta fexp rnd a (a + b) ).
    by rewrite -/x round_generic //; lra.
  have h: (pow t)/2 < b +  pow t <  pow t  by lra.
  have magbpt: pow ( t - 1) <= b + pow t < pow t.
    by rewrite bpow_plus powm1;lra.
  have ->:  (x + round beta fexp rnd (a + b - x) - (a + b))= 
    round beta fexp rnd (b + pow t) - (b + pow t).
    rewrite xa.
    by ring_simplify(a + b - (a -  pow t)); ring.
  case:(Z_lt_le_dec (emin + p) t)=> htemin; last first.
    have Fe: format (b + pow t).
      apply/Hauser=>//.
        apply/generic_format_bpow.
        by rewrite/fexp;lia.
      apply/(Rle_trans _ (pow t)); last by apply/bpow_le; lia.
      by split_Rabs; lra.
    rewrite round_generic // Rminus_eq_0 Rabs_R0.
    move:(bpow_ge_0 beta ex) (Rabs_pos (a + b)) (Rabs_pos x); nra.
  have uE: ulp (b + pow t) = pow (t  - p ).
    rewrite ulp_neq_0; last lra.
    rewrite /cexp /fexp; congr bpow.
    by rewrite (mag_unique_pos  _ _ t)// ;lia.
  have:  pow (t + p - 1) <= a .
    suff->: (t + p - 1  = maga - 1)%Z by lra.
    lia.
  case=>ha; last first.
    have pa_uB: pred beta fexp a <= a + b.
      rewrite -ha pred_bpow/fexp Z.max_l ;last lia.
      ring_simplify (t + p - 1 - p)%Z.
      suff: -b <= pow (t -1) by lra.
      rewrite -(Rabs_pos_eq (-b)); last lra.
      by rewrite Rabs_Ropp bpow_plus powm1; lra.  
    have : round beta fexp rnd  (pred beta fexp a )<= x by rewrite /x; apply/round_le.
    rewrite round_generic; last by apply/generic_format_pred.
    rewrite -ha pred_bpow/fexp Z.max_l; last lia.
    ring_simplify (t + p - 1 - p)%Z.
    (* impossible *)
    by rewrite xa;lra. 
  have : succ beta fexp (pow (t + p - 1)) <= a.
    apply/succ_le_lt=>//.
    by apply/generic_format_bpow; rewrite /fexp;lia.
  rewrite succ_eq_pos; last by apply/bpow_ge_0.
  rewrite ulp_bpow/fexp Z.max_l;last lia.
  ring_simplify  (t + p - 1 + 1 - p)%Z.
  move=> {} ha.
  by split;apply/(Rle_trans _ (ulp ( b + pow t)));try apply/error_le_ulp;
    rewrite uE;
    apply/(Rmult_le_reg_l (pow (-ex))); try (by apply/bpow_gt_0);
    rewrite -!Rmult_assoc -!bpow_plus;
    ring_simplify(-ex + ex)%Z; rewrite pow0 Rmult_1_l /ex;
    (have->:  (- (1 - 2 * p) + (t - p) = t + p - 1)%Z by ring);
    rewrite Rabs_pos_eq; lra.
pose z := x - a.
have zE: z = - (pow t)/2  by rewrite /z ; lra.
have abx: a + b - x = b + pow t /2 by lra.
have {} abB_bneg :  a - pow t / 2 < a + b < a by lra.
have bB: - pow t /2 < b < 0 by lra.
have eB: 0 < b + pow t / 2 < pow t /2 by lra.
rewrite abx.
have ->: (x + round beta fexp rnd (b + pow t / 2) - (a + b)) = 
          round beta fexp rnd (b + pow t / 2)  - ( b + pow t /2) by lra.
case:(Z_lt_le_dec  (t - p -1) emin)=>htpmin.
  have Fbp2: format (b + pow t / 2).
    apply/Hauser=>//.
      rewrite /Rdiv -powm1 -bpow_plus.
      apply/generic_format_bpow; rewrite /fexp; lia.
    apply/(Rle_trans _ ((pow t) /2))=>//.
      by rewrite Rabs_pos_eq; lra.
    rewrite /Rdiv -powm1 -bpow_plus; apply/bpow_le; lia.
  rewrite round_generic // Rminus_eq_0 Rabs_R0.
  by move:(bpow_ge_0 beta ex) (Rabs_pos (a + b)) (Rabs_pos x); nra.
have ut4: ulp (pow t /4) = pow (t - p -1).
  rewrite ulp_neq_0; last by move: (bpow_gt_0 beta t); lra.
  have hpt4: pow t /4 = pow (t -2) by rewrite (bpow_plus _ t)  bpow_opp.
  rewrite hpt4/cexp/fexp mag_bpow; congr bpow.
  by rewrite Z.max_l; lia.
have haux: Rabs (round beta fexp rnd (b + pow t / 2) - (b + pow t / 2)) <= ulp (pow t /4).
  apply/(Rle_trans _ (ulp (b + pow t / 2))).
    by apply/error_le_ulp.
  rewrite ut4  ulp_neq_0; last by lra.
  apply/bpow_le; rewrite /cexp /fexp ; try lia.
  suff:  (mag beta (b + pow t / 2) <= t - 1)%Z by lia.
  apply/mag_le_bpow; try lra.
  by rewrite (bpow_plus _ t) powm1 Rabs_pos_eq; lra.
suff:  ulp (pow t / 4) <= pow ex * Rabs (a + b) /\  
       ulp (pow t / 4) <=  pow ex * Rabs x by lra.
have xlB: pow (t + p - 2) <= x <= a + b.
  split; last lra.
  case:( casexE ) => -> [-> b0].
  suff:   pow (t + p - 2) +  pow t / 2 <=  pow (t + p - 1) by lra.
  have->:  pow (t + p - 2) = pow (t + p -1) /2 .
    rewrite /Rdiv -powm1 -bpow_plus; congr bpow; lia.
  suff : pow t <= pow (t + p - 1) by lra.
  by apply/bpow_le; lia.
have hint: (- (1 - 2 * p) + (t - p - 1) = t + p - 2)%Z by ring.
by split;
  apply/(Rmult_le_reg_l (pow (-ex))); try (by apply/bpow_gt_0);
  rewrite -!Rmult_assoc -!bpow_plus;
  ring_simplify(-ex + ex)%Z; rewrite pow0 Rmult_1_l ut4 -bpow_plus /ex; 
  rewrite hint !Rabs_pos_eq; lra.
Qed.

End F2Sum.
End Main.




