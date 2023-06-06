From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition shrink k n := (n %/ 2 ^ k.+1) * 2 ^ k + n %% 2 ^ k.
Definition scalen k n := (n %/ 2 ^ k) * 2 ^ k.+1 + n %% 2 ^ k.

Lemma shrink_scalen_k k n : shrink k (scalen k n + 2 ^ k) = n.
Proof.
rewrite /shrink /scalen -addnA divnMDl ?expn_gt0 //.
rewrite [_ %/ 2 ^ _.+1]divn_small ?addn0; last first.
  by rewrite expnS mul2n -addnn ltn_add2r ltn_mod expn_gt0.
by rewrite addnA modnDr expnS mulnA modnMDl modn_mod -divn_eq.
Qed.

Lemma shrink_scalen k n : shrink k (scalen k n) = n.
Proof.
rewrite /shrink /scalen divnMDl ?expn_gt0 //.
rewrite [_ %/ 2 ^ _.+1]divn_small ?addn0; last first.
  apply: ltn_trans (_ : 2 ^ k < _); first by rewrite ltn_mod ?expn_gt0.
  by rewrite ltn_exp2l.
by rewrite expnS mulnA modnMDl modn_mod -divn_eq.
Qed.

Lemma scalen_shrink k n : scalen k (shrink k n) + (n %/ 2 ^ k) %% 2 * 2 ^k = n.
Proof.
rewrite /shrink /scalen divnMDl ?expn_gt0 //.
rewrite [(_ %/ 2 ^ k)%N]divn_small ?ltn_mod ?expn_gt0  // addn0.
rewrite modnMDl modn_mod.
rewrite addnAC {2}expnS mulnA -mulnDl.
rewrite [RHS](divn_eq n (2 ^ k)); congr (_ * _ + _).
by rewrite [RHS](divn_eq _ 2) -divnMA -expnSr.
Qed. 

Lemma scalen_lt_k k n m : k <= n -> m < 2 ^ n -> scalen k m + 2 ^ k < 2 ^ n.+1.
Proof.
move=> kLn nLn; rewrite /scalen.
apply : leq_ltn_trans (_ : (2 ^ (n - k)).-1 * 2 ^ k.+1 + (2 ^ k.+1).-1 < _).
  rewrite -addnA leq_add ?leq_mul2r ?expn_eq0 //= -ltnS prednK ?expn_gt0 //.
    by rewrite ltn_divLR ?expn_gt0 // -expnD subnK.
  by rewrite expnS mul2n -addnn ltn_add2r ltn_mod expn_gt0.
rewrite -addnS prednK ?expn_gt0 //.
apply: leq_trans (_ : (2 ^ (n - k)).-1 * 2 ^ k.+1 + 2 ^ k.+1 <= _).
  by rewrite leq_add2l leq_exp2l.
rewrite addnC -mulSn prednK ?expn_gt0 //.
by rewrite -expnD addnS subnK.
Qed.

Definition scalen_k_ord k n (m : 'I_(2 ^ n)) (kLn : k <= n) := 
  Ordinal (scalen_lt_k kLn (ltn_ord m)).

Lemma scalen_lt k n m : k <= n -> m < 2 ^ n -> scalen k m < 2 ^ n.+1.
Proof.
move=> kLn nLn.
by apply: leq_ltn_trans (scalen_lt_k kLn nLn); rewrite leq_addr.
Qed.

Definition scalen_ord k n (m : 'I_(2 ^ n)) (kLn : k <= n) := 
  Ordinal (scalen_lt kLn (ltn_ord m)).

Lemma shrink_lt k n m : k <= n -> m < 2 ^ n.+1 -> shrink k m < 2 ^n.
Proof.
move=> kLn nLn.
rewrite /shrink.
apply : leq_ltn_trans (_ : (2 ^ (n - k)).-1 * 2 ^ k + (2 ^ k).-1 < _).
  rewrite leq_add ?leq_mul2r ?expn_eq0 //= -ltnS prednK ?expn_gt0 //.
    by rewrite ltn_divLR ?expn_gt0 // -expnD addnS subnK.
  by rewrite ltn_mod expn_gt0.
rewrite -addnS prednK ?expn_gt0 // addnC -mulSn prednK ?expn_gt0 //.
by rewrite -expnD subnK.
Qed.

Definition shrink_ord (n k : nat) (m : 'I_(2 ^ n.+1)) (H : (k <= n)) := 
  Ordinal (shrink_lt H (ltn_ord m)).

Lemma scalen_mod_lt n m : scalen n m %% 2 ^ n.+1 < 2 ^ n.
Proof.
rewrite modnMDl modn_small ?ltn_mod ? (leq_trans (ltn_pmod _ _)) ?expn_gt0 //.
by rewrite leq_exp2l.
Qed.

Lemma scalen_mod_leq n m : 2 ^ n <= (scalen n m + 2 ^ n) %% 2 ^ n.+1.
Proof.
rewrite -addnA modnMDl modn_small ?ltn_mod ?
        (leq_trans (ltn_pmod _ _)) ?expn_gt0 ?leq_addl //.
by rewrite expnS mul2n -addnn ltn_add2r ltn_mod expn_gt0.
Qed.
