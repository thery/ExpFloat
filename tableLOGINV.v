Require Import ZArith Reals  Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
Require Import tableINVERSE.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TableLoginv.

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

Definition LOGINV : seq (R * R) := 
  [:: 
    (-0x1.5ff3070a79p-2, -0x1.e9e439f105039p-45);
    (-0x1.5a42ab0f4dp-2, 0x1.e63af2df7ba69p-50);
    (-0x1.548a2c3addp-2, -0x1.3167e63081cf7p-45);
    (-0x1.4ec97326p-2, -0x1.34d7aaf04d104p-45);
    (-0x1.4900680401p-2, 0x1.8bccffe1a0f8cp-44);
    (-0x1.432ef2a04fp-2, 0x1.fb129931715adp-44);
    (-0x1.404308686ap-2, -0x1.f8ef43049f7d3p-44);
    (-0x1.3a64c55694p-2, -0x1.7a71cbcd735dp-44);
    (-0x1.347dd9a988p-2, 0x1.5594dd4c58092p-45);
    (-0x1.2e8e2bae12p-2, 0x1.67b1e99b72bd8p-45);
    (-0x1.2895a13de8p-2, -0x1.a8d7ad24c13fp-44);
    (-0x1.22941fbcf8p-2, 0x1.a6976f5eb0963p-44);
    (-0x1.1f8ff9e48ap-2, -0x1.7946c040cbe77p-45);
    (-0x1.1980d2dd42p-2, -0x1.b7b3a7a361c9ap-45);
    (-0x1.136870293bp-2, 0x1.d3e8499d67123p-44);
    (-0x1.1058bf9ae5p-2, 0x1.4ab9d817d52cdp-44);
    (-0x1.0a324e2739p-2, -0x1.c6bee7ef4030ep-47);
    (-0x1.0402594b4dp-2, -0x1.036b89ef42d7fp-48);
    (-0x1.fb9186d5e4p-3, 0x1.d572aab993c87p-47);
    (-0x1.f550a564b8p-3, 0x1.323e3a09202fep-45);
    (-0x1.e8c0252aa6p-3, 0x1.6805b80e8e6ffp-45);
    (-0x1.e27076e2bp-3, 0x1.a342c2af0003cp-44);
    (-0x1.d5c216b4fcp-3, 0x1.1ba91bbca681bp-45);
    (-0x1.c8ff7c79aap-3, 0x1.7794f689f8434p-45);
    (-0x1.c2968558c2p-3, 0x1.cfd73dee38a4p-45);
    (-0x1.b5b519e8fcp-3, 0x1.4b722ec011f31p-44);
    (-0x1.af3c94e80cp-3, 0x1.a4e633fcd9066p-52);
    (-0x1.a23bc1fe2cp-3, 0x1.539cd91dc9f0bp-44);
    (-0x1.9bb362e7ep-3, 0x1.1f2a8a1ce0ffcp-45);
    (-0x1.8e928de886p-3, -0x1.a8154b13d72d5p-44);
    (-0x1.87fa06520cp-3, -0x1.22120401202fcp-44);
    (-0x1.7ab890210ep-3, 0x1.bdb9072534a58p-45);
    (-0x1.740f8f5404p-3, 0x1.0b66c99018aa1p-44);
    (-0x1.6d60fe719ep-3, 0x1.bc6e557134767p-44);
    (-0x1.5ff3070a7ap-3, 0x1.8586f183bebf2p-44);
    (-0x1.59338d9982p-3, -0x1.0ba68b7555d4ap-48);
    (-0x1.4ba36f39a6p-3, 0x1.4354bb3f219e5p-44);
    (-0x1.44d2b6ccb8p-3, 0x1.70cc16135783cp-46);
    (-0x1.3dfc2b0eccp-3, -0x1.8a72a62b8c13fp-45);
    (-0x1.303d718e48p-3, 0x1.680b5ce3ecb05p-50);
    (-0x1.29552f82p-3, 0x1.5b967f4471dfcp-44);
    (-0x1.2266f190a6p-3, 0x1.4d20ab840e7f6p-45);
    (-0x1.1478584674p-3, -0x1.563451027c75p-46);
    (-0x1.0d77e7cd08p-3, -0x1.cb2cd2ee2f482p-44);
    (-0x1.0671512ca6p-3, 0x1.a47579cdc0a3dp-45);
    (-0x1.f0a30c0118p-4, 0x1.d599e83368e91p-44);
    (-0x1.e27076e2bp-4, 0x1.a342c2af0003cp-45);
    (-0x1.d4313d66ccp-4, 0x1.9454379135713p-45);
    (-0x1.c5e548f5bcp-4, -0x1.d0c57585fbe06p-46);
    (-0x1.a926d3a4acp-4, -0x1.563650bd22a9cp-44);
    (-0x1.9ab4246204p-4, 0x1.8a64826787061p-45);
    (-0x1.8c345d6318p-4, -0x1.b20f5acb42a66p-44);
    (-0x1.7da766d7bp-4, -0x1.2cc844480c89bp-44);
    (-0x1.60658a9374p-4, -0x1.0c3b1dee9c4f8p-44);
    (-0x1.51b073f06p-4, -0x1.83f69278e686ap-44);
    (-0x1.42edcbea64p-4, -0x1.bc0eeea7c9acdp-46);
    (-0x1.341d7961bcp-4, -0x1.1d0929983761p-44);
    (-0x1.253f62f0ap-4, -0x1.416f8fb69a701p-44);
    (-0x1.16536eea38p-4, 0x1.47c5e768fa309p-46);
    (-0x1.f0a30c0118p-5, 0x1.d599e83368e91p-45);
    (-0x1.d276b8adbp-5, -0x1.6a423c78a64bp-46);
    (-0x1.b42dd71198p-5, 0x1.c827ae5d6704cp-46);
    (-0x1.95c830ec9p-5, 0x1.c148297c5feb8p-45);
    (-0x1.77458f633p-5, 0x1.181dce586af09p-44);
    (-0x1.58a5bafc9p-5, 0x1.b2b739570ad39p-45);
    (-0x1.39e87b9fe8p-5, -0x1.eafd480ad9015p-44);
    (-0x1.1b0d98924p-5, 0x1.3401e9ae889bbp-44);
    (-0x1.f829b0e78p-6, -0x1.980267c7e09e4p-45);
    (-0x1.b9fc027bp-6, 0x1.b9a010ae6922ap-44);
    (-0x1.7b91b07d6p-6, 0x1.3b955b602ace4p-44);
    (-0x1.3cea44347p-6, 0x1.6a2c432d6a40bp-44);
    (-0x1.fc0a8b0fcp-7, -0x1.f1e7cf6d3a69cp-50);
    (-0x1.7dc475f82p-7, 0x1.eb1245b5da1f5p-44);
    (-0x1.fe02a6b1p-8, -0x1.9e23f0dda40e4p-46);
    (0, 0);
    (0, 0);
    (0x1.812121458p-8, 0x1.ad50382973f27p-46);
    (0x1.41929f968p-7, 0x1.977c755d01368p-46);
    (0x1.c317384c8p-7, -0x1.41f33fcefb9fep-44);
    (0x1.228fb1feap-6, 0x1.713e3284991fep-45);
    (0x1.63d617869p-6, 0x1.7abf389596542p-47);
    (0x1.a55f548c6p-6, -0x1.de0709f2d03c9p-45);
    (0x1.e72bf2814p-6, -0x1.8d75149774d47p-45);
    (0x1.0415d89e78p-5, -0x1.dddc7f461c516p-44);
    (0x1.252f32f8dp-5, 0x1.83e9ae021b67bp-45);
    (0x1.466aed42ep-5, -0x1.c167375bdfd28p-45);
    (0x1.67c94f2d48p-5, 0x1.dac20827cca0cp-44);
    (0x1.894aa149f8p-5, 0x1.9a19a8be97661p-44);
    (0x1.aaef2d0fbp-5, 0x1.0fc1a353bb42ep-45);
    (0x1.bbcebfc69p-5, -0x1.7bf868c317c2ap-46);
    (0x1.dda8adc68p-5, -0x1.1b1ac64d9e42fp-45);
    (0x1.ffa6911ab8p-5, 0x1.3008c98381a8fp-45);
    (0x1.10e45b3cbp-4, -0x1.7cf69284a3465p-44);
    (0x1.2207b5c784p-4, 0x1.49d8cfc10c7bfp-44);
    (0x1.2aa04a447p-4, 0x1.7a48ba8b1cb41p-44);
    (0x1.3bdf5a7d2p-4, -0x1.19bd0ad125895p-44);
    (0x1.4d3115d208p-4, -0x1.53a2582f4e1efp-48);
    (0x1.55e10050ep-4, 0x1.c1d740c53c72ep-47);
    (0x1.674f089364p-4, 0x1.a79994c9d3302p-44);
    (0x1.78d02263d8p-4, 0x1.69b5794b69fb7p-47);
    (0x1.8197e2f41p-4, -0x1.c0fe460d20041p-44);
    (0x1.9335e5d594p-4, 0x1.3115c3abd47dap-45);
    (0x1.a4e7640b1cp-4, -0x1.e42b6b94407c8p-47);
    (0x1.adc77ee5bp-4, -0x1.573b209c31904p-44);
    (0x1.bf968769fcp-4, 0x1.4218c8d824283p-45);
    (0x1.d179788218p-4, 0x1.36433b5efbeedp-44);
    (0x1.da72763844p-4, 0x1.a89401fa71733p-46);
    (0x1.ec739830ap-4, 0x1.11fcba80cdd1p-44);
    (0x1.f57bc7d9p-4, 0x1.76a6c9ea8b04ep-46);
    (0x1.03cdc0a51ep-3, 0x1.81a9cf169fc5cp-44);
    (0x1.08598b59e4p-3, -0x1.7e5dd7009902cp-45);
    (0x1.1178e8227ep-3, 0x1.1ef78ce2d07f2p-45);
    (0x1.160c8024b2p-3, 0x1.ec2d2a9009e3dp-45);
    (0x1.1f3b925f26p-3, -0x1.5f74e9b083633p-46);
    (0x1.23d712a49cp-3, 0x1.00d238fd3df5cp-46);
    (0x1.2d1610c868p-3, 0x1.39d6ccb81b4a1p-47);
    (0x1.31b994d3a4p-3, 0x1.f098ee3a5081p-44);
    (0x1.3b08b6758p-3, -0x1.aade8f29320fbp-44);
    (0x1.3fb45a5992p-3, 0x1.19713c0cae559p-44);
    (0x1.4913d8333cp-3, -0x1.53e43558124c4p-44);
    (0x1.4dc7b897bcp-3, 0x1.c79b60ae1ff0fp-47);
    (0x1.5737cc9018p-3, 0x1.9baa7a6b887f6p-44);
    (0x1.5bf406b544p-3, -0x1.27023eb68981cp-46);
    (0x1.6574ebe8c2p-3, -0x1.98c1d34f0f462p-44);
    (0x1.6a399dabbep-3, -0x1.8f934e66a15a6p-44);
    (0x1.6f0128b756p-3, 0x1.577390d31ef0fp-44);
    (0x1.7898d85444p-3, 0x1.8e67be3dbaf3fp-44);
    (0x1.7d6903caf6p-3, -0x1.4c06b17c301d7p-45);
    (0x1.871213750ep-3, 0x1.328eb42f9af75p-44);
    (0x1.8beafeb39p-3, -0x1.73d54aae92cd1p-47);
    (0x1.90c6db9fccp-3, -0x1.935f57718d7cap-46);
    (0x1.9a8778debap-3, 0x1.470fa3efec39p-44);
    (0x1.9f6c40708ap-3, -0x1.337d94bcd3f43p-44);
    (0x1.a454082e6ap-3, 0x1.60a77c81f7171p-44);
    (0x1.ae2ca6f672p-3, 0x1.7a8d5ae54f55p-44);
    (0x1.b31d8575bcp-3, 0x1.c794e562a63cbp-44);
    (0x1.b811730b82p-3, 0x1.e90683b9cd768p-46);
    (0x1.bd087383bep-3, -0x1.d4bc4595412b6p-45);
    (0x1.c6ffbc6fp-3, 0x1.ee138d3a69d43p-44);
    (0x1.cc000c9db4p-3, -0x1.d6d585d57aff9p-46);
    (0x1.d1037f2656p-3, -0x1.84a7e75b6f6e4p-47);
    (0x1.db13db0d48p-3, 0x1.2806a847527e6p-44);
    (0x1.e020cc6236p-3, -0x1.52b00adb91424p-45);
    (0x1.e530effe72p-3, -0x1.fdbdbb13f7c18p-44);
    (0x1.ea4449f04ap-3, 0x1.5e91663732a36p-44);
    (0x1.f474b134ep-3, -0x1.bae49f1df7b5ep-44);
    (0x1.f991c6cb3cp-3, -0x1.90d04cd7cc834p-44);
    (0x1.feb2233eap-3, 0x1.f3418de00938bp-45);
    (0x1.01eae5626cp-2, 0x1.a43dcfade85aep-44);
    (0x1.047e60cde8p-2, 0x1.dbdf10d397f3cp-45);
    (0x1.09aa572e6cp-2, 0x1.b50a1e1734342p-44);
    (0x1.0c42d67616p-2, 0x1.7188b163ceae9p-45);
    (0x1.0edd060b78p-2, 0x1.019b52d8435f5p-47);
    (0x1.1178e8227ep-2, 0x1.1ef78ce2d07f2p-44);
    (0x1.14167ef367p-2, 0x1.e0c07824daaf5p-44);
    (0x1.16b5ccbadp-2, -0x1.23299042d74bfp-44);
    (0x1.1bf99635a7p-2, -0x1.1ac89575c2125p-44);
    (0x1.1e9e16788ap-2, -0x1.82eaed3c8b65ep-44);
    (0x1.214456d0ecp-2, -0x1.caf0428b728a3p-44);
    (0x1.23ec5991ecp-2, -0x1.6dbe448a2e522p-44);
    (0x1.269621134ep-2, -0x1.1b61f10522625p-44);
    (0x1.2941afb187p-2, -0x1.210c2b730e28bp-44);
    (0x1.2bef07cdc9p-2, 0x1.a9cfa4a5004f4p-45);
    (0x1.314f1e1d36p-2, -0x1.8e27ad3213cb8p-45);
    (0x1.3401e12aedp-2, -0x1.17c73556e291dp-44);
    (0x1.36b6776be1p-2, 0x1.16ecdb0f177c8p-46);
    (0x1.396ce359bcp-2, -0x1.5839c5663663dp-47);
    (0x1.3c25277333p-2, 0x1.83b54b606bd5cp-46);
    (0x1.3edf463c17p-2, -0x1.f067c297f2c3fp-44);
    (0x1.419b423d5fp-2, -0x1.ce379226de3ecp-44);
    (0x1.44591e053ap-2, -0x1.6e95892923d88p-47);
    (0x1.4718dc271cp-2, 0x1.06c18fb4c14c5p-44);
    (0x1.49da7f3bccp-2, 0x1.07b334daf4b9ap-44);
    (0x1.4c9e09e173p-2, -0x1.e20891b0ad8a4p-45);
    (0x1.4f637ebbaap-2, -0x1.fc158cb3124b9p-44);
    (0x1.522ae0738ap-2, 0x1.ebe708164c759p-45);
    (0x1.54f431b7bep-2, 0x1.a8954c0910952p-46);
    (0x1.57bf753c8dp-2, 0x1.fadedee5d40efp-46);
    (0x1.5a8cadbbeep-2, -0x1.7c79b0af7ecf8p-48);
    (0x1.5d5bddf596p-2, -0x1.a0b2a08a465dcp-47);
    (0x1.602d08af09p-2, 0x1.ebe9176df3f65p-46);
    (0x1.630030b3abp-2, -0x1.db623e731aep-45)
  ].

Definition FLOGINV : seq (float * float) := 

  [:: ({| Fnum := -1511610845817; Fexp := -42 |},
     {| Fnum := -8618262569963577; Fexp := -97 |});
    ({| Fnum := -1487177191245; Fexp := -42 |},
     {| Fnum := 8553853342956137; Fexp := -102 |});
    ({| Fnum := -1462607035101; Fexp := -42 |},
     {| Fnum := -5372756640668919; Fexp := -97 |});
    ({| Fnum := -5616792358; Fexp := -34 |},
     {| Fnum := -5433213875179780; Fexp := -97 |});
    ({| Fnum := -1413051057153; Fexp := -42 |},
     {| Fnum := 6963000948428684; Fexp := -96 |});
    ({| Fnum := -1388062089295; Fexp := -42 |},
     {| Fnum := 8920516397569453; Fexp := -96 |});
    ({| Fnum := -1375514159210; Fexp := -42 |},
     {| Fnum := -8882903711348691; Fexp := -96 |});
    ({| Fnum := -1350310385300; Fexp := -42 |},
     {| Fnum := -416104145843037; Fexp := -92 |});
    ({| Fnum := -1324961343880; Fexp := -42 |},
     {| Fnum := 6009165327990930; Fexp := -97 |});
    ({| Fnum := -1299465350674; Fexp := -42 |},
     {| Fnum := 6327820845788120; Fexp := -97 |});
    ({| Fnum := -1273820691944; Fexp := -42 |},
     {| Fnum := -467119253012799; Fexp := -92 |});
    ({| Fnum := -1248025623800; Fexp := -42 |},
     {| Fnum := 7434309047355747; Fexp := -96 |});
    ({| Fnum := -1235071132810; Fexp := -42 |},
     {| Fnum := -6637116109667959; Fexp := -97 |});
    ({| Fnum := -1209047113026; Fexp := -42 |},
     {| Fnum := -7735315459873946; Fexp := -97 |});
    ({| Fnum := -1182868187451; Fexp := -42 |},
     {| Fnum := 8231513562181923; Fexp := -96 |});
    ({| Fnum := -1169720056549; Fexp := -42 |},
     {| Fnum := 5818192504902349; Fexp := -96 |});
    ({| Fnum := -1143305283385; Fexp := -42 |},
     {| Fnum := -7999971424207630; Fexp := -99 |});
    ({| Fnum := -1116730903373; Fexp := -42 |},
     {| Fnum := -4563766196055423; Fexp := -100 |});
    ({| Fnum := -2179989951972; Fexp := -43 |},
     {| Fnum := 8258615103798407; Fexp := -99 |});
    ({| Fnum := -2153131631800; Fexp := -43 |},
     {| Fnum := 5387485115974398; Fexp := -97 |});
    ({| Fnum := -2099167701670; Fexp := -43 |},
     {| Fnum := 6333579980760831; Fexp := -97 |});
    ({| Fnum := -129503817259; Fexp := -39 |},
     {| Fnum := 7375713698054204; Fexp := -96 |});
    ({| Fnum := -2017595929852; Fexp := -43 |},
     {| Fnum := 4990209687709723; Fexp := -97 |});
    ({| Fnum := -1962791434666; Fexp := -43 |},
     {| Fnum := 6607306429006900; Fexp := -97 |});
    ({| Fnum := -1935260604610; Fexp := -43 |},
     {| Fnum := 509998340651172; Fexp := -93 |});
    ({| Fnum := -1879939082492; Fexp := -43 |},
     {| Fnum := 5830860150480689; Fexp := -96 |});
    ({| Fnum := -1852147296268; Fexp := -43 |},
     {| Fnum := 7404537573642342; Fexp := -104 |});
    ({| Fnum := -1796298898988; Fexp := -43 |},
     {| Fnum := 5974529589157643; Fexp := -96 |});
    ({| Fnum := -110515072638; Fexp := -39 |},
     {| Fnum := 5051880687144956; Fexp := -97 |});
    ({| Fnum := -1711855757446; Fexp := -43 |},
     {| Fnum := -7460550145307349; Fexp := -96 |});
    ({| Fnum := -1683526930956; Fexp := -43 |},
     {| Fnum := -5102971978384124; Fexp := -96 |});
    ({| Fnum := -1626594091278; Fexp := -43 |},
     {| Fnum := 7841237811022424; Fexp := -97 |});
    ({| Fnum := -1597988885508; Fexp := -43 |},
     {| Fnum := 4704177167108769; Fexp := -96 |});
    ({| Fnum := -1569290351006; Fexp := -43 |},
     {| Fnum := 7818512681879399; Fexp := -96 |});
    ({| Fnum := -1511610845818; Fexp := -43 |},
     {| Fnum := 6852633612250098; Fexp := -96 |});
    ({| Fnum := -1482628635010; Fexp := -43 |},
     {| Fnum := -4708558542560586; Fexp := -100 |});
    ({| Fnum := -1424376150438; Fexp := -43 |},
     {| Fnum := 5688098792020453; Fexp := -96 |});
    ({| Fnum := -1395104599224; Fexp := -43 |},
     {| Fnum := 6487949163460668; Fexp := -98 |});
    ({| Fnum := -1365735313100; Fexp := -43 |},
     {| Fnum := -6939199927796031; Fexp := -97 |});
    ({| Fnum := -1306700910152; Fexp := -43 |},
     {| Fnum := 6333967825292037; Fexp := -102 |});
    ({| Fnum := -4988415874; Fexp := -35 |},
     {| Fnum := 6114830641995260; Fexp := -96 |});
    ({| Fnum := -1247267623078; Fexp := -43 |},
     {| Fnum := 5860443016980470; Fexp := -97 |});
    ({| Fnum := -1187430024820; Fexp := -43 |},
     {| Fnum := -376257674116213; Fexp := -94 |});
    ({| Fnum := -1157357882632; Fexp := -43 |},
     {| Fnum := -8077893672563842; Fexp := -96 |});
    ({| Fnum := -1127182576806; Fexp := -43 |},
     {| Fnum := 7396791013870141; Fexp := -97 |});
    ({| Fnum := -2133039251736; Fexp := -44 |},
     {| Fnum := 8261311665704593; Fexp := -96 |});
    ({| Fnum := -129503817259; Fexp := -40 |},
     {| Fnum := 7375713698054204; Fexp := -97 |});
    ({| Fnum := -2010870802124; Fexp := -44 |},
     {| Fnum := 7113030514202387; Fexp := -97 |});
    ({| Fnum := -1949466949052; Fexp := -44 |},
     {| Fnum := -8176343608966662; Fexp := -98 |});
    ({| Fnum := -1826012505260; Fexp := -44 |},
     {| Fnum := -6020260152093340; Fexp := -96 |});
    ({| Fnum := -1763958874628; Fexp := -44 |},
     {| Fnum := 6938228254339169; Fexp := -97 |});
    ({| Fnum := -1701685584664; Fexp := -44 |},
     {| Fnum := -7636063907752550; Fexp := -96 |});
    ({| Fnum := -102449442171; Fexp := -40 |},
     {| Fnum := -5291418037831835; Fexp := -96 |});
    ({| Fnum := -1513532068724; Fexp := -44 |},
     {| Fnum := -4718768343860472; Fexp := -96 |});
    ({| Fnum := -90647772934; Fexp := -40 |},
     {| Fnum := -6825120308815978; Fexp := -96 |});
    ({| Fnum := -1386969033316; Fexp := -44 |},
     {| Fnum := -7811956739971789; Fexp := -98 |});
    ({| Fnum := -1323344421308; Fexp := -44 |},
     {| Fnum := -313400166463329; Fexp := -92 |});
    ({| Fnum := -78718054154; Fexp := -40 |},
     {| Fnum := -5654758159918849; Fexp := -96 |});
    ({| Fnum := -1195400686136; Fexp := -44 |},
     {| Fnum := 5766244692108041; Fexp := -98 |});
    ({| Fnum := -2133039251736; Fexp := -45 |},
     {| Fnum := 8261311665704593; Fexp := -97 |});
    ({| Fnum := -125215410907; Fexp := -41 |},
     {| Fnum := -398307691636299; Fexp := -94 |});
    ({| Fnum := -1873374810520; Fexp := -45 |},
     {| Fnum := 8024763701555276; Fexp := -98 |});
    ({| Fnum := -108926275273; Fexp := -41 |},
     {| Fnum := 7903850472537784; Fexp := -97 |});
    ({| Fnum := -100736235059; Fexp := -41 |},
     {| Fnum := 4927860347678473; Fexp := -96 |});
    ({| Fnum := -92515577801; Fexp := -41 |},
     {| Fnum := 7647599799610681; Fexp := -97 |});
    ({| Fnum := -1348225179624; Fexp := -45 |},
     {| Fnum := -8637576528105493; Fexp := -96 |});
    ({| Fnum := -75981490468; Fexp := -41 |},
     {| Fnum := 5418524749629883; Fexp := -96 |});
    ({| Fnum := -135335186040; Fexp := -42 |},
     {| Fnum := -7177777203513828; Fexp := -97 |});
    ({| Fnum := -7415267963; Fexp := -38 |},
     {| Fnum := 7769153639715370; Fexp := -96 |});
    ({| Fnum := -101889804246; Fexp := -42 |},
     {| Fnum := 5551802334489828; Fexp := -96 |});
    ({| Fnum := -85071250247; Fexp := -42 |},
     {| Fnum := 6371413037851659; Fexp := -96 |});
    ({| Fnum := -136376267004; Fexp := -43 |},
     {| Fnum := -8759246343874204; Fexp := -102 |});
    ({| Fnum := -102479912834; Fexp := -43 |},
     {| Fnum := 8639019011121653; Fexp := -96 |});
    ({| Fnum := -8556553905; Fexp := -40 |},
     {| Fnum := -7285634860990692; Fexp := -98 |}); 
    ({| Fnum := 0; Fexp := emin |},  
     {| Fnum := 0; Fexp := emin |}); 
    ({| Fnum := 0; Fexp := emin |},  
     {| Fnum := 0; Fexp := emin |}); 
    ({| Fnum := 103382389848; Fexp := -44 |},
     {| Fnum := 7552560447045415; Fexp := -98 |});
    ({| Fnum := 86321527144; Fexp := -43 |},
     {| Fnum := 7168572439663464; Fexp := -98 |});
    ({| Fnum := 121088738504; Fexp := -43 |},
     {| Fnum := -5663807681575422; Fexp := -96 |});
    ({| Fnum := 77996957674; Fexp := -42 |},
     {| Fnum := 6495790818759166; Fexp := -97 |});
    ({| Fnum := 95519078505; Fexp := -42 |},
     {| Fnum := 6662986934084930; Fexp := -99 |});
    ({| Fnum := 113111288006; Fexp := -42 |},
     {| Fnum := -8409548636095433; Fexp := -97 |});
    ({| Fnum := 130774149140; Fexp := -42 |},
     {| Fnum := -6992143565933895; Fexp := -97 |});
    ({| Fnum := 1117058014840; Fexp := -45 |},
     {| Fnum := -8406625192887574; Fexp := -96 |});
    ({| Fnum := 78701080461; Fexp := -41 |},
     {| Fnum := 6824234347247227; Fexp := -97 |});
    ({| Fnum := 87622079534; Fexp := -41 |},
     {| Fnum := -7905984500333864; Fexp := -97 |});
    ({| Fnum := 1545270668616; Fexp := -45 |},
     {| Fnum := 8352029952756236; Fexp := -96 |});
    ({| Fnum := 1689174231544; Fexp := -45 |},
     {| Fnum := 7214559562135137; Fexp := -96 |});
    ({| Fnum := 114604298491; Fexp := -41 |},
     {| Fnum := 4780789119824942; Fexp := -97 |});
    ({| Fnum := 119133699177; Fexp := -41 |},
     {| Fnum := -6684509062921258; Fexp := -98 |});
    ({| Fnum := 128220585064; Fexp := -41 |},
     {| Fnum := -4980428588573743; Fexp := -97 |});
    ({| Fnum := 2197522815672; Fexp := -45 |},
     {| Fnum := 5348628406737551; Fexp := -97 |});
    ({| Fnum := 73253893067; Fexp := -40 |},
     {| Fnum := -6701975018812517; Fexp := -96 |});
    ({| Fnum := 1245669869444; Fexp := -44 |},
     {| Fnum := 5802728384153535; Fexp := -96 |});
    ({| Fnum := 80161842247; Fexp := -40 |},
     {| Fnum := 6654844201978689; Fexp := -96 |});
    ({| Fnum := 84791371730; Fexp := -40 |},
     {| Fnum := -4956395163244693; Fexp := -96 |});
    ({| Fnum := 1431047623176; Fexp := -44 |},
     {| Fnum := -5974907296211439; Fexp := -100 |});
    ({| Fnum := 91772421390; Fexp := -40 |},
     {| Fnum := 7913683608127278; Fexp := -99 |});
    ({| Fnum := 1543219221348; Fexp := -44 |},
     {| Fnum := 7452048716804866; Fexp := -96 |});
    ({| Fnum := 1618399618008; Fexp := -44 |},
     {| Fnum := 6363249947090871; Fexp := -99 |});
    ({| Fnum := 103506915137; Fexp := -40 |},
     {| Fnum := -7898772899233857; Fexp := -96 |});
    ({| Fnum := 1731776075156; Fexp := -44 |},
     {| Fnum := 5367112377649114; Fexp := -97 |});
    ({| Fnum := 1807768357660; Fexp := -44 |},
     {| Fnum := -8517601861044168; Fexp := -99 |});
    ({| Fnum := 115367997019; Fexp := -40 |},
     {| Fnum := -6038183016077572; Fexp := -96 |});
    ({| Fnum := 1922375838204; Fexp := -44 |},
     {| Fnum := 5666387087475331; Fexp := -97 |});
    ({| Fnum := 1999197733400; Fexp := -44 |},
     {| Fnum := 5458197816000237; Fexp := -96 |});
    ({| Fnum := 2037734848580; Fexp := -44 |},
     {| Fnum := 7469257896433459; Fexp := -98 |});
    ({| Fnum := 132191453962; Fexp := -40 |},
     {| Fnum := 301252135144913; Fexp := -92 |});
    ({| Fnum := 8413497305; Fexp := -36 |},
     {| Fnum := 6590939215212622; Fexp := -98 |});
    ({| Fnum := 1115848484126; Fexp := -43 |},
     {| Fnum := 6784660808531036; Fexp := -96 |});
    ({| Fnum := 1135373670884; Fexp := -43 |},
     {| Fnum := -6726663694553132; Fexp := -97 |});
    ({| Fnum := 1174554550910; Fexp := -43 |},
     {| Fnum := 5048376738252786; Fexp := -97 |});
    ({| Fnum := 1194210632882; Fexp := -43 |},
     {| Fnum := 8658459335630397; Fexp := -97 |});
    ({| Fnum := 1233655062310; Fexp := -43 |},
     {| Fnum := -6182891491440179; Fexp := -98 |});
    ({| Fnum := 1253443806364; Fexp := -43 |},
     {| Fnum := 4518046015414108; Fexp := -98 |});
    ({| Fnum := 1293155354728; Fexp := -43 |},
     {| Fnum := 5521115153806497; Fexp := -99 |});
    ({| Fnum := 1313078563748; Fexp := -43 |},
     {| Fnum := 546014599204993; Fexp := -92 |});
    ({| Fnum := 84566304600; Fexp := -39 |},
     {| Fnum := -7509565408223483; Fexp := -96 |});
    ({| Fnum := 1373120387474; Fexp := -43 |},
     {| Fnum := 4951185698776409; Fexp := -96 |});
    ({| Fnum := 1413377176380; Fexp := -43 |},
     {| Fnum := -5979433429181636; Fexp := -96 |});
    ({| Fnum := 1433574873020; Fexp := -43 |},
     {| Fnum := 8015122121490191; Fexp := -99 |});
    ({| Fnum := 1474109935640; Fexp := -43 |},
     {| Fnum := 7242103637182454; Fexp := -96 |});
    ({| Fnum := 1494447732036; Fexp := -43 |},
     {| Fnum := -5189849156458524; Fexp := -98 |});
    ({| Fnum := 1535264942274; Fexp := -43 |},
     {| Fnum := -7190931487913058; Fexp := -96 |});
    ({| Fnum := 1555744795582; Fexp := -43 |},
     {| Fnum := -7029405040383398; Fexp := -96 |});
    ({| Fnum := 1576272443222; Fexp := -43 |},
     {| Fnum := 6042061429141263; Fexp := -96 |});
    ({| Fnum := 1617472017476; Fexp := -43 |},
     {| Fnum := 7008819219246911; Fexp := -96 |});
    ({| Fnum := 1638144396022; Fexp := -43 |},
     {| Fnum := -5841065726902743; Fexp := -97 |});
    ({| Fnum := 1679635477774; Fexp := -43 |},
     {| Fnum := 5393015463587701; Fexp := -96 |});
    ({| Fnum := 106278415161; Fexp := -39 |},
     {| Fnum := -6541358318300369; Fexp := -99 |});
    ({| Fnum := 1721323200460; Fexp := -43 |},
     {| Fnum := -7096202799142858; Fexp := -98 |});
    ({| Fnum := 1763209436858; Fexp := -43 |},
     {| Fnum := 359607477201977; Fexp := -92 |});
    ({| Fnum := 1784227590282; Fexp := -43 |},
     {| Fnum := -5409430976675651; Fexp := -96 |});
    ({| Fnum := 1805296086634; Fexp := -43 |},
     {| Fnum := 6203959062524273; Fexp := -96 |});
    ({| Fnum := 1847585076850; Fexp := -43 |},
     {| Fnum := 416222510665557; Fexp := -92 |});
    ({| Fnum := 1868806059452; Fexp := -43 |},
     {| Fnum := 8014676707926987; Fexp := -96 |});
    ({| Fnum := 1890078362498; Fexp := -43 |},
     {| Fnum := 8603026652452712; Fexp := -98 |});
    ({| Fnum := 1911402234814; Fexp := -43 |},
     {| Fnum := -8246081008964278; Fexp := -97 |});
    ({| Fnum := 7633615983; Fexp := -35 |},
     {| Fnum := 8691883486649667; Fexp := -96 |});
    ({| Fnum := 1975685782964; Fexp := -43 |},
     {| Fnum := -8283000615186425; Fexp := -98 |});
    ({| Fnum := 1997218457174; Fexp := -43 |},
     {| Fnum := -6837306442315492; Fexp := -99 |});
    ({| Fnum := 2040442588488; Fexp := -43 |},
     {| Fnum := 5207744557950950; Fexp := -96 |});
    ({| Fnum := 2062134567478; Fexp := -43 |},
     {| Fnum := -5958256425505828; Fexp := -97 |});
    ({| Fnum := 2083880173170; Fexp := -43 |},
     {| Fnum := -8967460896078872; Fexp := -96 |});
    ({| Fnum := 2105679671370; Fexp := -43 |},
     {| Fnum := 6167256877967926; Fexp := -96 |});
    ({| Fnum := 134340088654; Fexp := -39 |},
     {| Fnum := -7791456984988510; Fexp := -96 |});
    ({| Fnum := 2171404208956; Fexp := -43 |},
     {| Fnum := -7051188696303668; Fexp := -96 |});
    ({| Fnum := 137088873450; Fexp := -39 |},
     {| Fnum := 8783005686469515; Fexp := -97 |});
    ({| Fnum := 1107747496556; Fexp := -42 |},
     {| Fnum := 7392965775230382; Fexp := -96 |});
    ({| Fnum := 1118811770344; Fexp := -42 |},
     {| Fnum := 8371617331248956; Fexp := -97 |});
    ({| Fnum := 1141024173676; Fexp := -42 |},
     {| Fnum := 7688480573571906; Fexp := -96 |});
    ({| Fnum := 1152172586518; Fexp := -42 |},
     {| Fnum := 6500910116956905; Fexp := -97 |});
    ({| Fnum := 1163349330808; Fexp := -42 |},
     {| Fnum := 4531865570784757; Fexp := -99 |});
    ({| Fnum := 1174554550910; Fexp := -42 |},
     {| Fnum := 5048376738252786; Fexp := -96 |});
    ({| Fnum := 1185788392295; Fexp := -42 |},
     {| Fnum := 8457475691752181; Fexp := -96 |});
    ({| Fnum := 74815687597; Fexp := -38 |},
     {| Fnum := -5122182362264767; Fexp := -96 |});
    ({| Fnum := 1219663115687; Fexp := -42 |},
     {| Fnum := -4974780480233765; Fexp := -96 |});
    ({| Fnum := 1231012919434; Fexp := -42 |},
     {| Fnum := -6806727853389406; Fexp := -96 |});
    ({| Fnum := 1242392088812; Fexp := -42 |},
     {| Fnum := -8073731745720483; Fexp := -96 |});
    ({| Fnum := 1253800776172; Fexp := -42 |},
     {| Fnum := -6434223005295906; Fexp := -96 |});
    ({| Fnum := 1265239135054; Fexp := -42 |},
     {| Fnum := -4985319138141733; Fexp := -96 |});
    ({| Fnum := 1276707320199; Fexp := -42 |},
     {| Fnum := -5084978063925899; Fexp := -96 |});
    ({| Fnum := 1288205487561; Fexp := -42 |},
     {| Fnum := 7490948196992244; Fexp := -97 |});
    ({| Fnum := 1311292398902; Fexp := -42 |},
     {| Fnum := -7004416597114040; Fexp := -97 |});
    ({| Fnum := 1322881460973; Fexp := -42 |},
     {| Fnum := -4921909400447261; Fexp := -96 |});
    ({| Fnum := 1334501141473; Fexp := -42 |},
     {| Fnum := 4906904320047048; Fexp := -98 |});
    ({| Fnum := 1346151602620; Fexp := -42 |},
     {| Fnum := -6055681998415421; Fexp := -99 |});
    ({| Fnum := 1357833007923; Fexp := -42 |},
     {| Fnum := 6820634458242396; Fexp := -98 |});
    ({| Fnum := 1369545522199; Fexp := -42 |},
     {| Fnum := -8732854619941951; Fexp := -96 |});
    ({| Fnum := 1381289311583; Fexp := -42 |},
     {| Fnum := -8131408756073452; Fexp := -96 |});
    ({| Fnum := 1393064543546; Fexp := -42 |},
     {| Fnum := -6449016113085832; Fexp := -99 |});
    ({| Fnum := 1404871386908; Fexp := -42 |},
     {| Fnum := 4622454178452677; Fexp := -96 |});
    ({| Fnum := 1416710011852; Fexp := -42 |},
     {| Fnum := 4639059904252826; Fexp := -96 |});
    ({| Fnum := 1428580589939; Fexp := -42 |},
     {| Fnum := -8480022537623716; Fexp := -97 |});
    ({| Fnum := 1440483294122; Fexp := -42 |},
     {| Fnum := -8938311388308665; Fexp := -96 |});
    ({| Fnum := 1452418298762; Fexp := -42 |},
     {| Fnum := 8653639717799769; Fexp := -97 |});
    ({| Fnum := 1464385779646; Fexp := -42 |},
     {| Fnum := 7469346495465810; Fexp := -98 |});
    ({| Fnum := 1476385913997; Fexp := -42 |},
     {| Fnum := 8916961695973615; Fexp := -98 |});
    ({| Fnum := 1488418880494; Fexp := -42 |},
     {| Fnum := -6693393182223608; Fexp := -100 |});
    ({| Fnum := 1500484859286; Fexp := -42 |},
     {| Fnum := -7330624556000732; Fexp := -99 |});
    ({| Fnum := 1512584032009; Fexp := -42 |},
     {| Fnum := 8653781275197285; Fexp := -98 |});
    ({| Fnum := 1524716581803; Fexp := -42 |},
     {| Fnum := -32668123607470; Fexp := -89 |})].

Lemma map_FLOGINV : [seq (F2R i.1, F2R i.2) | i <- FLOGINV] = LOGINV.
Proof.
do 90 (congr [:: (_, _), (_, _) & _];
  [rewrite /F2R /= /Z.pow_pos /=; lra|
  rewrite /F2R /= /Z.pow_pos /=; lra|
  rewrite /F2R /= /Z.pow_pos /=; lra|
  rewrite /F2R /= /Z.pow_pos /=; lra|
   idtac]).
by do 2 (congr [:: (_, _) & _]; try by rewrite /F2R /= /Z.pow_pos /=; lra).
Qed.

Lemma format_LOGINV x : x \in LOGINV -> format x.1 /\ format x.2.
Proof.
rewrite -map_FLOGINV.
have F y z l :
   format y -> format z -> (x \in l -> format x.1 /\ format x.2) ->
  (x \in [:: (y, z) & l] -> format x.1 /\ format x.2).
  by move=> Fy Fz IH; rewrite in_cons => /orP[/eqP->|/IH//].
do 181 (apply: (F); 
  [(by apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _)|
    by apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _ | idtac]).
by apply: F => //;
  apply: generic_format_FLT; apply: FLT_spec (refl_equal _) _ _.
Qed.

Lemma size_LOGINV : size LOGINV = 182%N.
Proof. by []. Qed.

Lemma size_FLOGINV : size FLOGINV = 182%N.
Proof. by []. Qed.

Lemma l1_LOGINV i : 
  (i < size LOGINV)%N ->  
  let r := nth 1 INVERSE i in
  let l1 := (nth (1,1) LOGINV i).1 in
  let l2 := (nth (1,1) LOGINV i).2 in
  [/\ is_imul l1 (pow (- 42)), is_imul l2 (pow (- 104)),
      l1 <> 0 -> 0.00587 < Rabs l1 < 0.347,
      l2 <> 0 ->  pow (- 52) < Rabs l2 < pow (- 43) &
      Rabs (l1 + l2 - (- ln r)) <= pow (- 97)].
Proof. 
move=> Hi r l1 l2; rewrite {}/r {}/l1 {}/l2; move: Hi.
rewrite -map_FLOGINV [size _]/=.
have F1 x : IPR_2 x = 2 * IPR x.
  by elim: x => //=; rewrite /IPR /=; lra.
have F2 x y : F2R (Float beta (Z.neg (xO x)) y) =
                 (Float beta (Z.neg x) (1 + y)).
  by rewrite /F2R ![Fnum _]/= /IZR {1}/IPR F1 /F2R /Fexp bpow_plus /= 
             /Z.pow_pos /=; lra.
have F3 x y : F2R (Float beta (Z.pos (xO x)) y) =
                 (Float beta (Z.pos x) (1 + y)).
  by rewrite /F2R ![Fnum _]/= /IZR {1}/IPR F1 /F2R /Fexp bpow_plus /= 
             /Z.pow_pos /=; lra.
do 74 (case: i => [_|i]; first by 
  rewrite 2![nth _ _ _]/= /fst /snd;
   split; 
   [rewrite ?F2; apply: imul_fexp_le => /=; lia |
    rewrite ?F2; apply: imul_fexp_le => /=; lia |
    move=> _; rewrite /F2R /= /Z.pow_pos /=; split_Rabs; lra |
    move=> _; rewrite /F2R /= /Z.pow_pos /=; split_Rabs; lra |
    rewrite /F2R /= /Z.pow_pos /=; interval with (i_prec 100)]).
do 2 (case: i => [_|i]; first by 
  rewrite 2![nth _ _ _]/= /fst /snd;
   split;
  [ exists 0%Z; rewrite /F2R /=; lra |
    exists 0%Z; rewrite /F2R /=; lra |
    case; rewrite /F2R /= /Z.pow_pos /=; lra |
    case; rewrite /F2R /= /Z.pow_pos /=; lra |
    rewrite /F2R /= /Z.pow_pos /=; interval with (i_prec 100)]
    ).
do 106 (case: i => [_|i]; first by 
  rewrite 2![nth _ _ _]/= /fst /snd;
   split; 
   [rewrite ?F3; apply: imul_fexp_le => /=; lia |
    rewrite ?F3; apply: imul_fexp_le => /=; lia |
    move=> _; rewrite /F2R /= /Z.pow_pos /=; split_Rabs; lra |
    move=> _; rewrite /F2R /= /Z.pow_pos /=; split_Rabs; lra |
    rewrite /F2R /= /Z.pow_pos /=; interval with (i_prec 150)]).
by [].
Qed.

End TableLoginv.

