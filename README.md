<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# ExpFloat

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/expfloat/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/expfloat/actions/workflows/docker-action.yml





Exponential in binary 64 

Algorithm FastTwoSum : 
- [Algorithm FastTwoSum](./prelim.v#L562-L564 "fastTwoSum")
- [Bounds on the error of FastTwoSum](./Fast2Sum_robust_flt.v#L944-L951 "FastTwoSum_bound")

Algorithm ExactMul  :
- [Algorithm ExactMult](./prelim.v#L497-L499 "exactMul")
- [Lemma 0](./prelim.v#L525-L526 "error_exactMul")

Algorithm FastSum  :
- [Algorithm FastSum](./prelim.v#L585-L586 "fastSum")
- [Lemma 1](./prelim.v#L727-L730 "fastSum_correct")

Algorithm P1 : 
- [Algorithm P1](./algoP1.v#L354-L362 "p1")
- [Absolute error of Sollya polynomial](./algoP1.v#L148-L149 "P_abs_error")
- [Relative error of Sollya polynomial](./algoP1.v#L336-L338 "P_rel_error")
- [Bound of `ph` of algorithm P1](./algoP1.v#L1708-L1713 "ph_bound_p1")
- [Bound of `pl` of algorithm P1](./algoP1.v#L1730-L1735 "pl_bound_p1")
- [Absolute error of algorithm P1 (first part Lemma 2)](./algoP1.v#L1741-L1746 "absolute_error_p1")
- [Relative error of algorithm P1](./algoP1.v#L1752-L1758 "rel_error_p1")
- [Refined relative error of algorithm P1 (second part Lemma 2)](./algoP1.v#L1765-L1771 "rel_error_32_p1")

Algorithm Log1 :
- [Definition of the `INVERSE` table](./tableINVERSE.v#L47-L78 "INVERSE")
- [Lemma 3](./tableINVERSE.v#L192-L197 "rt_float")   
- [Definition of the `LOGINV` table](./tableLOGINV.v#L107-L291 "LOGINV")
- [Definition of Log1](./algoLog1.v#L227-L238 "log1")
- [Lemma 4](./algoLog1.v#L2506-L2512 "err_lem4")

Algorithm Mul1 :
- [Definition of Mul1](./algoMul1.v#L67-L70 "mul1")
- [Lemma 5](./algoMul1.v#L73-L84 "err_lem5")

Algorithm Q1 :
- [Definition of the polynomial Q](./algoQ1.v#L127-L128 "Q")
- [Absolute error of the polynomial Q](./algoQ1.v#L130-L132 "Q_abs_error")
- [Algorithm Q1](./algoQ1.v#L140-L144 "q1")
- [Lemma 6](./algoQ1.v#L148-L153 "err_lem6")

Algorithm Exp1 :
- [table T1](./tableT1.v#L76-L142 "T1")
- [relative error for T1](./tableT1.v#L208-L211 "T1_rel_error_h2l2")
- [table T2](./tableT2.v#L76-L142 "T2")
- [relative error for T2](./tableT2.v#L209-L212 "T2_rel_error_h1l1")
- [algorithm Exp1](./algoExp1.v#L1846-L1874 "exp1")
- [Lemma 7](./algoExp1.v#L1891-L1899 "err_lem7")

Algorithm Phase1 :
- [algorithm Phase 1](./algoPhase1.v#L2104-L2114 "phase1")
- [Theorem 1](./algoPhase1.v#L2118-L2120 "phase1_thm1")

## Meta

- Author(s):
  - Laurent Théry
  - Laurence Rideau
- License: [MIT License](LICENSE)
- Compatible Rocq/Coq versions: 9.2 or later
- Additional dependencies:
  - [MathComp ssreflect 2.6.0 or later](https://math-comp.github.io)
  - [Coquelicot 3.4.5 or later](https://gitlab.inria.fr/coquelicot/coquelicot)
  - [Flocq 4.2.2 or later](https://gitlab.inria.fr/flocq/flocq)
  - [Interval 4.11.5 or later](https://gitlab.inria.fr/coqinterval/interval)
- Rocq/Coq namespace: `floatexp`
- Related publication(s): none

## Building and installation instructions

To build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/thery/expfloat.git
cd expfloat
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



