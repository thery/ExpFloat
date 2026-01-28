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
- [Algorithm FastTwoSum](./prelim.v#L563-L565)
- [Bounds on the error of FastTwoSum](./Fast2Sum_robust_flt.v#L944-L951)

Algorithm ExactMul  :
- [Algorithm ExactMult](./prelim.v#L498-L500)
- [Lemma 0](./prelim.v#L525-L528)

Algorithm FastSum  :
- [Algorithm FastSum](./prelim.v#L586-L587)
- [Lemma 1](./prelim.v#L728-L731)

Algorithm P1 : 
- [Algorithm P1](./algoP1.v#L354-L362)
- [Absolute error of Sollya polynomial](./algoP1.v#L148-L149)
- [Relative error of Sollya polynomial](./algoP1.v#L336-L338)
- [Bound of `ph` of algorithm P1](./algoP1.v#L1708-L1713)
- [Bound of `pl` of algorithm P1](./algoP1.v#L1730-L1735)
- [Absolute error of algorithm P1 (first part Lemma 2)](./algoP1.v#L1741-L1746)
- [Relative error of algorithm P1](./algoP1.v#L1752-L1758)
- [Refined relative error of algorithm P1 (second part Lemma 2)](./algoP1.v#L1765-L1771)

Algorithm Log1 :
- [Definition of the `INVERSE` table](./tableINVERSE.v#L47-L78)
- [Lemma 3](./tableINVERSE.v#L192-L197)   
- [Definition of the `LOGINV` table](./tableLOGINV.v#L107-L291)
- [Definition of Log1](./algoLog1.v#L227-L238)
- [Lemma 4](./algoLog1.v#L2506-L2512)

Algorithm Mul1 :
- [Definition of Mul1](./algoMul1.v#L67-L70)
- [Lemma 5](./algoMul1.v#L73-L84)

Algorithm Q1 :
- [Definition of the polynomial Q](./algoQ1.v#L127-L128)
- [Absolute error of the polynomial Q](./algoQ1.v#L130-L132)
- [Algorithm Q1](./algoQ1.v#L140-L144)
- [Lemma 6](./algoQ1.v#L148-L153)

Algorithm Exp1 :
- [table T1](./tableT1.v#L76-L142)
- [relative error for T1](./tableT1.v#L208-L211)
- [table T2](./tableT2.v#L76-L142)
- [relative error for T2](./tableT2.v#L209-L212)
- [algorithm Exp1](./algoExp1.v#L1847-L1875)
- [Lemma 7](./algoExp1.v#L1892-L1900)

Algorithm Phase1 :
- [algorithm Phase 1](./algoPhase1.v#L2106-L2116)
- [Theorem 1](./algoPhase1.v#L2120-L2122)

## Meta

- Author(s):
  - Laurent Théry
  - Laurence Rideau
- License: [MIT License](LICENSE)
- Compatible Rocq/Coq versions: 9.0 or later
- Additional dependencies:
  - [MathComp ssreflect 2.4.0 or later](https://math-comp.github.io)
  - [Coquelicot 3.4.3 or later](https://gitlab.inria.fr/coquelicot/coquelicot)
  - [MathComp algebra 2.4 or later](https://math-comp.github.io)
  - [Flocq 4.2.1 or later](https://gitlab.inria.fr/flocq/flocq)
  - [Interval 4.11.2 or later](https://gitlab.inria.fr/coqinterval/interval)
- Rocq/Coq namespace: `floatexp`
- Related publication(s): none

## Building and installation instructions

To build and install manually, do:

``` shell
git clone https://github.com/thery/expfloat.git
cd expfloat
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



