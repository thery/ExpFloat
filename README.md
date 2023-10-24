<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# ExpFloat

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/expfloat/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/expfloat/actions?query=workflow:"Docker%20CI"





Exponential in binary 64 

Progress

Algorithm FastTwoSum : 
- [Bounds on the error of FastTwoSum](./Fast2Sum_robust_flt.v#L946-L953)

Algorithm P1 : 
- [Algotiyhm P1](./algoP1.v#L356-L364)
- [Absolute error of Sollya polynomial](./algoP1.v#L150-L151)
- [Relative error of Sollya polynomial](./algoP1.v#L338-L340)
- [Bound of `ph` of algorithm P1](./algoP1.v#L1710-L1715)
- [Bound of `pl` of algorithm P1](./algoP1.v#L1732-L1737)
- [Absolute error of algorithm P1](./algoP1.v#L1743-L1748)
- [Relative error of algorithm P1](./algoP1.v#L1754-L1760)
- [Refined relative error of algorithm P1](./algoP1.v#L1767-L1773)

Algorithm Log1 :
- [Definition of the `INVERSE` table](./tableINVERSE.v#L47-L78)
- [Lemma 3](./tableINVERSE.v#L192-L197)   
- [Definition of the `LOGINV` table](./tableLOGINV.v#L107-L291)
- [Definition of Log1](./algoLog1.v#L227-L238)
- [Lemma 4](./algoLog1.v#L2508-L2514)

Algorithm Mul1 :
- [Definition of Mul1](./algoMul1.v#L67-L70)
- [Lemma 5](./algoMul1.v#L73-L84)

Algorithm Q1 :
- [Definition of the polynomial Q](./algoQ1.v#L127-L128)
- [Absolute error of the polynomial Q](./algoQ1.v#L130-L132)
- [Algorithm Q1](./algoQ1.v#L145-L149)
- [Lemma 6](./algoQ1.v#L153-L158)

Algorithm Exp1 :
- [table T1](./tableT1.v#L76-L142)
- [relative error for T1](./tableT1.v#L208-L211)
- [table T2](./tableT2.v#L76-L142)
- [relative error for T2](./tableT2.v#L209-L212)
- [algorithm Exp1](./algoExp1.v#L1848-L1876)
- [Lemma 7](./algoExp1.v#L1893-L1901)

Algorithm Phase1 :
- [algorithm Phase 1](./algoPhase1.v#L2144-L2154)
- [Theorem 1](./algoPhase1.v#L2158-L2160)

## Meta

- Author(s):
  - Laurent Théry
  - Laurence Rideau
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.18 or later
- Additional dependencies:
  - [MathComp ssreflect 1.17 or later](https://math-comp.github.io)
  - [Coquelicot 3.4.0 or later](https://gitlab.inria.fr/coquelicot/coquelicot)
  - [MathComp algebra 1.17 or later](https://math-comp.github.io)
  - [Flocq 4.1.3 or later](https://gitlab.inria.fr/flocq/flocq)
  - [Interval 4.8.1 or later](https://gitlab.inria.fr/coqinterval/interval)
- Coq namespace: `floatexp`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of ExpFloat
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-expfloat
```

To instead build and install manually, do:

``` shell
git clone https://github.com/thery/expfloat.git
cd expfloat
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



