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
- [Bounds on the error of FastTwoSum](./Fast2Sum_robust_flt.v#L1050-L1057)

Algorithm P1 : 
- [Algotiyhm P1](./algoP1.v#L358-L366)
- [Absolute error of Sollya polynomial](./algoP1.v#L151-L152)
- [Relative error of Sollya polynomial](./algoP1.v#L340-L342)
- [Bound of `ph` of algorithm P1](./algoP1.v#L1711-L1716)
- [Bound of `pl` of algorithm P1](./algoP1.v#L1733-L1738)
- [Absolute error of algorithm P1](./algoP1.v#L1744-L1749)
- [Relative error of algorithm P1](./algoP1.v#L1755-L1761)
- [Refined relative error of algorithm P1](./algoP1.v#L1768-L1774)

Algorithm Log1 :
- [Definition of the `INVERSE` table](./tableINVERSE.v#L48-L79)
- [Lemma 3](./tableINVERSE.v#L284-L289)   
- [Definition of the `LOGINV` table](./tableLOGINV.v#L108-L292)
- [Definition of Log1](./algoLog1.v#L172-L183)
- [Lemma 4](./algoLog1.v#L2585-L2591)

## Meta

- Author(s):
  - Laurent Théry
  - Laurence Rideau
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.17 or later
- Additional dependencies:
  - [MathComp ssreflect 1.17 or later](https://math-comp.github.io)
  - [Coquelicot 3.3.1 or later](https://gitlab.inria.fr/coquelicot/coquelicot)
  - [MathComp algebra 1.17 or later](https://math-comp.github.io)
  - [Flocq 4.1.1 or later](https://gitlab.inria.fr/flocq/flocq)
  - [Interval 4.7.0 or later](https://gitlab.inria.fr/coqinterval/interval)
- Coq namespace: `floatexp`
- Related publication(s): none

## Building and installation instructions

To build and install manually, do:

``` shell
git clone https://github.com/thery/expfloat.git
cd expfloat
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



