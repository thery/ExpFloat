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

Algorithm P1 : 
- [Absolute error of Sollya polynomial](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L344-L346)
- [Relative error of Sollya polynomial](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L576-L579)
- [Bound of `ph` of algorithm P1](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L2066-L2071)
- [Bound of `pl` of algorithm P1](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L2077-L2082)
- [Absolute error of algorithm P1](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L2088-L2093)
- [Relative error of algorithm P1](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L2099-L2105)
- [Refined relative error of algorithm P1](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L2112-L2119)

Algorithm Log1 :
- [Definition of the `INVERSE` table](https://github.com/thery/ExpFloat/blob/7e29fe8f6b9e68fb838339663fdd01402e9d10f3/algoLog1.v#L107-L138)
- [Lemma 3](https://github.com/thery/ExpFloat/blob/7e29fe8f6b9e68fb838339663fdd01402e9d10f3/algoLog1.v#L344-L349)   

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



