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
- [Absolute error of Sollya polynomial](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L344-L346)
- [Relative error of Sollya polynomial](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L576-L579)
- [Bound of `ph` of algorithm P1](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L2066-2071)
- [Bound of `pl` of algorithm P1](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L2077-2082)
- [Absolute error of algorithm P1](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L2088-2093)
- [Relative error of algorithm P1](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L2123-2129)
- [Refined relative error of algorithm P1](https://github.com/thery/ExpFloat/blob/f9a2fa5548a7a67f99c35514041a3d3b422d50f6/algoP1.v#L2112-2119)

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



