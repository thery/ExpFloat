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
- [Absolute error of Sollya polynomial](https://github.com/thery/ExpFloat/blob/e12afe8dd40ae8aac31915c839f13a6729392f6e/exp.v#L344-L346)
- [Relative error of Sollya polynomial](https://github.com/thery/ExpFloat/blob/e12afe8dd40ae8aac31915c839f13a6729392f6e/exp.v#L576-L579)
- [Bound of `ph` of algorithm P1](https://github.com/thery/ExpFloat/blob/e12afe8dd40ae8aac31915c839f13a6729392f6e/exp.v#L2090-L2095)
- [Bound of `pl` of algorithm P1](https://github.com/thery/ExpFloat/blob/e12afe8dd40ae8aac31915c839f13a6729392f6e/exp.v#L2101-L2106)
- [Absolute error of algorithm P1](https://github.com/thery/ExpFloat/blob/e12afe8dd40ae8aac31915c839f13a6729392f6e/exp.v#L2112-L2117)
- [Relative error of algorithm P1](https://github.com/thery/ExpFloat/blob/e12afe8dd40ae8aac31915c839f13a6729392f6e/exp.v#L2123-L2129)
- [Refined relative error of algorithm P1](https://github.com/thery/ExpFloat/blob/e12afe8dd40ae8aac31915c839f13a6729392f6e/exp.v#L2136-L2142)

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
- Coq namespace: `exp`
- Related publication(s): none

## Building and installation instructions


To build and install manually, do:

``` shell
git clone https://github.com/thery/expfloat.git
cd expfloat
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



