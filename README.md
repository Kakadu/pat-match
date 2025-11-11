[![Build aplas2020 4.14](https://github.com/Kakadu/pat-match/actions/workflows/aplas.yml/badge.svg?branch=aplas2020)](https://github.com/Kakadu/pat-match/actions/workflows/aplas.yml)
[![License](https://img.shields.io/badge/license-LGPL-blue)](https://github.com/Kakadu/pat-match/blob/master/LICENSE.LESSER)
[![Coverage Status](https://coveralls.io/repos/github/Kakadu/pat-match/badge.svg?branch=aplas2020)](https://coveralls.io/github/Kakadu/pat-match?branch=aplas2020)

[1]:  https://github.com/PLTools/OCanren/actions/workflows/master.yml/badge.svg
[2]:  https://github.com/PLTools/OCanren/actions

### Playground for OCanren and pattern matching

An artifact for [APLAS-2020 paper](https://link.springer.com/chapter/10.1007/978-3-030-64437-6_15).

Use `make bench` to run performance measurements and demos

Dependencies:

* `git submodule update --init`
* OCaml 4.14.x
    * `opam switch create 4.14.2+flambda --packages=ocaml-variants.4.14.2+options,ocaml-option-flambda --yes`
    * `opam exec -- opam install . --deps-only --with-tests`
