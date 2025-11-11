[![Build aplas2020-rework 4.14](https://github.com/Kakadu/pat-match/actions/workflows/aplas.yml/badge.svg?branch=aplas2020-rework)](https://github.com/Kakadu/pat-match/actions/workflows/aplas.yml)
[![License](https://img.shields.io/badge/license-LGPL-blue)](https://github.com/Kakadu/pat-match/blob/master/LICENSE.LESSER)
[![Coverage Status](https://coveralls.io/repos/github/Kakadu/pat-match/badge.svg?branch=aplas2020-rework)](https://coveralls.io/github/Kakadu/pat-match?branch=aplas2020-rework)

[1]:  https://github.com/PLTools/OCanren/actions/workflows/master.yml/badge.svg
[2]:  https://github.com/PLTools/OCanren/actions

### Playground for OCanren and pattern matching

Running

Unnested version with manual patching (artifact for APLAS-2020)

    make bench

Dependencies:

* `git submodule update --init`
* OCaml 4.14.x
    * `opam switch create 4.14.2+flambda --packages=ocaml-variants.4.14.2+options,ocaml-option-flambda --yes`
    * `opam exec -- opam install . --deps-only --with-tests`
