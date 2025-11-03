### Playground for OCanren and pattern matching

Running

Unnested version with manual patching (artefact for APLAS-2020)

    make switch

Dependencies:

* `git submodule update --init`
* OCaml 4.14.x
    * `opam switch create 4.14.2+flambda --packages=ocaml-variants.4.14.2+options,ocaml-option-flambda --yes`
    * `opam exec -- opam install . --deps-only --with-tests`
