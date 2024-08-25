(lang dune 2.7)

(name pat-match)

(cram enable)

(generate_opam_files)

(package
 (name pat-match)
 (depends
  lazy-trie
  ocamlgraph
  ppx_optcomp
  ppx_expect
  (mtime
   (= 2.0.0))
  (dune :build)
  (ocamlformat :build)))
