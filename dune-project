(lang dune 2.7)

(name pat-match)

(cram enable)

(maintainers "Dmitrii Kosarev https://github.com/Kakadu")

(bug_reports "https://github.com/Kakadu/pat-match/issues")

(license "LGPL-3.0-or-later")

(homepage "https://github.com/Kakadu/pat-match")

(generate_opam_files)

(package
 (name pat-match)
 (authors "Dmitrii Kosarev https://github.com/Kakadu")
 (synopsis
  "Synthesis of pattern mathcing compilation bia relational programmin (proof of concept)")
 (depends
  lazy-trie
  ocamlgraph
  ppx_optcomp
  ppx_expect
  (mtime
   (= 2.0.0))
  (dune :build)
  (ocamlformat :build)))
