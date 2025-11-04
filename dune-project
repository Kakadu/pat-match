(lang dune 3.7)

(name pat-match)

(cram enable)

(maintainers "Dmitrii Kosarev https://github.com/Kakadu")

(bug_reports "https://github.com/Kakadu/pat-match/issues")

(license "LGPL-3.0-or-later")

(homepage "https://github.com/Kakadu/pat-match")

(generate_opam_files)

(package
 (name pat-match)
 (allow_empty)
 (authors "Dmitrii Kosarev https://github.com/Kakadu")
 (synopsis
  "Synthesis of pattern mathcing compilation bia relational programmin (proof of concept)")
 (depends
  (dune :build)
  lazy-trie
  ocamlgraph
  ppx_optcomp
  ppx_expect
  (mtime
   (= 2.1.0))
  (ocamlformat
   (and
    (= 0.28.1)
    :build))))
