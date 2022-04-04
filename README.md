| Branch master           | FCPM branch          | 4.12.1 compiler      |
| ------------------------|----------------------|----------------------|
| [![pat-match][2]][1]    | [![pat-match][3]][1] | [![pat-match][4]][1] |

[1]:  https://github.com/Kakadu/pat-match/actions
[2]:  https://github.com/Kakadu/pat-match/workflows/Build_master/badge.svg?branch=master
[3]:  https://github.com/Kakadu/pat-match/workflows/Build_FCPM/badge.svg?branch=fcpm
[4]:  https://github.com/Kakadu/pat-match/workflows/Build_4.12.1/badge.svg?branch=master


### Playground for OCanren and pattern matching



Dependencies:

  opam install streaming z3 ocamlformat ppx_optcomp GT lazy-trie mtime ppx_expect --yes
  pin add noCanren --dev-repo --yes
  git clone git@github.com:Kakadu/OCanren.git\#wildcard+fd+diseq2
  
Run `make` to compile and run something...