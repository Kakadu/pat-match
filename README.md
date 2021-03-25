| Branch master         | FCPM branch        |
| ----------------------|--------------------|
| [![OCanren][1]][2]    | [![OCanren][3]][2] |

[1]:  https://github.com/Kakadu/pat-match/workflows/Build/badge.svg?branch=master
[2]:  https://github.com/Kakadu/pat-match/actions
[3]:  https://github.com/Kakadu/pat-match/workflows/Build/badge.svg?branch=fcpm


### Playground for OCanren and pattern matching

Running

Unnested version with manual patching (artefact for TEASE-LP 2020)

    make switch

Dependencies:

    opam pin add OCanren     https://github.com/kakadu/ocanren.git\#matching-paper
    opam pin add OCanren-ppx https://github.com/kakadu/ocanren.git\#matching-paper
