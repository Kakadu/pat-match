#!/bin/bash
#set -ex
cvc4=cvc4
bench="$1"

# Output other than "sat"/"unsat" is either written to stderr or to "err.log"
# in the directory specified by $2 if it has been set (e.g. when running on
# StarExec).
out_file=/dev/stderr

if [ -n "$STAREXEC_WALLCLOCK_LIMIT" ]; then
  # If we are running on StarExec, don't print to `/dev/stderr/` even when $2
  # is not provided.
  out_file="/dev/null"
fi

if [ -n "$2" ]; then
  out_file="$2/err.log"
fi

logic=$(expr "$(grep -m1 '^[^;]*set-logic' "$bench")" : ' *(set-logic  *\([A-Z_]*\) *) *$')

# use: trywith [params..]
# to attempt a run.  Only thing printed on stdout is "sat" or "unsat", in which
# case this run script terminates immediately.  Otherwise, this function
# returns normally and prints the output of the solver to $out_file.
function trywith {
  limit=$1; shift;
  result="$({ ulimit -S -t "$limit"; $cvc4 -L smt2.6 --no-incremental --no-type-checking --no-interactive "$@" $bench; } 2>&1)"
  case "$result" in
    sat|unsat) echo "$result"; exit 0;;
    *)         echo "$result" &> "$out_file";;
  esac
}

# use: finishwith [params..]
# to run cvc4. Only "sat" or "unsat" are output. Other outputs are written to
# $out_file.
function finishwith {
  result="$({ $cvc4 -L smt2.6 --no-incremental --no-type-checking --no-interactive "$@" $bench; } 2>&1)"
  case "$result" in
    sat|unsat) echo "$result"; exit 0;;
    *)         echo "$result" &> "$out_file";;
  esac
}

# the following is designed for a run time of 20 min.
case "$logic" in

QF_LRA)
  trywith 200 --miplib-trick --miplib-trick-subs=4 --use-approx --lemmas-on-replay-failure --replay-early-close-depth=4 --replay-lemma-reject-cut=128 --replay-reject-cut=512 --unconstrained-simp --use-soi
  finishwith --no-restrict-pivots --use-soi --new-prop --unconstrained-simp
  ;;
QF_LIA)
  # same as QF_LRA but add --pb-rewrites
  finishwith --miplib-trick --miplib-trick-subs=4 --use-approx --lemmas-on-replay-failure --replay-early-close-depth=4 --replay-lemma-reject-cut=128 --replay-reject-cut=512 --unconstrained-simp --use-soi --pb-rewrites --ite-simp --simp-ite-compress
  ;;
QF_NIA)
  trywith 480 --nl-ext-tplanes --decision=internal
  trywith 60 --nl-ext-tplanes --decision=justification
  trywith 60 --no-nl-ext-tplanes --decision=internal
  trywith 60 --no-arith-brab --nl-ext-tplanes --decision=internal
  # this totals up to more than 20 minutes, although notice that smaller bit-widths may quickly fail
  trywith 300 --solve-int-as-bv=2 --bitblast=eager --bv-sat-solver=cadical --no-bv-abstraction
  trywith 300 --solve-int-as-bv=4 --bitblast=eager --bv-sat-solver=cadical --no-bv-abstraction
  trywith 300 --solve-int-as-bv=8 --bitblast=eager --bv-sat-solver=cadical --no-bv-abstraction
  trywith 300 --solve-int-as-bv=16 --bitblast=eager --bv-sat-solver=cadical --no-bv-abstraction
  trywith 600 --solve-int-as-bv=32 --bitblast=eager --bv-sat-solver=cadical --no-bv-abstraction
  finishwith --nl-ext-tplanes --decision=internal
  ;;
QF_NRA)
  trywith 300 --nl-ext-tplanes --decision=internal
  trywith 300 --nl-ext-tplanes --decision=justification --no-nl-ext-factor
  trywith 30 --nl-ext-tplanes --decision=internal --solve-real-as-int
  finishwith --nl-ext-tplanes --decision=justification
  ;;
# all logics with UF + quantifiers should either fall under this or special cases below
ALIA|AUFLIA|AUFLIRA|AUFNIRA|UF|UFIDL|UFLIA|UFLRA|UFNIA|UFDT|UFDTLIA|AUFDTLIA|AUFBVDTLIA|AUFNIA)
  # initial runs 1 min
  trywith 30 --simplification=none --full-saturate-quant
  trywith 30 --no-e-matching --full-saturate-quant
  # trigger selections 3 min
  trywith 30 --relevant-triggers --full-saturate-quant
  trywith 30 --trigger-sel=max --full-saturate-quant
  trywith 30 --multi-trigger-when-single --full-saturate-quant
  trywith 30 --multi-trigger-when-single --multi-trigger-priority --full-saturate-quant
  trywith 30 --multi-trigger-cache --full-saturate-quant
  trywith 30 --no-multi-trigger-linear --full-saturate-quant
  # other 4 min
  trywith 30 --pre-skolem-quant --full-saturate-quant
  trywith 30 --inst-when=full --full-saturate-quant
  trywith 30 --no-e-matching --no-quant-cf --full-saturate-quant
  trywith 30 --full-saturate-quant --quant-ind
  trywith 30 --decision=internal --simplification=none --no-inst-no-entail --no-quant-cf --full-saturate-quant
  trywith 30 --decision=internal --full-saturate-quant
  trywith 30 --term-db-mode=relevant --full-saturate-quant
  trywith 30 --fs-interleave --full-saturate-quant
  # finite model find 3 min
  trywith 30 --finite-model-find --mbqi=none
  trywith 30 --finite-model-find --decision=internal
  trywith 30 --finite-model-find --macros-quant --macros-quant-mode=all
  trywith 30 --finite-model-find --uf-ss=no-minimal
  trywith 60 --finite-model-find --fmf-inst-engine
  # long runs 4 min
  trywith 240 --finite-model-find --decision=internal
  finishwith --full-saturate-quant
  ;;
ABVFP|BVFP|FP|UFFPDTLIRA|UFFPDTNIRA)
  finishwith --full-saturate-quant --fp-exp
  ;;
UFBV)
  # most problems in UFBV are essentially BV
  trywith 300 --full-saturate-quant --decision=internal
  trywith 300 --full-saturate-quant --cegqi-nested-qe --decision=internal
  trywith 30 --full-saturate-quant --no-cegqi-innermost --global-negate
  finishwith --finite-model-find
  ;;
BV)
  trywith 120 --full-saturate-quant
  trywith 120 --full-saturate-quant --no-cegqi-innermost
  trywith 300 --full-saturate-quant --cegqi-nested-qe --decision=internal
  trywith 30 --full-saturate-quant --no-cegqi-bv
  trywith 30 --full-saturate-quant --cegqi-bv-ineq=eq-slack
  # finish 10min
  finishwith --full-saturate-quant --no-cegqi-innermost --global-negate
  ;;
LIA|LRA|NIA|NRA)
  trywith 30 --full-saturate-quant --nl-ext-tplanes
  trywith 300 --full-saturate-quant --no-cegqi-innermost
  trywith 300 --full-saturate-quant --cegqi-nested-qe
  finishwith --full-saturate-quant --cegqi-nested-qe --decision=internal
  ;;
QF_AUFBV)
  trywith 600 --ite-simp
  finishwith --decision=justification-stoponly --ite-simp
  ;;
QF_ABV)
  trywith 50 --ite-simp --simp-with-care --repeat-simp --arrays-weak-equiv
  trywith 500 --arrays-weak-equiv
  finishwith --ite-simp --simp-with-care --repeat-simp --arrays-weak-equiv
  ;;
QF_UFBV)
  # Benchmarks with uninterpreted sorts cannot be solved with eager
  # bit-blasting currently
  trywith 1200 --bitblast=eager --bv-sat-solver=cadical
  finishwith
  ;;
QF_BV)
  finishwith --bv-div-zero-const --bitblast=eager --bv-sat-solver=cadical --no-bv-abstraction
  ;;
QF_AUFLIA)
  finishwith --no-arrays-eager-index --arrays-eager-lemmas --decision=justification
  ;;
QF_AX)
  finishwith --no-arrays-eager-index --arrays-eager-lemmas --decision=internal
  ;;
QF_AUFNIA)
  finishwith --decision=justification --no-arrays-eager-index --arrays-eager-lemmas
  ;;
QF_ALIA)
  trywith 140 --decision=justification --arrays-weak-equiv
  finishwith --decision=justification-stoponly --no-arrays-eager-index --arrays-eager-lemmas
  ;;
QF_S|QF_SLIA)
  trywith 300 --strings-exp --rewrite-divk --strings-fmf
  finishwith --strings-exp --rewrite-divk
  ;;
QF_ABVFP|QF_ABVFPLRA)
  finishwith --fp-exp
  ;;
QF_BVFP|QF_BVFPLRA)
  finishwith --fp-exp
  ;;
QF_FP|QF_FPLRA)
  finishwith --fp-exp
  ;;
*)
  # just run the default
  finishwith
  ;;

esac
