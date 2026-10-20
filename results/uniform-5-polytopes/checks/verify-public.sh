#!/usr/bin/env bash
# Hand off to Bash when invoked by a legacy shell-based verifier.
if [ -z "${BASH_VERSION:-}" ]; then exec bash "$0" "$@"; fi
# Standalone entry point after installing the documented dependencies.
# The replay needs no network or repository metadata.
# Bash 4.4 or later is required for inherited command-substitution errors.
if (( BASH_VERSINFO[0] < 4 || (BASH_VERSINFO[0] == 4 && BASH_VERSINFO[1] < 4) )); then
    echo 'Bash 4.4 or later is required; install it and put it on PATH.' >&2
    exit 2
fi
set -Eeuo pipefail
shopt -s inherit_errexit
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
script_dir=$(dirname -- "$0")
root=$(CDPATH= cd -- "$script_dir/.." && pwd)
cd "$root"
usage() { echo 'usage: bash checks/verify-public.sh [quick|full] [--part K/N] [--list]' >&2; exit 2; }
mode=quick
if (( $# > 0 )) && [[ $1 != -* ]]; then mode=$1; shift; fi
case "$mode" in quick|full) ;; *) usage ;; esac
part=1/1
list=0
while (( $# > 0 )); do
    case "$1" in
        --part) (( $# > 1 )) || usage; part=$2; shift 2 ;;
        --part=*) part=${1#--part=}; shift ;;
        --list) list=1; shift ;;
        *) usage ;;
    esac
done
[[ $part =~ ^([1-9][0-9]*)/([1-9][0-9]*)$ ]] || usage
k=${BASH_REMATCH[1]}
n=${BASH_REMATCH[2]}
(( k <= n )) || usage
# The independent steps, in the order a whole run takes them, each with its
# rough time in seconds on a two-core GitHub-hosted runner (full-mode times
# estimated). --part K/N runs share K of N, balanced by these times: longest
# first, each to the part with the least time so far. Every part repeats the
# dependency and inventory checks and the disposable copy below.
steps=(test-manifest test-optimization s1-b2 merge-check affine-check filter-check
    q5-check-a q5-check-b q5-corrupt snub chart-check s23-tests s23-replay caseb)
seconds=(1 8 106 7 4 4 4 6 3 6 13 80 1650 190)
if [ "$mode" = full ]; then
    seconds[13]=600
    steps+=(s23-p16 primary-library primary-s23 primary-caseb primary-wedge)
    seconds+=(6000 600 6000 600 1800)
fi
assigned=()
if (( n == 1 )); then
    for i in "${!steps[@]}"; do assigned[$i]=1; done
else
    load=()
    for ((p = 1; p <= n; p++)); do load[p]=0; done
    for i in $(for i in "${!steps[@]}"; do echo "${seconds[i]} $i"; done | sort -k1,1nr -k2,2n | cut -d' ' -f2); do
        best=1
        for ((p = 2; p <= n; p++)); do (( load[p] < load[best] )) && best=$p; done
        assigned[$i]=$best
        (( load[best] += seconds[i] ))
    done
fi
mine=()
for i in "${!steps[@]}"; do (( assigned[$i] == k )) && mine+=("${steps[i]}"); done
if (( list )); then
    (( ${#mine[@]} == 0 )) || printf '%s\n' "${mine[@]}"
    exit 0
fi
: "${PYTHON:?Set PYTHON to the documented flint 0.9.0 environment}"
: "${PYTHON_S23:=$PYTHON}"
py=$PYTHON
s23py=$PYTHON_S23
py=$("$py" -c 'import sys; print(sys.executable)')
s23py=$("$s23py" -c 'import sys; print(sys.executable)')
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
"$py" -c 'import sys, flint, sympy, mpmath, numpy, scipy; sys.version_info >= (3, 11) or sys.exit("Python >= 3.11 required"); (flint.__version__,sympy.__version__,mpmath.__version__,numpy.__version__,scipy.__version__)==("0.9.0","1.14.0","1.3.0","2.5.4","1.18.1") or sys.exit("dependency version mismatch")'
"$s23py" -c 'import sys, flint, sympy, mpmath; sys.version_info >= (3, 11) or sys.exit("Python >= 3.11 required"); (flint.__version__,sympy.__version__,mpmath.__version__)==("0.9.0","1.14.0","1.3.0") or sys.exit("dependency version mismatch")'
"$py" checks/check_manifest.py
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
# Existing drivers sometimes write results beside their code. Run disposable copies.
while IFS= read -r name; do
    parent=$(dirname "$name")
    mkdir -p "$work/$parent"
    cp "$name" "$work/$name"
done < checks/PUBLIC.txt
# Install the import name used by the wedge checker.
cp "$work/checks/w_bound.py" "$work/checks/check_caseb/bnb.py"
export PYTHON="$py"
run_step() {
    cd "$work/checks"
    case "$1" in
        test-manifest) cd "$root"; "$py" checks/test_manifest.py ;;
        test-optimization) cd "$root"; "$py" checks/test_optimization.py ;;
        s1-b2) bash independent-s1-b2/verify.sh ;;
        merge-check) "$py" independent-merge-filter/merge_check.py ;;
        affine-check) "$py" independent-merge-filter/affine_check.py ;;
        filter-check) "$py" check_filter.py ;;
        q5-check-a) "$py" model_audit/q5_check_a.py model_audit/q5_certificate.json ;;
        q5-check-b) "$py" model_audit/q5_check_b.py model_audit/q5_certificate.json ;;
        q5-corrupt) "$py" model_audit/q5_corrupt.py ;;
        snub) bash model_audit/snub_verify.sh ;;
        chart-check) "$py" check_caseb/chartcheck.py repair-caseb-w/chart-certificate.json ;;
        s23-tests) PYTHON="$s23py" bash verify_s23.sh tests ;;
        s23-replay) PYTHON="$s23py" bash verify_s23.sh replay ;;
        caseb)
            "$py" p1_literal_contract.py
            bash check_caseb/run.sh "$mode"
            ;;
        s23-p16)
            cd independent-s23
            "$s23py" unpack_inputs.py "$work/p16/input" --pmax 16
            "$s23py" run.py "$work/p16/input/u2_classes_p16.json" "$work/p16/s2.jsonl" --states
            "$s23py" check_equivalence.py "$work/p16/input/u2_classes_p16.json" certificates/equivalences-p16.json
            "$s23py" stage3.py --states "$work/p16/s2.jsonl" --models models \
                --known "$work/p16/input/u3_known_p16.json" --output "$work/p16/s3.jsonl" --jobs "${S23_JOBS:-2}"
            "$s23py" audit_stage3.py --classes "$work/p16/input/u2_classes_p16.json" \
                --states "$work/p16/s2.jsonl" --results "$work/p16/s3.jsonl" --models models \
                --known "$work/p16/input/u3_known_p16.json" --pmax 16 --receipt "$work/p16/s3.jsonl.frozen.json"
            "$s23py" ../count_convention.py "$work/p16/s3.jsonl" \
                --known "$work/p16/input/u3_known_p16.json" --classes "$work/p16/input/u2_classes_p16.json"
            "$s23py" ../test_v2_outcomes.py "$work/p16/s3.jsonl"
            "$s23py" ../report_bridge.py --independent "$work/p16/s3.jsonl"
            "$s23py" ../test_report_bridge.py --independent "$work/p16/s3.jsonl"
            "$s23py" ../encoding_correspondence.py --independent "$work/p16/s3.jsonl" \
                --output "$work/p16/encoding-accounting.json"
            ;;
        primary-library|primary-s23|primary-caseb|primary-wedge)
            "$py" replay_primary.py --part "${1#primary-}" --jobs "${S23_JOBS:-2}" --out "$work/$1"
            ;;
    esac
}
for step in "${mine[@]}"; do
    (( n == 1 )) || echo "== $step"
    run_step "$step"
done
if [ "$mode" = quick ]; then
    echo 'NON-PROOF CHECK: quick mode does not check the theorem; use full mode.'
fi
if (( n == 1 )); then
    printf 'uniform-5-polytopes public %s: PASS\n' "$mode"
else
    echo "NON-PROOF CHECK: part $k/$n runs only its share; every part from 1/$n to $n/$n must pass."
    printf 'uniform-5-polytopes public %s part %s/%s: PASS (%s)\n' "$mode" "$k" "$n" "${mine[*]}"
fi
