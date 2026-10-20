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
mode=${1:-quick}
case "$mode" in quick|full) ;; *) echo 'usage: bash checks/verify-public.sh [quick|full]' >&2; exit 2 ;; esac
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
"$py" checks/test_manifest.py
"$py" checks/test_optimization.py
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
cd "$work/checks"
export PYTHON="$py"
bash independent-s1-b2/verify.sh
"$py" independent-merge-filter/merge_check.py
"$py" independent-merge-filter/affine_check.py
"$py" check_filter.py
"$py" model_audit/q5_check_a.py model_audit/q5_certificate.json
"$py" model_audit/q5_check_b.py model_audit/q5_certificate.json
"$py" model_audit/q5_corrupt.py
bash model_audit/snub_verify.sh
"$py" check_caseb/chartcheck.py repair-caseb-w/chart-certificate.json
PYTHON="$s23py" bash verify_s23.sh
bash check_caseb/run.sh "$mode"
if [ "$mode" = full ]; then
    cd independent-s23
    "$s23py" unpack_inputs.py "$work/p16/input" --pmax 16
    "$s23py" run.py "$work/p16/input/u2_classes_p16.json" "$work/p16/s2.jsonl" --states
    "$s23py" check_equivalence.py "$work/p16/input/u2_classes_p16.json" certificates/equivalences-p16.json
    "$s23py" stage3.py --states "$work/p16/s2.jsonl" --models models \
        --known "$work/p16/input/u3_known_p16.json" --output "$work/p16/s3.jsonl" --jobs "${S23_JOBS:-2}"
    "$s23py" audit_stage3.py --classes "$work/p16/input/u2_classes_p16.json" \
        --states "$work/p16/s2.jsonl" --results "$work/p16/s3.jsonl" --models models \
        --known "$work/p16/input/u3_known_p16.json" --pmax 16 --receipt "$work/p16/s3.jsonl.frozen.json"
    cd ..
fi
if [ "$mode" = quick ]; then
    echo 'NON-PROOF CHECK: quick mode does not check the theorem; use full mode.'
fi
printf 'uniform-5-polytopes public %s: PASS\n' "$mode"
