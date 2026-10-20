#!/usr/bin/env bash
# Hand off to Bash when invoked by a legacy shell-based verifier.
if [ -z "${BASH_VERSION:-}" ]; then exec bash "$0" "$@"; fi
# Independent checkers for Case B (P1) and (W); see README.md and RESULT.md.
#   bash run.sh          full run (about 2.5 CPU-minutes)
#   bash run.sh quick    (P1), a sample of (W) fans, corruptions
# Writes p1.log, w.log, w_results.jsonl, w_summary.txt, corrupt_*.log here.
# Exits non-zero if a result differs from the expected one or a corruption
# is not detected.
# Bash is required for pipeline status and inherited command-substitution errors.
set -Eeuo pipefail
shopt -s inherit_errexit
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
script_dir=$(dirname "$0")
here=$(cd "$script_dir" && pwd)
cd "$here"
py=${PYTHON:-python3}
mode=${1:-full}

"$py" test_domain.py
"$py" test_acceptance.py

expect_p1='RESULT P1 total=168 closable=137 notclosable=28 degenerate=3 family=83 excluded=67 survivors=(4,4,7);(4,4,9);(4,4,11);(4,4,12);(4,4,13);(4,4,14);(4,4,15);(4,4,16);(3,3,3,7);(3,3,3,9);(3,3,3,11);(3,3,3,12);(3,3,3,13);(3,3,3,14);(3,3,3,15);(3,3,3,16)'
expect_wfail='(i)(38,3,7);(i)(39,3,7);(i)(40,3,7);(i)(41,3,7);(i)(23,3,8);(i)(17,3,9);(i)(19,4,5)'

echo "== (P1) family-polygon filter"
$py p1check.py > p1.log
got=$(grep '^RESULT P1' p1.log)
[ "$got" = "$expect_p1" ] || { echo "P1 differs: $got"; exit 1; }
echo "$got"

echo "== (P1) corruptions"
for c in delta44 antiprism; do
    st=0
    P1_CORRUPT=$c P1_OUT=/dev/null P1_OUT_EXCL=/dev/null $py p1check.py > corrupt_p1_$c.log 2>&1 || st=$?
    # Both deliberate mutations finish normally with a specific changed
    # summary. A crash, missing result or unrelated discrepancy is a failure.
    if [ "$st" -ne 0 ]; then
        echo "corruption $c child failed: exit $st"; cat corrupt_p1_$c.log; exit "$st"
    fi
    got=$(grep '^RESULT P1' corrupt_p1_$c.log) || {
        echo "corruption $c: missing result"; exit 1;
    }
    case "$c" in
        delta44) expect_corrupt='RESULT P1 total=168 closable=137 notclosable=28 degenerate=3 family=83 excluded=75 survivors=(3,3,3,7);(3,3,3,9);(3,3,3,11);(3,3,3,12);(3,3,3,13);(3,3,3,14);(3,3,3,15);(3,3,3,16)' ;;
        antiprism) expect_corrupt='RESULT P1 total=168 closable=137 notclosable=28 degenerate=3 family=83 excluded=75 survivors=(4,4,7);(4,4,9);(4,4,11);(4,4,12);(4,4,13);(4,4,14);(4,4,15);(4,4,16)' ;;
    esac
    [ "$got" = "$expect_corrupt" ] || {
        echo "corruption $c: unexpected result: $got"; exit 1;
    }
    echo "corruption $c: detected ($got)"
done

echo "== fan geometry self-test"
$py geomcheck.py | tail -1 | tee geom.log
grep -q ' 0 fans with errors' geom.log

echo "== (W) wedge lemma"
if [ "$mode" = quick ]; then
    echo "NON-PROOF CHECK: a sample of W fans; full mode is required for the theorem."
    $py wcheck.py --out w_results.jsonl \
        --only '(i)(4,6,10);(i)(3,3,3,3,5);(ii)q=16;(iii)(3,5);(i)(37,3,7);(i)(38,3,7);(i)(19,4,5);(m,4,4);(ii)q=m' > w.log
    $py summary.py w_results.jsonl '(i)(38,3,7);(i)(19,4,5)' --inventory quick > w_summary.txt || { cat w_summary.txt; exit 1; }
else
    $py wcheck.py --out w_results.jsonl > w.log
    $py summary.py w_results.jsonl "$expect_wfail" --inventory full > w_summary.txt || { cat w_summary.txt; exit 1; }
fi
tail -4 w_summary.txt

echo "== (W) corruption: separation constraints dropped"
W_CORRUPT=nodist $py wcheck.py --only '(i)(4,4,7)' --out corrupt_w_nodist.jsonl > corrupt_w_nodist.log
grep -q 'FAILED' corrupt_w_nodist.log || { echo "corruption nodist NOT detected"; exit 1; }
cat corrupt_w_nodist.log
echo "ALL OK"
