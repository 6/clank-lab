#!/bin/sh
# Replays the computer-assisted part. From the result's folder:
#   python3 -m pip install -r checks/requirements.txt
#   sh checks/run.sh
# 1. Checker 1 (CAPD 6.1.0 at a pinned commit, built here): the integrable control, the
#    certificate, then three corrupted certificates, each of which it must reject.
# 2. Checker 2 (python-flint ball arithmetic, independent of CAPD): the same.
# 3. The numbers in the Lean certificate axiom (lean/ABC/Cert.lean, lean/ABC/Flow.lean) are
#    compared with the certificate and with both checkers' output.
set -eu
cd "$(dirname "$0")/.."
PY=${PYTHON:-python3}
# cmake may come from the Python requirements: put that environment's bin directory first.
PATH="$($PY -I -c 'import os, sys; print(os.path.dirname(sys.executable))'):$PATH"
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
$PY checks/test_build.py
$PY checks/check_remainder.py
CAPD="$T/capd" SRC="$T/capd-src" sh checks/get-capd.sh > "$T/capd.log"
CAPD="$T/capd" OUT="$T/bnf" sh checks/build.sh > /dev/null
B="$T/bnf/bnf"
"$B" control | tail -1 | grep -q 'ALL CHECKS PASSED' || { echo "FAIL: checker 1 control"; exit 1; }
"$B" check checks/cert.txt > "$T/capd.out" || { cat "$T/capd.out"; echo "FAIL: checker 1 certificate"; exit 1; }
tail -1 "$T/capd.out" | grep -q 'ALL CHECKS PASSED' || { echo "FAIL: checker 1 certificate"; exit 1; }
echo "ok: checker 1 (CAPD) passes the control and the certificate"
sed 's/^centre_num_x .*/centre_num_x 6533236717816/' checks/cert.txt > "$T/c1.txt"   # centre moved by 2^-19
sed 's/^trace_hi .*/trace_hi -1.9646/' checks/cert.txt > "$T/c2.txt"                  # trace claim excludes the value
sed 's/^time_hi .*/time_hi 3.2352/' checks/cert.txt > "$T/c3.txt"                     # return-time claim excludes it
for c in c1 c2 c3; do
    if "$B" check "$T/$c.txt" > /dev/null 2>&1; then echo "FAIL: checker 1 accepted corruption $c"; exit 1; fi
done
echo "ok: checker 1 rejects corruptions c1, c2, c3"
$PY -I checks/check_arb.py checks/control-cert.txt | grep -q 'RESULT: ALL CHECKS PASS' || { echo "FAIL: checker 2 control"; exit 1; }
$PY -I checks/check_arb.py checks/cert.txt > "$T/arb.out" || { cat "$T/arb.out"; echo "FAIL: checker 2 certificate"; exit 1; }
grep -q 'RESULT: ALL CHECKS PASS' "$T/arb.out" || { echo "FAIL: checker 2 certificate"; exit 1; }
echo "ok: checker 2 (arb) passes the control and the certificate"
for c in c1 c2 c3; do
    if $PY -I checks/check_arb.py "$T/$c.txt" > /dev/null 2>&1; then echo "FAIL: checker 2 accepted corruption $c"; exit 1; fi
done
echo "ok: checker 2 rejects corruptions c1, c2, c3"
$PY -I checks/cert_import.py "$T/capd.out" "$T/arb.out" > "$T/import.txt" || { cat "$T/import.txt"; echo "FAIL: certificate import"; exit 1; }
echo "ok: the Lean certificate axiom's numbers match the certificate and both checkers' output"
