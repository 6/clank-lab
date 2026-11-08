#!/bin/sh
# Check the certificate data/certificate.json with three exact checkers and
# confirm that they reject six corrupted copies of it. Run from the result's
# folder: sh checks/check.sh. Python 3.8 or later, standard library only.
set -eu
cd "$(dirname "$0")/.."
PY=${PYTHON:-python3}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
n=0

# expect PROGRAM FILE TEXT: PROGRAM accepts FILE and prints TEXT.
expect() {
  out=$("$PY" -I "checks/$1" "$2") || { echo "$out"; echo "FAIL: checks/$1 rejected $2"; exit 1; }
  echo "$out"
  case $out in *"$3"*) ;; *) echo "FAIL: checks/$1 did not print: $3"; exit 1 ;; esac
  n=$((n + 1))
}

expect check_certificate.py data/certificate.json "ACCEPT: S is a 4-reptile 4-simplex"
expect check_independent.py data/certificate.json "ACCEPT: vol(S) = 1/576, phi^T phi = 2I, vol(T) = 1/144"
expect check_alcoves.py data/certificate.json "ACCEPT: S and the 4 pieces are distinct F4 alcoves inside phi(S)"

"$PY" -I checks/corrupt.py data/certificate.json "$work/c"
for f in "$work"/c/*.json; do
  # The independent checker ignores the separators and the alcove checker
  # ignores M, t and the separators, so a corruption confined to a field a
  # checker ignores is aimed at the others.
  case $(basename "$f") in
    separator-shifted.json) chks=check_certificate.py ;;
    M-not-orthogonal.json) chks="check_certificate.py check_independent.py" ;;
    *) chks="check_certificate.py check_independent.py check_alcoves.py" ;;
  esac
  for chk in $chks; do
    if out=$("$PY" -I "checks/$chk" "$f"); then
      echo "FAIL: $chk accepted the corruption $(basename "$f" .json)"; exit 1
    fi
    case $out in REJECT:*) ;; *) echo "$out"; echo "FAIL: $chk failed on $(basename "$f" .json) without a REJECT line"; exit 1 ;; esac
    echo "rejected $(basename "$f" .json): $chk: $out"
  done
  n=$((n + 1))
done
[ "$n" -eq 9 ] || { echo "FAIL: expected 3 checks and 6 corruptions, ran $n"; exit 1; }
echo "PASS: 3 checkers accept the certificate and reject all 6 corruptions"
