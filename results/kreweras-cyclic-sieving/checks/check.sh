#!/bin/sh
# Check the finite certificate for the exceptional types G2, F4, E6, E7, E8.
#
#   sh checks/check.sh            run every check
#   sh checks/check.sh --part K/N run every N-th check, starting at the K-th (1 <= K <= N)
#
# The checks: coxeter.py (the Coxeter element has order h and rank(c - 1) = n), checkers A and
# B on each type's certificate in data/, and corrupt.py (six corruptions of the E6 data, each
# rejected by both checkers). Needs Python 3.12 or later with checks/requirements.txt.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
py=${PYTHON:-python3}
part=1
parts=1
if [ "$#" -gt 0 ]; then
    if [ "$1" != "--part" ] || [ "$#" -ne 2 ]; then
        echo "usage: sh checks/check.sh [--part K/N]" >&2
        exit 2
    fi
    part=${2%/*}
    parts=${2#*/}
fi
case "$part$parts" in
    *[!0-9]*|'') echo "usage: sh checks/check.sh [--part K/N]" >&2; exit 2 ;;
esac
if [ "$part" -lt 1 ] || [ "$part" -gt "$parts" ]; then
    echo "usage: sh checks/check.sh [--part K/N]" >&2
    exit 2
fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

# Each check prints its result line; a checker's line must say ACCEPT.
accept() {
    out="$work/out"
    "$py" -I "$@" > "$out"
    cat "$out"
    grep -q '"status": "ACCEPT"' "$out"
}

i=0
ran=0
for task in coxeter A:G2 B:G2:4 A:F4 B:F4:3 A:E6 B:E6:2 A:E7 B:E7:1 A:E8 B:E8:1 corrupt; do
    i=$((i + 1))
    if [ $(( (i - 1) % parts )) -ne $((part - 1)) ]; then
        continue
    fi
    ran=$((ran + 1))
    case "$task" in
        coxeter) "$py" -I checks/coxeter.py ;;
        corrupt) "$py" -I checks/corrupt.py data/krew_tables.json data/E6.json ;;
        A:*) accept checks/check_a.py data/krew_tables.json "data/${task#A:}.json" ;;
        B:*)
            rest=${task#B:}
            accept checks/check_b.py data/krew_tables.json "data/${rest%:*}.json" "${rest#*:}" ;;
    esac
done
echo "PASS: $ran of 12 checks (part $part of $parts)"
