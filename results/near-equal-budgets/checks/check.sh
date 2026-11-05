#!/bin/sh
# Runs the six checks of the theorem from this result's folder: the market's hypotheses, the
# Farkas certificates, the independent ray computation, and three corrupted inputs that must be
# rejected. Usage: sh checks/check.sh [--part K/N]   (--part runs every N-th check, from the K-th)
set -eu
cd "$(dirname "$0")/.."
part=1
parts=1
if [ "$#" -gt 0 ]; then
    if [ "$1" != --part ] || [ "$#" -ne 2 ]; then
        echo "usage: sh checks/check.sh [--part K/N]" >&2
        exit 2
    fi
    part=${2%/*}
    parts=${2#*/}
    case "$part/$parts" in
        *[!0-9/]* | /* | */ | 0/* | */0) echo "--part needs K/N with 1 <= K <= N" >&2; exit 2 ;;
    esac
    if [ "$part" -gt "$parts" ]; then
        echo "--part needs K/N with 1 <= K <= N" >&2
        exit 2
    fi
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
python3 -I checks/corrupt.py data/certificate.json data/instance.json "$tmp"
number=0
passed=0

# check NAME EXPECT PATTERN COMMAND...: EXPECT is pass or reject; PATTERN must appear in the output.
check() {
    name=$1
    expect=$2
    pattern=$3
    shift 3
    number=$((number + 1))
    if [ $(((number - part) % parts)) -ne 0 ]; then
        return 0
    fi
    status=0
    "$@" >"$tmp/out" 2>&1 || status=$?
    cat "$tmp/out"
    if [ "$expect" = pass ] && [ "$status" -eq 0 ] && grep -qF "$pattern" "$tmp/out"; then
        echo "check $number ($name): passed"
    elif [ "$expect" = reject ] && [ "$status" -eq 1 ] && grep -qF "$pattern" "$tmp/out"; then
        echo "check $number ($name): rejected, as it must be"
    else
        echo "check $number ($name): FAILED"
        exit 1
    fi
    passed=$((passed + 1))
}

check "market hypotheses" pass "all 32 bundle values distinct" \
    python3 -I checks/check_instance.py data/instance.json data/certificate.json
check "Farkas certificates" pass "243 allocations certified; direction d=['-3', '2', '1']; radius r=1/17" \
    python3 -I checks/check_cert.py data/certificate.json
check "independent ray computation" pass "R=1/17" \
    python3 -I checks/check_ray.py data/instance.json
check "corruption 1: one multiplier doubled" reject "componentwise condition fails" \
    python3 -I checks/check_cert.py "$tmp/c1-certificate.json"
check "corruption 2: one value changed, certificate" reject "does not strictly prefer" \
    python3 -I checks/check_cert.py "$tmp/c2-certificate.json"
check "corruption 3: one value changed, ray computation" reject "feasible for delta in" \
    python3 -I checks/check_ray.py "$tmp/c3-instance.json"

if [ "$parts" -eq 1 ]; then
    echo "PASS: $passed of $number checks"
else
    echo "PASS: part $part/$parts ran $passed of the $number checks"
fi
