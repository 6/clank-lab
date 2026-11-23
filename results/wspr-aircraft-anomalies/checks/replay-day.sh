#!/bin/sh
# Replay one sample day from the public data and compare it with the recorded run:
# downloads the day and its two placebo days, labels and flags the day, compares its counts
# with data/per_day.csv, and spot-checks 20 random units against the raw data with check.py.
# About 30 CPU-minutes and 8 GB of memory.
# usage: sh checks/replay-day.sh DAY WORK      (DAY one of: python3 checks/days.py)
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
DAY=${1:?usage: replay-day.sh DAY WORK}; WORK=${2:?usage: replay-day.sh DAY WORK}; PY=${PYTHON:-python3}
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
mkdir -p "$WORK/data"
set -- $($PY -I "$HERE/days.py" --placebos | awk -v d="$DAY" '$1 == d')
test "$#" = 3 || { echo "not a sample day: $DAY" >&2; exit 2; }
for d in "$1" "$2" "$3"; do $PY -I "$HERE/fetch.py" "$d" "$WORK/data"; done
$PY -I "$HERE/prep.py" "$1" "$2" "$3" "$WORK/data" "$WORK/units-$1.npz"
$PY -I "$HERE/compare_day.py" "$WORK/units-$1.npz" "$HERE/../data/per_day.csv"
$PY -I "$HERE/check.py" "$WORK/units-$1.npz" "$WORK/data" 20 1
