#!/bin/sh
# Full replay from the public data: downloads every input for the 36 sample days (about
# 0.5 GB per day after reduction), labels and flags each day, and runs the frozen analysis.
# About 12 CPU-hours and 8 GB of memory per worker.
# usage: sh checks/replay.sh WORK [JOBS]      (results in WORK/results)
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${1:?usage: replay.sh WORK [JOBS]}; JOBS=${2:-2}; PY=${PYTHON:-python3}
DATA="$WORK/data"; UNITS="$WORK/units"; RESULTS="$WORK/results"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
mkdir -p "$DATA" "$UNITS" "$RESULTS"
$PY -I "$HERE/days.py" | xargs -P "$JOBS" -I{} $PY -I "$HERE/fetch.py" {} "$DATA"
$PY -I "$HERE/days.py" --placebos | xargs -P "$JOBS" -L 1 sh -c \
  "test -s \"$UNITS/units-\$0.npz\" || $PY -I \"$HERE/prep.py\" \$0 \$1 \$2 \"$DATA\" \"$UNITS/units-\$0.npz\""
$PY -I "$HERE/analyze.py" "$RESULTS" "$UNITS"/units-*.npz | tee "$RESULTS/summary.txt"
$PY -I "$HERE/sens.py" "$RESULTS" "$UNITS"/units-*.npz | tee "$RESULTS/sens.txt"
