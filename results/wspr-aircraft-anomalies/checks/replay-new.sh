#!/bin/sh
# Replay of the second sample from the public data (protocol-addendum.txt): downloads the 36 new
# dates, labels and flags each with the frozen code, spot-checks three drawn dates, and runs the
# frozen analysis on the new dates alone and pooled with the first sample, then sens.py on both.
# Run checks/replay.sh WORK first: the pooled analysis reads its units from WORK/units.
# About 13 CPU-hours and 8 to 9 GB of memory per worker.
# usage: sh checks/replay-new.sh WORK [JOBS]      (results in WORK/results-new, WORK/results-pooled)
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${1:?usage: replay-new.sh WORK [JOBS]}; JOBS=${2:-2}; PY=${PYTHON:-python3}
DATA="$WORK/data"; NEW="$WORK/units-new"; OLD="$WORK/units"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
test "$(ls "$OLD"/units-*.npz | wc -l)" -eq 36 || { echo "run checks/replay.sh WORK first" >&2; exit 2; }
mkdir -p "$DATA" "$NEW" "$WORK/results-new" "$WORK/results-pooled"
$PY -I "$HERE/days_new.py" | xargs -P "$JOBS" -I{} $PY -I "$HERE/fetch.py" {} "$DATA"
for d in $($PY -I "$HERE/days_new.py"); do
  if grep -q MISSING "$DATA/manifest-$d.txt"; then echo "$d: ADS-B snapshots missing" >&2; exit 3; fi
done
$PY -I "$HERE/days_new.py" --placebos | xargs -P "$JOBS" -L 1 sh -c \
  "test -s \"$NEW/units-\$0.npz\" || $PY -I \"$HERE/prep.py\" \$0 \$1 \$2 \"$DATA\" \"$NEW/units-\$0.npz\""
for d in 2022-02-01 2022-11-01 2026-08-01; do $PY -I "$HERE/check.py" "$NEW/units-$d.npz" "$DATA" 20 1; done
$PY -I "$HERE/analyze.py" "$WORK/results-new" "$NEW"/units-*.npz | tee "$WORK/results-new/summary.txt"
$PY -I "$HERE/analyze.py" "$WORK/results-pooled" "$NEW"/units-*.npz "$OLD"/units-*.npz | tee "$WORK/results-pooled/summary.txt"
$PY -I "$HERE/sens.py" "$WORK/sens-new" "$NEW"/units-*.npz | tee "$WORK/sens-new.txt"
$PY -I "$HERE/sens.py" "$WORK/sens-pooled" "$NEW"/units-*.npz "$OLD"/units-*.npz | tee "$WORK/sens-pooled.txt"
