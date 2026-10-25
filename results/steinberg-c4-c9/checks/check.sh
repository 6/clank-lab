#!/bin/sh
# Retained executable-certificate checks. Run from any directory.
# Check the Lean proof separately with the README's normal Lake commands.
set -eu
cd "$(dirname "$0")/.."
PY=${PYTHON:-python3}
CC=${CC:-cc}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
"$CC" -O2 -o "$work/drat-trim" checks/drat-trim.c
"$CC" -O2 -o "$work/cycles" checks/check_cycles.c
"$CC" -O2 -o "$work/planar" checks/check_planar.c

"$PY" checks/check_ore.py data/graph.txt data/ore-tree.json data/rotation.txt data/deletion-colorings.json

"$work/planar" data/graph.txt data/rotation.txt
"$PY" checks/check_planar.py data/graph.txt data/rotation.txt
"$work/cycles" data/graph.txt 14 4 9 10
"$PY" checks/check_cycles.py data/graph.txt 14 --forbid 4,9,10
"$PY" checks/check_col_elim.py data/graph.txt --expect noncolourable
"$PY" checks/col3_cnf.py data/graph.txt > "$work/col3.cnf"
"$PY" checks/check_dimacs.py data/col3.cnf "$work/col3.cnf"

# drat-trim can print resource diagnostics without a failing status.
# Require its exact success line as well as normal process termination.
verified() { tr '\r' '\n' < "$1" | grep -qx 's VERIFIED'; }
"$work/drat-trim" "$work/col3.cnf" data/col3.drat > "$work/drat.log" 2>&1
verified "$work/drat.log" || { cat "$work/drat.log"; exit 1; }
echo 'OK: drat-trim verifies the generated 3-colouring CNF'

reject() {
    label=$1
    shift
    if "$@" > "$work/reject.log" 2>&1; then
        cat "$work/reject.log"
        echo "FAIL: corruption accepted: $label"
        exit 1
    else
        code=$?
        [ "$code" -eq 1 ] && grep -q 'REJECT:' "$work/reject.log" || {
            cat "$work/reject.log"
            echo "FAIL: corruption did not produce a mathematical rejection: $label"
            exit 1
        }
    fi
    echo "OK: rejected $label"
}
reject_drat() {
    label=$1
    shift
    code=0
    "$work/drat-trim" "$@" > "$work/reject-drat.log" 2>&1 || code=$?
    if [ "$code" -ne 1 ] || verified "$work/reject-drat.log" ||
       ! tr '\r' '\n' < "$work/reject-drat.log" | grep -qx 's NOT VERIFIED'; then
        cat "$work/reject-drat.log"
        echo "FAIL: expected DRAT rejection: $label"
        exit 1
    fi
    echo "OK: rejected $label"
}

C=data/controls
# A real colourable graph, not merely a malformed input.
"$PY" checks/check_col_elim.py "$C/minus-edge.txt" --expect colourable
"$PY" checks/col3_cnf.py "$C/minus-edge.txt" > "$work/minus.cnf"
reject_drat 'DRAT on the edge-deleted graph' "$work/minus.cnf" data/col3.drat
reject 'C cycles on the C4 insertion' "$work/cycles" "$C/plus-c4.txt" 14 4 9 10
reject 'Python cycles on the C4 insertion' "$PY" checks/check_cycles.py "$C/plus-c4.txt" 14 --forbid 4,9,10
reject 'C cycles on the C9 insertion' "$work/cycles" "$C/plus-c9.txt" 14 4 9 10
reject 'Python cycles on the C9 insertion' "$PY" checks/check_cycles.py "$C/plus-c9.txt" 14 --forbid 4,9,10
reject 'C planarity on the swapped rotation' "$work/planar" data/graph.txt "$C/rotation-swapped.txt"
reject 'Python planarity on the swapped rotation' "$PY" checks/check_planar.py data/graph.txt "$C/rotation-swapped.txt"
reject_drat 'the truncated proof' "$work/col3.cnf" "$C/col3-truncated.drat"
reject 'Ore tree with a repeated K4 vertex' "$PY" checks/check_ore.py data/graph.txt "$C/ore-tree-invalid.json" data/rotation.txt data/deletion-colorings.json
echo 'PASS: planar, no C4/C9/C10, 4-critical, 27 K4 leaves and 26 Ore joins; all ten corruption checks passed'

# Independent replay of the rational drawing also checked by Lean.
"$PY" checks/draw_graph.py --check
reject_drawing() {
    expected=$1
    control=$2
    code=0
    "$PY" checks/draw_graph.py --corruption "$C/$control" > "$work/drawing-control.log" 2>&1 || code=$?
    if [ "$code" -ne 1 ] || ! grep -Fxq "REJECT: $expected" "$work/drawing-control.log"; then
        cat "$work/drawing-control.log"
        echo "FAIL: expected drawing rejection: $control"
        exit 1
    fi
    echo "OK: rejected $control"
}
reject_drawing 'drawing edge set differs from graph' drawing-missing-edge.json
reject_drawing 'nonincident edges (2, 23) and (32, 33) intersect' drawing-crossing.json
reject_drawing 'geometric rotation differs at 0' drawing-mirror.json
