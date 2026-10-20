#!/usr/bin/env bash
# Hand off to Bash when invoked by a legacy shell-based verifier.
if [ -z "${BASH_VERSION:-}" ]; then exec bash "$0" "$@"; fi
# Bash is required for pipeline status and inherited command-substitution errors.
set -Eeuo pipefail
shopt -s inherit_errexit
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
script_dir=$(dirname "$0")
cd "$script_dir/independent-s23"
py=${PYTHON:-python3}
work=$(mktemp -d "${TMPDIR:-/tmp}/independent-s23-verify.XXXXXX")
cleanup() {
    status=$?
    trap - EXIT HUP INT TERM
    if [ "$status" -ne 0 ]; then
        for log in "$work/s2.log" "$work/s3.log"; do
            if [ -f "$log" ]; then tail -n 15 "$log"; fi
        done
    fi
    if [ "${S23_KEEP_OUTPUT:-0}" = 1 ]; then
        echo "Replay artifacts: $work"
    else
        rm -rf "$work"
    fi
    exit "$status"
}
trap cleanup EXIT
"$py" - <<'PY'
import hashlib, json
from pathlib import Path
data = Path('certificates/equivalences-p16.json').read_bytes()
if hashlib.sha256(data).hexdigest() != '4cceb9dfd70d84a9a8ff64df0c0820224fd6ee9be0068e8832a363661063c6de':
    raise ValueError('equivalence certificate digest differs')
certificates = json.loads(data)
if len(certificates) != 181:
    raise ValueError('expected 181 equivalence certificates')
if sum(len(c['options']) for c in certificates.values()) != 5108:
    raise ValueError('expected 5108 equivalence options')
print('PASS frozen full-library equivalence certificate identity')
PY
"$py" runtime_versions.py
"$py" test_runtime_acceptance.py
"$py" test_core.py
"$py" test_s3_grid.py
"$py" test_stage3.py
"$py" test_handoff.py
"$py" test_r1_stage3.py
"$py" unpack_inputs.py "$work/input" --pmax 6
"$py" test_chiral_stage3.py --class "$work/input/u2_classes_p6.json"
"$py" run.py "$work/input/u2_classes_p6.json" "$work/s2.jsonl" --states >"$work/s2.log"
"$py" stage3.py --states "$work/s2.jsonl" --models models \
    --known "$work/input/u3_known_p6.json" --output "$work/s3.jsonl" \
    --jobs "${S23_JOBS:-2}" >"$work/s3.log"
"$py" audit_stage3.py --classes "$work/input/u2_classes_p6.json" \
    --states "$work/s2.jsonl" --results "$work/s3.jsonl" --models models \
    --known "$work/input/u3_known_p6.json" --pmax 6 --receipt "$work/s3.jsonl.frozen.json"
"$py" -c 'from provenance import authenticate; authenticate("../check_u3/inputs/u3_vfs_p6.json", "producer-p6/u3_vfs_p6.json")'
"$py" compare.py "$work/s2.jsonl" ../check_u3/inputs/u3_vfs_p6.json >"$work/s2-comparison.json"
"$py" compare_stage3.py "$work/s3.jsonl" ../check_u3/result_p6.json \
    --reference-signatures ../check_u3/inputs/u3_vfs_p6.json \
    --receipt "$work/s3.jsonl.frozen.json" --output "$work/s3-comparison.json"
echo 'PASS full P6 independent S2/S3, authenticated coverage, recorded conclusions and corruption controls'
