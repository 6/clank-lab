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
cd "$script_dir"
here=$(pwd)
export PYTHONDONTWRITEBYTECODE=1
PYTHON=${PYTHON:-python3}
pins_ok() {
    "$1" -c 'import sys, flint, sympy; (flint.__version__, sympy.__version__) == ("0.9.0", "1.14.0") or sys.exit("dependency version mismatch")' >/dev/null 2>&1
}
if ! pins_ok "$PYTHON"; then
    [ -x .venv/bin/python ] || "$PYTHON" -m venv .venv
    PYTHON="$here/.venv/bin/python"
    pins_ok "$PYTHON" || "$PYTHON" -m pip install --disable-pip-version-check -q -r requirements.txt
fi
export PYTHON
"$PYTHON" verify_identities.py
"$PYTHON" test_runtime_inputs.py
bash verify_library.sh --reference ../input_link/evidence/s1_facets_p16.json
"$PYTHON" test_stage1.py
"$PYTHON" verify_stage1.py
bash verify_b2.sh
"$PYTHON" check_result.py
