#!/usr/bin/env bash
# Hand off to Bash when invoked by a legacy shell-based verifier.
if [ -z "${BASH_VERSION:-}" ]; then exec bash "$0" "$@"; fi
# Bash is required for pipeline status and inherited command-substitution errors.
set -Eeuo pipefail
shopt -s inherit_errexit
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
script_dir=$(dirname -- "$0")
here=$(CDPATH= cd -- "$script_dir" && pwd)
python_cmd=${PYTHON:-python3}
"$python_cmd" -B "$here/snub_check.py"
"$python_cmd" -B "$here/snub_check_rational.py"
"$python_cmd" -B "$here/snub_corrupt.py"
