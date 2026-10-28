#!/usr/bin/env python3
"""Quote the exact existing endpoint axiom policy into a default Lake guard.

This is a source adapter, not a new mathematical proof or accepted build.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def source():
    spec = importlib.util.spec_from_file_location('endpoint_policy', ROOT / 'checks/guard_endpoint.py')
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    lines = ['import FinalAcceptance', 'import Lean.Util.CollectAxioms', '',
             '/-! Packaging adapter only. The imported probe checks the exact endpoint type.',
             'The policy is quoted from guard_endpoint.py, not from successful build output.',
             'This additionally requires all three recorded standard axioms to be present. -/',
             'open Lean Elab Command', '', 'run_cmd do',
             '  let specifications : List (Name × List String) := [']
    for at, (name, expected) in enumerate(sorted(guard.EXPECTED.items())):
        lines.append('    (``' + name + ', [')
        values = sorted(expected)
        lines.extend('      ' + json.dumps(value) + (',' if i + 1 < len(values) else '')
                     for i, value in enumerate(values))
        lines.append('    ])' + (',' if at + 1 < len(guard.EXPECTED) else ''))
    lines += ['  ]', '  for (theoremName, expected) in specifications do',
              '    let actual := (← Lean.collectAxioms theoremName).toList.map Name.toString',
              '    let missing := expected.filter fun name => !actual.contains name',
              '    let unexpected := actual.filter fun name => !expected.contains name',
              '    unless missing.isEmpty && unexpected.isEmpty && actual.length == expected.length do',
              '      throwError "Axiom policy mismatch for {theoremName}: missing={missing}; unexpected={unexpected}"',
              '  logInfo "PASS exact four-theorem axiom policy; endpoint has 692 native facts and three standard axioms"', '']
    return '\n'.join(lines)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    a = p.parse_args()
    text = source()
    path = ROOT / 'lean/PublicGuard.lean'
    if a.check:
        if path.read_bytes() != text.encode():
            raise SystemExit('public guard source differs from the unchanged named policy')
    else:
        path.write_bytes(text.encode())
    print(json.dumps({'status': 'PASS_PUBLIC_GUARD_SOURCE' if a.check else 'QUOTED_UNCOMPILED_PUBLIC_GUARD',
                      'Lean_compilation': False, 'bytes': len(text.encode())}, sort_keys=True))


if __name__ == '__main__':
    main()
