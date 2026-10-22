#!/usr/bin/env python3
"""Run the independent exact certificate check and negative controls."""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
controls = sorted((root/'data/controls').glob('drawing-*.json'))
steps = [
    ('three-point certificate', ['check_certificate.py', str(root/'data/certificate.json.gz'), str(root/'lean/ThomsonN10/Data.lean')]),
    ('eight certificate corruptions', ['corruptions.py', str(root/'data/certificate.json.gz'), str(root/'lean/ThomsonN10/Data.lean')]),
    ('separate decimal energy enclosure', ['energy_enclosure.py']),
    ('figure of the candidate (illustration only)', ['draw_antiprism.py', '--check']),
]
if len(sys.argv) > 1:
    if sys.argv[1:] != ['--list']:
        raise SystemExit('Usage: python3 -I checks/check.py [--list]')
    for title, _ in steps:
        print(title)
    print(f'{len(controls)} figure corruptions')
else:
    for title, arguments in steps:
        print('Checking ' + title, flush=True)
        subprocess.run([sys.executable, '-B', '-I', str(root/'checks'/arguments[0]), *arguments[1:]], check=True)
    print(f'Checking {len(controls)} figure corruptions', flush=True)
    for control in controls:
        result = subprocess.run([sys.executable, '-B', '-I', str(root/'checks/draw_antiprism.py'),
                                 '--corruption', str(control)], capture_output=True, text=True)
        if result.returncode != 1 or not result.stderr.startswith('REJECT:'):
            raise SystemExit(f'figure corruption {control.name} was not rejected')
        print(f'{control.name}: {result.stderr.strip()}')
    print(f'PASS: independent certificate, eight rejected corruptions, separate energy enclosure, '
          f'figure matches the candidate and rejects {len(controls)} corruptions')
