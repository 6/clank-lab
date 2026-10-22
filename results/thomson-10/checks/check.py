#!/usr/bin/env python3
"""Run the independent exact certificate check and negative controls."""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
steps = [
    ('three-point certificate', ['check_certificate.py', str(root/'data/certificate.json.gz'), str(root/'lean/ThomsonN10/Data.lean')]),
    ('eight certificate corruptions', ['corruptions.py', str(root/'data/certificate.json.gz'), str(root/'lean/ThomsonN10/Data.lean')]),
    ('separate decimal energy enclosure', ['energy_enclosure.py']),
]
if len(sys.argv) > 1:
    if sys.argv[1:] != ['--list']:
        raise SystemExit('Usage: python3 -I checks/check.py [--list]')
    for title, _ in steps:
        print(title)
else:
    for title, arguments in steps:
        print('Checking ' + title, flush=True)
        subprocess.run([sys.executable, '-B', '-I', str(root/'checks'/arguments[0]), *arguments[1:]], check=True)
    print('PASS: independent certificate, eight rejected corruptions, separate energy enclosure')
