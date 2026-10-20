"""Deliberate raw-process OPEN and dependency-version failures."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent


class RuntimeAcceptance(unittest.TestCase):
    def test_raw_s3_open_retains_output_and_frozen_receipt(self):
        for optimized in (False, True):
            for jobs in (1, 2):
                with self.subTest(optimized=optimized, jobs=jobs), tempfile.TemporaryDirectory() as work:
                    work = Path(work)
                    states, known, output = [work / n for n in ('states', 'known', 'output')]
                    states.write_text(json.dumps([dict(index=7, R=['1', '1'], status='OPEN')]))
                    known.write_text('[]')
                    proc = subprocess.run(
                        [sys.executable, *(['-O'] if optimized else []), str(HERE / 'stage3.py'),
                         '--states', str(states), '--models', 'models', '--known', str(known),
                         '--output', str(output), '--jobs', str(jobs)],
                        capture_output=True, text=True)
                    self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
                    self.assertEqual(json.loads(output.read_text())['status'], 'OPEN')
                    receipt = json.loads(Path(str(output) + '.frozen.json').read_text())
                    self.assertEqual((receipt['classes'], receipt['open']), (1, 1))

    def test_empty_selection_cannot_report_success(self):
        with tempfile.TemporaryDirectory() as work:
            work = Path(work)
            for name in ('states', 'known'):
                (work / name).write_text('[]')
            proc = subprocess.run(
                [sys.executable, str(HERE / 'stage3.py'), '--states', str(work / 'states'),
                 '--known', str(work / 'known'), '--models', 'models', '--output', str(work / 'out')],
                capture_output=True, text=True)
            self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
            self.assertTrue((work / 'out.frozen.json').is_file())

    def test_wrong_versions_rejected_by_both_raw_entries(self):
        for script, args in (
            ('run.py', ['absent-input', 'absent-output']),
            ('stage3.py', ['--states', 'absent', '--known', 'absent', '--models', 'models', '--output', 'absent'])):
            for module, wrong in (('flint', '0.8.0'), ('sympy', '0.0'), ('mpmath', '0.0')):
                for optimized in (False, True):
                    with self.subTest(script=script, module=module, optimized=optimized):
                        code = (
                            "import importlib,runpy,sys;"
                            f"importlib.import_module({module!r}).__version__={wrong!r};"
                            f"sys.argv={[script, *args]!r};"
                            f"runpy.run_path({str(HERE / script)!r},run_name='__main__')")
                        proc = subprocess.run([sys.executable, *(['-O'] if optimized else []), '-c', code],
                                              cwd=HERE, capture_output=True, text=True)
                        self.assertNotEqual(proc.returncode, 0)
                        self.assertIn(module + ' ', proc.stderr)
                        self.assertIn('required; found', proc.stderr)
                        self.assertNotIn('FileNotFoundError', proc.stderr)


if __name__ == '__main__':
    unittest.main()
