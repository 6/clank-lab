#!/usr/bin/env python3
"""Negative packaging controls; no Lean invocation or mathematical replay."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]


class BootstrapControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='adkz-bootstrap-test-')
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.root = self.base / 'bundle'
        shutil.copytree(ROOT / 'checks', self.root / 'checks',
                        ignore=shutil.ignore_patterns('__pycache__'))
        shutil.copytree(ROOT / 'data', self.root / 'data')
        (self.root / 'paper').mkdir()
        shutil.copyfile(ROOT / 'paper/paper.tex', self.root / 'paper/paper.tex')
        (self.root / 'lean').mkdir()
        self.out = self.root / 'lean'
        self.marker = self.base / 'BUILD_WAS_RUN'
        bindir = self.base / 'bin'
        bindir.mkdir()
        lake = bindir / 'lake'
        lake.write_text('#!/bin/sh\ntouch "$BUILD_MARKER"\nexit 97\n')
        lake.chmod(0o755)
        self.env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ['PATH'],
                        BUILD_MARKER=str(self.marker), PYTHONDONTWRITEBYTECODE='1')
        spec = importlib.util.spec_from_file_location(
            'tested_bootstrap', self.root / 'checks/bootstrap_kernel.py')
        self.mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.mod)

    def guarded_build_rejects(self, message, *args):
        # Same fail-closed boundary proposed for the public Lake build command.
        result = subprocess.run(['sh', '-c', '"$@" && lake build', 'guard',
            sys.executable, str(self.root / 'checks/bootstrap_kernel.py'),
            '--scope', 'control', *args], env=self.env, cwd=self.root,
            capture_output=True, text=True)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn(message, result.stderr)
        self.assertFalse(self.marker.exists())

    def test_missing_input_blocks_build(self):
        (self.root / 'data/source-certificate.json.gz.part01').unlink()
        self.guarded_build_rejects('missing or nonregular file')
        self.assertEqual(list(self.out.iterdir()), [])

    def test_tampered_input_blocks_build(self):
        p = self.root / 'data/control-certificate.json.gz'
        raw = p.read_bytes()
        p.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
        self.guarded_build_rejects('SHA256/size mismatch')
        self.assertEqual(list(self.out.iterdir()), [])

    def test_manifest_tamper_blocks_build(self):
        p = self.root / 'checks/generated-kernel-sha256.json'
        p.write_bytes(p.read_bytes() + b' ')
        self.guarded_build_rejects('manifest SHA256 mismatch')

    def test_recipe_tamper_blocks_build(self):
        p = self.root / 'checks/generate_source_kernel.py'
        p.write_bytes(p.read_bytes() + b'\n# tamper\n')
        self.guarded_build_rejects('SHA256/size mismatch')

    def test_missing_generated_file_check_blocks_build(self):
        self.guarded_build_rejects('missing generated files', '--check')

    def test_tampered_existing_output_blocks_build_without_repair(self):
        self.mod.bootstrap('control')
        p = self.out / 'ControlKernelChunk0KernelAsync.lean'
        p.write_bytes(p.read_bytes().replace(b'Fin 8', b'Fin 9', 1))
        damaged = p.read_bytes()
        self.guarded_build_rejects('SHA256/size mismatch')
        self.assertEqual(p.read_bytes(), damaged)

    def test_unexpected_module_blocks_build(self):
        (self.out / 'ControlKernelChunk999KernelAsync.lean').write_text('-- stale\n')
        self.guarded_build_rejects('unexpected generated files')

    def test_symlink_output_blocks_build(self):
        p = self.base / 'external.lean'
        p.write_text('-- invalid\n')
        (self.out / 'ControlKernelData.lean').symlink_to(p)
        self.guarded_build_rejects('missing or nonregular file')

    def test_wrong_generator_output_is_never_installed(self):
        run = subprocess.run

        def corrupt_after_prepare(cmd, **kwargs):
            result = run(cmd, **kwargs)
            if str(cmd[1]).endswith('prepare_kernel.py'):
                out = Path(cmd[cmd.index('--out') + 1])
                p = out / 'ControlKernelCompleteKernelAsync.lean'
                p.write_bytes(p.read_bytes() + b'-- tamper\n')
            return result

        with patch.object(self.mod.subprocess, 'run', side_effect=corrupt_after_prepare):
            with self.assertRaisesRegex(ValueError, 'SHA256/size mismatch'):
                self.mod.bootstrap('control')
        self.assertEqual(list(self.out.iterdir()), [])

    def test_missing_generator_output_is_never_installed(self):
        run = subprocess.run

        def delete_after_prepare(cmd, **kwargs):
            result = run(cmd, **kwargs)
            if str(cmd[1]).endswith('prepare_kernel.py'):
                out = Path(cmd[cmd.index('--out') + 1])
                (out / 'ControlKernelDataBlock1.lean').unlink()
            return result

        with patch.object(self.mod.subprocess, 'run', side_effect=delete_after_prepare):
            with self.assertRaisesRegex(ValueError, 'output set mismatch'):
                self.mod.bootstrap('control')
        self.assertEqual(list(self.out.iterdir()), [])

    def test_control_idempotence_and_missing_file_recovery(self):
        first = self.mod.bootstrap('control')
        frozen = {p.name: p.read_bytes() for p in self.out.iterdir()}
        self.assertEqual(first['generated_files'], 6)
        self.assertEqual(self.mod.bootstrap('control')['generated_files'], 0)
        (self.out / 'ControlKernelDataBlock1.lean').unlink()
        self.assertEqual(self.mod.bootstrap('control')['generated_files'], 1)
        self.assertEqual(frozen, {p.name: p.read_bytes() for p in self.out.iterdir()})
        self.assertEqual(self.mod.bootstrap('control', check=True)['verified_files'], 6)

    def test_written_certificate_status_and_changed_appendix(self):
        paper = self.root / 'paper/paper.tex'
        cmd = [sys.executable, '-I', str(self.root / 'checks/check_written_certificate.py'),
               '--data', str(self.root / 'data'), '--check-paper', str(paper),
               '--output', str(self.base / 'written.json')]
        good = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(good.returncode, 0, good.stderr)
        self.assertIn('PASS written certificate: 41 cones; 861 Cramer ratios', good.stderr)
        self.assertEqual(json.loads(good.stdout)['cones'], 41)
        text = paper.read_text()
        self.assertIn('This appendix specifies', text)
        paper.write_text(text.replace('This appendix specifies', 'This appendix corrupts', 1))
        bad = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(bad.returncode, 1, bad.stderr)
        self.assertIn('FAIL written certificate:', bad.stderr)
        self.assertIn('printed certificate differs from checked constants', bad.stderr)
        self.assertNotIn('PASS written certificate:', bad.stderr)

    def test_quickcheck_guard_precedes_every_run(self):
        # Exercise the real default entrypoint on an omitted-module bundle.
        p = self.root / 'data/chart.json'
        p.write_bytes(p.read_bytes() + b' ')
        work, cp = self.base / 'work', self.base / 'checkpoint.json'
        result = subprocess.run([sys.executable, '-I', str(self.root / 'checks/quickcheck.py'),
            '--cpus', '1', '--work', str(work), '--checkpoint', str(cp)],
            env=self.env, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('SHA256/size mismatch', result.stderr)
        self.assertEqual(list(work.iterdir()), [])
        self.assertFalse(cp.exists())
        self.assertFalse(self.marker.exists())

    def test_quickcheck_first_run_resume_use_same_materialized_signature(self):
        for name in ('lean-toolchain', 'lake-manifest.json'):
            shutil.copyfile(ROOT / 'lean' / name, self.out / name)
        # Deliberately stop at the first checker result, after the source signature.
        # No geometry verification or Lean build is run by this harness.
        # Inventory authentication is tested separately; this fixture deliberately
        # has only the bootstrap inputs and modifies a checker to stop execution.
        (self.root / 'checks/check_proof_sources.py').write_text("print('{}')\n")
        (self.root / 'checks/check_fraction.py').write_text("print('{}')\n")
        work, cp = self.base / 'work', self.base / 'checkpoint.json'
        cmd = [sys.executable, '-I', str(self.root / 'checks/quickcheck.py'),
               '--cpus', '1', '--work', str(work), '--checkpoint', str(cp)]
        for args in ([], ['--resume']):
            result = subprocess.run(cmd + args, env=self.env, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('KeyError', result.stderr)
            state = json.loads(cp.read_text())
            if not args:
                first = state['checking_sources_sha256']
            self.assertEqual(state['checking_sources_sha256'], first)
            self.assertEqual(len(list(self.out.glob('ControlKernel*.lean'))), 6)
            self.assertEqual(len(list(self.out.glob('SourceKernel*.lean'))), 0)
        self.assertFalse(self.marker.exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
