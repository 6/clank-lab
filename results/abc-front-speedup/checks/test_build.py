#!/usr/bin/env python3
"""Exercise build.sh with real pkg-config and the pinned CAPD wrapper."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


# Exact template from CAPD commit 37057e5899bccaa6cd5701057b7e6ea5e232ef8b,
# capdMake/libcapd/capd-config.in; only CMake's two placeholders are rendered.
CAPD_CONFIG = '''#!/bin/bash

export PKG_CONFIG_PATH=@PKG_CONFIG_PATH@${PATH_SEPARATOR}${PKG_CONFIG_PATH}
pkg-config --define-variable=capd_cxx=@CMAKE_CXX_COMPILER@ $* capd
'''
BUILD = Path(__file__).resolve().with_name('build.sh')


class BuildTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.capd = self.root / 'capd'
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        (self.capd / 'bin').mkdir(parents=True)
        headers = self.capd / 'include/capd/normalForms'
        headers.mkdir(parents=True)
        for name in ('normalForms.h', 'planarMaps.hpp', 'linearSubstitution.hpp'):
            (headers / name).write_text('// build overlay fixture\n')
        pcdir = self.capd / 'lib/pkgconfig'
        pcdir.mkdir(parents=True)
        (pcdir / 'capd.pc').write_text(
            f'prefix={self.capd}\nName: capd\nDescription: build regression fixture\n'
            'Version: 6.1.0\nCflags: -I${prefix}/include -DCAPD_FIXTURE=1\n'
            'Libs: -L${prefix}/lib -lcapd\n')
        self.config = self.capd / 'bin/capd-config'
        self.config.write_text(CAPD_CONFIG.replace('@PKG_CONFIG_PATH@', str(pcdir))
                               .replace('@CMAKE_CXX_COMPILER@', '/usr/bin/g++'))
        self.config.chmod(0o755)
        self.argv = self.root / 'compiler.json'
        compiler = self.bin / 'g++'
        compiler.write_text('#!/usr/bin/env python3\nimport json, os, sys\n'
                            'with open(os.environ["COMPILER_ARGV"], "w") as f:\n'
                            '    json.dump(sys.argv[1:], f)\n')
        compiler.chmod(0o755)
        self.env = dict(os.environ, CAPD=str(self.capd), OUT=str(self.root / 'out'),
                        COMPILER_ARGV=str(self.argv), PATH=f'{self.bin}:{os.environ["PATH"]}')
        # Isolate pkg-config's defaults and any caller workaround. Only the
        # rendered wrapper can make this fixture's capd.pc discoverable.
        self.env.pop('PATH_SEPARATOR', None)
        self.env.pop('PKG_CONFIG_SYSROOT_DIR', None)
        self.env['PKG_CONFIG_LIBDIR'] = str(self.root / 'no-default-pc')
        if not shutil.which('pkg-config'):
            self.fail('pkg-config is required to exercise the real CAPD wrapper')

    def test_real_wrapper_and_build_with_inherited_paths(self):
        inherited = str(self.root / 'python/lib/pkgconfig')
        env = dict(self.env, PKG_CONFIG_PATH=inherited)
        broken = subprocess.run([str(self.config), '--cflags'], env=env, capture_output=True, text=True)
        self.assertNotEqual(broken.returncode, 0, 'the old wrapper must reproduce the lookup failure')
        self.assertIn('capd', broken.stderr)
        for path in ('', inherited):
            with self.subTest(PKG_CONFIG_PATH=path):
                result = subprocess.run(['sh', str(BUILD)], env=dict(self.env, PKG_CONFIG_PATH=path),
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                argv = json.loads(self.argv.read_text())
                for flag in (f'-I{self.root}/out/include', f'-I{self.capd}/include',
                             '-DCAPD_FIXTURE=1', f'-L{self.capd}/lib', '-lcapd'):
                    self.assertIn(flag, argv)
                self.assertIn(str(BUILD.with_name('bnf.cpp')), argv)
                self.assertEqual(argv[argv.index('-o') + 1], str(self.root / 'out/bnf'))

    def test_config_failure_stops_before_compiler(self):
        real_wrapper = self.config.read_text()
        for option in ('--cflags', '--libs'):
            with self.subTest(option=option):
                self.argv.unlink(missing_ok=True)
                # The other query still goes through the real pkg-config wrapper.
                self.config.write_text('#!/bin/bash\n'
                                       f'if [ "$1" = "{option}" ]; then exit 17; fi\n'
                                       + real_wrapper)
                result = subprocess.run(['sh', str(BUILD)], env=dict(self.env, PKG_CONFIG_PATH=''),
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, 17, result.stderr)
                self.assertFalse(self.argv.exists(), 'compiler ran after a failed configuration query')


if __name__ == '__main__':
    unittest.main()
