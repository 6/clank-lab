"""Build the pinned proof tools in a separate directory (requires network)."""
import argparse
import os
from pathlib import Path
import platform
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
REVISIONS = {
    'cadical': ('https://github.com/arminbiere/cadical', 'c60730422e758ef1cebe7aeddf2dda31c996bf04'),
    'frat': ('https://github.com/digama0/frat', 'aa18581497830b49a6ab6cbc9e0dc778c14885b5'),
    'cake': ('https://github.com/tanyongkiam/cake_lpr', 'a36874a8b750b43fe4b385b8ddbf5b033e46a3fa'),
}


def build(destination):
    root = Path(destination).resolve()
    root.mkdir(parents=True, exist_ok=True)
    for name, (url, revision) in REVISIONS.items():
        src = root / (name + '-source')
        if not src.exists():
            subprocess.run(['git', 'clone', '--no-checkout', url, str(src)], check=True)
        subprocess.run(['git', '-C', str(src), 'checkout', '--detach', revision], check=True)
        if name == 'cadical':
            subprocess.run(['./configure'], cwd=src, check=True)
            subprocess.run(['make', '-j', str(os.cpu_count() or 2)], cwd=src, check=True)
            binary = src / 'build/cadical'
        elif name == 'frat':
            shutil.copyfile(HERE / 'Cargo.lock', src / 'Cargo.lock')
            subprocess.run(['cargo', 'build', '--release', '--locked'], cwd=src, check=True)
            binary = src / 'target/release/frat-rs'
        else:
            if platform.machine() not in ('aarch64', 'arm64', 'x86_64', 'amd64'):
                raise RuntimeError('cake_lpr requires ARMv8 or x86-64')
            target = 'cake_lpr_arm8' if platform.machine() in ('aarch64', 'arm64') else 'cake_lpr'
            subprocess.run(['make', target], cwd=src, check=True)
            binary = src / 'cake_lpr'
        shutil.copyfile(binary, root / ('frat-rs' if name == 'frat' else 'cake_lpr' if name == 'cake' else name))
        (root / ('frat-rs' if name == 'frat' else 'cake_lpr' if name == 'cake' else name)).chmod(0o755)
    subprocess.run(['cc', '-O2', str(HERE / 'lrat-check.c'), '-o', str(root / 'lrat-check')], check=True)
    return root


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('destination')
    build(ap.parse_args().destination)
