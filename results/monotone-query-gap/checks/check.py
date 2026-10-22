#!/usr/bin/env python3
"""Run both exact certificate checkers and their corruption controls."""

from pathlib import Path
import subprocess
import sys


def main():
    here = Path(__file__).resolve().parent
    certificate = here.parent / "data" / "certificate.json"
    checkers = (here / "check_cert.py", here / "check_independent.py")
    for checker in checkers:
        subprocess.run([sys.executable, "-I", str(checker), str(certificate)],
                       check=True)
    subprocess.run([sys.executable, "-I", str(here / "corrupt.py"),
                    str(certificate), *map(str, checkers)], check=True)
    print("PASS: both exact checkers accept; both reject every corruption")


if __name__ == "__main__":
    main()
