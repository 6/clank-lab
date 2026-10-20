"""Enforce the arithmetic versions required by this independent replay."""
import importlib


REQUIRED = {'flint': '0.9.0', 'sympy': '1.14.0', 'mpmath': '1.3.0'}


def require_versions():
    for name, expected in REQUIRED.items():
        actual = getattr(importlib.import_module(name), '__version__', None)
        if actual != expected:
            raise RuntimeError(f'{name} {expected} required; found {actual!r}')


if __name__ == '__main__':
    require_versions()
    print('PASS required independent S23 arithmetic versions')
