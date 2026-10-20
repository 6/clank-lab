"""Required model-index guard for the independent Case A interpreters.

Install once before construction, then retain through every dependent
search and fork. Repeated stages may reuse only caches built under it.
"""
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'model_audit'))
from model_guard import ModelGuard, GuardUndecided

_audit = None


def ensure_guard():
    global _audit
    if _audit is None:
        candidate = ModelGuard()
        candidate.__enter__()
        try:
            candidate.check_catalog()
        except Exception:
            candidate.__exit__(None, None, None)
            raise
        _audit = candidate
    _audit.require_active()
    return _audit


def record():
    audit = ensure_guard()
    return dict(active=True, scope='guard owner and forked workers; synchronized shared counters',
                queries=dict(audit.stats), sources={
                    name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                    for name in ('check_u3/geom.py', 'check_u3/tcert.py',
                                 'check_u3/ivla.py', 'check_u3/model_runtime.py',
                                 'model_audit/model_guard.py')})
