#!/usr/bin/env python3
"""Produce or check finite weak-parking certificates with explicit success markers."""
import argparse
import concurrent.futures
import copy
import gzip
import json
from pathlib import Path
import re
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
TARGET = HERE.parent
FIELDS = ('rank', 'h', 'group_order', 'roots', 'nc_count', 'orbits',
          'w_classes', 'class_sizes', 'class_orders', 'class_matrices', 'character')


def gap_value(value):
    if isinstance(value, dict):
        if not all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', k) for k in value):
            raise ValueError('invalid record field')
        return 'rec(' + ','.join(k + ':=' + gap_value(v) for k, v in value.items()) + ')'
    if isinstance(value, list):
        return '[' + ','.join(map(gap_value, value)) + ']'
    if type(value) is int:
        return str(value)
    raise ValueError('certificate requires integers, lists and records')


def gap_run(code, marker):
    start = time.monotonic()
    proc = subprocess.run(['gap', '-q', '-b', '-T'], input=code,
                          text=True, capture_output=True)
    log = (proc.stdout + proc.stderr).replace('\\\n', '')
    accepted = proc.returncode == 0 and marker in log and not re.search(
        r'Error,|Syntax error|Error:', log)
    return {'accepted': accepted, 'wall_seconds': round(time.monotonic()-start, 6),
            'log': log}


def read_pair(folder, n):
    data = json.loads((folder / f'e{n}-result.json').read_text())
    cert = json.loads(gzip.decompress((folder / f'e{n}-result.json.certificate.json.gz').read_bytes()))
    return data, cert


def check_one(data, cert):
    return gap_run('D:=' + gap_value(data) + ';; C:=' + gap_value(cert)
                   + ';; Read(' + json.dumps(str(HERE / 'check_certificate.g'))
                   + ');\n', 'CERTIFICATE PASS')


def spectral(data):
    import math
    import sympy as s
    x = s.Symbol('x')
    n, h = data['rank'], data['h']
    if len(data['class_matrices']) != data['w_classes'] or len(data['character']) != data['w_classes']:
        raise ValueError('class dimensions')
    for matrix, row in zip(data['class_matrices'], data['character']):
        if len(matrix) != n or any(len(r) != n for r in matrix) or len(row) != h:
            raise ValueError('matrix/table dimensions')
        p = s.Poly(s.Matrix(matrix).charpoly(x).as_expr(), x)
        for d, val in enumerate(row):
            factor = s.Poly(s.cyclotomic_poly(h // math.gcd(h, d), x), x)
            q, mult = p, 0
            while q.rem(factor).is_zero:
                q = q.exquo(factor)
                mult += 1
            if val != (h+1)**mult:
                raise ValueError('spectral mismatch')
    return True


def produce(folder, n):
    folder.mkdir(parents=True, exist_ok=True)
    out = folder / f'e{n}-result.json'
    result = gap_run(f'N:={n};; OUT:=' + json.dumps(str(out)) + ';; Read('
                     + json.dumps(str(HERE / 'producer.g')) + ');\n', 'RESULT rank')
    if not result['accepted'] or not out.exists():
        raise RuntimeError(result['log'])
    raw = json.loads(out.read_text())
    if raw['mismatches']:
        raise ValueError('producer mismatches')
    result.update(rank=n, cpu_ms=raw['total_cpu_ms'], comparisons=raw['w_classes']*raw['h'])
    result['log'] = '\n'.join(l for l in result['log'].splitlines()
                              if l.startswith(('NC ', 'ORBITS ', 'RESULT ')))
    out.write_text(json.dumps({k: raw[k] for k in FIELDS}, separators=(',', ':')) + '\n')
    cp = Path(str(out) + '.certificate.json')
    Path(str(cp) + '.gz').write_bytes(gzip.compress(cp.read_bytes(), mtime=0))
    cp.unlink()
    return result


def check(folder, n):
    data, cert = read_pair(folder, n)
    result = check_one(data, cert)
    if not result['accepted']:
        raise RuntimeError(result['log'])
    result.update(rank=n, spectral=spectral(data))
    return result


def mutations(folder):
    data, cert = read_pair(folder, 6)
    results = []
    changed = copy.deepcopy(data)
    changed['character'][0][0] += 1
    item = check_one(changed, cert)
    if item['accepted'] or 'certificate character mismatch' not in item['log']:
        raise ValueError('character corruption not rejected as intended')
    try:
        spectral(changed)
    except ValueError:
        item['spectral_rejected'] = True
    else:
        raise ValueError('spectral corruption accepted')
    item['mutation'] = 'character'
    results.append(item)
    # Remove the last (identity) cover leaf, adjusting count; no hash/count-only rejection.
    reduced, missing = copy.deepcopy(data), copy.deepcopy(cert)
    missing['parents'].pop()
    reduced['nc_count'] -= 1
    item = check_one(reduced, missing)
    if item['accepted'] or 'missing downward cover' not in item['log']:
        raise ValueError('planted cover gap not rejected as intended')
    item['mutation'] = 'cover'
    results.append(item)
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['produce', 'check', 'corruptions', 'direct-e6'])
    ap.add_argument('--data', type=Path, default=TARGET / 'data')
    ap.add_argument('--ranks', type=int, nargs='+', choices=[6, 7, 8], default=[6, 7, 8])
    ap.add_argument('--workers', type=int, default=3)
    args = ap.parse_args()
    folder = args.data.resolve()
    if args.mode == 'direct-e6':
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / 'direct.json'
            result = gap_run('OUT:=' + json.dumps(str(out)) + ';; Read('
                             + json.dumps(str(HERE / 'direct_e6.g')) + ');\n',
                             'INDEPENDENT E6 PASS')
            if not result['accepted']:
                raise RuntimeError(result['log'])
            direct = json.loads(out.read_text())
            result.update(cpu_ms=direct['cpu_ms'], comparisons=300)
            results = [result]
    elif args.mode == 'corruptions':
        results = mutations(folder)
    else:
        task = produce if args.mode == 'produce' else check
        workers = min(len(args.ranks), max(1, args.workers))
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            results = list(pool.map(lambda n: task(folder, n), args.ranks))
    for row in results:
        print(json.dumps(row))


if __name__ == '__main__':
    main()
