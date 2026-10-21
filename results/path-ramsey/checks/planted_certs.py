#!/usr/bin/env python3
"""Planted errors for the Lean certificate check: each must be rejected by
the kernel, and the unchanged control accepted.

  control        the K_10 / P_6 rung's certificate as made: accepted
  corrupt-step   one lemma's first literal negated: rejected
  drop-hint      the empty clause's last hint dropped: rejected
  bad-path       a path with a repeated vertex: rejected (not a path clause)
  swapped-cnf    the same certificate for the K_13 / P_7 formula: rejected
  swapped-base   encode 18 9 compared with data/cnf/k17p9.cnf instead of
                 k18p10.cnf: rejected

usage: planted_certs.py K10P6_CERT OUTDIR
  (run by check.py, after `lake build R3P10`; OUTDIR is under ../lean/generated)
"""
import os
import subprocess
import sys

LEAN = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean')
M = 6   # vertices per path in the P_6 rung


def dec(b):
    out, acc, sh = [], 0, 0
    for x in b:
        if x >= 64:
            out.append(acc + ((x - 64) << sh)); acc, sh = 0, 0
        else:
            acc += x << sh; sh += 6
    return out


def enc(nums):
    b = bytearray()
    for u in nums:
        while u >= 64:
            b.append(u & 63); u >>= 6
        b.append(64 + u)
    return bytes(b)


def steps(nums):
    """Start index of each proof step, after the paths."""
    i = 1 + nums[0] * (1 + M)
    out = []
    while i < len(nums):
        out.append(i)
        v = nums[i]
        if v == 0:
            i += 2 + nums[i + 1]
        else:
            h = nums[i + v]
            i += v + 1 + h
    return out


def lean(gen, name, body):
    src = os.path.join(gen, name + '.lean')
    with open(src, 'w') as f:
        f.write('import R3P10.Base\nnamespace R3P10\n' + body + '\nend R3P10\n')
    r = subprocess.run(['lake', 'env', 'lean', src], cwd=LEAN, capture_output=True, text=True)
    return r.returncode == 0 and 'error' not in r.stdout, (r.stdout + r.stderr).strip()


def main():
    cert, gen = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
    os.makedirs(gen, exist_ok=True)
    raw = open(cert, 'rb').read()
    nums = dec(raw)
    assert enc(nums) == raw
    st = steps(nums)
    adds = [i for i in st if nums[i] > 1]
    variants = {}
    v = list(nums); i = adds[len(adds) // 2]; v[i + 1] ^= 1          # negate the first literal
    variants['corrupt-step'] = v
    v = list(nums); i = st[-1]; assert v[i] == 1                     # the empty clause
    h = v[i + 1]; v[i + 1] = h - 1; del v[i + 1 + h]
    variants['drop-hint'] = v
    v = list(nums); assert v[0] > 0; v[3] = v[2]                     # path 0: vertex 1 := vertex 0
    variants['bad-path'] = v
    cases = [('control', f'lrat_unsat t 10 6 (encode 10 5) "{cert}"', True)]
    for name, v in variants.items():
        p = os.path.join(gen, name + '.cert')
        open(p, 'wb').write(enc(v))
        cases.append((name, f'lrat_unsat t 10 6 (encode 10 5) "{p}"', False))
    cases.append(('swapped-cnf', f'lrat_unsat t 13 7 (encode 13 6) "{cert}"', False))
    # the file is read relative to the generated source: ../../../data = the bundle's data
    rel = os.path.relpath(os.path.join(LEAN, '..', 'data', 'cnf', 'k17p9.cnf'), gen)
    cases.append(('swapped-base', f'native_decide_thm t : encode 18 9 = parseDimacs (include_str "{rel}")', False))
    bad = 0
    for name, body, want in cases:
        ok, out = lean(gen, name.replace('-', '_'), body)
        good = ok == want
        bad += not good
        err = next((l for l in out.splitlines() if 'error' in l), out[:200])
        why = '' if ok else ' (' + err.split('error: ', 1)[-1][:90] + ')'
        print(f"{'PASS' if good else 'FAIL'} {name}: {'accepted' if ok else 'rejected'}{why}", flush=True)
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
