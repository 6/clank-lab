"""Semantic CNF audit, independent of the encoder. See README.md for the rules."""
import itertools
import json
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
TGT = HERE


def receipts():
    rows = json.load(open(os.path.join(HERE, '..', 'data', 'cases.json')))
    out = []
    for row in rows:
        args = row['args']
        n, K = int(args[0]), int(args[1])
        caps = {}
        s0 = None
        rest = args[2:]
        while rest:
            if rest[0] == '--caps':
                caps = {i + 1: int(c) for i, c in enumerate(rest[1].split(','))}
            elif rest[0] == '--s0':
                s0 = int(rest[1])
            else:
                raise ValueError('unexpected encoder argument')
            rest = rest[2:]
        out.append(dict(row, n=n, K=K, enc_caps=caps, s0=s0))
    return out


class Cube:
    def __init__(self, n, captable):
        self.n = n
        self.N = 3 ** n
        self.cap = captable  # proved c_d, d < n
        self.cache = {}
        self.boxcache = {}

    def index(self, x):
        r = 0
        for v in x:
            r = 3 * r + v
        return r + 1

    def bits(self, masks):
        b = self.cache.get(masks)
        if b is None:
            b = 0
            for x in itertools.product(*[[v for v in range(3) if m >> v & 1] for m in masks]):
                b |= 1 << (self.index(x) - 1)
            self.cache[masks] = b
        return b

    def ub(self, masks):
        sizes = [bin(m).count('1') for m in masks]
        d = sizes.count(3)
        mult = 1
        for s in sizes:
            if s < 3:
                mult *= s
        if mult == 0:
            return 0
        if d == self.n:
            return self.N  # the whole cube: no cap of its own dimension
        return mult * self.cap[d]

    def as_box(self, b):
        """masks of the box whose point set is b, or None."""
        if b == 0:
            return None
        if b in self.boxcache:
            return self.boxcache[b]
        masks = [0] * self.n
        pts = []
        x = b
        while x:
            low = x & -x
            i = low.bit_length() - 1
            pts.append(i)
            x ^= low
        for i in pts:
            for c in range(self.n - 1, -1, -1):
                masks[c] |= 1 << (i % 3)
                i //= 3
        masks = tuple(masks)
        r = masks if self.bits(masks) == b else None
        self.boxcache[b] = r
        return r

    def lines(self):
        for w in itertools.product(range(4), repeat=self.n):
            if 3 in w:
                yield frozenset(self.index(tuple(v if c == 3 else c for c in w)) for v in range(3))


def proved_table(lemmas, n):
    """c_d for d < n from the proved lemmas {dim: K} (lemma says c_dim <= K - 1)."""
    t = {0: 1}
    for d in range(1, n):
        t[d] = min(3 * t[d - 1], lemmas[d] - 1) if d in lemmas else 3 * t[d - 1]
    return t


def audit(rec, lemmas, workdir, cnf_override=None, as_s0=None, as_K=None, keep_cnf=False):
    n, K, s0 = rec['n'], as_K or rec['K'], rec['s0'] if as_s0 is None else as_s0
    table = proved_table(lemmas, n)
    cube = Cube(n, table)
    cnf = os.path.join(workdir, rec['name'] + '.cnf')
    mp = os.path.join(workdir, rec['name'] + '.map')
    subprocess.run([sys.executable, os.path.join(TGT, 'encode.py')] + rec['args'] + ['-o', cnf, '--map', mp],
                   check=True, stderr=subprocess.DEVNULL)
    if cnf_override:
        cnf_override(cnf)
    res = {'name': rec['name'], 'n': n, 'K': K, 's0': s0, 'proved_caps_used': table}
    full = tuple([7] * n)
    sem = {}
    for line in open(mp):
        v, m, j = line.split()
        m = tuple(int(c) for c in m)
        assert len(m) == n and all(1 <= c <= 7 for c in m), line
        sem[int(v)] = (m, int(j))

    def lit_sem(lit):
        v = abs(lit)
        if v <= cube.N:
            i = v - 1
            x = []
            for _ in range(n):
                x.append(i % 3)
                i //= 3
            return tuple(1 << c for c in reversed(x)), 1
        return sem[v]

    slices = [tuple([1 << v] + [7] * (n - 1)) for v in range(3)]
    counts = {'LINE': 0, 'UP': 0, 'DOWN': 0, 'CAP': 0, 'PREM': 0}
    bad = []
    seen_lines = set()
    units_pos, order = set(), set()
    neg_units = set()
    with open(cnf) as f:
        hdr = f.readline().split()
        nv, nc = int(hdr[2]), int(hdr[3])
        ncl = 0
        for ln in f:
            cl = [int(x) for x in ln.split()]
            assert cl[-1] == 0
            cl = cl[:-1]
            ncl += 1
            assert all(0 < abs(l) <= nv for l in cl)
            rule = None
            pos = [l for l in cl if l > 0]
            neg = [-l for l in cl if l < 0]
            if not pos and len(neg) == 3 and all(v <= cube.N for v in neg):
                key = frozenset(neg)
                if key in LINES[n]:
                    rule = 'LINE'
                    seen_lines.add(key)
            if rule is None and len(pos) == 1 and neg:
                Sm, k = lit_sem(pos[0])
                S = cube.bits(Sm)
                tot, acc, ok = 0, 0, True
                for v in neg:
                    Pm, j = lit_sem(v)
                    P = cube.bits(Pm)
                    if P & acc or P & ~S:
                        ok = False
                        break
                    acc |= P
                    tot += j
                if ok and tot >= k:
                    rule = 'UP'
            if rule is None and len(neg) == 1 and pos:
                Sm, k = lit_sem(neg[0])
                S = cube.bits(Sm)
                tot, cover = 0, 0
                for v in pos:
                    Pm, j = lit_sem(v)
                    tot += min(j - 1, cube.ub(Pm))
                    cover |= cube.bits(Pm)
                R = S & ~cover
                if R:
                    Rm = cube.as_box(R)
                    tot = tot + cube.ub(Rm) if Rm else None
                if tot is not None and tot <= k - 1:
                    rule = 'DOWN'
            if rule is None and len(cl) == 1 and neg:
                Sm, k = lit_sem(neg[0])
                if cube.ub(Sm) <= k - 1:
                    rule = 'CAP'
            if rule is None:
                # hypotheses of the case
                if len(cl) == 1 and pos:
                    Sm, k = lit_sem(pos[0])
                    if Sm == full and k <= K:
                        rule = 'PREM'
                        units_pos.add(('root', k))
                    elif s0 is not None and Sm == slices[0] and k <= s0:
                        rule = 'PREM'
                        units_pos.add(('s0', k))
                elif len(cl) == 1 and neg:
                    Sm, k = lit_sem(neg[0])
                    if s0 is not None and Sm in slices and k - 1 >= s0:
                        rule = 'PREM'
                elif s0 is not None and len(pos) == 1 and len(neg) == 1:
                    Am, ta = lit_sem(pos[0])
                    Bm, tb = lit_sem(neg[0])
                    if Am in slices and Bm in slices and slices.index(Am) < slices.index(Bm) and ta <= tb:
                        rule = 'PREM'
                        order.add((slices.index(Am), slices.index(Bm), tb))
            if rule is None:
                if len(bad) < 20:
                    bad.append(ln.strip()[:200])
                counts.setdefault('UNJUSTIFIED', 0)
                counts['UNJUSTIFIED'] += 1
            else:
                counts[rule] += 1
            if len(cl) == 1 and neg:
                neg_units.add(lit_sem(neg[0]))
    res['header'] = [nv, nc]
    res['clauses'] = ncl
    res['header_ok'] = ncl == nc and max(sem, default=cube.N) <= nv
    res['rules'] = counts
    res['unjustified_examples'] = bad
    res['sound'] = 'UNJUSTIFIED' not in counts
    res['lines_expected'] = len(LINES[n])
    res['lines_present'] = len(seen_lines)
    complete = {'all_lines': seen_lines == LINES[n], 'root_unit': ('root', K) in units_pos}
    if s0 is not None:
        complete['s0_atleast'] = ('s0', s0) in units_pos
        complete['s0_atmost'] = (slices[0], s0 + 1) in neg_units or cube.ub(slices[0]) <= s0
        # order clauses a_0 >= a_1 >= a_2 for every threshold up to the slice cap
        top = cube.ub(slices[0])
        complete['order_01'] = all((0, 1, t) in order for t in range(1, top + 1))
        complete['order_12'] = all((1, 2, t) in order for t in range(1, top + 1))
    res['complete'] = complete
    res['ok'] = res['sound'] and res['header_ok'] and all(complete.values())
    if not keep_cnf:
        os.unlink(cnf)
    os.unlink(mp)
    return res


LINES = {}


def main():
    out = sys.argv[1]
    t0 = time.time()
    recs = receipts()
    for n in sorted({r['n'] for r in recs}):
        LINES[n] = set(Cube(n, {}).lines())
        assert len(LINES[n]) == 4 ** n - 3 ** n
    work = tempfile.mkdtemp(prefix='dhj-red-')
    report = {'cases': [], 'controls': []}
    # lemmas in order; each formula may only use what is proved before it
    lemmas = {}
    lem = [r for r in recs if r['s0'] is None]
    main_cases = [r for r in recs if r['s0'] is not None]
    for r in sorted(lem, key=lambda r: r['n']):
        a = audit(r, dict(lemmas), work)
        a['proves'] = 'c_%d <= %d (if UNSAT)' % (r['n'], r['K'] - 1)
        report['cases'].append(a)
        print(a['name'], a['ok'], a['rules'], file=sys.stderr)
        lemmas[r['n']] = r['K']
    for r in sorted(main_cases, key=lambda r: -r['s0']):
        a = audit(r, dict(lemmas), work)
        report['cases'].append(a)
        print(a['name'], a['ok'], a['rules'], a['complete'], file=sys.stderr)
    # cover
    n = 7
    K = main_cases[0]['K']
    assert all(r['n'] == n and r['K'] == K for r in main_cases)
    c6 = proved_table(lemmas, n)[6]
    need = [s for s in range(0, c6 + 1) if 3 * s >= K]
    have = sorted(r['s0'] for r in main_cases)
    report['cover'] = {'K': K, 'c6_proved': c6, 's0_needed': [need[0], need[-1]] if need else [],
                       'ok': have == need, 'lemma_chain': {str(d): k - 1 for d, k in lemmas.items()}}
    # controls: each must fail
    s440 = next(r for r in main_cases if r['s0'] == 440)
    L5 = next(r for r in lem if r['n'] == 5)

    def drop_first_line(path):
        with open(path) as f:
            hdr = f.readline().split()
            body = f.readlines()
        del body[0]
        with open(path, 'w') as f:
            f.write('p cnf %s %d\n' % (hdr[2], len(body)))
            f.writelines(body)

    ctl = [('drop-line s440', audit(s440, dict(lemmas), work, cnf_override=drop_first_line)),
           ('cap-loose L5 audited with c_4 <= 53', audit(L5, {1: 3, 4: 54}, work)),
           ('s0-shift s440 audited as s0 = 441', audit(s440, dict(lemmas), work, as_s0=441)),
           ('K-low s440 audited as K = 1302', audit(s440, dict(lemmas), work, as_K=1302))]
    for label, a in ctl:
        report['controls'].append({'control': label, 'rejected': not a['ok'], 'sound': a['sound'], 'rules': a['rules'], 'complete': a['complete'],
                                   'lines_present': a['lines_present'],
                                   'unjustified_examples': a['unjustified_examples'][:3]})
        print(label, 'rejected' if not a['ok'] else 'NOT REJECTED', file=sys.stderr)
    report['all_cases_ok'] = all(a['ok'] for a in report['cases'])
    report['all_controls_rejected'] = all(c['rejected'] for c in report['controls'])
    report['seconds'] = round(time.time() - t0, 1)
    with open(out, 'w') as f:
        json.dump(report, f, indent=1)
    os.rmdir(work)
    if not (report['all_cases_ok'] and report['cover']['ok'] and report['all_controls_rejected']):
        raise SystemExit('FAIL reduction')
    print('all_cases_ok', report['all_cases_ok'], 'cover', report['cover']['ok'],
          'controls_rejected', report['all_controls_rejected'])


if __name__ == '__main__':
    main()
