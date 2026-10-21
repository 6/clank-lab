#!/usr/bin/env python3
"""Repack a drat-trim LRAT refutation of BASE + LOG + UNITS (the file
check.py hands to drat-trim and cake_lpr) for Lean's LRAT checker
(../lean/R3P10/Cert.lean).

Lean checks the formula F ++ P, where F = BASE ++ UNITS (`encode 18 9 ++
cubeUnits c`, or BASE ++ negated cubes for the cover) and P holds, in order,
the path clauses of LOG that the proof uses, each given as a colour and a
vertex sequence (Lean rebuilds the clause and checks the path is valid).
Clause ids are renumbered to that order, lemma ids made consecutive after
it, and deletions of unused clauses dropped.  Nothing here is trusted: a
wrong repack makes the Lean check fail.

usage: pack.py BASE_CNF LOG NUNITS LRAT OUT_PREFIX --compact [--units-first]
  --compact writes OUT_PREFIX.cert, one string in the format decoded by
  `decodeCert` in ../lean/R3P10/Cert.lean (without it: OUT_PREFIX.paths and
  OUT_PREFIX.lrat, text or --binary, for Lean's own LRAT parser).
  --units-first: the input file has the units (or negated cubes) before
  LOG; default: BASE, LOG, UNITS.
"""
import sys



def edge_table(n):
    ed = [(i, j) for i in range(n) for j in range(i + 1, n)]
    return ed


def path_of(clause, ed):
    """Colour and vertex order of a path clause, or raise."""
    cs = set()
    adj = {}
    for l in clause:
        assert l < 0, clause
        v = -l - 1
        e, c = divmod(v, 3)
        cs.add(c)
        a, b = ed[e]
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    assert len(cs) == 1, clause
    ends = [v for v, nb in adj.items() if len(nb) == 1]
    assert len(ends) == 2 and all(len(nb) <= 2 for nb in adj.values()), clause
    p = [min(ends)]
    prev = None
    while len(p) < len(adj):
        nxt = [w for w in adj[p[-1]] if w != prev]
        prev = p[-1]
        p.append(nxt[0])
    assert len(set(p)) == len(p) == len(clause) + 1, clause
    return cs.pop(), p


def vertices(path):
    """n, from the encoder's header line `c encode.py n=.. m=..`."""
    with open(path) as f:
        for l in f:
            if l.startswith('c encode.py'):
                return int(l.split()[2].split('=')[1])
    raise ValueError('no encode.py header')


def count_clauses(path):
    n = 0
    with open(path) as f:
        for l in f:
            if l[0] not in 'cp' and l.strip():
                n += 1
    return n


def main():
    a = sys.argv[1:]
    binary = '--binary' in a
    compact = '--compact' in a
    units_first = '--units-first' in a
    a = [x for x in a if not x.startswith('--')]
    base, logp, nu, lratp, out = a[0], a[1], int(a[2]), a[3], a[4]
    nb = count_clauses(base)
    log = [list(map(int, l.split()))[:-1] for l in open(logp) if l.strip()]
    nl = len(log)
    if units_first:
        log0, unit0 = nb + nu, nb          # full ids: log nb+nu+1.., units nb+1..
    else:
        log0, unit0 = nb, nb + nl
    # pass 1: which log clauses the proof uses
    used = set()
    with open(lratp) as f:
        for line in f:
            t = line.split()
            if t[1] == 'd':
                continue
            z = t.index('0', 1)
            for x in t[z + 1:-1]:
                h = abs(int(x))
                if log0 < h <= log0 + nl:
                    used.add(h)
    order = sorted(used)
    ed = edge_table(vertices(base))
    idmap = {}
    for i in range(1, nb + 1):
        idmap[i] = i
    for j in range(nu):
        idmap[unit0 + 1 + j] = nb + 1 + j
    nxt = nb + nu + 1
    paths = []
    for h in order:
        paths.append(path_of(log[h - log0 - 1], ed))
        idmap[h] = nxt
        nxt += 1
    if compact:
        emit_compact(lratp, out + '.cert', idmap, nxt, paths)
        return
    with open(out + '.paths', 'w') as o:
        for c, p in paths:
            o.write(f"{c} {' '.join(map(str, p))}\n")
    emit(lratp, out + '.lrat', idmap, nxt, binary)


def c64(u, buf):
    """Little-endian base-64 digits: 0..63 continue, 64..127 end."""
    while u >= 64:
        buf.append(u & 63)
        u >>= 6
    buf.append(64 + u)


def emit_compact(lratp, outp, idmap, nxt, paths):
    buf = bytearray()
    c64(len(paths), buf)
    for c, p in paths:
        c64(c, buf)
        for v in p:
            c64(v, buf)
    with open(outp, 'wb') as o, open(lratp) as f:
        for line in f:
            t = line.split()
            if t[1] == 'd':
                ids = sorted(idmap[int(x)] for x in t[2:-1] if int(x) in idmap)
                if not ids:
                    continue
                c64(0, buf); c64(len(ids), buf)
                last = 0
                for x in ids:
                    c64(x - last, buf); last = x
            else:
                z = t.index('0', 1)
                lits = [int(x) for x in t[1:z]]
                hints = [int(x) for x in t[z + 1:-1]]
                assert all(h > 0 for h in hints), 'RAT hints are not supported'
                idmap[int(t[0])] = nxt
                c64(len(lits) + 1, buf)
                for l in lits:
                    c64(2 * l if l > 0 else 2 * -l + 1, buf)
                c64(len(hints), buf)
                for h in hints:
                    d = nxt - idmap[h]
                    assert d > 0
                    c64(d, buf)
                nxt += 1
            if len(buf) > 1 << 20:
                o.write(buf); buf.clear()
        o.write(buf)


def emit(lratp, outp, idmap, nxt, binary):
    def mapid(h):
        return idmap[h]
    o = open(outp, 'wb')
    last = None
    with open(lratp) as f:
        for line in f:
            t = line.split()
            if t[1] == 'd':
                ids = [idmap[int(x)] for x in t[2:-1] if int(x) in idmap]
                if not ids:
                    continue
                if binary:
                    o.write(b'd' + b''.join(venc(2 * i) for i in ids) + b'\x00')
                else:
                    o.write(f"{last if last else nxt - 1} d {' '.join(map(str, ids))} 0\n".encode())
                continue
            z = t.index('0', 1)
            lits = t[1:z]
            hints = [int(x) for x in t[z + 1:-1]]
            idmap[int(t[0])] = nxt
            hs = [(1 if x > 0 else -1) * idmap[abs(x)] for x in hints]
            if binary:
                o.write(b'a' + venc(2 * nxt) + b''.join(venc(lenc(int(l))) for l in lits) + b'\x00'
                        + b''.join(venc(lenc(h)) for h in hs) + b'\x00')
            else:
                o.write(f"{nxt} {' '.join(lits + ['0'] + [str(h) for h in hs])} 0\n".encode())
            last = nxt
            nxt += 1
    o.close()


def lenc(x):
    return 2 * x if x > 0 else 2 * (-x) + 1


def venc(u):
    b = bytearray()
    while u >= 0x80:
        b.append((u & 0x7f) | 0x80)
        u >>= 7
    b.append(u)
    return bytes(b)


if __name__ == '__main__':
    main()
