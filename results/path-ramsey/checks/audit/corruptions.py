#!/usr/bin/env python3
"""Corruptions the encoding auditor must reject, both ways.

usage: corruptions.py WORKDIR

Each control builds one corrupted artifact from the data files (or from
a patched copy of the pinned encoder, for a mis-stated reduction), runs
audit.py on it and requires FAIL; the matching uncorrupted run must pass.
One control is marked accepted by design and must pass (the lazy log).
Prints one line per control and exits 0 iff every control behaves.

  dropped path clause    (completeness) one clause removed from the eager
                         path-clause set of a small instance;
  over-strong clauses    (soundness) an extra unit on K_18, a lex-leader
                         inequality with its prefix condition dropped, a
                         lex-leader inequality in the wrong direction;
  bad logged clauses     a P_9 clause and a two-colour clause in the K_18 log;
  mis-stated reductions  an extra generator moving a path vertex, the colour
                         swap 0 <-> 1 instead of 1 <-> 2, a fixed P_10, a
                         fixed path with no rung below it, and a fixed P_4 on
                         K_5 (where R_3(P_4) = 6), the last run once more
                         with the lemma checks off, to show the exhaustive
                         class check catches it by itself;
  an outside review's    colours 1/2 swapped
                         on one edge, one edge's exactly-one block deleted,
                         every base clause deleted, every colour-2 path
                         clause deleted from an eager set, the same set as
                         a lazy log (accepted by design: ../README.md, L7), units
                         forcing a colour-0 triangle;
  inventory              a valid but ungenerated clause, a repeated clause;
  generated set          the auditor's own generated clauses mutated four
                         ways (inequality direction, prefix dropped,
                         definition or monotonicity clause dropped): its
                         group-by-group meaning check must catch each; and
                         a compared position dropped from one derivation.
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKS = os.path.dirname(HERE)
DATA = os.path.join(os.path.dirname(CHECKS), 'data')
AUDIT = os.path.join(HERE, 'audit.py')
PY = sys.executable


def audit(*args):
    r = subprocess.run([PY, AUDIT] + [str(a) for a in args], capture_output=True, text=True)
    return r.returncode, (r.stdout.strip().splitlines() or [''])[-1]


def read(path):
    hdr, cls = None, []
    for line in open(path):
        if line.startswith('c'):
            continue
        if line.startswith('p'):
            hdr = line.split()
        else:
            cls.append([int(x) for x in line.split()[:-1]])
    return int(hdr[2]), cls


def write(path, nv, cls):
    with open(path, 'w') as f:
        f.write(f'p cnf {nv} {len(cls)}\n')
        for c in cls:
            f.write(' '.join(map(str, c)) + ' 0\n')


def edge(n, a, b):
    E = [(i, j) for i in range(n) for j in range(i + 1, n)]
    return E.index((a, b))


def x(n, a, b, c):
    return 3 * edge(n, a, b) + c + 1


def patched_encoder(w, name, old, new):
    src = open(os.path.join(CHECKS, 'encode.py')).read()
    if src.count(old) != 1:
        sys.exit(f'{name}: patch does not apply to encode.py')
    p = os.path.join(w, f'encode-{name}.py')
    with open(p, 'w') as f:
        f.write(src.replace(old, new))
    return p


def encode(w, enc, n, m, k, name):
    out = os.path.join(w, name)
    with open(out, 'w') as f:
        subprocess.run([PY, enc, str(n), str(m), '--fix', str(k)], stdout=f, check=True)
    return out


def stated(n, k):
    sys.path.insert(0, HERE)
    import audit as A
    return [[list(p), list(s)] for p, s in A.stated_generators(n, k)]


def main():
    w = os.path.abspath(sys.argv[1])
    os.makedirs(w, exist_ok=True)
    cnf18 = os.path.join(DATA, 'cnf', 'k18p10.cnf')
    genlog = os.path.join(DATA, 'k18', 'genlog.txt')
    results = []

    def expect(name, args, must_fail=True):
        rc, msg = audit(*args)
        ok = (rc != 0) == must_fail and (msg.startswith('FAIL') == must_fail)
        results.append(ok)
        print(f'{"ok  " if ok else "BAD "} {name}: {"rejected" if rc else "accepted"}: {msg}')

    # the originals pass
    expect('original K_18 formula', ['cnf', cnf18, 18, 10, 9], False)
    expect('original K_18 generation log', ['paths', 18, 10, genlog], False)

    # 1. dropped path clause: the eager clause set of K_5, P_4 minus one
    full = os.path.join(w, 'paths-5-4.txt')
    expect('original eager K_5, P_4 (fixed P_3)', ['small', 5, 4, 3, '--dump-paths', full], False)
    lines = open(full).read().splitlines(True)
    dropped = os.path.join(w, 'paths-5-4-dropped.txt')
    open(dropped, 'w').writelines(lines[:7] + lines[8:])
    expect('dropped path clause (eager K_5, P_4)', ['small', 5, 4, 3, '--paths', dropped])

    # 2. over-strong clauses in the K_18 formula
    nv, cls = read(cnf18)
    bad = os.path.join(w, 'unit.cnf')
    write(bad, nv, cls + [[-x(18, 12, 15, 1)]])
    expect('extra unit: edge (12,15) not colour 1', ['cnf', bad, 18, 10, 9])

    ne = 18 * 17 // 2
    path = {edge(18, t, t + 1) for t in range(8)}
    pick = next(i for i, c in enumerate(cls)
                if len(c) == 3 and sum(abs(l) > 3 * ne for l in c) == 1 and all(l < 0 for l in c)
                and len({(abs(l) - 1) // 3 for l in c if abs(l) <= 3 * ne} - path) == 2)
    drop = [l for l in cls[pick] if abs(l) <= 3 * ne]
    bad = os.path.join(w, 'prefix.cnf')
    write(bad, nv, cls[:pick] + [drop] + cls[pick + 1:])
    expect(f'inequality without its prefix: clause {pick + 1} {cls[pick]} -> {drop}', ['cnf', bad, 18, 10, 9])

    # generator 0 is the transposition (9 10); its first compared position is
    # edge (0,9), whose image is X(0,10).  X(0,9) = 1 < 2 = X(0,10) is allowed.
    wrong = [-x(18, 0, 9, 1), -x(18, 0, 10, 2)]
    bad = os.path.join(w, 'direction.cnf')
    write(bad, nv, cls + [wrong])
    expect(f'inequality in the wrong direction {wrong}', ['cnf', bad, 18, 10, 9])

    # 3. bad logged clauses
    g = [[int(t) for t in l.split()[:-1]] for l in open(genlog)]
    bad = os.path.join(w, 'short.log')
    open(bad, 'w').write(''.join(' '.join(map(str, c)) + ' 0\n' for c in g[:3] + [g[3][:-1]] + g[4:]))
    expect('logged P_9 clause in the P_10 log', ['paths', 18, 10, bad])
    c0 = g[0][:]
    c0[0] = -(((-c0[0] - 1) // 3) * 3 + ((-c0[0] - 1) % 3 + 1) % 3 + 1)
    bad = os.path.join(w, 'mixed.log')
    open(bad, 'w').write(''.join(' '.join(map(str, c)) + ' 0\n' for c in [c0] + g[1:]))
    expect('logged two-colour clause', ['paths', 18, 10, bad])

    # 4. mis-stated reductions
    swap_line = '            gens.append((list(range(n)), [0, 2, 1]))\n        else:'
    enc = patched_encoder(w, 'extra', swap_line,
                          '            gens.append((list(range(n)), [0, 2, 1]))\n'
                          '            gens.append((transp(fixk - 1, fixk), ident_s))\n        else:')
    bad = encode(w, enc, 18, 10, 9, 'extra.cnf')
    expect('formula with an extra generator (8 9), audited against the stated reduction',
           ['cnf', bad, 18, 10, 9])
    gj = os.path.join(w, 'gens-extra.json')
    t = list(range(18)); t[8], t[9] = 9, 8
    json.dump(stated(18, 9) + [[t, [0, 1, 2]]], open(gj, 'w'))
    expect('extra generator (8 9) stated: moves a path vertex', ['cnf', bad, 18, 10, 9, '--gens', gj])

    enc = patched_encoder(w, 'swap01', swap_line,
                          '            gens.append((list(range(n)), [1, 0, 2]))\n        else:')
    bad = encode(w, enc, 18, 10, 9, 'swap01.cnf')
    gj = os.path.join(w, 'gens-swap01.json')
    json.dump(stated(18, 9)[:-1] + [[list(range(18)), [1, 0, 2]]], open(gj, 'w'))
    expect('colour swap 0 <-> 1 with a fixed colour-0 path', ['cnf', bad, 18, 10, 9, '--gens', gj])
    # the same on K_5, P_4, fixed P_3, lemma checks off: the class check alone
    bad5 = encode(w, enc, 5, 4, 3, 'swap01-5.cnf')
    gj5 = os.path.join(w, 'gens-swap01-5.json')
    json.dump(stated(5, 3)[:-1] + [[list(range(5)), [1, 0, 2]]], open(gj5, 'w'))
    expect('colour swap 0 <-> 1 on K_5, P_4 (stabiliser lemma on)',
           ['small', 5, 4, 3, '--cnf', bad5, '--gens', gj5])
    # With the lemma checks off this one is accepted, correctly: in K_5 the
    # swap's first compared position is the path edge (0,1), so its
    # inequality never binds and every class survives.  The stabiliser
    # condition is sufficient, not necessary; ../README.md, lemma L3.

    rj = os.path.join(w, 'rungs-p10.json')
    json.dump([[5, 3, 0], [6, 4, 3], [9, 5, 4], [10, 6, 5], [13, 7, 6], [14, 8, 7], [17, 9, 8], [18, 10, 10]],
              open(rj, 'w'))
    expect('fixed P_10 on K_18 (assumes what is to be proved)', ['ladder', '--rungs', rj])
    rj = os.path.join(w, 'rungs-gap.json')
    json.dump([[5, 3, 0], [6, 4, 3], [9, 5, 4], [10, 6, 5], [13, 7, 6], [14, 8, 7], [18, 10, 9]],
              open(rj, 'w'))
    expect('fixed P_9 on K_18 with the K_17 rung removed', ['ladder', '--rungs', rj])

    expect('fixed P_4 on K_5 (R_3(P_4) = 6): premise check', ['small', 5, 5, 4])
    expect('fixed P_4 on K_5 (lemma checks off: exhaustive class check)', ['small', 5, 5, 4, '--no-lemma'])

    # 5. an outside review's corruptions, rebuilt here from the data files
    #    and the encoder
    a = x(18, 12, 15, 1)
    swap = {a: a + 1, a + 1: a}
    bad = os.path.join(w, 'permuted-map.cnf')
    write(bad, nv, [[(1 if l > 0 else -1) * swap.get(abs(l), abs(l)) for l in c] for c in cls])
    expect('review: colours 1/2 swapped on edge (12,15) throughout the K_18 base', ['cnf', bad, 18, 10, 9])
    ev = {x(18, 12, 15, c) for c in range(3)}
    weak = [c for c in cls if not {abs(l) for l in c} <= ev]
    assert len(cls) - len(weak) == 4
    bad = os.path.join(w, 'missing-exactly-one.cnf')
    write(bad, nv, weak)
    expect('review: the four exactly-one clauses of edge (12,15) deleted, header repaired',
           ['cnf', bad, 18, 10, 9])
    bad = os.path.join(w, 'header-only.cnf')
    write(bad, nv, [])
    expect('review: every K_18 base clause deleted, variable count kept', ['cnf', bad, 18, 10, 9])
    nocol2 = os.path.join(w, 'paths-5-4-no-colour-2.txt')
    open(nocol2, 'w').writelines(l for l in lines if (-int(l.split()[0]) - 1) % 3 != 2)
    expect('review: every colour-2 path clause deleted from eager K_5, P_4', ['small', 5, 4, 3, '--paths', nocol2])
    # Accepted by design: `paths` checks that each logged clause is a path
    # clause, never that the log covers every path.  A refuted formula
    # missing path clauses is weaker, so its UNSAT still excludes every good
    # colouring (../README.md, L7).
    expect('review: the same incomplete set as a lazy log (accepted by design, L7)',
           ['paths', 5, 4, nocol2], False)
    nv5, cls5 = read(encode(w, os.path.join(CHECKS, 'encode.py'), 5, 5, 3, 'k5p5f3.cnf'))
    bad = os.path.join(w, 'triangle.cnf')
    write(bad, nv5, cls5 + [[x(5, a, b, 0)] for a, b in [(0, 1), (0, 2), (1, 2)]])
    expect('review: units forcing a colour-0 triangle on K_5, P_5, fixed P_3', ['cnf', bad, 5, 5, 3])

    # 6. inventory: clauses true for every admissible colouring, but not
    #    the generated set (the clause check alone accepts these)
    bad = os.path.join(w, 'implied-extra.cnf')
    write(bad, nv, cls + [[x(18, 12, 15, 0), x(18, 12, 15, 1), x(18, 12, 15, 2), x(18, 0, 17, 0)]])
    expect('extra clause implied by exactly-one (valid, not generated)', ['cnf', bad, 18, 10, 9])
    bad = os.path.join(w, 'duplicate.cnf')
    write(bad, nv, cls + [cls[0]])
    expect('a base clause repeated', ['cnf', bad, 18, 10, 9])

    # 7. the auditor's generated set is checked against the stated meaning
    #    group by group; a wrongly generated group must be caught in every
    #    auxiliary group it changes
    sys.path.insert(0, HERE)
    import audit as A
    E = A.Encoding(18, 9, A.stated_generators(18, 9))
    for mutant in ('direction', 'no-prefix', 'no-definition', 'no-monotone'):
        groups = [gr for gr in E.generated(mutant) if gr[0][0] == 'aux']
        if mutant in ('no-prefix', 'no-monotone'):      # no prefix at j = 1
            groups = [gr for gr in groups if E.aux[gr[0][1]][1] > 1]
        caught = 0
        for gr in groups:
            try:
                E.check_generated_meaning([gr])
            except A.Fail:
                caught += 1
        ok = caught == len(groups)
        results.append(ok)
        print(f'{"ok  " if ok else "BAD "} generated set mutated ({mutant}), K_18: caught in '
              f'{caught}/{len(groups)} auxiliary groups it changes')

    # one compared position dropped from the auditor's own derivation
    E = A.Encoding(18, 9, A.stated_generators(18, 9))
    E.comp[0] = E.comp[0][1:]
    try:
        E.check_positions()
        ok, msg = False, 'accepted'
    except A.Fail as e:
        ok, msg = True, f'rejected: FAIL {e}'
    results.append(ok)
    print(f'{"ok  " if ok else "BAD "} first compared position of generator 0 dropped from one derivation: {msg}')

    print(f'{sum(results)}/{len(results)} controls behave')
    sys.exit(0 if all(results) else 1)


if __name__ == '__main__':
    main()
