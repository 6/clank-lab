#!/usr/bin/env python3
"""Planted errors in the Lean development: each one makes the encoding or
its reduction unsound (or unfaithful to the formula the certificates are
for), and `lake build R3P10` must then fail inside the stated declaration.

For each plant: copy the Lean sources to a fresh directory (sharing the
pinned Mathlib build of ../lean/.lake/packages), apply one exact text
replacement and build.

usage: planted_lean.py   (run by check.py, after `lake exe cache get` in ../lean)
"""
import os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN = os.path.join(ROOT, 'lean')

# name, file, old text, new text, expected failure, why the plant is unsound
PLANTS = [
    ('path-clause-drops-an-edge', 'R3P10/Defs.lean',
     '∀ l : Int, l ∈ C ↔ ∃ (i : ℕ) (h : i + 1 < m),\n'
     '      l = -((var (eidx n (p ⟨i, by omega⟩) (p ⟨i + 1, h⟩)) c : ℕ) : Int)',
     '∀ l : Int, l ∈ C ↔ ∃ (i : ℕ) (h : i + 2 < m),\n'
     '      l = -((var (eidx n (p ⟨i, by omega⟩) (p ⟨i + 1, by omega⟩)) c : ℕ) : Int)',
     ('lean', 'paths_ok'),
     'a "path clause" missing its last edge is a P_{m-1} clause; a colouring '
     'with a monochromatic P_{m-1} and no P_m falsifies it'),
    ('encoder-drops-a-clause', 'R3P10/Defs.lean',
     'def fixUnits (n k : ℕ) : CNF := (List.range (k - 1)).map',
     'def fixUnits (n k : ℕ) : CNF := (List.range (k - 2)).map',
     ('lean', 'encode_k18'),
     'the formula Lean reasons about (here without the last fixed-path unit) '
     'would no longer be the one the certificates are for; dropping a clause keeps it sound, '
     'so only a comparison with the formula file can catch it: inside Lean, '
     '`encode_k18` (encode 18 9 = the parsed data/cnf/k18p10.cnf) now fails'),
    ('generator-moves-fixed-path', 'R3P10/Defs.lean',
     'if k ≤ i.val ∧ i < j then',
     'if k ≤ i.val + 1 ∧ i < j then',
     ('lean', 'gens_fix'),
     'the transposition (k-1 k) maps path edge (k-2, k-1) to (k-2, k), which '
     'need not have colour 0: not a symmetry of the fixed-path set'),
    ('fixed-path-one-edge-longer', 'R3P10/Defs.lean',
     'def fixUnits (n k : ℕ) : CNF := (List.range (k - 1)).map',
     'def fixUnits (n k : ℕ) : CNF := (List.range k).map',
     ('lean', 'fixUnits_ok'),
     'the rung below only provides a monochromatic P_k, not the extra edge (k-1, k)'),
    ('lex-comparison-reversed', 'R3P10/Defs.lean',
     '[sd (pre ++ [-A 1, -B 0]), sd (pre ++ [-A 2, -B 0]), sd (pre ++ [-A 2, -B 1]),',
     '[sd (pre ++ [-A 0, -B 1]), sd (pre ++ [-A 0, -B 2]), sd (pre ++ [-A 1, -B 2]),',
     ('lean', 'block_ok'),
     'the clauses would require X >=lex g(X), which the lex-least colouring '
     'of an orbit violates whenever X <lex g(X)'),
    ('skip-ignores-colour-map', 'R3P10/Defs.lean',
     "def skip (g : Gen n) (k : ℕ) : Bool := src g k == k && (List.finRange 3).all fun c => g.col c == c",
     "def skip (g : Gen n) (k : ℕ) : Bool := src g k == k",
     ('lean', 'vec_act_of_skip'),
     'a position fixed by the vertex map but recoloured by the colour map would '
     'be dropped from the comparison; the remaining chain is not implied by X <=lex g(X)'),
    ('k17-edge-recoloured', 'R3P10/Lower.lean',
     '[[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2],  -- row 0',
     '[[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2],  -- row 0',
     ('lean', 'k17_closed'),
     'edge {0, 9} recoloured 1 -> 0 joins the colour-0 cliques on A u B (9 vertices) '
     'and C u D (8), giving a colour-0 path on all 17 vertices (check_colouring.py '
     'rejects the recoloured data/k17-coloring.txt)'),
]

# plants that change the lower-bound colouring: the same change applied to
# data/k17-coloring.txt must give a colouring check_colouring.py 17 10 rejects, so
# the plant really creates a monochromatic P_10
COLOURING_PLANTS = {'k17-edge-recoloured': ('0 9 1\n', '0 9 0\n')}

SOURCES = ['R3P10', 'R3P10.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']


def decl_at(path, line):
    """The declaration (theorem/def/...) enclosing line `line` of `path`."""
    name = None
    with open(path) as f:
        for i, l in enumerate(f, 1):
            if i > line:
                break
            m = re.match(r'\s*(?:private\s+)?(?:theorem|lemma|def|abbrev|axiom|inductive|structure|native_decide_thm)\s+(\S+)', l)
            if m:
                name = m.group(1)
    return name


def run_plant(root, plant, log):
    name, rel, old, new, (kind, decl), why = plant
    proj = os.path.join(root, 'lean')
    p = os.path.join(proj, rel)
    s = open(p).read()
    if s.count(old) != 1:
        return False, f'plant text found {s.count(old)} times (expected once)'
    open(p, 'w').write(s.replace(old, new))
    shutil.rmtree(os.path.join(proj, '.lake', 'build'), ignore_errors=True)
    r = subprocess.run(['lake', 'build', 'R3P10'], cwd=proj, capture_output=True, text=True)
    out = r.stdout + r.stderr
    log.write(f'### {name}\n{out[-4000:]}\n')
    try:
        if kind == 'lean':
            if r.returncode == 0:
                return False, 'lake build succeeded'
            m = re.search(r'error: (R3P10/\w+\.lean):(\d+):\d+:', out)
            if not m:
                return False, 'build failed without a located Lean error'
            where = decl_at(os.path.join(proj, m.group(1)), int(m.group(2)))
            if where != decl:
                return False, f'first error in {where} ({m.group(1)}:{m.group(2)}), expected {decl}'
            if name in COLOURING_PLANTS:
                a, b = COLOURING_PLANTS[name]
                txt = open(os.path.join(ROOT, 'data', 'k17-coloring.txt')).read()
                if txt.count(a) != 1:
                    return False, f'colouring line {a.strip()!r} found {txt.count(a)} times'
                bad = os.path.join(root, 'k17_planted.txt')
                open(bad, 'w').write(txt.replace(a, b))
                c = subprocess.run([sys.executable, os.path.join(HERE, 'check_colouring.py'), '17', '10', bad],
                                   capture_output=True, text=True)
                if c.returncode == 0:
                    return False, 'the recoloured colouring still has no monochromatic P_10'
                return True, (f'lake build fails; first error in {decl} ({m.group(1)}:{m.group(2)}); '
                              f'check_colouring.py finds a monochromatic P_10 in the recoloured colouring')
            return True, f'lake build fails; first error in {decl} ({m.group(1)}:{m.group(2)})'
        return False, f'unknown plant kind {kind}'
    finally:
        open(p, 'w').write(s)


def main():
    report = sys.argv[1] if len(sys.argv) > 1 else None
    tmp = tempfile.mkdtemp(prefix='r3p10-planted-')
    try:
        root = tmp
        proj = os.path.join(root, 'lean')
        os.makedirs(os.path.join(proj, '.lake'))
        for x in SOURCES:
            src = os.path.join(LEAN, x)
            (shutil.copytree if os.path.isdir(src) else shutil.copy)(src, os.path.join(proj, x))
        os.symlink(os.path.join(LEAN, '.lake', 'packages'), os.path.join(proj, '.lake', 'packages'))
        os.symlink(os.path.join(ROOT, 'data'), os.path.join(root, 'data'))
        lines, ok_all = [], True
        with open(os.path.join(tmp, 'planted.log'), 'w') as log:
            for plant in PLANTS:
                ok, msg = run_plant(root, plant, log)
                ok_all &= ok
                lines.append(f'{"PASS" if ok else "FAIL"} {plant[0]}: {msg}. Unsound because {plant[5]}.')
                print(lines[-1], flush=True)
        if report:
            with open(report, 'w') as f:
                f.write('\n'.join(lines) + '\n')
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print('planted errors: all caught' if ok_all else 'planted errors: NOT all caught')
    sys.exit(0 if ok_all else 1)


if __name__ == '__main__':
    main()
