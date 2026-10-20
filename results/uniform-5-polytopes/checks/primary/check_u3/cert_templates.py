"""Certify every facet template named in a vertex-figure input (or listed in a
names file, one per line) and print one line per template: name, vertices,
neighbours of the base, |Stab(base)|, |Sym| = |Stab| * |V| (vertex-transitive),
cells through the base and their labels, the model's extra symmetries.

usage: python cert_templates.py (VFS.json | NAMES.txt)
Every certification failure raises (templates.py, tcert.py)."""
import json
import sys
import time
import templates
from templates import template
from model_runtime import ensure_guard


def main():
    ensure_guard()
    src = sys.argv[1]
    if src.endswith('.json'):
        data = json.load(open(src))
        names = sorted({f for c in data for vf in c['vfs'] for f in vf['facets']})
    else:
        names = [x.strip() for x in open(src) if x.strip()]
    t0 = time.process_time()
    for n in names:
        T = template(n)
        labels = ','.join(sorted({c['label'] for c in T.cells}))
        extra = ','.join(getattr(T.model, 'extra', [])) or '-'
        print('%-20s V=%-6d nb=%-3d stab=%-4d sym=%-6d cells=%-3d %s extra=%s'
              % (n, T.n, len(T.nb), len(T.stab), len(T.stab) * T.n, len(T.cells), labels, extra))
    g = templates.GAPS
    print('templates certified: %d; cells certified: %d; symmetry cosets certified: %d'
          % (g['templates'], g['cells'], g['trans_certified']))
    print('candidates rejected (certified): Gram %d, orthogonality %d, vertex image %d'
          % (g['rejected_gram'], g['rejected_orth'],
             g['rejected_vertex_local'] + g['rejected_vertex_global']))
    print('CPU seconds: %.1f' % (time.process_time() - t0), file=sys.stderr)


if __name__ == '__main__':
    main()
