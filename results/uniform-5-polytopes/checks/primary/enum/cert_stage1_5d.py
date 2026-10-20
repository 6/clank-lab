"""Certified 5-D stage 1: polygon neighbourhoods (cycles of 4-D facets around a p-gon)
and their radius intervals.  Inputs: cert_facets4_pPMAX.json (rigorous facet data),
cell radii from cert_poly3.  usage: cert_stage1_5d.py PMAX -> cert_stage1_5d_pPMAX.json"""
import sys, json
from flint import arb, ctx
import cert_poly3 as cp
from cert_stage1 import certify_cycle, cell_configs, r_interval

ctx.prec = 160
PI = arb.pi()
TWO_PI = 2 * PI


def ball(mid, rad):
    m = arb(mid.strip('[').split(' ')[0])
    r = float(rad.strip('[').split(' ')[0]) * 2 + 1e-35
    return m + arb(0, r)  # widen: stored radius (twice) plus decimal rounding of the midpoint


def main(pmax):
    facets = json.load(open('cert_facets4_p%d.json' % pmax))
    conf = cell_configs(128)   # lookup table only; was 16, which broke pmax > 16
    cellR = {}
    def cR(c):
        if c not in cellR:
            cellR[c] = cp.data(conf[c])['R']
        return cellR[c]
    facR = {f['name']: ball(*f['R']) for f in facets}
    sides = {}
    for f in facets:
        for p, a, b, mid, rad in f['orbits']:
            al = ball(mid, rad)
            sides.setdefault(p, []).append((f['name'], a, b, al))
            if a != b:
                sides[p].append((f['name'], b, a, al))
    out = []
    for p, S in sides.items():
        rho = 1 / (2 * (PI / p).sin())
        found = {}
        def canon(seq):
            k = len(seq); c = []
            for r in range(k):
                rot = seq[r:] + seq[:r]
                c.append(tuple((x[0], x[1], x[2]) for x in rot))
                c.append(tuple((x[0], x[2], x[1]) for x in reversed(rot)))
            return min(c)
        def dfs(seq, tot):
            if len(seq) >= 3 and seq[-1][2] == seq[0][1]:
                found.setdefault(canon(seq), list(seq))
            if len(seq) == 8:
                return
            for s in S:
                if seq and s[1] != seq[-1][2]:
                    continue
                t2 = tot + s[3]
                if t2 >= TWO_PI:
                    continue
                seq.append(s); dfs(seq, t2); seq.pop()
        dfs([], arb(0))
        for seq in found.values():
            rayR = [cR(s[2]) for s in seq]
            alphas = [s[3] for s in seq]
            Rmin = max([facR[s[0]] for s in seq] + [rho], key=lambda b: float(b.mid()))
            roots, nb = certify_cycle(rho, rayR, alphas, 1 / Rmin)
            rec = dict(p=p, facets=[s[0] for s in seq], cells=[s[2] for s in seq], boxes=nb)
            if roots is None:
                rec['status'] = 'UNDECIDED'
            else:
                rec['status'] = 'ROOT' if roots else 'NOROOT'
                rec['R'] = [r_interval(a, b) for a, b in roots]
            out.append(rec)
    print(len(out), 'cycles;', sum(r['status'] == 'ROOT' for r in out), 'with roots;',
          sum(r['status'] == 'UNDECIDED' for r in out), 'undecided', file=sys.stderr)
    return out


if __name__ == '__main__':
    pmax = int(sys.argv[1])
    json.dump(main(pmax), open('cert_stage1_5d_p%d.json' % pmax, 'w'), indent=0)
