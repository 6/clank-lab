#!/usr/bin/env python3
"""GPT-6 Astra: render/check the human-readable appendix from the frozen data.

This is a presentation consistency check, not a third independent obstruction
implementation. checker_a.py and checker_b.py establish the two proofs.
"""
import argparse
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BEGIN = '% BEGIN generated certificate appendix\n'
END = '% END generated certificate appendix\n'


def render(doc):
    cycles, pairs = doc['cycles'], doc['pairs']
    edges = [[tuple(sorted((a, b))) for a, b in zip(c, c[1:] + c[:1])]
             for c in cycles]
    boundary = Counter()
    parities = []
    for i, j in pairs:
        for e in edges[i]:
            boundary[e, j] += 1
        for e in edges[j]:
            boundary[e, i] += 1
        parity = 0
        for a, b in edges[i]:
            for c, d in edges[j]:
                first = {a, b, doc['vertices'] + i}
                order = sorted(first | {c, d, doc['vertices'] + j})
                parity ^= int(set(order[::2]) == first or set(order[1::2]) == first)
        parities.append(parity)
    if any(v % 2 for v in boundary.values()) or sum(parities) % 2 != 1:
        raise RuntimeError('appendix source does not certify an odd cycle')
    out = [r'\begin{appendices}', r'\section{The explicit certificate}\label{app:certificate}',
           r'The following lists completely specify the subcomplex $P$ and the cycle',
           r'$\bar z=\sum_{(i,j)\in S}[\Delta_i\times \Delta_j]$ in the unordered deleted product.',
           r'A row $(v_0,\ldots,v_r)$ denotes the closed cycle with successive edges',
           r'$v_0v_1,\ldots,v_{r-1}v_r,v_rv_0$. All indices start at zero.',
           r'\begin{center}\small', r'\begin{tabular}{r l @{\qquad} r l}',
           r'$i$ & $C_i$ & $i$ & $C_i$\\\hline']
    for i in range(23):
        out.append(f'{i} & $({",".join(map(str,cycles[i]))})$ & '
                   f'{i+23} & $({",".join(map(str,cycles[i+23]))})$'+r'\\')
    out += [r'\end{tabular}\end{center}',
            r'For every graph edge $e$ and every disk index $j$, count the selected',
            r'pairs containing $j$ whose other cycle contains $e$. These are the',
            r'coefficients of $\partial\bar z$; every count is even. The nonzero',
            r'integer counts have the following multiplicities: '+
            ', '.join(f'{v} occurs {n} times' for v,n in sorted(Counter(boundary.values()).items()))+'.',
            r'Thus $\partial\bar z=0$; equivalently the ordered lift $z$ is a cycle.',
            r'\par The table below lists every pair in $S$ and its moment-curve',
            r'intersection coefficient $\theta_{ij}$. For a direct check, cone $C_i$',
            r'to parameter $11+i$ and order each six-element set of two disjoint',
            r'triangles. A triangle pair contributes one exactly when its two',
            r'triples alternate in that order. Sum these contributions for each',
            r'disk pair and reduce modulo two.',
            r'\begin{center}\small',
            r'\begin{tabular}{r r r @{\qquad} r r r @{\qquad} r r r}',
            r'$i$&$j$&$\theta_{ij}$&$i$&$j$&$\theta_{ij}$&$i$&$j$&$\theta_{ij}$\\\hline']
    for row in range(27):
        cells=[]
        for k in (row,row+27,row+54):
            cells.extend(map(str, (*pairs[k],parities[k])) if k<len(pairs) else ['','',''])
        out.append(' & '.join(cells)+r'\\')
    out += [r'\end{tabular}\end{center}',
            f'Exactly {sum(parities)} of the 79 listed coefficients are one. Hence',
            r'$\langle\theta,\bar z\rangle=1$ in $\mathbf F_2$. The ordered-lift',
            r'half-chain calculation independently gives $I(z)=1$.',
            r'The public check regenerates this appendix from \texttt{data/h.json}',
            r'and requires an exact match; both obstruction checkers independently',
            r'verify the underlying certificate.', r'\end{appendices}']
    return '\n'.join(out)+'\n'


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true')
    args=ap.parse_args()
    expected=render(json.loads((ROOT/'data/h.json').read_text()))
    target=ROOT/'paper/paper.tex'
    source=target.read_text()
    if source.count(BEGIN)!=1 or source.count(END)!=1:
        raise RuntimeError('paper must have exactly one generated appendix region')
    before, tail=source.split(BEGIN)
    actual, after=tail.split(END)
    if args.write:
        target.write_text(before+BEGIN+expected+END+after)
    elif actual!=expected:
        raise RuntimeError('paper appendix differs from certificate data')
    print('PASS: appendix matches all 46 cycles, 79 pairs and their odd intersection sum.')


if __name__=='__main__':
    main()
