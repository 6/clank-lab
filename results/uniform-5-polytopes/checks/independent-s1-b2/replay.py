"""Reconstruct stage 1 without consuming any previous computation's tables."""
import argparse
import json
from pathlib import Path
from stage1 import Edge, run
from arithmetic import evaluate


def build():
    from library import library_records,cell_radius_squared
    records=library_records()
    labels={w[k] for r in records for w in r['words'] for k in ('A','B')}
    exact_cells={c:cell_radius_squared(c) for c in sorted(labels)}
    cells={c:evaluate(x) for c,x in exact_cells.items()}
    edges=[]
    for r in records:
        for w in r['words']:
            x=r['radius_squared'];c=w['cos_alpha']
            edges.append(Edge(r['name'],w['p'],w['A'],w['B'],
                              evaluate(x),evaluate(c),x,c))
    return records,edges,cells,exact_cells


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',required=True,type=Path)
    ap.add_argument('--compare-recorded',action='store_true')
    args=ap.parse_args()
    records,edges,cells,exact_cells=build()
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'library.json').write_text(json.dumps(records,default=str,sort_keys=True,indent=2)+'\n')
    result=run(edges,cells,exact_cells,args.output)
    if args.compare_recorded:
        from compare import compare_omega,compare_cycles,RECORDED_OMEGA
        comparison={'omega':compare_omega(args.output/'omega.json',RECORDED_OMEGA),
                    'cycles':compare_cycles(args.output/'cycles.json')}
        (args.output/'comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')
        print(json.dumps(comparison,indent=2))

if __name__=='__main__':main()
