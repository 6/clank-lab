"""Compare frozen independent output to recorded output, with explicit differences."""
import argparse
import hashlib
import json
from pathlib import Path
from combinatorics import signature_key


def main():
    p=argparse.ArgumentParser()
    p.add_argument('independent',type=Path)
    p.add_argument('reference',type=Path)
    p.add_argument('--subset',action='store_true',help='explicit partial comparison')
    args=p.parse_args()
    rows=[json.loads(line) for line in args.independent.read_text().splitlines()]
    ours={r['index']:r for r in rows}
    refs={r['index']:r for r in json.loads(args.reference.read_text())}
    differences=[]
    if not args.subset and set(ours)!=set(refs):
        differences.append({'classes_missing':sorted(set(refs)-set(ours)),'classes_extra':sorted(set(ours)-set(refs))})
    for i,row in sorted(ours.items()):
        if row['status']!='COMPLETE': differences.append({'index':i,'status':row['status']});continue
        a={signature_key(v) for v in row['vfs']}
        b={signature_key(v) for v in refs[i]['vfs']}
        if a!=b: differences.append({'index':i,'only_independent':sorted(a-b),'only_reference':sorted(b-a)})
    receipt={'independent_sha256':hashlib.sha256(args.independent.read_bytes()).hexdigest(),
             'reference_sha256':hashlib.sha256(args.reference.read_bytes()).hexdigest(),
             'subset':args.subset,'classes':len(ours),'vertex_figures':sum(len(r['vfs']) for r in ours.values()),
             'differences':differences}
    print(json.dumps(receipt,indent=2))
    return int(bool(differences))


if __name__=='__main__': raise SystemExit(main())
