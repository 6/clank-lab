"""Comparison only: this module never supplies data to reconstruction."""
import argparse
from collections import Counter
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path
from stage1 import canonical

RECORDED_OMEGA_SHA256='c7773fab6fff9110ea94b8c79debf887b3667396503e317ecd8cc54a3c89bc33'
BASE=Path(__file__).resolve().parent.parent
RECORDED_OMEGA=BASE/'acceptance-third/infinite/outputs/enum/u5_omega_p16.json'
RECORDED_CYCLES=BASE/'check_u1/cycles_p16.json.gz'


def read_json(path):
    path=Path(path)
    if path.suffix=='.gz':
        return json.loads(gzip.decompress(path.read_bytes()))
    return json.loads(path.read_text())


def compare_omega(own,recorded,require_hash=True):
    raw=Path(recorded).read_bytes()
    digest=hashlib.sha256(raw).hexdigest()
    if require_hash and digest != RECORDED_OMEGA_SHA256:
        raise ValueError('recorded Omega identity mismatch')
    a=read_json(own)['intervals'];b=json.loads(raw)['intervals']
    if len(a)!=7291 or len(a)!=len(b):
        raise ValueError('Omega cardinality disagreement')
    def key(r):
        l,h=map(Fraction,r[:2])
        if not 0<l<=h:
            raise ValueError('invalid radius interval')
        return l+h
    # All successful pairs give an explicit interval-containment bijection.
    # If sorting fails, report it; do not silently omit or coalesce intervals.
    a=sorted(a,key=key);b=sorted(b,key=key)
    bad=[]
    for i,(x,y) in enumerate(zip(a,b)):
        xl,xh=map(Fraction,x[:2]);yl,yh=map(Fraction,y[:2])
        if not yl<=xl<=xh<=yh:
            bad.append({'position':i,'independent':x,'recorded':y})
    if bad:
        raise ValueError('Omega containment disagreement: '+json.dumps(bad[:5]))
    return {'recorded_sha256':digest,'independent_sha256':hashlib.sha256(Path(own).read_bytes()).hexdigest(),
            'triples':len(a),'containment_bijection':len(a),'disagreements':0}


def compare_cycles(own,recorded=RECORDED_CYCLES):
    a=read_json(own);b=read_json(recorded)
    aa={(r['p'],canonical(tuple(map(tuple,r['word'])))):r for r in a}
    bb={(r['p'],canonical(tuple(zip(r['facets'],r['cells'])))):r for r in b}
    if len(aa)!=len(a) or len(bb)!=len(b):
        raise ValueError('duplicate cycle words')
    if aa.keys()!=bb.keys():
        raise ValueError('cycle enumeration disagreement: '+repr((len(aa.keys()-bb.keys()),len(bb.keys()-aa.keys()))))
    for key,x in aa.items():
        y=bb[key]
        expected=('FLAT' if y['flat'] else 'DEGENERATE' if y['degenerate']
                  else 'ROOT' if y['R'] else 'NO_ROOT')
        if x['status']!=expected:
            raise ValueError('cycle status disagreement: '+repr((key,x,y)))
        if x['status']=='ROOT':
            if len(y['R'])!=1:
                raise ValueError('recorded cycle has multiple roots')
            xl,xh=map(Fraction,x['R']);yl,yh=map(Fraction,y['R'][0])
            if not yl<=xl<=xh<=yh:
                raise ValueError('cycle root containment disagreement: '+repr((key,x,y)))
    return {'cycle_words':len(a),'status_counts':dict(Counter(r['status'] for r in a)),
            'recorded_cycles_sha256':hashlib.sha256(Path(recorded).read_bytes()).hexdigest(),
            'disagreements':0}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--directory',type=Path,required=True)
    args=ap.parse_args()
    out={'omega':compare_omega(args.directory/'omega.json',RECORDED_OMEGA),
         'cycles':compare_cycles(args.directory/'cycles.json')}
    (args.directory/'comparison.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
