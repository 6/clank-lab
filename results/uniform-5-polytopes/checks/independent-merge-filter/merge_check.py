"""Small certificate checker: reconstruct independently, check EVERY distance.
Does not import the correspondence search. All arithmetic is exact.
"""
import argparse
import json
import output_check
from pathlib import Path
from math import lcm
from exact import integral, distance
from wythoff import vertices

HERE=Path(__file__).resolve().parent


def common_points(a,b):
    va,vb=vertices(a),vertices(b)
    da,_=integral(va); db,_=integral(vb)
    d=lcm(da,db)
    return d,integral(va,d)[1],integral(vb,d)[1]


def check_points(a,b,permutation):
    n=len(a)
    if not (n==len(b)):
        raise AssertionError('vertex cardinality differs')
    if not (all(type(v) is int for v in permutation)):
        raise AssertionError('indices must be integers')
    if not (sorted(permutation)==list(range(n))):
        raise AssertionError('not a bijection')
    count=0
    for i in range(n):
        for j in range(i):
            if not (distance(a[i],a[j])==distance(b[permutation[i]],b[permutation[j]])):
                raise AssertionError(f'distance mismatch at {j},{i}')
            count+=1
    return count


def alias_pairs():
    # The manuscript table is frozen as mathematical data. Mutable TeX is
    # provenance, not a runtime input. Keep the independent transcription
    # comparison and all native metric checks; never import producer aliases.
    aliases=json.loads((HERE/'aliases.json').read_text())
    raw=[(a,b) for a,bs in aliases.items() for b in bs]
    table=json.loads((HERE/'manuscript-alias-table.json').read_text())
    if not (table['schema']=='uniform5-merge-alias-table-v1'):
        raise AssertionError('unknown alias table schema')
    if not (all(isinstance(row,list) and len(row)==2 and
               all(isinstance(x,str) and x for x in row) for row in table['pairs'])):
        raise AssertionError('malformed alias table')
    table_pairs=[tuple(row) for row in table['pairs']]
    if not (len(raw)==len(set(raw))==33):
        raise AssertionError('missing or duplicate alias')
    if not (len(table_pairs)==len(set(table_pairs))==33):
        raise AssertionError('missing or duplicate table pair')
    if not (set(raw)==set(table_pairs)):
        raise AssertionError('alias list differs from frozen manuscript table')
    return sorted(raw)


def verify(certificate):
    expected=alias_pairs()
    got=[(r['canonical'],r['alias']) for r in certificate]
    if not (got==expected):
        raise AssertionError('certificate omits, duplicates or changes an alias')
    rows=[]
    for r in certificate:
        a,b=r['canonical'],r['alias']
        d,va,vb=common_points(a,b)
        if not (len(va)==r['vertices']):
            raise AssertionError('wrong declared cardinality')
        count=check_points(va,vb,r['bijection'])
        rows.append({'canonical':a,'alias':b,'vertices':len(va),'pairs_checked':count,'coordinate_denominator':d})
    return rows


def rejected(fn):
    try: fn()
    except (AssertionError,ValueError): return True
    raise AssertionError('corruption accepted')


def controls(certificate):
    # Adjacent solved case: unit square vs its quarter-turn, all six distances.
    square=[((x,0,0,0),(y,0,0,0)) for x,y in [(0,0),(1,0),(1,1),(0,1)]]
    if not (check_points(square,square,[1,2,3,0])==6):
        raise AssertionError()
    rejected(lambda:check_points(square,square,[0,2,1,3]))
    r=next(r for r in certificate if r['canonical']=='B40001' and r['alias']=='pr-cube')
    d,a,b=common_points(r['canonical'],r['alias'])
    perm=r['bijection']
    bad=perm.copy(); bad[0]=bad[1]
    rejected(lambda:check_points(a,b,bad))
    bad=perm.copy(); bad[0],bad[1]=bad[1],bad[0]
    rejected(lambda:check_points(a,b,bad))
    # A perturbation of exactly 10^-12, represented by integral coordinates.
    factor=10**12
    aa=tuple(tuple(tuple(z*factor for z in x) for x in p) for p in a)
    bb=[[list(z*factor for z in x) for x in p] for p in b]
    bb[perm[0]][0][0]+=d
    rejected(lambda:check_points(aa,bb,perm))
    _,wrong_a,wrong_b=common_points('B40001','B41000')
    rejected(lambda:check_points(wrong_a,wrong_b,list(range(len(wrong_a)))))
    # Use deliberate metric scaling, preserving vertex count and permutation.
    scaled=tuple(tuple(tuple(2*z for z in x) for x in p) for p in b)
    rejected(lambda:check_points(a,scaled,perm))
    rejected(lambda:verify(certificate[:-1]))
    return {'square_control_pairs':6,'corruptions_rejected':7}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-result',action='store_true')
    args=parser.parse_args()
    certificate=json.loads((HERE/'merge-certificate.json').read_text())
    rows=verify(certificate)
    result={'status':'CERTIFIED','aliases':len(rows),'pairwise_distances_checked':sum(x['pairs_checked'] for x in rows),'checks':rows,'controls':controls(certificate)}
    path=HERE/'merge-result.json'
    if args.write_result:path.write_text(json.dumps(result,indent=2)+'\n')
    else:output_check.compare(result, output_check.read(path), 'merge-result.json')
    print(f"MERGE: {len(rows)}/33 exact congruences; {result['pairwise_distances_checked']} distances; 7 corruptions rejected")

if __name__=='__main__':main()
