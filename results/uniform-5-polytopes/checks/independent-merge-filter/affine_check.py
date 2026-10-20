"""Alternative exact MERGE checker via matched orthogonal bases.

No squared-distance formula or correspondence search is used here. Coordinates
are the same new Wythoff constructions. General rational field multiplication
and Gram-Schmidt prove a single isometry maps every vertex as specified.
"""
import json
from exact import ZERO, dot, inv, mul, sub
from merge_check import HERE, alias_pairs, common_points


def minus(x,y): return tuple(sub(a,b) for a,b in zip(x,y))
def minus_scaled(x,c,u):return tuple(sub(a,mul(c,b)) for a,b in zip(x,u))
def zero(x):return all(a==ZERO for a in x)


def accept(a,b,permutation):
    if len(a)!=len(b) or any(type(i) is not int for i in permutation) or sorted(permutation)!=list(range(len(a))):
        raise ValueError('not a vertex bijection')
    frame=[]
    for p,j in zip(a,permutation):
        x=minus(p,a[0]);y=minus(b[j],b[permutation[0]])
        for u,v,reciprocal in frame:
            c=mul(dot(x,u),reciprocal)
            x=minus_scaled(x,c,u);y=minus_scaled(y,c,v)
        if zero(x):
            if not zero(y):raise ValueError('affine correspondence inconsistent')
        else:
            if len(frame)>=4:raise ValueError('dimension exceeds four')
            nx=dot(x,x)
            if nx==ZERO or dot(y,y)!=nx or any(dot(y,v)!=ZERO for _,v,_ in frame):
                raise ValueError('matched bases are not isometric')
            frame.append((x,y,inv(nx)))
    return len(frame)


def corruptions(certificate):
    def reject(a,b,p):
        try:accept(a,b,p)
        except ValueError:return
        raise AssertionError('affine checker accepted corruption')
    sq=[((x,0,0,0),(y,0,0,0)) for x,y in [(0,0),(1,0),(1,1),(0,1)]]
    if not (accept(sq,sq,[1,2,3,0])==2):
        raise AssertionError()
    reject(sq,sq,[0,2,1,3])
    row=next(r for r in certificate if (r['canonical'],r['alias'])==('B40001','pr-cube'))
    d,a,b=common_points(row['canonical'],row['alias']);p=row['bijection']
    bad=p.copy();bad[0]=bad[1];reject(a,b,bad)
    bad=p.copy();bad[0],bad[1]=bad[1],bad[0];reject(a,b,bad)
    f=10**12
    aa=tuple(tuple(tuple(f*z for z in x) for x in v) for v in a)
    bb=[[list(f*z for z in x) for x in v] for v in b];bb[p[0]][0][0]+=d
    reject(aa,bb,p)
    _,x,y=common_points('B40001','B41000');reject(x,y,list(range(len(x))))
    scaled=tuple(tuple(tuple(2*z for z in x) for x in v) for v in b)
    reject(a,scaled,p)
    try:verify(certificate[:-1])
    except ValueError:pass
    else:raise AssertionError('omitted alias accepted')
    return 7


def verify(certificate):
    if [(r['canonical'],r['alias']) for r in certificate]!=alias_pairs():
        raise ValueError('alias coverage differs')
    for row in certificate:
        _,a,b=common_points(row['canonical'],row['alias'])
        if len(a)!=row['vertices'] or accept(a,b,row['bijection'])!=4:
            raise ValueError('cardinality or dimension differs')


def main():
    certificate=json.loads((HERE/'merge-certificate.json').read_text())
    verify(certificate)
    if not (corruptions(certificate)==7):
        raise AssertionError()
    print('MERGE affine checker: 33/33 isometries; 7 corruptions rejected')

if __name__=='__main__':main()
