#!/usr/bin/env python3
"""Emit kernel proofs from a discovered certificate; never search for vertices.

Generated bulk data/proofs belong outside the repository and keep/. The
kernel checks arithmetic, complete labels and every local neighbor. Neither
this generator nor the discovery program is part of the trusted proof.
"""
import argparse
from fractions import Fraction
import gzip
import hashlib
import json
from math import lcm
from pathlib import Path


def vec(xs):
    return '![' + ', '.join(xs) + ']'


def balanced(xs, codomain):
    if len(xs) == 1:
        return '(fun (_ : Fin 1) => (' + xs[0] + ' : ' + codomain + '))'
    m = len(xs)//2
    return f'(Fin.append (m := {m}) (n := {len(xs)-m}) ' + balanced(xs[:m], codomain) + ' ' + balanced(xs[m:], codomain) + ')'


def join_blocks(blocks, field):
    if len(blocks)==1:return f'source{field}Block{blocks[0][0]}'
    mid=len(blocks)//2;left=blocks[:mid];right=blocks[mid:]
    return (f'(Fin.append (m := {sum(b[2]-b[1] for b in left)}) '
            f'(n := {sum(b[2]-b[1] for b in right)}) '
            +join_blocks(left,field)+' '+join_blocks(right,field)+')')


def join_trees(blocks, coded):
    if len(blocks)==1:return f'sourceTreeBlock{blocks[0][0]}'
    mid=len(blocks)//2
    return (f'(SourceLayerTree.branch {coded[blocks[mid][1]][0]} '
            +join_trees(blocks[:mid],coded)+' '+join_trees(blocks[mid:],coded)+')')


def tree(xs):
    if len(xs) == 1:
        return f'(SourceLayerTree.leaf ({xs[0][1]}))'
    m = len(xs)//2
    return f'(SourceLayerTree.branch {xs[m][0]} {tree(xs[:m])} {tree(xs[m:])})'


def dispatch(chunks, low, high, indent='  '):
    if len(chunks) == 1:
        idx, _, _ = chunks[0]
        return f'{indent}exact source_chunk_{idx} i ({low}) ({high})\n'
    m = len(chunks)//2
    cut = chunks[m][1]
    h = f'h{cut}'
    return (f'{indent}by_cases {h} : i.val < {cut}\n'
            + f'{indent}·\n' + dispatch(chunks[:m], low, h, indent+'  ')
            + f'{indent}·\n' + dispatch(chunks[m:], f'Nat.le_of_not_lt {h}', high, indent+'  '))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--certificate', required=True)
    ap.add_argument('--input', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--kind', choices=['control','msw'], required=True)
    ap.add_argument('--chart')
    ap.add_argument('--chunk', type=int, default=64)
    args = ap.parse_args()
    raw = Path(args.certificate).read_bytes()
    c = json.loads(gzip.decompress(raw) if args.certificate.endswith('.gz') else raw)
    inp = Path(args.input).read_bytes()
    assert c['input_sha256'] == hashlib.sha256(inp).hexdigest()
    expected = json.loads(inp)
    if c['chart_last']:
        expected = [[r[-1]]+r[:-1] for r in expected]
    assert expected == c['matrix']
    A=[]
    for row in expected:
        q=list(map(Fraction,row)); den=lcm(*(x.denominator for x in q))
        A.append([int(x*den) for x in q])
    n,r=len(A),len(A[0]); d=r-1; N=len(c['vertices'])
    assert N and n==2*d and args.chunk>0
    if args.kind=='msw':
        assert (n,r)==(40,21) and args.chart
        assert A==json.loads(Path(args.chart).read_text())['matrix']
    rays=[]
    for row in c['vertices']:
        q=list(map(Fraction,row)); den=lcm(*(x.denominator for x in q))
        rays.append([int(x*den) for x in q])
    labels=c['labels']; assert len(labels)==N
    assert all(len(b)==d and len(set(b))==d and all(0<=i<n for i in b) for b in labels)
    ridge={}
    for v,b in enumerate(labels):
        for j in range(d):ridge.setdefault(tuple(sorted(b[:j]+b[j+1:])),[]).append((v,j))
    nxt=[[None]*d for _ in range(N)]
    for inc in ridge.values():
        assert len(inc)==2
        (v,j),(w,k)=inc;nxt[v][j]=w;nxt[w][k]=v
    levels=c['potential']; assert len(levels)==N and all(type(x) is int for x in levels)
    coded=sorted((sum(1<<i for i in b),levels[v]) for v,b in enumerate(labels))
    assert len(set(k for k,_ in coded))==N
    out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
    header=('import FiniteSourceBinding\n'+('import MSWSourceEndpoint\n' if args.kind=='msw' else '')
            +'set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
            +'namespace ADKZPricing.Generated\nopen Matrix Finset\n')
    amat='mswIntegralA' if args.kind=='msw' else vec([vec(list(map(str,row))) for row in A])
    blocks=[(i,start,min(N,start+args.chunk)) for i,start in enumerate(range(0,N,args.chunk))]
    for idx,start,end in blocks:
        size=end-start
        block=header
        for field,domain,values in [
            ('Rays',f'Fin {r} → ℤ',[vec(list(map(str,row))) for row in rays[start:end]]),
            ('Bases',f'Fin {d} → Fin {n}',[vec(list(map(str,row))) for row in labels[start:end]]),
            ('Next',f'Fin {d} → Fin {N}',[vec(list(map(str,row))) for row in nxt[start:end]]),
            ('Levels','ℤ',list(map(str,levels[start:end])))]:
            block+=f'noncomputable def source{field}Block{idx} : Fin {size} → {domain} := '+balanced(values,domain)+'\n'
        block+=f'noncomputable def sourceTreeBlock{idx} : SourceLayerTree := '+tree(coded[start:end])+'\n'
        block+='end ADKZPricing.Generated\n'
        (out/f'SourceKernelDataBlock{idx}.lean').write_text(block, encoding='utf-8', newline='\n')
    data=''.join(f'import SourceKernelDataBlock{i}\n' for i,_,_ in blocks)+header
    data+=f'noncomputable def sourceA : Matrix (Fin {n}) (Fin {r}) ℤ := {amat}\n'
    for field,domain in [('Rays',f'Fin {r} → ℤ'),('Bases',f'Fin {d} → Fin {n}'),
                         ('Next',f'Fin {d} → Fin {N}'),('Levels','ℤ')]:
        data+=f'noncomputable def source{field} : Fin {N} → {domain} := '+join_blocks(blocks,field)+'\n'
    data+='noncomputable def sourceTree : SourceLayerTree := '+join_trees(blocks,coded)+'\n'
    data+=f'noncomputable def sourceData : IntegerSourceData (n := {n}) (d := {d}) (Fin {N}) where\n'
    data+='  ray := sourceRays\n  basis := sourceBases\n  next := sourceNext\nend ADKZPricing.Generated\n'
    (out/'SourceKernelData.lean').write_text(data, encoding='utf-8', newline='\n')
    chunks=[]
    for start in range(0,N,args.chunk):
        end=min(N,start+args.chunk);idx=len(chunks);chunks.append((idx,start,end))
        s='import SourceKernelData\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace ADKZPricing.Generated\n'
        for v in range(start,end):
            s+=f'theorem source_vertex_{v} : integerSourceVertexCheck sourceA sourceData ({v} : Fin {N}) ∧\n'
            s+=f'    sourcePotentialVertexCheck sourceData sourceTree sourceLevels ({v} : Fin {N}) := by\n  unfold integerSourceVertexCheck sourcePotentialVertexCheck Function.Injective\n  decide\n'
        s+=f'theorem source_chunk_{idx} (i : Fin {N}) (hlo : {start} ≤ i.val) (hhi : i.val < {end}) :\n'
        s+='    integerSourceVertexCheck sourceA sourceData i ∧\n    sourcePotentialVertexCheck sourceData sourceTree sourceLevels i := by\n'
        s+='  interval_cases h : i.val\n'
        for v in range(start,end):
            s+=f'  · have hi : i = ({v} : Fin {N}) := Fin.ext h\n    subst i\n    exact source_vertex_{v}\n'
        s+='end ADKZPricing.Generated\n';(out/f'SourceKernelChunk{idx}.lean').write_text(s, encoding='utf-8', newline='\n')
    s=''.join(f'import SourceKernelChunk{i}\n' for i,_,_ in chunks)
    s+='namespace ADKZPricing.Generated\nopen Matrix Finset\nset_option maxRecDepth 1000000\n'
    s+=f'theorem source_checks (i : Fin {N}) : integerSourceVertexCheck sourceA sourceData i ∧\n'
    s+='    sourcePotentialVertexCheck sourceData sourceTree sourceLevels i := by\n'+dispatch(chunks,'Nat.zero_le i.val','i.isLt')
    s+='theorem source_valid : IntegerSourceValid sourceA sourceData :=\n  integerSourceValid_of_checks sourceA sourceData (fun v => (source_checks v).1)\n'
    s+='noncomputable def sourceCertificate := source_valid.toCertificate\n'
    s+='theorem source_local_potential : ∀ v j, sourceTree.potential (sourceCertificate.labels (sourceCertificate.next v j)) ≤\n'
    s+='    sourceTree.potential (sourceCertificate.labels v) + 1 :=\n  sourcePotential_local sourceA sourceData source_valid sourceTree sourceLevels (fun v => (source_checks v).2)\n'
    src,dst=c['endpoints'];gap=levels[dst]-levels[src]
    assert labels[src]==list(range(d)) and labels[dst]==list(range(d,n))
    if args.kind=='msw':
        assert gap==21
        s+='theorem source_specified_gap : (21 : ℤ) ≤ sourceTree.potential mswPlusLabels - sourceTree.potential mswMinusLabels := by decide\n'
        s+='theorem source_frozen_endpoint : ProposedEndpoint :=\n  msw_endpoint_of_source_certificate sourceCertificate sourceTree.potential source_local_potential source_specified_gap\n#print axioms source_frozen_endpoint\n'
    else:
        s+=f'theorem source_specified_gap : ({gap} : ℤ) ≤ sourceTree.potential (Finset.univ.image (sourceData.basis ({dst} : Fin {N}))) -\n'
        s+=f'    sourceTree.potential (Finset.univ.image (sourceData.basis ({src} : Fin {N}))) := by decide\n'
        s+='#print axioms source_valid\n#print axioms source_local_potential\n#print axioms source_specified_gap\n'
    s+='end ADKZPricing.Generated\n';(out/'SourceKernelComplete.lean').write_text(s, encoding='utf-8', newline='\n')
    files=sorted(out.glob('*.lean'))
    manifest={'kind':args.kind,'vertices':N,'chunks':len(chunks),'data_blocks':len(blocks),'gap':gap,
              'input_sha256':hashlib.sha256(inp).hexdigest(),
              'certificate_sha256':hashlib.sha256(raw).hexdigest(),
              'files':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
              'kernel_checked':False,'full_target_unit_complete':False}
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({k:v for k,v in manifest.items() if k!='files'}))


if __name__=='__main__':main()
