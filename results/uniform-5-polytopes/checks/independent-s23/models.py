"""Independent exact convex model library. No legacy implementations imported."""
from functools import cached_property, lru_cache
from itertools import combinations, permutations, product
from pathlib import Path
import json
import re
import sympy as sp
from flint import arb, ctx
from exact import Field, Undecided, dot, add, sub, scale, solve, identity, orbit

ctx.prec=max(ctx.prec,320)
HERE=Path(__file__).resolve().parent
FACET_MANIFEST_PATH=HERE.parent/'check_u1'/'inputs'/'u1_facets_p16.json'
MODEL_DATA=HERE.parent/'model_audit'

def cycle_key(v):
    v=tuple(v);return min(tuple(w[k:]+w[:k]) for w in (v,v[::-1]) for k in range(len(w)))

def metric_permutations(G, allowed=None):
    """All Gram automorphisms, by exhaustive exact backtracking (no cutoff)."""
    n=len(G); signatures=[(G[i][i],frozenset((x,G[i].count(x)) for x in set(G[i]))) for i in range(n)]
    cand=[[j for j in range(n) if signatures[i]==signatures[j] and (allowed is None or allowed(i,j))] for i in range(n)]
    order=sorted(range(n),key=lambda i:len(cand[i]));p=[-1]*n;used=set()
    def rec(k):
        if k==n:yield tuple(p);return
        i=order[k]
        for j in cand[i]:
            if j in used or any(G[i][h]!=G[j][p[h]] for h in order[:k]):continue
            p[i]=j;used.add(j);yield from rec(k+1);used.remove(j);p[i]=-1
    yield from rec(0)

class Facet:
    """Exact construction plus directed-ball Euclidean realization.

    Coordinates exact_vertices are in basis with metric metric. full vertices
    can be lazy; local exact_neighbours are always immediate. vf_to_intrinsic
    has 4 rows and 3 columns; vf_origin + frame*vf_point is neighbour.
    """
    def __init__(self,name,F,G,base,neighbours,edge_p,ridges,full_factory):
        self.name=name;self.field=F;self.metric=tuple(map(tuple,G));self.base_exact=base
        self.exact_neighbours=tuple(neighbours);self.base_index=0
        self.radius2_exact=dot(base,base,G);self.radius2=F.ball(self.radius2_exact)
        self.edge_p={tuple(sorted(k)):v for k,v in edge_p.items()}
        self.ridges=[]
        for vertices,label in ridges:
            vertices=set(vertices);start=min(vertices);order=[start];prev=None
            while True:
                adj=sorted(j for j in vertices if j!=prev and tuple(sorted((order[-1],j))) in self.edge_p)
                if not adj:raise ValueError('ridge cycle missing edge')
                nxt=adj[0]
                if nxt==start:break
                if nxt in order:raise ValueError('invalid ridge cycle')
                prev=order[-1];order.append(nxt)
            if set(order)!=vertices:raise ValueError('ridge cycle disconnected')
            self.ridges.append({'vertices':order,'label':label})
        self.ridges.sort(key=lambda r:(r['label'],tuple(r['vertices'])))
        self._full_factory=full_factory
        # Neighbour minus VF centre: centre is base*(1-1/(2R²)).
        self.vf_origin_exact=scale(base,F.one-F(1)/(F(2)*self.radius2_exact))
        self.vf_vectors_exact=tuple(sub(p,self.vf_origin_exact) for p in neighbours)
        self.vf_gram_exact=tuple(tuple(dot(x,y,G) for y in self.vf_vectors_exact) for x in self.vf_vectors_exact)
        self._realize()
    def _realize(self):
        F=self.field;n=len(self.metric)
        # Exact Gram-Schmidt chooses a frame, all norm positivity checked exactly.
        unit=[];norms=[];orth=[]
        for v in self.vf_vectors_exact:
            w=v
            for q,d in zip(orth,norms):w=sub(w,scale(q,dot(w,q,self.metric)/d))
            d=dot(w,w,self.metric)
            if not d:continue
            if F.sign(d)!=1:raise ValueError('nonpositive exact Gram norm')
            orth.append(w);norms.append(d)
            if len(orth)==n-1:break
        if len(orth)!=n-1:raise ValueError('VF lacks full affine dimension')
        self.vf_frame_exact=(tuple(orth),tuple(norms))
        if any(not F.ball(d)>0 for d in norms):raise Undecided('VF norm enclosure not separated from zero')
        self.vf_points=[tuple(F.ball(dot(v,q,self.metric))/F.ball(d).sqrt() for q,d in zip(orth,norms)) for v in self.vf_vectors_exact]
        # Cholesky columns realize root-basis vectors isometrically in R^n.
        L=[[arb(0) for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(i+1):
                t=F.ball(self.metric[i][j])-sum((L[i][k]*L[j][k] for k in range(j)),arb(0))
                if i==j:
                    if not t>0:raise Undecided('Cholesky positivity')
                    L[i][j]=t.sqrt()
                else:L[i][j]=t/L[j][j]
        self._T=tuple(tuple(L[j][i] for j in range(n)) for i in range(n))
        self.base_vertex=self._euclidean(self.base_exact)
        self.vf_origin=self._euclidean(self.vf_origin_exact)
        self.vf_to_intrinsic=tuple(tuple(self._euclidean(q)[i]/F.ball(d).sqrt() for q,d in zip(orth,norms)) for i in range(n))
        if any(not x.is_finite() for p in self.vf_points for x in p):raise Undecided('nonfinite VF realization')
    def _euclidean(self,p):return tuple(sum((a*self.field.ball(b) for a,b in zip(row,p)),arb(0)) for row in self._T)
    @cached_property
    def exact_vertices(self):
        pts=tuple(self._full_factory())
        if not pts or pts[0]!=self.base_exact:raise ValueError("base index mismatch")
        if len(set(pts))!=len(pts):raise ValueError('duplicate exact full vertices')
        return pts
    @cached_property
    def points4(self):return [self._euclidean(v) for v in self.exact_vertices]
    @property
    def vertices(self):return self.points4
    @cached_property
    def neighbours(self):
        d={p:i for i,p in enumerate(self.exact_vertices)};return [d[p] for p in self.exact_neighbours]
    def verify_stabilizer(self,perm):
        try:
            p=tuple(perm);n=len(self.vf_points)
            if len(p)!=n or sorted(p)!=list(range(n)):return False
            if any(self.vf_gram_exact[i][j]!=self.vf_gram_exact[p[i]][p[j]] for i in range(n) for j in range(n)):return False
            if {(tuple(sorted((p[i],p[j]))),v) for (i,j),v in self.edge_p.items()}!=set(self.edge_p.items()):return False
            original={(cycle_key(r['vertices']),r['label']) for r in self.ridges}
            return {(cycle_key(tuple(p[i] for i in r['vertices'])),r['label']) for r in self.ridges}==original
        except (TypeError,IndexError,ValueError):return False
    @cached_property
    def stabilizers(self):return [p for p in metric_permutations(self.vf_gram_exact) if self.verify_stabilizer(p)]
    @property
    def stabilizers_complete(self):return True
    @cached_property
    def cell_radius2_exact(self):
        F=self.field;out=[]
        for ridge in self.ridges:
            edges=[sub(self.exact_neighbours[i],self.base_exact) for i in ridge['vertices']]
            vs=independent_frame([(F.zero,)*len(self.metric)]+edges,self.metric,F,3)
            H=[[dot(a,b,self.metric) for b in vs] for a in vs]
            c=solve(H,[dot(a,a,self.metric)/F(2) for a in vs])
            w=tuple(sum((c[j]*vs[j][i] for j in range(3)),F.zero) for i in range(len(self.metric)))
            r2=dot(w,w,self.metric)
            if any(dot(w,a,self.metric)!=dot(a,a,self.metric)/F(2) for a in edges):raise ValueError('cell circumcentre inconsistent')
            out.append(r2)
        return tuple(out)
    @cached_property
    def cell_radius2(self):return tuple(self.field.ball(x) for x in self.cell_radius2_exact)
    @cached_property
    def polygon_radius2_exact(self):
        F=self.field
        return {e:F.one/(F(4)-dot(sub(self.exact_neighbours[e[0]],self.exact_neighbours[e[1]]),sub(self.exact_neighbours[e[0]],self.exact_neighbours[e[1]]),self.metric)) for e in self.edge_p}
    def closure_data(self,edge):
        """Paper closure constants for one source polygon, enclosing its angle."""
        e=tuple(sorted(edge));F=self.field;rho=self.polygon_radius2_exact[e]
        cells=[k for k,r in enumerate(self.ridges) if set(e)<=set(r['vertices'])]
        if len(cells)!=2:raise ValueError('polygon must have exactly two incident cells')
        d=tuple(self.cell_radius2_exact[k]-rho for k in cells);D=self.radius2_exact-rho
        if F.sign(D)!=1 or any(F.sign(x)!=1 for x in d) or any(F.sign(D-x)!=1 for x in d):raise ValueError('closure constant positivity')
        cos_alpha=(F.ball(d[0]*d[1]).sqrt()-F.ball((D-d[0])*(D-d[1])).sqrt())/F.ball(D)
        return {'p':self.edge_p[e],'rho2':F.ball(rho),'cell_indices':tuple(cells),'cell_d2':tuple(F.ball(x) for x in d),'cos_alpha':cos_alpha,'rho2_exact':rho,'cell_d2_exact':d}
    def verify_isometry(self,perm):
        try:verify_metric_permutation(self.exact_vertices,self.metric,self.field,perm);return True
        except (ValueError,TypeError,IndexError):return False

    def symmetries_to(self,vertex_index):
        """All full metric symmetries base -> target, exact affine extensions.

        Every full symmetry restricts to a VF Gram isometry. Enumerate all such
        restrictions and retain precisely the extensions permuting all vertices.
        Does not assume every local VF symmetry extends globally.
        """
        pts=self.exact_vertices;F=self.field;G=self.metric
        if not isinstance(vertex_index,int) or not 0<=vertex_index<len(pts):raise IndexError('target vertex out of range')
        t=pts[vertex_index]
        near=[p for p in pts if dot(sub(p,t),sub(p,t),G)==F(1)]
        if len(near)!=len(self.exact_neighbours):raise ValueError('nonuniform target degree')
        o=scale(t,F.one-F.one/(F(2)*self.radius2_exact));vv=[sub(p,o) for p in near]
        target=tuple(tuple(dot(a,b,G) for b in vv) for a in vv)
        source=self.vf_gram_exact;n=len(source)
        # Enumerate source->target distance/Gram bijections with exact pruning.
        cand=[[j for j in range(n) if sorted(source[i],key=repr)==sorted(target[j],key=repr)] for i in range(n)]
        p=[-1]*n;used=set();lookup={v:i for i,v in enumerate(pts)}
        basis=[self.base_exact];which=[-1]
        for i,v in enumerate(self.vf_vectors_exact):
            test=basis+[v]
            M=[[dot(a,b,G) for b in test] for a in test]
            try:solve(M,[F.one]*len(M))
            except Undecided:continue
            basis.append(v);which.append(i)
            if len(basis)==len(G):break
        H=[[dot(a,b,G) for b in basis] for a in basis]
        coefficients=[solve(H,[dot(a,v,G) for a in basis]) for v in pts]
        def rec(k):
            if k==n:
                dest=[t]+[vv[p[i]] for i in which[1:]]
                out=[]
                for c in coefficients:
                    v=tuple(sum((c[j]*dest[j][h] for j in range(len(G))),F.zero) for h in range(len(G)))
                    if v not in lookup:return
                    out.append(lookup[v])
                if len(set(out))==len(pts):yield tuple(out)
                return
            for j in cand[k]:
                if j in used or any(source[k][h]!=target[j][p[h]] for h in range(k)):continue
                p[k]=j;used.add(j);yield from rec(k+1);used.remove(j)
        yield from rec(0)

TABLE3={
 ('A',(0,0,1)):'tet',('A',(1,0,0)):'tet',('A',(0,1,0)):'oct',('A',(0,1,1)):'tut',('A',(1,1,0)):'tut',('A',(1,0,1)):'co',('A',(1,1,1)):'toe',
 ('B',(0,0,1)):'cube',('B',(1,0,0)):'oct',('B',(0,1,0)):'co',('B',(0,1,1)):'tic',('B',(1,1,0)):'toe',('B',(1,0,1)):'sirco',('B',(1,1,1)):'girco',
 ('H',(0,0,1)):'ico',('H',(1,0,0)):'doe',('H',(0,1,0)):'id',('H',(0,1,1)):'tid',('H',(1,1,0)):'ti',('H',(1,0,1)):'srid',('H',(1,1,1)):'grid'}

def diagram(kind,n):
    es={tuple(sorted((i,i+1))):3 for i in range(n-1)}
    if kind=='B':es[(n-2,n-1)]=4
    if kind=='H':es[(0,1)]=5
    if kind=='F':es[(1,2)]=4
    if kind=='D':es={tuple(sorted(e)):3 for e in [(i,i+1) for i in range(n-2)]+[(n-3,n-1)]}
    return es

def components(I,edges):
    out=[];left=set(I)
    while left:
        comp={min(left)};todo=list(comp)
        for i in todo:
            for j in left-comp:
                if tuple(sorted((i,j))) in edges:comp.add(j);todo.append(j)
        left-=comp;out.append(sorted(comp))
    return out

def face_dimension(I,edges,rings):return sum(len(c) for c in components(I,edges) if any(rings[i] for i in c))
def face_label(I,edges,rings):
    cs=[c for c in components(I,edges) if any(rings[i] for i in c)]
    if sum(map(len,cs))==2:
        if len(cs)==2:return 4
        a,b=cs[0];return edges[tuple(sorted((a,b)))]*(2 if rings[a] and rings[b] else 1)
    if len(cs)==3:return 'cube'
    if len(cs)==2:
        c=next(c for c in cs if len(c)==2);p=face_label(c,edges,rings)
        return 'cube' if p==4 else 'P'+str(p)
    c=cs[0]
    # Rank3 components are paths; choose orientation with 4 at right or 5 at left.
    for seq in permutations(c):
        es=[edges.get(tuple(sorted((seq[i],seq[i+1]))),2) for i in range(2)]
        kind={(3,3):'A',(3,4):'B',(5,3):'H'}.get(tuple(es))
        if kind:return TABLE3[kind,tuple(rings[i] for i in seq)]
    raise ValueError('unknown rank3 component')

@lru_cache(None)
def wythoff(name):
    kind=name[0];n=int(name[1]);rings=tuple(map(int,name[2:]));
    if len(rings)!=n or not any(rings) or not set(rings)<={0,1}:raise ValueError('invalid binary ring mask')
    es=diagram(kind,n);F=Field(sp.sqrt(5) if kind=='H' else sp.sqrt(2))
    cos={3:F(sp.Rational(1,2)),4:F(sp.sqrt(2)/2) if kind!='H' else None,5:F((1+sp.sqrt(5))/4) if kind=='H' else None}
    G=tuple(tuple(F(1) if i==j else -cos[es[i,j]] if (i,j) in es else -cos[es[j,i]] if (j,i) in es else F(0) for j in range(n)) for i in range(n))
    base=solve(G,[F(sp.Rational(r,2)) for r in rings])
    def ref(i,p):
        q=list(p);q[i]-=F(2)*sum((G[i][j]*p[j] for j in range(n)),F.zero);return tuple(q)
    zero=[i for i,r in enumerate(rings) if not r]
    def local(I):
        seeds=[ref(i,base) for i in I if rings[i]];out=[]
        for p in seeds:
            for q in orbit(p,[lambda v,i=i:ref(i,v) for i in I if not rings[i]]):
                if q not in out:out.append(q)
        return out
    neighbours=local(range(n));index={p:i for i,p in enumerate(neighbours)}
    zp=[tuple(index[ref(i,p)] for p in neighbours) for i in zero]
    def spread(v):return orbit(tuple(sorted(v)),[lambda v,p=p:tuple(sorted(p[i] for i in v)) for p in zp])
    edge_p={};ridges={}
    for dim in (2,3):
        for I in combinations(range(n),dim):
            if face_dimension(I,es,rings)!=dim:continue
            inds=[index[p] for p in local(I)];label=face_label(I,es,rings)
            for v in spread(inds):
                if dim==2:
                    if len(v)!=2:raise ValueError("rank2 face has wrong local degree")
                    if v in edge_p and edge_p[v]!=label:raise ValueError("inconsistent face label")
                    edge_p[v]=label
                else:ridges[v]=label
    return Facet(name,F,G,base,neighbours,edge_p,list(ridges.items()),lambda:orbit(base,[lambda v,i=i:ref(i,v) for i in range(n)]))

_MANIFEST=json.loads(FACET_MANIFEST_PATH.read_text())
ALIASES={a:r['name'] for r in _MANIFEST for a in [r['name']]+r['aliases']}
def names():return tuple(r['name'] for r in _MANIFEST)
@lru_cache(None)
def facet(name):
    ctx.prec=max(ctx.prec,320)
    name=ALIASES.get(name,name)
    if len(name)>2 and name[0] in 'ABDFH' and name[1]=='4':return wythoff(name)
    if name.startswith('duoprism-'):return duoprism(*map(int,name.split('-')[1:]),name=name)
    if name.startswith('antiprism-prism-'):return antiprism_prism(int(name.split('-')[-1]),name)
    if name.startswith('pr-'):return polyhedron_prism(name[3:],name)
    if name in ('sadi','gap'):return exceptional(name)
    raise KeyError(name)

def polygon_block(n,F):
    if not isinstance(n,int) or n<3:raise ValueError('polygon integer n>=3 required')
    c=F(sp.cos(2*sp.pi/n));s2=F.one-c*c;rho=F.one/(F(2)*(F.one-c))
    pts=[];x,y=F.one,F.zero
    for k in range(n):
        pts.append((x,y));x,y=c*x-s2*y,x+c*y
    if (x,y)!=(F.one,F.zero) or len(set(pts))!=n:raise ValueError("polygon closure fails")
    return pts,(rho,rho*s2),rho

def diagonal(values,F):return tuple(tuple(v if i==j else F.zero for j in range(len(values))) for i,v in enumerate(values))

def duoprism(p,q,name=None):
    name=name or f'duoprism-{p}-{q}'
    # Both cosines are explicit real algebraic generators. Their primitive
    # element is an exact sum, with Arb enclosing the intended embedding.
    F=Field((sp.cos(2*sp.pi/p),sp.cos(2*sp.pi/q)))
    A,gA,_=polygon_block(p,F);B,gB,_=polygon_block(q,F)
    G=diagonal(gA+gB,F);base=A[0]+B[0]
    near=[A[1]+B[0],A[-1]+B[0],A[0]+B[1],A[0]+B[-1]]
    ep={(0,1):p,(2,3):q,**{(i,j):4 for i in (0,1) for j in (2,3)}}
    prism=lambda n:'cube' if n==4 else 'P'+str(n)
    ridges=[((0,1,j),prism(p)) for j in (2,3)]+[((i,2,3),prism(q)) for i in (0,1)]
    return Facet(name,F,G,base,near,ep,ridges,lambda:[a+b for a in A for b in B])

def antiprism_data(n,F):
    c=F(sp.cos(sp.pi/n));s2=F.one-c*c;rho=F.one/(F(4)*s2);h2=F.one-F.one/(F(2)*(F.one+c))
    even=[];odd=[];x,y=F.one,F.zero
    for k in range(2*n):
        (odd if k%2 else even).append((x,y,F(-1 if k%2 else 1)))
        x,y=c*x-s2*y,x+c*y
    if (x,y)!=(F.one,F.zero):raise ValueError("antiprism closure fails")
    return even,odd,(rho,rho*s2,h2/F(4))

def antiprism_prism(n,name=None):
    name=name or f'antiprism-prism-{n}';F=Field(sp.cos(sp.pi/n))
    A,B,g=antiprism_data(n,F);one=(F.one,);minus=(-F.one,)
    base=A[0]+one;near=[A[1]+one,A[-1]+one,B[0]+one,B[-1]+one,A[0]+minus]
    ep={(0,1):n,(0,2):3,(2,3):3,(1,3):3,**{(i,4):4 for i in range(4)}}
    prism=lambda n:'cube' if n==4 else 'P'+str(n)
    ridges=[((0,1,2,3),'oct' if n==3 else 'A'+str(n))]+[((i,j,4),prism(p)) for (i,j),p in list(ep.items()) if j!=4]
    return Facet(name,F,diagonal(g+(F(sp.Rational(1,4)),),F),base,near,ep,ridges,lambda:[v+t for v in A+B for t in (one,minus)])

def polyhedron_prism(label,name=None):
    if label in ('snic','snid'):return snub_prism(label,name)
    kind,rings=next((k,r) for (k,r),v in TABLE3.items() if v==label)
    source=wythoff(kind+'3'+''.join(map(str,rings)));F=source.field;n=len(source.exact_neighbours)
    G=tuple(tuple(source.metric[i][j] if i<3 and j<3 else F(sp.Rational(1,4)) if i==j==3 else F.zero for j in range(4)) for i in range(4))
    base=source.base_exact+(F.one,);near=[v+(F.one,) for v in source.exact_neighbours]+[source.base_exact+(-F.one,)]
    ep=dict(source.edge_p);ep.update({(i,n):4 for i in range(n)})
    ridges=[(tuple(range(n)),label)]+[((i,j,n),'cube' if p==4 else 'P'+str(p)) for (i,j),p in source.edge_p.items()]
    return Facet(name or 'pr-'+label,F,G,base,near,ep,ridges,lambda:[v+(t,) for v in source.exact_vertices for t in (F.one,-F.one)])

def certificate_coordinate(F,p):return F(sp.Rational(p[0]))+F(sp.Rational(p[1]))*F(sp.sqrt(5))
def plain_dot(a,b,F):return sum((u*v for u,v in zip(a,b)),F.zero)
def independent_frame(points,G,F,dim):
    p=points[0];vs=[]
    for q in points[1:]:
        w=sub(q,p);test=vs+[w]
        H=[[dot(a,b,G) for b in test] for a in test]
        try:solve(H,[F.one]*len(test))
        except Undecided:continue
        vs.append(w)
        if len(vs)==dim:return vs
    raise ValueError('rank deficient certificate')

def verify_polygon(points,G,F):
    """Exact rank2, unit cyclic edges, and strict convex cyclic order."""
    vs=independent_frame(points,G,F,2);H=[[dot(a,b,G) for b in vs] for a in vs]
    coords=[]
    for p in points:
        w=sub(p,points[0]);c=solve(H,[dot(v,w,G) for v in vs])
        if w!=add(scale(vs[0],c[0]),scale(vs[1],c[1])):raise ValueError('nonplanar polygon')
        coords.append(c)
    signs=[]
    for i,a in enumerate(coords):
        b=coords[(i+1)%len(coords)]
        if dot(sub(points[i],points[(i+1)%len(points)]),sub(points[i],points[(i+1)%len(points)]),G)!=F.one:raise ValueError('nonunit polygon')
        for j,c in enumerate(coords):
            if j in (i,(i+1)%len(coords)):continue
            det=(b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
            signs.append(F.sign(det))
    if not signs or not (set(signs)=={1} or set(signs)=={-1}):raise ValueError('polygon not strictly cyclic convex')

def verify_metric_permutation(points,G,F,p):
    n=len(points)
    if sorted(p)!=list(range(n)):raise ValueError('nonbijective symmetry')
    # Basis Gram and coordinates suffice for every pair, avoiding O(n²) work.
    basis=[];which=[]
    for i,v in enumerate(points):
        test=basis+[v];H=[[dot(a,b,G) for b in test] for a in test]
        try:solve(H,[F.one]*len(test))
        except Undecided:continue
        basis.append(v);which.append(i)
        if len(basis)==len(G):break
    if len(basis)!=len(G):raise ValueError('symmetry frame singular')
    dest=[points[p[i]] for i in which];H=[[dot(a,b,G) for b in basis] for a in basis]
    if H!=[[dot(a,b,G) for b in dest] for a in dest]:raise ValueError('nonmetric symmetry basis')
    for i,v in enumerate(points):
        c=solve(H,[dot(a,v,G) for a in basis]);w=tuple(sum((a*b[j] for a,b in zip(c,dest)),F.zero) for j in range(len(G)))
        if w!=points[p[i]]:raise ValueError('symmetry extension mismatch')

def transitive(n,perms):
    if not perms:raise ValueError('no transitivity witnesses')
    if len(orbit(0,[lambda i,p=p:p[i] for p in perms]))!=n:raise ValueError('nontransitive witness group')

@lru_cache(None)
def exceptional(name):
    cert=next(m for m in json.loads((MODEL_DATA/'q5_certificate.json').read_text())['models'] if m['name']==name)
    F=Field(sp.sqrt(5));G=identity(4,F);cells=cert['cells'];N=len(cert['vertices_600'])
    normals=[tuple(certificate_coordinate(F,p) for p in c['normal']) for c in cells]
    offsets=[certificate_coordinate(F,c['offset']) for c in cells]
    points=[]
    # Reconstruct authoritative exact points from incident rational-quadratic
    # support equations. All certificate incidences are subsequently replayed.
    for i in range(N):
        incident=[j for j,c in enumerate(cells) if i in c['vertices']]
        for inds in combinations(incident,4):
            try:p=solve([normals[j] for j in inds],[offsets[j] for j in inds]);break
            except Undecided:pass
        else:raise ValueError('vertex has no independent incident supports')
        points.append(p)
    if len(set(points))!=N:raise ValueError('exceptional points not distinct')
    R2=dot(points[0],points[0],G)
    if F.sign(R2)!=1 or any(dot(p,p,G)!=R2 for p in points):raise ValueError('exceptional sphere mismatch')
    independent_frame(points,G,F,4)
    verify_exceptional_construction(name,points,F,G)
    if len({tuple(sorted(c['vertices'])) for c in cells})!=len(cells):raise ValueError('duplicate cells')
    poly_cells={}
    for ci,(cell,normal,offset) in enumerate(zip(cells,normals,offsets)):
        ids=cell['vertices'];local=[points[i] for i in ids];independent_frame(local,G,F,3)
        for i,p in enumerate(points):
            d=plain_dot(normal,p,F)-offset
            if i in ids:
                if d:raise ValueError('exceptional support equality')
            elif F.sign(d)!=-1:raise ValueError('exceptional strict support')
        if len({tuple(sorted(f['vertices'])) for f in cell['polygons']})!=len(cell['polygons']):raise ValueError('duplicate cell polygons')
        edge_faces={}
        for face in cell['polygons']:
            vs=face['vertices']
            if not set(vs)<=set(ids):raise ValueError('polygon outside cell')
            fn=tuple(certificate_coordinate(F,p) for p in face['normal']);fo=certificate_coordinate(F,face['offset'])
            for i in ids:
                d=plain_dot(fn,points[i],F)-fo
                if i in vs:
                    if d:raise ValueError('polygon support equality')
                elif F.sign(d)!=-1:raise ValueError('polygon strict support')
            verify_polygon([points[i] for i in vs],G,F)
            for a,b in zip(vs,vs[1:]+vs[:1]):
                key=tuple(sorted((a,b)));edge_faces[key]=edge_faces.get(key,0)+1
            key=tuple(sorted(vs));poly_cells[key]=poly_cells.get(key,0)+1
        if set(edge_faces.values())!={2}:raise ValueError('cell boundary not closed')
        for p in cell['symmetries']:verify_metric_permutation(local,G,F,p)
        transitive(len(local),cell['symmetries'])
        config=sorted(len(f['vertices']) for f in cell['polygons'] if ids[0] in f['vertices'])
        expected={'tet':[3,3,3],'ico':[3]*5,'A5':[3,3,3,5]}[cell['label']]
        if config!=expected:raise ValueError('wrong cell label')
    if set(poly_cells.values())!={2}:raise ValueError('exceptional boundary not closed')
    for p in cert['symmetries']:verify_metric_permutation(points,G,F,p)
    transitive(N,cert['symmetries'])
    nearids=sorted({j for c in cells for f in c['polygons'] for a,j in zip(f['vertices'],f['vertices'][1:]+f['vertices'][:1]) if a==0}|{a for c in cells for f in c['polygons'] for a,j in zip(f['vertices'],f['vertices'][1:]+f['vertices'][:1]) if j==0})
    ix={v:i for i,v in enumerate(nearids)};ep={};ridges=[]
    for c in cells:
        if 0 not in c['vertices']:continue
        ridges.append(([ix[i] for i in nearids if i in c['vertices']],c['label']))
        for f in c['polygons']:
            vs=f['vertices']
            if 0 not in vs:continue
            k=vs.index(0);a,b=vs[k-1],vs[(k+1)%len(vs)];key=tuple(sorted((ix[a],ix[b])));p=len(vs)
            if key in ep and ep[key]!=p:raise ValueError('inconsistent polygon size')
            ep[key]=p
    model=Facet(name,F,G,points[0],[points[i] for i in nearids],ep,ridges,lambda:points)
    model.certificate_verified=True
    return model

@lru_cache(None)
def snub_polyhedron(label):
    kind='B3' if label=='snic' else 'H3';u=sp.Symbol('u')
    if kind=='B3':
        root=sp.CRootOf(u**3-2*u**2+2*u-2,0);F=Field((root,sp.sqrt(2)))
        U=F(root);V=F(sp.sqrt(2))/F(2)*(U*U-U+F.one)
        c01=F(sp.Rational(1,2));c12=F(sp.sqrt(2)/2)
    else:
        root=sp.CRootOf(u**6-4*u**5-16*u**4+8*u**3+64*u**2-64,1);F=Field(root)
        U=F(root);r5=(-U**3+F(2)*U*U-F(4))/(F(2)*U*U-F(4))
        if r5*r5!=F(5) or F.sign(r5)!=1:raise ValueError('wrong snub algebraic conjugate')
        V=-(r5+F(3))/F(8)*U**3-(F.one+r5)/F(4)*U*U+U+(r5+F.one)/F(2)
        c01=(F.one+r5)/F(4);c12=F(sp.Rational(1,2))
    G=((F.one,-c01,F.zero),(-c01,F.one,-c12),(F.zero,-c12,F.one))
    rs=[]
    for i in range(3):
        M=[list(row) for row in identity(3,F)]
        for j in range(3):M[i][j]-=F(2)*G[i][j]
        rs.append(tuple(map(tuple,M)))
    def mm(A,B):return tuple(tuple(sum((A[i][k]*B[k][j] for k in range(3)),F.zero) for j in range(3)) for i in range(3))
    def mv(A,x):return tuple(plain_dot(row,x,F) for row in A)
    A=mm(rs[0],rs[1]);B=mm(rs[1],rs[2]);C=mm(A,B);seed=(F.one,U,V)
    e2=dot(sub(seed,mv(A,seed)),sub(seed,mv(A,seed)),G)
    if F.sign(e2)!=1:raise ValueError('nonpositive snub scale')
    if any(dot(sub(seed,mv(M,seed)),sub(seed,mv(M,seed)),G)!=e2 for M in (B,C)):raise ValueError('snub chord equations fail exactly')
    # Scaling the basis metric avoids adjoining the positive edge square root.
    G=tuple(tuple(v/e2 for v in row) for row in G)
    cert=json.loads((MODEL_DATA/'snub_certificate.json').read_text())['models'][kind]
    matrices=[identity(3,F)]
    for parent,g in cert['parents'][1:]:
        if not 0<=parent<len(matrices) or g not in (0,1):raise ValueError('bad snub construction word')
        matrices.append(mm((A,B)[g],matrices[parent]))
    pts=[mv(M,seed) for M in matrices];N=len(pts)
    if len(set(pts))!=N or N!=(24 if kind=='B3' else 60):raise ValueError('snub orbit not distinct')
    R2=dot(seed,seed,G)
    if any(dot(v,v,G)!=R2 for v in pts):raise ValueError('snub sphere mismatch')
    for M,p in zip((A,B),cert['permutations']):
        if sorted(p)!=list(range(N)) or any(mv(M,v)!=pts[p[i]] for i,v in enumerate(pts)):raise ValueError('snub generator index mismatch')
    transitive(N,cert['permutations']);independent_frame(pts,G,F,3)
    edge_faces={};faces=cert['faces']
    if len({tuple(sorted(v)) for v in faces})!=len(faces):raise ValueError('duplicate snub faces')
    for ids in faces:
        pp=[pts[i] for i in ids];verify_polygon(pp,G,F)
        a,b=sub(pp[1],pp[0]),sub(pp[2],pp[0])
        normal=(a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
        signs=[]
        for i,v in enumerate(pts):
            d=plain_dot(normal,sub(v,pp[0]),F)
            if i in ids:
                if d:raise ValueError('snub face not exactly planar')
            else:signs.append(F.sign(d))
        if set(signs) not in ({1},{-1}):raise ValueError('snub face not strictly supporting')
        for a,b in zip(ids,ids[1:]+ids[:1]):
            k=tuple(sorted((a,b)));edge_faces[k]=edge_faces.get(k,0)+1
    if set(edge_faces.values())!={2}:raise ValueError('snub hull boundary not closed')
    # Certified closed supporting boundary is complete by dual connectivity.
    nearids=sorted(j if i==0 else i for i,j in edge_faces if 0 in (i,j))
    if nearids!=sorted(cert['seeds']):raise ValueError('snub neighbour certificate mismatch')
    ix={v:i for i,v in enumerate(nearids)};ep={}
    for ids in faces:
        if 0 in ids:
            k=ids.index(0);a,b=ids[k-1],ids[(k+1)%len(ids)];ep[tuple(sorted((ix[a],ix[b])))]=len(ids)
    expected=[3,3,3,3,4 if kind=='B3' else 5]
    if sorted(ep.values())!=expected:raise ValueError('wrong snub configuration')
    m=Facet(label,F,G,seed,[pts[i] for i in nearids],ep,[(tuple(range(5)),label)],lambda:pts)
    m.certificate_verified=True
    return m

def snub_prism(label,name=None):
    source=snub_polyhedron(label);F=source.field;n=len(source.exact_neighbours)
    G=tuple(tuple(source.metric[i][j] if i<3 and j<3 else F(sp.Rational(1,4)) if i==j==3 else F.zero for j in range(4)) for i in range(4))
    base=source.base_exact+(F.one,);near=[v+(F.one,) for v in source.exact_neighbours]+[source.base_exact+(-F.one,)]
    ep=dict(source.edge_p);ep.update({(i,n):4 for i in range(n)})
    ridges=[(tuple(range(n)),label)]+[((i,j,n),'cube' if p==4 else 'P'+str(p)) for (i,j),p in source.edge_p.items()]
    return Facet(name or 'pr-'+label,F,G,base,near,ep,ridges,lambda:[v+(t,) for v in source.exact_vertices for t in (F.one,-F.one)])

_KNOWN_CONSTRUCTION_KEY=object()

class KnownModel:
    """Centered unit-edge 5D point model; full orbit is lazy."""
    def __init__(self,name,F,G,base,near,full_factory,provenance,construction_key=None):
        if construction_key is not _KNOWN_CONSTRUCTION_KEY:raise ValueError('KnownModel must be built by known(), with a proved construction recipe')
        self.name=name;self.field=F;self.metric=G;self.base_exact=base
        self.exact_neighbours=tuple(near);self.radius2_exact=dot(base,base,G)
        self.radius2=F.ball(self.radius2_exact);self.base_index=0;self._full_factory=full_factory;self.provenance=provenance
        # Realize with the same rigorous Cholesky implementation as facets.
        temp=Facet.__new__(Facet);temp.field=F;temp.metric=G;temp.base_exact=base
        temp.vf_origin_exact=scale(base,F.one-F.one/(F(2)*self.radius2_exact))
        temp.vf_vectors_exact=tuple(sub(p,temp.vf_origin_exact) for p in near)
        Facet._realize(temp);self._T=temp._T;self.base_vertex=temp.base_vertex
        # Bind the exact output of this construction to its theorem contract.
        # No full-factory invocation: near is already the complete structural
        # neighbour list from parabolic faces or the product edge identity.
        self._construction_signature=(name,tuple(map(tuple,G)),tuple(base),tuple(near),self.radius2_exact,known_facet_types(name))
    _euclidean=Facet._euclidean
    @cached_property
    def facet_types(self):return known_facet_types(self.name)
    @cached_property
    def neighbour_count(self):return len(self.exact_neighbours)
    def certify_known_model(self,full=False):
        """Certify the structural theorem contract; optionally audit full points.

        Default is lazy: exact construction binding, metric/rank, sphere,
        unit local edges and complete construction facet types are checked.
        Exhaustive neighbours and minimum distance follow from the documented
        parabolic/product face theorem, transitivity and inscribed unit edges.
        Set full=True for an additional exhaustive vertex audit.
        """
        F=self.field;G=self.metric
        name,metric,base,near,radius2,types=self._construction_signature
        if (self.name,tuple(map(tuple,G)),tuple(self.base_exact),tuple(self.exact_neighbours),self.radius2_exact,tuple(self.facet_types))!=(name,metric,base,near,radius2,types):raise ValueError('known structural construction binding mismatch')
        if self.base_index!=0 or len(base)!=5 or len(G)!=5 or any(len(row)!=5 for row in G):raise ValueError('known structural dimension/base contract')
        if G!=tuple(zip(*G)):raise ValueError('known metric not symmetric')
        # Exact LDL pivots prove positive definiteness of this exact metric.
        A=[list(row) for row in G]
        for i in range(5):
            pivot=A[i][i]
            if F.sign(pivot)!=1:raise ValueError('known metric not positive definite')
            for j in range(i+1,5):
                for k in range(i+1,5):A[j][k]-=A[j][i]*A[i][k]/pivot
        if radius2!=dot(base,base,G) or F.sign(radius2)!=1:raise ValueError('known structural radius mismatch')
        if len(set(near))!=len(near) or any(len(p)!=5 or p==base for p in near):raise ValueError('known structural neighbours not distinct')
        for p in near:
            if dot(p,p,G)!=radius2 or dot(sub(p,base),sub(p,base),G)!=F.one:raise ValueError('known structural unit edge/sphere mismatch')
        independent_frame([base]+list(near),G,F,5)
        if not types or types!=known_facet_types(name) or any(t not in names() for t in types):raise ValueError('known structural facet library precondition')
        if 'neighbour_count' in self.__dict__ and self.neighbour_count!=len(near):raise ValueError('known cached neighbour count mismatch')
        if full:self._certify_full_vertices()
        return True

    def _certify_full_vertices(self):
        """Replay exact metric/neighbour facts plus construction facet coverage.

        Uniformity, vertex transitivity and the exhaustive face rule are the
        documented mathematical construction premises, not inferred from balls.
        Full exact vertices are materialized to audit all distances at the base.
        """
        F=self.field;G=self.metric;pts=self.exact_vertices
        if len(self.base_exact)!=5 or len(G)!=5 or self.base_index!=0 or self.base_exact!=pts[0]:raise ValueError('known dimension/base contract')
        if F.sign(self.radius2_exact)!=1:raise ValueError('known radius not positive')
        independent_frame(pts,G,F,5)
        actual=[]
        for i,p in enumerate(pts):
            if dot(p,p,G)!=self.radius2_exact:raise ValueError('known vertex off sphere')
            d2=dot(sub(p,pts[0]),sub(p,pts[0]),G)
            if i==0:
                if d2:raise ValueError('known base mismatch')
            elif d2==F.one:actual.append(i)
            elif F.sign(d2-F.one)!=1:raise ValueError('known nonbase distance below one')
        index={p:i for i,p in enumerate(pts)}
        if any(p not in index for p in self.exact_neighbours):raise ValueError('known neighbour not a full vertex')
        wanted=[index[p] for p in self.exact_neighbours]
        if len(set(wanted))!=len(wanted) or set(actual)!=set(wanted) or list(self.neighbours)!=wanted:raise ValueError('known exact neighbour list incomplete')
        if not self.facet_types or tuple(self.facet_types)!=known_facet_types(self.name) or any(t not in names() for t in self.facet_types):raise ValueError('known facet library precondition missing')
        return True
    @cached_property
    def exact_vertices(self):
        pts=tuple(self._full_factory())
        if not pts or pts[0]!=self.base_exact or len(set(pts))!=len(pts):raise ValueError('known full index contract')
        return pts
    @cached_property
    def points5(self):return [self._euclidean(p) for p in self.exact_vertices]
    @property
    def vertices(self):return self.points5
    @cached_property
    def neighbours(self):
        ix={v:i for i,v in enumerate(self.exact_vertices)};return [ix[v] for v in self.exact_neighbours]

def known_names(P=16):
    """Unmerged construction names. P=16 gives the paper's 890-name family."""
    if not isinstance(P,int) or P<3 or P>16:raise ValueError('P must lie in 3..16')
    # Facets filtered by actual source polygon sizes (construction, no radius fingerprints).
    facets=[n for n in names() if (not n.startswith('duoprism-') or max(map(int,n.split('-')[1:]))<=P) and (not n.startswith('antiprism-prism-') or int(n.split('-')[-1])<=P)]
    solids=sorted(set(TABLE3.values())|{'snic','snid'})
    polys=[s for s in solids if max(polyhedron_polygon_sizes(s))<=P]
    polys += ['P'+str(n) for n in range(3,P+1) if n!=4]+['A'+str(n) for n in range(4,P+1)]
    # P4=cube and A3=oct are already in solids; therefore 44 factors at P16.
    return tuple(k+'5'+''.join(map(str,r)) for k in 'ABD' for r in product((0,1),repeat=5) if any(r))+tuple('prism-'+n for n in facets)+tuple('{'+str(p)+'}x'+s for p in range(3,P+1) for s in polys)

def _poly3(label):
    if label in ('snic','snid'):return snub_polyhedron(label)
    if label in set(TABLE3.values()):
        return wythoff(next(k+'3'+''.join(map(str,r)) for (k,r),v in TABLE3.items() if v==label))
    if label.startswith('A') and label[1:].isdigit():
        n=int(label[1:]);F=Field(sp.cos(sp.pi/n));A,B,g=antiprism_data(n,F);near=[A[1],A[-1],B[0],B[-1]]
        return Facet(label,F,diagonal(g,F),A[0],near,{(0,1):n,(0,2):3,(2,3):3,(1,3):3},[(tuple(range(4)),label)],lambda:A+B)
    if label.startswith('P') and label[1:].isdigit():
        n=int(label[1:]);F=Field(sp.cos(2*sp.pi/n));A,g,_=polygon_block(n,F);one=(F.one,);neg=(-F.one,)
        return Facet(label,F,diagonal(g+(F(sp.Rational(1,4)),),F),A[0]+one,[A[1]+one,A[-1]+one,A[0]+neg],{(0,1):n,(0,2):4,(1,2):4},[((0,1,2),label)],lambda:[v+t for v in A for t in (one,neg)])
    raise KeyError(label)

def normalize_known_name(name):
    match=re.fullmatch(r'\{([0-9]+)\}x(.+)',name)
    return 'product-'+match[1]+'-'+match[2] if match else name

@lru_cache(None)
def known_common_field(name):
    requested=name;name=normalize_known_name(name)
    ctx.prec=max(ctx.prec,320)
    if name[:2] in ('A5','B5','D5'):
        src=wythoff(name)
        return KnownModel(requested,src.field,src.metric,src.base_exact,src.exact_neighbours,lambda:src.exact_vertices,'finite Coxeter orbit and parabolic-face theorem',_KNOWN_CONSTRUCTION_KEY)
    if name.startswith('prism-'):
        src=facet(name[6:]);F=src.field;G=tuple(tuple(src.metric[i][j] if i<4 and j<4 else F(sp.Rational(1,4)) if i==j==4 else F.zero for j in range(5)) for i in range(5))
        base=src.base_exact+(F.one,);near=[v+(F.one,) for v in src.exact_neighbours]+[src.base_exact+(-F.one,)]
        return KnownModel(requested,F,G,base,near,lambda:[v+(t,) for v in src.exact_vertices for t in (F.one,-F.one)],'certified facet times unit segment; product identity',_KNOWN_CONSTRUCTION_KEY)
    if name.startswith('product-'):
        _,p,label=name.split('-',2);p=int(p);src=_poly3(label);F=Field((sp.cos(2*sp.pi/p),src.field.theta))
        theta=F(src.field.theta)
        def lift(x):
            out=F.zero
            for q in x.to_list():out=out*theta+F(sp.Rational(int(q.numerator),int(q.denominator)))
            return out
        A,g,_=polygon_block(p,F);baseB=tuple(map(lift,src.base_exact));nearB=[tuple(map(lift,v)) for v in src.exact_neighbours]
        Bmetric=tuple(tuple(map(lift,row)) for row in src.metric)
        G=tuple(tuple((g[i] if i==j else F.zero) if i<2 and j<2 else Bmetric[i-2][j-2] if i>=2 and j>=2 else F.zero for j in range(5)) for i in range(5))
        base=A[0]+baseB;near=[A[1]+baseB,A[-1]+baseB]+[A[0]+v for v in nearB]
        return KnownModel(requested,F,G,base,near,lambda:[a+tuple(map(lift,v)) for a in A for v in src.exact_vertices],'regular polygon times certified uniform polyhedron; product identity',_KNOWN_CONSTRUCTION_KEY)
    raise KeyError(name)


def verify_exceptional_construction(name,points,F,G):
    """Identify the exact 600-cell subset, independently of certificate indices."""
    phi=F((1+sp.sqrt(5))/2);zero=F.zero
    base=(zero,F.one,phi,phi-F.one);noncoordinate=set()
    for perm in permutations(range(4)):
        if sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4))%2:continue
        for signs in product((-1,1),repeat=3):
            v=(zero,)+tuple(F(t)*x*phi/F(2) for t,x in zip(signs,base[1:]))
            noncoordinate.add(tuple(v[i] for i in perm))
    coordinate=set(tuple(phi*F(t) if i==j else zero for i in range(4)) for j in range(4) for t in (-1,1))
    coordinate.update(tuple(phi*F(t)/F(2) for t in signs) for signs in product((-1,1),repeat=4))
    if len(noncoordinate)!=96 or len(coordinate)!=24 or noncoordinate&coordinate:raise ValueError('600-cell coordinate construction')
    actual=set(points)
    if name=='sadi':
        if actual!=noncoordinate:raise ValueError('sadi is not the exact 24-cell deletion')
        return
    whole=noncoordinate|coordinate
    if not actual<=whole or len(actual)!=100:raise ValueError('gap is not a 100-vertex 600-cell subset')
    removed=list(whole-actual);adj={i:[j for j in range(20) if j!=i and dot(sub(removed[i],removed[j]),sub(removed[i],removed[j]),G)==F.one] for i in range(20)}
    if any(len(v)!=2 for v in adj.values()):raise ValueError('removed sets not decagons')
    left=set(range(20));cycles=[]
    while left:
        start=min(left);cyc=[start];prev=None
        while True:
            nxt=next(j for j in adj[cyc[-1]] if j!=prev)
            if nxt==start:break
            if nxt in cyc:raise ValueError('removed cycle repeats')
            prev=cyc[-1];cyc.append(nxt)
        if len(cyc)!=10:raise ValueError('removed cycle not length ten')
        left-=set(cyc);cycles.append([removed[i] for i in cyc])
    if len(cycles)!=2:raise ValueError('not two removed decagons')
    for cyc in cycles:
        verify_polygon(cyc,G,F)
        # Circumcentre of this common-sphere planar polygon must be 0.
        if any(sum((p[j] for p in cyc),F.zero) for j in range(4)):raise ValueError('removed decagon not great')
    if any(dot(a,b,G) for a in cycles[0] for b in cycles[1]):raise ValueError('removed decagon planes not orthogonal')


def canonical_facet_type(name):
    if name not in ALIASES:raise Undecided('construction facet outside the 181-type library: '+name)
    return ALIASES[name]

def duoprism_type(p,q):return canonical_facet_type('duoprism-'+str(min(p,q))+'-'+str(max(p,q)))
def prism_type(label):
    if label.startswith('P') and label[1:].isdigit():return duoprism_type(4,int(label[1:]))
    if label.startswith('A') and label[1:].isdigit():return canonical_facet_type('antiprism-prism-'+label[1:])
    return canonical_facet_type('pr-'+label)

def rank4_type(I,edges,rings):
    """Exact parabolic diagram/product identity, with the allowed alias theorem."""
    cs=components(I,edges)
    if any(not any(rings[i] for i in c) for c in cs):raise ValueError('inactive rank4 component')
    if len(cs)==1:
        c=cs[0];degrees={i:sum(tuple(sorted((i,j))) in edges for j in c if i!=j) for i in c}
        if 3 in degrees.values():
            centre=next(i for i in c if degrees[i]==3);leaves=[i for i in c if i!=centre]
            a,b=next((a,b) for a,b in combinations(leaves,2) if rings[a]==rings[b]);other=next(i for i in leaves if i not in (a,b))
            raw='B4'+''.join(map(str,(rings[other],rings[centre],rings[a],0)))
            return canonical_facet_type(raw)
        for seq in permutations(c):
            labels=tuple(edges.get(tuple(sorted((seq[i],seq[i+1]))),2) for i in range(3))
            kind={(3,3,3):'A',(3,3,4):'B'}.get(labels)
            if kind:return canonical_facet_type(kind+'4'+''.join(str(rings[i]) for i in seq))
        raise Undecided('unsupported connected rank4 parabolic')
    if len(cs)==2 and sorted(map(len,cs))==[1,3]:return prism_type(face_label(next(c for c in cs if len(c)==3),edges,rings))
    polygons=[face_label(c,edges,rings) for c in cs if len(c)==2]
    if len(polygons)==2:return duoprism_type(*polygons)
    if len(polygons)==1:return duoprism_type(polygons[0],4)
    if len(cs)==4:return duoprism_type(4,4)
    raise Undecided('unsupported rank4 product')

@lru_cache(None)
def known_facet_types(name):
    """Complete SET of construction facet types (not occurrence multiplicity)."""
    name=normalize_known_name(name)
    if name[:2] in ('A5','B5','D5'):
        edges=diagram(name[0],5);rings=tuple(map(int,name[2:]))
        if len(rings)!=5 or set(rings)-{0,1} or not any(rings):raise ValueError('bad known rings')
        return tuple(sorted({rank4_type(I,edges,rings) for I in combinations(range(5),4) if face_dimension(I,edges,rings)==4}))
    if name.startswith('prism-'):
        src=canonical_facet_type(name[6:])
        return tuple(sorted({src}|{prism_type(label) for label in facet_cell_types(src)}))
    if name.startswith('product-'):
        _,p,label=name.split('-',2);p=int(p)
        return tuple(sorted({prism_type(label)}|{duoprism_type(p,q) for q in polyhedron_polygon_sizes(label)}))
    raise KeyError(name)

def certify_known_model(model,full=False):
    """Certify a KnownModel or name; full=True additionally audits every vertex."""
    return (known(model) if isinstance(model,str) else model).certify_known_model(full=full)


def wythoff_face_types(kind,n,rings,dim):
    edges=diagram(kind,n)
    return {face_label(I,edges,rings) for I in combinations(range(n),dim) if face_dimension(I,edges,rings)==dim}

@lru_cache(None)
def polyhedron_polygon_sizes(label):
    if label in ('snic','snid'):return frozenset((3,4 if label=='snic' else 5))
    if label.startswith('P') and label[1:].isdigit():return frozenset((4,int(label[1:])))
    if label.startswith('A') and label[1:].isdigit():return frozenset((3,int(label[1:])))
    kind,rings=next((k,r) for (k,r),v in TABLE3.items() if v==label)
    return frozenset(wythoff_face_types(kind,3,rings,2))

@lru_cache(None)
def facet_polygon_sizes(name):
    name=canonical_facet_type(name)
    if name[:2] in ('A4','B4','F4','H4','D4'):return frozenset(wythoff_face_types(name[0],4,tuple(map(int,name[2:])),2))
    if name.startswith('duoprism-'):return frozenset((4,*map(int,name.split('-')[1:])))
    if name.startswith('antiprism-prism-'):return frozenset((3,4,int(name.split('-')[-1])))
    if name.startswith('pr-'):return frozenset({4}|set(polyhedron_polygon_sizes(name[3:])))
    if name in ('sadi','gap'):
        # Exact hull/label validation precedes every use as a precondition.
        # Transitivity makes the base vertex incident to every polygon type.
        return frozenset(exceptional(name).edge_p.values())
    raise KeyError(name)

@lru_cache(None)
def facet_cell_types(name):
    name=canonical_facet_type(name)
    if name[:2] in ('A4','B4','F4','H4','D4'):return frozenset(wythoff_face_types(name[0],4,tuple(map(int,name[2:])),3))
    if name.startswith('duoprism-'):
        return frozenset('cube' if int(n)==4 else 'P'+n for n in name.split('-')[1:])
    if name.startswith('antiprism-prism-'):
        n=int(name.split('-')[-1]);return frozenset(('oct' if n==3 else 'A'+str(n),'P3','cube' if n==4 else 'P'+str(n)))
    if name.startswith('pr-'):
        label=name[3:];return frozenset({label}|{'cube' if p==4 else 'P'+str(p) for p in polyhedron_polygon_sizes(label)})
    if name in ('sadi','gap'):
        # Every cell type meets the base vertex by the certified transitive
        # group. Never let raw, unvalidated JSON labels justify exclusion.
        return frozenset(r['label'] for r in exceptional(name).ridges)
    raise KeyError(name)


@lru_cache(None)
def known(name):
    """Known S3 provider; orthogonal products retain separate exact fields."""
    normalized=normalize_known_name(name)
    if normalized[:2] in ('A5','B5','D5'):return known_common_field(name)
    from factored_known import build
    return build(name)
