"""Exact orthogonal products without constructing algebraic field composita.

Only factor-local operations decide equality/sign. Cartesian-product identities
certify global geometry. Returned Arb arrays concatenate exact factor embeddings.
"""
from collections.abc import Sequence
from functools import cached_property,lru_cache
from itertools import product
import sympy as sp
from flint import arb,ctx
from exact import Field,Undecided,dot,sub,identity
import models as M

class ExactRadiusSum:
    """Formal exact sum of factor radii; no cross-field equality heuristic."""
    def __init__(self,terms):self.terms=tuple(terms)
    def ball(self):return sum((F.ball(x) for F,x in self.terms),arb(0))
    def as_sympy(self):return sum((F.expr(x) for F,x in self.terms),sp.S.Zero)
    def __eq__(self,other):
        if self is other:return True
        if isinstance(other,ExactRadiusSum) and len(self.terms)==len(other.terms) and all(F is H and x==y for (F,x),(H,y) in zip(self.terms,other.terms)):return True
        raise Undecided('cross-field exact sum equality requires an explicit algebraic comparison')
    def __ne__(self,other):return not self.__eq__(other)

class _BasicFactor:
    def __init__(self,spec):
        self.spec=spec;F=Field();self.field=F
        if spec[0]=='segment':
            self.metric=((F(sp.Rational(1,4)),),);self.base_exact=(F.one,)
            self.exact_neighbours=((-self.base_exact[0],),);self._points=(self.base_exact,self.exact_neighbours[0]);self._neighbours=(1,)
        elif spec[0]=='polygon':
            n=spec[1]
            if not isinstance(n,int) or n<3:raise ValueError('polygon n>=3')
            F=Field(sp.cos(2*sp.pi/n));self.field=F;pts,metric,_=M.polygon_block(n,F)
            self.metric=M.diagonal(metric,F);self._points=tuple(pts);self.base_exact=pts[0]
            self.exact_neighbours=(pts[1],pts[-1]);self._neighbours=(1,n-1)
        else:raise ValueError('invalid basic factor')
        self.radius2_exact=dot(self.base_exact,self.base_exact,self.metric)
        self.radius2=F.ball(self.radius2_exact)
        self._scale=tuple(F.ball(self.metric[i][i]).sqrt() for i in range(len(self.metric)))
        if any(not x>0 for x in self._scale):raise Undecided('factor metric positivity')
        self.base_vertex=self._euclidean(self.base_exact)
    def _euclidean(self,p):return tuple(self.field.ball(x)*s for x,s in zip(p,self._scale))
    @property
    def exact_vertices(self):return self._points
    @property
    def neighbours(self):return self._neighbours

@lru_cache(None)
def _source(spec):
    kind,label=spec
    if kind in ('segment','polygon'):return _BasicFactor(spec)
    if kind=='solid':return M._poly3(label)
    if kind=='facet':return M.facet(label)
    raise ValueError('unknown factor specification')

@lru_cache(None)
def _info(spec):
    """Metadata stays lazy for exceptional factors with expensive hull replay."""
    if spec in (('facet','sadi'),('facet','gap')):
        F=Field(sp.sqrt(5));phi=F((1+sp.sqrt(5))/2)
        return (4,9 if spec[1]=='sadi' else 10,F,phi*phi)
    src=_source(spec)
    return (len(src.base_exact),len(src.exact_neighbours),src.field,src.radius2_exact)

def _validate_source(spec,full=False):
    src=_source(spec);F=src.field;G=src.metric;base=src.base_exact;near=tuple(src.exact_neighbours)
    dim,count,RF,r2=_info(spec)
    if len(base)!=dim or len(near)!=count or len(set(near))!=count:raise ValueError('factor structural dimension/count mismatch')
    # Validate metadata in the source field, without any cross-factor arithmetic.
    expected=F(RF.expr(r2))
    if src.radius2_exact!=expected or dot(base,base,G)!=expected or F.sign(expected)!=1:raise ValueError('factor radius metadata mismatch')
    if G!=tuple(zip(*G)):raise ValueError('factor metric not symmetric')
    A=[list(row) for row in G]
    for i in range(dim):
        pivot=A[i][i]
        if F.sign(pivot)!=1:raise ValueError('factor metric not positive definite')
        for j in range(i+1,dim):
            for k in range(i+1,dim):A[j][k]-=A[j][i]*A[i][k]/pivot
    M.independent_frame([base]+list(near),G,F,dim)
    for p in near:
        if len(p)!=dim or p==base or dot(p,p,G)!=expected or dot(sub(p,base),sub(p,base),G)!=F.one:raise ValueError('factor neighbour exact sphere/unit edge mismatch')
    if full:
        pts=src.exact_vertices
        if not pts or pts[0]!=base or len(set(pts))!=len(pts):raise ValueError('factor full index contract')
        wanted=set(near);actual=set()
        for i,p in enumerate(pts):
            if dot(p,p,G)!=expected:raise ValueError('factor full sphere mismatch')
            d=dot(sub(p,base),sub(p,base),G)
            if i==0:
                if d:raise ValueError('factor base mismatch')
            elif d==F.one:actual.add(p)
            elif F.sign(d-F.one)!=1:raise ValueError('factor separation below one')
        if actual!=wanted:raise ValueError('factor full neighbour completeness mismatch')
        if tuple(pts[j] for j in src.neighbours)!=near:raise ValueError('factor full neighbour indices mismatch')
    return True

class _ExactNeighbours(Sequence):
    """Length needs metadata only; coordinates are exact tuples by factor."""
    def __init__(self,owner):self.owner=owner
    def __len__(self):return sum(_info(s)[1] for s in self.owner.factor_specs)
    def __getitem__(self,key):
        if isinstance(key,slice):return tuple(self[i] for i in range(*key.indices(len(self))))
        if not isinstance(key,int):raise TypeError('integer neighbour index required')
        if key<0:key+=len(self)
        if not 0<=key<len(self):raise IndexError(key)
        specs=self.owner.factor_specs;offset=0
        for i,spec in enumerate(specs):
            count=_info(spec)[1]
            if key<offset+count:
                return tuple(tuple(_source(s).exact_neighbours[key-offset] if j==i else _source(s).base_exact) for j,s in enumerate(specs))
            offset+=count
        raise IndexError(key)

_KEY=object()
class FactoredKnownModel:
    """S3 product provider: exact factor data, concatenated Euclidean balls."""
    def __init__(self,name,specs,key=None):
        if key is not _KEY:raise ValueError('use models.known() for a proved factor recipe')
        self.name=name;self.factor_specs=tuple(specs);self.base_index=0
        self._binding=(name,self.factor_specs,M.known_facet_types(name))
        self.exact_neighbours=_ExactNeighbours(self)
        self.provenance='orthogonal product face theorem; separate exact factor fields'
    @cached_property
    def neighbour_count(self):return len(self.exact_neighbours)
    @cached_property
    def facet_types(self):return M.known_facet_types(self.name)
    @cached_property
    def radius2_exact(self):return ExactRadiusSum((_info(s)[2],_info(s)[3]) for s in self.factor_specs)
    @cached_property
    def radius2(self):return self.radius2_exact.ball()
    @cached_property
    def base_exact(self):return tuple(tuple(_source(s).base_exact) for s in self.factor_specs)
    @cached_property
    def base_vertex(self):return tuple(x for s in self.factor_specs for x in _source(s).base_vertex)
    @cached_property
    def exact_vertices(self):return tuple(product(*(_source(s).exact_vertices for s in self.factor_specs)))
    @cached_property
    def points5(self):
        blocks=[tuple(_source(s)._euclidean(v) for v in _source(s).exact_vertices) for s in self.factor_specs]
        return [tuple(x for b in parts for x in b) for parts in product(*blocks)]
    @property
    def vertices(self):return self.points5
    @cached_property
    def neighbours(self):
        sizes=[len(_source(s).exact_vertices) for s in self.factor_specs];strides=[1]*len(sizes)
        for i in range(len(sizes)-2,-1,-1):strides[i]=strides[i+1]*sizes[i+1]
        return [index*strides[i] for i,s in enumerate(self.factor_specs) for index in _source(s).neighbours]
    @property
    def field(self):raise Undecided('factored products have separate factor fields; use factor_specs, or known_common_field(name) explicitly')
    @property
    def metric(self):raise Undecided('factored products have separate factor metrics; use known_common_field(name) explicitly')
    def certify_known_model(self,full=False):
        name,specs,types=self._binding
        if (self.name,self.factor_specs,tuple(self.facet_types))!=(name,specs,types) or self.base_index!=0:raise ValueError('factored construction binding mismatch')
        if not isinstance(self.exact_neighbours,_ExactNeighbours) or self.exact_neighbours.owner is not self:raise ValueError('factored exact neighbour provider replaced')
        if sum(_info(s)[0] for s in specs)!=5:raise ValueError('factored dimension not five')
        if len(self.exact_neighbours)!=sum(_info(s)[1] for s in specs) or self.neighbour_count!=len(self.exact_neighbours):raise ValueError('factored neighbour count mismatch')
        if not types or types!=M.known_facet_types(name) or not set(types)<=set(M.names()):raise ValueError('factored facet library precondition')
        expected_terms=tuple((_info(s)[2],_info(s)[3]) for s in specs)
        if not isinstance(self.radius2_exact,ExactRadiusSum) or len(self.radius2_exact.terms)!=len(expected_terms) or any(F is not H or x!=y for (F,x),(H,y) in zip(self.radius2_exact.terms,expected_terms)):raise ValueError('factored radius construction binding mismatch')
        enclosure=sum((F.ball(x) for F,x in expected_terms),arb(0))
        if not self.radius2.is_finite() or not self.radius2.contains(enclosure):raise Undecided('factored radius ball containment not established')
        for s in specs:_validate_source(s,full=full)
        if full:
            # Distances are sums of nonnegative exact factor distances. Full
            # factor separation implies unit iff exactly one factor changes
            # along a unit edge. No common field or 5D all-pairs test is needed.
            pts=self.exact_vertices
            if not pts or pts[0]!=self.base_exact:raise ValueError('factored full base index')
            if tuple(pts[i] for i in self.neighbours)!=tuple(self.exact_neighbours):raise ValueError('factored full neighbour index mismatch')
        return True

def _solid_specs(label):
    if label.startswith('P') and label[1:].isdigit():return (('polygon',int(label[1:])),('segment',None))
    return (('solid',label),)

def build(name):
    normalized=M.normalize_known_name(name)
    if normalized.startswith('product-'):
        _,p,label=normalized.split('-',2);specs=(('polygon',int(p)),)+_solid_specs(label)
    elif normalized.startswith('prism-'):
        label=M.canonical_facet_type(normalized[6:])
        if label.startswith('duoprism-'):specs=tuple(('polygon',int(n)) for n in label.split('-')[1:])
        elif label.startswith('pr-'):specs=_solid_specs(label[3:])+(('segment',None),)
        elif label.startswith('antiprism-prism-'):specs=(('solid','A'+label.split('-')[-1]),('segment',None))
        else:specs=(('facet',label),)
        specs+=(('segment',None),)
    else:raise KeyError(name)
    return FactoredKnownModel(name,specs,_KEY)
