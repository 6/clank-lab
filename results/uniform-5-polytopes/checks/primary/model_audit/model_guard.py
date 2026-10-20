"""Checked grid-index contract for a fresh-process independent adapter.

This leaves geom/tcert unchanged. Install before any numerical orbit or
model cache is populated, retain the guard while building models/templates,
and require successful completion. The proof is wythoff_proof.md section 8.
"""
from fractions import Fraction as F
import argparse
import hashlib
import json
import math
import multiprocessing
from pathlib import Path
import sys
import time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'check_u3'))
import geom
import tcert

ROOT=Path(__file__).resolve().parents[1]
MASK_LABELS={
 'A3':{'001':'tet','100':'tet','010':'oct','011':'tut','110':'tut','101':'co','111':'toe'},
 'B3':{'001':'cube','100':'oct','010':'co','011':'tic','110':'toe','101':'sirco','111':'girco'},
 'H3':{'001':'ico','100':'doe','010':'id','011':'tid','110':'ti','101':'srid','111':'grid'},
}


class GuardUndecided(ArithmeticError):
    """The model/index contract was not certified; never an exclusion."""


def endpoint(t):
    s,m,e,bits=t
    if bits<0:raise GuardUndecided('nonfinite coordinate endpoint')
    out=F(int(m))
    out=out*(1<<int(e)) if e>=0 else out/F(1<<-int(e))
    return -out if s else out


def guard_point(v):
    if not 1<=len(v)<=5:raise GuardUndecided('unsupported grid dimension')
    mids=geom.vmid(v)
    for x,m in zip(v,mids):
        if not math.isfinite(m) or abs(m)>128:raise GuardUndecided('nonfinite/oversized grid midpoint')
        middle=F(*m.as_integer_ratio());lo,hi=map(endpoint,x._mpi_)
        if not middle-F(1,64)<=lo<=hi<=middle+F(1,64):
            raise GuardUndecided('grid midpoint enclosure bound failed')
        for scale in (2,4):
            scaled=m*scale
            if not math.isfinite(scaled) or F(*scaled.as_integer_ratio())!=middle*scale:
                raise GuardUndecided('inexact grid scaling')
            if math.floor(scaled)!=(middle*scale).__floor__():
                raise GuardUndecided('grid floor disagreement')


class ModelGuard:
    def __init__(self):
        self._keys=('pointset_queries','finder_queries','finder_vertices','catalog_masks')
        # Forked workers inherit the wrappers AND these synchronized counters.
        # A copied dictionary would silently omit all child queries in receipts.
        self._counts=multiprocessing.get_context('fork').Array('Q',len(self._keys))
        self._installed=False

    @property
    def stats(self):
        with self._counts.get_lock():
            return dict(zip(self._keys,self._counts[:]))

    def _count(self,key):
        with self._counts.get_lock():
            self._counts[self._keys.index(key)]+=1

    def require_active(self):
        if (not self._installed or geom.PointSet is not self.pointset
                or tcert.Finder is not self.finder):
            raise GuardUndecided('model guard wrappers are no longer active')

    def __enter__(self):
        if self._installed:
            raise GuardUndecided('model guard is already installed')
        # A later installation cannot retrospectively certify cached BFSs.
        for f in (geom.roots,geom.wythoff_perm,geom.snub_perm,geom.polytope4,geom.polytope5,
                  geom.poly3_sources,geom.label3,geom.polyhedron,tcert.model3,tcert.model4,tcert.model5):
            if f.cache_info().currsize:
                raise GuardUndecided('install model guard before orbit/model caches populate')
        self.old_pointset,self.old_finder=geom.PointSet,tcert.Finder
        old_pointset,old_finder=self.old_pointset,self.old_finder
        audit=self
        class GuardedPointSet(old_pointset):
            def find(self,v):
                guard_point(v);audit._count('pointset_queries')
                return super().find(v)
        class GuardedFinder(old_finder):
            def __init__(self,V):
                for v in V:guard_point(v);audit._count('finder_vertices')
                super().__init__(V)
            def find(self,y):
                guard_point(y);audit._count('finder_queries')
                return super().find(y)
        self.pointset,self.finder=GuardedPointSet,GuardedFinder
        geom.PointSet,tcert.Finder=self.pointset,self.finder
        self._installed=True
        return self

    def __exit__(self,*args):
        geom.PointSet,tcert.Finder=self.old_pointset,self.old_finder
        self._installed=False

    def check_catalog(self):
        # These are construction masks from the proved catalog, not a
        # numerical radius fingerprint asserted to be an exact identity.
        for diag,table in MASK_LABELS.items():
            for mask,label in table.items():
                got=geom.label3(diag,tuple(map(int,mask)))
                if got!=label:raise GuardUndecided('rank-three construction label mismatch')
                self._count('catalog_masks')
        for lab,(_,source) in geom.poly3_sources().items():
            if source[0]=='wythoff':
                _,diag,mask=source
                if MASK_LABELS[diag][''.join(map(str,mask))]!=lab:
                    raise GuardUndecided('polyhedron source/name mismatch')
            elif source not in (('snub','B3'),('snub','H3')) or lab!={'B3':'snic','H3':'snid'}[source[1]]:
                raise GuardUndecided('unknown polyhedron source')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--names',type=Path)
    p.add_argument('--only',nargs='+')
    p.add_argument('--dimension',type=int,choices=(4,5),default=4)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    if a.names:
        spec=json.loads(a.names.read_text());names=[r['name'] for r in spec]
    elif a.only:names=a.only
    else:p.error('provide --names or --only')
    if a.only:
        if not set(a.only)<=set(names):p.error('unknown selected model')
        names=[n for n in names if n in a.only]
    records=[]
    with ModelGuard() as audit:
        audit.check_catalog()
        for name in names:
            start=time.monotonic();before=dict(audit.stats)
            model=(tcert.model4 if a.dimension==4 else tcert.model5)(name)
            V=(geom.polytope4 if a.dimension==4 else geom.polytope5)(name)
            # These checks also reject damaged construction permutations.
            if len(V)!=model.n or len(tcert.orbit([0],model.gens))!=model.n:
                raise GuardUndecided('incomplete/transitivity index model')
            if any(sorted(map(int,g))!=list(range(model.n)) for g in model.gens):
                raise GuardUndecided('nonbijective model generator')
            rec=dict(name=name,vertices=len(V),wall_seconds=time.monotonic()-start,
                     guard_checks={k:audit.stats[k]-before[k] for k in before})
            records.append(rec);print(json.dumps(rec),flush=True)
    result=dict(claim='checked midpoint/grid execution contract; construction provenance supplied by R2 proofs',
                sources={f:hashlib.sha256((ROOT/'check_u3'/f).read_bytes()).hexdigest() for f in ('geom.py','tcert.py','ivla.py')},
                ordered_names=names,records=records,totals=audit.stats)
    a.out.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
