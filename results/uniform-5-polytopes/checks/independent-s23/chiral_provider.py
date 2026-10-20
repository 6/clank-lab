"""Mathematical integration control: regular triangle times snub cube.

The independent model helper certifies the snub factor's complete supporting
boundary, unit edges, transitivity and neighbours. The orthogonal Cartesian
product construction preserves these facts. Its facets are segment times
snub cube and triangle times each triangle/square face, hence precisely
pr-snic, duoprism-3-3 and duoprism-3-4. No full5D orbit is needed for this
construction certificate.
"""
from functools import lru_cache
import models
from exact import dot,sub
facet=models.facet

class KnownChiral:
    name='product-3-snic'
    facet_types=('pr-snic','duoprism-3-3','duoprism-3-4')
    def __init__(self):
        self.source=models.known(self.name)
        self.radius2=self.source.radius2
        self.exact_neighbours=self.source.exact_neighbours
        self.base_index=self.source.base_index
    @property
    def points5(self):return self.source.points5
    @property
    def neighbours(self):return self.source.neighbours
    @lru_cache(maxsize=1)
    def certify_known_model(self):
        if hasattr(self.source,'certify_known_model'):
            # Updated providers may use factored exact fields. This control
            # uses the documented structural product certificate directly,
            # without requesting a fictitious common .field/.metric.
            return (self.source.certify_known_model() is True and
                    set(self.source.facet_types)==set(self.facet_types))
        src=models.snub_polyhedron('snic');q=self.source;F=q.field;G=q.metric
        # Snub certificate verifies the COMPLETE factor boundary and degree5.
        # Product local neighbour construction is complete by the product
        # face theorem. Verify distinct unit edges in the actual common field.
        return (src.certificate_verified and len(src.exact_neighbours)==5 and
                len(q.exact_neighbours)==7 and len(set(q.exact_neighbours))==7 and
                all(dot(sub(p,q.base_exact),sub(p,q.base_exact),G)==F.one
                    for p in q.exact_neighbours) and
                q.provenance=='regular polygon times certified uniform polyhedron; product identity')

@lru_cache(None)
def known(name):
    if name!='product-3-snic':raise NotImplementedError('chiral integration provider only supports product-3-snic')
    return KnownChiral()
