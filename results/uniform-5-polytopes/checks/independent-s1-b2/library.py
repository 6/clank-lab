"""Independent exact reconstruction of the 181 unit-edge facet types.

Public API returns SymPy expressions. No repository input is imported/read.
The optional JSON comparison is a separate program, invoked only afterwards.
"""
from collections import Counter
from functools import lru_cache
import sympy as sp
from parabolic import coxeter, config_label

ALIASES = {
 'A40001':['A41000'], 'A40010':['A40100'], 'A40011':['A41100'],
 'A40101':['A41010'], 'A40111':['A41110'], 'A41011':['A41101'],
 'B40001':['pr-cube','duoprism-4-4'],
 'B40010':['D40011','D41001','D41010'],
 'B40100':['D40100','F40001','F41000'],
 'B40110':['D40111','D41101','D41110'],
 'B41000':['D40001','D40010','D41000'],
 'B41010':['D41011','F40010','F40100'],
 'B41100':['D40101','D40110','D41100'],
 'B41110':['D41111','F40011','F41100'],
 'F40101':['F41010'], 'F40111':['F41110'], 'F41011':['F41101'],
 'pr-oct':['antiprism-prism-3'],
}
ALIAS_TO_NAME = {alias:name for name,aliases in ALIASES.items() for alias in aliases}
CONFIGS = {
 'tet':(3,3,3), 'oct':(3,3,3,3), 'cube':(4,4,4),
 'ico':(3,3,3,3,3), 'doe':(5,5,5), 'tut':(3,6,6),
 'co':(3,4,3,4), 'tic':(3,8,8), 'toe':(4,6,6),
 'sirco':(3,4,4,4), 'girco':(4,6,8), 'id':(3,5,3,5),
 'tid':(5,6,6), 'ti':(3,10,10), 'srid':(3,4,5,4),
 'grid':(4,6,10), 'snic':(3,3,3,3,4), 'snid':(3,3,3,3,5),
}
_CELL_COSINES = {}


def clean(e):
    return sp.factor(sp.radsimp(e))


def polygon_radius_squared(p):
    return 1/(4*sp.sin(sp.pi/sp.sympify(p))**2)


def prism_radius_squared(n):
    return polygon_radius_squared(n)+sp.Rational(1,4)


def antiprism_radius_squared(n):
    n = sp.sympify(n)
    t = sp.cos(sp.pi/n)
    return (3-2*t)/(8*(1-t))


def prism_label(p):
    return 'cube' if p == 4 else 'P'+str(p)


@lru_cache(None)
def cell_radii():
    ans = {}
    for group in ('A3','B3','H3'):
        C = coxeter(group)
        for bits in range(1,8):
            J = frozenset(i for i in range(3) if bits & (1 << (2-i)))
            data = C.local_data(J)
            label = config_label(data['polygon_sizes'].values())
            radius = clean(C.f.expr(C.radius_squared(J)))
            if label in ans:
                if not (sp.simplify(ans[label]-radius) == 0):
                    raise AssertionError()
            ans[label] = radius
            normals = C.facet_normals(J,data['polygons'])
            for edge in data['edges']:
                U,V = [P for P in data['polygons'] if edge <= P]
                p,q = sorted((data['polygon_sizes'][U],data['polygon_sizes'][V]))
                sign,square = C.internal_cosine(normals,U,V)
                key = (label,p,q)
                cosine = sign*sp.sqrt(clean(C.f.expr(square)))
                if key in _CELL_COSINES:
                    if not (sp.simplify(_CELL_COSINES[key]-cosine) == 0):
                        raise AssertionError()
                _CELL_COSINES[key] = cosine
    # Neighbor-circle derivation: z=sin(t)^2, where four triangular
    # arcs t plus one n-gonal arc sum to pi. The unique z in (1/4,1/3)
    # solves 16(1-z)(1-2z)^2=4cos(pi/n)^2. R^2=z/(4z-1).
    z = sp.Symbol('z')
    poly = 16*(1-z)*(1-2*z)**2
    for label,n in (('snic',4),('snid',5)):
        polynomial = sp.expand(poly-2) if n == 4 else sp.expand(poly**2-3*poly+1)
        roots = sp.polys.polytools.intervals(polynomial,eps=sp.Rational(1,2**180))
        selected = []
        real_index = 0
        for (a,b),mult in roots:
            if sp.Rational(1,4) < a and b < sp.Rational(1,3):
                # For H3, conjugation adds a second root in a different
                # interval; impose the original positive sqrt(5) equation.
                if n == 4 or (poly.subs(z,(a+b)/2) > sp.Rational(5,2)):
                    selected.append(real_index)
            real_index += mult
        if not (len(selected) == 1):
            raise AssertionError((label,roots,selected))
        root = sp.CRootOf(polynomial,selected[0])
        ans[label] = root/(4*root-1)
    if not (set(ans) == set(CONFIGS)):
        raise AssertionError(set(CONFIGS)-set(ans))
    return ans


def cell_radius_squared(name):
    if name.startswith('P'):
        return clean(prism_radius_squared(int(name[1:])))
    if name.startswith('A'):
        n = int(name[1:])
        return clean(antiprism_radius_squared(n))
    return cell_radii()[name]


@lru_cache(None)
def word_cosine(radius_squared,p,A,B):
    rp2 = polygon_radius_squared(p)
    T = clean(radius_squared-rp2)
    a = clean(cell_radius_squared(A)-rp2)
    b = clean(cell_radius_squared(B)-rp2)
    # When both incident cells have equal radius, remove the square roots
    # exactly; all lengths here are strictly positive in a genuine facet.
    if A == B or a == b:
        return clean(2*a/T-1)
    return clean((sp.sqrt(clean(a*b))-sp.sqrt(clean((T-a)*(T-b))))/T)


def make_record(name,radius,occurrences,incidences=None,cosines=None):
    radius = clean(radius) if not radius.has(sp.CRootOf) else radius
    counts = Counter((p,*sorted((a,b))) for p,a,b in occurrences)
    words = []
    for (p,a,b),mult in sorted(counts.items()):
        words.append({'p':p,'A':a,'B':b,'multiplicity':mult,
                      'cos_alpha':cosines[p,a,b] if cosines is not None else word_cosine(radius,p,a,b)})
    record = {'name':name,'aliases':ALIASES.get(name,[]),
              'radius_squared':radius,'words':words}
    if incidences is not None:
        record['incidences'] = incidences
    return record


def wythoff_records():
    records = []
    for group in ('A4','B4','D4','F4','H4'):
        C = coxeter(group)
        for bits in range(1,16):
            pattern = format(bits,'04b')
            name = group+pattern
            if name in ALIAS_TO_NAME:
                continue
            J = frozenset(i for i,c in enumerate(pattern) if c == '1')
            data = C.local_data(J)
            radius = C.f.expr(C.radius_squared(J))
            normals = C.facet_normals(J,data['cells'])
            exact_cosines = {}
            cosines = {}
            for polygon,p in data['polygon_sizes'].items():
                U,V = [cell for cell in data['cells'] if polygon <= cell]
                a,b = sorted((data['labels'][U],data['labels'][V]))
                signed_square = C.internal_cosine(normals,U,V)
                key = (p,a,b)
                if key in exact_cosines:
                    if not (exact_cosines[key] == signed_square):
                        raise AssertionError()
                exact_cosines[key] = signed_square
                sign,square = signed_square
                cosines[key] = sign*sp.sqrt(clean(C.f.expr(square)))
            # Independently cross-check conventional cell radii with the
            # exact Gram solve on the active rank-three parabolic.
            for cell,I in data['cells'].items():
                label = data['labels'][cell]
                Rcell = C.f.expr(C.radius_squared(J,I))
                if not (sp.simplify(Rcell-cell_radius_squared(label)) == 0):
                    raise AssertionError((name,label))
            # Stable local vertex/face incidence export, independent of root
            # hash ordering. The root vectors themselves are exact strings.
            roots = sorted(v for singleton in data['edges'] for v in singleton)
            root_index = {v:i for i,v in enumerate(roots)}
            cells = sorted(data['cells'],key=lambda F:tuple(sorted(root_index[v] for v in F)))
            polygons = sorted(data['polygons'],key=lambda F:tuple(sorted(root_index[v] for v in F)))
            incidences = {
                'neighbor_roots':[[str(C.f.expr(x)) for x in v] for v in roots],
                'cells':[{'neighbors':sorted(root_index[v] for v in F),'label':data['labels'][F]} for F in cells],
                'polygons':[{'neighbors':sorted(root_index[v] for v in F),
                             'p':data['polygon_sizes'][F],
                             'cells':[i for i,Cc in enumerate(cells) if F <= Cc]} for F in polygons],
            }
            records.append(make_record(name,radius,data['occurrences'],incidences,cosines))
    if not (len(records) == 45):
        raise AssertionError()
    return records


def prism_record(name,label,configuration):
    conf = list(configuration)
    k = len(conf)
    occurrences = [(p,label,prism_label(p)) for p in conf]
    occurrences += [(4,prism_label(conf[i]),prism_label(conf[(i+1)%len(conf)]))
                    for i in range(len(conf))]
    cosines = {(p,*sorted((label,prism_label(p)))):sp.Integer(0) for p in conf}
    cell_radii()  # initializes the independently derived 3D dihedral map
    for i in range(k):
        p,q = sorted((conf[i],conf[(i+1)%k]))
        A,B = sorted((prism_label(p),prism_label(q)))
        if label in CONFIGS and label not in ('snic','snid'):
            cosine = _CELL_COSINES[label,p,q]
        elif label.startswith('A'):
            n = int(label[1:])
            t = sp.cos(sp.pi/n)
            cosine = (1-4*t)/3 if p == q == 3 else -sp.sqrt((1-t)/(3*(1+t)))
        else:
            cosine = word_cosine(cell_radius_squared(label)+sp.Rational(1,4),4,A,B)
        cosines[4,A,B] = cosine
    cells = [{'neighbors':list(range(k)),'label':label}]
    cells += [{'neighbors':[i,(i+1)%k,k],'label':prism_label(p)} for i,p in enumerate(conf)]
    polygons = [{'neighbors':[i,(i+1)%k],'p':p,'cells':[0,i+1]} for i,p in enumerate(conf)]
    polygons += [{'neighbors':[i,k],'p':4,'cells':[(i-1)%k+1,i+1]} for i in range(k)]
    return make_record(name,cell_radius_squared(label)+sp.Rational(1,4),occurrences,
                       {'construction':'polyhedron x segment','configuration':conf,
                        'neighbor_count':k+1,'cells':cells,'polygons':polygons},cosines)


def product_records(pmax=16):
    ans = [prism_record('pr-'+label,label,conf) for label,conf in CONFIGS.items() if label != 'cube']
    for n in range(4,pmax+1):
        ans.append(prism_record('antiprism-prism-'+str(n),'A'+str(n),(3,3,3,n)))
    for p in range(3,pmax+1):
        for q in range(p,pmax+1):
            if p == q == 4:
                continue
            occurrences = [(p,prism_label(p),prism_label(p)),
                           (q,prism_label(q),prism_label(q))]
            occurrences += [(4,prism_label(p),prism_label(q))]*4
            cosines = {(p,prism_label(p),prism_label(p)):-sp.cos(2*sp.pi/q),
                       (q,prism_label(q),prism_label(q)):-sp.cos(2*sp.pi/p),
                       (4,*sorted((prism_label(p),prism_label(q)))):sp.Integer(0)}
            # Neighbor labels 0,1 lie along the first polygon, 2,3 the
            # second. There are two cells of each prism type.
            cells = [{'neighbors':[0,1,i],'label':prism_label(p)} for i in (2,3)]
            cells += [{'neighbors':[i,2,3],'label':prism_label(q)} for i in (0,1)]
            polygons = [{'neighbors':[0,1],'p':p,'cells':[0,1]},
                        {'neighbors':[2,3],'p':q,'cells':[2,3]}]
            polygons += [{'neighbors':[i,j],'p':4,'cells':[j-2,i+2]} for i in (0,1) for j in (2,3)]
            ans.append(make_record('duoprism-%d-%d'%(p,q),
                                  polygon_radius_squared(p)+polygon_radius_squared(q),occurrences,
                                  {'construction':'polygon x polygon','p':p,'q':q,
                                   'neighbor_count':4,'cells':cells,'polygons':polygons},cosines))
    return ans


@lru_cache(None)
def library_records():
    from exceptional import exceptional_records
    records = wythoff_records()+exceptional_records()+product_records(16)
    records.sort(key=lambda r:r['name'])
    if not (len(records) == 181):
        raise AssertionError()
    if not (sum(len(r['words']) for r in records) == 558):
        raise AssertionError()
    if not (sum(w['multiplicity'] for r in records for w in r['words']) == 1277):
        raise AssertionError()
    return records


if __name__ == '__main__':
    import argparse
    from export import export_library
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',default='library.json')
    parser.add_argument('--bits',type=int,default=200)
    args = parser.parse_args()
    export_library(args.output,args.bits)
