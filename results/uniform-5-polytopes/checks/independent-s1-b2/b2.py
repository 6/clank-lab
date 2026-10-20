#!/usr/bin/env python3
"""Independent B2, derived solely from main.tex, sections 4.4--4.5.

Arithmetic: python-flint Arb, 320 bits; all acceptance uses certified balls
or outward-rounded integer intervals. No float participates in a decision.
Unresolved signs, root boxes, overlaps and missing positive controls fail.
"""
from receipt_policy import compare_receipt, read_receipt
import argparse
import bisect
import copy
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path
from flint import arb, fmpq, ctx

ctx.prec = 320
SCALE = 10**65
TOL = Fraction(1, 2**250)
PAIRS = ((3, 3), (3, 4), (3, 5))


class Unresolved(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise Unresolved(message)


def ball(q):
    if isinstance(q, Fraction):
        return arb(fmpq(q.numerator, q.denominator))
    return arb(q)


def hull(a, b):
    return ball(a).union(ball(b))


def sign(x):
    require(x.is_finite(), 'nonfinite arithmetic')
    if x > 0:
        return 1
    if x < 0:
        return -1
    raise Unresolved('uncertified sign: ' + str(x))


def fraction(x):
    q = x.fmpq()
    return Fraction(int(q.p), int(q.q))


def scaled(x):
    require(x.is_finite(), 'nonfinite enclosure')
    a, b = fraction(x.lower()) * SCALE, fraction(x.upper()) * SCALE
    return [a.numerator // a.denominator, -((-b.numerator) // b.denominator)]


def unscaled(ab):
    return hull(Fraction(ab[0], SCALE), Fraction(ab[1], SCALE))


def cosine(q):
    return arb.cos_pi_fmpq(fmpq(1, q))


def polygon_r2(q, slip=False):
    s = arb.sin_pi_fmpq(fmpq(2 if slip else 1, q))
    return 1 / (4 * s*s)


def antiprism_h2(n):
    c = arb.cos_pi_fmpq(fmpq(1, 2*n))
    return 1 - 1 / (4*c*c)


class Omega:
    def __init__(self, rows):
        require(isinstance(rows, list) and rows, 'empty Omega')
        self.source_rows=copy.deepcopy(rows)
        parsed = []
        self.inner = {}
        for row in rows:
            require(isinstance(row, list) and len(row) == 3, 'bad Omega row')
            a, b, ident = row
            # Fraction parses decimal strings exactly, and rejects NaN/Infinity.
            require(isinstance(a, str) and isinstance(b, str), 'non-string endpoint')
            a, b = Fraction(a), Fraction(b)
            require(0 < a <= b, 'reversed/nonpositive Omega')
            require(type(ident) is int, 'noninteger cycle id')
            lo = (a*SCALE).numerator // (a*SCALE).denominator
            hiq = b*SCALE
            hi = -((-hiq.numerator)//hiq.denominator)
            parsed.append((lo, hi, ident))
            loq=a*SCALE
            inner_lo=-((-loq.numerator)//loq.denominator)
            inner_hi=hiq.numerator//hiq.denominator
            self.inner.setdefault(ident,[]).append((inner_lo,inner_hi))
        parsed.sort()
        self.rows = parsed
        self.lo = [x[0] for x in parsed]
        self.prefix_hi = []
        top = -1
        for _, hi, _ in parsed:
            top = max(top, hi)
            self.prefix_hi.append(top)
        self.max_hi = top

    def query(self, ab):
        a, b = ab
        j = bisect.bisect_right(self.lo, b) - 1
        if j < 0 or self.prefix_hi[j] < a:
            # This is a certified lower bound on distance to the whole union.
            gaps = []
            if j >= 0:
                gaps.append(a - self.prefix_hi[j])
            if j+1 < len(self.lo):
                gaps.append(self.lo[j+1] - b)
            require(gaps and min(gaps) > 0, 'bad exclusion gap')
            return [], min(gaps)
        hits = []
        while j >= 0 and self.prefix_hi[j] >= a:
            lo, hi, ident = self.rows[j]
            if hi >= a:
                hits.append(ident)
            j -= 1
        require(hits, 'incomplete Omega query')
        return sorted(hits), 0

    def contains(self, ab, candidates):
        # Inward-rounded Omega endpoints prove actual containment, while
        # the outward endpoints above prove disjointness. Distinct roles.
        a,b=ab
        return any(lo<=a<=b<=hi for ident in candidates
                   for lo,hi in self.inner[ident])


def configurations(limit):
    """Enumerate all sorted tuples with exact sum(1-2/q)<2.

    For a partial tuple, completing with copies of its next entry gives
    the minimum possible angle sum. Once that sum reaches 2, larger
    entries are impossible too; hence the break discards no configuration.
    """
    def extend(prefix, left, lo, angle):
        if not left:
            yield prefix
            return
        for q in range(lo, limit+1):
            term = 1-Fraction(2, q)
            if angle + left*term >= 2:
                break
            yield from extend(prefix+(q,), left-1, q, angle+term)
    for k in (3, 4, 5):
        yield from extend((), k, 3, Fraction(0))


DEGENERATE = {(3,3,4), (3,4,6), (3,5,10)}


def configuration_radius(c, cosines):
    """Return R_c^2 or certified nonclosable/degenerate status."""
    sides = [4*cosines[q]**2 for q in c]
    if len(c) == 3:
        if c in DEGENERATE:
            # Exact identities from main.tex: 1+1=2, 1+2=3,
            # 1+(3+sqrt(5))/2=(5+sqrt(5))/2.
            return 'degenerate', None
        acute = sign(sides[0]+sides[1]-sides[2])
        if acute < 0:
            return 'not_closable', None
        A, B, C = sides
        s2 = A*B*C / ((A+B+C)**2 - 2*(A*A+B*B+C*C))
        require(s2 > 0 and s2 < 1, 'triangle radius domain')
        return 'closable', 1/(4*(1-s2))
    # For k>=4 the paper proves closability from the strict angle sum.
    # f is strictly decreasing. Establish strict signs at *certified*
    # endpoints; no fixed epsilon is ever interpreted as nonclosability.
    def f(s):
        return sum((cosines[q]/s).asin() for q in c)-arb.pi()
    lower = fraction(cosines[c[-1]].upper())
    require(sign(f(ball(1))) == -1, 'upper closure endpoint')
    found = False
    for exponent in range(8, 300, 8):
        a = lower+Fraction(1, 2**exponent)
        if a >= 1:
            continue
        v = f(ball(a))
        if v.is_finite() and v > 0:
            found = True
            break
    require(found, 'no certified interior lower closure endpoint')
    b = Fraction(1)
    while b-a > TOL:
        m = (a+b)/2
        s = sign(f(ball(m)))
        if s > 0:
            a = m
        else:
            b = m
    s = hull(a, b)
    require(s > cosines[c[-1]] and s < 1, 'closure bracket domain')
    return 'closable', 1/(4*(1-s*s))


def polyval(p, x):
    y = arb(0)
    for a in reversed(p):
        y = y*x+a
    return y


def derivative(p):
    return [i*p[i] for i in range(1, len(p))]


def nonroot_split(p, a, b):
    # A dyadic midpoint can be an exact root (n=3, gamma=1/2).
    # Choosing another interior point preserves exhaustive coverage.
    for numerator, denominator in ((1,2),(1,3),(2,3),(1,4),(3,4)):
        m=a+(b-a)*Fraction(numerator,denominator)
        v=polyval(p,ball(m))
        if v > 0 or v < 0:
            return m,sign(v)
    raise Unresolved('no certified nonroot split point')


def polynomial(n, pair):
    h = antiprism_h2(n)
    if pair == (3,3):
        # Cancel exactly (1-gamma), as specified in main.tex.
        return [h/2, 3*h/2, h-1]
    c1 = arb(1)/2
    c2 = arb(0) if pair == (3,4) else (1-arb(5).sqrt())/4
    # N=(1-c1^2-c2^2)+2*c1*c2*g-g^2; M=g+(1-c1-c2).
    a, b, d = 1-c1*c1-c2*c2, 2*c1*c2, 1-c1-c2
    return [h*a-d*d, h*(a+b)-(2*d-d*d), h*(b-1)-(1-2*d), 1-h]


def isolate_roots(p):
    """Cover [-1,1] by certified rootless or one-root intervals.

    A rootless box has nonzero interval evaluation, or monotone p with
    equal endpoint signs. Opposite endpoint signs + nonzero derivative
    prove exactly one root. Every split point must have nonzero p.
    Thus coverage does not depend on an expected root count.
    """
    dp = derivative(p)
    sign(polyval(p, ball(-1)))
    sign(polyval(p, ball(1)))
    stack = [(Fraction(-1), Fraction(1), 0)]
    roots = []
    boxes = 0
    while stack:
        a, b, depth = stack.pop()
        boxes += 1
        require(depth < 300, 'unresolved root subdivision')
        x = hull(a,b)
        v = polyval(p, x)
        if v > 0 or v < 0:
            continue
        sa, sb = sign(polyval(p,ball(a))), sign(polyval(p,ball(b)))
        d = polyval(dp, x)
        if d > 0 or d < 0:
            if sa == sb:
                continue
            while b-a > TOL:
                m,sm = nonroot_split(p,a,b)
                if sm == sa:
                    a = m
                else:
                    b = m
            require(-1 < a < b < 1, 'root touches domain endpoint')
            roots.append((a,b))
            continue
        m,_ = nonroot_split(p,a,b)
        stack.append((m,b,depth+1))
        stack.append((a,m,depth+1))
    roots.sort()
    return roots, boxes


def root_record(n, pair, ab):
    a,b = ab
    g = hull(a,b)
    c1 = arb(1)/2
    c2 = {3:arb(1)/2, 4:arb(0), 5:(1-arb(5).sqrt())/4}[pair[1]]
    N = 1-g*g-c1*c1-c2*c2+2*g*c1*c2
    require(N > 0, 'root norm undecided')
    eta_sign = sign(1+g-c1-c2)
    rad2 = polygon_r2(n)+antiprism_h2(n)/4+1/(2*(1+g))
    return {'pair':list(pair), 'gamma':[str(a),str(b)],
            'geometric':eta_sign < 0, 'radius':scaled(rad2.sqrt())}


def audit_root_records(n, pair, records):
    """Independent degree<=3 Sturm count and bracket validation."""
    p = polynomial(n,pair)
    seq = [p,derivative(p)]
    while len(seq[-1]) > 1:
        r = list(seq[-2])
        divisor = seq[-1]
        while len(r) >= len(divisor):
            f = r[-1]/divisor[-1]
            off = len(r)-len(divisor)
            for i in range(len(divisor)-1):
                r[off+i] -= f*divisor[i]
            # The leading term cancels algebraically, not approximately.
            r.pop()
        require(r and (r[-1]>0 or r[-1]<0), 'Sturm degree/repeated root unresolved')
        seq.append([-x for x in r])
    sign(seq[-1][0])
    def variations(x):
        signs = [sign(polyval(s,ball(x))) for s in seq]
        return sum(a!=b for a,b in zip(signs,signs[1:]))
    count = variations(-1)-variations(1)
    require(len(records)==count, 'missing/extra polynomial root')
    previous = Fraction(-1)
    for rec in records:
        a,b = map(Fraction,rec['gamma'])
        require(previous < a < b < 1, 'root bracket overlap/endpoint')
        require(variations(a)-variations(b)==1, 'root bracket Sturm count')
        require(sign(polyval(p,ball(a))) != sign(polyval(p,ball(b))), 'root bracket signs')
        require(rec == root_record(n,pair,(a,b)), 'root semantic label/radius mismatch')
        previous=b
    return count


def get_configurations(limit):
    cosines = {q:cosine(q) for q in range(3,limit+1)}
    good, statuses = [], {'closable':0,'not_closable':0,'degenerate':0}
    digest = hashlib.sha256()
    for c in configurations(limit):
        status, r2 = configuration_radius(c,cosines)
        statuses[status] += 1
        digest.update(json.dumps([c,status],separators=(',',':')).encode()+b'\n')
        if r2 is not None:
            # Also certify the q cutoff inequality for every retained tuple.
            # Equality is possible (right limit), so permit outward error
            # by using S>cos(max) for nontriangles and acuteness for triangles.
            good.append((c,r2))
    return good,statuses,digest.hexdigest()


def compute_unit(n, configs, qmax, omega, exclusion=True, slip=False):
    counts = {'i':0,'ii':0,'iii':0}
    hits = {'i':0,'ii':0,'iii':0,'geometric':0,'non_geometric':0}
    digest = hashlib.sha256()
    minimum = None
    closest = None
    roots = []
    def observe(kind, key, r, geometric=None):
        nonlocal minimum,closest
        ab = scaled(r)
        matches,gap = omega.query(ab)
        counts[kind] += 1
        if matches:
            hits[kind] += 1
            if geometric is not None:
                hits['geometric' if geometric else 'non_geometric'] += 1
            require(not exclusion, 'B2 overlap: '+str((n,kind,key,matches)))
            # Controls must prove inclusion, not just a possible overlap.
            require(omega.contains(ab,matches),'positive overlap without certified containment')
        elif minimum is None or gap < minimum:
            minimum,closest=gap,[kind,key,ab]
        digest.update(json.dumps([kind,key,ab,matches],separators=(',',':')).encode()+b'\n')
    rn = polygon_r2(n,slip)
    an = rn+antiprism_h2(n)/4
    for c,rc in configs:
        observe('i',list(c),(rn+rc).sqrt())
    for q in range(3,qmax+1):
        observe('ii',q,(an+polygon_r2(q)).sqrt())
    boxes = 0
    for pair in PAIRS:
        brackets, visited = isolate_roots(polynomial(n,pair))
        boxes += visited
        recs = [root_record(n,pair,ab) for ab in brackets]
        audit_root_records(n,pair,recs)
        for rec in recs:
            g = hull(*map(Fraction,rec['gamma']))
            observe('iii',[list(pair),rec['gamma']],
                    (an+1/(2*(1+g))).sqrt(),rec['geometric'])
        roots.extend(recs)
    branches={'geometric':sum(r['geometric'] for r in roots),
              'non_geometric':sum(not r['geometric'] for r in roots)}
    return {'n':n,'counts':counts,'hits':hits,'branches':branches,'radius_stream_sha256':digest.hexdigest(),
            'min_gap_scaled':minimum,'closest':closest,'roots':roots,'root_cover_boxes':boxes}


def controls(omega):
    configs,statuses,_ = get_configurations(16)
    units = [compute_unit(n,configs,16,omega,False) for n in range(3,17)]
    sums = {k:sum(u['hits'][k] for u in units) for k in units[0]['hits']}
    totals = {k:sum(u['counts'][k] for u in units) for k in ('i','ii','iii')}
    require(sums['i']==totals['i']==1750, 'type-i positive control')
    require(sums['ii']==totals['ii']==196, 'type-ii positive control')
    require(sums['geometric']==42 and sums['non_geometric']==2 and totals['iii']==70,
            'type-iii positive control')
    # The exact n=3, (3,4), gamma=1/2 control is sqrt(5/6).
    require(omega.query(scaled((arb(5)/6).sqrt()))[0], 'sqrt(5/6) control absent')
    return {'configurations':statuses,'counts':totals,'hits':sums}


def semantic_tests(omega):
    results=[]
    def rejects(name,fn):
        try:
            fn()
        except (Unresolved,ValueError,TypeError):
            results.append(name)
        else:
            raise Unresolved('semantic corruption accepted: '+name)
    brackets,_=isolate_roots(polynomial(17,(3,5)))
    recs=[root_record(17,(3,5),ab) for ab in brackets]
    require(not recs[1]['geometric'] and Fraction(recs[1]['gamma'][1])<0,
            'negative nongeometric corruption witness')
    rejects('dropped negative nongeometric root',lambda:audit_root_records(17,(3,5),recs[:1]))
    rejects('duplicate root',lambda:audit_root_records(17,(3,5),[recs[0],recs[0]]))
    bad=copy.deepcopy(recs);bad[0]['geometric']=not bad[0]['geometric']
    rejects('branch relabel',lambda:audit_root_records(17,(3,5),bad))
    bad=copy.deepcopy(recs);bad[0]['gamma'][0]='-1'
    rejects('endpoint bracket',lambda:audit_root_records(17,(3,5),bad))
    bad=copy.deepcopy(recs);bad[0]['radius'][0]+=10**30
    rejects('radius mutation',lambda:audit_root_records(17,(3,5),bad))
    rejects('unresolved sign',lambda:sign(hull(-1,1)))
    rejects('reversed Omega',lambda:Omega([['2','1',0]]))
    rejects('unbounded Omega',lambda:Omega([['1','Infinity',0]]))
    rejects('empty Omega',lambda:Omega([]))
    # Three *computed* witness radii, one from each family. Insert disjoint
    # intervals and exercise the same exclusion predicate as the main run.
    config=get_configurations(3)[0][0]
    witnesses=[(polygon_r2(17)+config[1]).sqrt(),
               (polygon_r2(17)+antiprism_h2(17)/4+polygon_r2(3)).sqrt(),
               unscaled(recs[0]['radius'])]
    inserted=[]
    for i,r in enumerate(witnesses):
        a,b=scaled(r)
        inserted.append([str(Fraction(a-100,SCALE)),str(Fraction(b+100,SCALE)),900000+i])
    poisoned=Omega(omega.source_rows+inserted)
    require(sum(bool(poisoned.query(scaled(r))[0]) for r in witnesses)==3,
            'three injected intervals not found')
    for i,r in enumerate(witnesses):
        rejects('injected radius '+str(i),lambda r=r:require(not poisoned.query(scaled(r))[0], 'injected hit'))
    full_configs=get_configurations(397)[0]
    injected_unit=compute_unit(17,full_configs,397,poisoned,False)
    require(sum(injected_unit['hits'][k] for k in ('i','ii','iii'))==3,
            'three inserted intervals do not give exactly three coincidences')
    results.append('three injected intervals give exactly three full-unit coincidences')
    # A deliberately wrong r_n=1/(2sin(2pi/n)) is r_(n/2) at even n.
    # Exercise this semantic error against actual Omega, not a synthetic one.
    require(omega.query(scaled((polygon_r2(18,True)+config[1]).sqrt()))[0],
            'wrong-angle control not detected')
    results.append('wrong polygon angle produces forbidden B2 overlap')
    control_configs=get_configurations(16)[0]
    wrong_hits=0
    for n in range(18,33,2):
        for _,rc in control_configs:
            ab=scaled((polygon_r2(n,True)+rc).sqrt())
            matches,_=omega.query(ab)
            require(matches and omega.contains(ab,matches),'wrong-angle containment control')
            wrong_hits+=1
    require(wrong_hits==1000,'wrong-angle coincidence count')
    results.append('wrong polygon angle gives 1000 certified type-i coincidences')
    # Prefix maxima handle nested intervals and arbitrarily remote starts.
    nested=Omega([['1','100',0],['2','3',1],['4','5',2]])
    require(nested.query([90*SCALE,91*SCALE])[0]==[0], 'nested interval query')
    results.append('nested complete Omega query')
    return results


def run(args):
    raw=Path(args.omega).read_bytes()
    omega=Omega(json.loads(raw)['intervals'])
    cutoff=scaled(polygon_r2(398).sqrt())
    require(cutoff[0]>omega.max_hi, 'finite cutoff 398 not certified')
    report={'schema':'independent-b2-arb-v1','omega_sha256':hashlib.sha256(raw).hexdigest(),
            'precision_bits':ctx.prec,'scale':str(SCALE),'root_tolerance':str(TOL),
            'cutoff':{'n':398,'r398':cutoff,'omega_max_upper_scaled':omega.max_hi,
                      'tail':'r_n increasing; each family R>r_n; i R_c>=r_qmax; ii R>=r_q'},
            'positive_controls':controls(omega),'semantic_tests':semantic_tests(omega)}
    print('positive and semantic controls passed',file=sys.stderr,flush=True)
    if args.controls_only:
        report['scope']='controls only; not full B2'
    else:
        configs,statuses,config_digest=get_configurations(397)
        require(len(configs)==1304,'closable multiset count disagrees with paper')
        report['configurations']={'statuses':statuses,'classification_sha256':config_digest,
            'radii_squared':[[list(c),scaled(rc)] for c,rc in configs]}
        ns=sorted(set(args.sample)) if args.sample else range(17,398)
        require(all(17<=n<=397 for n in ns),'sample out of range')
        report['scope']='sample only; not full B2' if args.sample else 'full B2'
        report['units']=[]
        for n in ns:
            unit=compute_unit(n,configs,397,omega)
            report['units'].append(unit)
            if n%25==0 or args.sample:
                print('certified n='+str(n),file=sys.stderr,flush=True)
        totals={k:sum(u['counts'][k] for u in report['units']) for k in ('i','ii','iii')}
        report['totals']=totals
        report['branches']={k:sum(u['branches'][k] for u in report['units'])
                            for k in ('geometric','non_geometric')}
        if not args.sample:
            require(totals=={'i':496824,'ii':150495,'iii':1905},'full coverage count mismatch')
            require(report['branches']=={'geometric':1143,'non_geometric':762},'root branch counts')
        report['undecided']=0
        report['coincidences']=0
    # Only successful runs emit certificates. Partial output cannot be accepted.
    encoded=json.dumps(report,sort_keys=True,separators=(',',':'))+'\n'
    if args.check:
        compare_receipt(report, read_receipt(args.check), 'b2-full.json')
    Path(args.output).write_text(encoded)
    print(json.dumps({'scope':report['scope'],'totals':report.get('totals'),
                      'sha256':hashlib.sha256(encoded.encode()).hexdigest()}),flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--omega',required=True)
    parser.add_argument('--output',required=True)
    parser.add_argument('--controls-only',action='store_true')
    parser.add_argument('--sample',type=int,nargs='+')
    parser.add_argument('--check',help='replay and compare an existing certificate')
    args=parser.parse_args()
    try:
        run(args)
    except Exception as exc:
        print('HARD FAILURE: '+str(exc),file=sys.stderr)
        raise


if __name__=='__main__':
    main()
