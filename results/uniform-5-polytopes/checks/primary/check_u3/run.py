"""Independent stage-3 checker: driver.

usage: python run.py VFS.json KNOWN.json OUT.json [--jobs N] [--classes i,j,...]
       [--perturb-radius EPS] [--mirror CLASS:VF:FACETTYPE]

Per class and vertex-figure signature: every realisation (search.py), its
unique exact radius (closure.py), local uniqueness (locuniq.py),
identification with a listed known polytope (identify.py), and for every
realisation not both identified and forced, a development (develop.py).
"""
import sys
import json
import time
import argparse
import multiprocessing as mp_
from collections import Counter
import ivla
from ivla import I
from mpmath import iv
import search
import canon
import closure
import locuniq
import identify
import develop
import geom
import ktypes
import templates
from templates import template
import model_runtime
KNOWN = {}

def class_job(args):
    c, known_in, opts = args
    t0 = time.process_time()
    R = I(c['R'])
    R2 = R * R
    out = {'index': c['index'], 'R': c['R'], 'vfs': []}
    reals = []
    for k, vf in enumerate(c['vfs']):
        sig = search.Signature(vf)
        try:
            states, stats = search.realise(R2, sig)
        except search.Undecided as e:
            out['vfs'].append({'facets': vf['facets'], 'error': 'undecided: %s' % e, 'search': {'undecided': 1, 'undecided:escaped:' + str(e): 1}})
            continue
        if stats['undecided']:
            out['vfs'].append({'facets': vf['facets'], 'error': 'undecided realisation search', 'search': dict(stats)})
            continue
        if opts.get('mirror') and opts['mirror'][0] == c['index'] and (opts['mirror'][1] == k):
            states = [(mirror_one_facet(s, opts['mirror'][2], R2, sig), w) for s, w in states]
            states = [(s, w) for s, w in states if s is not None]
        groups = {}
        for s, weak in states:
            groups.setdefault(canon.canonical(s), []).append((s, weak))
        rl = []
        for key in sorted(groups):
            s, weak = groups[key][0]
            rec = {'search_states': len(groups[key]), 'weak_convexity': weak, 'facets': len(s.facets), 'vf_points': len(s.pts) - 1}
            ok, info = closure.certify(s, R)
            rec['unique_root'] = ok
            rec['root'] = info
            lu = locuniq.check(s)
            rec['local_uniqueness'] = {k2: lu[k2] for k2 in ('neighbours', 'unique', 'valid_g', 'tested_g', 'forced')}
            rec['local_uniqueness']['failures'] = lu['failures'][:5]
            rec['local_uniqueness']['no_valid'] = lu['no_valid'][:5]
            rec['_state'] = s
            rl.append(rec)
            reals.append((k, len(rl) - 1, s))
        out['vfs'].append({'facets': sorted(vf['facets']), 'n_cycles': len(vf['cycles']), 'search': {kk: v for kk, v in stats.items()}, 'realisations': rl})
    if any(('error' in v for v in out['vfs'])):
        for v in out['vfs']:
            for rec in v.get('realisations', []):
                del rec['_state']
                rec['known_names'] = []
                rec['embedding'] = {}
                rec['verdict'] = 'OPEN'
        out['status'] = 'OPEN'
        out['known_in_class'] = sorted(known_in)
        out['known_unmatched'] = sorted(known_in)
        out['cpu_seconds'] = round(time.process_time() - t0, 2)
        return out
    embeds = {}
    spts = {}
    for k, r, s in reals:
        spts[k, r] = identify.star_points(s)
    out['known_in_class'] = sorted(known_in)
    for name in sorted(known_in):
        Q = KNOWN[name]
        for k, r, s in reals:
            res = identify.embed(s, Q, spts[k, r])
            embeds[name, k, r] = res
    for k, r, s in reals:
        rec = out['vfs'][k]['realisations'][r]
        names = []
        ev = {}
        for name in sorted(known_in):
            res = embeds[name, k, r]
            ev[name] = [res[0], res[1] if not isinstance(res[1], float) else float('%.3g' % res[1])]
            if res[0] != 'MATCH':
                continue
            others = [embeds[name, k2, r2][0] for k2, r2, _ in reals if (k2, r2) != (k, r)]
            if all((o in ('NO', 'NO-COUNT') for o in others)):
                names.append(name)
        rec['embedding'] = ev
        rec['known_names'] = names
        identified = bool(names) and rec['unique_root']
        forced = rec['local_uniqueness']['forced']
        if identified and forced:
            rec['verdict'] = 'KNOWN'
        else:
            log = []
            try:
                st = develop.develop(s, R2, max_vertices=opts.get('dev_max_vertices', 3000), max_branches=opts.get('dev_max_branches', 2000), log=log)
            except model_runtime.GuardUndecided:
                raise
            except Exception as e:
                st = {'error': repr(e), 'refuted': False}
            rec['development'] = st
            rec['development_log'] = log[:20]
            if st.get('refuted'):
                rec['verdict'] = 'REFUTED'
            else:
                rec['verdict'] = 'OPEN'
        del rec['_state']
    out['known_unmatched'] = [n for n in sorted(known_in) if not any((n in rec['known_names'] for v in out['vfs'] for rec in v.get('realisations', [])))]
    out['cpu_seconds'] = round(time.process_time() - t0, 2)
    return out

def mirror_one_facet(s, ftype, R2, sig):
    """corruption (b): replace the first facet of type `ftype` by its mirror
    image: compose its template map with an isometry M of the template's
    R^4 that fixes the base vertex and permutes its neighbours (so the
    vertex-figure points are unchanged) but is not a symmetry of the facet
    (it exists when the facet is chiral, e.g. pr-snic)."""
    import numpy as np
    import templates as tm
    from ivla import matmul
    fidx = next((i for i, F in enumerate(s.facets) if F.type == ftype))
    F = s.facets[fidx]
    T = F.T
    Vn = T.Vf[[0] + T.nb]
    look = tm.Lookup(Vn)
    cand = tm.isometries_vertexset(Vn, look, 0, 0, list(range(1, len(Vn))), list(range(1, len(Vn))))
    stabset = {tuple((int(p[j]) for j in T.nb)) for p in T.stab_perm}
    pick = None
    for S, perm in cand:
        img = tuple((T.nb[int(perm[k + 1]) - 1] for k in range(len(T.nb))))
        if img not in stabset:
            pick = (S, perm)
            break
    if pick is None:
        raise SystemExit('facet type %s is not chiral: no mirror corruption' % ftype)
    S, perm = pick
    tr = (0,) + tuple(T.nb[:3])
    A = [[T.V[t][r] for t in tr] for r in range(4)]
    B = [[T.V[0][r]] + [T.V[T.nb[int(perm[k + 1]) - 1]][r] for k in range(3)] for r in range(4)]
    from ivla import inverse
    M = matmul(B, inverse(A))
    G = search.Facet(F.type, T, matmul(F.L, M), F.c, {})
    G.m = {T.nb[k]: F.m[T.nb[int(perm[k + 1]) - 1]] for k in range(len(T.nb))}
    s2 = s.copy()
    s2.facets = list(s.facets)
    s2.facets[fidx] = G
    return s2

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('vfs')
    ap.add_argument('known')
    ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--classes', default='')
    ap.add_argument('--perturb-radius', default='')
    ap.add_argument('--mirror', default='')
    a = ap.parse_args()
    try:
        model_runtime.ensure_guard()
        return execute(a)
    except model_runtime.GuardUndecided as e:
        result = dict(status='OPEN', error=str(e), classes=[], known={}, summary=dict(model_guard_undecided=1))
        with open(a.out, 'w') as stream:
            json.dump(result, stream, indent=1)
        print(json.dumps(result))
        return 1

def execute(a):
    t0 = time.time()
    cpu0 = time.process_time()
    with open(a.vfs) as stream:
        data = json.load(stream)
    with open(a.known) as stream:
        known = json.load(stream)
    if a.perturb_radius:
        from mpmath import mp
        eps = mp.mpf(a.perturb_radius)
        for c in data:
            lo_, hi_ = (mp.mpf(x) for x in c['R'])
            c['R'] = [mp.nstr(lo_ + eps, 50), mp.nstr(hi_ + eps, 50)]
    library = {f for c in data for vf in c['vfs'] for f in vf['facets']}
    if a.classes:
        want = set((int(x) for x in a.classes.split(',')))
        data = [c for c in data if c['index'] in want]
    opts = {}
    if a.perturb_radius:
        opts['perturb'] = a.perturb_radius
    if a.mirror:
        ci, vi, ft = a.mirror.split(':')
        opts['mirror'] = (int(ci), int(vi), ft)
    names = sorted({f for c in data for vf in c['vfs'] for f in vf['facets']})
    for n in names:
        template(n)
    tt = time.time()
    print('templates: %d in %.1fs' % (len(names), tt - t0), flush=True)
    Rint = {c['index']: I(c['R']) for c in data}
    known_cls = {c['index']: [] for c in data}
    kinfo = {}
    for n in known:
        QR = iv.sqrt(geom.circumradius2_5(n))
        inside = [ci for ci, R in Rint.items() if R.a <= QR.a and QR.b <= R.b]
        touch = [ci for ci, R in Rint.items() if not (R.b < QR.a or QR.b < R.a)]
        if a.classes and (not touch):
            kinfo[n] = {'R': str(QR.mid)[:30], 'classes': [], 'overlapping': []}
            continue
        K = n[6:] if n.startswith('prism-') else None
        types = ktypes.facet_types(n, template if K is None or K in library else None)
        kinfo[n] = {'R': str(QR.mid)[:30], 'facet_types': sorted(types)}
        if not types <= library:
            kinfo[n]['outside_library'] = sorted(types - library)
            kinfo[n]['classes_by_radius'] = inside
            continue
        if touch:
            Q = identify.Known(n)
            KNOWN[n] = Q
            if not not (Q.R.b < QR.a or QR.b < Q.R.a):
                raise AssertionError()
            kinfo[n]['neighbours'] = {'upper': len(Q.nb), 'exact_from_construction': Q.n_lower, 'exact': Q.n_exact}
        kinfo[n].update({'classes': inside, 'overlapping': touch})
        for ci in inside:
            known_cls[ci].append(n)
    print('known polytopes: %d in %.1fs' % (len(known), time.time() - tt), flush=True)
    jobs = [(c, known_cls[c['index']], opts) for c in data]
    jobs.sort(key=lambda j: -sum((len(vf['facets']) for vf in j[0]['vfs'])))
    results = []
    if a.jobs > 1:
        ctx = mp_.get_context('fork')
        with ctx.Pool(a.jobs) as pool:
            for r in pool.imap_unordered(class_job, jobs):
                results.append(r)
                print('class %d: %s (%.1fs)' % (r['index'], [rec['verdict'] for v in r['vfs'] for rec in v.get('realisations', [])], r['cpu_seconds']), flush=True)
    else:
        for j in jobs:
            r = class_job(j)
            results.append(r)
            print('class %d: %s (%.1fs)' % (r['index'], [rec['verdict'] for v in r['vfs'] for rec in v.get('realisations', [])], r['cpu_seconds']), flush=True)
    results.sort(key=lambda r: r['index'])
    summ = summary(results, kinfo)
    mism = []
    for r in results:
        for v in r['vfs']:
            for rec in v.get('realisations', []):
                for nm in rec['known_names']:
                    if set(kinfo[nm]['facet_types']) != set(v['facets']):
                        mism.append((r['index'], nm))
    summ['facet_type_mismatches'] = mism
    summ['template_certificates'] = dict(templates.GAPS)
    summ['templates_certified'] = templates.GAPS['templates']
    summ['model_guard_undecided'] = 0
    summ['wall_seconds'] = round(time.time() - t0, 1)
    summ['cpu_seconds_main'] = round(time.process_time() - cpu0, 1)
    summ['cpu_seconds_classes'] = round(sum((r['cpu_seconds'] for r in results)), 1)
    with open(a.out, 'w') as stream:
        json.dump({'summary': summ, 'known': kinfo, 'classes': results, 'model_guard': model_runtime.record()}, stream, indent=1, default=str)
    print(json.dumps(summ, indent=1))
    return result_exit_code(summ, results)

def result_exit_code(summ, results):
    """Keep diagnostic output, but never signal success for OPEN/errors.

    Empty realisation lists are certified exclusions, not errors. A
    --classes run may leave known names outside the selected classes.
    Neither diagnostic is a reason to reject a completed scoped run.
    """
    for key, value in summ.items():
        if value and (key == 'verdict_OPEN' or 'error' in key.lower() or 'undecided' in key.lower() or (key in ('known_unmatched', 'facet_type_mismatches'))):
            return 1
    for result in results:
        if result.get('status') == 'OPEN' or result.get('error'):
            return 1
        for vf in result['vfs']:
            if 'error' in vf:
                return 1
            for rec in vf.get('realisations', []):
                if rec.get('verdict') == 'OPEN' or rec.get('error') or rec.get('development', {}).get('error'):
                    return 1
    return 0

def summary(results, kinfo):
    c = Counter()
    c['search_undecided'] = 0
    c['development_undecided'] = 0
    distinct = set()
    for r in results:
        c['classes'] += 1
        for v in r['vfs']:
            c['vertex_figures'] += 1
            c['search_undecided'] += v.get('search', {}).get('undecided', 0)
            if 'error' in v:
                c['vf_errors'] += 1
                continue
            if not v['realisations']:
                c['vf_without_realisation'] += 1
            for rec in v['realisations']:
                c['development_undecided'] += rec.get('development', {}).get('undecided', 0)
                c['realisations'] += 1
                c['search_states'] += rec['search_states']
                c['verdict_' + rec['verdict']] += 1
                c['unique_root'] += rec['unique_root']
                c['forced'] += rec['local_uniqueness']['forced']
                if rec['verdict'] == 'KNOWN':
                    distinct.add((r['index'], tuple(rec['known_names'])))
        c['known_unmatched'] += len(r['known_unmatched'])
    out = dict(c)
    out['distinct_known_polytopes'] = len(distinct)
    out['known_names_matched'] = sum((len(n) for _, n in distinct))
    out['known_names_in_no_class'] = sorted((n for n, k in kinfo.items() if not k.get('classes') and 'outside_library' not in k))
    out['known_outside_library'] = sorted((n for n, k in kinfo.items() if 'outside_library' in k))
    nc = Counter()
    for r in results:
        for v in r['vfs']:
            for rec in v.get('realisations', []):
                for nm, ev in rec.get('embedding', {}).items():
                    nc['embed_' + ev[0]] += 1
    out.update(nc)
    out['known_without_exact_count'] = sorted((n for n, k in kinfo.items() if 'neighbours' in k and k['neighbours']['exact'] is None))
    return out
if __name__ == '__main__':
    sys.exit(main())
