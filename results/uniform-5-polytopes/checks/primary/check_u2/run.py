"""Run the stage-2 checker over every radius class.

usage: python3 run.py CLASSES_JSON OUT_SIGS_JSON [--jobs N] [--stats STATS_JSON]
                      [--progress FILE] [--only i,j,...]
"""
import argparse, json, os, resource, sys, time
from multiprocessing import get_context

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'check_u3'))
import model_runtime


def work(cls):
    t0 = time.process_time()
    try:
        found, stats, _ = search.run_class(cls)
        err = None
    except Exception as e:          # reported, never skipped silently
        found, stats, err = {}, getattr(e, 'search_stats', {}), '%s: %s' % (type(e).__name__, e)
    cpu = time.process_time() - t0
    vfs = [json.loads(s) for s in sorted(found)]
    info = {'index': cls['index'], 'cpu': cpu, 'stats': stats, 'error': err,
            'vf_info': [found[s] for s in sorted(found)]}
    return {'index': cls['index'], 'vfs': vfs}, info


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('classes')
    ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=1)
    ap.add_argument('--stats')
    ap.add_argument('--progress')
    ap.add_argument('--only')
    ap.add_argument('--prebuild', action='store_true', help='build exact templates once before fork')
    a = ap.parse_args()
    try:
        if os.environ.get('U2_LEGACY') != '1':
            model_runtime.ensure_guard()
        return execute(a)
    except model_runtime.GuardUndecided as e:
        result = dict(summary=dict(status='OPEN', model_guard_undecided=1,
                                   completed_classes=0, errors=1), error=str(e))
        with open(a.out, 'w') as f:
            json.dump([], f)
        if a.stats:
            with open(a.stats, 'w') as f:
                json.dump(result, f)
        print(json.dumps(result))
        return 1


def execute(a):
    classes = json.load(open(a.classes))
    if a.only:
        want = set(int(x) for x in a.only.split(','))
        classes = [c for c in classes if c['index'] in want]
    # largest classes first for load balance
    order = sorted(classes, key=lambda c: -len(c['cycles']))
    t0 = time.time()
    type_builds = []
    if a.prebuild:
        names = sorted({n for c in classes for cy in c['cycles'] for n in cy['facets']})
        for nm in names:
            tb = time.process_time()
            T = search.get_type(nm)
            type_builds.append(dict(name=nm, cpu_seconds=time.process_time()-tb,
                                   neighbours=T.nv, symmetries=len(T.syms)))
            print('template', nm, 'cpu', round(type_builds[-1]['cpu_seconds'], 3), flush=True)
    res, infos = {}, {}
    prog = open(a.progress, 'w') if a.progress else None
    pool = get_context("fork").Pool(a.jobs)
    if True:
        for k, (r, info) in enumerate(pool.imap_unordered(work, order)):
            res[r['index']] = r
            infos[r['index']] = info
            if prog:
                prog.write('%d/%d class %d cpu %.2fs vfs %d%s\n' % (
                    k + 1, len(order), r['index'], info['cpu'], len(r['vfs']),
                    (' ERROR ' + info['error']) if info['error'] else ''))
                prog.flush()
    pool.close()
    pool.join()
    out = [res[c['index']] for c in classes]
    with open(a.out, 'w') as f:
        json.dump(out, f, sort_keys=True)
        f.write('\n')
    errs = [i for i in infos.values() if i['error']]
    total_cpu = sum(i['cpu'] for i in infos.values())
    ru = [resource.getrusage(w) for w in (resource.RUSAGE_SELF, resource.RUSAGE_CHILDREN)]
    rusage_cpu = sum(r.ru_utime + r.ru_stime for r in ru)
    summary = {'classes': len(classes), 'completed_classes': len(classes)-len(errs),
               'model_guard_undecided': sum(i['error'].startswith('GuardUndecided:') for i in errs),
               'undecided_classes': len(errs), 'model': 'legacy-unproved' if os.environ.get('U2_LEGACY') == '1' else 'interval-exact-model', 'cpu_seconds_rusage': round(rusage_cpu, 1), 'total_vfs': sum(len(r['vfs']) for r in out),
               'errors': len(errs), 'cpu_seconds_total': round(total_cpu, 1),
               'wall_seconds': round(time.time() - t0, 1), 'jobs': a.jobs,
               'nonstrict_vfs': sum(1 for i in infos.values() for v in i['vf_info']
                                    if not v['strict'])}
    if a.stats:
        with open(a.stats, 'w') as f:
            json.dump({'summary': summary, 'type_builds': type_builds,
                       'model_guard': (model_runtime.record() if os.environ.get('U2_LEGACY') != '1' else None),
                       'per_class': [infos[c['index']] for c in classes]}, f, indent=0,
                      sort_keys=True)
    print(json.dumps(summary))
    for e in errs:
        print('ERROR class %d: %s' % (e['index'], e['error']))
    return 1 if errs else 0


if __name__ == '__main__':
    sys.exit(main())
