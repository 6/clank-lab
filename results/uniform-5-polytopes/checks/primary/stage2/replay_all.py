"""Full P6/P10/P16 U2 replay on regenerated, pinned producer class inputs.

Templates are cached once across all three runs. No node or time cap. Any
class error or signature difference is a nonzero exit; undecided is never
converted to exhaustion. Does not call producer Stage 2 or Stage 3.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import sys

def require_certified_completions(stats, signatures):
    """Check the reported per-figure certificates, not just process success.

    Search completeness may safely retain a figure with undecided strict
    convexity. Such a figure cannot be accepted as a certified completion.
    Match the accounting to the actual output and inspect every strict flag.
    """
    summary = stats['summary']
    expected = {row['index']: len(row['vfs']) for row in signatures}
    if len(expected) != len(signatures):
        raise ValueError('duplicate signature class')
    rows = stats['per_class']
    if len(rows) != len(expected) or {row['index'] for row in rows} != set(expected):
        raise ValueError('incomplete or duplicate class certificates')
    for key in ('errors', 'undecided_classes', 'model_guard_undecided', 'nonstrict_vfs'):
        if type(summary[key]) is not int or summary[key] != 0:
            raise ValueError('uncertified completion: ' + key)
    if summary['model'] != 'interval-exact-model' or stats['model_guard']['active'] is not True:
        raise ValueError('exact model guard required')
    if summary['classes'] != len(expected) or summary['completed_classes'] != len(expected):
        raise ValueError('class accounting differs')
    if summary['total_vfs'] != sum(expected.values()):
        raise ValueError('figure accounting differs')
    for row in rows:
        if row['error'] is not None or len(row['vf_info']) != expected[row['index']]:
            raise ValueError('missing or failed figure certificate')
        if any((info.get('strict') is not True for info in row['vf_info'])):
            raise ValueError('non-strict figure certificate')

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('inputs')
    ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=10)
    ap.add_argument('--pmax', nargs='+', type=int, choices=(6, 10, 16), default=[16, 10, 6])
    a = ap.parse_args()
    if not len(set(a.pmax)) == len(a.pmax):
        raise AssertionError()
    target = Path(__file__).resolve().parents[1]
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=False)
    sys.path.insert(0, str(target / 'check_u2'))
    spec = importlib.util.spec_from_file_location('u2_driver', target / 'check_u2/run.py')
    driver = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = driver
    spec.loader.exec_module(driver)
    pins = {line.split()[1]: line.split()[0] for line in (target / 'check_u1/current-inputs.sha256').read_text().splitlines()}
    reports = []
    for p in a.pmax:
        src = Path(a.inputs) / f'producer-p{p}' / f'u2_classes_p{p}.json'
        digest = hashlib.sha256(src.read_bytes()).hexdigest()
        if not digest == pins[f'producer-p{p}/u2_classes_p{p}.json']:
            raise AssertionError('producer input pin mismatch')
        ru_before = [resource.getrusage(w) for w in (resource.RUSAGE_SELF, resource.RUSAGE_CHILDREN)]
        sys.argv = ['run.py', str(src), str(out / f'sigs-p{p}.json'), '--jobs', str(a.jobs), '--prebuild', '--stats', str(out / f'stats-p{p}.json'), '--progress', str(out / f'progress-p{p}.txt')]
        status = driver.main()
        if status != 0:
            raise RuntimeError(f'P{p} undecided/error (exit {status})')
        actual = json.loads((out / f'sigs-p{p}.json').read_text())
        refpath = target / 'check_u3/inputs/u3_vfs_p6.json' if p == 6 else target / f'check_u2/sigs_p{p}.json'
        reference = json.loads(refpath.read_text())
        expected = [dict(index=c['index'], vfs=c['vfs']) for c in reference]

        def normalized(records):
            return {c['index']: sorted((json.dumps(v, sort_keys=True) for v in c['vfs'])) for c in records}
        if not len({c['index'] for c in actual}) == len(actual):
            raise AssertionError()
        if not all((len({json.dumps(v, sort_keys=True) for v in c['vfs']}) == len(c['vfs']) for c in actual)):
            raise AssertionError()
        if not normalized(actual) == normalized(expected):
            raise AssertionError(f'P{p} CLASSIFICATION DIFFERENCE: STOP')
        stats = json.loads((out / f'stats-p{p}.json').read_text())
        require_certified_completions(stats, actual)
        ru_after = [resource.getrusage(w) for w in (resource.RUSAGE_SELF, resource.RUSAGE_CHILDREN)]
        per_run_cpu = sum((r.ru_utime + r.ru_stime for r in ru_after)) - sum((r.ru_utime + r.ru_stime for r in ru_before))
        reports.append(dict(pmax=p, input_sha256=digest, signatures_sha256=hashlib.sha256((out / f'sigs-p{p}.json').read_bytes()).hexdigest(), summary=stats['summary'], per_run_cpu_seconds=per_run_cpu, summary_rusage_is_process_cumulative=True, nodes=sum((c['stats']['nodes'] for c in stats['per_class'])), placements=sum((c['stats']['placements'] for c in stats['per_class'])), differences=0))
        (out / 'summary.json').write_text(json.dumps(reports, sort_keys=True, indent=2) + '\n')
        print('P%d comparison: identical' % p, flush=True)
if __name__ == '__main__':
    main()
