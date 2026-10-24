#!/usr/bin/env python3
"""Finite exact controls for the pseudo-Anosov-base extension, using the Dynnikov model.

Exit 0: all specified controls pass; exit 1: mathematical rejection;
exit 2: unsupported input / execution error. No universal or topological claim.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
MODEL = ROOT / 'check_dynnikov.py'
spec = importlib.util.spec_from_file_location('independent_dynnikov_b', MODEL)
B = importlib.util.module_from_spec(spec)
spec.loader.exec_module(B)

# Exact original payloads are recognized controls, NOT a free-group interpreter.
# Their geometric realizations are B.curves_for(K), as in the original Dynnikov model.
ORIGINALS = {
    'K1': {'C': [1, 2, -1, 3, 4]},
    'K2': {'Cp': [1, 2, 3, 4, 3, -4, -3]},
    'K3': {'C': [1, 2, 3], 'Cp': [2, 3, 4]},
    'K4': {'c': [-3, -2, -1, 3, 1, 2, 3, 4]},
}
MUTATIONS = {'c-exponent-k', 'a-exponent-plus', 'd-exponent-minus',
             'leftmost-first-g', 'leftmost-first-product', 'd-exponent-zero'}

class FrozenFailure(Exception):
    pass


def load_control(path):
    if path is None:
        return None, None
    payload = json.loads(Path(path).read_text())
    for label, original in ORIGINALS.items():
        if payload == original:
            return label, None
    if (isinstance(payload, dict) and set(payload) == {'mutation'}
            and isinstance(payload['mutation'], str)
            and payload['mutation'] in MUTATIONS):
        return None, payload['mutation']
    raise ValueError('unsupported control: only the four exact original payloads or named mutations')


def run(kmax, corruption, mutation):
    if not 1 <= kmax <= 30:
        raise ValueError('kmax must lie in 1..30 (finite CPU controls only)')
    report = {
        'checker': 'extension-Dynnikov-only',
        'model': '../check_dynnikov.py', 'k_values': list(range(1, kmax + 1)),
        'signs': [1, -1], 'corruption': corruption, 'mutation': mutation,
        'composition': 'rightmost first; model words act left to right',
        'scope': 'finite integer-coordinate action checks only; no all-k/all-n theorem, filling certificate, or pseudo-Anosov conclusion',
        'checks_by_group': {}, 'failures_by_group': {}, 'failures': [],
        'cases': [],
    }
    negative = corruption is not None or mutation is not None

    def check(group, expected, actual, context):
        counts = report['checks_by_group']
        counts[group] = counts.get(group, 0) + 1
        if actual != expected:
            counts = report['failures_by_group']
            counts[group] = counts.get(group, 0) + 1
            report['failures'].append(dict(group=group, expected=expected,
                                           actual=actual, **context))
            if not negative:
                raise FrozenFailure()

    try:
        # Validate only the independent model, not its old endpoint check_facts.
        tally = B.Tally(False)
        B.validate(tally, B.Rng(0x1A2B3C4D5E6F))
        check('model_validation_failures', 0, tally.failures,
              {'validation_checks': tally.checks})
        report['model_validation_checks'] = tally.checks
        cs = B.curves_for(corruption)
        report['curve_coordinates'] = {x: list(cs[x].coords) for x in B.PENTAGON}
        probes = [cs[x].coords for x in B.PENTAGON]
        probes += [(1, -2, 3, -4), (-2, 1, -3, 2), (2, 3, -1, -2), (-1, -1, 2, 3)]
        report['cancellation_probes'] = [list(v) for v in probes]
        for k in range(1, kmax + 1):
            for sign in (1, -1):
                # Reverse EVERY map twist globally, without changing curve labels.
                Ta, Tc, Td = [B.power(cs[x].twist(), sign) for x in ('a', 'c', 'd')]
                ae = 1 if mutation == 'a-exponent-plus' else -1
                ce = -k if mutation == 'c-exponent-k' else -(k + 1)
                de = (0 if mutation == 'd-exponent-zero' else
                      -1 if mutation == 'd-exponent-minus' else 1)
                factors = [B.power(Ta, ae), B.power(Tc, ce), B.power(Td, de)]
                g = sum(factors, []) if mutation == 'leftmost-first-g' else B.compose(*factors)
                t = B.compose(Ta, Tc)
                ns = sorted(set(range(-3, 4)) | {k, k + 1, k + 2})
                context = {'k': k, 'sign': sign}
                case = dict(context, n_values=ns, fixed_curve_actions=[], cancellations=[], intersections={})
                report['cases'].append(case)
                # These remain the ORIGINAL expected forms under every mutation.
                for n in ns:
                    tn = B.power(t, n)
                    literal = tn + g if mutation == 'leftmost-first-product' else B.compose(tn, g)
                    rhs = B.compose(B.power(Ta, n - 1), B.power(Tc, n - k - 1), Td)
                    actions = {x: list(B.act(literal, cs[x].coords)) for x in ('C', "C'")}
                    case['fixed_curve_actions'].append({'n': n, 'images': actions,
                        'fixed': {x: actions[x] == list(cs[x].coords) for x in actions}})
                    if n == 1:
                        check('fix_C_at_1', list(cs['C'].coords), actions['C'], dict(context, n=n))
                    if n == k + 1:
                        check('fix_Cprime_at_kplus1', list(cs["C'"].coords), actions["C'"], dict(context, n=n))
                    mismatch = []
                    for index, probe in enumerate(probes):
                        left, right = B.act(literal, probe), B.act(rhs, probe)
                        check('cancellation_action', list(right), list(left),
                              dict(context, n=n, probe_index=index, probe=list(probe)))
                        if left != right:
                            mismatch.append(index)
                    case['cancellations'].append({'n': n, 'mismatched_probe_indices': mismatch})
                ga = B.act(g, cs['a'].coords)
                case['g_a'] = list(ga)
                for x in ('a', 'c'):
                    value = cs[x].i_with(ga)
                    case['intersections'][x] = value
                    check('intersection_exact_4', 4, value, dict(context, curve=x, g_a=list(ga)))
                    moved = B.act(cs[x].twist(), ga) != ga
                    check('twist_moves_g_a', True, moved, dict(context, curve=x))
                # Exact original incidence data detect changes to the curve inputs.
                for x, y, value in [('a', 'c', 0), ('a', 'd', 2), ('c', 'd', 2),
                                    ('C', 'c', 0), ('C', 'd', 0), ("C'", 'a', 0), ("C'", 'd', 0)]:
                    check('curve_incidence', value, cs[x].i_with(cs[y].coords),
                          dict(context, curves=[x, y]))
    except FrozenFailure:
        report['stopped_at_first_frozen_failure'] = True
    report['failure_count'] = sum(report['failures_by_group'].values())
    report['verdict'] = 'REJECT' if report['failure_count'] else 'ACCEPT'
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--kmax', type=int, default=8)
    ap.add_argument('--input', type=Path)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    try:
        report = run(args.kmax, *load_control(args.input))
    except (ValueError, OSError, json.JSONDecodeError) as e:
        print(str(e), file=sys.stderr)
        return 2
    output = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    print(json.dumps({key: report[key] for key in ('verdict', 'k_values', 'signs',
          'corruption', 'mutation', 'checks_by_group', 'failures_by_group', 'failure_count')}))
    return 0 if report['verdict'] == 'ACCEPT' else 1

if __name__ == '__main__':
    sys.exit(main())
