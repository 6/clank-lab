"""Validate a W certificate against an explicit full/supplementary/sample inventory.

Require complete unique rows, exact domains, all V/P/F obligations and no
pending boxes. Seven point restrictions additionally require the partner
filter's singleton equality, recomputed from its inputs. D is auxiliary.
"""
import argparse
import ast
import json
import sys

import fans
import inventory
import partner


def validate_domains(rows):
    # Refuse a real-m overclaim even when numerical verdicts are unchanged.
    for r in rows:
        name = r["fan"]
        domain = r.get("parameter_domain")
        if name.startswith("(i)"):
            config = ast.literal_eval(name[3:].split("@")[0])
            if config[0] >= 17 and config[1:] in fans.BOUNDED_LIMITS:
                fans.integer_config(config)
                expected_m = {"kind": "integer_slice", "value": config[0], "min": 17,
                              "max": fans.BOUNDED_LIMITS[config[1:]]}
                if domain is None or domain.get("m") != expected_m:
                    raise ValueError(f"{name}: bounded m must be an explicit integer slice")
                if "@n=" in name:
                    n = int(name.split("@n=")[1])
                    if n != config[0] or domain.get("n") != {"kind": "integer_point", "value": n}:
                        raise ValueError(f"{name}: exceptional domain must be the integer point n=m")
                elif domain.get("n") != {"kind": "real", "min": 17, "includes_infinity": True}:
                    raise ValueError(f"{name}: full n domain must be continuous >=17 including infinity")


def validate_records(rows, scope, expect_fail=None):
    expected, failures = inventory.profile(scope)
    names = [r['fan'] for r in rows]
    if len(set(names)) != len(names):
        raise ValueError('duplicate fan record')
    if set(names) != set(expected):
        raise ValueError(f'inventory mismatch: missing={sorted(set(expected)-set(names))}; '
                         f'unexpected={sorted(set(names)-set(expected))}')
    if expect_fail is not None and (len(expect_fail) != len(set(expect_fail)) or set(expect_fail) != failures):
        raise ValueError('expected failures differ from explicit inventory')
    validate_domains(rows)
    by = {r['fan']: r for r in rows}
    for name, row in by.items():
        domain, kind, tests, pairs = expected[name]
        if scope == 'supplementary':
            kind = 'excluded-by-P1'
        if json.dumps(row.get('parameter_domain'), sort_keys=True, allow_nan=False) != \
                json.dumps(domain, sort_keys=True) or row.get('kind') != kind:
            raise ValueError(name + ': wrong domain or fan kind')
        if set(row.get('tests', {})) != tests or set(row.get('vertex_pairs', {})) != set(pairs):
            raise ValueError(name + ': missing or unexpected V/P/D/F test')
        for label, test in row['tests'].items():
            if type(test.get('ok')) is not bool:
                raise ValueError(name + '/' + label + ': boolean test flag required')
            for counter in ('pending', 'unresolved'):
                if type(test.get(counter)) is not int or test[counter] != 0:
                    raise ValueError(name + '/' + label + ': pending or unresolved boxes')
        for label, diagonal in pairs.items():
            test = row['vertex_pairs'][label]
            if type(test.get('ok')) is not bool or type(test.get('diagonal')) is not bool or test['diagonal'] != diagonal:
                raise ValueError(name + '/' + label + ': invalid F flag')
        vok = all(row['tests'][t]['ok'] for t in tests if t.startswith('V:'))
        pok = all(row['tests'][t]['ok'] for t in tests if t.startswith('P:'))
        fok = all(row['vertex_pairs'][t]['ok'] for t, diagonal in pairs.items() if not diagonal)
        if any(type(row.get(k)) is not bool or row[k] != v for k, v in [('V_ok', vok), ('P_ok', pok), ('F_ok', fok)]):
            raise ValueError(name + ': aggregate flags disagree with test content')
        verdict = 'CERTIFIED' if vok and pok and fok else 'FAILED'
        if row.get('verdict') != verdict or verdict != ('FAILED' if name in failures else 'CERTIFIED'):
            raise ValueError(name + ': verdict differs from required tests or inventory')
        direction = 'CERTIFIED' if row['tests']['D:+']['ok'] else 'not sufficient'
        if row.get('direction_test') != direction:
            raise ValueError(name + ': direction flag disagrees with test')
    for name in failures:
        if expected[name][1] != 'paired':
            continue
        c = inventory.config(name)
        if c not in inventory.EXCEPTIONS:
            raise ValueError(name + ': unsupported paired exception')
        # The receipt must itself say exactly the matching singleton. Also
        # recompute the radius-filter exclusion from its authoritative inputs;
        # a fabricated singleton in a certificate cannot authorize restriction.
        receipt = by[name].get('partner_filter', {})
        singleton = [[str(c[1:]), str(c[0])]]
        if receipt.get('allowed') != singleton:
            raise ValueError(name + ': partner filter must allow only matching n=m')
        _, allowed = partner.allowed(c[0], c[1:])
        if allowed != [(c[1:], c[0])]:
            raise ValueError(name + ': recomputed partner filter is not singleton n=m')
    return failures


def main(path, expect_fail=None, *, inventory=None):
    if inventory is None:
        raise ValueError('explicit acceptance inventory required')
    with open(path) as f:
        rows = [json.loads(l) for l in f if l.strip()]
    expect_fail = sorted(validate_records(rows, inventory, expect_fail))
    by = {r["fan"]: r for r in rows}
    validate_domains(rows)
    print("Domain: continuous n>=17 (including infinity); bounded-family m is integer only "
          "(3,7):17..41, (3,8):17..23, (3,9):17, (4,5):17..19; exceptions n=m are integer points.")
    cpu = sum(r["cpu"] for r in rows)
    boxes = sum(r["boxes"] for r in rows)
    ok_all = True
    failed = []
    print(f"{'fan':26s} {'verdict':10s} {'V':3s} {'P':3s} {'F':3s} {'D':4s} {'boxes':>11s} {'cpu s':>8s}  note")
    for r in rows:
        note = ""
        if r["verdict"] == "FAILED":
            w = None
            for k, t in r["tests"].items():
                if not t["ok"] and "witness" in t and t["witness"] and not k.startswith("D"):
                    w = (k, t["witness"])
                    break
            if w is None and r.get("pair_witness"):
                w = ("pair", r["pair_witness"])
            if w:
                k, wt = w
                if "params" in wt:
                    note = f"{k}: rigorous={wt.get('rigorous')} params={[round(x, 6) for x in wt['params']]} p.p'<={wt.get('p.p\'_upper', wt.get('p.p\'_float')):.6f}"
                else:
                    note = f"{k}: rigorous={wt.get('rigorous')} at {[round(x, 6) for x in wt['params+chart']]} obj<={wt['objective_upper']:.6f}"
            if "partner_filter" in r:
                note += f"; partner filter allows {r['partner_filter']['allowed']}"
            if "@n=" not in r["fan"]:
                failed.append(r["fan"])
        D = "yes" if r.get("direction_test") == "CERTIFIED" else "no"
        yn = lambda b: "ok" if b else "NO"
        print(f"{r['fan']:26s} {r['verdict']:10s} {yn(r['V_ok']):3s} {yn(r['P_ok']):3s} {yn(r['F_ok']):3s} {D:4s} "
              f"{r['boxes']:>11d} {r['cpu']:8.2f}  {note}")
    # acceptance: each failed fan has a CERTIFIED restricted run
    for f in failed:
        if by[f].get("kind") != "paired":
            # unpaired fans may fail only where expected (the supplementary
            # run of the configurations excluded by (P1))
            if expect_fail is None or f not in expect_fail:
                ok_all = False
                print(f"NOT ACCEPTED: unpaired fan {f} failed")
            continue
        rest = [k for k in by if k.startswith(f + "@n=")]
        if not rest or any(by[k]["verdict"] != "CERTIFIED" for k in rest):
            ok_all = False
            print(f"NOT ACCEPTED: {f} failed and has no certified restricted run")
    for r in rows:
        if "@n=" in r["fan"] and r["verdict"] != "CERTIFIED":
            ok_all = False
    diag = sorted({(r["fan"], k) for r in rows for k, v in r["vertex_pairs"].items() if v["diagonal"] and not v["ok"]})
    print(f"fans: {len([r for r in rows if '@n=' not in r['fan']])} (+{len(rows) - len([r for r in rows if '@n=' not in r['fan']])} restricted runs);"
          f" CERTIFIED over the full range: {len([r for r in rows if '@n=' not in r['fan'] and r['verdict'] == 'CERTIFIED'])};"
          f" FAILED: {failed}")
    print(f"long type-(i) diagonals (not needed, excluded combinatorially): {diag if diag else 'none'}")
    print(f"total boxes {boxes}, total CPU {cpu:.1f} s")
    if expect_fail is not None:
        ok_all &= sorted(failed) == sorted(expect_fail)
    print("ACCEPTED" if ok_all else "NOT ACCEPTED")
    return 0 if ok_all else 1


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument('path')
    ap.add_argument('failures', nargs='?')
    ap.add_argument('--inventory', required=True, choices=('full', 'supplementary', 'quick', 'controls'))
    args = ap.parse_args()
    exp = None if args.failures is None else [x for x in args.failures.split(';') if x]
    try:
        sys.exit(main(args.path, exp, inventory=args.inventory))
    except (ValueError, KeyError, TypeError) as error:
        print('NOT ACCEPTED:', error)
        sys.exit(1)
