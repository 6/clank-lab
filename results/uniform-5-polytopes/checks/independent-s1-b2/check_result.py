"""Explicit comparison with the paper's B2 claims and the cutoff boundary."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from flint import arb, fmpq, ctx
from receipt_policy import compare_receipt, read_receipt

HERE=Path(__file__).resolve().parent


def bounds(x):
    if not x.is_finite():
        raise ValueError('nonfinite cutoff')
    return [str(x.lower().fmpq()),str(x.upper().fmpq())]


def result():
    ctx.prec=320
    omega_raw=(HERE/'evidence/omega.json').read_bytes()
    omega=json.loads(omega_raw)['intervals']
    report=json.loads((HERE/'evidence/b2-full.json').read_text())
    expected={'i':496824,'ii':150495,'iii':1905}
    if report['scope']!='full B2' or report['totals']!=expected:
        raise ValueError('B2 scope/count disagreement with paper')
    if (report['coincidences'],report['undecided'],report['cutoff']['n'])!=(0,0,398):
        raise ValueError('B2 exclusion/cutoff disagreement with paper')
    if [unit['n'] for unit in report['units']]!=list(range(17,398)):
        raise ValueError('B2 finite range incomplete')
    if report['omega_sha256']!=hashlib.sha256(omega_raw).hexdigest():
        raise ValueError('B2 did not use the independent Omega')
    maxlo=max(Fraction(row[0]) for row in omega)
    maxhi=max(Fraction(row[1]) for row in omega)
    r397=bounds(1/(2*arb.sin_pi_fmpq(fmpq(1,397))))
    r398=bounds(1/(2*arb.sin_pi_fmpq(fmpq(1,398))))
    if not Fraction(r397[1])<maxlo<=maxhi<Fraction(r398[0]):
        raise ValueError('398 is not the certified first polygon-radius cutoff')
    return {'status':'CERTIFIED','reference':'paper/main.tex, Computation B2',
            'paper_counts':expected,'independent_counts':report['totals'],
            'total_radii':sum(expected.values()),'coincidences':0,'undecided':0,
            'omega_intervals':len(omega),'omega_sha256':report['omega_sha256'],
            'cutoff':{'last_finite_n':397,'first_tail_n':398,
                      'r397':r397,'r398':r398,'omega_max':[str(maxlo),str(maxhi)],
                      'strict_boundary_inequalities':True},
            'positive_controls':report['positive_controls'],
            'semantic_checks':len(report['semantic_tests']),'disagreements':0}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--write',action='store_true')
    args=ap.parse_args()
    actual=result()
    path=HERE/'evidence/b2-comparison.json'
    if args.write:
        path.write_text(json.dumps(actual,sort_keys=True,indent=2)+'\n')
    else:
        compare_receipt(actual, read_receipt(path), 'b2-comparison.json')
    print(json.dumps({'status':actual['status'],'total_radii':actual['total_radii'],
                      'cutoff':398,'disagreements':0},sort_keys=True))

if __name__=='__main__':main()
