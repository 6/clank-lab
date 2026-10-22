#!/usr/bin/env python3
"""Corruption tests for check_certificate.py: every corrupted certificate must be rejected.
Usage: python3 -I corruptions.py CERT.json.gz DATA.lean   (imports only the sibling checker)"""
import sys, os, gzip, json, copy, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_certificate as C

cert = json.load(gzip.open(sys.argv[1], 'rt'))
data = C.parse_data_lean(sys.argv[2])
C.parse_lean_height.cache = C.parse_lean_height(sys.argv[2].replace('Data.lean', 'Candidate.lean'))
rows = C.row_list()
ops = C.build_operators(data['pairCap'], log=lambda *a: None)
quiet = lambda *a: None

def run(name, mut):
    c = copy.deepcopy(cert); mut(c)
    t = time.time()
    try:
        bad, _ = C.check(c, data, ops, rows, log=quiet)
    except Exception as e:      # a crash is also a rejection
        bad = ['exception: %r' % (e,)]
    print('%-34s %s  (%d failure(s): %s)  %.1fs' % (name, 'REJECTED' if bad else 'ACCEPTED (!!)', len(bad), '; '.join(bad)[:110], time.time() - t))
    return bool(bad)

def f_entry(c):
    b = c['blocks'][9]; b['F_numerators'][5][7] = str(int(b['F_numerators'][5][7]) + 1)
def f_entry_moment(c):
    b = c['blocks'][0]; b['F_numerators'][0][0] = str(int(b['F_numerators'][0][0]) + 1)
def h_coeff(c): c['h_numerators'][5] = str(int(c['h_numerators'][5]) + 1)
def u_val(c):
    n, d = c['U'].split('/'); c['U'] = '%d/%s' % (int(n) + 1, d)
def swap_rows(c):
    r = c['row_exponents']; r[10], r[11] = r[11], r[10]
def swap_rows_and_residual(c):      # consistent relabelling of rows in the JSON: still must be rejected (rows are re-derived)
    r = c['row_exponents']; r[10], r[11] = r[11], r[10]
    s = c['residual']; s[10], s[11] = s[11], s[10]
def residual_entry(c):
    c['residual'][3] = '0/1'
def L_val(c): c['L'] = '0/1'
tests = [('F entry +1 (SOS block)', f_entry), ('F entry +1 (moment block)', f_entry_moment), ('h coefficient +1', h_coeff),
         ('U +1/2^200', u_val), ('swap two rows exponents', swap_rows), ('swap rows exps+residual', swap_rows_and_residual),
         ('residual entry zeroed', residual_entry), ('L zeroed', L_val)]
allrej = all([run(n, m) for n, m in tests])
print('ALL REJECTED' if allrej else 'SOME ACCEPTED'); sys.exit(0 if allrej else 1)
