"""(W) for the seven paired fans that FAIL over all n (RESULT.md): (m,3,7) m = 38..41, (23,3,8),
(17,3,9), (19,4,5).  Step 1, partner radius filter (ball arithmetic): the partner m-gon's cycle
gives R^2 = r_m^2 + r_n^2 + delta_{c2}(n) (type (i), configuration (n, c2)) or
R^2 = r_m^2 + r_n^2 + h_A(m)^2/4 (type (ii)), while F's gives R^2 = r_n^2 + r_m^2 + delta_{c1}(m).
delta_{c1}(m) > 0.35 here, which excludes type (ii) (h_A^2/4 < 3/16) and c2 in (4,4), (3,3,3), (3,6)
(delta <= 0.3373); among the bounded families only n = m with c2 = c1 is not separated.
Step 2: certify (W) for each fan at that single n.  usage: python3 wpoint.py  (~3 s)"""
import json, os, sys, time
from flint import arb
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from caseb_famfilter import tri_delta
from wrun import build, certify
from wgeom import float_lower, float_upper
from wconfigs import PAIRED_BOUNDED as BOUNDED, require_bounded_slice
PI = arb.pi()
CASES = [(38, (3, 7)), (39, (3, 7)), (40, (3, 7)), (41, (3, 7)), (23, (3, 8)), (17, (3, 9)), (19, (4, 5))]
ok = True
for m, c1 in CASES:
    require_bounded_slice(c1, m)
    d1 = tri_delta(m, *c1)
    if not d1 > arb('0.35'):
        raise AssertionError((m, c1))
    allowed = [(c2, n) for c2, ns in BOUNDED.items() for n in ns if tri_delta(n, *c2) is not None and (not (d1 < tri_delta(n, *c2) or d1 > tri_delta(n, *c2)))]
    if not allowed == [(c1, m)]:
        raise AssertionError((m, c1, allowed))
    fid = 'pi:%d,%s' % (m, ','.join(map(str, c1)))
    F = build(fid)
    b = (2 * F.Rc * (PI / m).sin()).atan()
    F.pbox = [(float_lower(b) - 1e-12, float_upper(b) + 1e-12)]
    t = time.process_time()
    res = certify(F)
    st = res['status'] if isinstance(res, dict) else res[0]['status']
    ok &= st == 'CERTIFIED'
    print(fid, 'partner filter leaves only n = m =', m, '; (W) at n = m:', st, 'cpu %.1f s' % (time.process_time() - t), flush=True)
print('wpoint', 'OK' if ok else 'FAILED')
sys.exit(0 if ok else 1)
