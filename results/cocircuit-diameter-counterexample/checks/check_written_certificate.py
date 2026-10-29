#!/usr/bin/env python3
"""Standalone exact written-certificate checker, Python 3 standard library only.
The matrix and witness are printed in the paper. Optional --data compares the pinned inputs.
All mathematical indices are one-based; Python storage indices are one less.
This written witness differs from the formal positive-functional witness.
"""
import argparse, hashlib, json, math, pathlib, resource, sys, time
from fractions import Fraction as Q
resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
T0 = time.process_time()
V = [7_889_496_505_278_816, -788_643_250_921_389_998, -322873814, 73_889_176_985_687_161, 0, -8_399_586_269_177, 16_778_123_544_418, 16_770_653_889_890, 16_773_144_135_505, 2_918_818_204_673_914, 2_039_103_229_854_373, 1_964_406_684_567_592, 2_477_284_371_671_404, 2_402_587_826_384_623, 11008963417, 193_944_140_058, 570_600_902_642, 574_335_730_279, 186_741_363_964, 112_044_818_677, 373_482_727_181]
K = [2, 5, 7, 13, 14, 15, 16, 17, 18, 19, 20, 21, 25, 27, 33, 35, 36, 37, 38, 39, 40]
SELECTIONS = [([0, 1], [], []), ([2, 4, 6, 8, 10, 11, 22, 23, 24, 26, 28, 29, 30, 31, 32], [2], [1]), ([3], [2, 19, 25], [8, 12, 34]), ([5], [2, 5, 7, 38], [1, 6, 12, 34]), ([7], [2, 7], [1, 11]), ([9], [5, 7, 33, 38, 39], [1, 4, 6, 11, 12]), ([12], [2, 5, 27], [3, 4, 26]), ([13], [2, 5, 13, 16, 21, 25], [4, 6, 12, 28, 30, 34]), ([14], [2, 14, 25, 27], [3, 12, 28, 32]), ([15], [2, 5, 15, 21, 25, 27], [4, 12, 26, 28, 31, 34]), ([16], [2, 5, 16, 21, 25], [3, 12, 30, 31, 34]), ([17], [2, 5, 17, 18], [3, 6, 22, 26]), ([18], [2, 5, 13, 18, 19], [3, 4, 12, 22, 26]), ([19], [2, 5, 19, 25, 27], [3, 6, 12, 26, 34]), ([20], [2, 5, 16, 18, 20], [3, 4, 12, 22, 24]), ([21], [2, 5, 13, 15, 21, 25], [1, 6, 12, 22, 32, 34]), ([25], [5, 7, 25, 33, 38, 39], [1, 4, 6, 12, 32, 34]), ([27], [2, 5, 19, 27], [1, 6, 26, 34]), ([33], [2, 5, 7, 25, 33, 37], [1, 4, 8, 11, 12, 24]), ([34, 38, 39], [5, 33, 38, 39], [1, 4, 6, 12]), ([35], [2, 5, 7, 33, 35, 38], [1, 3, 6, 8, 11, 12]), ([36], [5, 36, 39], [1, 6, 12]), ([37], [5, 36, 37], [3, 4, 12]), ([40], [2, 35, 38, 40], [1, 3, 6, 12])]
SPARSE = [(1, [(1, 1), (2, 100), (5, 21), (6, -7), (17, 1), (18, 1)]), (2, [(1, 1), (2, 100), (5, 16), (6, -15), (18, 1), (19, 1)]), (3, [(1, 1), (2, 100), (6, -32), (19, 1), (20, 1)]), (4, [(1, 1), (2, 100), (5, -16), (6, -15), (20, 1), (21, 1)]), (5, [(1, 1), (2, 100), (5, -21), (6, -7)]), (6, [(1, 1), (2, 100), (5, -20), (6, -4), (21, 1)]), (7, [(1, 1), (2, 100), (6, 32)]), (8, [(1, 1), (2, 100), (5, 20), (6, -4)]), (9, [(1, 100), (2, 10000), (3, 3), (4, -2), (6, -3000)]), (10, [(1, 100), (2, 10000), (3, -3), (4, -2), (6, 3000)]), (11, [(1, 2000), (2, 200000), (3, -3), (4, 7), (6, 63600), (16, 2000)]), (21, [(1, 1), (2, -100), (3, 30), (9, 1), (10, 1)]), (22, [(1, 1), (2, -100), (3, 4), (4, -15), (10, 1), (11, 1)]), (23, [(1, 2), (2, -200), (4, -33), (11, 2), (12, 2)]), (24, [(1, 1), (2, -100), (3, -1), (4, -16), (12, 1), (13, 1)]), (25, [(1, 2), (2, -200), (3, -55), (13, 2), (14, 2)]), (26, [(1, 1), (2, -100), (3, -17), (4, 18), (14, 1)]), (27, [(1, 1), (2, -100), (4, 38)]), (28, [(1, 1), (2, -100), (3, 22), (4, 17)]), (29, [(1, 5), (2, -500), (3, -50), (5, 1), (6, -1)]), (30, [(1, 100), (2, -10000), (3, 2999), (5, -12), (6, -20), (9, 100)]), (31, [(1, 10000), (2, -1000000), (3, 299999), (6, 100), (8, 10000)]), (32, [(1, 20000), (2, -2000000), (3, -549000), (5, 4), (6, 25), (7, 20000)])]

def matrix():
    M = [[0]*21 for _ in range(40)]
    for i, entries in SPARSE:
        for j, x in entries: M[i-1][j-1] = x
    a = {1:2000, 2:200000, 3:3, 4:7, 6:-63600, 15:2000}
    t = {j:2*10**(10 if j <= 9 else 13 if j == 10 else 14) for j in range(7,15)}
    b = {1:2000, 2:-200000, 3:-54000, 5:4, 6:-25}
    h = dict(zip(range(15,22), [2*10**8, 2*10**10, 2*10**10, 2*10**10, 2*10**11, 2*10**11, 2*10**12]))
    def fill(i, base, extra):
        M[i-1] = [base.get(j,0)+extra.get(j,0) for j in range(1,22)]
    fill(12,a,t)
    for j in range(7,15): fill(j+6,a,{k:(t[k] if k<j else -t[k]) for k in range(7,j+1)})
    fill(33,b,h)
    for j in range(15,22): fill(j+19,b,{k:(h[k] if k<j else -h[k]) for k in range(15,j+1)})
    return M

def determinant(A):
    """Integer Bareiss elimination with row pivoting and exact divisibility checks."""
    A = [r[:] for r in A]; n = len(A); previous = 1; sign = 1
    for k in range(n-1):
        pivot = next((r for r in range(k,n) if A[r][k]),None)
        if pivot is None: return 0
        if pivot != k: A[k],A[pivot] = A[pivot],A[k]; sign = -sign
        p = A[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                v = A[i][j]*p-A[i][k]*A[k][j]
                assert v % previous == 0
                A[i][j] = v//previous
            A[i][k] = 0
        previous = p
    return sign*A[-1][-1]

def bases():
    out = {}
    for es, removed, added in SELECTIONS:
        assert set(removed) <= set(K) and not (set(added)&set(K))
        B = sorted((set(K)-set(removed))|set(added))
        assert len(B)==21 and len(removed)==len(added)
        for e in es:
            assert e not in out
            out[e] = B
    assert set(out)==set(range(41))
    return out

def check(M):
    C = [40000*x for x in V]; output=[]; global_min=None; min_location=None
    for e,B in sorted(bases().items()):
        A = [[(-1 if e==i+1 else 1)*M[i][j] for i in range(40)] for j in range(21)]
        T = [[A[j][i-1] for i in B] for j in range(21)]
        delta = determinant(T); assert delta != 0
        rhs = [C[j]-sum(A[j]) for j in range(21)]
        numerators=[]
        for r in range(21):
            replaced = [row[:] for row in T]
            for j in range(21): replaced[j][r] = rhs[j]
            numerators.append(determinant(replaced))
        excess = [Q(x,delta) for x in numerators]
        assert min(excess) > 8
        # Independently verify the identity using integer common denominators.
        weights = [delta]*40
        for r,i in enumerate(B): weights[i-1] += numerators[r]
        assert all(sum(weights[i]*A[j][i] for i in range(40)) == delta*C[j] for j in range(21))
        mn = min(excess)
        if global_min is None or mn<global_min:
            global_min=mn; min_location=[e,B[excess.index(mn)]]
        output.append({'cone':e,'basis':B,'signed_determinant':str(delta),'minimum_excess':str(mn),'minimum_basis_weight_floor':1+mn.numerator//mn.denominator})
    return {'kind':'written-certificate-separate-from-formal-witness','rank':21,'cones':41,'weights_per_cone':40,'cramer_ratios_checked':861,'all_weights_at_least_one':True,'all_basis_weights_greater_than_nine':True,'global_minimum_excess':str(global_min),'minimum_location_cone_row':min_location,'checks':output}

def authenticate(path,M):
    path=pathlib.Path(path)
    expected={'chart.json':'db616c106a54e637d7641b2a74ed2754b9149dac4150cddd25a67358f14efd0f','msw-input.json':'abfd9665052110590d8824d0861ab323c1e20468f1169ec1307cfb9686cbb95d'}
    for name,h in expected.items():
        assert hashlib.sha256((path/name).read_bytes()).hexdigest()==h
    chart=json.loads((path/'chart.json').read_text()); assert chart['matrix']==M
    raw=json.loads((path/'msw-input.json').read_text())
    assert len(raw)==40 and all(len(r)==21 for r in raw)
    scales=[]
    for row,integerrow in zip(raw,M):
        q=list(map(Q,row)); s=math.lcm(*(x.denominator for x in q)); scales.append(s)
        assert [int(s*x) for x in q]==integerrow
    assert scales==chart['row_scales'] and chart['source_sha256']==expected['msw-input.json']
    assert len(chart['weights'])==41
    for e,w in enumerate(chart['weights']):
        assert len(w)==40 and min(w)>=1
        assert all(sum(w[i]*(-1 if e==i+1 else 1)*M[i][j] for i in range(40))==chart['chart'][j] for j in range(21))
    return {'source_matrix_identical':True,'source_row_lcm_scales_identical':True,'separate_formal_chart_41_identities_and_1640_positive_weights_verified':True,'input_sha256':expected}

def appendix_tex():
    def cells(xs): return r'\varnothing' if not xs else ','.join(map(str,xs))
    source_rows=[]
    for i,entries in SPARSE:
        r=dict(entries); s=r[1]
        terms=[]
        for j,x in entries:
            if j<=6: continue
            terms.append(('' if x==1 else str(x))+f'u_{{{j}}}')
        tail='+'.join(terms) or '0'
        source_rows.append(f"{i}&{s}&{r.get(3,0)}&{r.get(4,0)}&{r.get(5,0)}&{r.get(6,0)}&${tail}$"+r'\\')
    vector_rows=[]
    for j in range(7):
        vector_rows.append('&'.join(f'{k+1}&{V[k]}' for k in [j,j+7,j+14])+r'\\')
    selection_rows=[]
    for es,removed,added in SELECTIONS:
        label=r'\mathcal D' if len(es)>3 else cells(es)
        selection_rows.append(f'${label}$&${cells(removed)}$&${cells(added)}$'+r'\\')
    template=r'''% BEGIN EXPLICIT CERTIFICATE
This appendix specifies the source matrix $M_0$ and a positive functional
for the cones obtained by reversing at most one row. Row and column labels
are one-based: $1\le i\le40$, $1\le j\le21$; $e=0$ denotes the
nonnegative cone and $e=1,\ldots,40$ reverses row $e$.

\subsection*{The integer source matrix}
Let $u_j$ denote the $j$th coordinate row of $\mathbb Z^{21}$ and let $m_i$
be row $i$ of $M_0$. For the rows in the following table set
\[
 m_i=s_i(u_1+100\eta_i u_2)+a_i u_3+b_i u_4+p_i u_5+q_i u_6+T_i,
 \qquad \eta_i=\begin{cases}1&i\le20,\\-1&i\ge21.\end{cases}
\]
\begin{center}\small
\setlength{\tabcolsep}{7pt}
\begin{tabular}{r|rrrrr|l}
$i$&$s_i$&$a_i$&$b_i$&$p_i$&$q_i$&$T_i$\\\hline
@@SOURCE@@
\end{tabular}
\end{center}
The remaining seventeen rows are specified by two triangular recipes. Define
\[
 \begin{aligned}
 \alpha&=2000u_1+200000u_2+3u_3+7u_4-63600u_6+2000u_{15},\\
 (t_7,\ldots,t_{14})&=2(10^{10},10^{10},10^{10},10^{13},10^{14},10^{14},10^{14},10^{14}).
 \end{aligned}
\]
Then
\[
 m_{12}=\alpha+\sum_{k=7}^{14}t_ku_k,\qquad
 m_{j+6}=\alpha+\sum_{k=7}^{j-1}t_ku_k-t_ju_j\quad(7\le j\le14).
\]
Likewise define
\[
 \begin{aligned}
 \gamma&=2000u_1-200000u_2-54000u_3+4u_5-25u_6,\\
 (h_{15},\ldots,h_{21})&=2(10^8,10^{10},10^{10},10^{10},10^{11},10^{11},10^{12}).
 \end{aligned}
\]
Then
\[
 m_{33}=\gamma+\sum_{k=15}^{21}h_ku_k,\qquad
 m_{j+19}=\gamma+\sum_{k=15}^{j-1}h_ku_k-h_ju_j\quad(15\le j\le21).
\]
Empty sums are zero, and all entries not specified by these recipes are zero.
These recipes give exactly the $40\times21$ integer matrix obtained by clearing
each source row's reduced denominators by their least common multiple.
\subsection*{The functional and weights}
Set $c(z)=40000\sum_{j=1}^{21}v_jz_j$, where the integers $v_j$ are
\begin{center}\small
\setlength{\tabcolsep}{5pt}
\begin{tabular}{r r|r r|r r}
$j$&$v_j$&$j$&$v_j$&$j$&$v_j$\\\hline
@@VECTOR@@
\end{tabular}
\end{center}
Let $\sigma_{0,i}=1$ for every $i$; for $1\le e\le40$ let
$\sigma_{e,e}=-1$ and $\sigma_{e,i}=1$ for $i\ne e$.
For each $e$, specify an increasing list $B_e=(\ell_1,\ldots,\ell_{21})$ as follows:
\[
 \begin{gathered}
 K=\{2,5,7,13,14,15,16,17,18,19,20,21,25,27,33,35,36,37,38,39,40\},\\
 B_e=\operatorname{sort}\bigl((K\setminus R_e)\cup S_e\bigr).
 \end{gathered}
\]
In the table, $\mathcal D=\{2,4,6,8,10,11,22,23,24,26,28,29,30,31,32\}$.
Each displayed comma-separated entry denotes a set, and a multi-label row
assigns the same sets to every listed $e$.
\begin{center}\scriptsize
\setlength{\tabcolsep}{14pt}
\renewcommand{\arraystretch}{1.03}
\begin{tabular}{r|l|l}
$e$&$R_e$ (delete from $K$)&$S_e$ (add to $K$)\\\hline
@@BASES@@
\end{tabular}
\end{center}
Write $c^{\mathsf T}=40000(v_1,\ldots,v_{21})^{\mathsf T}$ and define
\[
 \begin{gathered}
 N_e=[\,\sigma_{e,\ell_1}m_{\ell_1}^{\mathsf T}\ \cdots\
       \sigma_{e,\ell_{21}}m_{\ell_{21}}^{\mathsf T}\,],\qquad \Delta_e=\det N_e,\\
 d_e=c^{\mathsf T}-\sum_{i=1}^{40}\sigma_{e,i}m_i^{\mathsf T}.
 \end{gathered}
\]
Let $N_e[r\leftarrow d_e]$ mean replace column $r$ of $N_e$ by $d_e$, and put
\[
 \lambda_{e,i}=\begin{cases}
 1+\det(N_e[r\leftarrow d_e])/\Delta_e,&i=\ell_r\ (1\le r\le21),\\
 1,&i\notin B_e.
 \end{cases}
\]
Evaluating these integer determinants exactly gives
\[
 \Delta_e\ne0\quad(0\le e\le40),\qquad
 \frac{\det(N_e[r\leftarrow d_e])}{\Delta_e}>8
 \quad(0\le e\le40,\ 1\le r\le21).
\]
Thus all weights are at least $1$ (basis weights exceed $9$), and Cramer's rule gives
$c=\sum_{i=1}^{40}\lambda_{e,i}\sigma_{e,i}m_i$ for every $e$.
Also $\Delta_0\ne0$ gives $\operatorname{rank}M_0=21$. If $z\ne0$ has all
signed slacks $\sigma_{e,i}m_i z\ge0$, full column rank makes at least one
slack positive, so $c(z)>0$. Every datum needed for these finite checks is
printed in this appendix. An exact checker of these formulas is included
in \cite{supplement}.
% END EXPLICIT CERTIFICATE
'''
    rendered = template.replace('@@SOURCE@@','\n'.join(source_rows)).replace('@@VECTOR@@','\n'.join(vector_rows)).replace('@@BASES@@','\n'.join(selection_rows))
    import re
    return re.sub(r'(?<![\w])\d{10,}(?![\w])', lambda m: '$'+format(int(m.group()),',d').replace(',',r'\,')+'$', rendered)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--data',help='optional pinned bundle data directory')
    ap.add_argument('--emit-tex',help='write the explicit appendix fragment')
    ap.add_argument('--check-paper',help='check the marked paper appendix against the explicit constants')
    ap.add_argument('--output',default='verification-results.json')
    args=ap.parse_args()
    M=matrix(); result=check(M)
    if args.data: result['original_data_verification']=authenticate(args.data,M)
    if args.emit_tex: pathlib.Path(args.emit_tex).write_text(appendix_tex())
    if args.check_paper:
        paper=pathlib.Path(args.check_paper).read_text()
        assert paper.count('% BEGIN EXPLICIT CERTIFICATE')==paper.count('% END EXPLICIT CERTIFICATE')==1
        fragment=paper[paper.index('% BEGIN EXPLICIT CERTIFICATE'):paper.index('% END EXPLICIT CERTIFICATE')+len('% END EXPLICIT CERTIFICATE')]
        assert fragment==appendix_tex().rstrip(), 'printed certificate differs from checked constants'
    result['matrix_canonical_sha256']=hashlib.sha256(json.dumps(M,separators=(',',':')).encode()).hexdigest()
    result['cpu_seconds']=time.process_time()-T0
    result['peak_rss_native_units']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    result['peak_rss_unit_note']='KiB on Linux; bytes on macOS; see external /usr/bin/time -v for measured maximum'
    pathlib.Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='checks'},indent=2))
if __name__=='__main__':
    try:
        main()
    except (AssertionError, ValueError, OSError, ZeroDivisionError) as error:
        print(f'FAIL written certificate: {type(error).__name__}: {error}', file=sys.stderr)
        raise SystemExit(1)
    print('PASS written certificate: 41 cones; 861 Cramer ratios; all identities and weight bounds verified.', file=sys.stderr)
