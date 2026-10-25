# Computation, controls, and historical evidence

This companion retains the detailed computation record, control scope, and historical evidence accompanying the nonexistence result. Labels in backticks identify equations or sections of the paper; the mathematical reductions are in its appendix. The commands and executable checks remain specified in [the checker guide](README.md). Historical observations do not replace a fresh complete CPU search.

## History and the new case
We recall the existence question and explain how the present computation
extends earlier classifications. Williamson introduced the construction in 1944 [Williamson].
The odd-order Williamson conjecture asserts that these four blocks exist
for every odd positive integer $`n`$; Turyn recorded the more general
all-orders conjecture in 1972 [Turyn].
Baumert, Golomb and Hall's computer construction at block order $`23`$
yielded a Hadamard matrix of order $`92`$ [BGH].
Baumert and Hall subsequently enumerated the odd block orders through
$`23`$ [BH]. Later searches by Sawade, Koukouvinos and Kounias,
and Đoković [Djokovic1992,Djokovic1995] extended the odd-order classifications; the history,
including corrections to incomplete enumerations, is reviewed by
Bright, Kotsireas and Ganesh [BKG] (Section 1).
Đoković disproved the conjecture at order $`35`$ in 1993
[Djokovic]. Holzmann, Kharaghani and Tayfeh-Rezaie completed the
odd-order enumeration through $`59`$, including nonexistence at $`47`$, $`53`$
and $`59`$ [HKT]. Their work dates to a 2007 manuscript [HKT]. Turyn's construction supplies orders $`61`$ and $`63`$.
Lang and Schneider also classified order $`61`$, as credited by
Bright, Kotsireas and Ganesh [BKG] (Section 1), in their work on
Turyn-type Williamson matrices [LS].
Bright, Kotsireas and Ganesh's MathCheck SAT and computer-algebra work, first posted
in 2018, enumerated all even orders through $`70`$ and the odd
multiples of three through $`69`$, including a new class at order $`63`$
[BKG]. Bright's March 20, 2019 research statement describes $`65`$ as
“currently the smallest order for which it is unknown” whether Williamson
matrices exist [BrightStatement] (Section 4.2); it also lists $`67`$ as
unenumerated. The present theorem answers the order-$`65`$ case negatively;
order $`67`$ remains open. The Wikipedia article on the Williamson conjecture
lists nonexistence at $`35,47,53,59`$; it does not identify $`65`$ as open. (<https://en.wikipedia.org/wiki/Williamson_conjecture>, consulted October 22, 2026.)
The open status of $`65`$ cited here rests on Bright's 2019 statement and
version 2 (September 6, 2026) of Kharaghani, Mohammadian, Tayfeh-Rezaie and Zaitsev's paper
[KMTZ] (Section 2.3).

There is substantial recent progress for a related family. Kharaghani,
Mohammadian, Tayfeh-Rezaie and Zaitsev's version 2 [KMTZ]
constructs *near-Williamson* matrices at order $`65`$: these satisfy
$`AA^{\mathsf T}+BB^{\mathsf T}+CC^{\mathsf T}+DD^{\mathsf T}=260I_{65}`$,
with $`B,C,D`$ symmetric, while $`A`$ need not be symmetric. The work was
first posted on May 9, 2026 as a three-author version 1 by Kharaghani,
Mohammadian and Tayfeh-Rezaie, titled *A search for Hadamard matrices
of Williamson type*, with existence through odd order $`63`$.
The four-author version 2, dated September 6, 2026, establishes near-Williamson existence
at every odd order through $`69`$ and enumerates that broader family through
odd order $`47`$. Its order-$`65`$ example does not have symmetric $`A`$.
Our theorem excludes only the construction with four symmetric circulant blocks.
Section 2.3 of version 2 [KMTZ] still includes $`65`$ among the Williamson
orders for which matrices have not been found; its order-$`65`$ search
constructs near-Williamson examples and does not exhaust the symmetric case.
The recent survey by Egan, Kotsireas, London and Ó Catháin, first posted
on October 19, 2026, places these developments in the broader Hadamard
construction problem [EKLO]; it records the known nonexistence orders
$`35,47,53,59`$, without reporting a settlement of the order-$`65`$ case.

Bennett, Bright, Colinot and Nayak's work, first posted January 29, 2026,
enumerates circulant Williamson-type matrices through order $`21`$, allowing
nonsymmetric blocks [BBCN]. Their correspondence with quaternionic
perfect sequences gives an enumeration algorithm for that broader family.
This is relevant progress in Williamson-type enumeration; the present
order-$`65`$ search concerns symmetric blocks and uses neither their code
nor their quaternionic correspondence.

Zhang's April 2, 2026 report [Zhang] (Section 7.4) describes an
AI-assisted attempt on the exact order-$`65`$ problem and expressly leaves
it unsolved. This earlier attempt is relevant background; none of its
code, data, or proposed reductions is used here.

The new contribution is completion of the order-$`65`$ problem with no
restriction on the four symmetric circulant blocks beyond their defining
equation. Compression and spectral restrictions are established
methods, developed in particular by Đoković and Kotsireas
[DK] and used in the MathCheck SAT and computer-algebra enumeration
[BKG]. The difficult step here is excluding *every* lift of
a possible compression, meaning every choice of full rows having that
compression. Excluding the compressed objects alone does not settle the
question. A direct join of pairs of full rows, with conservative spectral bounds,
completes this step. This replaces the SAT-based lifting step of
Bright, Kotsireas and Ganesh's MathCheck system, whose published enumeration treats even
orders and orders divisible by three. Their enumeration does not include
$`65`$, which has neither of those properties.
Holzmann, Kharaghani and Tayfeh-Rezaie already used row and pair spectral
bounds [HKT] (Section 3). After choosing the first two blocks, they
used the product identity to eliminate the fourth and solved linearized
equations modulo $`4`$ for the third, checking the original equations
finally. Here compression, a multiplier restriction on one row, and
two-sided pair bounds instead precede a direct join of the two full-row
pairs. These are combinations of established tools, not a new general
construction principle. The measured cost below describes this
implementation; no controlled comparison with the earlier programs is
available, and no speedup over them is claimed.
The central limitation is explicit: checking the records is much cheaper than repeating the search, but does
not prove correctness of the filtering and matching operations.

Section 2 of the paper gives the argument's structure. Appendices A–C justify the finite reductions and matching test, and Appendix D states the exhaustion outcome and concludes the proof. Section 3 summarizes the checks, reproduction commands, and trust boundary; the detailed controls and historical evidence follow here.



The complete CPU enumeration and two separately written complete GPU
searches all find no solution. They use the same mathematical compression
and symmetry reductions. The CPU implementation supplies its own row
generator, cosine calculations, class and unit enumeration, and pair join;
it does not read the GPU implementations' generated input files. The row
sets and class counts agree. Their pair filters differ, so the CPU and GPU
survivor counts are not expected to coincide and are not claimed to do so.
[Corroborating GPU computations](#corroborating-gpu-computations) documents the prior GPU computations and the
limits of their retained evidence. The per-unit comparisons below are
between the CPU search and the NumPy join, not between the GPU searches.
The public CPU implementation supplies a full replay without a GPU.

## Two independent record checkers
The record checks establish the cover and its arithmetic accounting.
The first regenerates CPU inputs using the CPU generators, but checks the
cover with separately written code. The second has its own row, cosine,
cover, and record-checking code written from the mathematical specification.
Their row sets agree byte for byte, and both accept the complete cover
and pair totals. Neither rederives survivor or key-match counts.
[Record-checking and control details](#record-checking-and-control-details) describes their scope and input sharing.

Here and throughout, independent means separately implemented, not
produced by separate human teams or independently replicated by outside
institutions. The AI provenance is stated on the first page.

Both checkers reject deliberately altered records and an incomplete
cover. [Corruption controls](#corruption-controls) states the changes tested.

These are *coverage and accounting* checks. Neither checker proves
that every pair was correctly filtered, stored, and matched by the search.
In particular, a search bug could lose all genuine matches while leaving
consistent pair counts. The receipts are an exhaustion record, not a
short independently checkable proof of all the unsuccessful joins.

## Known cases and independent joins
Known solutions and independently computed pair joins test that the
search can both recover solutions and reject false candidates. A
*baseline enumeration* means a reference search with fewer
reductions. The baseline used here, without the search-time spectral, compression,
or product reductions, reproduces the published equivalence-class counts
at every odd order from $`3`$ through $`33`$ [HKT] (Table 1):

```math

\begin{array}{c|rrrrrrrr}
n&3&5&7&9&11&13&15&17\\ \hline
\#&1&1&2&3&1&4&4&4\\[2pt]
n&19&21&23&25&27&29&31&33\\ \hline
\#&6&7&1&10&6&1&2&5
\end{array}

```

The equivalences used for odd-order class comparison are row negation,
row permutation, and a common invertible multiplier, as in
[BKG] (Section 2.2). The trivial order $`1`$ has one class as well.

Controls at orders $`9`$ through $`35`$ compare the reduced search with the
baseline, switching individual reductions off, removing both row sorting
and orbit reduction, and using compression alone. The corresponding solution sets agree after taking their
*symmetry closures*: all normalized quadruples obtainable by
permuting rows and applying a common invertible multiplier. The order-$`35`$
reference uses a spectral row filter and yields no solution.

A *row-filtered baseline* additionally applies the single-row
spectral restriction, but no pair filter or product-key restriction.
At order $`39`$ the controls recover the single published class and compare
with a row-filtered baseline. At order $`45`$ multiple compression factors
recover its single class; the variant comparisons use the symmetry closure
of the search output as reference, so those comparisons are consistency
checks, not an independent classification. At order $`55`$, both compression
factors $`5`$ and $`11`$ discover the single published class without receiving
a witness as input. In particular factor $`5`$ tests the same compression
factor as order $`65`$. These positive controls show that the search can
recover solutions, including repeated rows, where they exist.

A separately written implementation using NumPy arrays reconstructs row
lists, filters, and joins without sharing search code or using the product
identity. It compares the list sizes and survivor counts and performs its
own exact autocorrelation join. It agrees on all $`3{,}309`$ order-$`45`$ units
and recovers that order's solution.

At order $`65`$, it checks $`300`$ units sampled uniformly without replacement
with NumPy's `default_rng(65)`, together with the $`12`$ units having
the largest enumerated-pair counts. These two sets are disjoint. The $`312`$
units contain $`7{,}955{,}197{,}270`$ surviving-pair instances, counted as above, about $`0.4833%`$
of the total in Table `tab:counts` in the paper. Every sampled join gives zero
solutions, and all list sizes agree with the receipts.

Both survivor counts agree with the records on every checked unit.
The bookkeeping for numerical rounding boundaries, and further order-$`55`$
checks, is given in [Record-checking and control details](#record-checking-and-control-details).
These are sample-based implementation tests, not
a substitute for the complete enumeration. A positive matching test on
order-$`65`$ data, described in [Positive matching control at order 65](#positive-matching-control-at-order-65), also checks
that deliberately shortened keys produce the same nonzero match count
in separate join implementations.

## Public replay and data
The public commands distinguish checking the record from repeating the
complete search. From the public folder, install `checks/requirements.txt` and invoke
`python3 checks/check.py`; the full requirements and mode descriptions
are in `checks/README.md`. The default check regenerates the order-$`65`$
rows and cover with both checkers and validates all receipts and corruption
controls. It also checks known-order counts, witness validity at orders $`39`$,
$`45`$, and $`55`$, and discovery at $`39`$ and $`45`$. It does not repeat all
order-$`65`$ pair joins. The `--full-controls` option adds the
unfiltered baseline counts through $`33`$ and discovery at $`55`$; the
`--full-search` option repeats every order-$`65`$ CPU join. The default mode checks the supplied records; the last mode recomputes
their mathematical results.

The full retained mask array alone has $`1{,}584{,}203{,}988`$ bytes,
one little-endian unsigned 32-bit integer per retained row. An optional dataset deposit could hold the complete row data, class and
unit data, full receipt collection, and control outputs for comparison. The compact class, unit, and receipt data needed by the default
check are already included in the public folder; the dataset is not required
for that check. The optional deposit contents and replay commands are specified in
`data/README.md`. The row data are regenerated from the public programs; no external
dataset is needed to run them. No separate dataset deposit exists and no
dataset DOI has been assigned. The complete CPU
search recorded about $`271`$ CPU-hours for its joins; this is a scale
estimate for a replay, not the cost of the short record checks.



## Corruption controls
This appendix records deliberate alterations that the independent
checkers must reject. They test whether the checks detect the particular
coverage and accounting errors for which they are designed.

Corruption controls exercise both implementations: deletion of a receipt,
a duplicate unit, an incorrect row-list size, an incorrect pair count,
keys truncated below their prescribed $`64`$ bits, a missing cover representative, and a
false solution must all be rejected. Additional row-data corruptions test
that the enumerated classes have not silently lost a row. The planted
cover gap is tested by the exhaustive cover computation itself, by re-enumerating the admissible tuples.


## Positive matching control at order 65
This control tests the matching path on a full order-$`65`$ unit whose
normal $`64`$-bit keys have no matches. It truncates keys to $`32`$ bits to
create deliberate collisions, leaving the row lists and spectral filters
unchanged. This is a diagnostic setting, not the setting used to conclude
nonexistence.

For unit $`5200`$, the four list sizes are
$`56{,}372`$, $`13{,}092`$, $`12{,}776`$, and $`2{,}830`$.
The two sides have $`6{,}611{,}810`$ and $`1{,}872{,}629`$ surviving pairs.
The public search and a separately implemented join both find exactly
$`2{,}918`$ matching $`32`$-bit keys and zero exact solutions. These matches
are false collisions, not Williamson witnesses. Changing the expected
match count makes the control reject. The default public check includes
this test, alongside the unmodified $`64`$-bit receipt checks.

For scale only, if the pair keys were independent uniform random
$`64`$-bit values, the expected total number of equal keys would be

```math

 \frac{\sum_U S_{U,1}S_{U,2}}{2^{64}}
 =\frac{6{,}493{,}019{,}596{,}516{,}340{,}568}{2^{64}}
 \approx0.3519872976,

```

where $`S_{U,1}`$ and $`S_{U,2}`$ are the survivor counts on the two sides
of unit $`U`$. At $`32`$ bits the same hypothetical model gives about
$`2{,}883`$ matches for unit $`5200`$, compared with the observed $`2{,}918`$.
The actual keys are deterministic and structured: no uniformity or
independence is proved, and these ratios are not probability bounds or
evidence of complete exhaustion. The control's evidential content is the
exact agreement of the two implemented joins on a nonzero match count.

## Computation by row-sum type
The following breakdown of the CPU receipts shows how the search cost
is distributed among the five possible absolute row-sum types. Survivors
count both sides of each pair join; CPU times are rounded.


| Absolute row sums | Units | Surviving pairs | CPU-hours |
|---|---:|---:|---:|
| $`(1,3,5,15)`$ | 19,793 | $`439{,}857{,}850{,}463`$ | 55.946  |
| $`(1,3,9,13)`$ | 21,291 | $`528{,}816{,}451{,}429`$ | 102.765  |
| $`(3,3,11,11)`$ | 4,733 | $`103{,}766{,}383{,}699`$ | 16.208  |
| $`(3,7,9,11)`$ | 19,692 | $`449{,}073{,}745{,}221`$ | 70.162  |
| $`(7,7,9,9)`$ | 5,190 | $`124{,}377{,}127{,}312`$ | 26.245  |
## Record-checking and control details
This appendix specifies implementation sharing and explains the numerical
comparison flags omitted from the main computational summary.

The record checks establish the cover and its arithmetic accounting. The
first checker reuses the CPU row and unit generators to regenerate their
outputs, constructs a separate
exact-vector cover enumeration, computes its own count of minimal masks
under $`K`$, and checks every receipt against these data. In particular,
each unit appears exactly once, its listed row counts agree, and each
enumerated pair count is the product of the corresponding list sizes.
The checker rejects records whose option fields do not state the full
$`64`$-bit key and prescribed necessary filters, and requires each recorded
solution count to be zero. It checks the recorded options; this alone
does not establish that the executable honored them. Survivor
and key-match counts are read from the records, not independently derived
by this checker. Its cover code does
not import the unit generator or the search.

The second checker was written from the mathematical specification
without using the first implementation's code. It shares the problem
definition and the supplied records, not the row generator, cosine table,
cover-enumeration code, or receipt-checking code. It enumerates all $`2^{32}`$ masks with its own C++ code and
integer cosine enclosures, obtains the same row set, performs its own
exact cover enumeration, and validates all unit records. Its regenerated row file agrees byte for byte with the first
implementation's. Both checkers accept the same cover and receipt totals.
They do not rederive the survivor or key-match counts.


Keys truncated to
$`12`$ bits test collisions. A constrained-capacity test exercises restarts;
its effective initial capacity is $`1{,}024`$ entries. 
When a value $`64\widetilde\lambda_x(k)^2\pm0.01`$ is within $`10^{-7}`$
of an integer, different summation orders may change its rounded enclosure.
The automatic survivor-count comparison is skipped for that unit, while
the independent solution search still runs. This affects $`103`$ of the
$`312`$ sampled units. Comparing the printed integer counts separately shows
that both survivor counts agree with their receipts in all $`312`$ units,
including those $`103`$.
At order $`55`$, the same implementation checks $`300`$ units sampled with
seed $`55`$ and the additional known-solution unit. It recovers the solution;
the printed survivor counts agree in all $`301`$ units, including the $`29`$
randomly sampled units whose automatic count comparison is skipped.

## Corroborating GPU computations
This appendix distinguishes the earlier complete GPU searches from the
CPU implementation distributed with this paper. Their results are
corroborating computational evidence, not formal verification of the CPU
program or per-unit agreement with its stronger pair filter.

Both GPU computations covered all $`70{,}699`$ compressed units and found
zero solutions. We call them the *primary GPU search* and the
*independent GPU replay*. The primary GPU search recorded about
$`23.805`$ GPU-hours of full-search time in its portable progress summary.
The independent GPU replay used a separately written implementation,
regenerated the row sets and checked the complete unit cover before enumerating
$`146{,}369{,}334{,}587{,}912`$ ordered pairs. It retained
$`3{,}610{,}911{,}823{,}878`$ pairs and found $`30`$ hash matches, all rejected
by exact autocorrelation checks. Its completed search intervals contain
each unit exactly once. This independent GPU replay recorded about
$`2.060`$ GPU-hours of search time and about $`2.143`$ occupied GPU-hours
including setup and controls. These resource measures are historical;
they are not controlled performance comparisons between algorithms.

The independent GPU replay used an integer lower bound for the pair
spectrum and did not use either the product-identity key or the
one-designated-row multiplier reduction. It therefore enumerated a
different number of pairs and retained more pairs than the CPU search.
Both full searches agree with the CPU search on the mathematical answer,
not on survivor or match totals. Their inputs, recorded build choices,
completed unit intervals, and outputs were checked against the retained
source and data records. Positive discovery controls at orders $`25`$,
$`35`$, and $`45`$ gave the known $`10`$, $`0`$, and $`1`$ equivalence classes.

The earlier GPU sources and output collections are not distributed in
this public CPU bundle. The portable record of the primary GPU search does not
recheck all original raw execution records, and neither CUDA program is
formally verified. The later CPU search is a separately coded, complete
repetition of the mathematical exhaustion; the fast public record checks
are not another complete repetition. All implementations share the
mathematical specification, and no independent human-team or institutional
replication is claimed. The self-contained reproduction route supplied
here is the complete CPU search, with the trust boundary stated in
Section `sec:computation` in the paper.


## References

[Williamson] J. Williamson, Hadamard's determinant theorem and the sum of four squares,
Duke Mathematical Journal 11 (1944), 65–81.
<https://doi.org/10.1215/S0012-7094-44-01108-7>.

[Turyn] R. J. Turyn, An infinite class of Williamson matrices,
Journal of Combinatorial Theory, Series A 12 (1972), 319–321.
<https://doi.org/10.1016/0097-3165(72)90095-7>.

[BGH] L. Baumert, S. W. Golomb and M. Hall, Jr., Discovery of an Hadamard
matrix of order 92, Bulletin of the American Mathematical Society
68 (1962), 237–238.
<https://doi.org/10.1090/S0002-9904-1962-10761-7>.

[BH] L. Baumert and M. Hall, Jr., Hadamard matrices of the Williamson type,
Mathematics of Computation 19 (1965), 442–447.
<https://doi.org/10.2307/2003674>.

[Djokovic1992] D. Ž. Đoković, Williamson matrices of orders $`4\cdot29`$ and $`4\cdot31`$,
Journal of Combinatorial Theory, Series A 59 (1992), 309–311.
<https://doi.org/10.1016/0097-3165(92)90071-2>.

[Djokovic1995] D. Ž. Đoković, Note on Williamson matrices of orders $`25`$ and $`37`$,
Journal of Combinatorial Mathematics and Combinatorial Computing
18 (1995), 171–175.
<https://combinatorialpress.com/jcmcc/vol18/>.

[Djokovic] D. Ž. Đoković, Williamson matrices of order $`4n`$ for $`n=33,35,39`$,
Discrete Mathematics 115 (1993), 267–271.
<https://doi.org/10.1016/0012-365X(93)90495-F>.

[HKT] W. H. Holzmann, H. Kharaghani and B. Tayfeh-Rezaie,
Williamson matrices up to order 59, Designs, Codes and Cryptography
46 (2008), 343–352; a 2007 manuscript.
<https://doi.org/10.1007/s10623-007-9163-5>.

[LS] W. Lang and E. Schneider, Turyn type Williamson matrices up to order 99,
Designs, Codes and Cryptography 62 (2012), 79–84;
first published online March 5, 2011.
<https://doi.org/10.1007/s10623-011-9492-2>.

[Zhang] S. Y. Zhang, Programmable Emergence via Cognitive Engine: Longitudinal
Evidence of AI Research Maturation, April 2, 2026.
<https://doi.org/10.5281/zenodo.19392279>.

[DK] D. Ž. Đoković and I. S. Kotsireas,
Compression of periodic complementary sequences and applications,
Designs, Codes and Cryptography 74 (2015), 365–377;
arXiv:1302.0571, first posted February 4, 2013.
<https://doi.org/10.1007/s10623-013-9862-z>.

[BKG] C. Bright, I. Kotsireas and V. Ganesh,
Applying Computer Algebra Systems with SAT Solvers to the Williamson
Conjecture, arXiv:1804.01172, first posted April 3, 2018;
Journal of Symbolic Computation 100 (2020), 187–209.
<https://arxiv.org/abs/1804.01172>.
<https://doi.org/10.1016/j.jsc.2019.07.024>.

[BBCN] A. Bennett, C. Bright, P. Colinot and A. Nayak,
Quaternionic Perfect Sequences and Hadamard Matrices,
arXiv:2601.22337, first posted January 29, 2026.
<https://arxiv.org/abs/2601.22337>.

[BrightStatement] C. Bright, Extended Research Statement, March 20, 2019.
<https://cs.curtisbright.com/extended-research-statement.pdf>.

[EKLO] R. Egan, I. Kotsireas, S. London and P. Ó Catháin,
Recent progress in the construction of Hadamard matrices,
arXiv:2610.27175, first posted October 19, 2026.
<https://arxiv.org/abs/2610.27175>.

[KMTZ] H. Kharaghani, A. Mohammadian, B. Tayfeh-Rezaie and V. Zaitsev,
A Search for Hadamard Matrices of Near-Williamson Type,
arXiv:2605.08661v2, September 6, 2026.
First posted May 9, 2026 as version 1 by H. Kharaghani, A. Mohammadian
and B. Tayfeh-Rezaie, titled *A search for Hadamard matrices of Williamson type*.
<https://arxiv.org/html/2605.08661v2>.

## Implementation details accompanying the journal-style edition

The following details were moved from the paper without changing the implementation.
They specify the original build, key constants, and record fields. The mathematical
arguments for complete matching and conservative arithmetic remain in the paper.

```text
The public build invokes GCC with \texttt{-O3 -fopenmp} and links
\texttt{libm}; it invokes G++ with \texttt{-O3 -std=c++17 -fopenmp}
for the second checker. The recorded CPU search additionally used
\texttt{-march=native}. No build uses \texttt{-ffast-math}. The coefficients $R_s$ are the successive outputs of the public
\texttt{splitmix64} function, initialized with the hexadecimal seed
\texttt{5713a1d2c0ffee65}, with the low bit set to one. The outputs are indexed from $s=0$ to $32$, with indices $1$ through $32$
used in $f$. The fixed multiplier $R$ is hexadecimal
\texttt{d6e8feb86659fd93}. The complete key function is specified in
\texttt{checks/search.c}. A receipt is a record for one
unit: the four classes, pairing, designated row, list sizes, enumerated
pair counts, survivor counts, matching keys, solutions, and number of
passes. A pass processes one part of the pair lists, as defined in
Appendix~\ref{app:join}; every order-$65$ unit uses one pass. A key match
is a surviving left pair and a surviving right pair with equal keys.
A surviving pair is counted once for each side of each unit where it occurs.
The complete receipt collection has no unresolved unit.

```

The lower spectral enclosure has the following qualification, retained from the paper:
"No strictly positive gap is claimed after clamping."

## Historical statements and source locators

These detailed source formulations accompany the narrative history in the paper.
The TeX source notation is retained here to preserve exact quotations and statements.

```text
Turyn's 1972 abstract records ``it has been conjectured that one such exists
of any order $4t$'' and ``An infinite family is constructed here''~\cite{Turyn}.
Koukouvinos and Kounias (1990, Section 1, p.~162) credit Baumert, Golomb
and Hall (1962) with ``Williamson matrices for $m=23$'' (Hadamard order $92$),
and Baumert and Hall (1965) with ``all solutions for $3\leq m\leq23$''
(at odd block orders)~\cite{KK1990,BGH,BH}.
\DJ okovi\'c's 1995 note (Section 5, p.~174) records ``An exhaustive computer
search for non-equivalent solutions'' by Sawade (1977), Koukouvinos and
Kounias (1988, 1990), and \DJ okovi\'c (1992, 1993); its Table 1 corrects
the order-$25$ count~\cite{Sawade,KK1988,KK1990,Djokovic1992,Djokovic,Djokovic1995}.
The same note (Section 1, p.~172), citing his 1993 paper, records
``it has none for $n=35$'', disproving the odd-order conjecture; Section 5
records corrections at $33$ and $39$~\cite{Djokovic1995,Djokovic}.
Holzmann, Kharaghani and Tayfeh-Rezaie enumerate odd orders through $59$,
with none at $47$, $53$ and $59$: December 12, 2007 manuscript,
Section 4, Table 1~\cite{HKT}.
Bright, Kotsireas and Ganesh's version 2, p.~3, reports ``the order 61 was
enumerated by Lang and Schneider (2012)''~\cite{BKG,LS}; the latter paper's
title specifies Turyn type.

Nearby work includes Egan, Kotsireas, London and \'O Cath\'ain's
October 19, 2026 survey (version 1, Section 2.1: ``Williamson matrices do
not exist at every odd order'', listing $35,47,53,59$)~\cite{EKLO},
Bennett, Bright, Colinot and Nayak's quaternionic perfect-sequence
enumeration (version 1, abstract: ``does not require the sequences to be
symmetric'')~\cite{BBCN}, and Zhang's April 2, 2026 AI-assisted
account~\cite[Section 7.4]{Zhang}.

```

## Normalization and storage details

The original sequence normalization and complete storage argument are retained below.

```text
A symmetric row of order $65$, normalized to start with $+1$, is
encoded by its $32$ remaining signs. Row sums and Fourier eigenvalues
supply necessary conditions. Summing entries in each residue class modulo
$13$ compresses each row to an integer vector. Rows are grouped by row sum
and compression, and four classes form an admissible tuple when their
compressed autocorrelations satisfy the required equations. A lift chooses
one full row from each class.

Surviving pairs on one side are stored by linear probing in a table whose
size exceeds twice the number of entries. No entry is deleted or
overwritten. A probe continues through every equal key until the first
empty slot, so repeated keys and repeated rows are retained. A capacity
overflow abandons the whole attempt and restarts in passes partitioned by
the high bits of this same key on both sides. Equal keys always belong to
the same pass. Every reported order-$65$ unit completed in one pass.
```

The historical question was documented in the following original source formulation:

```text
The existence question belongs to the Williamson construction of Hadamard
matrices; see Bright, Kotsireas and Ganesh, arXiv version 2,
Theorem 2 and Definition 5~\cite{BKG}. Bright's research statement, dated
March 20, 2019, Section 4.2~\cite{BrightStatement}, calls $65$
``currently the smallest order for which it is unknown'' whether Williamson
matrices exist. For the neighboring near-Williamson question, see
Kharaghani, Mohammadian, Tayfeh-Rezaie and Zaitsev, arXiv version 2,
Definition 1.1 and Table 6~\cite{KMTZ}.

```

## Terminology in the stored enumeration

The programs call a compressed orbit representative a unit. The paper uses
the mathematical name; the original definition and associated mathematical
paragraphs remain exactly as originally stated below.

```text
\setcounter{theorem}{3}
\begin{lemma}\label{lem:cover}
Let one representative of each orbit of admissible sorted class tuples
under $(\Z/13\Z)^*/\{1,-1\}$ be retained. Every order-$65$ Williamson
solution is equivalent, by a common multiplier and a permutation of its
rows, to a lift of a retained tuple.
\end{lemma}
\begin{proof}
A solution's tuple is admissible by Lemma~\ref{lem:compression}.
Choose a multiplier carrying it to its orbit representative, lift that
multiplier modulo $65$, and apply it to all four full rows. Re-sort rows
of equal absolute row sum. The resulting solution has the representative
tuple. All lifts of the representative are searched, even if more than one
multiplier carries the original tuple to it. Multipliers permute the exact
eigenvalues. Transformed solution rows therefore still satisfy
$\lambda_x(k)^2\leq260$ and pass the numerical filter with its proved
margin.
\end{proof}
The stored enumeration uses the following label.
A \emph{unit} is one representative in this lemma. The cover check computes
the exact compressed tuples and verifies membership of their representatives
in the supplied unit list. It checks invalid and duplicate representatives
as well as missing ones.

A further symmetry reduces one row list in each unit. The subgroup
\[
 K=\{u\in(\Z/65\Z)^*:u\equiv1\pmod{13}\}=\{1,14,27,53\}
\]
fixes every compressed vector. Choose one designated position in the unit
and retain only rows whose mask is least in its $K$-orbit.
Applying a common element of $K$ that minimizes that row preserves a
solution in the same unit. It is essential that this restriction applies
to only one designated row; independent minimization of all four rows
would not be justified.

\begin{lemma}\label{lem:pair}
Every pair belonging to a solution in the four lists passes
\eqref{eq:pair} on both sides.
\end{lemma}
\begin{proof}
For its complementary rows $c,d$, equation~\eqref{eq:spectral} gives
$64(\lambda_a(k)^2+\lambda_b(k)^2)=Q-64\lambda_c(k)^2-64\lambda_d(k)^2$.
Replacing each square by the appropriate lower or upper enclosure proves
the inequalities before clamping. Raising a negative upper bound to zero
only weakens the upper test. Raising a negative lower bound to zero changes
nothing, because $h_a+h_b$ is nonnegative.
\end{proof}
If a list is empty there is no solution in the unit. The implementation details are given in Appendix~\ref{app:join}.
```

### Navigation in the journal-style edition

The opening guide above describes the earlier layout. In version 3,
Section 2 treats rows, autocorrelations and spectra; Section 3 gives
compression and the multiplier orbits; and Section 4 develops pair
filtering and product matching, followed by the proof of Theorem 1 in
Section 4.4. All five key lemmas and their proofs are in the main text.
Section 5 reports computational verification. Appendix A gives the
enumeration totals, Appendix B the numerical error bound, and Appendix C
the exact hashing and storage checks. The verbatim passages retained above
preserve earlier definitions and implementation explanations; their
original labels refer to the paper rather than to numbered sections of
this Markdown companion.

### Historical hardware and validation in version 3

The archived CPU enumeration used four ranges with 12-thread jobs and
recorded 271.326 CPU-hours; its processor models and full elapsed time
were not recorded. The primary GPU enumeration recorded 23.805 GPU-hours.
A separately written GPU implementation used four NVIDIA GB10 GPUs for
about 2.060 GPU-hours of search, or 2.143 GPU-hours including setup and
smaller-order checks. These are historical measures from different filters,
not a controlled performance comparison. The GPU sources are not part of
this CPU archive, and not all original primary GPU records were rechecked.

The paper's table through order 33 describes the archived unfiltered
baseline enumeration. The default checker uses row-sum grouping through
23 and also a single-row PSD filter at 25–33; `--full-controls` selects
the unfiltered baseline through 33 and discovery at 55. The full validation
at 55 discovers the solution with both compression factors 5 and 11
without supplying a witness. The existing commands above distinguish these
checks from the exhaustive order-65 search.

The verbatim historical passages above retain earlier source locators.
For Zhang, the current paper uses the Zenodo record description; the
earlier Section 7.4 locator was not independently confirmed.
