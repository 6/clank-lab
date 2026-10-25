# Checking notes for the concise and journal-style edition

These are previously reported checks and conventions, retained from the published version. No new mathematical computation or formal build was performed for this edition. The commands in [README.md](README.md) reproduce the checks. The mathematical statements below use the paper’s notation.

## Historical records and source access

```tex
The theorem is computer-assisted. Its scope is exactly these parameters
in this group. The mathematical reduction and its coverage are proved
in Lean; the exhaustive integer computations that reject the covered
leaves are external to Lean. Section~\ref{sec:formal} states this
boundary precisely.

Vera L\'opez and Garc\'ia S\'anchez undertook a systematic study of
abelian difference sets with $100<k\leq150$~\cite{VeraGarcia1997}.
Their Table~1, printed page~105, marks the present group and parameters
with a question mark, meaning unknown according to their convention on
page~101. That paper was published in 1997; the publisher gives
February~28, 1997. This supplies a published unresolved-status record,
without asserting that it was the first occasion on which the question
was asked.

Gordon's La Jolla Difference Set Repository has made such group-specific
questions accessible and maintained their connection with the
literature. In his presentation of August~3, 2019, Gordon singled out
the present case as the ``Smallest Open Case''~\cite[slide~38]{Gordon2019}.
Here slide~38 is physical PDF page~49. The repository's archived
version~1.3, dated April~24, 2026, also records the exact entry
$\operatorname{DS}(243,121,60,[3,9,9])$ as Open~\cite{GordonData}.
The entry has a status and an empty comment, with no per-entry date.
The archive date therefore does not date the original insertion or
last review of this entry. Similarly, the website's September~3, 2026
update label is a site-level date. The entry's original insertion and
last-review dates have not been recovered.

These are explicit applications and failures of hypotheses, not a
claim to have exhausted all uses of these methods. The historical
Open entries document the question; they cannot establish an
exhaustive priority claim. Some older originals, including Lander's
Theorem~4.38~\cite{Lander1983} and the Hall, Paley, and Lehmer works
cited for historical credit, were not read in full. Hall's survey is
not used to infer that a cyclic-group statement alone covers every
abelian hypothesis of the multiplier specialization.
Theorem~\ref{thm:main} rests on the
reduction and exhaustion given here, rather than on an inference
from an Open label or from the absence of a located earlier answer.
```

## Encoding and affine-map comparisons

```tex
Elements of $G$ are encoded by $81x+9y+z$, using the
least nonnegative coordinate representatives; elements of $Q$ by
$9x+3\bar y+\bar z$.

All these lifts have been checked on the full 243-point group
for bijectivity, translation in $H$, scalar commutation, and
additivity of the linear part on every generator edge.
The generator-edge identities imply additivity for arbitrary
pairs by telescoping along a coordinate-generator path.


Their chosen full-$G$ lifts preserve $S_0$, commute with the
scalar, and act consistently on every $K$-coset. These facts
are checked for the actual point maps, including full
pairwise additivity in the separate quotient-map check.
The chosen lifts need not themselves form a 27-element
subgroup of affine maps on $G$. The stabilizer of order three
on $H$ and the induced group of order~27 on $Q$ refer to
different actions; neither is asserted to be the full affine
stabilizer of $S_0$ on $G$.
```

## Lifting families and decoding

```tex
The local families have been checked independently of
the search tables: scalar orbits were reconstructed
from modular coordinates and all their required
subfamilies formed, then compared as sets with every
option emitted by each compiled search kernel.
A separate completeness check also enumerated all
three-point and six-point subsets of each nine-point
cell and tested scalar closure directly. Both checks
cover all $8\cdot24\cdot3=576$ labeled options and
the thirteen initial points. The comparison definition
comes from scalar fixedness and subset size, rather
than from treating an existing option table as complete.

Separate checks reconstruct every prefix's rank,
digits, and cylinder endpoints and compare them with
both complete decoder output streams. They check
all $N$ IDs and exact endpoints, not a sample or
aggregate length alone. The interval walk checks
that the first endpoint is zero, each start equals
the previous stop, and the last stop is $N$.
Those finite comparisons establish the contents of
the supplied decoder outputs; identifying the outputs
with executions of the intended compiled decoders is
an external provenance assertion, not a Lean theorem.

Production searches use the bound~60 and exclude
the relaxed-bound features used for controls.
```

## Complete independent lifting computation

```tex
A complete additional direct replay reproduced
every range. A separately written third lifting
kernel also exhausted all 1,038 ranges, matching
each range's validity, node, and solution counts
and the digest of its canonical per-prefix row
stream. That kernel has its own recursive
traversal, difference arithmetic, option
construction, ID decoder, and driver. Its
six-cell labeling convention was selected by
testing the two conventions against one range;
this fixes labels only. Permuting the labels
cannot add or remove a subset, and the complete
pass then matched every range.
```

## Completeness, controls and independence

```tex
Agreement of the production kernels alone
does not establish that their shared
decomposition is complete. The proof uses
the full local option-family comparisons,
the separately written exhaustive lifting
pass, the independent finite cover, and
the Lean coverage implication, in addition
to production agreement.

The finite cover checks exact equality of
the singleton sets and legal-map orbit,
the derived quotient set and covered
case orbits, every local option family,
all prefix cylinders, and the range
partition. Three semantic gap controls
exercise these obligations. One deletes
ID~4095 and compensates by duplicating
another ID while preserving the number
of interval records and their summed
length. A second duplicates one legal
option while retaining its cell and
cardinality. A third duplicates a case
of the same orbit size. Each is rejected
with a missing ID, subset, or quotient
image witness, respectively. Their
rejection does not rely on unchanged
file digests or aggregate counts.

Further mutation tests reject altered
scalar partitions, missing maps,
nonimages in the case list, and two
representatives from one quotient
orbit. Replacing a representative
by another member of its own orbit
is accepted, as it should be. An
altered range digest is rejected
by both fresh production kernels.
A changed node count, even with its
aggregate total updated consistently,
is rejected by fresh replay although
it passes the static consistency
check. These tests distinguish
semantic checking from integrity
and formatting checks.

There is a genuine positive discovery
control at parameters $(121,40,13)$
in $C_{121}$: three generic
implementations, without a supplied
witness, recover 88 multiplier-invariant
difference sets at 996,935 nodes.
These are invariant sets without
equivalence reduction. The same
parameters in $C_{11}^2$ give a
negative control; that negative
outcome is not positive discovery
evidence for the present search.

The actual order-243 ternary path
has additional positive controls.
Eight independently constructed
fixed 121-point sets, one in each
case, are supplied through forced
digit paths with relaxed test-only
bound $M=\max_{g\ne0}d_P(g)$.
Both production kernels recover
their exact points at their
specified depth-twelve IDs and
reject bound $M-1$:
\[
\begin{array}{c|r|r}
c&\operatorname{id}&M\\\hline
0&91{,}615&66\\
1&815{,}056&72\\
2&1{,}486{,}729&69\\
3&1{,}750{,}181&72\\
4&2{,}473{,}622&69\\
5&3{,}145{,}295&69\\
6&3{,}214{,}101&69\\
7&3{,}937{,}542&72
\end{array}
\]
For example, the case-zero word is
\[
\texttt{011122200011122200011122}.
\]
It has prefix ID~91,615 and $M=66$.
Each test returns one exact witness
and thirteen tail nodes. These are
bounded-count lifting and witness
controls, not $(243,121,60)$
difference sets: their bounds are
66--72. Neighboring IDs are checked
against their own reconstructed
sets; a neighbor is not assumed
to have no solution at a relaxed
bound. Tests of omitted options,
serialized continuation versus
uninterrupted execution, and
residual symmetries also agree.
Residual symmetries are used for
controls, not for reducing the
production search domain.

A separate 10,000-ID comparison
matches all per-ID rows between
the production kernels and an
additional coordinate-based
implementation. This is a sample
control and does not replace
the complete third-kernel pass
or prove coverage of a range.

The scope of independence is
specific. The compressed and
direct production kernels share
a compilation unit, task and
serialization code, prefix
convention, $S_0$, scalar-partition
and case inputs, cell order,
and option contents. Their
difference representations,
updates, and traversals differ;
they are not independent
derivations of the entire
reduction. The third complete
kernel shares no search or
certificate-driver code with
them, but reads the same
validated scalar-partition
and case files and uses $S_0$.
It reconstructs its own options
and validates orbit membership;
it does not itself discover
the singleton class or quotient
representatives.

Those common mathematical
inputs are instead validated
by separate programs that
regenerate scalar orbits,
enumerate all singleton
candidates, classify quotient
arrays in two different ways,
and check legal full-group
maps and exact case coverage.
Thus the evidence composes
independent input-completeness
checks with a complete separate
lifting exhaustion. A complete
search fed directly by a newly
self-generated chain of all
front-end data is not claimed.
The common mathematical
implications are justified by
the arguments and formalization,
not inferred from matching
search totals.
```

## Formal and executable correspondence; logical axioms

```tex
Equality of the Lean
leaf table with the
implemented search
options is also an
external comparison,
covering all 576 options
and thirteen singleton
points, strengthened by
the complete compiled
option dumps and separate
definition-based checks.
It is neither an omitted
hypothesis of
\texttt{coverage} nor a
formal proof of the C++
implementation, compiler,
or execution environment.
The finite cover's
decoder comparisons
likewise retain the
execution-provenance
boundary stated in
Section~\ref{sec:lifting}.

The recorded kernel
checks of the reductions
and conditional final
theorem use only
\texttt{propext},
\texttt{Classical.choice},
and \texttt{Quot.sound}.
Planted formal errors
are rejected: dropping
the last range, pruning
when a count reaches
$\lambda$ rather than
exceeds it, weakening
the exact leaf criterion
to $\lambda+1$, and
omitting an admissible
singleton survivor.
The first three false
statements also have
formal counterexamples.
These checks establish
the stated reduction
scope; they do not
turn the external
search into a
whole-theorem Lean
proof from the
definitions.
```

## Qualifications on comparisons with published restrictions

```tex
Turyn's character restrictions~\cite{Turyn1965} allow this application:
$\operatorname{ord}_3(61)=1$ is odd. At the nontrivial character
orders $3$ and $9$, the prime $61$ is not self-conjugate. Indeed, its
powers modulo $3$ equal $1$, and modulo $9$ cycle through $7,4,1$,
never $-1$. Obstructions requiring a common prime divisor of $n$ and
$v$ have no such prime here; in particular that ingredient of the
Lander-type restrictions in Leung--Ma--Schmidt~\cite{LeungMaSchmidt2004}
is absent. That comparison uses the stated common-prime setting,
without claiming a full reading of that paper's proof.
The multiplier theorem does apply and provides symmetry,
as proved in Section~\ref{sec:multiplier}; that symmetry alone is
not a nonexistence result.

For the field-descent function of Leung and
Schmidt~\cite[Definition~2.6]{LeungSchmidt2005}, one obtains
$F(9,61)=3$. Here $\operatorname{ord}_3(61)=1$ and
$61\not\equiv1\pmod9$, so the exponent $b_3=1$ is permitted in
that definition. Taking their factor $A$ to be the entire group and
the complementary factor trivial, Theorem~4.3 gives
\[
 \exp(G)\leq243\sqrt{\frac{3^2}{4\cdot61\cdot\varphi(3)}}
 =\frac{729}{\sqrt{488}}\approx33.0003,
\]
which permits exponent~9. Their Theorem~A cannot instead split off a
$C_9$ factor: its coprimality condition would require
$\gcd(9,\exp(C_3\times C_9))=1$, whereas this gcd is~9.
Theorem~4.1 requires a cyclic Sylow subgroup, also absent here.

Arasu and Ma's 2001 nonexistence result~\cite{ArasuMa2001} resolves
$C_9\times C_{27}$. The relevant theorem, as explicitly restated and
extended by Miller~\cite[Theorems~1 and~3]{Miller2025}, assumes
\[
 G=C_{p^e}\times J,\qquad e\geq2,\qquad
 \exp(\operatorname{Syl}_p J)<p^e.
\]
Splitting off $C_9$ in the present group leaves another $C_9$, so
the strict exponent inequality fails. The forbidden-multiplier
congruences would demand both $t\equiv4\pmod9$ and
$t\equiv1\pmod9$. Although the older numerical condition
$4(p-1)n=488>243$ holds, it cannot repair the failed group
hypothesis. This comparison uses Miller's restatement; the full
2001 original was not available for a complete reading.

Chen, Xiang, and Sehgal~\cite{ChenXiangSehgal1994} study skew Hadamard
abelian difference sets, which satisfy the additional partition
$G=\{0\}\mathbin{\dot\cup}D\mathbin{\dot\cup}(-D)$.
The present parameters do not supply this hypothesis. Consequently
a skew-only exponent bound cannot be applied to the ordinary
difference-set question. This scope distinction follows from the
published abstract; the full original was not obtained, and no
numerical specialization of its bound is needed here.

Recent work on signed difference sets by He and
Wu~\cite{HeWu2026} includes ordinary difference sets but does not
yield this exclusion by the criteria considered here. Their
Theorem~3.2 has the same failed self-conjugacy test for~61;
Theorem~4.2 requires even $v$; Theorem~4.4 requires $k=v-1$;
and Theorem~4.7 requires an elementary abelian group and a defect
bound, whereas this group is not elementary abelian and the defect
is $d=122>5$. Miller's and
He--Wu's cited versions are preprints, not claimed here as verified
journal publications.
```

## Range assertions and their formal packaging

```tex
These are 1,038 semantic
assertions. A receipt
formulation packages each
assertion as the
\texttt{clear} field of
$\operatorname{Receipt}(r,\operatorname{digest}_r)$;
the digest is only a
label, not additional
mathematical evidence.
Lean does not compute
SHA-256 here, interpret
C++ output, or derive
the assertions from
digest strings. The external
exhaustive computations
in Appendix~\ref{sec:search}
supply that part of the
computer-assisted proof.

```

## Affine maps and their linear parts

```tex
The affine
map $F$ need not fix zero; it is its linear part $A$ that is
a group automorphism.
```

## The quotient convention

```tex
This is an integer multiplicity array on $G/K$, not a subset
of $G$ and not an array on $G/H$.
```

## Symmetry and reported counts

```tex
No search count is
divided by one of these symmetry orders.
```

## Exact leaf checking

```tex
The direct kernel
also checks the exact leaf condition explicitly.
```

## Completion records

```tex
An explicit
completion state is required for each prefix;
an absent result, interruption, or partial
continuation is not evidence of exhaustion.
```

## Finite tables in the formal proof

```tex
The formal singleton proof
uses its own finite
classification: fourteen
layer-zero representatives,
64 layer-one shear classes,
52,220 patterns, and twelve
survivors with legal words
to $S_0$. These numbers
describe that classification,
not the 5,335,092-mask
enumeration in
\eqref{eq:maskcount}.
The quotient proof checks
all $2^{13}$ assignments
and the legal witnesses
to the eight actual
case rows. Generated
witness tables have their
required properties and
completeness checked in
the kernel; they are not
imported as axioms.
```

## Certificate comparisons

```tex
The compact computational certificate records
each interval and its counts and row-stream
digest. A static check verifies interval geometry
and consistency, while replay recomputes the
rows and compares their counts and digests.
The digest binds a comparison to a particular
row stream; it is not a proof of a universal
nonexistence assertion. The exhaustive executions
and their arithmetic and coverage checks supply
the external computational part of the proof.
```

## Singleton enumeration counts

```tex
This is a count of candidate singleton
subsets, not of difference sets or of all fixed 121-point sets.
```

## Allowed quotient multiplicities

```tex
The absence of
zero and nine is an enumeration result, not an assumption
used to exclude possible arrays.
```

## Centered and uncentered translates

```tex
It is a consequence of the classification, not an
additional unexplained pruning condition. For an
uncentered translate the distinguished thirteen-point
coset can move; $|D\cap H|=13$ is not asserted for an
arbitrary translate of the original difference set.
```

## Lifting family counts

```tex
The bijection does not require enumeration of all
these leaves. Different representative arrays give
disjoint families because their quotient arrays differ;
no assertion is made that all these leaves represent
distinct affine-equivalence classes.
```

## Traversal counts

```tex
These are traversal counts, not numbers of
inequivalent subsets or an assertion that all
$8\cdot3^{24}$ leaves were visited individually.
```

## Uniqueness in the coverage implication

```tex
This is an existence
statement; the normalizing
map or normalized
representative for the
original $D$ need not be
unique. The interval of
each ID is unique.
```

## Exact formal-statement locators

The theorem is `DS243.no_difference_set` in `lean/DS243/Main.lean`, lines 150–156. Its receipt-form hypothesis is equivalent to the range-assertion form displayed in the paper: `lean/Checks.lean`, lines 3525–3529, checks both statement types and `Receipt r s ↔ RangeClear r`. No formal source or build changed for this edition.

## Formal reduction scope

```tex
The formalization
proves the first-multiplier
specialization by the
classical group-ring argument,
as well as centering, the
index-three moments, the
singleton congruences,
legal normalizations,
quotient inversion, lifting,
pruning, and ID partition.
```

## Executable correspondence and source locations

```tex
The correspondence between the formal leaf table and the executable
options, and the exhaustive range assertions, are external checks.
The checking notes, including the logical axioms, are
\href{https://github.com/6/clank-lab/tree/difference-set-243-v3/results/difference-set-243}{\texttt{checks/edition-notes.md}}
and \texttt{checks/README.md} in the accompanying source bundle.
The pinned Lean development is in its \texttt{lean/} directory; the
bundle's README gives the reproduction commands.
```

## Difference-class implementation

```tex
All partial sets are unions of scalar orbits, so
$d_P(61g)=d_P(g)$. Reversing ordered pairs gives
$d_P(-g)=d_P(g)$ as well. There are 36 classes
outside $H$ under $g\mapsto\pm61^ig$, each of
size six, and thirteen nonzero classes inside $H$,
each of size two. Thus there are 49 nonzero
difference classes. The compressed kernel stores
the common count on each class and uses precomputed
option contributions. The direct kernel instead
adds and removes points and maintains the full
elementwise difference vector. Compression is
justified by constancy of contributions on these
classes, rather than by averaging counts.
```

## Production comparison conventions

```tex
The two production passes agree on the complete
ordered rows of ID, prefix-validity, node count,
and solution count for all 4,251,528 IDs,
and on node counts in every
one of the 1,038 ranges. With their common node-count
convention, the totals are
```

## Size of the lifting families

```tex
There are $3^{24}=282{,}429{,}536{,}481$ syntactic
leaves per case before difference-count pruning.
```

## Certificate completeness records

```tex
A prefix rejected before depth twelve must still have
an explicit completed record; pruning is not a reason
to omit its ID from the partition.
```

## Published coverage statement and its hypotheses

```tex
In particular,
\texttt{coverage} proves the
following implication, with
no hypotheses about outputs
of a finite enumerator or
of a search: if $D$ is a
difference set, then there
exist $u\in G$, a word $w$
of legal affine maps, an
integer $r<1038$, an
$\operatorname{id}\in I_r$,
and a twelve-digit tail
$\boldsymbol t$ such that
\begin{equation}\label{eq:coverage}
 F_w(D-u)=\mathcal L\left(
 \left\lfloor\frac{\operatorname{id}}{531441}\right\rfloor,
 \operatorname{digits}(\operatorname{id},\boldsymbol t)
 \right).
\end{equation}
Here the first twelve digits
are the leading-zero-preserving
base-three expansion of
$\operatorname{id}\bmod531441$
and the last twelve are
$\boldsymbol t$. The map
$F_w$ is an additive
automorphism followed by a
translation in $H$.
This is an existence
statement; the normalizing
map or normalized
representative for the
original $D$ need not be
unique. The interval of
each ID is unique.
```
