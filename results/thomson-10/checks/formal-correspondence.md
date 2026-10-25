# Formal definitions and checking details

The following source correspondence and implementation notes accompany the
journal-style edition. Mathematical expressions in the retained notes use
LaTeX notation; the Lean and checking guides give executable commands.

The current certificates are in [the authenticated published bundle](<https://github.com/6/clank-lab/tree/e987408cf2d4c27c6e0c10d9f1a522ce3156c632/results/thomson-10>).
The polynomial coefficients and candidate upper bound are `hCoeff` and
`certU` in `lean/ThomsonN10/Data.lean`; the fixed factor matrices are
embedded in the Lean certificate sources and `data/certificate.json.gz`.
[Checking instructions](README.md) and the [Lean guide](../lean/README.md)
give the commands, exact inputs, dependency versions and historical timings.
These certificates are unchanged in this edition.

The retained source-access limitations also remain: the original Yudin,
Andreev and Delsarte–Goethals–Seidel papers were not consulted; their roles
are attributed through the cited Cohn–Kumar, Bachoc–Vallentin and Cohn–Woo
texts. Unsuccessful publisher-metadata requests for Schwartz and Föppl are
not successful source reads. Schwartz is cited in the authenticated arXiv
version; no unchecked journal metadata is added. Erber's direct PDF access
failed, while the retained Fermilab primary text was available; the journal
Table1 was not inspected. The Cambridge capture's access date was not
independently authenticated. The nine-point original upstream archive was
not supplied with its public copy. No unsuccessful or excluded provider
was retried for this edition, and none of these gaps is treated as verified.

The following blocks retain exact historical TeX excerpts for comparison;
they are source records rather than Markdown exposition.

```text
This appendix identifies the formal statements, certificates and
independent computations behind the preceding argument. The distribution
contains a normal Lake project, rational certificates and a checker using
Python's standard library. The Lean theorem begins with the definitions of unit sphere,
injectivity, Coulomb energy and congruence; no numerical optimization
output is treated as an axiom. The final theorem combines the root proof, pair separation, three-point
bound, polynomial lower bound, the slack bound outside the seven windows,
classification of the interval patterns and quantitative local energy
inequality described above.
The formal trust base is the Lean kernel and the three axioms printed
below, together with the faithful match between its statement and
Theorem~\ref{thm:main}. Paths beginning with \texttt{lean/} or
\texttt{checks/} are relative to the bundle root. Other Lean source paths
below are relative to \texttt{lean/ThomsonN10/}.

\paragraph{Checking artifacts.}
The project uses Lean~4.34.1. Its Mathlib revision is
\begin{center}\texttt{d13f23b723b8a846827a245b89c10fc7d3f11612}.\end{center}
Both dependencies are pinned by the included toolchain and manifest.
The build checks the theorem statements and the following
\texttt{\#print axioms} outputs. Any change to an axiom list makes the
build fail:
\begin{quote}\small\ttfamily
'ThomsonN10.thomson\_ten\_complete' depends on axioms:\\
{}[propext, Classical.choice, Quot.sound]\\[3pt]
'ThomsonN10.candidate\_admissible' depends on axioms:\\
{}[propext, Classical.choice, Quot.sound]\\[3pt]
'ThomsonN10.Cert.L1.Data.residual\_agrees\_JSON' depends on axioms:\\
{}[propext, Classical.choice, Quot.sound]
\end{quote}
Neither \texttt{native\_decide} nor \texttt{ofReduceBool} is used in the
included Lean proof, including the decompressed certificate source.
In particular, no native-computation axiom occurs in the printed
transitive dependencies of the final theorem. These are the standard Lean
axioms for propositional extensionality, classical choice and quotients.

The standard-library Python checker is an independent implementation
that checks the same rational three-point certificate used by Lean.
It expands the kernel and weighted-square polynomials from their definitions, checks
the factor matrices and all 274 residual coefficients, bounds their total
absolute error, and checks the candidate-energy upper bound over the
entire height interval. The command \texttt{python3 -I checks/check.py}
also runs eight corruption tests, all of which are rejected: it changes
entries in each kind of factor matrix, a minorant coefficient, the
candidate upper bound, row exponents, row exponents together with the
residual, a residual entry, and the residual norm. The Python implementation does not check the scalar minorant,
the slack bound outside the windows, exhaustive passage from spherical
configurations to interval patterns, window classification, full stationarity,
orthogonal alignment or local Hessian argument; those obligations are
proved by Lean. Its precise inputs and obligations are documented in
\texttt{checks/README.md}. Independence here concerns the implementation
of the shared certificate checks, not a second independent proof of every
step of the global theorem.





The root argument in Section~\ref{sec:candidate} is formalized in
\nolinkurl{Param/Root.lean}.
\nolinkurl{Param/Final.lean} identifies those functions and
endpoints with \texttt{stationarity}, \texttt{heightLower} and
\texttt{heightUpper}. It proves
\nolinkurl{ParameterExistsUnique_holds}.



The following are the definitions in \texttt{Basic.lean}, with the
mathematical glyphs typeset:


The challenge declarations in
\texttt{lean/Challenge.lean} are:


The identities and
harmonic expansion are in \nolinkurl{Cert/LP/Data.lean}; the scalar
inequalities are in \nolinkurl{Cert/LP/Scalar.lean}. The sum bound and
separation conclusion are in \nolinkurl{Cert/LP/Proof.lean}. The letter
$g$ here denotes the polynomial called \texttt{h} in those files.



The recurrence and projection argument are in
\nolinkurl{Cert/SDP/CircleKernel.lean} and
\nolinkurl{Cert/SDP/ProjectionComplex.lean}; the symmetrization and
correction are in \nolinkurl{Cert/SDP/FactoredKernels.lean}.



The candidate upper bound is verified by
\nolinkurl{Cert/CandidateUpper.lean}.



These weights are \texttt{domainWeight} in
\nolinkurl{Cert/SDP/CertificateBound.lean}.



The certificate stores 20 matrices of factors: eight nonzero matrices
for the three-point kernels (called moment blocks in the data), and twelve
for the weighted squares (called sum-of-squares blocks). It has 42,950
integer entries and 274 residual coefficients; two zero moment blocks
are omitted. Its compressed JSON file is 1,246,399 bytes and expands to
2,670,249 bytes. Expanding these factors and bounding the coefficient
sum are exact rational calculations. The identity is
\nolinkurl{Cert.L1.l1_hidentity}; its summation is
\nolinkurl{Cert.SDP.factored_certificate_pair_bound}.



The finite certificate treats
84 sorted anchor-color triples, of which 43 are eligible. It contains
14,749 norm tests, 79 extension records and 1,960 pair-color tests. Its
nine seven-clique witnesses each give a bijective relabeling to the same
reference interval pattern. The count is of witnesses in the enumeration,
not of incongruent ten-point configurations.

The interval-pattern conclusion is the theorem
\nolinkurl{Windows.WindowClassification_holds}.



The soundness proof is in \texttt{Scalar/Checker.lean};
\texttt{Scalar/Bridge.lean} carries out the substitution and
\texttt{Scalar/Exterior.lean} proves the slack bound outside the windows.

The compressed JSON file is input to the independent Python checker.
Lean uses the corresponding coefficient tables as literal Lean data;
it does not parse that JSON file during proof checking.
The theorem \texttt{residual\_agrees\_JSON} equates the residual computed
from those factors with the literal polynomial \texttt{JSONResidual}
exported from the supplied table. The Python checker separately verifies
the external JSON residual and its coefficient norm.
The compressed file \texttt{AmbientKernelData.lean.gz} contains Lean
source for the Hessian certificate, not JSON. The build expands that
source before importing it; all its assertions are then kernel-checked.
No proof generator is run as a trusted build step.



In \nolinkurl{Local/Certificates/AmbientKernelBounds.lean},
the theorem \texttt{flattened\_posDef} proves positive definiteness.

The theorem that proves~\eqref{eq:psd} for the explicitly defined
Hessian is listed below its source file. The last line is the Lean
namespace prefix for both this theorem and \texttt{flattened\_posDef}:
\begin{quote}\small\ttfamily
Local/Certificates/AmbientHessian.lean\\
candidate\_augmented\_hessian\_posSemidef\\
ThomsonN10.Local.Certificates.AmbientKernel
\end{quote}



The stationarity calculation in Section~\ref{sec:local} has the following
formal correspondence. In \nolinkurl{Local/LocalStationarity.lean},
\texttt{candidate\_force\_relation} converts that derivative equation to a
linear relation among the seven inverse-cube distance weights. The
identity \nolinkurl{orbit_force_balance} checks all force components and uses this relation
to make each point's force radial;
\nolinkurl{candidate_force_eq_radialCoefficient} identifies the multiplier
with the exact spherical radial coefficient. This proves stationarity
for arbitrary tangent perturbations at all ten points.


The script
\nolinkurl{checks/energy_enclosure.py} performs this computation and prints
the two endpoints in the energy remark in Section~\ref{sec:energy}. Lean proves that the
height interval $[a,b]$ contains its unique stationary root; Python uses the interval as input and does not
prove root existence or uniqueness.



\subsection{Code and cutoff provenance}\label{app:provenance}
The original code attribution, historical comparisons and cutoff account
are retained in \nolinkurl{checks/context.md}; the file-level credits and
full MIT notice remain in \nolinkurl{THIRD_PARTY.md}.


```

## Additional mathematical conventions

Retained exact mathematical passages from the preceding edition.

```text
\paragraph{Checking artifacts.}
The project uses Lean~4.34.1. Its Mathlib revision is
\begin{center}\texttt{d13f23b723b8a846827a245b89c10fc7d3f11612}.\end{center}
Both dependencies are pinned by the included toolchain and manifest.
The build checks the theorem statements and the following
\texttt{\#print axioms} outputs. Any change to an axiom list makes the
build fail:
\begin{quote}\small\ttfamily
'ThomsonN10.thomson\_ten\_complete' depends on axioms:\\
{}[propext, Classical.choice, Quot.sound]\\[3pt]
'ThomsonN10.candidate\_admissible' depends on axioms:\\
{}[propext, Classical.choice, Quot.sound]\\[3pt]
'ThomsonN10.Cert.L1.Data.residual\_agrees\_JSON' depends on axioms:\\
{}[propext, Classical.choice, Quot.sound]
\end{quote}
Neither \texttt{native\_decide} nor \texttt{ofReduceBool} is used in the
included Lean proof, including the decompressed certificate source.
In particular, no native-computation axiom occurs in the printed
transitive dependencies of the final theorem. These are the standard Lean
axioms for propositional extensionality, classical choice and quotients.

The standard-library Python checker is an independent implementation
that checks the same rational three-point certificate used by Lean.
It expands the kernel and weighted-square polynomials from their definitions, checks
the factor matrices and all 274 residual coefficients, bounds their total
absolute error, and checks the candidate-energy upper bound over the
entire height interval. The command \texttt{python3 -I checks/check.py}
also runs eight corruption tests, all of which are rejected: it changes
entries in each kind of factor matrix, a minorant coefficient, the
candidate upper bound, row exponents, row exponents together with the
residual, a residual entry, and the residual norm. The Python implementation does not check the scalar minorant,
the slack bound outside the windows, exhaustive passage from spherical
configurations to interval patterns, window classification, full stationarity,
orthogonal alignment or local Hessian argument; those obligations are
proved by Lean. Its precise inputs and obligations are documented in
\texttt{checks/README.md}. Independence here concerns the implementation
of the shared certificate checks, not a second independent proof of every
step of the global theorem.



\subsection{The exact height interval}\label{app:interval}
This subsection supplies the exact root interval and derivative formula.
For the rational height interval used in Section~\ref{sec:candidate},
let $A$ and $D$ be the integers specified below, with $D$ the denominator.
Its endpoints $a,b$ are defined by
\[
 a=A/D,\qquad b=(2A+1)/(2D),
\]
{\scriptsize
\begin{align*}
 A&=513213568640798381215999065069135718731748351905698829816800875926548421101580455514066781,\\
 D&=2^{283}\cdot5^7.
\end{align*}
}
For the explicit stationarity equation, set
\[
 u_-(h)=2-\sqrt2+(2+\sqrt2)h^2,\qquad
 u_+(h)=2+\sqrt2+(2-\sqrt2)h^2.
\]
The derivative of the family energy is
\begin{align}
 S(h)={}&\frac{(4\sqrt2+2)h}{(1-h^2)\sqrt{1-h^2}}
 -\frac{8(2+\sqrt2)h}{u_-(h)\sqrt{u_-(h)}}
 -\frac{8(2-\sqrt2)h}{u_+(h)\sqrt{u_+(h)}}\nonumber\\
 &+\frac8{(2-2h)\sqrt{2-2h}}-\frac8{(2+2h)\sqrt{2+2h}}=F'(h).
 \label{eq:stationarity}
\end{align}
```

## Additional source and verification notes

The following unchanged passages supply details relocated from the paper.

```text
The recorded standalone build took about 33 minutes with two compiler
threads, using Mathlib's cache and artifacts from an interrupted setup;
the processor model was not recorded. About 10 GiB of RAM and swap is
recommended. The Python check finishes in seconds. The accompanying
README gives pinned dependencies and reproduction commands.


The historical reference is Thomson's 1904 paper~\cite[p.~237]{thomson},
whose opening specifies the ``motion of a ring of $n$ negatively
electrified particles''. For the general question, Cohn and Woo~\cite[Section~1.1]{cohnwoo}
use the phrase ``potential energy minimization''. Here the metric space
is the unit sphere and the potential is inverse distance.
This work builds directly on Aravind Karthigeyan's AI-generated
nine-point project~\cite[README]{n9}.
Its stated ``global optimality and uniqueness for nine distinct points''
is for the $D_{3h}$ tricapped trigonal prism on the unit sphere, with
equality up to orthogonal transformation and permutation.
We reuse most of its MIT-licensed Lean code and follow its proof design:
the statement structure, three-point certificate checks, Bernstein
inequalities, interval classification, orthogonal alignment, higher-order
error bound and interval Hessian method. The new inputs are the ten-point
energy, interval-classification and Hessian certificates. The hardest step
is the three-point energy certificate: its error must be small enough to
force geometric localization. The interval centered at $-1$ contains
the antipodal pole pair; a five-point counting argument supplies the
linearly independent triple needed for classification.



Neither is a premise here. We share the cutoff $32.717$; whether our
choice was independent or taken from that work cannot be established.

In the data, a \emph{norm test} is the four-by-four Gram-determinant
interval test for one proposed node; an \emph{extension record} stores
one retained node. A \emph{pair-color test} checks the cross-Gram
determinant for two nodes and a proposed pair color. A
\emph{seven-clique witness} is the color-preserving candidate labeling
for seven compatible nodes and the three anchor points.



No exact-sharpness assertion is inferred from these small numbers.
```

## Source mapping for the fixed data and local estimates

The polynomial coefficients `hCoeff` and the upper bound `certU` are in
[`Data.lean`](../lean/ThomsonN10/Data.lean).
[`GramStability.lean`](../lean/ThomsonN10/Local/GramStability.lean), especially
`triangular_scalar_stability`, proves the scalar product, square-root and
quotient perturbation estimates with rational constants.
[`GramAlignment.lean`](../lean/ThomsonN10/Local/GramAlignment.lean) transfers
them through the coordinate recovery and minimizing orthogonal alignment.
These are symbolic perturbation estimates, rather than a separate interval
certificate for the conditioning argument.
The pair remainder inequality is `pair_potential_algebraic_lower` in
[`LocalPotential.lean`](../lean/ThomsonN10/Local/LocalPotential.lean).

```text
Neither is a premise here. Both use the cutoff $32.717$; the checking
guide records the provenance of its use here.
```

## Figure description

Exact detailed caption retained from the preceding edition:

```text
The candidate $p(h_*)$. Left: a side view of the ten points and
the edges of their convex hull, hidden edges dashed. The poles $p_0,p_1$
are red, the upper square $p_2,\ldots,p_5$ at height $h=h_*$ is blue, and
the lower square $p_6,\ldots,p_9$ at height $-h$ is orange; the dashed
ellipses are the equator and the two circles of latitude. Right: the view
from above, in which the lower square (dashed) is the upper square rotated
by $\pi/4$. A label $i$ marks $p_i$.
```

## Logical foundations and recorded runtime

The exact declaration names for the logical principles stated in the paper
are retained here with the existing recorded timing:

```text
The permitted axioms are \texttt{propext}, \texttt{Classical.choice} and
\texttt{Quot.sound}; no native-computation axiom is used.
A partially cached two-thread build took about 33 minutes; its processor
model was not retained. The Python check takes seconds.
```

This is existing authenticated evidence, not a new build or calculation.
The processor model and an empty-cache benchmark remain unavailable.

## Preserved assembly and notation details

The following original exposition records the same theorem assembly and notation; the full argument now appears in the main paper.

```tex
Let $m$ and $\mathcal R$ be the polynomial minorant and residual specified
in Section~\ref{sec:global}, let $U$ be the fixed rational upper bound in
Appendix~\ref{app:certificates}, and put
$L=45(2^{-130}+\|\mathcal R\|_1)$.
Here $\|\mathcal R\|_1$ is the sum of the absolute values of the residual's
rational coefficients. This calligraphic $\mathcal R$ is distinct from the
matrix $R$ of infinitesimal rotation directions in Section~\ref{sec:local}.

\subsection{Assembly of the estimates}
The root assertion and candidate admissibility follow from
Section~\ref{app:candidate}.
For a competitor of energy at most $\E(p)$, a two-point bound first gives
$\langle x_i,x_j\rangle<13/20$ for distinct indices. A degree-16 polynomial
minorant and a rational three-point certificate bound the total pairwise
slack (pair energy minus its polynomial lower bound) by $L<10^{-30}$. Outside seven intervals of radius
$\delta=10^{-10}$ around the candidate's inner products, even one pair's
slack would be at least $10^{-30}$.
A count of the ten triangles on five points produces a linearly independent
triple. Each remaining point is assigned three intervals according to its inner
products with that triple. Vanishing four-by-four Gram determinants constrain the
assignments for a point and for each pair; the finite classification verifies
a candidate labeling that preserves all surviving pair intervals.
Orthogonal least-squares
alignment then gives total displacement
$\rho=(\sum_i\|y_i-p_i\|^2)^{1/2}\leq10000\delta=10^{-6}$
for the aligned configuration $y$.
Full spherical stationarity, a constrained-Hessian bound and a cubic
remainder estimate give $\E(y)-\E(p)\geq\rho^2/200$ for an aligned
configuration with $\rho\leq10^{-3}$. Hence $\rho=0$.
Sections~\ref{sec:global} and~\ref{sec:local} give every reduction.
Orthogonal transformations and relabeling preserve energy, giving the
converse equality implication as well.

```

```tex
We reuse most of its MIT-licensed Lean
code and its proof design: three-point bounds, Bernstein inequalities,
interval classification, orthogonal alignment and interval Hessian
estimates.
```

## Relocated source wording and checking locators

The journal-style edition moves the supplementary archive locator here.
The source wording below also retains the preceding contribution descriptions
and the original location-reference wording; exact source quotations and
pinpoints are now adjacent to the paper's credit. Mathematical statements
and checked dependencies are unchanged.

```tex
The \href{https://github.com/6/clank-lab/tree/thomson-10-v6/results/thomson-10}{version 6 supplement}
contains the formalization, certificates and reproduction instructions,
including the guide \emph{Independent certificate check}.

where\linebreak
$U\approx

Appendix~\ref{app:certificates} gives its exact value.

Third, the sum $\|\mathcal R\|_1$

Appendix~\ref{app:certificates} gives the triple-to-pair averaging and
explains the factor 45 in $L$.

Let $g$ be the quartic polynomial specified in
Appendix~\ref{app:separation}.

in Section~\ref{sec:energy}.

These blocks specify the sphere-constrained second variation, including
the radial correction.

error bound and interval Hessian method.

Nearby Lean work includes Tran's seven-point proof~\cite{n7},

\nolinkurl{thomson_seven} and \nolinkurl{thomson_seven_unique}~\cite{n7},

The earlier cases include F\"oppl's stability results~\cite[p.~190]{foppl},

Delsarte--Yudin linear programming; here the error is small enough to
```

```tex
This calligraphic $\mathcal R$ is distinct from the
matrix $R$ of infinitesimal rotation directions in Section~\ref{sec:local}.

Let $H(h)$ be the $30\times30$ matrix given by the following blocks at
$p(h)$,

The proof depends on Lean as described in
Section~\ref{sec:verification}.
```

```tex
This is the ten-point case of the energy-minimization problem associated
with Thomson's atomic model~\cite[p.~237]{thomson}.
```

```tex
The
corresponding formal lemmas are listed in Appendix~\ref{app:local}.

The independent Python implementation checks the same rational
three-point certificate.
```

## Attribution quotation and source-locator repair

The README section “Verification In Brief” describes the SDP, Bernstein,
Gram-rigidity, alignment and Hessian components. It is not a pinpoint for
the whole previously accepted reuse account, especially statement shape and
the higher-order error estimate. That account remains the author's
description of the actual MIT-licensed reuse; it does not attribute those
words to the README. The frozen Challenge header separately records the
shared statement shape. The nine-point upstream source-chain access gap
remains disclosed; no new upstream acquisition or replay was performed.

The source excerpts below preserve preceding wording and record the
quotation/pinpoint repair. Protected mathematical statements are unchanged.

```tex
F\"oppl's ``stabile arrangements~\cite[p.~190]{foppl}

sphere~\cite[Opening]{n7}

Our three-point bound uses Bachoc and Vallentin
and Cohn and Woo. We build directly on its proof design

Aravind Karthigeyan's AI-generated Lean proof establishes global
optimality and uniqueness of the tricapped trigonal prism for nine
distinct points on the unit sphere.

error bound and interval Hessian method~\cite[Verification In Brief]{n9}.

Concurrent ten-point Lean work by \texttt{saberwatchmanga} (formerly
\texttt{terry2418}) includes the ten-point posting~\cite[README]{concurrent},
local minimality~\cite[Status]{concurrentlocal} and a chord
restriction~\cite[Opening]{concurrentchord}; its README
states ``Global minimality is not proved.''
Neither is a premise here.

The following coordinates and energy formula specify the candidate in
Theorem~\ref{thm:main}.

His seven-point README calls
```

The following exact formal dependency locators accompany the mathematical
local argument in the paper; they are checking-note material.

```tex
The formal theorem \texttt{candidate\_augmented\_hessian\_posSemidef}
identifies this bound with the constrained Hessian above.

The formal lemmas are \texttt{candidate\_force\_relation},
\texttt{orbit\_force\_balance} and
\texttt{candidate\_force\_eq\_radialCoefficient}.
```

```tex
The minimizer is the tricapped trigonal prism.
```

## Bibliographic display names

The journal-style edition gives the exact retained README headings for the
root concurrent posting, N=8 warrant, five-point Riesz project and separate
local/chord projects. The previous project identifiers, dates, authors,
source URLs and versions remain. The seven-point Zarco title, including
“(Conjecture 1 of Armentano et al.)”, is unchanged. Earlier display wording
is retained below for comparison; these are citation metadata changes,
not changes to the mathematical statements or checked artifacts.

```tex
\bibitem{concurrent}
\texttt{saberwatchmanga} (formerly \texttt{terry2418}),
Lean-verified local minimality for ten charges on a sphere
(October 7, 2026), and A Lean-checked distance restriction for ten charges
on a sphere (October 11, 2026).
\url{https://github.com/saberwatchmanga/-lean-finite-certificates}.
October 7 posting, root README, revision \texttt{7ba9eb3}:
\url{https://github.com/saberwatchmanga/-lean-finite-certificates/blob/7ba9eb38db36c9cb957ff26758b66bbacc31d8bc/README.md}.


\bibitem{n8warrant}
J. Tooby-Smith and A. Zughaid, A warrant for the N=8 Thomson problem, in Lean4,
README, revision \texttt{2c35d62}, September 2026.
\url{https://github.com/jstoobysmith/Thomson-N-8-Warrant/blob/2c35d62e07d72686931da4bc3e062d668e858eda/README.md}.


\bibitem{zarco5}
A. Zarco (\texttt{alejandrozarco}), \texttt{five-points-riesz},
README, revision \texttt{aeb4588}, October 2026.
\url{https://github.com/alejandrozarco/five-points-riesz/blob/aeb4588ccbb1ccb91c315fedeb79a18042b5fe13/README.md}.


\bibitem{concurrentlocal}
\texttt{saberwatchmanga} (formerly \texttt{terry2418}),
\texttt{Thomson10LocalMinimum}, README, revision \texttt{7ba9eb3}, October 2026.
\url{https://github.com/saberwatchmanga/-lean-finite-certificates/blob/7ba9eb38db36c9cb957ff26758b66bbacc31d8bc/Thomson10LocalMinimum/README.md}.


\bibitem{concurrentchord}
\texttt{saberwatchmanga} (formerly \texttt{terry2418}),
\texttt{Thomson10Chord1935}, README, revision \texttt{bc74bc0}, October 2026.
\url{https://github.com/saberwatchmanga/-lean-finite-certificates/blob/bc74bc050f4c39123e894b3fd3873ba17f60289a/Thomson10Chord1935/README.md}.

```

The paper now links its first reference to the checking guide directly to
the public guide. The prior visible wording is unchanged:

```tex
The classification is proved in Lean; the checking guide identifies its
certificate and formal soundness statement.
```


## Preceding abstract and attribution wording

Retained exact excerpts preceding the source-scope clarification. These are
historical wording, not a claim that the paper still uses them.

```tex

Aravind Karthigeyan's AI-generated Lean proof establishes ``global
optimality and uniqueness for nine distinct points on the unit sphere''.
The minimizer is the ``tricapped trigonal prism''. Bachoc and Vallentin and Cohn and Woo supply the three-point positivity
bounds used here. We build directly on this nine-point proof's design
and reuse most of its MIT-licensed Lean code to settle the ten-point case
of Thomson's problem: the bicapped square antiprism uniquely minimizes
Coulomb energy, up to orthogonal transformations and relabeling.
Its height is the unique critical point in a specified rational interval.
The new inputs are the ten-point energy, interval-classification and
Hessian certificates. A three-point semidefinite bound confines every
competitor of no greater energy to the candidate's inner-product pattern;
orthogonal alignment and a quantitative local energy inequality then
force congruence. Here the pattern consists of short
inner-product intervals, whose coherent assignment is established by finite
Gram-determinant classification.
Lean checks the complete optimality and equality theorem
from the definitions. A separate Python implementation verifies the
rational three-point certificate.
Thomson's atomic model appears in ``On the structure of the atom''~\cite[p.~237]{thomson}.
Karthigeyan's nine-point Lean proof~\cite[README]{n9} establishes
``global optimality and uniqueness for nine distinct points'', for the
$D_{3h}$ tricapped trigonal prism. We reuse most of its MIT-licensed Lean code and follow its proof design:
the statement structure, three-point certificate checks, Bernstein
inequalities, interval classification, orthogonal alignment, higher-order
error bound and interval Hessian method. The new inputs are the ten-point certificates. The hardest
step is obtaining a three-point bound accurate enough to force geometric
localization.

The earlier cases include F\"oppl's ``stabile'' arrangements~\cite[p.~190]{foppl},
Yudin's simplex and cross-polytope optima and Andreev's icosahedron,
as credited by Cohn and Kumar~\cite[Section~1]{cohnkumar}; see also
\cite{yudin,andreev}. Schwartz proved the five-point case~\cite[Theorem~1.1]{schwartz}.
The numerical ten-point predecessors are Erber and Hockney~\cite[Table~1]{erber}
and Wales and Ulker~\cite{cambridge}.

Bachoc and Vallentin~\cite[Section~1]{bachoc} credit the ``LP method'' to
Delsarte, Goethals and Seidel~\cite{delsarte}. Cohn and
Woo~\cite[Section~1.1]{cohnwoo} state that its energy application was
``first carried out for energy minimization by Yudin''~\cite{yudin}.
Our three-point bound uses Bachoc and Vallentin~\cite[Corollary~3.5]{bachoc}
and Cohn and Woo~\cite[Theorem~5]{cohnwoo}.

Nearby Lean work includes Tran's ``pentagonal bipyramid is the lowest-energy way to place seven electrons on a sphere''~\cite[Opening]{n7},
Kryvonos, Liehr and Taylor's eight-point theorem~\cite[Theorem~1.1]{n8},
Tooby-Smith and Zughaid's eight-point formal verification
project~\cite{n8warrant}, and Zarco's five-point and seven-point formal
verification projects~\cite{zarco5,zarco7}.
Concurrent ten-point Lean work by \texttt{saberwatchmanga} (formerly
\texttt{terry2418}) includes local minimality~\cite[Status]{concurrentlocal} and a chord
restriction~\cite[Opening]{concurrentchord}. Neither is a premise here.
The ten-point posting's README~\cite[README]{concurrent}
states ``Global minimality is not proved.'' We share the cutoff $32.717$; whether our choice was independent or taken
from that work cannot be established. Appendix~\ref{app:related} gives the
precise comparisons.

The proofs, the Lean formalization, the certificate checkers and the text
were produced by AI models (from OpenAI and Anthropic), working under the
author's direction. This work is checked in Lean from the definitions and
has not yet been reviewed by experts.


```


## Scope of the nine-point reuse account

The pinned nine-point README states its result and generation credits. Its
proof-method paragraph names rational three-point SDP certificates, Bernstein
minorants, Gram-pattern rigidity, alignment and an augmented-Hessian bound.
Our more detailed list describes the code we reused, including statement
structure and the higher-order error estimate. The upstream source archive
was unavailable for independent source comparison; those two reuse items
are not verified against that archive. This access gap is retained, and no
new acquisition, retry or mathematical execution was attempted.


## Complete published proof-overview and scope excerpts

These are exact excerpts from the corrected published version. Commands
and historical checking instructions describe the accepted artifacts; this
edition does not rerun them.

```tex
No symmetry is assumed of competitors. The candidate has two poles and
two squares at opposite heights, rotated by $\pi/4$ (Figure~\ref{fig:antiprism}).
Optimizing its height alone would not exclude asymmetric competitors.

\paragraph{Proof overview.}
For a competitor of energy at most $\E(p)$, a two-point bound first gives
$\langle x_i,x_j\rangle<13/20$ for distinct indices. A degree-16 polynomial
minorant and a rational three-point certificate bound the total pairwise
slack (pair energy minus its polynomial lower bound) by $L<10^{-30}$. Outside seven intervals of radius
$\delta=10^{-10}$ around the candidate's inner products, even one pair's
slack would be at least $10^{-30}$. A finite Gram-determinant classification
forces a common interval pattern after relabeling. Orthogonal least-squares
alignment then gives total displacement
$\rho=(\sum_i\|y_i-p_i\|^2)^{1/2}\leq10000\delta=10^{-6}$
for the aligned configuration $y$.
Full spherical stationarity, a constrained-Hessian bound and a cubic
remainder estimate give $\E(y)-\E(p)\geq\rho^2/200$ for an aligned
configuration with $\rho\leq10^{-3}$. Hence $\rho=0$.
Appendices~\ref{sec:global} and~\ref{sec:local} give every reduction.

\paragraph{Checked scope and reproduction.}
Lean proves the root assertion, candidate admissibility, global optimality
and the entire equality equivalence from the definitions; all certificate
obligations are discharged. The trust base is the Lean kernel, the standard
axioms \texttt{propext}, \texttt{Classical.choice},
\texttt{Quot.sound}, and
the match between the formal definitions and the statement above. There is
no native-computation axiom. The independent Python implementation checks
the same rational three-point certificate and rejects its corruptions; it
does not independently prove the geometric or local arguments. Its decimal
energy enclosure and figure check are supplementary, outside the Lean
theorem. The figure is drawn from the Lean
definition of the candidate by \nolinkurl{checks/draw_antiprism.py}, which
checks that the drawn points are the candidate's; it is not part of the
proof.
Appendix~\ref{app:formal} specifies these boundaries.

With elan, Git, gzip and Python 3.10 or later installed, run from the
result folder:
\begin{verbatim}
cd lean
lake exe cache get
lake build
cd ..
python3 -I checks/check.py
\end{verbatim}
The toolchain and dependencies are pinned. The guides in
\nolinkurl{lean/README.md} and \nolinkurl{checks/README.md} give memory
requirements and the certificate inputs.

\clearpage
\begin{appendices}

```

```tex
The argument combines global energy bounds with local uniqueness.
```


```tex
Upstream archive comparison remains unavailable (Appendix~\ref{app:related}).
```


```tex
Nearby formal work includes Hung Tran's AI-assisted seven-point
```


## Complete published attribution excerpt

```tex
\paragraph{Context and contribution.}
The historical reference is Thomson's 1904 paper~\cite[p.~237]{thomson},
whose opening specifies the ``motion of a ring of $n$ negatively
electrified particles''. For the general question, Cohn and Woo~\cite[Section~1.1, arXiv v2]{cohnwoo}
use the phrase ``potential energy minimization''. Here the metric space
is the unit sphere and the potential is inverse distance.
This work builds directly on Aravind Karthigeyan's AI-generated
nine-point project~\cite[README, revision \texttt{168ff0c}]{n9}.
Its stated ``global optimality and uniqueness for nine distinct points''
is for the $D_{3h}$ tricapped trigonal prism on the unit sphere, with
equality up to orthogonal transformation and permutation.
We reuse most of its MIT-licensed Lean code and follow its proof design:
the statement structure, three-point certificate checks, Bernstein
inequalities, interval classification, orthogonal alignment, higher-order
error bound and interval Hessian method. The new inputs are the ten-point
energy, interval-classification and Hessian certificates. The hardest step
is the three-point energy certificate: its error must be small enough to
force geometric localization. The interval centered at $-1$ contains
the antipodal pole pair; a five-point counting argument supplies the
linearly independent triple needed for classification.

\paragraph{Earlier and concurrent work.}
F\"oppl's 1912 ICM contribution~\cite[p.~190]{foppl} calls the tetrahedral,
octahedral and icosahedral arrangements ``stabile'', a stability statement.
Cohn and Kumar~\cite[Section~1, arXiv v2]{cohnkumar} credit Yudin~\cite{yudin} with
``regular simplex and cross polytope'' optima and Andreev~\cite{andreev} with the
icosahedron; their own universal-optimality result is Theorem~1.2 and
Table~1. Schwartz's five-point result is Theorem~1.1 of arXiv
v5~\cite{schwartz}. The numerical ten-point predecessors are Erber and
Hockney's Table~1~\cite{erber} and Wales and Ulker's database entry~\cite{cambridge}.
Delsarte, Goethals and Seidel's~\cite{delsarte} lineage is credited in Bachoc and
Vallentin's Section~1 (arXiv v4); Yudin's energy-bound lineage in Cohn and
Woo's Section~1.1 (arXiv v2). Our three-point tools are their
Corollary~3.5 and Theorem~5, respectively~\cite{bachoc,cohnwoo}.

Nearby formal work includes Hung Tran's AI-assisted seven-point
\nolinkurl{thomson_seven} and \nolinkurl{thomson_seven_unique}~\cite{n7},
and Kryvonos, Liehr and Taylor's eight-point Theorem~1.1 (arXiv
v1)~\cite{n8}. Joseph Tooby-Smith and Alex Zughaid separately give an
eight-point ``warrant'', still ``a work in progress''~\cite{n8warrant}.
Alex Zarco's five-point README states \nolinkurl{five_coulomb} and
\nolinkurl{five_coulomb_unique}, with status ``produced by AI models''
and ``not peer reviewed''~\cite[Opening; named Lean declarations]{zarco5};
its ``Known results'' credits Schwartz. His seven-point README calls
its result an ``AI-produced warrant'' for ``the logarithmic energy of
seven points'', ``not peer reviewed''; its Coulomb section says it
``uses Hung Tran's local lemma''~\cite[Opening; Coulomb]{zarco7}.
Concurrent ten-point work by \texttt{saberwatchmanga} (formerly
\texttt{terry2418}) includes the October 7 posting~\cite[README, revision
\texttt{7ba9eb3}]{concurrent}, whose ``Thomson N=10 local minimum'' section
states ``Global minimality is not proved.''
The local project's Status section reports ``a local minimum in the full
space of ten unit-sphere points''~\cite[Status]{concurrentlocal}. For ten distinct
unit-sphere points, energy at most $32.717$ requires ``at least one pair
farther apart than 1.935''~\cite[Opening]{concurrentchord}; that README
says ``Global minimality is not proved.''
Neither is a premise here. We share the cutoff $32.717$; whether our
choice was independent or taken from that work cannot be established.


```

Two earlier connective sentences are retained here as edition history.
The current paper removes the incomplete list label and uses a mathematical
appendix pointer; neither change alters a bound or a proof step.

```tex
The content of the certificate is threefold. First, the sum of $K$ over
all ordered triples of distinct indices is nonnegative for every
configuration of ten unit vectors.
gives~\eqref{eq:psd}. Appendix~\ref{app:local} identifies the checked
matrix calculation.
```

## Superseded presentation prose

The following excerpts record the previous v6 presentation for preservation
comparison. The revised paper states each nearby result in plain words;
these older status quotations and role labels are historical source text.

```text
Aravind Karthigeyan directed and published an AI-generated Lean proof
which establishes ``global
optimality and uniqueness for nine distinct points on the unit sphere''.
The minimizer is the ``tricapped trigonal prism''. Bachoc and Vallentin and Cohn and Woo supply the three-point positivity
bounds used here. We build directly on this nine-point proof's design
and reuse most of its MIT-licensed Lean code to settle the ten-point case
of Thomson's problem: the bicapped square antiprism uniquely minimizes
Coulomb energy, up to orthogonal transformations and relabeling.
Its height is the unique critical point in a specified rational interval.
A three-point semidefinite bound confines every
competitor of no greater energy to the candidate's inner-product pattern;
orthogonal alignment and a quantitative local energy inequality then
force congruence. Here the pattern consists of short
inner-product intervals, whose coherent assignment is established by finite
Gram-determinant classification. Lean checks this result.

Nearby work includes Tran's ``pentagonal bipyramid is the lowest-energy way to place seven electrons on a sphere''~\cite[Opening]{n7},

Tooby-Smith and Zughaid's eight-point ``warrant'', ``a work in progress''~\cite{n8warrant},
and Zarco's five-point ``exact three-point certificates'' and seven-point
``AI-produced warrant'', ``not peer reviewed''~\cite{zarco5,zarco7}.

restriction~\cite[Opening]{concurrentchord}. Neither is a premise here.
The ten-point posting's README~\cite[README]{concurrent}
states ``Global minimality is not proved.'' We share the cutoff $32.717$; whether our choice was independent or taken
from that work cannot be established. See Appendix~\ref{app:related}.

Nearby formal work includes Hung Tran's seven-point
\nolinkurl{thomson_seven} and \nolinkurl{thomson_seven_unique}~\cite[theorems thomson\_seven and thomson\_seven\_unique]{n7},
and Kryvonos, Liehr and Taylor's eight-point Theorem~1.1~\cite{n8}. Tran writes,
``I gave the agents the problem as two fixed Lean statements''~\cite{n7}. Joseph Tooby-Smith and Alex Zughaid separately give an
eight-point ``warrant'', still ``a work in progress''~\cite{n8warrant}.
Alex Zarco's five-point README states \nolinkurl{five_coulomb} and
\nolinkurl{five_coulomb_unique}, with status ``produced by AI models''
and ``not peer reviewed''~\cite[Opening; named Lean declarations]{zarco5};
its ``Known results'' credits Schwartz. The seven-point README calls
its result an ``AI-produced warrant'' for ``the logarithmic energy of
seven points'', ``not peer reviewed''; its Coulomb section says it
``uses Hung Tran's local lemma''~\cite[Opening; Coulomb]{zarco7}.
Concurrent ten-point work by \texttt{saberwatchmanga} (formerly
\texttt{terry2418}) includes the October 7 posting~\cite[README]{concurrent}, whose ``Thomson N=10 local minimum'' section
states ``Global minimality is not proved.''
The local project's Status section reports ``a local minimum in the full
space of ten unit-sphere points''~\cite[Status]{concurrentlocal}. For ten distinct
unit-sphere points, energy at most $32.717$ requires ``at least one pair
farther apart than 1.935''~\cite[Opening]{concurrentchord}; that README
says ``Global minimality is not proved.''


A. Karthigeyan (director and publisher), \emph{The Nine-Point Coulomb

```

The earlier presentation combined the local-minimum posting and the later
chord restriction under one date. The corrected citations identify them
separately and cite the chord source for the shared cutoff. Superseded
source excerpt:

```text
Concurrent ten-point Lean work by \texttt{saberwatchmanga} (formerly
\texttt{terry2418}) includes local minimality~\cite[Status]{concurrentlocal} and a chord
restriction~\cite[Opening]{concurrentchord}, documented in the October 7
posting~\cite[README]{concurrent}. We share its energy cutoff
$32.717$~\cite[Thomson N=10 local minimum]{concurrent}\cite[Opening]{concurrentchord}.
```

## Earlier presentation of source limitations

These superseded excerpts preserve the earlier attribution and source-access
wording. The paper gives the same limitations in plain prose, identifies
the supplementary materials and uses the complete Föppl page range.

```text
Aravind Karthigeyan's Lean proof establishes global optimality and
uniqueness of the tricapped trigonal prism for nine distinct points;
we build on its design and reuse most of its Lean code.
Bachoc and Vallentin and Cohn and Woo supply the three-point positivity
bounds. A three-point semidefinite bound confines every competitor of

The nine-point README credits ``AI-generated'' work by ``Opus 5.5'' and
``GPT-6 Astra'', and calls the project ``a research release requesting external review''~\cite[README]{n9}.
Its original upstream archive is ``not included in this public copy''~\cite[Publication Copy]{n9};
that archive was unavailable for independent source comparison.
The detailed reuse list in the introduction records our account of the code
we reused, including statement structure and the higher-order error estimate;
it is not a quotation from the README.
The numerical reference to Erber and Hockney uses Table~1 in the retained
extraction of the Fermilab preprint; the journal's Table~1 was not inspected. The Cambridge
capture's access date is retained historical metadata, not independently
authenticated here. The original Yudin, Andreev and Delsarte--Goethals--Seidel
papers were not consulted: their contributions are attributed through the
cited Cohn--Kumar, Bachoc--Vallentin and Cohn--Woo sources. Schwartz is cited
in the authenticated arXiv version; unsuccessful publisher-metadata access
for Schwartz and F\"oppl is not represented as a successful source read.

F\"oppl's 1912 ICM contribution~\cite[p.~190]{foppl} calls the tetrahedral,

optimality and uniqueness~\cite[Theorem~1.1]{n8}, also verified in Lean by

The checking guide records their source correspondence and the independent
certificate checks.

```

## Earlier descriptions of nearby formalizations

The paper gives the nearby sources' caveats once in plain words, with
precise locators. These excerpts preserve the preceding descriptions:

```text
Tooby-Smith and Zughaid's eight-point Lean verification~\cite[Opening]{n8warrant},

Tooby-Smith and Zughaid~\cite[Opening]{n8warrant}.
Zarco supplies exact three-point certificates for the five-point Riesz
energies with exponents one through six and Lean proofs for exponents
one and two, including \nolinkurl{five_coulomb} and

Zarco's seven-point project verifies the pentagonal bipyramid's uniqueness

The ten-point local result establishes a local minimum in the full space

```

## Earlier proof overview prose

The paper now explicitly assembles the established root, classification,
alignment and local estimate at the start of the final proof. The following
introductory prose is retained for exact source comparison.

```text
error bound and interval Hessian method. The new inputs are the ten-point certificates. The hardest step is the three-point bound's accuracy for geometric localization.
The energy loss must be small enough to enforce the inner-product intervals.

The candidate has the following coordinates.

To pass from the second variation to an energy inequality, we bound the
higher-order error. For a nonzero pair-difference vector $d$ and its

```

## Supplement citation and formal-statement locator

Reference to the already published proof/data bundle makes the supplied
coefficients unambiguous. All previously cited entries retain their exact
source titles and locators. The formal-statement cross-reference is now
next to the routine candidate-admissibility verification. Superseded prose:

```text
Appendix~\ref{app:statements} identifies the formal statements
of both the optimization theorem and this candidate-validity assertion.

$m(t)=\sum_{j=0}^{16}c_jt^j-2^{-130}$, where the coefficients $c_j$ are the \href{https://github.com/6/clank-lab/tree/e987408cf2d4c27c6e0c10d9f1a522ce3156c632/results/thomson-10}{supplied rational certificate data}. The downward

```

## Earlier quotation formatting

The operator requested plain cited prose in place of related-work quotations.
The exact superseded source lines below retain the historical presentation
for the static relocation audit; no mathematical statement is replaced.

```tex
Thomson wrote ``On the structure of the atom''~\cite[p.~237]{thomson}.
``global optimality and uniqueness for nine distinct points'', for the
F\"oppl lists ``stabilen Anordnungen''~\cite[p.~190]{foppl}.
Bachoc and Vallentin~\cite[Section~1]{bachoc} credit the ``LP method'' to
Woo~\cite[Section~1.1]{cohnwoo} state that its energy application was
``first carried out for energy minimization by Yudin''~\cite{yudin}.
The nine-point README credits ``AI-generated'' work by ``Opus 5.5'' and
``GPT-6 Astra''~\cite[README]{n9}. Its original upstream archive was unavailable
F\"oppl's 1912 ICM contribution~\cite[pp.~189--190]{foppl} calls the tetrahedral,
octahedral and icosahedral arrangements ``stabile'', a stability statement.
The same list includes ``$10=1+4+4+1$'' among ``stabilen Anordnungen''~\cite[p.~190]{foppl}.
``regular simplex and cross polytope'' optima and Andreev~\cite{andreev} with the
```

## Details relocated from the journal paper

The following retained source excerpts supply the full formal correspondence,
source-access limitations and historical source locators. The paper cites the
mathematical conclusions; these notes retain the detailed checking record.

### Exact formal correspondence and logical dependencies

```text
% Formal bridge begin
\paragraph{Formal theorem.}
The closed Lean declarations have types
{\small
\begin{verbatim}
ThomsonN10.thomson_ten_complete : ThomsonN10.Challenge.CompleteTarget
ThomsonN10.candidate_admissible (h : ThomsonN10.CandidateParameter) :
  ThomsonN10.IsSphereConfiguration (ThomsonN10.candidate h)
\end{verbatim}
}
Here \texttt{CompleteTarget} asserts that exactly one real height in the
specified interval satisfies the stationarity equation; and for every
\texttt{CandidateParameter h} and every \texttt{Configuration x}
satisfying \texttt{IsSphereConfiguration x}, \texttt{candidate h} has
energy at most that of \texttt{x}, and \texttt{x} has that same energy
if and only if \texttt{Congruent x (candidate h)}.
The parameter subtype imposes precisely
that interval and equation; \texttt{heightLower}, \texttt{heightUpper} and
\texttt{stationarity} are $a$, $b$ and $S$ above. The existence clause
prevents vacuous parameter quantification, and \texttt{candidate h} has
the coordinates displayed in Section~\ref{app:candidate}.

A \texttt{Configuration} is a map from \texttt{Fin 10} to
\texttt{EuclideanSpace} over the reals on \texttt{Fin 3}, hence a labeled
ten-point map into $\R^3$. The sphere predicate means unit norm at every
index and injectivity. The formal \texttt{coulombEnergy} is the displayed
sum over unordered pairs. Lean's real inverse at zero is zero: collisions
are excluded by injectivity, rather than assigned infinite energy.
The predicate \texttt{Congruent} uses a real-linear isometric equivalence
and a permutation of \texttt{Fin 10}, exactly $O(3)$ (including reflections)
and relabeling. The separate admissibility theorem supplies the candidate's
unit norms and injectivity. Together these declarations give
Theorem~\ref{thm:main}, without external certificate hypotheses.
% Formal bridge end

The upper bound $\E(p)\leq U$ in Lemma~\ref{lem:threepoint} is proved in Lean.
Each certificate assertion used in the proof is itself
proved in Lean.
The formal proof uses propositional extensionality, classical choice and
quotient soundness. Lean checks the
root, admissibility, global optimality and the full equality equivalence.
The \href{https://github.com/6/clank-lab/tree/thomson-10-v6/results/thomson-10}{independent Python implementation} checks the same rational
three-point certificate; the
geometric and local arguments are proved in Lean. Its supplementary
energy enclosure and the figure check are outside that theorem.
```

### Detailed prior-work locators and source-access record

```text
\section{Related work}\label{app:related}
We compare earlier global energy results, numerical candidates and
related formal verifications.
The nine-point README credits AI-generated work by Opus 5.5 and
GPT-6 Astra~\cite[README]{n9}. Its original upstream archive was unavailable
for comparison~\cite[Publication Copy]{n9}; the introduction's reuse list
is our account of the code reused.
We cite Yudin, Andreev and Delsarte--Goethals--Seidel through Cohn--Kumar,
Bachoc--Vallentin and Cohn--Woo; their original papers were not consulted.
Erber and Hockney's Table~1 is cited from the Fermilab preprint extraction;
the journal's Table~1 and the Cambridge entry's access date were not
independently checked. Publisher metadata for Schwartz and F\"oppl could
not be obtained; the Schwartz reference uses the authenticated arXiv version.

F\"oppl's 1912 ICM contribution~\cite[pp.~189--190]{foppl} describes stability of the tetrahedral,
octahedral and icosahedral arrangements.
The same list includes $10=1+4+4+1$ among the stable arrangements~\cite[p.~190]{foppl}.
Cohn and Kumar~\cite[Section~1]{cohnkumar} credit Yudin~\cite{yudin} with
regular simplex and cross-polytope optima and Andreev~\cite{andreev} with the
icosahedron; their own universal-optimality result is Theorem~1.2 and
Table~1. Schwartz's five-point result is Theorem~1.1 of~\cite{schwartz}. The numerical ten-point predecessors are Erber and
Hockney's Table~1~\cite{erber} and Wales and Ulker's database entry~\cite{cambridge}.
Delsarte, Goethals and Seidel's~\cite{delsarte} lineage is credited in Bachoc and
Vallentin's Section~1; Yudin's energy-bound lineage in Cohn and
Woo's Section~1.1. Our three-point tools are their
Corollary~3.5 and Theorem~5, respectively~\cite{bachoc,cohnwoo}.

Tran proves optimality and uniqueness of the pentagonal bipyramid for
seven charges in \nolinkurl{thomson_seven} and
\nolinkurl{thomson_seven_unique}~\cite[theorems thomson\_seven and thomson\_seven\_unique]{n7};
his account describes giving the agents two fixed Lean statements.
Kryvonos, Liehr and Taylor prove the eight-point square antiprism's
optimality and uniqueness~\cite[Theorem~1.1]{n8}, also formalized in Lean by
Tooby-Smith and Zughaid, who describe their development as ongoing
work~\cite[Opening]{n8warrant}.
Zarco presents exact three-point certificates for the five-point Riesz
energies with exponents one through six and Lean formalizations for
exponents one and two, including \nolinkurl{five_coulomb} and
\nolinkurl{five_coulomb_unique}~\cite[Statement; Lean]{zarco5};
its Known results section credits Schwartz.
Zarco's seven-point project formalizes the pentagonal bipyramid's uniqueness
for logarithmic energy and inverse-square energy, and its Coulomb argument
uses Tran's local lemma~\cite[Opening; Lean; Coulomb]{zarco7}.
Both Zarco projects remain unreviewed~\cite[Opening]{zarco5,zarco7}.
The ten-point local project reports a local minimum in the full space
of ten unit-sphere points~\cite[Status]{concurrentlocal}. For ten distinct
unit-sphere points, energy at most $32.717$ requires at least one pair
farther apart than 1.935~\cite[Opening]{concurrentchord}.
Global optimality is outside both ten-point statements.
```

### Formal definitions and propositions

```text
\subsection{Formal theorem statements}\label{app:statements}
The formal propositions quantify over the same admissible competitors
as Theorem~\ref{thm:main}.
The optimality and uniqueness assertions, together with parameter
existence and uniqueness, form the declaration
\nolinkurl{ThomsonN10.thomson_ten_complete}. Its type is
\nolinkurl{ThomsonN10.Challenge.CompleteTarget}.

The other declaration
\nolinkurl{ThomsonN10.candidate_admissible} proves unit norm and injectivity for every
\texttt{CandidateParameter}. Theorem~\ref{thm:main} combines these two
declarations.
In Lean, a configuration is a map from \texttt{Fin 10} to Euclidean
three-space, and \texttt{IsSphereConfiguration} means exactly that each
vector has norm one and the map is injective. The total Lean function
uses the field convention $0^{-1}=0$, so a collision is excluded by the
injectivity hypothesis; it is not assigned infinite energy.

The formal definitions are:
\begin{alltt}\small
abbrev R3 := EuclideanSpace \(\mathbb{R}\) (Fin 3)
abbrev Configuration := Fin 10 \(\to\) R3

def IsSphereConfiguration (x : Configuration) : Prop :=
  (\(\forall\) i, \(\|\)x i\(\|\) = 1) \(\land\) Function.Injective x

noncomputable def coulombEnergy (x : Configuration) : \(\mathbb{R}\) :=
  \(\sum\) i : Fin 10, \(\sum\) j \(\in\) Finset.Ioi i, (\(\|\)x i - x j\(\|\))\textsuperscript{-1}

def Congruent (x y : Configuration) : Prop :=
  \(\exists\) (g : R3 \(\simeq\)\textsubscript{li}[\(\mathbb{R}\)] R3) (p : Equiv.Perm (Fin 10)), \(\forall\) i, x i = g (y (p i))
\end{alltt}
Here the isometry-equivalence notation means a bijective real linear
isometry, hence an element of $O(3)$. The theorem combines the following propositions:
\begin{alltt}\small
def ParameterExistsUnique : Prop :=
  \(\exists\)! h : \(\mathbb{R}\), (heightLower : \(\mathbb{R}\)) \(\leq\) h \(\land\) h \(\leq\) (heightUpper : \(\mathbb{R}\)) \(\land\) stationarity h = 0

def GlobalOptimality : Prop :=
  \(\forall\) h : CandidateParameter, \(\forall\) x : Configuration,
    IsSphereConfiguration x \(\to\) coulombEnergy (candidate h) \(\leq\) coulombEnergy x

def GlobalUniqueness : Prop :=
  \(\forall\) h : CandidateParameter, \(\forall\) x : Configuration,
    IsSphereConfiguration x \(\to\)
    (coulombEnergy x = coulombEnergy (candidate h) \(\leftrightarrow\) Congruent x (candidate h))

def CompleteTarget : Prop := ParameterExistsUnique \(\land\) GlobalOptimality \(\land\) GlobalUniqueness
\end{alltt}
The first component specifies the height; the second is the lower bound;
the third gives both directions of the equality case. Candidate validity
is supplied by the separate theorem already identified above.
```

### Supplementary energy evaluation

```text
\subsection{The separate energy calculation}\label{app:energy}
This subsection explains how to check the separate energy enclosure
in Appendix~\ref{sec:energy}. This calculation is checked only by Python.
It is computed by
rational interval evaluation of the candidate's 45 pair energies over
$[a,b]$. Square roots are enclosed using integer square roots on a dyadic grid
of spacing $2^{-420}$, rounding outward. Reciprocal and summation
operations preserve the rational bounds. Lean proves that the
height interval $[a,b]$ contains its unique stationary root; Python uses the interval as input and does not
prove root existence or uniqueness.
```

### Energy enclosure

```text
\paragraph{Remark (energy enclosure).}\label{sec:energy}
A separate rigorous evaluation of the candidate energy gives
\[
 32.716949460147<\E(p)<32.716949460149,
\]
so the energy starts $32.71694946\ldots$. This rigorous rational-interval
computation is separate from the formal theorem. Appendix~\ref{app:energy}
gives the independent Python calculation and its exact inputs.
```

### Authenticated source editions and detailed locators

```text
\begin{thebibliography}{99}
\small
\bibitem{thomson}
J. J. Thomson, On the structure of the atom: an investigation of the
stability and periods of oscillation of a number of corpuscles arranged
at equal intervals around the circumference of a circle; with application
of the results to the theory of atomic structure,
\emph{Philosophical Magazine} 7 (1904), 237--265.
\href{https://doi.org/10.1080/14786440409463107}{doi:10.1080/14786440409463107}.

\bibitem{n9}
A. Karthigeyan, \emph{The Nine-Point Coulomb
Thomson Problem}, MIT-licensed Lean project, revision \texttt{168ff0c},
October 6, 2026.
\url{https://github.com/aravindkarthigeyan/thomson-n9-lean/tree/168ff0c98cab4dfda0460ba55f8d169070ac385e}.

\bibitem{delsarte}
P. Delsarte, J. M. Goethals and J. J. Seidel, Spherical codes and designs,
\emph{Geometriae Dedicata} 6 (1977), 363--388.
\href{https://doi.org/10.1007/BF03187604}{doi:10.1007/BF03187604}.

\bibitem{yudin}
V. A. Yudin, Minimum potential energy of a point system of charges,
\emph{Diskretnaya Matematika} 4 (1992), no.~2, 115--121;
English translation in \emph{Discrete Mathematics and Applications}
3 (1993), no.~1, 75--81.
\href{https://doi.org/10.1515/dma.1993.3.1.75}{doi:10.1515/dma.1993.3.1.75}.

\bibitem{bachoc}
C. Bachoc and F. Vallentin, New upper bounds for kissing numbers from
semidefinite programming, \emph{Journal of the American Mathematical
Society} 21 (2008), 909--924.
\href{https://doi.org/10.1090/S0894-0347-07-00589-9}{doi:10.1090/S0894-0347-07-00589-9}.

arXiv version 4, October 3, 2007.
\url{https://arxiv.org/abs/math/0608426v4}.

\bibitem{cohnwoo}
H. Cohn and J. Woo, Three-point bounds for energy minimization,
\emph{Journal of the American Mathematical Society} 25 (2012), 929--958.
\href{https://arxiv.org/abs/1103.0485v2}{arXiv:1103.0485v2}.
Version 2, June 24, 2013.


\bibitem{foppl}
L. F\"oppl, Stabile Anordnungen von Elektronen im Atom,
in \emph{Proceedings of the Fifth International Congress of Mathematicians},
Cambridge, 1912, vol.~II (Cambridge University Press, 1913), 188--191.
\url{https://www.mathunion.org/fileadmin/ICM/Proceedings/ICM1912.2/ICM1912.2.ocr.pdf}.

\bibitem{andreev}
N. N. Andreev, An extremal property of the icosahedron,
\emph{East Journal on Approximations} 2 (1996), no.~4, 459--462.
\href{https://www.mathnet.ru/eng/person9017}{Author's publication list}.
Review: \href{https://zbmath.org/?q=an:0877.51021}{Zbl 0877.51021}.

\bibitem{cohnkumar}
H. Cohn and A. Kumar, Universally optimal distribution of points on spheres,
\emph{Journal of the American Mathematical Society} 20 (2007), 99--148.
arXiv version 2, October 19, 2006.
\url{https://arxiv.org/abs/math/0607446v2}.

\bibitem{schwartz}
R. E. Schwartz, The 5 Electron Case of Thomson's Problem,
arXiv version 5, February 8, 2010 (first posted January 21, 2010).
\url{https://arxiv.org/abs/1001.3702v5}.

\bibitem{erber}
T. Erber and G. M. Hockney, Equilibrium configurations of $N$ equal charges
on a sphere, \emph{Journal of Physics A: Mathematical and General}
24 (1991), L1369--L1377, Table~1.
\href{https://doi.org/10.1088/0305-4470/24/23/008}{doi:10.1088/0305-4470/24/23/008}.
\url{https://lss.fnal.gov/archive/1991/pub/Pub-91-222-T.pdf}.

\bibitem{cambridge}
D. J. Wales and S. Ulker, Cambridge Cluster Database, Thomson problem,
ten-point entry, accessed October 24, 2026.
\url{https://www-wales.ch.cam.ac.uk/~wales/CCD/Thomson/table.html}.

\bibitem{concurrent}
\texttt{saberwatchmanga} (formerly \texttt{terry2418}),
\emph{Lean Certificates: Finite Results and Thomson N=10}.
Lean-verified local minimality for ten charges on a sphere
(October 7, 2026), and A Lean-checked distance restriction for ten charges
on a sphere (October 11, 2026).
\url{https://github.com/saberwatchmanga/-lean-finite-certificates}.
October 7 posting, root README, revision \texttt{7ba9eb3}:
\url{https://github.com/saberwatchmanga/-lean-finite-certificates/blob/7ba9eb38db36c9cb957ff26758b66bbacc31d8bc/README.md}.

\bibitem{n7}
H. Tran, A Lean Proof of the Thomson Problem for Seven Electrons,
Vals AI blog, September 28, 2026, Problem section.
\url{https://www.vals.ai/blogs/thomson-n7-lean-proof}.

\bibitem{n8}
L. Kryvonos, L. Liehr and M. A. Taylor, Energy minimization for eight
points on the sphere, arXiv version 1, September 18, 2026.
\url{https://arxiv.org/abs/2609.22077v1}.

\bibitem{n8warrant}
J. Tooby-Smith and A. Zughaid, A warrant for the N = 8 Thomson problem, in Lean 4,
README, revision \texttt{2c35d62}, September 2026.
\url{https://github.com/jstoobysmith/Thomson-N-8-Warrant/blob/2c35d62e07d72686931da4bc3e062d668e858eda/README.md}.

\bibitem{zarco5}
A. Zarco (\texttt{alejandrozarco}), \emph{Five points on the sphere: exact three-point certificates for the
Riesz energies $s = 1, \dots, 6$, and Lean formalisations for $s = 1$
(Coulomb) and $s = 2$}, \texttt{five-points-riesz},
README, revision \texttt{aeb4588}, October 2026.
\url{https://github.com/alejandrozarco/five-points-riesz/blob/aeb4588ccbb1ccb91c315fedeb79a18042b5fe13/README.md}.

\bibitem{zarco7}
A. Zarco (\texttt{alejandrozarco}), \emph{The pentagonal bipyramid as the unique
logarithmic-energy minimiser for seven points on the sphere: an unreviewed
Lean 4 warrant (Conjecture 1 of Armentano et al.)},
\texttt{thomson-n7-log}, README, revision \texttt{fd2f8b2}, October 2026,
including its Coulomb section.
\url{https://github.com/alejandrozarco/thomson-n7-log/blob/fd2f8b2e7eb0e89ba4f82f6d2c3e98862f89bc28/README.md}.

\bibitem{concurrentlocal}
\texttt{saberwatchmanga} (formerly \texttt{terry2418}),
\emph{Lean-verified local minimality for ten charges on a sphere},
\texttt{Thomson10LocalMinimum}, README, revision \texttt{7ba9eb3}, October 2026.
\url{https://github.com/saberwatchmanga/-lean-finite-certificates/blob/7ba9eb38db36c9cb957ff26758b66bbacc31d8bc/Thomson10LocalMinimum/README.md}.

\bibitem{concurrentchord}
\texttt{saberwatchmanga} (formerly \texttt{terry2418}),
\emph{A Lean-checked distance restriction for ten charges on a sphere},
\texttt{Thomson10Chord1935}, README, revision \texttt{bc74bc0}, October 2026.
\url{https://github.com/saberwatchmanga/-lean-finite-certificates/blob/bc74bc050f4c39123e894b3fd3873ba17f60289a/Thomson10Chord1935/README.md}.
\bibitem{supplement}
P. Graham, \emph{The Thomson problem for N = 10}, proof sources and
certificates, version 5 (2026), repository revision \texttt{e987408}. The certificates are unchanged in this edition.
\href{https://github.com/6/clank-lab/tree/e987408cf2d4c27c6e0c10d9f1a522ce3156c632/results/thomson-10}{Repository}.

\end{thebibliography}
```

### Relocated definitions, contribution details and qualifications

```text
The nine-point Lean proof directed by Karthigeyan~\cite[README]{n9} establishes
global optimality and uniqueness for nine distinct points, for the
$D_{3h}$ tricapped trigonal prism. We reuse most of its MIT-licensed Lean code. Our reuse includes:
the statement structure, three-point certificate checks, Bernstein
inequalities, interval classification, orthogonal alignment, higher-order
error bound and interval Hessian method. The ten-point data establish the polynomial, classification and Hessian bounds below.

Here and below, admissibility means precisely unit norm and injectivity.

The conclusion fixes
an interval pattern and bounds every Gram-matrix entry; it does not yet
say that the inner products are equal.

The type \texttt{CandidateParameter} consists exactly of reals in this
interval satisfying $S(h)=0$. Root uniqueness is asserted in this
specified interval, not for all real heights.




These decimals describe the exact rational data, and are not used as
proof inputs.
These are fixed data, not optimization variables in the theorem.

Its decimal begins
$0.422687424043986\ldots$.

Its decimal begins $0.422687424043986\ldots$. The root existence and
uniqueness in this specified interval are proved in Lean. This interval
selects the candidate; the global theorem still compares it with every
admissible configuration, including all other heights.
```

### Certificate and formalization overview

```text
Lean checks the complete optimality and equality theorem
from the definitions. A separate Python implementation verifies the
rational three-point certificate.
The new inputs are the ten-point energy, interval-classification and
Hessian certificates.
The formal definitions below identify the statements used in the proof.
The supplementary files supplied with this paper contain the certificates,
Lean proof and checking instructions. The checking guide records the formal
source correspondence and the independent certificate checks.
```


### Earlier terminology in the mathematical source

These exact source lines locate the presentation-only terminology changes.
The energy, domain and matrix themselves are unchanged.

```text
The family energy is $F(h)=\E(p(h))$, with the explicit expression
finite Gram-determinant classification makes their assignments coherent,
on the \emph{capped Gram domain}
This is their \emph{cross-Gram matrix}. It has rank at most three, so its
```

### Proof passages before the additional relocation

The anchor-conditioning derivation and Hessian blocks now appear in the
main proof. These earlier connecting passages preserve their exact source
correspondence; no mathematical statement or interval bound changed.

```text
For alignment we choose the fixed candidate triple $p_2,p_3,p_6$ and the
corresponding relabeled competitor triple. These need not be the anchor
triple used during classification: \eqref{eq:gram} controls every pair,
so it also controls these chosen triples. Aligning the anchor
frames---the orthonormal bases obtained by Gram--Schmidt from these
triples---controls their coordinates; the inner products with the anchor
points then control the other points. The estimates in
Appendix~\ref{app:conditioning} construct an alignment with total
displacement at most $10000\delta$. A minimizing alignment is at least
as good, so
\[
 \rho\leq10000\delta=10^{-6}.
\]
Let $H(h)$ be the $30\times30$ matrix defined in Appendix~\ref{app:local} at
$p(h)$, and abbreviate $H=H(h_*)$. At the stationary candidate, this is
the constrained second variation. The pair-Hessian blocks are defined in Appendix~\ref{app:local}.
\subsection{Conditioning of the anchor alignment}\label{app:conditioning}
We convert the bounds on inner products into a small displacement from
the candidate.
A quantitative Gram-stability argument turns~\eqref{eq:gram} into an
orthogonal alignment. It uses the candidate anchor points $p_2,p_3,p_6$:
the absolute values of the inner products of pairs $(2,3)$, $(2,6)$ and $(3,6)$ are at
most $19/100$, $41/100$ and $41/100$, respectively. The corresponding
pairs of relabeled competitor anchor points consequently satisfy the absolute
inner-product bounds $1/5,5/12,5/12$. In Gram--Schmidt, each residual
is the component of an anchor point orthogonal to the span of the
preceding anchor points. The lengths of the two residuals are at least
$2/3$ and $1/2$. Thus the divisions used to recover coordinates from
inner products have denominators bounded away from zero.

In the resulting orthonormal frames, the coordinate differences for each
point are at most $\delta$, $22\delta$ and $646\delta$, respectively.
These scalar estimates follow by applying the product, square-root and
quotient difference bounds to the Gram--Schmidt formulas; they are
proved by scalar perturbation estimates with rational constants. Relaxing each to
$650\delta$ and summing the 30 coordinate squares gives
$\rho^2\leq30(650\delta)^2\leq(10000\delta)^2$ for the constructed
alignment. Minimality transfers this bound to the minimizing alignment.


The global and local constants serve different steps. The windows have
radius $10^{-10}$, and the coordinate estimate loses a factor of $10^4$.
The resulting radius $10^{-6}$ is one thousand times smaller than the
local energy estimate's permitted radius $10^{-3}$.

\subsection{Local inequalities}\label{app:local}
In the block formula at a general height,
the radial coefficient means
$\lambda_i(h)=-\tfrac12\sum_{j\ne i}\|p_i(h)-p_j(h)\|^{-1}$;
stationarity is asserted only at $h_*$.
For a nonzero pair-difference vector $d$, the pair
Hessian is
\[
 B(d)=\frac{3dd^{\mathsf T}}{\|d\|^5}
           -\frac{I_3}{\|d\|^3},
\]
where the off-diagonal block of $H$ for two different point indices is the
negative of $B(p_i-p_j)$. The diagonal block at point $i$ is the sum of
$B(p_i-p_j)$ over the other nine points, minus the radial coefficient at
that point times the three-by-three identity. These blocks specify the sphere-constrained second variation, including
the radial correction.

The following inequalities establish full stationarity and the
finite-radius energy gap.
The interval Hessian calculation encloses the arithmetic and square-root
operations over the full height interval. Its change-of-basis matrix is
upper triangular with all diagonal entries equal to one, hence invertible.
Interval bounds on the transformed matrix certify strict diagonal
dominance.



The gradient is the negative of the physical force.
The formal coordinate calculation rewrites the height equation as a
relation among the seven inverse-cube distance weights, one for each
candidate inner-product class, and checks the gradient at every point.





The local estimate uses the
exact unit-sphere identity $\langle p_i,y_i-p_i\rangle
=-\|y_i-p_i\|^2/2$. Its final conclusion is
$\E(y)-\E(p)\geq\rho^2/200$ for aligned displacement norm
$\rho\leq1/1000$.


```

Earlier wording of the graph adjacency definition:

```text
Join two nodes when at least one color survives the pair test, retaining
the list of all surviving colors on that edge.
```

### Explanatory remarks moved out of the proof

```text
The displayed $10^{-30}$ bound is conservative: most of $L$ comes from
the downward minorant shift, while the residual norm is about $10^{-56}$.
In particular, the shift is included once in the defined loss $L$.
Both
properties enter the energy estimate below.
The coefficients $c_j$ are the supplied rational certificate data.
Join two nodes when at least one color survives the pair test, retaining
points of an actual configuration give such a clique. They give distinct
nodes because the pair test excludes all seven colors when the two node
```

Earlier heading: \paragraph{Slack outside the windows.}

Earlier appendix cross-reference, updated after the proof heading moved:

```text
The following estimates supply the pair bounds used in Section~\ref{sec:local}.
```
