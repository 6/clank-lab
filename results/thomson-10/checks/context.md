# Historical context and credits

Material relocated from version 4, with personal pronouns in credits replaced by names. The current theorem
and proof details are in the [paper](../paper/paper.pdf). Historical
comparisons below are records of the earlier edition, not new claims.

## Former abstract and introduction

```text
\begin{abstract}
Thomson's problem, originating in Thomson's 1904 atomic model, asks for the least
Coulomb energy of points on a sphere. For $N = 10$ distinct points on the unit
sphere in $\R^3$, we prove that the energy
$\sum_{i<j}\|x_i-x_j\|^{-1}$ is minimized uniquely, up to orthogonal maps
and relabeling, by the $D_{4d}$ bicapped square antiprism. Its height
parameter is the distance of either square from the equatorial plane.
The chosen height is the unique critical point of the energy in a
specified exact interval. Adapting the nine-point proof design,
the proof first confines the inner products of every
competitor of no greater energy to seven small intervals. Classifying
the possible interval patterns and aligning the configurations then
reduces the problem to a quantitative local energy inequality that
forces equality with the candidate. The computer-assisted proof is
formally verified in Lean.
\end{abstract}

The proofs, the Lean formalization, the certificate checkers and the text
were produced by AI models (from OpenAI and Anthropic), working under the
author's direction.

\section{Introduction}
Thomson's problem asks for the least Coulomb energy of $N$ distinct unit
vectors in three dimensions. The problem originates in Thomson's 1904
atomic model~\cite{thomson}. For $N = 10$ charges, the familiar candidate has
two poles and two squares at opposite heights, rotated by $\pi/4$
relative to one another (Figure~\ref{fig:antiprism}). Their height is approximately $0.4226874$ and
the energy is approximately $32.71694946$. We prove that this $D_{4d}$
bicapped square antiprism is the unique global minimizer, up to orthogonal maps and
relabeling; Theorem~\ref{thm:main} gives the exact statement. No symmetry is assumed of competitors.

Optimizing within this one-parameter family does not settle the global
problem: competitors may have no symmetry. The main task is to localize
all such competitors. The two-point bound used here is only about
$32.66696$, below the candidate energy, so it cannot establish optimality.
Its role is to separate points. A three-point bound then puts every
competitor's energy above the candidate energy minus $10^{-30}$ whenever
all distinct pair inner products are at most $13/20$. The hard step is to turn this small energy error into
control of every competitor's geometry. The window classification does
this; the local energy inequality removes the error entirely.

The proof has four steps. First, a two-point bound separates distinct
points, after which a polynomial lower bound for pair energy and a
three-point energy estimate force all pairwise inner products of a
competitor of no greater energy into seven small intervals around the
candidate's inner products. Second, a finite classification shows that
these intervals can occur on the pairs in only the candidate's pattern,
up to relabeling. Third, an orthogonal alignment converts this control of
inner products into a bound on the point displacements. Finally, the
height equation and symmetry give full spherical stationarity, and a
positive second variation, together with a bound on the higher-order
error, makes every sufficiently small nonzero aligned displacement
increase the energy. This last step turns approximate localization into
exact equality.

The argument builds directly on the nine-point proof published by
Aravind Karthigeyan, which Anthropic's Opus 5.5 and OpenAI's GPT-6 Astra
generated under Karthigeyan's direction and which, unreviewed, Karthigeyan released
requesting external review~\cite{n9}, including substantial reuse of its
MIT-licensed Lean code. For the ten-point geometry we supply new
energy, window-classification and Hessian certificates. The formal proof covers optimality, every equality
case and the fact that the candidate consists of distinct unit vectors.
To our knowledge no earlier rigorous proof for $N=10$ exists, and we make
no priority claim. Concurrent ten-point Lean proofs establish local
minimality and a long-chord condition~\cite{concurrent}; neither asserts
global optimality. The prior exact cases and these concurrent results
are described in Section~\ref{sec:prior}. Neither the present work nor
the nine-point work is yet peer-reviewed.
The theorem includes uniqueness, and its Lean verification is a formal
proof. Being the first rigorous proof or the first formal proof is a
historical claim, subject to the qualification just stated.

\paragraph{What is new beyond nine points.}
The proof follows the design of the nine-point project step by step and
reuses most of its Lean code: the form of the statement, the three-point
bound with its certificate checks, the Bernstein checks
of one-variable inequalities, the interval tests of the window
classification, the orthogonal alignment, the higher-order error bound and
the interval method for the Hessian. As it stood, that machinery did not
reach ten points in three places. First, a three-point certificate belongs
to one configuration, and we needed one that is sharp at the antiprism, so
that it misses the candidate energy by less than $10^{-30}$. Second, the
nine-point classification excludes inner products near $-1$ by a
Gram-determinant estimate and works with six windows. Here the poles are
antipodal, so $-1$ is a genuine seventh window, and the two poles with two
opposite points of a square lie in one plane through the origin. Every
triangle among those four points is then degenerate, so the nine-point
proof that four points always contain an anchor triple fails; a counting
argument over five points replaces it (Section~\ref{sec:global}). Third,
the local bound certifies one matrix. The ten-point Hessian is
$30\times30$, and its smallest eigenvalue transverse to rotations is about
$0.096$, against about $0.144$ for nine points, so the shift, the radius
and the interval data are new, as is the stationarity calculation for the
$D_{4d}$ symmetry. The first of the three was the hardest. A numerical
semidefinite solution is far less accurate than $10^{-30}$; our
certificate rounds, to rationals with denominator $2^{200}$, an exact
three-point certificate that is sharp for ten points, whose one-variable
polynomial touches the pair potential at $-1$ and at the six other
candidate inner products.

Section~\ref{sec:candidate} defines the candidate and states the theorem.
Section~\ref{sec:global} proves the two global localization steps;
Section~\ref{sec:local} completes the argument by alignment and local
rigidity. The separate numerical energy enclosure follows the theorem, and
Section~\ref{sec:prior} records the prior and concurrent work. Appendix~\ref{app:formal} supplies the exact parameter interval,
formal declarations, certificate sizes and checking requirements. The
text explains the mathematical reductions; the accompanying Lean proof
checks the rational inequalities and finite classifications they use.


```

## Prior and concurrent work

```text
\section{Prior and concurrent work}\label{sec:prior}
The theorem fits a sequence of exact results for small numbers of points.
We record that context, the code and proof design used here, and the
concurrent partial results for ten points.

The numerical candidate predates these formal proofs. Erber and
Hockney's 1991 numerical study~\cite{erber} reports ten-point energy
$32.71694946$. The Cambridge Cluster Database~\cite{cambridge} lists
$D_{4d}$ symmetry and energy $32.7169494$. The separate rigorous
enclosure remark in Section~\ref{sec:energy} agrees with the Erber--Hockney value and refines the
database's shorter numerical approximation.

The immediate precedent is the MIT-licensed \texttt{thomson-n9-lean}
project~\cite{n9}, directed and published by Aravind Karthigeyan. Its
README calls it AI-generated, by Anthropic's Opus 5.5 and OpenAI's GPT-6
Astra, with the
mathematics, formal code, checks and exposition ``developed through AI
agents under human direction'', and describes it as ``a research release
requesting external review and fresh-machine reproduction, not a claim of
completed peer review or priority''. We adapt
its global localization and local rigidity argument, including substantial
reuse of its formal code. Appendix~\ref{app:provenance} identifies the
revision, its nine-point theorem and our ten-point changes.

The classical configurations include the antipodal pair, equilateral
triangle, regular tetrahedron and regular octahedron. The tetrahedral
four-electron configuration appears in F\"oppl's 1912 stability analysis
of electron arrangements~\cite{foppl}; this historical stability result
should be distinguished from a global minimum theorem. Yudin's
energy bounds, published in Russian in 1992 and in English in 1993,
prove the octahedral case~\cite{yudin}. For twelve points, Andreev's
1996 paper proves that the icosahedron maximizes the product of pairwise
distances and, as its zbMATH review records, claims the corresponding
results for the Coulomb energy~\cite{andreev}; Cohn and Kumar credit Andreev
with the icosahedron as the unique minimum~\cite{cohnkumar}, and their
2007 universal-optimality theorem, which covers the Coulomb energy,
includes the tetrahedron, octahedron and icosahedron. Schwartz proved the
five-point triangular bipyramid optimal in a 2010 preprint, published in
2013~\cite{schwartz}.

Recent work includes Hung Tran's AI-assisted seven-point Lean proof,
published on the Vals AI blog in September 2026: Tran fixed the two Lean
statements and deployed ten agents running Anthropic's Sonnet 5.5, which
did the proof work in about 15 hours, and Tran ran five checks on the
result, including a second kernel~\cite{n7}. Kryvonos, Liehr and Taylor's
September 18, 2026 paper~\cite{n8} proves that the square antiprism is the
unique global minimizer for eight points for both Coulomb and logarithmic
energy, with a computer-assisted proof verified in Lean. Joseph
Tooby-Smith and Alex Zughaid also released a Lean-checked warrant in
September 2026 for the eight-point Coulomb problem~\cite{n8warrant}.
Their README describes it as a formal check that the square antiprism
solves the eight-point case uniquely, and calls it a complete warrant,
not a proof, that is still a work in progress; it does not state
uniqueness up to orthogonal maps and relabeling.
Alex Zarco (\texttt{alejandrozarco}) released AI-produced, unreviewed
Lean warrants for two smaller cases in September--October 2026. For five points, a
single sharp three-point semidefinite certificate, with a finite
enumeration for uniqueness, shows that the triangular bipyramid uniquely
minimizes the Coulomb energy, a theorem already known from Schwartz; the
Lean formalization states uniqueness up to orthogonal maps and
relabeling~\cite{zarco5}. Zarco's seven-point
repository, prepared in late September with its Lean part added on
October 1 and chiefly on the logarithmic energy, added on October 8 a
second check of
Tran's Coulomb theorem with its own certificates and a Lean development
that uses Tran's local lemma~\cite{zarco7}. We use no code from either.
The general methodology belongs to the Delsarte--Yudin theory of energy
bounds~\cite{delsarte,yudin}. The specific three-point lineage is the
semidefinite-programming framework of Bachoc and Vallentin~\cite{bachoc}
and its energy-minimization extension by Cohn and Woo~\cite{cohnwoo}.
The immediate design and formal implementation precedent here is the
nine-point project.

Concurrent ten-point formalizations maintained by
\texttt{saberwatchmanga} (formerly \texttt{terry2418}), in the
\texttt{-lean-finite-certificates} project~\cite{concurrent}, give two further partial results. Its October 7, 2026 posting proves full-space local minimality for
an exactly specified height, with strict increase on a 17-dimensional
slice removing rotations. Its October 11, 2026 posting proves that any
configuration of energy at most $32.717$ has a chord longer than $1.935$.
These are rigorous partial results; that project expressly makes no claim
of global optimality. The present
proof uses neither result as a premise and uses no code from that project.
Both use the cutoff $32.717$. We cannot establish whether our choice was
independent or taken from that work; Appendix~\ref{app:provenance}
explains its mathematical role.



```

## Build timing

```text
A resumed build using two compiler threads and a partially populated
build/dependency cache took about 33 minutes. A full build from an
empty cache has not been timed.

```

## Code and cutoff provenance

```text
\subsection{Code and cutoff provenance}\label{app:provenance}
This subsection records the source of the reused formal code and the
relation between the two ten-point energy cutoffs.

The MIT-licensed Lean code of the
\texttt{thomson-n9-lean} project~\cite{n9} supplies the immediate
precedent. Its AI-produced October 6, 2026 revision \texttt{168ff0c} proves
that the $D_{3h}$ tricapped trigonal prism is the unique Coulomb minimizer
for nine distinct unit-sphere points, up to orthogonal maps and
permutations, with its parameter defined by a unique root in a specified
interval. Our Lean files adapt its theorem organization, energy bound with a small
certified error, classification of inner-product intervals, orthogonal
alignment and local energy argument. The adaptations supply the
ten-point geometry, candidate inner products, certificate data and their
connection to the final theorem. A file-level attribution and account of
changes is provided in \texttt{THIRD\_PARTY.md}. The prose is new; the
reused material is formal code.

Our preliminary energy cutoff
$32717/1000$ is exactly the $32.717$ used in the October 11, 2026
chord-bound result of \texttt{saberwatchmanga}~\cite{concurrent}: it is the
known candidate energy rounded upward to three decimal places. Under this
cap, our two-point certificate proves that every distinct pair has inner
product below $13/20$. That assertion is not deduced from their existence
of a chord longer than $1.935$. We cannot establish whether $32.717$ was chosen independently or taken
from that work; no step of this proof uses the earlier result.


```

## Original references

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

\bibitem{foppl}
L. F\"oppl, Stabile Anordnungen von Elektronen im Atom,
\emph{Journal f\"ur die reine und angewandte Mathematik} 141 (1912),
251--302. \href{https://doi.org/10.1515/crll.1912.141.251}{doi:10.1515/crll.1912.141.251}.
See also the author's ICM 1912 report, vol.~II, p.~190,
\url{https://www.mathunion.org/fileadmin/ICM/Proceedings/ICM1912.2/ICM1912.2.ocr.pdf}.

\bibitem{erber}
T. Erber and G. M. Hockney, Equilibrium configurations of $N$ equal charges
on a sphere, \emph{Journal of Physics A: Mathematical and General}
24 (1991), L1369--L1377, Table~1.
\href{https://doi.org/10.1088/0305-4470/24/23/008}{doi:10.1088/0305-4470/24/23/008}.
\url{https://lss.fnal.gov/archive/1991/pub/Pub-91-222-T.pdf}.

\bibitem{cambridge}
D. J. Wales and S. Ulker, Cambridge Cluster Database, Thomson problem,
ten-point entry.
\url{https://www-wales.ch.cam.ac.uk/~wales/CCD/Thomson/table.html}.

\bibitem{schwartz}
R. E. Schwartz, The Five-Electron Case of Thomson's Problem,
\emph{Experimental Mathematics} 22 (2013), 157--186.
\href{https://doi.org/10.1080/10586458.2013.766570}{doi:10.1080/10586458.2013.766570}.
Preprint: The 5 Electron Case of Thomson's Problem, January 21, 2010,
\href{https://arxiv.org/abs/1001.3702}{arXiv:1001.3702}.

\bibitem{andreev}
N. N. Andreev, An extremal property of the icosahedron,
\emph{East Journal on Approximations} 2 (1996), no.~4, 459--462.
\href{https://www.mathnet.ru/eng/person9017}{Author's publication list}.
Review: \href{https://zbmath.org/?q=an:0877.51021}{Zbl 0877.51021}.

\bibitem{cohnkumar}
H. Cohn and A. Kumar, Universally optimal distribution of points on
spheres, \emph{Journal of the American Mathematical Society} 20 (2007),
99--148. \href{https://arxiv.org/abs/math/0607446}{arXiv:math/0607446}.

\bibitem{concurrent}
\texttt{saberwatchmanga} (formerly \texttt{terry2418}),
Lean-verified local minimality for ten charges on a sphere
(October 7, 2026), and A Lean-checked distance restriction for ten charges
on a sphere (October 11, 2026).
\url{https://github.com/saberwatchmanga/-lean-finite-certificates}.

\bibitem{n7}
H. Tran, A Lean Proof of the Thomson Problem for Seven Electrons,
Vals AI blog,
September 28, 2026.
\url{https://www.vals.ai/blogs/thomson-n7-lean-proof}.

\bibitem{n8}
L. Kryvonos, L. Liehr and M. A. Taylor, Energy minimization for eight
points on the sphere, September 18, 2026.
\href{https://arxiv.org/abs/2609.22077}{arXiv:2609.22077}.

\bibitem{n8warrant}
J. Tooby-Smith and A. Zughaid, \texttt{Thomson-N-8-Warrant},
Lean-checked warrant for the eight-point Coulomb Thomson problem,
September 2026.
\url{https://github.com/jstoobysmith/Thomson-N-8-Warrant}.

\bibitem{zarco5}
A. Zarco (\texttt{alejandrozarco}), \emph{Five points on the sphere: exact
three-point certificates for the Riesz energies $s=1,\dots,6$, and Lean
formalisations for $s=1$ (Coulomb) and $s=2$}, October 2026.
\href{https://doi.org/10.5281/zenodo.23125753}{doi:10.5281/zenodo.23125753}.
\url{https://github.com/alejandrozarco/five-points-riesz}.

\bibitem{zarco7}
A. Zarco (\texttt{alejandrozarco}), \emph{The pentagonal bipyramid as the unique
logarithmic-energy minimiser for seven points on the sphere: an unreviewed
Lean 4 warrant (Conjecture 1 of Armentano et al.)}, September--October 2026, with a Coulomb second check
added October 8, 2026.
\href{https://doi.org/10.5281/zenodo.23086382}{doi:10.5281/zenodo.23086382}.
\url{https://github.com/alejandrozarco/thomson-n7-log}.

\bibitem{n9}
A. Karthigeyan (director and publisher), \texttt{thomson-n9-lean},
MIT-licensed Lean code, AI-generated by Anthropic's Opus 5.5 and OpenAI's
GPT-6 Astra, unreviewed,
revision \texttt{168ff0c}, October 6, 2026.
\url{https://github.com/aravindkarthigeyan/thomson-n9-lean}.

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

\bibitem{cohnwoo}
H. Cohn and J. Woo, Three-point bounds for energy minimization,
\emph{Journal of the American Mathematical Society} 25 (2012), 929--958.
\href{https://arxiv.org/abs/1103.0485}{arXiv:1103.0485}.
\end{thebibliography}

```

## Earlier README credits, with person references rephrased

```text
[Karthigeyan's October 6, 2026 project](https://github.com/aravindkarthigeyan/thomson-n9-lean/blob/168ff0c98cab4dfda0460ba55f8d169070ac385e/README.md) proves the nine-point tricapped trigonal prism uniquely optimal. Its README says it was AI-generated by Anthropic's Opus 5.5 and OpenAI's GPT-6 Astra under Karthigeyan's direction, is unreviewed, and is a research release requesting external review. We substantially adapt its Lean code, certificate design, window classification and local-to-global argument. Our contribution is the $N=10$ instance and its certificates. [THIRD_PARTY.md](THIRD_PARTY.md) records origins, changes and the MIT license; upstream prose was not copied.

Classical credits include [Föppl (1912), N = 4](https://www.mathunion.org/fileadmin/ICM/Proceedings/ICM1912.2/ICM1912.2.ocr.pdf), [Yudin (1992; English translation 1993), N = 6](https://www.mathnet.ru/eng/dm737), and [Schwartz (2010 preprint; 2013 journal), N = 5](https://arxiv.org/abs/1001.3702). For $N=12$, [Andreev (1996)](https://zbmath.org/?q=an:0877.51021) proves that the icosahedron maximizes the product of distances and, as its review records, claims the Coulomb case; [Cohn and Kumar (2007)](https://arxiv.org/html/math/0607446) credit Andreev with the icosahedron as the unique minimum and prove universal optimality, which covers Coulomb energy, for the tetrahedron, octahedron and icosahedron.

[Hung Tran (September 2026, on the Vals AI blog)](https://www.vals.ai/blogs/thomson-n7-lean-proof) gave an AI-assisted Lean proof of unique optimality for $N=7$: Tran fixed the Lean statements and deployed ten agents running Anthropic's Sonnet 5.5, which did the proof work in about 15 hours, and Tran ran five checks on the result. [Kryvonos, Liehr and Taylor (September 2026)](https://arxiv.org/abs/2609.22077) proved unique Coulomb and logarithmic optimality for $N=8$, with Lean verification. [Joseph Tooby-Smith and Alex Zughaid (September 2026)](https://github.com/jstoobysmith/Thomson-N-8-Warrant/blob/2c35d62e07d72686931da4bc3e062d668e858eda/README.md) also supplied a Lean-checked $N=8$ Coulomb warrant. Their README describes it as a formal check that the square antiprism solves the eight-point case uniquely, and calls it a complete warrant, not a proof, that is still a work in progress; it does not state uniqueness up to orthogonal maps and relabeling. Alex Zarco's AI-produced, unreviewed Lean warrants (September–October 2026) cover two smaller cases: [five points](https://github.com/alejandrozarco/five-points-riesz/blob/aeb4588ccbb1ccb91c315fedeb79a18042b5fe13/README.md), where a single sharp three-point certificate, with a finite enumeration for uniqueness, shows the triangular bipyramid uniquely minimizes Coulomb energy (known from Schwartz), and [seven points (Conjecture 1 of Armentano et al.)](https://github.com/alejandrozarco/thomson-n7-log/blob/fd2f8b2e7eb0e89ba4f82f6d2c3e98862f89bc28/README.md), chiefly logarithmic energy, with a second check of Tran's Coulomb theorem added October 8 that uses Tran's local lemma.

The bounds build on [Delsarte–Goethals–Seidel (1977)](https://doi.org/10.1007/BF03187604), Yudin, [Bachoc–Vallentin (2008)](https://arxiv.org/abs/math/0608426) and [Cohn–Woo (2012)](https://arxiv.org/abs/1103.0485).

Concurrent work by saberwatchmanga (formerly terry2418) proves [N = 10 local minimality (October 7, 2026)](https://github.com/saberwatchmanga/-lean-finite-certificates/tree/7ba9eb38db36c9cb957ff26758b66bbacc31d8bc/Thomson10LocalMinimum) and [a chord bound (October 11, 2026)](https://github.com/saberwatchmanga/-lean-finite-certificates/tree/bc74bc050f4c39123e894b3fd3873ba17f60289a/Thomson10Chord1935), not global optimality. Neither is a premise here. Both chord and separation arguments use $32.717$, the candidate energy rounded upward; we cannot establish whether our cutoff was chosen independently or taken from that work.

The enclosure agrees with the numerical energy of [Erber–Hockney (1991)](https://lss.fnal.gov/archive/1991/pub/Pub-91-222-T.pdf) and the $D_{4d}$ entry in the [Cambridge Cluster Database](https://www-wales.ch.cam.ac.uk/~wales/CCD/Thomson/table.html). Numerical identification, rigorous proof and formal proof with uniqueness are distinct. To our knowledge no earlier rigorous proof for $N=10$ exists, and we make no priority claim.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).


```

## Earlier attribution wording

```text
The content of the certificate is threefold. First, the sum of $K$ over
all ordered triples of distinct indices is nonnegative for every
configuration of ten unit vectors. This is the three-point positivity
of Bachoc--Vallentin and Cohn--Woo~\cite{bachoc,cohnwoo}, with the
repeated-index corrections specified in Appendix~\ref{app:kernels}.
Second, $W$ is a sum of weighted polynomial squares, and is nonnegative
on the \emph{capped Gram domain}
$u,v,t\in[-1,13/20]$, $1+2uvt-u^2-v^2-t^2\geq0$.
The six weights are listed in Appendix~\ref{app:certificates}.
Third, the sum $\|\mathcal R\|_1$ of the absolute values of the residual's
rational coefficients is tiny:
$\|\mathcal R\|_1\approx1.1673222012517146\cdot10^{-56}$.
Every residual monomial has absolute value at most one on this domain,
so this coefficient sum bounds the residual pointwise.
```
