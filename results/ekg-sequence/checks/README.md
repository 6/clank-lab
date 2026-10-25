# Checking details

The standard proof commands and exact statements are in
[the Lean README](../lean/README.md). The paper gives the full written
proof and distinguishes its written deductions from separate Lean theorems.
[Detailed source interfaces](details.tex) retain the axiom output, file map
and statement-by-statement correspondence. The optional numerical
illustration is described in [data/README.md](../data/README.md).

[Source context](context.tex) records the exact prior-work expressions and
convention comparisons used by the paper, with their original references.
It adds no theorem or verification claim.


The inherited PNT source comments cite
[Romyar Sharifi's Algebraic number theory notes](https://www.math.ucla.edu/~sharifi/algnum.pdf).
Theorem 7.1.12 supports the continuation and simple-pole portion of the
comment that cites it; it does not itself assert nonvanishing on the whole
line with real part 1. Corollary 7.2.3 states Dirichlet density, rather than
by itself the stronger weighted asymptotic mentioned in the surrounding
comment. These qualifications concern source commentary. The imported
files and the audited Lean proofs remain unchanged.

The main endpoint was independently checked on October 18, 2026, on a
12-core Linux ARM64 system in 23 minutes 22 seconds (1,316 user seconds,
57 system seconds, peak memory 4.8 GiB). That check included the canonical
sequence and smoothing tests and rejection of a changed coefficient.
It preceded the later consequence files and is a historical validation of
the main endpoint, rather than a timing of this presentation edition.

The TeX notes reuse the paper's notation, macros and bibliography. To make
an optional reading copy containing them, run the following from the
bundle root with Python 3 and a LaTeX installation:

```sh
python3 - <<'PYNOTES'
from pathlib import Path
paper = Path("paper/paper.tex").read_text()
notes = (r"\begingroup\sloppy" + "\n" + r"\input{checks/context.tex}"
         + "\n" + r"\input{checks/details.tex}" + "\n" + r"\endgroup")
Path("paper-with-notes.tex").write_text(
    paper.replace(r"\end{appendices}", notes + "\n" + r"\end{appendices}", 1))
PYNOTES
pdflatex -interaction=nonstopmode -halt-on-error paper-with-notes.tex
pdflatex -interaction=nonstopmode -halt-on-error paper-with-notes.tex
```

The numerical data README and frozen summary describe the earlier
nine-decimal display, retained in the source-context notes. The present
paper uses the same values rounded to four places; rational-log
certification details are in the detailed source interfaces above.

The frozen numerical README's reference to certification "in the paper"
now refers to the detailed checking notes, under "Numerical illustration".
The proof data and its original README are preserved byte-for-byte.
