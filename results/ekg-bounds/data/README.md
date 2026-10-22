# Data

| File | Contents |
|---|---|
| `cover-p3-13328000000.csv.xz` | the middle-range certificate: one row per interval $[e_a, e_b)$ of frontier values, with the integers `ea, eb, M, Y, Q, hc, bq` of `CoverRow` in `../lean/Statement/TheoremTP3.lean`; the other columns are decimal values for information only, and the checker ignores them |
| `prefix-checkpoints.txt` | the recorded results of both prefix programs to $1.6 \times 10^{10}$ terms, compared line by line by `../checks/check.py` |
| `figure.py` | draws the figure of $a(n)/n$ (optional; requires matplotlib) |
| `figure-data.csv`, `ratio.pdf`, `ratio.svg` | its output: the plotted values, and the figure for the paper and the README |

The figure is an illustration and is not part of the proof. `figure.py`
computes $a(1..10^6)$ from the definition; `python3 checks/check.py quick`
checks every value in `figure-data.csv` against the prefix programs'
output.
