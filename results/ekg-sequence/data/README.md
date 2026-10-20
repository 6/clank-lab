# Optional numerical illustration

The table illustrates the theorem and is not used in its proof. On Linux
with a C++20 compiler, regenerate its 500-million-term calculation in a
separate work directory:

```sh
g++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -o ekg-table /path/to/data/ekg-table.cpp
./ekg-table 500000000 1000000000 ekg-table.csv ekg-table-summary.json
```

The generator needs about 3.13 GB of array storage. It independently checks
the first 4096 terms by direct gcd search and trial-division smoothing and
rejects a changed prefix. Integer fields and digests can be compared with
the supplied table and summary; final floating-point digits may vary
by platform. For a small check, use `4096 16384` as the two numeric
arguments. The supplied ratios were independently certified with exact
rational logarithm bounds as described in the paper.
