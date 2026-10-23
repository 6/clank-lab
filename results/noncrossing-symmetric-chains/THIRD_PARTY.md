# Third-party material

The paper, mathematical input data, certificates, Lean development, and checker
sources in this folder are distributed under Apache-2.0. No third-party source
code, executable, or article file is included. The group constructions are
new implementations of the mathematical root data cited in the paper,
including the roots and generating reflections described by Oura and
Sekiguchi. The cited papers' programs are not copied into this bundle.

The checks use separately installed Python, Node.js, GAP with its standard
libraries and the SmallGrp identification package, and Lean with its bundled
standard library. Each dependency remains under its upstream license;
invoking an independently installed program does not relicense it. In
particular, GAP and SmallGrp are installed dependencies, not redistributed
material. Installation requirements are recorded in the README and
[checks/README.md](checks/README.md).
