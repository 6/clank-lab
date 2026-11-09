#!/bin/sh
# Build bnf against CAPD 6.1.0 (NATIVE intervals) installed at $CAPD.
# CAPD's normalForms.h does not compile for complex<interval> jets (its
# factorial is converted through TypeTraits<complex>::Real); the overlay below
# patches only that conversion and leaves every formula unchanged.
set -e
CAPD=${CAPD:?set CAPD to the CAPD install directory}
OUT=${OUT:?set OUT to the build directory}
mkdir -p "$OUT/include/capd/normalForms"
sed 's/typename capd::TypeTraits<ScalarType>::Real fac = mp.factorial();/double fac = (double)mp.factorial();/' \
  "$CAPD/include/capd/normalForms/normalForms.h" > "$OUT/include/capd/normalForms/normalForms.h"
cp "$CAPD/include/capd/normalForms/planarMaps.hpp" "$CAPD/include/capd/normalForms/linearSubstitution.hpp" "$OUT/include/capd/normalForms/"
# The pinned capd-config wrapper joins its pkg-config directory to the
# inherited path using PATH_SEPARATOR, which it does not define itself.
# Separate assignments make a failed lookup stop this script before g++.
cflags=$(PATH_SEPARATOR=: "$CAPD/bin/capd-config" --cflags)
libs=$(PATH_SEPARATOR=: "$CAPD/bin/capd-config" --libs)
# Deliberate word splitting: pkg-config returns lists of compiler/linker flags.
g++ -I"$OUT/include" $cflags -o "$OUT/bnf" "$(dirname "$0")/bnf.cpp" $libs
echo "built $OUT/bnf"
