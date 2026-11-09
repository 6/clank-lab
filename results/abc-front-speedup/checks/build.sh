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
g++ -I"$OUT/include" $("$CAPD/bin/capd-config" --cflags) -o "$OUT/bnf" "$(dirname "$0")/bnf.cpp" $("$CAPD/bin/capd-config" --libs)
echo "built $OUT/bnf"
