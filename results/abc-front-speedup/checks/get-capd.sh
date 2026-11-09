#!/bin/sh
# Fetch and build CAPD 6.1.0 (github.com/CAPDGroup/CAPD at the pinned commit)
# with NATIVE intervals (its bundled filib does not build on arm64).
# Installs to $CAPD. About 75 CPU-seconds, 0.5 GB.
set -e
CAPD=${CAPD:?set CAPD to the install directory}
SRC=${SRC:?set SRC to the source directory}
COMMIT=37057e5899bccaa6cd5701057b7e6ea5e232ef8b
[ -d "$SRC/.git" ] || git clone -q https://github.com/CAPDGroup/CAPD.git "$SRC"
git -C "$SRC" checkout -q "$COMMIT"
mkdir -p "$SRC/build" && cd "$SRC/build"
cmake .. -DCAPD_INTERVAL_TYPE=NATIVE -DCAPD_BUILD_ALL=OFF -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$CAPD" > cmake.log
make -j2 > make.log && make install > install.log
echo "CAPD $COMMIT installed in $CAPD"
