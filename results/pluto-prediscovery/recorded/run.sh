#!/usr/bin/env bash
set -euo pipefail

usage() {
    echo "Usage: recorded/run.sh WORK {methodA-december|methodA-february|ma733|fixed-positions|catalogs|shape|weak-trails|orbits|all} [...]" >&2
    exit 2
}
(( $# >= 2 )) || usage
for step in "${@:2}"; do
    case "$step" in
        methodA-december|methodA-february|ma733|fixed-positions|catalogs|shape|weak-trails|orbits|all) ;;
        *) usage ;;
    esac
done

S=$(cd -- "$(dirname -- "$0")" && pwd)
A="$S/method-a"
B="$S/method-b"
mkdir -p -- "$1"
W=$(cd -- "$1" && pwd)
shift
P=${PYTHON:-python3}
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MPLBACKEND=Agg
export PYTHONDONTWRITEBYTECODE=1
mkdir -p "$W/receipts" "$W/inputs"

# Use an outside process-group timeout and save the resource receipt separately.
unit() {
    local name=$1
    shift
    /usr/bin/time -v -o "$RECEIPTS/$name.time" timeout --kill-after=5s 540s "$@"
}
json() {
    local out=$1
    shift
    unit "$(basename "$out" .json)" "$@" > "$out.part"
    mv -- "$out.part" "$out"
}
cached() {
    local file=$1
    shift
    if [[ ! -s "$file" ]]; then
        unit "$(basename "$file")" "$@"
    fi
}
download() {
    local file=$1 url=$2
    if [[ ! -s "$file" ]]; then
        unit "$(basename "$file")" curl -fsSL --retry 2 "$url" -o "$file.part"
        mv -- "$file.part" "$file"
    fi
}
mosaic() {
    local plate=$1
    cached "$W/inputs/${plate}_mosaic.fits.fz" "$P" "$B/fetch_plates.py" "$W/inputs" "$plate"
}
tracks() {
    local plate=$1
    shift
    for body in "$@"; do
        cached "$W/inputs/hz_${plate}_${body}.npz" "$P" "$B/hz2.py" "$W/inputs" "$plate" "$body"
    done
}

method_a_december() {
    local d="$W/methodA-december" raw="$W/methodA-december/inputs"
    mkdir -p "$d/scratch"
    unit fetch "$P" "$A/fetch.py" "$raw" > "$d/downloads.sha256"
    unit extra-inputs "$P" "$A/extra_inputs.py" "$raw"
    json "$d/historical.json" "$P" "$A/measure.py" "$raw" historical --open-track
    json "$d/archive-clock-pair.json" "$P" "$A/measure.py" "$raw" pair --open-track
    local check_status=0
    unit check-archive "$P" "$A/check.py" "$d/archive-clock-pair.json" || check_status=1
    unit archive-site "$P" "$A/site_check.py" "$raw" "$d/archive-clock-pair.json" > "$d/archive-site.jsonl"
    json "$d/archive-site.json" "$P" "$S/inputs.py" json-lines "$d/archive-site.jsonl"
    for plate in ma00731 ma00733; do
        json "$d/$plate-179.json" "$P" "$A/plate_clock.py" "$d/scratch" "$plate" 179
        local hour=-5.80203
        [[ $plate == ma00731 ]] || hour=-5.34139
        for body in 1436 2891; do
            json "$d/$plate-$body.json" "$P" "$A/plate_clock.py" "$d/scratch" "$plate" "$body" --test-hour="$hour"
        done
    done
    unit correct-clock "$P" "$A/correct_clock.py" "$raw" "$d/fixed" "$d/ma00731-179.json" "$d/ma00733-179.json"
    json "$d/controls.json" "$P" "$A/measure.py" "$d/fixed" pair
    json "$d/corrected-pair.json" "$P" "$A/measure.py" "$d/fixed" pair --open-track
    unit check-corrected "$P" "$A/check.py" "$d/corrected-pair.json" || check_status=1
    json "$d/diagnostics.json" "$P" "$A/pair_diagnostics.py" "$d/fixed" "$d/corrected-pair.json" --figure "$d/december-pair.png"
    json "$d/native.json" "$P" "$A/native_stamps.py" "$d/fixed" "$d/scratch"
    json "$d/catalogue.json" "$P" "$A/catalogue_checks.py" "$d/fixed" "$d/ma00731-179.json" "$d/ma00733-179.json"
    download "$d/scratch/de421.bsp" https://ssd.jpl.nasa.gov/ftp/eph/planets/bsp/de421.bsp
    json "$d/ma00731-geometry.json" "$P" "$A/audit_ma731.py" "$d/fixed" "$d/scratch/de421.bsp" "$d/corrected-pair.json"
    for y in 0 1 2; do
        for x in -2 -1 0 1 2; do
            [[ $x,$y != 0,0 ]] || continue
            json "$d/null_${x}_${y}.json" "$P" "$A/field_nulls.py" "$d/fixed" "$d/scratch" "$d/corrected-pair.json" "$x" "$y"
        done
    done
    for plate in B3383a B3384b; do
        json "$d/$plate.json" "$P" "$A/heidelberg_control.py" "$d/scratch" "$plate"
    done
    return "$check_status"
}

method_a_february() (
    mkdir -p "$W/methodA-february"
    cd "$W/methodA-february"
    for field in tracks k179 k168 k417 hist pluto aux; do
        unit "feb-$field" "$P" "$A/heidelberg1909_inputs.py" "$field"
    done
    for plate in B2247a B2248b; do
        unit "$plate-clock" "$P" "$A/heidelberg1909_clock.py" "$plate" > "$plate.clock.part"
        mv -- "$plate.clock.part" "$plate.clock"
    done
    unit feb-historic-open "$P" "$A/heidelberg1909_measure.py" historic --open
    for mode in feb fixed; do
        unit "$mode-controls" "$P" "$A/heidelberg1909_measure.py" "$mode"
        unit "$mode-open" "$P" "$A/heidelberg1909_measure.py" "$mode" --open
    done
    unit feb-outputs "$P" "$S/inputs.py" february .
)

ma733() {
    local d="$W/ma733" i="$W/inputs"
    mkdir -p "$d"
    for p in 731 733; do
        mosaic "ma00$p"
        cached "$i/cut$p.npy" "$P" "$B/cut.py" "$i/ma00${p}_mosaic.fits.fz" "$i/cut$p"
        tracks "$p" 999 179
        json "$d/ma00$p-179.json" "$P" "$B/trail.py" "$p" 179 "$i/ma00${p}_mosaic.fits.fz" "$i"
    done
    cached "$i/gaia.fits" "$P" "$B/cats.py" "$i"
    cached "$i/apass.fits" "$P" "$B/apass.py" "$i"
    for p in 731 733; do
        unit "astrom$p" "$P" "$B/astrom.py" "$p" "$i/ma00${p}_mosaic.fits.fz" "$i"
    done
    cached "$i/pluto_hz.json" "$P" "$B/plutohz.py" "$i"
    unit december-measure "$P" "$B/measure.py" "$i"
    unit december-archive "$P" "$B/archpos.py" "$i"
    unit pipeline-ma733 "$P" "$B/pipeline.py" ma733 "$i/ma00733_mosaic.fits.fz" 1 \
        85.872769077 16.017045092 85.873938791 16.017012857 85.871596225 16.017076450 1908.976 16.33 "$i"
    unit robust-ma733 "$P" "$B/robust.py" "$i" "$i" 733
    unit ma733-output "$P" "$S/inputs.py" ma733 "$i" "$d"
}

fixed_positions() {
    local d="$W/fixed-positions"
    local workers=${FIXED_JOBS:-1}
    [[ $workers =~ ^[1-9][0-9]*$ ]] || { echo "FIXED_JOBS must be a positive integer" >&2; return 2; }
    mkdir -p "$d/cutouts"
    for position in december february; do
        local key=ma731 ra=85.893709844 dec=16.016634745 tag=
        if [[ $position == february ]]; then
            key=1909 ra=84.9614918 dec=16.1337235 tag=1909
        fi
        local dates="$d/exps_${key}pos.json"
        json "$dates" "$P" "$S/inputs.py" exposures "$ra" "$dec"
        unit "$position-plates" "$P" "$S/inputs.py" plates "$dates" > "$d/$position-plates.txt"
        local status=0
        local -a plates=() pids=()
        mapfile -t plates < "$d/$position-plates.txt"
        # The first plate populates the common catalogues before the parallel units.
        if (( ${#plates[@]} )); then
            fixed_plate "${plates[0]}" || status=1
        fi
        for plate in "${plates[@]:1}"; do
            fixed_plate "$plate" &
            pids+=("$!")
            if (( ${#pids[@]} == workers )); then
                for pid in "${pids[@]}"; do wait "$pid" || status=1; done
                pids=()
            fi
        done
        for pid in "${pids[@]}"; do wait "$pid" || status=1; done
        json "$d/$position.json" "$P" "$S/inputs.py" fixed "$d" "$tag" "$d/$position-plates.txt" || status=1
        (( status == 0 )) || return "$status"
    done
}

fixed_plate() {
    local file="$d/fixedpos${tag:+_$tag}_$1.json"
    if [[ ! -s "$file" ]]; then
        POS_RA=$ra POS_DEC=$dec POS_TAG=$tag \
            unit "fixed-$position-$1" "$P" "$B/fixedpos.py" "$d" "$d/cutouts" "$1"
    fi
}

catalogs() {
    local d="$W/catalogs"
    mkdir -p "$d" "$d/february"
    unit catalogs-december "$P" "$B/deepcats.py" "$d"
    POS_RA=84.9614918 POS_DEC=16.1337235 POS_TAG=1909 \
        unit catalogs-february "$P" "$B/deepcats.py" "$d/february"
    json "$d/february/B2247a-gaia.json" "$P" "$S/inputs.py" february-gaia "$d/february" "$W/methodA-february/pluto.csv"
    cached "$W/inputs/gaia.fits" "$P" "$B/cats.py" "$W/inputs"
}

shape() {
    local d="$W/shape"
    mkdir -p "$d"
    mosaic ma00731
    unit defect "$P" "$B/defect.py" "$W/inputs" "$d" "$d/profile.png"
    unit srcshape "$P" "$B/srcshape.py" "$W/inputs" "$d" "$d/srcshape.json" \
        3.59:271.5 10:270 20:270 37.7:270 51.5:277.7 59.7:243.1
}

weak_trails() {
    local d="$W/weak-trails" i="$W/inputs"
    mkdir -p "$d"
    local bodies=(179 1436 2891 4204 2175 3147 9593 13567 25493)
    for p in 731 733; do
        mosaic "ma00$p"
        tracks "$p" "${bodies[@]}"
        for body in "${bodies[@]}"; do
            json "$d/ma00$p-$body.json" "$P" "$B/trail.py" "$p" "$body" "$i/ma00${p}_mosaic.fits.fz" "$i"
        done
    done
    unit forced-windows "$P" "$B/forcedwin.py" "$i" > "$d/forced-windows.txt"
    unit stack-clock "$P" "$B/stackclock.py" "$i" > "$d/stack-clock.txt"
    unit weak-output "$P" "$S/inputs.py" weak "$d"
}

orbits() {
    local d="$W/orbits" n="$W/orbits/nbody"
    mkdir -p "$d/ephem" "$n"
    download "$d/ephem/linux_p1550p2650.440" https://ssd.jpl.nasa.gov/ftp/eph/planets/Linux/de440/linux_p1550p2650.440
    download "$d/ephem/sb441-n16.bsp" https://ssd.jpl.nasa.gov/ftp/eph/small_bodies/asteroids_de441/sb441-n16.bsp
    if [[ ! -s "$d/orbits.json" ]]; then
        json "$d/orbits.json" "$P" "$S/inputs.py" sbdb
    fi
    cached "$d/planets.json" "$P" "$B/sbplanets.py" "$d/planets.json"
    local elements="$d/orbits.json"
    case "${ORBIT_MODE:-validate}" in
        validate)
            json "$d/sample.json" "$P" "$S/inputs.py" sample "$elements"
            elements="$d/sample.json"
            n="$d/validation"
            mkdir -p "$n"
            unit orbit-rest-sample "$P" "$B/sbnbody.py" "$elements" "$d/planets.json" "$n" 0 1 rest
            unit orbit-neo-sample "$P" "$B/sbassist.py" "$elements" "$d/ephem" "$n" 0 1
            ;;
        full)
            for (( c=0; c<64; c++ )); do
                local shard
                printf -v shard 'rest%03d' "$c"
                cached "$n/$shard.npz" "$P" "$B/sbnbody.py" "$elements" "$d/planets.json" "$n" "$c" 64 rest
            done
            for (( c=0; c<40; c++ )); do
                local shard
                printf -v shard 'neo%03d' "$c"
                cached "$n/$shard.npz" "$P" "$B/sbassist.py" "$elements" "$d/ephem" "$n" "$c" 40
            done
            unit orbit-horizons "$P" "$B/knownsb.py" "$elements" "$n" "$d/ma00731-approaches.json" c
            ;;
        *) echo "ORBIT_MODE must be validate or full" >&2; return 2 ;;
    esac
    for group in rest neo; do
        unit "validate-$group" "$P" "$B/sbvalidate.py" "$elements" "$n" 20 "$group"
        mv -- "$n/validate_$group.json" "$d/ma00731-validation-$group.json"
    done
}

steps=()
for step in "$@"; do
    if [[ $step == all ]]; then
        steps+=(methodA-december methodA-february ma733 fixed-positions catalogs shape weak-trails orbits)
    else
        steps+=("$step")
    fi
done
for step in "${steps[@]}"; do
    RECEIPTS="$W/receipts/$step"
    mkdir -p "$RECEIPTS"
    case $step in
        methodA-december) method_a_december ;;
        methodA-february) method_a_february ;;
        ma733) ma733 ;;
        fixed-positions) fixed_positions ;;
        catalogs) catalogs ;;
        shape) shape ;;
        weak-trails) weak_trails ;;
        orbits) orbits ;;
    esac
done
