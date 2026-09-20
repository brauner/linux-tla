#!/bin/bash
# Run every configuration at the same time on a big machine.
# ./run-parallel.sh [workers-per-run] [heap-per-run]
cd "$(dirname "$0")"
w=${1:-32}; h=${2:-24g}
export TLA2TOOLS=${TLA2TOOLS:-$PWD/tla2tools.jar} TLC_HEAP=$h
export TLC_METADIR=${TLC_METADIR:-/tmp/$USER-tlc-close_range}
mkdir -p logs
cfgs=($(ls *.cfg | sed 's/\.cfg$//'))
for cfg in "${cfgs[@]}"; do
    opts=; [ "$cfg" = refine_new_w4 ] && opts="-maxSetSize 2000000"
    TLC_OPTS=$opts ./check.sh "$cfg" "$w" > /dev/null 2>&1 &
done
wait
./summarize.sh > /dev/null
echo ALL-DONE >> logs/summary.txt
