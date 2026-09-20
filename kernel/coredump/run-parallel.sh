#!/bin/bash
# Run every configuration at the same time on a big machine.
# ./run-parallel.sh [workers-per-run] [heap-per-run]
cd "$(dirname "$0")"
w=${1:-32}; h=${2:-24g}
export TLA2TOOLS=${TLA2TOOLS:-$PWD/tla2tools.jar} TLC_HEAP=$h
export TLC_METADIR=${TLC_METADIR:-/tmp/$USER-tlc-coredump}
mkdir -p logs
cfgs=($(ls *.cfg | sed 's/\.cfg$//' | grep -v -e '^IoWqExitBit' -e '^CorePattern'))
for cfg in "${cfgs[@]}"; do
    ./check.sh "$cfg" "$w" > /dev/null 2>&1 &
done
wait
printf '%-26s %-10s %-12s %-10s %s\n' config expected result states check > logs/summary.txt
for cfg in "${cfgs[@]}"; do
    expect=$(sed -n 's/.*expected: //p' "$cfg.cfg")
    log=logs/$cfg.log
    if grep -q 'TLC threw an unexpected exception\|Parsing or semantic analysis failed\|Assertion' "$log"; then result=ERROR
    elif grep -q 'Invariant .* is violated\|Temporal properties were violated' "$log"; then result=violation
    elif grep -q 'Model checking completed. No error has been found' "$log"; then result=pass
    else result=unknown; fi
    states=$(sed -n 's/^\([0-9]*\) states generated, \([0-9]*\) distinct states found.*/\2/p' "$log" | tail -1)
    mark=$([ "$result" = "$expect" ] && echo ok || echo MISMATCH)
    printf '%-26s %-10s %-12s %-10s %s\n' "$cfg" "$expect" "$result" "$states" "$mark" >> logs/summary.txt
done
echo ALL-DONE >> logs/summary.txt
