#!/bin/bash
# Run every configuration (or the ones named on the command line) one after
# the other and print a summary.  ./check-all.sh [cfg...]
cd "$(dirname "$0")"
cfgs=("$@")
[ ${#cfgs[@]} -eq 0 ] && cfgs=($(ls *.cfg | sed 's/\.cfg$//'))
mkdir -p logs
printf '%-26s %-10s %-12s %s\n' config expected result states > logs/summary.txt
for cfg in "${cfgs[@]}"; do
    expect=$(sed -n 's/.*expected: //p' "$cfg.cfg")
    ./check.sh "$cfg" "${TLC_WORKERS:-8}" > /dev/null 2>&1
    log=logs/$cfg.log
    if grep -q 'TLC threw an unexpected exception\|Parsing or semantic analysis failed\|Assertion' "$log"; then
        result=ERROR
    elif grep -q 'Invariant .* is violated\|Temporal properties were violated\|is not a valid' "$log"; then
        result=violation
    elif grep -q 'Model checking completed. No error has been found' "$log"; then
        result=pass
    else
        result=unknown
    fi
    states=$(sed -n 's/^\([0-9]*\) states generated, \([0-9]*\) distinct states found.*/\2/p' "$log" | tail -1)
    mark=$([ "$result" = "$expect" ] && echo ok || echo MISMATCH)
    printf '%-26s %-10s %-12s %-10s %s\n' "$cfg" "$expect" "$result" "$states" "$mark" | tee -a logs/summary.txt
done
