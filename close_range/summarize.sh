#!/bin/bash
# Build logs/summary.txt from whatever logs/*.log exist.
cd "$(dirname "$0")"
printf '%-20s %-10s %-12s %-10s %-12s %s\n' config expected result states time check > logs/summary.txt
for log in logs/*.log; do
    cfg=${log#logs/}; cfg=${cfg%.log}
    [ -f "$cfg.cfg" ] || continue
    expect=$(sed -n 's/.*expected: //p' "$cfg.cfg")
    if grep -q 'TLC threw an unexpected exception\|Parsing or semantic analysis failed\|Assertion\|OutOfMemory\|when writing the disk' "$log"; then result=ERROR
    elif grep -q 'Invariant .* is violated\|Temporal properties were violated' "$log"; then result=violation
    elif grep -q 'Model checking completed. No error has been found' "$log"; then result=pass
    else result=running; fi
    states=$(sed -n 's/^\([0-9]*\) states generated, \([0-9]*\) distinct states found.*/\2/p' "$log" | tail -1)
    mark=$([ "$result" = "$expect" ] && echo ok || echo MISMATCH)
    took=$(sed -n 's/^Finished in \(.*\) at .*/\1/p' "$log" | tail -1 | tr -d ' ')
    printf '%-20s %-10s %-12s %-10s %-12s %s\n' "$cfg" "$expect" "$result" "$states" "${took:--}" "$mark" >> logs/summary.txt
done
cat logs/summary.txt
