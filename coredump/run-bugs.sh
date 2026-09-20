#!/bin/bash
# Wait for the green batch, then run every configuration that switches a fix off.
cd "$(dirname "$0")"
while pgrep -f 'check-all.sh signals_fixed' >/dev/null; do sleep 5; done
printf '%-26s %-10s %-12s %s\n' config expected result states > logs/summary-bugs.txt
for cfg in signals_no_rcu signals_no_retarget signals_retarget_only signals_sigpending_only signals_no_freezer \
           sqpoll_deadlock sqpoll_mask_only sqpoll_no_gate_signaled plain_strict plain_no_exec_cancel cdhole_no_gate; do
    expect=$(sed -n 's/.*expected: //p' "$cfg.cfg")
    ./check.sh "$cfg" "${TLC_WORKERS:-8}" > /dev/null 2>&1
    log=logs/$cfg.log
    if grep -q 'TLC threw an unexpected exception\|Parsing or semantic analysis failed\|Assertion' "$log"; then result=ERROR
    elif grep -q 'Invariant .* is violated\|Temporal properties were violated' "$log"; then result=violation
    elif grep -q 'Model checking completed. No error has been found' "$log"; then result=pass
    else result=unknown; fi
    states=$(sed -n 's/^\([0-9]*\) states generated, \([0-9]*\) distinct states found.*/\2/p' "$log" | tail -1)
    mark=$([ "$result" = "$expect" ] && echo ok || echo MISMATCH)
    printf '%-26s %-10s %-12s %-10s %s\n' "$cfg" "$expect" "$result" "$states" "$mark" >> logs/summary-bugs.txt
done
echo BUGS-DONE >> logs/summary-bugs.txt
