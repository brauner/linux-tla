#!/bin/bash
# One line per configuration: what its run is doing.  ./status.sh [cfg...]
# States: pass, violation, ERROR (TLC gave up), running (with the last progress
# line), dead (no process and no result; says whether a checkpoint exists for
# ./resume.sh), never (no log).
cd "$(dirname "$0")"
cfgs=("$@"); [ ${#cfgs[@]} -eq 0 ] && cfgs=($(ls *.cfg | sed 's/\.cfg$//'))
printf '%-32s %-10s %-10s %s\n' config expected state detail
for cfg in "${cfgs[@]}"; do
    expect=$(sed -n 's/.*expected: //p' "$cfg.cfg" | head -1)
    log=logs/$cfg.log; detail=
    pid=$(cat "logs/$cfg.pid" 2>/dev/null); alive=0
    [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null && alive=1
    if [ ! -f "$log" ]; then state=never
    elif grep -q 'TLC threw an unexpected exception\|Parsing or semantic analysis failed\|Assertion\|OutOfMemory\|when writing the disk\|Semantic errors' "$log"; then
        state=ERROR; detail=$(grep -m1 'Exception\|Error\|Assertion\|failed' "$log" | cut -c1-80)
    elif grep -q 'Invariant .* is violated\|Temporal properties were violated\|is not a valid\|Deadlock reached' "$log"; then
        state=violation; detail="$(grep -m1 -o 'Invariant [A-Za-z]* is violated\|Temporal properties were violated\|Deadlock reached' "$log"), $(sed -n 's/^\([0-9]*\) states generated, \([0-9]*\) distinct.*/\2 states/p' "$log" | tail -1), $(sed -n 's/^Finished in \(.*\) at .*/\1/p' "$log" | tail -1)"
    elif grep -q 'Model checking completed. No error has been found' "$log"; then
        state=pass; detail="$(sed -n 's/^\([0-9]*\) states generated, \([0-9]*\) distinct.*/\2 states/p' "$log" | tail -1), $(sed -n 's/^Finished in \(.*\) at .*/\1/p' "$log" | tail -1)"
    elif [ $alive = 1 ]; then
        state=running; detail="pid $pid, $(grep -E '^(Progress|Checking|Finished checking)' "$log" | tail -1 | cut -c1-110)"
    else
        chk=$(sed -n 's/^Checkpointing of run //p' "$log" | tail -1)
        state=dead
        if [ -n "$chk" ] && grep -q '^Checkpointing completed' "$log" && [ -d "$chk" ]; then detail="checkpoint $(grep '^Checkpointing completed' "$log" | tail -1 | sed 's/.*at (\(.*\))/\1/'), ./resume.sh $cfg"
        else detail="no checkpoint, ./start.sh $cfg"; fi
    fi
    case $state in pass|violation) [ "$state" = "$expect" ] && detail="$detail, ok" || detail="$detail, MISMATCH";; esac
    printf '%-32s %-10s %-10s %s\n' "$cfg" "$expect" "$state" "$detail"
done
