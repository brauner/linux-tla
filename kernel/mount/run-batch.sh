#!/bin/bash
# Run a set of configurations with a concurrency limit and write logs/summary.txt.
# ./run-batch.sh <concurrent> <workers-per-run> <heap> cfg1 cfg2 ...
# (no cfgs: every *.cfg in the directory)
# Configurations whose log already carries a verdict are skipped, so the
# batch can simply be started again after an interruption; unfinished ones
# resume from their TLC checkpoint (see check.sh).
cd "$(dirname "$0")"
par=${1:-8}; w=${2:-16}; h=${3:-16g}; shift 3
cfgs=("$@"); [ ${#cfgs[@]} -eq 0 ] && cfgs=($(ls *.cfg | sed 's/\.cfg$//'))
export TLA2TOOLS=${TLA2TOOLS:-$PWD/tla2tools.jar} TLC_HEAP=$h
export TLC_METADIR=${TLC_METADIR:-/tmp/$USER-tlc-mount}
mkdir -p logs
verdict() {
    local log=logs/$1.log
    [ -f "$log" ] || { echo none; return; }
    if grep -q 'TLC threw an unexpected exception\|Parsing or semantic analysis failed' "$log"; then echo ERROR
    elif grep -q 'is violated\|Temporal properties were violated' "$log"; then echo violation
    elif grep -q 'No error has been found' "$log"; then echo pass
    else echo running; fi
}
todo=()
for cfg in "${cfgs[@]}"; do
    case $(verdict "$cfg") in pass|violation|ERROR) ;; *) todo+=("$cfg");; esac
done
echo "$(date -u +%FT%TZ) batch start: ${#todo[@]} to run, ${#cfgs[@]} total" >> logs/batch.out
printf '%s\n' "${todo[@]}" | xargs -r -P "$par" -I{} sh -c "./check.sh {} $w > /dev/null 2>&1"
{
printf '%-30s %-10s %-10s %-9s %s\n' config expected result states check
for cfg in "${cfgs[@]}"; do
    expect=$(sed -n 's/.*expected: //p' "$cfg.cfg")
    result=$(verdict "$cfg")
    states=$(sed -n 's/^\([0-9]*\) states generated, \([0-9]*\) distinct states found.*/\2/p' "logs/$cfg.log" 2>/dev/null | tail -1)
    mark=$([ "$result" = "$expect" ] && echo ok || echo MISMATCH)
    [ "$states" = "1" ] && mark="$mark (prelude stuck?)"
    printf '%-30s %-10s %-10s %-9s %s\n' "$cfg" "$expect" "$result" "$states" "$mark"
done
echo "$(date -u +%FT%TZ) batch done"
} > logs/summary.txt
cat logs/summary.txt >> logs/batch.out
