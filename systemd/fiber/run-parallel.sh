#!/bin/bash
# Start every configuration (or the ones named) at the same time, each detached
# like ./start.sh: ./run-parallel.sh [workers-per-run] [heap-per-run] [cfg...]
# Configurations that already passed or failed as expected are skipped, so the
# script can be re-run after a crash or a reboot to pick up what is missing
# (./resume.sh continues a dead run from its checkpoint instead).
# ./status.sh shows how they are doing; ./summarize.sh writes logs/summary.txt.
cd "$(dirname "$0")"
w=${1:-8}; h=${2:-8g}; [ $# -ge 2 ] && shift 2 || shift $#
cfgs=("$@"); [ ${#cfgs[@]} -eq 0 ] && cfgs=($(ls *.cfg | sed 's/\.cfg$//'))
for cfg in "${cfgs[@]}"; do
    if [ -f "logs/$cfg.log" ] && grep -q 'Model checking completed. No error has been found\|Invariant .* is violated\|Temporal properties were violated\|Deadlock reached' "logs/$cfg.log"; then
        echo "$cfg: done already ($(./status.sh "$cfg" | tail -1 | awk '{print $3}')), skipping"
        continue
    fi
    ./start.sh "$cfg" "$w" "$h"
done
