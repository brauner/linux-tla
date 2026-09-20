#!/bin/bash
# Start every configuration (or the ones named) at the same time on a big
# machine, each detached like ./start.sh: ./run-parallel.sh [workers-per-run] [heap-per-run] [cfg...]
# ./status.sh shows how they are doing; ./summarize.sh writes logs/summary.txt.
cd "$(dirname "$0")"
w=${1:-8}; h=${2:-8g}; [ $# -ge 2 ] && shift 2 || shift $#
cfgs=("$@"); [ ${#cfgs[@]} -eq 0 ] && cfgs=($(ls *.cfg | sed 's/\.cfg$//'))
for cfg in "${cfgs[@]}"; do
    ./start.sh "$cfg" "$w" "$h"
done
