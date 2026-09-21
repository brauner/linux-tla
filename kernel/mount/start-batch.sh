#!/bin/bash
# Start run-batch.sh detached from the terminal (survives ssh/laptop loss).
# ./start-batch.sh <concurrent> <workers-per-run> <heap> [cfgs...]
# Progress: logs/*.log, logs/batch.out; verdicts: logs/summary.txt when done.
# Start it again after an interruption: finished configurations are skipped,
# unfinished ones resume from their checkpoint.
cd "$(dirname "$0")"
mkdir -p logs
if [ -f logs/batch.pid ] && kill -0 "$(cat logs/batch.pid)" 2>/dev/null; then
    echo "batch already running, pid $(cat logs/batch.pid)"; exit 1
fi
setsid nohup ./run-batch.sh "$@" >> logs/batch.out 2>&1 < /dev/null &
echo $! > logs/batch.pid
echo "started pid $(cat logs/batch.pid); progress in logs/batch.out and logs/*.log"
