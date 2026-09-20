#!/bin/bash
# Run ./check.sh detached from the terminal and the ssh session, so that the run
# survives a disconnect: ./start.sh <config-name> [workers] [heap]
# The pid lands in logs/<cfg>.pid, the output in logs/<cfg>.log; ./status.sh
# shows how the runs are doing, ./resume.sh restarts a dead one from its last
# checkpoint, kill -- -<pid> stops one.
set -u
cd "$(dirname "$0")"
cfg=$1; workers=${2:-8}; heap=${3:-${TLC_HEAP:-4g}}
mkdir -p logs
if [ -s "logs/$cfg.pid" ] && kill -0 "$(cat "logs/$cfg.pid")" 2>/dev/null; then
    echo "$cfg: already running, pid $(cat "logs/$cfg.pid")"; exit 1
fi
export TLA2TOOLS=${TLA2TOOLS:-$PWD/tla2tools.jar} TLC_HEAP=$heap
setsid bash -c 'echo $$ > "logs/$0.pid"; exec ./check.sh "$0" "$1"' "$cfg" "$workers" > "logs/$cfg.out" 2>&1 < /dev/null &
sleep 1
echo "$cfg: started, pid $(cat "logs/$cfg.pid"), log logs/$cfg.log"
