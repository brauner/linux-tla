#!/bin/bash
# Detached finisher, runs on jens: waits until no TLC run of this model is alive and the full
# meson test of the fixed tree is done, then builds the summary, the traces, RESULTS.txt and the
# README results table in place. Pull with
#   rsync -a --exclude '*.jar' jens:src/git/linux-tla/systemd/fiber/ ~/src/git/linux-tla/systemd/fiber/
cd "$(dirname "$0")"
while true; do
    alive=0
    for p in $(cat logs/*.pid 2>/dev/null); do kill -0 "$p" 2>/dev/null && alive=1; done
    sp=$(cat ~/src/git/systemd-fiber/build/test-all-fixed.pid 2>/dev/null); [ -n "$sp" ] && kill -0 "$sp" 2>/dev/null && alive=1
    [ $alive = 0 ] && break
    sleep 120
done
./summarize.sh > /dev/null
cp logs/summary.txt RESULTS.txt
mkdir -p traces
for c in $(ls *.cfg | sed 's/\.cfg$//'); do
    grep -q "expected: violation" "$c.cfg" || continue
    [ -f "logs/$c.log" ] && grep -q "Error:" "logs/$c.log" || continue
    ./extract-trace.sh "logs/$c.log" > "traces/$c.txt" 2>&1
done
grep -q RESULTS_TABLE README.md && python3 fill-results.py --readme > /dev/null
{
    echo "finished at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "full meson test of the fixed tree:"
    grep -E "^(Ok|Fail|Expected Fail|Unexpected Pass|Skipped|Timeout):" ~/src/git/systemd-fiber/build/test-all-fixed.log
    grep -E " FAIL " ~/src/git/systemd-fiber/build/test-all-fixed.log
    echo "model:"
    cat logs/summary.txt
} > FINISHED.txt
