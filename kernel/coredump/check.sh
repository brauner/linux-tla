#!/bin/bash
# Run TLC on one configuration: ./check.sh <config-name> [workers]
# Needs tla2tools.jar; point TLA2TOOLS at it.
set -u
cd "$(dirname "$0")"
cfg=$1
workers=${2:-8}
jar=${TLA2TOOLS:-./tla2tools.jar}
layout=${cfg%%_*}
module=MC_$layout
meta=${TLC_METADIR:-/tmp/tlc-coredump}/$cfg
mkdir -p "$meta" logs
mkdir -p "$meta/tmp"
java -XX:+UseParallelGC -Xmx${TLC_HEAP:-6g} -Djava.io.tmpdir="$meta/tmp" -cp "$jar" tlc2.TLC \
     -workers "$workers" -deadlock -cleanup -metadir "$meta" \
     -config "$cfg.cfg" "$module.tla" 2>&1 | tee "logs/$cfg.log" | \
     grep -E 'Error|violated|Finished|states generated|distinct|Invariant|Temporal|is not|Deadlock|Assertion|Attempted|TLC threw|stack trace|Exception|EXCEPT|MC_|not enabled|line [0-9]+' 
echo "exit: ${PIPESTATUS[0]}  (full log: logs/$cfg.log)"
