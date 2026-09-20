#!/bin/bash
# Run TLC on one configuration: ./check.sh <config-name> [workers]
# Needs tla2tools.jar; point TLA2TOOLS at it.  TLC_OPTS passes extra options to
# TLC (refine_new_w4 needs -maxSetSize 2000000 for its 1.7M initial tables).
set -u
cd "$(dirname "$0")"
cfg=$1
workers=${2:-8}
jar=${TLA2TOOLS:-./tla2tools.jar}
case "$cfg" in
    refine_*) module=CloseRange ;;
    race_*)   module=RangeCloseRace ;;
    dupfd_*)  module=DupFdRace ;;
    *) echo "unknown configuration prefix: $cfg" >&2; exit 1 ;;
esac
meta=${TLC_METADIR:-/tmp/tlc-close_range}/$cfg
mkdir -p "$meta/tmp" logs
java -XX:+UseParallelGC -Xmx${TLC_HEAP:-6g} -Djava.io.tmpdir="$meta/tmp" -cp "$jar" tlc2.TLC \
     -workers "$workers" -deadlock -cleanup -metadir "$meta" ${TLC_OPTS:-} \
     -config "$cfg.cfg" "$module.tla" 2>&1 | tee "logs/$cfg.log" | \
     grep -E 'Error|violated|Finished|states generated|distinct|Invariant|Temporal|is not|Deadlock|Assertion|Attempted|TLC threw|stack trace|Exception|fails for|not enabled|line [0-9]+'
echo "exit: ${PIPESTATUS[0]}  (full log: logs/$cfg.log)"
