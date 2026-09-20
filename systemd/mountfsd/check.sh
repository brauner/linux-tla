#!/bin/bash
# Run TLC on one configuration in the foreground: ./check.sh <config-name> [workers]
# Needs tla2tools.jar; point TLA2TOOLS at it.  TLC_HEAP sets the heap (4g),
# TLC_OPTS passes extra options, TLC_METADIR the directory for TLC's metadata
# and checkpoints (/tmp/$USER-tlc-mountfsd), TLC_CHECKPOINT the minutes
# between checkpoints (10).  TLC_RECOVER=1 resumes from the newest checkpoint
# of the configuration instead of starting over.
set -u
cd "$(dirname "$0")"
cfg=$1
workers=${2:-8}
jar=${TLA2TOOLS:-./tla2tools.jar}
module=VeritySharing
meta=${TLC_METADIR:-/tmp/$USER-tlc-mountfsd}/$cfg
log=logs/$cfg.log
mkdir -p "$meta/tmp" logs
if [ "${TLC_RECOVER:-0}" = 1 ]; then
    chk=$(sed -n 's/^Checkpointing of run //p' "$log" 2>/dev/null | tail -1)
    [ -n "$chk" ] && grep -q '^Checkpointing completed' "$log" && [ -d "$chk" ] || { echo "$cfg: no checkpoint to recover from"; exit 2; }
    echo "Recovering from $chk" | tee -a "$log"
    where=(-recover "$chk"); tee=(tee -a "$log")
else
    where=(-metadir "$meta"); tee=(tee "$log")
fi
java -XX:+UseParallelGC -Xmx${TLC_HEAP:-4g} -Djava.io.tmpdir="$meta/tmp" -cp "$jar" tlc2.TLC \
     -workers "$workers" -deadlock -checkpoint "${TLC_CHECKPOINT:-10}" "${where[@]}" ${TLC_OPTS:-} \
     -config "$cfg.cfg" "$module.tla" 2>&1 | "${tee[@]}" | \
     grep -E 'Error|violated|Finished|states generated|distinct|Invariant|Temporal|is not|Deadlock|Assertion|Attempted|TLC threw|stack trace|Exception|fails for|not enabled|line [0-9]+|Checkpointing|Recover'
rc=${PIPESTATUS[0]}
# A finished run needs no metadata any more; a killed one keeps its checkpoint for resume.sh.
grep -q 'Model checking completed\|Invariant .* is violated\|Temporal properties were violated\|is not a valid' "$log" && rm -rf "$meta"
echo "exit: $rc  (full log: $log)"
