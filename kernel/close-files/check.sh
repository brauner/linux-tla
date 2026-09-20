#!/bin/bash
# Run TLC on one configuration: ./check.sh <config-name>   (module = prefix before '_')
set -u
cd "$(dirname "$0")"
cfg=$1
jar=${TLA2TOOLS:-./tla2tools.jar}
module=${cfg%%_*}
meta=${TLC_METADIR:-/tmp/tlc-close-files}/$cfg
mkdir -p "$meta/tmp" logs
java -Djava.io.tmpdir="$meta/tmp" -cp "$jar" tlc2.TLC -workers "${TLC_WORKERS:-2}" -deadlock -cleanup \
     -metadir "$meta" -config "$cfg.cfg" "$module.tla" > "logs/$cfg.log" 2>&1
expect=$(sed -n 's/.*expected: //p' "$cfg.cfg")
log=logs/$cfg.log
if grep -q 'TLC threw an unexpected exception\|Parsing or semantic analysis failed' "$log"; then result=ERROR
elif grep -q 'Invariant .* is violated\|Temporal properties were violated' "$log"; then result=violation
elif grep -q 'Model checking completed. No error has been found' "$log"; then result=pass
else result=unknown; fi
states=$(sed -n 's/^\([0-9]*\) states generated, \([0-9]*\) distinct states found.*/\2/p' "$log" | tail -1)
printf '%-46s %-10s %-10s %-8s %s\n' "$cfg" "$expect" "$result" "$states" "$([ "$result" = "$expect" ] && echo ok || echo MISMATCH)"
