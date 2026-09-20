#!/bin/bash
# Print the violated property, the flag combination the invariant printed and the
# full counterexample of a TLC run from a check.sh log.
# ./extract-trace.sh logs/<cfg>.log
log=$1
grep -m1 'Error: ' "$log"
grep -m1 '"fails for"' "$log"
awk '/Error: The (behavior|following)/,/states generated/' "$log" \
  | grep -v 'states generated' | grep -v '"fails for"' \
  | sed -E 's/ line [0-9]+, col [0-9]+ to line [0-9]+, col [0-9]+ of module [A-Za-z]+//'
