#!/bin/bash
# Print the violated property and the counterexample of a check.sh log.
# ./extract-trace.sh logs/<cfg>.log
grep -m1 'Error: ' "$1"
awk '/Error: The (behavior|following)/,0' "$1" \
  | grep -E '^State [0-9]+|^Back to state|^Stuttering|^/\\ ' \
  | sed -E 's/ line [0-9]+, col [0-9]+ to line [0-9]+, col [0-9]+ of module [A-Za-z]+//'
