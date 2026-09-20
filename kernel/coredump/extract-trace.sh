#!/bin/bash
# Print the violated property and the action sequence of a TLC
# counterexample, with the variables that matter, from a check.sh log.
# ./extract-trace.sh logs/<cfg>.log
log=$1
grep -m1 'Error: ' "$log"
awk '/Error: The (behavior|following)/,0' "$log" \
  | grep -E '^State [0-9]+|^Back to state|^Stuttering|^/\\ (pc|pending|shared|sigpending|notify|blocked|flags|group|core|dumper|counted|decremented|released|release_list|freed|wqexit|twq|refput|dump|freeze|hist) ' \
  | sed -E 's/ line [0-9]+, col [0-9]+ to line [0-9]+, col [0-9]+ of module [A-Za-z]+//'
