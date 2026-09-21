#!/bin/bash
# Print the violated property and, for every state of a TLC counterexample, the
# action that led to it plus the fields that matter (loop state, fibers, live
# futures).  ./extract-trace.sh logs/<cfg>.log
log=$1
grep -m1 'Error: ' "$log"
awk '/Error: The (behavior|following)/,0' "$log" | python3 "$(dirname "$0")/trace.py"
