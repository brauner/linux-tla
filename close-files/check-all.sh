#!/bin/bash
# Run every configuration and write logs/summary.txt
cd "$(dirname "$0")"
mkdir -p logs
{ printf '%-46s %-10s %-10s %-8s %s\n' config expected result states check
  for cfg in $(ls *.cfg | sed 's/\.cfg$//'); do ./check.sh "$cfg"; done; } | tee logs/summary.txt
