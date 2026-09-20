#!/bin/bash
# Restart a run that died (killed, machine rebooted) from its newest checkpoint,
# detached like ./start.sh: ./resume.sh <config-name> [workers] [heap]
cd "$(dirname "$0")"
TLC_RECOVER=1 exec ./start.sh "$@"
