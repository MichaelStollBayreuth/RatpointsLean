#!/usr/bin/env bash

# Run the comparator check for this project locally, with Lake's built-in `lake comparator`
# (Lean v4.35.0 and later). It certifies that the repository proves the challenge statements of
# comparator/Challenge.lean that the config lists; see comparator/README.md for what is checked.
#
# Usage: scripts/run-comparator.sh [CONFIG] [OPTIONS]
#   CONFIG   the challenge description (default: comparator/challenges.json)
#   OPTIONS  passed on to `lake comparator`, e.g. `--paranoid` to run all external checkers
#            bundled with Lean besides its own kernel, as the certification of a stage does
#
# Requires bubblewrap (`bwrap`) with unprivileged user namespaces; `lake comparator` builds and
# exports both modules inside its sandbox and never loads the project's `.olean`s itself.

set -euo pipefail

# Move to the repository root (this script lives in scripts/).
cd "$(dirname "$0")/.."

CONFIG="comparator/challenges.json"
if [ $# -gt 0 ] && [ "${1#-}" = "$1" ]; then
  CONFIG="$1"
  shift
fi

if [ ! -f "$CONFIG" ]; then
  echo "ERROR: no comparator config $CONFIG (see comparator/README.md)." >&2
  exit 2
fi

# Build the library first, outside the sandbox, where the caller's environment applies (the
# sandbox clears it but for PATH), so that the sandboxed builds of Challenge and Solution find it
# current and only replay it.
lake build RatpointsModel Ratpoints

# Exit 0 and "Your solution is okay!" = certified; exit 1 = rejected; exit 2 = could not start
# (also when the config is missing, above).
exec lake comparator --config "$CONFIG" "$@"
