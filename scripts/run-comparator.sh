#!/usr/bin/env bash

# Run the leanprover/comparator check for this project locally.
#
# Certifies that the repository proves the challenge statements of comparator/Challenge.lean
# that the config lists (default: comparator/challenges.json). See comparator/README.md for what
# is checked.
#
# Requires three binaries, each given by its environment variable or else found on the PATH:
#   COMPARATOR_BIN         the `comparator` binary (built from leanprover/comparator)
#   COMPARATOR_LEAN4EXPORT `lean4export`, built at THIS project's Lean version
#   COMPARATOR_LANDRUN     `landrun`, built from its `main` branch
# NB: rebuild lean4export whenever the project's Lean version changes.

set -euo pipefail

: "${COMPARATOR_BIN:=$(command -v comparator || echo comparator)}"
: "${COMPARATOR_LEAN4EXPORT:=$(command -v lean4export || echo lean4export)}"
: "${COMPARATOR_LANDRUN:=$(command -v landrun || echo landrun)}"
export COMPARATOR_LEAN4EXPORT COMPARATOR_LANDRUN
case "$COMPARATOR_LANDRUN" in
  /*) export PATH="$(dirname "$COMPARATOR_LANDRUN"):$PATH" ;;
esac

# Config file to check (default: all challenge theorems).
CONFIG="${1:-comparator/challenges.json}"

# Move to the repository root (this script lives in scripts/).
cd "$(dirname "$0")/.."

if [ ! -f "$CONFIG" ]; then
  echo "ERROR: no comparator config $CONFIG (the challenge statements come in stage B with the" >&2
  echo "theorems of the brute-force reference; see comparator/README.md)." >&2
  exit 1
fi

# Fail early with a helpful message if a binary is missing.
for bin in "$COMPARATOR_BIN" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_LANDRUN"; do
  if [ ! -x "$bin" ]; then
    echo "ERROR: comparator binary not found or not executable: $bin" >&2
    echo "See comparator/README.md for how to build it; give its path by the environment." >&2
    exit 1
  fi
done

# Ensure the library oleans are current so the sandboxed Solution build reuses them.
lake build RatpointsModel Ratpoints

# Run the check (exit 0 and "Your solution is okay!" = certified).
exec lake env "$COMPARATOR_BIN" "$CONFIG"
