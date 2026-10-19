#!/usr/bin/env bash
# Full project check. Run from anywhere; operates on the repository root.
#
#   scripts/check_all.sh            # build + all source checks
#   scripts/check_all.sh --no-build # source checks only
#
# The module checker reads the git index: new .lean files must be staged (`git add`) first.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
MANIFEST="manifest/frozen_anchors.json"
status=0

if [[ "${1:-}" != "--no-build" ]]; then
  echo "== lake build"
  if ! lake build; then status=1; fi
fi

echo "== module system and file size (max 1500 lines)"
python3 scripts/check_lean_modules.py --root . --max-lines 1500 || status=1

echo "== project source checks"
python3 scripts/project_checks.py --root . --manifest "$MANIFEST" || status=1

echo "== frozen statements against the manifest"
python3 scripts/check_frozen_anchors.py --root . --manifest "$MANIFEST" || status=1

if [[ $status -eq 0 ]]; then echo "ALL CHECKS PASSED"; else echo "CHECKS FAILED" >&2; fi
exit $status
