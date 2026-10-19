#!/usr/bin/env bash
# Axiom audit for compiled declarations, using an untracked probe outside the repo.
#
#   scripts/print_axioms.sh TwoComponentCoulomb.Some.Module TwoComponentCoulomb.someDecl [more decls...]
#
# The module must already be built (`lake build <module>`). Fails if any listed
# declaration depends on an axiom other than propext, Classical.choice and
# Quot.sound (in particular `sorryAx`).
set -euo pipefail

if [[ $# -lt 2 ]]; then
  echo "usage: $0 MODULE DECL [DECL...]" >&2
  exit 2
fi
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODULE="$1"; shift
PROBE_DIR="$(mktemp -d)"
trap 'rm -rf "$PROBE_DIR"' EXIT
PROBE="$PROBE_DIR/AxiomProbe.lean"
{
  echo "import $MODULE"
  for decl in "$@"; do echo "#print axioms $decl"; done
} > "$PROBE"

cd "$ROOT"
OUT="$(lake env lean "$PROBE" 2>&1)" || { echo "$OUT"; echo "AXIOM PROBE FAILED TO ELABORATE" >&2; exit 1; }
echo "$OUT"
BAD="$(printf '%s\n' "$OUT" | tr ',[]' '\n\n\n' | sed 's/^ *//; s/ *$//' \
  | grep -E '^[A-Za-z_][A-Za-z0-9_.]*$' \
  | grep -v -x -E 'propext|Classical\.choice|Quot\.sound' || true)"
if printf '%s\n' "$OUT" | grep -q "depends on axioms" && [[ -n "$BAD" ]]; then
  echo "NONSTANDARD AXIOMS: $BAD" >&2
  exit 1
fi
echo "AXIOMS OK"
