#!/usr/bin/env bash
# Elaborated ABI hash of a compiled declaration, for manifest `abi_sha256` fields.
#
#   scripts/abi_hash.sh <Module> <Decl> def      # type and body (definitions)
#   scripts/abi_hash.sh <Module> <Decl> theorem  # type only (theorems; proof excluded)
#
# The hash is the SHA-256 of the fully elaborated `pp.all` rendering, so it changes
# whenever the declaration's meaning-carrying content changes, and only then (for a
# fixed toolchain). The module must already be built. The probe lives outside the
# repository and is deleted on exit.
set -euo pipefail

if [[ $# -ne 3 || ( "$3" != "def" && "$3" != "theorem" ) ]]; then
  echo "usage: $0 MODULE DECL def|theorem" >&2
  exit 2
fi
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODULE="$1"; DECL="$2"; KIND="$3"
PROBE_DIR="$(mktemp -d)"
trap 'rm -rf "$PROBE_DIR"' EXIT
PROBE="$PROBE_DIR/AbiProbe.lean"
{
  echo "import $MODULE"
  echo "set_option pp.all true"
  echo "set_option format.width 100000"
  if [[ "$KIND" == "def" ]]; then
    echo "#print $DECL"
  else
    echo "#check @$DECL"
  fi
} > "$PROBE"

cd "$ROOT"
OUT="$(lake env lean "$PROBE" 2>&1)" || { echo "$OUT" >&2; echo "ABI PROBE FAILED" >&2; exit 1; }
# Drop the probe path prefix from any message so the hash is location-independent.
printf '%s\n' "$OUT" | sed "s|$PROBE_DIR/AbiProbe.lean:[0-9]*:[0-9]*: ||" | shasum -a 256 | cut -d' ' -f1
