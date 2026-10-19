#!/usr/bin/env python3
"""Project-specific source checks that complement the vendored checkers.

* Always: forbid escape hatches in project Lean code (code comments and strings
  are masked): heartbeat / recursion-depth overrides, `native_decide`,
  `implemented_by`, `extern`, `opaque`, and `debug.skipKernelTC`.
* When the frozen-anchor manifest has no anchors yet (before any declaration is frozen),
  the vendored `check_frozen_anchors.py` refuses to run.  In that case this
  script performs its placeholder sweep instead: no `sorry`/`admit` anywhere
  and no project-owned `axiom`/`constant` command.

Exit status: 0 PASS, 1 FAIL.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_frozen_anchors import Guard  # noqa: E402  (vendored, unmodified)

FORBIDDEN = [
    (re.compile(r"\bset_option\s+maxHeartbeats\b"), "heartbeat override"),
    (re.compile(r"\bset_option\s+synthInstance\.maxHeartbeats\b"), "instance heartbeat override"),
    (re.compile(r"\bset_option\s+maxRecDepth\b"), "recursion-depth override"),
    (re.compile(r"\bset_option\s+debug\.skipKernelTC\b"), "kernel type-check bypass"),
    (re.compile(r"\bnative_decide\b"), "`native_decide` (adds Lean.ofReduceBool)"),
    (re.compile(r"\bimplemented_by\b"), "`implemented_by`"),
    (re.compile(r"@\[\s*extern\b"), "`extern`"),
    (re.compile(r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|public|noncomputable)\s+)*opaque\b"),
     "`opaque` declaration"),
]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    args = parser.parse_args(argv)

    guard = Guard(args.root)
    errors: list[str] = []

    for path in sorted(guard.project_files()):
        code = guard.code_mask(guard.read_utf8(path))
        for pattern, what in FORBIDDEN:
            for match in pattern.finditer(code):
                line = code.count("\n", 0, match.start()) + 1
                errors.append(f"forbidden {what}: {path.relative_to(guard.root)}:{line}")

    data = json.loads(args.manifest.read_text(encoding="utf-8"))
    anchors = data.get("anchors")
    if isinstance(anchors, list) and not anchors:
        guard.check_all_sorries()
        guard.check_forbidden_axioms_constants()
        errors.extend(guard.errors)
        mode = "pre-anchor placeholder sweep"
    else:
        mode = "forbidden-token sweep (anchors present: run check_frozen_anchors.py too)"

    if errors:
        print(f"PROJECT CHECKS FAILED ({mode}):", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(f"PROJECT CHECKS OK ({mode})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
