# Scripts

| Script | Purpose |
|---|---|
| `check_all.sh` | The full project check: build, module and file-size checks, forbidden-construct sweep, frozen statements against the manifest |
| `check_frozen_anchors.py` | Fail-closed check of the frozen declarations against `manifest/frozen_anchors.json`: file hashes, the five proof-body markers, the sealed proof bodies (`by exact <provider>`), and no `sorry` or custom axiom anywhere in the project |
| `check_lean_modules.py` | Every Lean file is a module (`module` header) and has at most 1500 lines (reads the git index) |
| `project_checks.py` | Forbidden escape hatches in project Lean code: heartbeat and recursion-depth overrides, `native_decide`, `implemented_by`, `extern`, `opaque`, `debug.skipKernelTC` |
| `print_axioms.sh` | Axiom audit of compiled declarations through a temporary probe; allows only `propext`, `Classical.choice` and `Quot.sound` |
| `abi_hash.sh` | SHA-256 of a declaration's fully elaborated `pp.all` form (the `abi_sha256` field of the manifest) |

`check_frozen_anchors.py` and `check_lean_modules.py` are used unmodified from
[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills) by
Scott Armstrong (Copyright © 2026 Scott Armstrong;
commit `05a07311f16bc581729e52f3e73647b95fa9bef1`, skills `lean-orchestrator`
and `lean-project-architecture`), licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The `references/module-system.md`
that `check_lean_modules.py` mentions is part of that collection. The other scripts are part of
this project and are released under the Apache License 2.0.
