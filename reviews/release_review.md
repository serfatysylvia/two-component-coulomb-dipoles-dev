# Release review: hygiene and reproducibility (final)

**Reviewed:** commit `14d049f`, the second release candidate. It replaces `c553d18`, which I reviewed first.
**Reviewer:** independent of the people who prepared the release. I edited no files.
**Date:** 2026-10-18

## Summary verdict

**Ready to publish, once `reviews/` is added and the two author decisions below are taken.**

- Of the ten findings from the first review, eight are fully resolved.
- F1 (the missing `reviews/` directory) is resolved by adding `reviews/` to the published tree.
- F9 is resolved except the copyright holder's name, which is the authors' decision.
- R21 is now correctly marked `PENDING` and needs the authors' approval at the publication gate.
- One new low-severity finding (N1) and one cosmetic one (N2) remain. Neither blocks publication.

Two changes since the first candidate needed fresh verification: a dead-code sweep that deleted 46 declarations, and an elaboration pass that changed proofs only. Neither altered any public statement:

- The 32 frozen statements are still identical to the approved ones after the R21 renaming.
- The type of each of the 1,870 surviving public declarations is unchanged.
- No docstring refers to a deleted declaration.

| # | Check | Verdict |
|---|---|---|
| 1 | Private material | PASS |
| 2 | Scope | PASS |
| 3 | Statement preservation | PASS |
| 4 | Reproducibility | PASS |
| 5 | Documentation accuracy | PASS (N1, N2 open; both minor) |
| 6 | Licensing and attribution | PASS (copyright holder name still to be set by the authors) |
| 7 | CI | PASS |

## 1. Private material: PASS

- I searched all 175 tracked files, including `scripts/`, the workflow and the new `source/README.md`. Searches covered:
  - local paths;
  - account names and e-mail addresses;
  - credential patterns;
  - assistant or tool names;
  - development vocabulary: brief, worker, orchestrator, campaign, ledger, landing, milestone, packet, wave, errata, `v1`/`v2`, beta2, dashboard.
- There are no hits outside the manuscript, apart from three expected ones:
  - the public repository URL in `README.md` and `CITATION.cff`;
  - the required CC BY 4.0 attribution of the vendored scripts, which names their upstream project, its author and its public URL (`README.md`, `scripts/README.md`);
  - the upstream skill names in that attribution.
- The dependency-graph identifiers and the "audited" and "source-facing" wording are gone. The remaining development terms (frozen statement or anchor, provider, sealed, gates, conditional helper) are now defined in a Terminology section of `README.md`. I checked the definitions against `manifest/frozen_anchors.json`; for example, each provider has the same short name as its frozen theorem in a provider namespace.
- The repository has a single reachable commit and no unreachable objects.

## 2. Scope: PASS

- The dead-code sweep removed the earlier revision's truncated-Dirichlet estimates. `Integrals/DirichletTrunc.lean` now holds only the exponential Markov bound and a one-dimensional integral, used in `UpperBound/NearestNeighborModelCritical.lean`.
- No file, declaration name or docstring refers to the earlier revision's statements or rate.
- Nothing from the other formalization in the development repository is present.
- `Theorem1ShapeRate` remains. It is a weaker internal form of Theorem 1, used in Steps 5–6 of Theorem 2, is implied by `theorem_1`, and is described neutrally. No action needed.

## 3. Statement preservation: PASS

- **Probes.** I generated `pp.all` probes (`#print` for the 25 definitions, `#check @` for the 7 theorems) from the candidate's manifest.
- **Where they ran:** in the fresh clone, and in the private development repository against the approved names `errorRateV2`, `theorem_1_v2`, `theorem_2_v2`, `proposition_3_9_v2` and `lemma_3_5`. The private repository's frozen files and manifest are unchanged since the first review.
- **Comparison.** I mapped only those five names, token-wise. **32 of 32 outputs are byte-identical.** The public outputs are also byte-identical to those of the first candidate.
- **The renaming is injective.** The private outputs mention only the successor names.
- **Manifest hashes.** I recomputed all 32 `abi_sha256` values with `scripts/abi_hash.sh`: 32 of 32 match, and they are unchanged from the first candidate. Only `full_file_sha256` values changed, because the frozen files' header comments changed.
- **Frozen files changed only in comments:**
  - the added licence line;
  - the approval references (R17/R18 plus R19, matching the manifest);
  - the `smearedCharge` docstring, which now notes the zero measure for `a ≤ 0`, as R16 states.
- **Dead-code sweep and elaboration pass.** I dumped the type hash of every public `TwoComponentCoulomb.*` declaration in both candidates:
  - first candidate: 1,916 declarations; new candidate: 1,870;
  - all 1,870 survivors have identical type hashes;
  - none was added, and exactly 46 were removed.
- **No dangling references to deleted declarations:**
  - Every identifier quoted in backticks in a comment resolves to an existing declaration or is notation.
  - A whole-word search for all 46 deleted names finds one hit, `h.1.isIsolatedPair` in proof code. It resolves to the surviving `IsIsolatedDipole.isIsolatedPair`.

## 4. Reproducibility: PASS

**Fresh-checkout logs**
- `run.log`: clone at `14d049f`; the cache, build, `check_all` and axiom steps all exit 0.
- `cache.log`: every dependency was materialized at its manifest revision. The Mathlib oleans came from the machine's existing cache, so the download path is first exercised by CI.
- `build.log`: "Build completed successfully (3349 jobs)". All 156 project modules were compiled from scratch. No warnings. Wall time 2 m 08 s.
- `check_all.log`: all checks passed.
- `axioms.log`: each of the seven theorems depends only on `propext`, `Classical.choice` and `Quot.sound`.

**My reruns in the clone**
- `lake build --no-build`: all targets up to date.
- `scripts/check_all.sh --no-build`: pass.
- `scripts/print_axioms.sh` on the seven theorems, on the providers `TwoComponentCoulomb.Main.theorem_1`, `TwoComponentCoulomb.Main.theorem_2`, `TwoComponentCoulomb.UpperBound.proposition_3_10` and `TwoComponentCoulomb.UpperBound.lemma_3_6`, and on `errorRate`: standard axioms only.
- No Lean file contains `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `extern` or any `set_option`.

**Pins and unchanged files**
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `LICENSE`, `CITATION.cff`, the manuscript and every script except `scripts/README.md` are byte-identical to the first candidate.
- All nine dependency checkouts sit at their pinned SHAs and are clean.

## 5. Documentation accuracy: PASS

- **Every Appendix A citation from the first review is fixed:**
  - the renumbering slips are corrected;
  - the line references are corrected, for example l. 217–222 for the nearest-neighbour graph, (nn3) at l. 367, l. 1538, l. 1542, l. 472–473, l. 970–973 and 982–985, l. 1856–1860, l. 1772, l. 203–213, and l. 192 and 191–200;
  - the labels that do not exist have been removed;
  - the misspelled labels are fixed, except the remnants listed as N1.
- **Changed citations.** I read every changed citation line against `source/dipole-formation.tex`: 71 in `UpperBound/` (the second editorial pass) and 31 elsewhere. All are correct.
- **Automated checks.** A label check over every label-like token finds no nonexistent labels and no dependency-graph identifiers. The only misspelled labels are the N1 remnants.
- **`README.md`.** The results table, commands, layout, licence section and Terminology section are accurate. The README now names `reviews/statement_audit.md` and `reviews/release_review.md`.
- **`source/README.md`.** It is accurate: the SHA-256 matches, the file is for reference only, and the figures and `bib.bib` are indeed not shipped.
- **`RULINGS.md`.**
  - The header now states that the file is condensed and edited, which superseded rulings are restated, and that R14 is omitted.
  - R19 attributes the "standing assumptions" wording to Proposition 2.2 and Corollary 2.3 (l. 435, 453).
  - R21 is `PENDING`.
  - The meanings of the other rulings are unchanged.

## 6. Licensing and attribution: PASS

- **Vendored scripts.** `scripts/README.md` and the licence section of `README.md` now attribute `scripts/check_frozen_anchors.py` and `scripts/check_lean_modules.py` to *LeanAutoformalizationSkills* by Scott Armstrong. They give the upstream URL and commit `05a07311f16bc581729e52f3e73647b95fa9bef1`, the CC BY 4.0 licence with a link, and the note "used unmodified". They also explain the reference to `references/module-system.md`.
  - The upstream commit is public.
  - Both files at that commit are byte-identical to the shipped copies (SHA-256 `9970a0ac…12a4` and `c69733b2…3e73`).
  - The attribution follows the upstream's own suggested form.
- **Lean headers.** All 156 Lean files now carry "Released under Apache 2.0 license as described in the file LICENSE."
- **Manuscript.** `source/README.md` records the manuscript's status (© its authors, not covered by the Apache licence).
- **Still open, for the authors:** the copyright holder and software author are still the placeholder "TwoComponentCoulomb contributors".

## 7. CI: PASS

- The workflow sets `permissions: contents: read`.
- Actions are pinned to commit SHAs. I confirmed on GitHub that:
  - `actions/checkout@11bd71901bbe5b1630ceea73d27597364c9af683` is tag v4.2.2;
  - `leanprover/lean-action@f061402b660e0c34644504b324e830f2991d4865` is tag v1.6.1, and its `action.yml` defines the inputs used (`auto-config`, `use-mathlib-cache`, `build`).
- No secrets are used.
- The build, `check_all.sh --no-build` and the axiom audit match the README.

## Resolution of the first review's findings

| ID | Finding (first review) | Status | Evidence |
|---|---|---|---|
| F1 | `reviews/` missing from the tree | **Resolved by the addition of `reviews/` to the published tree** | Commit `14d049f` does not yet contain `reviews/`. The published tree adds it and otherwise differs from `14d049f` only by that directory. `README.md` cites `reviews/statement_audit.md` and `reviews/release_review.md`, so the added files must carry exactly these names. |
| F2 | Vendored CC BY 4.0 scripts without attribution | Resolved | See Check 6: attribution with author, URL, commit, licence and link, and "unmodified"; upstream files verified byte-identical. |
| F3 | R21 marked `EXPLICIT`; the header claimed texts were "as recorded" | Resolved | R21 is `PENDING` and a `PENDING` status value is defined. The header describes the edits accurately. |
| F4 | Wrong docstring citations | Resolved, except N1 | All Appendix A items are fixed and the 102 changed citations verified; see Check 5. |
| F5 | R19 misattributed the "standing assumptions" wording | Resolved | R19 now cites Proposition 2.2 and Corollary 2.3 (l. 435, 453). |
| F6 | Dependency-graph identifiers and labels that do not exist | Resolved | No `label#node` identifiers remain; `claim:` and `defn:` identifiers are gone. |
| F7 | Undefined development vocabulary | Resolved | Terminology section in `README.md`; "audited" and "source-facing" are gone from the Lean files. |
| F8 | CI actions on mutable tags; no `permissions` block | Resolved | SHAs pinned and verified; `permissions: contents: read`. |
| F9 | Copyright placeholder; no licence line; manuscript carve-out only in the README | Resolved except the holder's name | The licence line is in all 156 headers and `source/README.md` exists. The holder name awaits the authors. |
| F10 | Binder names `h35`/`h39`; R14 placeholder; "the plan" | Resolved | Binders renamed `h36`/`h310`; R14 omitted; the `DEFAULT` definition reworded. |

## New findings

| ID | Severity | Finding | Suggested fix |
|---|---|---|---|
| N1 | Low | Nine occurrences of the half-corrected label `eq:n neutral-conv`, in `Fluctuations/MomentA1.lean:29`, `Fluctuations/MomentA3.lean:29` and `Fluctuations/TiltedIsolated.lean:17, 24, 470, 472, 480, 543, 545`. The source label is `eq:n neutral conv` (l. 1244). | Respell (comment-only), then rerun the build and `scripts/check_all.sh`. |
| N2 | Cosmetic | `LowerBound/PartitionLower.lean:23, 159` cite l. 1769–1771 for the radius ϱ, which is defined at l. 1772 (this predates the first review). | Change to l. 1770–1772. |
| N3 | Info | The upstream's notice "Copyright © 2026 Scott Armstrong" is not reproduced verbatim. The attribution matches the upstream's own recommended form, so this is optional. `CITATION.cff` lists only `Apache-2.0`. | Optionally add the © line next to the attribution, and list `CC-BY-4.0` for the two scripts in `CITATION.cff`. |

## Actions at the publication gate

1. Add `reviews/` with `statement_audit.md`, `release_review.md` (this report) and a README (F1).
2. Obtain the authors' approval of R21, then change its status from `PENDING` to `EXPLICIT`.
3. Have the authors confirm the copyright holder and software author in the headers and in `CITATION.cff`.
4. Optionally fix N1 and N2. These are comment-only edits; afterwards rerun the build, `scripts/check_all.sh` and the axiom audit on the final commit.

None of these actions touches a frozen file or a proof.
