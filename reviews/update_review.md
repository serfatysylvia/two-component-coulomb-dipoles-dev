# Update review: Proposition 4.1 on the paper's route

**Reviewed:** commit `aeafcbb`, a proposed update on top of the published commit `aa8884a`.
**Reviewer:** independent of the people who prepared the release. I edited no files.
**Date:** 2026-10-22

## Summary verdict

**Ready with changes.** The update does what it claims, and it does not touch any statement:

- The 32 frozen declarations and the manifest are byte-identical to `aa8884a`.
- A fresh clone builds, passes all project checks, and the seven results still depend only on
  `propext`, `Classical.choice` and `Quot.sound`.
- The proof of `proposition_4_1` now uses the screened-dipole construction at the term level.
  This includes the weak Neumann problem, the divergence theorem on a disc, (hui), (estimatesv),
  (majof), (align57) and the `φ_β` expectation of Step 3.
- No module of the previous route (R12a) remains.

Four changes are needed before publishing, all in comments or documentation:

- **U1:** remove a dependency-graph phrase from a docstring.
- **U2:** correct one wrong line citation, which occurs three times.
- **U3:** qualify the README's new sentence "The proofs follow the paper's arguments."
- **U4:** extend `reviews/README.md`, and the README's paragraph on reviews, to cover this update.

The other findings are cosmetic or informational. None of the changes touches a frozen file or a
proof.

| # | Check | Verdict |
|---|---|---|
| 1 | Private material and commit metadata | PASS, except U1 (one development-vocabulary phrase) |
| 2 | Statement preservation | PASS |
| 3 | Scope | PASS |
| 4 | Documentation accuracy | PASS with findings (U2, U3 low; U5, U6 cosmetic; U7 informational) |
| 5 | Proof status, build and axioms | PASS |
| 6 | `reviews/` stays accurate | CHANGE REQUIRED (U4) |

## 1. Private material and commit metadata: PASS (U1)

**Commit metadata.** `git log --format=fuller -2` shows `aeafcbb` with author and committer
`Sylvia Serfaty <152826837+serfatysylvia@users.noreply.github.com>`, the same identity as `aa8884a`.
Other facts:

- The parent of `aeafcbb` is `aa8884a`, and `origin/main` is `aa8884a`.
- The repository has no other branches or commits.
- The commit message names only paper equations and rulings (R12a, R22, R22a).

**Added lines.** I swept every added line of `git diff aa8884a aeafcbb` for the following:

- local paths and scratch locations;
- account and repository names, assistant names, and credential patterns;
- development file names (`two-comp5-revised*`), and development declaration names (`_v2`, `V2`,
  `v1`);
- development vocabulary: worker, orchestrator, campaign, phase, packet, wave, ledger, brief,
  landing, milestone, errata, beta2, dashboard, depgraph, `TODO`;
- revision-history words: previous, former, earlier, replaced, no longer, now.

The only hits are the following:

- The `RULINGS.md` header names R12a as "an earlier proof route ... replaced by the paper's own
  argument in R22". This is needed to explain the gap in numbering, as for R14.
- One development phrase in a docstring (**U1**).

**U1.** `LowerBound/ScreenedLower.lean:147` reads "**Step 1 integrated** (source l. 1816--1834,
*the graph node of the pair integral bound*, with the correction constant `β`)". "Graph node"
refers to the dependency graph of the development workflow, which is not shipped. The first release
review removed that vocabulary (its finding F6). The phrase is new in `aeafcbb`; `aa8884a` contains
no "graph node".

## 2. Statement preservation: PASS

- **Frozen files and manifest.** `git diff --stat aa8884a aeafcbb -- TwoComponentCoulomb/Frozen
  manifest` is empty, so all 32 frozen files and `manifest/frozen_anchors.json` are byte-identical.
- **Frozen-anchor check.** In the update tree, `python3 scripts/check_frozen_anchors.py --root .
  --manifest manifest/frozen_anchors.json` prints `FROZEN-ANCHOR GUARD OK`.
- **No hidden semantic change.**
  - The frozen files import only Mathlib, other frozen files and their providers. The providers
    are private imports in the theorem anchors only.
  - No frozen definition depends on a changed module.
  - The `abi_sha256` values (the hash of the `pp.all` elaboration) were recomputed with
    `scripts/abi_hash.sh` in the built clone: 32 of 32 match the manifest. These are the 25
    definitions, by type and body, and the 7 theorems, by type.
- **Sealed proof unchanged.** The sealed proof of `Frozen/Proposition41.lean` is still
  `by exact TwoComponentCoulomb.LowerBound.proposition_4_1`. Its provider still states exactly
  the frozen statement.

## 3. Scope: PASS

`git diff --name-status aa8884a aeafcbb` touches 20 files (+3120/−1423 lines).

**Deleted:** the R12a modules `LowerBound/AngularAverage.lean`, `LowerBound/DipoleJensen.lean` and
`LowerBound/DiscFactor.lean`.

**Added**, all in the proof of Proposition 4.1:

- `LowerBound/NeumannDipole.lean`
- `LowerBound/ScreenedField.lean`
- `LowerBound/NeumannEnergy.lean`
- `LowerBound/ScreenedLower.lean`
- `LowerBound/PairFactor.lean`
- `LowerBound/PhiExpectation.lean`
- `Potential/DiscDivergence.lean` (the divergence theorem on a disc, used only by `ScreenedField`)

**Modified:**

- the Proposition 4.1 modules `CriticalLower`, `LabelSum`, `LowerAssembly`, `LowerJensen`,
  `PartitionLower`, `Proposition41` and `RadiusTail`;
- `LowerBound/PolarPi.lean`, in its module docstring only: its R12a consumer is gone, and it now
  serves upper-bound modules;
- `README.md` and `RULINGS.md`.

**Unchanged:** `TwoComponentCoulomb.lean`, every other library directory, `scripts/`, `reviews/`,
`source/`, the CI workflow, `CITATION.cff`, `LICENSE`, `lakefile.toml`, `lake-manifest.json` and
`lean-toolchain`.

**Counts.** Lean files go from 156 to 160 (3 removed, 7 added), and tracked files from 178 to 182.
No change is hidden.

## 4. Documentation accuracy: PASS with findings

**RULINGS R22 and R22a against the code.**

- **R22a's formula.** R22a gives `v_i(z) = log|1 − (z − x_i)·conj(y_i − x_i)/ϱ(x_i)²|`. This is
  exactly `neumannCorrection ρ c y z = Real.log ‖1 - (z - c) * conj (y - c) / ρ²‖`. Here
  `c = x_i`; `ρ = ϱ(x_i)` (`lowerRadius`) for β > 2, and `ρ = t` for β = 2, as in the paper,
  l. 1820.
- **The rest of R22a.** Its weak form is `integral_ball_fderiv_neumannField`, for ξ of class C¹ on
  a neighbourhood of the closed disc, proved via `integral_ball_divergence`. Its "proves
  (estimatesv) from the explicit v_i" is `norm_neumannCorrectionField_le`, with the constant 2.
- **R22's steps.** Each step of R22 is a named theorem in the proof of `proposition_4_1` (Check 5):
  - (divE) is `integral_fderiv_apply_screenedField`;
  - (hui) is `integral_norm_sq_electricField_le_screened`;
  - the energy of a disc is `integral_ball_norm_sq_neumannField`;
  - (majof) is `energy_sum_elim_le_screened`, with constant 1;
  - J_β is `pairFactor β β λ`, so A_β = β, which suffices because the constant of (majof) is 1;
  - (align57) is `exists_log_pairFactor_ge`;
  - the bound on E_ℚ[φ_β(ϱ(x_1))] is `expectation_isolatedPhi_lowerRadius_le`;
  - the energy error N t² at β = 2 comes from `partitionFunction_ge_placement_annulus`.
- **Constant in `CriticalLower`.** Its constant changes from `12 + 16π` to `14 + 16π`, which is
  consistent with the extra factor `e^{-2t²}` and `2t² ≤ 2t`.
- **The `RULINGS.md` header** correctly records the omission of R12a.

**Line citations.** I checked every line citation added by the diff (44 distinct ranges) against
`source/dipole-formation.tex`; its SHA-256 is recomputed and matches. All point to the right
passage, with two exceptions:

- the wrong line in **U2**;
- several ranges that run onto adjacent blank or formatting lines (**U5**).

**Names and labels.** All 215 backticked tokens in the changed files were checked:

- They resolve to declarations in the tree, to Mathlib names (for example
  `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`, which exists at Mathlib
  `v4.35.0-rc2`), or to module names.
- The rest are variables, or names quoted in the existing R21.
- Every cited equation label exists in the source: divE, hui, estimatesv, majof, minz3, align57,
  eq:volume-lower, eq:Jensen, defvarphi, eq:rewrF, eq:heta, geta0 and eq:defgeta.

**Mathematical content of the new docstrings.** I checked these against the code and the paper:

- the image point lies outside `B(c, 2ρ)` when `|y − c| ≤ ρ/2`;
- `∇v = −a/(ρ² − conj(ζ) a)`;
- the cutoff radii 13ρ/16 and 7ρ/8 enclose the charges, which lie in `B(c, 3ρ/4)`;
- the error `(1/4π)·2π·2 = 1` of (majof);
- `log(1 − x) ≥ −2x` in (align57).

They are correct.

**README.** The new paragraph is accurate about Proposition 4.1. Its first sentence is the subject
of **U3**. "Screened dipoles" is the subject of **U6**.

## 5. Proof status, build and axioms: PASS

**Forbidden constructs.** `git grep` over all Lean files of the update tree for `sorry`, `admit`,
`axiom`, `native_decide`, `implemented_by`, `opaque`, `extern` and `set_option` finds no code use.
The only hits are the prose word "constant" and the Boolean function `decide` in
`NearestNeighbor/Isolated.lean`; both predate the update. There are no `exact?`, `apply?` or
`simp?`.

**Fresh clone of `aeafcbb`,** in a temporary directory:

- `lake exe cache get` exits 0. Mathlib came from the local cache ("No files to download"), so the
  download path is exercised only by CI.
- `lake build` reports "Build completed successfully (3354 jobs)". All 160 project modules were
  compiled, with 0 warnings, in 188 s of wall time.
- `scripts/check_all.sh --no-build` prints
  `check_lean_modules: PASS (160 Lean files, ...)`, `PROJECT CHECKS OK`,
  `FROZEN-ANCHOR GUARD OK` and `ALL CHECKS PASSED`.
- `scripts/print_axioms.sh` was run on `TwoComponentCoulomb`, on the seven results of the README,
  and on the provider `TwoComponentCoulomb.LowerBound.proposition_4_1`. Each depends on
  `[propext, Classical.choice, Quot.sound]`, and the script prints `AXIOMS OK`.

**Term-level consumption.** I used a transient probe, deleted afterwards. It walks the constants
used by `TwoComponentCoulomb.LowerBound.proposition_4_1`, 398 project declarations. It confirms
that the proof uses all of the following:

- `energy_sum_elim_le_screened`
- `integral_ball_fderiv_neumannField`
- `integral_norm_sq_electricField_le_screened`
- `norm_neumannCorrectionField_le`
- `inner_neumannField_eq_zero`
- `integral_ball_divergence`
- `exists_log_pairFactor_ge`
- `expectation_isolatedPhi_lowerRadius_le`
- `partitionFunction_ge_pairFactor`
- `partitionFunction_ge_placement_annulus`

So the published route is the one described in R22, both for β > 2 and for β = 2.

## 6. `reviews/`: change required (U4)

`reviews/README.md` says that the published tree differs from the final reviewed candidate
`14d049f` only by three things:

- the `reviews/` directory;
- the changes N1–N3;
- the authors' decisions at publication.

After `aeafcbb` this is false. The README's paragraph "Before release, independent reviewers ..."
also covers only the initial release. See **U4** for what to add.

## Findings

| ID | Severity | Finding | Evidence | Suggested fix |
|---|---|---|---|---|
| U1 | Low | Development-workflow vocabulary in a public docstring. | `LowerBound/ScreenedLower.lean:147`: "(source l. 1816--1834, the graph node of the pair integral bound, with the correction constant `β`)". The phrase refers to the unshipped dependency graph; the first release review removed such identifiers (F6). It is new in `aeafcbb`. | Replace with "(source l. 1816--1834, with the correction constant `β`)". |
| U2 | Low | Wrong line citation, introduced by the update. | `LowerBound/LabelSum.lean`: the docstrings of `labelSet` ("source l. 1825, 1833"), `pairwise_disjoint_labelSet` ("source l. 1825, 1833") and `partitionFunction_ge_label_sum` ("source l. 1825 and eq. (minz3)"). The sentence "The N! assignments of negative labels are disjoint" is on l. 1820 (β = 2) and l. 1833 (Step 2); l. 1825 is "Using N! ≥ (N/e)^N proves (eq:lbz2) ...". `aa8884a` cited l. 1820 correctly. | Change "1825" to "1820" in the three places. |
| U3 | Low | "The proofs follow the paper's arguments" is unqualified. | It is accurate at the level of overall structure, and Proposition 4.1 now follows the paper. But `RULINGS.md` records R12b (the electric formulation through the explicit disc potential) and R12c (§3 machinery proved once in a weighted/tilted generality). Module docstrings also record local technical variations. For example, `UpperBound/CriticalRadial.lean` (a pointwise bound "which replaces the source's split at `2λ`"); `Fluctuations/MomentCombine.lean` ("elementary replacements of Hölder's and Jensen's inequalities"; (eq:finalA3) used at `t = 12πcC_A` instead of `t = 1`); `Fluctuations/MomentA2.lean` (`C₀ = 61` instead of `60`); `Integrals/DirichletTrunc.lean` ("bounded directly instead of by integration by parts"); `UpperBound/CriticalCells.lean` (a factor "in place of the source's `N^h J_λ(1/ℓ)^h (CN/d)^d`"). None of these changes a statement or an overall argument, but a reader may take the sentence as step-for-step identity. | For example: "The proofs follow the paper's arguments, with the implementation choices recorded in R12b, R12c and R22a and local technical variations noted in the module docstrings. In Step 1 of Proposition 4.1, ...". |
| U4 | Low (required for accuracy) | `reviews/README.md`, and the README's paragraph on reviews, describe only the initial publication. | `reviews/README.md` states that the published tree differs from `14d049f` only by `reviews/`, N1–N3 and the authors' decisions. `README.md` says "Before release, independent reviewers ...". | (a) Add a row to the table: `update_review.md` (this report), scope "update `aeafcbb`: proof of Proposition 4.1 on the paper's route (R22, R22a)", candidate `aeafcbb`. (b) Scope the "differs only by" sentence to the initial publication `aa8884a`. Add that the later update replaces the proof of Proposition 4.1 by the paper's argument (R22, R22a). It deletes three proof modules and adds seven. It changes only proof modules under `TwoComponentCoulomb/LowerBound/`, the new `Potential/DiscDivergence.lean`, `README.md` and `RULINGS.md`. The 32 frozen files and the manifest are byte-identical, so the statement audit still applies. List any fixes applied after this review (U1–U3, U5–U7), so that the published commit's differences from `aeafcbb` are stated. (c) In `README.md`, add one sentence pointing to `reviews/update_review.md` for the Proposition 4.1 update. (d) Commit this report as `reviews/update_review.md` if it is to be cited. |
| U5 | Cosmetic | Several new line ranges run onto blank or formatting lines, or are slightly off. | R22 "l. 1762–1902": the proof is l. 1761–1900. Step 1 is l. 1762–1825, but the docstrings of `DiscDivergence`, `NeumannDipole`, `NeumannEnergy` and `ScreenedField` cite "l. 1762–1827", and `ScreenedLower` "l. 1762--1826". `PhiExpectation` cites Step 3 as "l. 1864--1902"; it is l. 1864–1899. `ScreenedField` gives the Neumann problem as "l. 1777–1785" (l. 1777–1784). `exists_pairFactor_ge` cites "l. 1837--1841" (the bound is l. 1837–1840). `exists_log_pairFactor_ge` cites "l. 1848--1851" ((align57) is l. 1848–1850). `NeumannDipole` cites the decomposition `u_i = ... + v_i` as "(l. 1800–1806)"; it is defined on l. 1798. The energy of a disc is cited as "l. 1807–1814" in `NeumannEnergy` but "l. 1807–1815" in `NeumannDipole` and `ScreenedField`. | Optional: tighten to the ranges given. |
| U6 | Cosmetic | "Screened dipoles" is not the paper's term but reads as if it were. | The source does not contain "screen". `README.md` writes "(the screened dipoles)", R22 writes "(the screened dipoles)", and the commit title says "the paper's screened dipoles". | Optional: write "(the Neumann construction)", or "(here called the screened dipoles)". Reword the commit title, for example "Proposition 4.1: the proof follows the paper's Neumann construction (R22)". |
| U7 | Info | Declarations left without consumers. | Formerly used only by the removed R12a modules: `lintegral_pi_complex_eq_polar` and `lintegral_fin_prod_eq_prod` in `LowerBound/PolarPi.lean`, whose title still advertises "a Fubini lemma for products of radial weights", and `lowerRadius_nonneg` in `RadiusTail.lean`. New and unused: `neumannCorrection_apply`, `neumannCorrectionField_apply`, `neumannCorrectionHolo_apply`, `neumannPotential_apply`, `neumannHolo_apply`, `differentiableOn_neumannCorrectionHolo` and `integrable_neumannPotential`. The section note before the `_apply` lemmas says "later modules use these equations", but only `neumannField_apply` is used. `measurable_pairFactor` and `continuousOn_pairFactor` are also unused. `PolarPi`'s docstring calls `PhaseSpace/RadialSimplex.lean` an upper-bound module, and `PolarPi` now lives in `LowerBound/` while serving only upper-bound code. | Optional, as in the first release's dead-code sweep: delete the unused declarations or keep them as documented API, and fix the `PolarPi` title and the NeumannDipole section note. |
| U8 | Info | Commit trailer. | `aa8884a` ends with a `Co-Authored-By` trailer; `aeafcbb` has none. Author and committer are correct. | The authors' choice; only consistency is at stake. |
| U9 | Info | R22 is marked `EXPLICIT`. | `RULINGS.md` defines `EXPLICIT` as "the authors answered this ruling directly". | At the publication gate, have the authors confirm the text of R22, as was done for R21. |

## Actions before publishing the update

1. Fix U1 and U2 (comments only), and decide on U3.
2. Update `reviews/README.md` and the README's paragraph on reviews (U4), and add this report as
   `reviews/update_review.md`.
3. Optionally apply U5–U7.
4. Rerun `lake build`, `scripts/check_all.sh` and the README's axiom audit on the final commit.
   Confirm that `TwoComponentCoulomb/Frozen/` and `manifest/` are still byte-identical to
   `aa8884a`.
5. Have the authors confirm R22 (U9) and approve the push.

None of these actions touches a frozen file or a proof.
