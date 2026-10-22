# Dipole formation in the two-component plasma, in Lean

[![Build and axiom audit](https://github.com/serfatysylvia/two-component-coulomb-dipoles-dev/actions/workflows/build.yml/badge.svg)](https://github.com/serfatysylvia/two-component-coulomb-dipoles-dev/actions/workflows/build.yml)

A Lean 4 / Mathlib formalization of the main results of

> J. Boursier and S. Serfaty, *Dipole Formation in the Two-component Plasma*,
> [arXiv:2410.01025](https://arxiv.org/abs/2410.01025).

The formalized text is the authors' revised manuscript in `source/dipole-formation.tex`,
pinned at SHA-256 `2c6fc7b48ee7e9c0e4e8bb9591e513edba49ece4ce6c54bb493c4026147726f6`. Its
statements and numbering differ from arXiv version 1. Line numbers in this repository, in
`RULINGS.md` and in the Lean docstrings refer to that file.

## Results

All seven results below are proved. Their proofs use only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). The repository contains no `sorry` and no
custom axioms.

| Result | Source (l.) | Lean declaration | Statement file |
|---|---|---|---|
| Theorem 1 | 235–274 | `TwoComponentCoulomb.theorem_1` | `TwoComponentCoulomb/Frozen/Theorem1.lean` |
| Theorem 2 | 297–305 | `TwoComponentCoulomb.theorem_2` | `TwoComponentCoulomb/Frozen/Theorem2.lean` |
| Proposition 2.2 | 434–443 | `TwoComponentCoulomb.proposition_2_2` | `TwoComponentCoulomb/Frozen/Proposition22.lean` |
| Corollary 2.3 | 452–464 | `TwoComponentCoulomb.corollary_2_3` | `TwoComponentCoulomb/Frozen/Corollary23.lean` |
| Lemma 3.6 | 922–946 | `TwoComponentCoulomb.lemma_3_6` | `TwoComponentCoulomb/Frozen/Lemma36.lean` |
| Proposition 3.10 | 1423–1455 | `TwoComponentCoulomb.proposition_3_10` | `TwoComponentCoulomb/Frozen/Proposition310.lean` |
| Proposition 4.1 | 1745–1759 | `TwoComponentCoulomb.proposition_4_1` | `TwoComponentCoulomb/Frozen/Proposition41.lean` |

Theorem 1 gives `0 < Z < ∞` and the free-energy expansion of `log Z` up to
`O(N ω_λ) + O(log(N+1))`; the exponential moment bound showing that the energy reduces to the
nearest-neighbour interactions of dipoles; and the bounds on the number of isolated dipoles,
on the number of long isolated dipoles for β > 2, and on dipole lengths at β = 2. Theorem 2 is
the tail bound for fluctuations of linear statistics with Lipschitz test functions.
The intermediate results are the paper's nearest-neighbour energy decomposition (Prop 2.2,
Cor 2.3), the free energy of the reduced dipole model (Lemma 3.6), and the upper and lower
bounds on the partition function (Props 3.10 and 4.1).

## How to read the statements

Each of these seven statements, and each of the 25 definitions they use (the energy, the
partition function and Gibbs measure, the nearest-neighbour graph and its dipoles, the error
rate ω_λ, and so on), lives alone in a file under `TwoComponentCoulomb/Frozen/`. The authors
approved every one of them in its exact Lean form before it was proved, and
`manifest/frozen_anchors.json` records each file's hashes, its source range and the approval.
`scripts/check_frozen_anchors.py` checks the files against the manifest.

The choices made in transcribing the paper are recorded in `RULINGS.md`: for example, ℝ² is
modelled by `ℂ` (R1), every `O_β(·)` becomes an explicit constant quantified before `N`, `λ`,
`R` and `p₀` (R11), the constants of Theorem 2 are uniform in the test function (R7), and
‖∇ξ₀‖_∞ is read as a Lipschitz constant (R8). Quantities that the paper defines only for
β ≥ 2 take `2 ≤ β` as an argument (R6).

Before release, independent reviewers compared every frozen statement and definition with the
source and checked the proofs' axioms (`reviews/statement_audit.md`), and checked the release
itself: its derivation from the development repository, a clean build and its documentation
(`reviews/release_review.md`). The later update of the proof of Proposition 4.1 was reviewed in
`reviews/update_review.md`.

The proof of Proposition 4.1 is the paper's argument (R22). In its Step 1 (the construction of
the screened dipoles), the Neumann problem on each disc is solved explicitly by an image charge,
and the estimate (estimatesv) is proved from that formula (R22a). The other implementation
choices are recorded in `RULINGS.md` (for example R12b and R12c), and the module docstrings note
where a proof step is carried out differently in detail from the paper.

## Terminology

The docstrings use a few terms for how the proofs are organized.

* A **frozen statement** (or **anchor**) is one of the 32 declarations in
  `TwoComponentCoulomb/Frozen/`, approved by the authors in its exact form.
* Each frozen theorem has a **provider**: the theorem of the same name in an ordinary module
  (for example `TwoComponentCoulomb.Main.theorem_1`) that proves exactly the frozen statement. The
  frozen theorem is **sealed**: its proof is `by exact` the provider, checked by
  `scripts/check_frozen_anchors.py`.
* The **gates** are the frozen intermediate results (Proposition 2.2, Corollary 2.3, Lemma 3.6,
  Propositions 3.10 and 4.1). For example, `theorem_1_of_gates` derives Theorem 1 from the
  statements of Lemma 3.6 and Proposition 3.10; the frozen proofs then supply those statements.
* A **conditional helper** is an internal lemma with extra hypotheses that is applied only after
  those hypotheses are proved; it never stands in for a frozen statement.

## Build and check

Install Lean with [elan](https://github.com/leanprover/elan), then:

```bash
lake exe cache get   # download the compiled Mathlib
lake build
```

The toolchain is Lean `v4.35.0-rc2` (`lean-toolchain`), with Mathlib `v4.35.0-rc2`; the exact
revisions of all dependencies are pinned in `lake-manifest.json`. `import TwoComponentCoulomb`
gives the seven results. To audit their axioms:

```bash
scripts/print_axioms.sh TwoComponentCoulomb \
  TwoComponentCoulomb.theorem_1 TwoComponentCoulomb.theorem_2 \
  TwoComponentCoulomb.proposition_2_2 TwoComponentCoulomb.corollary_2_3 \
  TwoComponentCoulomb.lemma_3_6 TwoComponentCoulomb.proposition_3_10 \
  TwoComponentCoulomb.proposition_4_1
```

`scripts/check_all.sh` runs the full project check: the build, the module and file-size
checks, a sweep for forbidden constructs (heartbeat overrides, `native_decide`, `opaque`, ...)
and the frozen-statement check against the manifest. `scripts/README.md` describes each script.

## Layout

| Path | Contents |
|---|---|
| `source/` | The paper (the authors' revised LaTeX source) |
| `TwoComponentCoulomb/Frozen/` | The frozen statements and definitions |
| `TwoComponentCoulomb/Potential/` | Disc potentials, Newton's theorem, the electric formulation |
| `TwoComponentCoulomb/NearestNeighbor/` | Nearest-neighbour maps and radii, graph structure, counting |
| `TwoComponentCoulomb/Integrals/` | Dirichlet-type and radial integrals, Stirling and entropy bounds |
| `TwoComponentCoulomb/PhaseSpace/` | Graph partition of configuration space, Gunson–Panta variables |
| `TwoComponentCoulomb/Gibbs/` | Partition function and Gibbs measure |
| `TwoComponentCoulomb/Energy/` | §2: nearest-neighbour lower bound |
| `TwoComponentCoulomb/UpperBound/` | §3: upper bound on the partition function |
| `TwoComponentCoulomb/LowerBound/` | §4: lower bound |
| `TwoComponentCoulomb/Fluctuations/` | §5: fluctuations of linear statistics |
| `TwoComponentCoulomb/Main/` | Assembly of the proofs of Theorems 1 and 2 |
| `manifest/` | Hashes, sources and approvals of the frozen declarations |
| `RULINGS.md` | The authors' rulings on how the statements read the paper |
| `reviews/` | Independent reviews of the statements and of the release |
| `scripts/` | Project checks |

## License and citation

The Lean code and the project's scripts are © 2026 Sylvia Serfaty and are
released under the Apache License 2.0 (`LICENSE`). Two checking scripts,
`scripts/check_frozen_anchors.py` and `scripts/check_lean_modules.py`, are used unmodified from
[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills) by
Scott Armstrong (Copyright © 2026 Scott Armstrong), licensed under [CC BY
4.0](https://creativecommons.org/licenses/by/4.0/) (see `scripts/README.md`). The manuscript in
`source/` is © its authors and is included for reference only; it is not covered by these licenses
(see `source/README.md`). If you use this formalization, please cite the paper (see `CITATION.cff`).
