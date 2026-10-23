**ALL MATCH. All 32 frozen declarations match the current manuscript.** The frozen upper bound corresponds jointly to current Propositions **3.9 and 3.10**.

Declaration names below omit `TwoComponentCoulomb.`. Current line ranges refer to [source/dipole-formation.tex](../source/dipole-formation.tex). Numbering of the revision of 2026-10-18 refers to commit `3d96e40`. “Unnumbered” means the definition or display has no printed number. Labels identify the containing result where the definition itself has none.

| # | Frozen declaration | Number in the revision of 2026-10-18 | Current number | Current label; lines | Verdict and comparison |
|---|---|---|---|---|---|
| 1 | `logKernel` | Eq. (1.4) | Unnumbered | No label; 122–125 | **MATCH**: same \(g(x)=-\log|x|\), with the accepted convention at zero. |
| 2 | `box` | Unnumbered | Unnumbered | No label; 110 | **MATCH**: same \(\Lambda=[0,\sqrt N]^2\). |
| 3 | `smearedCharge` | Unnumbered | Unnumbered | No label; 133 | **MATCH**: uniform measure of mass one on the disc, with radius \(\lambda>0\). |
| 4 | `kappa` | Eq. (1.6) | Unnumbered | Former `defkappa` label removed; 134–135 | **MATCH**: identical unit-disc self-interaction integral. |
| 5 | `smearedKernel` | Eq. (1.9) | Eq. (1.6) | `eq:defgeta`; 148–149 | **MATCH**: identical double integral between two smeared charges. |
| 6 | `charge` | Unnumbered | Unnumbered | No label; 201 | **MATCH**: positive charges first, negative charges second. Signs are unchanged. |
| 7 | `energy` | Eq. (1.8) | Eq. (1.5) | `eq:F3`; 140–143 | **MATCH**: same signed bilinear integral, factor \(1/2\), and subtraction \(N(g(\lambda)+\kappa)\). |
| 8 | `partitionFunction` | Eq. (1.12) | Unnumbered | Former `eq:ZRV` label removed; 161–162 | **MATCH**: same Lebesgue integral over \(\Lambda^{2N}\), without a factorial normalization. |
| 9 | `gibbsMeasure` | Eq. (1.11) | Eq. (1.7) | `defP`; 157–159 | **MATCH**: density \(Z^{-1}e^{-\beta F_\lambda}\) against the same Lebesgue measure. |
| 10 | `dipoleConstant` | Eq. (1.17) | Eq. (1.11) | `def:Cbeta`; 193–199 | **MATCH**: same radial integral for \(\beta>2\), and \(2\pi\) at \(\beta=2\). |
| 11 | `M0` | Unnumbered | Unnumbered | No label; 218 | **MATCH**: \(M_0=36\). |
| 12 | `nearestNeighbor` | Unnumbered | Unnumbered | No label; 202 | **MATCH**: nearest other point. Approved tie breaking affects only the excluded null set. |
| 13 | `IsIsolatedDipole` | Unnumbered | Unnumbered | No label; 207–215; also `defIdip`, 382–388 | **MATCH**: a whole two-vertex component with opposite signs. |
| 14 | `isolatedDipoles` | Unnumbered, Thm. 1(iii) | Unnumbered, Thm. 1(iii) | `theorem:th1`; 215, 250–251; also `defIdip`, 382–388 | **MATCH**: counts unordered dipoles once. Manuscript vertex count is twice this count. |
| 15 | `longIsolatedDipoles` | Unnumbered, Thm. 1(iii) | Unnumbered, Thm. 1(iii) | `theorem:th1`; 255; also `prop:upper bound`, 1357 | **MATCH**: isolated dipoles with actual length strictly greater than \(R\). |
| 16 | `reducedEnergy` | Unnumbered, Thm. 1(ii) | Unnumbered, Thm. 1(ii) | `theorem:th1`; 247–249; also `lemma:part nn`, 872–874 | **MATCH**: same sum over **all neutral two-cycles**, including those with attached trees. |
| 17 | `fluct` | Unnumbered, Thm. 2 | Unnumbered, Thm. 2 | `prop:linear`; 295 | **MATCH**: same signed point statistic integrated over \(\Lambda\). |
| 18 | `IsGeneric` | Unnumbered | Unnumbered | No label; 202, 351 | **MATCH**: distinct points and distinct distances for distinct unordered pairs. |
| 19 | `secondNearestNeighbor` | Unnumbered | Unnumbered | No separate label, following `nn3`; 370–371 | **MATCH**: excludes the point itself and its first neighbor. \(N\ge2\). |
| 20 | `firstNeighborRadius` | Eq. (2.3) | Eq. (2.2) | `nn2`; 368–369 | **MATCH**: one quarter of the first-neighbor distance, maximized with \(\lambda\). |
| 21 | `secondNeighborRadius` | Eq. (2.4), \(p=2\) | Eq. (2.3), \(p=2\) | `nn3`; 370–371 | **MATCH**: same exclusion, factor \(1/4\), and truncation by \(\lambda\). |
| 22 | `IsIsolatedPair` | Eq. (2.5) | Eq. (2.4) | `defIdip`; 378–386 | **MATCH**: isolated two-cycle, without a sign restriction. |
| 23 | `numComponents` | Unnumbered | Unnumbered | No label; 378–380 | **MATCH**: weakly connected components. Current wording explicitly says to forget orientations. |
| 24 | `reducedPartitionFunction` | Unnumbered, Lem. 3.6 | Unnumbered, Lem. 3.5 | `lemma:part nn`; 870–878 | **MATCH**: same integral of \(e^{-\beta\widetilde F_\lambda}\) over \(\Lambda^{2N}\). |
| 25 | `proposition_2_2` | Prop. 2.2; Eq. (2.9) | Prop. 2.2; Eq. (2.7) | `prop:mino2`, `minoF02`; 440–449 | **MATCH**: same standing assumptions, universal constant, cycle/tree sums, signs, and quadratic error. |
| 26 | `corollary_2_3` | Cor. 2.3; Eq. (2.10) | Cor. 2.3; Eq. (2.8) | `coromino`, `minoF02 bis`; 458–470 | **MATCH**: same retained-pair conditions, logarithmic gain, quadratic loss, and \(C(N-K)\) loss. |
| 27 | `lemma_3_6` | Lem. 3.6 | **Lem. 3.5** | `lemma:part nn`; 870–894 | **MATCH**: same positivity, finiteness, expansion, and both error-rate branches. The threshold cap is equivalent by shrinking it. |
| 28 | `proposition_4_1` | Prop. 4.1 | Prop. 4.1 | `prop:lower bound`, `lbz`, `eq:lbz2`; 1657–1668 | **MATCH**: current \(\varepsilon_\lambda\), defined at 334–340, expands to exactly the frozen errors; critical error remains \(CN|\log\lambda|^{-1/5}\). |
| 29 | `errorRate` | Eq. (1.18) | Eq. (1.12) | `eq:defgammal`; 221–229 | **MATCH**: all four branches, exponents, and \(M_0=36\) unchanged. |
| 30 | `proposition_3_10` | Prop. 3.10 | **Props. 3.9 and 3.10 jointly** | `prop:upper bound`, 1340–1363; `prop:critical upper`, 1575–1582; consequence explained at 1584 | **MATCH**: \(\beta>2\) clauses are now Prop. 3.9; the critical weighted estimate is Prop. 3.10 and implies the remaining critical clauses. |
| 31 | `theorem_1` | Thm. 1 | Thm. 1 | `theorem:th1`; 220–266 | **MATCH**: every conclusion and parameter range is preserved. The free-energy expansion is now split into Eqs. (1.13a–b). |
| 32 | `theorem_2` | Thm. 2 | Thm. 2 | `prop:linear`; 294–301; gradient convention at 302 | **MATCH**: same uniform constants, test functions, scaling, strict event inequality, and tail exponent. |

The following renames preserve the existing statements. For the joint upper-bound declaration, I recommend explicitly naming **both** current propositions. All declaration names remain relative to `TwoComponentCoulomb.`; file paths are relative to `TwoComponentCoulomb/`.

| Existing public declaration or file | Recommended name |
|---|---|
| `lemma_3_6` | `lemma_3_5` |
| `UpperBound.lemma_3_6` | `UpperBound.lemma_3_5` |
| `lemma_3_6_of_two_lt` | `lemma_3_5_of_two_lt` |
| `lemma_3_6_two` | `lemma_3_5_two` |
| `Lemma36Statement` | `Lemma35Statement` |
| `TwoComponentCoulomb/Frozen/Lemma36.lean` | `Frozen/Lemma35.lean` |
| `TwoComponentCoulomb/UpperBound/Lemma36.lean` | `UpperBound/Lemma35.lean` |
| `proposition_3_10`, joint frozen statement | `proposition_3_9_and_3_10` |
| `UpperBound.proposition_3_10`, joint implementation | `UpperBound.proposition_3_9_and_3_10` |
| `Proposition310Statement` | `Proposition39And310Statement` |
| `UpperAssembly.proposition_3_10_main_of_two_lt` | `UpperAssembly.proposition_3_9_main_of_two_lt` |
| `UpperAssembly.proposition_3_10_main_of_two_lt_rate` | `UpperAssembly.proposition_3_9_main_of_two_lt_rate` |
| `LongDipoles.proposition_3_10_long_of_two_lt` | `LongDipoles.proposition_3_9_long_of_two_lt` |
| `LongDipoles.proposition_3_10_long_of_two_lt_rate` | `LongDipoles.proposition_3_9_long_of_two_lt_rate` |
| `TwoComponentCoulomb/Frozen/Proposition310.lean` | `Frozen/Proposition39And310.lean` |
| `TwoComponentCoulomb/UpperBound/Proposition310.lean` | `UpperBound/Proposition39And310.lean` |

The critical declarations `proposition_3_10_main_two`, `proposition_3_10_critical`, namespace `Prop310Critical`, and file `UpperBound/Proposition310Critical.lean` can retain their numbers: their current counterpart is Proposition 3.10. Theorem 1, Theorem 2, Proposition 2.2, Corollary 2.3, and Proposition 4.1 also retain their numbers. If separate public exports are preferred, the natural names are `proposition_3_9` for the \(\beta>2\) result and `proposition_3_10` for the critical weighted estimate.

There are **no MISMATCH or NO COUNTERPART cases**. The substantive checks behind that conclusion are:

- **The upper-bound split preserves the complete frozen statement.** Current Proposition 3.9 contains the three \(\beta>2\) estimates, including the event \(D_R\ge n\) and the normalized tail \(\mu_\beta([R/\lambda,\infty))\). Current Proposition 3.10 contains the frozen critical weighted integral. Taking \(R=1\), writing \(m\) for the number of isolated dipoles, and using \(D_1\ge0\) gives both the partition-function bound and, on \(m=p_0\), a gain \(N-p_0\). Since
  \[
  N-p_0\ge N\left(1-\frac{p_0}{N}\right)^2,
  \]
  this supplies the frozen critical Gaussian count bound. The thresholds can be shared by taking their minimum. The new marked count \(\widehat p_0\) in the proof does not replace the actual isolated-dipole count in these statements.

- **The dependent definitions agree.** The energy retains its self-interaction subtraction; the Gibbs measure uses the same unnormalized Lebesgue reference measure; \(\widetilde F_\lambda\) includes neutral two-cycles without requiring isolation; and \(D_R\) counts unordered isolated dipoles of length \(>R\). The factors of two between particle counts and dipole counts are consistent.

- **Rates and uniformity agree.** Both sources use the same four branches of \(\omega_\lambda\), the same reduced-model rate, and the same lower-bound errors. Constants remain uniform in \(N,\lambda,R\), and the count parameters in their stated ranges. Theorem 2’s constants remain independent of the test function. The integral, logarithm, tie-breaking, and Lipschitz conventions are those recorded in [RULINGS.md](../RULINGS.md).

During the audit no files were edited, and neither Lean nor `lake` was run. The audited current manuscript has SHA-256 `f217f2cace961b1cbd66315ae194d10a72d054d34683823d5870deb818462b91`.
