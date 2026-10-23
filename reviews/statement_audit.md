# Statement audit: frozen declarations against the source (refute-first)

Audited tree: commit `c553d18`. Source: `source/dipole-formation.tex`. Its SHA-256 was recomputed as `2c6fc7b48ee7e9c0e4e8bb9591e513edba49ece4ce6c54bb493c4026147726f6`, which matches `README.md`, `RULINGS.md` and every manifest entry. Toolchain: Lean `v4.35.0-rc2`, Mathlib `v4.35.0-rc2`.

## Summary verdict

**PASS.** All 32 frozen declarations in `TwoComponentCoulomb/Frozen/` (25 definitions and 7 theorems) say what the pinned source says, read through the rulings in `RULINGS.md`. I found no unfaithful statement, no hypothesis smuggling, no vacuous or trivialized conjunct, and no non-standard axiom. Each ruling that shapes a statement is either a null-set or domain convention that the statements never consume, or a reformulation equivalent to the source. No ruling changes the mathematics. The findings at the end are informational or cosmetic only.

| Check | Verdict |
|---|---|
| 1. Definitions (25) | PASS |
| 2. Theorems (7) | PASS |
| 3. Hypothesis smuggling | PASS (0 EXCESS binders) |
| 4. Provider consumption and build | PASS |
| 5. Axioms | PASS |
| 6. Docstrings of the frozen files | PASS (cosmetic notes only) |

## Integrity of the frozen set

- `scripts/check_all.sh --no-build`:
  ```
  == module system and file size (max 1500 lines)
  check_lean_modules: PASS (156 Lean files, 0 comparator configurations)
  == project source checks
  PROJECT CHECKS OK (forbidden-token sweep (anchors present: run check_frozen_anchors.py too))
  == frozen statements against the manifest
  FROZEN-ANCHOR GUARD OK
  ALL CHECKS PASSED
  ```
- **File hashes, recomputed independently of the checker:**
  - All 25 definition files match their `full_file_sha256`.
  - Every `definition_closure` hash matches.
  - For all 7 theorems, the `prefix_sha256` and `suffix_sha256` match. The hashed region is every byte before and after the proof body.
  - Each theorem file contains each of the five `FROZEN_ANCHOR_*` markers exactly once.
- **One declaration per file:** each of the 32 frozen files contains exactly one declaration.
- **Elaborated forms:** `scripts/abi_hash.sh <module> <decl> def|theorem` was rerun for all 32 declarations. All 32 match the manifest's `abi_sha256`.
- **Forbidden tokens:** a sweep of every tracked `.lean` file for `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `implemented_by`, `extern`, `maxHeartbeats` and `maxRecDepth` found nothing.

## Check 1: Definitions (PASS)

Every definition is a literal definition. None is defined by a characterization, and none uses `Classical.choose`. So for all 25:

- WELL_DEFINEDNESS: N/A_LITERAL
- CHARACTERIZATION: N/A_LITERAL
- CHOICE_INDEPENDENCE: N/A

The two nearest-neighbour maps choose with the deterministic `Finset.min'` (R4). Where `open scoped Classical` appears, it only supplies decidability instances, which do not change any value.

| Declaration | Source | Lean body against source | Carrier and conventions | BODY_MATCH / PUBLIC_CARRIER |
|---|---|---|---|---|
| `logKernel` | l. 137–139 | `-Real.log ‖x‖` = g(x) = −log\|x\| | ℂ ≅ ℝ² (R1). g(0) = 0 by Mathlib's `log 0 = 0`. This only affects the diagonal, a null set; arguments elsewhere are ≥ λ > 0 | OK / OK |
| `box` | l. 125 | `reProdIm (Icc 0 √N) (Icc 0 √N)` = [0,√N]² | — | OK / OK |
| `smearedCharge` | l. 148 | `cond volume (ball z a)` = (vol B)⁻¹·vol\|_B, the uniform mass-1 measure on B(z,a) for a > 0 (R2) | Zero measure for a ≤ 0 (R16), never consumed. The library proves `isProbabilityMeasure_smearedCharge` for a > 0 (`Potential/SmearedCharge.lean`) | OK / OK |
| `kappa` | l. 149–150 | ∫ g(x−y) d(δ₀⁽¹⁾⊗δ₀⁽¹⁾) (R3, R15) | Integrable. The library proves `kappa_eq : kappa = 1/4` | OK / OK |
| `smearedKernel` | l. 162–163 | ∫ g(x−y) d(δ₀^λ⊗δ_z^λ) | Total in λ (R16). The library proves Newton's identity `smearedKernel_eq_logKernel` for \|z\| ≥ 2λ and the scaling `smearedKernel_eq_logKernel_add` (eq. approxgeta, l. 418) | OK / OK |
| `charge` | l. 216 | `inl ↦ 1`, `inr ↦ −1` (checked by `rfl`) | Index type `Fin N ⊕ Fin N` (R1) | OK / OK |
| `energy` | l. 155–158 | ½ Σ_a Σ_b d_a d_b ∫ g(x−y) d(δ_{z_a}^λ⊗δ_{z_b}^λ) − N(g(λ)+κ): the bilinear expansion of eq:F3 (R3, R15). The diagonal terms are the self-interactions g(λ)+κ (l. 152, 159) | Total in λ (R16) | OK / OK |
| `partitionFunction` | l. 176–177 | ∫⁻ over Λ^{2N} of `ofReal (exp (−β F_λ))`, in [0,∞] (R10) | Product Lebesgue measure; `volume` on ℂ is Lebesgue on ℝ² (`Complex.volume_preserving_equiv_real_prod`) | OK / OK |
| `gibbsMeasure` | l. 172–174 | Z⁻¹ • (vol\|_{Λ^{2N}}).withDensity(e^{−βF_λ}) | A probability measure whenever Z < ∞ (`isProbabilityMeasure_gibbsMeasure`; Z > 0 for N ≥ 1 by `partitionFunction_pos`) | OK / OK |
| `dipoleConstant` | l. 208–213 | 2π if β = 2, else 2π ∫_{(0,∞)} e^{β g₁(r)} r dr | Takes `2 ≤ β` (R6). For β > 2 the integrand is integrable (`integrableOn_exp_smearedKernel_one`) and the value is positive (`dipoleConstant_pos`), so the Bochner integral is the true integral | OK / OK |
| `M0` | l. 233 | `36` | — | OK / OK |
| `nearestNeighbor` | l. 217 | Minimiser of \|z_i − z_j\| over j ≠ i. Ties go to the smallest index in the order x₁…x_N, y₁…y_N, via `finSumFinEquiv` (R4) | Total; the tie-break differs from the source only on the null set excluded at l. 217. `nearestNeighbor_spec` proves φ₁(i) ≠ i, minimality and the tie-break | OK / OK |
| `IsIsolatedDipole` | l. 222–230 | 2-cycle, no other vertex points into {i, φ₁ i}, and d_i d_{φ₁ i} = −1 (R5) | Equivalent to "forms a whole component" (`isIsolatedPair_iff_component`, `isIsolatedDipole_iff`) | OK / OK |
| `isolatedDipoles` | l. 230, 259 | Image of i ↦ {i, φ₁ i} over isolated-dipole vertices. Its cardinality is the number of isolated dipoles, i.e. \|I^dip\|/2 | — | OK / OK |
| `longIsolatedDipoles` | l. 263 | As above, restricted to R < \|z_i − z_{φ₁ i}\| ("length larger than R"; D_R of l. 1440, R20(4)) | — | OK / OK |
| `reducedEnergy` | l. 255–257 | −½ Σ_i g_λ(z_i − z_{φ₁ i}) 1{φ₁∘φ₁(i) = i, d_i d_{φ₁ i} = −1} | Not restricted to isolated cycles, as in the source | OK / OK |
| `fluct` | l. 298 | Σ_i d_i 1_Λ(z_i) ξ(z_i) = ∫_Λ ξ d(Σ δ_{x_i} − δ_{y_i}) | — | OK / OK |
| `errorRate` | l. 236–244 | Branches: β = 2: \|log λ\|^{−1/5}; β < 4: λ^{2(β−2)/(12−β+2M₀)}; β = 4: (λ\|log λ\|)^{2/(6+M₀)}; otherwise λ^{2/(4+M₀)}. Each branch was checked by `norm_num` at β = 2, 3, 4, 5 | Takes `2 ≤ β` (R6). 0 < ω ≤ 1 on (0, e⁻¹) (`errorRate_pos`, `errorRate_le_one`) | OK / OK |
| `IsGeneric` | l. 217, 348 | Injective Z, and equal distances only for the same unordered pair (R18(1)) | Exactly the excluded null set | OK / OK |
| `secondNearestNeighbor` | l. 367–368 | Minimiser over j ∉ {i, φ₁ i}, with the same tie-break (R4) | Takes `2 ≤ N` (R18(4)) | OK / OK |
| `firstNeighborRadius` | l. 365 (nn2) | max(¼ min_{j≠i} \|z_i − z_j\|, λ) | — | OK / OK |
| `secondNeighborRadius` | l. 367 (nn3, p = 2) | max(¼ min_{j∉{i,φ₁ i}} \|z_i − z_j\|, λ) | Takes `2 ≤ N` | OK / OK |
| `IsIsolatedPair` | l. 375–385 (defIdip) | 2-cycle with no attached tree (I^pair) | Component characterization proved (`isIsolatedPair_iff_component`) | OK / OK |
| `numComponents` | l. 375 | Number of connected components of `SimpleGraph.fromRel (φ₁ i = j)`, i.e. weakly connected components (l. 375) | `numComponents_le : K ≤ N` | OK / OK |
| `reducedPartitionFunction` | l. 922–930 | ∫⁻ over Λ^{2N} of e^{−β F̃_λ} | — | OK / OK |

DEFINITION_VERDICT: PASS for all 25.

## Check 2: Theorems (PASS)

Each theorem's body is `by exact <provider>`. Binders were classified as follows:

- **TYPING:** a variable that only forms a type.
- **SOURCE:** a premise stated in the source.
- **RULED:** a premise fixed by a ruling.
- **STANDING:** a field of a standing assumption.
- **EXCESS:** anything else.

No theorem has a STANDING or EXCESS binder. Every existentially quantified constant comes before N, λ, R, p₀ and ξ₀, as R7 and R11 require.

### Theorem 1 (`theorem_1`, l. 235–274)

**Binders (31).**

| Binder (clause) | Bin | Citation |
|---|---|---|
| `β : ℝ` | TYPING | l. 236 |
| `hβ : 2 ≤ β` | SOURCE | l. 236, 245 ("For β ≥ 2"); R6 |
| clause A (items 1, 2 and 3a): `N : ℕ`, `lam : ℝ`, `p₀ : ℕ` | TYPING ×3 | — |
| clause A: `2 ≤ N`, `0 < lam`, `lam < lamβ` | SOURCE ×3 | l. 245 |
| clause A: `p₀ ≤ N` | SOURCE | l. 259 |
| clause B (item 3b): `N`, `lam`, `R`, `p₀'` | TYPING ×4 | — |
| clause B: `2 < β` | SOURCE | l. 263 |
| clause B: `2 ≤ N`, `0 < lam`, `lam < lamβ` | SOURCE ×3 | l. 245 |
| clause B: `2 * lam ≤ R`, `p₀' ≤ N` | SOURCE ×2 | l. 263 |
| clause B: `C₁ * (lam / R) ^ (β - 2) ≤ p₀' / N` | SOURCE | l. 263 (x₀ ≥ C_β α) |
| clause C (β = 2 bullet): `N`, `lam`, `R`, `p₀'` | TYPING ×4 | — |
| clause C: `β = 2` | SOURCE | l. 267 |
| clause C: `2 ≤ N`, `0 < lam`, `lam < lamβ` | SOURCE ×3 | l. 267; shared threshold R20(1) |
| clause C: `2 * lam ≤ R`, `R ≤ 1`, `p₀' ≤ N` | SOURCE ×3 | l. 267 |

Counts: TYPING 12, SOURCE 19, STANDING 0, RULED 0, EXCESS 0.

**Conclusions.**
- λ_β ∈ (0, e⁻¹), quantified first.
- Item 1: 0 < Z < ∞, and the two-sided bound \|log Z − (2N log N + N((2−β)log λ·1_{β>2} + log\|log λ\|·1_{β=2} + log 𝒵_β − 1))\| ≤ C(Nω_λ + log(N+1)). This is eq:devlogz, l. 247–249.
- Item 2: E_P[e^{β(F_λ − F̃_λ)}] ≤ e^{CNω + C log(N+1)}. This is eq:momexp, l. 251–257, in the form fixed by R10.
- Item 3a: P(#isolated dipoles = p₀) ≤ exp(−cN(1 − p₀/N)² + CNω + C log(N+1)). This is eq:b1.
- Item 3b: eq:b2, with α = (λ/R)^{β−2}.
- Item 3c: eq:critical lengths.

The joint form with one shared λ_β follows R9 and R20(1). The separate C₁ (threshold) and C₂ (error) follow R20(3). Using one C for items 1, 2 and 3a, and a separate c in 3b, is equivalent to the source: every bound gets weaker as C grows. In 3b, raising C₁ to at least 1 makes log(x₀/α) ≥ 0, so taking the minimum of the c's also only weakens the bound.

Not formalized: the remark "observe that ω_λ = o_λ(1)" (l. 244). It is a property of the literal definition, since every exponent is positive, and is not a claim about the model.

**Vacuity and Lean conventions.**
- `toReal` is applied only after 0 < Z < ∞ is asserted in the same conjunction.
- Every `ofReal` argument is exp(·), or a positive multiple of it, so `ofReal` never truncates.
- Every `rpow` base is positive: λ/R > 0 and N+1 > 0.
- Every log argument is positive:
  - \|log λ\| > 1 because λ < e⁻¹;
  - 𝒵_β > 0 by `dipoleConstant_pos`;
  - p₀' ≥ 1 is forced in 3b, since C₁α > 0.
- No division by zero: N ≥ 2 and \|log λ\| > 1.
- ω_λ ∈ (0, 1].

### Theorem 2 (`theorem_2`, l. 297–305)

**Binders (13).**

| Binder | Bin | Citation |
|---|---|---|
| `β`, `M`, `ξ₀ : ℂ → ℝ`, `N`, `lam` | TYPING ×5 | l. 298–299; R1 |
| `hβ : 2 ≤ β` | SOURCE | l. 298 |
| `Mβ < M` | SOURCE | l. 299 |
| `HasCompactSupport ξ₀` | SOURCE | l. 298; R7 |
| `L : ℝ≥0` | RULED | R8 |
| `LipschitzWith L ξ₀` | SOURCE | l. 298; R8 |
| `2 ≤ N`, `0 < lam`, `lam < lamβ` | SOURCE ×3 | l. 299 |

Counts: TYPING 5, SOURCE 7, RULED 1, EXCESS 0.

**Quantifier order.** ∃ λ_β, M_β, C_β, then ∀ M > M_β, then ∃ c, then ∀ ξ₀, L, N, λ. So c depends on β and M only and is uniform in ξ₀ (l. 299, R7).

**Conclusion.**
- The event is {M N ω_λ^{1/2} L² < Fluct_N(ξ)²}, with ξ = ξ₀(N^{−1/2}·), and its probability is at most C_β e^{−c√N ω_λ}.
- Every Lipschitz constant L works, and the best one is ‖∇ξ₀‖_∞ (l. 305). So the R8 reading is equivalent to the source.
- Not restating 0 < Z < ∞ (R17) does not make the statement vacuous. For fixed λ > 0 the energy is bounded on the bounded box, so Z is finite and positive for every λ > 0, and `gibbsMeasure` is a genuine probability measure throughout the range.

### Proposition 2.2 (`proposition_2_2`, l. 434–443) and Corollary 2.3 (`corollary_2_3`, l. 452–464)

**Binders (7 each).**

| Binder | Bin | Citation |
|---|---|---|
| `N`, `lam`, `Z` | TYPING ×3 | R1 |
| `hN : 2 ≤ N` | SOURCE | l. 348 |
| `0 < lam` | SOURCE | l. 142, 148; all λ > 0 by R18(5) |
| `∀ i, Z i ∈ box N` | SOURCE | l. 125 |
| `IsGeneric Z` | RULED | R18(1); l. 217, 348 |

Counts per theorem: TYPING 3, SOURCE 3, RULED 1, EXCESS 0. ∃ C comes before every binder ("C universal", l. 442, 463).

**Proposition 2.2.** Under genericity, the cycles are exactly the 2-cycles, so the sums over 𝒞_k and ℐ_k ∖ 𝒞_k become sums over 2-cycle vertices and over tree vertices (R18(3)). I checked the parse with an out-of-tree probe. A fully parenthesized restatement is syntactically identical (`Expr.eqv` = true) to the frozen type. In particular, the factor ½ multiplies the difference of the cycle sum and the tree sum, as in the source (`\hal\sum_k\Bigg(…−\sum_{ℐ_k∖𝒞_k}…\Bigg)`). The term d_i D_i equals `charge i * (charge i + charge (φ₁ i))` (eq. defD, l. 430).

**Corollary 2.3.**
- The filters encode the source's index sets exactly:
  - I^pair ∖ I^dip with φ₂(i), φ₂(φ₁(i)) ∈ I^pair;
  - I^dip with the same two conditions.
- K = `numComponents`, and N − K ≥ 0 by `numComponents_le`.
- The parse was confirmed the same way as for Proposition 2.2.
- A single shared C is the source's form, and the bound is monotone in C.

### Lemma 3.6 (`lemma_3_6`, l. 922–946)

**Binders (7).** `β`, `N`, `lam` are TYPING. `hβ` (l. 923), `2 ≤ N`, `0 < lam` and `lam < lam₀` (l. 923) are SOURCE. Counts: TYPING 3, SOURCE 4, EXCESS 0.

**Conclusion.** 0 < 𝒦 < ∞, and \|log 𝒦 − main term\| ≤ C(N ω̄_λ + log(N+1)). Here ω̄_λ = \|log λ\|^{−1/2} at β = 2 and λ^{min((β−2)/2, 1)} otherwise (def:o nn, l. 938–943).

The cap λ_β ≤ e⁻² is omitted (R19). This is equivalent, because any threshold can be lowered to min(λ₀, e⁻²). It also exposes no Lean convention to exploit: a larger λ₀ only adds obligations.

### Proposition 3.10 (`proposition_3_10`, l. 1423–1455)

**Binders (30).**

| Binder (clause) | Bin | Citation |
|---|---|---|
| `β` | TYPING | — |
| `hβ` | SOURCE | l. 1424 |
| clause A (ubz and eq:neutral bound): `N`, `lam`, `p₀` | TYPING ×3 | — |
| clause A: `2 ≤ N`, `0 < lam`, `lam < lam₀`, `p₀ ≤ N` | SOURCE ×4 | l. 1424, 1430 |
| clause B (eq:u bound): `N`, `lam`, `R`, `p₀'` | TYPING ×4 | — |
| clause B: `2 < β`, `2 ≤ N`, `0 < lam`, `lam < lam₀`, `2 * lam ≤ R`, `1 ≤ p₀'`, `p₀' ≤ N`, `C₁·α ≤ p₀'/N` | SOURCE ×8 | l. 1440 |
| clause C (eq:critical upper): `N`, `lam`, `R` | TYPING ×3 | — |
| clause C: `β = 2`, `2 ≤ N`, `0 < lam`, `lam < lam₀`, `2 * lam ≤ R`, `R ≤ 1` | SOURCE ×6 | l. 1447 |

Counts: TYPING 11, SOURCE 19, EXCESS 0.

**Conclusions.**
- 0 < λ₀ ≤ e⁻² (R20(2)).
- ubz in the form Z ≤ exp(…) (R10).
- 𝒜(p₀) = {\|I^dip\| = 2p₀}, written `(isolatedDipoles Z).card = p₀` (R18(4)).
- α = μ_β([R/λ, ∞)) is written out as (2π/𝒵_β)∫_{[R/λ,∞)} e^{βg₁(r)} r dr (eq:defmu, l. 205).
- The event is {D_R ≥ p₀'}, with D_R = `longIsolatedDipoles` (R20(4)).
- The critical weight is e^{−2F_λ + N − \|I^dip\|/2 + D_R}. A pp.all inspection confirms that the casts sit at the leaves, so the arithmetic is real, with no truncated ℕ subtraction.

Separate constants c, C₁, C₂ are equivalent to the source's reused symbols by the same monotonicity argument as for Theorem 1, using α ≤ 1.

### Proposition 4.1 (`proposition_4_1`, l. 1745–1759)

**Binders (7).** `β`, `N`, `lam` are TYPING. `hβ` (β ∈ (2,∞) or β = 2), `2 ≤ N`, `0 < lam` and `lam < lam₀` ("as λ → 0, uniformly in N ≥ 2", l. 1746) are SOURCE. Counts: TYPING 3, SOURCE 4, EXCESS 0.

**Conclusion.** exp(2N log N + N(log\|log λ\| or (2−β)log λ) + N(log 𝒵_β − 1) − CN·err) ≤ Z. The error term is:
- \|log λ\|^{−1/5} at β = 2;
- λ^{β−2} for β ∈ (2,4);
- λ²\|log λ\|² at β = 4;
- λ²\|log λ\| for β > 4.

These are lbz and eq:lbz2. The O_β term enters a lower bound with a minus sign, which is correct.

## Check 3: Hypothesis smuggling (PASS)

- Every binder of the seven theorems is classified above: 102 binders in total, 0 EXCESS. No binder is an estimate, an intermediate result or a proof step.
- The Prop-valued definitions are `IsGeneric`, `IsIsolatedDipole` and `IsIsolatedPair`. Each is a predicate defined in the source (l. 217/348, 230, 381–383). None is an assumption bundle.
- The only extra arguments of definitions are `2 ≤ β` (R6) and `2 ≤ N` (R18(4)). These are domain conditions, not mathematical content.

**Elaboration independence.** Each frozen theorem file imports its provider privately. To rule out a provider changing how the statement elaborates (instances, notation), I re-elaborated each statement's text out of tree, importing only that file's `public import`s, so with no provider. Its `pp.all` rendering and `Expr.hash` are identical to those of the compiled frozen declaration, for all 7 theorems:

```
theorem_1 pp.all IDENTICAL (37480 bytes)    theorem_2 pp.all IDENTICAL (10158 bytes)
proposition_2_2 IDENTICAL (6740 bytes)      corollary_2_3 IDENTICAL (10648 bytes)
lemma_3_6 IDENTICAL (12401 bytes)           proposition_3_10 IDENTICAL (67893 bytes)
proposition_4_1 IDENTICAL (12301 bytes)
```

The library outside `Frozen/` declares only `Prop`-valued instances (`Nontrivial`, `IsFiniteMeasure`, a `local` `MeasurableSingletonClass`). It declares no notation or macros.

## Check 4: Provider consumption (PASS)

- **Build:** `lake build TwoComponentCoulomb` → `Build completed successfully (3349 jobs).`
- **Proof bodies:** each of the 7 is exactly `by exact <implementation.export>` from the manifest:

| Theorem | Provider |
|---|---|
| `theorem_1` | `TwoComponentCoulomb.Main.theorem_1` |
| `theorem_2` | `TwoComponentCoulomb.Main.theorem_2` |
| `proposition_2_2` | `TwoComponentCoulomb.Energy.proposition_2_2` |
| `corollary_2_3` | `TwoComponentCoulomb.Energy.corollary_2_3` |
| `lemma_3_6` | `TwoComponentCoulomb.UpperBound.lemma_3_6` |
| `proposition_3_10` | `TwoComponentCoulomb.UpperBound.proposition_3_10` |
| `proposition_4_1` | `TwoComponentCoulomb.LowerBound.proposition_4_1` |

`#print TwoComponentCoulomb.theorem_1` gives `fun β hβ => TwoComponentCoulomb.Main.theorem_1`.

**Out-of-tree probe** (`import TwoComponentCoulomb`), run with `lake env lean <probe>`:

```lean
example : type_of% @TwoComponentCoulomb.theorem_1 := @TwoComponentCoulomb.Main.theorem_1
-- … likewise for the other six with their providers
```

All seven compile. Comparing the declared types directly:

```
theorem_1 vs Main.theorem_1: eqv (up to binder info) = true; strict = false
theorem_2 vs Main.theorem_2: eqv (up to binder info) = true; strict = false
proposition_2_2 vs Energy.proposition_2_2: eqv (up to binder info) = true; strict = true
corollary_2_3 vs Energy.corollary_2_3: eqv (up to binder info) = true; strict = true
lemma_3_6 vs UpperBound.lemma_3_6: eqv (up to binder info) = true; strict = false
proposition_3_10 vs UpperBound.proposition_3_10: eqv (up to binder info) = true; strict = false
proposition_4_1 vs LowerBound.proposition_4_1: eqv (up to binder info) = true; strict = false
```

The five "strict = false" cases differ only in binder info: those providers take `{β : ℝ} {hβ : 2 ≤ β}` as implicit arguments, while the frozen statements take them explicitly. The form without `@` (`:= TwoComponentCoulomb.Main.theorem_1`) therefore fails with "Type mismatch" for those five, because Lean inserts metavariables for the implicit arguments. This is not a statement discrepancy.

## Check 5: Axioms (PASS)

```
$ scripts/print_axioms.sh TwoComponentCoulomb TwoComponentCoulomb.theorem_1 TwoComponentCoulomb.theorem_2 \
    TwoComponentCoulomb.proposition_2_2 TwoComponentCoulomb.corollary_2_3 TwoComponentCoulomb.lemma_3_6 \
    TwoComponentCoulomb.proposition_3_10 TwoComponentCoulomb.proposition_4_1
'TwoComponentCoulomb.theorem_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoComponentCoulomb.theorem_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoComponentCoulomb.proposition_2_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoComponentCoulomb.corollary_2_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoComponentCoulomb.lemma_3_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoComponentCoulomb.proposition_3_10' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoComponentCoulomb.proposition_4_1' depends on axioms: [propext, Classical.choice, Quot.sound]
AXIOMS OK
```

The same script run on all 25 definitions also gives `[propext, Classical.choice, Quot.sound]` for each, ending `AXIOMS OK`.

## Check 6: Docstrings of the frozen files (PASS)

- **Source ranges:** every module docstring's "Source: l. …" equals the manifest range for all 32 files. The ranges point at the right source text, and the LaTeX labels sit at the cited lines:
  - `theorem:th1` l. 235, `prop:linear` l. 297, `prop:mino2` l. 434, `coromino` l. 452, `lemma:part nn` l. 922, `prop:upper bound` l. 1423, `prop:lower bound` l. 1745;
  - equations at l. 149, 155, 163, 172, 176, 208, 237, 365, 367, 380.
- **Numbering:** the source's counters (`prop` numbered within sections; `lem` and `coro` share it) give exactly Proposition 2.2, Corollary 2.3, Lemma 3.6, Proposition 3.10 and Proposition 4.1.
- **Content:** each declaration docstring describes its statement or definition correctly. The cosmetic notes are listed under findings.

## The 32 frozen declarations

| # | Declaration | File | Source range | Ruling(s) | Verdict |
|---|---|---|---|---|---|
| 1 | `logKernel` | `Frozen/LogKernel.lean` | l. 137–139 | R17, R19 | PASS |
| 2 | `box` | `Frozen/Box.lean` | l. 125 | R17, R19 | PASS |
| 3 | `smearedCharge` | `Frozen/SmearedCharge.lean` | l. 148 | R2, R16, R17 | PASS |
| 4 | `kappa` | `Frozen/Kappa.lean` | l. 149–150 | R15, R17 | PASS |
| 5 | `smearedKernel` | `Frozen/SmearedKernel.lean` | l. 162–163 | R16, R17 | PASS |
| 6 | `charge` | `Frozen/Charge.lean` | l. 216 | R1, R17 | PASS |
| 7 | `energy` | `Frozen/Energy.lean` | l. 155–158 | R3, R15, R16 | PASS |
| 8 | `partitionFunction` | `Frozen/PartitionFunction.lean` | l. 176–177 | R10, R16 | PASS |
| 9 | `gibbsMeasure` | `Frozen/GibbsMeasure.lean` | l. 172–174 | R10, R16 | PASS |
| 10 | `dipoleConstant` | `Frozen/DipoleConstant.lean` | l. 208–213 | R6 | PASS |
| 11 | `M0` | `Frozen/M0.lean` | l. 233 | R17 | PASS |
| 12 | `nearestNeighbor` | `Frozen/NearestNeighbor.lean` | l. 217 | R4 | PASS |
| 13 | `IsIsolatedDipole` | `Frozen/IsIsolatedDipole.lean` | l. 222–230 | R5 | PASS |
| 14 | `isolatedDipoles` | `Frozen/IsolatedDipoles.lean` | l. 230, 259 | R17 | PASS |
| 15 | `longIsolatedDipoles` | `Frozen/LongIsolatedDipoles.lean` | l. 263 | R17, R20(4) | PASS |
| 16 | `reducedEnergy` | `Frozen/ReducedEnergy.lean` | l. 255–257 | R17 | PASS |
| 17 | `fluct` | `Frozen/Fluct.lean` | l. 298 | R17 | PASS |
| 18 | `IsGeneric` | `Frozen/IsGeneric.lean` | l. 217, 348 | R18(1) | PASS |
| 19 | `secondNearestNeighbor` | `Frozen/SecondNearestNeighbor.lean` | l. 367–368 | R4, R18(4) | PASS |
| 20 | `firstNeighborRadius` | `Frozen/FirstNeighborRadius.lean` | l. 365 | R18 | PASS |
| 21 | `secondNeighborRadius` | `Frozen/SecondNeighborRadius.lean` | l. 367 | R18(4) | PASS |
| 22 | `IsIsolatedPair` | `Frozen/IsIsolatedPair.lean` | l. 375–385 | R5, R18 | PASS |
| 23 | `numComponents` | `Frozen/NumComponents.lean` | l. 375 | R18 | PASS |
| 24 | `reducedPartitionFunction` | `Frozen/ReducedPartitionFunction.lean` | l. 922–930 | R18 | PASS |
| 25 | `errorRate` | `Frozen/ErrorRate.lean` | l. 236–244 | R6, R20 | PASS |
| 26 | `theorem_1` | `Frozen/Theorem1.lean` | l. 235–274 | R9, R10, R11, R20 | PASS |
| 27 | `theorem_2` | `Frozen/Theorem2.lean` | l. 297–305 | R7, R8, R17, R20 | PASS |
| 28 | `proposition_2_2` | `Frozen/Proposition22.lean` | l. 434–443 | R18(1,3,5), R19 | PASS |
| 29 | `corollary_2_3` | `Frozen/Corollary23.lean` | l. 452–464 | R18(1,5), R19 | PASS |
| 30 | `lemma_3_6` | `Frozen/Lemma36.lean` | l. 922–946 | R18(4), R19 | PASS |
| 31 | `proposition_3_10` | `Frozen/Proposition310.lean` | l. 1423–1455 | R10, R20 | PASS |
| 32 | `proposition_4_1` | `Frozen/Proposition41.lean` | l. 1745–1759 | R11, R19 | PASS |

All files are under `TwoComponentCoulomb/`.

## Findings, by severity

There are no Critical, Major or Minor findings. Every item below is informational or cosmetic.

1. **Informational: implicit arguments in the providers.** The providers of `theorem_1`, `theorem_2`, `lemma_3_6`, `proposition_3_10` and `proposition_4_1` take `{β} {hβ}` as implicit arguments. A consumption probe must therefore write `@Provider` (Check 4). Their types equal the frozen types up to binder info.
2. **Informational: thresholds.** Lemma 3.6 and Proposition 4.1 put no upper cap on their threshold λ₀. Lemma 3.6 drops the source's λ_β ≤ e⁻² (R19). This is equivalent to the source, and the existential threshold cannot be exploited through Lean's conventions for log or rpow at λ ≥ 1, because a larger λ₀ only adds obligations.
3. **Informational: constants.** Theorem 1 (3b) and Proposition 3.10 (eq:u bound) use separate constants (c, C₁, C₂) where the source reuses c_β and C_β. As argued above, this is equivalent.
4. **Informational: Theorem 2 and finiteness of Z.** Theorem 2 does not restate 0 < Z < ∞ (R17). Because Z is finite for every λ > 0, the Gibbs measure is never the zero measure, and the tail bound is never vacuous.
5. **Informational: total extensions.** `logKernel 0 = 0` (from `Real.log 0 = 0`), and the λ ≤ 0 values of R16, are never consumed: they occur only on null sets or outside every statement's λ range. The remark "ω_λ = o_λ(1)" (l. 244) is not stated as a theorem. It follows from the literal definition, and the library proves 0 < ω_λ ≤ 1 on (0, e⁻¹).
6. **Cosmetic: docstrings.**
   - The `smearedCharge` docstring says "the uniform probability measure on B(z, a)". That holds only for a > 0; for a ≤ 0 it is the zero measure (R16).
   - The module docstrings of the 28 declarations kept under R19 cite R17 or R18 only, while their manifest entries cite "R17, R19" or "R18, R19".
7. **Cosmetic: `reviews/` directory.** `README.md` says the reviewers' reports are in `reviews/`, but that directory does not exist at the audited commit. It is resolved once this report is added there.