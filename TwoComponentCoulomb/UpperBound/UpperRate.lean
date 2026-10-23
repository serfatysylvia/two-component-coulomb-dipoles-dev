/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.ErrorRate
public import TwoComponentCoulomb.UpperBound.LongDipoles
import TwoComponentCoulomb.Main.ErrorRateBounds

/-!
# Proposition 3.9 for `β > 2`: the bounds with the rate `errorRate`

Source: Proposition 3.9 (`prop:upper bound`, l. 1340–1363), proof for `β > 2`
(l. 1367–1568), with the error rate `ω_λ = errorRate β λ` of (eq:defgammal) (l. 221–229).

For `β > 2` the supremum bounds of Step 3 (l. 1507–1513) are, up to constants, the rates in
(eq:defgammal). The `β > 2` chain is generic in the rate
(`TwoComponentCoulomb.UpperRateHyp` and the `_rate` declarations of
`UpperBound/UpperOptimization.lean`, `UpperBound/UpperCellBound.lean`,
`UpperBound/UpperAssembly.lean` and `UpperBound/LongDipoles.lean`), so it suffices to check the
rate hypotheses for `errorRate`.

## Main results

* `TwoComponentCoulomb.upperRateHyp_errorRate`: `errorRate` satisfies the rate hypotheses of
  the upper bound for `β > 2`: it dominates the rates of Proposition 3.8 (l. 1183–1189,
  1905--1911) and the suprema of `χ_β` (l. 1507–1513).
* `TwoComponentCoulomb.UpperAssembly.proposition_3_9_main_of_two_lt`: (ubz) and
  (eq:neutral bound) for `β > 2` with `errorRate` (l. 1342–1355).
* `TwoComponentCoulomb.LongDipoles.proposition_3_9_long_of_two_lt`: (eq:u bound) for `β > 2`
  with `errorRate` (l. 1357–1362).

These are the `β > 2` parts of the frozen `TwoComponentCoulomb.proposition_3_9_and_3_10` (with the
threshold still to be capped at `e⁻²` in `UpperBound/Proposition39And310.lean`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### The rate hypotheses for `errorRate` -/

section Rate

/-- `errorRate` for `2 < β < 4`, in the form of the supremum bound of Step 3. -/
private theorem errorRate_eq_of_lt_four {β : ℝ} (hβ : 2 < β) (h4 : β < 4) (lam : ℝ) :
    errorRate β hβ.le lam = lam ^ (2 * (β - 2) / (12 - β + 2 * M0)) := by
  unfold errorRate
  rw [ite_eq_right hβ.ne', ite_eq_left h4]

/-- `errorRate` for `β = 4`, in the form of the supremum bound of Step 3. -/
private theorem errorRate_eq_of_eq_four (hβ : 2 < (4 : ℝ)) (lam : ℝ) :
    errorRate 4 hβ.le lam = (lam * |Real.log lam|) ^ (2 / (M0 + 6)) := by
  unfold errorRate
  rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num), ite_eq_left rfl,
    add_comm (6 : ℝ) M0]

/-- `errorRate` for `β > 4`, in the form of the supremum bound of Step 3. -/
private theorem errorRate_eq_of_four_lt {β : ℝ} (hβ : 2 < β) (h4 : 4 < β) (lam : ℝ) :
    errorRate β hβ.le lam = lam ^ (2 / (M0 + 4)) := by
  unfold errorRate
  rw [ite_eq_right hβ.ne', ite_eq_right (not_lt.2 h4.le), ite_eq_right h4.ne',
    add_comm (4 : ℝ) M0]

/-- **Supremum of `χ_β` against `errorRate`** (source l. 1507–1513): for `β > 2` and `C_β = C`
there is `C' > 0` with `χ_β(δ) ≤ C' ω_λ` for all `0 < λ < 1` and `δ ≥ 0`; the three suprema of
Step 3 are, up to the constant, exactly the rates of (eq:defgammal). -/
private theorem exists_chiBeta_le_errorRate {β : ℝ} (hβ : 2 < β) (C : ℝ) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ lam δ : ℝ, 0 < lam → lam < 1 → 0 ≤ δ →
      chiBeta β hβ lam C δ ≤ C' * errorRate β hβ.le lam := by
  rcases lt_trichotomy β 4 with h4 | rfl | h4
  · have hB : 0 < M0 + 2 + 4 - β / 2 := by rw [M0_eq]; linarith
    refine ⟨(M0 + 2 + 4 - β / 2) * Real.exp (C / (M0 + 2 + 4 - β / 2) - 1),
      mul_pos hB (Real.exp_pos _), fun lam δ h0 h1 hδ => ?_⟩
    rw [errorRate_eq_of_lt_four hβ h4]
    exact chiBeta_le_of_lt_four hβ h4 C h0 h1 hδ
  · have hB : 0 < M0 + 6 := by rw [M0_eq]; norm_num
    refine ⟨(M0 + 6) * Real.exp (C / (M0 + 6) - 1), mul_pos hB (Real.exp_pos _),
      fun lam δ h0 h1 hδ => ?_⟩
    rw [errorRate_eq_of_eq_four hβ]
    exact chiBeta_le_of_eq_four hβ C h0 h1 hδ
  · have hB : 0 < M0 + 4 := by rw [M0_eq]; norm_num
    refine ⟨(M0 + 4) * Real.exp (C / (M0 + 4) - 1), mul_pos hB (Real.exp_pos _),
      fun lam δ h0 h1 hδ => ?_⟩
    rw [errorRate_eq_of_four_lt hβ h4]
    exact chiBeta_le_of_four_lt hβ h4 C h0 h1 hδ

/-- **`errorRate` satisfies the rate hypotheses of the upper bound for `β > 2`**: `ω_λ =
errorRate β λ` (eq:defgammal, l. 221–229) is nonnegative, dominates the error rates of
Proposition 3.8 for `0 < λ ≤ e⁻¹` and dominates the suprema of
`χ_β` (Step 3, l. 1507–1513). -/
theorem upperRateHyp_errorRate (β : ℝ) (hβ : 2 < β) :
    UpperRateHyp β hβ (errorRate β hβ.le) where
  nonneg lam hlam := by
    unfold errorRate
    split_ifs <;> positivity
  isolated_le _ h0 h1 := isolatedRate_le_errorRate hβ h0 h1
  chi_le := exists_chiBeta_le_errorRate hβ

end Rate

/-! ### (ubz) and (eq:neutral bound) for `β > 2` with `errorRate` -/

namespace UpperAssembly

/-- **(ubz) and (eq:neutral bound) for `β > 2`** (`prop:upper bound`, Proposition 3.9, source
l. 1342–1355, proof l. 1367–1532): there are `λ₀ > 0` and
`C, c > 0`, depending only on `β`, such that for `N ≥ 2` and `0 < λ < λ₀`
`Z ≤ exp (2N log N + N((2-β) log λ + log 𝒵_β - 1 + C ω_λ) + C log (N + 1))` and, for every
`p₀ ≤ N`, `∫_{Λ^{2N} ∩ {|I^dip| = 2p₀}} e^{-β F_λ} ≤ exp (2N log N + N (2-β) log λ
+ N (log 𝒵_β - 1) - c N ((p₀ - N)/N)² + C N ω_λ + C log (N + 1))`, with
`ω_λ = errorRate β λ` (eq:defgammal). This is the first block of the frozen statement of
`proposition_3_9_and_3_10` with its `if`s resolved for `β > 2` (the threshold `λ₀ ≤ e⁻²` is imposed in
`UpperBound/Proposition39And310.lean`). -/
theorem proposition_3_9_main_of_two_lt {β : ℝ} (hβ : 2 < β) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          partitionFunction N β lam
              ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1
                  + C * errorRate β hβ.le lam)
                + C * Real.log (N + 1))) ∧
          ∀ p₀ : ℕ, p₀ ≤ N →
            ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
                {Z | (isolatedDipoles Z).card = p₀},
                ENNReal.ofReal (Real.exp (-β * energy lam Z))
              ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam)
                + N * (Real.log (dipoleConstant β hβ.le) - 1)
                - c * N * (((p₀ : ℝ) - N) / N) ^ 2
                + C * N * errorRate β hβ.le lam + C * Real.log (N + 1))) :=
  proposition_3_9_main_of_two_lt_rate hβ _ (upperRateHyp_errorRate β hβ)

end UpperAssembly

/-! ### (eq:u bound) for `β > 2` with `errorRate` -/

namespace LongDipoles

/-- **the union bound over long pairs and (eq:u bound) for `β > 2`** (`prop:upper bound`, Proposition 3.9, source
l. 1357–1362, proof l. 1547–1568): there are `λ₀ > 0` and
`c, C₁, C₂ > 0`, depending only on `β`, such that for `N ≥ 2`, `0 < λ < λ₀`, `R ≥ 2λ` and
`1 ≤ p₀' ≤ N` with `C₁ α ≤ x₀ = p₀'/N`, `α = μ_β([R/λ, ∞)) =
(2π/𝒵_β) ∫_{R/λ}^∞ e^{β g_1(r)} r dr`,
`∫_{Λ^{2N} ∩ {D_R ≥ p₀'}} e^{-β F_λ} ≤ exp (2N log N + N((2-β) log λ + log 𝒵_β - 1)
  - c N x₀ log (x₀/α) + C₂ N ω_λ + C₂ log (N + 1))`, with `ω_λ = errorRate β λ` and `D_R`
the number of isolated dipoles of length greater than `R` (l. 1357). This is the long-dipole
clause of the frozen statement of `proposition_3_9_and_3_10`, with `c = 1/2`. -/
theorem proposition_3_9_long_of_two_lt {β : ℝ} (hβ : 2 < β) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, 1 ≤ p₀' → p₀' ≤ N →
          C₁ * (2 * Real.pi / dipoleConstant β hβ.le *
              ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r) ≤ (p₀' : ℝ) / N →
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
              {Z | p₀' ≤ (longIsolatedDipoles Z R).card},
              ENNReal.ofReal (Real.exp (-β * energy lam Z))
            ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1)
                - c * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) /
                    (2 * Real.pi / dipoleConstant β hβ.le *
                      ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r))
                + C₂ * N * errorRate β hβ.le lam + C₂ * Real.log (N + 1))) :=
  proposition_3_9_long_of_two_lt_rate hβ _ (upperRateHyp_errorRate β hβ)

end LongDipoles

end TwoComponentCoulomb

end
