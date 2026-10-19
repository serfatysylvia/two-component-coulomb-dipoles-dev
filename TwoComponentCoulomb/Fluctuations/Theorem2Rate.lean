/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.RadiiControlRates
public import TwoComponentCoulomb.Fluctuations.Theorem2AssemblyRates
public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.Energy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TwoComponentCoulomb.Frozen.M0
public import TwoComponentCoulomb.Frozen.GibbsMeasure
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.Frozen.PartitionFunction
public import TwoComponentCoulomb.Frozen.ReducedEnergy
public import TwoComponentCoulomb.UpperBound.IsolatedRadial
import TwoComponentCoulomb.Main.Theorem1AssemblyBounds

/-!
# Theorem 2, Steps 5--6: the rate properties, and Theorem 1 for a general rate

The error rate `ω_λ` enters the proof of Theorem 2 (source l. 2182--2247) both in the event
threshold `M N √ω_λ` and in the tail `e^{-c √N ω_λ}`. Steps 5--6 are proved for a general rate
function `ω : ℝ → ℝ` with the elementary properties collected in `Theorem2RateHyp`; they are
instantiated at `ω = errorRate β hβ` in `Fluctuations/Theorem2RateInstance.lean`.

* `Theorem2RateHyp β hβ ω` : the rate properties consumed by Steps 5--6 (positivity and `ω ≤ 1`
  on `(0, e⁻¹)`; for `β > 2`, `ω ≤ λ^a` and `λ^{4(β-2)/β} ≤ ω`; for `β = 2`, the two comparisons
  of `R₀ = ω^{1/4}`; the comparison `φ_β(γ) + γ² ≤ 3 √ω` for the choice of `γ`). It is a
  hypothesis of conditional helpers only; `errorRate` satisfies it
  (`theorem2RateHyp_errorRate`).
* `Theorem1ShapeRate β hβ ω` : the statement of Theorem 1 with `ω` in place of `ω_λ`, in the
  weaker form consumed by Steps 5--6: the `β > 2` long-dipole bound has the error `C₂ N √ω`, and the
  `β = 2` long-dipole bound has the term `(1 + log |log λ| + log (1/R)) / |log λ|` in place of
  `log (1/R) / |log λ|`. The frozen `theorem_1` implies
  `Theorem1ShapeRate β hβ (errorRate β hβ)` (`theorem1ShapeRate_of_theorem_1`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### The rate properties of Steps 5--6 -/

/-- **The properties of the rate `ω` used in Theorem 2, Steps 5--6** (source l. 2182--2247).
Each field is an elementary inequality about `ω` on an explicit range of `λ`. This
is a hypothesis of conditional helpers only; the `errorRate` instance is
`theorem2RateHyp_errorRate`. -/
structure Theorem2RateHyp (β : ℝ) (hβ : 2 ≤ β) (ω : ℝ → ℝ) : Prop where
  /-- `0 < ω(λ)` for `0 < λ < e⁻¹`. -/
  pos : ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) → 0 < ω lam
  /-- `ω(λ) ≤ 1` for `0 < λ < e⁻¹`. -/
  le_one : ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) → ω lam ≤ 1
  /-- For `β > 2`, `ω(λ) ≤ λ^a` for some `a > 0` and all `0 < λ < e⁻¹`. -/
  le_rpow : 2 < β → ∃ a : ℝ, 0 < a ∧ ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) → ω lam ≤ lam ^ a
  /-- For `β > 2`, `λ^{4(β-2)/β} ≤ ω(λ)` for `0 < λ < e⁻¹`. -/
  rpow_le : 2 < β → ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) → lam ^ (4 * (β - 2) / β) ≤ ω lam
  /-- For `β = 2`, `2λ ≤ ω(λ)^{1/4}` for `0 < λ < e⁻⁴`. -/
  two_mul_le_rpow_quarter : β = 2 → ∀ lam : ℝ, 0 < lam → lam < Real.exp (-4) →
    2 * lam ≤ ω lam ^ (1 / 4 : ℝ)
  /-- For `β = 2`, `(1 + log |log λ| + log (1/ω(λ)^{1/4})) / |log λ| ≤ 5 ω(λ)` for
  `0 < λ < e⁻⁴`. -/
  log_div_le : β = 2 → ∀ lam : ℝ, 0 < lam → lam < Real.exp (-4) →
    (1 + Real.log |Real.log lam| + Real.log (1 / ω lam ^ (1 / 4 : ℝ))) / |Real.log lam|
      ≤ 5 * ω lam
  /-- `φ_β(γ) + γ² ≤ 3 √ω(λ)` for `γ = gammaChoice β λ` and `0 < λ < e⁻⁴`. -/
  gammaChoice_le : ∀ lam : ℝ, 0 < lam → lam < Real.exp (-4) →
    isolatedPhi β hβ lam (gammaChoice β lam) + gammaChoice β lam ^ 2 ≤ 3 * Real.sqrt (ω lam)

/-! ### Theorem 1 for a general rate -/

/-- **The statement of Theorem 1 with a general rate `ω`**, in the form consumed by Steps 5--6
of the proof of Theorem 2: the statement of the frozen `TwoComponentCoulomb.theorem_1`
(`theorem:th1`, source l. 235--274) with `errorRate β hβ` replaced by `ω`, except that the
`β > 2` long-dipole bound has the error `C₂ N √ω` and its constants in the order (threshold, gain,
error), and the `β = 2` long-dipole bound has the term `(1 + log |log λ| + log (1/R)) / |log λ|`
in place of `log (1/R) / |log λ|` and its own threshold `λ₀`. Since `ω_λ ≤ √ω_λ` for
`ω_λ ≤ 1`, the frozen `theorem_1` implies `Theorem1ShapeRate β hβ (errorRate β hβ)`
(`theorem1ShapeRate_of_theorem_1`). This is a hypothesis of conditional helpers only. -/
def Theorem1ShapeRate (β : ℝ) (hβ : 2 ≤ β) (ω : ℝ → ℝ) : Prop :=
    ∃ lamβ : ℝ, 0 < lamβ ∧ lamβ < Real.exp (-1) ∧
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
          0 < partitionFunction N β lam ∧ partitionFunction N β lam < ∞ ∧
          |Real.log (partitionFunction N β lam).toReal
              - (2 * N * Real.log N
                + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                  + (if β = 2 then Real.log |Real.log lam| else 0)
                  + (Real.log (dipoleConstant β hβ) - 1)))|
            ≤ C * (N * ω lam + Real.log (N + 1)) ∧
          ∫⁻ Z, ENNReal.ofReal (Real.exp (β * (energy lam Z - reducedEnergy lam Z)))
              ∂gibbsMeasure N β lam
            ≤ ENNReal.ofReal (Real.exp (C * N * ω lam + C * Real.log (N + 1))) ∧
          ∀ p₀ : ℕ, p₀ ≤ N →
            gibbsMeasure N β lam {Z | (isolatedDipoles Z).card = p₀}
              ≤ ENNReal.ofReal (Real.exp (-c * N * (1 - (p₀ : ℝ) / N) ^ 2
                + C * N * ω lam + C * Real.log (N + 1)))) ∧
      (2 < β → ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, p₀' ≤ N →
          c * (lam / R) ^ (β - 2) ≤ (p₀' : ℝ) / N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (Real.exp
                (-C₁ * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) / (lam / R) ^ (β - 2))
                  + C₂ * N * Real.sqrt (ω lam) + C₂ * Real.log (N + 1)))) ∧
      (β = 2 → ∃ C lam₀ : ℝ, 0 < C ∧ 0 < lam₀ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 → ∀ p₀' : ℕ, p₀' ≤ N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (((N : ℝ) + 1) ^ C * Real.exp (-(p₀' : ℝ) + C * N *
                (ω lam
                  + (1 + Real.log |Real.log lam| + Real.log (1 / R)) / |Real.log lam|))))

end TwoComponentCoulomb

end
