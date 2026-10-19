/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.Theorem2Rate
public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.Energy
public import TwoComponentCoulomb.Frozen.ErrorRate
public import TwoComponentCoulomb.Frozen.GibbsMeasure
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.Frozen.PartitionFunction
public import TwoComponentCoulomb.Frozen.ReducedEnergy
import TwoComponentCoulomb.Main.ErrorRateBounds
import TwoComponentCoulomb.Main.Theorem1AssemblyBounds

/-!
# Theorem 2, Steps 5--6: the rate `errorRate`, and Theorem 1 in the general-rate shape

Source: Theorem 1 (`theorem:th1`, l. 235--274), Theorem 2 (`prop:linear`, l. 297--305), and the
proof of Theorem 2, Steps 5--6 (l. 2182--2247).

Steps 5--6 of the proof of Theorem 2 are proved for a general rate `ω` with the properties
`Theorem2RateHyp` (`Fluctuations/Theorem2Rate.lean`), consuming Theorem 1 in the shape
`Theorem1ShapeRate`. This file supplies the two inputs for the rate `ω_λ = errorRate β hβ λ`.

* `theorem2RateHyp_errorRate` : `Theorem2RateHyp β hβ (errorRate β hβ)`, from the elementary
  rate facts of `Main/ErrorRateBounds.lean`.
* `theorem1ShapeRate_of_theorem_1` : the statement of the frozen `theorem_1` (copied verbatim as the
  hypothesis `h`) implies `Theorem1ShapeRate β hβ (errorRate β hβ)`. This is an internal
  *conditional helper*; it is not a frozen statement and never stands in for one. The proof
  of `theorem_2` (`Main/Theorem2.lean`) discharges its hypothesis with the frozen `theorem_1`. The
  two statements differ only in the form of the two long-dipole bullets, as follows.
  * For `β > 2`, `theorem_1` has constants `(c, C₁, C₂)` with `C₁` the threshold and `c` the
    gain, while `Theorem1ShapeRate` has `c` the threshold, `C₁` the gain and `C₂ √ω_λ` the
    error; the constants are swapped and `ω_λ ≤ √ω_λ` (from `0 < ω_λ ≤ 1` on `(0, e⁻¹)`) is
    used.
  * For `β = 2`, `Theorem1ShapeRate` has the larger error term
    `(1 + log |log λ| + log (1/R)) / |log λ|` in place of `log (1/R) / |log λ|`
    (`1 + log |log λ| ≥ 0` for `0 < λ < e⁻¹`), and the threshold `λ₀ = λ_β`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-- The rate properties of Steps 5--6 (`Theorem2RateHyp`) for the rate
`ω_λ = errorRate β hβ λ`. -/
theorem theorem2RateHyp_errorRate (β : ℝ) (hβ : 2 ≤ β) :
    Theorem2RateHyp β hβ (errorRate β hβ) where
  pos _ h0 h1 := errorRate_pos β hβ h0 h1
  le_one _ h0 h1 := errorRate_le_one β hβ h0 h1
  le_rpow h2 := exists_errorRate_le_rpow β hβ h2
  rpow_le h2 _ h0 h1 := rpow_le_errorRate β hβ h2 h0 h1
  two_mul_le_rpow_quarter h _ h0 h1 := (R0_regime_of_eq_two hβ h h0 h1).1
  log_div_le h _ h0 h1 := (R0_regime_of_eq_two hβ h h0 h1).2
  gammaChoice_le _ h0 h1 := gamma_regime β hβ h0 h1 rfl

/-- **Conditional helper (not a frozen statement)**: the statement of the frozen
`TwoComponentCoulomb.theorem_1` (`theorem:th1`, source l. 235--274), copied verbatim as the
hypothesis `h`, implies `Theorem1ShapeRate β hβ (errorRate β hβ)`, the form of Theorem 1
consumed by Steps 5--6 of the proof of Theorem 2 (`theorem_2_of_moment_rate`).

The first block of `Theorem1ShapeRate` is the first block of `h`. In the `β > 2` bullet the
constants `(c, C₁, C₂)` of `h` become `(C₁, c, C₂)` and the error `C₂ N ω_λ` is bounded by
`C₂ N √ω_λ`. In the `β = 2` bullet the term `log (1/R) / |log λ|` is bounded by
`(1 + log |log λ| + log (1/R)) / |log λ|`. -/
theorem theorem1ShapeRate_of_theorem_1 (β : ℝ) (hβ : 2 ≤ β)
    (h : ∃ lamβ : ℝ, 0 < lamβ ∧ lamβ < Real.exp (-1) ∧
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
          0 < partitionFunction N β lam ∧ partitionFunction N β lam < ∞ ∧
          |Real.log (partitionFunction N β lam).toReal
              - (2 * N * Real.log N
                + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                  + (if β = 2 then Real.log |Real.log lam| else 0)
                  + (Real.log (dipoleConstant β hβ) - 1)))|
            ≤ C * (N * errorRate β hβ lam + Real.log (N + 1)) ∧
          ∫⁻ Z, ENNReal.ofReal (Real.exp (β * (energy lam Z - reducedEnergy lam Z)))
              ∂gibbsMeasure N β lam
            ≤ ENNReal.ofReal (Real.exp (C * N * errorRate β hβ lam + C * Real.log (N + 1))) ∧
          ∀ p₀ : ℕ, p₀ ≤ N →
            gibbsMeasure N β lam {Z | (isolatedDipoles Z).card = p₀}
              ≤ ENNReal.ofReal (Real.exp (-c * N * (1 - (p₀ : ℝ) / N) ^ 2
                + C * N * errorRate β hβ lam + C * Real.log (N + 1)))) ∧
      (2 < β → ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, p₀' ≤ N →
          C₁ * (lam / R) ^ (β - 2) ≤ (p₀' : ℝ) / N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (Real.exp
                (-c * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) / (lam / R) ^ (β - 2))
                  + C₂ * N * errorRate β hβ lam + C₂ * Real.log (N + 1)))) ∧
      (β = 2 → ∃ C : ℝ, 0 < C ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
        ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 → ∀ p₀' : ℕ, p₀' ≤ N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (((N : ℝ) + 1) ^ C * Real.exp (-(p₀' : ℝ) + C * N *
                (errorRate β hβ lam + Real.log (1 / R) / |Real.log lam|))))) :
    Theorem1ShapeRate β hβ (errorRate β hβ) := by
  obtain ⟨lamβ, hlam0, hlam1, hmain, hgt, heq⟩ := h
  refine ⟨lamβ, hlam0, hlam1, hmain, ?_, ?_⟩
  · intro h2
    obtain ⟨c, C₁, C₂, hc, hC₁, hC₂, hbound⟩ := hgt h2
    refine ⟨C₁, c, C₂, hC₁, hc, hC₂, fun N hN lam hl0 hl1 R hR p hp hthr => ?_⟩
    refine (hbound N hN lam hl0 hl1 R hR p hp hthr).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hl1' : lam < Real.exp (-1) := hl1.trans hlam1
    have hω0 : 0 ≤ errorRate β hβ lam := (errorRate_pos β hβ hl0 hl1').le
    have hω1 : errorRate β hβ lam ≤ 1 := errorRate_le_one β hβ hl0 hl1'
    have hsq : errorRate β hβ lam ≤ Real.sqrt (errorRate β hβ lam) :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    have hCN : 0 ≤ C₂ * (N : ℝ) := mul_nonneg hC₂.le (Nat.cast_nonneg N)
    have := mul_le_mul_of_nonneg_left hsq hCN
    linarith
  · intro h2
    obtain ⟨C, hC, hbound⟩ := heq h2
    refine ⟨C, lamβ, hC, hlam0, fun N hN lam hl0 hl1 R hR hR1 p hp => ?_⟩
    refine (hbound N hN lam hl0 hl1 R hR hR1 p hp).trans ?_
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (by positivity))
    have hℓ : 1 < |Real.log lam| := one_lt_abs_log hl0 (hl1.trans hlam1)
    have hlog : 0 ≤ Real.log |Real.log lam| := Real.log_nonneg hℓ.le
    have hdiv : Real.log (1 / R) / |Real.log lam|
        ≤ (1 + Real.log |Real.log lam| + Real.log (1 / R)) / |Real.log lam| :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hCN : 0 ≤ C * (N : ℝ) := mul_nonneg hC.le (Nat.cast_nonneg N)
    have := mul_le_mul_of_nonneg_left hdiv hCN
    linarith

end TwoComponentCoulomb

end
