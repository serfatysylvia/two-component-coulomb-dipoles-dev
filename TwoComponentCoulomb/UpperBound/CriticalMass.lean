/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Integrals.GaussianMass
import TwoComponentCoulomb.UpperBound.ReducedMatching

/-!+# The common critical Gaussian mass

The cycle mass `J_λ(1/ℓ)` in (eq:critical-fixed-graph), with `ℓ = |log λ|`.
The same mass is used for isolated pairs and for the other cycles.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-- The common Gaussian mass `J_λ(1/ℓ)`. -/
noncomputable def criticalCycleMass (lam : ℝ) : ℝ :=
  ∫ u : ℂ, Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|)

/-- The tail `J_λ(1/ℓ; R)` carried by pairs longer than `R`. -/
noncomputable def criticalTailMass (lam R : ℝ) : ℝ :=
  ∫ u : ℂ, if R < ‖u‖ then
    Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|) else 0

/-- A tail of the Gaussian mass is nonnegative. -/
theorem criticalTailMass_nonneg (lam R : ℝ) : 0 ≤ criticalTailMass lam R := by
  apply integral_nonneg
  intro u
  dsimp only
  split_ifs <;> positivity

/-- The Gaussian mass as a nonnegative integral. -/
theorem ofReal_criticalCycleMass {lam : ℝ} (hlam : 0 < lam)
    (hle : lam ≤ Real.exp (-1)) :
    ENNReal.ofReal (criticalCycleMass lam) =
      ∫⁻ u : ℂ, ENNReal.ofReal
        (Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|)) :=
  ofReal_integral_eq_lintegral_ofReal (integrable_gaussianMass hlam hle)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)

/-- The common cycle mass is positive in the critical regime. -/
theorem criticalCycleMass_pos {lam : ℝ} (hlam : 0 < lam)
    (hle : lam ≤ Real.exp (-1)) : 0 < criticalCycleMass lam := by
  obtain ⟨hℓ, h2⟩ := two_mul_le_sqrt_neg_log hlam hle
  have hab : |Real.log lam| = -Real.log lam := abs_of_neg (by linarith)
  apply integral_gaussianMass_pos hlam
  · rw [hab]
    linarith
  · simpa only [hab] using h2

/-- The upper half of the critical Gaussian mass asymptotic. -/
theorem exists_criticalCycleMass_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      criticalCycleMass lam ≤
        2 * Real.pi * (|Real.log lam| + (1 / 2) * Real.log |Real.log lam|) + C := by
  obtain ⟨C, hC⟩ := exists_abs_gaussianMass_sub_le
  refine ⟨C, (abs_nonneg _).trans
    (hC (Real.exp (-1)) (Real.exp_pos _) le_rfl), fun lam hlam hle => ?_⟩
  have h := (abs_le.1 (hC lam hlam hle)).2
  unfold criticalCycleMass
  linarith only [h]

end TwoComponentCoulomb

end
