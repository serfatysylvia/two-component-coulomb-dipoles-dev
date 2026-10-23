/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Integrals.GaussianMass
import TwoComponentCoulomb.Integrals.Radial

/-!
# The two-sided critical Gaussian tail expansion

Source `source/dipole-formation.tex`, `eq:critical-BR`. Outside the core the
kernel is logarithmic. In polar coordinates, split the radial integral at `√ℓ`.
The middle interval differs from the logarithmic integral by at most `1/2`, and the
remaining tail lies between zero and `1/2`.
-/

public section

open MeasureTheory Set

namespace TwoComponentCoulomb

/-- The critical tail is `2π (log (1/R) + ½ log ℓ) + O(1)`, uniformly for
`0 < λ ≤ e⁻¹`, `ℓ = |log λ|` and `2λ ≤ R ≤ 1`. -/
private theorem abs_integral_tail_gaussianMass_sub_le_open {lam R : ℝ} (hlam : 0 < lam)
    (hle : lam ≤ Real.exp (-1)) (hR : 2 * lam ≤ R) (hR1 : R ≤ 1) :
    |(∫ u : ℂ, (if R < ‖u‖ then
        Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|) else 0)) -
      2 * Real.pi * (Real.log (1 / R) + 1 / 2 * Real.log |Real.log lam|)| ≤ Real.pi := by
  obtain ⟨h1, -⟩ := two_mul_le_sqrt_neg_log hlam hle
  have hab : |Real.log lam| = -Real.log lam := abs_of_neg (by linarith)
  set ℓ := -Real.log lam
  have hℓ : 0 < ℓ := by dsimp [ℓ]; linarith
  have hR0 : 0 < R := by linarith
  have hRs : R ≤ Real.sqrt ℓ := hR1.trans (Real.one_le_sqrt.2 h1)
  have hf : ∀ u : ℂ, (if R < ‖u‖ then
      Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|) else 0) =
      (Ioi R).indicator (gaussianProfile lam ℓ) ‖u‖ := by
    intro u
    rw [hab, gaussianProfile_eq_comp_norm]
    by_cases hu : R < ‖u‖
    · rw [ite_eq_left hu, indicator_of_mem (mem_Ioi.2 hu)]
    · rw [ite_eq_right hu, indicator_of_notMem (by simpa using hu)]
  simp_rw [hf]
  rw [integral_comp_norm_complex]
  have h2 : ∀ y : ℝ, y * (Ioi R).indicator (gaussianProfile lam ℓ) y =
      (Ioi R).indicator (fun y => y * gaussianProfile lam ℓ y) y := by
    intro y
    by_cases hy : y ∈ Ioi R
    · rw [indicator_of_mem hy, indicator_of_mem hy]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
  simp_rw [h2]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hR0.le,
    setIntegral_congr_fun measurableSet_Ioi
      (fun y hy => mul_gaussianProfile_of_le hlam (hR.trans (mem_Ioi.1 hy).le)),
    ← Ioc_union_Ioi_eq_Ioi hRs,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_exp_neg_sq_div_Ioc ℓ hR0) (integrableOn_exp_neg_sq_div_Ioi hℓ)]
  have hlo := le_integral_exp_neg_sq_div_Ioc hℓ hR0 hRs
  have hhi := integral_exp_neg_sq_div_Ioc_le hℓ hR0 hRs
  have ht0 := integral_exp_neg_sq_div_Ioi_nonneg hℓ
  have ht1 := integral_exp_neg_sq_div_Ioi_le hℓ
  rw [Real.log_sqrt hℓ.le] at hlo hhi
  rw [one_div R, Real.log_inv, hab, abs_le]
  constructor <;>
    nlinarith only [hlo, hhi, ht0, ht1, Real.pi_pos]

/-- The manuscript's two-sided expansion for `J_λ(1/ℓ;R)`, with the closed
radial tail `|u| ≥ R` and a universal absolute error `π`. -/
theorem abs_integral_tail_gaussianMass_sub_le {lam R : ℝ} (hlam : 0 < lam)
    (hle : lam ≤ Real.exp (-1)) (hR : 2 * lam ≤ R) (hR1 : R ≤ 1) :
    |(∫ u : ℂ in {u | R ≤ ‖u‖},
        Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|)) -
      2 * Real.pi * (Real.log (1 / R) + 1 / 2 * Real.log |Real.log lam|)| ≤ Real.pi := by
  have heq : (∫ u : ℂ in {u | R ≤ ‖u‖},
      Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|)) =
      ∫ u : ℂ, (if R < ‖u‖ then
        Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|) else 0) := by
    rw [← integral_indicator (measurableSet_le measurable_const measurable_norm)]
    apply integral_congr_ae
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume (0 : ℂ) R)] with u hu
    have hne : ‖u‖ ≠ R := by simpa using hu
    by_cases h : R < ‖u‖
    · rw [indicator_of_mem (show u ∈ {u : ℂ | R ≤ ‖u‖} from h.le), ite_eq_left h]
    · have hnot : ¬R ≤ ‖u‖ := fun hle => h (lt_of_le_of_ne hle hne.symm)
      rw [indicator_of_notMem (show u ∉ {u : ℂ | R ≤ ‖u‖} from hnot), ite_eq_right h]
  rw [heq]
  exact abs_integral_tail_gaussianMass_sub_le_open hlam hle hR hR1

end TwoComponentCoulomb

end
