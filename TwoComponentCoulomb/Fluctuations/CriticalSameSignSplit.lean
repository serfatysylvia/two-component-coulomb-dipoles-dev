/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.SourcePairRadial
public import TwoComponentCoulomb.UpperBound.CriticalRadial
import TwoComponentCoulomb.Gibbs.Measurability
import TwoComponentCoulomb.Integrals.GaussianMass
import TwoComponentCoulomb.Integrals.LogFacts

/-!
# The critical same-sign radial integral in Theorem 2

Source `source/dipole-formation.tex`, proof of Theorem 2, Step 2,
(eq:critical electric). The paper separates `(a/ρ)^4` and
`min (a/θ) 1 ^ 4`. Each core is bounded by the critical correction integral.
The cutoff contribution outside `4θ` is bounded by the Gaussian tail.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-- **The critical same-sign integral as written in Step 2**: split the `ρ` correction
from the cutoff correction, then use the core estimate and the Gaussian tail. -/
theorem exists_lintegral_critical_sameSign_split_le :
    ∃ C : ℝ, 0 < C ∧ ∀ lam γ ρ : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      2 * lam ≤ γ → γ ≤ 1 → lam ≤ ρ →
      ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal
        (Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|) *
          (displacementScale lam u / max (min ρ γ) (displacementScale lam u)) ^ 4) ≤
        ENNReal.ofReal (C * (1 + Real.log |Real.log lam| + Real.log (1 / γ))) := by
  obtain ⟨C, hC, hcore⟩ := lintegral_sameSignPair_le (β := 2) le_rfl
  refine ⟨2 * C + 2 * Real.pi, by positivity, ?_⟩
  intro lam γ ρ hlam hle hγ hγ1 hρ
  have hγ0 : 0 < γ := by linarith
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  have hℓ1 := one_le_abs_log hlam hle
  have hℓ0 : 0 < |Real.log lam| := by linarith
  let X : ℂ → ℝ := fun u => Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|)
  let R : ℂ → ℝ≥0∞ := fun u => ENNReal.ofReal
    (X u * (displacementScale lam u / ρ) ^ 4)
  let G : ℂ → ℝ≥0∞ := fun u => ENNReal.ofReal
    (X u * min (displacementScale lam u / γ) 1 ^ 4)
  have hg : Measurable (smearedKernel lam) := measurable_smearedKernel lam
  have hd : Measurable (displacementScale lam) := (continuous_displacementScale lam).measurable
  have hRm : Measurable R := by dsimp [R, X]; fun_prop
  have hX : ∀ u, X u ≤ Real.exp (2 * smearedKernel lam u) := by
    intro u
    exact Real.exp_le_exp.2 (sub_le_self _ (by positivity))
  have hR : ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), R u ≤ ENNReal.ofReal C := by
    refine (lintegral_mono fun u => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hX u) (by positivity))).trans ?_
    simpa only [show (2 * (2 : ℝ)) = 4 by norm_num, Real.rpow_ofNat,
      sub_self, Real.rpow_zero, mul_one] using hcore lam ρ hlam hρ
  have hGcore : ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * γ), G u ≤ ENNReal.ofReal C := by
    have hpt : ∀ u ∈ Metric.closedBall (0 : ℂ) (4 * γ), G u ≤ ENNReal.ofReal
        (Real.exp (2 * smearedKernel lam u) * (displacementScale lam u / γ) ^ 4) := by
      intro u hu
      have ha := displacementScale_le_of_norm_le (show lam ≤ γ by linarith)
        (show ‖u‖ ≤ 4 * γ by simpa using hu)
      dsimp only [G]
      rw [min_eq_left ((div_le_one hγ0).2 ha)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hX u) (by positivity))
    refine (setLIntegral_mono' Metric.isClosed_closedBall.measurableSet hpt).trans ?_
    simpa only [show (2 * (2 : ℝ)) = 4 by norm_num, Real.rpow_ofNat,
      sub_self, Real.rpow_zero, mul_one] using hcore lam γ hlam (show lam ≤ γ by linarith)
  let T : ℂ → ℝ := fun u => if γ < ‖u‖ then X u else 0
  have hTnn : ∀ u, 0 ≤ T u := by intro u; dsimp [T, X]; split_ifs <;> positivity
  have hT : ∫⁻ u, ENNReal.ofReal (T u) ≤ ENNReal.ofReal
      (2 * Real.pi * ((1 / 2) * Real.log |Real.log lam| + Real.log (1 / γ) + 1 / 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_tail_gaussianMass hlam hle)
      (ae_of_all _ hTnn)]
    exact ENNReal.ofReal_le_ofReal (integral_tail_gaussianMass_le hlam hle hγ hγ1)
  have hGtail : ∫⁻ u in (Metric.closedBall (0 : ℂ) (4 * γ))ᶜ, G u ≤
      ∫⁻ u, ENNReal.ofReal (T u) := by
    refine (setLIntegral_mono' Metric.isClosed_closedBall.measurableSet.compl fun u hu => ?_).trans
      (setLIntegral_le_lintegral _ _)
    have hu' : 4 * γ < ‖u‖ := by simpa using hu
    have ha0 := displacementScale_pos hlam u
    dsimp only [G, T]
    rw [ite_eq_left (by linarith : γ < ‖u‖)]
    exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (Real.exp_pos _).le
      (pow_le_one₀ (by positivity) (min_le_right _ _)))
  have hG : ∫⁻ u, G u ≤ ENNReal.ofReal C + ENNReal.ofReal
      (2 * Real.pi * ((1 / 2) * Real.log |Real.log lam| + Real.log (1 / γ) + 1 / 2)) := by
    rw [← lintegral_add_compl _ Metric.isClosed_closedBall.measurableSet]
    exact add_le_add hGcore (hGtail.trans hT)
  have hsplit : ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal
        (X u * (displacementScale lam u / max (min ρ γ) (displacementScale lam u)) ^ 4) ≤
      (∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), R u) + ∫⁻ u, G u := by
    calc _ ≤ ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), R u + G u := by
          refine lintegral_mono fun u => ?_
          have ha0 := displacementScale_pos hlam u
          dsimp only [R, G]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          have hp := SourcePairRadial.cutoff_rpow_le ha0 hρ0 hγ0 (by norm_num : (0 : ℝ) ≤ 4)
          simp only [Real.rpow_ofNat] at hp
          exact ENNReal.ofReal_le_ofReal (by
            simpa only [mul_add] using mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le)
      _ ≤ _ := by
          rw [lintegral_add_left hRm]
          exact add_le_add le_rfl (setLIntegral_le_lintegral _ _)
  have hlogℓ : 0 ≤ Real.log |Real.log lam| := Real.log_nonneg hℓ1
  have hlogγ : 0 ≤ Real.log (1 / γ) := Real.log_nonneg ((one_le_div hγ0).2 hγ1)
  refine (hsplit.trans (add_le_add hR hG)).trans ?_
  rw [← ENNReal.ofReal_add hC.le (by positivity),
    ← ENNReal.ofReal_add hC.le (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_nonneg hC.le hlogℓ, mul_nonneg hC.le hlogγ,
    mul_nonneg Real.pi_pos.le hlogℓ, Real.pi_pos]

end TwoComponentCoulomb

end
