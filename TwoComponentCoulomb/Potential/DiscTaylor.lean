/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Potential.DiscField
public import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The averaged Taylor argument for the unit-disc potential

The proof of (idg1), source `source/dipole-formation.tex`, l. 414–419, uses the
`1`-Lipschitz gradient of `ψ = discPotential 1`. Its average on the unit disc vanishes.
The first-order remainder is bounded by `|w|² / 2`, by integration along the segment
from `x` to `x + w`. Averaging gives the same bound for `g₁(w) - κ`.
-/

public section

open MeasureTheory InnerProductSpace

namespace TwoComponentCoulomb

/-- The average of the gradient of the unit-disc potential is zero (source (idg1)). -/
theorem integral_discField_one : ∫ x, discField 1 x ∂smearedCharge 0 1 = 0 := by
  have h := (measurableEmbedding_neg (α := ℂ)).integral_map
    (μ := smearedCharge 0 1) (discField 1)
  rw [map_neg_smearedCharge, neg_zero] at h
  have he : ∀ x : ℂ, discField 1 (-x) = -discField 1 x := by
    intro x
    simp only [discField, norm_neg, smul_neg]
  simp_rw [he] at h
  rw [integral_neg] at h
  exact (smul_eq_zero.mp (show (2 : ℝ) • (∫ x, discField 1 x ∂smearedCharge 0 1) = 0 by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h)).resolve_left (by norm_num)

/-- Taylor's estimate for `ψ`, with the coefficient supplied by its `1`-Lipschitz gradient. -/
theorem abs_discPotential_one_taylor_le (x w : ℂ) :
    |discPotential 1 (x + w) - discPotential 1 x - inner ℝ (discField 1 x) w| ≤
      ‖w‖ ^ 2 / 2 := by
  let R : ℝ → ℝ := fun t => discPotential 1 (x + t • w) - discPotential 1 x -
    t * inner ℝ (discField 1 x) w
  let D : ℝ → ℝ := fun t => inner ℝ (discField 1 (x + t • w) - discField 1 x) w
  have hD : Continuous D := by
    exact (((continuous_discField one_pos).comp
      (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const).inner
      continuous_const
  have hder : ∀ t, HasDerivAt R (D t) t := by
    intro t
    have h := (hasFDerivAt_discPotential one_pos (x + t • w)).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const w).const_add x)
    simpa only [R, D, Function.comp_apply, id_eq, Pi.sub_apply, toDual_apply_apply,
      inner_sub_left, one_smul, one_mul, Pi.sub_def] using (h.sub_const (discPotential 1 x)).sub
        ((hasDerivAt_id t).mul_const (inner ℝ (discField 1 x) w))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hder t) (hD.intervalIntegrable 0 1)
  have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖D t‖ ≤ t * ‖w‖ ^ 2 := by
    intro t ht
    have hL := lipschitzWith_discField_one.norm_sub_le (x + t • w) x
    simp only [NNReal.coe_one, one_mul, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg ht.1.le] at hL
    change ‖inner ℝ (discField 1 (x + t • w) - discField 1 x) w‖ ≤ _
    calc _ ≤ ‖discField 1 (x + t • w) - discField 1 x‖ * ‖w‖ := norm_inner_le_norm _ _
      _ ≤ (t * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg w)
      _ = t * ‖w‖ ^ 2 := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := D) (g := fun t => t * ‖w‖ ^ 2) zero_le_one
    (Filter.Eventually.of_forall hbound)
    ((show Continuous (fun t : ℝ => t * ‖w‖ ^ 2) from
      continuous_id.mul continuous_const).intervalIntegrable 0 1)
  rw [hFTC] at hnorm
  simpa [R, intervalIntegral.integral_mul_const,
    Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using hnorm

/-- The averaged first-order Taylor identity of (idg1). -/
theorem smearedKernel_one_sub_kappa_eq_integral_taylor (w : ℂ) :
    smearedKernel 1 w - kappa = ∫ x,
      (discPotential 1 (x + w) - discPotential 1 x - inner ℝ (discField 1 x) w)
        ∂smearedCharge 0 1 := by
  have hc := (contDiff_discPotential one_pos).continuous
  have hI : Integrable (discField 1) (smearedCharge 0 1) := by
    rw [smearedCharge_eq]
    exact ((continuous_discField one_pos).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall |>.smul_measure
        (ENNReal.inv_ne_top.2 (Metric.measure_ball_pos volume 0 one_pos).ne')
  have hmean : ∫ x, inner ℝ (discField 1 x) w ∂smearedCharge 0 1 = 0 := by
    have h := (toDual ℝ ℂ w).integral_comp_comm hI
    rw [integral_discField_one] at h
    simpa only [toDual_apply_apply, real_inner_comm, inner_zero_left, inner_zero_right] using h
  have hshift : ∫ x, discPotential 1 (x + w) ∂smearedCharge 0 1 = smearedKernel 1 w := by
    rw [← integral_comp_neg_smearedCharge (fun x => discPotential 1 (x + w)) 1]
    have he : ∀ x : ℂ, discPotential 1 (-x + w) = discPotential 1 (x - w) := by
      intro x
      have : -x + w = -(x - w) := by ring
      simp only [this, discPotential, norm_neg]
    simp_rw [he]
    exact (smearedKernel_eq_integral_potential one_pos w).symm
  have hA : Integrable (fun x => discPotential 1 (x + w)) (smearedCharge 0 1) :=
    integrable_smearedCharge_of_continuous (hc.comp (continuous_id.add continuous_const)) 0 1
  have hB : Integrable (discPotential 1) (smearedCharge 0 1) :=
    integrable_smearedCharge_of_continuous hc 0 1
  have hC : Integrable (fun x => inner ℝ (discField 1 x) w) (smearedCharge 0 1) :=
    integrable_smearedCharge_of_continuous
      ((continuous_discField one_pos).inner continuous_const) 0 1
  rw [integral_sub (f := fun x => discPotential 1 (x + w) - discPotential 1 x)
    (g := fun x => inner ℝ (discField 1 x) w) (hA.sub hB) hC,
    integral_sub (f := fun x => discPotential 1 (x + w)) (g := discPotential 1) hA hB,
    hshift, hmean, sub_zero]
  change smearedKernel 1 w - kappa = smearedKernel 1 w - _
  congr 1
  have hk : kappa = smearedKernel 1 0 := rfl
  rw [hk]
  simpa only [sub_zero, discPotential] using smearedKernel_eq_integral_potential one_pos 0

/-- The sharp quadratic bound in (idg1), obtained by averaging Taylor's estimate. -/
theorem abs_smearedKernel_one_sub_kappa_le_half (w : ℂ) :
    |smearedKernel 1 w - kappa| ≤ ‖w‖ ^ 2 / 2 := by
  have := isProbabilityMeasure_smearedCharge 0 one_pos
  rw [smearedKernel_one_sub_kappa_eq_integral_taylor, ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le (μ := smearedCharge 0 1)
    (f := fun x => discPotential 1 (x + w) - discPotential 1 x - inner ℝ (discField 1 x) w)
    (integrable_const (‖w‖ ^ 2 / 2))
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using abs_discPotential_one_taylor_le x w)
  simpa using h

end TwoComponentCoulomb

end
