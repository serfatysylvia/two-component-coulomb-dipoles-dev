/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TwoComponentCoulomb.Frozen.Kappa
public import TwoComponentCoulomb.Frozen.LogKernel
public import TwoComponentCoulomb.Frozen.SmearedCharge
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.Potential.DiscPotential
public import TwoComponentCoulomb.Potential.PairIntegral
public import TwoComponentCoulomb.Potential.SmearedCharge

/-!
# The potential of a uniform disc, as an integral against `smearedCharge`

Newton's theorem (`setIntegral_log_norm_sub_ball_of_le` and `setIntegral_log_norm_sub_ball_of_ge`)
rephrased for the probability measure `δ_z^{(a)} = smearedCharge z a` and the kernel
`g = logKernel` (source l. 128–152, 499–518).

* `integral_logKernel_sub_smearedCharge_of_le` : outside the disc (`a ≤ |x - z|`) the potential is
  `g(x - z)`.
* `integral_logKernel_sub_smearedCharge_of_ge` : inside the disc (`|x - z| ≤ a`) it is
  `-log a + (1 - |x - z|² / a²) / 2`.
* `integral_logKernel_sub_smearedCharge` : both cases in a single closed form, and
  `continuous_closedFormDiscPotential` : this closed form is a continuous function of `x - z`.
* `integrable_logKernel_prod_smearedCharge` : `g(x - y)` is integrable for the product of two
  uniform disc measures.
* `smearedKernel_eq_integral_integral` : `g_λ(z)` as an iterated integral (Fubini), and
  `smearedKernel_eq_integral_potential` : its form with the closed-form disc potential inserted.

The file also records the measure-theoretic facts about `smearedCharge` used for these purposes:
it is concentrated on the disc (`ae_mem_ball_smearedCharge`), has no atoms
(`smearedCharge_singleton`), integrates continuous functions
(`integrable_smearedCharge_of_continuous`), and is invariant under `x ↦ -x` for discs centred at
`0` (`integral_comp_neg_smearedCharge`).
-/

public section

open MeasureTheory

namespace TwoComponentCoulomb

/-! ### Elementary facts on `logKernel` at positive real arguments -/

theorem logKernel_ofReal {t : ℝ} (ht : 0 < t) : logKernel (t : ℂ) = -Real.log t := by
  simp [logKernel, abs_of_pos ht]

theorem logKernel_ofReal_mul {t : ℝ} (ht : 0 < t) {u : ℂ} (hu : u ≠ 0) :
    logKernel ((t : ℂ) * u) = logKernel (t : ℂ) + logKernel u := by
  have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  simp only [logKernel, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
  rw [Real.log_mul ht.ne' hu']
  ring

/-! ### Basic measure-theoretic facts on `smearedCharge` -/

/-- Almost every point for `δ_z^{(a)}` lies in the disc `B(z, a)`. -/
theorem ae_mem_ball_smearedCharge (z : ℂ) (a : ℝ) :
    ∀ᵐ x ∂smearedCharge z a, x ∈ Metric.ball z a :=
  ProbabilityTheory.ae_cond_mem Metric.isOpen_ball.measurableSet

/-- `δ_z^{(a)}` has no atoms. -/
theorem smearedCharge_singleton (z x : ℂ) (a : ℝ) : smearedCharge z a {x} = 0 :=
  ProbabilityTheory.cond_absolutelyContinuous (measure_singleton x)

/-- The diagonal is a null set for the product of two uniform disc measures. -/
theorem ae_prod_smearedCharge_ne (z w : ℂ) (a b : ℝ) :
    ∀ᵐ p ∂(smearedCharge z a).prod (smearedCharge w b), p.1 ≠ p.2 := by
  have hm : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} := isClosed_diagonal.measurableSet
  rw [ae_iff]
  have : {p : ℂ × ℂ | ¬p.1 ≠ p.2} = {p : ℂ × ℂ | p.1 = p.2} := by simp
  rw [this, Measure.measure_prod_null hm]
  refine Filter.Eventually.of_forall fun x => ?_
  have : Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 = p.2} = {x} := by
    ext y; simp [eq_comm]
  simp [this, smearedCharge_singleton]

/-- Continuous functions are integrable for `δ_z^{(a)}`. -/
theorem integrable_smearedCharge_of_continuous {f : ℂ → ℝ} (hf : Continuous f) (z : ℂ) (a : ℝ) :
    Integrable f (smearedCharge z a) := by
  rcases le_or_gt a 0 with ha | ha
  · rw [smearedCharge_of_nonpos z ha]
    exact integrable_zero_measure
  have h : IntegrableOn f (Metric.ball z a) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall z a)).mono_set
      Metric.ball_subset_closedBall
  rw [smearedCharge_eq]
  exact h.smul_measure (ENNReal.inv_ne_top.2 (Metric.measure_ball_pos volume z ha).ne')

/-- `δ_0^{(a)}` is invariant under the antipodal map. -/
theorem integral_comp_neg_smearedCharge (f : ℂ → ℝ) (a : ℝ) :
    ∫ x, f (-x) ∂smearedCharge 0 a = ∫ x, f x ∂smearedCharge 0 a := by
  have h := (measurableEmbedding_neg (α := ℂ)).integral_map (μ := smearedCharge 0 a) f
  rw [map_neg_smearedCharge, neg_zero] at h
  exact h.symm

/-! ### The potential of a uniform disc -/

/-- **Newton's theorem for `δ_z^{(a)}`, exterior case**: for `a ≤ |x - z|` the potential of the
uniform disc is the potential `g(x - z)` of its centre. -/
theorem integral_logKernel_sub_smearedCharge_of_le (x z : ℂ) {a : ℝ} (ha : 0 < a)
    (h : a ≤ ‖x - z‖) :
    ∫ y, logKernel (x - y) ∂smearedCharge z a = logKernel (x - z) := by
  rw [integral_smearedCharge _ z ha]
  simp only [logKernel, integral_neg, smul_eq_mul]
  rw [setIntegral_log_norm_sub_ball_of_le x z ha h]
  field_simp

/-- **Newton's theorem for `δ_z^{(a)}`, interior case**: for `|x - z| ≤ a` the potential of the
uniform disc is `-log a + (1 - |x - z|² / a²) / 2`. -/
theorem integral_logKernel_sub_smearedCharge_of_ge (x z : ℂ) {a : ℝ} (ha : 0 < a)
    (h : ‖x - z‖ ≤ a) :
    ∫ y, logKernel (x - y) ∂smearedCharge z a =
      -Real.log a + (1 - ‖x - z‖ ^ 2 / a ^ 2) / 2 := by
  rw [integral_smearedCharge _ z ha]
  simp only [logKernel, integral_neg, smul_eq_mul]
  rw [setIntegral_log_norm_sub_ball_of_ge x z ha h]
  field_simp
  ring

/-- **Newton's theorem for `δ_z^{(a)}`** in a single closed form:
`∫ g(x - y) dδ_z^{(a)}(y) = -log (max a |x - z|) + (1 - min(|x - z|, a)² / a²) / 2`. -/
theorem integral_logKernel_sub_smearedCharge (x z : ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ y, logKernel (x - y) ∂smearedCharge z a =
      -Real.log (max a ‖x - z‖) + (1 - min ‖x - z‖ a ^ 2 / a ^ 2) / 2 := by
  rcases le_total a ‖x - z‖ with h | h
  · rw [integral_logKernel_sub_smearedCharge_of_le x z ha h, max_eq_right h, min_eq_right h]
    simp [logKernel, ha.ne']
  · rw [integral_logKernel_sub_smearedCharge_of_ge x z ha h, max_eq_left h, min_eq_left h]

/-- The closed form of the potential of the disc of radius `a > 0` is continuous in `u = x - z`. -/
theorem continuous_closedFormDiscPotential {a : ℝ} (ha : 0 < a) :
    Continuous fun u : ℂ => -Real.log (max a ‖u‖) + (1 - min ‖u‖ a ^ 2 / a ^ 2) / 2 := by
  have h1 : Continuous fun u : ℂ => Real.log (max a ‖u‖) :=
    Continuous.log (continuous_const.max continuous_norm)
      fun u => (lt_of_lt_of_le ha (le_max_left _ _)).ne'
  have h2 : Continuous fun u : ℂ => min ‖u‖ a := continuous_norm.min continuous_const
  fun_prop

/-! ### Integrability and the iterated form of `smearedKernel` -/

/-- The kernel `g(x - y)` is integrable for the product of two uniform disc measures. -/
theorem integrable_logKernel_prod_smearedCharge (z w : ℂ) (a b : ℝ) :
    Integrable (fun p : ℂ × ℂ => logKernel (p.1 - p.2))
      ((smearedCharge z a).prod (smearedCharge w b)) := by
  rcases le_or_gt a 0 with ha | ha
  · rw [smearedCharge_of_nonpos z ha, Measure.zero_prod]
    exact integrable_zero_measure
  rcases le_or_gt b 0 with hb | hb
  · rw [smearedCharge_of_nonpos w hb, Measure.prod_zero]
    exact integrable_zero_measure
  have h : Integrable (fun p : ℂ × ℂ => logKernel (p.1 - p.2))
      ((volume.restrict (Metric.ball z a)).prod (volume.restrict (Metric.ball w b))) :=
    (integrable_log_norm_sub_prod_ball z w a b).neg
  have hz : (volume (Metric.ball z a))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (Metric.measure_ball_pos volume z ha).ne'
  have hw : (volume (Metric.ball w b))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (Metric.measure_ball_pos volume w hb).ne'
  rw [smearedCharge_eq, smearedCharge_eq, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul]
  exact h.smul_measure (ENNReal.mul_ne_top hz hw)

/-- `g_λ(z)` as an iterated integral: first the potential of the disc `B(z, λ)` at `x`, then the
average over `x ∈ B(0, λ)` (Fubini). -/
theorem smearedKernel_eq_integral_integral (lam : ℝ) (z : ℂ) :
    smearedKernel lam z =
      ∫ x, (∫ y, logKernel (x - y) ∂smearedCharge z lam) ∂smearedCharge 0 lam :=
  integral_prod _ (integrable_logKernel_prod_smearedCharge 0 z lam lam)

/-- The iterated form of `g_λ(z)` with Newton's closed form for the potential of the disc inserted:
`g_λ(z) = ∫ (-log (max λ |x - z|) + (1 - min(|x - z|, λ)² / λ²) / 2) dδ_0^{(λ)}(x)`. -/
theorem smearedKernel_eq_integral_potential {lam : ℝ} (hlam : 0 < lam) (z : ℂ) :
    smearedKernel lam z =
      ∫ x, (-Real.log (max lam ‖x - z‖) + (1 - min ‖x - z‖ lam ^ 2 / lam ^ 2) / 2)
        ∂smearedCharge 0 lam := by
  rw [smearedKernel_eq_integral_integral]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    integral_logKernel_sub_smearedCharge x z hlam)

end TwoComponentCoulomb

end
