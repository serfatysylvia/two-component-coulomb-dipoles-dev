/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Newton's theorem for the uniform disc

The logarithmic potential of a uniform disc is explicit (source l. 128–152, 499–518): for `a > 0`
and `u = x - z`,

* `∫_{B(z,a)} log |x - y| dy = π a² log |x - z|` if `a ≤ |x - z|`
  (`setIntegral_log_norm_sub_ball_of_le`),
* `∫_{B(z,a)} log |x - y| dy = π a² (log a - (1 - |x - z|² / a²) / 2)` if `|x - z| ≤ a`
  (`setIntegral_log_norm_sub_ball_of_ge`).

The proof goes through polar coordinates (`Complex.polarCoord`): the integral over a disc of
radius `a` about `0` is `∫₀^a r (∫_{-π}^{π} F(r e^{iθ}) dθ) dr`
(`setIntegral_ball_zero_eq_polar`), and the inner integral for `F(w) = log |u - w|` is `2π`
times the circle average `log r + log⁺ (|u| / r) = log (max r |u|)` of Mathlib
(`integral_Ioo_log_norm_sub_circleMap`). The remaining radial integral is elementary
(`radial_integral_of_le`, `radial_integral_of_ge`).

We also prove that the logarithmic kernel is integrable on discs
(`integrableOn_log_norm_sub_ball`), integrable on products of discs
(`integrable_log_norm_sub_prod_ball`), and that its `L¹` norm on a disc is bounded uniformly in
the pole `x` ranging over a bounded set (`setIntegral_abs_log_norm_sub_ball_le`).
-/

public section

open MeasureTheory Metric Set

namespace TwoComponentCoulomb

/-! ### Local integrability of `log ‖·‖` -/

/-- The function `log ‖·‖` is integrable on every disc centred at `0` in `ℂ`. -/
theorem integrableOn_log_norm_ball_zero (R : ℝ) :
    IntegrableOn (fun x : ℂ => Real.log ‖x‖) (ball (0 : ℂ) R) := by
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := Real.log) (r := R),
    Complex.finrank_real_complex]
  have : Continuous fun y : ℝ => y ^ (2 - 1) • Real.log y := by
    simpa using Real.continuous_mul_log
  exact (this.integrableOn_Icc (a := 0) (b := R)).mono_set Ioo_subset_Icc_self

/-- The logarithmic kernel `y ↦ log ‖x - y‖` is integrable on every disc of `ℂ`, wherever the
pole `x` lies. -/
theorem integrableOn_log_norm_sub_ball (x z : ℂ) (a : ℝ) :
    IntegrableOn (fun y : ℂ => Real.log ‖x - y‖) (Metric.ball z a) := by
  rcases le_or_gt a 0 with ha | ha
  · rw [Metric.ball_eq_empty.2 ha]; exact integrableOn_empty
  set ρ : ℝ := ‖x - z‖ + a with hρ
  have h0 : Integrable (indicator (ball (0 : ℂ) ρ) fun w : ℂ => Real.log ‖w‖) := by
    rw [integrable_indicator_iff measurableSet_ball]
    exact integrableOn_log_norm_ball_zero ρ
  have h1 := h0.comp_sub_right x
  have h2 : IntegrableOn (fun y : ℂ => Real.log ‖x - y‖) (ball x ρ) := by
    rw [← integrable_indicator_iff measurableSet_ball]
    refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ ball x ρ
    · have : y - x ∈ ball (0 : ℂ) ρ := by
        rw [mem_ball_zero_iff]; exact mem_ball_iff_norm.1 hy
      simp [indicator, hy, this, norm_sub_rev]
    · have : y - x ∉ ball (0 : ℂ) ρ := by
        rw [mem_ball_zero_iff]; exact fun h => hy (mem_ball_iff_norm.2 h)
      simp [indicator, hy, this]
  refine h2.mono_set fun y hy => ?_
  rw [mem_ball_iff_norm] at hy ⊢
  calc ‖y - x‖ = ‖(y - z) + (z - x)‖ := by congr 1; ring
    _ ≤ ‖y - z‖ + ‖z - x‖ := norm_add_le _ _
    _ < a + ‖x - z‖ := by rw [norm_sub_rev z x]; linarith
    _ = ρ := by rw [hρ]; ring

/-! ### Polar coordinates on a disc -/

/-- Integrability of `G` on `ℂ` transfers to integrability of the polar-coordinate integrand
`r • G (r e^{iθ})` on the polar target `(0, ∞) × (-π, π)`. -/
theorem integrableOn_polarCoord_target {G : ℂ → ℝ} (hGm : Measurable G) (hG : Integrable G) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • G (Complex.polarCoord.symm p))
      Complex.polarCoord.target := by
  have hmeas : Measurable fun p : ℝ × ℝ => p.1 • G (Complex.polarCoord.symm p) := by
    have : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
        fun p => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p; exact Complex.polarCoord_symm_apply p
    have hc : Measurable fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
      rw [this]
      exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I)).measurable
    exact measurable_fst.smul (hGm.comp hc)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h1 : ∫⁻ p in Complex.polarCoord.target, ‖p.1 • G (Complex.polarCoord.symm p)‖ₑ =
      ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • (fun w : ℂ => ‖G w‖ₑ) (Complex.polarCoord.symm p) := by
    refine setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    simp [Real.enorm_eq_ofReal hp1.le]
  rw [h1]
  exact (Complex.lintegral_comp_polarCoord_symm (fun w : ℂ => ‖G w‖ₑ)).trans_lt hG.2

/-- The inverse polar coordinate map is the parametrization of circles about `0`. -/
theorem polarCoord_symm_eq_circleMap (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
  rw [Complex.polarCoord_symm_apply]
  simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Integration over a disc in polar coordinates:
`∫_{B(0,a)} F = ∫₀^a r (∫_{-π}^{π} F(r e^{iθ}) dθ) dr`, for `F` measurable and integrable on the
disc. -/
theorem setIntegral_ball_zero_eq_polar {F : ℂ → ℝ} (hF : Measurable F) {a : ℝ}
    (hint : IntegrableOn F (ball (0 : ℂ) a)) :
    ∫ w in ball (0 : ℂ) a, F w =
      ∫ r in Ioo 0 a, r * ∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ) := by
  have hG : Integrable (indicator (ball (0 : ℂ) a) F) :=
    (integrable_indicator_iff measurableSet_ball).2 hint
  have hGm : Measurable (indicator (ball (0 : ℂ) a) F) := hF.indicator measurableSet_ball
  have h1 := Complex.integral_comp_polarCoord_symm (indicator (ball (0 : ℂ) a) F)
  have h2 := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun p : ℝ × ℝ => p.1 • indicator (ball (0 : ℂ) a) F (Complex.polarCoord.symm p))
    (s := Ioi 0) (t := Ioo (-Real.pi) Real.pi) (integrableOn_polarCoord_target hGm hG)
  rw [integral_indicator measurableSet_ball] at h1
  rw [← h1]
  have h3 : ∫ p in polarCoord.target, p.1 • indicator (ball (0 : ℂ) a) F
      (Complex.polarCoord.symm p) = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        r • indicator (ball (0 : ℂ) a) F (Complex.polarCoord.symm (r, θ)) := h2
  rw [h3]
  have h4 : ∀ r ∈ Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        r • indicator (ball (0 : ℂ) a) F (Complex.polarCoord.symm (r, θ)) =
      indicator (Iio a) (fun r => r * ∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ)) r := by
    intro r hr
    have hr0 : 0 < r := hr
    simp_rw [polarCoord_symm_eq_circleMap]
    by_cases hra : r < a
    · have : ∀ θ, circleMap 0 r θ ∈ ball (0 : ℂ) a := by
        intro θ
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr0]; exact hra
      simp [indicator, hra, this, integral_const_mul]
    · have : ∀ θ, circleMap 0 r θ ∉ ball (0 : ℂ) a := by
        intro θ
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr0]; exact hra
      simp [indicator, hra, this]
  rw [setIntegral_congr_fun measurableSet_Ioi h4, setIntegral_indicator measurableSet_Iio,
    Ioi_inter_Iio]

/-! ### The circle average of the logarithmic kernel -/

/-- `log r + log⁺ (|u| / r) = log (max r |u|)` for `r > 0`. -/
theorem log_add_posLog_inv_mul_norm (u : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.log r + Real.posLog (r⁻¹ * ‖u‖) = Real.log (max r ‖u‖) := by
  rcases le_total ‖u‖ r with h | h
  · have h1 : r⁻¹ * ‖u‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ hr]; simpa using h
    rw [(Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (by positivity)]; exact h1),
      max_eq_left h, add_zero]
  · have hu : 0 < ‖u‖ := lt_of_lt_of_le hr h
    have h1 : 1 ≤ r⁻¹ * ‖u‖ := by
      rw [le_inv_mul_iff₀ hr]; simpa using h
    rw [Real.posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; exact h1),
      Real.log_mul (inv_ne_zero hr.ne') hu.ne', Real.log_inv, max_eq_right h]
    ring

/-- The circle integral of the logarithmic kernel: for `r > 0`,
`∫_{-π}^{π} log |u - r e^{iθ}| dθ = 2π log (max r |u|)`. -/
theorem integral_Ioo_log_norm_sub_circleMap (u : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ θ in Ioo (-Real.pi) Real.pi, Real.log ‖u - circleMap 0 r θ‖ =
      2 * Real.pi * Real.log (max r ‖u‖) := by
  have hca := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := u) (c := 0) (R := r)
    hr.ne'
  rw [Real.circleAverage_def, zero_sub, norm_neg, log_add_posLog_inv_mul_norm u hr] at hca
  have hper : Function.Periodic (fun θ => Real.log ‖circleMap 0 r θ - u‖) (2 * Real.pi) :=
    fun θ => by simp [periodic_circleMap 0 r θ]
  have h1 := hper.intervalIntegral_add_eq (-Real.pi) 0
  have h2 : ∫ θ in (-Real.pi)..Real.pi, Real.log ‖u - circleMap 0 r θ‖ =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log ‖circleMap 0 r θ - u‖ := by
    rw [← zero_add (2 * Real.pi), ← h1]
    have : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [this]
    simp_rw [norm_sub_rev u]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), h2]
  rw [smul_eq_mul] at hca
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  field_simp at hca
  linarith

/-! ### The radial integrals -/

theorem integral_Ioo_eq_intervalIntegral {f : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) :
    ∫ r in Ioo 0 a, f r = ∫ r in (0 : ℝ)..a, f r := by
  rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo]

/-- The radial integral when the pole is inside the disc. -/
theorem radial_integral_of_le {s a : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) :
    ∫ r in (0 : ℝ)..a, r * (2 * Real.pi * Real.log (max r s)) =
      Real.pi * a ^ 2 * Real.log a - Real.pi * a ^ 2 / 2 + Real.pi * s ^ 2 / 2 := by
  set h : ℝ → ℝ := fun r => r * (2 * Real.pi * Real.log (max r s)) with hh
  have h1 : EqOn h (fun r => 2 * Real.pi * Real.log s * r) (uIcc 0 s) := by
    intro r hr
    rw [uIcc_of_le hs] at hr
    simp only [hh, max_eq_right hr.2]
    ring
  have h2 : EqOn h (fun r => 2 * Real.pi * (r * Real.log r)) (uIcc s a) := by
    intro r hr
    rw [uIcc_of_le hsa] at hr
    simp only [hh, max_eq_left hr.1]
    ring
  have hi1 : IntervalIntegrable h volume 0 s := by
    refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.congr (by fun_prop) h1
  have hi2 : IntervalIntegrable h volume s a := by
    refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.congr
      (Real.continuous_mul_log.continuousOn.const_smul (2 * Real.pi)) h2
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    intervalIntegral.integral_congr h1, intervalIntegral.integral_congr h2]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id]
  have hF : ∫ r in s..a, r * Real.log r =
      (a ^ 2 / 2 * Real.log a - a ^ 2 / 4) - (s ^ 2 / 2 * Real.log s - s ^ 2 / 4) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := fun r : ℝ => r ^ 2 / 2 * Real.log r - r ^ 2 / 4) (f' := fun r : ℝ => r * Real.log r)
      hsa ?_ ?_ ?_
    · have : Continuous fun r : ℝ => r ^ 2 / 2 * Real.log r - r ^ 2 / 4 := by
        have h3 : Continuous fun r : ℝ => r * (r * Real.log r) :=
          continuous_id.mul Real.continuous_mul_log
        have : (fun r : ℝ => r ^ 2 / 2 * Real.log r - r ^ 2 / 4) =
            fun r => (r * (r * Real.log r)) / 2 - r ^ 2 / 4 := by
          funext r; ring
        rw [this]
        fun_prop
      exact this.continuousOn
    · intro x hx
      have hx0 : x ≠ 0 := (lt_of_le_of_lt hs hx.1).ne'
      have := (((hasDerivAt_pow 2 x).div_const 2).mul (Real.hasDerivAt_log hx0)).sub
        ((hasDerivAt_pow 2 x).div_const 4)
      convert this using 1
      field_simp
      ring
    · exact (Real.continuous_mul_log.intervalIntegrable _ _)
  rw [hF]
  ring

/-- The radial integral when the pole is outside the disc. -/
theorem radial_integral_of_ge {s a : ℝ} (ha : 0 ≤ a) (hsa : a ≤ s) :
    ∫ r in Ioo 0 a, r * (2 * Real.pi * Real.log (max r s)) =
      Real.pi * a ^ 2 * Real.log s := by
  have h1 : ∀ r ∈ Ioo 0 a, r * (2 * Real.pi * Real.log (max r s)) =
      2 * Real.pi * Real.log s * r := by
    intro r hr
    rw [max_eq_right (hr.2.le.trans hsa)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo h1, integral_Ioo_eq_intervalIntegral ha,
    intervalIntegral.integral_const_mul, integral_id]
  ring

/-! ### Newton's theorem -/

/-- Newton's theorem for the disc centred at `0`, in radial form. -/
theorem setIntegral_ball_zero_log_norm_sub (u : ℂ) (a : ℝ) :
    ∫ w in ball (0 : ℂ) a, Real.log ‖u - w‖ =
      ∫ r in Ioo 0 a, r * (2 * Real.pi * Real.log (max r ‖u‖)) := by
  have hm : Measurable fun w : ℂ => Real.log ‖u - w‖ :=
    Real.measurable_log.comp (measurable_norm.comp (measurable_const.sub measurable_id))
  rw [setIntegral_ball_zero_eq_polar hm (integrableOn_log_norm_sub_ball u 0 a)]
  refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
  rw [integral_Ioo_log_norm_sub_circleMap u hr.1]

/-- Translation of discs. -/
theorem setIntegral_ball_eq_setIntegral_ball_zero (f : ℂ → ℝ) (z : ℂ) (a : ℝ) :
    ∫ y in ball z a, f y = ∫ w in ball (0 : ℂ) a, f (z + w) := by
  have h := (measurePreserving_add_left volume z).setIntegral_preimage_emb
    (measurableEmbedding_addLeft z) f (ball z a)
  have hs : (fun w : ℂ => z + w) ⁻¹' ball z a = ball (0 : ℂ) a := by
    ext w; simp
  rw [hs] at h
  exact h.symm

theorem setIntegral_log_norm_sub_ball_eq (x z : ℂ) (a : ℝ) :
    ∫ y in ball z a, Real.log ‖x - y‖ =
      ∫ w in ball (0 : ℂ) a, Real.log ‖(x - z) - w‖ := by
  rw [setIntegral_ball_eq_setIntegral_ball_zero]
  simp_rw [sub_sub]

/-- **Newton's theorem, exterior case.** For a pole `x` outside the disc `B(z, a)`, the
logarithmic potential of the uniform disc equals that of a point mass at the centre:
`∫_{B(z,a)} log |x - y| dy = π a² log |x - z|`. -/
theorem setIntegral_log_norm_sub_ball_of_le (x z : ℂ) {a : ℝ} (ha : 0 < a)
    (hx : a ≤ ‖x - z‖) :
    ∫ y in Metric.ball z a, Real.log ‖x - y‖ = Real.pi * a ^ 2 * Real.log ‖x - z‖ := by
  rw [setIntegral_log_norm_sub_ball_eq, setIntegral_ball_zero_log_norm_sub _ a]
  exact radial_integral_of_ge ha.le hx

/-- **Newton's theorem, interior case.** For a pole `x` inside the disc `B(z, a)`,
`∫_{B(z,a)} log |x - y| dy = π a² (log a - (1 - |x - z|² / a²) / 2)`. -/
theorem setIntegral_log_norm_sub_ball_of_ge (x z : ℂ) {a : ℝ} (ha : 0 < a)
    (hx : ‖x - z‖ ≤ a) :
    ∫ y in Metric.ball z a, Real.log ‖x - y‖ =
      Real.pi * a ^ 2 * (Real.log a - (1 - ‖x - z‖ ^ 2 / a ^ 2) / 2) := by
  rw [setIntegral_log_norm_sub_ball_eq, setIntegral_ball_zero_log_norm_sub _ a,
    integral_Ioo_eq_intervalIntegral ha.le, radial_integral_of_le (norm_nonneg _) hx]
  field_simp
  ring

/-! ### Uniform `L¹` bounds -/

/-- Explicit uniform `L¹` bound for the logarithmic kernel on a disc: if `|x - z| ≤ R` then
`∫_{B(z,a)} |log |x - y|| dy ≤ π a² log (max (R + a) 1) + π / 2`. -/
theorem setIntegral_abs_log_norm_sub_ball_le_explicit (x z : ℂ) {a R : ℝ} (ha : 0 < a)
    (hx : ‖x - z‖ ≤ R) :
    ∫ y in Metric.ball z a, |Real.log ‖x - y‖| ≤
      Real.pi * a ^ 2 * Real.log (max (R + a) 1) + Real.pi / 2 := by
  set C0 : ℝ := Real.log (max (R + a) 1) with hC0def
  have hC0 : 0 ≤ C0 := Real.log_nonneg (le_max_right _ _)
  set G : ℂ → ℝ := indicator (ball x 1) fun y => -Real.log ‖x - y‖ with hG
  have hGint : Integrable G := by
    rw [hG, integrable_indicator_iff measurableSet_ball]
    exact (integrableOn_log_norm_sub_ball x x 1).neg
  have hG0 : ∀ y, 0 ≤ G y := by
    intro y
    by_cases hy : y ∈ ball x 1
    · have : ‖x - y‖ < 1 := mem_ball_iff_norm'.1 hy
      simp only [hG, indicator_of_mem hy]
      linarith [Real.log_nonpos (norm_nonneg _) this.le]
    · simp [hG, hy]
  have hpt : ∀ y ∈ ball z a, |Real.log ‖x - y‖| ≤ C0 + G y := by
    intro y hy
    by_cases hy1 : y ∈ ball x 1
    · have h1 : ‖x - y‖ < 1 := mem_ball_iff_norm'.1 hy1
      have h2 : Real.log ‖x - y‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) h1.le
      simp only [hG, indicator_of_mem hy1]
      rw [abs_of_nonpos h2]
      linarith
    · have h1 : 1 ≤ ‖x - y‖ := not_lt.1 fun h => hy1 (mem_ball_iff_norm'.2 h)
      have h2 : ‖x - y‖ ≤ R + a := by
        have h3 : ‖y - z‖ < a := mem_ball_iff_norm.1 hy
        calc ‖x - y‖ = ‖(x - z) - (y - z)‖ := by congr 1; ring
          _ ≤ ‖x - z‖ + ‖y - z‖ := norm_sub_le _ _
          _ ≤ R + a := by linarith
      have h4 : Real.log ‖x - y‖ ≤ C0 :=
        Real.log_le_log (by linarith) (h2.trans (le_max_left _ _))
      rw [abs_of_nonneg (Real.log_nonneg h1)]
      have := hG0 y
      linarith
  have hfin : volume (ball z a) ≠ ⊤ := measure_ball_lt_top.ne
  have hconst : IntegrableOn (fun _ : ℂ => C0) (ball z a) := integrableOn_const hfin
  calc ∫ y in Metric.ball z a, |Real.log ‖x - y‖|
      ≤ ∫ y in ball z a, (C0 + G y) :=
        setIntegral_mono_on (integrableOn_log_norm_sub_ball x z a).abs
          (hconst.add hGint.integrableOn) measurableSet_ball hpt
    _ = C0 * volume.real (ball z a) + ∫ y in ball z a, G y := by
        rw [integral_add hconst hGint.integrableOn, setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ C0 * (Real.pi * a ^ 2) + ∫ y, G y := by
        have hvol : volume.real (ball z a) = Real.pi * a ^ 2 := by
          rw [Measure.real, Complex.volume_ball]
          simp [ENNReal.toReal_mul, ENNReal.toReal_pow, ha.le]
          ring
        have h6 : ∫ y in ball z a, G y ≤ ∫ y, G y :=
          setIntegral_le_integral hGint (Filter.Eventually.of_forall hG0)
        rw [hvol]
        linarith
    _ = Real.pi * a ^ 2 * C0 + Real.pi / 2 := by
        have h5 : ∫ y, G y = Real.pi / 2 := by
          rw [hG, integral_indicator measurableSet_ball, integral_neg,
            setIntegral_log_norm_sub_ball_of_ge x x one_pos (by simp)]
          simp
          ring
        rw [h5]
        ring

/-- A uniform `L¹` bound for the logarithmic kernel on a disc, uniform in the pole `x`
ranging over a bounded set. -/
theorem setIntegral_abs_log_norm_sub_ball_le (z : ℂ) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    ∃ C : ℝ, ∀ x : ℂ, ‖x - z‖ ≤ R → ∫ y in Metric.ball z a, |Real.log ‖x - y‖| ≤ C :=
  ⟨Real.pi * a ^ 2 * Real.log (max (R + a) 1) + Real.pi / 2, fun x hx =>
    setIntegral_abs_log_norm_sub_ball_le_explicit x z ha hx⟩

/-! ### Integrability on products of discs -/

/-- The logarithmic kernel `(x, y) ↦ log ‖x - y‖` is integrable for the product of the
restrictions of Lebesgue measure to two discs. -/
theorem integrable_log_norm_sub_prod_ball (z w : ℂ) (a b : ℝ) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      ((MeasureTheory.volume.restrict (Metric.ball z a)).prod
        (MeasureTheory.volume.restrict (Metric.ball w b))) := by
  rcases le_or_gt a 0 with ha | ha
  · rw [Metric.ball_eq_empty.2 ha, Measure.restrict_empty, Measure.zero_prod]
    exact integrable_zero_measure
  rcases le_or_gt b 0 with hb | hb
  · rw [Metric.ball_eq_empty.2 hb, Measure.restrict_empty, Measure.prod_zero]
    exact integrable_zero_measure
  have : IsFiniteMeasure (volume.restrict (ball z a)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_ball_lt_top : volume (ball z a) < ⊤)⟩
  have hmeas : AEStronglyMeasurable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      ((volume.restrict (ball z a)).prod (volume.restrict (ball w b))) :=
    (Real.measurable_log.comp
      (measurable_norm.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall fun x => integrableOn_log_norm_sub_ball x w b, ?_⟩
  obtain ⟨C, hC⟩ := setIntegral_abs_log_norm_sub_ball_le w hb (a + ‖z - w‖)
  refine Integrable.of_bound (C := C) ?_ ?_
  · exact hmeas.norm.integral_prod_right'
  · refine (ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : ‖x - w‖ ≤ a + ‖z - w‖ := by
      have h1 : ‖x - z‖ < a := mem_ball_iff_norm.1 hx
      calc ‖x - w‖ = ‖(x - z) + (z - w)‖ := by congr 1; ring
        _ ≤ ‖x - z‖ + ‖z - w‖ := norm_add_le _ _
        _ ≤ a + ‖z - w‖ := by linarith
    have h2 := hC x hx'
    rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    simpa [Real.norm_eq_abs] using h2

end TwoComponentCoulomb

end
