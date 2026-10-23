/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.SmearedKernel
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Potential.SmearedKernel
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Gaussian mass of the critical case `β = 2`

Source l. 703–707, 738: Lemma 3.3 (`lem:critical radial`), part (2), `(eq:critical-B)`; it is
used for `β = 2` in the proof of Lemma 3.5 (`lemma:part nn`, ). With `ℓ = |log λ|`
the Gaussian mass `B = J_λ(1/ℓ) = ∫_{ℝ²} e^{2 g_λ(u) - |u|²/ℓ} du` is `2π (ℓ + ½ log ℓ + O(1))`.

* `integrable_gaussianMass` : the integrand is integrable (`0 < λ ≤ e⁻¹`).
* `exists_abs_gaussianMass_sub_le` : `|B - 2π (ℓ + ½ log ℓ)| ≤ C`, uniformly in `0 < λ ≤ e⁻¹`.

Proof. In polar coordinates (`integral_comp_norm_complex`), `B = 2π ∫₀^∞ r e^{2 g_λ(r) - r²/ℓ} dr`.
The radial integral is split at `2λ` and at `√ℓ`.

* On `(0, 2λ]` the integrand is at most `r e^{2C} λ⁻²` (since `g_λ ≤ -log λ + C`), so the
  integral is in `[0, 2 e^{2C}]`.
* On `[2λ, ∞)` one has `g_λ(r) = -log r`, so the integrand is `e^{-r²/ℓ} / r`.
  Between `2λ` and `√ℓ` this lies between `1/r - r/ℓ` and `1/r` (from `1 - x ≤ e^{-x} ≤ 1`),
  giving `log √ℓ - log (2λ) - 1/2` and `log √ℓ - log (2λ)` as bounds for the integral.
  Beyond `√ℓ` it is at most `(r/ℓ) e^{-r²/ℓ}`, which has the primitive `-½ e^{-r²/ℓ}`, so the tail
  is in `[0, 1/2]`.

Finally `log √ℓ - log (2λ) = ℓ + ½ log ℓ - log 2`. As in the other files, the `O(1)` of the source
is an explicit constant `C`, quantified before `λ`.
-/

public section

open MeasureTheory Set

namespace TwoComponentCoulomb

/-! ### The profile `e^{-y²/ℓ} / y` for `y ≥ √ℓ` -/

/-- `y ↦ e^{-y²/ℓ} / y` is continuous on `[a, ∞)` for `a > 0`. -/
theorem continuousOn_exp_neg_sq_div (ℓ : ℝ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y : ℝ => Real.exp (-(y ^ 2 / ℓ)) / y) (Ici a) := by
  refine ContinuousOn.div (by fun_prop) continuousOn_id (fun y hy => ?_)
  exact (ha.trans_le hy).ne'

/-- `e^{-y²/ℓ} / y ≥ 0` for `y ≥ 0`. -/
theorem exp_neg_sq_div_nonneg (ℓ : ℝ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ Real.exp (-(y ^ 2 / ℓ)) / y :=
  div_nonneg (Real.exp_pos _).le hy

/-- The primitive `-½ e^{-y²/ℓ}` of `(y/ℓ) e^{-y²/ℓ}`. -/
theorem hasDerivAt_neg_half_exp {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => -(1 / 2) * Real.exp (-(y ^ 2 / ℓ)))
      (y / ℓ * Real.exp (-(y ^ 2 / ℓ))) y := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / ℓ) (2 * y / ℓ) y := by
    simpa using (hasDerivAt_pow 2 y).div_const ℓ
  have h3 : HasDerivAt (fun y : ℝ => -(y ^ 2 / ℓ)) (-(2 * y / ℓ)) y := h1.neg
  have h2 := (h3.exp).const_mul (-(1 / 2))
  convert h2 using 1
  field_simp

/-- The primitive `-½ e^{-y²/ℓ}` tends to `0` at `+∞`. -/
theorem tendsto_neg_half_exp {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Filter.Tendsto (fun y : ℝ => -(1 / 2) * Real.exp (-(y ^ 2 / ℓ))) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun y : ℝ => y ^ 2 / ℓ) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (two_ne_zero)).atTop_div_const hℓ
  have h2 := Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp h1)
  have h4 := h2.const_mul (-(1 / 2))
  rwa [mul_zero] at h4

/-- `(y/ℓ) e^{-y²/ℓ}` is integrable on `(b, ∞)` for `b ≥ 0`. -/
theorem integrableOn_Ioi_mul_exp {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (fun y : ℝ => y / ℓ * Real.exp (-(y ^ 2 / ℓ))) (Ioi b) :=
  integrableOn_Ioi_deriv_of_nonneg (g := fun y : ℝ => -(1 / 2) * Real.exp (-(y ^ 2 / ℓ)))
    (l := 0) (by fun_prop) (fun y _ => hasDerivAt_neg_half_exp hℓ y)
    (fun y hy => by have := hb.trans_lt hy; positivity) (tendsto_neg_half_exp hℓ)

/-- `∫_b^∞ (y/ℓ) e^{-y²/ℓ} dy = ½ e^{-b²/ℓ}` for `b ≥ 0`. -/
theorem integral_Ioi_mul_exp {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ} (hb : 0 ≤ b) :
    ∫ y in Ioi b, y / ℓ * Real.exp (-(y ^ 2 / ℓ)) = (1 / 2) * Real.exp (-(b ^ 2 / ℓ)) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (g := fun y : ℝ => -(1 / 2) * Real.exp (-(y ^ 2 / ℓ)))
    (l := 0) (by fun_prop) (fun y _ => hasDerivAt_neg_half_exp hℓ y)
    (fun y hy => by have := hb.trans_lt hy; positivity) (tendsto_neg_half_exp hℓ)]
  ring

/-- For `y ≥ √ℓ`, `e^{-y²/ℓ} / y ≤ (y/ℓ) e^{-y²/ℓ}`. -/
theorem exp_neg_sq_div_le_mul_exp {ℓ y : ℝ} (hℓ : 0 < ℓ) (hy : Real.sqrt ℓ ≤ y) :
    Real.exp (-(y ^ 2 / ℓ)) / y ≤ y / ℓ * Real.exp (-(y ^ 2 / ℓ)) := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  have hy0 : 0 < y := hs.trans_le hy
  have h1 : ℓ ≤ y ^ 2 := by
    have := pow_le_pow_left₀ hs.le hy 2
    rwa [Real.sq_sqrt hℓ.le] at this
  have h2 : 1 / y ≤ y / ℓ := by
    rw [div_le_div_iff₀ hy0 hℓ]
    linarith
  calc Real.exp (-(y ^ 2 / ℓ)) / y = Real.exp (-(y ^ 2 / ℓ)) * (1 / y) := by rw [mul_one_div]
    _ ≤ Real.exp (-(y ^ 2 / ℓ)) * (y / ℓ) := by gcongr
    _ = y / ℓ * Real.exp (-(y ^ 2 / ℓ)) := mul_comm _ _

/-- The tail `e^{-y²/ℓ} / y` is integrable on `(√ℓ, ∞)`. -/
theorem integrableOn_exp_neg_sq_div_Ioi {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IntegrableOn (fun y : ℝ => Real.exp (-(y ^ 2 / ℓ)) / y) (Ioi (Real.sqrt ℓ)) := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  refine Integrable.mono' (integrableOn_Ioi_mul_exp hℓ hs.le)
    ((continuousOn_exp_neg_sq_div ℓ hs).mono Ioi_subset_Ici_self |>.aestronglyMeasurable
      measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
  rw [Real.norm_of_nonneg (exp_neg_sq_div_nonneg ℓ (hs.trans (mem_Ioi.1 hy)).le)]
  exact exp_neg_sq_div_le_mul_exp hℓ (mem_Ioi.1 hy).le

/-- The tail integral beyond `√ℓ` is nonnegative. -/
theorem integral_exp_neg_sq_div_Ioi_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) :
    0 ≤ ∫ y in Ioi (Real.sqrt ℓ), Real.exp (-(y ^ 2 / ℓ)) / y := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  exact setIntegral_nonneg measurableSet_Ioi fun y hy => exp_neg_sq_div_nonneg ℓ (hs.trans hy).le

/-- The tail integral beyond `√ℓ` is at most `1/2`. -/
theorem integral_exp_neg_sq_div_Ioi_le {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ y in Ioi (Real.sqrt ℓ), Real.exp (-(y ^ 2 / ℓ)) / y ≤ 1 / 2 := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  calc ∫ y in Ioi (Real.sqrt ℓ), Real.exp (-(y ^ 2 / ℓ)) / y
      ≤ ∫ y in Ioi (Real.sqrt ℓ), y / ℓ * Real.exp (-(y ^ 2 / ℓ)) :=
        setIntegral_mono_on (integrableOn_exp_neg_sq_div_Ioi hℓ) (integrableOn_Ioi_mul_exp hℓ hs.le)
          measurableSet_Ioi fun y hy => exp_neg_sq_div_le_mul_exp hℓ (mem_Ioi.1 hy).le
    _ = (1 / 2) * Real.exp (-(Real.sqrt ℓ ^ 2 / ℓ)) := integral_Ioi_mul_exp hℓ hs.le
    _ ≤ (1 / 2) * 1 := by
        gcongr
        rw [Real.exp_le_one_iff, neg_nonpos]
        positivity
    _ = 1 / 2 := mul_one _

/-! ### The middle range `a ≤ y ≤ √ℓ` -/

/-- `e^{-y²/ℓ} / y` is integrable on every bounded interval `(a, b]` with `a > 0`. -/
theorem integrableOn_exp_neg_sq_div_Ioc (ℓ : ℝ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => Real.exp (-(y ^ 2 / ℓ)) / y) (Ioc a b) :=
  (((continuousOn_exp_neg_sq_div ℓ ha).mono Icc_subset_Ici_self).integrableOn_Icc).mono_set
    Ioc_subset_Icc_self

/-- Upper bound: `∫_a^{√ℓ} e^{-y²/ℓ} / y ≤ log √ℓ - log a`. -/
theorem integral_exp_neg_sq_div_Ioc_le {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a)
    (hab : a ≤ Real.sqrt ℓ) :
    ∫ y in Ioc a (Real.sqrt ℓ), Real.exp (-(y ^ 2 / ℓ)) / y ≤
      Real.log (Real.sqrt ℓ) - Real.log a := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  rw [← intervalIntegral.integral_of_le hab]
  have h1 : ∫ y in a..Real.sqrt ℓ, 1 / y = Real.log (Real.sqrt ℓ) - Real.log a := by
    rw [integral_one_div_of_pos ha hs, Real.log_div hs.ne' ha.ne']
  rw [← h1]
  have hc : ∀ y ∈ Icc a (Real.sqrt ℓ), 0 < y := fun y hy => ha.trans_le hy.1
  refine intervalIntegral.integral_mono_on hab
    ((continuousOn_exp_neg_sq_div ℓ ha).mono Icc_subset_Ici_self |>.intervalIntegrable_of_Icc hab)
    (ContinuousOn.intervalIntegrable_of_Icc hab ?_) fun y hy => ?_
  · exact continuousOn_const.div continuousOn_id fun y hy => (hc y hy).ne'
  · have := hc y hy
    rw [div_le_div_iff_of_pos_right this]
    exact Real.exp_le_one_iff.2 (by simp only [neg_nonpos]; positivity)

/-- Lower bound: `∫_a^{√ℓ} e^{-y²/ℓ} / y ≥ log √ℓ - log a - 1/2`, from `e^{-x} ≥ 1 - x`. -/
theorem le_integral_exp_neg_sq_div_Ioc {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a)
    (hab : a ≤ Real.sqrt ℓ) :
    Real.log (Real.sqrt ℓ) - Real.log a - 1 / 2 ≤
      ∫ y in Ioc a (Real.sqrt ℓ), Real.exp (-(y ^ 2 / ℓ)) / y := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  rw [← intervalIntegral.integral_of_le hab]
  have hc : ∀ y ∈ Icc a (Real.sqrt ℓ), 0 < y := fun y hy => ha.trans_le hy.1
  have hi1 : IntervalIntegrable (fun y : ℝ => 1 / y) volume a (Real.sqrt ℓ) :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (continuousOn_const.div continuousOn_id fun y hy => (hc y hy).ne')
  have hi2 : IntervalIntegrable (fun y : ℝ => y / ℓ) volume a (Real.sqrt ℓ) :=
    (continuous_id.div_const ℓ).intervalIntegrable _ _
  have h1 : ∫ y in a..Real.sqrt ℓ, (1 / y - y / ℓ) =
      Real.log (Real.sqrt ℓ) - Real.log a - (Real.sqrt ℓ ^ 2 - a ^ 2) / 2 / ℓ := by
    rw [intervalIntegral.integral_sub hi1 hi2, integral_one_div_of_pos ha hs,
      Real.log_div hs.ne' ha.ne', intervalIntegral.integral_div, integral_id]
  have h2 : (Real.sqrt ℓ ^ 2 - a ^ 2) / 2 / ℓ ≤ 1 / 2 := by
    rw [div_le_iff₀ hℓ, Real.sq_sqrt hℓ.le]
    nlinarith [sq_nonneg a]
  have h3 : ∫ y in a..Real.sqrt ℓ, (1 / y - y / ℓ) ≤
      ∫ y in a..Real.sqrt ℓ, Real.exp (-(y ^ 2 / ℓ)) / y := by
    refine intervalIntegral.integral_mono_on hab (hi1.sub hi2)
      ((continuousOn_exp_neg_sq_div ℓ ha).mono Icc_subset_Ici_self |>.intervalIntegrable_of_Icc hab)
      fun y hy => ?_
    have hy0 := hc y hy
    have h4 := Real.add_one_le_exp (-(y ^ 2 / ℓ))
    have h5 : 1 / y - y / ℓ = (-(y ^ 2 / ℓ) + 1) / y := by
      field_simp
      ring
    rw [h5]
    exact div_le_div_of_nonneg_right h4 hy0.le
  linarith

/-! ### The radial profile of the Gaussian mass -/

/-- The radial profile of the Gaussian mass: `y ↦ exp(2 g_λ(y) - y²/ℓ)`. -/
noncomputable def gaussianProfile (lam ℓ y : ℝ) : ℝ :=
  Real.exp (2 * smearedKernel lam (y : ℂ) - y ^ 2 / ℓ)

/-- The profile is continuous. -/
theorem continuous_gaussianProfile {lam : ℝ} (hlam : 0 < lam) (ℓ : ℝ) :
    Continuous (gaussianProfile lam ℓ) := by
  unfold gaussianProfile
  have := (continuous_smearedKernel hlam).comp Complex.continuous_ofReal
  fun_prop

/-- The integrand of the Gaussian mass is the radial function `gaussianProfile λ ℓ (|u|)`. -/
theorem gaussianProfile_eq_comp_norm (lam ℓ : ℝ) (u : ℂ) :
    Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ) = gaussianProfile lam ℓ ‖u‖ := by
  unfold gaussianProfile
  rw [← smearedKernel_eq_norm lam u]

/-- Outside `B(0, 2λ)`: `y e^{2 g_λ(y) - y²/ℓ} = e^{-y²/ℓ} / y`. -/
theorem mul_gaussianProfile_of_le {lam ℓ : ℝ} (hlam : 0 < lam) {y : ℝ} (hy : 2 * lam ≤ y) :
    y * gaussianProfile lam ℓ y = Real.exp (-(y ^ 2 / ℓ)) / y := by
  have hy0 : 0 < y := by linarith
  unfold gaussianProfile
  rw [smearedKernel_ofReal_of_le hlam hy,
    show 2 * -Real.log y - y ^ 2 / ℓ = -(Real.log y + Real.log y) - y ^ 2 / ℓ by ring,
    Real.exp_sub, Real.exp_neg, Real.exp_add, Real.exp_log hy0, Real.exp_neg]
  field_simp

/-- Inside `B(0, 2λ)`: from `g_λ ≤ -log λ + C`, the profile is at most `e^{2C} / λ²`. -/
theorem gaussianProfile_le {C : ℝ}
    (hC : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, smearedKernel lam z ≤ -Real.log lam + C)
    {lam : ℝ} (hlam : 0 < lam) {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) :
    gaussianProfile lam ℓ y ≤ Real.exp (2 * C) / lam ^ 2 := by
  unfold gaussianProfile
  calc Real.exp (2 * smearedKernel lam (y : ℂ) - y ^ 2 / ℓ)
      ≤ Real.exp (2 * (-Real.log lam + C)) := by
        apply Real.exp_le_exp.2
        have := hC lam hlam (y : ℂ)
        have : 0 ≤ y ^ 2 / ℓ := by positivity
        linarith
    _ = Real.exp (2 * C) / lam ^ 2 := by
        rw [show 2 * (-Real.log lam + C) = 2 * C - (Real.log lam + Real.log lam) by ring,
          Real.exp_sub, Real.exp_add, Real.exp_log hlam, sq]


/-! ### The radial integral -/

/-- The radial integrand `y ↦ y e^{2 g_λ(y) - y²/ℓ}` is integrable on `(0, ∞)`. -/
theorem integrableOn_mul_gaussianProfile {lam ℓ : ℝ} (hlam : 0 < lam) (hℓ : 0 < ℓ)
    (h2 : 2 * lam ≤ Real.sqrt ℓ) :
    IntegrableOn (fun y : ℝ => y * gaussianProfile lam ℓ y) (Ioi 0) := by
  have h1 : IntegrableOn (fun y : ℝ => y * gaussianProfile lam ℓ y) (Ioc 0 (2 * lam)) :=
    ((continuous_id.mul (continuous_gaussianProfile hlam ℓ)).continuousOn.integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have h3 : IntegrableOn (fun y : ℝ => y * gaussianProfile lam ℓ y) (Ioi (2 * lam)) := by
    have h4 : IntegrableOn (fun y : ℝ => Real.exp (-(y ^ 2 / ℓ)) / y) (Ioi (2 * lam)) := by
      rw [← Ioc_union_Ioi_eq_Ioi h2]
      exact (integrableOn_exp_neg_sq_div_Ioc ℓ (by linarith)).union
        (integrableOn_exp_neg_sq_div_Ioi hℓ)
    exact h4.congr_fun (fun y hy => (mul_gaussianProfile_of_le hlam (mem_Ioi.1 hy).le).symm)
      measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ 2 * lam)]
  exact h1.union h3

/-- The radial integral is within `2 e^{2C} + 1/2` of `log √ℓ - log (2λ)`. -/
theorem abs_integral_mul_gaussianProfile_sub_le {C : ℝ}
    (hC : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, smearedKernel lam z ≤ -Real.log lam + C)
    {lam ℓ : ℝ} (hlam : 0 < lam) (hℓ : 0 < ℓ) (h2 : 2 * lam ≤ Real.sqrt ℓ) :
    |(∫ y in Ioi (0 : ℝ), y * gaussianProfile lam ℓ y) -
        (Real.log (Real.sqrt ℓ) - Real.log (2 * lam))| ≤ 2 * Real.exp (2 * C) + 1 / 2 := by
  have ha : 0 < 2 * lam := by linarith
  have hint := integrableOn_mul_gaussianProfile hlam hℓ h2
  have hI2 : IntegrableOn (fun y : ℝ => y * gaussianProfile lam ℓ y) (Ioi (2 * lam)) :=
    hint.mono_set (Ioi_subset_Ioi ha.le)
  have hI1 : IntegrableOn (fun y : ℝ => y * gaussianProfile lam ℓ y) (Ioc 0 (2 * lam)) :=
    hint.mono_set (fun x hx => hx.1)
  have hT : ∫ y in Ioi (2 * lam), y * gaussianProfile lam ℓ y =
      (∫ y in Ioc (2 * lam) (Real.sqrt ℓ), Real.exp (-(y ^ 2 / ℓ)) / y) +
        ∫ y in Ioi (Real.sqrt ℓ), Real.exp (-(y ^ 2 / ℓ)) / y := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun y hy => mul_gaussianProfile_of_le hlam (mem_Ioi.1 hy).le)]
    conv_lhs => rw [← Ioc_union_Ioi_eq_Ioi h2]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_exp_neg_sq_div_Ioc ℓ ha) (integrableOn_exp_neg_sq_div_Ioi hℓ)
  have hS : ∫ y in Ioi (0 : ℝ), y * gaussianProfile lam ℓ y =
      (∫ y in Ioc 0 (2 * lam), y * gaussianProfile lam ℓ y) +
        ∫ y in Ioi (2 * lam), y * gaussianProfile lam ℓ y := by
    conv_lhs => rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2
  have hin0 : 0 ≤ ∫ y in Ioc 0 (2 * lam), y * gaussianProfile lam ℓ y := by
    refine setIntegral_nonneg measurableSet_Ioc fun y hy => ?_
    exact mul_nonneg hy.1.le (Real.exp_pos _).le
  have hin1 : ∫ y in Ioc 0 (2 * lam), y * gaussianProfile lam ℓ y ≤ 2 * Real.exp (2 * C) := by
    rw [← intervalIntegral.integral_of_le ha.le]
    calc ∫ y in (0 : ℝ)..2 * lam, y * gaussianProfile lam ℓ y
        ≤ ∫ y in (0 : ℝ)..2 * lam, y * (Real.exp (2 * C) / lam ^ 2) := by
          refine intervalIntegral.integral_mono_on ha.le
            ((continuous_id.mul (continuous_gaussianProfile hlam ℓ)).intervalIntegrable _ _)
            (continuous_id.mul continuous_const |>.intervalIntegrable _ _) fun y hy => ?_
          exact mul_le_mul_of_nonneg_left (gaussianProfile_le hC hlam hℓ y) hy.1
      _ = 2 * Real.exp (2 * C) := by
          rw [intervalIntegral.integral_mul_const, integral_id]
          field_simp
          ring
  have hmid1 := integral_exp_neg_sq_div_Ioc_le hℓ ha h2
  have hmid2 := le_integral_exp_neg_sq_div_Ioc hℓ ha h2
  have htail1 := integral_exp_neg_sq_div_Ioi_nonneg hℓ
  have htail2 := integral_exp_neg_sq_div_Ioi_le hℓ
  rw [hS, hT, abs_le]
  constructor <;> linarith

/-! ### The Gaussian mass `B` (Lemma 3.3, `(eq:critical-B)`) -/

/-- For `0 < λ ≤ e⁻¹`: `ℓ = -log λ ≥ 1` and `2λ ≤ √ℓ`. -/
theorem two_mul_le_sqrt_neg_log {lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Real.exp (-1)) :
    1 ≤ -Real.log lam ∧ 2 * lam ≤ Real.sqrt (-Real.log lam) := by
  have h1 : Real.log lam ≤ -1 := by
    have := Real.log_le_log hlam hle
    rwa [Real.log_exp] at this
  have h2 : 1 ≤ -Real.log lam := by linarith
  refine ⟨h2, ?_⟩
  have h3 : 2 * Real.exp (-1) ≤ 1 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [mul_inv_le_iff₀ (Real.exp_pos 1)]
    linarith
  calc 2 * lam ≤ 2 * Real.exp (-1) := by linarith
    _ ≤ 1 := h3
    _ ≤ Real.sqrt (-Real.log lam) := Real.one_le_sqrt.2 h2

/-- The integrand of the Gaussian mass `B` is integrable for `λ ≤ e⁻¹`. -/
theorem integrable_gaussianMass {lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Real.exp (-1)) :
    Integrable (fun u : ℂ =>
      Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|)) := by
  obtain ⟨h1, h2⟩ := two_mul_le_sqrt_neg_log hlam hle
  have hab : |Real.log lam| = -Real.log lam :=
    abs_of_neg (by linarith)
  rw [hab]
  have hf : (fun u : ℂ => Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / -Real.log lam)) =
      fun u : ℂ => gaussianProfile lam (-Real.log lam) ‖u‖ :=
    funext (gaussianProfile_eq_comp_norm lam (-Real.log lam))
  rw [hf]
  exact (integrable_comp_norm_complex_iff _).2
    (integrableOn_mul_gaussianProfile hlam (by linarith) h2)

/-- The Gaussian mass `B = ∫_{ℝ²} e^{2 g_λ(u) - |u|²/ℓ} du`, `ℓ = |log λ|`, equals
`2π (ℓ + ½ log ℓ + O(1))` (source l. 703–707, `(eq:critical-B)` of Lemma 3.3). -/
theorem exists_abs_gaussianMass_sub_le :
    ∃ C : ℝ, ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      |(∫ u : ℂ, Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|)) -
        2 * Real.pi * (|Real.log lam| + (1 / 2) * Real.log |Real.log lam|)| ≤ C := by
  obtain ⟨C, hC⟩ := exists_smearedKernel_le
  refine ⟨2 * Real.pi * (2 * Real.exp (2 * C) + 2), fun lam hlam hle => ?_⟩
  obtain ⟨h1, h2⟩ := two_mul_le_sqrt_neg_log hlam hle
  have hab : |Real.log lam| = -Real.log lam :=
    abs_of_neg (by linarith)
  rw [hab]
  have hf : (fun u : ℂ => Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / -Real.log lam)) =
      fun u : ℂ => gaussianProfile lam (-Real.log lam) ‖u‖ :=
    funext (gaussianProfile_eq_comp_norm lam (-Real.log lam))
  have hℓ : 0 < -Real.log lam := by linarith
  rw [hf, integral_comp_norm_complex]
  have hJ := abs_integral_mul_gaussianProfile_sub_le hC hlam hℓ h2
  set J := ∫ y in Ioi (0 : ℝ), y * gaussianProfile lam (-Real.log lam) y with hJdef
  have hL : Real.log (Real.sqrt (-Real.log lam)) - Real.log (2 * lam) =
      -Real.log lam + (1 / 2) * Real.log (-Real.log lam) - Real.log 2 := by
    rw [Real.log_sqrt hℓ.le, Real.log_mul two_ne_zero hlam.ne']
    ring
  rw [hL] at hJ
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key : |J - (-Real.log lam + (1 / 2) * Real.log (-Real.log lam))| ≤
      2 * Real.exp (2 * C) + 2 := by
    rw [abs_le] at hJ ⊢
    constructor <;> linarith [hJ.1, hJ.2]
  calc |2 * Real.pi * J - 2 * Real.pi * (-Real.log lam + (1 / 2) * Real.log (-Real.log lam))|
      = 2 * Real.pi * |J - (-Real.log lam + (1 / 2) * Real.log (-Real.log lam))| := by
        rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    _ ≤ 2 * Real.pi * (2 * Real.exp (2 * C) + 2) := by gcongr

end TwoComponentCoulomb

end
