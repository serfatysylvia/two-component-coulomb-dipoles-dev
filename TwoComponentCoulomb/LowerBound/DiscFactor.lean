/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Integrals.Radial

/-!
# The disc factor of the lower bound (Proposition 4.1, Step 2)

Source: Proposition 4.1, Step 2 (l. 1828–1852), eqs. (minz3) and (align57), by the route of
ruling R12a (no `-A_β s²/r²` correction in the exponent of `J_β`, l. 1831).

For `β > 2`, `λ > 0` and `r ≥ 4λ` the disc factor `J(r) = ∫_{B̄(0, r/2)} e^{β g_λ}` is the full mass
`𝒵_β λ^{2-β}` minus the exact tail `2π (r/2)^{2-β} / (β - 2)`. Since `𝒵_β` exceeds the mass of the
tail from radius `2`, the relative tail is bounded by `x₀ < 1`, and so
`J(r) ≥ 𝒵_β λ^{2-β} exp(-C_β (λ/r)^{β-2})`.

* `integral_ball_exp_smearedKernel_pos` : `∫_{B(0,t)} e^{β g_λ} > 0`.
* `two_pi_mul_two_rpow_div_lt_dipoleConstant` : `𝒵_β > 2π 2^{2-β} / (β - 2)`.
* `exp_neg_div_le_one_sub` : the elementary inequality `exp(-x/(1-x₀)) ≤ 1 - x`.
* `disc_factor_ge` : the disc factor bound (1).
-/

public section

open MeasureTheory Set

namespace TwoComponentCoulomb

/-- The mass of `e^{β g_λ}` in a disc of positive radius is positive. -/
theorem integral_ball_exp_smearedKernel_pos {β lam t : ℝ} (hβ : 2 < β) (hlam : 0 < lam)
    (ht : 0 < t) :
    0 < ∫ u in Metric.ball (0 : ℂ) t, Real.exp (β * smearedKernel lam u) := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun u : ℂ => Real.exp (β * smearedKernel lam u)) ∩
        Metric.ball (0 : ℂ) t = Metric.ball (0 : ℂ) t := by
      refine inter_eq_right.2 fun u _ => ?_
      exact (Real.exp_pos _).ne'
    rw [this]
    exact Metric.measure_ball_pos volume 0 ht
  · exact Filter.Eventually.of_forall fun u => (Real.exp_pos _).le
  · exact (integrable_exp_smearedKernel hβ hlam).integrableOn

/-- `𝒵_β` exceeds the mass `2π 2^{2-β} / (β - 2)` of the tail of `μ_β` beyond radius `2`
(the integral over `[0, 2]` is positive). -/
theorem two_pi_mul_two_rpow_div_lt_dipoleConstant {β : ℝ} (hβ : 2 < β) :
    2 * Real.pi * ((2 : ℝ) ^ (2 - β) / (β - 2)) < dipoleConstant β hβ.le := by
  have h := integral_ball_exp_smearedKernel (β := β) (lam := 1) (t := 2) hβ one_pos (by norm_num)
  have hpos := integral_ball_exp_smearedKernel_pos (β := β) (lam := 1) (t := 2) hβ one_pos
    (by norm_num)
  rw [h, Real.one_rpow, mul_one] at hpos
  linarith

/-- The elementary inequality `exp(-x/(1-x₀)) ≤ 1 - x` for `0 ≤ x ≤ x₀ < 1`. -/
theorem exp_neg_div_le_one_sub {x x₀ : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) (hx₀ : x₀ < 1) :
    Real.exp (-(x / (1 - x₀))) ≤ 1 - x := by
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 < 1 - x₀ := by linarith
  have h3 := Real.one_sub_inv_le_log_of_pos h1
  have h4 : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by
    field_simp
    ring
  have h5 : x / (1 - x₀) ≥ x / (1 - x) := by
    apply div_le_div_of_nonneg_left hx h2 (by linarith)
  calc Real.exp (-(x / (1 - x₀))) ≤ Real.exp (Real.log (1 - x)) := by
        apply Real.exp_le_exp.2
        linarith
    _ = 1 - x := Real.exp_log h1

/-- **The disc factor** (source l. 1837–1850, eq. (align57), by the route of R12a without the
exponent correction of `J_β`): for `β > 2` there is `C > 0` such that for all `λ > 0` and `r ≥ 4λ`,
`∫_{B̄(0, r/2)} e^{β g_λ} ≥ 𝒵_β λ^{2-β} exp(-C (λ/r)^{β-2})`. -/
theorem disc_factor_ge {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam r : ℝ, 0 < lam → 4 * lam ≤ r →
      dipoleConstant β hβ.le * lam ^ (2 - β) * Real.exp (-(C * (lam / r) ^ (β - 2))) ≤
        ∫ u in Metric.closedBall (0 : ℂ) (r / 2), Real.exp (β * smearedKernel lam u) := by
  have hZ := dipoleConstant_pos β hβ.le
  have hb : 0 < β - 2 := by linarith
  set Z := dipoleConstant β hβ.le with hZdef
  -- the relative tail at `r = 4 lam`
  set x₀ : ℝ := 2 * Real.pi * ((2 : ℝ) ^ (2 - β) / (β - 2)) / Z with hx₀def
  have hx₀lt : x₀ < 1 := by
    rw [hx₀def, div_lt_one hZ]
    exact two_pi_mul_two_rpow_div_lt_dipoleConstant hβ
  have hx₀pos : 0 < x₀ := by positivity
  set K : ℝ := 2 * Real.pi * (2 : ℝ) ^ (β - 2) / ((β - 2) * Z) with hK
  have hKpos : 0 < K := by positivity
  have h1x₀ : 0 < 1 - x₀ := by linarith
  refine ⟨K / (1 - x₀), div_pos hKpos h1x₀, fun lam r hlam hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have h2r : 2 * lam ≤ r / 2 := by linarith
  have hy0 : 0 ≤ (lam / r) ^ (β - 2) := by positivity
  -- the relative tail
  have hrpow : (r / 2) ^ (2 - β) = (2:ℝ) ^ (β - 2) * lam ^ (2 - β) * (lam / r) ^ (β - 2) := by
    rw [Real.div_rpow hlam.le hr0.le, Real.div_rpow hr0.le (by norm_num : (0:ℝ) ≤ 2),
      show 2 - β = -(β - 2) by ring, Real.rpow_neg hlam.le, Real.rpow_neg hr0.le,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    have h1 : lam ^ (β - 2) ≠ 0 := (Real.rpow_pos_of_pos hlam _).ne'
    have h2 : r ^ (β - 2) ≠ 0 := (Real.rpow_pos_of_pos hr0 _).ne'
    have h3 : (2:ℝ) ^ (β - 2) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    field_simp
  set y : ℝ := (lam / r) ^ (β - 2) with hy
  have hlamr : lam / r ≤ 1 / 4 := by
    rw [div_le_iff₀ hr0]
    linarith
  have hy4 : y ≤ (1 / 4 : ℝ) ^ (β - 2) :=
    Real.rpow_le_rpow (by positivity) hlamr hb.le
  have hquart : (1 / 4 : ℝ) ^ (β - 2) = ((2:ℝ) ^ (β - 2))⁻¹ ^ 2 := by
    rw [show (1 / 4 : ℝ) = ((2:ℝ)⁻¹) ^ 2 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul
      (by norm_num), mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast,
      Real.inv_rpow (by norm_num)]
  -- `x = K y` is the relative tail `T / A`
  set x : ℝ := K * y with hx
  have hx0 : 0 ≤ x := by positivity
  have hxx : x ≤ x₀ := by
    have h2b : (0 : ℝ) < (2:ℝ) ^ (β - 2) := Real.rpow_pos_of_pos (by norm_num) _
    have h22 : (2:ℝ) ^ (2 - β) = ((2:ℝ) ^ (β - 2))⁻¹ := by
      rw [show 2 - β = -(β - 2) by ring, Real.rpow_neg (by norm_num)]
    have : x ≤ K * ((2:ℝ) ^ (β - 2))⁻¹ ^ 2 := by
      rw [hx]
      exact mul_le_mul_of_nonneg_left (hy4.trans_eq hquart) hKpos.le
    refine this.trans_eq ?_
    rw [hx₀def, hK, h22]
    field_simp
  have hmain : Z * lam ^ (2 - β) * Real.exp (-(K / (1 - x₀) * y)) ≤
      ∫ u in Metric.ball (0 : ℂ) (r / 2), Real.exp (β * smearedKernel lam u) := by
    rw [integral_ball_exp_smearedKernel hβ hlam h2r, hrpow]
    have hA : 0 < Z * lam ^ (2 - β) := mul_pos hZ (Real.rpow_pos_of_pos hlam _)
    have hexp := exp_neg_div_le_one_sub hx0 hxx hx₀lt
    have hT : 2 * Real.pi * ((2:ℝ) ^ (β - 2) * lam ^ (2 - β) * y / (β - 2)) =
        Z * lam ^ (2 - β) * x := by
      rw [hx, hK]
      field_simp
    rw [hT]
    have : K / (1 - x₀) * y = x / (1 - x₀) := by
      rw [hx]
      ring
    rw [this]
    calc Z * lam ^ (2 - β) * Real.exp (-(x / (1 - x₀))) ≤ Z * lam ^ (2 - β) * (1 - x) :=
          mul_le_mul_of_nonneg_left hexp hA.le
      _ = Z * lam ^ (2 - β) - Z * lam ^ (2 - β) * x := by ring
  refine hmain.trans ?_
  refine setIntegral_mono_set (integrable_exp_smearedKernel hβ hlam).integrableOn
    (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le) ?_
  exact Filter.Eventually.of_forall Metric.ball_subset_closedBall

end TwoComponentCoulomb

end
