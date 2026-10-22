/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.IsolatedRadial
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# The pair factor `J_β(r)` of the lower bound (Proposition 4.1, Step 2)

Source: Proposition 4.1, Step 2 (l. 1828--1851), eqs. (minz3)
and (align57), following ruling R22 (with the correction `-A s²/r²` in the exponent).

For `r ≥ 4λ` the pair factor is
`J_β(r) = ∫_{B(0, r/2)} exp(β g_λ(u) - A |u|²/r²) du = ∫_0^{r/2} 2π s exp(β g_λ(s) - A s²/r²) ds`,
where the constant `A ≥ 0` comes from the energy bound (majof) of Step 1. For `β > 2` the source
proves `c_β ≤ J_β(r) / (𝒵_β λ^{2-β}) ≤ 1` and
`0 ≤ 𝒵_β λ^{2-β} - J_β(r) ≤ C_β 𝒵_β λ^{2-β} φ_β(r)`, hence (align57)
`log (J_β(r) / (𝒵_β λ^{2-β})) ≥ -C_β φ_β(r)`. The constants depend only on `β` and `A`.

* `pairFactor` : the pair factor `J_β(r)` (`minz3`).
* `pairFactor_pos` : `J_β(r) > 0`.
* `measurable_pairFactor`, `continuousOn_pairFactor` : regularity in `r`.
* `pairFactor_le` : `J_β(r) ≤ 𝒵_β λ^{2-β}` (drop the correction).
* `exists_pairFactor_ge` : `J_β(r) ≥ c_β 𝒵_β λ^{2-β}` (restrict to `B(0, 2λ)`).
* `exists_integral_closedBall_exp_mul_sq_le_of_two_lt` : the quadratic correction
  `∫_{|u| ≤ 4ρ} e^{β g_λ} (a(u)/ρ)² ≤ C λ^{2-β} φ_β(ρ)` for `β > 2`, for every `0 < λ ≤ ρ`
  (no smallness of `λ`), and `isolatedPhi_div_four_le` : `φ_β(r/4) ≤ 16 φ_β(r)`.
* `exists_sub_pairFactor_le` : the defect bound `𝒵_β λ^{2-β} - J_β(r) ≤ C 𝒵_β λ^{2-β} φ_β(r)`
  (the tail outside `B(0, r/2)` plus `1 - e^{-t} ≤ t`).
* `exists_log_pairFactor_ge` : (align57); `exists_pairFactor_ge_exp` : its exponential form
  `J_β(r) ≥ 𝒵_β λ^{2-β} exp(-C φ_β(r))`.
-/

public section

open MeasureTheory Set Filter Topology

namespace TwoComponentCoulomb

/-- The pair factor `J_β(r) = ∫_{B(0, r/2)} exp(β g_λ(u) − A |u|²/r²) du` of Step 2 (`minz3`);
in polar coordinates it is the source's `∫_0^{r/2} 2π s exp(β g_λ(s) − A s²/r²) ds`. -/
@[expose] noncomputable def pairFactor (β A lam r : ℝ) : ℝ :=
  ∫ u in Metric.ball (0 : ℂ) (r / 2), Real.exp (β * smearedKernel lam u - A * ‖u‖ ^ 2 / r ^ 2)

/-! ### The integrand -/

theorem continuous_pairFactor_integrand {β A lam r : ℝ} (hlam : 0 < lam) :
    Continuous fun u : ℂ => Real.exp (β * smearedKernel lam u - A * ‖u‖ ^ 2 / r ^ 2) :=
  (((continuous_smearedKernel hlam).const_mul β).sub
    (((continuous_norm.pow 2).const_mul A).div_const _)).rexp

theorem integrableOn_ball_pairFactor_integrand {β A lam r : ℝ} (hlam : 0 < lam) (t : ℝ) :
    IntegrableOn (fun u : ℂ => Real.exp (β * smearedKernel lam u - A * ‖u‖ ^ 2 / r ^ 2))
      (Metric.ball (0 : ℂ) t) :=
  ((continuous_pairFactor_integrand hlam).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) t)).mono_set Metric.ball_subset_closedBall

/-- A continuous positive function has positive integral over a disc of positive radius. -/
theorem setIntegral_ball_pos_of_continuous {f : ℂ → ℝ} (hf : Continuous f) (hpos : ∀ u, 0 < f u)
    {t : ℝ} (ht : 0 < t) : 0 < ∫ u in Metric.ball (0 : ℂ) t, f u := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support f ∩ Metric.ball (0 : ℂ) t = Metric.ball (0 : ℂ) t :=
      inter_eq_right.2 fun u _ => (hpos u).ne'
    rw [this]
    exact Metric.measure_ball_pos volume 0 ht
  · exact Eventually.of_forall fun u => (hpos u).le
  · exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) t)).mono_set
      Metric.ball_subset_closedBall

/-- `J_β(r) > 0` for `λ > 0` and `r > 0`. -/
theorem pairFactor_pos {β A lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) :
    0 < pairFactor β A lam r :=
  setIntegral_ball_pos_of_continuous (continuous_pairFactor_integrand hlam)
    (fun _ => Real.exp_pos _) (half_pos hr)

/-! ### The upper bound `J_β(r) ≤ 𝒵_β λ^{2-β}` -/

/-- `J_β(r) ≤ 𝒵_β λ^{2-β}` for `β > 2`, `A ≥ 0`, `λ > 0` (drop the correction and extend the
disc to the plane, eq. (3.20b)). -/
theorem pairFactor_le {β A lam r : ℝ} (hβ : 2 < β) (hA : 0 ≤ A) (hlam : 0 < lam) :
    pairFactor β A lam r ≤ dipoleConstant β hβ.le * lam ^ (2 - β) := by
  rw [← integral_exp_smearedKernel hβ hlam]
  calc pairFactor β A lam r
      ≤ ∫ u in Metric.ball (0 : ℂ) (r / 2), Real.exp (β * smearedKernel lam u) := by
        refine setIntegral_mono (integrableOn_ball_pairFactor_integrand hlam _)
          (integrable_exp_smearedKernel hβ hlam).integrableOn fun u => ?_
        exact Real.exp_le_exp.2 (sub_le_self _ (by positivity))
    _ ≤ ∫ u, Real.exp (β * smearedKernel lam u) :=
        setIntegral_le_integral (integrable_exp_smearedKernel hβ hlam)
          (Eventually.of_forall fun u => (Real.exp_pos _).le)

/-! ### The lower bound `J_β(r) ≥ c_β 𝒵_β λ^{2-β}` -/

/-- `J_β(r) ≥ c_β 𝒵_β λ^{2-β}` for `β > 2`, `A ≥ 0` and `r ≥ 4λ` (source l. 1837--1840, restricting
the radial integral to `[0, 2λ]`, where `A s²/r² ≤ A/4`). -/
theorem exists_pairFactor_ge {β : ℝ} (hβ : 2 < β) {A : ℝ} (hA : 0 ≤ A) :
    ∃ c > 0, ∀ lam r : ℝ, 0 < lam → 4 * lam ≤ r →
      c * (dipoleConstant β hβ.le * lam ^ (2 - β)) ≤ pairFactor β A lam r := by
  set Z := dipoleConstant β hβ.le with hZdef
  have hZ : 0 < Z := dipoleConstant_pos β hβ.le
  set T : ℝ := 2 * Real.pi * ((2 : ℝ) ^ (2 - β) / (β - 2)) with hT
  -- `Z - T` is the mass of `e^{β g_1}` in `B(0, 2)`
  have hZT : 0 < Z - T := by
    have h := integral_ball_exp_smearedKernel (β := β) (lam := 1) (t := 2) hβ one_pos
      (by norm_num)
    rw [Real.one_rpow, mul_one] at h
    rw [← h]
    exact setIntegral_ball_pos_of_continuous (continuous_exp_mul_smearedKernel one_pos)
      (fun _ => Real.exp_pos _) two_pos
  refine ⟨Real.exp (-(A / 4)) * ((Z - T) / Z), by positivity, fun lam r hlam hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have h2 : 2 * lam ≤ r / 2 := by linarith
  have hcore : ∫ u in Metric.ball (0 : ℂ) (2 * lam), Real.exp (β * smearedKernel lam u) =
      lam ^ (2 - β) * (Z - T) := by
    rw [integral_ball_exp_smearedKernel hβ hlam le_rfl, Real.mul_rpow (by norm_num) hlam.le, hT]
    ring
  calc Real.exp (-(A / 4)) * ((Z - T) / Z) * (Z * lam ^ (2 - β))
      = ∫ u in Metric.ball (0 : ℂ) (2 * lam),
          Real.exp (-(A / 4)) * Real.exp (β * smearedKernel lam u) := by
        rw [integral_const_mul, hcore]
        field_simp
    _ ≤ ∫ u in Metric.ball (0 : ℂ) (2 * lam),
          Real.exp (β * smearedKernel lam u - A * ‖u‖ ^ 2 / r ^ 2) := by
        refine setIntegral_mono_on
          ((continuous_exp_mul_smearedKernel hlam).const_mul _ |>.continuousOn.integrableOn_compact
            (isCompact_closedBall (0 : ℂ) (2 * lam)) |>.mono_set Metric.ball_subset_closedBall)
          (integrableOn_ball_pairFactor_integrand hlam _) measurableSet_ball fun u hu => ?_
        have hu' : ‖u‖ ≤ r / 2 := (mem_ball_zero_iff.1 hu).le.trans h2
        have hsq : ‖u‖ ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu' 2
        have hq : A * ‖u‖ ^ 2 / r ^ 2 ≤ A / 4 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hsq hA]
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith)
    _ ≤ pairFactor β A lam r :=
        setIntegral_mono_set (integrableOn_ball_pairFactor_integrand hlam _)
          (Eventually.of_forall fun u => (Real.exp_pos _).le)
          (Metric.ball_subset_ball h2).eventuallyLE

/-! ### The quadratic correction for `β > 2` -/

/-- **Quadratic correction** for `β > 2` (source l. 1305--1309, used at l. 1842--1847): for
`0 < λ ≤ ρ`, `∫_{|u| ≤ 4ρ} e^{β g_λ(u)} (a(u)/ρ)² du ≤ C λ^{2-β} φ_β(ρ)`, with
`a(u) = (|u|/4) ∨ λ`. This is the `β > 2` part of `exists_integral_closedBall_exp_mul_sq_le`, whose
hypothesis `λ ≤ e^{-1}` is needed only for `β = 2`; the proof is the same. -/
theorem exists_integral_closedBall_exp_mul_sq_le_of_two_lt {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ρ : ℝ, 0 < lam → lam ≤ ρ →
      ∫ u in Metric.closedBall (0 : ℂ) (4 * ρ),
          Real.exp (β * smearedKernel lam u) * (displacementScale lam u / ρ) ^ 2 ≤
        C * lam ^ (2 - β) * isolatedPhi β hβ.le lam ρ := by
  obtain ⟨K, hK0, hK⟩ := exists_integral_closedBall_exp_mul_pow_le (β := β) (κ := 2)
    (by linarith) zero_le_two
  have hK' : ∀ lam ρ : ℝ, 0 < lam → lam ≤ ρ →
      ∫ u in Metric.closedBall (0 : ℂ) (4 * ρ),
          Real.exp (β * smearedKernel lam u) * (displacementScale lam u / ρ) ^ 2 ≤
        K * lam ^ (2 - β) * (lam / ρ) ^ 2 +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ (3 - β) := by
    intro lam ρ hlam hρ
    have h := hK lam ρ hlam hρ
    simp only [Real.rpow_two, Real.rpow_neg (lt_of_lt_of_le hlam hρ).le] at h
    rwa [show (1 : ℝ) - β + 2 = 3 - β by ring] at h
  rcases lt_or_ge β 4 with h4 | h4
  · -- `2 < β < 4`
    refine ⟨K + 2 * Real.pi * 4 ^ (4 - β) / (4 - β), by
      have : 0 < 4 - β := sub_pos.2 h4
      positivity, fun lam ρ hlam hρ => ?_⟩
    have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
    have hq0 : 0 < lam / ρ := by positivity
    have hq1 : lam / ρ ≤ 1 := (div_le_one hρ0).2 hρ
    have hp : isolatedPhi β hβ.le lam ρ = (lam / ρ) ^ (β - 2) := by
      simp [isolatedPhi, hβ.ne', h4]
    rw [hp]
    have i1 : (lam / ρ) ^ 2 ≤ (lam / ρ) ^ (β - 2) := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (by linarith only [h4])
    have i2 : ∫ y in (2 * lam)..(4 * ρ), y ^ (3 - β) ≤ (4 * ρ) ^ (4 - β) / (4 - β) := by
      have := intervalIntegral_rpow_le_of_neg_one_lt (p := 3 - β) (s := 2 * lam) (t := 4 * ρ)
        (by linarith only [h4]) (by positivity)
      rwa [show 3 - β + 1 = 4 - β by ring] at this
    have i3 : (ρ ^ 2)⁻¹ * (4 * ρ) ^ (4 - β) = 4 ^ (4 - β) * ρ ^ (2 - β) := by
      rw [Real.mul_rpow (by norm_num) hρ0.le, show 4 - β = 2 + (2 - β) by ring,
        Real.rpow_add hρ0, Real.rpow_two]
      field_simp
    have i4 : lam ^ (2 - β) * (lam / ρ) ^ (β - 2) = ρ ^ (2 - β) := by
      have := rpow_neg_mul_div_rpow hlam hρ0 (β - 2)
      rwa [neg_sub] at this
    calc _ ≤ K * lam ^ (2 - β) * (lam / ρ) ^ 2 +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ (3 - β) := hK' lam ρ hlam hρ
      _ ≤ K * lam ^ (2 - β) * (lam / ρ) ^ (β - 2) +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ((4 * ρ) ^ (4 - β) / (4 - β)) :=
          add_le_add (mul_le_mul_of_nonneg_left i1 (by positivity))
            (mul_le_mul_of_nonneg_left i2 (by positivity))
      _ = (K + 2 * Real.pi * 4 ^ (4 - β) / (4 - β)) * (lam ^ (2 - β) * (lam / ρ) ^ (β - 2)) := by
          linear_combination (2 * Real.pi / (4 - β)) * i3 -
            (2 * Real.pi * 4 ^ (4 - β) / (4 - β)) * i4
      _ = _ := by ring
  rcases h4.eq_or_lt with h4 | h4
  · -- `β = 4`
    subst h4
    refine ⟨K + 2 * Real.pi, by positivity, fun lam ρ hlam hρ => ?_⟩
    have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
    have hL : 0 ≤ Real.log (ρ / lam) := Real.log_nonneg ((one_le_div hlam).2 hρ)
    have hp : isolatedPhi 4 hβ.le lam ρ = (lam / ρ) ^ 2 * (1 + Real.log (ρ / lam)) := by
      simp [isolatedPhi]
    have hlog : ∫ y in (2 * lam)..(4 * ρ), y ^ ((3 : ℝ) - 4) ≤ 1 + Real.log (ρ / lam) := by
      rw [show (3 : ℝ) - 4 = -1 by norm_num, intervalIntegral_rpow_neg_one (by positivity)
        (by positivity), show 4 * ρ / (2 * lam) = 2 * (ρ / lam) by field_simp; ring,
        Real.log_mul (by norm_num) (by positivity)]
      exact add_le_add_left ((Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)) _
    have e1 : lam ^ ((2 : ℝ) - 4) = (lam ^ 2)⁻¹ := by
      rw [show (2 : ℝ) - 4 = -(2 : ℝ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_two]
    have e2 : (ρ ^ 2)⁻¹ = (lam ^ 2)⁻¹ * (lam / ρ) ^ 2 := by field_simp
    rw [hp]
    calc _ ≤ K * lam ^ ((2 : ℝ) - 4) * (lam / ρ) ^ 2 +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ ((3 : ℝ) - 4) :=
          hK' lam ρ hlam hρ
      _ ≤ K * lam ^ ((2 : ℝ) - 4) * ((lam / ρ) ^ 2 * (1 + Real.log (ρ / lam))) +
          2 * Real.pi * (ρ ^ 2)⁻¹ * (1 + Real.log (ρ / lam)) := by
          have hA : 0 ≤ K * lam ^ ((2 : ℝ) - 4) * (lam / ρ) ^ 2 := by positivity
          have : K * lam ^ ((2 : ℝ) - 4) * (lam / ρ) ^ 2 ≤
              K * lam ^ ((2 : ℝ) - 4) * ((lam / ρ) ^ 2 * (1 + Real.log (ρ / lam))) := by
            rw [← mul_assoc]
            exact le_mul_of_one_le_right hA (le_add_of_nonneg_right hL)
          have h2 : 2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ ((3 : ℝ) - 4) ≤
              2 * Real.pi * (ρ ^ 2)⁻¹ * (1 + Real.log (ρ / lam)) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
          exact add_le_add this h2
      _ = (K + 2 * Real.pi) * lam ^ ((2 : ℝ) - 4) * ((lam / ρ) ^ 2 * (1 + Real.log (ρ / lam))) := by
          rw [e1, e2]
          ring
  · -- `β > 4`
    have hb : 0 < β - 4 := sub_pos.2 h4
    refine ⟨K + 2 * Real.pi * 2 ^ (4 - β) / (β - 4), by positivity, fun lam ρ hlam hρ => ?_⟩
    have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
    have hp : isolatedPhi β hβ.le lam ρ = (lam / ρ) ^ 2 := by
      simp [isolatedPhi, hβ.ne', not_lt.2 h4.le, h4.ne']
    rw [hp]
    have i2 : ∫ y in (2 * lam)..(4 * ρ), y ^ (3 - β) ≤ (2 * lam) ^ (4 - β) / (β - 4) := by
      have := intervalIntegral_rpow_le_of_lt_neg_one (p := 3 - β) (s := 2 * lam) (t := 4 * ρ)
        (by linarith only [h4]) (by positivity) (by linarith only [hlam, hρ])
      rwa [show 3 - β + 1 = 4 - β by ring, show -(4 - β) = β - 4 by ring] at this
    have i3 : (ρ ^ 2)⁻¹ * (2 * lam) ^ (4 - β) = 2 ^ (4 - β) * (lam ^ (2 - β) * (lam / ρ) ^ 2) := by
      rw [Real.mul_rpow (by norm_num) hlam.le, show 4 - β = 2 + (2 - β) by ring,
        Real.rpow_add hlam, Real.rpow_two]
      field_simp
    calc _ ≤ K * lam ^ (2 - β) * (lam / ρ) ^ 2 +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ (3 - β) := hK' lam ρ hlam hρ
      _ ≤ K * lam ^ (2 - β) * (lam / ρ) ^ 2 +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ((2 * lam) ^ (4 - β) / (β - 4)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left i2 (by positivity))
      _ = (K + 2 * Real.pi * 2 ^ (4 - β) / (β - 4)) * (lam ^ (2 - β) * (lam / ρ) ^ 2) := by
          linear_combination (2 * Real.pi / (β - 4)) * i3
      _ = _ := by ring

/-- For `β > 2` and `r ≥ 4λ`, `φ_β(r/4) ≤ 16 φ_β(r)`. -/
theorem isolatedPhi_div_four_le {β : ℝ} (hβ : 2 < β) {lam r : ℝ} (hlam : 0 < lam)
    (hr : 4 * lam ≤ r) :
    isolatedPhi β hβ.le lam (r / 4) ≤ 16 * isolatedPhi β hβ.le lam r := by
  have hr0 : 0 < r := by linarith
  have hq : lam / (r / 4) = 4 * (lam / r) := by field_simp
  have hq0 : 0 ≤ lam / r := by positivity
  unfold isolatedPhi
  split_ifs with h h4 h4'
  · exact absurd h hβ.ne'
  · rw [hq, Real.mul_rpow (by norm_num) hq0]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc (4 : ℝ) ^ (β - 2) ≤ (4 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [h4])
      _ = 16 := by norm_num
  · rw [hq]
    have hlog : Real.log (r / 4 / lam) ≤ Real.log (r / lam) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith) hlam.le)
    have : (4 * (lam / r)) ^ 2 = 16 * (lam / r) ^ 2 := by ring
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith only [hlog]) (sq_nonneg _)) (by norm_num)
  · rw [hq]
    exact le_of_eq (by ring)

/-! ### The defect bound -/

/-- **Defect bound** (source l. 1842--1847): for `β > 2` and `A ≥ 0` there is `C > 0` with
`0 ≤ 𝒵_β λ^{2-β} - J_β(r) ≤ C 𝒵_β λ^{2-β} φ_β(r)` for all `λ > 0`, `r ≥ 4λ`. The defect is the
exact tail `2π (r/2)^{2-β}/(β - 2)` of `e^{β g_λ}` outside `B(0, r/2)` plus
`∫_{B(0,r/2)} e^{β g_λ} (1 - e^{-A|u|²/r²}) ≤ (A/r²) ∫_{B(0,r/2)} |u|² e^{β g_λ}`. -/
theorem exists_sub_pairFactor_le {β : ℝ} (hβ : 2 < β) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C > 0, ∀ lam r : ℝ, 0 < lam → 4 * lam ≤ r →
      dipoleConstant β hβ.le * lam ^ (2 - β) - pairFactor β A lam r ≤
        C * (dipoleConstant β hβ.le * lam ^ (2 - β)) * isolatedPhi β hβ.le lam r := by
  obtain ⟨Cq, hCq, hq⟩ := exists_integral_closedBall_exp_mul_sq_le_of_two_lt hβ
  set Z := dipoleConstant β hβ.le with hZdef
  have hZ : 0 < Z := dipoleConstant_pos β hβ.le
  have hb : 0 < β - 2 := by linarith
  refine ⟨2 * Real.pi * 2 ^ (β - 2) / ((β - 2) * Z) + 16 * A * Cq / Z, by positivity,
    fun lam r hlam hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hlr : lam ≤ r := by linarith
  have hρ : lam ≤ r / 4 := by linarith
  have h2 : 2 * lam ≤ r / 2 := by linarith
  have hφ0 : 0 ≤ isolatedPhi β hβ.le lam r := isolatedPhi_nonneg hβ.le hlam hlr
  set φ := isolatedPhi β hβ.le lam r with hφdef
  have hfi : Integrable fun u : ℂ => Real.exp (β * smearedKernel lam u) :=
    integrable_exp_smearedKernel hβ hlam
  -- the split `𝒵_β λ^{2-β} - J = tail + ∫_B e^{β g_λ} (1 - e^{-A|u|²/r²})`
  have hsplit : Z * lam ^ (2 - β) - pairFactor β A lam r =
      2 * Real.pi * ((r / 2) ^ (2 - β) / (β - 2)) +
        ∫ u in Metric.ball (0 : ℂ) (r / 2), (Real.exp (β * smearedKernel lam u) -
          Real.exp (β * smearedKernel lam u - A * ‖u‖ ^ 2 / r ^ 2)) := by
    rw [integral_sub hfi.integrableOn (integrableOn_ball_pairFactor_integrand hlam _),
      integral_ball_exp_smearedKernel hβ hlam h2, pairFactor]
    ring
  -- the tail
  have htail : 2 * Real.pi * ((r / 2) ^ (2 - β) / (β - 2)) ≤
      2 * Real.pi * 2 ^ (β - 2) / ((β - 2) * Z) * (Z * lam ^ (2 - β)) * φ := by
    have e : (r / 2) ^ (2 - β) = 2 ^ (β - 2) * (lam ^ (2 - β) * (lam / r) ^ (β - 2)) := by
      have i4 : lam ^ (2 - β) * (lam / r) ^ (β - 2) = r ^ (2 - β) := by
        have := rpow_neg_mul_div_rpow hlam hr0 (β - 2)
        rwa [neg_sub] at this
      rw [i4, Real.div_rpow hr0.le (by norm_num), show 2 - β = -(β - 2) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    have hφ := rpow_div_le_isolatedPhi hβ.le hβ hlam hlr
    rw [e]
    have : 2 * Real.pi * 2 ^ (β - 2) / ((β - 2) * Z) * (Z * lam ^ (2 - β)) * φ =
        2 * Real.pi * (2 ^ (β - 2) * (lam ^ (2 - β) * φ) / (β - 2)) := by
      field_simp
    rw [this]
    gcongr
  -- the correction
  have hdef : ∫ u in Metric.ball (0 : ℂ) (r / 2), (Real.exp (β * smearedKernel lam u) -
        Real.exp (β * smearedKernel lam u - A * ‖u‖ ^ 2 / r ^ 2)) ≤
      16 * A * Cq / Z * (Z * lam ^ (2 - β)) * φ := by
    have hcq : Continuous fun u : ℂ =>
        Real.exp (β * smearedKernel lam u) * (displacementScale lam u / (r / 4)) ^ 2 :=
      (continuous_exp_mul_smearedKernel hlam).mul
        (((continuous_displacementScale lam).div_const _).pow 2)
    calc ∫ u in Metric.ball (0 : ℂ) (r / 2), (Real.exp (β * smearedKernel lam u) -
          Real.exp (β * smearedKernel lam u - A * ‖u‖ ^ 2 / r ^ 2))
        ≤ ∫ u in Metric.ball (0 : ℂ) (r / 2),
            A * (Real.exp (β * smearedKernel lam u) *
              (displacementScale lam u / (r / 4)) ^ 2) := by
          refine setIntegral_mono
            (hfi.integrableOn.sub (integrableOn_ball_pairFactor_integrand hlam _))
            ((hcq.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) (r / 2))).mono_set
              Metric.ball_subset_closedBall |>.const_mul A) fun u => ?_
          have ht : A * ‖u‖ ^ 2 / r ^ 2 ≤ A * (displacementScale lam u / (r / 4)) ^ 2 := by
            have h1 : ‖u‖ / r ≤ displacementScale lam u / (r / 4) := by
              rw [div_le_div_iff₀ hr0 (by positivity)]
              have := le_max_left (‖u‖ / 4) lam
              unfold displacementScale
              nlinarith
            have h2 : (‖u‖ / r) ^ 2 ≤ (displacementScale lam u / (r / 4)) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h1 2
            rw [mul_div_assoc, ← div_pow]
            exact mul_le_mul_of_nonneg_left h2 hA
          have hexp := Real.add_one_le_exp (-(A * ‖u‖ ^ 2 / r ^ 2))
          have hf0 := Real.exp_pos (β * smearedKernel lam u)
          rw [sub_eq_add_neg (β * smearedKernel lam u), Real.exp_add]
          nlinarith [mul_le_mul_of_nonneg_left ht hf0.le]
      _ = A * ∫ u in Metric.ball (0 : ℂ) (r / 2),
            Real.exp (β * smearedKernel lam u) * (displacementScale lam u / (r / 4)) ^ 2 :=
          integral_const_mul _ _
      _ ≤ A * ∫ u in Metric.closedBall (0 : ℂ) (4 * (r / 4)),
            Real.exp (β * smearedKernel lam u) * (displacementScale lam u / (r / 4)) ^ 2 := by
          refine mul_le_mul_of_nonneg_left (setIntegral_mono_set
            (hcq.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
            (Eventually.of_forall fun u => by positivity) ?_) hA
          refine (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ?_)
            ).eventuallyLE
          linarith
      _ ≤ A * (Cq * lam ^ (2 - β) * isolatedPhi β hβ.le lam (r / 4)) :=
          mul_le_mul_of_nonneg_left (hq lam (r / 4) hlam hρ) hA
      _ ≤ A * (Cq * lam ^ (2 - β) * (16 * φ)) := by
          gcongr
          exact isolatedPhi_div_four_le hβ hlam hr
      _ = 16 * A * Cq / Z * (Z * lam ^ (2 - β)) * φ := by
          field_simp
  rw [hsplit]
  calc _ ≤ 2 * Real.pi * 2 ^ (β - 2) / ((β - 2) * Z) * (Z * lam ^ (2 - β)) * φ +
        16 * A * Cq / Z * (Z * lam ^ (2 - β)) * φ := add_le_add htail hdef
    _ = _ := by ring

/-! ### (align57) -/

/-- **(align57)** (source l. 1848--1850): for `β > 2` and `A ≥ 0` there is `C > 0` with
`log (J_β(r) / (𝒵_β λ^{2-β})) ≥ -C φ_β(r)` for all `λ > 0`, `r ≥ 4λ`. If the relative defect
`x = 1 - J_β(r) / (𝒵_β λ^{2-β}) ≤ C₁ φ_β(r)` is at most `1/2`, then `log (1 - x) ≥ -2x`; otherwise
`2 C₁ φ_β(r) > 1` and the lower bound `J_β(r) ≥ c 𝒵_β λ^{2-β}` gives `log ≥ log c`. -/
theorem exists_log_pairFactor_ge {β : ℝ} (hβ : 2 < β) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C > 0, ∀ lam r : ℝ, 0 < lam → 4 * lam ≤ r →
      -(C * isolatedPhi β hβ.le lam r) ≤
        Real.log (pairFactor β A lam r / (dipoleConstant β hβ.le * lam ^ (2 - β))) := by
  -- `log (1 - x) ≥ -2x` for `0 ≤ x ≤ 1/2`
  have hlog1 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → -(2 * x) ≤ Real.log (1 - x) := by
    intro x hx hx2
    have h1 : 0 < 1 - x := by linarith
    have h3 := Real.one_sub_inv_le_log_of_pos h1
    have h4 : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by
      field_simp
      ring
    have h5 : x / (1 - x) ≤ 2 * x := by
      rw [div_le_iff₀ h1]
      nlinarith
    linarith
  obtain ⟨c, hc, hcJ⟩ := exists_pairFactor_ge hβ hA
  obtain ⟨C₁, hC₁, hdef⟩ := exists_sub_pairFactor_le hβ hA
  have hZ := dipoleConstant_pos β hβ.le
  set L := -Real.log (min c 1) with hL
  have hL0 : 0 ≤ L := by
    rw [hL, neg_nonneg]
    exact Real.log_nonpos (le_min hc.le zero_le_one) (min_le_right _ _)
  refine ⟨2 * C₁ * (1 + L), by positivity, fun lam r hlam hr => ?_⟩
  set M := dipoleConstant β hβ.le * lam ^ (2 - β) with hM
  have hM0 : 0 < M := mul_pos hZ (Real.rpow_pos_of_pos hlam _)
  set J := pairFactor β A lam r with hJ
  set φ := isolatedPhi β hβ.le lam r with hφ
  have hφ0 : 0 ≤ φ := isolatedPhi_nonneg hβ.le hlam (by linarith)
  set x := (M - J) / M with hx
  have hJM : J / M = 1 - x := by
    rw [hx, sub_div, div_self hM0.ne']
    ring
  have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.2 (pairFactor_le hβ hA hlam)) hM0.le
  have hxφ : x ≤ C₁ * φ := by
    rw [hx, div_le_iff₀ hM0]
    have := hdef lam r hlam hr
    linarith
  have hC₁φ : 0 ≤ C₁ * φ := mul_nonneg hC₁.le hφ0
  rcases le_or_gt x (1 / 2) with hx2 | hx2
  · rw [hJM]
    calc -(2 * C₁ * (1 + L) * φ) ≤ -(2 * (C₁ * φ)) := by
          nlinarith [mul_nonneg hC₁φ hL0]
      _ ≤ -(2 * x) := by linarith
      _ ≤ Real.log (1 - x) := hlog1 x hx0 hx2
  · have hφ1 : 1 ≤ 2 * (C₁ * φ) := by linarith
    have hcJ' : min c 1 ≤ J / M := by
      rw [le_div_iff₀ hM0]
      exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hM0.le).trans (hcJ lam r hlam hr)
    have hlog : -L ≤ Real.log (J / M) := by
      rw [hL, neg_neg]
      exact Real.log_le_log (lt_min hc one_pos) hcJ'
    calc -(2 * C₁ * (1 + L) * φ) ≤ -L := by
          nlinarith [mul_le_mul_of_nonneg_left hφ1 (by linarith : (0 : ℝ) ≤ 1 + L)]
      _ ≤ _ := hlog

/-- Exponential form of (align57): `J_β(r) ≥ 𝒵_β λ^{2-β} exp(-C φ_β(r))` for `β > 2`, `A ≥ 0`,
`λ > 0` and `r ≥ 4λ`. -/
theorem exists_pairFactor_ge_exp {β : ℝ} (hβ : 2 < β) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C > 0, ∀ lam r : ℝ, 0 < lam → 4 * lam ≤ r →
      dipoleConstant β hβ.le * lam ^ (2 - β) * Real.exp (-(C * isolatedPhi β hβ.le lam r)) ≤
        pairFactor β A lam r := by
  obtain ⟨C, hC, h⟩ := exists_log_pairFactor_ge hβ hA
  refine ⟨C, hC, fun lam r hlam hr => ?_⟩
  have hM0 : 0 < dipoleConstant β hβ.le * lam ^ (2 - β) :=
    mul_pos (dipoleConstant_pos β hβ.le) (Real.rpow_pos_of_pos hlam _)
  have hJ : 0 < pairFactor β A lam r := pairFactor_pos hlam (by linarith)
  have := Real.exp_le_exp.2 (h lam r hlam hr)
  rw [Real.exp_log (div_pos hJ hM0), le_div_iff₀ hM0] at this
  rw [mul_comm]
  exact this

/-! ### Regularity in `r` -/

/-- `r ↦ J_β(r)` is measurable (for `λ > 0`). -/
theorem measurable_pairFactor {β A lam : ℝ} (hlam : 0 < lam) :
    Measurable fun r : ℝ => pairFactor β A lam r := by
  set F : ℝ × ℂ → ℝ := fun p => {q : ℝ × ℂ | ‖q.2‖ < q.1 / 2}.indicator
    (fun q => Real.exp (β * smearedKernel lam q.2 - A * ‖q.2‖ ^ 2 / q.1 ^ 2)) p with hF
  have hFm : StronglyMeasurable F := by
    refine Measurable.stronglyMeasurable (Measurable.indicator ?_ ?_)
    · exact Real.measurable_exp.comp
        ((((continuous_smearedKernel hlam).measurable.comp measurable_snd).const_mul β).sub
          (((measurable_snd.norm.pow_const 2).const_mul A).div (measurable_fst.pow_const 2)))
    · exact measurableSet_lt measurable_snd.norm (measurable_fst.div_const 2)
  have h : (fun r : ℝ => pairFactor β A lam r) = fun r => ∫ u, F (r, u) := by
    funext r
    rw [pairFactor, ← integral_indicator measurableSet_ball]
    congr 1
    funext u
    simp only [hF, indicator, mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
  rw [h]
  exact (hFm.integral_prod_right' (ν := volume)).measurable

/-- `r ↦ J_β(r)` is continuous on `(0, ∞)` (for `λ > 0`), by dominated convergence: the boundary
circle `|u| = r₀/2` is a null set. -/
theorem continuousOn_pairFactor {β A lam : ℝ} (hlam : 0 < lam) :
    ContinuousOn (fun r : ℝ => pairFactor β A lam r) (Ioi 0) := by
  intro r₀ hr₀
  have hr₀ : 0 < r₀ := hr₀
  refine ContinuousAt.continuousWithinAt ?_
  set g : ℝ → ℂ → ℝ := fun r u => Real.exp (β * smearedKernel lam u - A * ‖u‖ ^ 2 / r ^ 2)
    with hg
  have h : (fun r : ℝ => pairFactor β A lam r) =
      fun r => ∫ u, (Metric.ball (0 : ℂ) (r / 2)).indicator (g r) u := by
    funext r
    rw [pairFactor, integral_indicator measurableSet_ball]
  rw [h]
  have hgc : Continuous fun u : ℂ => Real.exp (β * smearedKernel lam u + |A| / 4) :=
    (((continuous_smearedKernel hlam).const_mul β).add continuous_const).rexp
  refine continuousAt_of_dominated (bound := (Metric.ball (0 : ℂ) r₀).indicator
    fun u => Real.exp (β * smearedKernel lam u + |A| / 4)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun r =>
      ((continuous_pairFactor_integrand hlam).measurable.indicator
        measurableSet_ball).aestronglyMeasurable
  · have hmem : Ioo 0 (2 * r₀) ∈ 𝓝 r₀ := Ioo_mem_nhds hr₀ (by linarith)
    filter_upwards [hmem] with r hr
    refine Eventually.of_forall fun u => ?_
    by_cases hu : u ∈ Metric.ball (0 : ℂ) (r / 2)
    · have hu' : ‖u‖ < r / 2 := mem_ball_zero_iff.1 hu
      have hu0 : u ∈ Metric.ball (0 : ℂ) r₀ := mem_ball_zero_iff.2 (by linarith [hr.2])
      rw [indicator_of_mem hu, indicator_of_mem hu0, Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.2
      have hr0 : 0 < r := hr.1
      have hsq : ‖u‖ ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu'.le 2
      have h1 : |A * ‖u‖ ^ 2 / r ^ 2| ≤ |A| / 4 := by
        rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg ‖u‖), abs_of_pos (by positivity : 0 < r ^ 2),
          div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hsq (abs_nonneg A)]
      linarith [neg_abs_le (A * ‖u‖ ^ 2 / r ^ 2)]
    · rw [indicator_of_notMem hu, norm_zero]
      exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) u
  · exact ((hgc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) r₀)).mono_set
      Metric.ball_subset_closedBall).integrable_indicator measurableSet_ball
  · have hs : volume (Metric.sphere (0 : ℂ) (r₀ / 2)) = 0 :=
      Measure.addHaar_sphere volume (0 : ℂ) (r₀ / 2)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hs] with u hu
    have hne : ‖u‖ ≠ r₀ / 2 := fun h => hu (mem_sphere_zero_iff_norm.2 h)
    rcases hne.lt_or_gt with hlt | hgt
    · have hev : (fun r => (Metric.ball (0 : ℂ) (r / 2)).indicator (g r) u) =ᶠ[𝓝 r₀]
          fun r => g r u := by
        have : {r : ℝ | ‖u‖ < r / 2} ∈ 𝓝 r₀ :=
          (isOpen_lt continuous_const (continuous_id.div_const 2)).mem_nhds hlt
        filter_upwards [this] with r hr
        exact indicator_of_mem (mem_ball_zero_iff.2 hr) _
      have hc : ContinuousAt (fun r : ℝ => g r u) r₀ :=
        (continuousAt_const.sub (continuousAt_const.div (continuousAt_id.pow 2)
          (pow_ne_zero 2 hr₀.ne'))).rexp
      exact hc.congr hev.symm
    · have hev : (fun r => (Metric.ball (0 : ℂ) (r / 2)).indicator (g r) u) =ᶠ[𝓝 r₀]
          fun _ => (0 : ℝ) := by
        have : {r : ℝ | r / 2 < ‖u‖} ∈ 𝓝 r₀ :=
          (isOpen_lt (continuous_id.div_const 2) continuous_const).mem_nhds hgt
        filter_upwards [this] with r hr
        exact indicator_of_notMem (fun h => by linarith [mem_ball_zero_iff.1 h]) _
      exact continuousAt_const.congr hev.symm

end TwoComponentCoulomb

end
