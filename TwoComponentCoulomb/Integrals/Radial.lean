/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.SmearedKernel
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Radial integrals of the smeared kernel (the constant `𝒵_β`)

Source l. 188–198 (the definition of μ_β, `def:Cbeta`), l. 816–825 (the planar pair-mass identity) and l. 1357–1362 (the
tails of `μ_β` used in (eq:u bound)).

* `integral_comp_norm_complex`, `integrable_comp_norm_complex_iff` : polar coordinates for radial
  functions on `ℂ`, `∫ f(|x|) dx = 2π ∫₀^∞ r f(r) dr`.
* `integrableOn_exp_smearedKernel_one` : for `β > 2` the density `exp(β g₁(r)) r` of `μ_β` is
  integrable on `(0, ∞)`, since `g₁(r) = -log r` for `r ≥ 2`.
* `integral_Ici_exp_smearedKernel_one` : the explicit tail `∫_s^∞ exp(β g₁(r)) r dr = s^{2-β}/(β-2)`
  for `s ≥ 2`.
* `dipoleConstant_pos` : `𝒵_β > 0` for `β ≥ 2` (source l. 199).
* `integrable_exp_smearedKernel`, `integral_exp_smearedKernel` : the planar pair-mass identity,
  `∫_{ℝ²} exp(β g_λ(u)) du = 𝒵_β λ^{2-β}` for `β > 2`, `λ > 0`.
* `integral_ball_exp_smearedKernel` and `exists_integral_ball_exp_smearedKernel_ge` : the same
  integral over the disc `B(0, t)`, `t ≥ 2λ`, with the exact missing tail
  `2π t^{2-β}/(β-2)`, i.e. a relative defect `C_β (λ/t)^{β-2}`.
-/

public section

open MeasureTheory Set

namespace TwoComponentCoulomb

/-! ### Polar coordinates for radial functions on `ℂ` -/

/-- Integration of a radial function on `ℂ`: `∫ f(|x|) dx = 2π ∫₀^∞ r f(r) dr`. -/
theorem integral_comp_norm_complex (f : ℝ → ℝ) :
    ∫ x : ℂ, f ‖x‖ = 2 * Real.pi * ∫ y in Ioi (0 : ℝ), y * f y := by
  rw [integral_fun_norm_addHaar (volume : Measure ℂ) f]
  simp only [Complex.finrank_real_complex, Measure.real, Complex.volume_ball, smul_eq_mul]
  simp
  ring

/-- Integrability of a radial function on `ℂ` in polar coordinates. -/
theorem integrable_comp_norm_complex_iff (f : ℝ → ℝ) :
    Integrable (fun x : ℂ => f ‖x‖) ↔ IntegrableOn (fun y : ℝ => y * f y) (Ioi 0) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ) (f := f)]
  simp [Complex.finrank_real_complex]

/-! ### The profile `exp(β g_λ)` -/

/-- `g_λ(r) = -log r` for real `r ≥ 2λ`. -/
theorem smearedKernel_ofReal_of_le {lam : ℝ} (hlam : 0 < lam) {r : ℝ} (hr : 2 * lam ≤ r) :
    smearedKernel lam (r : ℂ) = -Real.log r := by
  have h : 2 * lam ≤ ‖(r : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact hr
  rw [smearedKernel_eq_logKernel hlam h]
  simp only [logKernel, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ r)]

/-- Outside `B(0, 2λ)` the radial profile is `exp(β g_λ(r)) r = r^{1-β}`. -/
theorem exp_mul_smearedKernel_mul_of_le (β : ℝ) {lam : ℝ} (hlam : 0 < lam) {r : ℝ}
    (hr : 2 * lam ≤ r) :
    Real.exp (β * smearedKernel lam (r : ℂ)) * r = r ^ (1 - β) := by
  have hr0 : 0 < r := by linarith
  rw [smearedKernel_ofReal_of_le hlam hr, Real.rpow_sub hr0, Real.rpow_one,
    Real.rpow_def_of_pos hr0, div_eq_mul_inv, ← Real.exp_neg, mul_comm r _]
  congr 2
  ring

/-- Scaling along a ray: `exp(β g_λ(y)) = λ^{-β} exp(β g_1(y / λ))`. -/
theorem exp_mul_smearedKernel_ofReal_eq {lam : ℝ} (hlam : 0 < lam) (β y : ℝ) :
    Real.exp (β * smearedKernel lam (y : ℂ)) =
      lam ^ (-β) * Real.exp (β * smearedKernel 1 ((lam⁻¹ * y : ℝ) : ℂ)) := by
  rw [smearedKernel_eq_logKernel_add hlam]
  have : ((y : ℂ) / lam) = ((lam⁻¹ * y : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [this, logKernel, Complex.norm_real, Real.norm_of_nonneg hlam.le, mul_add, Real.exp_add,
    Real.rpow_def_of_pos hlam]
  congr 2
  ring

/-- `exp(β g_λ(u))` is the radial function `y ↦ exp(β g_λ(y))` of `|u|`. -/
theorem exp_smearedKernel_eq_comp_norm (lam β : ℝ) (u : ℂ) :
    Real.exp (β * smearedKernel lam u) =
      (fun y : ℝ => Real.exp (β * smearedKernel lam (y : ℂ))) ‖u‖ := by
  simp only
  rw [← smearedKernel_eq_norm lam u]

/-! ### The density of `μ_β` (`β > 2`) -/

/-- The density `r ↦ exp(β g_1(r)) r` is continuous. -/
theorem continuous_exp_smearedKernel_one_mul (β : ℝ) :
    Continuous fun r : ℝ => Real.exp (β * smearedKernel 1 (r : ℂ)) * r :=
  ((continuous_const.mul
    ((continuous_smearedKernel one_pos).comp Complex.continuous_ofReal)).rexp).mul continuous_id

/-- The tail `{r ≥ s}`, `s ≥ 2`, of the density of `μ_β` is integrable. -/
theorem integrableOn_Ioi_exp_smearedKernel_one {β : ℝ} (hβ : 2 < β) {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn (fun r : ℝ => Real.exp (β * smearedKernel 1 (r : ℂ)) * r) (Ioi s) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := 1 - β) (by linarith) (by linarith : 0 < s)
  refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
  exact (exp_mul_smearedKernel_mul_of_le β one_pos (by linarith [mem_Ioi.1 hr])).symm

/-- The density `exp(β g_1(r)) r` of `μ_β` is integrable on `(0, ∞)` for `β > 2`
(source l. 188–198). -/
theorem integrableOn_exp_smearedKernel_one {β : ℝ} (hβ : 2 < β) :
    IntegrableOn (fun r : ℝ => Real.exp (β * smearedKernel 1 r) * r) (Ioi 0) := by
  have h1 : IntegrableOn (fun r : ℝ => Real.exp (β * smearedKernel 1 (r : ℂ)) * r) (Ioc 0 2) :=
    ((continuous_exp_smearedKernel_one_mul β).continuousOn.integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 2)]
  exact h1.union (integrableOn_Ioi_exp_smearedKernel_one hβ le_rfl)

/-- `∫_{r ≥ t} r^{1-β} dr = t^{2-β} / (β - 2)` for `β > 2`, `t > 0`. -/
theorem integral_Ici_rpow_one_sub {β t : ℝ} (hβ : 2 < β) (ht : 0 < t) :
    ∫ r in Ici t, r ^ (1 - β) = t ^ (2 - β) / (β - 2) := by
  rw [integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) ht]
  have e : 1 - β + 1 = 2 - β := by ring
  have hne : β - 2 ≠ 0 := by linarith
  rw [e, neg_div, ← div_neg, neg_sub]

/-- The tail of `μ_β`: `∫_{r ≥ s} exp(β g_1(r)) r dr = s^{2-β} / (β - 2)` for `s ≥ 2`
(source l. 1357–1362, since `g_1(r) = -log r` for `r ≥ 2`). -/
theorem integral_Ici_exp_smearedKernel_one {β : ℝ} (hβ : 2 < β) {s : ℝ} (hs : 2 ≤ s) :
    ∫ r in Ici s, Real.exp (β * smearedKernel 1 r) * r = s ^ (2 - β) / (β - 2) := by
  rw [← integral_Ici_rpow_one_sub hβ (by linarith : 0 < s)]
  exact setIntegral_congr_fun measurableSet_Ici
    (fun r hr => exp_mul_smearedKernel_mul_of_le β one_pos (by linarith [mem_Ici.1 hr]))

/-! ### The constant `𝒵_β` -/

/-- For `β > 2` the constant `𝒵_β` is `2π ∫₀^∞ exp(β g_1(r)) r dr`. -/
theorem dipoleConstant_of_ne {β : ℝ} (hβ : 2 ≤ β) (hne : β ≠ 2) :
    dipoleConstant β hβ =
      2 * Real.pi * ∫ r in Ioi (0 : ℝ), Real.exp (β * smearedKernel 1 r) * r := by
  simp [dipoleConstant, hne]

/-- The normalising integral of `μ_β` is positive. -/
theorem integral_exp_smearedKernel_one_pos {β : ℝ} (hβ : 2 < β) :
    0 < ∫ r in Ioi (0 : ℝ), Real.exp (β * smearedKernel 1 r) * r := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun r : ℝ => Real.exp (β * smearedKernel 1 r) * r) ∩ Ioi 0 =
        Ioi 0 := by
      refine inter_eq_right.2 fun r hr => ?_
      exact (mul_pos (Real.exp_pos _) hr).ne'
    rw [this]
    simp
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => ?_)
    exact (mul_pos (Real.exp_pos _) hr).le
  · exact integrableOn_exp_smearedKernel_one hβ

/-- `𝒵_β > 0` for `β ≥ 2` (source l. 199). -/
theorem dipoleConstant_pos (β : ℝ) (hβ : 2 ≤ β) : 0 < dipoleConstant β hβ := by
  by_cases h : β = 2
  · simp [dipoleConstant, h, Real.pi_pos]
  · rw [dipoleConstant_of_ne hβ h]
    exact mul_pos (by positivity)
      (integral_exp_smearedKernel_one_pos (lt_of_le_of_ne hβ (Ne.symm h)))

/-! ### `∫ exp(β g_λ) = 𝒵_β λ^{2-β}` -/

/-- Scaling of the radial integrand: `y e^{β g_λ(y)} = λ^{1-β} s e^{β g_1(s)}` at `s = y / λ`. -/
theorem mul_exp_smearedKernel_eq {lam : ℝ} (hlam : 0 < lam) (β y : ℝ) :
    y * Real.exp (β * smearedKernel lam (y : ℂ)) =
      lam ^ (1 - β) * ((lam⁻¹ * y) * Real.exp (β * smearedKernel 1 ((lam⁻¹ * y : ℝ) : ℂ))) := by
  rw [exp_mul_smearedKernel_ofReal_eq hlam, Real.rpow_sub hlam, Real.rpow_neg hlam.le,
    Real.rpow_one]
  have : lam ^ β ≠ 0 := (Real.rpow_pos_of_pos hlam β).ne'
  field_simp

/-- The radial integrand `y e^{β g_λ(y)}` is integrable on `(0, ∞)` for `β > 2`. -/
theorem integrableOn_mul_exp_smearedKernel {β lam : ℝ} (hβ : 2 < β) (hlam : 0 < lam) :
    IntegrableOn (fun y : ℝ => y * Real.exp (β * smearedKernel lam (y : ℂ))) (Ioi 0) := by
  have h1 : IntegrableOn (fun s : ℝ => s * Real.exp (β * smearedKernel 1 (s : ℂ)))
      (Ioi (lam⁻¹ * 0)) := by
    rw [mul_zero]
    refine (integrableOn_exp_smearedKernel_one hβ).congr_fun (fun s _ => ?_) measurableSet_Ioi
    exact mul_comm _ _
  have h2 : IntegrableOn (fun y : ℝ => lam ^ (1 - β) *
      ((lam⁻¹ * y) * Real.exp (β * smearedKernel 1 ((lam⁻¹ * y : ℝ) : ℂ)))) (Ioi 0) :=
    ((integrableOn_Ioi_comp_mul_left_iff
      (fun s : ℝ => s * Real.exp (β * smearedKernel 1 (s : ℂ))) 0 (inv_pos.2 hlam)).2 h1).const_mul
      (lam ^ (1 - β))
  exact h2.congr_fun (fun y _ => (mul_exp_smearedKernel_eq hlam β y).symm) measurableSet_Ioi

/-- Scaling of the radial integral: `∫₀^∞ y e^{β g_λ(y)} dy = λ^{2-β} ∫₀^∞ r e^{β g_1(r)} dr`. -/
theorem integral_mul_exp_smearedKernel {β lam : ℝ} (hlam : 0 < lam) :
    ∫ y in Ioi (0 : ℝ), y * Real.exp (β * smearedKernel lam (y : ℂ)) =
      lam ^ (2 - β) * ∫ r in Ioi (0 : ℝ), Real.exp (β * smearedKernel 1 r) * r := by
  have h1 : ∫ y in Ioi (0 : ℝ), y * Real.exp (β * smearedKernel lam (y : ℂ)) =
      lam ^ (1 - β) * ∫ y in Ioi (0 : ℝ),
        ((lam⁻¹ * y) * Real.exp (β * smearedKernel 1 ((lam⁻¹ * y : ℝ) : ℂ))) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun y _ => mul_exp_smearedKernel_eq hlam β y)
  rw [h1, integral_comp_mul_left_Ioi
    (fun s : ℝ => s * Real.exp (β * smearedKernel 1 (s : ℂ))) 0 (inv_pos.2 hlam), mul_zero, inv_inv]
  simp only [smul_eq_mul]
  rw [← mul_assoc, show 2 - β = (1 - β) + 1 by ring, Real.rpow_add hlam, Real.rpow_one]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun y _ => mul_comm _ _)

/-- `exp(β g_λ)` is integrable on `ℝ²` for `β > 2`, `λ > 0`. -/
theorem integrable_exp_smearedKernel {β lam : ℝ} (hβ : 2 < β) (hlam : 0 < lam) :
    Integrable (fun u : ℂ => Real.exp (β * smearedKernel lam u)) := by
  have hf : (fun u : ℂ => Real.exp (β * smearedKernel lam u)) =
      fun u : ℂ => (fun y : ℝ => Real.exp (β * smearedKernel lam (y : ℂ))) ‖u‖ :=
    funext (exp_smearedKernel_eq_comp_norm lam β)
  rw [hf]
  exact (integrable_comp_norm_complex_iff _).2 (integrableOn_mul_exp_smearedKernel hβ hlam)

/-- Source the planar pair-mass identity, l. 816–825: `∫_{ℝ²} exp(β g_λ(u)) du = 𝒵_β λ^{2-β}` for `β > 2`. -/
theorem integral_exp_smearedKernel {β lam : ℝ} (hβ : 2 < β) (hlam : 0 < lam) :
    ∫ u : ℂ, Real.exp (β * smearedKernel lam u) = dipoleConstant β hβ.le * lam ^ (2 - β) := by
  have hf : (fun u : ℂ => Real.exp (β * smearedKernel lam u)) =
      fun u : ℂ => (fun y : ℝ => Real.exp (β * smearedKernel lam (y : ℂ))) ‖u‖ :=
    funext (exp_smearedKernel_eq_comp_norm lam β)
  rw [hf, integral_comp_norm_complex (fun y : ℝ => Real.exp (β * smearedKernel lam (y : ℂ))),
    integral_mul_exp_smearedKernel hlam, dipoleConstant_of_ne hβ.le hβ.ne']
  ring

/-! ### Truncation to a disc -/

/-- The mass of `exp(β g_λ)` outside `B(0, t)`, `t ≥ 2λ`, is exactly `2π t^{2-β} / (β - 2)`. -/
theorem integral_compl_ball_exp_smearedKernel {β lam t : ℝ} (hβ : 2 < β) (hlam : 0 < lam)
    (ht : 2 * lam ≤ t) :
    ∫ u in (Metric.ball (0 : ℂ) t)ᶜ, Real.exp (β * smearedKernel lam u) =
      2 * Real.pi * (t ^ (2 - β) / (β - 2)) := by
  have ht0 : 0 < t := by linarith
  set G : ℝ → ℝ := fun y => Real.exp (β * smearedKernel lam (y : ℂ)) with hG
  have h1 : ∀ x : ℂ, indicator (Metric.ball (0 : ℂ) t)ᶜ
      (fun u : ℂ => Real.exp (β * smearedKernel lam u)) x = indicator (Ici t) G ‖x‖ := by
    intro x
    have hmem : x ∈ (Metric.ball (0 : ℂ) t)ᶜ ↔ ‖x‖ ∈ Ici t := by
      simp
    by_cases hx : x ∈ (Metric.ball (0 : ℂ) t)ᶜ
    · rw [indicator_of_mem hx, indicator_of_mem (hmem.1 hx)]
      exact exp_smearedKernel_eq_comp_norm lam β x
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hmem.2 h))]
  rw [← integral_indicator (Metric.isOpen_ball.measurableSet.compl)]
  simp_rw [h1]
  rw [integral_comp_norm_complex]
  have h2 : ∀ y : ℝ, y * indicator (Ici t) G y = indicator (Ici t) (fun y => y * G y) y := by
    intro y
    by_cases hy : y ∈ Ici t
    · rw [indicator_of_mem hy, indicator_of_mem hy]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
  simp_rw [h2]
  rw [setIntegral_indicator measurableSet_Ici, inter_eq_right.2 (Ici_subset_Ioi.2 ht0),
    ← integral_Ici_rpow_one_sub hβ ht0]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ici (fun r hr => ?_)
  rw [hG, mul_comm]
  exact exp_mul_smearedKernel_mul_of_le β hlam (by linarith [mem_Ici.1 hr])

/-- The mass of `exp(β g_λ)` in `B(0, t)`, `t ≥ 2λ`: the full mass `𝒵_β λ^{2-β}` minus the exact
tail `2π t^{2-β} / (β - 2)`. -/
theorem integral_ball_exp_smearedKernel {β lam t : ℝ} (hβ : 2 < β) (hlam : 0 < lam)
    (ht : 2 * lam ≤ t) :
    ∫ u in Metric.ball (0 : ℂ) t, Real.exp (β * smearedKernel lam u) =
      dipoleConstant β hβ.le * lam ^ (2 - β) - 2 * Real.pi * (t ^ (2 - β) / (β - 2)) := by
  have h := integral_add_compl (Metric.isOpen_ball (x := (0 : ℂ)) (ε := t)).measurableSet
    (integrable_exp_smearedKernel hβ hlam)
  rw [integral_exp_smearedKernel hβ hlam, integral_compl_ball_exp_smearedKernel hβ hlam ht] at h
  linarith

/-- Truncated version of the planar pair-mass identity, used for the lower bound in Lemma 3.5:
`∫_{B(0,t)} exp(β g_λ) ≥ 𝒵_β λ^{2-β} (1 - C_β (λ/t)^{β-2})` for `t ≥ 2λ`, with the explicit
constant `C_β = 2π / ((β - 2) 𝒵_β)`. -/
theorem exists_integral_ball_exp_smearedKernel_ge {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam t : ℝ, 0 < lam → 2 * lam ≤ t →
      dipoleConstant β hβ.le * lam ^ (2 - β) * (1 - C * (lam / t) ^ (β - 2)) ≤
        ∫ u in Metric.ball (0 : ℂ) t, Real.exp (β * smearedKernel lam u) := by
  have hZ := dipoleConstant_pos β hβ.le
  have hb : 0 < β - 2 := by linarith
  refine ⟨2 * Real.pi / ((β - 2) * dipoleConstant β hβ.le), by positivity, fun lam t hlam ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [integral_ball_exp_smearedKernel hβ hlam ht]
  have e : lam ^ (2 - β) * (lam / t) ^ (β - 2) = t ^ (2 - β) := by
    rw [Real.div_rpow hlam.le ht0.le, show 2 - β = -(β - 2) by ring, Real.rpow_neg hlam.le,
      Real.rpow_neg ht0.le]
    have : lam ^ (β - 2) ≠ 0 := (Real.rpow_pos_of_pos hlam _).ne'
    field_simp
  have : dipoleConstant β hβ.le * lam ^ (2 - β) *
      (1 - 2 * Real.pi / ((β - 2) * dipoleConstant β hβ.le) * (lam / t) ^ (β - 2)) =
      dipoleConstant β hβ.le * lam ^ (2 - β) - 2 * Real.pi * (t ^ (2 - β) / (β - 2)) := by
    rw [← e]
    field_simp
  exact this.le

end TwoComponentCoulomb

end
