/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TwoComponentCoulomb.Potential.DiscPotential
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Group.Integral

/-!
# The fundamental solution of the Laplacian in `ℝ² ≅ ℂ`

The kernel `g(x) = -log |x|` has gradient `∇g(u) = -u / |u|²` (source l. 123, 176–185).
Theorem 2, Step 1 (source l. 1842–1866) needs Green's formula `∫ ξ dμ = (1 / 2π) ∫ ∇ξ · ∇h`
for compactly supported test functions `ξ`; here we prove its single-charge form without
Green's theorem. For `ξ` of class `C¹` with compact support and every `y ∈ ℂ`,

`∫ ∇ξ(x) · ∇g(x - y) dx = 2π ξ(y)`

(`integral_fderiv_apply_gradLogKernel`; the integrability for `y = 0` is
`integrable_fderiv_apply_gradLogKernel_zero`). The proof is in polar coordinates about `y`: along
the ray `r ↦ y + r e^{iθ}` one has `r ∇ξ(y + r e^{iθ}) · ∇g(r e^{iθ}) = -∂_r [ξ(y + r e^{iθ})]`, the
Jacobian `r` of the polar-coordinate map cancelling the singularity of the gradient. The radial
integral is `ξ(y)` by the fundamental theorem of calculus, and the angular integral over
`(-π, π)` gives the factor `2π`.

Here `∇ξ(x) · v` is `fderiv ℝ ξ x v` and the gradient of `g` is written
`-((‖u‖ ^ 2)⁻¹ : ℝ) • u` (it is `0` at `u = 0`, a null set).

* `integrableOn_inv_norm_ball_zero` : `‖·‖⁻¹` is integrable on discs of `ℂ`.
* `integrableOn_comp_sub_ball` : integrability of `y ↦ f (x - y)` on a disc from that of `f`
  on discs centred at `0`.
-/

public section

open MeasureTheory Metric Set

namespace TwoComponentCoulomb

/-- The function `‖·‖⁻¹` is integrable on every disc centred at `0` in `ℂ`. -/
theorem integrableOn_inv_norm_ball_zero (R : ℝ) :
    IntegrableOn (fun x : ℂ => ‖x‖⁻¹) (ball (0 : ℂ) R) := by
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := fun y : ℝ => y⁻¹) (r := R),
    Complex.finrank_real_complex]
  refine (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun (fun y hy => ?_) measurableSet_Ioo
  have : y ≠ 0 := hy.1.ne'
  simp [this]

/-- If `f` is integrable on every disc centred at `0`, then `y ↦ f (x - y)` is integrable on
every disc of `ℂ`, wherever `x` lies. -/
theorem integrableOn_comp_sub_ball {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : ∀ R : ℝ, IntegrableOn f (ball (0 : ℂ) R)) (x z : ℂ) (a : ℝ) :
    IntegrableOn (fun y : ℂ => f (x - y)) (ball z a) := by
  set ρ : ℝ := ‖x - z‖ + a with hρ
  have h0 : Integrable (indicator (ball (0 : ℂ) ρ) f) :=
    (integrable_indicator_iff measurableSet_ball).2 (hf ρ)
  have h1 := h0.comp_sub_left x
  refine h1.integrableOn.congr_fun (fun y hy => ?_) measurableSet_ball
  have hmem : x - y ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff]
    rw [mem_ball_iff_norm] at hy
    calc ‖x - y‖ = ‖(x - z) + (z - y)‖ := by congr 1; ring
      _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
      _ < ‖x - z‖ + a := by rw [norm_sub_rev z y]; linarith
  simp [indicator, hmem]

/-- The gradient `-u / |u|²` of the kernel `g` has modulus `|u|⁻¹`. -/
theorem norm_gradLogKernel (w : ℂ) : ‖-((‖w‖ ^ 2)⁻¹ : ℝ) • w‖ = ‖w‖⁻¹ := by
  by_cases hw : w = 0
  · simp [hw]
  · have : 0 < ‖w‖ := norm_pos_iff.2 hw
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp

/-- Measurability of `w ↦ ∇η(w) · ∇g(w)` for `η` of class `C¹`. -/
theorem measurable_fderiv_apply_gradLogKernel_zero {η : ℂ → ℝ} (hη : ContDiff ℝ 1 η) :
    Measurable fun w : ℂ => fderiv ℝ η w (-((‖w‖ ^ 2)⁻¹ : ℝ) • w) := by
  have h1 : (fun w : ℂ => fderiv ℝ η w (-((‖w‖ ^ 2)⁻¹ : ℝ) • w)) =
      fun w => -((‖w‖ ^ 2)⁻¹ : ℝ) * fderiv ℝ η w w := by
    funext w
    rw [map_smul, smul_eq_mul]
  rw [h1]
  have h2 : Continuous fun w : ℂ => fderiv ℝ η w w :=
    (hη.continuous_fderiv one_ne_zero).clm_apply continuous_id
  exact (measurable_norm.pow_const 2 |>.inv.neg).mul h2.measurable

/-- Integrability of `w ↦ ∇η(w) · ∇g(w)` (pole at `0`): it is bounded by `C / |w|` and
vanishes outside a disc. -/
theorem integrable_fderiv_apply_gradLogKernel_zero {η : ℂ → ℝ} (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) :
    Integrable fun w : ℂ => fderiv ℝ η w (-((‖w‖ ^ 2)⁻¹ : ℝ) • w) := by
  obtain ⟨C, hC⟩ := (hη.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ))
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1 hc.isCompact.isBounded
  have hG : Integrable (indicator (ball (0 : ℂ) R) fun w : ℂ => C * ‖w‖⁻¹) :=
    (integrable_indicator_iff measurableSet_ball).2
      ((integrableOn_inv_norm_ball_zero R).const_mul C)
  refine hG.mono' (measurable_fderiv_apply_gradLogKernel_zero hη).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  by_cases hw : w ∈ ball (0 : ℂ) R
  · rw [indicator_of_mem hw]
    calc ‖fderiv ℝ η w (-((‖w‖ ^ 2)⁻¹ : ℝ) • w)‖
        ≤ ‖fderiv ℝ η w‖ * ‖-((‖w‖ ^ 2)⁻¹ : ℝ) • w‖ := (fderiv ℝ η w).le_opNorm _
      _ ≤ C * ‖w‖⁻¹ := by
        rw [norm_gradLogKernel]
        exact mul_le_mul_of_nonneg_right (hC w) (by positivity)
  · rw [indicator_of_notMem hw]
    have : w ∉ tsupport η := fun h => hw (hR h)
    simp [fderiv_of_notMem_tsupport ℝ this]

/-- Derivative of `r ↦ η (r e^{iθ})` along a ray. -/
theorem hasDerivAt_comp_circleMap_radius {η : ℂ → ℝ} (hη : ContDiff ℝ 1 η) (θ r : ℝ) :
    HasDerivAt (fun s : ℝ => η (circleMap 0 s θ))
      (fderiv ℝ η (circleMap 0 r θ) (Complex.exp (θ * Complex.I))) r := by
  have h1 : HasDerivAt (fun s : ℝ => circleMap 0 s θ) (Complex.exp (θ * Complex.I)) r := by
    have := ((hasDerivAt_id r).ofReal_comp.mul_const (Complex.exp (θ * Complex.I))).const_add 0
    simpa [circleMap] using this
  exact (hη.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r h1

/-- The restriction of a `C¹` function to a ray `r ↦ r e^{iθ}` is `C¹`. -/
theorem contDiff_comp_circleMap_radius {η : ℂ → ℝ} (hη : ContDiff ℝ 1 η) (θ : ℝ) :
    ContDiff ℝ 1 fun s : ℝ => η (circleMap 0 s θ) := by
  have : ContDiff ℝ 1 fun s : ℝ => circleMap 0 s θ := by
    simp only [circleMap, zero_add]
    exact Complex.ofRealCLM.contDiff.mul contDiff_const
  exact hη.comp this

/-- The restriction of a compactly supported function to a ray has compact support. -/
theorem hasCompactSupport_comp_circleMap_radius {η : ℂ → ℝ} (hc : HasCompactSupport η) (θ : ℝ) :
    HasCompactSupport fun s : ℝ => η (circleMap 0 s θ) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1 hc.isCompact.isBounded
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs => ?_
  by_contra hne
  have h1 : circleMap 0 s θ ∈ ball (0 : ℂ) R := hR (subset_tsupport _ hne)
  rw [mem_ball_zero_iff, norm_circleMap_zero] at h1
  exact hs ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩

/-- The Jacobian `r` of the polar coordinates cancels the singularity of `∇g`:
`r ∇η(r e^{iθ}) · ∇g(r e^{iθ}) = -∂_r [η(r e^{iθ})]`. -/
theorem radial_smul_fderiv_apply_gradLogKernel {η : ℂ → ℝ} (hη : ContDiff ℝ 1 η) {r : ℝ}
    (hr : 0 < r) (θ : ℝ) :
    r • fderiv ℝ η (Complex.polarCoord.symm (r, θ))
        (-((‖Complex.polarCoord.symm (r, θ)‖ ^ 2)⁻¹ : ℝ) • Complex.polarCoord.symm (r, θ)) =
      -deriv (fun s : ℝ => η (circleMap 0 s θ)) r := by
  rw [(hasDerivAt_comp_circleMap_radius hη θ r).deriv, polarCoord_symm_eq_circleMap,
    norm_circleMap_zero, abs_of_pos hr]
  have h1 : circleMap 0 r θ = r • Complex.exp (θ * Complex.I) := by
    simp [circleMap, Complex.real_smul]
  rw [h1, ← smul_assoc, map_smul]
  simp only [smul_eq_mul]
  field_simp

/-- The radial integral of `r ∇η(r e^{iθ}) · ∇g(r e^{iθ})` is `η(0)`, for every angle `θ`. -/
theorem integral_Ioi_radial_fderiv_apply_gradLogKernel {η : ℂ → ℝ} (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) (θ : ℝ) :
    ∫ r in Ioi (0 : ℝ), r • fderiv ℝ η (Complex.polarCoord.symm (r, θ))
        (-((‖Complex.polarCoord.symm (r, θ)‖ ^ 2)⁻¹ : ℝ) • Complex.polarCoord.symm (r, θ)) =
      η 0 := by
  rw [setIntegral_congr_fun measurableSet_Ioi fun r hr =>
    radial_smul_fderiv_apply_gradLogKernel hη hr θ, integral_neg,
    (hasCompactSupport_comp_circleMap_radius hc θ).integral_Ioi_deriv_eq
      (contDiff_comp_circleMap_radius hη θ) 0]
  simp

/-- The fundamental solution of the Laplacian in weak form, with the pole at `0`. -/
theorem integral_fderiv_apply_gradLogKernel_zero {η : ℂ → ℝ} (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) :
    ∫ w : ℂ, fderiv ℝ η w (-((‖w‖ ^ 2)⁻¹ : ℝ) • w) = 2 * Real.pi * η 0 := by
  set F : ℂ → ℝ := fun w => fderiv ℝ η w (-((‖w‖ ^ 2)⁻¹ : ℝ) • w) with hF
  have hint : Integrable F := integrable_fderiv_apply_gradLogKernel_zero hη hc
  have hI := integrableOn_polarCoord_target (measurable_fderiv_apply_gradLogKernel_zero hη) hint
  rw [← Complex.integral_comp_polarCoord_symm F]
  have hT : _root_.polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl
  rw [hT]
  rw [Complex.polarCoord_target] at hI
  have hI' : Integrable (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hI
  have h1 : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, p.1 • F (Complex.polarCoord.symm p) =
      ∫ θ in Ioo (-Real.pi) Real.pi,
        ∫ r in Ioi (0 : ℝ), r • F (Complex.polarCoord.symm (r, θ)) := by
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod _ _,
      ← Measure.prod_restrict]
    exact integral_prod_symm _ hI'
  rw [h1]
  have h2 : ∀ θ ∈ Ioo (-Real.pi) Real.pi,
      ∫ r in Ioi (0 : ℝ), r • F (Complex.polarCoord.symm (r, θ)) = η 0 := fun θ _ =>
    integral_Ioi_radial_fderiv_apply_gradLogKernel hη hc θ
  rw [setIntegral_congr_fun measurableSet_Ioo h2, setIntegral_const]
  rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), smul_eq_mul]
  ring

/-! ### Translation to the pole `y` -/

/-- Translating the pole from `y` to `0`. -/
theorem fderiv_apply_gradLogKernel_translate {ξ : ℂ → ℝ} (y x : ℂ) :
    fderiv ℝ ξ x (-((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y)) =
      fderiv ℝ (fun w => ξ (y + w)) (x - y) (-((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y)) := by
  rw [fderiv_comp_add_left, add_sub_cancel]

/-- **The fundamental solution of the Laplacian in `ℝ²`, in weak form.** For `ξ` of class `C¹`
with compact support and every `y ∈ ℂ`,
`∫ ∇ξ(x) · ∇g(x - y) dx = 2π ξ(y)` where `∇g(u) = -u / |u|²`. -/
theorem integral_fderiv_apply_gradLogKernel {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport ξ) (y : ℂ) :
    ∫ x, fderiv ℝ ξ x (-((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y)) = 2 * Real.pi * ξ y := by
  have hη : ContDiff ℝ 1 fun w => ξ (y + w) := hξ.comp (contDiff_const.add contDiff_id)
  have hηc : HasCompactSupport fun w => ξ (y + w) :=
    hc.comp_isClosedEmbedding (Homeomorph.addLeft y).isClosedEmbedding
  have h := integral_fderiv_apply_gradLogKernel_zero hη hηc
  simp only [add_zero] at h
  simp only [fderiv_apply_gradLogKernel_translate y]
  rw [integral_sub_right_eq_self (fun w => fderiv ℝ (fun w => ξ (y + w)) w
    (-((‖w‖ ^ 2)⁻¹ : ℝ) • w)) y]
  exact h

end TwoComponentCoulomb

end
