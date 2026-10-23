/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smooth approximation of Lipschitz functions and smooth cutoffs on `ℂ`

Auxiliary tools for Theorem 2, Step 1 (source l. 1844–1876). The
argument there applies Green's formula to a Lipschitz test function; in the formalization Green's
formula is available for `C¹` functions only (`integral_fderiv_apply_electricField`), so a
Lipschitz test function is first replaced by a mollification.

* `exists_contDiff_lipschitz_approx` : a `K`-Lipschitz function `f : ℂ → ℝ` is within `K ε`
  (uniformly) of a smooth `K`-Lipschitz function `f ⋆ ρ_ε`, where `ρ_ε` is a normed bump function
  supported in `B(0, ε)`.
* `exists_cutoff` : a family of smooth cutoffs `χ_R` (`R > 0`), equal to `1` on `B̄(0, R)`, vanishing
  outside `B(0, 2R)`, with `‖∇χ_R‖ ≤ Kχ / R` for a universal constant `Kχ`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Convolution ContDiff

namespace TwoComponentCoulomb

/-! ### Mollification of Lipschitz functions -/

/-- A real `K`-Lipschitz function on `ℂ` is within `K ε` of a smooth `K`-Lipschitz function
(its mollification by a normed bump function of outer radius `ε`). -/
theorem exists_contDiff_lipschitz_approx {f : ℂ → ℝ} {K : ℝ}
    (hf : ∀ x y, |f x - f y| ≤ K * ‖x - y‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ (∀ x y, |g x - g y| ≤ K * ‖x - y‖) ∧
      ∀ x, |g x - f x| ≤ K * ε := by
  have hK : 0 ≤ K := by
    have h := hf 1 0
    simp only [sub_zero, norm_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hcont : Continuous f := by
    have h : LipschitzWith K.toNNReal f := LipschitzWith.of_dist_le_mul fun x y => by
      simpa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal K hK] using hf x y
    exact h.continuous
  set φ : ContDiffBump (0 : ℂ) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩ with hφ
  set ρ : ℂ → ℝ := φ.normed volume with hρ
  have hρc : Continuous ρ := φ.continuous_normed
  have hρcs : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have hρ0 : ∀ t, 0 ≤ ρ t := φ.nonneg_normed
  have hρ1 : ∫ t, ρ t = 1 := φ.integral_normed
  have hint : ∀ x, Integrable (fun t => ρ t • f (x - t)) := fun x =>
    Continuous.integrable_of_hasCompactSupport
      (hρc.smul (hcont.comp (continuous_const.sub continuous_id))) hρcs.smul_right
  refine ⟨ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f, ?_, ?_, ?_⟩
  · exact hρcs.contDiff_convolution_left _ φ.contDiff_normed hcont.locallyIntegrable
  · intro x y
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
    rw [← integral_sub (hint x) (hint y)]
    have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
    have hg : Integrable (fun t => ρ t * (K * ‖x - y‖)) := hρi.mul_const _
    refine (Real.norm_eq_abs _ ▸ norm_integral_le_of_norm_le hg
      (Filter.Eventually.of_forall fun t => ?_)).trans (le_of_eq ?_)
    · rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 t), Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (hρ0 t)
      calc |f (x - t) - f (y - t)| ≤ K * ‖x - t - (y - t)‖ := hf _ _
        _ = K * ‖x - y‖ := by rw [sub_sub_sub_cancel_right]
    · rw [integral_mul_const, hρ1, one_mul]
  · intro x
    have h := φ.dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := K * ε)
      hcont.aestronglyMeasurable fun y hy => by
        have hy' : ‖y - x‖ < ε := by simpa [dist_eq_norm] using hy
        rw [Real.dist_eq]
        refine (hf y x).trans ?_
        exact mul_le_mul_of_nonneg_left hy'.le hK
    rwa [Real.dist_eq] at h

/-! ### Smooth cutoffs -/

/-- **Smooth cutoffs at all scales**: there is a universal constant `Kχ` such that for every
`R > 0` there is a smooth `χ : ℂ → ℝ` with `0 ≤ χ ≤ 1`, `χ = 1` on `B̄(0, R)`, `χ = 0` outside
`B(0, 2R)` and `‖∇χ‖ ≤ Kχ / R`. -/
theorem exists_cutoff :
    ∃ Kχ : ℝ, 0 ≤ Kχ ∧ ∀ R : ℝ, 0 < R → ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → χ x = 1) ∧ (∀ x, 2 * R ≤ ‖x‖ → χ x = 0) ∧
      ∀ x, ‖fderiv ℝ χ x‖ ≤ Kχ / R := by
  let f : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hf : ContDiff ℝ ∞ (f : ℂ → ℝ) := f.contDiff
  have hf1 : ContDiff ℝ 1 (f : ℂ → ℝ) := f.contDiff
  obtain ⟨K, hK⟩ := (hf1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (f.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨max K 0, le_max_right _ _, fun R hR => ⟨fun x => f (R⁻¹ • x), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hf.comp (contDiff_id.const_smul R⁻¹)
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * R)) fun x hx => ?_
    simp only [mem_closedBall, dist_zero_right, not_le] at hx
    refine f.zero_of_le_dist ?_
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), inv_mul_eq_div]
    show 2 ≤ ‖x‖ / R
    rw [le_div_iff₀ hR]
    linarith
  · exact fun x => ⟨f.nonneg, f.le_one⟩
  · intro x hx
    refine f.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR),
      inv_mul_eq_div]
    show ‖x‖ / R ≤ 1
    rw [div_le_one hR]
    exact hx
  · intro x hx
    refine f.zero_of_le_dist ?_
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), inv_mul_eq_div]
    show 2 ≤ ‖x‖ / R
    rw [le_div_iff₀ hR]
    linarith
  · intro x
    have h1 : HasFDerivAt (fun y : ℂ => f (R⁻¹ • y))
        ((fderiv ℝ f (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ ℂ)) x :=
      (hf1.differentiable one_ne_zero (R⁻¹ • x)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul R⁻¹)
    rw [h1.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h2 : ‖(R⁻¹ • ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)‖ ≤ R⁻¹ := by
      refine (norm_smul_le R⁻¹ (ContinuousLinearMap.id ℝ ℂ)).trans ?_
      rw [norm_inv, Real.norm_eq_abs, abs_of_pos hR]
      exact mul_le_of_le_one_right (inv_nonneg.2 hR.le) ContinuousLinearMap.norm_id_le
    calc ‖fderiv ℝ f (R⁻¹ • x)‖ * ‖(R⁻¹ • ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)‖
        ≤ max K 0 * R⁻¹ :=
          mul_le_mul ((hK _).trans (le_max_left _ _)) h2 (norm_nonneg _) (le_max_right _ _)
      _ = max K 0 / R := by rw [div_eq_mul_inv]

end TwoComponentCoulomb

end
