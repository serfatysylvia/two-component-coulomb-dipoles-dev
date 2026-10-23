/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.RadiiControlRates
public import TwoComponentCoulomb.Fluctuations.SourceScale

/-!
# Theorem 2, Step 6: the scale and the polynomial prefactor

Source: `source/dipole-formation.tex`, l. 2105–2120.
`gammaChoice` is the four-case scale `manuscriptGammaChoice`, including the logarithmic
factor at `β = 4`. `manuscriptGammaChoice_rate` proves `φ_β(γ) + γ² ≤ 3 ω_λ`.
`gammaChoice_bounds` gives its range. `exists_min_one_le_exp` absorbs the polynomial
prefactor in the probability bound.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-! ### The parameter `γ` -/

/-- The parameter `γ` of Step 6 is the manuscript's four-case choice. -/
noncomputable def gammaChoice (β lam : ℝ) : ℝ :=
  manuscriptGammaChoice β lam

/-- The rate-free part of the regime of `γ`: `2λ ≤ γ ≤ 1` for `0 < λ < e⁻⁴`. -/
theorem gammaChoice_bounds (β : ℝ) (hβ : 2 ≤ β) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < Real.exp (-4)) : 2 * lam ≤ gammaChoice β lam ∧ gammaChoice β lam ≤ 1 :=
  manuscriptGammaChoice_bounds β hβ h0 h1

/-- **Source l. 2105–2115, for a general rate function `ω`**: if `φ_β(γ) + γ² ≤ 3 √ω(λ)` for
`0 < λ < e⁻⁴`, then for `λ` small, `2λ ≤ γ ≤ 1` and `φ_β(γ) + γ² ≤ 3 √ω(λ)`. -/
theorem exists_gammaChoice_regime_rate (β : ℝ) (hβ : 2 ≤ β) {ω : ℝ → ℝ}
    (hγ : ∀ lam : ℝ, 0 < lam → lam < Real.exp (-4) →
      isolatedPhi β hβ lam (gammaChoice β lam) + gammaChoice β lam ^ 2 ≤ 3 * Real.sqrt (ω lam)) :
    ∃ lamG : ℝ, 0 < lamG ∧ lamG ≤ Real.exp (-1) ∧ ∀ lam : ℝ, 0 < lam → lam < lamG →
      2 * lam ≤ gammaChoice β lam ∧ gammaChoice β lam ≤ 1 ∧
        isolatedPhi β hβ lam (gammaChoice β lam) + gammaChoice β lam ^ 2
          ≤ 3 * Real.sqrt (ω lam) :=
  ⟨Real.exp (-4), Real.exp_pos _, Real.exp_le_exp.2 (by norm_num), fun _ h0 h1 =>
    ⟨(gammaChoice_bounds β hβ h0 h1).1, (gammaChoice_bounds β hβ h0 h1).2, hγ _ h0 h1⟩⟩

/-! ### Absorption of the polynomial prefactor -/

/-- **Source l. 2116–2119**: `min{1, K (N+1)^C e^{-c N x}} ≤ C' e^{-c' √N x}` for all `N ≥ 1`
and `x ≥ 0`, with `C'`, `c'` depending only on `K`, `C`, `c`. -/
theorem exists_min_one_le_exp {K C c : ℝ} (hK : 0 < K) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 ≤ x →
      min 1 (K * Real.exp (C * Real.log (N + 1) - c * N * x))
        ≤ C' * Real.exp (-(c' * Real.sqrt N * x)) := by
  refine ⟨max K (Real.exp (3 * C)), c / 2, lt_max_of_lt_left hK, half_pos hc, ?_⟩
  intro N hN x hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hs1 : 1 ≤ Real.sqrt N := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hN1
  have hlogN : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  by_cases hbig : 2 * C * Real.log ((N : ℝ) + 1) ≤ c * N * x
  · -- the exponential decay dominates the polynomial factor
    refine (min_le_right _ _).trans ?_
    have h1 : C * Real.log ((N : ℝ) + 1) - c * N * x ≤ -(c / 2 * Real.sqrt N * x) := by
      have h2 : Real.sqrt N ≤ N := by
        have := mul_le_mul_of_nonneg_left hs1 hs0.le
        linarith only [this, hsq]
      have h3 : c / 2 * Real.sqrt N * x ≤ c / 2 * N * x := by
        have : 0 ≤ c / 2 * x := by positivity
        have := mul_le_mul_of_nonneg_left h2 this
        linarith only [this]
      linarith only [hbig, h3]
    calc K * Real.exp (C * Real.log ((N : ℝ) + 1) - c * N * x)
        ≤ K * Real.exp (-(c / 2 * Real.sqrt N * x)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hK.le
      _ ≤ max K (Real.exp (3 * C)) * Real.exp (-(c / 2 * Real.sqrt N * x)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · -- otherwise `√N x` is bounded
    push Not at hbig
    refine (min_le_left _ _).trans ?_
    have hlog : Real.log ((N : ℝ) + 1) ≤ 3 * Real.sqrt N := by
      have h1 : Real.log ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div (by linarith) (by norm_num)
      rw [← Real.sqrt_eq_rpow] at h1
      have h2 : Real.sqrt ((N : ℝ) + 1) ≤ 3 / 2 * Real.sqrt N := by
        rw [Real.sqrt_le_left (by positivity)]
        linarith only [hsq, hN1]
      linarith
    have hx' : c * (Real.sqrt N * x) < 6 * C := by
      have h1 : c * N * x < 2 * C * (3 * Real.sqrt N) := by
        calc c * N * x < 2 * C * Real.log ((N : ℝ) + 1) := hbig
          _ ≤ 2 * C * (3 * Real.sqrt N) := by gcongr
      have h2 : c * N * x = Real.sqrt N * (c * (Real.sqrt N * x)) := by
        have : Real.sqrt N * (c * (Real.sqrt N * x)) = c * x * (Real.sqrt N * Real.sqrt N) := by
          ring
        rw [this, hsq]
        ring
      rw [h2] at h1
      have h3 : Real.sqrt N * (c * (Real.sqrt N * x)) < Real.sqrt N * (6 * C) := by
        linarith
      exact lt_of_mul_lt_mul_left h3 hs0.le
    have h4 : -(c / 2 * Real.sqrt N * x) ≥ -(3 * C) := by linarith only [hx']
    calc (1 : ℝ) ≤ Real.exp (3 * C) * Real.exp (-(c / 2 * Real.sqrt N * x)) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith)
      _ ≤ max K (Real.exp (3 * C)) * Real.exp (-(c / 2 * Real.sqrt N * x)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

end TwoComponentCoulomb

end
