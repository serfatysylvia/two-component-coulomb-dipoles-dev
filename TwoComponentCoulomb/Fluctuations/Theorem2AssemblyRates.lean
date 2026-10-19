/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.RadiiControlRates
public import TwoComponentCoulomb.UpperBound.IsolatedRadial
import Mathlib.Analysis.Real.Pi.Bounds
import TwoComponentCoulomb.Main.Theorem1AssemblyBounds

/-!
# Theorem 2, Step 6: the choice of `γ` and the absorption of the polynomial prefactor

Source: proof of Theorem 2, Step 6 (l. 2231--2246).

* `gammaChoice` : the parameter `γ`. The source takes `|log λ|^{-1/2}` (`β = 2`), `λ^{(β-2)/β}`
  (`2 < β < 4`), `λ^{1/2} |log λ|^{1/4}` (`β = 4`) and `λ^{1/2}` (`β > 4`). Only the consequence
  `2λ ≤ γ ≤ 1` and `φ_β(γ) + γ² = O(√ω_λ)` is used below, and the last two cases are covered by
  the simpler choice `γ = λ^{1/2}` (`φ_4(λ^{1/2}) = λ (1 + ½ |log λ|)`).
* `gammaChoice_bounds` (with its three cases `gammaChoice_bounds_of_eq_two`,
  `gammaChoice_bounds_of_lt_four`, `gammaChoice_bounds_of_four_le`) : the rate-free part
  `2λ ≤ γ ≤ 1`.
* `exists_gammaChoice_regime_rate` : for a general rate function `ω` with
  `φ_β(γ) + γ² ≤ 3 √ω(λ)`, for `λ` small, `2λ ≤ γ ≤ 1` and `φ_β(γ) + γ² ≤ 3 √ω(λ)`. For
  `ω = errorRate β hβ` the comparison is `gamma_regime` (`Main/ErrorRateBounds.lean`; indeed
  `φ_β(γ) + γ² = O(ω_λ)` in the source's choice, l. 2240--2241).
* `exists_min_one_le_exp` : the elementary bound
  `min{1, K (N+1)^C e^{-c N x}} ≤ C' e^{-c' √N x}` (source l. 2242--2245).
-/

@[expose] public section

namespace TwoComponentCoulomb

/-! ### The parameter `γ` -/

/-- The parameter `γ` of Step 6: `|log λ|^{-1/2}` for `β = 2`, `λ^{(β-2)/β}` for `2 < β < 4`
and `λ^{1/2}` for `β ≥ 4`. -/
noncomputable def gammaChoice (β lam : ℝ) : ℝ :=
  if β = 2 then |Real.log lam| ^ (-(1 / 2 : ℝ))
  else if β < 4 then lam ^ ((β - 2) / β)
  else Real.sqrt lam

theorem exp_neg_four_le_quarter : Real.exp (-4) ≤ 1 / 4 := by
  rw [Real.exp_neg, inv_eq_one_div]
  have : (4 : ℝ) + 1 ≤ Real.exp 4 := Real.add_one_le_exp 4
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- The bounds `2λ ≤ γ ≤ 1` at `β = 2`, for `0 < λ < e⁻⁴`. -/
theorem gammaChoice_bounds_of_eq_two {β : ℝ} (h : β = 2) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < Real.exp (-4)) : 2 * lam ≤ gammaChoice β lam ∧ gammaChoice β lam ≤ 1 := by
  have hlam1 : lam < 1 := h1.trans (Real.exp_lt_one_iff.2 (by norm_num))
  have hL4 : 4 < |Real.log lam| := by
    have : Real.log lam < -4 := by
      rw [Real.log_lt_iff_lt_exp h0]
      exact h1
    rw [abs_of_neg (by linarith)]
    linarith
  have hlamL := mul_abs_log_lt_one h0 hlam1
  have hγ : gammaChoice β lam = (Real.sqrt |Real.log lam|)⁻¹ := by
    simp only [gammaChoice, h, ite_true]
    rw [Real.rpow_neg (abs_nonneg _), Real.sqrt_eq_rpow]
  rw [hγ]
  generalize hLdef : |Real.log lam| = L at hL4 hlamL ⊢
  have hL0 : 0 < L := by linarith
  set t := Real.sqrt L with ht
  have ht2 : t ^ 2 = L := Real.sq_sqrt hL0.le
  have ht0 : 0 < t := Real.sqrt_pos.2 hL0
  have ht2' : 2 ≤ t := by
    rw [ht]
    exact Real.le_sqrt_of_sq_le (by linarith)
  refine ⟨?_, inv_le_one_of_one_le₀ (by linarith)⟩
  -- `2 λ ≤ 1/t`
  rw [← one_div, le_div_iff₀ ht0]
  have hlt2 : lam * t ^ 2 < 1 := by rw [ht2]; exact hlamL
  have hm := mul_le_mul_of_nonneg_left ht2' (mul_nonneg h0.le ht0.le)
  linarith only [hm, hlt2]

/-- The bounds `2λ ≤ γ ≤ 1` for `2 < β < 4`, for `0 < λ ≤ 1/4`. -/
theorem gammaChoice_bounds_of_lt_four {β : ℝ} (h2 : 2 < β) (h4 : β < 4) {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam ≤ 1 / 4) :
    2 * lam ≤ gammaChoice β lam ∧ gammaChoice β lam ≤ 1 := by
  have hlam1 : lam ≤ 1 := by linarith
  have hγ : gammaChoice β lam = lam ^ ((β - 2) / β) := by
    simp only [gammaChoice, h2.ne', h4, ite_false, ite_true]
  have hβ0 : 0 < β := by linarith
  set e : ℝ := (β - 2) / β with he
  have he0 : 0 ≤ e := div_nonneg (by linarith) hβ0.le
  have he1 : 2 / β + e = 1 := by rw [he]; field_simp; ring
  have hsplit : lam = lam ^ (2 / β) * lam ^ e := by
    rw [← Real.rpow_add h0, he1, Real.rpow_one]
  rw [hγ]
  refine ⟨?_, Real.rpow_le_one h0.le hlam1 he0⟩
  -- `2 λ ≤ λ^e`
  have hq : lam ^ (2 / β) ≤ 1 / 2 := by
    calc lam ^ (2 / β) ≤ (1 / 4 : ℝ) ^ (2 / β) :=
          Real.rpow_le_rpow h0.le h1 (by positivity)
      _ ≤ (1 / 4 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by
            rw [div_le_div_iff₀ (by norm_num) hβ0]
            linarith)
      _ = 1 / 2 := by
          rw [← Real.sqrt_eq_rpow, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hpos : 0 ≤ lam ^ e := Real.rpow_nonneg h0.le _
  calc 2 * lam = 2 * (lam ^ (2 / β) * lam ^ e) := by rw [← hsplit]
    _ ≤ 2 * ((1 / 2) * lam ^ e) := by gcongr
    _ = lam ^ e := by ring

/-- The bounds `2λ ≤ γ ≤ 1` for `β ≥ 4`, for `0 < λ < e⁻⁴`. -/
theorem gammaChoice_bounds_of_four_le {β : ℝ} (h4 : 4 ≤ β) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < Real.exp (-4)) : 2 * lam ≤ gammaChoice β lam ∧ gammaChoice β lam ≤ 1 := by
  have hlam4 : lam ≤ 1 / 4 := (h1.trans_le exp_neg_four_le_quarter).le
  have hγ : gammaChoice β lam = Real.sqrt lam := by
    have h2 : β ≠ 2 := by linarith
    have h3 : ¬ β < 4 := by linarith
    simp only [gammaChoice, h2, h3, ite_false]
  have hs0 : 0 < Real.sqrt lam := Real.sqrt_pos.2 h0
  have hs2 : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt h0.le
  have hs1 : Real.sqrt lam ≤ 1 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  rw [hγ]
  refine ⟨?_, by linarith⟩
  have hm := mul_le_mul_of_nonneg_left (show 2 * Real.sqrt lam ≤ 1 by linarith only [hs1])
    hs0.le
  linarith only [hm, hs2]

/-- The rate-free part of the regime of `γ`: `2λ ≤ γ ≤ 1` for `0 < λ < e⁻⁴`. -/
theorem gammaChoice_bounds (β : ℝ) (hβ : 2 ≤ β) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < Real.exp (-4)) : 2 * lam ≤ gammaChoice β lam ∧ gammaChoice β lam ≤ 1 := by
  by_cases h2 : β = 2
  · exact gammaChoice_bounds_of_eq_two h2 h0 h1
  · have h2' : 2 < β := lt_of_le_of_ne hβ (Ne.symm h2)
    by_cases h4 : β < 4
    · exact gammaChoice_bounds_of_lt_four h2' h4 h0 (h1.trans_le exp_neg_four_le_quarter).le
    · exact gammaChoice_bounds_of_four_le (not_lt.1 h4) h0 h1

/-- **Source l. 2231--2241, for a general rate function `ω`**: if `φ_β(γ) + γ² ≤ 3 √ω(λ)` for
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

/-- **Source l. 2242--2245**: `min{1, K (N+1)^C e^{-c N x}} ≤ C' e^{-c' √N x}` for all `N ≥ 1`
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
