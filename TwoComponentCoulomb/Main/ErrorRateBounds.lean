/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.M0
public import TwoComponentCoulomb.Frozen.ErrorRate
public import TwoComponentCoulomb.Main.Theorem1AssemblyBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary bounds for the error rate `ω_λ = errorRate β hβ λ`

Source: `source/dipole-formation.tex`, (eq:defgammal), l. 221–229.
With `M₀ = 36` and `ℓ = |log λ|`, the four rates are `ℓ^{-1/5}`, `λ^{2(β-2)/(84-β)}`,
`(λℓ)^{1/21}` and `λ^{1/20}`. This module proves their positivity, smallness and the
comparisons used by Theorems 1 and 2. The radius comparisons are used in Step 5 of
Theorem 2 (l. 2060–2072). The four-case scale comparison is in
`Fluctuations/SourceScale.lean`.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-! ### The four branches -/

/-- `ω_λ` at `β = 2`: `|log λ|^{-1/5}`. -/
theorem errorRate_of_eq_two {β : ℝ} (hβ : 2 ≤ β) (h : β = 2) (lam : ℝ) :
    errorRate β hβ lam = |Real.log lam| ^ (-(1 / 5 : ℝ)) := by
  simp [errorRate, h]

/-- `ω_λ` for `2 < β < 4` (`M₀ = 36`): `λ^{2(β-2)/(84-β)}`. -/
theorem errorRate_of_lt_four {β : ℝ} (hβ : 2 ≤ β) (h : β ≠ 2) (h4 : β < 4) (lam : ℝ) :
    errorRate β hβ lam = lam ^ (2 * (β - 2) / (84 - β)) := by
  simp only [errorRate, h, h4, ite_false, ite_true, M0]
  congr 2
  ring

/-- `ω_λ` at `β = 4` (`M₀ = 36`): `(λ |log λ|)^{1/21}`. -/
theorem errorRate_of_eq_four {β : ℝ} (hβ : 2 ≤ β) (h : β = 4) (lam : ℝ) :
    errorRate β hβ lam = (lam * |Real.log lam|) ^ (1 / 21 : ℝ) := by
  simp only [errorRate, h, M0]
  norm_num

/-- `ω_λ` for `β > 4` (`M₀ = 36`): `λ^{1/20}`. -/
theorem errorRate_of_four_lt {β : ℝ} (hβ : 2 ≤ β) (h : 4 < β) (lam : ℝ) :
    errorRate β hβ lam = lam ^ (1 / 20 : ℝ) := by
  have h2 : β ≠ 2 := by linarith
  have h3 : ¬ β < 4 := by linarith
  have h4 : β ≠ 4 := by linarith
  simp only [errorRate, h2, h3, h4, ite_false, M0]
  norm_num

/-! ### Positivity and `ω_λ ≤ 1` -/

/-- `ω_λ > 0` for `0 < λ < e⁻¹`. -/
theorem errorRate_pos (β : ℝ) (hβ : 2 ≤ β) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < Real.exp (-1)) : 0 < errorRate β hβ lam := by
  have hl := one_lt_abs_log h0 h1
  by_cases h2 : β = 2
  · rw [errorRate_of_eq_two hβ h2]
    exact Real.rpow_pos_of_pos (by linarith) _
  by_cases h3 : β < 4
  · rw [errorRate_of_lt_four hβ h2 h3]
    exact Real.rpow_pos_of_pos h0 _
  by_cases h4 : β = 4
  · rw [errorRate_of_eq_four hβ h4]
    exact Real.rpow_pos_of_pos (mul_pos h0 (by linarith)) _
  · rw [errorRate_of_four_lt hβ (lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h4))]
    exact Real.rpow_pos_of_pos h0 _

/-- `ω_λ ≤ 1` for `0 < λ < e⁻¹`. -/
theorem errorRate_le_one (β : ℝ) (hβ : 2 ≤ β) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < Real.exp (-1)) : errorRate β hβ lam ≤ 1 := by
  have hl := one_lt_abs_log h0 h1
  have hlam1 : lam < 1 := h1.trans (Real.exp_lt_one_iff.2 (by norm_num))
  by_cases h2 : β = 2
  · rw [errorRate_of_eq_two hβ h2]
    exact Real.rpow_le_one_of_one_le_of_nonpos hl.le (by norm_num)
  by_cases h3 : β < 4
  · rw [errorRate_of_lt_four hβ h2 h3]
    exact Real.rpow_le_one h0.le hlam1.le (div_nonneg (by linarith) (by linarith))
  by_cases h4 : β = 4
  · rw [errorRate_of_eq_four hβ h4]
    exact Real.rpow_le_one (by positivity) (mul_abs_log_lt_one h0 hlam1).le (by norm_num)
  · rw [errorRate_of_four_lt hβ (lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h4))]
    exact Real.rpow_le_one h0.le hlam1.le (by norm_num)

/-! ### The error rates of Propositions 3.8 and 4.1 and of Lemma 3.5 are at most `ω_λ` -/

/-- **Error-rate domination, Proposition 3.8** : for `β > 2` and
`0 < λ ≤ e⁻¹`, the error rate of Proposition 3.8 (`prop:isolated`; `λ^{β-2}` for `2 < β < 4`,
`λ² ℓ²` for `β = 4`, `λ² ℓ` for `β > 4`, with `ℓ = |log λ|`) is at most `ω_λ`. -/
theorem isolatedRate_le_errorRate {β : ℝ} (hβ : 2 < β) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ Real.exp (-1)) :
    (if β < 4 then lam ^ (β - 2) else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
      else lam ^ 2 * |Real.log lam|) ≤ errorRate β hβ.le lam := by
  have hlt1 : lam < 1 := lt_of_le_of_lt h1 (Real.exp_lt_one_iff.2 (by norm_num))
  have hx1 : lam * |Real.log lam| ≤ 1 := (mul_abs_log_lt_one h0 hlt1).le
  rcases lt_trichotomy β 4 with h4 | rfl | h4
  · rw [ite_eq_left h4, errorRate_of_lt_four hβ.le hβ.ne' h4]
    refine Real.rpow_le_rpow_of_exponent_ge h0 hlt1.le ?_
    rw [div_le_iff₀ (by linarith)]
    linarith only [mul_nonneg (sub_nonneg.2 hβ.le) (show (0 : ℝ) ≤ 82 - β by linarith only [h4])]
  · rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, errorRate_of_eq_four hβ.le rfl]
    have hx0 : 0 < lam * |Real.log lam| :=
      mul_pos h0 (abs_pos.2 (Real.log_neg h0 hlt1).ne)
    have h5 : lam ^ 2 * |Real.log lam| ^ 2 = (lam * |Real.log lam|) ^ (2 : ℝ) := by
      rw [Real.rpow_two, mul_pow]
    rw [h5]
    exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by norm_num)
  · rw [ite_eq_right (not_lt.2 h4.le), ite_eq_right h4.ne', errorRate_of_four_lt hβ.le h4]
    calc lam ^ 2 * |Real.log lam| = lam * (lam * |Real.log lam|) := by ring
      _ ≤ lam * 1 := by gcongr
      _ = lam := mul_one lam
      _ ≤ lam ^ (1 / 20 : ℝ) := Real.self_le_rpow_of_le_one h0.le hlt1.le (by norm_num)

/-- **Error-rate domination, Proposition 4.1** : the error term of
Proposition 4.1 is at most `ω_λ` for `0 < λ < e⁻¹`. -/
theorem lowerRate_le_errorRate (β : ℝ) (hβ : 2 ≤ β) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < Real.exp (-1)) :
    (if β = 2 then |Real.log lam| ^ (-(1 / 5 : ℝ))
      else if β < 4 then lam ^ (β - 2)
      else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
      else lam ^ 2 * |Real.log lam|) ≤ errorRate β hβ lam := by
  by_cases h2 : β = 2
  · rw [ite_eq_left h2, errorRate_of_eq_two hβ h2]
  · have hβ2 : 2 < β := lt_of_le_of_ne hβ (Ne.symm h2)
    rw [ite_eq_right h2]
    exact isolatedRate_le_errorRate hβ2 h0 h1.le

/-- **Error-rate domination, Lemma 3.5** : the error rate `ω̄_λ` of the reduced
dipole model (eq. (def:o nn), l. 880–885) is at most `ω_λ` for `0 < λ < e⁻¹`. -/
theorem reducedRate_le_errorRate (β : ℝ) (hβ : 2 ≤ β) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < Real.exp (-1)) :
    (if β = 2 then |Real.log lam| ^ (-(1 / 2 : ℝ)) else lam ^ min ((β - 2) / 2) 1)
      ≤ errorRate β hβ lam := by
  have hl := one_lt_abs_log h0 h1
  have hlam1 : lam < 1 := h1.trans (Real.exp_lt_one_iff.2 (by norm_num))
  by_cases h2 : β = 2
  · rw [ite_eq_left h2, errorRate_of_eq_two hβ h2]
    exact Real.rpow_le_rpow_of_exponent_le hl.le (by norm_num)
  have hβ2 : 2 < β := lt_of_le_of_ne hβ (Ne.symm h2)
  rw [ite_eq_right h2]
  by_cases h3 : β < 4
  · rw [errorRate_of_lt_four hβ h2 h3]
    refine Real.rpow_le_rpow_of_exponent_ge h0 hlam1.le (le_min ?_ ?_)
    · rw [div_le_iff₀ (by linarith)]
      linarith only [mul_nonneg (sub_nonneg.2 hβ2.le) (show (0 : ℝ) ≤ 80 - β by linarith only [h3])]
    · rw [div_le_iff₀ (by linarith)]
      linarith only [h3]
  have hmin : (1 / 20 : ℝ) ≤ min ((β - 2) / 2) 1 := le_min (by linarith) (by norm_num)
  have h5 : lam ^ min ((β - 2) / 2) 1 ≤ lam ^ (1 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge h0 hlam1.le hmin
  by_cases h4 : β = 4
  · rw [errorRate_of_eq_four hβ h4]
    have h6 : lam ^ (1 / 20 : ℝ) ≤ lam ^ (1 / 21 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge h0 hlam1.le (by norm_num)
    have h7 : lam ^ (1 / 21 : ℝ) ≤ (lam * |Real.log lam|) ^ (1 / 21 : ℝ) :=
      Real.rpow_le_rpow h0.le (le_mul_of_one_le_right h0.le hl.le) (by norm_num)
    exact h5.trans (h6.trans h7)
  · rw [errorRate_of_four_lt hβ (lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h4))]
    exact h5

/-! ### Bounds on `ω_λ` for `β > 2` -/

/-- Elementary: `exp (-|log λ|) = λ` for `0 < λ < 1`. -/
private theorem exp_neg_abs_log_aux {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    Real.exp (-|Real.log lam|) = lam := by
  rw [abs_of_neg (Real.log_neg h0 h1), neg_neg, Real.exp_log h0]

/-- Elementary: `L ≤ exp (L / 2)` for `L ≥ 0`. -/
private theorem le_exp_half_aux {L : ℝ} (hL : 0 ≤ L) : L ≤ Real.exp (L / 2) := by
  have h1 : L / 4 + 1 ≤ Real.exp (L / 4) := Real.add_one_le_exp _
  have h2 : Real.exp (L / 2) = Real.exp (L / 4) * Real.exp (L / 4) := by
    rw [← Real.exp_add]
    ring_nf
  rw [h2]
  nlinarith [sq_nonneg (L / 4 - 1), mul_le_mul h1 h1 (by linarith) (Real.exp_pos _).le]

/-- Elementary: `λ |log λ| ≤ λ^{1/2}` for `0 < λ < 1`. -/
private theorem mul_abs_log_le_rpow_half_aux {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    lam * |Real.log lam| ≤ lam ^ (1 / 2 : ℝ) := by
  have hexp := exp_neg_abs_log_aux h0 h1
  have hlog : Real.log lam = -|Real.log lam| := by
    rw [abs_of_neg (Real.log_neg h0 h1), neg_neg]
  have h3 := le_exp_half_aux (abs_nonneg (Real.log lam))
  generalize |Real.log lam| = L at hexp hlog h3
  rw [Real.rpow_def_of_pos h0, hlog]
  calc lam * L = Real.exp (-L) * L := by rw [hexp]
    _ ≤ Real.exp (-L) * Real.exp (L / 2) := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = Real.exp (-L * (1 / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- For `β > 2`, `ω_λ ≤ λ^a` for some exponent `a = a_β > 0` and all `0 < λ < e⁻¹`. In
particular `ω_λ → 0` as `λ → 0`. -/
theorem exists_errorRate_le_rpow (β : ℝ) (hβ : 2 ≤ β) (h2 : 2 < β) :
    ∃ a : ℝ, 0 < a ∧ ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) →
      errorRate β hβ lam ≤ lam ^ a := by
  by_cases h3 : β < 4
  · refine ⟨2 * (β - 2) / (84 - β), div_pos (by linarith) (by linarith), fun lam h0 h1 => ?_⟩
    rw [errorRate_of_lt_four hβ h2.ne' h3]
  by_cases h4 : β = 4
  · refine ⟨1 / 42, by norm_num, fun lam h0 h1 => ?_⟩
    have hlam1 : lam < 1 := h1.trans (Real.exp_lt_one_iff.2 (by norm_num))
    rw [errorRate_of_eq_four hβ h4]
    have h5 : (lam * |Real.log lam|) ^ (1 / 21 : ℝ) ≤ (lam ^ (1 / 2 : ℝ)) ^ (1 / 21 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (mul_abs_log_le_rpow_half_aux h0 hlam1) (by norm_num)
    refine h5.trans (le_of_eq ?_)
    rw [← Real.rpow_mul h0.le]
    norm_num
  · have h6 : 4 < β := lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h4)
    refine ⟨1 / 20, by norm_num, fun lam h0 h1 => ?_⟩
    rw [errorRate_of_four_lt hβ h6]

/-- For `β > 2`, `λ^{4(β-2)/β} ≤ ω_λ` for `0 < λ < e⁻¹`. -/
theorem rpow_le_errorRate (β : ℝ) (hβ : 2 ≤ β) (h2 : 2 < β) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < Real.exp (-1)) : lam ^ (4 * (β - 2) / β) ≤ errorRate β hβ lam := by
  have hlam1 : lam < 1 := h1.trans (Real.exp_lt_one_iff.2 (by norm_num))
  have hl := one_lt_abs_log h0 h1
  by_cases h3 : β < 4
  · rw [errorRate_of_lt_four hβ h2.ne' h3]
    refine Real.rpow_le_rpow_of_exponent_ge h0 hlam1.le ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have h336 : (0 : ℝ) ≤ 336 - 6 * β := by linarith only [h3]
    linarith only [mul_nonneg (sub_nonneg.2 h2.le) h336]
  by_cases h4 : β = 4
  · rw [errorRate_of_eq_four hβ h4]
    have h5 : 4 * (β - 2) / β = 2 := by rw [h4]; norm_num
    rw [h5]
    have h6 : lam ^ (2 : ℝ) ≤ lam ^ (1 / 21 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge h0 hlam1.le (by norm_num)
    have h7 : lam ^ (1 / 21 : ℝ) ≤ (lam * |Real.log lam|) ^ (1 / 21 : ℝ) :=
      Real.rpow_le_rpow h0.le (le_mul_of_one_le_right h0.le hl.le) (by norm_num)
    exact h6.trans h7
  · have h6 : 4 < β := lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h4)
    rw [errorRate_of_four_lt hβ h6]
    refine Real.rpow_le_rpow_of_exponent_ge h0 hlam1.le ?_
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith only [h6]

/-! ### The radius `R₀` (Theorem 2, Step 5, source l. 2060–2068) -/

/-- The regime of `R₀ = ω_λ^{1/4}` at `β = 2` for `0 < λ < e⁻⁴`: `2λ ≤ R₀` and
`(1 + log |log λ| + log (1/R₀)) / |log λ| ≤ 5 ω_λ`. -/
theorem R0_regime_of_eq_two {β : ℝ} (hβ : 2 ≤ β) (h : β = 2) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < Real.exp (-4)) :
    2 * lam ≤ errorRate β hβ lam ^ (1 / 4 : ℝ) ∧
      (1 + Real.log |Real.log lam| + Real.log (1 / errorRate β hβ lam ^ (1 / 4 : ℝ)))
          / |Real.log lam| ≤ 5 * errorRate β hβ lam := by
  have hlam1 : lam < 1 := h1.trans (Real.exp_lt_one_iff.2 (by norm_num))
  have hL4 : 4 < |Real.log lam| := by
    have : Real.log lam < -4 := by
      rw [Real.log_lt_iff_lt_exp h0]
      exact h1
    rw [abs_of_neg (by linarith)]
    linarith
  have hlamL := mul_abs_log_lt_one h0 hlam1
  rw [errorRate_of_eq_two hβ h]
  generalize hLdef : |Real.log lam| = L at hL4 hlamL ⊢
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  rw [← Real.rpow_mul hL0.le]
  have he : -(1 / 5 : ℝ) * (1 / 4) = -(1 / 20) := by norm_num
  rw [he]
  constructor
  · -- `2 λ ≤ L^{-1/20}`
    have h2 : (2 : ℝ) ≤ L ^ (-(1 / 20 : ℝ)) * L := by
      have h3 : L ^ (-(1 / 20 : ℝ)) * L = L ^ (-(1 / 20 : ℝ) + 1) := by
        rw [Real.rpow_add hL0, Real.rpow_one]
      rw [h3]
      have h4 : L ^ (1 / 2 : ℝ) ≤ L ^ (-(1 / 20 : ℝ) + 1) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have h5 : (2 : ℝ) ≤ L ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.le_sqrt_of_sq_le (by linarith)
      linarith
    refine le_of_mul_le_mul_right ?_ hL0
    linarith only [h2, hlamL]
  · -- the logarithmic bound
    have hlogR : Real.log (1 / L ^ (-(1 / 20 : ℝ))) = (1 / 20) * Real.log L := by
      rw [one_div, Real.log_inv, Real.log_rpow hL0]
      ring
    rw [hlogR, div_le_iff₀ hL0]
    have hlogL : Real.log L ≤ L ^ (4 / 5 : ℝ) / (4 / 5) :=
      Real.log_le_rpow_div hL0.le (by norm_num)
    have hs1 : 1 ≤ L ^ (4 / 5 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hs3 : L ^ (-(1 / 5 : ℝ)) * L = L ^ (4 / 5 : ℝ) := by
      rw [← Real.rpow_add_one hL0.ne']
      norm_num
    rw [mul_assoc, hs3]
    linarith only [hlogL, hs1]

end TwoComponentCoulomb

end
