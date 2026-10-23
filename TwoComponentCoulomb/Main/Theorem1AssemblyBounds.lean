/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TwoComponentCoulomb.Frozen.M0

/-!
# Elementary logarithm bounds for the assembly of Theorem 1

The proof of Theorem 1 (l. 1808–1837) bounds the error rates of Lemma 3.5 and Proposition 4.1
by `ω_λ = errorRate β hβ λ` (eq. (eq:defgammal), l. 221–229), the rate of Propositions 3.9 and 3.10 and
Theorem 1; these comparisons are proved in `Main/ErrorRateBounds.lean`.
This file holds the two elementary facts about `|log λ|` that they use (`λ ≤ λ |log λ| ≤ 1` for
`λ ≤ e⁻¹`, ).

* `one_lt_abs_log` : `1 < |log λ|` for `0 < λ < e⁻¹`.
* `mul_abs_log_lt_one` : `λ |log λ| < 1` for `0 < λ < 1`.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- For `0 < λ < e⁻¹`, `|log λ| > 1`. -/
theorem one_lt_abs_log {lam : ℝ} (h0 : 0 < lam) (h1 : lam < Real.exp (-1)) :
    1 < |Real.log lam| := by
  have h : Real.log lam < -1 := by
    rw [Real.log_lt_iff_lt_exp h0]
    exact h1
  rw [abs_of_neg (by linarith)]
  linarith

/-- For `0 < λ < 1`, `λ |log λ| < 1`. -/
theorem mul_abs_log_lt_one {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) : lam * |Real.log lam| < 1 := by
  have hlog : Real.log lam < 0 := Real.log_neg h0 h1
  rw [abs_of_neg hlog]
  have h := Real.log_le_sub_one_of_pos (inv_pos.2 h0)
  rw [Real.log_inv] at h
  have h2 : lam * (lam⁻¹ - 1) = 1 - lam := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h h0.le]

end TwoComponentCoulomb

end
