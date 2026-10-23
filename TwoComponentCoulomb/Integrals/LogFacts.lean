/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Elementary facts on `log λ` for `0 < λ ≤ e⁻¹`, and on `exp`

The standing smallness condition `0 < λ ≤ e^{-1}` of §3 (e.g. Propositions 3.6–3.8) gives
`log λ ≤ -1` and `ℓ = |log λ| ≥ 1`. These two facts are shared by many modules, as are the
elementary bounds `exp (-1) ≤ 1 / 2` and the convexity bound `e^{c s} ≤ 1 + (e^c - 1) s` for
`0 ≤ s ≤ 1`.
-/

@[expose] public section

namespace TwoComponentCoulomb

variable {lam : ℝ}

theorem log_le_neg_one (hlam : 0 < lam) (hlam1 : lam ≤ Real.exp (-1)) : Real.log lam ≤ -1 :=
  (Real.log_le_iff_le_exp hlam).2 hlam1

theorem one_le_abs_log (hlam : 0 < lam) (hlam1 : lam ≤ Real.exp (-1)) : 1 ≤ |Real.log lam| := by
  have := log_le_neg_one hlam hlam1
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- `exp (-1) ≤ 1 / 2`. -/
theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h

/-- Convexity of `exp`: `e^{c s} ≤ 1 + (e^c - 1) s` for `0 ≤ s ≤ 1` (source l. 2021–2027, used for
the tilt `e^{2t ((a/γ)² ∧ 1)}`). -/
theorem exp_mul_le_one_add {c s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (c * s) ≤ 1 + (Real.exp c - 1) * s := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ c) (sub_nonneg.2 hs1) hs0
    (by ring : 1 - s + s = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [mul_comm c]
  nlinarith [h]

end TwoComponentCoulomb

end
