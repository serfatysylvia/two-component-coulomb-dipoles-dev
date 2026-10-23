/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Stirling bounds for the factorial

Source: `source/dipole-formation.tex`, l. 1735 (`N! ≥ (N/e)^N`) and l. 1803
(`log N! ≥ N log N - N + 1`), used at the end of the proof of Proposition 4.1.

* `log_factorial_stirling_le` : the upper logarithmic Stirling bound from the
  decreasing Stirling sequence.
* `log_factorial_ge` : `N log N - N + 1 ≤ log N!` for `N ≥ 1`, from the
  lower Stirling formula, with `N = 1` treated separately.
* `ofReal_exp_le_of_factorial_mul` : the assembly step of Proposition 4.1: for `N ≥ 1`, `A > 0`
  and `E ∈ ℝ`, `exp (2 N log N + N (log A - 1) - E) ≤ N! · N^N · A^N · e^{-E}`.
-/

public section

open scoped Nat

namespace TwoComponentCoulomb

/-- The upper logarithmic Stirling bound, from the monotonicity of the Stirling
sequence: `log N! ≤ N log N - N + 1 + ½ log N`. -/
theorem log_factorial_stirling_le {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N ! : ℝ) ≤ (N : ℝ) * Real.log N - N + 1 + Real.log N / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (N - 1))
  change Real.log (Stirling.stirlingSeq ((N - 1) + 1)) ≤
    Real.log (Stirling.stirlingSeq 1) at h
  rw [Nat.sub_add_cancel hN, Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
    Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.2 (by norm_num)).ne',
    Real.log_exp, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.log_mul two_ne_zero hN0.ne',
    Real.log_div hN0.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  linarith only [h]

/-- **Stirling lower bound** (source l. 1803): for `N ≥ 1`, `N log N - N + 1 ≤ log N!`. -/
theorem log_factorial_ge {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * Real.log N - N + 1 ≤ Real.log (N ! : ℝ) := by
  by_cases h1 : N = 1
  · subst N
    simp
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hst := Stirling.le_log_factorial_stirling (show N ≠ 0 by omega)
  have hexp : Real.exp 2 ≤ 2 * Real.pi * N := by
    have he : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    have h3 : Real.exp 1 < 3 := by linarith only [Real.exp_one_lt_d9]
    have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith only [h3, Real.exp_pos 1, hp, hN2,
      mul_le_mul_of_nonneg_left hN2 Real.pi_pos.le]
  have hl : 2 ≤ Real.log (2 * Real.pi) + Real.log N := by
    rw [← Real.log_mul (by positivity) hN0.ne']
    exact (Real.le_log_iff_exp_le (by positivity)).2 hexp
  linarith only [hst, hl]

/-- **Assembly step.** For `N ≥ 1`, `A > 0` and `E ∈ ℝ`,
`exp (2 N log N + N (log A - 1) - E) ≤ N! · N^N · A^N · e^{-E}`. -/
theorem ofReal_exp_le_of_factorial_mul {N : ℕ} (hN : 1 ≤ N) {A : ℝ} (hA : 0 < A) (E : ℝ) :
    ENNReal.ofReal (Real.exp (2 * N * Real.log N + N * (Real.log A - 1) - E)) ≤
      ENNReal.ofReal ((N ! : ℝ) * (N : ℝ) ^ N * A ^ N * Real.exp (-E)) := by
  refine ENNReal.ofReal_le_ofReal ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hfpos : (0 : ℝ) < (N ! : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hst := log_factorial_ge hN
  have h1 : Real.exp (2 * N * Real.log N + N * (Real.log A - 1) - E) =
      Real.exp ((N : ℝ) * Real.log N - N) * Real.exp ((N : ℝ) * Real.log N) *
        Real.exp ((N : ℝ) * Real.log A) * Real.exp (-E) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp ((N : ℝ) * Real.log N) = (N : ℝ) ^ N := by
    rw [Real.exp_nat_mul, Real.exp_log hN0]
  have h3 : Real.exp ((N : ℝ) * Real.log A) = A ^ N := by
    rw [Real.exp_nat_mul, Real.exp_log hA]
  have h4 : Real.exp ((N : ℝ) * Real.log N - N) ≤ (N ! : ℝ) := by
    calc Real.exp ((N : ℝ) * Real.log N - N) ≤ Real.exp (Real.log (N ! : ℝ)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = (N ! : ℝ) := Real.exp_log hfpos
  rw [h1, h2, h3]
  have hA' : 0 < A ^ N := by positivity
  have hN' : 0 < (N : ℝ) ^ N := by positivity
  have := Real.exp_pos (-E)
  nlinarith [mul_le_mul_of_nonneg_right h4 (mul_pos hN' hA').le, mul_pos hN' hA']

end TwoComponentCoulomb

end
