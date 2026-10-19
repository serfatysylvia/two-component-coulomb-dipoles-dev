/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# The elementary Stirling lower bound `log N! ≥ N log N - N + 1`

Source: l. 1825 (`N! ≥ (N/e)^N`) and l. 1899
(`log N! ≥ N log N - N + 1`), used at the end of the proof of Proposition 4.1.

* `log_factorial_ge` : `N log N - N + 1 ≤ log N!` for `N ≥ 1`, by induction on `N`: the increment
  of `log N! - N log N + N` is `1 - N log (1 + 1/N) ≥ 0`.
* `ofReal_exp_le_of_factorial_mul` : the assembly step of Proposition 4.1: for `N ≥ 1`, `A > 0`
  and `E ∈ ℝ`, `exp (2 N log N + N (log A - 1) - E) ≤ N! · N^N · A^N · e^{-E}`.
-/

public section

open scoped Nat

namespace TwoComponentCoulomb

/-- **Stirling lower bound** (source l. 1899): for `N ≥ 1`, `N log N - N + 1 ≤ log N!`. -/
theorem log_factorial_ge {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * Real.log N - N + 1 ≤ Real.log (N ! : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hfac : ((n + 1)! : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfpos : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hlog : Real.log (((n + 1)! : ℕ) : ℝ) = Real.log ((n : ℝ) + 1) + Real.log (n ! : ℝ) := by
      rw [hfac, Real.log_mul (by positivity) hfpos.ne']
    have hdiff : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
      have h := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
      rw [Real.log_div (by positivity) hn0.ne'] at h
      have : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
      linarith
    have hkey : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
      calc (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ n * (1 / n) :=
            mul_le_mul_of_nonneg_left hdiff hn0.le
        _ = 1 := by field_simp
    push_cast
    rw [hlog]
    nlinarith [hkey, ih]

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
