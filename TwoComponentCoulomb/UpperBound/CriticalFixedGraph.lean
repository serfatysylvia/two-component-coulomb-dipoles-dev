/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.CriticalCells
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The fixed-graph product at criticality

The exponential form of the retained-coordinate estimate is rewritten as the
product in (eq:critical-fixed-graph). The tree factor is `(CN/d)^d`, including
`d = 0`, where the empty product is one.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-- The Dirichlet tree factor, including the zero-tree case. -/
theorem critical_tree_factor_eq {C : ℝ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (d : ℕ) :
    (C * N / d) ^ d =
      Real.exp ((d : ℝ) * Real.log ((N : ℝ) / d) + d * Real.log C) := by
  rcases d.eq_zero_or_pos with rfl | hd
  · simp
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [show C * (N : ℝ) / d = C * (N / d) by ring,
    ← Real.exp_log (mul_pos hC (div_pos hn hd0)), ← Real.exp_nat_mul,
    Real.log_mul hC.ne' (div_pos hn hd0).ne']
  congr 1
  ring

/-- An internal product conversion of the shared cell estimate. The remaining
cycles keep the common mass `J_λ(1/ℓ)`. -/
theorem exists_critical_fixedGraphEnvelope {c₁ CJ : ℝ} (hc₁ : 0 ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N K m p₀ : ℕ), 0 < N → p₀ ≤ m → m ≤ K → K ≤ N →
      K - m ≤ 2 * (N - K) → ∀ lam Mn Ms : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      0 < Mn → 0 < Ms →
      ENNReal.ofReal (Real.exp (criticalCellExponent c₁ CJ lam Mn Ms N K m p₀)) ≤
        ENNReal.ofReal (Real.exp (C * (N - K : ℕ) + C * N / |Real.log lam|) *
          (N : ℝ) ^ K * Mn ^ p₀ * Ms ^ (m - p₀) * criticalCycleMass lam ^ (K - m) *
          (C * N / (N - K : ℕ)) ^ (N - K)) := by
  let C := 1 + 6 * c₁ + 72 / Real.pi + Real.exp CJ
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 6 * c₁ ≤ C := by
    dsimp [C]
    have hp : 0 ≤ 72 / Real.pi := by positivity
    linarith only [hp, Real.exp_pos CJ]
  have hCp : 72 / Real.pi ≤ C := by dsimp [C]; linarith only [hc₁, Real.exp_pos CJ]
  have hCe : Real.exp CJ ≤ C := by
    dsimp [C]
    have hp : 0 ≤ 72 / Real.pi := by positivity
    linarith only [hc₁, hp]
  have hCJ : CJ ≤ Real.log C := (Real.le_log_iff_exp_le hC).2 hCe
  refine ⟨C, hC, fun N K m p₀ hN hp₀ hmK hKN hr2 lam Mn Ms hlam hle hMn hMs => ?_⟩
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hj := criticalCycleMass_pos hlam hle
  have hℓ := one_le_abs_log hlam hle
  have hℓ0 : 0 < |Real.log lam| := by linarith only [hℓ]
  have hmN := hmK.trans hKN
  have hKR : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hmr : (m : ℝ) ≤ K := by exact_mod_cast hmK
  have hr : (K : ℝ) - m ≤ 2 * ((N : ℝ) - K) := by
    exact_mod_cast (show K - m ≤ 2 * (N - K) from hr2)
  have hcost : c₁ * (2 * (N : ℝ) - 2 * m) ≤ C * ((N : ℝ) - K) := by
    have h1 := mul_le_mul_of_nonneg_left hr hc₁
    have h2 := mul_le_mul_of_nonneg_right hC1 (sub_nonneg.2 hKR)
    nlinarith only [h1, h2]
  have hpack : 72 * (N : ℝ) / (Real.pi * |Real.log lam|) ≤ C * N / |Real.log lam| := by
    have h := mul_le_mul_of_nonneg_right hCp (show 0 ≤ (N : ℝ) / |Real.log lam| by positivity)
    convert h using 1 <;> ring
  have htree := mul_le_mul_of_nonneg_left hCJ (show 0 ≤ (N : ℝ) - K by linarith only [hKR])
  have hp (x : ℝ) (hx : 0 < x) (k : ℕ) : x ^ k = Real.exp ((k : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  rw [critical_tree_factor_eq hC hN, hp _ hn, hp _ hMn, hp _ hMs, hp _ hj,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  rw [criticalCellExponent, Nat.cast_sub hKN, Nat.cast_sub hp₀, Nat.cast_sub hmK]
  linear_combination hcost + hpack + htree

end TwoComponentCoulomb

end
