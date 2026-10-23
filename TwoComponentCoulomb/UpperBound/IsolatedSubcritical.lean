/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.IsolatedOptimization

/-!
# Representative optimization with no cycle correction

For `2 < β < 3`, the parameter `2(β - 2)` is below `2`, so its cycle
correction vanishes. The paper, lines 1293–1299, 1321–1324,
applies the supremum inequality directly to `t (A - log t)` in this regime.
-/

@[expose] public section

open Finset
open scoped ENNReal

namespace TwoComponentCoulomb.IsolatedSubcritical

open IsolatedOptimization

/-- Entropy, the binomial factor and the quadratic gain, followed by the supremum
inequality without an additional logarithmic branch. -/
theorem exponent_le {p p₀ q k : ℕ} (hpq : p₀ + q = p) (hp : 0 < p) (hk : k ≤ p₀)
    (C₀ C₆ L : ℝ) :
    p * Real.log p - p₀ * Real.log p₀ - q * Real.log q + C₀ * q + Real.log (p₀.choose k)
        + p * ((q : ℝ) / p) ^ 2 + ((k + q : ℕ) : ℝ) * L + C₆ * ((k + q : ℕ) : ℝ) ≤
      p * Real.exp (2 + Real.log 2 + |C₀| + C₆ + L) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have hpq' : (p : ℝ) = p₀ + q := by exact_mod_cast hpq.symm
  have hq : (q : ℝ) ≤ p := by rw [hpq']; linarith [(Nat.cast_nonneg p₀ : (0 : ℝ) ≤ p₀)]
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  let M : ℝ := ((k + q : ℕ) : ℝ)
  have hM : M = k + q := by dsimp [M]; push_cast; ring
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hE := entropy_le hpq hp hk
  have hconc := mul_log_add_le hk0 hq0
  have hsq : (p : ℝ) * ((q : ℝ) / p) ^ 2 ≤ q := by
    rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith only [mul_le_mul_of_nonneg_left hq (mul_nonneg hq0 hP.le)]
  have hC₀ : C₀ * q ≤ |C₀| * M :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₀) hq0).trans
      (mul_le_mul_of_nonneg_left (by rw [hM]; linarith) (abs_nonneg C₀))
  have e1 := mul_log_div M (two_ne_zero : (2 : ℝ) ≠ 0)
  have e2 := mul_log_div M hP.ne'
  have hopt := mul_sub_log_le_exp (2 + Real.log 2 + |C₀| + C₆ + L) (div_nonneg hM0 hP.le)
  have hopt' := mul_le_mul_of_nonneg_left hopt hP.le
  have hcancel : (p : ℝ) * (M / p) = M := mul_div_cancel₀ M hP.ne'
  rw [← mul_assoc, hcancel] at hopt'
  have hopt'' : M * (2 + Real.log 2 + |C₀| + C₆ + L - Real.log (M / p)) ≤
      p * Real.exp (2 + Real.log 2 + |C₀| + C₆ + L) :=
    hopt'.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hP.le)
  rw [← hM] at hconc
  have e4 : M * Real.log p = k * Real.log p + q * Real.log p := by rw [hM]; ring
  linarith only [hE, hconc, hsq, hC₀, e1, e2, e4, hopt'', hM, hk0, hq0]

/-- Sum the expanded representative terms when the cycle correction is zero. -/
theorem ofReal_exp_mul_le {N p p₀ q : ℕ} (hpq : p₀ + q = p) (hp : 0 < p) (hpN : p ≤ N)
    (C₀ C₆ : ℝ) {Z m : ℝ} (hZ : 0 < Z) (hm : 0 < m) {W : ℝ≥0∞}
    (hW : W ≤ ∑ k ∈ range (p₀ + 1), (p₀.choose k : ℝ≥0∞) *
      (ENNReal.ofReal m ^ k * ENNReal.ofReal m ^ q *
        ENNReal.ofReal (Real.exp (p * Real.log N + C₆ * ((k + q : ℕ) : ℝ))))) :
    ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q + C₀ * q)) *
        (ENNReal.ofReal Z ^ p * W) ≤
      ENNReal.ofReal (Real.exp (p * Real.log N + p * Real.log Z - p * ((q : ℝ) / p) ^ 2
        + p * Real.exp (2 + Real.log 2 + |C₀| + C₆ + Real.log m) + Real.log (N + 1))) := by
  refine (mul_le_mul_right (mul_le_mul_right hW _) _).trans ?_
  refine sum_le_ofReal_exp (by omega : p₀ ≤ N) _ _ _ _ fun k hk => ?_
  have hk' : k ≤ p₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [ofReal_exp_mul_eq hZ hm hm (Nat.choose_pos hk') p k q]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h := exponent_le hpq hp hk' C₀ C₆ (Real.log m)
  have e : ((k + q : ℕ) : ℝ) * Real.log m = k * Real.log m + q * Real.log m := by
    push_cast; ring
  linarith

end TwoComponentCoulomb.IsolatedSubcritical

end
