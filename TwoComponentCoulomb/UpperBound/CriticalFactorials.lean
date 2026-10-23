/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.CriticalGraphs
import TwoComponentCoulomb.Integrals.Stirling
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Elementary factorial estimates for the critical graph sum

Source: `source/dipole-formation.tex`, subsection 3.5, Step 3, l. 1635–1645.
The estimates `(2n)! ≤ 4^n (n!)²` and `N!/p₀! ≤ N^{N-p₀}` normalize the
fixed-graph product before the entropy optimization.
-/

@[expose] public section

open scoped Nat

namespace TwoComponentCoulomb.CriticalFactorials

/-- `(2n)! ≤ 4^n (n!)²`, including `n = 0`. -/
theorem factorial_two_mul_le (n : ℕ) : (2 * n)! ≤ 4 ^ n * (n !) ^ 2 := by
  have he := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 2 * n)
  rw [show 2 * n - n = n by omega] at he
  calc (2 * n)! = (2 * n).choose n * (n !) ^ 2 := by rw [← he]; ring
    _ ≤ 2 ^ (2 * n) * (n !) ^ 2 := Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ = _ := by rw [pow_mul]; norm_num

/-- The factorial ratio `N!/p₀! ≤ N^{N-p₀}`, without division. -/
theorem factorial_le_mul_pow {N p₀ : ℕ} (hp₀ : p₀ ≤ N) :
    N ! ≤ p₀ ! * N ^ (N - p₀) := by
  have he := Nat.factorial_mul_descFactorial (Nat.sub_le N p₀)
  rw [Nat.sub_sub_self hp₀] at he
  rw [← he]
  exact Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow N (N - p₀))

/-- **The elementary reduction of the critical graph count**. The factorials of
the unused neutral labels cancel after `(2n)! ≤ 4^n(n!)²`. One factor `N!` remains
for the normalization in Step 3 of the paper. -/
theorem card_critGraphs_elementary_mul_le {N K m p₀ : ℕ}
    (hp₀ : p₀ ≤ m) (hmK : m ≤ K) (hKN : K ≤ N) :
    (critGraphs N K m p₀).card * ((2 * N - 2 * K)! * (m - p₀)! * (K - m)! * 2 ^ (K - p₀)) ≤
      N ! * N ^ (N - p₀) * 4 ^ (N - p₀) * (2 * N) ^ (2 * N - 2 * K) := by
  have hp₀N := (hp₀.trans hmK).trans hKN
  have hsharp := card_critGraphs_mul_pow_le hp₀ hmK hKN
  have hfac := factorial_two_mul_le (N - p₀)
  rw [show 2 * (N - p₀) = 2 * N - 2 * p₀ by omega] at hfac
  have hratio := factorial_le_mul_pow hp₀N
  let A := p₀ ! * ((N - p₀)!) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hmul : ((critGraphs N K m p₀).card *
      ((2 * N - 2 * K)! * (m - p₀)! * (K - m)! * 2 ^ (K - p₀))) * A ≤
      (N ! * N ^ (N - p₀) * 4 ^ (N - p₀) * (2 * N) ^ (2 * N - 2 * K)) * A := by
    calc _ = (critGraphs N K m p₀).card *
          (p₀ ! * ((N - p₀)!) ^ 2 * (2 * N - 2 * K)! * (m - p₀)! * (K - m)! *
            2 ^ (K - p₀)) := by dsimp [A]; ring
      _ ≤ (N !) ^ 2 * (2 * N - 2 * p₀)! * (2 * N) ^ (2 * N - 2 * K) := hsharp
      _ ≤ (N !) ^ 2 * (4 ^ (N - p₀) * ((N - p₀)!) ^ 2) *
          (2 * N) ^ (2 * N - 2 * K) := by gcongr
      _ ≤ (N ! * (p₀ ! * N ^ (N - p₀))) * (4 ^ (N - p₀) * ((N - p₀)!) ^ 2) *
          (2 * N) ^ (2 * N - 2 * K) := by rw [pow_two]; gcongr
      _ = _ := by dsimp [A]; ring
  exact (mul_le_mul_iff_left₀ hA).1 (by simpa only [mul_comm A] using hmul)

/-- The elementary lower bound `k! ≥ (k/e)^k`, including the empty factorial. -/
theorem mul_log_sub_le_log_factorial (k : ℕ) :
    (k : ℝ) * Real.log k - k ≤ Real.log (k ! : ℝ) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  · linarith only [log_factorial_ge hk]

/-- **The graph count after the elementary factorial comparisons**. One factor
`N!` is retained. The three other factorials supply the tree and cycle entropies. -/
theorem card_critGraphs_le_normalized {N K m p₀ : ℕ} (hN : 0 < N)
    (hp₀ : p₀ ≤ m) (hmK : m ≤ K) (hKN : K ≤ N) :
    ((critGraphs N K m p₀).card : ℝ) ≤ Real.exp
      (Real.log (N ! : ℝ) + ((N - p₀ : ℕ) + 2 * (N - K : ℕ)) * Real.log N -
        2 * (N - K : ℕ) * Real.log (N - K : ℕ) -
        (m - p₀ : ℕ) * Real.log (m - p₀ : ℕ) -
        (K - m : ℕ) * Real.log (K - m : ℕ) +
        10 * ((N - K : ℕ) + (K - m : ℕ) + (m - p₀ : ℕ))) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let d := N - K
  let q := m - p₀
  let h := K - m
  have hd : 2 * N - 2 * K = 2 * d := by dsimp [d]; omega
  have hsum : N - p₀ = d + h + q := by dsimp [d, h, q]; omega
  have hmul := card_critGraphs_elementary_mul_le hp₀ hmK hKN
  rw [hd] at hmul
  let A := N ! * N ^ (N - p₀) * 4 ^ (N - p₀) * (2 * N) ^ (2 * d)
  let D := (2 * d)! * (q !) * (h !)
  have hmul' : (critGraphs N K m p₀).card * D ≤ A := by
    calc _ ≤ (critGraphs N K m p₀).card * D * 2 ^ (K - p₀) :=
          le_mul_of_one_le_right (Nat.zero_le _) (one_le_pow₀ (by norm_num))
      _ ≤ A := by simpa only [D, q, h, A, mul_assoc] using hmul
  have hA : (0 : ℝ) < A := by dsimp [A]; positivity
  have hD : (0 : ℝ) < D := by dsimp [D]; positivity
  have hc : ((critGraphs N K m p₀).card : ℝ) ≤ (A : ℝ) / D := by
    rw [le_div_iff₀ hD]
    exact_mod_cast hmul'
  refine hc.trans ?_
  rw [← Real.exp_log (div_pos hA hD), Real.log_div hA.ne' hD.ne']
  apply Real.exp_le_exp.2
  have hq := mul_log_sub_le_log_factorial q
  have hh := mul_log_sub_le_log_factorial h
  have hdlog : 2 * (d : ℝ) * Real.log d - 2 * d ≤ Real.log ((2 * d)! : ℝ) := by
    have ht := mul_log_sub_le_log_factorial (2 * d)
    rcases d.eq_zero_or_pos with he | he
    · simp [he]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast he
    have hl := Real.log_le_log hd0 (by linarith : (d : ℝ) ≤ 2 * d)
    push_cast at ht
    nlinarith only [ht, mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * (d : ℝ))]
  have hAlog : Real.log (A : ℝ) = Real.log (N ! : ℝ) +
      (N - p₀ : ℕ) * Real.log N + (N - p₀ : ℕ) * Real.log 4 +
      (2 * (d : ℝ)) * (Real.log 2 + Real.log N) := by
    dsimp [A]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_mul (by norm_num) hn.ne']
    push_cast
    ring
  have hDlog : Real.log (D : ℝ) = Real.log ((2 * d)! : ℝ) +
      Real.log (q ! : ℝ) + Real.log (h ! : ℝ) := by
    dsimp [D]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  rw [hAlog, hDlog]
  have hl4 : Real.log 4 ≤ 3 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hl2 : Real.log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsumR : ((N - p₀ : ℕ) : ℝ) = (d : ℝ) + h + q := by exact_mod_cast hsum
  have he1 := mul_le_mul_of_nonneg_left hl4 (Nat.cast_nonneg (N - p₀) : (0 : ℝ) ≤ (N - p₀ : ℕ))
  have he2 := mul_le_mul_of_nonneg_left hl2 (by positivity : 0 ≤ 2 * (d : ℝ))
  change _ ≤ Real.log (N ! : ℝ) + ((N - p₀ : ℕ) + 2 * (d : ℝ)) * Real.log N -
    2 * (d : ℝ) * Real.log d - (q : ℝ) * Real.log q - (h : ℝ) * Real.log h +
      10 * ((d : ℝ) + h + q)
  nlinarith only [hq, hh, hdlog, he1, he2, hsumR,
    Nat.cast_nonneg d (α := ℝ), Nat.cast_nonneg h (α := ℝ), Nat.cast_nonneg q (α := ℝ)]

end TwoComponentCoulomb.CriticalFactorials

end
