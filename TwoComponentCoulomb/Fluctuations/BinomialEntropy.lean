/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic

/-!
# Entropy and the binomial factor in Theorem 2

Source `source/dipole-formation.tex`, the entropy comparison used before (eq:F(1))
and in Theorem 2, Step 3. For `q ≤ m`, the exponential entropy lies between
`choose m q` and `(m+1) choose m q`. The binomial summand with parameter `q/m`
is maximal at `q`. Summing its `m+1` terms proves the comparison.
-/

@[expose] public section

open Finset

namespace TwoComponentCoulomb

/-- The entropy factor is between the binomial coefficient and `m+1` times that
coefficient. Both endpoint counts are included. -/
theorem binomial_entropy_bounds {m q : ℕ} (hq : q ≤ m) :
    Real.log (m.choose q : ℝ) ≤
        m * Real.log m - q * Real.log q - ((m - q : ℕ) : ℝ) * Real.log (m - q : ℕ) ∧
      m * Real.log m - q * Real.log q - ((m - q : ℕ) : ℝ) * Real.log (m - q : ℕ) ≤
        Real.log (m.choose q : ℝ) + Real.log (m + 1) := by
  by_cases hq0 : q = 0
  · subst hq0
    simp only [Nat.choose_zero_right, Nat.cast_one, Real.log_one, Nat.cast_zero,
      zero_mul, sub_zero, Nat.sub_zero, sub_self, zero_add]
    exact ⟨le_rfl, Real.log_nonneg (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])⟩
  by_cases hqm : q = m
  · subst hqm
    simp only [Nat.choose_self, Nat.cast_one, Real.log_one, sub_self, Nat.sub_self,
      Nat.cast_zero, Real.log_zero, mul_zero, zero_add]
    exact ⟨le_rfl, Real.log_nonneg (by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])⟩
  have hqpos : 0 < q := by omega
  have hrpos : 0 < m - q := by omega
  have hmpos : 0 < m := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hrR : (0 : ℝ) < (m - q : ℕ) := by exact_mod_cast hrpos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  let T : ℕ → ℝ := fun s => (m.choose s : ℝ) * (q : ℝ) ^ s * ((m - q : ℕ) : ℝ) ^ (m - s)
  have hTnn : ∀ s, 0 ≤ T s := by intro s; dsimp [T]; positivity
  have hrel : ∀ s, s < m →
      ((s : ℝ) + 1) * (m - q : ℕ) * T (s + 1) = ((m - s : ℕ) : ℝ) * q * T s := by
    intro s hs
    have hchoose := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq m s)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hchoose
    dsimp only [T]
    have hpow : ((m - q : ℕ) : ℝ) ^ (m - s) =
        ((m - q : ℕ) : ℝ) ^ (m - (s + 1)) * (m - q : ℕ) := by
      rw [show m - s = m - (s + 1) + 1 by omega, pow_succ]
    rw [hpow, pow_succ]
    linear_combination ((q : ℝ) ^ s * ((m - q : ℕ) : ℝ) ^ (m - (s + 1)) * q *
      (m - q : ℕ)) * hchoose
  have hinc : ∀ s, s < q → T s ≤ T (s + 1) := by
    intro s hs
    have hsm : s < m := by omega
    have hcoeff : ((s : ℝ) + 1) * (m - q : ℕ) ≤ ((m - s : ℕ) : ℝ) * q := by
      rw [Nat.cast_sub hq, Nat.cast_sub hsm.le]
      have hsq : (s : ℝ) + 1 ≤ q := by exact_mod_cast hs
      nlinarith
    have hf : 0 < ((s : ℝ) + 1) * (m - q : ℕ) := by positivity
    apply (mul_le_mul_iff_right₀ hf).1
    calc _ ≤ (((m - s : ℕ) : ℝ) * q) * T s := mul_le_mul_of_nonneg_right hcoeff (hTnn s)
      _ = _ := (hrel s hsm).symm
  have hdec : ∀ s, q ≤ s → T (s + 1) ≤ T s := by
    intro s hs
    by_cases hsm : s < m
    · have hcoeff : ((m - s : ℕ) : ℝ) * q ≤ ((s : ℝ) + 1) * (m - q : ℕ) := by
        rw [Nat.cast_sub hq, Nat.cast_sub hsm.le]
        have hqs : (q : ℝ) ≤ s := by exact_mod_cast hs
        have hprod := mul_nonneg hmR.le (sub_nonneg.2 hqs)
        have hr : (q : ℝ) ≤ m := by exact_mod_cast hq
        nlinarith only [hprod, hr]
      have hf : 0 < ((s : ℝ) + 1) * (m - q : ℕ) := by positivity
      apply (mul_le_mul_iff_right₀ hf).1
      rw [hrel s hsm]
      exact mul_le_mul_of_nonneg_right hcoeff (hTnn s)
    · have hchoose : m.choose (s + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      dsimp only [T]
      rw [hchoose, Nat.cast_zero, zero_mul, zero_mul]
      exact hTnn s
  have hmax : ∀ s, T s ≤ T q := by
    intro s
    by_cases hs : s ≤ q
    · have hmono : Monotone (fun n => T (min n q)) := monotone_nat_of_le_succ fun n => by
        by_cases hn : n < q
        · simpa only [min_eq_left hn.le, min_eq_left (show n + 1 ≤ q by omega)] using hinc n hn
        · simp only [min_eq_right (show q ≤ n by omega), min_eq_right (show q ≤ n + 1 by omega)]
          exact le_rfl
      simpa only [min_eq_left hs, min_self] using hmono hs
    · exact (antitoneOn_nat_Ici_of_succ_le hdec) (by simp) (by simp; omega) (by omega)
  have hsum : ∑ s ∈ range (m + 1), T s = (m : ℝ) ^ m := by
    calc ∑ s ∈ range (m + 1), T s = ((q : ℝ) + (m - q : ℕ)) ^ m := by
          rw [add_pow]
          refine sum_congr rfl fun s _ => ?_
          dsimp only [T]
          ring
      _ = _ := by rw [Nat.cast_sub hq]; congr 1; ring
  have hlow : T q ≤ (m : ℝ) ^ m := by
    rw [← hsum]
    exact single_le_sum (fun i _ => hTnn i) (mem_range.2 (by omega))
  have hhigh : (m : ℝ) ^ m ≤ (m + 1) * T q := by
    rw [← hsum]
    have h := sum_le_card_nsmul (range (m + 1)) (fun s => T s) (T q) (fun s _ => hmax s)
    simpa only [card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using h
  have hc : (0 : ℝ) < m.choose q := by exact_mod_cast Nat.choose_pos hq
  have htq : 0 < T q := by dsimp [T]; positivity
  have hlogT : Real.log (T q) = Real.log (m.choose q : ℝ) +
      q * Real.log q + ((m - q : ℕ) : ℝ) * Real.log (m - q : ℕ) := by
    dsimp [T]
    rw [Real.log_mul (mul_pos hc (by positivity)).ne' (by positivity),
      Real.log_mul hc.ne' (by positivity), Real.log_pow, Real.log_pow]
  have hlo := Real.log_le_log htq hlow
  have hhi := Real.log_le_log (pow_pos hmR m) hhigh
  rw [hlogT, Real.log_pow] at hlo
  rw [Real.log_pow, Real.log_mul (by positivity) htq.ne', hlogT] at hhi
  constructor <;> linarith

end TwoComponentCoulomb

end
