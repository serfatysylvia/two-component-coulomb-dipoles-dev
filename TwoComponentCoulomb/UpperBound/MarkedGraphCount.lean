/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import TwoComponentCoulomb.Frozen.M0
public import TwoComponentCoulomb.Integrals.Stirling
public import TwoComponentCoulomb.NearestNeighbor.TwiceIsolated
public import TwoComponentCoulomb.UpperBound.MarkedGraphCover

/-!
# The logarithmic count of the marked graphs (Proposition 3.10, Step 1)

Source: l. 1462--1510: the enumeration of `D_{2N,K,p,p₀}` and its
logarithmic form (eq:logD), which uses the geometric constraint `K - p ≤ (M₀ + 2)(N - K)` of
eq. (eq:K-p) (`TwoComponentCoulomb.numComponents_le_numTwiceIsolated_add`).

* `TwoComponentCoulomb.mul_log_sub_le_log_factorial`, `TwoComponentCoulomb.log_factorial_le_add`:
  `n log n - n ≤ log n! ≤ n log n - n + log (n + 1) + 1`.
* `TwoComponentCoulomb.card_markedGraphs_mul_le`: the count of
  `TwoComponentCoulomb.card_markedGraphs_le` in the factorial form
  `|D| · p₀! ((N-p₀)!)² (2N-2K)! (p-p₀)! (K-p)! ≤ (N!)² (2N-2p₀)! (2N)^{2N-2K}`.
* `TwoComponentCoulomb.card_markedGraphs_le_exp` (eq:logD): for `N ≥ 2` and `p₀ ≤ p ≤ K ≤ N`,
  `|D_{2N,K,p,p₀}| ≤ exp (2N log N - (2N-2K) log ((N-K)/N) - p₀ log p₀ - (p-p₀) log (p-p₀)
    - (K-p) log (K-p) - N + C₀ log (N+1) + C₀ (N-K) + C₀ (p-p₀))` with `C₀ = 60`.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset
open scoped Nat

/-! ### Two-sided Stirling bounds -/

/-- `n log n - n ≤ log n!` for every `n` (with `0 log 0 = 0`). -/
theorem mul_log_sub_le_log_factorial (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n ! : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := log_factorial_ge hn
    linarith

/-- `log n! ≤ n log n - n + log (n + 1) + 1` for every `n`. -/
theorem log_factorial_le_add (n : ℕ) :
    Real.log (n ! : ℝ) ≤ n * Real.log n - n + Real.log (n + 1) + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
  simp only [Function.comp] at h
  have hf := Stirling.log_stirlingSeq_formula (k + 1)
  rw [Stirling.stirlingSeq_one] at h
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have h2 : Real.log (Real.exp 1 / √2) = 1 - Real.log 2 / 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp, Real.log_sqrt (by norm_num)]
  rw [h2] at h
  have hlog2 : Real.log (2 * ((k + 1 : ℕ) : ℝ)) = Real.log 2 + Real.log ((k + 1 : ℕ) : ℝ) :=
    Real.log_mul (by norm_num) hk.ne'
  have hdiv : Real.log (((k + 1 : ℕ) : ℝ) / Real.exp 1) = Real.log ((k + 1 : ℕ) : ℝ) - 1 := by
    rw [Real.log_div hk.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hmono : Real.log ((k + 1 : ℕ) : ℝ) ≤ Real.log (((k + 1 : ℕ) : ℝ) + 1) :=
    Real.log_le_log hk (by linarith)
  have hnn : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at hf h hlog2 hdiv hmono hnn ⊢
  rw [hlog2, hdiv] at hf
  linarith

/-! ### The count in factorial form -/

variable {N : ℕ}

/-- The count of Step 1 (source l. 1464--1488) in factorial form:
`|D_{2N,K,p,p₀}| · p₀! ((N-p₀)!)² (2N-2K)! (p-p₀)! (K-p)! ≤ (N!)² (2N-2p₀)! (2N)^{2N-2K}`. -/
theorem card_markedGraphs_mul_le (hN : 2 ≤ N) {K p p₀ : ℕ} (hp₀ : p₀ ≤ p) (hpK : p ≤ K)
    (hKN : K ≤ N) :
    (markedGraphs hN K p p₀).card *
        (p₀ ! * ((N - p₀)!) ^ 2 * (2 * N - 2 * K)! * (p - p₀)! * (K - p)!) ≤
      (N !) ^ 2 * (2 * N - 2 * p₀)! * (2 * N) ^ (2 * N - 2 * K) := by
  have hc := card_markedGraphs_le hN (K := K) (p := p) (p₀ := p₀)
  refine (Nat.mul_le_mul_right _ hc).trans (le_of_eq ?_)
  have e1 : N.choose p₀ * p₀ ! * (N - p₀)! = N ! :=
    Nat.choose_mul_factorial_mul_factorial (by omega)
  have e2 : (N - p₀)! * N.descFactorial p₀ = N ! := Nat.factorial_mul_descFactorial (by omega)
  have e3 : (2 * N - 2 * p₀).choose (K - p₀) * (K - p₀)! * (2 * N - 2 * p₀ - (K - p₀))! =
      (2 * N - 2 * p₀)! := Nat.choose_mul_factorial_mul_factorial (by omega)
  have e4 : (2 * N - 2 * p₀ - (K - p₀) - (K - p₀))! *
      (2 * N - 2 * p₀ - (K - p₀)).descFactorial (K - p₀) = (2 * N - 2 * p₀ - (K - p₀))! :=
    Nat.factorial_mul_descFactorial (by omega)
  have e5 : (K - p₀).choose (p - p₀) * (p - p₀)! * (K - p₀ - (p - p₀))! = (K - p₀)! :=
    Nat.choose_mul_factorial_mul_factorial (by omega)
  have h4 : 2 * N - 2 * p₀ - (K - p₀) - (K - p₀) = 2 * N - 2 * K := by omega
  have h5 : K - p₀ - (p - p₀) = K - p := by omega
  rw [h4] at e4
  rw [h5] at e5
  calc _ = (N.choose p₀ * p₀ ! * (N - p₀)!) * ((N - p₀)! * N.descFactorial p₀) *
        ((2 * N - 2 * p₀).choose (K - p₀) * ((2 * N - 2 * K)! *
          (2 * N - 2 * p₀ - (K - p₀)).descFactorial (K - p₀))) *
        ((K - p₀).choose (p - p₀) * (p - p₀)! * (K - p)!) * (2 * N) ^ (2 * N - 2 * K) := by
        ring
    _ = N ! * N ! * ((2 * N - 2 * p₀).choose (K - p₀) * (2 * N - 2 * p₀ - (K - p₀))!) *
        (K - p₀)! * (2 * N) ^ (2 * N - 2 * K) := by rw [e1, e2, e4, e5]
    _ = _ := by
        rw [← e3]
        ring

/-! ### The Stirling analysis -/

theorem two_mul_mul_log_two_mul {x : ℝ} (hx : 0 ≤ x) :
    2 * x * Real.log (2 * x) = 2 * x * Real.log 2 + 2 * (x * Real.log x) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  · rw [Real.log_mul (by norm_num) hx'.ne']
    ring

/-- For `x ≥ 0` and `y > 0`: `(2 x) log (x / y) = 2 x (log x - log y)`, also for `x = 0`. -/
theorem mul_log_div_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    2 * x * Real.log (x / y) = 2 * x * (Real.log x - Real.log y) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  · rw [Real.log_div hx'.ne' hy.ne']

theorem log_three_gt_one : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact Real.exp_one_lt_three

theorem factorial_cast_pos (n : ℕ) : (0 : ℝ) < ((n ! : ℕ) : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

/-- The Stirling analysis of the count (source l. 1489--1510), in the form `log A - log D ≤ R` for
the numerator `A` and the denominator `D` of `card_markedGraphs_mul_le`. The geometric constraint
`K ≤ p + 38 (N - K)` of eq. (eq:K-p) is used to absorb the factors `2^{N-p₀}`. -/
theorem log_count_sub_le (hN : 2 ≤ N) {K p p₀ : ℕ} (hp₀ : p₀ ≤ p) (hpK : p ≤ K) (hKN : K ≤ N)
    (h38 : K ≤ p + 38 * (N - K)) :
    Real.log (((N !) ^ 2 * (2 * N - 2 * p₀)! * (2 * N) ^ (2 * N - 2 * K) : ℕ) : ℝ) -
      Real.log ((p₀ ! * ((N - p₀)!) ^ 2 * (2 * N - 2 * K)! * (p - p₀)! * (K - p)! : ℕ) : ℝ) ≤
    2 * N * Real.log N - (2 * N - 2 * K) * Real.log (((N : ℝ) - K) / N)
      - p₀ * Real.log p₀ - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀)
      - ((K : ℝ) - p) * Real.log ((K : ℝ) - p) - N + 60 * Real.log (N + 1)
      + 60 * (N - K) + 60 * (p - p₀) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- casts of natural subtractions
  have hc1 : ((N - p₀ : ℕ) : ℝ) = N - p₀ := Nat.cast_sub (by omega)
  have hc2 : ((2 * N - 2 * p₀ : ℕ) : ℝ) = 2 * ((N : ℝ) - p₀) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hc3 : ((2 * N - 2 * K : ℕ) : ℝ) = 2 * ((N : ℝ) - K) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hc4 : ((p - p₀ : ℕ) : ℝ) = (p : ℝ) - p₀ := Nat.cast_sub hp₀
  have hc5 : ((K - p : ℕ) : ℝ) = (K : ℝ) - p := Nat.cast_sub hpK
  have hc6 : ((N - K : ℕ) : ℝ) = (N : ℝ) - K := Nat.cast_sub hKN
  have hK38 : (K : ℝ) ≤ p + 38 * ((N : ℝ) - K) := by
    have : (K : ℝ) ≤ p + 38 * ((N - K : ℕ) : ℝ) := by exact_mod_cast h38
    rwa [hc6] at this
  have hpR : (p : ℝ) ≤ K := by exact_mod_cast hpK
  have hp₀R : (p₀ : ℝ) ≤ p := by exact_mod_cast hp₀
  have hKR : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hN3 : (3 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  -- logarithms of the numerator and the denominator
  have hlA : Real.log (((N !) ^ 2 * (2 * N - 2 * p₀)! * (2 * N) ^ (2 * N - 2 * K) : ℕ) : ℝ) =
      2 * Real.log ((N ! : ℕ) : ℝ) + Real.log (((2 * N - 2 * p₀)! : ℕ) : ℝ) +
        (2 * ((N : ℝ) - K)) * (Real.log 2 + Real.log N) := by
    have hA1 : ((N ! : ℕ) : ℝ) ^ 2 ≠ 0 := (pow_pos (factorial_cast_pos N) 2).ne'
    have hA2 : (((2 * N - 2 * p₀)! : ℕ) : ℝ) ≠ 0 := (factorial_cast_pos _).ne'
    have hA3 : (2 * (N : ℝ)) ^ (2 * N - 2 * K) ≠ 0 := (pow_pos (by positivity) _).ne'
    push_cast
    rw [Real.log_mul (mul_ne_zero hA1 hA2) hA3, Real.log_mul hA1 hA2, Real.log_pow, Real.log_pow,
      Real.log_mul two_ne_zero hNpos.ne']
    push_cast
    rw [hc3]
  have hlD : Real.log ((p₀ ! * ((N - p₀)!) ^ 2 * (2 * N - 2 * K)! * (p - p₀)! * (K - p)! : ℕ) : ℝ)
      = Real.log ((p₀ ! : ℕ) : ℝ) + 2 * Real.log (((N - p₀)! : ℕ) : ℝ) +
        Real.log (((2 * N - 2 * K)! : ℕ) : ℝ) + Real.log (((p - p₀)! : ℕ) : ℝ) +
        Real.log (((K - p)! : ℕ) : ℝ) := by
    have h1 := (factorial_cast_pos p₀).ne'
    have h2 : (((N - p₀)! : ℕ) : ℝ) ^ 2 ≠ 0 := (pow_pos (factorial_cast_pos _) 2).ne'
    have h3 := (factorial_cast_pos (2 * N - 2 * K)).ne'
    have h4 := (factorial_cast_pos (p - p₀)).ne'
    have h5 := (factorial_cast_pos (K - p)).ne'
    push_cast
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4) h5,
      Real.log_mul (mul_ne_zero (mul_ne_zero h1 h2) h3) h4,
      Real.log_mul (mul_ne_zero h1 h2) h3, Real.log_mul h1 h2, Real.log_pow]
    push_cast
    ring
  -- Stirling bounds
  have u₁ := log_factorial_le_add N
  have u₂ := log_factorial_le_add (2 * N - 2 * p₀)
  have l₁ := mul_log_sub_le_log_factorial p₀
  have l₂ := mul_log_sub_le_log_factorial (N - p₀)
  have l₃ := mul_log_sub_le_log_factorial (2 * N - 2 * K)
  have l₄ := mul_log_sub_le_log_factorial (p - p₀)
  have l₅ := mul_log_sub_le_log_factorial (K - p)
  rw [hc2] at u₂
  rw [hc1] at l₂
  rw [hc3] at l₃
  rw [hc4] at l₄
  rw [hc5] at l₅
  have t₂ := two_mul_mul_log_two_mul (x := (N : ℝ) - p₀) (by linarith)
  have t₃ := two_mul_mul_log_two_mul (x := (N : ℝ) - K) (by linarith)
  have hdiv := mul_log_div_eq (x := (N : ℝ) - K) (y := N) (by linarith) hNpos
  have hL2 : Real.log (2 * ((N : ℝ) - p₀) + 1) ≤ Real.log 2 + Real.log ((N : ℝ) + 1) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    refine Real.log_le_log (by linarith only [hp₀R, hpR, hKR]) ?_
    have : (0 : ℝ) ≤ p₀ := Nat.cast_nonneg _
    linarith
  have hlog2 := Real.log_two_lt_d9
  have hL1 : 1 < Real.log ((N : ℝ) + 1) :=
    log_three_gt_one.trans_le (Real.log_le_log (by norm_num) hN3)
  have hprod : ((N : ℝ) - p₀) * Real.log 2 ≤ ((N : ℝ) - p₀) * 0.7 :=
    mul_le_mul_of_nonneg_left (by norm_num at hlog2 ⊢; linarith) (by linarith)
  rw [hlA, hlD]
  linarith

/-! ### The logarithmic count (eq:logD) -/

/-- **Equation (eq:logD)** (source l. 1507--1510). For `N ≥ 2` and `p₀ ≤ p ≤ K ≤ N`, the number of
marked graphs satisfies
`|D_{2N,K,p,p₀}| ≤ exp (2N log N - (2N-2K) log ((N-K)/N) - p₀ log p₀ - (p-p₀) log (p-p₀)
  - (K-p) log (K-p) - N + C₀ log (N+1) + C₀ (N-K) + C₀ (p-p₀))` with `C₀ = 60`, where
`0 log 0 = 0`. (For a nonempty `D_{2N,K,p,p₀}` this is `log |D| ≤ …`.) The geometric constraint
`K - p ≤ (M₀ + 2)(N - K)` of eq. (eq:K-p) holds for every element of `D_{2N,K,p,p₀}`, and is the
only place where the realizability is used. -/
theorem card_markedGraphs_le_exp (hN : 2 ≤ N) {K p p₀ : ℕ} (hp₀ : p₀ ≤ p) (hpK : p ≤ K)
    (hKN : K ≤ N) :
    ((markedGraphs hN K p p₀).card : ℝ) ≤ Real.exp
      (2 * N * Real.log N - (2 * N - 2 * K) * Real.log (((N : ℝ) - K) / N)
        - p₀ * Real.log p₀ - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀)
        - ((K : ℝ) - p) * Real.log ((K : ℝ) - p) - N + 60 * Real.log (N + 1)
        + 60 * (N - K) + 60 * (p - p₀)) := by
  rcases (markedGraphs hN K p p₀).eq_empty_or_nonempty with he | hne
  · rw [he]
    simpa using (Real.exp_pos _).le
  obtain ⟨γ, hγ⟩ := hne
  obtain ⟨Z, -, hZ, -, -, hK, hp, -⟩ := mem_markedGraphs.1 hγ
  have h38 : K ≤ p + 38 * (N - K) := by
    have := numComponents_le_numTwiceIsolated_add hN hZ.1
    rwa [hK, hp] at this
  have hmul := card_markedGraphs_mul_le hN hp₀ hpK hKN
  have hlog := log_count_sub_le hN hp₀ hpK hKN h38
  set A : ℕ := (N !) ^ 2 * (2 * N - 2 * p₀)! * (2 * N) ^ (2 * N - 2 * K) with hA
  set D : ℕ := p₀ ! * ((N - p₀)!) ^ 2 * (2 * N - 2 * K)! * (p - p₀)! * (K - p)! with hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := by
      rw [hD]
      positivity
    exact_mod_cast this
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have hN0 : 0 < 2 * N := by omega
    have : 0 < A := by
      rw [hA]
      positivity
    exact_mod_cast this
  have hcard : ((markedGraphs hN K p p₀).card : ℝ) ≤ (A : ℝ) / D := by
    rw [le_div_iff₀ hDpos]
    exact_mod_cast hmul
  refine hcard.trans ?_
  rw [← Real.exp_log (div_pos hApos hDpos), Real.log_div hApos.ne' hDpos.ne']
  exact Real.exp_le_exp.2 hlog

/-- Equation (eq:logD) with an absolute constant `C₀` (source l. 1507--1510). -/
theorem exists_card_markedGraphs_le_exp :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (K p p₀ : ℕ), p₀ ≤ p → p ≤ K → K ≤ N →
      ((markedGraphs hN K p p₀).card : ℝ) ≤ Real.exp
        (2 * N * Real.log N - (2 * N - 2 * K) * Real.log (((N : ℝ) - K) / N)
          - p₀ * Real.log p₀ - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀)
          - ((K : ℝ) - p) * Real.log ((K : ℝ) - p) - N + C₀ * Real.log (N + 1)
          + C₀ * (N - K) + C₀ * (p - p₀)) :=
  ⟨60, by norm_num, fun _ hN _ _ _ h1 h2 h3 => card_markedGraphs_le_exp hN h1 h2 h3⟩

end TwoComponentCoulomb

end
