/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# The combinatorial sum in the upper bound of Lemma 3.6

Source: l. 950--968 (proof of Lemma 3.6, upper bound). After integrating
the Boltzmann weight of the reduced model against a sum over partial matchings of positive and
negative charges, a matching of size `p` contributes
`N ^ (2 N - p) A ^ p` (with `A` the mass of the pair weight), and there are
`C(N, p)² p! = (N !)² / (p ! ((N - p) !)²)` of them. The source sums this over `p`, puts `d = N - p`,
and uses `N ! / (N - d) ! ≤ N ^ d` and `∑_d (x ^ d / d !)² ≤ e ^ {2 x}` with `x = N / √A`.

* `sum_matchings_le` : for `A > 0`,
  `∑_{p ≤ N} (N !)² / (p ! ((N - p) !)²) N ^ (2 N - p) A ^ p ≤ N ! N ^ N A ^ N e ^ {2 N / √A}`.
-/

public section

open scoped Nat

namespace TwoComponentCoulomb

/-- Termwise bound (source l. 963--964): with `d = N - p`, `N ! / p ! ≤ N ^ d`, so that the `p`-th
term is at most `N ! N ^ N A ^ N (x ^ d / d !)²` with `x = N / √A`. -/
theorem matching_term_le (N p : ℕ) (hp : p ≤ N) {A : ℝ} (hA : 0 < A) :
    ((N ! : ℝ) ^ 2 / (p ! * ((N - p) ! : ℝ) ^ 2)) * (N : ℝ) ^ (2 * N - p) * A ^ p ≤
      N ! * (N : ℝ) ^ N * A ^ N * (((N : ℝ) / Real.sqrt A) ^ (N - p) / ((N - p) ! : ℝ)) ^ 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, N = p + d := ⟨N - p, by omega⟩
  have hd : p + d - p = d := by omega
  have h2 : 2 * (p + d) - p = (p + d) + d := by omega
  rw [hd, h2]
  -- `N ! ≤ p ! * N ^ d`
  have hfac : ((p + d) ! : ℝ) ≤ (p ! : ℝ) * ((p + d : ℕ) : ℝ) ^ d := by
    have h1 : (p + d - d) ! * (p + d).descFactorial d = (p + d) ! :=
      Nat.factorial_mul_descFactorial (by omega)
    have h3 : (p + d).descFactorial d ≤ (p + d) ^ d := Nat.descFactorial_le_pow _ _
    have h4 : (p + d) ! ≤ p ! * (p + d) ^ d := by
      rw [← h1, Nat.add_sub_cancel]
      exact Nat.mul_le_mul_left _ h3
    exact_mod_cast h4
  have hp0 : (0 : ℝ) < (p ! : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have hd0 : (0 : ℝ) < (d ! : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have hN0 : (0 : ℝ) ≤ ((p + d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  have hsqpos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  set M : ℝ := ((p + d : ℕ) : ℝ) with hM
  have hrhs : (M / Real.sqrt A) ^ d / (d ! : ℝ) = M ^ d / Real.sqrt A ^ d / (d ! : ℝ) := by
    rw [div_pow]
  have hAd : A ^ (p + d) = A ^ p * Real.sqrt A ^ d * Real.sqrt A ^ d := by
    rw [pow_add, mul_assoc, ← mul_pow, Real.mul_self_sqrt hA.le]
  calc ((p + d) ! : ℝ) ^ 2 / (p ! * (d ! : ℝ) ^ 2) * M ^ ((p + d) + d) * A ^ p
      = ((p + d) ! : ℝ) * (((p + d) ! : ℝ) / p !) / (d ! : ℝ) ^ 2 * M ^ ((p + d) + d) * A ^ p := by
        field_simp
    _ ≤ ((p + d) ! : ℝ) * M ^ d / (d ! : ℝ) ^ 2 * M ^ ((p + d) + d) * A ^ p := by
        gcongr
        rw [div_le_iff₀ hp0]
        calc ((p + d) ! : ℝ) ≤ (p ! : ℝ) * M ^ d := hfac
          _ = M ^ d * p ! := mul_comm _ _
    _ = ((p + d) ! : ℝ) * M ^ (p + d) * A ^ (p + d) *
          ((M / Real.sqrt A) ^ d / (d ! : ℝ)) ^ 2 := by
        rw [hrhs, hAd]
        field_simp
        ring

/-- **Source l. 958--968.** The sum over the sizes `p` of the matchings:
`∑_{p ≤ N} (N !)² / (p ! ((N - p) !)²) · N ^ (2 N - p) · A ^ p ≤ N ! · N ^ N · A ^ N · e ^ {2 N / √A}`
for `A > 0`. -/
theorem sum_matchings_le (N : ℕ) {A : ℝ} (hA : 0 < A) :
    ∑ p ∈ Finset.range (N + 1),
        ((N ! : ℝ) ^ 2 / (p ! * ((N - p) ! : ℝ) ^ 2)) * (N : ℝ) ^ (2 * N - p) * A ^ p ≤
      N ! * (N : ℝ) ^ N * A ^ N * Real.exp (2 * N / Real.sqrt A) := by
  set x : ℝ := (N : ℝ) / Real.sqrt A with hx
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg A)
  have hterm : ∀ p ∈ Finset.range (N + 1),
      ((N ! : ℝ) ^ 2 / (p ! * ((N - p) ! : ℝ) ^ 2)) * (N : ℝ) ^ (2 * N - p) * A ^ p ≤
        N ! * (N : ℝ) ^ N * A ^ N * ((x ^ (N - p) / ((N - p) ! : ℝ)) ^ 2) := fun p hp =>
    matching_term_le N p (by simpa [Nat.lt_succ_iff] using hp) hA
  calc _ ≤ ∑ p ∈ Finset.range (N + 1),
        N ! * (N : ℝ) ^ N * A ^ N * ((x ^ (N - p) / ((N - p) ! : ℝ)) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = N ! * (N : ℝ) ^ N * A ^ N * ∑ p ∈ Finset.range (N + 1),
          (x ^ (N - p) / ((N - p) ! : ℝ)) ^ 2 := by rw [Finset.mul_sum]
    _ = N ! * (N : ℝ) ^ N * A ^ N * ∑ d ∈ Finset.range (N + 1),
          (x ^ d / (d ! : ℝ)) ^ 2 := by
        congr 1
        have := Finset.sum_range_reflect (fun d : ℕ => (x ^ d / (d ! : ℝ)) ^ 2) (N + 1)
        simpa using this
    _ ≤ N ! * (N : ℝ) ^ N * A ^ N * Real.exp (2 * N / Real.sqrt A) := by
        gcongr
        calc ∑ d ∈ Finset.range (N + 1), (x ^ d / (d ! : ℝ)) ^ 2
            ≤ (∑ d ∈ Finset.range (N + 1), x ^ d / (d ! : ℝ)) ^ 2 :=
              Finset.sum_sq_le_sq_sum_of_nonneg fun d _ => by positivity
          _ ≤ (Real.exp x) ^ 2 :=
              pow_le_pow_left₀ (Finset.sum_nonneg fun d _ => by positivity)
                (Real.sum_le_exp_of_nonneg hx0 (N + 1)) 2
          _ = Real.exp (2 * N / Real.sqrt A) := by
              rw [← Real.exp_nat_mul, hx]
              congr 1
              push_cast
              ring

end TwoComponentCoulomb

end
