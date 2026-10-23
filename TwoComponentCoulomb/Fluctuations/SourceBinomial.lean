/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.BinomialEntropy
import Mathlib.Data.Nat.Choose.Sum

/-!
# The binomial calculation in Theorem 2, Step 3

Source `source/dipole-formation.tex`, proof of Theorem 2, Step 3.
The paper sums the added same-sign radial contribution by an exact
binomial identity followed by the binomial theorem. The estimates below retain
these two steps. The maximal binomial summand gives the explicit entropy factor
`(m+1) choose m q` used in the manuscript.
-/

@[expose] public section

open Finset

namespace TwoComponentCoulomb.SourceBinomial

/-- The identity and monotonicity used in the written expansion. -/
theorem choose_expansion {m q s : ℕ} (hq : q ≤ m) (hs : s ≤ q) :
    m.choose q * q.choose s = m.choose (q - s) * (m - q + s).choose s ∧
      (m - q + s).choose s ≤ m.choose s := by
  constructor
  · have h := Nat.choose_mul (n := m) (k := q) (s := q - s) (by omega)
    rw [Nat.choose_symm hs, show m - (q - s) = m - q + s by omega] at h
    simpa only [show q - (q - s) = s by omega] using h
  · exact Nat.choose_mono s (by omega)

/-- The binomial theorem bounds the truncated sum of the added constants. -/
theorem sum_choose_mul_pow_le {m q : ℕ} (hq : q ≤ m) {x : ℝ} (hx : 0 ≤ x) :
    ∑ s ∈ range (q + 1), (m.choose s : ℝ) * x ^ s ≤ (1 + x) ^ m := by
  calc _ ≤ ∑ s ∈ range (m + 1), (m.choose s : ℝ) * x ^ s := by
        exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intros; positivity)
    _ = (1 + x) ^ m := by
        rw [add_comm (1 : ℝ) x, add_pow]
        simp only [one_pow, mul_one]
        exact sum_congr rfl fun s _ => mul_comm _ _

/-- The entropy comparison preceding (eq:F(1)), with the arbitrary same-sign
allowance `exp (C₀ q)`. -/
theorem entropy_factor_le {m p₀ q : ℕ} (hpq : p₀ + q = m) (C₀ : ℝ) :
    Real.exp (m * Real.log m - p₀ * Real.log p₀ - q * Real.log q + C₀ * q) ≤
      (m + 1) * (m.choose q : ℝ) * Real.exp (C₀ * q) := by
  have hq : q ≤ m := by omega
  have h := (binomial_entropy_bounds hq).2
  rw [show m - q = p₀ by omega] at h
  have hc : (0 : ℝ) < m.choose q := by exact_mod_cast Nat.choose_pos hq
  calc _ ≤ Real.exp (Real.log (m.choose q : ℝ) + Real.log (m + 1) + C₀ * q) :=
        Real.exp_le_exp.2 (by linarith)
    _ = _ := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hc, Real.exp_log (by positivity)]
        ring

/-- The entropy comparison in the expansion, proved with the exact binomial identity.
The factor `m+1` records the conversion between entropy and binomial conventions. -/
theorem entropy_expansion_le {m p₀ q s : ℕ} (hpq : p₀ + q = m) (hs : s ≤ q) :
    Real.log (q.choose s : ℝ) +
        (m * Real.log m - p₀ * Real.log p₀ - q * Real.log q) -
        (m * Real.log m - ((p₀ + s : ℕ) : ℝ) * Real.log (p₀ + s : ℕ) -
          ((q - s : ℕ) : ℝ) * Real.log (q - s : ℕ)) ≤
      Real.log (m.choose s : ℝ) + Real.log (m + 1) := by
  have hq : q ≤ m := by omega
  have hqm : q - s ≤ m := by omega
  have hsm : s ≤ m := by omega
  have hmqs : m - (q - s) = p₀ + s := by omega
  have hmp : m - q = p₀ := by omega
  have hlo := (binomial_entropy_bounds hq).2
  have hhi := (binomial_entropy_bounds hqm).1
  rw [hmp] at hlo
  rw [hmqs] at hhi
  have he := (choose_expansion hq hs).1
  have hle := (choose_expansion hq hs).2
  have hlog := congrArg (fun n : ℕ => Real.log (n : ℝ)) he
  simp only [Nat.cast_mul] at hlog
  rw [Real.log_mul (by exact_mod_cast (Nat.choose_pos hq).ne')
    (by exact_mod_cast (Nat.choose_pos hs).ne'),
    Real.log_mul (by exact_mod_cast (Nat.choose_pos hqm).ne')
      (by exact_mod_cast (Nat.choose_pos (show s ≤ m - q + s by omega)).ne')] at hlog
  have hmono : Real.log ((m - q + s).choose s : ℝ) ≤ Real.log (m.choose s : ℝ) :=
    Real.log_le_log (by exact_mod_cast Nat.choose_pos (show s ≤ m - q + s by omega))
      (by exact_mod_cast hle)
  linarith

end TwoComponentCoulomb.SourceBinomial

end
