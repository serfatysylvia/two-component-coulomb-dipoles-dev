/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TwoComponentCoulomb.Frozen.M0

/-!
# Proposition 3.10, Steps 2--3: the real-variable calculus

Source: proof of Proposition 3.10 (`prop:upper bound`), l. 1575--1620:
the entropy estimate (l. 1575--1579), the function `χ_β` (`defchi`, l. 1587--1594) and its
optimization (Step 3, l. 1598--1620). Nothing here refers to configurations or graphs: it is pure
real analysis, consumed by the assembly of `eq:quadra x3`.

Notation (as in the source): `ℓ = |log λ|`, `α₀ = M₀ + 2`, `δ = (N - K) / N`, and `0 log 0 = 0`
(this is Mathlib's `Real.log 0 = 0`).

## Main definitions and results

* `TwoComponentCoulomb.chiBeta`: the function `χ_β(δ)` of `defchi`, with its constant `C_β` as an
  explicit argument `C`, for `β > 2`; `chiBeta β _ lam C 0 = 0` is the value of the formula.
* `TwoComponentCoulomb.mul_add_mul_log_inv_le`: `s (A + B log (1/s)) ≤ B e^{A/B - 1}`
  (l. 1598--1600).
* `TwoComponentCoulomb.entropy_le`: `-(p/N) log (p/N) - ((K-p)/N) log ((K-p)/N)
  ≤ α₀ δ log (1/δ) + C δ` for `K - p ≤ (M₀ + 2)(N - K)` (l. 1575--1579).
* `TwoComponentCoulomb.chiBeta_le_of_lt_four`, `chiBeta_le_of_eq_four`, `chiBeta_le_of_four_lt`:
  the three supremum bounds of l. 1602--1609 (compared with `errorRate` in
  `UpperBound/UpperRate.lean`, l. 1610).
* `TwoComponentCoulomb.UpperRateHyp`: the three properties of the error rate used by the whole
  `β > 2` upper-bound chain: nonnegativity, domination of the error rates `λ^{β-2}`
  (`2 < β < 4`), `λ² ℓ²` (`β = 4`), `λ² ℓ` (`β > 4`) of Proposition 3.9 (l. 1564--1566), and the
  supremum bound of Step 3. The declarations with suffix `_rate` (here and in `UpperCellBound`,
  `UpperAssembly`, `LongDipoles`) are stated for a rate function `ω` satisfying `UpperRateHyp`;
  they are instantiated at `errorRate` in `UpperBound/UpperRate.lean`, where
  `TwoComponentCoulomb.upperRateHyp_errorRate` proves that `ω_λ = errorRate` has the three
  properties.
* `TwoComponentCoulomb.exists_chiBeta_le_neg_sq_add_rate`: `χ_β(δ) ≤ -δ² + C ω(λ)` (l. 1610).
* `TwoComponentCoulomb.one_sub_div_le`, `TwoComponentCoulomb.exists_neg_sq_sub_le`:
  `1 - p₀/N ≤ (1 + α₀) δ + (p - p₀)/N` and the merging of the two quadratic gains
  (l. 1610--1619); `TwoComponentCoulomb.quadra_x3_main_term_rate` is the resulting bound for the
  main term of `eq:2cases p` (the case `p ≥ N/2`).
* `TwoComponentCoulomb.delta_ge_of_lt_half`, `TwoComponentCoulomb.exists_chiBeta_le_neg_mul`,
  `TwoComponentCoulomb.exists_chiBeta_add_le_neg`, `TwoComponentCoulomb.quadra_x3_small_p`: the
  case `p < N/2` (l. 1620): there `δ ≥ [2 (1 + α₀)]⁻¹`, `χ_β ≤ -c ℓ` uniformly, and any fixed
  crude error `C_β N` is absorbed.

`chiBeta` takes the hypothesis `2 < β` as an (unused) argument, so that it is defined exactly on
the carrier of the source (ruling R6); the constant `C_β` of `defchi` is the argument `C`.
-/

@[expose] public section

namespace TwoComponentCoulomb

theorem M0_eq : M0 = 36 := rfl

/-! ### The supremum inequality (source l. 1598--1600) -/

/-- **Supremum inequality** (source l. 1598--1600): for `B > 0` and `s ≥ 0`,
`s (A + B log (1/s)) ≤ B e^{A/B - 1}`. -/
theorem mul_add_mul_log_inv_le {A B s : ℝ} (hB : 0 < B) (hs : 0 ≤ s) :
    s * (A + B * Real.log (1 / s)) ≤ B * Real.exp (A / B - 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp only [zero_mul]
    positivity
  · have h1 := Real.add_one_le_exp (A / B - 1 - Real.log s)
    have h2 : Real.exp (A / B - 1 - Real.log s) = Real.exp (A / B - 1) / s := by
      rw [Real.exp_sub, Real.exp_log hs]
    rw [h2, le_div_iff₀ hs] at h1
    have h3 : s * (A + B * Real.log (1 / s)) =
        B * ((A / B - 1 - Real.log s + 1) * s) := by
      rw [one_div, Real.log_inv]
      field_simp
      ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left h1 hB.le

/-! ### The entropy estimate (source l. 1575--1579) -/

/-- `-x log x ≤ 1 - x` for `x ≥ 0`. -/
private theorem neg_mul_log_le_one_sub {x : ℝ} (hx : 0 ≤ x) : -(x * Real.log x) ≤ 1 - x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hx) hx.le
    have e : x * (1 - x⁻¹) = x - 1 := by field_simp
    linarith

/-- For `0 < a` and `0 ≤ y ≤ a`: `-y log y ≤ a max (log (1/a), 0) + a`. -/
private theorem neg_mul_log_le_of_le {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (hya : y ≤ a) :
    -(y * Real.log y) ≤ a * max (Real.log (1 / a)) 0 + a := by
  rcases hy.eq_or_lt with rfl | hy
  · simp only [zero_mul, neg_zero]
    positivity
  · have h1 : Real.log (a / y) ≤ a / y - 1 := Real.log_le_sub_one_of_pos (div_pos ha hy)
    have h2 : y * Real.log (a / y) ≤ a - y := by
      have h := mul_le_mul_of_nonneg_left h1 hy.le
      have e : y * (a / y - 1) = a - y := by field_simp
      linarith
    rw [Real.log_div ha.ne' hy.ne', mul_sub] at h2
    have h4 : -(y * Real.log a) ≤ a * max (Real.log (1 / a)) 0 := by
      rw [one_div, Real.log_inv]
      calc -(y * Real.log a) = y * (-Real.log a) := by ring
        _ ≤ y * max (-Real.log a) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hy.le
        _ ≤ a * max (-Real.log a) 0 := mul_le_mul_of_nonneg_right hya (le_max_right _ _)
    linarith

/-- **Entropy estimate**, real-variable form (source l. 1575--1579): if `x, y, δ ≥ 0`,
`x + y + δ = 1`, `δ ≤ 1` and `y ≤ α δ` with `α ≥ 1`, then
`-x log x - y log y ≤ α δ log (1/δ) + (2 α + 1) δ`. -/
theorem entropy_le_of_sum_eq_one {α δ x y : ℝ} (hα : 1 ≤ α) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hsum : x + y + δ = 1) (hyα : y ≤ α * δ) :
    -(x * Real.log x) - y * Real.log y ≤ α * δ * Real.log (1 / δ) + (2 * α + 1) * δ := by
  rcases hδ.eq_or_lt with rfl | hδ
  · have hy0 : y = 0 := le_antisymm (by simpa using hyα) hy
    have hx1 : x = 1 := by linarith
    subst hy0 hx1
    simp
  · have hx1 : -(x * Real.log x) ≤ (1 + α) * δ := by
      have := neg_mul_log_le_one_sub hx
      linarith only [this, hsum, hyα]
    have hαδ : 0 < α * δ := by positivity
    have hlog0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    have hy1 : -(y * Real.log y) ≤ α * δ * Real.log (1 / δ) + α * δ := by
      have h := neg_mul_log_le_of_le hαδ hy hyα
      have hlog : max (Real.log (1 / (α * δ))) 0 ≤ Real.log (1 / δ) := by
        refine max_le ?_ hlog0
        refine Real.log_le_log (by positivity) ?_
        exact one_div_le_one_div_of_le hδ (le_mul_of_one_le_left hδ.le hα)
      have := mul_le_mul_of_nonneg_left hlog hαδ.le
      linarith
    linarith

/-- **Entropy estimate** (source l. 1575--1579): for naturals `p ≤ K ≤ N`, `N ≥ 1`, with
`K - p ≤ (M₀ + 2)(N - K)` (eq. `eq:K-p`) and `δ = (N - K)/N`,
`-(p/N) log (p/N) - ((K-p)/N) log ((K-p)/N) ≤ α₀ δ log (1/δ) + C δ` with `α₀ = M₀ + 2` and the
absolute constant `C = 2 α₀ + 1`. -/
theorem entropy_le {N K p : ℕ} (hN : 1 ≤ N) (hpK : p ≤ K) (hKN : K ≤ N)
    (hKp : (K : ℝ) - p ≤ (M0 + 2) * ((N : ℝ) - K)) :
    -((p : ℝ) / N * Real.log ((p : ℝ) / N)) -
        ((K : ℝ) - p) / N * Real.log (((K : ℝ) - p) / N) ≤
      (M0 + 2) * (((N : ℝ) - K) / N) * Real.log (1 / (((N : ℝ) - K) / N)) +
        (2 * (M0 + 2) + 1) * (((N : ℝ) - K) / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpK' : (p : ℝ) ≤ K := by exact_mod_cast hpK
  have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  refine entropy_le_of_sum_eq_one (α := M0 + 2) (by rw [M0_eq]; norm_num) ?_ ?_ ?_ ?_ ?_ ?_
  · exact div_nonneg (by linarith) hNpos.le
  · rw [div_le_one hNpos]; linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  · exact div_nonneg hp0 hNpos.le
  · exact div_nonneg (by linarith) hNpos.le
  · field_simp
    ring
  · rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hKp hNpos.le

/-! ### The function `χ_β` (source `defchi`, l. 1587--1594) -/

/-- The function `χ_β(δ)` of `defchi` (source l. 1587--1594), for `β > 2`, `ℓ = |log λ|` and
`α₀ = M₀ + 2`, with the constant `C_β` as the explicit argument `C`:

* `δ [-(β-2) ℓ + (α₀ + 4 - β/2) log (1/δ) + C]` for `2 < β < 4`;
* `δ [-2 ℓ + 2 log ℓ + (α₀ + 4) log (1/δ) + C]` for `β = 4`;
* `δ [-2 ℓ + (α₀ + 2) log (1/δ) + C]` for `β > 4`.

The source's value `χ_β(0) = 0` is the value of the formula at `δ = 0`, since the bracket is
multiplied by `δ`. -/
noncomputable def chiBeta (β : ℝ) (_hβ : 2 < β) (lam C δ : ℝ) : ℝ :=
  if β < 4 then
    δ * (-(β - 2) * |Real.log lam| + (M0 + 2 + 4 - β / 2) * Real.log (1 / δ) + C)
  else if β = 4 then
    δ * (-2 * |Real.log lam| + 2 * Real.log |Real.log lam| + (M0 + 2 + 4) * Real.log (1 / δ) + C)
  else
    δ * (-2 * |Real.log lam| + (M0 + 2 + 2) * Real.log (1 / δ) + C)

section ChiEquations

variable {β : ℝ} {hβ : 2 < β} {lam C δ : ℝ}

theorem chiBeta_of_lt_four (h : β < 4) :
    chiBeta β hβ lam C δ =
      δ * (-(β - 2) * |Real.log lam| + (M0 + 2 + 4 - β / 2) * Real.log (1 / δ) + C) := by
  simp [chiBeta, h]

theorem chiBeta_of_eq_four (h : β = 4) :
    chiBeta β hβ lam C δ =
      δ * (-2 * |Real.log lam| + 2 * Real.log |Real.log lam| + (M0 + 2 + 4) * Real.log (1 / δ)
        + C) := by
  simp [chiBeta, h]

theorem chiBeta_of_four_lt (h : 4 < β) :
    chiBeta β hβ lam C δ =
      δ * (-2 * |Real.log lam| + (M0 + 2 + 2) * Real.log (1 / δ) + C) := by
  simp [chiBeta, not_lt.2 h.le, h.ne']

/-- `χ_β(0) = 0` (source l. 1587). -/
theorem chiBeta_zero : chiBeta β hβ lam C 0 = 0 := by
  simp [chiBeta]

/-- Shifting the constant `C_β` by `c` adds `c δ`. -/
theorem chiBeta_add_const (c : ℝ) :
    chiBeta β hβ lam (C + c) δ = chiBeta β hβ lam C δ + c * δ := by
  unfold chiBeta
  split_ifs <;> ring

end ChiEquations

/-! ### The supremum of `χ_β` (source l. 1597--1609) -/

section Sup

theorem abs_log_eq {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    |Real.log lam| = -Real.log lam :=
  abs_of_neg (Real.log_neg h0 h1)

private theorem exp_mul_log_add {lam c d : ℝ} (h0 : 0 < lam) :
    Real.exp (c * Real.log lam + d) = Real.exp d * lam ^ c := by
  rw [Real.exp_add, Real.rpow_def_of_pos h0, mul_comm, mul_comm (Real.log lam) c]

/-- **Supremum of `χ_β`, case `2 < β < 4`** (source l. 1602--1605): by the supremum inequality,
`χ_β(δ) ≤ B e^{C/B - 1} λ^{2(β-2)/(12-β+2M₀)}` with `B = α₀ + 4 - β/2`. -/
theorem chiBeta_le_of_lt_four {β : ℝ} (hβ : 2 < β) (h4 : β < 4) (C : ℝ) {lam δ : ℝ}
    (h0 : 0 < lam) (h1 : lam < 1) (hδ : 0 ≤ δ) :
    chiBeta β hβ lam C δ ≤ (M0 + 2 + 4 - β / 2) * Real.exp (C / (M0 + 2 + 4 - β / 2) - 1) *
      lam ^ (2 * (β - 2) / (12 - β + 2 * M0)) := by
  have hB : 0 < M0 + 2 + 4 - β / 2 := by rw [M0_eq]; linarith
  have hDB : 12 - β + 2 * M0 = 2 * (M0 + 2 + 4 - β / 2) := by ring
  rw [chiBeta_of_lt_four h4, abs_log_eq h0 h1]
  have key := mul_add_mul_log_inv_le (A := (β - 2) * Real.log lam + C) hB hδ
  have e1 : δ * (-(β - 2) * -Real.log lam + (M0 + 2 + 4 - β / 2) * Real.log (1 / δ) + C) =
      δ * ((β - 2) * Real.log lam + C + (M0 + 2 + 4 - β / 2) * Real.log (1 / δ)) := by ring
  rw [e1]
  refine key.trans (le_of_eq ?_)
  have e2 : ((β - 2) * Real.log lam + C) / (M0 + 2 + 4 - β / 2) - 1 =
      (2 * (β - 2) / (12 - β + 2 * M0)) * Real.log lam + (C / (M0 + 2 + 4 - β / 2) - 1) := by
    rw [hDB, mul_div_mul_left _ _ two_ne_zero]
    ring
  rw [e2, exp_mul_log_add h0]
  ring

/-- **Supremum of `χ_β`, case `β = 4`** (source l. 1605--1606): by the supremum inequality,
`χ_4(δ) ≤ (M₀ + 6) e^{C/(M₀+6) - 1} (λ ℓ)^{2/(M₀+6)}`. -/
theorem chiBeta_le_of_eq_four (hβ : 2 < (4 : ℝ)) (C : ℝ) {lam δ : ℝ}
    (h0 : 0 < lam) (h1 : lam < 1) (hδ : 0 ≤ δ) :
    chiBeta 4 hβ lam C δ ≤ (M0 + 6) * Real.exp (C / (M0 + 6) - 1) *
      (lam * |Real.log lam|) ^ (2 / (M0 + 6)) := by
  have hB : 0 < M0 + 6 := by rw [M0_eq]; norm_num
  have hℓ : 0 < -Real.log lam := neg_pos.2 (Real.log_neg h0 h1)
  rw [chiBeta_of_eq_four rfl, abs_log_eq h0 h1]
  have key := mul_add_mul_log_inv_le
    (A := 2 * Real.log (lam * -Real.log lam) + C) hB hδ
  rw [Real.log_mul h0.ne' hℓ.ne'] at key
  have e1 : δ * (-2 * -Real.log lam + 2 * Real.log (-Real.log lam) + (M0 + 2 + 4) *
      Real.log (1 / δ) + C) =
      δ * (2 * (Real.log lam + Real.log (-Real.log lam)) + C + (M0 + 6) * Real.log (1 / δ)) := by
    ring
  rw [e1]
  have e2 : (2 * (Real.log lam + Real.log (-Real.log lam)) + C) / (M0 + 6) - 1 =
      (2 / (M0 + 6)) * Real.log (lam * -Real.log lam) + (C / (M0 + 6) - 1) := by
    rw [Real.log_mul h0.ne' hℓ.ne']
    ring
  refine key.trans (le_of_eq ?_)
  rw [e2, exp_mul_log_add (mul_pos h0 hℓ)]
  ring

/-- **Supremum of `χ_β`, case `β > 4`** (source l. 1606--1607): by the supremum inequality,
`χ_β(δ) ≤ (M₀ + 4) e^{C/(M₀+4) - 1} λ^{2/(M₀+4)}`. -/
theorem chiBeta_le_of_four_lt {β : ℝ} (hβ : 2 < β) (h4 : 4 < β) (C : ℝ) {lam δ : ℝ}
    (h0 : 0 < lam) (h1 : lam < 1) (hδ : 0 ≤ δ) :
    chiBeta β hβ lam C δ ≤ (M0 + 4) * Real.exp (C / (M0 + 4) - 1) * lam ^ (2 / (M0 + 4)) := by
  have hB : 0 < M0 + 4 := by rw [M0_eq]; norm_num
  rw [chiBeta_of_four_lt h4, abs_log_eq h0 h1]
  have key := mul_add_mul_log_inv_le (A := 2 * Real.log lam + C) hB hδ
  have e1 : δ * (-2 * -Real.log lam + (M0 + 2 + 2) * Real.log (1 / δ) + C) =
      δ * (2 * Real.log lam + C + (M0 + 4) * Real.log (1 / δ)) := by ring
  rw [e1]
  have e2 : (2 * Real.log lam + C) / (M0 + 4) - 1 =
      (2 / (M0 + 4)) * Real.log lam + (C / (M0 + 4) - 1) := by
    ring
  refine key.trans (le_of_eq ?_)
  rw [e2, exp_mul_log_add h0]
  ring

end Sup

/-! The error rates of Proposition 3.9 are compared with `ω_λ` through the field `isolated_le` of
`UpperRateHyp` (for `errorRate`: `TwoComponentCoulomb.isolatedRate_le_errorRate`,
`Main/ErrorRateBounds.lean`). -/

/-! ### The rate hypotheses of the upper bound for `β > 2` -/

/-- **The rate hypotheses of the upper bound for `β > 2`.** The proof of Proposition 3.10 for
`β > 2` (source l. 1459--1664) uses only three properties of the error rate `λ ↦ ω_λ`; a function
`ω : ℝ → ℝ` with these properties can replace `ω_λ` throughout the `β > 2` chain (the `_rate`
declarations). The properties are: `ω` is nonnegative; it dominates the error rates of
Proposition 3.9 (l. 1237--1246); and it dominates the supremum of `χ_β` (Step 3, l. 1598--1610).
The rate `errorRate` satisfies them (`upperRateHyp_errorRate`, `UpperBound/UpperRate.lean`). -/
structure UpperRateHyp (β : ℝ) (hβ : 2 < β) (ω : ℝ → ℝ) : Prop where
  /-- `ω_λ ≥ 0` for `λ > 0`. -/
  nonneg : ∀ lam, 0 < lam → 0 ≤ ω lam
  /-- The error rates `λ^{β-2}`, `λ² ℓ²`, `λ² ℓ` (`2 < β < 4`, `β = 4`, `β > 4`) of
  Proposition 3.9 are at most `ω_λ` for `0 < λ ≤ e⁻¹`. -/
  isolated_le : ∀ lam, 0 < lam → lam ≤ Real.exp (-1) →
    (if β < 4 then lam ^ (β - 2) else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
      else lam ^ 2 * |Real.log lam|) ≤ ω lam
  /-- Step 3: for every constant `C = C_β` of `defchi` there is `C'` with
  `χ_β(δ) ≤ C' ω_λ` for all `0 < λ < 1` and `δ ≥ 0`. -/
  chi_le : ∀ C : ℝ, ∃ C' : ℝ, 0 < C' ∧ ∀ lam δ : ℝ, 0 < lam → lam < 1 → 0 ≤ δ →
    chiBeta β hβ lam C δ ≤ C' * ω lam

/-! ### `χ_β ≤ -δ² + C ω_λ` (source l. 1609--1610) -/

/-- **`χ_β(δ) ≤ -δ² + C'' ω_λ`, generic rate** (source l. 1610): for a rate
`ω` satisfying `UpperRateHyp`, applying its supremum bound to `χ_β(δ) + δ²` (the constant `C + 1`)
and using `δ² ≤ δ`. The constant `C''` depends only on `β`, `ω` and `C`; the estimate holds for
all `0 < λ < 1` and `δ ∈ [0, 1]`. -/
theorem exists_chiBeta_le_neg_sq_add_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ)
    (hω : UpperRateHyp β hβ ω) (C : ℝ) :
    ∃ C'' : ℝ, 0 < C'' ∧ ∀ lam δ : ℝ, 0 < lam → lam < 1 → 0 ≤ δ → δ ≤ 1 →
      chiBeta β hβ lam C δ ≤ -δ ^ 2 + C'' * ω lam := by
  obtain ⟨C'', hC'', h⟩ := hω.chi_le (C + 1)
  refine ⟨C'', hC'', fun lam δ h0 h1 hδ hδ1 => ?_⟩
  have h2 := h lam δ h0 h1 hδ
  rw [chiBeta_add_const] at h2
  linarith only [h2, mul_nonneg hδ (sub_nonneg.2 hδ1)]

/-! ### The quadratic merge (source l. 1611--1615) -/

/-- **`1 - p₀/N ≤ (1 + α₀) δ + (p - p₀)/N`** (source l. 1611--1613), from `N - p₀ = (N - K) +
(K - p) + (p - p₀)` and `K - p ≤ α₀ (N - K)` (eq. `eq:K-p`). -/
theorem one_sub_div_le {N K p p₀ : ℕ} (hN : 1 ≤ N)
    (hKp : (K : ℝ) - p ≤ (M0 + 2) * ((N : ℝ) - K)) :
    1 - (p₀ : ℝ) / N ≤ (1 + (M0 + 2)) * (((N : ℝ) - K) / N) + ((p : ℝ) - p₀) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← sub_nonneg]
  have e : (1 + (M0 + 2)) * (((N : ℝ) - K) / N) + ((p : ℝ) - p₀) / N - (1 - (p₀ : ℝ) / N) =
      ((1 + (M0 + 2)) * ((N : ℝ) - K) + p - N) / N := by
    field_simp
    ring
  rw [e]
  exact div_nonneg (by linarith only [hKp]) hNpos.le

/-- **Merging the two quadratic gains** (source l. 1613--1615): for `c > 0` there is an absolute
`c' > 0` (depending only on `c`) with
`-δ² - c ((p - p₀)/N)² ≤ -c' (1 - p₀/N)²`, where `δ = (N - K)/N`, for `p₀ ≤ N` and
`K - p ≤ (M₀ + 2)(N - K)`. It follows from `(a + b)² ≤ 2 a² + 2 b²` and
`1 - p₀/N ≤ (1 + α₀) δ + (p - p₀)/N`. -/
theorem exists_neg_sq_sub_le {c : ℝ} (hc : 0 < c) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ {N K p p₀ : ℕ}, 1 ≤ N → p₀ ≤ N →
      (K : ℝ) - p ≤ (M0 + 2) * ((N : ℝ) - K) →
      -(((N : ℝ) - K) / N) ^ 2 - c * (((p : ℝ) - p₀) / N) ^ 2 ≤ -(c' * (1 - (p₀ : ℝ) / N) ^ 2) := by
  have hk : 0 < 1 + (M0 + 2) := by rw [M0_eq]; norm_num
  refine ⟨min (c / 2) (1 / (2 * (1 + (M0 + 2)) ^ 2)), lt_min (by positivity) (by positivity), ?_⟩
  intro N K p p₀ hN hp₀ hKp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hp₀' : (p₀ : ℝ) ≤ N := by exact_mod_cast hp₀
  set c' := min (c / 2) (1 / (2 * (1 + (M0 + 2)) ^ 2)) with hc'
  have hc'0 : 0 < c' := lt_min (by positivity) (by positivity)
  have h1 : 2 * c' ≤ c := by
    have := min_le_left (c / 2) (1 / (2 * (1 + (M0 + 2)) ^ 2))
    linarith
  have h2 : 2 * c' * (1 + (M0 + 2)) ^ 2 ≤ 1 := by
    have h := min_le_right (c / 2) (1 / (2 * (1 + (M0 + 2)) ^ 2))
    have h' : c' * (2 * (1 + (M0 + 2)) ^ 2) ≤ 1 := by
      rw [← le_div_iff₀ (by positivity)]
      exact h
    linarith
  set δ := ((N : ℝ) - K) / N with hδ
  set b := ((p : ℝ) - p₀) / N with hb
  set u := 1 - (p₀ : ℝ) / N with hu
  have hu0 : 0 ≤ u := by
    rw [hu, sub_nonneg, div_le_one hNpos]
    exact hp₀'
  have hule : u ≤ (1 + (M0 + 2)) * δ + b := one_sub_div_le hN hKp
  have h3 : u ^ 2 ≤ ((1 + (M0 + 2)) * δ + b) ^ 2 := pow_le_pow_left₀ hu0 hule 2
  have h4 : ((1 + (M0 + 2)) * δ + b) ^ 2 ≤ 2 * (1 + (M0 + 2)) ^ 2 * δ ^ 2 + 2 * b ^ 2 := by
    linarith only [sq_nonneg ((1 + (M0 + 2)) * δ - b)]
  have h5 : c' * u ^ 2 ≤ c' * (2 * (1 + (M0 + 2)) ^ 2 * δ ^ 2 + 2 * b ^ 2) :=
    mul_le_mul_of_nonneg_left (h3.trans h4) hc'0.le
  have h6 := mul_le_mul_of_nonneg_right h2 (sq_nonneg δ)
  have h7 := mul_le_mul_of_nonneg_right h1 (sq_nonneg b)
  linarith only [h5, h6, h7]

/-- **The main term of `eq:2cases p` for the case `p ≥ N/2`, generic rate** (source
l. 1610--1619): for a rate `ω` satisfying `UpperRateHyp` and the constants `C = C_β`,
`c = c_β > 0` of `eq:2cases p` there are `c' > 0` and `C'' > 0`, depending only on `β`, `ω`, `C`
and `c`, with `N χ_β(δ) - c (p - p₀)²/N ≤ -c' (N - p₀)²/N + C'' N ω_λ` for `δ = (N - K)/N`,
`0 < λ < 1`, `1 ≤ N`, `p₀ ≤ N`, `K ≤ N` and `K - p ≤ (M₀ + 2)(N - K)`. -/
theorem quadra_x3_main_term_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) (hω : UpperRateHyp β hβ ω)
    (C c : ℝ) (hc : 0 < c) :
    ∃ c' C'' : ℝ, 0 < c' ∧ 0 < C'' ∧ ∀ (lam : ℝ) (N K p p₀ : ℕ), 0 < lam → lam < 1 → 1 ≤ N →
      p₀ ≤ N → K ≤ N → (K : ℝ) - p ≤ (M0 + 2) * ((N : ℝ) - K) →
      (N : ℝ) * chiBeta β hβ lam C (((N : ℝ) - K) / N) - c * ((p : ℝ) - p₀) ^ 2 / N ≤
        -(c' * ((N : ℝ) - p₀) ^ 2 / N) + C'' * N * ω lam := by
  obtain ⟨C'', hC'', h5⟩ := exists_chiBeta_le_neg_sq_add_rate hβ ω hω C
  obtain ⟨c', hc', h6⟩ := exists_neg_sq_sub_le hc
  refine ⟨c', C'', hc', hC'', ?_⟩
  intro lam N K p p₀ h0 h1 hN hp₀ hKN hKp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hδ0 : 0 ≤ ((N : ℝ) - K) / N := div_nonneg (by linarith) hNpos.le
  have hδ1 : ((N : ℝ) - K) / N ≤ 1 := by
    rw [div_le_one hNpos]
    linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have h7 := mul_le_mul_of_nonneg_left (h5 lam _ h0 h1 hδ0 hδ1) hNpos.le
  have h8 := mul_le_mul_of_nonneg_left (h6 hN hp₀ hKp) hNpos.le
  have e1 : (N : ℝ) * (-(((N : ℝ) - K) / N) ^ 2 - c * (((p : ℝ) - p₀) / N) ^ 2) =
      -((N : ℝ) * (((N : ℝ) - K) / N) ^ 2) - c * ((p : ℝ) - p₀) ^ 2 / N := by
    field_simp
  have e2 : (N : ℝ) * -(c' * (1 - (p₀ : ℝ) / N) ^ 2) = -(c' * ((N : ℝ) - p₀) ^ 2 / N) := by
    field_simp
  have e3 : (N : ℝ) * (-((N - K) / N) ^ 2 + C'' * ω lam) =
      -((N : ℝ) * (((N : ℝ) - K) / N) ^ 2) + C'' * N * ω lam := by
    ring
  rw [e1, e2] at h8
  rw [e3] at h7
  linarith

/-! ### The case `p < N/2` (source l. 1620) -/

/-- **`δ ≥ [2 (1 + α₀)]⁻¹` for `p < N/2`** (source l. 1620): from `N/2 < N - p ≤ (1 + α₀)(N - K)`,
which uses `K - p ≤ α₀ (N - K)` (eq. `eq:K-p`). -/
theorem delta_ge_of_lt_half {N K p : ℕ} (hN : 1 ≤ N) (hp : (p : ℝ) < N / 2)
    (hKp : (K : ℝ) - p ≤ (M0 + 2) * ((N : ℝ) - K)) :
    1 / (2 * (1 + (M0 + 2))) ≤ ((N : ℝ) - K) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : 0 < 2 * (1 + (M0 + 2)) := by rw [M0_eq]; norm_num
  rw [div_le_div_iff₀ hk hNpos]
  linarith only [hp, hKp]

section SmallP

/-- The bracket of `χ_β` for `δ ≥ δ₀`: `χ_β(δ) = δ · Br` with `Br ≤ D - m ℓ`, where
`m = min (β - 2) 1`, `D = (M₀ + 6) log (2 (1 + α₀)) + |C|` and `ℓ = |log λ|`. -/
private theorem exists_bracket {β : ℝ} (hβ : 2 < β) (C : ℝ) {lam δ : ℝ} (h0 : 0 < lam)
    (h1 : lam < 1) (hδ0 : 1 / (2 * (1 + (M0 + 2))) ≤ δ) (hδ1 : δ ≤ 1) :
    ∃ Br : ℝ, chiBeta β hβ lam C δ = δ * Br ∧
      Br ≤ (M0 + 6) * Real.log (2 * (1 + (M0 + 2))) + |C| - min (β - 2) 1 * |Real.log lam| := by
  have hk : 1 < 2 * (1 + (M0 + 2)) := by rw [M0_eq]; norm_num
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδ0
  have hL0 : 0 ≤ Real.log (2 * (1 + (M0 + 2))) := Real.log_nonneg hk.le
  have hlog0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
  have hlogL : Real.log (1 / δ) ≤ Real.log (2 * (1 + (M0 + 2))) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ hδpos]
    rw [div_le_iff₀ (by linarith)] at hδ0
    linarith
  have hℓ : 0 ≤ |Real.log lam| := abs_nonneg _
  have hℓ' : 0 < -Real.log lam := neg_pos.2 (Real.log_neg h0 h1)
  have hm1 : min (β - 2) 1 ≤ β - 2 := min_le_left _ _
  have hm2 : min (β - 2) 1 ≤ 1 := min_le_right _ _
  have hC : C ≤ |C| := le_abs_self C
  rcases lt_trichotomy β 4 with h4 | rfl | h4
  · refine ⟨_, chiBeta_of_lt_four h4, ?_⟩
    have hB : (M0 + 2 + 4 - β / 2) * Real.log (1 / δ) ≤ (M0 + 6) * Real.log (2 * (1 + (M0 + 2))) :=
      mul_le_mul (by linarith) hlogL hlog0 (by rw [M0_eq]; norm_num)
    have hmℓ := mul_le_mul_of_nonneg_right hm1 hℓ
    linarith only [hB, hC, hmℓ]
  · refine ⟨_, chiBeta_of_eq_four rfl, ?_⟩
    have hB : (M0 + 2 + 4) * Real.log (1 / δ) ≤ (M0 + 6) * Real.log (2 * (1 + (M0 + 2))) := by
      have := mul_le_mul_of_nonneg_left hlogL (show 0 ≤ M0 + 6 by rw [M0_eq]; norm_num)
      linarith
    have hlg : Real.log |Real.log lam| ≤ |Real.log lam| / 2 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < |Real.log lam| / Real.exp 1 by
        rw [abs_log_eq h0 h1]; positivity)
      rw [Real.log_div (by rw [abs_log_eq h0 h1]; exact hℓ'.ne') (Real.exp_pos 1).ne',
        Real.log_exp] at h
      have he : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have : |Real.log lam| / Real.exp 1 ≤ |Real.log lam| / 2 :=
        div_le_div_of_nonneg_left hℓ (by norm_num) he
      linarith
    have hm4 : min ((4 : ℝ) - 2) 1 = 1 := by norm_num
    rw [hm4]
    linarith
  · refine ⟨_, chiBeta_of_four_lt h4, ?_⟩
    have hB : (M0 + 2 + 2) * Real.log (1 / δ) ≤ (M0 + 6) * Real.log (2 * (1 + (M0 + 2))) :=
      mul_le_mul (by rw [M0_eq]; norm_num) hlogL hlog0 (by rw [M0_eq]; norm_num)
    have hmℓ := mul_le_mul_of_nonneg_right hm2 hℓ
    linarith only [hB, hC, hmℓ, hℓ]

/-- **`χ_β ≤ -c ℓ` for `δ ≥ δ₀`** (source l. 1620, "`χ_β(δ) → -∞` uniformly"): with
`δ₀ = [2 (1 + α₀)]⁻¹` there are `c > 0` and `0 < λ₀ < 1`, depending only on `β` and `C`, with
`χ_β(δ) ≤ -c |log λ|` for all `0 < λ ≤ λ₀` and `δ ∈ [δ₀, 1]`. -/
theorem exists_chiBeta_le_neg_mul {β : ℝ} (hβ : 2 < β) (C : ℝ) :
    ∃ c lam₀ : ℝ, 0 < c ∧ 0 < lam₀ ∧ lam₀ < 1 ∧ ∀ lam δ : ℝ, 0 < lam → lam ≤ lam₀ →
      1 / (2 * (1 + (M0 + 2))) ≤ δ → δ ≤ 1 → chiBeta β hβ lam C δ ≤ -(c * |Real.log lam|) := by
  have hk : 0 < 2 * (1 + (M0 + 2)) := by rw [M0_eq]; norm_num
  have hL0 : 0 ≤ Real.log (2 * (1 + (M0 + 2))) := Real.log_nonneg (by rw [M0_eq]; norm_num)
  have hm0 : 0 < min (β - 2) 1 := lt_min (by linarith) one_pos
  have hD0 : 0 ≤ (M0 + 6) * Real.log (2 * (1 + (M0 + 2))) + |C| :=
    add_nonneg (mul_nonneg (by rw [M0_eq]; norm_num) hL0) (abs_nonneg _)
  set m := min (β - 2) 1 with hm
  set D := (M0 + 6) * Real.log (2 * (1 + (M0 + 2))) + |C| with hD
  have hexp : -(2 * D / m + 1) < 0 := by
    have : 0 ≤ 2 * D / m := by positivity
    linarith
  refine ⟨1 / (2 * (1 + (M0 + 2))) * m / 2, Real.exp (-(2 * D / m + 1)),
    div_pos (mul_pos (one_div_pos.2 hk) hm0) two_pos, Real.exp_pos _, Real.exp_lt_one_iff.2 hexp, ?_⟩
  intro lam δ h0 hle hδ0 hδ1
  have hlam1 : lam < 1 :=
    lt_of_le_of_lt hle (Real.exp_lt_one_iff.2 hexp)
  have hlogle : Real.log lam ≤ -(2 * D / m + 1) := (Real.log_le_iff_le_exp h0).2 hle
  have hℓ : |Real.log lam| = -Real.log lam := abs_log_eq h0 hlam1
  obtain ⟨Br, hchi, hBr⟩ := exists_bracket hβ C h0 hlam1 hδ0 hδ1
  have hmℓ : 2 * D ≤ m * |Real.log lam| := by
    have h2 : 2 * D / m ≤ |Real.log lam| := by linarith
    rw [div_le_iff₀ hm0] at h2
    linarith
  have hBr' : Br ≤ -(m * |Real.log lam| / 2) := by linarith
  have hnonneg : 0 ≤ m * |Real.log lam| := mul_nonneg hm0.le (abs_nonneg _)
  have hneg : Br ≤ 0 := hBr'.trans (by linarith)
  rw [hchi]
  calc δ * Br ≤ 1 / (2 * (1 + (M0 + 2))) * Br := mul_le_mul_of_nonpos_right hδ0 hneg
    _ ≤ 1 / (2 * (1 + (M0 + 2))) * (-(m * |Real.log lam| / 2)) :=
        mul_le_mul_of_nonneg_left hBr' (one_div_pos.2 hk).le
    _ = -(1 / (2 * (1 + (M0 + 2))) * m / 2 * |Real.log lam|) := by ring

/-- **`χ_β + C_β' ≤ -T` for `δ ≥ δ₀` and `λ` small** (source l. 1620): for any constants
`Cb` (a crude error `C_β` of the source, absorbed per unit `N`) and `T`, there is `0 < λ₀ < 1`,
depending only on `β`, `C`, `Cb` and `T`, with `χ_β(δ) + Cb ≤ -T` for `0 < λ ≤ λ₀` and
`δ ∈ [[2 (1 + α₀)]⁻¹, 1]`. -/
theorem exists_chiBeta_add_le_neg {β : ℝ} (hβ : 2 < β) (C Cb T : ℝ) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ < 1 ∧ ∀ lam δ : ℝ, 0 < lam → lam ≤ lam₀ →
      1 / (2 * (1 + (M0 + 2))) ≤ δ → δ ≤ 1 → chiBeta β hβ lam C δ + Cb ≤ -T := by
  obtain ⟨c, lam₁, hc, h1, h1', h⟩ := exists_chiBeta_le_neg_mul hβ C
  refine ⟨min lam₁ (Real.exp (-(|Cb + T| / c + 1))), lt_min h1 (Real.exp_pos _),
    lt_of_le_of_lt (min_le_left _ _) h1', ?_⟩
  intro lam δ h0 hle hδ0 hδ1
  have hlam1 : lam < 1 := lt_of_le_of_lt (hle.trans (min_le_left _ _)) h1'
  have hlog : Real.log lam ≤ -(|Cb + T| / c + 1) :=
    (Real.log_le_iff_le_exp h0).2 (hle.trans (min_le_right _ _))
  have hℓ : |Real.log lam| = -Real.log lam := abs_log_eq h0 hlam1
  have h2 := h lam δ h0 (hle.trans (min_le_left _ _)) hδ0 hδ1
  have h3 : |Cb + T| / c ≤ |Real.log lam| := by linarith
  rw [div_le_iff₀ hc] at h3
  have h4 : Cb + T ≤ |Cb + T| := le_abs_self _
  linarith only [h2, h3, h4]

/-- **The case `p < N/2` of `eq:quadra x3`** (source l. 1595, 1620): for the constants
`C = C_β` of `defchi`, a crude error `Cb = C_β` and a target `T ≥ 0` (any of the constants
`c_β'` of `eq:quadra x3`), there is `0 < λ₀ < 1`, depending only on `β`, `C`, `Cb` and `T`, such
that for `λ ≤ λ₀`, `1 ≤ N`, `p₀ ≤ N`, `p < N/2` and `K - p ≤ (M₀ + 2)(N - K)`,
`N χ_β(δ) + Cb N ≤ -T (N - p₀)²/N`, where `δ = (N - K)/N`.
The quadratic term `-c (p - p₀)²/N ≤ 0` of `eq:2cases p` is dropped. -/
theorem quadra_x3_small_p {β : ℝ} (hβ : 2 < β) (C Cb T : ℝ) (hT : 0 ≤ T) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ < 1 ∧ ∀ (lam : ℝ) (N K p p₀ : ℕ), 0 < lam → lam ≤ lam₀ →
      1 ≤ N → p₀ ≤ N → (p : ℝ) < N / 2 → (K : ℝ) - p ≤ (M0 + 2) * ((N : ℝ) - K) →
      (N : ℝ) * chiBeta β hβ lam C (((N : ℝ) - K) / N) + Cb * N ≤ -(T * ((N : ℝ) - p₀) ^ 2 / N) := by
  obtain ⟨lam₀, h0, h1, h⟩ := exists_chiBeta_add_le_neg hβ C Cb T
  refine ⟨lam₀, h0, h1, ?_⟩
  intro lam N K p p₀ hlam hle hN hp₀ hp hKp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hp₀' : (p₀ : ℝ) ≤ N := by exact_mod_cast hp₀
  have hδ1 : ((N : ℝ) - K) / N ≤ 1 := by
    rw [div_le_one hNpos]
    linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have h2 := h lam _ hlam hle (delta_ge_of_lt_half hN hp hKp) hδ1
  have h3 := mul_le_mul_of_nonneg_left h2 hNpos.le
  have h4 : ((N : ℝ) - p₀) ^ 2 / N ≤ N := by
    rw [div_le_iff₀ hNpos]
    have hp₀0 : (0 : ℝ) ≤ p₀ := Nat.cast_nonneg p₀
    calc ((N : ℝ) - p₀) ^ 2 ≤ (N : ℝ) ^ 2 :=
          pow_le_pow_left₀ (by linarith only [hp₀']) (by linarith only [hp₀0]) 2
      _ = N * N := sq _
  have h5 : T * (((N : ℝ) - p₀) ^ 2 / N) ≤ T * N := mul_le_mul_of_nonneg_left h4 hT
  have e1 : T * ((N : ℝ) - p₀) ^ 2 / N = T * (((N : ℝ) - p₀) ^ 2 / N) := by ring
  rw [e1]
  linarith only [h3, h5]

end SmallP

end TwoComponentCoulomb

end
