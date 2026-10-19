/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Exponential

/-!
# Proposition 3.9, Steps 3--4: the entropy and optimization calculus

Source: proof of Proposition 3.9 (`prop:isolated`), l. 1337--1415:
the elementary entropy inequalities of Step 3 (l. 1344--1352), the supremum inequality of Step 4
(l. 1392--1395) and its application to the bounds of Step 3 (l. 1396--1408), and the entropy
bookkeeping of the crude case (l. 1415). Nothing in this file refers to configurations:
it is pure real analysis, consumed by `Isolated.lean`.

Throughout, `p = p₀ + q` is the number of pairs, `p₀` the number of neutral pairs (the pairs
*not* assigned the logarithmic term), `q` the number of same-sign pairs, `k ≤ p₀` the number of
selected neutral factors, and `x₀ = q/p`, `x₁ = k/p`, `t = x₀ + x₁`. The entropy of `f(p₀)` is
`p log p - p₀ log p₀ - q log q + C₀ q` (with `0 log 0 = 0`, which is Mathlib's `Real.log 0 = 0`).

## Main results

* `IsolatedOptimization.mul_sub_log_le_exp`: the supremum inequality
  `sup_{0 < s ≤ 1} s (A - log s) ≤ e^{A - 1}` (the case `η = 1` of l. 1392--1395),
  valid for every `s ≥ 0`; the general form
  `s (A + B log (1/s)) ≤ B e^{A/B - 1}` is `TwoComponentCoulomb.mul_add_mul_log_inv_le`.
* `IsolatedOptimization.mul_sub_log_add_log_max_le`: the supremum inequality applied to both
  branches of a maximum, `s (A - log s) + (s/2) log (max (X s) (Y²)) ≤ X e^{2A} + Y e^A`
  (the branches of l. 1396--1405).
* `IsolatedOptimization.log_choose_le`, `IsolatedOptimization.entropy_le`,
  `IsolatedOptimization.mul_log_add_le`: the entropy inequalities of l. 1344--1352.
* `IsolatedOptimization.exponent_le_single`, `IsolatedOptimization.exponent_le_two`: the
  exponent of the term `k` of Step 3, divided by `p`, plus the quadratic gain `x₀²` (l. 1407),
  is bounded by the optimized error, for one marked species (`β ≤ 4`, Proposition 3.7) and two
  species (`β > 4`, Proposition 3.8).
* `IsolatedOptimization.sum_le_ofReal_exp`: the sum over `0 ≤ k ≤ p₀` costs at most `log (N + 1)`
  beyond its largest term (l. 1343).
* `IsolatedOptimization.entropy_le_crude`: the entropy of `f(p₀)` is at most `(1 + |C₀|) p`
  (l. 1415).
-/

@[expose] public section

open Finset
open scoped ENNReal Nat

namespace TwoComponentCoulomb

namespace IsolatedOptimization

/-! ### The supremum inequality (source l. 1392--1395) -/

/-- `s (a - log s) ≤ e^{a-1}` for every `s ≥ 0`: the supremum inequality of source l. 1392--1395
with `η = 1`. -/
theorem mul_sub_log_le_exp (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    s * (a - Real.log s) ≤ Real.exp (a - 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp only [zero_mul]
    exact (Real.exp_pos _).le
  · have h := Real.log_le_sub_one_of_pos (x := Real.exp (a - 1) / s) (by positivity)
    rw [Real.log_div (Real.exp_pos _).ne' hs.ne', Real.log_exp] at h
    have h' : a - Real.log s ≤ Real.exp (a - 1) / s := by linarith
    calc s * (a - Real.log s) ≤ s * (Real.exp (a - 1) / s) :=
          mul_le_mul_of_nonneg_left h' hs.le
      _ = Real.exp (a - 1) := by field_simp

/-- **The supremum inequality on both branches of a maximum** (source l. 1396--1405): for `s ≥ 0`,
`X, Y > 0` and `Γ ≤ log (max (X s) (Y²))`,
`s (A - log s) + (s/2) Γ ≤ X e^{2A} + Y e^{A}`. On the branch `X s` the inequality is applied with
`η = 1/2`, on the branch `Y²` with `η = 1`. -/
theorem mul_sub_log_add_log_max_le (A : ℝ) {X Y s Γ : ℝ} (hX : 0 < X) (hY : 0 < Y) (hs : 0 ≤ s)
    (hΓ : Γ ≤ Real.log (max (X * s) (Y ^ 2))) :
    s * (A - Real.log s) + s / 2 * Γ ≤ X * Real.exp (2 * A) + Y * Real.exp A := by
  have hXe : 0 < X * Real.exp (2 * A) := by positivity
  have hYe : 0 < Y * Real.exp A := by positivity
  rcases hs.eq_or_lt with rfl | hs
  · simp only [zero_mul, zero_div, zero_add]
    positivity
  have hΓ' : s / 2 * Γ ≤ s / 2 * Real.log (max (X * s) (Y ^ 2)) :=
    mul_le_mul_of_nonneg_left hΓ (by positivity)
  rcases le_total (Y ^ 2) (X * s) with h | h
  · rw [max_eq_left h, Real.log_mul hX.ne' hs.ne'] at hΓ'
    have h1 := mul_sub_log_le_exp (2 * A + Real.log X) hs.le
    have e1 : Real.exp (2 * A + Real.log X - 1) ≤ X * Real.exp (2 * A) := by
      rw [show 2 * A + Real.log X - 1 = (2 * A - 1) + Real.log X by ring, Real.exp_add,
        Real.exp_log hX, mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hX.le
    have : s * (A - Real.log s) + s / 2 * (Real.log X + Real.log s) =
        (1 / 2) * (s * (2 * A + Real.log X - Real.log s)) := by ring
    linarith only [hΓ', this, h1, e1, hXe, hYe]
  · rw [max_eq_right h, Real.log_pow, Nat.cast_ofNat] at hΓ'
    have h1 := mul_sub_log_le_exp (A + Real.log Y) hs.le
    have e1 : Real.exp (A + Real.log Y - 1) ≤ Y * Real.exp A := by
      rw [show A + Real.log Y - 1 = (A - 1) + Real.log Y by ring, Real.exp_add,
        Real.exp_log hY, mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hY.le
    have : s * (A - Real.log s) + s / 2 * (2 * Real.log Y) =
        s * (A + Real.log Y - Real.log s) := by ring
    linarith only [hΓ', this, h1, e1, hXe, hYe]

/-- The supremum inequality in the variables `M = p s` of Step 3: for `0 < P`, `0 ≤ M`,
`X, Y > 0` and `Γ ≤ log (max (X M/P) (Y²))`,
`M (A - log (M/P)) + (M/2) Γ ≤ P (X e^{2A} + Y e^{A})`. -/
theorem mul_sub_log_div_add_le (A : ℝ) {P M X Y Γ : ℝ} (hP : 0 < P) (hM : 0 ≤ M) (hX : 0 < X)
    (hY : 0 < Y) (hΓ : Γ ≤ Real.log (max (X * (M / P)) (Y ^ 2))) :
    M * (A - Real.log (M / P)) + M / 2 * Γ ≤ P * (X * Real.exp (2 * A) + Y * Real.exp A) := by
  have h := mul_sub_log_add_log_max_le A hX hY (div_nonneg hM hP.le) hΓ
  have e : M * (A - Real.log (M / P)) + M / 2 * Γ =
      P * (M / P * (A - Real.log (M / P)) + M / P / 2 * Γ) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h hP.le

/-! ### The entropy inequalities (source l. 1344--1352) -/

/-- `x log (x/y) = x log x - x log y` for `y ≠ 0`, including `x = 0`. -/
theorem mul_log_div (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    x * Real.log (x / y) = x * Real.log x - x * Real.log y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Real.log_div hx hy]
    ring

/-- `a - s ≤ a log a - a log s` for `a ≥ 0`, `s > 0` (from `log x ≤ x - 1`). -/
theorem sub_le_mul_log_sub (a : ℝ) {s : ℝ} (ha : 0 ≤ a) (hs : 0 < s) :
    a - s ≤ a * Real.log a - a * Real.log s := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_sub, Real.log_zero, mul_zero, zero_mul, sub_zero, neg_nonpos]
    exact hs.le
  · have h := Real.log_le_sub_one_of_pos (div_pos hs ha)
    rw [Real.log_div hs.ne' ha.ne'] at h
    have : a * (Real.log s - Real.log a) ≤ a * (s / a - 1) := mul_le_mul_of_nonneg_left h ha.le
    rw [mul_sub, mul_sub, mul_div_cancel₀ _ ha.ne', mul_one] at this
    linarith

/-- **Concavity of the entropy** (source l. 1350, `-x₀ log x₀ - x₁ log x₁ ≤ t log (2/t)`):
for `a, b ≥ 0`, `(a + b) log ((a + b)/2) ≤ a log a + b log b`. -/
theorem mul_log_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * Real.log ((a + b) / 2) ≤ a * Real.log a + b * Real.log b := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0
    simp
  · have hs : 0 < (a + b) / 2 := by positivity
    have h1 := sub_le_mul_log_sub a ha hs
    have h2 := sub_le_mul_log_sub b hb hs
    linarith only [h1, h2]

/-- **The binomial bound** (source l. 1346): `log C(n, k) ≤ k log n - k log k + k` for `k ≤ n`,
i.e. `log C(p₀, k) ≤ k log (p₀/k) + k`. -/
theorem log_choose_le {n k : ℕ} (hk : k ≤ n) :
    Real.log (n.choose k) ≤ k * Real.log n - k * Real.log k + k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  have hK : (0 : ℝ) < k := by exact_mod_cast hk0
  have hn : (0 : ℝ) < n := by exact_mod_cast hk0.trans_le hk
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have h1 : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k ! := Nat.choose_le_pow_div k n
  have h2 : (k : ℝ) ^ k / k ! ≤ Real.exp k := Real.pow_div_factorial_le_exp (k : ℝ) hK.le k
  have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have h3 : (n.choose k : ℝ) ≤ (n : ℝ) ^ k * Real.exp k / (k : ℝ) ^ k := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hf] at h2
    rw [le_div_iff₀ hf] at h1
    calc (n.choose k : ℝ) * (k : ℝ) ^ k ≤ (n.choose k : ℝ) * (Real.exp k * k !) :=
          mul_le_mul_of_nonneg_left h2 hc.le
      _ = (n.choose k : ℝ) * k ! * Real.exp k := by ring
      _ ≤ (n : ℝ) ^ k * Real.exp k := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have h4 := Real.log_le_log hc h3
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_exp] at h4
  linarith

/-- **The entropy of `f(p₀)` with the binomial factor** (source l. 1344--1352): for `k ≤ p₀`,
`p = p₀ + q > 0`,
`p log p - p₀ log p₀ - q log q + log C(p₀, k) ≤ q + q log p - q log q + k log p - k log k + k`
(the first step uses `-(1 - x₀) log (1 - x₀) ≤ x₀`). -/
theorem entropy_le {p p₀ q k : ℕ} (hpq : p₀ + q = p) (hp : 0 < p) (hk : k ≤ p₀) :
    p * Real.log p - p₀ * Real.log p₀ - q * Real.log q + Real.log (p₀.choose k) ≤
      q + q * Real.log p - q * Real.log q + (k * Real.log p - k * Real.log k + k) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have hpq' : (p : ℝ) = p₀ + q := by exact_mod_cast hpq.symm
  have h1 := sub_le_mul_log_sub (p₀ : ℝ) (Nat.cast_nonneg _) hP
  have h2 := log_choose_le hk
  have h3 : (k : ℝ) * Real.log p₀ ≤ k * Real.log p := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · have : (0 : ℝ) < p₀ := by exact_mod_cast hk0.trans_le hk
      exact mul_le_mul_of_nonneg_left (Real.log_le_log this (by linarith)) (Nat.cast_nonneg _)
  have e : (p : ℝ) * Real.log p = p₀ * Real.log p + q * Real.log p := by rw [hpq']; ring
  linarith

/-- **The crude entropy bound** (source l. 1415):
`p log p - p₀ log p₀ - q log q + C₀ q ≤ (1 + |C₀|) p` for `p = p₀ + q > 0`. -/
theorem entropy_le_crude {p p₀ q : ℕ} (hpq : p₀ + q = p) (hp : 0 < p) (C₀ : ℝ) :
    p * Real.log p - p₀ * Real.log p₀ - q * Real.log q + C₀ * q ≤ (1 + |C₀|) * p := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have hpq' : (p : ℝ) = p₀ + q := by exact_mod_cast hpq.symm
  have h0 := entropy_le hpq hp (Nat.zero_le p₀) (k := 0)
  simp only [Nat.choose_zero_right, Nat.cast_one, Real.log_one, add_zero, CharP.cast_eq_zero,
    zero_mul, sub_zero] at h0
  have h1 := sub_le_mul_log_sub (q : ℝ) (Nat.cast_nonneg _) hP
  have hq : (q : ℝ) ≤ p := by rw [hpq']; linarith [(Nat.cast_nonneg p₀ : (0 : ℝ) ≤ p₀)]
  have h2 : C₀ * q ≤ |C₀| * p :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₀) (Nat.cast_nonneg q)).trans
      (mul_le_mul_of_nonneg_left hq (abs_nonneg C₀))
  linarith only [h0, h1, h2]

/-! ### The exponent of the term `k` (Step 3) and its optimization (Step 4) -/

/-- **Steps 3--4 for one marked species** (source l. 1337--1379 and l. 1392--1408, the cases
`2 ≤ β ≤ 4`). Let `p = p₀ + q > 0`, `k ≤ p₀`, `M = k + q`, and suppose that the integral of
the `M` selected factors is bounded by Proposition 3.7 with exponent
`p log N + C₆ M + (M/2) Γ`, where `Γ ≤ log (max (X M/p) (Y²))` (this is `γ_{β, M}` with `p ≤ N`),
and that each selected factor carries the constant `m = e^L`. Then the exponent of the term `k`
(entropy, binomial factor, constants, `γ`), plus the quadratic gain `p (q/p)²`, is at most
`p (X e^{2A} + Y e^{A})` with `A = 2 + log 2 + |C₀| + C₆ + L`. -/
theorem exponent_le_single {p p₀ q k : ℕ} (hpq : p₀ + q = p) (hp : 0 < p) (hk : k ≤ p₀)
    (C₀ C₆ L : ℝ) {X Y Γ : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hΓ : Γ ≤ Real.log (max (X * (((k + q : ℕ) : ℝ) / p)) (Y ^ 2))) :
    p * Real.log p - p₀ * Real.log p₀ - q * Real.log q + C₀ * q + Real.log (p₀.choose k)
        + p * ((q : ℝ) / p) ^ 2 + ((k + q : ℕ) : ℝ) * L + C₆ * ((k + q : ℕ) : ℝ)
        + ((k + q : ℕ) : ℝ) / 2 * Γ ≤
      p * (X * Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆ + L))
        + Y * Real.exp (2 + Real.log 2 + |C₀| + C₆ + L)) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have hpq' : (p : ℝ) = p₀ + q := by exact_mod_cast hpq.symm
  have hq : (q : ℝ) ≤ p := by rw [hpq']; linarith [(Nat.cast_nonneg p₀ : (0 : ℝ) ≤ p₀)]
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set M : ℝ := ((k + q : ℕ) : ℝ) with hMdef
  have hM : M = k + q := by rw [hMdef]; push_cast; ring
  have hM0 : 0 ≤ M := by rw [hM]; positivity
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
  have hopt := mul_sub_log_div_add_le (2 + Real.log 2 + |C₀| + C₆ + L) hP hM0 hX hY hΓ
  rw [← hM] at hconc
  have e4 : M * Real.log p = k * Real.log p + q * Real.log p := by rw [hM]; ring
  linarith only [hE, hconc, hsq, hC₀, e1, e2, e4, hopt, hM, hk0, hq0]

/-- **Steps 3--4 for two marked species** (source l. 1380--1387 and l. 1392--1408, the case
`β > 4`). Let `p = p₀ + q > 0`, `k ≤ p₀`, and suppose that the integral of the selected factors is
bounded by Proposition 3.8 with exponent `p log N + C₇ (k + q) + (k/2) Γ₁ + (q/2) Γ₂`, where
`Γ₁ ≤ log (max (X₁ k/p) (Y₁²))` and `Γ₂ ≤ log (max (X₂ q/p) (Y₂²))`, and that the `k` neutral
(resp. `q` same-sign) factors carry the constant `e^{L₁}` (resp. `e^{L₂}`). Then the exponent of the
term `k`, plus the quadratic gain `p (q/p)²`, is at most
`p (X₁ e^{2A₁} + Y₁ e^{A₁} + X₂ e^{2A₂} + Y₂ e^{A₂})` with `A_i = 2 + |C₀| + C₇ + L_i`. -/
theorem exponent_le_two {p p₀ q k : ℕ} (hpq : p₀ + q = p) (hp : 0 < p) (hk : k ≤ p₀)
    (C₀ C₇ L₁ L₂ : ℝ) {X₁ Y₁ X₂ Y₂ Γ₁ Γ₂ : ℝ} (hX₁ : 0 < X₁) (hY₁ : 0 < Y₁) (hX₂ : 0 < X₂)
    (hY₂ : 0 < Y₂) (hΓ₁ : Γ₁ ≤ Real.log (max (X₁ * ((k : ℝ) / p)) (Y₁ ^ 2)))
    (hΓ₂ : Γ₂ ≤ Real.log (max (X₂ * ((q : ℝ) / p)) (Y₂ ^ 2))) :
    p * Real.log p - p₀ * Real.log p₀ - q * Real.log q + C₀ * q + Real.log (p₀.choose k)
        + p * ((q : ℝ) / p) ^ 2 + k * L₁ + q * L₂ + C₇ * ((k : ℝ) + q)
        + k / 2 * Γ₁ + q / 2 * Γ₂ ≤
      p * (X₁ * Real.exp (2 * (2 + |C₀| + C₇ + L₁)) + Y₁ * Real.exp (2 + |C₀| + C₇ + L₁)
        + (X₂ * Real.exp (2 * (2 + |C₀| + C₇ + L₂)) + Y₂ * Real.exp (2 + |C₀| + C₇ + L₂))) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have hpq' : (p : ℝ) = p₀ + q := by exact_mod_cast hpq.symm
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hE := entropy_le hpq hp hk
  have hsq : (p : ℝ) * ((q : ℝ) / p) ^ 2 ≤ q := by
    have hq : (q : ℝ) ≤ p := by rw [hpq']; linarith [(Nat.cast_nonneg p₀ : (0 : ℝ) ≤ p₀)]
    rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith only [mul_le_mul_of_nonneg_left hq (mul_nonneg hq0 hP.le)]
  have hC₀ : C₀ * q ≤ |C₀| * q := mul_le_mul_of_nonneg_right (le_abs_self C₀) hq0
  have e1 := mul_log_div (k : ℝ) hP.ne'
  have e2 := mul_log_div (q : ℝ) hP.ne'
  have h1 := mul_sub_log_div_add_le (2 + |C₀| + C₇ + L₁) hP hk0 hX₁ hY₁ hΓ₁
  have h2 := mul_sub_log_div_add_le (2 + |C₀| + C₇ + L₂) hP hq0 hX₂ hY₂ hΓ₂
  have hk1 : (k : ℝ) * 1 ≤ k * (2 + |C₀|) := by
    exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg C₀]) hk0
  linarith only [hE, hsq, hC₀, e1, e2, h1, h2, hk1]

/-! ### The sum over `k` (source l. 1343) -/

/-- **The sum over `0 ≤ k ≤ n` costs at most `log (N + 1)`** (source l. 1343): if every term
`e^E · (Z · F k)` is at most `e^Y`, then `e^E · (Z · ∑_{k ≤ n} F k) ≤ e^{Y + log (N + 1)}` for
`n ≤ N`. -/
theorem sum_le_ofReal_exp {n N : ℕ} (hn : n ≤ N) (E Y : ℝ) (Z : ℝ≥0∞) (F : ℕ → ℝ≥0∞)
    (hF : ∀ k ∈ range (n + 1),
      ENNReal.ofReal (Real.exp E) * (Z * F k) ≤ ENNReal.ofReal (Real.exp Y)) :
    ENNReal.ofReal (Real.exp E) * (Z * ∑ k ∈ range (n + 1), F k) ≤
      ENNReal.ofReal (Real.exp (Y + Real.log (N + 1))) := by
  rw [mul_sum, mul_sum]
  refine (sum_le_card_nsmul _ _ _ hF).trans ?_
  rw [card_range, nsmul_eq_mul, Real.exp_add, Real.exp_log (by positivity),
    ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm (ENNReal.ofReal (Real.exp Y))]
  refine mul_le_mul_left ?_ _
  rw [show ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n + 1 : ℕ) : ℝ) from
    (ENNReal.ofReal_natCast _).symm]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  exact_mod_cast Nat.add_le_add_right hn 1

/-- Product of `ofReal` exponentials and powers, as one exponential: for `c ≥ 1` a natural number,
`m₁, m₂, Z > 0`,
`e^E · (Z^p · (c · (m₁^k · m₂^q · e^F))) = e^{E + p log Z + log c + k log m₁ + q log m₂ + F}`. -/
theorem ofReal_exp_mul_eq {E F Z m₁ m₂ : ℝ} (hZ : 0 < Z) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) {c : ℕ}
    (hc : 0 < c) (p k q : ℕ) :
    ENNReal.ofReal (Real.exp E) * (ENNReal.ofReal Z ^ p * ((c : ℝ≥0∞) *
        (ENNReal.ofReal m₁ ^ k * ENNReal.ofReal m₂ ^ q * ENNReal.ofReal (Real.exp F)))) =
      ENNReal.ofReal (Real.exp (E + p * Real.log Z + Real.log c + k * Real.log m₁
        + q * Real.log m₂ + F)) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hZ.le, ← ENNReal.ofReal_pow hm₁.le,
    ← ENNReal.ofReal_pow hm₂.le, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hc',
    Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hZ, Real.exp_log hm₁,
    Real.exp_log hm₂]
  ring

/-! ### Assembly of Steps 3--4 -/

/-- **Steps 3--4 assembled, one marked species** (source l. 1337--1408, `2 ≤ β ≤ 4`). Let
`p = p₀ + q`, `0 < p ≤ N`, and let `W` (the integral over the representatives) be bounded by the
expansion `∑_{k ≤ p₀} C(p₀, k) m^{k+q} e^{p log N + C₆ (k+q) + ((k+q)/2) Γ(k+q)}` of Step 3, where
`Γ(k + q) ≤ log (max (X (k+q)/p) (Y²))`. Then, with the entropy of `f(p₀)`,
`e^{p log p - p₀ log p₀ - q log q + C₀ q} Z^p W ≤
  exp (p log N + p log Z - p (q/p)² + p (X e^{2A} + Y e^{A}) + log (N + 1))`,
`A = 2 + log 2 + |C₀| + C₆ + log m`. -/
theorem ofReal_exp_mul_le_single {N p p₀ q : ℕ} (hpq : p₀ + q = p) (hp : 0 < p) (hpN : p ≤ N)
    (C₀ C₆ : ℝ) {Z m X Y : ℝ} (hZ : 0 < Z) (hm : 0 < m) (hX : 0 < X) (hY : 0 < Y)
    (Γ : ℕ → ℝ)
    (hΓ : ∀ k ≤ p₀, Γ (k + q) ≤ Real.log (max (X * (((k + q : ℕ) : ℝ) / p)) (Y ^ 2)))
    {W : ℝ≥0∞}
    (hW : W ≤ ∑ k ∈ range (p₀ + 1), (p₀.choose k : ℝ≥0∞) *
      (ENNReal.ofReal m ^ k * ENNReal.ofReal m ^ q * ENNReal.ofReal (Real.exp (p * Real.log N
        + C₆ * ((k + q : ℕ) : ℝ) + ((k + q : ℕ) : ℝ) / 2 * Γ (k + q))))) :
    ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q + C₀ * q)) *
        (ENNReal.ofReal Z ^ p * W) ≤
      ENNReal.ofReal (Real.exp (p * Real.log N + p * Real.log Z - p * ((q : ℝ) / p) ^ 2
        + p * (X * Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆ + Real.log m))
          + Y * Real.exp (2 + Real.log 2 + |C₀| + C₆ + Real.log m)) + Real.log (N + 1))) := by
  have hp₀N : p₀ ≤ N := by omega
  calc _ ≤ ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
          + C₀ * q)) * (ENNReal.ofReal Z ^ p * ∑ k ∈ range (p₀ + 1), (p₀.choose k : ℝ≥0∞) *
            (ENNReal.ofReal m ^ k * ENNReal.ofReal m ^ q * ENNReal.ofReal (Real.exp
              (p * Real.log N + C₆ * ((k + q : ℕ) : ℝ) + ((k + q : ℕ) : ℝ) / 2 * Γ (k + q))))) := by
        gcongr
    _ ≤ _ := by
        refine sum_le_ofReal_exp hp₀N _ _ _ _ fun k hk => ?_
        have hk' : k ≤ p₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        rw [ofReal_exp_mul_eq hZ hm hm (Nat.choose_pos hk') p k q]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h := exponent_le_single hpq hp hk' C₀ C₆ (Real.log m) hX hY (hΓ k hk')
        have e : ((k + q : ℕ) : ℝ) * Real.log m = k * Real.log m + q * Real.log m := by
          push_cast; ring
        linarith

/-- **Steps 3--4 assembled, two marked species** (source l. 1380--1408, `β > 4`). As
`ofReal_exp_mul_le_single`, with the `k` neutral factors carrying `m₁` and the exponent
`(k/2) Γ₁(k)`, and the `q` same-sign factors carrying `m₂` and the exponent `(q/2) Γ₂`
(Proposition 3.8). -/
theorem ofReal_exp_mul_le_two {N p p₀ q : ℕ} (hpq : p₀ + q = p) (hp : 0 < p) (hpN : p ≤ N)
    (C₀ C₇ : ℝ) {Z m₁ m₂ X₁ Y₁ X₂ Y₂ : ℝ} (hZ : 0 < Z) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hX₁ : 0 < X₁) (hY₁ : 0 < Y₁) (hX₂ : 0 < X₂) (hY₂ : 0 < Y₂) (Γ₁ : ℕ → ℝ) (Γ₂ : ℝ)
    (hΓ₁ : ∀ k ≤ p₀, Γ₁ k ≤ Real.log (max (X₁ * ((k : ℝ) / p)) (Y₁ ^ 2)))
    (hΓ₂ : Γ₂ ≤ Real.log (max (X₂ * ((q : ℝ) / p)) (Y₂ ^ 2)))
    {W : ℝ≥0∞}
    (hW : W ≤ ∑ k ∈ range (p₀ + 1), (p₀.choose k : ℝ≥0∞) *
      (ENNReal.ofReal m₁ ^ k * ENNReal.ofReal m₂ ^ q * ENNReal.ofReal (Real.exp (p * Real.log N
        + C₇ * ((k : ℝ) + q) + k / 2 * Γ₁ k + q / 2 * Γ₂)))) :
    ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q + C₀ * q)) *
        (ENNReal.ofReal Z ^ p * W) ≤
      ENNReal.ofReal (Real.exp (p * Real.log N + p * Real.log Z - p * ((q : ℝ) / p) ^ 2
        + p * (X₁ * Real.exp (2 * (2 + |C₀| + C₇ + Real.log m₁))
          + Y₁ * Real.exp (2 + |C₀| + C₇ + Real.log m₁)
          + (X₂ * Real.exp (2 * (2 + |C₀| + C₇ + Real.log m₂))
            + Y₂ * Real.exp (2 + |C₀| + C₇ + Real.log m₂))) + Real.log (N + 1))) := by
  have hp₀N : p₀ ≤ N := by omega
  calc _ ≤ ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
          + C₀ * q)) * (ENNReal.ofReal Z ^ p * ∑ k ∈ range (p₀ + 1), (p₀.choose k : ℝ≥0∞) *
            (ENNReal.ofReal m₁ ^ k * ENNReal.ofReal m₂ ^ q * ENNReal.ofReal (Real.exp
              (p * Real.log N + C₇ * ((k : ℝ) + q) + k / 2 * Γ₁ k + q / 2 * Γ₂)))) := by
        gcongr
    _ ≤ _ := by
        refine sum_le_ofReal_exp hp₀N _ _ _ _ fun k hk => ?_
        have hk' : k ≤ p₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        rw [ofReal_exp_mul_eq hZ hm₁ hm₂ (Nat.choose_pos hk') p k q]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h := exponent_le_two hpq hp hk' C₀ C₇ (Real.log m₁) (Real.log m₂) hX₁ hY₁ hX₂ hY₂
          (hΓ₁ k hk') hΓ₂
        linarith

end IsolatedOptimization

end TwoComponentCoulomb

end
