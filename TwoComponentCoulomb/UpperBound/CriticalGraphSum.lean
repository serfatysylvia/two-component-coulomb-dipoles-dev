/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.NumComponents
public import TwoComponentCoulomb.NearestNeighbor.TwiceIsolated
public import TwoComponentCoulomb.UpperBound.CriticalCells
public import TwoComponentCoulomb.UpperBound.MarkedGraphCover
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import TwoComponentCoulomb.Integrals.Stirling
import TwoComponentCoulomb.UpperBound.CriticalRadial
public import TwoComponentCoulomb.UpperBound.CriticalFactorials

/-!
# The sum over the nearest-neighbour graphs at `β = 2` (Proposition 3.10, eq. (eq:critical upper))

Source: l. 1635–1651 (proof of Proposition 3.10, `β = 2`: counting, Stirling, optimization), also
used for the electric moment of Theorem 2 at `β = 2` (l. 1903–1932). The supremum over `δ = d/N`
is `O(ℓ^{-1/5}) = O(ω_λ)`, and the bounds below carry the rate `ℓ^{-1/5}` itself.

Write `ℓ = |log λ|`. The integral over `Λ^{2N}` is split over the nearest-neighbour graphs
`f = φ₁(Z)` (a finite partition of `Λ^{2N}`). A graph with `K` components, `m` isolated pairs and
`p₀` isolated neutral pairs contributes at most `exp (criticalCellExponent …)`
(`UpperBound/CriticalCells.lean`). The unordered cycle count retains the factor `2^{-(K-p₀)}`. The elementary
comparisons `(2n)! ≤ 4^n(n!)²` and `N!/p₀! ≤ N^{N-p₀}` cancel the unused
neutral labels. The bound `k! ≥ (k/e)^k` supplies the other factorial estimates.
We then normalize by `N! N^N J_λ(1/ℓ)^N`, retaining the loss `J^{-(d+q)}`.
The tree entropy contributes coefficient three. The constraint `h ≤ 2d`
contributes two more, so the first entropy optimization has coefficient five.
The same-sign optimization has coefficient one. The sum over `(K,m,p₀)` costs
`3 log(N+1)`. The upper factorial estimate converts the retained `N!` to the
stated free-energy main term only at the end.

This is stated for a general integrand whose cell integrals are bounded by
`exp (criticalCellExponent …)`, with neutral and same-sign pair masses `Mₙ` and `Mₛ ≤ C₀ E`. The
instances are (eq:critical upper) (`UpperBound/CriticalUpper.lean`, `Mₛ` constant) and
(eq:critical electric) (`Fluctuations/CriticalElectric.lean`, `Mₛ` of order `E`).

## Main results

* `TwoComponentCoulomb.critical_count_cell_normalized_le`: the elementary count
  multiplied by the cell estimate and normalized by `N! N^N J_λ(1/ℓ)^N`.
* `TwoComponentCoulomb.mul_add_mul_log_div_le` : the supremum bound.
* `TwoComponentCoulomb.neutralMass`, `TwoComponentCoulomb.log_neutralMass_le`: the radial integral
  bound `Mₙ` of a neutral pair and `log Mₙ ≤ log (2πℓ) + C (1 + log ℓ + log (1/R))/ℓ`.
* `TwoComponentCoulomb.critical_exponent_le` (source l. 1641–1644): the bound on the exponent of
  a type `(K, m, p₀)`.
* `TwoComponentCoulomb.lintegral_pi_box_eq_sum_nnCell` : the partition into cells.
* `TwoComponentCoulomb.exists_lintegral_pi_box_le_of_cell_le` (source l. 1637–1652): if every cell
  integral is at most `exp (criticalCellExponent …)`, then
  `∫_{Λ^{2N}} G ≤ exp (2N log N + N (log (2πℓ) - 1) + C N (ℓ^{-1/5} + E/ℓ) + C log (N+1))`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal Nat

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### Elementary inequalities -/

/-- `x log n - x log x = x log (n/x)`, also for `x = 0`. -/
theorem mul_log_sub_mul_log_eq {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) :
    x * Real.log n - x * Real.log x = x * Real.log (n / x) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  · rw [Real.log_div hn.ne' hx'.ne']
    ring

/-- `x log (n/x) ≤ n - x` (from `log y ≤ y - 1`). -/
theorem mul_log_div_le_sub {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) :
    x * Real.log (n / x) ≤ n - x := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp [hn.le]
  · have h := Real.log_le_sub_one_of_pos (div_pos hn hx')
    calc x * Real.log (n / x) ≤ x * (n / x - 1) := mul_le_mul_of_nonneg_left h hx
      _ = n - x := by field_simp

/-- `d log (n/d) ≥ 0` for `0 ≤ d ≤ n`. -/
theorem mul_log_div_nonneg {d n : ℝ} (hd : 0 ≤ d) (hdn : d ≤ n) : 0 ≤ d * Real.log (n / d) := by
  rcases hd.eq_or_lt with rfl | hd'
  · simp
  · exact mul_nonneg hd (Real.log_nonneg (by rw [le_div_iff₀ hd']; linarith))

/-- For `0 ≤ h ≤ 2d` and `d ≤ n`: `h log (n/h) ≤ 2d log (n/d) + 2d` . -/
theorem mul_log_div_le_of_le_two_mul {h d n : ℝ} (hh : 0 ≤ h) (hhd : h ≤ 2 * d) (hdn : d ≤ n)
    (hn : 0 < n) : h * Real.log (n / h) ≤ 2 * d * Real.log (n / d) + 2 * d := by
  have hd : 0 ≤ d := by linarith
  have hdl := mul_log_div_nonneg hd hdn
  rcases hh.eq_or_lt with rfl | hh'
  · simp only [zero_mul]
    linarith
  have hd' : 0 < d := by linarith
  have e : Real.log (n / h) = Real.log (n / (2 * d)) + Real.log (2 * d / h) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [e, mul_add]
  have h1 : h * Real.log (2 * d / h) ≤ 2 * d - h := mul_log_div_le_sub hh (by linarith)
  have h2 : h * Real.log (n / (2 * d)) ≤ 2 * d * Real.log (n / d) := by
    by_cases hL : 0 ≤ Real.log (n / (2 * d))
    · have h3 : Real.log (n / (2 * d)) ≤ Real.log (n / d) :=
        Real.log_le_log (by positivity) (div_le_div_of_nonneg_left hn.le hd' (by linarith))
      calc h * Real.log (n / (2 * d)) ≤ 2 * d * Real.log (n / (2 * d)) :=
            mul_le_mul_of_nonneg_right hhd hL
        _ ≤ 2 * d * Real.log (n / d) := mul_le_mul_of_nonneg_left h3 (by linarith)
    · have : h * Real.log (n / (2 * d)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hh (le_of_lt (not_le.1 hL))
      linarith only [this, hdl]
  linarith

/-- **The supremum bound** : for `x ≥ 0`, `n, a > 0`,
`x (a log (n/x) + b) ≤ a n e^{b/a - 1}`, i.e. `sup_{s > 0} s (a log (1/s) + b) ≤ a e^{b/a-1}`. -/
theorem mul_add_mul_log_div_le {x n a b : ℝ} (hx : 0 ≤ x) (hn : 0 < n) (ha : 0 < a) :
    x * (a * Real.log (n / x) + b) ≤ a * n * Real.exp (b / a - 1) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp only [zero_mul]
    positivity
  set y := n * Real.exp (b / a) / x with hy
  have hy0 : 0 < y := by positivity
  have hlog : Real.log y = Real.log (n / x) + b / a := by
    rw [hy, mul_div_right_comm, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  -- `log y ≤ y / e`
  have hle : Real.log y ≤ y * Real.exp (-1) := by
    have h := Real.log_le_sub_one_of_pos (mul_pos hy0 (Real.exp_pos (-1)))
    rw [Real.log_mul hy0.ne' (Real.exp_pos _).ne', Real.log_exp] at h
    linarith
  calc x * (a * Real.log (n / x) + b) = a * x * Real.log y := by
        rw [hlog]; field_simp
    _ ≤ a * x * (y * Real.exp (-1)) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = a * n * Real.exp (b / a - 1) := by
        rw [hy, Real.exp_sub, Real.exp_neg]
        field_simp

/-- `log (ℓ + x) ≤ log ℓ + x/ℓ` for `ℓ > 0`, `x ≥ 0`. -/
theorem log_add_le_log_add_div {ℓ x : ℝ} (hℓ : 0 < ℓ) (hx : 0 ≤ x) :
    Real.log (ℓ + x) ≤ Real.log ℓ + x / ℓ := by
  have e : ℓ + x = ℓ * (1 + x / ℓ) := by field_simp
  rw [e, Real.log_mul hℓ.ne' (by positivity)]
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + x / ℓ by positivity)
  linarith

/-! ### The neutral pair mass -/

/-- The exact mass `J_λ(1/ℓ) + K J_λ(1/ℓ; R) + C`. For the Gibbs tilt,
`K = e-1` and the bounded corrections are absorbed in `C`. For the electric
moment the cutoff tail has coefficient `K`. -/
noncomputable def neutralMass (lam R K C : ℝ) : ℝ :=
  criticalCycleMass lam + K * criticalTailMass lam R + C

theorem neutralMass_pos {lam R K C : ℝ} (hlam : 0 < lam) (hle : lam ≤ Real.exp (-1))
    (hK : 0 ≤ K) (hC : 0 ≤ C) : 0 < neutralMass lam R K C := by
  have hj := criticalCycleMass_pos hlam hle
  have ht := criticalTailMass_nonneg lam R
  unfold neutralMass
  positivity

/-- **The relative radial error** in the corrected neutral mass in subsection 3.5. The common mass is
bounded by `2π(ℓ + ½ log ℓ) + CB`, and the tail by its Gaussian radial estimate.
The logarithmic mass is at most `log(2πℓ) + (1+K+C+CB)S/ℓ`. -/
theorem log_neutralMass_le {lam R K C CB : ℝ} (hlam : 0 < lam) (hle : lam ≤ Real.exp (-1))
    (hCB : 0 ≤ CB) (hB : criticalCycleMass lam ≤
      2 * Real.pi * (|Real.log lam| + (1 / 2) * Real.log |Real.log lam|) + CB)
    (hR : 2 * lam ≤ R) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hℓ : 1 ≤ |Real.log lam|) (hR0 : 0 < R) (hR1 : R ≤ 1) :
    Real.log (neutralMass lam R K C) ≤ Real.log (2 * Real.pi * |Real.log lam|) +
      (1 + K + (C + CB)) * (1 + Real.log |Real.log lam| + Real.log (1 / R)) / |Real.log lam| := by
  set ℓ := |Real.log lam| with hℓdef
  have hℓ0 : 0 < ℓ := by linarith only [hℓ]
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hlogR : 0 ≤ Real.log (1 / R) :=
    Real.log_nonneg (by rw [le_div_iff₀ hR0]; linarith only [hR1])
  set X : ℝ := (1 / 2) * Real.log ℓ + K * ((1 / 2) * Real.log ℓ + Real.log (1 / R) + 1 / 2) +
    (C + CB) / (2 * Real.pi) with hX
  have hX0 : 0 ≤ X := by positivity
  have hM : neutralMass lam R K C ≤ 2 * Real.pi * ℓ + 2 * Real.pi * X := by
    have hT := integral_tail_gaussianMass_le hlam hle hR hR1
    change criticalTailMass lam R ≤ _ at hT
    have hKT := mul_le_mul_of_nonneg_left hT hK
    dsimp [neutralMass, X]
    have he : 2 * Real.pi * ((C + CB) / (2 * Real.pi)) = C + CB := by field_simp
    dsimp [ℓ] at *
    nlinarith only [hB, hKT, he]
  refine (Real.log_le_log (neutralMass_pos hlam hle hK hC) hM).trans ?_
  refine (log_add_le_log_add_div (by positivity) (by positivity)).trans ?_
  have e : 2 * Real.pi * X / (2 * Real.pi * ℓ) = X / ℓ := by field_simp
  rw [e]
  have hXle : X ≤ (1 + K + (C + CB)) * (1 + Real.log ℓ + Real.log (1 / R)) := by
    have h1 : K * ((1 / 2) * Real.log ℓ + Real.log (1 / R) + 1 / 2) ≤
        K * (1 + Real.log ℓ + Real.log (1 / R)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlogℓ]) hK
    have h2 : (C + CB) / (2 * Real.pi) ≤ C + CB := by
      rw [div_le_iff₀ (by positivity)]
      exact le_mul_of_one_le_right (add_nonneg hC hCB) (by linarith only [Real.pi_gt_three])
    have h3 : C + CB ≤ (C + CB) * (1 + Real.log ℓ + Real.log (1 / R)) :=
      le_mul_of_one_le_right (add_nonneg hC hCB) (by linarith only [hlogℓ, hlogR])
    linarith only [h1, h2, h3, hX, hlogℓ, hlogR]
  have := div_le_div_of_nonneg_right hXle hℓ0.le
  linarith only [this]

/-! ### The optimization  -/
/-- **The two critical entropy optimizations**. After the elementary
normalization, the tree entropy is `3d log(n/d)` and the remaining-cycle entropy
is `h log(n/h)`. Using `h ≤ 2d` gives coefficient five. The same-sign entropy
has coefficient one. Their suprema have orders `ℓ^{-1/5}` and `E/ℓ`.
The common mass `J` has the same logarithmic upper estimate as the neutral mass. -/
theorem critical_exponent_le {c₁ CJ Cm Cj C₀ : ℝ} (hc₁ : 0 ≤ c₁) (hCJ : 0 ≤ CJ)
    (hCm : 0 ≤ Cm) (hCj : 0 ≤ Cj) (hC₀ : 0 ≤ C₀)
    {n p q h d ℓ E Mn Ms J : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (hn : n = p + q + h + d) (hn0 : 0 < n) (hhd : h ≤ 2 * d) (hℓ : 1 ≤ ℓ)
    (hE : 1 + Real.log ℓ ≤ E) (hMn : Real.log Mn ≤ Real.log (2 * Real.pi * ℓ) + Cm * E / ℓ)
    (hJ : Real.log J ≤ Real.log (2 * Real.pi * ℓ) + Cj * E / ℓ)
    (hMs : 0 < Ms) (hMsE : Ms ≤ C₀ * E) :
    3 * d * Real.log (n / d) + h * Real.log (n / h) + q * Real.log (n / q) +
        10 * (d + h + q) + c₁ * (2 * h + 2 * d) + 72 * n / (Real.pi * ℓ) +
        p * Real.log Mn + q * Real.log Ms + h * Real.log J + CJ * d ≤
      n * Real.log (2 * Real.pi * ℓ) +
        (5 * Real.exp ((32 + 6 * c₁ + CJ) / 5) + C₀ * Real.exp (32 + 6 * c₁ + CJ) + Cm + Cj + 24) *
          n * (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) := by
  set A := 32 + 6 * c₁ + CJ with hA
  set L := Real.log (2 * Real.pi * ℓ) with hLdef
  have hℓ0 : 0 < ℓ := by linarith only [hℓ]
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hE1 : 1 ≤ E := by linarith only [hE, hlogℓ]
  have hL : L = Real.log (2 * Real.pi) + Real.log ℓ := by
    rw [hLdef, Real.log_mul (by positivity) hℓ0.ne']
  have hdn : d ≤ n := by linarith only [hn, hp, hq, hh]
  have hpn : p ≤ n := by linarith only [hn, hq, hh, hd]
  -- the entropy terms
  have F4 : h * Real.log (n / h) ≤ 2 * d * Real.log (n / d) + 2 * d :=
    mul_log_div_le_of_le_two_mul hh hhd hdn hn0
  have F5 : h * Real.log J ≤ h * L + n * (Cj * E / ℓ) := by
    have hhn : h ≤ n := by linarith only [hn, hp, hq, hd]
    have h1 := mul_le_mul_of_nonneg_left hJ hh
    have h2 := mul_le_mul_of_nonneg_right hhn (show 0 ≤ Cj * E / ℓ by positivity)
    linarith only [h1, h2]
  -- the neutral pairs
  have F6 : p * Real.log Mn ≤ p * L + n * (Cm * E / ℓ) := by
    have h1 := mul_le_mul_of_nonneg_left hMn hp
    have h2 : p * (Cm * E / ℓ) ≤ n * (Cm * E / ℓ) :=
      mul_le_mul_of_nonneg_right hpn (by positivity)
    linarith only [h1, h2]
  -- the two suprema
  have S1 := mul_add_mul_log_div_le (a := 5) (b := A - L) hd hn0 (by norm_num)
  have S2 := mul_add_mul_log_div_le (a := 1) (b := Real.log Ms + A - L) hq hn0 one_pos
  have X1 : Real.exp ((A - L) / 5 - 1) ≤ Real.exp (A / 5) * ℓ ^ (-(1 / 5 : ℝ)) := by
    have e : Real.exp ((A - L) / 5 - 1) = Real.exp (A / 5) * Real.exp (-1) *
        (2 * Real.pi * ℓ) ^ (-(1 / 5 : ℝ)) := by
      rw [Real.rpow_def_of_pos (by positivity), ← hLdef, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [e]
    have h1 : (2 * Real.pi * ℓ) ^ (-(1 / 5 : ℝ)) ≤ ℓ ^ (-(1 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hℓ0
        (le_mul_of_one_le_left hℓ0.le (by linarith only [Real.pi_gt_three])) (by norm_num)
    have h3 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have h4 : 0 ≤ (2 * Real.pi * ℓ) ^ (-(1 / 5 : ℝ)) := by positivity
    calc Real.exp (A / 5) * Real.exp (-1) * (2 * Real.pi * ℓ) ^ (-(1 / 5 : ℝ))
        ≤ Real.exp (A / 5) * 1 * (2 * Real.pi * ℓ) ^ (-(1 / 5 : ℝ)) := by gcongr
      _ ≤ Real.exp (A / 5) * 1 * ℓ ^ (-(1 / 5 : ℝ)) := by gcongr
      _ = _ := by ring
  have X2 : Real.exp ((Real.log Ms + A - L) / 1 - 1) ≤ C₀ * Real.exp A * E / ℓ := by
    have e : Real.exp ((Real.log Ms + A - L) / 1 - 1) =
        Ms * Real.exp A * Real.exp (-1) / (2 * Real.pi * ℓ) := by
      rw [div_one, sub_eq_add_neg, sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_add,
        Real.exp_log hMs, Real.exp_neg, hLdef, Real.exp_log (by positivity), Real.exp_neg]
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) hℓ0]
    have h3 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have h5 : 1 ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
    have h6 : 0 ≤ C₀ * E * Real.exp A * ℓ := by positivity
    calc Ms * Real.exp A * Real.exp (-1) * ℓ ≤ (C₀ * E) * Real.exp A * 1 * ℓ := by gcongr
      _ = C₀ * E * Real.exp A * ℓ * 1 := by ring
      _ ≤ C₀ * E * Real.exp A * ℓ * (2 * Real.pi) := mul_le_mul_of_nonneg_left h5 h6
      _ = C₀ * Real.exp A * E * (2 * Real.pi * ℓ) := by ring
  have S1' : d * (5 * Real.log (n / d) + (A - L)) ≤
      5 * Real.exp (A / 5) * (n * ℓ ^ (-(1 / 5 : ℝ))) := by
    refine S1.trans ?_
    have := mul_le_mul_of_nonneg_left X1 (show (0 : ℝ) ≤ 5 * n by positivity)
    linarith only [this]
  have S2' : q * (1 * Real.log (n / q) + (Real.log Ms + A - L)) ≤
      C₀ * Real.exp A * (n * (E / ℓ)) := by
    refine S2.trans ?_
    have h1 := mul_le_mul_of_nonneg_left X2 (show (0 : ℝ) ≤ 1 * n by positivity)
    have e : 1 * n * (C₀ * Real.exp A * E / ℓ) = C₀ * Real.exp A * (n * (E / ℓ)) := by ring
    linarith only [h1, e]
  -- the remaining error terms
  have R2 : 72 * n / (Real.pi * ℓ) ≤ 24 * (n * (E / ℓ)) := by
    have hc : 72 / Real.pi ≤ 24 := by
      rw [div_le_iff₀ Real.pi_pos]
      linarith only [Real.pi_gt_three]
    have h1 := mul_le_mul_of_nonneg_right hc (show 0 ≤ n / ℓ by positivity)
    have h2 := mul_le_mul_of_nonneg_left hE1 (show 0 ≤ 24 * (n / ℓ) by positivity)
    have he : 72 * n / (Real.pi * ℓ) = (72 / Real.pi) * (n / ℓ) := by ring
    rw [he]
    have he2 : 24 * (n / ℓ) * E = 24 * (n * (E / ℓ)) := by ring
    linarith only [h1, h2, he2]
  have R4 : n * (Cm * E / ℓ) = Cm * (n * (E / ℓ)) := by ring
  -- the linear part
  have hkey : 3 * d * Real.log (n / d) + h * Real.log (n / h) + q * Real.log (n / q) +
        10 * (d + h + q) + c₁ * (2 * h + 2 * d) + 72 * n / (Real.pi * ℓ) +
        p * Real.log Mn + q * Real.log Ms + h * Real.log J + CJ * d ≤
      n * L + 5 * Real.exp (A / 5) * (n * ℓ ^ (-(1 / 5 : ℝ))) +
        (C₀ * Real.exp A + Cm + Cj + 24) * (n * (E / ℓ)) := by
    have hc6 := mul_le_mul_of_nonneg_left hhd hc₁
    have hdA : d * A = 32 * d + 6 * (c₁ * d) + CJ * d := by rw [hA]; ring
    have hqA : q * A = 32 * q + 6 * (c₁ * q) + CJ * q := by rw [hA]; ring
    have hcq := mul_nonneg hc₁ hq
    have hCJq := mul_nonneg hCJ hq
    have hnL : n * L = p * L + q * L + h * L + d * L := by rw [hn]; ring
    have hCj : n * (Cj * E / ℓ) = Cj * (n * (E / ℓ)) := by ring
    linarith only [F4, F5, F6, S1', S2', R2, R4, hc6, hdA, hqA, hcq, hCJq, hnL,
      hn, hp, hq, hd, hhd, hCj]
  refine hkey.trans ?_
  have hA0 : 0 ≤ n * ℓ ^ (-(1 / 5 : ℝ)) := by positivity
  have hB0 : 0 ≤ n * (E / ℓ) := by positivity
  have e1 : 5 * Real.exp (A / 5) * (n * ℓ ^ (-(1 / 5 : ℝ))) ≤
      (5 * Real.exp (A / 5) + C₀ * Real.exp A + Cm + Cj + 24) * (n * ℓ ^ (-(1 / 5 : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hA0
    have : 0 ≤ C₀ * Real.exp A := by positivity
    linarith only [this, hCm, hCj]
  have e2 : (C₀ * Real.exp A + Cm + Cj + 24) * (n * (E / ℓ)) ≤
      (5 * Real.exp (A / 5) + C₀ * Real.exp A + Cm + Cj + 24) * (n * (E / ℓ)) := by
    refine mul_le_mul_of_nonneg_right ?_ hB0
    have : 0 ≤ 5 * Real.exp (A / 5) := by positivity
    linarith only [this]
  have e3 : (5 * Real.exp (A / 5) + C₀ * Real.exp A + Cm + Cj + 24) * n *
      (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) =
      (5 * Real.exp (A / 5) + C₀ * Real.exp A + Cm + Cj + 24) * (n * ℓ ^ (-(1 / 5 : ℝ))) +
        (5 * Real.exp (A / 5) + C₀ * Real.exp A + Cm + Cj + 24) * (n * (E / ℓ)) := by ring
  rw [e3]
  linarith only [e1, e2]

/-- **Normalization by `N! N^N J_λ(1/ℓ)^N`** in subsection 3.5. The three tree
entropy terms and the two remaining-cycle entropy terms have not yet been
optimized. The loss of logarithmic mass is `J^{-(d+q)}`. -/
theorem critical_count_cell_normalized_le {N K m p₀ : ℕ} (hN : 0 < N)
    (hp₀ : p₀ ≤ m) (hmK : m ≤ K) (hKN : K ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (hle : lam ≤ Real.exp (-1)) (c₁ CJ Mn Ms : ℝ) :
    ((critGraphs N K m p₀).card : ℝ) *
        Real.exp (criticalCellExponent c₁ CJ lam Mn Ms N K m p₀) ≤
      (N ! : ℝ) * (N : ℝ) ^ N * criticalCycleMass lam ^ N * Real.exp
        (3 * ((N : ℝ) - K) * Real.log (N / ((N : ℝ) - K)) +
          ((K : ℝ) - m) * Real.log (N / ((K : ℝ) - m)) +
          ((m : ℝ) - p₀) * Real.log (N / ((m : ℝ) - p₀)) +
          10 * (((N : ℝ) - K) + ((K : ℝ) - m) + ((m : ℝ) - p₀)) +
          c₁ * (2 * ((K : ℝ) - m) + 2 * ((N : ℝ) - K)) +
          72 * N / (Real.pi * |Real.log lam|) +
          p₀ * (Real.log Mn - Real.log (criticalCycleMass lam)) +
          ((m : ℝ) - p₀) * Real.log Ms -
          (((N : ℝ) - K) + ((m : ℝ) - p₀)) * Real.log (criticalCycleMass lam) +
          CJ * ((N : ℝ) - K)) := by
  have hc := CriticalFactorials.card_critGraphs_le_normalized hN hp₀ hmK hKN
  push_cast [Nat.cast_sub ((hp₀.trans hmK).trans hKN), Nat.cast_sub hKN,
    Nat.cast_sub hp₀, Nat.cast_sub hmK] at hc
  refine (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans_eq ?_
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hm : (m : ℝ) ≤ K := by exact_mod_cast hmK
  have hp : (p₀ : ℝ) ≤ m := by exact_mod_cast hp₀
  have eD := mul_log_sub_mul_log_eq (x := (N : ℝ) - K) (by linarith only [hK]) hn
  have eH := mul_log_sub_mul_log_eq (x := (K : ℝ) - m) (by linarith only [hm]) hn
  have eQ := mul_log_sub_mul_log_eq (x := (m : ℝ) - p₀) (by linarith only [hp]) hn
  have heN : (N : ℝ) ^ N = Real.exp (N * Real.log N) := by
    rw [Real.exp_nat_mul, Real.exp_log hn]
  have heJ : criticalCycleMass lam ^ N = Real.exp (N * Real.log (criticalCycleMass lam)) := by
    rw [Real.exp_nat_mul, Real.exp_log (criticalCycleMass_pos hlam hle)]
  rw [heN, heJ, ← Real.exp_log (show (0 : ℝ) < (N ! : ℝ) by positivity),
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  simp only [Real.log_exp]
  congr 1
  rw [criticalCellExponent]
  linear_combination 2 * eD + eH + eQ

/-! ### The partition into cells -/

/-- **Partition by the graph** : the integral over `Λ^{2N}` is the sum over the
self-maps `f` of the integrals over the cells `Λ^{2N} ∩ {φ₁ = f}`. -/
theorem lintegral_pi_box_eq_sum_nnCell (G : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) :
    ∫⁻ Z in Set.univ.pi (fun _ : Fin N ⊕ Fin N => box N), G Z =
      ∑ f : Fin N ⊕ Fin N → Fin N ⊕ Fin N,
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f},
          G Z := by
  have hU : (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) =
      ⋃ f ∈ (Finset.univ : Finset (Fin N ⊕ Fin N → Fin N ⊕ Fin N)),
        (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f} := by
    ext Z
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    exact ⟨fun hZ => ⟨nearestNeighbor Z, hZ, rfl⟩, fun ⟨_, hZ, _⟩ => hZ⟩
  conv_lhs => rw [hU]
  refine lintegral_biUnion_finset ?_ (fun f _ => measurableSet_cell f) G
  intro f _ f' _ hff'
  refine Set.disjoint_left.2 fun Z hZ hZ' => hff' ?_
  rw [← hZ.2, ← hZ'.2]

/-! ### The sum over the graphs (source l. 1648–1650) -/

/-- **The sum over the nearest-neighbour graphs** (the assembly of the proof of (eq:critical upper),
source l. 1648–1650, for a general integrand). For constants `c₁, C_J, C_m, C₀ ≥ 0` there is `C`
such that: if for `N ≥ 2` and `0 < λ ≤ e⁻²` the integral of `G` over every cell
`Λ^{2N} ∩ {φ₁ = f}` is at most `exp (criticalCellExponent c₁ C_J λ Mₙ Mₛ …)`, with
`log Mₙ ≤ log (2πℓ) + C_m E/ℓ`, `0 < Mₛ ≤ C₀ E` and `E ≥ 1 + log ℓ`, then
`∫_{Λ^{2N}} G ≤ exp (2N log N + N (log (2πℓ) - 1) + C N (ℓ^{-1/5} + E/ℓ) + C log (N+1))`.
The elementary count is normalized by `N! N^N J^N` before the two entropy
optimizations. The sum over the types costs `3 log (N+1)`. -/
theorem exists_lintegral_pi_box_le_of_cell_le {c₁ CJ Cm C₀ : ℝ} (hc₁ : 0 ≤ c₁) (hCJ : 0 ≤ CJ)
    (hCm : 0 ≤ Cm) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 2 ≤ N → ∀ lam Mn Ms E : ℝ, 0 < lam → lam ≤ Real.exp (-2) →
      1 + Real.log |Real.log lam| ≤ E →
      Real.log Mn ≤ Real.log (2 * Real.pi * |Real.log lam|) + Cm * E / |Real.log lam| →
      0 < Ms → Ms ≤ C₀ * E →
      ∀ G : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞,
        (∀ (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (Z₀ : Fin N ⊕ Fin N → ℂ), nearestNeighbor Z₀ = f →
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f},
              G Z ≤
            ENNReal.ofReal (Real.exp (criticalCellExponent c₁ CJ lam Mn Ms N (numComponents Z₀)
              (numIsolatedPairs Z₀) (isolatedDipoles Z₀).card))) →
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N, G Z ≤
          ENNReal.ofReal (Real.exp (2 * N * Real.log N
            + N * (Real.log (2 * Real.pi * |Real.log lam|) - 1)
            + C * N * (|Real.log lam| ^ (-(1 / 5 : ℝ)) + E / |Real.log lam|)
            + C * Real.log (N + 1))) := by
  obtain ⟨CB, hCB, hB⟩ := exists_criticalCycleMass_le
  set Cj := 1 + CB with hCj
  have hCj0 : 0 ≤ Cj := by positivity
  set C₁ := 5 * Real.exp ((32 + 6 * c₁ + CJ) / 5) + C₀ * Real.exp (32 + 6 * c₁ + CJ) + Cm + Cj + 24
    with hC₁
  refine ⟨max C₁ 6, by positivity, ?_⟩
  intro N hN lam Mn Ms E hlam hlam2 hE hMn hMs hMsE G hcell
  set ℓ := |Real.log lam| with hℓdef
  have hℓ1 : 1 ≤ ℓ := one_le_abs_log hlam (hlam2.trans (Real.exp_le_exp.2 (by norm_num)))
  have hℓ0 : 0 < ℓ := by linarith only [hℓ1]
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN1 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith only [hNpos])
  have hle1 := hlam2.trans (Real.exp_le_exp.2 (by norm_num : (-2 : ℝ) ≤ -1))
  have hJ : Real.log (criticalCycleMass lam) ≤ Real.log (2 * Real.pi * ℓ) + Cj * E / ℓ := by
    have h := log_neutralMass_le (R := 1) (K := 0) (C := 0) hlam hle1 hCB (hB lam hlam hle1)
      (by have h2 := (two_mul_le_sqrt_neg_log hlam hle1).2
          have he : 2 * Real.exp (-1) ≤ 1 := by
            rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos 1)]
            linarith only [Real.exp_one_gt_d9]
          exact (mul_le_mul_of_nonneg_left hle1 (by norm_num)).trans he)
      le_rfl le_rfl hℓ1 zero_lt_one le_rfl
    simp only [neutralMass, zero_mul, add_zero, div_one, Real.log_one] at h
    change Real.log (criticalCycleMass lam) ≤
      Real.log (2 * Real.pi * ℓ) + (1 + (0 + CB)) * (1 + Real.log ℓ) / ℓ at h
    have hS : (1 + CB) * (1 + Real.log ℓ) / ℓ ≤ Cj * E / ℓ := by
      dsimp [Cj]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE (by positivity)) hℓ0.le
    simp only [zero_add] at h
    linarith only [h, hS]
  have hfact : Real.log (N ! : ℝ) ≤ (N : ℝ) * Real.log N - N + 3 * Real.log (N + 1) := by
    have hf := log_factorial_stirling_le (by omega : 1 ≤ N)
    have hl := Real.log_le_log hNpos (by linarith : (N : ℝ) ≤ N + 1)
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ N + 1 by exact_mod_cast (by omega : 2 ≤ N + 1))
    linarith only [hf, hl, h2, Real.log_two_gt_d9]
  set Target := 2 * N * Real.log N + N * (Real.log (2 * Real.pi * ℓ) - 1)
    + max C₁ 6 * N * (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) + max C₁ 6 * Real.log (N + 1) with hT
  -- the bound for each type `(K, m, p₀)`
  set T := Finset.range (N + 1) ×ˢ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)) with hTdef
  have hper : ∀ t ∈ T, ((critGraphs N t.1 t.2.1 t.2.2).card : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (criticalCellExponent c₁ CJ lam Mn Ms N t.1 t.2.1 t.2.2)) ≤
      ENNReal.ofReal (Real.exp (Target - 3 * Real.log (N + 1))) := by
    rintro ⟨K, m, p₀⟩ -
    dsimp only
    rcases (critGraphs N K m p₀).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.card_empty, Nat.cast_zero, zero_mul]
      exact zero_le
    obtain ⟨hp₀m, hmK, hKN, hr2⟩ := critGraphs_constraints hne
    have hnorm := critical_count_cell_normalized_le (by omega : 0 < N) hp₀m hmK hKN
      hlam hle1 c₁ CJ Mn Ms
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (hnorm.trans ?_)
    have heN : (N : ℝ) ^ N = Real.exp (N * Real.log N) := by
      rw [Real.exp_nat_mul, Real.exp_log hNpos]
    have heJ : criticalCycleMass lam ^ N = Real.exp (N * Real.log (criticalCycleMass lam)) := by
      rw [Real.exp_nat_mul, Real.exp_log (criticalCycleMass_pos hlam hle1)]
    rw [heN, heJ, ← Real.exp_log (show (0 : ℝ) < (N ! : ℝ) by positivity),
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hp₀mR : (p₀ : ℝ) ≤ m := by exact_mod_cast hp₀m
    have hmKR : (m : ℝ) ≤ K := by exact_mod_cast hmK
    have hKNR : (K : ℝ) ≤ N := by exact_mod_cast hKN
    have hr2R : (K : ℝ) - m ≤ 2 * ((N : ℝ) - K) := by
      have : ((K - m : ℕ) : ℝ) ≤ ((2 * (N - K) : ℕ) : ℝ) := by exact_mod_cast hr2
      push_cast [Nat.cast_sub hmK, Nat.cast_sub hKN] at this
      linarith only [this]
    have key := critical_exponent_le (n := N) (p := p₀) (q := (m : ℝ) - p₀)
      (h := (K : ℝ) - m) (d := (N : ℝ) - K) (ℓ := ℓ) (E := E) (Mn := Mn) (Ms := Ms) (J := criticalCycleMass lam) hc₁ hCJ hCm hCj0
      hC₀ (Nat.cast_nonneg _) (by linarith only [hp₀mR]) (by linarith only [hmKR])
      (by linarith only [hKNR]) (by ring) hNpos hr2R hℓ1 hE hMn hJ hMs hMsE
    have hfin :
        Real.log (N ! : ℝ) + N * Real.log N + N * Real.log (criticalCycleMass lam) +
          (3 * (N - K) * Real.log (N / (N - K)) + (K - m) * Real.log (N / (K - m)) +
            (m - p₀) * Real.log (N / (m - p₀)) + 10 * ((N - K) + (K - m) + (m - p₀)) +
            c₁ * (2 * (K - m) + 2 * (N - K)) + 72 * N / (Real.pi * |Real.log lam|) +
            p₀ * (Real.log Mn - Real.log (criticalCycleMass lam)) +
            (m - p₀) * Real.log Ms - ((N - K) + (m - p₀)) * Real.log (criticalCycleMass lam) +
            CJ * (N - K)) =
        Real.log (N ! : ℝ) + N * Real.log N +
          (3 * (N - K) * Real.log (N / (N - K)) + (K - m) * Real.log (N / (K - m)) +
            (m - p₀) * Real.log (N / (m - p₀)) + 10 * ((N - K) + (K - m) + (m - p₀)) +
            c₁ * (2 * (K - m) + 2 * (N - K)) + 72 * N / (Real.pi * ℓ) +
            p₀ * Real.log Mn + (m - p₀) * Real.log Ms +
            (K - m) * Real.log (criticalCycleMass lam) + CJ * (N - K)) := by
      rw [← hℓdef]
      ring
    rw [hfin]
    have hC6 : (6 : ℝ) ≤ max C₁ 6 := le_max_right _ _
    have hCC : C₁ ≤ max C₁ 6 := le_max_left _ _
    have hE1 : 1 ≤ E := by linarith only [hE, hlogℓ]
    have hpos : 0 ≤ (N : ℝ) * (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) := by positivity
    have h1 : C₁ * N * (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) ≤
        max C₁ 6 * N * (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) := by
      have := mul_le_mul_of_nonneg_right hCC hpos
      linarith only [this]
    have h2 : 6 * Real.log ((N : ℝ) + 1) ≤ max C₁ 6 * Real.log (N + 1) :=
      mul_le_mul_of_nonneg_right hC6 hlogN1
    rw [hT]
    linarith only [key, h1, h2, hfact]
  -- the partition into cells and the sum over the types
  have hcell' : ∀ f : Fin N ⊕ Fin N → Fin N ⊕ Fin N,
      ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f}, G Z ≤
        ∑ t ∈ T, (if f ∈ critGraphs N t.1 t.2.1 t.2.2 then
          ENNReal.ofReal (Real.exp (criticalCellExponent c₁ CJ lam Mn Ms N t.1 t.2.1 t.2.2))
          else 0) := by
    intro f
    by_cases hf : ∃ Z₀ : Fin N ⊕ Fin N → ℂ, nearestNeighbor Z₀ = f
    · obtain ⟨Z₀, hZ₀⟩ := hf
      have hb := hcell f Z₀ hZ₀
      have ht₀T : (numComponents Z₀, numIsolatedPairs Z₀, (isolatedDipoles Z₀).card) ∈ T := by
        rw [hTdef, Finset.mem_product, Finset.mem_product, Finset.mem_range, Finset.mem_range,
          Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le (numComponents_le Z₀),
          Nat.lt_succ_of_le (numIsolatedPairs_le Z₀),
          Nat.lt_succ_of_le (isolatedDipoles_card_le Z₀)⟩
      have hft : f ∈ critGraphs N (numComponents Z₀) (numIsolatedPairs Z₀)
          (isolatedDipoles Z₀).card :=
        mem_critGraphs.2 ⟨Z₀, hZ₀, rfl, rfl, rfl⟩
      have hsingle := Finset.single_le_sum
        (f := fun t : ℕ × ℕ × ℕ => if f ∈ critGraphs N t.1 t.2.1 t.2.2 then
          ENNReal.ofReal (Real.exp (criticalCellExponent c₁ CJ lam Mn Ms N t.1 t.2.1 t.2.2))
          else 0) (fun _ _ => zero_le) ht₀T
      simp only at hsingle
      rw [ite_eq_left hft] at hsingle
      exact hb.trans hsingle
    · have hempty : (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
          {Z | nearestNeighbor Z = f} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun Z hZ => hf ⟨Z, hZ.2⟩
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
      exact zero_le
  rw [lintegral_pi_box_eq_sum_nnCell]
  calc ∑ f : Fin N ⊕ Fin N → Fin N ⊕ Fin N,
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f}, G Z
      ≤ ∑ f : Fin N ⊕ Fin N → Fin N ⊕ Fin N, ∑ t ∈ T,
          (if f ∈ critGraphs N t.1 t.2.1 t.2.2 then
            ENNReal.ofReal (Real.exp (criticalCellExponent c₁ CJ lam Mn Ms N t.1 t.2.1 t.2.2))
            else 0) := Finset.sum_le_sum fun f _ => hcell' f
    _ = ∑ t ∈ T, ((critGraphs N t.1 t.2.1 t.2.2).card : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (criticalCellExponent c₁ CJ lam Mn Ms N t.1 t.2.1 t.2.2)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _t ∈ T, ENNReal.ofReal (Real.exp (Target - 3 * Real.log (N + 1))) :=
        Finset.sum_le_sum hper
    _ = ENNReal.ofReal (Real.exp Target) := by
        rw [Finset.sum_const, nsmul_eq_mul, hTdef, Finset.card_product, Finset.card_product,
          Finset.card_range]
        have e : (((N + 1) * ((N + 1) * (N + 1)) : ℕ) : ℝ≥0∞) =
            ENNReal.ofReal (Real.exp (3 * Real.log (N + 1))) := by
          have h3 : Real.exp (3 * Real.log ((N : ℝ) + 1)) = ((N : ℝ) + 1) ^ 3 := by
            rw [show (3 : ℝ) * Real.log ((N : ℝ) + 1) = ((3 : ℕ) : ℝ) * Real.log ((N : ℝ) + 1) by
              norm_num, ← Real.log_pow, Real.exp_log (by positivity)]
          rw [← ENNReal.ofReal_natCast, h3]
          congr 1
          push_cast
          ring
        rw [e, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring

end TwoComponentCoulomb

end
