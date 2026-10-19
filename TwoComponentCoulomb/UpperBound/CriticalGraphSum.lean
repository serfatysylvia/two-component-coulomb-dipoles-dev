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
import TwoComponentCoulomb.UpperBound.MarkedGraphCount

/-!
# The sum over the nearest-neighbour graphs at `β = 2` (Proposition 3.10, eq. (eq:critical upper))

Source: l. 1698--1739 (proof of Proposition 3.10, `β = 2`: counting, Stirling, optimization), also
used for the electric moment of Theorem 2 at `β = 2` (l. 2023--2055). The supremum over `δ = d/N`
is `O(ℓ^{-1/5}) = O(ω_λ)` (l. 1739, 2055), and the bounds below carry the rate `ℓ^{-1/5}` itself.

Write `ℓ = |log λ|`. The integral over `Λ^{2N}` is split over the nearest-neighbour graphs
`f = φ₁(Z)` (a finite partition of `Λ^{2N}`). A graph with `K` components, `m` isolated pairs and
`p₀` isolated neutral pairs contributes at most `exp (pairCellExponent …)`
(`UpperBound/CriticalCells.lean`). The number of such graphs is bounded by the marked-graph count of
Step 1 of the proof of Proposition 3.10, with the isolated pairs marked (source l. 1709--1713; the
source's additional factor `2^{-(K-p₀)}` is not needed). Stirling's formula, `h = K - m ≤ 2d`,
`d = N - K`, and the optimization `sup_{s > 0} s (A log (1/s) + b) ≤ A e^{b/A - 1}` (source
l. 1714--1739) then give the bound, the sum over `(K, m, p₀)` costing `3 log (N + 1)`.

This is stated for a general integrand whose cell integrals are bounded by
`exp (pairCellExponent …)`, with neutral and same-sign pair masses `Mₙ` and `Mₛ ≤ C₀ E`. The
instances are (eq:critical upper) (`UpperBound/CriticalUpper.lean`, `Mₛ` constant) and
(eq:critical electric) (`Fluctuations/CriticalElectric.lean`, `Mₛ` of order `E`).

## Main results

* `TwoComponentCoulomb.critGraphs`, `TwoComponentCoulomb.card_critGraphs_le_exp`: the nearest-
  neighbour graphs with `K` components, `m` isolated pairs and `p₀` isolated dipoles, and their
  count (source l. 1709--1713).
* `TwoComponentCoulomb.mul_add_mul_log_div_le` (source l. 1598--1600, 1733--1738): the supremum
  bound.
* `TwoComponentCoulomb.neutralMass`, `TwoComponentCoulomb.log_neutralMass_le` (eq:critical-TR,
  l. 1698--1701): the radial integral bound `Mₙ` of a neutral pair and
  `log Mₙ ≤ log (2πℓ) + C (1 + log ℓ + log (1/R))/ℓ`.
* `TwoComponentCoulomb.critical_exponent_le` (source l. 1714--1739): the bound on the exponent of
  a type `(K, m, p₀)`.
* `TwoComponentCoulomb.lintegral_pi_box_eq_sum_nnCell` (source l. 1668): the partition into cells.
* `TwoComponentCoulomb.exists_lintegral_pi_box_le_of_cell_le` (source l. 1709--1739): if every cell
  integral is at most `exp (pairCellExponent …)`, then
  `∫_{Λ^{2N}} G ≤ exp (2N log N + N (log (2πℓ) - 1) + C N (ℓ^{-1/5} + E/ℓ) + C log (N+1))`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal Nat

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### The graphs with given `(K, m, p₀)` and their number -/

open scoped Classical in
/-- The nearest-neighbour graphs `f = φ₁(Z)` with `K` components, `m` isolated pairs and `p₀`
isolated neutral pairs (source l. 1668, 1709). -/
noncomputable def critGraphs (N K m p₀ : ℕ) : Finset (Fin N ⊕ Fin N → Fin N ⊕ Fin N) :=
  univ.filter fun f => ∃ Z : Fin N ⊕ Fin N → ℂ, nearestNeighbor Z = f ∧ numComponents Z = K ∧
    numIsolatedPairs Z = m ∧ (isolatedDipoles Z).card = p₀

theorem mem_critGraphs {K m p₀ : ℕ} {f : Fin N ⊕ Fin N → Fin N ⊕ Fin N} :
    f ∈ critGraphs N K m p₀ ↔ ∃ Z : Fin N ⊕ Fin N → ℂ, nearestNeighbor Z = f ∧
      numComponents Z = K ∧ numIsolatedPairs Z = m ∧ (isolatedDipoles Z).card = p₀ := by
  simp [critGraphs]

/-- The isolated pairs of `φ₁(Z)`, marked: a marked involution in the sense of Step 1. -/
theorem isMarkedInvolution_isolatedPairSet (Z : Fin N ⊕ Fin N → ℂ) :
    IsMarkedInvolution (numComponents Z) (numIsolatedPairs Z) (isolatedDipoles Z).card
      (cycleInvolution Z) (isolatedPairSet Z) := by
  classical
  have hT : ∀ i ∈ isolatedPairSet Z, i ∈ cycleVerts Z := fun i hi =>
    isolatedPairSet_subset_cycleVerts hi
  refine ⟨cycleInvolution_involutive Z, ?_, ?_, ?_, card_isolatedPairSet, ?_⟩
  · rw [movedPoints_cycleInvolution]
    exact card_cycleVerts_eq_two_mul_numComponents Z
  · rw [movedPoints_cycleInvolution]
    exact hT
  · intro i hi
    rw [cycleInvolution_of_mem_cycleVerts (hT i hi)]
    exact (mem_isolatedPairSet Z).2 (isIsolatedPair_nearestNeighbor ((mem_isolatedPairSet Z).1 hi))
  · rw [← card_filter_isIsolatedDipole Z]
    congr 1
    ext i
    rw [Finset.mem_filter, Finset.mem_filter, ← charge_mul_eq_neg_one_iff, isIsolatedDipole_iff,
      mem_isolatedPairSet]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi, h2⟩
      rw [cycleInvolution_of_mem_cycleVerts (mem_cycleVerts_of_isIsolatedPair hi)] at h2
      exact ⟨hi, h2⟩
    · rintro ⟨hi, h2⟩
      rw [cycleInvolution_of_mem_cycleVerts (mem_cycleVerts_of_isIsolatedPair hi)]
      exact ⟨hi, h2⟩

theorem critGraphs_subset (K m p₀ : ℕ) :
    critGraphs N K m p₀ ⊆ (markedCover N K m p₀).biUnion fun γ =>
      Fintype.piFinset fun i => if γ.1 i ≠ i then ({γ.1 i} : Finset (Fin N ⊕ Fin N)) else univ := by
  intro f hf
  obtain ⟨Z, hf, hK, hm, hp₀⟩ := mem_critGraphs.1 hf
  have hmi := isMarkedInvolution_isolatedPairSet Z
  rw [hK, hm, hp₀] at hmi
  refine Finset.mem_biUnion.2 ⟨(cycleInvolution Z, isolatedPairSet Z), mem_markedCover hmi, ?_⟩
  rw [Fintype.mem_piFinset]
  intro i
  by_cases hi : i ∈ cycleVerts Z
  · have hne : cycleInvolution Z i ≠ i := by
      rw [cycleInvolution_of_mem_cycleVerts hi]
      exact nearestNeighbor_ne Z i
    simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte, Finset.mem_singleton]
    rw [cycleInvolution_of_mem_cycleVerts hi, ← hf]
  · have : ¬ (cycleInvolution Z i ≠ i) := by
      rw [cycleInvolution_of_not_mem_cycleVerts hi]
      exact fun h' => h' rfl
    simp only [this, ↓reduceIte, Finset.mem_univ]

/-- **The number of graphs** (source l. 1709--1713), before Stirling's formula:
`|D| ≤ C(N,p₀) (N)_{p₀} · C(2N-2p₀, K-p₀) (2N-p₀-K)_{K-p₀} · C(K-p₀, m-p₀) · (2N)^{2N-2K}`. -/
theorem card_critGraphs_le (K m p₀ : ℕ) :
    (critGraphs N K m p₀).card ≤ N.choose p₀ * N.descFactorial p₀ *
      ((2 * N - 2 * p₀).choose (K - p₀) *
        (2 * N - 2 * p₀ - (K - p₀)).descFactorial (K - p₀)) * (K - p₀).choose (m - p₀) *
      (2 * N) ^ (2 * N - 2 * K) := by
  refine (Finset.card_le_card (critGraphs_subset K m p₀)).trans (Finset.card_biUnion_le.trans ?_)
  have hfib : ∀ γ ∈ markedCover N K m p₀,
      (Fintype.piFinset fun i => if γ.1 i ≠ i then ({γ.1 i} : Finset (Fin N ⊕ Fin N))
        else univ).card = (2 * N) ^ (2 * N - 2 * K) := by
    intro γ hγ
    rw [card_piFinset_unmoved, card_moved_of_mem_markedCover hγ]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const]
  exact Nat.mul_le_mul_right _ card_markedCover_le

/-- The count in factorial form:
`|D| · p₀! ((N-p₀)!)² (2N-2K)! (m-p₀)! (K-m)! ≤ (N!)² (2N-2p₀)! (2N)^{2N-2K}`. -/
theorem card_critGraphs_mul_le {K m p₀ : ℕ} (hp₀ : p₀ ≤ m) (hmK : m ≤ K) (hKN : K ≤ N) :
    (critGraphs N K m p₀).card *
        (p₀ ! * ((N - p₀)!) ^ 2 * (2 * N - 2 * K)! * (m - p₀)! * (K - m)!) ≤
      (N !) ^ 2 * (2 * N - 2 * p₀)! * (2 * N) ^ (2 * N - 2 * K) := by
  have hc := card_critGraphs_le (N := N) K m p₀
  refine (Nat.mul_le_mul_right _ hc).trans (le_of_eq ?_)
  have e1 : N.choose p₀ * p₀ ! * (N - p₀)! = N ! :=
    Nat.choose_mul_factorial_mul_factorial (by omega)
  have e2 : (N - p₀)! * N.descFactorial p₀ = N ! := Nat.factorial_mul_descFactorial (by omega)
  have e3 : (2 * N - 2 * p₀).choose (K - p₀) * (K - p₀)! * (2 * N - 2 * p₀ - (K - p₀))! =
      (2 * N - 2 * p₀)! := Nat.choose_mul_factorial_mul_factorial (by omega)
  have e4 : (2 * N - 2 * p₀ - (K - p₀) - (K - p₀))! *
      (2 * N - 2 * p₀ - (K - p₀)).descFactorial (K - p₀) = (2 * N - 2 * p₀ - (K - p₀))! :=
    Nat.factorial_mul_descFactorial (by omega)
  have e5 : (K - p₀).choose (m - p₀) * (m - p₀)! * (K - p₀ - (m - p₀))! = (K - p₀)! :=
    Nat.choose_mul_factorial_mul_factorial (by omega)
  have h4 : 2 * N - 2 * p₀ - (K - p₀) - (K - p₀) = 2 * N - 2 * K := by omega
  have h5 : K - p₀ - (m - p₀) = K - m := by omega
  rw [h4] at e4
  rw [h5] at e5
  calc _ = (N.choose p₀ * p₀ ! * (N - p₀)!) * ((N - p₀)! * N.descFactorial p₀) *
        ((2 * N - 2 * p₀).choose (K - p₀) * ((2 * N - 2 * K)! *
          (2 * N - 2 * p₀ - (K - p₀)).descFactorial (K - p₀))) *
        ((K - p₀).choose (m - p₀) * (m - p₀)! * (K - m)!) * (2 * N) ^ (2 * N - 2 * K) := by
        ring
    _ = N ! * N ! * ((2 * N - 2 * p₀).choose (K - p₀) * (2 * N - 2 * p₀ - (K - p₀))!) *
        (K - p₀)! * (2 * N) ^ (2 * N - 2 * K) := by rw [e1, e2, e4, e5]
    _ = _ := by
        rw [← e3]
        ring

/-- **The logarithmic count** (source l. 1709--1714, with Stirling's formula): for `N ≥ 2`, if the
set of graphs with parameters `(K, m, p₀)` is nonempty, then `p₀ ≤ m ≤ K ≤ N`, `K - m ≤ 2(N - K)`,
and its size is at most
`exp (2N log N - (2N-2K) log ((N-K)/N) - p₀ log p₀ - (m-p₀) log (m-p₀) - (K-m) log (K-m) - N
  + 60 log (N+1) + 60 (N-K) + 60 (m-p₀))`. -/
theorem card_critGraphs_le_exp (hN : 2 ≤ N) {K m p₀ : ℕ} (hne : (critGraphs N K m p₀).Nonempty) :
    p₀ ≤ m ∧ m ≤ K ∧ K ≤ N ∧ K - m ≤ 2 * (N - K) ∧
      ((critGraphs N K m p₀).card : ℝ) ≤ Real.exp
        (2 * N * Real.log N - (2 * N - 2 * K) * Real.log (((N : ℝ) - K) / N)
          - p₀ * Real.log p₀ - ((m : ℝ) - p₀) * Real.log ((m : ℝ) - p₀)
          - ((K : ℝ) - m) * Real.log ((K : ℝ) - m) - N + 60 * Real.log (N + 1)
          + 60 * (N - K) + 60 * (m - p₀)) := by
  obtain ⟨f, hf⟩ := hne
  obtain ⟨Z, -, hK, hm, hp₀⟩ := mem_critGraphs.1 hf
  have hp₀m : p₀ ≤ m := by
    classical
    rw [← hp₀, ← hm]
    have h1 := card_filter_isIsolatedDipole Z
    have h2 := card_isolatedPairSet (Z := Z)
    have h3 : (univ.filter (IsIsolatedDipole Z)).card ≤ (isolatedPairSet Z).card := by
      refine Finset.card_le_card fun i hi => ?_
      exact (mem_isolatedPairSet Z).2 (Finset.mem_filter.1 hi).2.isIsolatedPair
    omega
  have hmK : m ≤ K := hm ▸ hK ▸ numIsolatedPairs_le_numComponents Z
  have hKN : K ≤ N := hK ▸ numComponents_le Z
  have hr2 : K - m ≤ 2 * (N - K) := by
    have := numComponents_le_numIsolatedPairs_add Z
    rw [hK, hm] at this
    omega
  refine ⟨hp₀m, hmK, hKN, hr2, ?_⟩
  have h38 : K ≤ m + 38 * (N - K) := by omega
  have hmul := card_critGraphs_mul_le (N := N) hp₀m hmK hKN
  have hlog := log_count_sub_le hN hp₀m hmK hKN h38
  set A : ℕ := (N !) ^ 2 * (2 * N - 2 * p₀)! * (2 * N) ^ (2 * N - 2 * K) with hA
  set D : ℕ := p₀ ! * ((N - p₀)!) ^ 2 * (2 * N - 2 * K)! * (m - p₀)! * (K - m)! with hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := by rw [hD]; positivity
    exact_mod_cast this
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have hN0 : 0 < 2 * N := by omega
    have : 0 < A := by rw [hA]; positivity
    exact_mod_cast this
  have hcard : ((critGraphs N K m p₀).card : ℝ) ≤ (A : ℝ) / D := by
    rw [le_div_iff₀ hDpos]
    exact_mod_cast hmul
  refine hcard.trans ?_
  rw [← Real.exp_log (div_pos hApos hDpos), Real.log_div hApos.ne' hDpos.ne']
  exact Real.exp_le_exp.2 hlog

/-! ### Elementary inequalities -/

/-- `x log n - x log x = x log (n/x)`, also for `x = 0`. -/
theorem mul_log_sub_mul_log_eq {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) :
    x * Real.log n - x * Real.log x = x * Real.log (n / x) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  · rw [Real.log_div hn.ne' hx'.ne']
    ring

/-- `-x log (x/n) = x log (n/x)`, also for `x = 0`. -/
theorem neg_mul_log_div_eq {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) :
    -(x * Real.log (x / n)) = x * Real.log (n / x) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  · rw [Real.log_div hn.ne' hx'.ne', Real.log_div hx'.ne' hn.ne']
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

/-- For `0 ≤ h ≤ 2d` and `d ≤ n`: `h log (n/h) ≤ 2d log (n/d) + 2d` (source l. 1720--1722). -/
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

/-- **The supremum bound** (source l. 1598--1600, 1733--1738): for `x ≥ 0`, `n, a > 0`,
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

/-- The bound `2π (ℓ + ½ log ℓ) + K · 2π (½ log ℓ + log (1/R) + ½) + C` on the radial integral of
a neutral pair, `ℓ = |log λ|`: `T_R = J_λ(1/ℓ) + C + (e-1)(J_λ(1/ℓ;R) + C)` in (eq:critical upper)
(source l. 1693--1696, `K = e - 1`) and `J_λ(1/ℓ) + C'S` in (eq:critical electric) (source
l. 2026--2036, `R = γ`). -/
noncomputable def neutralMass (lam R K C : ℝ) : ℝ :=
  2 * Real.pi * (|Real.log lam| + (1 / 2) * Real.log |Real.log lam|) +
    K * (2 * Real.pi * ((1 / 2) * Real.log |Real.log lam| + Real.log (1 / R) + 1 / 2)) + C

theorem neutralMass_pos {lam R K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hℓ : 1 ≤ |Real.log lam|)
    (hR0 : 0 < R) (hR1 : R ≤ 1) : 0 < neutralMass lam R K C := by
  have hlogℓ : 0 ≤ Real.log |Real.log lam| := Real.log_nonneg hℓ
  have hlogR : 0 ≤ Real.log (1 / R) :=
    Real.log_nonneg (by rw [le_div_iff₀ hR0]; linarith only [hR1])
  unfold neutralMass
  positivity

/-- **The neutral pair bound**: `log Mₙ ≤ log (2πℓ) + (1 + K + C) S/ℓ` with
`S = 1 + log ℓ + log (1/R)`, from `Mₙ = 2πℓ + 2π (½ log ℓ + K (½ log ℓ + log (1/R) + ½)) + C`
(eq:critical-TR, source l. 1698--1701, from (eq:critical-B) and (eq:critical-BR), l. 707--715:
`J_λ(1/ℓ) = 2π (ℓ + ½ log ℓ) + O(1)` and `J_λ(1/ℓ;R) = 2π (log (1/R) + ½ log ℓ) + O(1)`). -/
theorem log_neutralMass_le {lam R K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hℓ : 1 ≤ |Real.log lam|) (hR0 : 0 < R) (hR1 : R ≤ 1) :
    Real.log (neutralMass lam R K C) ≤ Real.log (2 * Real.pi * |Real.log lam|) +
      (1 + K + C) * (1 + Real.log |Real.log lam| + Real.log (1 / R)) / |Real.log lam| := by
  set ℓ := |Real.log lam| with hℓdef
  have hℓ0 : 0 < ℓ := by linarith only [hℓ]
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hlogR : 0 ≤ Real.log (1 / R) :=
    Real.log_nonneg (by rw [le_div_iff₀ hR0]; linarith only [hR1])
  set X : ℝ := (1 / 2) * Real.log ℓ + K * ((1 / 2) * Real.log ℓ + Real.log (1 / R) + 1 / 2) +
    C / (2 * Real.pi) with hX
  have hX0 : 0 ≤ X := by positivity
  have hM : neutralMass lam R K C = 2 * Real.pi * ℓ + 2 * Real.pi * X := by
    rw [neutralMass, hX, ← hℓdef]
    field_simp
    ring
  rw [hM]
  refine (log_add_le_log_add_div (by positivity) (by positivity)).trans ?_
  have e : 2 * Real.pi * X / (2 * Real.pi * ℓ) = X / ℓ := by field_simp
  rw [e]
  have hXle : X ≤ (1 + K + C) * (1 + Real.log ℓ + Real.log (1 / R)) := by
    have h1 : K * ((1 / 2) * Real.log ℓ + Real.log (1 / R) + 1 / 2) ≤
        K * (1 + Real.log ℓ + Real.log (1 / R)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlogℓ]) hK
    have h2 : C / (2 * Real.pi) ≤ C := by
      rw [div_le_iff₀ (by positivity)]
      exact le_mul_of_one_le_right hC (by linarith only [Real.pi_gt_three])
    have h3 : C ≤ C * (1 + Real.log ℓ + Real.log (1 / R)) :=
      le_mul_of_one_le_right hC (by linarith only [hlogℓ, hlogR])
    linarith only [h1, h2, h3, hX, hlogℓ, hlogR]
  have := div_le_div_of_nonneg_right hXle hℓ0.le
  linarith only [this]

/-! ### The optimization (source l. 1714--1739) -/
/-- **The exponent bound** (source l. 1714--1739, also used at l. 2045--2055). With `d = N - K`
tree vertices, `h = K - m ≤ 2d` non-isolated cycles, `q = m - p₀` same-sign pairs and `p = p₀`
neutral pairs (`n = p + q + h + d`), the sum of the logarithmic count of the graphs and of the
logarithm of the cell bound, minus `2n log n`, is at most `n (log (2πℓ) - 1) + C n (ℓ^{-1/5} + E/ℓ)`,
where `E ≥ 1 + log ℓ`, `log Mₙ ≤ log (2πℓ) + C_m E/ℓ` bounds the neutral pair and `Mₛ ≤ C₀ E` the
same-sign pair (a constant `Mₛ` in (eq:critical upper), with `C₀ = Mₛ`). The suprema over `δ = d/n`
and `ζ = q/n` are bounded by `mul_add_mul_log_div_le`: `5 e^{A/5} ℓ^{-1/5}` (the exponent `1/5` is
the reciprocal of the coefficient `5 = 3 + 2` of `δ log (1/δ)`, source l. 1739) and
`sup ζ (log (1/ζ) + log Mₛ + A - log (2πℓ)) ≤ Mₛ e^{A-1}/(2πℓ) ≤ C₀ e^A E/ℓ`. -/
theorem critical_exponent_le {c₁ CJ Cm C₀ : ℝ} (hc₁ : 0 ≤ c₁) (hCJ : 0 ≤ CJ) (hCm : 0 ≤ Cm)
    (hC₀ : 0 ≤ C₀) {n p q h d ℓ E Mn Ms : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (hn : n = p + q + h + d) (hn0 : 0 < n) (hhd : h ≤ 2 * d) (hℓ : 1 ≤ ℓ)
    (hE : 1 + Real.log ℓ ≤ E) (hMn : Real.log Mn ≤ Real.log (2 * Real.pi * ℓ) + Cm * E / ℓ)
    (hMs : 0 < Ms) (hMsE : Ms ≤ C₀ * E) :
    (2 * d * Real.log (n / d) - p * Real.log p - q * Real.log q - h * Real.log h - n
        + 60 * (d + q))
      + (c₁ * (2 * h + 2 * d) + 36 * n / (Real.pi * ℓ) + p * Real.log Mn + q * Real.log Ms
        + (p + q) * Real.log n + h * Real.log n + h * Real.log (ℓ + Real.log (n / h))
        + h * Real.log (2 * Real.pi) + d * Real.log (n / d) + CJ * d
        + CJ * n * (Real.log ℓ / ℓ))
    ≤ n * (Real.log (2 * Real.pi * ℓ) - 1) +
      (5 * Real.exp ((65 + 6 * c₁ + CJ) / 5) + C₀ * Real.exp (65 + 6 * c₁ + CJ) + Cm + 13 + CJ) *
        n * (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) := by
  set A := 65 + 6 * c₁ + CJ with hA
  set L := Real.log (2 * Real.pi * ℓ) with hLdef
  have hℓ0 : 0 < ℓ := by linarith only [hℓ]
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hE1 : 1 ≤ E := by linarith only [hE, hlogℓ]
  have hL : L = Real.log (2 * Real.pi) + Real.log ℓ := by
    rw [hLdef, Real.log_mul (by positivity) hℓ0.ne']
  have hdn : d ≤ n := by linarith only [hn, hp, hq, hh]
  have hpn : p ≤ n := by linarith only [hn, hq, hh, hd]
  -- the entropy terms
  have F2 : p * Real.log n - p * Real.log p ≤ n - p := by
    rw [mul_log_sub_mul_log_eq hp hn0]; exact mul_log_div_le_sub hp hn0
  have F3 : q * Real.log n - q * Real.log q = q * Real.log (n / q) := mul_log_sub_mul_log_eq hq hn0
  have F4 : h * Real.log n - h * Real.log h ≤ 2 * d * Real.log (n / d) + 2 * d := by
    rw [mul_log_sub_mul_log_eq hh hn0]
    exact mul_log_div_le_of_le_two_mul hh hhd hdn hn0
  -- the cycles of the non-isolated components
  have F5 : h * Real.log (ℓ + Real.log (n / h)) ≤ h * Real.log ℓ + n / ℓ := by
    rcases hh.eq_or_lt with rfl | hh'
    · simp only [zero_mul, zero_add]
      positivity
    have hlg : 0 ≤ Real.log (n / h) :=
      Real.log_nonneg (by rw [le_div_iff₀ hh']; linarith only [hn, hp, hq, hd])
    have h1 := mul_le_mul_of_nonneg_left (log_add_le_log_add_div hℓ0 hlg) hh
    have h2 : h * Real.log (n / h) ≤ n - h := mul_log_div_le_sub hh hn0
    have h3 : h * (Real.log (n / h) / ℓ) ≤ n / ℓ := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hℓ0]
      linarith only [h2, hh]
    linarith only [h1, h3]
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
  have R1 : n / ℓ ≤ n * (E / ℓ) := by
    have e : n * (E / ℓ) = E * (n / ℓ) := by ring
    rw [e]
    exact le_mul_of_one_le_left (by positivity) hE1
  have R2 : 36 * n / (Real.pi * ℓ) ≤ 12 * (n * (E / ℓ)) := by
    have h1 : 36 / Real.pi ≤ 12 := by
      rw [div_le_iff₀ Real.pi_pos]
      linarith only [Real.pi_gt_three]
    have h2 : 36 / Real.pi ≤ 12 * E := by linarith only [h1, hE1]
    have e1 : 36 * n / (Real.pi * ℓ) = (36 / Real.pi) * (n / ℓ) := by
      field_simp
    have e2 : 12 * (n * (E / ℓ)) = (12 * E) * (n / ℓ) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have R3 : CJ * n * (Real.log ℓ / ℓ) ≤ CJ * (n * (E / ℓ)) := by
    have : Real.log ℓ / ℓ ≤ E / ℓ := div_le_div_of_nonneg_right (by linarith only [hE]) hℓ0.le
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ CJ * n by positivity)
    linarith only [this]
  have R4 : n * (Cm * E / ℓ) = Cm * (n * (E / ℓ)) := by ring
  -- the linear part
  have hkey : (2 * d * Real.log (n / d) - p * Real.log p - q * Real.log q - h * Real.log h - n
        + 60 * (d + q))
      + (c₁ * (2 * h + 2 * d) + 36 * n / (Real.pi * ℓ) + p * Real.log Mn + q * Real.log Ms
        + (p + q) * Real.log n + h * Real.log n + h * Real.log (ℓ + Real.log (n / h))
        + h * Real.log (2 * Real.pi) + d * Real.log (n / d) + CJ * d
        + CJ * n * (Real.log ℓ / ℓ))
      ≤ n * (L - 1) + 5 * Real.exp (A / 5) * (n * ℓ ^ (-(1 / 5 : ℝ))) +
        (C₀ * Real.exp A + Cm + 13 + CJ) * (n * (E / ℓ)) := by
    have hc6 : c₁ * h ≤ c₁ * (2 * d) := mul_le_mul_of_nonneg_left hhd hc₁
    have hdA : d * A = 65 * d + 6 * (c₁ * d) + CJ * d := by rw [hA]; ring
    have hqA : q * A = 65 * q + 6 * (c₁ * q) + CJ * q := by rw [hA]; ring
    have hcq : 0 ≤ c₁ * q := mul_nonneg hc₁ hq
    have hCJq : 0 ≤ CJ * q := mul_nonneg hCJ hq
    have hhL : h * L = h * Real.log (2 * Real.pi) + h * Real.log ℓ := by rw [hL]; ring
    have hnL : n * L = p * L + q * L + h * L + d * L := by rw [hn]; ring
    linarith only [F2, F3, F4, F5, F6, S1', S2', R1, R2, R3, R4, hc6, hdA, hqA, hcq, hCJq, hhL,
      hnL, hn, hp, hq, hd, hhd]
  refine hkey.trans ?_
  have hA0 : 0 ≤ n * ℓ ^ (-(1 / 5 : ℝ)) := by positivity
  have hB0 : 0 ≤ n * (E / ℓ) := by positivity
  have e1 : 5 * Real.exp (A / 5) * (n * ℓ ^ (-(1 / 5 : ℝ))) ≤
      (5 * Real.exp (A / 5) + C₀ * Real.exp A + Cm + 13 + CJ) * (n * ℓ ^ (-(1 / 5 : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hA0
    have : 0 ≤ C₀ * Real.exp A := by positivity
    linarith only [this, hCm, hCJ]
  have e2 : (C₀ * Real.exp A + Cm + 13 + CJ) * (n * (E / ℓ)) ≤
      (5 * Real.exp (A / 5) + C₀ * Real.exp A + Cm + 13 + CJ) * (n * (E / ℓ)) := by
    refine mul_le_mul_of_nonneg_right ?_ hB0
    have : 0 ≤ 5 * Real.exp (A / 5) := by positivity
    linarith only [this]
  have e3 : (5 * Real.exp (A / 5) + C₀ * Real.exp A + Cm + 13 + CJ) * n *
      (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) =
      (5 * Real.exp (A / 5) + C₀ * Real.exp A + Cm + 13 + CJ) * (n * ℓ ^ (-(1 / 5 : ℝ))) +
        (5 * Real.exp (A / 5) + C₀ * Real.exp A + Cm + 13 + CJ) * (n * (E / ℓ)) := by ring
  rw [e3]
  linarith only [e1, e2]

/-! ### The partition into cells -/

/-- **Partition by the graph** (source l. 1668): the integral over `Λ^{2N}` is the sum over the
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

/-! ### The sum over the graphs (source l. 1709--1739) -/

/-- **The sum over the nearest-neighbour graphs** (the assembly of the proof of (eq:critical upper),
source l. 1709--1739, for a general integrand). For constants `c₁, C_J, C_m, C₀ ≥ 0` there is `C`
such that: if for `N ≥ 2` and `0 < λ ≤ e⁻²` the integral of `G` over every cell
`Λ^{2N} ∩ {φ₁ = f}` is at most `exp (pairCellExponent c₁ C_J λ Mₙ Mₛ …)`, with
`log Mₙ ≤ log (2πℓ) + C_m E/ℓ`, `0 < Mₛ ≤ C₀ E` and `E ≥ 1 + log ℓ`, then
`∫_{Λ^{2N}} G ≤ exp (2N log N + N (log (2πℓ) - 1) + C N (ℓ^{-1/5} + E/ℓ) + C log (N+1))`.
The number of graphs is bounded by the marked-graph count (`card_critGraphs_le_exp`), and the sum
over the types `(K, m, p₀)` costs `3 log (N+1)`. -/
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
            ENNReal.ofReal (Real.exp (pairCellExponent c₁ CJ lam Mn Ms N (numComponents Z₀)
              (numIsolatedPairs Z₀) (isolatedDipoles Z₀).card))) →
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N, G Z ≤
          ENNReal.ofReal (Real.exp (2 * N * Real.log N
            + N * (Real.log (2 * Real.pi * |Real.log lam|) - 1)
            + C * N * (|Real.log lam| ^ (-(1 / 5 : ℝ)) + E / |Real.log lam|)
            + C * Real.log (N + 1))) := by
  set C₁ := 5 * Real.exp ((65 + 6 * c₁ + CJ) / 5) + C₀ * Real.exp (65 + 6 * c₁ + CJ) + Cm + 13 + CJ
    with hC₁
  refine ⟨max C₁ 63, by positivity, ?_⟩
  intro N hN lam Mn Ms E hlam hlam2 hE hMn hMs hMsE G hcell
  set ℓ := |Real.log lam| with hℓdef
  have hℓ1 : 1 ≤ ℓ := one_le_abs_log hlam (hlam2.trans (Real.exp_le_exp.2 (by norm_num)))
  have hℓ0 : 0 < ℓ := by linarith only [hℓ1]
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN1 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith only [hNpos])
  set Target := 2 * N * Real.log N + N * (Real.log (2 * Real.pi * ℓ) - 1)
    + max C₁ 63 * N * (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) + max C₁ 63 * Real.log (N + 1) with hT
  -- the bound for each type `(K, m, p₀)`
  set T := Finset.range (N + 1) ×ˢ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)) with hTdef
  have hper : ∀ t ∈ T, ((critGraphs N t.1 t.2.1 t.2.2).card : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (pairCellExponent c₁ CJ lam Mn Ms N t.1 t.2.1 t.2.2)) ≤
      ENNReal.ofReal (Real.exp (Target - 3 * Real.log (N + 1))) := by
    rintro ⟨K, m, p₀⟩ -
    dsimp only
    rcases (critGraphs N K m p₀).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.card_empty, Nat.cast_zero, zero_mul]
      exact zero_le
    obtain ⟨hp₀m, hmK, hKN, hr2, hcard⟩ := card_critGraphs_le_exp hN hne
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le).trans ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hp₀mR : (p₀ : ℝ) ≤ m := by exact_mod_cast hp₀m
    have hmKR : (m : ℝ) ≤ K := by exact_mod_cast hmK
    have hKNR : (K : ℝ) ≤ N := by exact_mod_cast hKN
    have hr2R : (K : ℝ) - m ≤ 2 * ((N : ℝ) - K) := by
      have : ((K - m : ℕ) : ℝ) ≤ ((2 * (N - K) : ℕ) : ℝ) := by exact_mod_cast hr2
      push_cast [Nat.cast_sub hmK, Nat.cast_sub hKN] at this
      linarith only [this]
    have key := critical_exponent_le (n := N) (p := p₀) (q := (m : ℝ) - p₀)
      (h := (K : ℝ) - m) (d := (N : ℝ) - K) (ℓ := ℓ) (E := E) (Mn := Mn) (Ms := Ms) hc₁ hCJ hCm
      hC₀ (Nat.cast_nonneg _) (by linarith only [hp₀mR]) (by linarith only [hmKR])
      (by linarith only [hKNR]) (by ring) hNpos hr2R hℓ1 hE hMn hMs hMsE
    have e1 : -((2 * (N : ℝ) - 2 * K) * Real.log (((N : ℝ) - K) / N)) =
        2 * ((N : ℝ) - K) * Real.log (N / ((N : ℝ) - K)) := by
      have := neg_mul_log_div_eq (x := (N : ℝ) - K) (n := N) (by linarith only [hKNR]) hNpos
      linear_combination 2 * this
    have hfin : (2 * N * Real.log N - (2 * N - 2 * K) * Real.log (((N : ℝ) - K) / N)
          - p₀ * Real.log p₀ - ((m : ℝ) - p₀) * Real.log ((m : ℝ) - p₀)
          - ((K : ℝ) - m) * Real.log ((K : ℝ) - m) - N + 60 * Real.log (N + 1)
          + 60 * (N - K) + 60 * (m - p₀)) +
        pairCellExponent c₁ CJ lam Mn Ms N K m p₀ =
        2 * N * Real.log N + 60 * Real.log (N + 1) +
          ((2 * ((N : ℝ) - K) * Real.log (N / ((N : ℝ) - K)) - p₀ * Real.log p₀
              - ((m : ℝ) - p₀) * Real.log ((m : ℝ) - p₀) - ((K : ℝ) - m) * Real.log ((K : ℝ) - m)
              - N + 60 * (((N : ℝ) - K) + ((m : ℝ) - p₀)))
            + (c₁ * (2 * ((K : ℝ) - m) + 2 * ((N : ℝ) - K)) + 36 * N / (Real.pi * ℓ)
              + p₀ * Real.log Mn + ((m : ℝ) - p₀) * Real.log Ms
              + (p₀ + ((m : ℝ) - p₀)) * Real.log N + ((K : ℝ) - m) * Real.log N
              + ((K : ℝ) - m) * Real.log (ℓ + Real.log (N / ((K : ℝ) - m)))
              + ((K : ℝ) - m) * Real.log (2 * Real.pi)
              + ((N : ℝ) - K) * Real.log (N / ((N : ℝ) - K)) + CJ * ((N : ℝ) - K)
              + CJ * N * (Real.log ℓ / ℓ))) := by
      rw [pairCellExponent, ← hℓdef]
      linear_combination e1
    rw [hfin]
    have hC63 : (63 : ℝ) ≤ max C₁ 63 := le_max_right _ _
    have hCC : C₁ ≤ max C₁ 63 := le_max_left _ _
    have hE1 : 1 ≤ E := by linarith only [hE, hlogℓ]
    have hpos : 0 ≤ (N : ℝ) * (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) := by positivity
    have h1 : C₁ * N * (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) ≤
        max C₁ 63 * N * (ℓ ^ (-(1 / 5 : ℝ)) + E / ℓ) := by
      have := mul_le_mul_of_nonneg_right hCC hpos
      linarith only [this]
    have h2 : 63 * Real.log ((N : ℝ) + 1) ≤ max C₁ 63 * Real.log (N + 1) :=
      mul_le_mul_of_nonneg_right hC63 hlogN1
    rw [hT]
    linarith only [key, h1, h2]
  -- the partition into cells and the sum over the types
  have hcell' : ∀ f : Fin N ⊕ Fin N → Fin N ⊕ Fin N,
      ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f}, G Z ≤
        ∑ t ∈ T, (if f ∈ critGraphs N t.1 t.2.1 t.2.2 then
          ENNReal.ofReal (Real.exp (pairCellExponent c₁ CJ lam Mn Ms N t.1 t.2.1 t.2.2))
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
          ENNReal.ofReal (Real.exp (pairCellExponent c₁ CJ lam Mn Ms N t.1 t.2.1 t.2.2))
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
            ENNReal.ofReal (Real.exp (pairCellExponent c₁ CJ lam Mn Ms N t.1 t.2.1 t.2.2))
            else 0) := Finset.sum_le_sum fun f _ => hcell' f
    _ = ∑ t ∈ T, ((critGraphs N t.1 t.2.1 t.2.2).card : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (pairCellExponent c₁ CJ lam Mn Ms N t.1 t.2.1 t.2.2)) := by
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
