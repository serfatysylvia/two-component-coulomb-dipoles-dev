/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.UpperBound.EnergySplit
public import TwoComponentCoulomb.UpperBound.MarkedGraphCount
public import TwoComponentCoulomb.UpperBound.NearestNeighborModelCritical
public import TwoComponentCoulomb.UpperBound.UpperOptimization
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.UpperBound.IsolatedReduction

/-!
# Proposition 3.10, Steps 2--3: the bound for one marked graph (`β > 2`)

Source: proof of Proposition 3.10, l. 1513--1620: (eq:F(1)), (eq:F(2)),
(eq:2cases p) and (eq:quadra x3) for one marked graph `γ ∈ D_{2N,K,p,p₀}`.

The file is organised so that the counting and the optimization are independent of the integrand
(they are reused with tilted integrands): an energy-specific argument only has to establish the
per-cell bound `TwoComponentCoulomb.UpperCellBound.CellBoundRate` for its cell integrals.

## Real-variable part

* `TwoComponentCoulomb.UpperCellBound.mul_log_shift_le` (l. 1553--1556):
  `m log m - (p₀ + m - p) log (p₀ + m - p) ≥ p log p - p₀ log p₀` for `p₀ ≤ p ≤ m`
  (with `0 log 0 = 0`), by the convexity of `x ↦ x log x`.
* The error rates `λ^{β-2}` (`2 < β < 4`), `λ² ℓ²` (`β = 4`), `λ² ℓ` (`β > 4`) of
  Proposition 3.9 are at most `ω_λ` for `0 < λ ≤ e⁻¹` (l. 1564--1566): this is the field
  `isolated_le` of the rate hypotheses `UpperRateHyp` (`UpperBound/UpperOptimization.lean`).
* `TwoComponentCoulomb.UpperCellBound.cell_exponent_le` (l. 1575--1594): (eq:logD), the entropy
  comparison, the main terms of (eq:F(1)) and (eq:F(2)), the tree terms and the entropy bound
  combine into `2N log N + N((2-β) log λ + log 𝒵_β - 1) + N χ_β(δ) + 60 log (N + 1)`.

## Generic per-graph layer

* `TwoComponentCoulomb.UpperCellBound.entropy_mul_le_main_rate`,
  `TwoComponentCoulomb.UpperCellBound.entropy_mul_le_crude` ((eq:F(1)), l. 1553--1565, 1595): a
  bound of the shape of Proposition 3.9 for an abstract `I`-block integral at the pair counts
  `(m, p₀ + m - p)` gives the bound with the entropy of (eq:logD), with an extra exponent `X`.
* `TwoComponentCoulomb.UpperCellBound.exists_lintegral_nnEnergy_le` ((eq:F(2)), l. 1566--1573):
  Lemma 3.5 on the block `Iᶜ`, and on all points.
* `TwoComponentCoulomb.UpperCellBound.CellBoundRate`: the per-cell bound (the right side of
  (eq:2cases p) before the count), main form or crude form (`p < N/2`), with an extra exponent.
* `TwoComponentCoulomb.UpperCellBound.exists_card_mul_le_of_cellBound_rate` (l. 1580--1620): for
  any cell integral satisfying `CellBoundRate`, `|D_{2N,K,p,p₀}| · J ≤ exp (2N log N
  + N((2-β) log λ + log 𝒵_β - 1) - c' (N - p₀)²/N + C' N ω(λ) + C' log (N + 1) + X)`
  (eq:quadra x3).

`entropy_mul_le_main_rate`, `CellBoundRate` and `exists_card_mul_le_of_cellBound_rate` are stated
for a rate function `ω` satisfying `TwoComponentCoulomb.UpperRateHyp` in place of `ω_λ`; they are
instantiated at `errorRate` in `UpperBound/UpperRate.lean`.

## Separation of variables with events (l. 1542--1551, used in Step 4)

* `TwoComponentCoulomb.UpperCellBound.lintegral_markedCell_le_mul_event`: (gred3) with an event on
  the block `I` and an arbitrary first-block energy; `lintegral_markedCell_le_event`: the case
  `Iᶜ = ∅`.
* `TwoComponentCoulomb.UpperCellBound.lintegral_pair_long_le`: the block of a single isolated pair
  required to be longer than `R` (the case `m = 1`).
-/

@[expose] public section

namespace TwoComponentCoulomb

namespace UpperCellBound

/-! ### The entropy comparison (source l. 1553--1556) -/

/-- Convexity of `x ↦ x log x`: the increment over an interval of length `s` grows with the
position, `φ(a) - φ(a - s) ≤ φ(b) - φ(b - s)` for `s ≤ a ≤ b`. -/
theorem mul_log_sub_mul_log_le {a b s : ℝ} (hs : 0 ≤ s) (has : s ≤ a) (hab : a ≤ b) :
    a * Real.log a - (a - s) * Real.log (a - s) ≤ b * Real.log b - (b - s) * Real.log (b - s) := by
  have hcv := Real.convexOn_mul_log
  rcases hs.eq_or_lt with rfl | hs'
  · simp
  rcases hab.eq_or_lt with rfl | hab'
  · exact le_rfl
  have hm : ∀ x : ℝ, 0 ≤ x → x ∈ Set.Ici (0 : ℝ) := fun x hx => hx
  have h1 := hcv.secant_mono (a := a - s) (x := a) (y := b) (hm _ (by linarith)) (hm _ (by linarith))
    (hm _ (by linarith)) (by linarith) (by linarith) hab
  have h2 := hcv.secant_mono (a := b) (x := a - s) (y := b - s) (hm _ (by linarith))
    (hm _ (by linarith)) (hm _ (by linarith)) (by linarith) (by linarith) (by linarith)
  have e1 : a - (a - s) = s := by ring
  have e2 : b - s - b = -s := by ring
  have e3 : ((a - s) * Real.log (a - s) - b * Real.log b) / (a - s - b) =
      (b * Real.log b - (a - s) * Real.log (a - s)) / (b - (a - s)) := by
    rw [← neg_div_neg_eq]
    ring_nf
  rw [e1] at h1
  rw [e2, e3] at h2
  have h3 : (a * Real.log a - (a - s) * Real.log (a - s)) / s ≤
      (b * Real.log b - (b - s) * Real.log (b - s)) / s := by
    refine h1.trans (h2.trans (le_of_eq ?_))
    rw [div_neg, ← neg_div]
    ring_nf
  exact (div_le_div_iff_of_pos_right hs').1 h3

/-- **Entropy comparison** (source l. 1553--1556): for `p₀ ≤ p ≤ m`,
`m log m - (p₀ + m - p) log (p₀ + m - p) ≥ p log p - p₀ log p₀`, with `0 log 0 = 0`. -/
theorem mul_log_shift_le {m p p₀ : ℝ} (hp₀ : 0 ≤ p₀) (hp : p₀ ≤ p) (hm : p ≤ m) :
    p * Real.log p - p₀ * Real.log p₀ ≤
      m * Real.log m - (p₀ + m - p) * Real.log (p₀ + m - p) := by
  have h := mul_log_sub_mul_log_le (a := p) (b := m) (s := p - p₀) (by linarith) (by linarith) hm
  have e1 : p - (p - p₀) = p₀ := by ring
  have e2 : m - (p - p₀) = p₀ + m - p := by ring
  rw [e1, e2] at h
  exact h

/-! ### The exponent of one marked graph (source l. 1575--1594) -/

/-- `x log (x / n) = x log x - x log n` for `x ≥ 0`, `n > 0` (with `0 log 0 = 0`). -/
theorem mul_log_div_eq {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) :
    x * Real.log (x / n) = x * Real.log x - x * Real.log n := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  · rw [Real.log_div hx'.ne' hn.ne']
    ring

/-- For `ℓ ≥ 1` and `0 < δ ≤ 1`: `log (ℓ + log (1/δ)) ≤ log ℓ + log (1/δ)`, from
`ℓ + log (1/δ) ≤ ℓ/δ` (source l. 1595). -/
theorem log_add_log_inv_le {ℓ δ : ℝ} (hℓ : 1 ≤ ℓ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (ℓ + Real.log (1 / δ)) ≤ Real.log ℓ + Real.log (1 / δ) := by
  have hinv : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hlog0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg hinv
  have hlog1 : Real.log (1 / δ) ≤ 1 / δ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hle : ℓ + Real.log (1 / δ) ≤ ℓ * (1 / δ) := by
    linarith only [hlog1, mul_nonneg (sub_nonneg.2 hℓ) (sub_nonneg.2 hinv)]
  rw [← Real.log_mul (by linarith) (by positivity)]
  exact Real.log_le_log (by linarith) hle

/-- **The exponent of one marked graph** (source l. 1575--1594, the core of (eq:2cases p)): for
`β > 2`, `N ≥ 1`, `p₀ ≤ p ≤ K ≤ N` with `K - p ≤ (M₀ + 2)(N - K)` (eq:K-p) and `0 < λ ≤ e⁻¹`, the sum
of

* the logarithmic count (eq:logD) with `C₀ = 60`,
* minus the entropy `p log p - p₀ log p₀ - (p - p₀) log (p - p₀) + 60 (p - p₀)` (the entropy of
  `f(p₀)` of Proposition 3.9 after the comparison of l. 1553--1556),
* the main terms `K (log N + (2 - β) log λ + log 𝒵_β)` of (eq:F(1)) and (eq:F(2)),
* the tree terms `(2N - 2K) (…)` of (eq:F(2)), and
* any error `A (N - K)`,

is at most `2N log N + N((2-β) log λ + log 𝒵_β - 1) + N χ_β(δ) + 60 log (N + 1)`, with
`δ = (N - K)/N` and the constant `C_β = 2(M₀ + 2) + 61 + |A| + |log 𝒵_β|` in `χ_β` (`defchi`). -/
theorem cell_exponent_le {β : ℝ} (hβ : 2 < β) (A : ℝ) {N K p p₀ : ℕ} {lam : ℝ}
    (hN : 1 ≤ N) (hpK : p ≤ K) (hKN : K ≤ N)
    (hKp : (K : ℝ) - p ≤ (M0 + 2) * ((N : ℝ) - K)) (hlam : 0 < lam)
    (hlam1 : lam ≤ Real.exp (-1)) :
    (2 * N * Real.log N - (2 * N - 2 * K) * Real.log (((N : ℝ) - K) / N)
        - p₀ * Real.log p₀ - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀)
        - ((K : ℝ) - p) * Real.log ((K : ℝ) - p) - N + 60 * Real.log (N + 1)
        + 60 * (N - K) + 60 * (p - p₀))
      - (p * Real.log p - p₀ * Real.log p₀ - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀)
          + 60 * ((p : ℝ) - p₀))
      + K * (Real.log N + (2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le))
      + (2 * N - 2 * K) * ((if β < 4 then (1 - β / 4) * Real.log (N / ((N : ℝ) - K)) else 0) +
          (if β = 4 then Real.log (|Real.log lam| + Real.log (N / ((N : ℝ) - K))) else 0) +
          (if 4 < β then (2 - β / 2) * Real.log lam else 0))
      + A * ((N : ℝ) - K) ≤
    2 * N * Real.log N + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1)
      + N * chiBeta β hβ lam (2 * (M0 + 2) + 1 + 60 + |A| + |Real.log (dipoleConstant β hβ.le)|)
          (((N : ℝ) - K) / N)
      + 60 * Real.log (N + 1) := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hpK' : (p : ℝ) ≤ K := by exact_mod_cast hpK
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hlt1 : lam < 1 := lt_of_le_of_lt hlam1 (Real.exp_lt_one_iff.2 (by norm_num))
  set n : ℝ := (N : ℝ) with hn
  set δ : ℝ := (n - K) / n with hδ
  set ℓ : ℝ := |Real.log lam| with hℓdef
  set L : ℝ := Real.log (dipoleConstant β hβ.le) with hL
  set tree : ℝ := (if β < 4 then (1 - β / 4) * Real.log (n / (n - K)) else 0) +
          (if β = 4 then Real.log (ℓ + Real.log (n / (n - K))) else 0) +
          (if 4 < β then (2 - β / 2) * Real.log lam else 0) with htree
  set Cχ : ℝ := 2 * (M0 + 2) + 1 + 60 + |A| + |L| with hCχ
  have hlogl : Real.log lam = -ℓ := by rw [hℓdef, abs_log_eq hlam hlt1]; ring
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓdef, abs_log_eq hlam hlt1]
    have := (Real.log_le_iff_le_exp hlam).2 hlam1
    linarith
  have hnδ : n - K = n * δ := by rw [hδ]; field_simp
  have hδ0 : 0 ≤ δ := div_nonneg (by linarith) hn0.le
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one hn0]; linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hnδ0 : 0 ≤ n * δ := mul_nonneg hn0.le hδ0
  have hinv : n / (n - K) = 1 / δ := by rw [hδ, one_div_div]
  -- the count term
  have e1 : (2 * n - 2 * K) * Real.log ((n - K) / n) = -2 * (n * (δ * Real.log (1 / δ))) := by
    rw [← hδ, one_div, Real.log_inv, show 2 * n - 2 * K = 2 * (n - K) by ring, hnδ]
    ring
  -- the entropy
  have hent := entropy_le hN hpK hKN hKp
  rw [← hn, ← hδ] at hent
  have e2 : (K : ℝ) * Real.log n - p * Real.log p - ((K : ℝ) - p) * Real.log ((K : ℝ) - p) =
      n * (-((p : ℝ) / n * Real.log ((p : ℝ) / n)) -
        ((K : ℝ) - p) / n * Real.log (((K : ℝ) - p) / n)) := by
    have h1 := mul_log_div_eq hp0 hn0
    have h2 := mul_log_div_eq (x := (K : ℝ) - p) (by linarith) hn0
    have h3 : n * (-((p : ℝ) / n * Real.log ((p : ℝ) / n)) -
        ((K : ℝ) - p) / n * Real.log (((K : ℝ) - p) / n)) =
        -((p : ℝ) * Real.log ((p : ℝ) / n)) - ((K : ℝ) - p) * Real.log (((K : ℝ) - p) / n) := by
      field_simp
    rw [h3, h1, h2]
    ring
  have hent' : (K : ℝ) * Real.log n - p * Real.log p - ((K : ℝ) - p) * Real.log ((K : ℝ) - p) ≤
      (M0 + 2) * (n * (δ * Real.log (1 / δ))) + (2 * (M0 + 2) + 1) * (n * δ) := by
    rw [e2]
    have := mul_le_mul_of_nonneg_left hent hn0.le
    have e : n * ((M0 + 2) * δ * Real.log (1 / δ) + (2 * (M0 + 2) + 1) * δ) =
        (M0 + 2) * (n * (δ * Real.log (1 / δ))) + (2 * (M0 + 2) + 1) * (n * δ) := by ring
    linarith
  -- the main terms
  have e3 : (K : ℝ) * ((2 - β) * Real.log lam + L) =
      n * ((2 - β) * Real.log lam + L) - (β - 2) * (n * (δ * ℓ)) - L * (n * δ) := by
    have hK : (K : ℝ) = n - n * δ := by linarith
    rw [hK, hlogl]
    ring
  have hLabs : -L * (n * δ) ≤ |L| * (n * δ) :=
    mul_le_mul_of_nonneg_right (by linarith [neg_abs_le L]) hnδ0
  have hAabs : A * (n * δ) ≤ |A| * (n * δ) := mul_le_mul_of_nonneg_right (le_abs_self A) hnδ0
  have hlog_nn : 0 ≤ Real.log (1 / δ) := by
    rcases hδ0.eq_or_lt with h | h
    · rw [← h]; simp
    · exact Real.log_nonneg (by rw [le_div_iff₀ h]; linarith)
  -- the tree terms and `χ_β`, case by case
  rcases lt_trichotomy β 4 with h4 | rfl | h4
  · have ht : (2 * n - 2 * K) * tree = (2 - β / 2) * (n * (δ * Real.log (1 / δ))) := by
      rw [htree, ite_eq_left h4, ite_eq_right h4.ne, ite_eq_right (not_lt.2 h4.le), hinv,
        show 2 * n - 2 * K = 2 * (n - K) by ring, hnδ]
      ring
    have hchi : n * chiBeta β hβ lam Cχ δ = -(β - 2) * (n * (δ * ℓ)) +
        (M0 + 2 + 4 - β / 2) * (n * (δ * Real.log (1 / δ))) + Cχ * (n * δ) := by
      rw [chiBeta_of_lt_four h4]
      ring
    rw [hchi]
    have e4 : (K : ℝ) * (Real.log n + (2 - β) * Real.log lam + L) =
        K * Real.log n + K * ((2 - β) * Real.log lam + L) := by ring
    rw [e4, e3, e1, ht, hnδ]
    linarith
  · have ht : (2 * n - 2 * K) * tree ≤ 2 * (n * (δ * Real.log ℓ)) +
        2 * (n * (δ * Real.log (1 / δ))) := by
      rw [htree, ite_eq_right (lt_irrefl 4), ite_eq_left rfl, ite_eq_right (lt_irrefl 4), hinv,
        show 2 * n - 2 * K = 2 * (n * δ) by rw [← hnδ]; ring]
      rcases hδ0.eq_or_lt with h | h
      · rw [← h]; simp
      · have h1 := log_add_log_inv_le hℓ1 h hδ1
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (n * δ))
        simp only [zero_add, add_zero]
        linarith
    have hchi : n * chiBeta 4 hβ lam Cχ δ = -2 * (n * (δ * ℓ)) + 2 * (n * (δ * Real.log ℓ)) +
        (M0 + 2 + 4) * (n * (δ * Real.log (1 / δ))) + Cχ * (n * δ) := by
      rw [chiBeta_of_eq_four rfl]
      ring
    rw [hchi]
    have e4 : (K : ℝ) * (Real.log n + (2 - 4) * Real.log lam + L) =
        K * Real.log n + K * ((2 - 4) * Real.log lam + L) := by ring
    rw [e4, e3, e1, hnδ]
    linarith
  · have ht : (2 * n - 2 * K) * tree = (β - 4) * (n * (δ * ℓ)) := by
      rw [htree, ite_eq_right (not_lt.2 h4.le), ite_eq_right h4.ne', ite_eq_left h4, hlogl,
        show 2 * n - 2 * K = 2 * (n - K) by ring, hnδ]
      ring
    have hchi : n * chiBeta β hβ lam Cχ δ = -2 * (n * (δ * ℓ)) +
        (M0 + 2 + 2) * (n * (δ * Real.log (1 / δ))) + Cχ * (n * δ) := by
      rw [chiBeta_of_four_lt h4]
      ring
    rw [hchi]
    have e4 : (K : ℝ) * (Real.log n + (2 - β) * Real.log lam + L) =
        K * Real.log n + K * ((2 - β) * Real.log lam + L) := by ring
    rw [e4, e3, e1, ht, hnδ]
    linarith

/-! ### Exponential bookkeeping in `ℝ≥0∞` -/

section Exp

open scoped ENNReal

theorem ofReal_exp_mul_ofReal_exp (x y : ℝ) :
    ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (Real.exp y) = ENNReal.ofReal (Real.exp (x + y)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]

/-- From `e^e Y ≤ e^c` to `Y ≤ e^{c - e}`. -/
theorem le_ofReal_exp_sub {Y : ℝ≥0∞} {e c : ℝ}
    (h : ENNReal.ofReal (Real.exp e) * Y ≤ ENNReal.ofReal (Real.exp c)) :
    Y ≤ ENNReal.ofReal (Real.exp (c - e)) := by
  have h1 : ENNReal.ofReal (Real.exp (-e)) * ENNReal.ofReal (Real.exp e) = 1 := by
    rw [ofReal_exp_mul_ofReal_exp, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]
  calc Y = ENNReal.ofReal (Real.exp (-e)) * (ENNReal.ofReal (Real.exp e) * Y) := by
        rw [← mul_assoc, h1, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-e)) * ENNReal.ofReal (Real.exp c) := mul_le_mul_right h _
    _ = ENNReal.ofReal (Real.exp (c - e)) := by
        rw [ofReal_exp_mul_ofReal_exp]
        ring_nf

/-- Combination of the four bounds of one marked graph: `|D| ≤ e^a`, `cell ≤ e^b Y₁ Y₂`,
`e^e Y₁ ≤ e^{c₁}`, `Y₂ ≤ e^{c₂}` give `|D| · cell ≤ e^{a + b - e + c₁ + c₂}`. -/
theorem mul_le_ofReal_exp_of_le {D X Y₁ Y₂ : ℝ≥0∞} {a b e c₁ c₂ t : ℝ}
    (hD : D ≤ ENNReal.ofReal (Real.exp a)) (hX : X ≤ ENNReal.ofReal (Real.exp b) * (Y₁ * Y₂))
    (h₁ : ENNReal.ofReal (Real.exp e) * Y₁ ≤ ENNReal.ofReal (Real.exp c₁))
    (h₂ : Y₂ ≤ ENNReal.ofReal (Real.exp c₂)) (ht : a + b - e + c₁ + c₂ ≤ t) :
    D * X ≤ ENNReal.ofReal (Real.exp t) := by
  have h₁' := le_ofReal_exp_sub h₁
  calc D * X ≤ ENNReal.ofReal (Real.exp a) * (ENNReal.ofReal (Real.exp b) *
        (ENNReal.ofReal (Real.exp (c₁ - e)) * ENNReal.ofReal (Real.exp c₂))) :=
        mul_le_mul' hD (hX.trans (by gcongr))
    _ = ENNReal.ofReal (Real.exp (a + (b + ((c₁ - e) + c₂)))) := by
        rw [ofReal_exp_mul_ofReal_exp, ofReal_exp_mul_ofReal_exp, ofReal_exp_mul_ofReal_exp]
    _ ≤ ENNReal.ofReal (Real.exp t) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))

/-- The bound of one cell: `cell ≤ e^b Y₁ Y₂`, `e^e Y₁ ≤ e^{c₁}`, `Y₂ ≤ e^{c₂}` give
`cell ≤ e^{b - e + c₁ + c₂}`. -/
theorem le_ofReal_exp_of_le_mul {X Y₁ Y₂ : ℝ≥0∞} {b e c₁ c₂ t : ℝ}
    (hX : X ≤ ENNReal.ofReal (Real.exp b) * (Y₁ * Y₂))
    (h₁ : ENNReal.ofReal (Real.exp e) * Y₁ ≤ ENNReal.ofReal (Real.exp c₁))
    (h₂ : Y₂ ≤ ENNReal.ofReal (Real.exp c₂)) (ht : b - e + c₁ + c₂ ≤ t) :
    X ≤ ENNReal.ofReal (Real.exp t) := by
  have h := mul_le_ofReal_exp_of_le (D := 1) (a := 0) (by simp) hX h₁ h₂
    (by linarith : 0 + b - e + c₁ + c₂ ≤ t)
  simpa using h

/-- The bound of one cell with a single block: `cell ≤ e^b Y`, `e^e Y ≤ e^{c}` give
`cell ≤ e^{b - e + c}`. -/
theorem le_ofReal_exp_of_le_mul_one {X Y : ℝ≥0∞} {b e c t : ℝ}
    (hX : X ≤ ENNReal.ofReal (Real.exp b) * Y)
    (h₁ : ENNReal.ofReal (Real.exp e) * Y ≤ ENNReal.ofReal (Real.exp c)) (ht : b - e + c ≤ t) :
    X ≤ ENNReal.ofReal (Real.exp t) :=
  le_ofReal_exp_of_le_mul (Y₂ := 1) (c₂ := 0) (by simpa using hX) h₁ (by simp) (by linarith)

end Exp

/-! ### Reference sets and the integrand of Lemma 3.5 -/

section RefSet

/-- For a self-map `f` without fixed points, the 2-cycle vertices are twice as many as the
reference vertices: `|{i | f (f i) = i}| = 2 |gpRefSet key f|`. -/
theorem two_mul_card_gpRefSet_eq {ι : Type*} [Fintype ι] {key : ι ↪ ℕ} {f : ι → ι}
    (hf0 : ∀ i, f i ≠ i) [Fintype {i // i ∈ gpRefSet key f}] [Fintype {i // f (f i) = i}] :
    2 * Fintype.card {i // i ∈ gpRefSet key f} = Fintype.card {i // f (f i) = i} := by
  classical
  have hcyc := card_cycIdx (key := key) hf0
  have e1 : Fintype.card (CycIdx key f) =
      (Finset.univ.filter fun i => i ∉ gpRefSet key f ∧ f (f i) = i).card := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∉ gpRefSet key f)
      fun i => f (f i) = i)
  have e2 : Fintype.card {i // i ∈ gpRefSet key f} =
      (Finset.univ.filter fun i => i ∈ gpRefSet key f).card :=
    Fintype.card_of_subtype _ fun i => by simp
  have e2' : Fintype.card (CycIdx key f) =
      (Finset.univ.filter fun i => i ∈ gpRefSet key f).card := by
    rw [hcyc]
    convert e2
  have e5 : Fintype.card {i // f (f i) = i} = (Finset.univ.filter fun i => f (f i) = i).card :=
    Fintype.card_of_subtype _ fun i => by simp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun i => f (f i) = i) (fun i => i ∈ gpRefSet key f)
  have e3 : (Finset.univ.filter fun i => f (f i) = i).filter (fun i => i ∈ gpRefSet key f) =
      Finset.univ.filter fun i => i ∈ gpRefSet key f := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  have e4 : (Finset.univ.filter fun i => f (f i) = i).filter (fun i => i ∉ gpRefSet key f) =
      Finset.univ.filter fun i => i ∉ gpRefSet key f ∧ f (f i) = i := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [e3, e4] at hsplit
  omega

theorem exp_neg_mul_nnEnergy {ι : Type*} [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (β lam : ℝ)
    (z : ι → ℂ) :
    Real.exp (-β * nnEnergy key lam z) =
      Real.exp ((β / 2) * ∑ i, smearedKernel lam (z i - z (nnMap key z i))) := by
  unfold nnEnergy
  ring_nf

end RefSet

/-! ### (eq:F(1)) (source l. 1553--1565), for an abstract `I`-block integral -/

section F1

open scoped ENNReal

/-- **(eq:F(1)), main form** (source l. 1553--1565), for an abstract `I`-block integral `Y`: a bound
of the shape of (eq:n neutral conv) at the pair counts `(m, p₀')`, `p₀' = p₀ + m - p` (with an
error rate `r ≤ ω_λ` and an extra exponent `X`), gives, by the entropy comparison of l. 1553--1556
and `(p-p₀)²/m ≥ (p-p₀)²/N`, the bound with the entropy
`p log p - p₀ log p₀ - (p - p₀) log (p - p₀) + 60 (p - p₀)` of (eq:logD):
`e^{entropy} Y ≤ exp (m (log N + (2-β) log λ + log 𝒵_β) - c (p-p₀)²/N + C_b N ω_λ
  + C_b log (N + 1) + X)`.

Here `ω` is any function: no property of `ω` is used, only `r ≤ ω λ` (l. 1559--1566). -/
theorem entropy_mul_le_main_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) {c Cb r X : ℝ} (hc : 0 ≤ c)
    (hCb : 0 ≤ Cb) {N m p p₀ p₀' : ℕ} (hm : 0 < m) (hmN : m ≤ N) (hp₀ : p₀ ≤ p) (hpm : p ≤ m)
    (hp₀' : p₀' + p = p₀ + m) {lam : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ ω lam)
    {Y : ℝ≥0∞}
    (hY : ENNReal.ofReal (Real.exp (m * Real.log m - p₀' * Real.log p₀'
        - ((m : ℝ) - p₀') * Real.log ((m : ℝ) - p₀') + 60 * ((m : ℝ) - p₀'))) * Y ≤
      ENNReal.ofReal (Real.exp (m * (Real.log N + (2 - β) * Real.log lam
        + Real.log (dipoleConstant β hβ.le)) - c * m * (((m : ℝ) - p₀') / m) ^ 2
        + Cb * m * r + Cb * Real.log (N + 1) + X))) :
    ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
        - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + 60 * ((p : ℝ) - p₀))) * Y ≤
      ENNReal.ofReal (Real.exp (m * (Real.log N + (2 - β) * Real.log lam
        + Real.log (dipoleConstant β hβ.le)) - c * ((p : ℝ) - p₀) ^ 2 / N
        + Cb * N * ω lam + Cb * Real.log (N + 1) + X)) := by
  have hcast : (p₀' : ℝ) = p₀ + m - p := by
    have : ((p₀' + p : ℕ) : ℝ) = ((p₀ + m : ℕ) : ℝ) := by rw [hp₀']
    push_cast at this
    linarith
  have hq : (m : ℝ) - p₀' = (p : ℝ) - p₀ := by rw [hcast]; ring
  rw [hq, hcast] at hY
  have hp₀r : (p₀ : ℝ) ≤ p := by exact_mod_cast hp₀
  have hpm' : (p : ℝ) ≤ m := by exact_mod_cast hpm
  have hshift := mul_log_shift_le (Nat.cast_nonneg p₀) hp₀r hpm'
  have hE : ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
      - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + 60 * ((p : ℝ) - p₀))) ≤
      ENNReal.ofReal (Real.exp (m * Real.log m - (p₀ + m - p) * Real.log (p₀ + m - p)
      - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + 60 * ((p : ℝ) - p₀))) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
  refine (mul_le_mul_left hE _).trans (hY.trans (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.2 ?_)))
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hm0 hmN'
  have hgain : c * ((p : ℝ) - p₀) ^ 2 / N ≤ c * m * (((p : ℝ) - p₀) / m) ^ 2 := by
    have e2 : c * m * (((p : ℝ) - p₀) / m) ^ 2 = c * ((p : ℝ) - p₀) ^ 2 / m := by
      field_simp
    rw [e2]
    exact div_le_div_of_nonneg_left (by positivity) hm0 hmN'
  have herr : Cb * m * r ≤ Cb * N * ω lam := by
    have := mul_le_mul hmN' hr hr0 hN0.le
    have := mul_le_mul_of_nonneg_left this hCb
    linarith
  linarith

/-- **(eq:F(1)), crude form** (source l. 1595): a bound of any shape `B` at the pair counts
`(m, p₀')`, `p₀' = p₀ + m - p`, with the entropy of Proposition 3.9, gives the same bound with the
smaller entropy `p log p - p₀ log p₀ - (p - p₀) log (p - p₀) + 60 (p - p₀)` of (eq:logD). -/
theorem entropy_mul_le_crude {m p p₀ p₀' : ℕ} (hp₀ : p₀ ≤ p) (hpm : p ≤ m)
    (hp₀' : p₀' + p = p₀ + m) {B : ℝ} {Y : ℝ≥0∞}
    (hY : ENNReal.ofReal (Real.exp (m * Real.log m - p₀' * Real.log p₀'
        - ((m : ℝ) - p₀') * Real.log ((m : ℝ) - p₀') + 60 * ((m : ℝ) - p₀'))) * Y ≤
      ENNReal.ofReal (Real.exp B)) :
    ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
        - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + 60 * ((p : ℝ) - p₀))) * Y ≤
      ENNReal.ofReal (Real.exp B) := by
  have hcast : (p₀' : ℝ) = p₀ + m - p := by
    have : ((p₀' + p : ℕ) : ℝ) = ((p₀ + m : ℕ) : ℝ) := by rw [hp₀']
    push_cast at this
    linarith
  have hq : (m : ℝ) - p₀' = (p : ℝ) - p₀ := by rw [hcast]; ring
  rw [hq, hcast] at hY
  have hp₀r : (p₀ : ℝ) ≤ p := by exact_mod_cast hp₀
  have hpm' : (p : ℝ) ≤ m := by exact_mod_cast hpm
  have hshift := mul_log_shift_le (Nat.cast_nonneg p₀) hp₀r hpm'
  have hE : ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
      - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + 60 * ((p : ℝ) - p₀))) ≤
      ENNReal.ofReal (Real.exp (m * Real.log m - (p₀ + m - p) * Real.log (p₀ + m - p)
      - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + 60 * ((p : ℝ) - p₀))) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
  exact (mul_le_mul_left hE _).trans hY

end F1

/-! ### (eq:F(2)) (source l. 1566--1573) and Lemma 3.5 on the whole configuration -/

section F2

open scoped ENNReal

variable {N : ℕ}

/-- **(eq:F(2))** (source l. 1566--1573) and Lemma 3.5 on all `2N` points: for `β > 2` there is
`C₄`, depending only on `β`, such that for every configuration `Z₀` with nearest-neighbour map
`φ`, `K` components and `m` isolated pairs, and `0 < λ ≤ e⁻¹`,

* the integral of `e^{-β F⁽²⁾}` over the cell of the restriction `γ²` of `φ` to `Iᶜ`
  (`2(N - m)` points, `K - m` components) is at most
  `exp ((K - m)(log N + (2-β) log λ + log 𝒵_β) + (2N - 2K) τ_β + C₄ (N - K))`;
* the integral of `e^{-β F^nn}` over the cell `{γ_{2N} = φ}` is at most
  `exp (K (log N + (2-β) log λ + log 𝒵_β) + (2N - 2K) τ_β + C₄ (N - K))`,

where `τ_β = (1 - β/4) log (N/(N-K)) 1_{β<4} + log (ℓ + log (N/(N-K))) 1_{β=4} +
(2 - β/2) log λ 1_{β>4}`. -/
theorem exists_lintegral_nnEnergy_le {β : ℝ} (hβ : 2 < β) :
    ∃ C₄ : ℝ, ∀ (N : ℕ) (Z₀ : Fin N ⊕ Fin N → ℂ) (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N),
      0 < N → nearestNeighbor Z₀ = φ → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      (∀ [Nontrivial {i // i ∉ pairVerts φ}],
        ∫⁻ y in (Set.univ.pi fun _ : {i // i ∉ pairVerts φ} => box N) ∩
            {y | nnMap (subtypeKey (· ∉ pairVerts φ) (sumKey N)) y = complRestrict φ},
            ENNReal.ofReal (Real.exp (-β *
              nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam y)) ≤
          ENNReal.ofReal (Real.exp (((numComponents Z₀ : ℝ) - numIsolatedPairs Z₀) *
            (Real.log N + (2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le)) +
            (2 * N - 2 * numComponents Z₀) *
              ((if β < 4 then (1 - β / 4) * Real.log (N / ((N : ℝ) - numComponents Z₀)) else 0) +
              (if β = 4 then Real.log (|Real.log lam| + Real.log (N / ((N : ℝ) - numComponents Z₀)))
                else 0) +
              (if 4 < β then (2 - β / 2) * Real.log lam else 0)) +
            C₄ * ((N : ℝ) - numComponents Z₀)))) ∧
      (∀ [Nontrivial (Fin N ⊕ Fin N)],
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nnMap (sumKey N) Z = φ},
            ENNReal.ofReal (Real.exp (-β * nnEnergy (sumKey N) lam Z)) ≤
          ENNReal.ofReal (Real.exp ((numComponents Z₀ : ℝ) *
            (Real.log N + (2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le)) +
            (2 * N - 2 * numComponents Z₀) *
              ((if β < 4 then (1 - β / 4) * Real.log (N / ((N : ℝ) - numComponents Z₀)) else 0) +
              (if β = 4 then Real.log (|Real.log lam| + Real.log (N / ((N : ℝ) - numComponents Z₀)))
                else 0) +
              (if 4 < β then (2 - β / 2) * Real.log lam else 0)) +
            C₄ * ((N : ℝ) - numComponents Z₀)))) := by
  obtain ⟨C₄, h34⟩ := lintegral_cell_le_of_two_lt.{0} hβ
  refine ⟨C₄, fun N Z₀ φ hN hφ lam hlam hlam1 => ⟨fun {_} => ?_, fun {_} => ?_⟩⟩
  · set K := numComponents Z₀ with hK
    set m := numIsolatedPairs Z₀ with hm
    have hmK : m ≤ K := numIsolatedPairs_le_numComponents Z₀
    have hKN : K ≤ N := numComponents_le Z₀
    have hcard : Fintype.card {i // i ∉ pairVerts φ} = 2 * (N - m) :=
      card_compl_pairVerts_subtype hφ
    have hR : Fintype.card {i // i ∈ gpRefSet (subtypeKey (· ∉ pairVerts φ) (sumKey N))
        (complRestrict φ)} = K - m := by
      have h1 := two_mul_card_gpRefSet_eq (key := subtypeKey (· ∉ pairVerts φ) (sumKey N))
        (complRestrict_ne_of_nearestNeighbor hφ)
      have h2 := card_cycle_complRestrict hφ
      rw [h2] at h1
      omega
    have h := h34 {i // i ∉ pairVerts φ} (subtypeKey (· ∉ pairVerts φ) (sumKey N)) N (N - m)
      (K - m) (complRestrict φ) hN (Nat.sub_le N m) hcard hR lam hlam hlam1
    simp_rw [exp_neg_mul_nnEnergy]
    refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq ?_)))
    rw [Nat.cast_sub (hmK.trans hKN), Nat.cast_sub hmK,
      show (N : ℝ) - m - ((K : ℝ) - m) = N - K by ring]
    ring
  · set K := numComponents Z₀ with hK
    have hKN : K ≤ N := numComponents_le Z₀
    have hφ' : φ = nnMap (sumKey N) Z₀ := hφ.symm.trans (nearestNeighbor_eq_nnMap_fun Z₀)
    have hR : Fintype.card {i // i ∈ gpRefSet (sumKey N) φ} = K := by
      have h1 := two_mul_card_gpRefSet_eq (key := sumKey N) (f := φ)
        (fun i => hφ ▸ nearestNeighbor_ne Z₀ i)
      have h2 := card_cycleVerts_eq_two_mul_numComponents Z₀
      have h3 : Fintype.card {i // φ (φ i) = i} = (cycleVerts Z₀).card :=
        Fintype.card_of_subtype _ fun i => by rw [mem_cycleVerts, hφ]
      rw [h3, h2] at h1
      omega
    have hcard : Fintype.card (Fin N ⊕ Fin N) = 2 * N := by simp [two_mul]
    have h := h34 (Fin N ⊕ Fin N) (sumKey N) N N K φ hN le_rfl hcard hR lam hlam hlam1
    simp_rw [exp_neg_mul_nnEnergy]
    refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq ?_)))
    ring

end F2

/-! ### The per-cell bound and Step 3 for one marked graph (source l. 1580--1620) -/

section CellBound

open scoped ENNReal

/-- **The per-cell bound with a generic rate** (Proposition 3.10, Step 2, eq:2cases p, source
l. 1580--1595): the bound on the cell integral `J` of one
marked graph of `D_{2N,K,p,p₀}` obtained from (gred3), (eq:F(1)) and (eq:F(2)), before the count
of the graphs, with the error rate `ω_λ` replaced by `ω λ` for an arbitrary `ω : ℝ → ℝ`. Either
the main form

`J ≤ exp (A (N - K) - H + K (log N + (2-β) log λ + log 𝒵_β) + (2N - 2K) τ_β - c (p - p₀)²/N
  + C_b N ω(λ) + C_b log (N + 1) + X)`

holds, or `p < N/2` and the crude form

`J ≤ exp (A (N - K) - H + K (log N + (2-β) log λ + log 𝒵_β) + (2N - 2K) τ_β + C_b N + X)`

holds. Here `H = p log p - p₀ log p₀ - (p - p₀) log (p - p₀) + 60 (p - p₀)` is the entropy of
(eq:logD), `τ_β = (1 - β/4) log (N/(N-K)) 1_{β<4} + log (|log λ| + log (N/(N-K))) 1_{β=4}
+ (2 - β/2) log λ 1_{β>4}` the tree term of (eq:F(2)), `A (N - K)` collects the errors
`C_β (N - K)` of (gred3) and (eq:F(2)), and `X` is an extra exponent (for instance the long-pair
factor of Step 4, or an additional error `E N`). The integrand is arbitrary: this is the interface
between the energy-specific estimates and the counting of `exists_card_mul_le_of_cellBound_rate`.
-/
def CellBoundRate (β : ℝ) (hβ : 2 < β) (ω : ℝ → ℝ) (A c Cb : ℝ) (N K p p₀ : ℕ) (lam X : ℝ)
    (J : ℝ≥0∞) : Prop :=
  J ≤ ENNReal.ofReal (Real.exp (A * ((N : ℝ) - K)
      - (p * Real.log p - p₀ * Real.log p₀ - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀)
        + 60 * ((p : ℝ) - p₀))
      + K * (Real.log N + (2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le))
      + (2 * N - 2 * K) * ((if β < 4 then (1 - β / 4) * Real.log (N / ((N : ℝ) - K)) else 0) +
          (if β = 4 then Real.log (|Real.log lam| + Real.log (N / ((N : ℝ) - K))) else 0) +
          (if 4 < β then (2 - β / 2) * Real.log lam else 0))
      - c * ((p : ℝ) - p₀) ^ 2 / N + Cb * N * ω lam + Cb * Real.log (N + 1)
      + X)) ∨
  ((p : ℝ) < N / 2 ∧
    J ≤ ENNReal.ofReal (Real.exp (A * ((N : ℝ) - K)
      - (p * Real.log p - p₀ * Real.log p₀ - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀)
        + 60 * ((p : ℝ) - p₀))
      + K * (Real.log N + (2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le))
      + (2 * N - 2 * K) * ((if β < 4 then (1 - β / 4) * Real.log (N / ((N : ℝ) - K)) else 0) +
          (if β = 4 then Real.log (|Real.log lam| + Real.log (N / ((N : ℝ) - K))) else 0) +
          (if 4 < β then (2 - β / 2) * Real.log lam else 0))
      + Cb * N + X)))

/-- The constraints `p₀ ≤ p ≤ K ≤ N` and `K - p ≤ (M₀ + 2)(N - K)` (eq:K-p) hold as soon as
`D_{2N,K,p,p₀}` is nonempty. -/
theorem constraints_of_nonempty {N : ℕ} {hN : 2 ≤ N} {K p p₀ : ℕ}
    (hne : (markedGraphs hN K p p₀).Nonempty) :
    p₀ ≤ p ∧ p ≤ K ∧ K ≤ N ∧ (K : ℝ) - p ≤ (M0 + 2) * ((N : ℝ) - K) := by
  obtain ⟨γ, hγ⟩ := hne
  obtain ⟨Z, -, hgen, -, -, hK, hp, hp₀⟩ := mem_markedGraphs.1 hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hp, ← hp₀]
    exact numNeutralTwiceIsolated_le_numTwiceIsolated
  · rw [← hp, ← hK]
    exact numTwiceIsolated_le_numIsolatedPairs.trans (numIsolatedPairs_le_numComponents Z)
  · rw [← hK]
    exact numComponents_le Z
  · have := numComponents_sub_le_M0_add_two_mul hN hgen.1
    rwa [hK, hp] at this

/-- **(eq:quadra x3) for one marked graph, generic rate** (source l. 1580--1620: (eq:logD),
(eq:2cases p) with `χ_β`, and Step 3), for an arbitrary cell integral `J`
satisfying the per-cell bound `CellBoundRate` with a rate `ω` satisfying `UpperRateHyp`: for
`β > 2` and constants `A`, `c > 0`, `C_b ≥ 0` there are `c', C' > 0` and `0 < λ₀ ≤ e⁻¹`, depending
only on `β, ω, A, c, C_b`, such that for `N ≥ 2`, `0 < λ < λ₀`, every nonempty `D_{2N,K,p,p₀}` and
every extra exponent `X`, `|D_{2N,K,p,p₀}| · J ≤ exp (2N log N + N((2-β) log λ + log 𝒵_β - 1)
  - c' (N - p₀)²/N + C' N ω(λ) + C' log (N + 1) + X)`. -/
theorem exists_card_mul_le_of_cellBound_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ)
    (hω : UpperRateHyp β hβ ω) (A c Cb : ℝ) (hc : 0 < c) (hCb : 0 ≤ Cb) :
    ∃ c' C' lam₀ : ℝ, 0 < c' ∧ 0 < C' ∧ 0 < lam₀ ∧ lam₀ ≤ Real.exp (-1) ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (K p p₀ : ℕ) (lam : ℝ), 0 < lam → lam < lam₀ →
      (markedGraphs hN K p p₀).Nonempty → ∀ (X : ℝ) (J : ℝ≥0∞),
      CellBoundRate β hβ ω A c Cb N K p p₀ lam X J →
        ((markedGraphs hN K p p₀).card : ℝ≥0∞) * J ≤
          ENNReal.ofReal (Real.exp (2 * N * Real.log N
            + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1)
            - c' * ((N : ℝ) - p₀) ^ 2 / N + C' * N * ω lam
            + C' * Real.log (N + 1) + X)) := by
  set L := Real.log (dipoleConstant β hβ.le) with hL
  set Cχ := 2 * (M0 + 2) + 1 + 60 + |A| + |L| with hCχ
  obtain ⟨c', C'', hc', hC'', hmain⟩ := quadra_x3_main_term_rate hβ ω hω Cχ c hc
  obtain ⟨lam₁, hlam₁, hlam₁', hsmall⟩ := quadra_x3_small_p hβ Cχ Cb c' hc'.le
  refine ⟨c', C'' + Cb + 60, min lam₁ (Real.exp (-1)), hc', by positivity,
    lt_min hlam₁ (Real.exp_pos _), min_le_right _ _, ?_⟩
  intro N hN K p p₀ lam hlam hlamlt hne X J hJ
  have hlam1 : lam ≤ Real.exp (-1) := hlamlt.le.trans (min_le_right _ _)
  have hlamle : lam ≤ lam₁ := hlamlt.le.trans (min_le_left _ _)
  have hlt1 : lam < 1 := lt_of_le_of_lt hlam1 (Real.exp_lt_one_iff.2 (by norm_num))
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hp₀p, hpK, hKN, hKp⟩ := constraints_of_nonempty hne
  have hp₀N : p₀ ≤ N := hp₀p.trans (hpK.trans hKN)
  have hcard := card_markedGraphs_le_exp hN hp₀p hpK hKN
  have hD : ((markedGraphs hN K p p₀).card : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp
      (2 * N * Real.log N - (2 * N - 2 * K) * Real.log (((N : ℝ) - K) / N)
        - p₀ * Real.log p₀ - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀)
        - ((K : ℝ) - p) * Real.log ((K : ℝ) - p) - N + 60 * Real.log (N + 1)
        + 60 * (N - K) + 60 * (p - p₀))) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard
  have hcore := cell_exponent_le (p₀ := p₀) hβ A hN1 hpK hKN hKp hlam hlam1
  have hω0 : 0 ≤ ω lam := hω.nonneg lam hlam
  have hlogN : 0 ≤ Real.log (N + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rcases hJ with hJ | ⟨hpN, hJ⟩
  · have hq := hmain lam N K p p₀ hlam hlt1 hN1 hp₀N hKN hKp
    calc _ ≤ _ := mul_le_mul' hD hJ
      _ = _ := ofReal_exp_mul_ofReal_exp _ _
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : C'' * N * ω lam + Cb * N * ω lam ≤
        (C'' + Cb + 60) * N * ω lam := by
      have := mul_nonneg hN0 hω0
      linarith only [this]
    have h2 : (60 + Cb) * Real.log (N + 1) ≤ (C'' + Cb + 60) * Real.log (N + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hlogN
    linarith
  · have hq := hsmall lam N K p p₀ hlam hlamle hN1 hp₀N hpN hKp
    calc _ ≤ _ := mul_le_mul' hD hJ
      _ = _ := ofReal_exp_mul_ofReal_exp _ _
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : 0 ≤ (C'' + Cb + 60) * N * ω lam := by
      have := mul_nonneg hN0 hω0
      have : 0 ≤ C'' + Cb + 60 := by linarith
      positivity
    have h2 : 60 * Real.log (N + 1) ≤ (C'' + Cb + 60) * Real.log (N + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hlogN
    linarith

end CellBound

/-! ### The separation of variables with an event on the block `I` (source l. 1546--1551) -/

section Split

open MeasureTheory
open scoped ENNReal

variable {N : ℕ}

/-- **(gred3) with an event on the block `I`**: if on the cell of `γ = (φ, T)` the energy satisfies
`F_λ(Z) ≥ F₁(Z|_I) + F⁽²⁾(Z|_{Iᶜ}) - c`, and the event `E` forces `Z|_I ∈ E₁`, then
`∫_{Λ^{2N} ∩ E ∩ {γ_{2N} = γ}} e^{-β F_λ} ≤ e^{β c} ∫_{Λ^{2m} ∩ {γ_{2m} = γ¹} ∩ E₁} e^{-β F₁}
  ∫_{Λ^{2N-2m} ∩ {γ_{2N-2m} = γ²}} e^{-β F⁽²⁾}`. -/
theorem lintegral_markedCell_le_mul_event (hN : 2 ≤ N) {lam β c : ℝ} (hβ : 0 ≤ β)
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}]
    (F₁ : ({i // i ∈ pairVerts φ} → ℂ) → ℝ) (hF₁ : Measurable F₁)
    (hsplit : ∀ Z ∈ markedCell hN φ T, (∀ i, Z i ∈ box N) →
      F₁ (fun j : {i // i ∈ pairVerts φ} => Z j)
        + nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
          (fun j : {i // i ∉ pairVerts φ} => Z j) - c ≤ energy lam Z)
    (E : Set (Fin N ⊕ Fin N → ℂ)) (E₁ : Set ({i // i ∈ pairVerts φ} → ℂ))
    (hE₁ : MeasurableSet E₁) (hE : ∀ Z ∈ E, (fun j : {i // i ∈ pairVerts φ} => Z j) ∈ E₁) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) ≤
      ENNReal.ofReal (Real.exp (β * c)) *
        ((∫⁻ x in (Set.univ.pi fun _ : {i // i ∈ pairVerts φ} => box N) ∩
            ({x | nnMap (subtypeKey (· ∈ pairVerts φ) (sumKey N)) x = pairRestrict φ} ∩ E₁),
            ENNReal.ofReal (Real.exp (-β * F₁ x))) *
          ∫⁻ y in (Set.univ.pi fun _ : {i // i ∉ pairVerts φ} => box N) ∩
            {y | nnMap (subtypeKey (· ∉ pairVerts φ) (sumKey N)) y = complRestrict φ},
            ENNReal.ofReal (Real.exp (-β *
              nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam y))) := by
  classical
  set S := markedCell hN φ T ∩ {Z | (fun j : {i // i ∈ pairVerts φ} => Z j) ∈ E₁} with hS
  have hres : Measurable fun Z : Fin N ⊕ Fin N → ℂ => fun j : {i // i ∈ pairVerts φ} => Z j :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hSm : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ S) :=
    (measurableSet_pi_box N).inter ((measurableSet_markedCell hN φ T).inter (hres hE₁))
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ S,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) := by
        refine lintegral_mono_set ?_
        rintro Z ⟨⟨hZΛ, hZE⟩, hZc⟩
        exact ⟨hZΛ, hZc, hE Z hZE⟩
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ S,
        ENNReal.ofReal (Real.exp (β * c)) *
          (ENNReal.ofReal (Real.exp (-β * F₁ (fun j : {i // i ∈ pairVerts φ} => Z j))) *
            ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∉ pairVerts φ} => Z j)))) := by
        refine setLIntegral_mono' hSm fun Z hZ => ?_
        obtain ⟨hZΛ, hZc, -⟩ := hZ
        exact ofReal_exp_neg_mul_le_mul hβ (hsplit Z hZc fun i => hZΛ i (Set.mem_univ i))
    _ = ENNReal.ofReal (Real.exp (β * c)) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ S,
          ENNReal.ofReal (Real.exp (-β * F₁ (fun j : {i // i ∈ pairVerts φ} => Z j))) *
            ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∉ pairVerts φ} => Z j))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        refine setLIntegral_subtype_mul_le (pairVerts φ) (box N) S
          ({x | nnMap (subtypeKey (· ∈ pairVerts φ) (sumKey N)) x = pairRestrict φ} ∩ E₁)
          {y | nnMap (subtypeKey (· ∉ pairVerts φ) (sumKey N)) y = complRestrict φ}
          (fun Z hZ => ⟨⟨nnMap_pairRestrict hZ.1.2.1, hZ.2⟩, nnMap_complRestrict hZ.1.2.1⟩)
          (measurable_ofReal_exp_neg_mul hF₁ β)
          (measurable_ofReal_exp_neg_mul (measurable_nnEnergy _ lam) β)

/-- **The cell integral with an event, on all indices** (the case `Iᶜ = ∅`): if on the cell
`F_λ ≥ F - c` and `E ⊆ E'`, then `∫_{Λ^{2N} ∩ E ∩ {γ_{2N} = γ}} e^{-β F_λ} ≤
e^{β c} ∫_{Λ^{2N} ∩ {γ_{2N} = φ} ∩ E'} e^{-β F}`. -/
theorem lintegral_markedCell_le_event [Nontrivial (Fin N ⊕ Fin N)] (hN : 2 ≤ N) {lam β c : ℝ}
    (hβ : 0 ≤ β) {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (F : (Fin N ⊕ Fin N → ℂ) → ℝ)
    (hsplit : ∀ Z ∈ markedCell hN φ T, (∀ i, Z i ∈ box N) → F Z - c ≤ energy lam Z)
    (E E' : Set (Fin N ⊕ Fin N → ℂ)) (hE' : MeasurableSet E') (hE : E ⊆ E') :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) ≤
      ENNReal.ofReal (Real.exp (β * c)) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nnMap (sumKey N) Z = φ} ∩ E',
          ENNReal.ofReal (Real.exp (-β * F Z)) := by
  have hm : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
      (markedCell hN φ T ∩ E')) :=
    (measurableSet_pi_box N).inter ((measurableSet_markedCell hN φ T).inter hE')
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ (markedCell hN φ T ∩ E'),
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) := by
        refine lintegral_mono_set ?_
        rintro Z ⟨⟨hZΛ, hZE⟩, hZc⟩
        exact ⟨hZΛ, hZc, hE hZE⟩
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ (markedCell hN φ T ∩ E'),
        ENNReal.ofReal (Real.exp (β * c)) * ENNReal.ofReal (Real.exp (-β * F Z)) := by
        refine setLIntegral_mono' hm fun Z hZ => ?_
        exact ofReal_exp_neg_mul_le hβ (hsplit Z hZ.2.1 fun i => hZ.1 i (Set.mem_univ i))
    _ = ENNReal.ofReal (Real.exp (β * c)) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ (markedCell hN φ T ∩ E'),
          ENNReal.ofReal (Real.exp (-β * F Z)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right (lintegral_mono_set ?_) _
        rintro Z ⟨hZΛ, hZc, hZE⟩
        exact ⟨⟨hZΛ, (nearestNeighbor_eq_nnMap_fun Z).symm.trans hZc.2.1⟩, hZE⟩

end Split

/-! ### One isolated pair (`m = 1`) -/

section Pair

open MeasureTheory Finset
open scoped ENNReal

/-- In a two-element index type, the nearest-neighbour map is the other point. -/
theorem nnMap_eq_of_card_two {ι : Type} [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) {f : ι → ι}
    (hc : Fintype.card ι = 2) (hf0 : ∀ i, f i ≠ i) (z : ι → ℂ) : nnMap key z = f := by
  classical
  funext i
  obtain ⟨a, b, hab, huniv⟩ := Finset.card_eq_two.1 (show (Finset.univ : Finset ι).card = 2 by
    rw [Finset.card_univ, hc])
  have hall : ∀ x : ι, x = a ∨ x = b := fun x => by
    have : x ∈ ({a, b} : Finset ι) := huniv ▸ Finset.mem_univ x
    simpa using this
  have h1 := nnMap_ne key z i
  have h2 := hf0 i
  rcases hall i with rfl | rfl <;> rcases hall (nnMap key z i) with h | h <;>
    rcases hall (f i) with h' | h' <;> simp_all

/-- The mass of `e^{β g_λ}` on `{|u| > R}`, `R ≥ 2λ`, is at most `2π R^{2-β}/(β - 2)`. -/
theorem lintegral_long_le {β : ℝ} (hβ : 2 < β) {lam Rl : ℝ} (hlam : 0 < lam)
    (hRl : 2 * lam ≤ Rl) :
    ∫⁻ u : ℂ, ENNReal.ofReal (Real.exp (β * smearedKernel lam u)) *
        ({v : ℂ | Rl < ‖v‖}.indicator (fun _ => (1 : ℝ≥0∞)) u) ≤
      ENNReal.ofReal (2 * Real.pi * (Rl ^ (2 - β) / (β - 2))) := by
  have hpt : ∀ u : ℂ, ENNReal.ofReal (Real.exp (β * smearedKernel lam u)) *
      ({v : ℂ | Rl < ‖v‖}.indicator (fun _ => (1 : ℝ≥0∞)) u) ≤
      (Metric.ball (0 : ℂ) Rl)ᶜ.indicator
        (fun u => ENNReal.ofReal (Real.exp (β * smearedKernel lam u))) u := by
    intro u
    by_cases hlong : Rl < ‖u‖
    · have hmem : u ∈ (Metric.ball (0 : ℂ) Rl)ᶜ := by
        simp only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt]
        exact hlong.le
      rw [Set.indicator_of_mem (show u ∈ {v : ℂ | Rl < ‖v‖} from hlong), mul_one,
        Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem (show u ∉ {v : ℂ | Rl < ‖v‖} from hlong), mul_zero]
      exact zero_le
  calc _ ≤ ∫⁻ u, (Metric.ball (0 : ℂ) Rl)ᶜ.indicator
        (fun u => ENNReal.ofReal (Real.exp (β * smearedKernel lam u))) u := lintegral_mono hpt
    _ = ∫⁻ u in (Metric.ball (0 : ℂ) Rl)ᶜ, ENNReal.ofReal (Real.exp (β * smearedKernel lam u)) :=
        lintegral_indicator Metric.isOpen_ball.measurableSet.compl _
    _ = ENNReal.ofReal (∫ u in (Metric.ball (0 : ℂ) Rl)ᶜ, Real.exp (β * smearedKernel lam u)) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_exp_smearedKernel hβ hlam).integrableOn
          (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)).symm
    _ = _ := by rw [integral_compl_ball_exp_smearedKernel hβ hlam hRl]

/-- **The integral over one isolated pair required to be long** (source l. 1542, 1644--1649, the
case `m = 1`): for a two-element index type with the swap `f` and a vertex `j₀`, the integral of
`e^{-β F^nn}` over the cell intersected with `{|z_{f j₀} - z_{j₀}| > R}` is at most
`N · 2π R^{2-β}/(β - 2)` (one representative in `Λ`, one displacement outside `B(0, R)`). -/
theorem lintegral_pair_long_le {β : ℝ} (hβ : 2 < β) {ι : Type} [Fintype ι] [Nontrivial ι]
    (key : ι ↪ ℕ) {f : ι → ι} (hc : Fintype.card ι = 2) (hf0 : ∀ i, f i ≠ i)
    (hf2 : ∀ i, f (f i) = i) (j₀ : ι) (N : ℕ) {lam Rl : ℝ} (hlam : 0 < lam)
    (hRl : 2 * lam ≤ Rl) :
    ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩
        ({z | nnMap key z = f} ∩ {z | Rl < ‖z (f j₀) - z j₀‖}),
        ENNReal.ofReal (Real.exp (-β * nnEnergy key lam z)) ≤
      ENNReal.ofReal (N * (2 * Real.pi * (Rl ^ (2 - β) / (β - 2)))) := by
  classical
  have hR : ∀ i, ∃ n, f^[n] i ∈ gpRefSet key f :=
    gpRefSet_reaches hf0 (fun i => ⟨0, hf2 i⟩)
  have hRf : ∀ i, i ∈ gpRefSet key f ↔ f i ∉ gpRefSet key f := fun i =>
    gpRefSet_mem_iff_not_mem (hf2 i) (hf0 i)
  have hcR : 2 * Fintype.card {i // i ∈ gpRefSet key f} = 2 := by
    rw [UpperCellBound.two_mul_card_gpRefSet_eq hf0, ← hc]
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun i => hf2 i)
  have hcR1 : Fintype.card {i // i ∈ gpRefSet key f} = 1 := by omega
  have hcN : Fintype.card {i // i ∉ gpRefSet key f} = 1 := by
    rw [Fintype.card_subtype_compl, hc, hcR1]
  have huniv : (Finset.univ : Finset ι) = {j₀, f j₀} := by
    refine (Finset.eq_univ_of_card _ ?_).symm
    rw [Finset.card_pair (hf0 j₀).symm, hc]
  -- the integrand is a function of the displacement `z_{f j₀} - z_{j₀}`
  set ind : ℂ → ℝ≥0∞ := {v : ℂ | Rl < ‖v‖}.indicator (fun _ => (1 : ℝ≥0∞)) with hind
  have hindm : Measurable ind :=
    measurable_const.indicator (measurableSet_lt measurable_const measurable_norm)
  set G : ℂ → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (β * smearedKernel lam v)) * ind v
    with hGdef
  have hGm : Measurable G := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul hindm
    exact Real.measurable_exp.comp ((measurable_smearedKernel lam).const_mul β)
  have hGneg : ∀ v, G (-v) = G v := by
    intro v
    simp only [hGdef, hind, smearedKernel_neg, Set.indicator, Set.mem_ofPred_eq, norm_neg]
  have hE : ∀ z : ι → ℂ, Real.exp (-β * nnEnergy key lam z) =
      Real.exp (β * smearedKernel lam (z (f j₀) - z j₀)) := by
    intro z
    congr 1
    unfold nnEnergy
    rw [nnMap_eq_of_card_two key hc hf0, huniv, Finset.sum_pair (hf0 j₀).symm, hf2,
      show z j₀ - z (f j₀) = -(z (f j₀) - z j₀) by ring, smearedKernel_neg]
    ring
  set F : (ι → ℂ) → ℝ≥0∞ := fun z => G (z (f j₀) - z j₀) with hFdef
  set m₀ : ι := if j₀ ∈ gpRefSet key f then f j₀ else j₀ with hm₀
  have hm₀R : m₀ ∉ gpRefSet key f := by
    rw [hm₀]
    split_ifs with hj
    · exact (hRf j₀).1 hj
    · exact hj
  have hFG : ∀ u, F ((gpLinearEquiv f (gpRefSet key f) hR).symm u) =
      ∏ i : {i // i ∉ gpRefSet key f}, G (u i) := by
    intro u
    have hsub : ∀ x : {i // i ∉ gpRefSet key f}, x = ⟨m₀, hm₀R⟩ := fun x =>
      Fintype.card_le_one_iff.1 (le_of_eq hcN) x ⟨m₀, hm₀R⟩
    rw [Fintype.prod_eq_single ⟨m₀, hm₀R⟩ (fun x hx => absurd (hsub x) hx)]
    simp only [hFdef]
    by_cases hj : j₀ ∈ gpRefSet key f
    · have h1 := gp_symm_sub_of_mem hR u hf0 hj
      have hm : m₀ = f j₀ := by rw [hm₀, ite_eq_left hj]
      rw [hm, show (gpLinearEquiv f (gpRefSet key f) hR).symm u (f j₀) -
        (gpLinearEquiv f (gpRefSet key f) hR).symm u j₀ =
          -((gpLinearEquiv f (gpRefSet key f) hR).symm u j₀ -
            (gpLinearEquiv f (gpRefSet key f) hR).symm u (f j₀)) by ring, h1, neg_neg]
    · have h1 := gp_symm_sub_of_notMem hR u hj
      have hm : m₀ = j₀ := by rw [hm₀, ite_eq_right hj]
      rw [hm, show (gpLinearEquiv f (gpRefSet key f) hR).symm u (f j₀) -
        (gpLinearEquiv f (gpRefSet key f) hR).symm u j₀ =
          -((gpLinearEquiv f (gpRefSet key f) hR).symm u j₀ -
            (gpLinearEquiv f (gpRefSet key f) hR).symm u (f j₀)) by ring, h1, hGneg]
  have hcell := lintegral_cell_le_prod (N := N) key (gpRefSet key f) hR F (fun _ => G)
    (fun _ => hGm) hFG
  rw [hcR1, pow_one] at hcell
  have hmeasL : MeasurableSet {z : ι → ℂ | Rl < ‖z (f j₀) - z j₀‖} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hcellm : MeasurableSet {z : ι → ℂ | nnMap key z = f} := by
    have : {z : ι → ℂ | nnMap key z = f} = ⋂ i, {z | nnMap key z i = f i} := by
      ext z; simp [funext_iff]
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_nnMap_eq key i (f i)
  have hball : ∫⁻ v in {v : {i // i ∉ gpRefSet key f} → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ 36 * N / Real.pi},
      ∏ i : {i // i ∉ gpRefSet key f}, G (v i) ≤
        ENNReal.ofReal (2 * Real.pi * (Rl ^ (2 - β) / (β - 2))) := by
    calc _ ≤ ∫⁻ v : {i // i ∉ gpRefSet key f} → ℂ, ∏ i, G (v i) := setLIntegral_le_lintegral _ _
      _ = ∫⁻ v in Set.univ.pi fun _ : {i // i ∉ gpRefSet key f} => (Set.univ : Set ℂ),
            ∏ i, G (v i) := by rw [Set.pi_univ, Measure.restrict_univ]
      _ = ∏ _i : {i // i ∉ gpRefSet key f}, ∫⁻ u in (Set.univ : Set ℂ), G u :=
          IsolatedReduction.lintegral_pi_set_prod _ (fun _ => MeasurableSet.univ) (fun _ => G)
            (fun _ => hGm)
      _ = ∫⁻ u, G u := by
          rw [Finset.prod_const, Finset.card_univ, hcN, pow_one, Measure.restrict_univ]
      _ ≤ _ := lintegral_long_le hβ hlam hRl
  calc _ ≤ ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f}, F z := by
        refine (setLIntegral_mono' ((MeasurableSet.univ_pi fun _ => measurableSet_box N).inter
          (hcellm.inter hmeasL)) fun z hz => ?_).trans
          (lintegral_mono_set (Set.inter_subset_inter_right _ Set.inter_subset_left))
        have h1 : ind (z (f j₀) - z j₀) = 1 :=
          Set.indicator_of_mem (show z (f j₀) - z j₀ ∈ {v : ℂ | Rl < ‖v‖} from hz.2.2) _
        simp only [hFdef, hGdef, hE z, h1, mul_one, le_refl]
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi * (Rl ^ (2 - β) / (β - 2))) :=
        hcell.trans (mul_le_mul_right hball _)
    _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]

end Pair

end UpperCellBound

end TwoComponentCoulomb

end
