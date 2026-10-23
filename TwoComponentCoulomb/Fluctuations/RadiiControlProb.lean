/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.RadiiControlRates
public import TwoComponentCoulomb.Fluctuations.Theorem2Rate
public import TwoComponentCoulomb.Frozen.GibbsMeasure
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import TwoComponentCoulomb.Main.Theorem1AssemblyBounds
import TwoComponentCoulomb.NearestNeighbor.Isolated

/-!
# Theorem 2, Step 5: the probability of `A_Mᶜ` (eq. (eq:PAM))

Source: proof of Theorem 2, Step 5 (l. 2060–2072). With a rate function `ω` in place of `ω_λ`
and `R₀ = R0Rate β ω λ`, the event of the source is `A_M = {N - ½|I^dip| + D_{R₀} ≤ M N √ω}`
(`eventARate`). A union bound over the counts of isolated dipoles (Theorem 1, (b1)) and of long
isolated dipoles (Theorem 1, (b2) for `β > 2` and the critical-lengths bound for `β = 2`) gives,
for `M` large, `ℙ(A_Mᶜ) ≤ C (N+1)^C e^{-c M N ω}` (eq. (eq:PAM), l. 2070–2072).

The statements of Theorem 1 enter only as the hypotheses `hb1`, `hb2`, `hb3` of the conditional
helpers below: the three clauses of Theorem 1 used in Step 5, stated with `ω` in the form of
`Theorem1ShapeRate` (`Fluctuations/Theorem2Rate.lean`).

* `exponent_b1_le`, `exponent_b2_le`, `exponent_b3_le` : the exponent comparisons.
* `measure_le_card_mul_of_subset_biUnion` : the union bound over counts.
* `gibbsMeasure_isolatedDipoles_deficit_le_rate`,
  `gibbsMeasure_longIsolatedDipoles_le_of_two_lt_rate`,
  `gibbsMeasure_longIsolatedDipoles_le_of_eq_two_rate` : the union bounds for the deficit of
  isolated dipoles and for the long isolated dipoles.
* `eventARate` : the event `A_M`.
* `exists_gibbsMeasure_eventARate_compl_le` : (eq:PAM), under the rate properties
  `Theorem2RateHyp β hβ ω`.

Steps 5--6 are proved for a general rate function `ω` (see `Fluctuations/Theorem2Rate.lean`);
the instance `ω = errorRate β hβ` is taken in the proof of Theorem 2 (`Main/Theorem2.lean`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### Exponent comparisons -/

/-- The exponent of (b1) on `{N - p > M N √ω / 2}`: `≤ C log (N+1) - M N ω` for `M` large. -/
theorem exponent_b1_le {c C M N ω p : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hM1 : 1 ≤ M)
    (hMc : 4 * (C + 1) / c ≤ M) (hN : 0 < N) (hω : 0 ≤ ω)
    (hp : M * N * Real.sqrt ω / 2 < N - p) :
    -c * N * (1 - p / N) ^ 2 + C * N * ω ≤ -(M * N * ω) := by
  have hu : M * Real.sqrt ω / 2 < 1 - p / N := by
    have : 1 - p / N = (N - p) / N := by field_simp
    rw [this, lt_div_iff₀ hN]
    linarith
  have hu0 : 0 ≤ M * Real.sqrt ω / 2 := by positivity
  have hu2 : (M * Real.sqrt ω / 2) ^ 2 ≤ (1 - p / N) ^ 2 := pow_le_pow_left₀ hu0 hu.le 2
  have h2 : (M * Real.sqrt ω / 2) ^ 2 = M ^ 2 * ω / 4 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hω]
    ring
  rw [h2] at hu2
  have hcM : (C + 1) * M ≤ c * M ^ 2 / 4 := by
    have : 4 * (C + 1) ≤ c * M := by
      have := (div_le_iff₀ hc).1 hMc
      linarith
    linarith only [mul_le_mul_of_nonneg_right this (by linarith only [hM1] : (0 : ℝ) ≤ M)]
  have hNω : 0 ≤ N * ω := by positivity
  have h3 : -c * N * (1 - p / N) ^ 2 ≤ -c * N * (M ^ 2 * ω / 4) := by
    have := mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ c * N)
    linarith only [this]
  have h4 : (C + M) * (N * ω) ≤ (c * M ^ 2 / 4) * (N * ω) :=
    mul_le_mul_of_nonneg_right (by linarith only [hcM, mul_nonneg hC (sub_nonneg.2 hM1)]) hNω
  linarith only [h3, h4]

/-- The exponent of (b2) on `{D_{R₀} > M N √ω / 2}` for `β > 2`, where `(λ/R₀)^{β-2} = a ≤ √ω`. -/
theorem exponent_b2_le {C₁ C₂ M N ω x a : ℝ} (hC₁ : 0 < C₁)
    (hM : 2 * Real.exp 1 ≤ M) (hM' : 4 * C₂ / C₁ ≤ M) (hN : 0 < N) (hω0 : 0 < ω) (hω1 : ω ≤ 1)
    (ha0 : 0 < a) (ha : a ≤ Real.sqrt ω) (hx : M * Real.sqrt ω / 2 < x) :
    -C₁ * N * x * Real.log (x / a) + C₂ * N * Real.sqrt ω ≤ -(C₁ / 4 * M * N * ω) := by
  have hs0 : 0 < Real.sqrt ω := Real.sqrt_pos.2 hω0
  have hM0 : 0 < M := by linarith [Real.exp_pos 1]
  have hx0 : 0 < x := lt_of_le_of_lt (by positivity) hx
  have hxa : Real.exp 1 ≤ x / a := by
    have h1 : M / 2 < x / Real.sqrt ω := by
      rw [lt_div_iff₀ hs0]
      linarith
    have h2 : x / Real.sqrt ω ≤ x / a := div_le_div_of_nonneg_left hx0.le ha0 ha
    linarith [Real.exp_pos 1]
  have hlog : 1 ≤ Real.log (x / a) := (Real.le_log_iff_exp_le (by positivity)).2 hxa
  have h1 : x ≤ x * Real.log (x / a) := le_mul_of_one_le_right hx0.le hlog
  have hsω : ω ≤ Real.sqrt ω := by
    have := Real.sqrt_le_sqrt hω1
    rw [Real.sqrt_one] at this
    calc ω = Real.sqrt ω * Real.sqrt ω := (Real.mul_self_sqrt hω0.le).symm
      _ ≤ Real.sqrt ω * 1 := by gcongr
      _ = Real.sqrt ω := mul_one _
  have h3 : C₁ * N * x ≤ C₁ * N * (x * Real.log (x / a)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 4 * C₂ ≤ C₁ * M := by
    have := (div_le_iff₀ hC₁).1 hM'
    linarith
  have h5 : C₁ * N * (M * Real.sqrt ω / 2) ≤ C₁ * N * x :=
    mul_le_mul_of_nonneg_left hx.le (by positivity)
  have hNs : 0 ≤ N * Real.sqrt ω := by positivity
  have h6 : (C₁ * M / 4) * (N * ω) ≤ (C₁ * M / 4) * (N * Real.sqrt ω) := by
    have : 0 ≤ C₁ * M / 4 := by
      have : 0 ≤ M := by linarith [Real.exp_pos 1]
      positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsω hN.le) this
  linarith only [h3, h5, h6, mul_le_mul_of_nonneg_right h4 hNs]

/-- The exponent of the critical-lengths bound on `{D_{R₀} > M N √ω / 2}` for `β = 2`:
`-p + C N (ω + e) ≤ -(M/4) N ω` if `e ≤ K ω` and `M ≥ 4 C (1 + K)`. -/
theorem exponent_b3_le {C M N ω p e K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hM : 4 * C * (1 + K) ≤ M)
    (hN : 0 ≤ N) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (he : e ≤ K * ω)
    (hp : M * N * Real.sqrt ω / 2 < p) :
    -p + C * N * (ω + e) ≤ -(M / 4 * N * ω) := by
  have hsω : ω ≤ Real.sqrt ω := by
    have := Real.sqrt_le_sqrt hω1
    rw [Real.sqrt_one] at this
    calc ω = Real.sqrt ω * Real.sqrt ω := (Real.mul_self_sqrt hω0).symm
      _ ≤ Real.sqrt ω * 1 := by gcongr
      _ = Real.sqrt ω := mul_one _
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  have h1 : M * N * ω / 2 ≤ p := by
    have : M * N * ω ≤ M * N * Real.sqrt ω := by
      have : 0 ≤ M * N := by positivity
      exact mul_le_mul_of_nonneg_left hsω this
    linarith
  have h2 : C * N * (ω + e) ≤ C * N * ((1 + K) * ω) :=
    mul_le_mul_of_nonneg_left (by linarith only [he]) (by positivity)
  have h3 : 4 * C * (1 + K) * (N * ω) ≤ M * (N * ω) :=
    mul_le_mul_of_nonneg_right hM (by positivity)
  linarith only [h1, h2, h3]

/-! ### Union bound over the counts -/

/-- Union bound over a finite set `S` of counts: if `s ⊆ ⋃_{p ∈ S} E p` and each `E p` has mass
at most `b`, then `μ s ≤ |S| b`. -/
theorem measure_le_card_mul_of_subset_biUnion {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {s : Set X} (E : ℕ → Set X) (S : Finset ℕ) (b : ℝ≥0∞) (hs : s ⊆ ⋃ p ∈ S, E p)
    (hb : ∀ p ∈ S, μ (E p) ≤ b) : μ s ≤ S.card * b := by
  calc μ s ≤ μ (⋃ p ∈ S, E p) := measure_mono hs
    _ ≤ ∑ p ∈ S, μ (E p) := measure_biUnion_finset_le S E
    _ ≤ S.card • b := Finset.sum_le_card_nsmul S _ b hb
    _ = S.card * b := nsmul_eq_mul _ _

/-- `(n + 1) e^E = e^{log (n+1) + E}` in `[0, ∞]`. -/
theorem natCast_succ_mul_ofReal_exp (n : ℕ) (E : ℝ) :
    ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp E) =
      ENNReal.ofReal (Real.exp (Real.log ((n : ℝ) + 1) + E)) := by
  have h : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) + 1) := by
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  rw [h, ← ENNReal.ofReal_mul (by positivity), Real.exp_add, Real.exp_log (by positivity)]

/-- The union of two exceptional events, each bounded by an exponential. -/
theorem measure_le_two_mul_of_subset_union {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {s E₁ E₂ : Set X} (h : s ⊆ E₁ ∪ E₂) {a₁ a₂ b : ℝ}
    (h1 : μ E₁ ≤ ENNReal.ofReal (Real.exp a₁)) (h2 : μ E₂ ≤ ENNReal.ofReal (Real.exp a₂))
    (ha₁ : a₁ ≤ b) (ha₂ : a₂ ≤ b) : μ s ≤ ENNReal.ofReal (2 * Real.exp b) := by
  have hb : 0 ≤ Real.exp b := (Real.exp_pos b).le
  calc μ s ≤ μ (E₁ ∪ E₂) := measure_mono h
    _ ≤ μ E₁ + μ E₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp b) + ENNReal.ofReal (Real.exp b) :=
        add_le_add (h1.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ha₁)))
          (h2.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ha₂)))
    _ = ENNReal.ofReal (2 * Real.exp b) := by
        rw [← ENNReal.ofReal_add hb hb]
        congr 1
        ring

/-! ### The deficit of isolated dipoles (Theorem 1, (b1)) -/

/-- Union bound over the counts `p₀` of isolated dipoles with `N - p₀ > M N √ω / 2`, using
Theorem 1, (b1) , for a general rate function `ω`. -/
theorem gibbsMeasure_isolatedDipoles_deficit_le_rate (β : ℝ) (ω : ℝ → ℝ) {lam₀ C c : ℝ}
    (hC : 0 < C) (hc : 0 < c)
    (hb1 : ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ p₀ : ℕ, p₀ ≤ N →
      gibbsMeasure N β lam {Z | (isolatedDipoles Z).card = p₀}
        ≤ ENNReal.ofReal (Real.exp (-c * N * (1 - (p₀ : ℝ) / N) ^ 2
          + C * N * ω lam + C * Real.log (N + 1))))
    {M : ℝ} (hM1 : 1 ≤ M) (hMc : 4 * (C + 1) / c ≤ M) {N : ℕ} (hN : 2 ≤ N) {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam < lam₀) (hω0 : 0 ≤ ω lam) :
    gibbsMeasure N β lam
        {Z | M * N * Real.sqrt (ω lam) / 2 < N - (isolatedDipoles Z).card}
      ≤ ENNReal.ofReal (Real.exp ((C + 1) * Real.log (N + 1)
          - M * N * ω lam)) := by
  classical
  set w := ω lam with hw
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set S : Finset ℕ := (Finset.range (N + 1)).filter
    (fun p => M * N * Real.sqrt w / 2 < (N : ℝ) - p) with hS
  have hsub : {Z : Fin N ⊕ Fin N → ℂ | M * N * Real.sqrt w / 2 < N - (isolatedDipoles Z).card}
      ⊆ ⋃ p ∈ S, {Z | (isolatedDipoles Z).card = p} := by
    intro Z hZ
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨(isolatedDipoles Z).card, Finset.mem_filter.2
      ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (isolatedDipoles_card_le Z)), hZ⟩, rfl⟩
  have hbound : ∀ p ∈ S, gibbsMeasure N β lam {Z | (isolatedDipoles Z).card = p} ≤
      ENNReal.ofReal (Real.exp (C * Real.log (N + 1) - M * N * w)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    refine (hb1 N hN lam h0 h1 p (Nat.lt_succ_iff.1 (Finset.mem_range.1 hp1))).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := exponent_b1_le hc hC.le hM1 hMc hN0 hω0 hp2
    linarith
  refine (measure_le_card_mul_of_subset_biUnion _ _ S _ hsub hbound).trans ?_
  have hcard : S.card ≤ N + 1 := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  calc (S.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (C * Real.log (N + 1) - M * N * w))
      ≤ ((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (C * Real.log (N + 1) - M * N * w)) :=
        mul_le_mul_left (by exact_mod_cast hcard) _
    _ = ENNReal.ofReal (Real.exp (Real.log ((N : ℝ) + 1) +
          (C * Real.log (N + 1) - M * N * w))) := natCast_succ_mul_ofReal_exp N _
    _ = _ := by
        congr 2
        ring

/-! ### Long isolated dipoles -/

/-- Union bound over the counts `p'` of isolated dipoles of length larger than `R` with
`p' > M N √ω / 2`, for `β > 2`, using Theorem 1, (b2), when `(λ/R)^{β-2} = √ω`
, for a general rate function `ω`. -/
theorem gibbsMeasure_longIsolatedDipoles_le_of_two_lt_rate (β : ℝ) (ω : ℝ → ℝ)
    {lam₀ c' C₁ C₂ : ℝ}
    (hC₁ : 0 < C₁)
    (hb2 : ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, p₀' ≤ N →
          c' * (lam / R) ^ (β - 2) ≤ (p₀' : ℝ) / N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (Real.exp
                (-C₁ * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) / (lam / R) ^ (β - 2))
                  + C₂ * N * Real.sqrt (ω lam) + C₂ * Real.log (N + 1))))
    {M : ℝ} (hM : 2 * Real.exp 1 ≤ M) (hM2 : 2 * c' ≤ M) (hM3 : 4 * C₂ / C₁ ≤ M) {N : ℕ}
    (hN : 2 ≤ N) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < lam₀) {R : ℝ} (hR : 2 * lam ≤ R)
    (hRa : (lam / R) ^ (β - 2) = Real.sqrt (ω lam))
    (hω0 : 0 < ω lam) (hω1 : ω lam ≤ 1) :
    gibbsMeasure N β lam
        {Z | M * N * Real.sqrt (ω lam) / 2 < (longIsolatedDipoles Z R).card}
      ≤ ENNReal.ofReal (Real.exp ((C₂ + 1) * Real.log (N + 1)
          - C₁ / 4 * M * N * ω lam)) := by
  classical
  set w := ω lam with hw
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs0 : 0 < Real.sqrt w := Real.sqrt_pos.2 hω0
  set S : Finset ℕ := (Finset.range (N + 1)).filter
    (fun p => M * N * Real.sqrt w / 2 < (p : ℝ)) with hS
  have hsub : {Z : Fin N ⊕ Fin N → ℂ | M * N * Real.sqrt w / 2 < (longIsolatedDipoles Z R).card}
      ⊆ ⋃ p ∈ S, {Z | (longIsolatedDipoles Z R).card = p} := by
    intro Z hZ
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨(longIsolatedDipoles Z R).card, Finset.mem_filter.2
      ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (longIsolatedDipoles_card_le Z R)), hZ⟩, rfl⟩
  have hbound : ∀ p ∈ S, gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p} ≤
      ENNReal.ofReal (Real.exp (C₂ * Real.log (N + 1) - C₁ / 4 * M * N * w)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    have hx : M * Real.sqrt w / 2 < (p : ℝ) / N := by
      rw [lt_div_iff₀ hN0]
      linarith
    have hM0 : 0 < M := by linarith [Real.exp_pos 1]
    have hcond : c' * (lam / R) ^ (β - 2) ≤ (p : ℝ) / N := by
      rw [hRa]
      have : c' * Real.sqrt w ≤ M * Real.sqrt w / 2 := by
        linarith only [mul_le_mul_of_nonneg_right hM2 hs0.le]
      linarith
    refine (hb2 N hN lam h0 h1 R hR p (Nat.lt_succ_iff.1 (Finset.mem_range.1 hp1)) hcond).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    rw [hRa]
    have := exponent_b2_le (x := (p : ℝ) / N) (a := Real.sqrt w) hC₁ hM hM3 hN0 hω0 hω1 hs0
      le_rfl hx
    linarith
  refine (measure_le_card_mul_of_subset_biUnion _ _ S _ hsub hbound).trans ?_
  have hcard : S.card ≤ N + 1 := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  calc (S.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (C₂ * Real.log (N + 1) - C₁ / 4 * M * N * w))
      ≤ ((N + 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (C₂ * Real.log (N + 1) - C₁ / 4 * M * N * w)) :=
        mul_le_mul_left (by exact_mod_cast hcard) _
    _ = ENNReal.ofReal (Real.exp (Real.log ((N : ℝ) + 1) +
          (C₂ * Real.log (N + 1) - C₁ / 4 * M * N * w))) := natCast_succ_mul_ofReal_exp N _
    _ = _ := by
        congr 2
        ring

/-- Union bound over the counts `p'` of isolated dipoles of length larger than `R` with
`p' > M N √ω / 2`, for `β = 2`, using the critical-lengths bound (Theorem 1, third clause) with
`R = R₀` , for a general rate function `ω`. -/
theorem gibbsMeasure_longIsolatedDipoles_le_of_eq_two_rate (β : ℝ) (ω : ℝ → ℝ) {lam₃ C : ℝ}
    (hC : 0 < C)
    (hb3 : ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₃ →
        ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 → ∀ p₀' : ℕ, p₀' ≤ N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (((N : ℝ) + 1) ^ C * Real.exp (-(p₀' : ℝ) + C * N *
                (ω lam
                  + (1 + Real.log |Real.log lam| + Real.log (1 / R)) / |Real.log lam|))))
    {M : ℝ} (hM : 24 * C ≤ M) {N : ℕ} (hN : 2 ≤ N) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < lam₃)
    {R : ℝ} (hR : 2 * lam ≤ R) (hR1 : R ≤ 1)
    (hK : (1 + Real.log |Real.log lam| + Real.log (1 / R)) / |Real.log lam|
      ≤ 5 * ω lam) (hω0 : 0 ≤ ω lam) (hω1 : ω lam ≤ 1) :
    gibbsMeasure N β lam
        {Z | M * N * Real.sqrt (ω lam) / 2 < (longIsolatedDipoles Z R).card}
      ≤ ENNReal.ofReal (Real.exp ((C + 1) * Real.log (N + 1) - M / 4 * N * ω lam)) := by
  classical
  set w := ω lam with hw
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set S : Finset ℕ := (Finset.range (N + 1)).filter
    (fun p => M * N * Real.sqrt w / 2 < (p : ℝ)) with hS
  have hsub : {Z : Fin N ⊕ Fin N → ℂ | M * N * Real.sqrt w / 2 < (longIsolatedDipoles Z R).card}
      ⊆ ⋃ p ∈ S, {Z | (longIsolatedDipoles Z R).card = p} := by
    intro Z hZ
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨(longIsolatedDipoles Z R).card, Finset.mem_filter.2
      ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (longIsolatedDipoles_card_le Z R)), hZ⟩, rfl⟩
  have hbound : ∀ p ∈ S, gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p} ≤
      ENNReal.ofReal (Real.exp (C * Real.log (N + 1) - M / 4 * N * w)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    refine (hb3 N hN lam h0 h1 R hR hR1 p (Nat.lt_succ_iff.1 (Finset.mem_range.1 hp1))).trans ?_
    rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := exponent_b3_le (C := C) (K := 5) hC.le (by norm_num) (by linarith) hN0.le hω0 hω1 hK
      hp2
    linarith only [this]
  refine (measure_le_card_mul_of_subset_biUnion _ _ S _ hsub hbound).trans ?_
  have hcard : S.card ≤ N + 1 := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  calc (S.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (C * Real.log (N + 1) - M / 4 * N * w))
      ≤ ((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (C * Real.log (N + 1) - M / 4 * N * w)) :=
        mul_le_mul_left (by exact_mod_cast hcard) _
    _ = ENNReal.ofReal (Real.exp (Real.log ((N : ℝ) + 1) +
          (C * Real.log (N + 1) - M / 4 * N * w))) := natCast_succ_mul_ofReal_exp N _
    _ = _ := by
        congr 2
        ring

/-! ### The event `A_M` and (eq:PAM) -/

/-- The event `A_M = {N - ½|I^dip| + D_{R₀} ≤ M N √ω(λ)}` of Step 5 for a general rate function
`ω` (source l. 2061–2068), with `R₀ = R0Rate β ω λ`. -/
def eventARate (β : ℝ) (ω : ℝ → ℝ) (N : ℕ) (lam M : ℝ) : Set (Fin N ⊕ Fin N → ℂ) :=
  {Z | (N : ℝ) - (isolatedDipoles Z).card + (longIsolatedDipoles Z (R0Rate β ω lam)).card
    ≤ M * N * Real.sqrt (ω lam)}

/-- The complement of `A_M` is contained in the union of the deficit event and the long-dipole
event, each with half of the budget `M N √ω` (source: "a union bound"), for a general rate
function `ω`. -/
theorem eventARate_compl_subset (β : ℝ) (ω : ℝ → ℝ) (N : ℕ) (lam M : ℝ) :
    (eventARate β ω N lam M)ᶜ ⊆
      {Z | M * N * Real.sqrt (ω lam) / 2 < N - (isolatedDipoles Z).card} ∪
        {Z | M * N * Real.sqrt (ω lam) / 2 <
          (longIsolatedDipoles Z (R0Rate β ω lam)).card} := by
  intro Z hZ
  simp only [eventARate, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hZ
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  by_contra h
  push Not at h
  linarith [h.1, h.2]

/-- **(eq:PAM) for a general rate function `ω`** (source l. 2070–2072): if
`ω` has the rate properties `Theorem2RateHyp β hβ ω`, then for `M` large and `λ` small,
`ℙ(A_Mᶜ) ≤ 2 (N+1)^{C} e^{-c M N ω(λ)}`. The hypotheses `hb1`, `hb2`, `hb3` are the three
clauses of Theorem 1 used in Step 5, stated with `ω` (as in `Theorem1ShapeRate`): (b1), (b2) for
`β > 2`, and the critical-lengths bound for `β = 2`. -/
theorem exists_gibbsMeasure_eventARate_compl_le (β : ℝ) (hβ : 2 ≤ β) (ω : ℝ → ℝ)
    (hω : Theorem2RateHyp β hβ ω) {lam₀ : ℝ} (hlam₀ : 0 < lam₀)
    (hb1 : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ p₀ : ℕ, p₀ ≤ N →
        gibbsMeasure N β lam {Z | (isolatedDipoles Z).card = p₀}
          ≤ ENNReal.ofReal (Real.exp (-c * N * (1 - (p₀ : ℝ) / N) ^ 2
            + C * N * ω lam + C * Real.log (N + 1))))
    (hb2 : 2 < β → ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, p₀' ≤ N →
          c * (lam / R) ^ (β - 2) ≤ (p₀' : ℝ) / N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (Real.exp
                (-C₁ * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) / (lam / R) ^ (β - 2))
                  + C₂ * N * Real.sqrt (ω lam) + C₂ * Real.log (N + 1))))
    (hb3 : β = 2 → ∃ C lam₃ : ℝ, 0 < C ∧ 0 < lam₃ ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₃ →
        ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 → ∀ p₀' : ℕ, p₀' ≤ N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (((N : ℝ) + 1) ^ C * Real.exp (-(p₀' : ℝ) + C * N *
                (ω lam
                  + (1 + Real.log |Real.log lam| + Real.log (1 / R)) / |Real.log lam|)))) :
    ∃ lamA MA CA cA : ℝ, 0 < lamA ∧ lamA ≤ Real.exp (-1) ∧ 0 < MA ∧ 0 < CA ∧ 0 < cA ∧
      ∀ M : ℝ, MA ≤ M → ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamA →
        gibbsMeasure N β lam (eventARate β ω N lam M)ᶜ
          ≤ ENNReal.ofReal (2 * Real.exp (CA * Real.log (N + 1)
            - cA * M * N * ω lam)) := by
  obtain ⟨lamR, hlamR, hlamRe, hreg⟩ := exists_R0Rate_regime hβ hω.pos hω.le_rpow hω.rpow_le
    hω.two_mul_le_rpow_quarter hω.log_div_le
  obtain ⟨C, c, hC, hc, hb1'⟩ := hb1
  by_cases h2 : β = 2
  · obtain ⟨C₃, lam₃, hC₃, hlam₃, hb3'⟩ := hb3 h2
    refine ⟨min (min lam₀ lam₃) lamR, max (max 1 (4 * (C + 1) / c)) (24 * C₃),
      max (C + 1) (C₃ + 1), 1 / 4, lt_min (lt_min hlam₀ hlam₃) hlamR,
      (min_le_right _ _).trans hlamRe, lt_of_lt_of_le one_pos
        ((le_max_left _ _).trans (le_max_left _ _)), lt_of_lt_of_le (by linarith) (le_max_left _ _),
      by norm_num, fun M hM N hN lam h0 hlt => ?_⟩
    have hl0 : lam < lam₀ := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_left _ _))
    have hl3 : lam < lam₃ := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_right _ _))
    have hlR : lam < lamR := lt_of_lt_of_le hlt (min_le_right _ _)
    have hle : lam < Real.exp (-1) := lt_of_lt_of_le hlR hlamRe
    have hω0 := hω.pos lam h0 hle
    have hω1 := hω.le_one lam h0 hle
    obtain ⟨hR2, hR4, -, hK⟩ := hreg lam h0 hlR
    have hR1 : R0Rate β ω lam ≤ 1 := le_one_of_le_rpow_quarter hω0.le hω1 hR4
    have hM1 : 1 ≤ M := (le_max_left _ _).trans ((le_max_left _ _).trans hM)
    have hMc : 4 * (C + 1) / c ≤ M := (le_max_right _ _).trans ((le_max_left _ _).trans hM)
    have hM3 : 24 * C₃ ≤ M := (le_max_right _ _).trans hM
    have hE1 := gibbsMeasure_isolatedDipoles_deficit_le_rate β ω hC hc
      (fun N hN lam h0 h1 p hp => hb1' N hN lam h0 h1 p hp) hM1 hMc hN h0 hl0 hω0.le
    have hE2 := gibbsMeasure_longIsolatedDipoles_le_of_eq_two_rate β ω hC₃ hb3' hM3 hN h0 hl3 hR2
      hR1 (hK h2) hω0.le hω1
    refine measure_le_two_mul_of_subset_union _ (eventARate_compl_subset β ω N lam M) hE1 hE2 ?_ ?_
    · have hL : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith)
      have hP : 0 ≤ M * N * ω lam := by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have : 0 ≤ M := by linarith
        positivity
      have := le_max_left (C + 1) (C₃ + 1)
      linarith only [mul_nonneg hL (sub_nonneg.2 this), hP]
    · have hL : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith)
      have := le_max_right (C + 1) (C₃ + 1)
      linarith only [mul_nonneg hL (sub_nonneg.2 this)]
  · have h2' : 2 < β := lt_of_le_of_ne hβ (Ne.symm h2)
    obtain ⟨c', C₁, C₂, hc', hC₁, hC₂, hb2'⟩ := hb2 h2'
    refine ⟨min lam₀ lamR,
      max (max (max 1 (4 * (C + 1) / c)) (max (2 * Real.exp 1) (2 * c'))) (4 * C₂ / C₁),
      max (C + 1) (C₂ + 1), min 1 (C₁ / 4), lt_min hlam₀ hlamR,
      (min_le_right _ _).trans hlamRe, lt_of_lt_of_le one_pos
        ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))),
      lt_of_lt_of_le (by linarith) (le_max_left _ _), lt_min one_pos (by positivity),
      fun M hM N hN lam h0 hlt => ?_⟩
    have hl0 : lam < lam₀ := lt_of_lt_of_le hlt (min_le_left _ _)
    have hlR : lam < lamR := lt_of_lt_of_le hlt (min_le_right _ _)
    have hle : lam < Real.exp (-1) := lt_of_lt_of_le hlR hlamRe
    have hω0 := hω.pos lam h0 hle
    have hω1 := hω.le_one lam h0 hle
    obtain ⟨hR2, hR4, hRa, -⟩ := hreg lam h0 hlR
    have hM1 : 1 ≤ M := (le_max_left _ _).trans ((le_max_left _ _).trans
      ((le_max_left _ _).trans hM))
    have hMc : 4 * (C + 1) / c ≤ M := (le_max_right _ _).trans ((le_max_left _ _).trans
      ((le_max_left _ _).trans hM))
    have hMe : 2 * Real.exp 1 ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_left _ _).trans hM))
    have hMc' : 2 * c' ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_left _ _).trans hM))
    have hM3 : 4 * C₂ / C₁ ≤ M := (le_max_right _ _).trans hM
    have hE1 := gibbsMeasure_isolatedDipoles_deficit_le_rate β ω hC hc
      (fun N hN lam h0 h1 p hp => hb1' N hN lam h0 h1 p hp) hM1 hMc hN h0 hl0 hω0.le
    have hE2 := gibbsMeasure_longIsolatedDipoles_le_of_two_lt_rate β ω hC₁ hb2' hMe hMc' hM3 hN h0
      hl0 hR2 (hRa h2') hω0 hω1
    refine measure_le_two_mul_of_subset_union _ (eventARate_compl_subset β ω N lam M) hE1 hE2 ?_ ?_
    · have hL : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith)
      have hP : 0 ≤ M * N * ω lam := by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have : 0 ≤ M := by linarith
        positivity
      have h1 := le_max_left (C + 1) (C₂ + 1)
      have h3 := min_le_left 1 (C₁ / 4)
      linarith only [mul_nonneg hL (sub_nonneg.2 h1), mul_nonneg hP (sub_nonneg.2 h3)]
    · have hL : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith)
      have hP : 0 ≤ M * N * ω lam := by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have : 0 ≤ M := by linarith
        positivity
      have h1 := le_max_right (C + 1) (C₂ + 1)
      have h3 := min_le_right 1 (C₁ / 4)
      linarith only [mul_nonneg hL (sub_nonneg.2 h1), mul_nonneg hP (sub_nonneg.2 h3)]

end TwoComponentCoulomb

end
