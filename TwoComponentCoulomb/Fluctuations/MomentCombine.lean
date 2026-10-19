/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.ElectricLower
public import TwoComponentCoulomb.Fluctuations.MomentA2
public import TwoComponentCoulomb.Fluctuations.Theorem2Assembly
import TwoComponentCoulomb.Fluctuations.CriticalElectric
import TwoComponentCoulomb.Fluctuations.MomentA1
import TwoComponentCoulomb.Fluctuations.MomentA3
import TwoComponentCoulomb.Gibbs.Basic
import TwoComponentCoulomb.Gibbs.Generic
import TwoComponentCoulomb.UpperBound.MarkedCells
import TwoComponentCoulomb.UpperBound.PairBlocks
import TwoComponentCoulomb.UpperBound.UpperAssembly
import TwoComponentCoulomb.UpperBound.UpperRate

/-!
# Theorem 2, Step 6: the Hölder combination of (eq:A1), (eq:A2), (eq:finalA3)

Source: proof of Theorem 2 (`prop:linear`), Step 6, l. 2212--2219 ("Hölder's inequality with
three factors and `𝔼[e^{sX}] ≤ (𝔼[e^{rX}])^{s/r}` give the following bound from (eq:A1), (eq:A2)
and (eq:finalA3)"), and the statement of `MomentBoundRate` (`Fluctuations/Theorem2Assembly.lean`).

Write `A₁, A₂, A₃` for `linearA1, linearA2, linearA3` (`Fluctuations/ElectricLower.lean`) and
`Q = ∫ |∇h_α|²`. By Step 2 (`exists_integral_norm_sq_electricField_le_linearA`) there is `C_A` with
`Q/(4π) ≤ A₁ + C_A (A₂ + A₃)` for generic configurations. Fix `c > 0` with `12π c ≤ β` and
`12π c C_A ≤ 1`. Then, almost surely, `c Q ≤ a + b + d` with `a = 4πc A₁`, `b = 4πc C_A A₂`,
`d = 4πc C_A A₃`, and `e^{a+b+d} ≤ e^{3a} + e^{3b} + e^{3d}` (the elementary replacement of
Hölder's inequality with three factors: `a + b + d ≤ 3 max (a, b, d)`). The three exponential
moments are

* `𝔼[e^{12πc A₁}] ≤ 1 + 𝔼[e^{β A₁}]` (as `12π c ≤ β`, `e^{s x} ≤ 1 + e^{r x}` for `0 ≤ s ≤ r`: the
  elementary replacement of Jensen's inequality, the Gibbs measure being a probability measure),
* `𝔼[e^{12πc C_A A₂}] ≤ 1 + 𝔼[e^{A₂}]` (as `12π c C_A ≤ 1`),
* `𝔼[e^{12πc C_A A₃}]`, directly (eq:finalA3 with `t = 12π c C_A`),

bounded by (eq:A1), (eq:A2) (`momentA2_le_rate`) and (eq:finalA3). (The source fixes `t = 1` in
(eq:finalA3) and lowers the exponent by `𝔼[e^{sX}] ≤ (𝔼[e^{rX}])^{s/r}`; here (eq:finalA3) is used
directly at `t = 12π c C_A`.)

The results are stated for a rate function `ω` satisfying `UpperRateHyp` in place of `ω_λ`, with
conclusion `MomentBoundRate β hβ.le ω` (`Fluctuations/Theorem2Assembly.lean`); the instance
`ω = errorRate β` is `momentBound_of_two_lt` (`Fluctuations/Moment.lean`).

## Main results

* `MomentCombine.measurable_linearA2`, `MomentCombine.measurable_linearA3`: `A₂, A₃` are
  measurable functions of the configuration (so that integrals of sums split).
* `MomentCombine.lintegral_exp_add_le`, `MomentCombine.lintegral_exp_mul_le_one_add`: the
  elementary replacements of Hölder's and Jensen's inequalities.
* `momentBound_of_moments_rate`: `MomentBoundRate β _ ω` from the exponential moments (eq:A1),
  (eq:finalA3) (hypotheses) and (eq:A2) (`momentA2_le_rate`). This is a conditional helper.
* `momentBound_of_two_lt_rate`: `MomentBoundRate β hβ.le ω` for `β > 2`, from `momentA1_le_rate`
  and `momentA3_le_rate`.
-/

@[expose] public section

namespace TwoComponentCoulomb

namespace MomentCombine

open Finset MeasureTheory
open scoped ENNReal

variable {N : ℕ}

/-! ### Measurability of `A₂` and `A₃` -/

section Measurability

open scoped Classical in
/-- A sum over a measurably varying index set is measurable. -/
theorem measurable_sum_filter {P : (Fin N ⊕ Fin N → ℂ) → Fin N ⊕ Fin N → Prop}
    [inst : ∀ Z, DecidablePred (P Z)]
    {f : (Fin N ⊕ Fin N → ℂ) → Fin N ⊕ Fin N → ℝ}
    (hP : ∀ i, MeasurableSet {Z | P Z i}) (hf : ∀ i, Measurable fun Z => f Z i) :
    Measurable fun Z => ∑ i ∈ Finset.univ.filter (P Z), f Z i := by
  simp only [Finset.sum_filter]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite (hP i) (hf i) measurable_const

theorem measurableSet_isIsolatedDipole_secondNearestNeighbor (hN : 2 ≤ N) (i : Fin N ⊕ Fin N) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | IsIsolatedDipole Z (secondNearestNeighbor hN Z i)} := by
  have hset : {Z : Fin N ⊕ Fin N → ℂ | IsIsolatedDipole Z (secondNearestNeighbor hN Z i)} =
      ⋃ j, {Z | secondNearestNeighbor hN Z i = j} ∩ {Z | IsIsolatedDipole Z j} := by
    ext Z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨j, hj, h⟩ => hj ▸ h⟩
  rw [hset]
  exact MeasurableSet.iUnion fun j =>
    (measurableSet_secondNearestNeighbor_eq hN i j).inter (measurableSet_isIsolatedDipole j)

/-- The second-neighbour radius `r̃₂(zᵢ)` is a measurable function of the configuration. -/
theorem measurable_secondNeighborRadius_apply (hN : 2 ≤ N) (lam : ℝ) (i : Fin N ⊕ Fin N) :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => secondNeighborRadius hN lam Z i := by
  have hNpos : 0 < N := by omega
  have : Nontrivial (Fin N ⊕ Fin N) :=
    ⟨⟨Sum.inl ⟨0, hNpos⟩, Sum.inr ⟨0, hNpos⟩, Sum.inl_ne_inr⟩⟩
  have h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N) := by
    rw [Fintype.card_sum, Fintype.card_fin]; omega
  have e : (fun Z : Fin N ⊕ Fin N → ℂ => secondNeighborRadius hN lam Z i) =
      fun Z => nnRadius2 h3 (sumKey N) lam Z i :=
    funext fun Z => secondNeighborRadius_eq_nnRadius2 hN h3 lam Z i
  rw [e]
  exact measurable_nnRadius2 (sumKey N) h3 lam i

open scoped Classical in
/-- The index set of the sums defining `A₂` and `A₃` is measurable: the events
`{i ∈ I^dip, φ₂ i ∈ I^dip, φ₂ (φ₁ i) ∈ I^pair}`. -/
theorem measurableSet_dipIndex (hN : 2 ≤ N) (i : Fin N ⊕ Fin N) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | IsIsolatedDipole Z i ∧
      IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))} :=
  (measurableSet_isIsolatedDipole i).inter
    ((measurableSet_isIsolatedDipole_secondNearestNeighbor hN i).inter
      (measurableSet_isIsolatedPair_secondNearestNeighbor_nearestNeighbor hN i))

open scoped Classical in
/-- `A₂` is a measurable function of the configuration. -/
theorem measurable_linearA2 (hN : 2 ≤ N) (lam : ℝ) :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => linearA2 hN lam Z := by
  unfold linearA2
  refine Measurable.add ?_ (measurable_const.sub (measurable_const.mul ?_))
  · refine measurable_sum_filter (P := fun Z i => IsIsolatedDipole Z i ∧
      IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)))
      (fun i => measurableSet_dipIndex hN i) fun i => ?_
    exact ((measurable_firstNeighborRadius_apply hN lam i).div
      (measurable_secondNeighborRadius_apply hN lam i)).pow_const 2
  · have e : (fun Z : Fin N ⊕ Fin N → ℂ =>
        ((Finset.univ.filter (IsIsolatedDipole Z)).card : ℝ)) =
        fun Z => ((2 * (isolatedDipoles Z).card : ℕ) : ℝ) :=
      funext fun Z => by rw [card_filter_isIsolatedDipole Z]
    rw [e]
    exact (measurable_of_countable (fun n : ℕ => ((2 * n : ℕ) : ℝ))).comp
      (measurable_card_isolatedDipoles (N := N))

open scoped Classical in
/-- `A₃` is a measurable function of the configuration. -/
theorem measurable_linearA3 (hN : 2 ≤ N) (lam γ : ℝ) :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => linearA3 hN lam γ Z := by
  unfold linearA3
  refine measurable_sum_filter (P := fun Z i => IsIsolatedDipole Z i ∧
      IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)))
      (fun i => measurableSet_dipIndex hN i) fun i => ?_
  exact (((measurable_firstNeighborRadius_apply hN lam i).div_const γ).pow_const 2).min
    measurable_const

end Measurability

/-! ### The Gibbs measure: genericity and total mass -/

section GibbsMeasure

/-- The Gibbs measure is absolutely continuous with respect to Lebesgue measure. -/
theorem gibbsMeasure_absolutelyContinuous (N : ℕ) (β lam : ℝ) :
    gibbsMeasure N β lam ≪ (volume : Measure (Fin N ⊕ Fin N → ℂ)) := by
  unfold gibbsMeasure
  exact Measure.AbsolutelyContinuous.smul_left
    ((withDensity_absolutelyContinuous _ _).trans Measure.restrict_le_self.absolutelyContinuous) _

/-- Almost every configuration is generic for the Gibbs measure. -/
theorem ae_isGeneric_gibbsMeasure (N : ℕ) (β lam : ℝ) :
    ∀ᵐ Z ∂gibbsMeasure N β lam, IsGeneric Z :=
  ae_isGeneric_of_absolutelyContinuous (gibbsMeasure_absolutelyContinuous N β lam)

/-- For `β > 2`, the Gibbs measure is a probability measure for `N ≥ 2` and `λ` small
(`0 < Z < ∞`, by the upper bound (ubz) of Proposition 3.10). -/
theorem exists_isProbabilityMeasure_gibbsMeasure {β : ℝ} (hβ : 2 < β) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      IsProbabilityMeasure (gibbsMeasure N β lam) := by
  obtain ⟨lam₀, hlam₀, C, c, hC, hc, h⟩ := UpperAssembly.proposition_3_10_main_of_two_lt hβ
  refine ⟨lam₀, hlam₀, fun N hN lam hlam hlamlt => ?_⟩
  exact isProbabilityMeasure_gibbsMeasure (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (h N hN lam hlam hlamlt).1) (by omega)

end GibbsMeasure

/-! ### The elementary replacements of Hölder's and Jensen's inequalities -/

section Elementary

/-- `e^{a+b+d} ≤ e^{3a} + e^{3b} + e^{3d}`, since `a + b + d ≤ 3 max (a, b, d)`. -/
theorem exp_add_add_le {a b d : ℝ} :
    Real.exp (a + b + d) ≤ Real.exp (3 * b) + Real.exp (3 * d) + Real.exp (3 * a) := by
  have h : a + b + d ≤ 3 * a ∨ a + b + d ≤ 3 * b ∨ a + b + d ≤ 3 * d := by
    by_contra h
    push Not at h
    linarith [h.1, h.2.1, h.2.2]
  have ha := Real.exp_pos (3 * a)
  have hb := Real.exp_pos (3 * b)
  have hd := Real.exp_pos (3 * d)
  rcases h with h | h | h
  · linarith [Real.exp_le_exp.2 h]
  · linarith [Real.exp_le_exp.2 h]
  · linarith [Real.exp_le_exp.2 h]

/-- **Hölder with three factors, in the elementary form** (source l. 2212--2216): if
`Q ≤ a + b + d` almost everywhere, with `b, d` measurable, then
`∫ e^Q ≤ ∫ e^{3a} + ∫ e^{3b} + ∫ e^{3d}`. -/
theorem lintegral_exp_add_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {Q a b d : X → ℝ}
    (hb : Measurable b) (hd : Measurable d) (h : ∀ᵐ x ∂μ, Q x ≤ a x + b x + d x) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (Q x)) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp (3 * a x)) ∂μ + ∫⁻ x, ENNReal.ofReal (Real.exp (3 * b x)) ∂μ
        + ∫⁻ x, ENNReal.ofReal (Real.exp (3 * d x)) ∂μ := by
  have hmb : Measurable fun x => ENNReal.ofReal (Real.exp (3 * b x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hb.const_mul 3))
  have hmd : Measurable fun x => ENNReal.ofReal (Real.exp (3 * d x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hd.const_mul 3))
  calc _ ≤ ∫⁻ x, (ENNReal.ofReal (Real.exp (3 * b x)) + ENNReal.ofReal (Real.exp (3 * d x))
        + ENNReal.ofReal (Real.exp (3 * a x))) ∂μ := by
        refine lintegral_mono_ae (h.mono fun x hx => ?_)
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal
          ((Real.exp_le_exp.2 hx).trans exp_add_add_le)
    _ = _ := by
        have hmbd : Measurable fun x => ENNReal.ofReal (Real.exp (3 * b x)) +
            ENNReal.ofReal (Real.exp (3 * d x)) := hmb.add hmd
        rw [lintegral_add_left hmbd, lintegral_add_left hmb]
        ring

/-- **Jensen's inequality, in the elementary form** (source l. 2213--2215, "`𝔼[e^{sX}] ≤
(𝔼[e^{rX}])^{s/r}`"): for a probability measure and `0 ≤ s ≤ r`, `e^{s x} ≤ 1 + e^{r x}` gives
`∫ e^{s A} ≤ 1 + ∫ e^{r A}`. -/
theorem lintegral_exp_mul_le_one_add {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] (A : X → ℝ) {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (s * A x)) ∂μ ≤
      1 + ∫⁻ x, ENNReal.ofReal (Real.exp (r * A x)) ∂μ := by
  calc _ ≤ ∫⁻ x, (1 + ENNReal.ofReal (Real.exp (r * A x))) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rcases le_total 0 (A x) with hx | hx
        · have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hsr hx)
          linarith
        · have : s * A x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs hx
          have := Real.exp_le_one_iff.2 this
          linarith [Real.exp_pos (r * A x)]
    _ = _ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- The real inequality closing the combination: the three exponential moments `1 + e^{R₁}`,
`1 + e^{R₂}`, `e^{R₃}` are at most `e^R` for `R = C (N (φ + ω) + L)`, `C = C₁ + C₂ + C₃ + 2`,
as soon as `5 ≤ e^{2L}` (here `L = log (N+1)`, `N ≥ 2`). -/
theorem add_exp_le_exp {C₁ C₂ C₃ N φ ω L : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hN : 0 ≤ N) (hφ : 0 ≤ φ) (hω : 0 ≤ ω) (hL : 0 ≤ L) (h5 : 5 ≤ Real.exp (2 * L)) :
    (1 + Real.exp (C₁ * N * (φ + ω) + C₁ * L)) + (1 + Real.exp (C₂ * N * ω + C₂ * L))
        + Real.exp (C₃ * N * (φ + ω) + C₃ * L) ≤
      Real.exp ((C₁ + C₂ + C₃ + 2) * N * (φ + ω) + (C₁ + C₂ + C₃ + 2) * L) := by
  have hNφ : 0 ≤ N * φ := mul_nonneg hN hφ
  have hNω : 0 ≤ N * ω := mul_nonneg hN hω
  set R : ℝ := (C₁ + C₂ + C₃ + 2) * N * (φ + ω) + (C₁ + C₂ + C₃ + 2) * L - 2 * L with hR
  have hR1 : C₁ * N * (φ + ω) + C₁ * L ≤ R := by
    rw [hR]
    linarith only [mul_nonneg (add_nonneg hC₂ hC₃) hNφ, mul_nonneg (add_nonneg hC₂ hC₃) hNω,
      mul_nonneg (add_nonneg hC₂ hC₃) hL, hNφ, hNω]
  have hR2 : C₂ * N * ω + C₂ * L ≤ R := by
    rw [hR]
    linarith only [mul_nonneg (add_nonneg hC₁ hC₃) hNω, mul_nonneg (add_nonneg hC₁ hC₃) hL,
      mul_nonneg (add_nonneg hC₁ (add_nonneg hC₂ hC₃)) hNφ, hNφ, hNω]
  have hR3 : C₃ * N * (φ + ω) + C₃ * L ≤ R := by
    rw [hR]
    linarith only [mul_nonneg (add_nonneg hC₁ hC₂) hNφ, mul_nonneg (add_nonneg hC₁ hC₂) hNω,
      mul_nonneg (add_nonneg hC₁ hC₂) hL, hNφ, hNω]
  have hR0 : 0 ≤ R := by
    linarith only [hR1, mul_nonneg hC₁ hNφ, mul_nonneg hC₁ hNω, mul_nonneg hC₁ hL]
  have e1 := Real.exp_le_exp.2 hR1
  have e2 := Real.exp_le_exp.2 hR2
  have e3 := Real.exp_le_exp.2 hR3
  have e0 : 1 ≤ Real.exp R := Real.one_le_exp hR0
  have eR : Real.exp ((C₁ + C₂ + C₃ + 2) * N * (φ + ω) + (C₁ + C₂ + C₃ + 2) * L) =
      Real.exp R * Real.exp (2 * L) := by
    rw [← Real.exp_add]
    congr 1
    rw [hR]
    ring
  rw [eR]
  linarith only [e1, e2, e3, e0, mul_le_mul_of_nonneg_left h5 (Real.exp_pos R).le]

end Elementary

end MomentCombine

open MeasureTheory
open scoped ENNReal

/-- **Theorem 2, Step 6: the exponential moment of the electric energy for `β > 2`, generic rate**
(source l. 2212--2219), a *conditional helper*, for a rate `ω` satisfying `UpperRateHyp` in place
of `ω_λ`. The exponential moments (eq:A1) and
(eq:finalA3) with `ω` are hypotheses (they are the statements of `momentA1_le_rate` and
`momentA3_le_rate`), and (eq:A2) with `ω` is `momentA2_le_rate`. The conclusion is
`MomentBoundRate β _ ω`, with the radii `αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)` (`alphaRadius`); besides the three
moments, only `ω ≥ 0` (the field `UpperRateHyp.nonneg`) is used. -/
theorem momentBound_of_moments_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) (hω : UpperRateHyp β hβ ω)
    (hA1 : ∀ C_A : ℝ, ∃ C lam₁ : ℝ, 0 < C ∧ 0 < lam₁ ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam < lam₁ → ∀ γ : ℝ, 2 * lam ≤ γ → γ ≤ 1 →
        ∫⁻ Z, ENNReal.ofReal (Real.exp (β * linearA1 hN lam γ C_A Z)) ∂gibbsMeasure N β lam ≤
          ENNReal.ofReal (Real.exp (C * N * (isolatedPhi β hβ.le lam γ + ω lam)
            + C * Real.log (N + 1))))
    (hA3 : ∀ t : ℝ, 0 < t → ∃ C lam₁ : ℝ, 0 < C ∧ 0 < lam₁ ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam < lam₁ → ∀ γ : ℝ, 2 * lam ≤ γ → γ ≤ 1 →
        ∫⁻ Z, ENNReal.ofReal (Real.exp (t * linearA3 hN lam γ Z)) ∂gibbsMeasure N β lam ≤
          ENNReal.ofReal (Real.exp (C * N * (isolatedPhi β hβ.le lam γ + ω lam)
            + C * Real.log (N + 1)))) :
    MomentBoundRate β hβ.le ω := by
  obtain ⟨C_A, hCA, hstep2⟩ := exists_integral_norm_sq_electricField_le_linearA
  -- the choice of `c`: `12π c ≤ β` and `12π c C_A ≤ 1`
  have hπ : 0 < Real.pi := Real.pi_pos
  have hβ0 : 0 < β := by linarith
  set c : ℝ := min (β / (12 * Real.pi)) (1 / (12 * Real.pi * C_A)) with hcdef
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hc1 : 12 * Real.pi * c ≤ β := by
    have := min_le_left (β / (12 * Real.pi)) (1 / (12 * Real.pi * C_A))
    rw [← hcdef] at this
    calc 12 * Real.pi * c ≤ 12 * Real.pi * (β / (12 * Real.pi)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = β := by field_simp
  have hc2 : 12 * Real.pi * c * C_A ≤ 1 := by
    have := min_le_right (β / (12 * Real.pi)) (1 / (12 * Real.pi * C_A))
    rw [← hcdef] at this
    calc 12 * Real.pi * c * C_A ≤ 12 * Real.pi * (1 / (12 * Real.pi * C_A)) * C_A :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity)) hCA.le
      _ = 1 := by field_simp
  set t : ℝ := 12 * Real.pi * c * C_A with htdef
  have ht : 0 < t := by positivity
  obtain ⟨C₁, lam₁₁, hC₁, hlam₁₁, h1⟩ := hA1 C_A
  obtain ⟨C₃, lam₁₃, hC₃, hlam₁₃, h3⟩ := hA3 t ht
  obtain ⟨C₂, lam₁₂, hC₂, hlam₁₂, h2⟩ := momentA2_le_rate hβ ω hω
  obtain ⟨lam₁₄, hlam₁₄, hprob⟩ := MomentCombine.exists_isProbabilityMeasure_gibbsMeasure hβ
  have hα : ∀ (N : ℕ) (hN : 2 ≤ N) (lam γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ),
      (fun i => if h : 2 ≤ N then alphaRadius h lam γ Z i else γ) = alphaRadius hN lam γ Z :=
    fun N hN lam γ Z => funext fun i => dite_eq_left hN
  refine ⟨fun N lam γ Z i => if h : 2 ≤ N then alphaRadius h lam γ Z i else γ, c,
    C₁ + C₂ + C₃ + 2, min (min lam₁₁ lam₁₂) (min lam₁₃ lam₁₄), hc, by positivity,
    lt_min (lt_min hlam₁₁ hlam₁₂) (lt_min hlam₁₃ hlam₁₄), ?_, ?_, ?_⟩
  · intro N hN lam γ hlam _ _ _ Z i
    simp only [dite_eq_left hN]
    exact ⟨alphaRadius_pos hN hlam γ Z i, alphaRadius_le_max hN lam γ Z i⟩
  · intro N hN lam γ hlam _ _ _
    simp only [hα N hN]
    exact (measurable_integral_norm_sq_electricField_alphaRadius hN lam γ).aemeasurable
  · intro N hN lam γ hlam hlamlt hγ hγ1
    simp only [hα N hN]
    have hl11 : lam < lam₁₁ :=
      hlamlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hl12 : lam < lam₁₂ :=
      hlamlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hl13 : lam < lam₁₃ :=
      hlamlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hl14 : lam < lam₁₄ :=
      hlamlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have := hprob N hN lam hlam hl14
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hlogN : 0 ≤ Real.log (N + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
    have hω0 : 0 ≤ ω lam := hω.nonneg lam hlam
    have hφ0 : 0 ≤ isolatedPhi β hβ.le lam γ := isolatedPhi_nonneg hβ.le hlam (by linarith)
    set μ := gibbsMeasure N β lam with hμ
    set A₁ : (Fin N ⊕ Fin N → ℂ) → ℝ := fun Z => linearA1 hN lam γ C_A Z with hA₁
    set A₂ : (Fin N ⊕ Fin N → ℂ) → ℝ := fun Z => linearA2 hN lam Z with hA₂
    set A₃ : (Fin N ⊕ Fin N → ℂ) → ℝ := fun Z => linearA3 hN lam γ Z with hA₃
    set Q : (Fin N ⊕ Fin N → ℂ) → ℝ :=
      fun Z => ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2 with hQ
    -- Step 2 almost everywhere: `c Q ≤ 4π c A₁ + 4π c C_A A₂ + 4π c C_A A₃`
    have hae : ∀ᵐ Z ∂μ, c * Q Z ≤ 4 * Real.pi * c * A₁ Z + 4 * Real.pi * c * C_A * A₂ Z
        + 4 * Real.pi * c * C_A * A₃ Z := by
      refine (MomentCombine.ae_isGeneric_gibbsMeasure N β lam).mono fun Z hZ => ?_
      have h := hstep2 N hN lam γ hlam hγ hγ1 Z hZ
      have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 4 * Real.pi * c)
      have e : 4 * Real.pi * c * (1 / (4 * Real.pi) * Q Z) = c * Q Z := by field_simp
      simp only [hA₁, hA₂, hA₃]
      linarith only [h', e]
    have hmain := MomentCombine.lintegral_exp_add_le (μ := μ) (Q := fun Z => c * Q Z)
      (a := fun Z => 4 * Real.pi * c * A₁ Z) (b := fun Z => 4 * Real.pi * c * C_A * A₂ Z)
      (d := fun Z => 4 * Real.pi * c * C_A * A₃ Z)
      ((MomentCombine.measurable_linearA2 hN lam).const_mul _)
      ((MomentCombine.measurable_linearA3 hN lam γ).const_mul _) hae
    -- the three exponential moments
    have hT₁ : ∫⁻ Z, ENNReal.ofReal (Real.exp (3 * (4 * Real.pi * c * A₁ Z))) ∂μ ≤
        1 + ENNReal.ofReal (Real.exp (C₁ * N * (isolatedPhi β hβ.le lam γ +
          ω lam) + C₁ * Real.log (N + 1))) := by
      have hj := MomentCombine.lintegral_exp_mul_le_one_add (μ := μ) A₁
        (s := 12 * Real.pi * c) (r := β) (by positivity) hc1
      have e : ∀ Z, 3 * (4 * Real.pi * c * A₁ Z) = 12 * Real.pi * c * A₁ Z := fun Z => by ring
      simp only [e]
      exact hj.trans (add_le_add le_rfl (h1 N hN lam hlam hl11 γ hγ hγ1))
    have hT₂ : ∫⁻ Z, ENNReal.ofReal (Real.exp (3 * (4 * Real.pi * c * C_A * A₂ Z))) ∂μ ≤
        1 + ENNReal.ofReal (Real.exp (C₂ * N * ω lam +
          C₂ * Real.log (N + 1))) := by
      have hj := MomentCombine.lintegral_exp_mul_le_one_add (μ := μ) A₂
        (s := t) (r := 1) ht.le hc2
      have e : ∀ Z, 3 * (4 * Real.pi * c * C_A * A₂ Z) = t * A₂ Z := fun Z => by
        rw [htdef]; ring
      simp only [e]
      refine hj.trans (add_le_add le_rfl ?_)
      simpa only [one_mul] using h2 N hN lam hlam hl12
    have hT₃ : ∫⁻ Z, ENNReal.ofReal (Real.exp (3 * (4 * Real.pi * c * C_A * A₃ Z))) ∂μ ≤
        ENNReal.ofReal (Real.exp (C₃ * N * (isolatedPhi β hβ.le lam γ +
          ω lam) + C₃ * Real.log (N + 1))) := by
      have e : ∀ Z, 3 * (4 * Real.pi * c * C_A * A₃ Z) = t * A₃ Z := fun Z => by
        rw [htdef]; ring
      simp only [e]
      exact h3 N hN lam hlam hl13 γ hγ hγ1
    have h5 : (5 : ℝ) ≤ Real.exp (2 * Real.log (N + 1)) := by
      rw [two_mul, Real.exp_add, Real.exp_log (by positivity)]
      have : (3 : ℝ) ≤ N + 1 := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast hN
        linarith only [this]
      linarith only [mul_le_mul this this (by norm_num) (by linarith only [this])]
    have hfin := MomentCombine.add_exp_le_exp hC₁.le hC₂.le hC₃.le hN0 hφ0 hω0 hlogN h5
    refine hmain.trans ?_
    calc _ ≤ (1 + ENNReal.ofReal (Real.exp (C₁ * N * (isolatedPhi β hβ.le lam γ +
            ω lam) + C₁ * Real.log (N + 1)))) +
          (1 + ENNReal.ofReal (Real.exp (C₂ * N * ω lam +
            C₂ * Real.log (N + 1)))) +
          ENNReal.ofReal (Real.exp (C₃ * N * (isolatedPhi β hβ.le lam γ +
            ω lam) + C₃ * Real.log (N + 1))) := by gcongr
      _ = ENNReal.ofReal ((1 + Real.exp (C₁ * N * (isolatedPhi β hβ.le lam γ +
            ω lam) + C₁ * Real.log (N + 1))) +
          (1 + Real.exp (C₂ * N * ω lam + C₂ * Real.log (N + 1))) +
          Real.exp (C₃ * N * (isolatedPhi β hβ.le lam γ +
            ω lam) + C₃ * Real.log (N + 1))) := by
          rw [ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le,
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add zero_le_one (Real.exp_pos _).le,
            ENNReal.ofReal_add zero_le_one (Real.exp_pos _).le, ENNReal.ofReal_one]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hfin

/-- **The moment bound for `β > 2`, generic rate** (the output of Theorem 2, Steps 2--4, and
Step 6, source l. 1995--2219): for a rate `ω` satisfying `UpperRateHyp`,
`momentBound_of_moments_rate` applied to the proved exponential moments `momentA1_le_rate` (eq:A1)
and `momentA3_le_rate` (eq:finalA3) gives `MomentBoundRate β _ ω`. -/
theorem momentBound_of_two_lt_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) (hω : UpperRateHyp β hβ ω) :
    MomentBoundRate β hβ.le ω :=
  momentBound_of_moments_rate hβ ω hω (momentA1_le_rate hβ ω hω)
    fun _ ht => momentA3_le_rate hβ ω hω ht

end TwoComponentCoulomb

end
