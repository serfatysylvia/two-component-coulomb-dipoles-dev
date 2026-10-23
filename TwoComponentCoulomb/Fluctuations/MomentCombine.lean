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
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Theorem 2, Step 6: the Hölder combination of (eq:A1), (eq:A2), (eq:finalA3)

Source `source/dipole-formation.tex`, proof of Theorem 2, Step 6 (l. 2086–2093).
The paper spells out Hölder with three factors and moment interpolation.

Step 2 gives `Q/(4π) ≤ A₁ + C_A (A₂ + A₃)` almost everywhere. Choose `c > 0` with
`12πc ≤ β` and `12πc C_A ≤ 1`. Fix `t = 1` in (eq:finalA3). Interpolation on the
Gibbs probability space gives `𝔼[e^{sA}] ≤ 𝔼[e^{rA}]^{s/r}` for `0 ≤ s ≤ r`.
Hölder with three equal exponents then combines the moments of `A₁`, `A₂` and `A₃`.

* `MomentCombine.lintegral_exp_mul_le_rpow`: the moment interpolation inequality.
* `MomentCombine.lintegral_exp_sum_le_holder`: Hölder with three factors.
* `momentBound_of_moments_rate`: the combination for a rate satisfying `UpperRateHyp`.
  Its moment hypotheses are internal inputs supplied by the proved moment theorems.
* `momentBound_of_two_lt_rate`: the resulting electric moment for `β > 2`.
The unsuffixed declarations specialize the rate to `errorRate`. The instance
uses `errorRate` in `Fluctuations/Moment.lean`.
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
(`0 < Z < ∞`, by the upper bound of Propositions 3.9 and 3.10). -/
theorem exists_isProbabilityMeasure_gibbsMeasure {β : ℝ} (hβ : 2 < β) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      IsProbabilityMeasure (gibbsMeasure N β lam) := by
  obtain ⟨lam₀, hlam₀, C, c, hC, hc, h⟩ := UpperAssembly.proposition_3_9_main_of_two_lt hβ
  refine ⟨lam₀, hlam₀, fun N hN lam hlam hlamlt => ?_⟩
  exact isProbabilityMeasure_gibbsMeasure (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (h N hN lam hlam hlamlt).1) (by omega)

end GibbsMeasure

/-! ### Hölder's inequality and moment interpolation -/

/-- Powers of a positive exponential, in the nonnegative integral convention. -/
theorem ofReal_exp_rpow (x t : ℝ) :
    ENNReal.ofReal (Real.exp x) ^ t = ENNReal.ofReal (Real.exp (t * x)) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm]

/-- **Moment interpolation** (Theorem 2, Step 6): on a probability space,
`𝔼[e^{sA}] ≤ 𝔼[e^{rA}]^{s/r}` for `0 ≤ s ≤ r` and `r > 0`.
Apply Hölder to `(e^{rA})^{s/r}` and the function `1`. -/
theorem lintegral_exp_mul_le_rpow {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {A : X → ℝ} (hA : Measurable A)
    {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (s * A x)) ∂μ ≤
      (∫⁻ x, ENNReal.ofReal (Real.exp (r * A x)) ∂μ) ^ (s / r) := by
  have hp : 0 ≤ s / r := div_nonneg hs hr.le
  have hp1 : s / r ≤ 1 := (div_le_one hr).2 hsr
  have h := ENNReal.lintegral_mul_norm_pow_le
    (μ := μ) (f := fun x => ENNReal.ofReal (Real.exp (r * A x)))
    (g := fun _ => 1) ((hA.const_mul r).exp.ennreal_ofReal.aemeasurable)
    aemeasurable_const hp (sub_nonneg.2 hp1) (by ring : s / r + (1 - s / r) = 1)
  simp only [ENNReal.one_rpow, mul_one, lintegral_const, measure_univ,
    ENNReal.one_rpow] at h
  convert h using 1
  apply lintegral_congr
  intro x
  rw [ofReal_exp_rpow]
  congr 2
  field_simp

/-- **Hölder with three factors** (Theorem 2, Step 6): the exponential of the sum
has integral at most the product of the three cube roots of the moments at triple exponent. -/
theorem lintegral_exp_sum_le_holder {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (A : Fin 3 → X → ℝ) (hA : ∀ i, Measurable (A i)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (∑ i, A i x)) ∂μ ≤
      ∏ i, (∫⁻ x, ENNReal.ofReal (Real.exp (3 * A i x)) ∂μ) ^ (1 / 3 : ℝ) := by
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) (Finset.univ : Finset (Fin 3))
    (f := fun i x => ENNReal.ofReal (Real.exp (3 * A i x)))
    (p := fun _ => (1 / 3 : ℝ))
    (fun i _ => ((hA i).const_mul 3).exp.ennreal_ofReal.aemeasurable)
    (by norm_num) (by intros; norm_num)
  simp only [ofReal_exp_rpow] at h
  convert h using 1
  apply lintegral_congr
  intro x
  simp only [show ∀ i, (1 / 3 : ℝ) * (3 * A i x) = A i x by intro i; ring]
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]

/-- Interpolation followed by an upper bound for the larger exponential moment.
The nonnegative exponent bound allows replacing its power `s/r ≤ 1` by `1`. -/
theorem lintegral_exp_mul_le_exp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {A : X → ℝ} (hA : Measurable A)
    {s r R : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr : 0 < r) (hR : 0 ≤ R)
    (h : ∫⁻ x, ENNReal.ofReal (Real.exp (r * A x)) ∂μ ≤ ENNReal.ofReal (Real.exp R)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (s * A x)) ∂μ ≤ ENNReal.ofReal (Real.exp R) := by
  calc _ ≤ (∫⁻ x, ENNReal.ofReal (Real.exp (r * A x)) ∂μ) ^ (s / r) :=
        lintegral_exp_mul_le_rpow hA hs hsr hr
    _ ≤ ENNReal.ofReal (Real.exp R) ^ (s / r) :=
        ENNReal.rpow_le_rpow h (div_nonneg hs hr.le)
    _ = ENNReal.ofReal (Real.exp (s / r * R)) := ofReal_exp_rpow R (s / r)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
        (mul_le_of_le_one_left hR ((div_le_one hr).2 hsr)))

open scoped Classical in
/-- The first auxiliary energy is measurable, as are its finite graph-defined sums. -/
theorem measurable_linearA1 (hN : 2 ≤ N) (lam γ C : ℝ) :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => linearA1 hN lam γ C Z := by
  have : MeasurableSingletonClass (Fin N ⊕ Fin N) := ⟨fun x => by
    rcases x with a | a <;> simp [measurableSet_sum_iff]⟩
  unfold linearA1
  refine Measurable.sub (Measurable.add (measurable_energy lam) ?_) ?_
  · refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
    exact (measurable_smearedKernel lam).comp
      (by
        let G : (Fin N ⊕ Fin N → ℂ) × (Fin N ⊕ Fin N → Fin N ⊕ Fin N) → ℂ :=
          fun p => p.1 i - p.1 (p.2 i)
        have hG : Measurable G := measurable_from_prod_countable_left fun f => by
          dsimp [G]
          fun_prop
        exact hG.comp (measurable_id.prodMk measurable_nearestNeighbor))
  · refine measurable_sum_filter (fun i => ?_) (fun i => ?_)
    · exact (measurableSet_isIsolatedPair i).inter
        ((measurableSet_isIsolatedDipole i).compl.inter
          ((measurableSet_isIsolatedPair_secondNearestNeighbor hN i).inter
            (measurableSet_isIsolatedPair_secondNearestNeighbor_nearestNeighbor hN i)))
    · exact (((measurable_alphaRadius hN lam γ i).div
        (measurable_firstNeighborRadius_apply hN lam i)).log).sub_const C

end MomentCombine

open MeasureTheory
open scoped ENNReal

/-- **Theorem 2, Step 6: the exponential moment of the electric energy for `β > 2`, generic rate**
(source l. 2086–2093), a *conditional helper*: `momentBound_of_moments_rate` for a
rate `ω` satisfying `UpperRateHyp` in place of `ω_λ`. The exponential moments (eq:A1) and
(eq:finalA3) with `ω` are hypotheses (they are the statements of `momentA1_le_rate` and
`momentA3_le_rate`), and (eq:A2) with `ω` is `momentA2_le_rate`. The conclusion is
`MomentBoundRate β _ ω`, with the radii `αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)` (`alphaRadius`). Besides the three
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
  obtain ⟨C₃, lam₁₃, hC₃, hlam₁₃, h3⟩ := hA3 1 one_pos
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
    -- Fix the A₃ estimate at t = 1, then interpolate all three moments.
    set R : ℝ := (C₁ + C₂ + C₃ + 2) * N * (isolatedPhi β hβ.le lam γ + ω lam)
      + (C₁ + C₂ + C₃ + 2) * Real.log (N + 1) with hRdef
    have hR0 : 0 ≤ R := by positivity
    have hR1 : C₁ * N * (isolatedPhi β hβ.le lam γ + ω lam) +
        C₁ * Real.log (N + 1) ≤ R := by
      dsimp [R]
      nlinarith [mul_nonneg hC₂.le (mul_nonneg hN0 (add_nonneg hφ0 hω0)),
        mul_nonneg hC₃.le (mul_nonneg hN0 (add_nonneg hφ0 hω0)),
        mul_nonneg hC₂.le hlogN, mul_nonneg hC₃.le hlogN]
    have hR2 : C₂ * N * ω lam + C₂ * Real.log (N + 1) ≤ R := by
      dsimp [R]
      nlinarith [mul_nonneg hC₁.le (mul_nonneg hN0 (add_nonneg hφ0 hω0)),
        mul_nonneg hC₃.le (mul_nonneg hN0 (add_nonneg hφ0 hω0)),
        mul_nonneg hC₂.le (mul_nonneg hN0 hφ0),
        mul_nonneg hC₁.le hlogN, mul_nonneg hC₃.le hlogN]
    have hR3 : C₃ * N * (isolatedPhi β hβ.le lam γ + ω lam) +
        C₃ * Real.log (N + 1) ≤ R := by
      dsimp [R]
      nlinarith [mul_nonneg hC₁.le (mul_nonneg hN0 (add_nonneg hφ0 hω0)),
        mul_nonneg hC₂.le (mul_nonneg hN0 (add_nonneg hφ0 hω0)),
        mul_nonneg hC₁.le hlogN, mul_nonneg hC₂.le hlogN]
    have hm1 := MomentCombine.measurable_linearA1 hN lam γ C_A
    have hm2 := MomentCombine.measurable_linearA2 hN lam
    have hm3 := MomentCombine.measurable_linearA3 hN lam γ
    have hT1 := MomentCombine.lintegral_exp_mul_le_exp (μ := μ) hm1
      (s := 12 * Real.pi * c) (r := β) (by positivity) hc1 hβ0 hR0
      ((h1 N hN lam hlam hl11 γ hγ hγ1).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hR1)))
    have h2' : ∫⁻ Z, ENNReal.ofReal (Real.exp (1 * A₂ Z)) ∂μ ≤
        ENNReal.ofReal (Real.exp (C₂ * N * ω lam + C₂ * Real.log (N + 1))) := by
      simpa only [one_mul] using h2 N hN lam hlam hl12
    have hT2 := MomentCombine.lintegral_exp_mul_le_exp (μ := μ) hm2
      (s := t) (r := 1) ht.le hc2 one_pos hR0
      (h2'.trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hR2)))
    have hT3 := MomentCombine.lintegral_exp_mul_le_exp (μ := μ) hm3
      (s := t) (r := 1) ht.le hc2 one_pos hR0
      ((h3 N hN lam hlam hl13 γ hγ hγ1).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hR3)))
    let B : Fin 3 → (Fin N ⊕ Fin N → ℂ) → ℝ :=
      ![fun Z => 4 * Real.pi * c * A₁ Z,
        fun Z => 4 * Real.pi * c * C_A * A₂ Z,
        fun Z => 4 * Real.pi * c * C_A * A₃ Z]
    have hBm : ∀ i, Measurable (B i) := by
      intro i
      fin_cases i
      · exact hm1.const_mul _
      · exact hm2.const_mul _
      · exact hm3.const_mul _
    have hBT : ∀ i, ∫⁻ Z, ENNReal.ofReal (Real.exp (3 * B i Z)) ∂μ ≤
        ENNReal.ofReal (Real.exp R) := by
      intro i
      fin_cases i
      · convert hT1 using 1
        congr 2
        funext Z
        congr 2
        dsimp [B]
        ring
      · convert hT2 using 1
        congr 2
        funext Z
        congr 2
        dsimp [B, t]
        ring
      · convert hT3 using 1
        congr 2
        funext Z
        congr 2
        dsimp [B, t]
        ring
    calc ∫⁻ Z, ENNReal.ofReal (Real.exp (c * Q Z)) ∂μ
        ≤ ∫⁻ Z, ENNReal.ofReal (Real.exp (∑ i, B i Z)) ∂μ := by
          refine lintegral_mono_ae (hae.mono fun Z hZ => ?_)
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
            (by simpa [B, Fin.sum_univ_succ, add_assoc] using hZ))
      _ ≤ ∏ i, (∫⁻ Z, ENNReal.ofReal (Real.exp (3 * B i Z)) ∂μ) ^ (1 / 3 : ℝ) :=
          MomentCombine.lintegral_exp_sum_le_holder B hBm
      _ ≤ ∏ _i : Fin 3, ENNReal.ofReal (Real.exp R) ^ (1 / 3 : ℝ) := by
          gcongr with i
          exact hBT i
      _ = ENNReal.ofReal (Real.exp R) := by
          simp only [MomentCombine.ofReal_exp_rpow, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
            ← Real.exp_nat_mul]
          congr 2
          ring

/-- **`MomentBoundRate` for `β > 2`, generic rate** (the output of Theorem 2, Steps 2--4, and Step 6,
source l. 1872–2093): for a rate `ω` satisfying `UpperRateHyp`,
`momentBound_of_moments_rate` applied to the proved exponential moments `momentA1_le_rate` (eq:A1)
and `momentA3_le_rate` (eq:finalA3) gives `MomentBoundRate β _ ω`. -/
theorem momentBound_of_two_lt_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) (hω : UpperRateHyp β hβ ω) :
    MomentBoundRate β hβ.le ω :=
  momentBound_of_moments_rate hβ ω hω (momentA1_le_rate hβ ω hω)
    fun _ ht => momentA3_le_rate hβ ω hω ht

end TwoComponentCoulomb

end
