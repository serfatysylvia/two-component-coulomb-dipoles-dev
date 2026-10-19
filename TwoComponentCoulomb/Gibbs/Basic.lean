/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TwoComponentCoulomb.Frozen.GibbsMeasure
public import TwoComponentCoulomb.Frozen.ReducedEnergy
public import TwoComponentCoulomb.Gibbs.Measurability

/-!
# Plumbing for the Gibbs measure

Elementary facts on the box `Λ = [0, √N]²` (source l. 125), the
partition function `partitionFunction` (eq. (eq:ZRV), l. 176--177) and the Gibbs measure
`gibbsMeasure` (eq. (defP), l. 172--174), used in the proofs of Theorems 1 and 2.

Throughout, `Λ` denotes `Set.univ.pi fun _ : Fin N ⊕ Fin N => box N`, the domain of integration of
the partition function.

* `volume_reProdIm_Icc_Icc` : the area of a rectangle `[a, b] × [c, d]` in `ℂ`.
* `measurableSet_box`, `measurableSet_pi_box`, `volume_box`, `volume_pi_box` : `Λ` is measurable,
  with volume `N ^ (2 * N)`.
* `partitionFunction_pos` : `0 < Z_{N,β}^λ` for `N ≥ 1`.
* `isProbabilityMeasure_gibbsMeasure` : `ℙ_{N,β}^λ` is a probability measure as soon as the
  partition function is finite.
* `gibbsMeasure_apply`, `gibbsMeasure_apply'`, `lintegral_gibbsMeasure` : integrals against the
  Gibbs measure as normalised integrals of the Boltzmann weight over `Λ`.
* `lintegral_gibbsMeasure_exp_energy_sub_reducedEnergy` : the identity
  `𝔼[e^{β(F_λ - F̃_λ)}] = K / Z` behind Theorem 1 (2) (source l. 1923--1933), where
  `K = ∫_Λ e^{-β F̃_λ}`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### The box -/

theorem measurableSet_box (N : ℕ) : MeasurableSet (box N) :=
  (isClosed_Icc.reProdIm isClosed_Icc).measurableSet

/-- The domain `Λ` of the partition function is measurable. -/
theorem measurableSet_pi_box (N : ℕ) :
    MeasurableSet (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) :=
  MeasurableSet.univ_pi fun _ => measurableSet_box N

/-- The area of a rectangle `[a, b] × [c, d]` in `ℂ`. -/
theorem volume_reProdIm_Icc_Icc (a b c d : ℝ) :
    volume (Complex.reProdIm (Set.Icc a b) (Set.Icc c d)) =
      ENNReal.ofReal (b - a) * ENNReal.ofReal (d - c) := by
  have h : Complex.reProdIm (Set.Icc a b) (Set.Icc c d) =
      Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d) := by
    ext z
    simp only [Complex.mem_reProdIm, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
      Set.mem_prod]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]

/-- The box `[0, √N]²` has area `N`. -/
theorem volume_box (N : ℕ) : volume (box N) = (N : ℝ≥0∞) := by
  have h : box N = Complex.measurableEquivRealProd ⁻¹'
      (Set.Icc 0 (Real.sqrt N) ×ˢ Set.Icc 0 (Real.sqrt N)) := by
    ext z
    simp only [box, Complex.mem_reProdIm, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
      Set.mem_prod]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    Real.mul_self_sqrt (Nat.cast_nonneg N), ENNReal.ofReal_natCast]

/-- The domain `Λ = [0, √N]²ᴺ·²` of the partition function has volume `N ^ (2 N)`. -/
theorem volume_pi_box (N : ℕ) :
    volume (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) = (N : ℝ≥0∞) ^ (2 * N) := by
  rw [volume_pi_pi]
  simp [volume_box, Finset.prod_const, two_mul]

theorem volume_pi_box_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < volume (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) := by
  rw [volume_pi_box]
  exact ENNReal.pow_pos (by exact_mod_cast hN) _

/-! ### The Boltzmann weight -/

theorem measurable_ofReal_exp_neg_mul_energy {N : ℕ} (β lam : ℝ) :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => ENNReal.ofReal (Real.exp (-β * energy lam Z)) :=
  ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp ((measurable_energy lam).const_mul (-β)))

/-! ### The partition function -/

/-- The partition function `Z_{N,β}^λ` is positive for `N ≥ 1`: the Boltzmann weight is
everywhere positive and `Λ` has positive volume. -/
theorem partitionFunction_pos {N : ℕ} (hN : 1 ≤ N) (β lam : ℝ) :
    0 < partitionFunction N β lam := by
  unfold partitionFunction
  rw [lintegral_pos_iff_support (measurable_ofReal_exp_neg_mul_energy β lam)]
  have : Function.support (fun Z : Fin N ⊕ Fin N → ℂ =>
      ENNReal.ofReal (Real.exp (-β * energy lam Z))) = Set.univ := by
    ext Z
    simp [Function.mem_support, Real.exp_pos]
  rw [this, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact volume_pi_box_pos hN

/-! ### The Gibbs measure -/

/-- Mass of a set under the Gibbs measure, without a measurability hypothesis on the set. -/
theorem gibbsMeasure_apply' {N : ℕ} {β lam : ℝ} (s : Set (Fin N ⊕ Fin N → ℂ)) :
    gibbsMeasure N β lam s = (partitionFunction N β lam)⁻¹ *
      ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ s,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) := by
  unfold gibbsMeasure
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply',
    Measure.restrict_restrict' (measurableSet_pi_box N), Set.inter_comm]

/-- Mass of a measurable set under the Gibbs measure: the Boltzmann integral over `Λ ∩ s`,
divided by the partition function. (The measurability of `s` is in fact not needed, see
`gibbsMeasure_apply'`.) -/
theorem gibbsMeasure_apply {N : ℕ} {β lam : ℝ} (s : Set (Fin N ⊕ Fin N → ℂ))
    (hs : MeasurableSet s) :
    gibbsMeasure N β lam s = (partitionFunction N β lam)⁻¹ *
      ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ s,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) := by
  unfold gibbsMeasure
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs, Measure.restrict_restrict hs,
    Set.inter_comm]

/-- The Gibbs measure of the whole space is `Z⁻¹ * Z`. -/
theorem gibbsMeasure_univ {N : ℕ} {β lam : ℝ} :
    gibbsMeasure N β lam Set.univ = (partitionFunction N β lam)⁻¹ * partitionFunction N β lam := by
  rw [gibbsMeasure_apply' Set.univ, Set.inter_univ]
  rfl

/-- The Gibbs measure is a probability measure as soon as the partition function is finite
(it is positive for `N ≥ 1` by `partitionFunction_pos`). -/
theorem isProbabilityMeasure_gibbsMeasure {N : ℕ} {β lam : ℝ}
    (hZ : partitionFunction N β lam ≠ ∞) (hN : 1 ≤ N) :
    IsProbabilityMeasure (gibbsMeasure N β lam) :=
  ⟨by rw [gibbsMeasure_univ, ENNReal.inv_mul_cancel (partitionFunction_pos hN β lam).ne' hZ]⟩

/-- Integrals against the Gibbs measure: `𝔼[f] = Z⁻¹ ∫_Λ f e^{-β F_λ}`. -/
theorem lintegral_gibbsMeasure {N : ℕ} {β lam : ℝ} (f : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ Z, f Z ∂gibbsMeasure N β lam = (partitionFunction N β lam)⁻¹ *
      ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
        f Z * ENNReal.ofReal (Real.exp (-β * energy lam Z)) := by
  unfold gibbsMeasure
  rw [lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_ofReal_exp_neg_mul_energy β lam) hf]
  simp_rw [Pi.mul_apply, mul_comm]

/-- Version of `lintegral_gibbsMeasure` without the measurability hypothesis on `f`. -/
theorem lintegral_gibbsMeasure' {N : ℕ} {β lam : ℝ} (f : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) :
    ∫⁻ Z, f Z ∂gibbsMeasure N β lam = (partitionFunction N β lam)⁻¹ *
      ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
        f Z * ENNReal.ofReal (Real.exp (-β * energy lam Z)) := by
  unfold gibbsMeasure
  rw [lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (measurable_ofReal_exp_neg_mul_energy β lam)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  simp_rw [Pi.mul_apply, mul_comm]

/-- The identity behind Theorem 1 (2) (source l. 1923--1933):
`𝔼[e^{β(F_λ - F̃_λ)}] = Z⁻¹ ∫_Λ e^{-β F̃_λ}`. -/
theorem lintegral_gibbsMeasure_exp_energy_sub_reducedEnergy {N : ℕ} {β lam : ℝ} :
    ∫⁻ Z, ENNReal.ofReal (Real.exp (β * (energy lam Z - reducedEnergy lam Z)))
        ∂gibbsMeasure N β lam =
      (partitionFunction N β lam)⁻¹ *
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
          ENNReal.ofReal (Real.exp (-β * reducedEnergy lam Z)) := by
  have hm : Measurable fun Z : Fin N ⊕ Fin N → ℂ =>
      ENNReal.ofReal (Real.exp (β * (energy lam Z - reducedEnergy lam Z))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_energy lam).sub (measurable_reducedEnergy lam)).const_mul β))
  rw [lintegral_gibbsMeasure _ hm]
  congr 1
  refine lintegral_congr fun Z => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

end TwoComponentCoulomb

end
