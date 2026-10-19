/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TwoComponentCoulomb.Frozen.SmearedCharge

/-!
# API for the uniform disc measure `smearedCharge`

Basic facts about `δ_z^{(a)} = smearedCharge z a`, the uniform probability measure on the disc
`B(z, a)` (source l. 148).

* `smearedCharge_eq` : `δ_z^{(a)} = |B(z, a)|⁻¹ • (volume restricted to B(z, a))`.
* `smearedCharge_of_nonpos` : the measure is `0` when `a ≤ 0` (the disc is empty).
* `isProbabilityMeasure_smearedCharge` : it is a probability measure when `0 < a`.
* `integral_smearedCharge` : integrals against it are averages over the disc.
* `map_add_right_smearedCharge`, `map_ofReal_mul_smearedCharge`,
  `map_mul_smearedCharge_of_norm_eq_one`, `map_neg_smearedCharge` : the behaviour under
  translations, real dilations, rotations and the antipodal map.

The transport lemmas hold for every real radius `a` (for `a ≤ 0` both sides are `0`); they follow
from the single general lemma `map_cond_of_map_eq_smul` on pushforwards of conditional measures.
No integrability of any function is used.
-/

public section

open MeasureTheory

namespace TwoComponentCoulomb

/-! ### The general transport lemma for conditional measures -/

/-- Pushing a conditional measure forward along a measurable embedding `f` with
`μ.map f = k • ν` (`0 < k < ∞`) gives the conditional measure of `ν` on the corresponding set. -/
theorem map_cond_of_map_eq_smul {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurableEmbedding f) {k : ENNReal}
    (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (hmap : μ.map f = k • ν) {s : Set α} {t : Set β}
    (hst : f ⁻¹' t = s) :
    (ProbabilityTheory.cond μ s).map f = ProbabilityTheory.cond ν t := by
  have h1 : μ s = k * ν t := by
    rw [← hst, ← hf.map_apply, hmap, Measure.smul_apply, smul_eq_mul]
  have h2 : (μ.restrict s).map f = k • ν.restrict t := by
    rw [← hst, ← hf.restrict_map, hmap, Measure.restrict_smul]
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul _ hf.measurable.aemeasurable, h2, h1, smul_smul, ENNReal.mul_inv
    (Or.inl hk0) (Or.inl hkt), mul_comm k⁻¹, mul_assoc, ENNReal.inv_mul_cancel hk0 hkt, mul_one]

/-! ### Basic properties -/

/-- `δ_z^{(a)}` is the restriction of the Lebesgue measure to the disc, normalised by the disc
volume. -/
theorem smearedCharge_eq (z : ℂ) (a : ℝ) :
    smearedCharge z a = (volume (Metric.ball z a))⁻¹ • volume.restrict (Metric.ball z a) := rfl

/-- The disc `B(z, a)` is empty for `a ≤ 0`, so the uniform measure on it is `0`. -/
@[simp]
theorem smearedCharge_of_nonpos (z : ℂ) {a : ℝ} (ha : a ≤ 0) : smearedCharge z a = 0 := by
  unfold smearedCharge
  rw [Metric.ball_eq_empty.2 ha, ProbabilityTheory.cond_empty]

/-- For a positive radius, `δ_z^{(a)}` is a probability measure. -/
theorem isProbabilityMeasure_smearedCharge (z : ℂ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (smearedCharge z a) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (Metric.measure_ball_pos volume z ha).ne' measure_ball_lt_top.ne

/-- `δ_z^{(a)}` is a finite measure for every real `a`. -/
instance isFiniteMeasure_smearedCharge (z : ℂ) (a : ℝ) : IsFiniteMeasure (smearedCharge z a) := by
  rcases le_or_gt a 0 with ha | ha
  · rw [smearedCharge_of_nonpos z ha]
    infer_instance
  · have := isProbabilityMeasure_smearedCharge z ha
    infer_instance

/-- The volume of a disc in `ℂ`, as a real number. -/
theorem volume_real_ball_complex (z : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    volume.real (Metric.ball z a) = Real.pi * a ^ 2 := by
  rw [Measure.real, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal ha]
  simp [mul_comm]

/-- Integrals against `δ_z^{(a)}` are averages over the disc `B(z, a)` (for `a > 0`). -/
theorem integral_smearedCharge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E)
    (z : ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ x, f x ∂smearedCharge z a = (Real.pi * a ^ 2)⁻¹ • ∫ x in Metric.ball z a, f x := by
  rw [smearedCharge_eq, integral_smul_measure, ENNReal.toReal_inv]
  congr 2
  exact volume_real_ball_complex z ha.le

/-! ### Transport of `smearedCharge` by isometries and dilations of `ℂ` -/

/-- Translation: `(· + w)` pushes `δ_z^{(a)}` to `δ_{z+w}^{(a)}`. -/
theorem map_add_right_smearedCharge (z w : ℂ) (a : ℝ) :
    (smearedCharge z a).map (· + w) = smearedCharge (z + w) a := by
  refine map_cond_of_map_eq_smul (k := 1) (measurableEmbedding_addRight w) one_ne_zero
    ENNReal.one_ne_top ?_ ?_
  · rw [map_add_right_eq_self, one_smul]
  · ext x
    simp [Complex.dist_eq]

/-- Real dilation: `x ↦ c x` (`c > 0`) pushes `δ_z^{(a)}` to `δ_{c z}^{(c a)}`. -/
theorem map_ofReal_mul_smearedCharge (z : ℂ) (a : ℝ) {c : ℝ} (hc : 0 < c) :
    (smearedCharge z a).map (fun x => (c : ℂ) * x) = smearedCharge (c * z) (c * a) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hemb : MeasurableEmbedding (fun x : ℂ => (c : ℂ) * x) :=
    measurableEmbedding_mulLeft₀ (Complex.ofReal_ne_zero.2 hc0)
  have hmap : (volume : Measure ℂ).map (fun x : ℂ => (c : ℂ) * x) =
      ENNReal.ofReal |(c ^ Module.finrank ℝ ℂ)⁻¹| • volume := by
    rw [← Measure.map_addHaar_smul volume hc0]
    rfl
  refine map_cond_of_map_eq_smul hemb ?_ ENNReal.ofReal_ne_top hmap ?_
  · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.2 (inv_ne_zero (pow_ne_zero _ hc0))
  · ext x
    simp [Complex.dist_eq, ← mul_sub, abs_of_pos hc, hc]

/-- Rotation: `x ↦ u x` (`‖u‖ = 1`) pushes `δ_z^{(a)}` to `δ_{u z}^{(a)}`. -/
theorem map_mul_smearedCharge_of_norm_eq_one (z : ℂ) (a : ℝ) {u : ℂ} (hu : ‖u‖ = 1) :
    (smearedCharge z a).map (fun x => u * x) = smearedCharge (u * z) a := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hrot := (LinearIsometryEquiv.measurePreserving
    (rotation (⟨u, mem_sphere_zero_iff_norm.2 hu⟩ : Circle))).map_eq
  have hfun : ⇑(rotation (⟨u, mem_sphere_zero_iff_norm.2 hu⟩ : Circle)) = fun x : ℂ => u * x :=
    funext (rotation_apply _)
  rw [hfun] at hrot
  refine map_cond_of_map_eq_smul (k := 1) (measurableEmbedding_mulLeft₀ hu0) one_ne_zero
    ENNReal.one_ne_top (by rw [hrot, one_smul]) ?_
  ext x
  simp [Complex.dist_eq, ← mul_sub, hu]

/-- Antipodal map: `x ↦ -x` pushes `δ_z^{(a)}` to `δ_{-z}^{(a)}`. -/
theorem map_neg_smearedCharge (z : ℂ) (a : ℝ) :
    (smearedCharge z a).map Neg.neg = smearedCharge (-z) a := by
  refine map_cond_of_map_eq_smul (k := 1) measurableEmbedding_neg one_ne_zero
    ENNReal.one_ne_top ?_ ?_
  · rw [Measure.map_neg_eq_self, one_smul]
  · ext x
    simp [Complex.dist_eq]

end TwoComponentCoulomb

end
