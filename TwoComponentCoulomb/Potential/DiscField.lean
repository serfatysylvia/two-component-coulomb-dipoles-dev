/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import TwoComponentCoulomb.Frozen.LogKernel
public import TwoComponentCoulomb.Frozen.SmearedCharge
import TwoComponentCoulomb.Potential.DiscPotential
import TwoComponentCoulomb.Potential.Fundamental
import TwoComponentCoulomb.Potential.SmearedCharge
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Group.Integral

/-!
# The potential and the field of a uniform disc

For `a > 0` let `δ_z^{(a)} = smearedCharge z a` be the uniform probability measure on the disc
`B(z, a)` and `g(x) = -log |x|`. By Newton's theorem (source l. 128–152, 499–518) the potential
`g * δ_0^{(a)}` is the explicit radial function `discPotential a`, and its gradient is the explicit
field `discField a` (ruling R12b: the electric formulation is implemented through these
explicit radial disc potentials).

* `discPotential a u = -log (max a |u|) + (1 - min(|u|, a)² / a²) / 2`.
* `discField a u = -u / max(a, |u|)²`.

Main results (for `a > 0`):

* `hasGradientAt_discPotential` : `discField a u` is the gradient of `discPotential a` at `u`
  (`hasFDerivAt_discPotential` gives the `fderiv` form,
  `continuous_discField` and `contDiff_discPotential` the regularity).
* `integral_gradLogKernel_smearedCharge` : Newton's theorem for the field, i.e. the average of the
  point field `-(x - y) / |x - y|²` over `y ∼ δ_z^{(a)}` is `discField a (x - z)`. The proof is by
  polar coordinates about `z` and the mean value property for the holomorphic function
  `y ↦ 1 / (u - y)` (the point field is `-conj (1 / (x - y))`): the circle average is `-1/conj u`
  for a circle not enclosing `u` and `0` for a circle enclosing it.
* `integral_fderiv_apply_discField` : the single-charge Green identity used in Theorem 2, Step 1
  (source l. 1842–1866): for `ξ` of class `C¹` with compact support,
  `∫ ∇ξ(x) · discField a (x - z) dx = 2π ∫ ξ dδ_z^{(a)}`. It follows from
  `integral_fderiv_apply_gradLogKernel` (`Potential/Fundamental.lean`) by Fubini.

Auxiliary results: vector-valued polar coordinates on a disc, and integrability of the point
field on products with `smearedCharge`.
-/

@[expose] public section

open MeasureTheory Metric Set InnerProductSpace Filter Topology

namespace TwoComponentCoulomb

/-- The potential `g * δ₀^{(a)}` of the uniform unit-mass disc of radius `a`, in closed form. -/
noncomputable def discPotential (a : ℝ) (u : ℂ) : ℝ :=
  -Real.log (max a ‖u‖) + (1 - min ‖u‖ a ^ 2 / a ^ 2) / 2

/-- The field `∇(g * δ₀^{(a)})(u) = -u / max(a, |u|)²` of the uniform disc of radius `a`. -/
noncomputable def discField (a : ℝ) (u : ℂ) : ℂ :=
  -((max a ‖u‖ ^ 2)⁻¹ : ℝ) • u

/-! ### Polar coordinates on discs, vector-valued -/

/-- Polar coordinates, vector-valued: integrability on the polar target. -/
theorem integrableOn_polarCoord_target_of_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {G : ℂ → E} (hGm : Measurable G) (hG : Integrable G) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • G (Complex.polarCoord.symm p))
      Complex.polarCoord.target := by
  have hmeas : Measurable fun p : ℝ × ℝ => p.1 • G (Complex.polarCoord.symm p) := by
    have : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
        fun p => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p; exact Complex.polarCoord_symm_apply p
    have hc : Measurable fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
      rw [this]
      exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I)).measurable
    exact measurable_fst.smul (hGm.comp hc)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h1 : ∫⁻ p in Complex.polarCoord.target, ‖p.1 • G (Complex.polarCoord.symm p)‖ₑ =
      ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • (fun w : ℂ => ‖G w‖ₑ) (Complex.polarCoord.symm p) := by
    refine setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    simp [enorm_smul, Real.enorm_eq_ofReal hp1.le]
  rw [h1]
  exact (Complex.lintegral_comp_polarCoord_symm (fun w : ℂ => ‖G w‖ₑ)).trans_lt hG.2

/-- Integration over a disc in polar coordinates, vector-valued version. -/
theorem setIntegral_ball_zero_eq_polar_of_measurable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {F : ℂ → E} (hF : Measurable F) {a : ℝ}
    (hint : IntegrableOn F (ball (0 : ℂ) a)) :
    ∫ w in ball (0 : ℂ) a, F w =
      ∫ r in Ioo 0 a, r • ∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ) := by
  have hG : Integrable (indicator (ball (0 : ℂ) a) F) :=
    (integrable_indicator_iff measurableSet_ball).2 hint
  have hGm : Measurable (indicator (ball (0 : ℂ) a) F) := hF.indicator measurableSet_ball
  have h1 := Complex.integral_comp_polarCoord_symm (indicator (ball (0 : ℂ) a) F)
  have h2 := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun p : ℝ × ℝ => p.1 • indicator (ball (0 : ℂ) a) F (Complex.polarCoord.symm p))
    (s := Ioi 0) (t := Ioo (-Real.pi) Real.pi)
    (integrableOn_polarCoord_target_of_integrable hGm hG)
  rw [integral_indicator measurableSet_ball] at h1
  rw [← h1]
  have h3 : ∫ p in polarCoord.target, p.1 • indicator (ball (0 : ℂ) a) F
      (Complex.polarCoord.symm p) = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        r • indicator (ball (0 : ℂ) a) F (Complex.polarCoord.symm (r, θ)) := h2
  rw [h3]
  have h4 : ∀ r ∈ Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        r • indicator (ball (0 : ℂ) a) F (Complex.polarCoord.symm (r, θ)) =
      indicator (Iio a) (fun r => r • ∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ)) r := by
    intro r hr
    have hr0 : 0 < r := hr
    simp_rw [polarCoord_symm_eq_circleMap]
    by_cases hra : r < a
    · have : ∀ θ, circleMap 0 r θ ∈ ball (0 : ℂ) a := by
        intro θ
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr0]; exact hra
      simp [indicator, hra, this, integral_smul]
    · have : ∀ θ, circleMap 0 r θ ∉ ball (0 : ℂ) a := by
        intro θ
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr0]; exact hra
      simp [indicator, hra, this]
  rw [setIntegral_congr_fun measurableSet_Ioi h4, setIntegral_indicator measurableSet_Iio,
    Ioi_inter_Iio]

/-- Translation of discs, vector-valued version. -/
theorem setIntegral_ball_eq_setIntegral_ball_zero_of_vec {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (z : ℂ) (a : ℝ) :
    ∫ y in ball z a, f y = ∫ w in ball (0 : ℂ) a, f (z + w) := by
  have h := (measurePreserving_add_left volume z).setIntegral_preimage_emb
    (measurableEmbedding_addLeft z) f (ball z a)
  have hs : (fun w : ℂ => z + w) ⁻¹' ball z a = ball (0 : ℂ) a := by
    ext w; simp
  rw [hs] at h
  exact h.symm

/-! ### Circle averages of the point field -/

/-- The point field `-v / |v|²` is `-conj (1 / v)`. -/
theorem gradLogKernel_eq_neg_conj_inv (v : ℂ) :
    -((‖v‖ ^ 2)⁻¹ : ℝ) • v = -(starRingEnd ℂ) v⁻¹ := by
  rw [Complex.inv_def]
  simp [Complex.normSq_eq_norm_sq, Complex.real_smul]
  ring

/-- The integral over `θ ∈ (-π, π)` of a function on the circle of radius `r` is `2π` times its
circle average. -/
theorem integral_Ioo_circleMap_eq_circleAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (r : ℝ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ) =
      (2 * Real.pi) • Real.circleAverage f 0 r := by
  have hper : Function.Periodic (fun θ => f (circleMap 0 r θ)) (2 * Real.pi) :=
    fun θ => by simp [periodic_circleMap 0 r θ]
  have h1 := hper.intervalIntegral_add_eq (-Real.pi) 0
  have h2 : ∫ θ in (-Real.pi)..Real.pi, f (circleMap 0 r θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), f (circleMap 0 r θ) := by
    rw [← zero_add (2 * Real.pi), ← h1]
    have : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [this]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), h2, Real.circleAverage_def,
    smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- Mean value property for a pole outside the circle. -/
theorem circleAverage_inv_sub_of_lt {u : ℂ} {r : ℝ} (h : |r| < ‖u‖) :
    Real.circleAverage (fun y : ℂ => (u - y)⁻¹) 0 r = u⁻¹ := by
  have hne : ∀ y ∈ closedBall (0 : ℂ) |r|, u - y ≠ 0 := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    exact sub_ne_zero.2 (fun h' => by rw [← h'] at hy; linarith)
  have h1 : ContinuousOn (fun y : ℂ => (u - y)⁻¹) (closedBall (0 : ℂ) |r|) :=
    (continuousOn_const.sub continuousOn_id).inv₀ hne
  have h2 : ∀ y ∈ ball (0 : ℂ) |r| \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun y : ℂ => (u - y)⁻¹) y := by
    intro y hy
    exact (differentiableAt_const u |>.sub differentiableAt_id).inv
      (hne y (ball_subset_closedBall hy.1))
  rw [circleAverage_of_differentiable_on_off_countable countable_empty h1 h2]
  simp

/-- Mean value property for a nonzero pole inside the circle. -/
theorem circleAverage_inv_sub_of_gt {u : ℂ} {r : ℝ} (hu : u ≠ 0) (h : ‖u‖ < |r|) :
    Real.circleAverage (fun y : ℂ => (u - y)⁻¹) 0 r = 0 := by
  have hw : u ∈ ball (0 : ℂ) |r| := by rwa [mem_ball_zero_iff]
  have hsph : ∀ y ∈ sphere (0 : ℂ) |r|, u - y ≠ 0 := by
    intro y hy
    rw [mem_sphere_zero_iff_norm] at hy
    exact sub_ne_zero.2 (fun h' => by rw [← h'] at hy; linarith)
  have hmv := circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable
    (f := fun _ : ℂ => (1 : ℂ)) (c := 0) (R := r) (w := u) countable_empty
    continuousOn_const (fun z _ => differentiableAt_const _) hw
  have hcont : ContinuousOn (fun y : ℂ => (u - y)⁻¹) (sphere (0 : ℂ) |r|) :=
    (continuousOn_const.sub continuousOn_id).inv₀ hsph
  have hcongr : Real.circleAverage (fun z : ℂ => ((z - 0) / (z - u)) • (1 : ℂ)) 0 r =
      Real.circleAverage (fun z : ℂ => (1 : ℂ) - u • (u - z)⁻¹) 0 r := by
    refine Real.circleAverage_congr_sphere fun z hz => ?_
    have h1 : u - z ≠ 0 := hsph z hz
    have h2 : z - u ≠ 0 := fun h' => h1 (by rw [← neg_sub, h', neg_zero])
    simp only [sub_zero, smul_eq_mul, mul_one]
    field_simp
    ring
  have hi1 : CircleIntegrable (fun _ : ℂ => (1 : ℂ)) 0 r :=
    continuousOn_const.circleIntegrable'
  have hi2 : CircleIntegrable (fun z : ℂ => u • (u - z)⁻¹) 0 r :=
    ContinuousOn.circleIntegrable'
      (by simpa only [smul_eq_mul] using continuousOn_const.fun_mul hcont)
  rw [hcongr, Real.circleAverage_fun_sub hi1 hi2, Real.circleAverage_const,
    Real.circleAverage_fun_smul] at hmv
  have : u • Real.circleAverage (fun y : ℂ => (u - y)⁻¹) 0 r = 0 := by
    linear_combination (-1 : ℂ) * hmv
  rcases smul_eq_zero.1 this with h | h
  · exact absurd h hu
  · exact h

/-- The circle average of the point field of a charge outside the circle. -/
theorem integral_Ioo_gradLogKernel_sub_circleMap_of_lt {u : ℂ} {r : ℝ} (hr : 0 < r)
    (hu : r < ‖u‖) :
    ∫ θ in Ioo (-Real.pi) Real.pi,
        -((‖u - circleMap 0 r θ‖ ^ 2)⁻¹ : ℝ) • (u - circleMap 0 r θ) =
      (2 * Real.pi) • (-((‖u‖ ^ 2)⁻¹ : ℝ) • u) := by
  simp_rw [gradLogKernel_eq_neg_conj_inv]
  rw [integral_neg, integral_conj, integral_Ioo_circleMap_eq_circleAverage (fun y => (u - y)⁻¹) r,
    circleAverage_inv_sub_of_lt (by rwa [abs_of_pos hr])]
  simp [Complex.real_smul, map_ofNat]

/-- The circle average of the point field of a charge inside the circle vanishes. -/
theorem integral_Ioo_gradLogKernel_sub_circleMap_of_gt {u : ℂ} {r : ℝ} (hr : 0 < r)
    (hu : ‖u‖ < r) :
    ∫ θ in Ioo (-Real.pi) Real.pi,
        -((‖u - circleMap 0 r θ‖ ^ 2)⁻¹ : ℝ) • (u - circleMap 0 r θ) = 0 := by
  by_cases hu0 : u = 0
  · subst hu0
    have h1 : ∀ θ, -((‖0 - circleMap 0 r θ‖ ^ 2)⁻¹ : ℝ) • (0 - circleMap 0 r θ) =
        (r ^ 2)⁻¹ • circleMap 0 r θ := by
      intro θ
      rw [zero_sub, norm_neg, norm_circleMap_zero, abs_of_pos hr]
      simp
    simp_rw [h1]
    rw [integral_smul, integral_Ioo_circleMap_eq_circleAverage (fun y => y) r,
      circleAverage_of_differentiable_on_off_countable (f := fun y : ℂ => y) countable_empty
        continuousOn_id (fun z _ => differentiableAt_id)]
    simp
  · simp_rw [gradLogKernel_eq_neg_conj_inv]
    rw [integral_neg, integral_conj,
      integral_Ioo_circleMap_eq_circleAverage (fun y => (u - y)⁻¹) r,
      circleAverage_inv_sub_of_gt hu0 (by rwa [abs_of_pos hr])]
    simp

/-! ### The field of a disc -/

/-- The point field `u ↦ -u / |u|²` is measurable. -/
theorem measurable_gradLogKernel : Measurable fun w : ℂ => -((‖w‖ ^ 2)⁻¹ : ℝ) • w :=
  ((measurable_norm.pow_const 2).inv.neg).smul measurable_id

/-- The point field `u ↦ -u / |u|²` is integrable on discs centred at `0` (its modulus is
`|u|⁻¹`). -/
theorem integrableOn_gradLogKernel_ball_zero (R : ℝ) :
    IntegrableOn (fun w : ℂ => -((‖w‖ ^ 2)⁻¹ : ℝ) • w) (ball (0 : ℂ) R) :=
  (integrableOn_inv_norm_ball_zero R).mono' measurable_gradLogKernel.aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => (norm_gradLogKernel w).le)

/-- Newton's theorem for the field, centred at `0`. -/
theorem integral_gradLogKernel_sub_ball_zero (u : ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ w in ball (0 : ℂ) a, -((‖u - w‖ ^ 2)⁻¹ : ℝ) • (u - w) =
      (Real.pi * min a ‖u‖ ^ 2) • (-((‖u‖ ^ 2)⁻¹ : ℝ) • u) := by
  have hint : IntegrableOn (fun w : ℂ => -((‖u - w‖ ^ 2)⁻¹ : ℝ) • (u - w)) (ball (0 : ℂ) a) :=
    integrableOn_comp_sub_ball (f := fun w : ℂ => -((‖w‖ ^ 2)⁻¹ : ℝ) • w)
      integrableOn_gradLogKernel_ball_zero u 0 a
  have hm : Measurable fun w : ℂ => -((‖u - w‖ ^ 2)⁻¹ : ℝ) • (u - w) :=
    measurable_gradLogKernel.comp (measurable_const.sub measurable_id)
  rw [setIntegral_ball_zero_eq_polar_of_measurable hm hint]
  set c : ℂ := (2 * Real.pi) • (-((‖u‖ ^ 2)⁻¹ : ℝ) • u) with hc
  have h1 : ∀ᵐ r : ℝ, r ∈ Ioo 0 a → r • ∫ θ in Ioo (-Real.pi) Real.pi,
        -((‖u - circleMap 0 r θ‖ ^ 2)⁻¹ : ℝ) • (u - circleMap 0 r θ) =
      (indicator (Iio ‖u‖) (fun r : ℝ => r) r) • c := by
    filter_upwards [(Set.countable_singleton ‖u‖).ae_notMem volume] with r hrne hr
    have hne : r ≠ ‖u‖ := hrne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [integral_Ioo_gradLogKernel_sub_circleMap_of_lt hr.1 h, indicator_of_mem (mem_Iio.2 h)]
    · rw [integral_Ioo_gradLogKernel_sub_circleMap_of_gt hr.1 h,
        indicator_of_notMem (by simpa using h.le)]
      simp
  rw [setIntegral_congr_ae measurableSet_Ioo h1, integral_smul_const,
    setIntegral_indicator measurableSet_Iio, Ioo_inter_Iio,
    integral_Ioo_eq_intervalIntegral (le_min ha.le (norm_nonneg _)), integral_id, hc]
  rw [smul_smul]
  congr 1
  ring

/-- **Newton's theorem for the field** : the average of the point field
`-(x - y) / |x - y|²` over the uniform disc `B(z, a)` is the field `discField a (x - z)` of the
disc. -/
theorem integral_gradLogKernel_smearedCharge {a : ℝ} (ha : 0 < a) (x z : ℂ) :
    ∫ y, -((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y) ∂smearedCharge z a = discField a (x - z) := by
  rw [integral_smearedCharge _ z ha,
    setIntegral_ball_eq_setIntegral_ball_zero_of_vec _ z a]
  have h1 : ∀ w : ℂ, -((‖x - (z + w)‖ ^ 2)⁻¹ : ℝ) • (x - (z + w)) =
      -((‖(x - z) - w‖ ^ 2)⁻¹ : ℝ) • ((x - z) - w) := fun w => by rw [sub_sub]
  simp_rw [h1]
  rw [integral_gradLogKernel_sub_ball_zero (x - z) ha, discField]
  simp only [smul_smul]
  by_cases hu : x - z = 0
  · simp [hu]
  rcases le_total a ‖x - z‖ with h | h
  · rw [min_eq_left h, max_eq_right h]
    congr 1
    field_simp
  · rw [min_eq_right h, max_eq_left h]
    have hpos : 0 < ‖x - z‖ := norm_pos_iff.2 hu
    congr 1
    field_simp

/-! ### The smeared Green identity -/

/-- Measurability of `(x, y) ↦ ∇ξ(x) · ∇g(x - y)` on `ℂ × ℂ`. -/
theorem measurable_fderiv_apply_gradLogKernel_sub {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) :
    Measurable fun p : ℂ × ℂ => fderiv ℝ ξ p.1 (-((‖p.1 - p.2‖ ^ 2)⁻¹ : ℝ) • (p.1 - p.2)) := by
  have h1 : (fun p : ℂ × ℂ => fderiv ℝ ξ p.1 (-((‖p.1 - p.2‖ ^ 2)⁻¹ : ℝ) • (p.1 - p.2))) =
      fun p => -((‖p.1 - p.2‖ ^ 2)⁻¹ : ℝ) * fderiv ℝ ξ p.1 (p.1 - p.2) := by
    funext p
    rw [map_smul, smul_eq_mul]
  rw [h1]
  have h2 : Continuous fun p : ℂ × ℂ => fderiv ℝ ξ p.1 (p.1 - p.2) :=
    ((hξ.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply
      (continuous_fst.sub continuous_snd)
  exact (((measurable_fst.sub measurable_snd).norm.pow_const 2).inv.neg).mul h2.measurable

/-- A uniform bound for the potential-type integral `∫ ‖x - y‖⁻¹ dδ_z^{(a)}(y)`. -/
theorem exists_integral_inv_norm_sub_smearedCharge_le (z : ℂ) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    ∃ M : ℝ, ∀ x ∈ ball (0 : ℂ) R, ∫ y, ‖x - y‖⁻¹ ∂smearedCharge z a ≤ M := by
  set ρ : ℝ := R + ‖z‖ + a with hρ
  refine ⟨(Real.pi * a ^ 2)⁻¹ * ∫ w in ball (0 : ℂ) ρ, ‖w‖⁻¹, fun x hx => ?_⟩
  rw [mem_ball_zero_iff] at hx
  rw [integral_smearedCharge _ z ha, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsub : ball z a ⊆ ball x ρ := by
    intro y hy
    rw [mem_ball_iff_norm] at hy ⊢
    calc ‖y - x‖ = ‖(y - z) + (z - 0) - (x - 0)‖ := by congr 1; ring
      _ ≤ ‖y - z‖ + ‖z - 0‖ + ‖x - 0‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
      _ < ρ := by
        simp only [sub_zero]
        linarith
  have hint : IntegrableOn (fun y : ℂ => ‖x - y‖⁻¹) (ball x ρ) :=
    integrableOn_comp_sub_ball (f := fun w : ℂ => ‖w‖⁻¹) integrableOn_inv_norm_ball_zero x x ρ
  calc ∫ y in ball z a, ‖x - y‖⁻¹ ≤ ∫ y in ball x ρ, ‖x - y‖⁻¹ :=
        setIntegral_mono_set hint (Filter.Eventually.of_forall fun y => by positivity)
          (Filter.Eventually.of_forall hsub)
    _ = ∫ w in ball (0 : ℂ) ρ, ‖w‖⁻¹ := by
        rw [setIntegral_ball_eq_setIntegral_ball_zero_of_vec]
        simp

/-- The point field `y ↦ -(x - y) / |x - y|²` is integrable against `δ_z^{(a)}`. -/
theorem integrable_gradLogKernel_sub_smearedCharge {a : ℝ} (ha : 0 < a) (x z : ℂ) :
    Integrable (fun y : ℂ => -((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y)) (smearedCharge z a) := by
  rw [smearedCharge_eq]
  refine Integrable.smul_measure ?_
    (ENNReal.inv_ne_top.2 (Metric.measure_ball_pos volume z ha).ne')
  exact integrableOn_comp_sub_ball (f := fun w : ℂ => -((‖w‖ ^ 2)⁻¹ : ℝ) • w)
    integrableOn_gradLogKernel_ball_zero x z a

/-- The modulus `y ↦ |x - y|⁻¹` of the point field is integrable against `δ_z^{(a)}`. -/
theorem integrable_inv_norm_sub_smearedCharge {a : ℝ} (ha : 0 < a) (x z : ℂ) :
    Integrable (fun y : ℂ => ‖x - y‖⁻¹) (smearedCharge z a) := by
  rw [smearedCharge_eq]
  refine Integrable.smul_measure ?_
    (ENNReal.inv_ne_top.2 (Metric.measure_ball_pos volume z ha).ne')
  exact integrableOn_comp_sub_ball (f := fun w : ℂ => ‖w‖⁻¹) integrableOn_inv_norm_ball_zero x z a

/-- Integrability of `(x, y) ↦ ∇ξ(x) · ∇g(x - y)` for the product of Lebesgue measure and the
uniform measure on a disc. -/
theorem integrable_fderiv_apply_gradLogKernel_sub_smearedCharge {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) {a : ℝ} (ha : 0 < a) (z : ℂ) :
    Integrable (fun p : ℂ × ℂ => fderiv ℝ ξ p.1 (-((‖p.1 - p.2‖ ^ 2)⁻¹ : ℝ) • (p.1 - p.2)))
      (volume.prod (smearedCharge z a)) := by
  have := isProbabilityMeasure_smearedCharge z ha
  obtain ⟨C, hC⟩ := (hξ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ))
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1 hc.isCompact.isBounded
  obtain ⟨M, hM⟩ := exists_integral_inv_norm_sub_smearedCharge_le z ha R
  have hmeas := (measurable_fderiv_apply_gradLogKernel_sub hξ).aestronglyMeasurable
    (μ := volume.prod (smearedCharge z a))
  have hvanish : ∀ x, x ∉ ball (0 : ℂ) R → fderiv ℝ ξ x = 0 := fun x hx =>
    fderiv_of_notMem_tsupport ℝ fun h => hx (hR h)
  have hnorm : ∀ x y : ℂ, ‖fderiv ℝ ξ x (-((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y))‖ ≤
      ‖fderiv ℝ ξ x‖ * ‖x - y‖⁻¹ := fun x y => by
    refine ((fderiv ℝ ξ x).le_opNorm _).trans ?_
    rw [norm_gradLogKernel]
  have hinv : ∀ x : ℂ, Integrable (fun y : ℂ => ‖x - y‖⁻¹) (smearedCharge z a) :=
    fun x => integrable_inv_norm_sub_smearedCharge ha x z
  rw [integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · -- integrability in `y` for fixed `x`
    exact (fderiv ℝ ξ x).integrable_comp (integrable_gradLogKernel_sub_smearedCharge ha x z)
  · -- integrability in `x` of the `y`-integral of the norm
    have hg : Integrable (indicator (ball (0 : ℂ) R) fun _ : ℂ => C * M) := by
      rw [integrable_indicator_iff measurableSet_ball]
      exact integrableOn_const measure_ball_lt_top.ne
    refine hg.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact hmeas.norm.integral_prod_right'
    · by_cases hx : x ∈ ball (0 : ℂ) R
      · rw [indicator_of_mem hx]
        rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
        calc ∫ y, ‖fderiv ℝ ξ x (-((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y))‖ ∂smearedCharge z a
            ≤ ∫ y, C * ‖x - y‖⁻¹ ∂smearedCharge z a := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
                ?_ (Filter.Eventually.of_forall fun y => ?_)
              · exact (hinv x).const_mul C
              · exact (hnorm x y).trans (mul_le_mul_of_nonneg_right (hC x) (by positivity))
          _ = C * ∫ y, ‖x - y‖⁻¹ ∂smearedCharge z a := integral_const_mul _ _
          _ ≤ C * M := by
              refine mul_le_mul_of_nonneg_left (hM x hx) ?_
              exact (norm_nonneg _).trans (hC 0)
      · rw [indicator_of_notMem hx]
        simp [hvanish x hx]

/-- **The smeared Green identity** (the single-charge identity used in Theorem 2, Step 1,
source l. 1842–1866): for `ξ` of class `C¹` with compact support,
`∫ ∇ξ(x) · discField a (x - z) dx = 2π ∫ ξ dδ_z^{(a)}`. -/
theorem integral_fderiv_apply_discField {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport ξ) {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ∫ x, fderiv ℝ ξ x (discField a (x - z)) = 2 * Real.pi * ∫ y, ξ y ∂smearedCharge z a := by
  have hprod := integrable_fderiv_apply_gradLogKernel_sub_smearedCharge hξ hc ha z
  have h1 : ∀ x : ℂ, fderiv ℝ ξ x (discField a (x - z)) =
      ∫ y, fderiv ℝ ξ x (-((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y)) ∂smearedCharge z a := fun x => by
    rw [← integral_gradLogKernel_smearedCharge ha x z]
    exact ((fderiv ℝ ξ x).integral_comp_comm
      (integrable_gradLogKernel_sub_smearedCharge ha x z)).symm
  simp_rw [h1]
  rw [integral_integral_swap
    (f := fun x y => fderiv ℝ ξ x (-((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y))) hprod]
  simp_rw [integral_fderiv_apply_gradLogKernel hξ hc]
  rw [integral_const_mul]

/-- **Newton's theorem**: `discPotential a` is the potential `g * δ_0^{(a)}` of the uniform disc,
i.e. `∫ g(x - y) dδ_z^{(a)}(y) = discPotential a (x - z)`. -/
theorem integral_logKernel_sub_smearedCharge_eq_discPotential {a : ℝ} (ha : 0 < a) (x z : ℂ) :
    ∫ y, logKernel (x - y) ∂smearedCharge z a = discPotential a (x - z) := by
  rw [integral_smearedCharge _ z ha]
  simp only [logKernel, integral_neg, smul_eq_mul]
  unfold discPotential
  rcases le_total a ‖x - z‖ with h | h
  · rw [setIntegral_log_norm_sub_ball_of_le x z ha h, max_eq_right h, min_eq_right h]
    field_simp
    simp
  · rw [setIntegral_log_norm_sub_ball_of_ge x z ha h, max_eq_left h, min_eq_left h]
    field_simp
    ring

/-! ### Gradient of the potential -/

/-- The radial profile of the disc potential as a function of `t = |u|²`. -/
noncomputable def discProfile (a t : ℝ) : ℝ :=
  -Real.log (max (a ^ 2) t) / 2 + (1 - min t (a ^ 2) / a ^ 2) / 2

/-- The disc potential is a function of `|u|²`: `discPotential a u = discProfile a (|u|²)`. -/
theorem discPotential_eq_discProfile {a : ℝ} (ha : 0 < a) (u : ℂ) :
    discPotential a u = discProfile a (‖u‖ ^ 2) := by
  unfold discPotential discProfile
  rcases le_total a ‖u‖ with h | h
  · have h2 : a ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ ha.le h 2
    rw [max_eq_right h, min_eq_right h, max_eq_right h2, min_eq_right h2, Real.log_pow]
    push_cast
    ring
  · have h2 : ‖u‖ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [max_eq_left h, min_eq_left h, max_eq_left h2, min_eq_left h2, Real.log_pow]
    push_cast
    ring

/-- The profile `discProfile a` is differentiable on all of `ℝ`, with derivative
`-1 / (2 max(a², t))`. The two closed forms agree to first order at `t = a²`. -/
theorem hasDerivAt_discProfile {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (discProfile a) (-(2 * max (a ^ 2) t)⁻¹) t := by
  have hA : 0 < a ^ 2 := by positivity
  set A : ℝ := a ^ 2 with hAdef
  have hPin : ∀ s : ℝ, HasDerivAt (fun s : ℝ => -Real.log A / 2 + (1 - s / A) / 2)
      (-(2 * A)⁻¹) s := by
    intro s
    have := ((((hasDerivAt_id' s).div_const A).const_sub 1).div_const 2).const_add
      (-Real.log A / 2)
    exact this.congr_deriv (by field_simp)
  have hPout : ∀ s : ℝ, 0 < s → HasDerivAt (fun s : ℝ => -Real.log s / 2) (-(2 * s)⁻¹) s := by
    intro s hs
    have := ((Real.hasDerivAt_log hs.ne').neg).div_const 2
    exact this.congr_deriv (by field_simp)
  have hin : ∀ s ∈ Iic A, discProfile a s = -Real.log A / 2 + (1 - s / A) / 2 := by
    intro s hs
    unfold discProfile
    rw [max_eq_left hs, min_eq_left hs]
  have hout : ∀ s ∈ Ici A, discProfile a s = -Real.log s / 2 := by
    intro s hs
    unfold discProfile
    rw [max_eq_right hs, min_eq_right hs, div_self hA.ne']
    ring
  rcases lt_trichotomy t A with h | h | h
  · rw [max_eq_left h.le]
    exact (hPin t).congr_of_eventuallyEq
      (by filter_upwards [Iio_mem_nhds h] with s hs using hin s (show s ≤ A from hs.le))
  · rw [h, max_self]
    have h1 : HasDerivWithinAt (discProfile a) (-(2 * A)⁻¹) (Iic A) A := by
      refine ((hPin A).hasDerivWithinAt).congr (fun s hs => hin s hs) (hin A (mem_Iic.2 le_rfl))
    have h2 : HasDerivWithinAt (discProfile a) (-(2 * A)⁻¹) (Ici A) A := by
      refine ((hPout A hA).hasDerivWithinAt).congr (fun s hs => hout s hs)
        (hout A (mem_Ici.2 le_rfl))
    have := h1.union h2
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
    exact this
  · rw [max_eq_right h.le]
    exact (hPout t (hA.trans h)).congr_of_eventuallyEq
      (by filter_upwards [Ioi_mem_nhds h] with s hs using hout s (show A ≤ s from hs.le))

/-- `max (a², b²) = (max (a, b))²` for nonnegative `a`, `b`. -/
theorem max_sq_eq_sq_max {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (a ^ 2) (b ^ 2) = max a b ^ 2 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ ha h 2)]
  · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ hb h 2)]

/-- **The gradient of the potential of a uniform disc.** -/
theorem hasGradientAt_discPotential {a : ℝ} (ha : 0 < a) (u : ℂ) :
    HasGradientAt (discPotential a) (discField a u) u := by
  have h1 := (hasDerivAt_discProfile ha (‖u‖ ^ 2)).comp_hasFDerivAt u
    (hasStrictFDerivAt_norm_sq u).hasFDerivAt
  have heq : discPotential a = discProfile a ∘ fun x : ℂ => ‖x‖ ^ 2 :=
    funext fun v => discPotential_eq_discProfile ha v
  rw [hasGradientAt_iff_hasFDerivAt, heq]
  refine h1.congr_fderiv ?_
  ext v
  simp only [discField, toDual_apply_apply, smul_apply, innerSL_apply_apply,
    nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, real_inner_smul_left,
    max_sq_eq_sq_max ha.le (norm_nonneg u)]
  have : 0 < max a ‖u‖ := lt_of_lt_of_le ha (le_max_left _ _)
  field_simp

/-- The Fréchet derivative of `discPotential a` at `u`, in the `fderiv` form of the gradient. -/
theorem hasFDerivAt_discPotential {a : ℝ} (ha : 0 < a) (u : ℂ) :
    HasFDerivAt (discPotential a) (toDual ℝ ℂ (discField a u)) u :=
  (hasGradientAt_discPotential ha u).hasFDerivAt

/-- `discPotential a` is differentiable on `ℂ`. -/
theorem differentiable_discPotential {a : ℝ} (ha : 0 < a) : Differentiable ℝ (discPotential a) :=
  fun u => (hasFDerivAt_discPotential ha u).differentiableAt

/-- The field of the disc is continuous. -/
theorem continuous_discField {a : ℝ} (ha : 0 < a) : Continuous (discField a) := by
  unfold discField
  have hpos : ∀ u : ℂ, max a ‖u‖ ^ 2 ≠ 0 := fun u =>
    pow_ne_zero 2 (lt_of_lt_of_le ha (le_max_left _ _)).ne'
  exact (((continuous_const.max continuous_norm).pow 2).inv₀ hpos).neg.smul continuous_id

/-- `discPotential a` is of class `C¹` (it is `C^{1,1}`, not `C²`, across the circle `|u| = a`). -/
theorem contDiff_discPotential {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (discPotential a) := by
  refine contDiff_one_iff_fderiv.2 ⟨differentiable_discPotential ha, ?_⟩
  have : fderiv ℝ (discPotential a) = fun u => toDual ℝ ℂ (discField a u) :=
    funext fun u => (hasFDerivAt_discPotential ha u).fderiv
  rw [this]
  exact (toDual ℝ ℂ).continuous.comp (continuous_discField ha)

/-! ### Lipschitz continuity of the gradient -/

private lemma discField_one_mixed {x y : ℂ} (hx : ‖x‖ ≤ 1) (hy : 1 ≤ ‖y‖) :
    ‖discField 1 x - discField 1 y‖ ≤ ‖x - y‖ := by
  have hb : 0 < ‖y‖ := lt_of_lt_of_le one_pos hy
  have hq : 0 ≤ (‖y‖ ^ 2)⁻¹ := by positivity
  have hq1 : (‖y‖ ^ 2)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 (by nlinarith)
  have hc : inner ℝ x y ≤ ‖y‖ :=
    (real_inner_le_norm x y).trans (by nlinarith [norm_nonneg y])
  have hp : 0 ≤ ‖y‖ ^ 2 + 1 - 2 * inner ℝ x y := by
    nlinarith [sq_nonneg (‖y‖ - 1)]
  have he : ‖x - y‖ ^ 2 - ‖x - (‖y‖ ^ 2)⁻¹ • y‖ ^ 2 =
      (1 - (‖y‖ ^ 2)⁻¹) * (‖y‖ ^ 2 + 1 - 2 * inner ℝ x y) := by
    simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq,
      real_inner_smul_right]
    field_simp
    ring
  have hs : ‖x - (‖y‖ ^ 2)⁻¹ • y‖ ≤ ‖x - y‖ := by
    have := mul_nonneg (sub_nonneg.2 hq1) hp
    rw [← he] at this
    nlinarith [norm_nonneg (x - (‖y‖ ^ 2)⁻¹ • y), norm_nonneg (x - y)]
  simpa only [discField, max_eq_left hx, max_eq_right hy, one_pow, inv_one,
    neg_smul, one_smul, neg_sub_neg, norm_sub_rev] using hs

/-- The gradient of the unit-disc potential is `1`-Lipschitz (source (idg1)). -/
theorem lipschitzWith_discField_one : LipschitzWith 1 (discField 1) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  simp only [NNReal.coe_one, one_mul]
  by_cases hx : ‖x‖ ≤ 1
  · by_cases hy : ‖y‖ ≤ 1
    · simp only [discField, max_eq_left hx, max_eq_left hy, one_pow, inv_one,
        neg_one_smul, neg_sub_neg, norm_sub_rev, le_refl]
    · exact discField_one_mixed hx (le_of_not_ge hy)
  · by_cases hy : ‖y‖ ≤ 1
    · simpa only [norm_sub_rev] using discField_one_mixed hy (le_of_not_ge hx)
    · have hx0 : x ≠ 0 := norm_pos_iff.1 (by linarith [lt_of_not_ge hx])
      have hy0 : y ≠ 0 := norm_pos_iff.1 (by linarith [lt_of_not_ge hy])
      have he : ∀ u : ℂ, 1 ≤ ‖u‖ → discField 1 u = -(starRingEnd ℂ) u⁻¹ := by
        intro u hu
        simpa only [discField, max_eq_right hu] using gradLogKernel_eq_neg_conj_inv u
      rw [he x (le_of_not_ge hx), he y (le_of_not_ge hy), neg_sub_neg,
        ← map_sub, Complex.norm_conj]
      have hd := dist_inv_inv₀ hx0 hy0
      rw [dist_eq_norm, dist_eq_norm] at hd
      rw [norm_sub_rev, hd]
      exact div_le_self (norm_nonneg _) (by nlinarith [lt_of_not_ge hx, lt_of_not_ge hy])

/-- Scaling the disc field to radius one. -/
theorem discField_eq_smul_one {a : ℝ} (ha : 0 < a) (u : ℂ) :
    discField a u = a⁻¹ • discField 1 (a⁻¹ • u) := by
  have hm : max 1 (a⁻¹ * ‖u‖) = a⁻¹ * max a ‖u‖ := by
    rw [mul_max_of_nonneg _ _ (inv_nonneg.2 ha.le), inv_mul_cancel₀ ha.ne']
  simp only [discField, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha.le), hm,
    smul_smul]
  congr 1
  field_simp

/-- Positive-radius disc potentials have Lipschitz gradients, hence are locally `C^{1,1}`. -/
theorem lipschitzWith_discField {a : ℝ} (ha : 0 < a) :
    LipschitzWith ((a ^ 2)⁻¹).toNNReal (discField a) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  simp only [Real.coe_toNNReal _ (inv_nonneg.2 (sq_nonneg a))]
  rw [discField_eq_smul_one ha x, discField_eq_smul_one ha y, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 ha.le)]
  calc a⁻¹ * ‖discField 1 (a⁻¹ • x) - discField 1 (a⁻¹ • y)‖
      ≤ a⁻¹ * ‖a⁻¹ • x - a⁻¹ • y‖ := by
        gcongr
        simpa using lipschitzWith_discField_one.norm_sub_le (a⁻¹ • x) (a⁻¹ • y)
    _ = (a ^ 2)⁻¹ * ‖x - y‖ := by
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha.le)]
        ring

end TwoComponentCoulomb

end
