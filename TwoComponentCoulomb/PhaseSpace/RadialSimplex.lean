/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import TwoComponentCoulomb.Integrals.Dirichlet
public import TwoComponentCoulomb.LowerBound.PolarPi

/-!
# Radial integrals over a ball of `κ → ℂ` reduce to the simplex

Source l. 832–843 (polar reduction of the integral over `B_2`). For a finite index type `κ`
and measurable functions `g_i : ℝ → [0,∞]`, the integral of the product of radial weights
`∏_i g_i(|u_i|)` over the ball `{u : κ → ℂ | ∑_i |u_i|² ≤ s}` becomes, after the substitution
`t_i = |u_i|²` (each `u_i ∈ ℂ` contributes `2π r dr = π dt`), an integral over the open simplex
`{t ∈ (0,∞)^κ | ∑ t_i < s}` (the boundary `{∑ t_i = s}` and the coordinate hyperplanes are
Lebesgue-null):
`∫⁻_{∑|u_i|² ≤ s} ∏ g_i(|u_i|) du = π^|κ| ∫⁻_{t ∈ (0,∞)^κ, ∑ t_i < s} ∏ g_i(√t_i) dt`.

## Main results

* `TwoComponentCoulomb.lintegral_complex_comp_norm_sq`: `∫⁻_ℂ φ(|u|²) = π ∫⁻_{(0,∞)} φ`.
* `TwoComponentCoulomb.map_norm_sq_volume`, `TwoComponentCoulomb.map_pi_norm_sq_volume`:
  the push-forwards of Lebesgue measure under `u ↦ |u|²`, coordinatewise on `κ → ℂ`.
* `TwoComponentCoulomb.volume_sum_eq_const`: the hyperplane `{∑ t_i = s}` is null.
* `TwoComponentCoulomb.lintegral_sumSq_le_prod_radial_eq`: the reduction for an arbitrary
  finite index type.
* `TwoComponentCoulomb.lintegral_ball_prod_radial_eq`: the same for `κ = Fin n`, with the domain
  `posSimplex n s`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### One complex coordinate -/

/-- Radial functions of `|u|²` on the plane: `∫⁻_ℂ φ(|u|²) du = π ∫⁻_{t > 0} φ(t) dt`. -/
theorem lintegral_complex_comp_norm_sq (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ u : ℂ, φ (‖u‖ ^ 2) = ENNReal.ofReal Real.pi * ∫⁻ t in Ioi (0 : ℝ), φ t := by
  have h := lintegral_radial_set Set.univ MeasurableSet.univ (fun r => φ (r ^ 2))
    (hφ.comp (measurable_id.pow_const 2))
  simp only [Set.mem_univ, Set.ofPred_true, Measure.restrict_univ, Set.indicator_univ] at h
  rw [h]
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x ^ 2) (2 * x) (Ioi 0) x := by
    intro x _
    have := (hasDerivAt_pow 2 x).hasDerivWithinAt (s := Ioi (0 : ℝ))
    simpa using this
  have hinj : Set.InjOn (fun x : ℝ => x ^ 2) (Ioi 0) := by
    intro x hx y hy hxy
    exact (pow_left_inj₀ (le_of_lt hx) (le_of_lt hy) two_ne_zero).1 hxy
  have himg : (fun x : ℝ => x ^ 2) '' Ioi 0 = Ioi 0 := by
    ext y
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      positivity
    · intro hy
      exact ⟨Real.sqrt y, Real.sqrt_pos.2 hy, Real.sq_sqrt hy.le⟩
  have hsub := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj φ
  rw [himg] at hsub
  rw [hsub, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : 0 < t := ht
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * t), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The push-forward of Lebesgue measure on `ℂ` under `u ↦ |u|²` is `π` times Lebesgue measure
on `(0,∞)`. -/
theorem map_norm_sq_volume :
    Measure.map (fun u : ℂ => ‖u‖ ^ 2) volume =
      ENNReal.ofReal Real.pi • (volume : Measure ℝ).restrict (Ioi 0) := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map hφ (measurable_norm.pow_const 2), lintegral_complex_comp_norm_sq φ hφ,
    lintegral_smul_measure, smul_eq_mul]

/-! ### Several coordinates -/

section Pi

variable {κ : Type*} [Fintype κ]

/-- A constant multiple in each factor of a product measure pulls out as a power. -/
theorem pi_smul_eq (ν : Measure ℝ) (c : ℝ≥0∞) [SigmaFinite ν] [SigmaFinite (c • ν)] :
    Measure.pi (fun _ : κ => c • ν) = c ^ Fintype.card κ • Measure.pi (fun _ : κ => ν) := by
  refine Measure.pi_eq fun s _ => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

/-- The push-forward of Lebesgue measure on `κ → ℂ` under the coordinatewise map `u ↦ (|u_i|²)`
is `π^|κ|` times Lebesgue measure restricted to the open orthant `(0,∞)^κ`. -/
theorem map_pi_norm_sq_volume :
    Measure.map (fun (u : κ → ℂ) i => ‖u i‖ ^ 2) volume =
      ENNReal.ofReal Real.pi ^ Fintype.card κ •
        (volume : Measure (κ → ℝ)).restrict (Set.univ.pi fun _ : κ => Ioi (0 : ℝ)) := by
  have : SigmaFinite (ENNReal.ofReal Real.pi • (volume : Measure ℝ).restrict (Ioi 0)) :=
    (inferInstance : SigmaFinite ((Real.toNNReal Real.pi) • (volume : Measure ℝ).restrict (Ioi 0)))
  have : SigmaFinite (Measure.map (fun u : ℂ => ‖u‖ ^ 2) volume) := by
    rw [map_norm_sq_volume]
    infer_instance
  rw [volume_pi, Measure.pi_map_pi (fun _ => (measurable_norm.pow_const 2).aemeasurable),
    map_norm_sq_volume, pi_smul_eq, volume_pi, Measure.restrict_pi_pi]

/-- A hyperplane `{t | ∑ t_i = s}` of `κ → ℝ` (`κ` nonempty) is Lebesgue-null. -/
theorem volume_sum_eq_const [Nonempty κ] (s : ℝ) :
    (volume : Measure (κ → ℝ)) {t | ∑ i, t i = s} = 0 := by
  obtain ⟨i₀⟩ := ‹Nonempty κ›
  classical
  let L : (κ → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hL : ∀ t, L t = ∑ i, t i := fun t => by simp [L]
  have hK : LinearMap.ker L ≠ ⊤ := by
    intro h
    have h1 : (Pi.single i₀ (1 : ℝ) : κ → ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hL] at h1
    simp at h1
  have hset : {t : κ → ℝ | ∑ i, t i = s} =
      (fun t => t + (-(Pi.single i₀ s : κ → ℝ))) ⁻¹' (LinearMap.ker L : Set (κ → ℝ)) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, hL,
      Pi.add_apply, Pi.neg_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_pi_single']
    simp only [Finset.mem_univ, ite_true]
    constructor <;> intro h <;> linarith
  rw [hset, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume _ hK

/-- **Polar reduction to the simplex** (source l. 832–843): for a finite index type `κ`,
measurable `g_i : ℝ → [0,∞]` and `s > 0`,
`∫⁻_{∑|u_i|² ≤ s} ∏ g_i(|u_i|) du = π^|κ| ∫⁻_{t ∈ (0,∞)^κ, ∑ t_i < s} ∏ g_i(√t_i) dt`. -/
theorem lintegral_sumSq_le_prod_radial_eq {s : ℝ} (hs : 0 < s) (g : κ → ℝ → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) :
    ∫⁻ u in {u : κ → ℂ | ∑ i, ‖u i‖ ^ 2 ≤ s}, ∏ i, g i ‖u i‖ =
      ENNReal.ofReal Real.pi ^ Fintype.card κ *
        ∫⁻ t in {t : κ → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < s},
          ∏ i, g i (Real.sqrt (t i)) := by
  set T : (κ → ℂ) → (κ → ℝ) := fun u i => ‖u i‖ ^ 2 with hT
  set Ψ : (κ → ℝ) → ℝ≥0∞ := fun t => ∏ i, g i (Real.sqrt (t i)) with hΨ
  set A : Set (κ → ℝ) := {t | ∑ i, t i ≤ s} with hA
  set P : Set (κ → ℝ) := Set.univ.pi fun _ => Ioi (0 : ℝ) with hP
  have hTm : Measurable T :=
    measurable_pi_iff.2 fun i => ((measurable_pi_apply i).norm).pow_const 2
  have hΨm : Measurable Ψ :=
    Finset.measurable_prod _ fun i _ =>
      (hg i).comp (Real.continuous_sqrt.measurable.comp (measurable_pi_apply i))
  have hAm : MeasurableSet A :=
    measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const
  have h1 : ∫⁻ u in {u : κ → ℂ | ∑ i, ‖u i‖ ^ 2 ≤ s}, ∏ i, g i ‖u i‖ =
      ∫⁻ u in T ⁻¹' A, Ψ (T u) := by
    have hfun : (fun u : κ → ℂ => ∏ i, g i ‖u i‖) = fun u => Ψ (T u) := by
      funext u
      simp only [hΨ, hT, Real.sqrt_sq (norm_nonneg _)]
    rw [hfun]
    rfl
  have hae : (A ∩ P : Set (κ → ℝ)) =ᵐ[volume]
      {t : κ → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < s} := by
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · have : A ∩ P = {t : κ → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < s} := by
        ext t
        simp [hA, hP, hs, hs.le]
      rw [this]
    · rw [ae_eq_set]
      refine ⟨measure_mono_null ?_ (volume_sum_eq_const s), ?_⟩
      · rintro t ⟨⟨htA, htP⟩, hnot⟩
        have htP' : ∀ i, 0 < t i := fun i => htP i (Set.mem_univ i)
        have hle : ∑ i, t i ≤ s := htA
        refine le_antisymm hle (not_lt.1 fun hlt => hnot ⟨htP', hlt⟩)
      · convert measure_empty (μ := (volume : Measure (κ → ℝ)))
        refine Set.eq_empty_of_forall_notMem fun t ht => ht.2 ⟨ht.1.2.le, fun i _ => ht.1.1 i⟩
  rw [h1, ← setLIntegral_map hAm hΨm hTm, map_pi_norm_sq_volume, Measure.restrict_smul,
    lintegral_smul_measure, smul_eq_mul, Measure.restrict_restrict hAm]
  congr 1
  exact setLIntegral_congr hae

end Pi

/-- **Polar reduction to the simplex** for `κ = Fin n` (source l. 832–843):
`∫⁻_{∑|u_i|² ≤ s} ∏ g_i(|u_i|) du = π^n ∫⁻_{t ∈ (0,∞)^n, ∑ t_i < s} ∏ g_i(√t_i) dt`. -/
theorem lintegral_ball_prod_radial_eq {n : ℕ} {s : ℝ} (hs : 0 < s) (g : Fin n → ℝ → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) :
    ∫⁻ u in {u : Fin n → ℂ | ∑ i, ‖u i‖ ^ 2 ≤ s}, ∏ i, g i ‖u i‖ =
      ENNReal.ofReal Real.pi ^ n *
        ∫⁻ t in {t : Fin n → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < s},
          ∏ i, g i (Real.sqrt (t i)) := by
  simpa using lintegral_sumSq_le_prod_radial_eq hs g hg

/-- The domain of `lintegral_ball_prod_radial_eq` is the open simplex `posSimplex n s` of the
Dirichlet integral (Lemma 3.1). -/
theorem lintegral_ball_prod_radial_eq_posSimplex {n : ℕ} {s : ℝ} (hs : 0 < s)
    (g : Fin n → ℝ → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    ∫⁻ u in {u : Fin n → ℂ | ∑ i, ‖u i‖ ^ 2 ≤ s}, ∏ i, g i ‖u i‖ =
      ENNReal.ofReal Real.pi ^ n *
        ∫⁻ t in posSimplex n s, ∏ i, g i (Real.sqrt (t i)) :=
  lintegral_ball_prod_radial_eq hs g hg


end TwoComponentCoulomb

end
