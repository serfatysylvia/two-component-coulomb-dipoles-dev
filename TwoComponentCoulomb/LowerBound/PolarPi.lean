/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Polar coordinates on `ℂ` and on `Fin N → ℂ`, and a Fubini lemma for products of radial weights

Tools for the dipole lower bound of Proposition 4.1 (source Step 1, by the
route of ruling R12a), where each displacement `y_i - x_i = s_i e^{iθ_i}` is written in polar
coordinates.

* `lintegral_complex_eq_polar` : `∫⁻_ℂ f = ∫⁻_{s > 0} ∫⁻_{|θ| < π} s f(s e^{iθ})`.
* `lintegral_pi_complex_eq_polar` : the same on `(Fin N → ℂ)`, with the weight `∏ s_i`.
* `lintegral_fin_prod_eq_prod` : Tonelli for a product of one-variable functions on `Fin n → ℝ`.
* `lintegral_radial_set` : the integral of a radial function over `{u | |u| ∈ R}`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### Polar coordinates -/

/-- `Complex.polarCoord.symm (s, θ) = s e^{iθ}`, in the form of Mathlib's `circleMap`. -/
theorem polarCoord_symm_apply_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

/-- `(s, θ) ↦ s e^{iθ}` is measurable. -/
theorem measurable_circleMap_zero_uncurry : Measurable fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
  simp only [circleMap_zero]
  fun_prop

/-- Polar coordinates in the plane for a nonnegative function:
`∫⁻_ℂ f = ∫⁻_{s > 0} ∫⁻_{θ ∈ (-π, π)} s f(s e^{iθ})`. -/
theorem lintegral_complex_eq_polar (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal s * f (circleMap 0 s θ) := by
  rw [← Complex.lintegral_comp_polarCoord_symm f]
  simp only [polarCoord_symm_apply_eq_circleMap, smul_eq_mul]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  exact ((ENNReal.measurable_ofReal.comp measurable_fst).mul
    (hf.comp measurable_circleMap_zero_uncurry)).aemeasurable

/-- Polar coordinates in each of the `N` coordinates of `Fin N → ℂ`:
`∫⁻ G = ∫⁻_{s ∈ (0,∞)^N} ∫⁻_{θ ∈ (-π,π)^N} (∏ s_i) G(s_i e^{iθ_i})`. -/
theorem lintegral_pi_complex_eq_polar {N : ℕ} (G : (Fin N → ℂ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ u, G u = ∫⁻ s in Set.univ.pi (fun _ : Fin N => Ioi (0 : ℝ)),
      ∫⁻ θ in Set.univ.pi (fun _ : Fin N => Ioo (-Real.pi) Real.pi),
        (∏ i, ENNReal.ofReal (s i)) * G (fun i => circleMap 0 (s i) (θ i)) := by
  rw [← Complex.lintegral_comp_pi_polarCoord_symm G]
  simp only [polarCoord_symm_apply_eq_circleMap]
  set g : (Fin N → ℝ) × (Fin N → ℝ) → ℝ≥0∞ := fun q =>
    (∏ i, ENNReal.ofReal (q.1 i)) * G (fun i => circleMap 0 (q.1 i) (q.2 i)) with hg
  have hgm : Measurable g := by
    have h1 : Measurable fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
        fun i => circleMap 0 (q.1 i) (q.2 i) := by
      refine measurable_pi_iff.2 fun i => ?_
      exact measurable_circleMap_zero_uncurry.comp
        (by fun_prop : Measurable fun q : (Fin N → ℝ) × (Fin N → ℝ) => (q.1 i, q.2 i))
    have h2 : Measurable fun q : (Fin N → ℝ) × (Fin N → ℝ) => ∏ i, ENNReal.ofReal (q.1 i) := by
      fun_prop
    exact h2.mul (hG.comp h1)
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N) (fun _ => volume)
    (fun _ => volume)
  have hpre : (Set.univ.pi fun _ : Fin N => Complex.polarCoord.target) =
      MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin N) ⁻¹'
        ((Set.univ.pi fun _ : Fin N => Ioi (0 : ℝ)) ×ˢ
          (Set.univ.pi fun _ : Fin N => Ioo (-Real.pi) Real.pi)) := by
    ext p
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_preimage, Set.mem_prod,
      Complex.polarCoord_target, Set.mem_Ioi, Set.mem_Ioo, forall_and]
    exact Iff.rfl
  have h := hmp.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin N)).measurableEmbedding g
    ((Set.univ.pi fun _ : Fin N => Ioi (0 : ℝ)) ×ˢ
      (Set.univ.pi fun _ : Fin N => Ioo (-Real.pi) Real.pi))
  rw [hpre]
  refine h.trans ?_
  have h3 : ((volume : Measure (Fin N → ℝ)).prod (volume : Measure (Fin N → ℝ))).restrict
      ((Set.univ.pi fun _ : Fin N => Ioi (0 : ℝ)) ×ˢ
        (Set.univ.pi fun _ : Fin N => Ioo (-Real.pi) Real.pi)) =
      ((volume : Measure (Fin N → ℝ)).restrict (Set.univ.pi fun _ : Fin N => Ioi (0 : ℝ))).prod
        ((volume : Measure (Fin N → ℝ)).restrict
          (Set.univ.pi fun _ : Fin N => Ioo (-Real.pi) Real.pi)) :=
    (Measure.prod_restrict _ _).symm
  change ∫⁻ b in _, g b ∂((volume : Measure (Fin N → ℝ)).prod (volume : Measure (Fin N → ℝ))) = _
  rw [h3, lintegral_prod _ hgm.aemeasurable]

/-! ### Products of one-variable functions -/

/-- **Tonelli** for a product of functions of one variable each, on `Fin n → ℝ`. -/
theorem lintegral_fin_prod_eq_prod {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → ℝ, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : ℝ × (Fin n → ℝ),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : ℝ), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf _),
            ← lintegral_prod_mul (hf 0).aemeasurable]
          exact (Finset.measurable_prod _ fun i _ =>
            (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/-! ### Radial functions -/

/-- The integral of a radial function `ρ(|u|)` over the set `{u | |u| ∈ R}` of the plane, in polar
coordinates: `∫⁻_{|u| ∈ R} ρ(|u|) du = ∫⁻_{t > 0} t · 1_R(t) ρ(t) · 2π dt`. -/
theorem lintegral_radial_set (R : Set ℝ) (hR : MeasurableSet R) (ρ : ℝ → ℝ≥0∞)
    (hρ : Measurable ρ) :
    ∫⁻ u in {u : ℂ | ‖u‖ ∈ R}, ρ ‖u‖ =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t * (R.indicator ρ t * ENNReal.ofReal (2 * Real.pi)) := by
  have hS : MeasurableSet {u : ℂ | ‖u‖ ∈ R} := measurable_norm hR
  have hm : Measurable ({u : ℂ | ‖u‖ ∈ R}.indicator fun u => ρ ‖u‖) :=
    (hρ.comp measurable_norm).indicator hS
  rw [← lintegral_indicator hS, lintegral_complex_eq_polar _ hm]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have h1 : ∀ θ : ℝ, {u : ℂ | ‖u‖ ∈ R}.indicator (fun u => ρ ‖u‖) (circleMap 0 t θ) =
      R.indicator ρ t := by
    intro θ
    have : ‖circleMap 0 t θ‖ = t := by rw [norm_circleMap_zero, abs_of_pos ht]
    by_cases h : t ∈ R
    · simp [Set.indicator_of_mem, this, h]
    · simp [Set.indicator_of_notMem, this, h]
  simp only [h1, setLIntegral_const, Real.volume_Ioo]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
  ring

end TwoComponentCoulomb

end
