/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TwoComponentCoulomb.Potential.DiscPotential
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# The divergence theorem on a disc

Mathlib proves the divergence theorem on boxes only. Proposition 4.1, Step 1, of the
paper (l. 1671–1734) solves Neumann problems on disjoint discs
(ruling R22a); we verify them in weak form, which needs the divergence theorem on a closed disc of
`ℂ ≅ ℝ²` for fields of class `C¹`.

* `divergence F z = ∂₁F₁(z) + ∂₂F₂(z)` for `F : ℂ → ℂ`.
* `integral_ball_divergence` : for `F` of class `C¹` on an open set containing `B̄(c, ρ)`,
  `∫_{B(c,ρ)} div F = ρ ∫_{-π}^{π} ⟪F(c + ρe^{iθ}), e^{iθ}⟫ dθ`.
* `divergence_smul` : the product rule `div (φ G) = ∇φ · G + φ div G`.
* `divergence_conj` : the conjugate of a holomorphic function is divergence free.
* `integral_ball_fderiv_apply_of_divergence_eq_zero` : Green's identity on a disc for a
  divergence-free field `G`, `∫_{B(c,ρ)} ∇φ · G = ρ ∫_{-π}^{π} φ ⟪G, e^{iθ}⟫ dθ`.

The proof maps the rectangle `[0, ρ] × [-π, π]` to the disc by the polar coordinates
`(r, θ) ↦ c + r e^{iθ}` and applies Mathlib's divergence theorem on the rectangle
(`MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`) to the pair of functions
`f(r, θ) = r ⟪F(c + r e^{iθ}), e^{iθ}⟫` and `g(r, θ) = ⟪F(c + r e^{iθ}), i e^{iθ}⟫`. Since the
divergence is the trace of the differential in the orthonormal basis `(e^{iθ}, i e^{iθ})`,
`∂_r f + ∂_θ g = r div F(c + r e^{iθ})` (`fderiv_polarRadial_add_fderiv_polarAngular`), the
Jacobian of the polar coordinates. On the boundary of the rectangle, `f` vanishes on `r = 0`, the
two sides `θ = ±π` cancel by periodicity, and `r = ρ` gives the flux.
-/

@[expose] public section

open MeasureTheory Metric Set Complex

namespace TwoComponentCoulomb

/-- The divergence `∂₁F₁ + ∂₂F₂` of a vector field `F : ℂ → ℂ` (`ℂ ≅ ℝ²`). -/
noncomputable def divergence (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ F z 1).re + (fderiv ℝ F z Complex.I).im

/-! ### Linear algebra -/

/-- An `ℝ`-linear map on `ℂ` is determined by its values at `1` and `i`. -/
theorem clm_apply_eq_re_smul_add_im_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (L : ℂ →L[ℝ] E) (z : ℂ) : L z = z.re • L 1 + z.im • L I := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    rw [real_smul, real_smul, mul_one, re_add_im]
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul]

/-- The trace of an `ℝ`-linear map of `ℂ` computed in the orthonormal basis `(e^{iθ}, i e^{iθ})`
is its trace `(L 1).re + (L i).im` in the basis `(1, i)`. -/
theorem inner_apply_circleMap_add_inner_apply_I_mul_circleMap (L : ℂ →L[ℝ] ℂ) (θ : ℝ) :
    inner ℝ (L (circleMap 0 1 θ)) (circleMap 0 1 θ) +
        inner ℝ (L (I * circleMap 0 1 θ)) (I * circleMap 0 1 θ) =
      (L 1).re + (L I).im := by
  rw [clm_apply_eq_re_smul_add_im_smul L (circleMap 0 1 θ),
    clm_apply_eq_re_smul_add_im_smul L (I * circleMap 0 1 θ)]
  simp only [Complex.inner, mul_re, mul_im, conj_re, conj_im, add_re, add_im, smul_re, smul_im,
    smul_eq_mul, I_re, I_im, circleMap_zero_re, circleMap_zero_im, one_mul]
  linear_combination ((L 1).re + (L I).im) * Real.cos_sq_add_sin_sq θ

/-! ### Partial derivatives on `ℝ × ℝ` -/

/-- The partial derivative in the first variable of a function on `ℝ × ℝ`. -/
theorem hasDerivAt_comp_prodMk_left_of_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ × ℝ → E} {L : ℝ × ℝ →L[ℝ] E} {r θ : ℝ} (hf : HasFDerivAt f L (r, θ)) :
    HasDerivAt (fun s => f (s, θ)) (L (1, 0)) r :=
  hf.comp_hasDerivAt (f := fun s : ℝ => (s, θ)) r ((hasDerivAt_id r).prodMk (hasDerivAt_const r θ))

/-- The partial derivative in the second variable of a function on `ℝ × ℝ`. -/
theorem hasDerivAt_comp_prodMk_right_of_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ × ℝ → E} {L : ℝ × ℝ →L[ℝ] E} {r θ : ℝ} (hf : HasFDerivAt f L (r, θ)) :
    HasDerivAt (fun t => f (r, t)) (L (0, 1)) θ :=
  hf.comp_hasDerivAt (f := fun t : ℝ => (r, t)) θ ((hasDerivAt_const θ r).prodMk (hasDerivAt_id θ))

/-! ### Polar coordinates -/

/-- The derivative of `r ↦ c + r e^{iθ}`. -/
theorem hasDerivAt_circleMap_radius (c : ℂ) (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => circleMap c s θ) (circleMap 0 1 θ) r := by
  have := ((hasDerivAt_id r).ofReal_comp.mul_const (Complex.exp (θ * I))).const_add c
  simpa only [circleMap, ofReal_one, one_mul, zero_add, hasDerivAt_const_add_iff, id_eq]
    using this

/-- The polar coordinates `(r, θ) ↦ c + r e^{iθ}` are differentiable. -/
theorem differentiable_circleMap_uncurry (c : ℂ) :
    Differentiable ℝ fun p : ℝ × ℝ => circleMap c p.1 p.2 := by
  have h : (fun p : ℝ × ℝ => circleMap c p.1 p.2) =
      fun p => c + (p.1 : ℂ) * circleMap 0 1 p.2 := by
    funext p
    simp only [circleMap, ofReal_one, one_mul, zero_add]
  rw [h]
  exact (differentiable_const c).add ((ofRealCLM.differentiable.comp differentiable_fst).mul
    ((differentiable_circleMap 0 1).comp differentiable_snd))

/-- The derivative in `r` of `f(r, θ) = r ⟪F(c + r e^{iθ}), e^{iθ}⟫`, the radial flux density in
polar coordinates. -/
theorem hasDerivAt_polarRadial {F : ℂ → ℂ} {c : ℂ} {r θ : ℝ}
    (hF : DifferentiableAt ℝ F (circleMap c r θ)) :
    HasDerivAt (fun s : ℝ => s * inner ℝ (F (circleMap c s θ)) (circleMap 0 1 θ))
      (inner ℝ (F (circleMap c r θ)) (circleMap 0 1 θ) +
        r * inner ℝ (fderiv ℝ F (circleMap c r θ) (circleMap 0 1 θ)) (circleMap 0 1 θ)) r := by
  have h1 := (hF.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_circleMap_radius c r θ)).inner ℝ
    (hasDerivAt_const r (circleMap 0 1 θ))
  convert (hasDerivAt_id' r).mul h1 using 1
  · rfl
  · rw [inner_zero_right, zero_add, one_mul, Function.comp_apply]

/-- The derivative in `θ` of `g(r, θ) = ⟪F(c + r e^{iθ}), i e^{iθ}⟫`, the angular flux density in
polar coordinates. -/
theorem hasDerivAt_polarAngular {F : ℂ → ℂ} {c : ℂ} {r θ : ℝ}
    (hF : DifferentiableAt ℝ F (circleMap c r θ)) :
    HasDerivAt (fun t : ℝ => inner ℝ (F (circleMap c r t)) (I * circleMap 0 1 t))
      (-inner ℝ (F (circleMap c r θ)) (circleMap 0 1 θ) +
        r * inner ℝ (fderiv ℝ F (circleMap c r θ) (I * circleMap 0 1 θ))
          (I * circleMap 0 1 θ)) θ := by
  have h1 := (hF.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap c r θ)).inner ℝ
    ((hasDerivAt_circleMap 0 1 θ).const_mul I)
  have h2 : circleMap 0 r θ * I = r • (I * circleMap 0 1 θ) := by
    simp only [circleMap_zero, Complex.real_smul, ofReal_one, one_mul]
    ring
  have h3 : I * (circleMap 0 1 θ * I) = -circleMap 0 1 θ := by
    rw [mul_comm, mul_assoc, I_mul_I, mul_neg_one]
  convert h1 using 1
  · rfl
  · rw [h2, h3, map_smul, real_inner_smul_left, inner_neg_right, Function.comp_apply]

/-- The radial flux density `f(r, θ) = r ⟪F(c + r e^{iθ}), e^{iθ}⟫` is differentiable where `F`
is. -/
theorem differentiableAt_polarRadial {F : ℂ → ℂ} {c : ℂ} {p : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F (circleMap c p.1 p.2)) :
    DifferentiableAt ℝ
      (fun q : ℝ × ℝ => q.1 * inner ℝ (F (circleMap c q.1 q.2)) (circleMap 0 1 q.2)) p :=
  differentiableAt_fst.mul ((hF.comp p (differentiable_circleMap_uncurry c p)).inner ℝ
    ((differentiable_circleMap 0 1).comp differentiable_snd p))

/-- The angular flux density `g(r, θ) = ⟪F(c + r e^{iθ}), i e^{iθ}⟫` is differentiable where `F`
is. -/
theorem differentiableAt_polarAngular {F : ℂ → ℂ} {c : ℂ} {p : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F (circleMap c p.1 p.2)) :
    DifferentiableAt ℝ
      (fun q : ℝ × ℝ => inner ℝ (F (circleMap c q.1 q.2)) (I * circleMap 0 1 q.2)) p :=
  (hF.comp p (differentiable_circleMap_uncurry c p)).inner ℝ
    ((differentiable_const I).mul ((differentiable_circleMap 0 1).comp differentiable_snd) p)

/-- **The divergence in polar coordinates.** With `f(r, θ) = r ⟪F(c + r e^{iθ}), e^{iθ}⟫` and
`g(r, θ) = ⟪F(c + r e^{iθ}), i e^{iθ}⟫`, `∂_r f + ∂_θ g = r div F(c + r e^{iθ})`. -/
theorem fderiv_polarRadial_add_fderiv_polarAngular {F : ℂ → ℂ} {c : ℂ} {r θ : ℝ}
    (hF : DifferentiableAt ℝ F (circleMap c r θ)) :
    fderiv ℝ (fun q : ℝ × ℝ => q.1 * inner ℝ (F (circleMap c q.1 q.2)) (circleMap 0 1 q.2))
        (r, θ) (1, 0) +
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ (F (circleMap c q.1 q.2)) (I * circleMap 0 1 q.2))
        (r, θ) (0, 1) =
      r * divergence F (circleMap c r θ) := by
  have e1 := (hasDerivAt_comp_prodMk_left_of_hasFDerivAt
    (differentiableAt_polarRadial (p := (r, θ)) hF).hasFDerivAt).unique
    (hasDerivAt_polarRadial hF)
  have e2 := (hasDerivAt_comp_prodMk_right_of_hasFDerivAt
    (differentiableAt_polarAngular (p := (r, θ)) hF).hasFDerivAt).unique
    (hasDerivAt_polarAngular hF)
  rw [e1, e2, divergence, ← inner_apply_circleMap_add_inner_apply_I_mul_circleMap]
  ring

/-! ### The divergence theorem on a disc -/

/-- The divergence of an arbitrary field is measurable. -/
theorem measurable_divergence (F : ℂ → ℂ) : Measurable (divergence F) :=
  (Complex.measurable_re.comp (measurable_fderiv_apply_const ℝ F 1)).add
    (Complex.measurable_im.comp (measurable_fderiv_apply_const ℝ F I))

/-- The divergence of a field of class `C¹` on an open set is continuous there. -/
theorem continuousOn_divergence {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) :
    ContinuousOn (divergence F) U := by
  have h := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  exact (continuous_re.comp_continuousOn (h.clm_apply continuousOn_const)).add
    (continuous_im.comp_continuousOn (h.clm_apply continuousOn_const))

/-- Integration of the divergence over a disc in polar coordinates. -/
theorem integral_ball_divergence_eq_polar {F : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) {U : Set ℂ}
    (hU : IsOpen U) (hcU : closedBall c ρ ⊆ U) (hF : ContDiffOn ℝ 1 F U) :
    ∫ z in ball c ρ, divergence F z =
      ∫ r in (0 : ℝ)..ρ, r * ∫ θ in (-Real.pi)..Real.pi, divergence F (circleMap c r θ) := by
  have hint : IntegrableOn (fun w => divergence F (c + w)) (ball (0 : ℂ) ρ) := by
    refine (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) ρ) ?_).mono_set
      ball_subset_closedBall
    refine (continuousOn_divergence hU hF).comp (continuousOn_const.add continuousOn_id)
      fun w hw => hcU ?_
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    simpa only [add_sub_cancel_left, sub_zero] using hw
  rw [setIntegral_ball_eq_setIntegral_ball_zero,
    setIntegral_ball_zero_eq_polar (F := fun w => divergence F (c + w))
      ((measurable_divergence F).comp (measurable_const_add c)) hint,
    intervalIntegral.integral_of_le hρ, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun r _ => ?_
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  simp only [circleMap, zero_add]

/-- **Divergence theorem on a disc**: for `F` of class `C¹` on an open set containing
`B̄(c, ρ)`, `∫_{B(c,ρ)} div F = ρ ∫_{-π}^{π} ⟪F(c + ρe^{iθ}), e^{iθ}⟫ dθ`. -/
theorem integral_ball_divergence {F : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {U : Set ℂ}
    (hU : IsOpen U) (hcU : Metric.closedBall c ρ ⊆ U) (hF : ContDiffOn ℝ 1 F U) :
    ∫ z in Metric.ball c ρ, divergence F z =
      ρ * ∫ θ in (-Real.pi)..Real.pi, inner ℝ (F (circleMap c ρ θ)) (circleMap 0 1 θ) := by
  set f : ℝ × ℝ → ℝ := fun q => q.1 * inner ℝ (F (circleMap c q.1 q.2)) (circleMap 0 1 q.2)
    with hf
  set g : ℝ × ℝ → ℝ := fun q => inner ℝ (F (circleMap c q.1 q.2)) (I * circleMap 0 1 q.2)
    with hg
  have hmem : ∀ q ∈ uIcc 0 ρ ×ˢ uIcc (-Real.pi) Real.pi, circleMap c q.1 q.2 ∈ U := by
    intro q hq
    have hq1 := hq.1
    rw [uIcc_of_le hρ.le] at hq1
    exact hcU (closedBall_subset_closedBall hq1.2 (circleMap_mem_closedBall c hq1.1 q.2))
  have hdiff : ∀ q ∈ uIcc 0 ρ ×ˢ uIcc (-Real.pi) Real.pi,
      DifferentiableAt ℝ F (circleMap c q.1 q.2) := fun q hq =>
    (hF.differentiableOn one_ne_zero _ (hmem q hq)).differentiableAt (hU.mem_nhds (hmem q hq))
  have hkey : ∀ q ∈ uIcc 0 ρ ×ˢ uIcc (-Real.pi) Real.pi,
      fderiv ℝ f q (1, 0) + fderiv ℝ g q (0, 1) = q.1 * divergence F (circleMap c q.1 q.2) :=
    fun q hq => fderiv_polarRadial_add_fderiv_polarAngular (r := q.1) (θ := q.2) (hdiff q hq)
  have hsub : Ioo (min 0 ρ) (max 0 ρ) ×ˢ Ioo (min (-Real.pi) Real.pi) (max (-Real.pi) Real.pi) ⊆
      uIcc 0 ρ ×ˢ uIcc (-Real.pi) Real.pi :=
    prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hrect := integral2_divergence_prod_of_hasFDerivAt f g (fderiv ℝ f) (fderiv ℝ g)
    0 (-Real.pi) ρ Real.pi
    (fun q hq => (differentiableAt_polarRadial (hdiff q hq)).continuousAt.continuousWithinAt)
    (fun q hq => (differentiableAt_polarAngular (hdiff q hq)).continuousAt.continuousWithinAt)
    (fun q hq => (differentiableAt_polarRadial (hdiff q (hsub hq))).hasFDerivAt)
    (fun q hq => (differentiableAt_polarAngular (hdiff q (hsub hq))).hasFDerivAt)
    (by
      refine IntegrableOn.congr_fun ?_ (fun q hq => (hkey q hq).symm)
        (measurableSet_uIcc.prod measurableSet_uIcc)
      refine ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) ?_
      refine continuousOn_fst.mul ((continuousOn_divergence hU hF).comp ?_ hmem)
      exact (differentiable_circleMap_uncurry c).continuous.continuousOn)
  have hL : (∫ x in (0 : ℝ)..ρ, ∫ y in (-Real.pi)..Real.pi,
      fderiv ℝ f (x, y) (1, 0) + fderiv ℝ g (x, y) (0, 1)) =
      ∫ r in (0 : ℝ)..ρ, r * ∫ θ in (-Real.pi)..Real.pi, divergence F (circleMap c r θ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun y hy => hkey (x, y) ⟨hx, hy⟩
  have hper : ∀ x : ℝ, g (x, Real.pi) = g (x, -Real.pi) := by
    intro x
    have h2pi : -Real.pi + 2 * Real.pi = Real.pi := by ring
    have h1 := periodic_circleMap c x (-Real.pi)
    have h2 := periodic_circleMap 0 1 (-Real.pi)
    rw [h2pi] at h1 h2
    simp only [hg, h1, h2]
  rw [integral_ball_divergence_eq_polar hρ.le hU hcU hF, ← hL, hrect]
  simp only [hper, sub_self, zero_add, hf, zero_mul, intervalIntegral.integral_zero, sub_zero,
    intervalIntegral.integral_const_mul]

/-! ### Calculus of the divergence -/

/-- Product rule: `div (φ G) = ∇φ · G + φ div G`. -/
theorem divergence_smul {φ : ℂ → ℝ} {G : ℂ → ℂ} {z : ℂ} (hφ : DifferentiableAt ℝ φ z)
    (hG : DifferentiableAt ℝ G z) :
    divergence (fun w => φ w • G w) z = fderiv ℝ φ z (G z) + φ z * divergence G z := by
  rw [divergence, divergence, fderiv_fun_smul hφ hG,
    clm_apply_eq_re_smul_add_im_smul (fderiv ℝ φ z) (G z)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, add_re, add_im, smul_re,
    smul_im, smul_eq_mul]
  ring

/-- The conjugate of a holomorphic function is divergence free (Cauchy–Riemann). -/
theorem divergence_conj {h : ℂ → ℂ} {z : ℂ} (hh : DifferentiableAt ℂ h z) :
    divergence (fun w => (starRingEnd ℂ) (h w)) z = 0 := by
  have h1 : HasFDerivAt (fun w => (starRingEnd ℂ) (h w))
      (conjCLE.toContinuousLinearMap.comp ((fderiv ℂ h z).restrictScalars ℝ)) z :=
    conjCLE.hasFDerivAt.comp z (hh.hasFDerivAt.restrictScalars ℝ)
  have hI : fderiv ℂ h z I = I * fderiv ℂ h z 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [divergence, h1.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearEquiv.coe_coe, ContinuousAlgEquiv.coeCLE_apply, conjCAE_apply, hI, conj_re,
    map_mul, conj_I, mul_im, neg_re, neg_im, I_re, I_im]
  ring

/-- **Green's identity on a disc** for a divergence-free field: if `φ` and `G` are `C¹` on an open
set containing `B̄(c, ρ)` and `div G = 0` on `B(c, ρ)`, then
`∫_{B(c,ρ)} ∇φ · G = ρ ∫_{-π}^{π} φ(c + ρe^{iθ}) ⟪G(c + ρe^{iθ}), e^{iθ}⟫ dθ`. -/
theorem integral_ball_fderiv_apply_of_divergence_eq_zero {φ : ℂ → ℝ} {G : ℂ → ℂ} {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) {U : Set ℂ} (hU : IsOpen U) (hcU : Metric.closedBall c ρ ⊆ U)
    (hφ : ContDiffOn ℝ 1 φ U) (hG : ContDiffOn ℝ 1 G U)
    (hdiv : ∀ z ∈ Metric.ball c ρ, divergence G z = 0) :
    ∫ z in Metric.ball c ρ, fderiv ℝ φ z (G z) =
      ρ * ∫ θ in (-Real.pi)..Real.pi,
        φ (circleMap c ρ θ) * inner ℝ (G (circleMap c ρ θ)) (circleMap 0 1 θ) := by
  have h1 : ∫ z in ball c ρ, fderiv ℝ φ z (G z) =
      ∫ z in ball c ρ, divergence (fun w => φ w • G w) z := by
    refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
    have hzU : z ∈ U := hcU (ball_subset_closedBall hz)
    rw [divergence_smul ((hφ.differentiableOn one_ne_zero z hzU).differentiableAt
      (hU.mem_nhds hzU)) ((hG.differentiableOn one_ne_zero z hzU).differentiableAt
      (hU.mem_nhds hzU)), hdiv z hz, mul_zero, add_zero]
  rw [h1, integral_ball_divergence (F := fun w => φ w • G w) hρ hU hcU (hφ.smul hG)]
  simp only [real_inner_smul_left]

end TwoComponentCoulomb
