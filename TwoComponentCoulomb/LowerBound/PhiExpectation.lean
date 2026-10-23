/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.LowerBound.RadiusTail
public import TwoComponentCoulomb.UpperBound.IsolatedRadial

/-!
# The expectation of `φ_β(ϱ(x_i))` on the placement set

Source: Proposition 4.1, Step 3 (l. 1775–1803), as
required by ruling R22.

Let `H = H(N, N, 4λ, 8λ)` (`placementSet N N (4 * lam) (8 * lam)`), let `ℚ` be the normalised
Lebesgue measure on `H`, and let `ϱ(x_i) = lowerRadius hN X i`, so that `ϱ(x_i) ∈ [4λ, 1]` on `H`.
The source integrates the tail bound `ℚ(ϱ(x_1) ≤ r) ≤ C (r² + r / √N)` (l. 1776–1778; Lean:
`radius_tail_le`) against the decreasing profile `φ_β` of (defvarphi) (Lean: `isolatedPhi`):
writing `φ_β(ϱ) = φ_β(1) + ∫_ϱ^1 (-φ_β'(s)) ds` and exchanging the integrals (Tonelli),
`E_ℚ[φ_β(ϱ(x_1))] ≤ φ_β(1) + C ∫_{4λ}^1 (-φ_β'(r)) (r² + r / √N) dr ≤ C_β (ε_λ + η_λ / √N)`
(l. 1787–1792), the last step by elementary integration.

* `integral_comp_lowerRadius_le_of_eq_add_integral`, `integral_comp_lowerRadius_le` : the
  integration step for a general `f` with continuous derivative `f' ≤ 0` on `[4λ, 1]`:
  `∫_H f(ϱ(x_i)) ≤ vol H · (f(1) + ∫_{4λ}^1 (-f'(s)) (32π s² + 16 s / √N) ds)`, with the
  constants of `radius_tail_le`.
* `integrableOn_comp_lowerRadius`, `integrableOn_isolatedPhi_lowerRadius` : integrability.
* `hasDerivAt_div_rpow`, `hasDerivAt_div_sq_mul_one_add_log`, `isolatedPhi_eq_of_lt_four`,
  `isolatedPhi_eq_of_eq_four`, `isolatedPhi_eq_of_four_lt` : the profile `φ_β` for `β > 2` and
  its derivative.
* `integral_div_lowerRadius_rpow_le`, `eta_rpow_part_le`,
  `exists_integral_isolatedPhi_le_of_lt_four`, `exists_integral_isolatedPhi_le_of_four_lt` : the
  elementary integration for the power profiles (`2 < β < 4` and `β > 4`).
* `hasDerivAt_phiFour_primitive`, `exists_integral_isolatedPhi_le_four` : the elementary
  integration for `β = 4`.
* `expectation_isolatedPhi_lowerRadius_le` : `∫_H φ_β(ϱ(x_i)) ≤ C_β (ε_λ + η_λ / √N) vol H` for
  `0 < λ < 1/64`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### The general integration step -/

/-- `ϱ(x_i) ≤ 1`. -/
theorem lowerRadius_le_one (hN : 2 ≤ N) (X : Fin N → ℂ) (i : Fin N) :
    lowerRadius hN X i ≤ 1 :=
  ((le_lowerRadius_iff hN X i).1 le_rfl).2.2

/-- On `H(N, N, 4λ, 8λ)` with `4λ ≤ 1`, `ϱ(x_i) ∈ [4λ, 1]`. -/
theorem lowerRadius_mem_Icc (hN : 2 ≤ N) {lam : ℝ} (h4 : 4 * lam ≤ 1) {X : Fin N → ℂ}
    (hX : X ∈ placementSet N N (4 * lam) (8 * lam)) (i : Fin N) :
    lowerRadius hN X i ∈ Icc (4 * lam) 1 :=
  ⟨four_mul_le_lowerRadius hN h4 hX i, lowerRadius_le_one hN X i⟩

/-- Lebesgue measure restricted to `H(N, n, a, b)` is finite. -/
theorem isFiniteMeasure_restrict_placementSet (N n : ℕ) (a b : ℝ) :
    IsFiniteMeasure (volume.restrict (placementSet N n a b)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact volume_placementSet_lt_top _ _ _ _⟩

/-- A function continuous on `[4λ, 1]`, composed with `ϱ(x_i)`, is integrable on
`H = H(N, N, 4λ, 8λ)`. -/
theorem integrableOn_comp_lowerRadius (hN : 2 ≤ N) {lam : ℝ} (h4 : 4 * lam ≤ 1) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (4 * lam) 1)) (i : Fin N) :
    IntegrableOn (fun X => f (lowerRadius hN X i)) (placementSet N N (4 * lam) (8 * lam)) := by
  have := isFiniteMeasure_restrict_placementSet N N (4 * lam) (8 * lam)
  have hHm := measurableSet_placementSet N N (4 * lam) (8 * lam)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hcont : ContinuousOn (fun X => f (lowerRadius hN X i))
      (placementSet N N (4 * lam) (8 * lam)) :=
    hf.comp (continuous_lowerRadius hN i).continuousOn
      (fun X hX => lowerRadius_mem_Icc hN h4 hX i)
  exact Integrable.of_bound (hcont.aestronglyMeasurable hHm) C
    ((ae_restrict_iff' hHm).2 (Filter.Eventually.of_forall fun X hX =>
      hC _ (lowerRadius_mem_Icc hN h4 hX i)))

/-- **The integration step of Step 3** (source l. 1787–1792), in integrated form: if
`f(x) = f(1) + ∫_x^1 g` on `[4λ, 1]` with `g ≥ 0` continuous, then by Tonelli and the tail bound
`radius_tail_le`,
`∫_H f(ϱ(x_i)) ≤ vol H · (f(1) + ∫_{4λ}^1 g(s) (32π s² + 16 s / √N) ds)`. -/
theorem integral_comp_lowerRadius_le_of_eq_add_integral (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (h64 : 64 * lam ≤ 1) {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc (4 * lam) 1))
    (hg : ContinuousOn g (Icc (4 * lam) 1)) (hg0 : ∀ s ∈ Icc (4 * lam) 1, 0 ≤ g s)
    (hfg : ∀ x ∈ Icc (4 * lam) 1, f x = f 1 + ∫ s in x..1, g s) (i : Fin N) :
    ∫ X in placementSet N N (4 * lam) (8 * lam), f (lowerRadius hN X i) ≤
      (volume (placementSet N N (4 * lam) (8 * lam))).toReal *
        (f 1 + ∫ s in (4 * lam)..1, g s * (32 * Real.pi * s ^ 2 + 16 * s / Real.sqrt N)) := by
  set H := placementSet N N (4 * lam) (8 * lam) with hH
  have := isFiniteMeasure_restrict_placementSet N N (4 * lam) (8 * lam)
  have hHm : MeasurableSet H := measurableSet_placementSet _ _ _ _
  have hfin : volume H ≠ ∞ := (volume_placementSet_lt_top _ _ _ _).ne
  have h4 : 4 * lam ≤ 1 := by linarith
  set a := 4 * lam with ha
  have ha0 : 0 < a := by positivity
  set c : ℝ → ℝ := fun s => 32 * Real.pi * s ^ 2 + 16 * s / Real.sqrt N with hc
  have hc0 : ∀ s, 0 ≤ s → 0 ≤ c s := fun s hs => by positivity
  set ϱ : (Fin N → ℂ) → ℝ := fun X => lowerRadius hN X i with hϱ
  have hϱm : Measurable ϱ := measurable_lowerRadius hN i
  have hϱH : ∀ X ∈ H, ϱ X ∈ Icc a 1 := fun X hX => lowerRadius_mem_Icc hN h4 hX i
  have hgi : ∀ x ∈ Icc a 1, IntegrableOn g (Ioc x 1) := fun x hx =>
    (hg.mono (Icc_subset_Icc_left hx.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  set ν : Measure ℝ := volume.restrict (Ioc a 1) with hν
  set μ : Measure (Fin N → ℂ) := volume.restrict H with hμ
  -- the integrand of Tonelli
  set G : (Fin N → ℂ) → ℝ → ℝ≥0∞ := fun X s =>
    ({p : (Fin N → ℂ) × ℝ | ϱ p.1 < p.2}).indicator (fun p => ENNReal.ofReal (g p.2)) (X, s)
    with hG
  have hGm : AEMeasurable (Function.uncurry G) (μ.prod ν) := by
    have h1 : AEMeasurable g ν := (hg.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
    have h2 : AEMeasurable (fun p : (Fin N → ℂ) × ℝ => ENNReal.ofReal (g p.2)) (μ.prod ν) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable h1).comp_snd
    exact h2.indicator (measurableSet_lt (hϱm.comp measurable_fst) measurable_snd)
  -- the section in `s`
  have hsec : ∀ X ∈ H, ENNReal.ofReal (f (ϱ X) - f 1) = ∫⁻ s, G X s ∂ν := by
    intro X hX
    have hx := hϱH X hX
    have e1 : f (ϱ X) - f 1 = ∫ s in Ioc (ϱ X) 1, g s := by
      rw [hfg _ hx, ← intervalIntegral.integral_of_le hx.2]
      ring
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc (ϱ X) 1)] g :=
      (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs =>
        hg0 s ⟨by linarith [hx.1, hs.1], hs.2⟩)
    rw [e1, ofReal_integral_eq_lintegral_ofReal (hgi _ hx) hnn]
    have e2 : ∀ s, G X s = (Ioi (ϱ X)).indicator (fun s => ENNReal.ofReal (g s)) s := by
      intro s
      simp only [hG, indicator_apply, mem_ofPred_eq, mem_Ioi]
    simp_rw [e2]
    rw [hν, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    congr 2
    ext s
    simp only [mem_Ioc, mem_inter_iff, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, lt_of_le_of_lt hx.1 h1, h2⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
  -- the section in `X`
  have hsecX : ∀ s ∈ Ioc a 1, ∫⁻ X, G X s ∂μ ≤
      ENNReal.ofReal (g s * c s) * volume H := by
    intro s hs
    have hs0 : 0 < s := lt_trans ha0 hs.1
    have e1 : ∀ X, G X s = ({X | ϱ X < s}).indicator (fun _ => ENNReal.ofReal (g s)) X := by
      intro X
      simp only [hG, indicator_apply, mem_ofPred_eq]
    simp_rw [e1]
    rw [lintegral_indicator_const (measurableSet_lt hϱm measurable_const), hμ,
      Measure.restrict_apply (measurableSet_lt hϱm measurable_const),
      ENNReal.ofReal_mul' (hc0 s hs0.le), mul_assoc]
    refine mul_le_mul_right ?_ _
    refine le_trans (measure_mono ?_) (radius_tail_le hN hlam h64 hs0 i)
    rintro X ⟨h1, h2⟩
    exact ⟨h2, le_of_lt h1⟩
  -- Tonelli
  have hlin : ∫⁻ X, ENNReal.ofReal (f (ϱ X) - f 1) ∂μ ≤
      ENNReal.ofReal (∫ s in a..1, g s * c s) * volume H := by
    have hgc : ContinuousOn (fun s => g s * c s) (Icc a 1) :=
      hg.mul (by fun_prop)
    have hgcnn : 0 ≤ᵐ[ν] fun s => g s * c s :=
      (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs =>
        mul_nonneg (hg0 s ⟨hs.1.le, hs.2⟩) (hc0 s (ha0.trans hs.1).le))
    calc ∫⁻ X, ENNReal.ofReal (f (ϱ X) - f 1) ∂μ = ∫⁻ X, ∫⁻ s, G X s ∂ν ∂μ :=
          setLIntegral_congr_fun hHm (fun X hX => hsec X hX)
      _ = ∫⁻ s, ∫⁻ X, G X s ∂μ ∂ν := lintegral_lintegral_swap hGm
      _ ≤ ∫⁻ s, ENNReal.ofReal (g s * c s) * volume H ∂ν :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2
            (Filter.Eventually.of_forall hsecX))
      _ = ENNReal.ofReal (∫ s in a..1, g s * c s) * volume H := by
          rw [lintegral_mul_const' _ _ hfin, intervalIntegral.integral_of_le h4,
            ofReal_integral_eq_lintegral_ofReal
              (hgc.integrableOn_Icc.mono_set Ioc_subset_Icc_self) hgcnn]
  -- back to Bochner integrals
  have hint : IntegrableOn (fun X => f (ϱ X)) H := integrableOn_comp_lowerRadius hN h4 hf i
  have hnn : 0 ≤ᵐ[μ] fun X => f (ϱ X) - f 1 :=
    (ae_restrict_iff' hHm).2 (Filter.Eventually.of_forall fun X hX => by
      have hx := hϱH X hX
      show 0 ≤ f (ϱ X) - f 1
      rw [hfg _ hx, add_sub_cancel_left]
      exact intervalIntegral.integral_nonneg hx.2 fun s hs =>
        hg0 s ⟨hx.1.trans hs.1, hs.2⟩)
  have hI0 : 0 ≤ ∫ s in a..1, g s * c s :=
    intervalIntegral.integral_nonneg h4 fun s hs =>
      mul_nonneg (hg0 s hs) (hc0 s (ha0.le.trans hs.1))
  have hkey : ∫ X in H, (f (ϱ X) - f 1) ≤ (volume H).toReal * ∫ s in a..1, g s * c s := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn (hint.sub (integrable_const _)).1]
    refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg ENNReal.toReal_nonneg hI0)
      (hlin.trans (le_of_eq ?_))
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin, mul_comm]
  have hsplit : ∫ X in H, f (ϱ X) =
      (∫ X in H, (f (ϱ X) - f 1)) + (volume H).toReal * f 1 := by
    rw [integral_sub hint (integrable_const (f 1)), setIntegral_const, measureReal_def, smul_eq_mul]
    ring
  rw [hsplit]
  linarith only [hkey]

/-- **The integration step of Step 3** (source l. 1787–1792): if `f` is differentiable on
`[4λ, 1]` with continuous derivative `f' ≤ 0`, then writing
`f(ϱ) = f(1) + ∫_ϱ^1 (-f'(s)) ds`, Tonelli and the tail bound `radius_tail_le` give
`∫_H f(ϱ(x_i)) ≤ vol H · (f(1) + ∫_{4λ}^1 (-f'(s)) (32π s² + 16 s / √N) ds)`. -/
theorem integral_comp_lowerRadius_le (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (h64 : 64 * lam ≤ 1) {f f' : ℝ → ℝ} (hf : ∀ s ∈ Icc (4 * lam) 1, HasDerivAt f (f' s) s)
    (hf' : ContinuousOn f' (Icc (4 * lam) 1)) (hf'0 : ∀ s ∈ Icc (4 * lam) 1, f' s ≤ 0)
    (i : Fin N) :
    ∫ X in placementSet N N (4 * lam) (8 * lam), f (lowerRadius hN X i) ≤
      (volume (placementSet N N (4 * lam) (8 * lam))).toReal *
        (f 1 + ∫ s in (4 * lam)..1, -f' s * (32 * Real.pi * s ^ 2 + 16 * s / Real.sqrt N)) := by
  refine integral_comp_lowerRadius_le_of_eq_add_integral (g := fun s => -f' s) hN hlam h64
    (fun s hs => (hf s hs).continuousAt.continuousWithinAt) hf'.neg
    (fun s hs => neg_nonneg.2 (hf'0 s hs)) (fun x hx => ?_) i
  have hsub : uIcc x 1 ⊆ Icc (4 * lam) 1 := by
    rw [uIcc_of_le hx.2]
    exact Icc_subset_Icc_left hx.1
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hf s (hsub hs)) ((hf'.mono hsub).intervalIntegrable)]
  ring

/-! ### The profile `φ_β` and its derivative -/

/-- The derivative of `x ↦ (λ/x)^p` at `s > 0` is `-p (λ/s)^p / s`. -/
theorem hasDerivAt_div_rpow {lam p s : ℝ} (hlam : 0 < lam) (hs : 0 < s) :
    HasDerivAt (fun x => (lam / x) ^ p) (-(p * (lam / s) ^ p / s)) s := by
  have h1 : HasDerivAt (fun x => lam / x) ((0 * s - lam * 1) / s ^ 2) s :=
    (hasDerivAt_const s lam).div (hasDerivAt_id' s) hs.ne'
  have h2 := h1.rpow_const (p := p) (Or.inl (div_pos hlam hs).ne')
  convert h2 using 1
  rw [Real.rpow_sub_one (div_pos hlam hs).ne']
  field_simp
  ring

/-- The derivative of `φ_4(x) = (λ/x)² (1 + log(x/λ))` at `s > 0` is
`-(λ/s)² (1 + 2 log(s/λ)) / s`. -/
theorem hasDerivAt_div_sq_mul_one_add_log {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s) :
    HasDerivAt (fun x => (lam / x) ^ 2 * (1 + Real.log (x / lam)))
      (-((lam / s) ^ 2 * (1 + 2 * Real.log (s / lam)) / s)) s := by
  have h1 : HasDerivAt (fun x => lam / x) ((0 * s - lam * 1) / s ^ 2) s :=
    (hasDerivAt_const s lam).div (hasDerivAt_id' s) hs.ne'
  have h2 : HasDerivAt (fun x => Real.log (x / lam)) ((1 / lam) / (s / lam)) s :=
    ((hasDerivAt_id' s).div_const lam).log (div_pos hs hlam).ne'
  have h3 := (h1.pow 2).mul (h2.const_add 1)
  convert h3 using 1
  simp only [Pi.pow_apply]
  have hs0 := hs.ne'
  have hl0 := hlam.ne'
  norm_num
  field_simp
  ring

/-- `φ_β(x) = (λ/x)^{β-2}` for `2 < β < 4` (defvarphi). -/
theorem isolatedPhi_eq_of_lt_four {β : ℝ} (hβ : 2 < β) (h4 : β < 4) (lam : ℝ) :
    isolatedPhi β hβ.le lam = fun x => (lam / x) ^ (β - 2) := by
  funext x
  simp only [isolatedPhi, hβ.ne', h4, ↓reduceIte]

/-- `φ_4(x) = (λ/x)² (1 + log(x/λ))` (defvarphi). -/
theorem isolatedPhi_eq_of_eq_four {β : ℝ} (hβ : 2 < β) (h4 : β = 4) (lam : ℝ) :
    isolatedPhi β hβ.le lam = fun x => (lam / x) ^ 2 * (1 + Real.log (x / lam)) := by
  funext x
  unfold isolatedPhi
  split_ifs with h2 h4'
  · exact absurd h2 hβ.ne'
  · exact absurd h4 h4'.ne
  · rfl

/-- `φ_β(x) = (λ/x)²` for `β > 4` (defvarphi). -/
theorem isolatedPhi_eq_of_four_lt {β : ℝ} (hβ : 2 < β) (h4 : 4 < β) (lam : ℝ) :
    isolatedPhi β hβ.le lam = fun x => (lam / x) ^ (2 : ℝ) := by
  funext x
  simp only [isolatedPhi, hβ.ne', not_lt.2 h4.le, h4.ne', ↓reduceIte, Real.rpow_two]

/-- For `β > 2`, `φ_β` is continuous at every `s > 0`. -/
theorem continuousAt_isolatedPhi {β : ℝ} (hβ : 2 < β) {lam s : ℝ} (hlam : 0 < lam)
    (hs : 0 < s) : ContinuousAt (isolatedPhi β hβ.le lam) s := by
  rcases lt_trichotomy β 4 with h4 | h4 | h4
  · rw [isolatedPhi_eq_of_lt_four hβ h4]
    exact (hasDerivAt_div_rpow hlam hs).continuousAt
  · rw [isolatedPhi_eq_of_eq_four hβ h4]
    exact (hasDerivAt_div_sq_mul_one_add_log hlam hs).continuousAt
  · rw [isolatedPhi_eq_of_four_lt hβ h4]
    exact (hasDerivAt_div_rpow hlam hs).continuousAt

/-- `φ_β(ϱ(x_i))` is integrable on `H = H(N, N, 4λ, 8λ)` for `β > 2`. -/
theorem integrableOn_isolatedPhi_lowerRadius {β : ℝ} (hβ : 2 < β) (hN : 2 ≤ N) {lam : ℝ}
    (hlam : 0 < lam) (h4 : 4 * lam ≤ 1) (i : Fin N) :
    IntegrableOn (fun X => isolatedPhi β hβ.le lam (lowerRadius hN X i))
      (placementSet N N (4 * lam) (8 * lam)) :=
  integrableOn_comp_lowerRadius hN h4 (fun s hs =>
    (continuousAt_isolatedPhi hβ hlam (lt_of_lt_of_le (by positivity) hs.1)).continuousWithinAt) i

/-! ### The power profiles -/

/-- **The integration step for `f(r) = (λ/r)^p`**, `p > 0` (the profile `φ_β` for `β < 4`, with
`p = β - 2`, and for `β > 4`, with `p = 2`): here `-f'(s) = p (λ/s)^p / s`, so
`∫_H (λ/ϱ(x_i))^p ≤ vol H · (λ^p + p λ^p (32π A + (16/√N) B))` with
`A = ∫_{4λ}^1 s^{1-p} ds` and `B = ∫_{4λ}^1 s^{-p} ds`. -/
theorem integral_div_lowerRadius_rpow_le (hN : 2 ≤ N) {p lam : ℝ} (hp : 0 < p) (hlam : 0 < lam)
    (h64 : 64 * lam ≤ 1) (i : Fin N) :
    ∫ X in placementSet N N (4 * lam) (8 * lam), (lam / lowerRadius hN X i) ^ p ≤
      (volume (placementSet N N (4 * lam) (8 * lam))).toReal *
        (lam ^ p + p * lam ^ p * (32 * Real.pi * (∫ s in (4 * lam)..1, s ^ (1 - p)) +
          16 / Real.sqrt N * (∫ s in (4 * lam)..1, s ^ (-p)))) := by
  have h4 : 4 * lam ≤ 1 := by linarith
  have hpos : ∀ s ∈ Icc (4 * lam) 1, 0 < s := fun s hs => lt_of_lt_of_le (by positivity) hs.1
  have hcont : ContinuousOn (fun s => -(p * (lam / s) ^ p / s)) (Icc (4 * lam) 1) := by
    intro s hs
    have hs0 := hpos s hs
    exact ((continuousAt_const.mul ((continuousAt_const.div continuousAt_id hs0.ne').rpow_const
      (Or.inr hp.le))).div continuousAt_id hs0.ne').neg.continuousWithinAt
  have hnp : ∀ s ∈ Icc (4 * lam) 1, -(p * (lam / s) ^ p / s) ≤ 0 := by
    intro s hs
    have hs0 := hpos s hs
    have : 0 ≤ p * (lam / s) ^ p / s := by positivity
    linarith
  refine (integral_comp_lowerRadius_le hN hlam h64 (f := fun x => (lam / x) ^ p)
    (fun s hs => hasDerivAt_div_rpow hlam (hpos s hs)) hcont hnp i).trans (le_of_eq ?_)
  congr 1
  have h0 : (0 : ℝ) ∉ uIcc (4 * lam) 1 := by
    rw [uIcc_of_le h4]
    intro h
    linarith [h.1]
  have hrp : ∀ q : ℝ, IntervalIntegrable (fun s : ℝ => s ^ q) volume (4 * lam) 1 := fun q =>
    intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
  have hcongr : ∫ s in (4 * lam)..1, -(-(p * (lam / s) ^ p / s)) *
      (32 * Real.pi * s ^ 2 + 16 * s / Real.sqrt N) =
      ∫ s in (4 * lam)..1,
        p * lam ^ p * (32 * Real.pi * s ^ (1 - p) + 16 / Real.sqrt N * s ^ (-p)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 < s := hpos s (by rwa [uIcc_of_le h4] at hs)
    have hsp : 0 < s ^ p := Real.rpow_pos_of_pos hs0 p
    rw [Real.div_rpow hlam.le hs0.le, Real.rpow_sub hs0, Real.rpow_one, Real.rpow_neg hs0.le]
    field_simp
  show (lam / 1) ^ p + _ = _
  rw [div_one, hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    ((hrp _).const_mul _) ((hrp _).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- Combination of the `ε`- and `η`-parts: if `E ≤ C₁ ε` and `F ≤ C₂ η`, then
`V (E + F / q) ≤ (C₁ + C₂) (ε + η / q) V`. -/
theorem mul_add_div_le_of_le {V E F ε η q C₁ C₂ : ℝ} (hV : 0 ≤ V) (hq : 0 < q) (hε : 0 ≤ ε)
    (hη : 0 ≤ η) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hE : E ≤ C₁ * ε) (hF : F ≤ C₂ * η) :
    V * (E + F / q) ≤ (C₁ + C₂) * (ε + η / q) * V := by
  have h1 : F / q ≤ C₂ * η / q := div_le_div_of_nonneg_right hF hq.le
  have h2 : 0 ≤ C₂ * ε := mul_nonneg hC₂ hε
  have h3 : 0 ≤ C₁ * (η / q) := mul_nonneg hC₁ (div_nonneg hη hq.le)
  have e : (C₁ + C₂) * (ε + η / q) = C₁ * ε + C₂ * η / q + (C₂ * ε + C₁ * (η / q)) := by ring
  rw [mul_comm _ V, e]
  exact mul_le_mul_of_nonneg_left (by linarith only [hE, h1, h2, h3]) hV

/-- The `η`-part for `2 < β < 4`: `(β - 2) λ^{β-2} · 16 ∫_{4λ}^1 s^{-(β-2)} ds ≤ C η_λ`. -/
theorem eta_rpow_part_le {β : ℝ} (hβ : 2 < β) (h4 : β < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → 64 * lam ≤ 1 →
      (β - 2) * lam ^ (β - 2) * (16 * ∫ s in (4 * lam)..1, s ^ (-(β - 2))) ≤
        C * lowerEta β hβ lam := by
  have hγ : 0 < β - 2 := by linarith
  rcases lt_trichotomy β 3 with h3 | h3 | h3
  · have h3' : 0 < 3 - β := by linarith
    refine ⟨(β - 2) * (16 * (1 / (3 - β))), by positivity, fun lam hlam h64 => ?_⟩
    have hB := intervalIntegral_rpow_le_of_neg_one_lt (p := -(β - 2)) (s := 4 * lam) (t := 1)
      (by linarith) (by positivity)
    rw [Real.one_rpow, show -(β - 2) + 1 = 3 - β by ring] at hB
    simp only [lowerEta, h3, ↓reduceIte]
    have hp : 0 ≤ lam ^ (β - 2) := by positivity
    calc _ ≤ (β - 2) * lam ^ (β - 2) * (16 * (1 / (3 - β))) := by gcongr
      _ = _ := by ring
  · subst h3
    refine ⟨16, by norm_num, fun lam hlam h64 => ?_⟩
    have hB : ∫ s in (4 * lam)..1, s ^ (-((3 : ℝ) - 2)) = Real.log (4 * lam)⁻¹ := by
      rw [show -((3 : ℝ) - 2) = -1 by norm_num,
        intervalIntegral_rpow_neg_one (by positivity) one_pos, one_div]
    have hE : lowerEta 3 hβ lam = lam * |Real.log lam| := by simp [lowerEta]
    rw [hB, hE, show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one]
    have hL := log_inv_four_mul_le hlam h64
    have := mul_le_mul_of_nonneg_left hL hlam.le
    linarith only [this]
  · have h3' : 0 < β - 3 := by linarith
    refine ⟨(β - 2) * (16 / (β - 3)), by positivity, fun lam hlam h64 => ?_⟩
    have h4l : 4 * lam ≤ 1 := by linarith
    have hB := intervalIntegral_rpow_le_of_lt_neg_one (p := -(β - 2)) (s := 4 * lam) (t := 1)
      (by linarith) (by positivity) h4l
    rw [show -(β - 2) + 1 = 3 - β by ring, show -(3 - β) = β - 3 by ring] at hB
    simp only [lowerEta, not_lt.2 h3.le, h3.ne', ↓reduceIte]
    have hpow : lam ^ (β - 2) * (4 * lam) ^ (3 - β) ≤ lam := by
      rw [Real.mul_rpow (by norm_num) hlam.le]
      have h4p : (4 : ℝ) ^ (3 - β) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      have e : lam ^ (β - 2) * lam ^ (3 - β) = lam := by
        rw [← Real.rpow_add hlam, show β - 2 + (3 - β) = (1 : ℝ) by ring, Real.rpow_one]
      calc lam ^ (β - 2) * ((4 : ℝ) ^ (3 - β) * lam ^ (3 - β))
          = (4 : ℝ) ^ (3 - β) * (lam ^ (β - 2) * lam ^ (3 - β)) := by ring
        _ ≤ 1 * lam := by rw [e]; gcongr
        _ = lam := one_mul _
    have hp : 0 ≤ lam ^ (β - 2) := by positivity
    calc (β - 2) * lam ^ (β - 2) * (16 * ∫ s in (4 * lam)..1, s ^ (-(β - 2)))
        ≤ (β - 2) * lam ^ (β - 2) * (16 * ((4 * lam) ^ (3 - β) / (β - 3))) := by gcongr
      _ = (β - 2) * (16 / (β - 3)) * (lam ^ (β - 2) * (4 * lam) ^ (3 - β)) := by ring
      _ ≤ (β - 2) * (16 / (β - 3)) * lam := by gcongr

/-- **Step 3 for `2 < β < 4`** (source l. 1787–1792), where `φ_β(r) = (λ/r)^{β-2}`:
`∫_H φ_β(ϱ(x_i)) ≤ C (ε_λ + η_λ / √N) vol H` for `64 λ ≤ 1`. -/
theorem exists_integral_isolatedPhi_le_of_lt_four {β : ℝ} (hβ : 2 < β) (h4 : β < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → 64 * lam ≤ 1 → ∀ i : Fin N,
      ∫ X in placementSet N N (4 * lam) (8 * lam), isolatedPhi β hβ.le lam (lowerRadius hN X i) ≤
        C * (lowerEps β hβ lam + lowerEta β hβ lam / Real.sqrt N) *
          (volume (placementSet N N (4 * lam) (8 * lam))).toReal := by
  have hγ : 0 < β - 2 := by linarith
  have h4' : 0 < 4 - β := by linarith
  obtain ⟨C₂, hC₂, hη⟩ := eta_rpow_part_le hβ h4
  refine ⟨(1 + (β - 2) * (32 * Real.pi * (1 / (4 - β)))) + C₂, by positivity,
    fun N hN lam hlam h64 i => ?_⟩
  rw [isolatedPhi_eq_of_lt_four hβ h4]
  refine (integral_div_lowerRadius_rpow_le hN hγ hlam h64 i).trans ?_
  have hA := intervalIntegral_rpow_le_of_neg_one_lt (p := 1 - (β - 2)) (s := 4 * lam) (t := 1)
    (by linarith) (by positivity)
  rw [Real.one_rpow, show 1 - (β - 2) + 1 = 4 - β by ring] at hA
  have hε : lowerEps β hβ lam = lam ^ (β - 2) := by simp only [lowerEps, h4, ↓reduceIte]
  have hp : 0 ≤ lam ^ (β - 2) := by positivity
  have hE : lam ^ (β - 2) + (β - 2) * lam ^ (β - 2) *
      (32 * Real.pi * ∫ s in (4 * lam)..1, s ^ (1 - (β - 2))) ≤
      (1 + (β - 2) * (32 * Real.pi * (1 / (4 - β)))) * lowerEps β hβ lam := by
    rw [hε]
    calc _ ≤ lam ^ (β - 2) + (β - 2) * lam ^ (β - 2) * (32 * Real.pi * (1 / (4 - β))) := by
          gcongr
      _ = _ := by ring
  have hq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  have e : lam ^ (β - 2) + (β - 2) * lam ^ (β - 2) *
      (32 * Real.pi * (∫ s in (4 * lam)..1, s ^ (1 - (β - 2))) +
        16 / Real.sqrt N * (∫ s in (4 * lam)..1, s ^ (-(β - 2)))) =
      (lam ^ (β - 2) + (β - 2) * lam ^ (β - 2) *
        (32 * Real.pi * ∫ s in (4 * lam)..1, s ^ (1 - (β - 2)))) +
      (β - 2) * lam ^ (β - 2) * (16 * ∫ s in (4 * lam)..1, s ^ (-(β - 2))) / Real.sqrt N := by
    ring
  rw [e]
  exact mul_add_div_le_of_le ENNReal.toReal_nonneg hq (lowerEps_nonneg hβ hlam)
    (lowerEta_nonneg hβ hlam) (by positivity) hC₂.le hE (hη lam hlam h64)

/-- **Step 3 for `β > 4`** (source l. 1787–1792), where `φ_β(r) = (λ/r)²`:
`∫_H φ_β(ϱ(x_i)) ≤ C (ε_λ + η_λ / √N) vol H` for `64 λ ≤ 1`. -/
theorem exists_integral_isolatedPhi_le_of_four_lt {β : ℝ} (hβ : 2 < β) (h4 : 4 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → 64 * lam ≤ 1 → ∀ i : Fin N,
      ∫ X in placementSet N N (4 * lam) (8 * lam), isolatedPhi β hβ.le lam (lowerRadius hN X i) ≤
        C * (lowerEps β hβ lam + lowerEta β hβ lam / Real.sqrt N) *
          (volume (placementSet N N (4 * lam) (8 * lam))).toReal := by
  refine ⟨(1 + 64 * Real.pi) + 8, by positivity, fun N hN lam hlam h64 i => ?_⟩
  rw [isolatedPhi_eq_of_four_lt hβ h4]
  refine (integral_div_lowerRadius_rpow_le hN two_pos hlam h64 i).trans ?_
  have h4l : 4 * lam ≤ 1 := by linarith
  have hA : ∫ s in (4 * lam)..1, s ^ (1 - (2 : ℝ)) = Real.log (4 * lam)⁻¹ := by
    rw [show 1 - (2 : ℝ) = -1 by norm_num,
      intervalIntegral_rpow_neg_one (by positivity) one_pos, one_div]
  have hB := intervalIntegral_rpow_le_of_lt_neg_one (p := -(2 : ℝ)) (s := 4 * lam) (t := 1)
    (by norm_num) (by positivity) h4l
  rw [show -(2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, show -(-1 : ℝ) = 1 by norm_num,
    div_one] at hB
  have hε : lowerEps β hβ lam = lam ^ 2 * |Real.log lam| := by
    simp only [lowerEps, not_lt.2 h4.le, h4.ne', ↓reduceIte]
  have hη : lowerEta β hβ lam = lam := by
    simp only [lowerEta, show ¬ β < 3 by linarith, show β ≠ 3 by linarith, ↓reduceIte]
  have hL := log_inv_four_mul_le hlam h64
  have hl1 := one_le_abs_log_of_sixtyFour_mul_le hlam h64
  have hsq : 0 ≤ lam ^ 2 := by positivity
  have hE : lam ^ 2 + 2 * lam ^ 2 * (32 * Real.pi * Real.log (4 * lam)⁻¹) ≤
      (1 + 64 * Real.pi) * lowerEps β hβ lam := by
    rw [hε]
    have e1 := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 64 * Real.pi * lam ^ 2)
    have e2 := mul_le_mul_of_nonneg_left hl1 hsq
    linarith only [e1, e2]
  have hF : 2 * lam ^ 2 * (16 * ∫ s in (4 * lam)..1, s ^ (-(2 : ℝ))) ≤ 8 * lowerEta β hβ lam := by
    rw [hη]
    calc 2 * lam ^ 2 * (16 * ∫ s in (4 * lam)..1, s ^ (-(2 : ℝ)))
        ≤ 2 * lam ^ 2 * (16 * (4 * lam)⁻¹) := by gcongr
      _ = 8 * lam := by field_simp; ring
  have hq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  rw [Real.rpow_two, hA]
  have e : lam ^ 2 + 2 * lam ^ 2 * (32 * Real.pi * Real.log (4 * lam)⁻¹ +
        16 / Real.sqrt N * (∫ s in (4 * lam)..1, s ^ (-(2 : ℝ)))) =
      (lam ^ 2 + 2 * lam ^ 2 * (32 * Real.pi * Real.log (4 * lam)⁻¹)) +
      2 * lam ^ 2 * (16 * ∫ s in (4 * lam)..1, s ^ (-(2 : ℝ))) / Real.sqrt N := by
    ring
  rw [e]
  exact mul_add_div_le_of_le ENNReal.toReal_nonneg hq (lowerEps_nonneg hβ hlam)
    (lowerEta_nonneg hβ hlam) (by positivity) (by norm_num) hE hF

/-! ### The critical profile `β = 4` -/

/-- A primitive of `-φ_4'(s) (32π s² + 16 s / q)`, where
`-φ_4'(s) = (λ/s)² (1 + 2 log(s/λ)) / s`. -/
theorem hasDerivAt_phiFour_primitive {lam q s : ℝ} (hlam : 0 < lam) (hq : q ≠ 0) (hs : 0 < s) :
    HasDerivAt (fun x => lam ^ 2 * (32 * Real.pi * (Real.log (x / lam) + Real.log (x / lam) ^ 2) -
        16 / q * (3 + 2 * Real.log (x / lam)) / x))
      (-(-((lam / s) ^ 2 * (1 + 2 * Real.log (s / lam)) / s)) *
        (32 * Real.pi * s ^ 2 + 16 * s / q)) s := by
  have hL : HasDerivAt (fun x => Real.log (x / lam)) ((1 / lam) / (s / lam)) s :=
    ((hasDerivAt_id' s).div_const lam).log (div_pos hs hlam).ne'
  have h := (((hL.add (hL.fun_pow 2)).const_mul (32 * Real.pi)).sub
    ((((hL.const_mul 2).const_add 3).const_mul (16 / q)).div (hasDerivAt_id' s)
      hs.ne')).const_mul (lam ^ 2)
  convert h using 1
  have hs0 := hs.ne'
  have hl0 := hlam.ne'
  norm_num
  field_simp
  ring

/-- **Step 3 for `β = 4`** (source l. 1787–1792), where `φ_4(r) = (λ/r)² (1 + log(r/λ))`:
`∫_H φ_4(ϱ(x_i)) ≤ C (ε_λ + η_λ / √N) vol H` for `64 λ ≤ 1`. -/
theorem exists_integral_isolatedPhi_le_four {β : ℝ} (hβ : 2 < β) (h4 : β = 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → 64 * lam ≤ 1 → ∀ i : Fin N,
      ∫ X in placementSet N N (4 * lam) (8 * lam), isolatedPhi β hβ.le lam (lowerRadius hN X i) ≤
        C * (lowerEps β hβ lam + lowerEta β hβ lam / Real.sqrt N) *
          (volume (placementSet N N (4 * lam) (8 * lam))).toReal := by
  subst h4
  refine ⟨(2 + 64 * Real.pi) + 36, by positivity, fun N hN lam hlam h64 i => ?_⟩
  rw [isolatedPhi_eq_of_eq_four hβ rfl]
  have h4l : 4 * lam ≤ 1 := by linarith
  have hpos : ∀ s ∈ Icc (4 * lam) 1, 0 < s := fun s hs => lt_of_lt_of_le (by positivity) hs.1
  have hcont : ContinuousOn (fun s => -((lam / s) ^ 2 * (1 + 2 * Real.log (s / lam)) / s))
      (Icc (4 * lam) 1) := by
    intro s hs
    have hs0 := hpos s hs
    exact ((((continuousAt_const.div continuousAt_id hs0.ne').pow 2).mul
      (continuousAt_const.add (continuousAt_const.mul
        ((continuousAt_id.div_const lam).log (div_pos hs0 hlam).ne')))).div
      continuousAt_id hs0.ne').neg.continuousWithinAt
  have hnp : ∀ s ∈ Icc (4 * lam) 1,
      -((lam / s) ^ 2 * (1 + 2 * Real.log (s / lam)) / s) ≤ 0 := by
    intro s hs
    have hs0 := hpos s hs
    have hlog : 0 ≤ Real.log (s / lam) :=
      Real.log_nonneg ((one_le_div hlam).2 (by linarith [hs.1]))
    have : 0 ≤ (lam / s) ^ 2 * (1 + 2 * Real.log (s / lam)) / s := by positivity
    linarith
  refine (integral_comp_lowerRadius_le hN hlam h64
    (f := fun x => (lam / x) ^ 2 * (1 + Real.log (x / lam)))
    (fun s hs => hasDerivAt_div_sq_mul_one_add_log hlam (hpos s hs)) hcont hnp i).trans ?_
  have hq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  have hsub : uIcc (4 * lam) 1 = Icc (4 * lam) 1 := uIcc_of_le h4l
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_phiFour_primitive hlam hq.ne' (hpos s (hsub ▸ hs)))
    (ContinuousOn.intervalIntegrable (by rw [hsub]; exact hcont.neg.mul (by fun_prop)))]
  -- evaluation at the endpoints
  set ℓ := |Real.log lam| with hℓ
  have hl1 : 1 ≤ ℓ := one_le_abs_log_of_sixtyFour_mul_le hlam h64
  have hL1 : Real.log (1 / lam) = ℓ := by
    rw [one_div, Real.log_inv, hℓ, abs_of_nonpos (Real.log_nonpos hlam.le (by linarith))]
  have hL4 : Real.log (4 * lam / lam) = Real.log 4 := by
    rw [mul_div_assoc, div_self hlam.ne', mul_one]
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl43 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hε : lowerEps 4 hβ lam = lam ^ 2 * ℓ ^ 2 := by simp [lowerEps, hℓ]
  have hη : lowerEta 4 hβ lam = lam := by norm_num [lowerEta]
  have e : (lam / 1) ^ 2 * (1 + Real.log (1 / lam)) +
      (lam ^ 2 * (32 * Real.pi * (Real.log (1 / lam) + Real.log (1 / lam) ^ 2) -
          16 / Real.sqrt N * (3 + 2 * Real.log (1 / lam)) / 1) -
        lam ^ 2 * (32 * Real.pi * (Real.log (4 * lam / lam) + Real.log (4 * lam / lam) ^ 2) -
          16 / Real.sqrt N * (3 + 2 * Real.log (4 * lam / lam)) / (4 * lam))) =
      (lam ^ 2 * (1 + ℓ) + 32 * Real.pi * (lam ^ 2 * (ℓ + ℓ ^ 2)) -
          32 * Real.pi * (lam ^ 2 * (Real.log 4 + Real.log 4 ^ 2))) +
        (4 * lam * (3 + 2 * Real.log 4) - 16 * lam ^ 2 * (3 + 2 * ℓ)) / Real.sqrt N := by
    rw [hL1, hL4]
    have hl0 := hlam.ne'
    have hq0 := hq.ne'
    field_simp
    ring
  rw [e]
  have hsq : 0 ≤ lam ^ 2 := by positivity
  have hE : lam ^ 2 * (1 + ℓ) + 32 * Real.pi * (lam ^ 2 * (ℓ + ℓ ^ 2)) -
      32 * Real.pi * (lam ^ 2 * (Real.log 4 + Real.log 4 ^ 2)) ≤
      (2 + 64 * Real.pi) * lowerEps 4 hβ lam := by
    rw [hε]
    have hℓ2 : ℓ ≤ ℓ ^ 2 := le_self_pow₀ hl1 two_ne_zero
    have k1 : lam ^ 2 * (1 + ℓ) ≤ lam ^ 2 * (2 * ℓ ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hsq
    have k2 : 32 * Real.pi * (lam ^ 2 * (ℓ + ℓ ^ 2)) ≤
        32 * Real.pi * (lam ^ 2 * (2 * ℓ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hsq) (by positivity)
    have k3 : 0 ≤ 32 * Real.pi * (lam ^ 2 * (Real.log 4 + Real.log 4 ^ 2)) := by positivity
    have e2 : (2 + 64 * Real.pi) * (lam ^ 2 * ℓ ^ 2) =
        lam ^ 2 * (2 * ℓ ^ 2) + 32 * Real.pi * (lam ^ 2 * (2 * ℓ ^ 2)) := by ring
    rw [e2]
    linarith only [k1, k2, k3]
  have hF : 4 * lam * (3 + 2 * Real.log 4) - 16 * lam ^ 2 * (3 + 2 * ℓ) ≤
      36 * lowerEta 4 hβ lam := by
    rw [hη]
    have k1 : 4 * lam * (3 + 2 * Real.log 4) ≤ 4 * lam * 9 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have k2 : 0 ≤ 16 * lam ^ 2 * (3 + 2 * ℓ) := by positivity
    linarith only [k1, k2]
  exact mul_add_div_le_of_le ENNReal.toReal_nonneg hq (lowerEps_nonneg hβ hlam)
    (lowerEta_nonneg hβ hlam) (by positivity) (by norm_num) hE hF

/-! ### The expectation -/

/-- **Expectation of `φ_β(ϱ(x_i))` over `H`** (source
Proposition 4.1, Step 3, l. 1787–1792):
`E_ℚ[φ_β(ϱ(x_1))] ≤ φ_β(1) + C ∫_{4λ}^1 (-φ_β'(r)) (r² + r/√N) dr ≤ C_β (ε_λ + η_λ / √N)`,
written as `∫_H φ_β(ϱ(x_i)) ≤ C (ε_λ + η_λ / √N) vol H` for `0 < λ < 1/64`. -/
theorem expectation_isolatedPhi_lowerRadius_le {β : ℝ} (hβ : 2 < β) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam < lam₀ →
      ∀ i : Fin N,
        ∫ X in placementSet N N (4 * lam) (8 * lam), isolatedPhi β hβ.le lam (lowerRadius hN X i) ≤
          C * (lowerEps β hβ lam + lowerEta β hβ lam / Real.sqrt N) *
            (volume (placementSet N N (4 * lam) (8 * lam))).toReal := by
  obtain ⟨C, hC, h⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam →
      64 * lam ≤ 1 → ∀ i : Fin N,
        ∫ X in placementSet N N (4 * lam) (8 * lam), isolatedPhi β hβ.le lam (lowerRadius hN X i) ≤
          C * (lowerEps β hβ lam + lowerEta β hβ lam / Real.sqrt N) *
            (volume (placementSet N N (4 * lam) (8 * lam))).toReal := by
    rcases lt_trichotomy β 4 with h4 | h4 | h4
    · exact exists_integral_isolatedPhi_le_of_lt_four hβ h4
    · exact exists_integral_isolatedPhi_le_four hβ h4
    · exact exists_integral_isolatedPhi_le_of_four_lt hβ h4
  exact ⟨1 / 64, C, by norm_num, hC, fun N hN lam hlam hlam₀ i =>
    h N hN lam hlam (by linarith) i⟩

end TwoComponentCoulomb

end
