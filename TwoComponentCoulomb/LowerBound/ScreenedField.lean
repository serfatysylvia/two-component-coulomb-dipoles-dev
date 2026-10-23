/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.LowerBound.NeumannDipole
public import TwoComponentCoulomb.Potential.DiscDivergence
public import TwoComponentCoulomb.Potential.Electric
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.ElectricEnergy
import TwoComponentCoulomb.Potential.PairIntegral

/-!
# The weak Neumann problem, the pasted field and eq. (hui) (Proposition 4.1, Step 1)

Source: Proposition 4.1, Step 1 (l. 1671–1734), as ruled in
R22. On each disc `B(x_i, ϱ(x_i))` the source lets `u_i` solve the Neumann problem
`-Δu_i = 2π(δ_{x_i}^{(λ)} - δ_{y_i}^{(λ)})` in `B(x_i, ϱ(x_i))`, `∂_ν u_i = 0` on its boundary
(l. 1686–1693), pastes the fields into `E = Σ_i 1_{B(x_i, ϱ(x_i))} ∇u_i` (l. 1695–1696), observes
eq. (divE) `-div E = 2π Σ_i (δ_{x_i}^{(λ)} - δ_{y_i}^{(λ)}) = -Δh_λ` in `ℝ²` (l. 1697–1699), and
deduces eq. (hui) `∫ |∇h_λ|² ≤ Σ_i ∫_{B(x_i, ϱ(x_i))} |∇u_i|²` from the `L²` projection onto
gradients (l. 1700–1707). Under ruling R22a, `u_i` is the explicit image-charge solution
`neumannPotential` of `LowerBound/NeumannDipole.lean` (with its correction `v_i` and eq.
(estimatesv)), and the Neumann problem is checked in weak form by the divergence theorem on a disc
(`Potential/DiscDivergence.lean`). Here `c, y, ρ` stand for `x_i, y_i, ϱ(x_i)`.

Main results (standing hypotheses `0 < λ`, `4λ ≤ ρ`, `|y - c| ≤ ρ/2`):

* `integral_ball_fderiv_neumannField` : the Neumann problem in weak form,
  `∫_{B(c,ρ)} ∇ξ · ∇u = 2π (∫ ξ dδ_c^{(λ)} - ∫ ξ dδ_y^{(λ)})` for `ξ` of class `C¹` on a
  neighbourhood of `B̄(c, ρ)` (l. 1686–1693). With a smooth cutoff `χ` (`χ = 1` on `B̄(c, 13ρ/16)`,
  `χ = 0` off `B(c, 7ρ/8)`) we split `ξ = χξ + (1 - χ)ξ`.
  `integral_ball_fderiv_neumannField_of_contDiff` treats `χξ`: the disc potentials give the
  whole-plane Green identity `integral_fderiv_apply_discField`, and `∇v` is divergence free with
  `χξ = 0` on `∂B(c, ρ)`. `integral_ball_fderiv_neumannField_of_eq_zero` treats `(1 - χ)ξ`: the
  divergence theorem applies to `(1 - χ)ξ ∇u`, which is `C¹` because `∇u` is antiholomorphic (hence
  smooth and divergence free) on the annulus `3ρ/4 < |z - c| < 2ρ`, and the flux vanishes by the
  Neumann condition `inner_neumannField_eq_zero`.
* `screenedField` : the pasted field `E` (l. 1695–1696).
* `integral_fderiv_apply_screenedField` : eq. (divE) in weak form,
  `∫ ∇ξ · E = 2π Σ_i (∫ ξ dδ_{x_i}^{(λ)} - ∫ ξ dδ_{y_i}^{(λ)})` for `ξ` of class `C¹` on `ℂ`;
  `integral_fderiv_apply_screenedField_eq_electricField` : its reading `-div E = -Δh_λ`,
  `∫ ∇ξ · E = ∫ ∇ξ · ∇h_λ` for `ξ` of class `C¹` with compact support (l. 1697–1699).
* `integral_norm_sq_electricField_le_screened` : eq. (hui) for disjoint discs (l. 1700–1707), from
  `∫ |E|² = Σ_i ∫_{B(x_i, ϱ(x_i))} |∇u_i|²` (`integral_norm_sq_screenedField`),
  `∫ ∇h_λ · E = ∫ |∇h_λ|²` (eq. (divE) tested against `h_λ` and the energy identity
  `integral_norm_sq_electricField`), and `0 ≤ ∫ |E - ∇h_λ|²`.

The energy of each ball (l. 1717–1724) and eq. (majof) (l. 1726) are in
`LowerBound/NeumannEnergy.lean`.
-/

public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ComplexConjugate

namespace TwoComponentCoulomb

/-! ### Cutoffs and fields vanishing near a point -/

/-- A smooth cutoff about `c`: `χ = 1` on `B̄(c, 13ρ/16)` and `χ = 0` off `B(c, 7ρ/8)`. -/
theorem exists_neumannCutoff {ρ : ℝ} (hρ : 0 < ρ) (c : ℂ) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 1 χ ∧ (∀ z, ‖z - c‖ ≤ 13 * ρ / 16 → χ z = 1) ∧
      ∀ z, 7 * ρ / 8 ≤ ‖z - c‖ → χ z = 0 := by
  let f : ContDiffBump c := ⟨13 * ρ / 16, 7 * ρ / 8, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, fun z hz => ?_, fun z hz => ?_⟩
  · exact f.one_of_mem_closedBall (mem_closedBall_iff_norm.2 hz)
  · exact f.zero_of_le_dist (by rwa [dist_eq_norm])

/-- The divergence only depends on the germ of the field. -/
theorem divergence_eq_of_eventuallyEq {F G : ℂ → ℂ} {z : ℂ} (h : F =ᶠ[𝓝 z] G) :
    divergence F z = divergence G z := by
  rw [divergence, divergence, h.fderiv_eq]

/-- A function vanishing on the open set `{r < |z - c|}` vanishes near each of its points. -/
theorem eventuallyEq_zero_of_lt_norm_sub {E : Type*} [Zero E] {φ : ℂ → E} {c z : ℂ} {r : ℝ}
    (hφ : ∀ w, r ≤ ‖w - c‖ → φ w = 0) (hz : r < ‖z - c‖) : φ =ᶠ[𝓝 z] fun _ => 0 := by
  have hopen : IsOpen {w : ℂ | r < ‖w - c‖} :=
    isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
  filter_upwards [hopen.mem_nhds hz] with w hw using hφ w (le_of_lt hw)

/-- A function vanishing on the open set `{|z - c| < r}` vanishes near each of its points. -/
theorem eventuallyEq_zero_of_norm_sub_lt {E : Type*} [Zero E] {φ : ℂ → E} {c z : ℂ} {r : ℝ}
    (hφ : ∀ w, ‖w - c‖ < r → φ w = 0) (hz : ‖z - c‖ < r) : φ =ᶠ[𝓝 z] fun _ => 0 := by
  have hopen : IsOpen {w : ℂ | ‖w - c‖ < r} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw using hφ w hw

/-- If `χ` is `C¹` and vanishes off `B(c, r)`, and `ξ` is `C¹` on an open set containing
`B̄(c, r)`, then `χ ξ` is `C¹` on `ℂ`. -/
theorem contDiff_mul_of_contDiffOn {χ ξ : ℂ → ℝ} {c : ℂ} {r : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hcU : closedBall c r ⊆ U) (hχ : ContDiff ℝ 1 χ) (hχ0 : ∀ z, r ≤ ‖z - c‖ → χ z = 0)
    (hξ : ContDiffOn ℝ 1 ξ U) : ContDiff ℝ 1 fun z => χ z * ξ z := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : ‖z - c‖ ≤ r
  · have hzU : z ∈ U := hcU (mem_closedBall_iff_norm.2 hz)
    exact hχ.contDiffAt.mul (hξ.contDiffAt (hU.mem_nhds hzU))
  · refine contDiffAt_const.congr_of_eventuallyEq
      (eventuallyEq_zero_of_lt_norm_sub (φ := fun w => χ w * ξ w) (fun w hw => ?_) (not_le.1 hz))
    rw [hχ0 w hw, zero_mul]

/-! ### The Neumann problem in weak form -/

section Weak

variable {lam ρ : ℝ} {c y : ℂ}

/-- `∇ξ · ∇u` is integrable on `B(c, ρ)` for `ξ` of class `C¹` on a neighbourhood of `B̄(c, ρ)`. -/
theorem integrableOn_ball_fderiv_apply_neumannField (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) {ξ : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hcU : closedBall c ρ ⊆ U) (hξ : ContDiffOn ℝ 1 ξ U) :
    IntegrableOn (fun z => fderiv ℝ ξ z (neumannField lam ρ c y z)) (ball c ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : ContinuousOn (fun z => fderiv ℝ ξ z) (closedBall c ρ) :=
    (hξ.continuousOn_fderiv_of_isOpen hU le_rfl).mono hcU
  have h2 : ContinuousOn (neumannField lam ρ c y) (closedBall c ρ) :=
    (continuousOn_neumannField hlam hρ hy).mono (closedBall_subset_ball (by linarith))
  exact ((h1.clm_apply h2).integrableOn_compact (isCompact_closedBall c ρ)).mono_set
    ball_subset_closedBall

/-- `|∇u|²` is integrable on `B(c, ρ)`. -/
theorem integrableOn_ball_norm_sq_neumannField (hlam : 0 < lam)
    (hρ : 4 * lam ≤ ρ) (hy : ‖y - c‖ ≤ ρ / 2) :
    IntegrableOn (fun w => ‖neumannField lam ρ c y w‖ ^ 2) (ball c ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have hcont : ContinuousOn (fun w => ‖neumannField lam ρ c y w‖ ^ 2) (closedBall c ρ) :=
    ((continuousOn_neumannField hlam hρ hy).mono (closedBall_subset_ball (by linarith))).norm.pow 2
  exact (hcont.integrableOn_compact (μ := volume) (isCompact_closedBall _ _)).mono_set
    ball_subset_closedBall

/-- **The weak Neumann problem, compactly supported part**: for `φ` of class `C¹` on `ℂ` vanishing
off `B(c, 7ρ/8)`, `∫_{B(c,ρ)} ∇φ · ∇u = 2π ∫ φ d(δ_c^{(λ)} - δ_y^{(λ)})`. The disc potentials give
the whole-plane Green identity, and `∇v` is divergence free with `φ = 0` on `∂B(c, ρ)`. -/
theorem integral_ball_fderiv_neumannField_of_contDiff (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφ0 : ∀ z, 7 * ρ / 8 ≤ ‖z - c‖ → φ z = 0) :
    ∫ z in ball c ρ, fderiv ℝ φ z (neumannField lam ρ c y z) =
      2 * Real.pi * ((∫ w, φ w ∂smearedCharge c lam) - ∫ w, φ w ∂smearedCharge y lam) := by
  have hρ0 : 0 < ρ := by linarith
  have hfd0 : ∀ z, z ∉ ball c ρ → fderiv ℝ φ z = 0 := by
    intro z hz
    rw [mem_ball_iff_norm, not_lt] at hz
    rw [(eventuallyEq_zero_of_lt_norm_sub hφ0 (by linarith)).fderiv_eq, fderiv_const_apply]
  have hφc : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall c (7 * ρ / 8)) fun z hz => hφ0 z ?_
    rw [mem_closedBall_iff_norm, not_le] at hz
    exact hz.le
  have hdφ : Continuous fun z => fderiv ℝ φ z := hφ.continuous_fderiv one_ne_zero
  have hA : Continuous fun z => fderiv ℝ φ z (discField lam (z - c)) :=
    hdφ.clm_apply ((continuous_discField hlam).comp (continuous_id.sub continuous_const))
  have hB : Continuous fun z => fderiv ℝ φ z (discField lam (z - y)) :=
    hdφ.clm_apply ((continuous_discField hlam).comp (continuous_id.sub continuous_const))
  have hC : ContinuousOn (fun z => fderiv ℝ φ z (neumannCorrectionField ρ c y z))
      (closedBall c ρ) :=
    hdφ.continuousOn.clm_apply ((continuousOn_neumannCorrectionField hρ0 hy).mono
      (closedBall_subset_ball (by linarith)))
  have iA := (hA.continuousOn.integrableOn_compact (μ := volume)
    (isCompact_closedBall c ρ)).mono_set ball_subset_closedBall
  have iB := (hB.continuousOn.integrableOn_compact (μ := volume)
    (isCompact_closedBall c ρ)).mono_set ball_subset_closedBall
  have iC := (hC.integrableOn_compact (μ := volume) (isCompact_closedBall c ρ)).mono_set
    ball_subset_closedBall
  have eA : ∫ z in ball c ρ, fderiv ℝ φ z (discField lam (z - c)) =
      2 * Real.pi * ∫ w, φ w ∂smearedCharge c lam := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [hfd0 z hz, zero_apply]]
    exact integral_fderiv_apply_discField hφ hφc hlam c
  have eB : ∫ z in ball c ρ, fderiv ℝ φ z (discField lam (z - y)) =
      2 * Real.pi * ∫ w, φ w ∂smearedCharge y lam := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [hfd0 z hz, zero_apply]]
    exact integral_fderiv_apply_discField hφ hφc hlam y
  have hconj : neumannCorrectionField ρ c y = fun w => conj (neumannCorrectionHolo ρ c y w) :=
    funext (neumannCorrectionField_eq_conj ρ c y)
  have eC : ∫ z in ball c ρ, fderiv ℝ φ z (neumannCorrectionField ρ c y z) = 0 := by
    rw [integral_ball_fderiv_apply_of_divergence_eq_zero hρ0 isOpen_ball
      (closedBall_subset_ball (by linarith)) hφ.contDiffOn
      (contDiffOn_neumannCorrectionField hρ0 hy) fun z hz => ?_]
    · have h0 : ∀ θ : ℝ, φ (circleMap c ρ θ) = 0 := fun θ => hφ0 _ (by
        rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ0]
        linarith)
      simp only [h0, zero_mul, intervalIntegral.integral_zero, mul_zero]
    · rw [hconj]
      refine divergence_conj (differentiableAt_neumannCorrectionHolo hρ0 hy ?_)
      rw [mem_ball_iff_norm] at hz
      linarith
  have hsplit : ∀ z, fderiv ℝ φ z (neumannField lam ρ c y z) =
      fderiv ℝ φ z (discField lam (z - c)) - fderiv ℝ φ z (discField lam (z - y)) +
        fderiv ℝ φ z (neumannCorrectionField ρ c y z) := fun z => by
    rw [neumannField_apply, map_add, map_sub]
  have iAB : IntegrableOn (fun z => fderiv ℝ φ z (discField lam (z - c)) -
      fderiv ℝ φ z (discField lam (z - y))) (ball c ρ) := iA.sub iB
  simp_rw [hsplit]
  rw [integral_add iAB iC, integral_sub iA iB, eA, eB, eC]
  ring

/-- **The weak Neumann problem, part vanishing near the charges**: for `ψ` of class `C¹` on a
neighbourhood of `B̄(c, ρ)` vanishing on `B(c, 13ρ/16)`, `∫_{B(c,ρ)} ∇ψ · ∇u = 0`. By the
divergence theorem for `ψ ∇u`, which is `C¹` because `∇u` is smooth on the annulus
`3ρ/4 < |z - c| < 2ρ`; there `div ∇u = 0` (`∇u` is antiholomorphic), and the flux vanishes by
the Neumann condition. -/
theorem integral_ball_fderiv_neumannField_of_eq_zero (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) {ψ : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hcU : closedBall c ρ ⊆ U)
    (hψ : ContDiffOn ℝ 1 ψ U) (hψ0 : ∀ z, ‖z - c‖ < 13 * ρ / 16 → ψ z = 0) :
    ∫ z in ball c ρ, fderiv ℝ ψ z (neumannField lam ρ c y z) = 0 := by
  have hρ0 : 0 < ρ := by linarith
  set G := neumannField lam ρ c y with hGdef
  set F : ℂ → ℂ := fun w => ψ w • G w with hFdef
  set V := U ∩ ball c (2 * ρ) with hVdef
  have hV : IsOpen V := hU.inter isOpen_ball
  have hcV : closedBall c ρ ⊆ V := subset_inter hcU (closedBall_subset_ball (by linarith))
  have hFev : ∀ z, ‖z - c‖ < 13 * ρ / 16 → F =ᶠ[𝓝 z] fun _ => 0 := fun z hz =>
    eventuallyEq_zero_of_norm_sub_lt (fun w hw => by rw [hFdef]; simp [hψ0 w hw]) hz
  have hann : ∀ z ∈ V, ¬‖z - c‖ < 13 * ρ / 16 →
      z ∈ {w : ℂ | 3 * ρ / 4 < ‖w - c‖ ∧ ‖w - c‖ < 2 * ρ} := fun z hz h =>
    ⟨by linarith, mem_ball_iff_norm.1 hz.2⟩
  have hGat : ∀ z ∈ V, ¬‖z - c‖ < 13 * ρ / 16 → ContDiffAt ℝ 1 G z := fun z hz h =>
    (contDiffOn_neumannField_annulus hρ hy).contDiffAt
      ((isOpen_neumannAnnulus ρ c).mem_nhds (hann z hz h))
  have hψat : ∀ z ∈ V, ContDiffAt ℝ 1 ψ z := fun z hz => hψ.contDiffAt (hU.mem_nhds hz.1)
  have hF : ContDiffOn ℝ 1 F V := by
    intro z hz
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases h : ‖z - c‖ < 13 * ρ / 16
    · exact contDiffAt_const.congr_of_eventuallyEq (hFev z h)
    · exact (hψat z hz).smul (hGat z hz h)
  have hdiv : ∀ z ∈ ball c ρ, divergence F z = fderiv ℝ ψ z (G z) := by
    intro z hz
    have hzV := hcV (ball_subset_closedBall hz)
    by_cases h : ‖z - c‖ < 13 * ρ / 16
    · rw [divergence_eq_of_eventuallyEq (hFev z h),
        (eventuallyEq_zero_of_norm_sub_lt hψ0 h).fderiv_eq]
      simp [divergence]
    · rw [hFdef, divergence_smul ((hψat z hzV).differentiableAt one_ne_zero)
        ((hGat z hzV h).differentiableAt one_ne_zero)]
      have hz' := hann z hzV h
      have hGH : G =ᶠ[𝓝 z] fun w => conj (neumannHolo ρ c y w) := by
        filter_upwards [(isOpen_neumannAnnulus ρ c).mem_nhds hz'] with w hw
        exact neumannField_eq_conj_neumannHolo hρ hy hw.1
      rw [divergence_eq_of_eventuallyEq hGH,
        divergence_conj (differentiableAt_neumannHolo hy hz'.1 hz'.2), mul_zero, add_zero]
  have hbd : ∀ θ : ℝ, inner ℝ (F (circleMap c ρ θ)) (circleMap 0 1 θ) = 0 := by
    intro θ
    have hnorm : ‖circleMap c ρ θ - c‖ = ρ := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ0]
    have hN := inner_neumannField_eq_zero hlam hρ hy hnorm
    have hsc : circleMap c ρ θ - c = ρ • circleMap 0 1 θ := by
      rw [circleMap_sub_center, circleMap_zero, circleMap_zero, Complex.real_smul,
        Complex.ofReal_one, one_mul]
    rw [hsc, real_inner_smul_right, mul_eq_zero] at hN
    rw [hFdef, real_inner_smul_left, hN.resolve_left hρ0.ne', mul_zero]
  rw [← setIntegral_congr_fun measurableSet_ball hdiv, integral_ball_divergence hρ0 hV hcV hF]
  simp only [hbd, intervalIntegral.integral_zero, mul_zero]

/-- **The Neumann problem in weak form** (source l. 1688–1689, ruling R22a): for `ξ` of class `C¹`
on an open set containing `B̄(c, ρ)`,
`∫_{B(c,ρ)} ∇ξ · ∇u = 2π (∫ ξ dδ_c^{(λ)} - ∫ ξ dδ_y^{(λ)})`, i.e. `-Δu = 2π(δ_c^{(λ)} - δ_y^{(λ)})`
in `B(c, ρ)` with `∂_ν u = 0` on `∂B(c, ρ)`. -/
theorem integral_ball_fderiv_neumannField {lam ρ : ℝ} {c y : ℂ} (hlam : 0 < lam)
    (hρ : 4 * lam ≤ ρ) (hy : ‖y - c‖ ≤ ρ / 2) {ξ : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hcU : Metric.closedBall c ρ ⊆ U) (hξ : ContDiffOn ℝ 1 ξ U) :
    ∫ z in Metric.ball c ρ, fderiv ℝ ξ z (neumannField lam ρ c y z) =
      2 * Real.pi * ((∫ w, ξ w ∂smearedCharge c lam) - ∫ w, ξ w ∂smearedCharge y lam) := by
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨χ, hχ, hχ1, hχ0⟩ := exists_neumannCutoff hρ0 c
  set φ : ℂ → ℝ := fun z => χ z * ξ z with hφdef
  set ψ : ℂ → ℝ := fun z => ξ z - φ z with hψdef
  have hsub : closedBall c (7 * ρ / 8) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hcU
  have hφ : ContDiff ℝ 1 φ := contDiff_mul_of_contDiffOn hU hsub hχ hχ0 hξ
  have hφ0 : ∀ z, 7 * ρ / 8 ≤ ‖z - c‖ → φ z = 0 := fun z hz => by
    rw [hφdef]
    simp only [hχ0 z hz, zero_mul]
  have hψ : ContDiffOn ℝ 1 ψ U := hξ.sub hφ.contDiffOn
  have hψ0 : ∀ z, ‖z - c‖ < 13 * ρ / 16 → ψ z = 0 := fun z hz => by
    rw [hψdef, hφdef]
    simp only [hχ1 z hz.le, one_mul, sub_self]
  have hδ : ∀ w₀ : ℂ, ‖w₀ - c‖ ≤ ρ / 2 →
      ∫ w, φ w ∂smearedCharge w₀ lam = ∫ w, ξ w ∂smearedCharge w₀ lam := by
    intro w₀ hw₀
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_ball_smearedCharge w₀ lam] with w hw
    have hw' : ‖w - c‖ ≤ 13 * ρ / 16 := by
      rw [mem_ball_iff_norm] at hw
      have := norm_add_le (w - w₀) (w₀ - c)
      rw [sub_add_sub_cancel] at this
      linarith
    rw [hφdef]
    simp only [hχ1 w hw', one_mul]
  have hsplit : ∀ z ∈ ball c ρ, fderiv ℝ ξ z (neumannField lam ρ c y z) =
      fderiv ℝ φ z (neumannField lam ρ c y z) + fderiv ℝ ψ z (neumannField lam ρ c y z) := by
    intro z hz
    have hzU : z ∈ U := hcU (ball_subset_closedBall hz)
    have hξz : DifferentiableAt ℝ ξ z :=
      (hξ.differentiableOn one_ne_zero z hzU).differentiableAt (hU.mem_nhds hzU)
    rw [hψdef, fderiv_fun_sub hξz (hφ.differentiable one_ne_zero z),
      sub_apply]
    ring
  have hc : ‖c - c‖ ≤ ρ / 2 := by rw [sub_self, norm_zero]; linarith
  rw [setIntegral_congr_fun measurableSet_ball hsplit,
    integral_add (integrableOn_ball_fderiv_apply_neumannField hlam hρ hy hU hcU hφ.contDiffOn)
      (integrableOn_ball_fderiv_apply_neumannField hlam hρ hy hU hcU hψ),
    integral_ball_fderiv_neumannField_of_contDiff hlam hρ hy hφ hφ0,
    integral_ball_fderiv_neumannField_of_eq_zero hlam hρ hy hU hcU hψ hψ0, add_zero, hδ c hc,
    hδ y hy]

end Weak

/-! ### The pasted field `E` and eq. (divE) -/

/-- The pasted field `E = Σ_i 1_{B(x_i, ρ_i)} ∇u_i` (source l. 1695–1696). -/
noncomputable def screenedField {N : ℕ} (lam : ℝ) (ρ : Fin N → ℝ) (X Y : Fin N → ℂ) (z : ℂ) : ℂ :=
  ∑ i, (Metric.ball (X i) (ρ i)).indicator (fun w => neumannField lam (ρ i) (X i) (Y i) w) z

section Pasted

variable {N : ℕ} {lam : ℝ} {ρ : Fin N → ℝ} {X Y : Fin N → ℂ}

/-- Unfolding `screenedField`. -/
theorem screenedField_apply (lam : ℝ) (ρ : Fin N → ℝ) (X Y : Fin N → ℂ) (z : ℂ) :
    screenedField lam ρ X Y z =
      ∑ i, (ball (X i) (ρ i)).indicator (fun w => neumannField lam (ρ i) (X i) (Y i) w) z := by
  rw [screenedField]

/-- `∇ξ · E = Σ_i 1_{B(x_i, ρ_i)} ∇ξ · ∇u_i`. -/
theorem fderiv_apply_screenedField (ξ : ℂ → ℝ) (z : ℂ) :
    fderiv ℝ ξ z (screenedField lam ρ X Y z) =
      ∑ i, (ball (X i) (ρ i)).indicator
        (fun w => fderiv ℝ ξ w (neumannField lam (ρ i) (X i) (Y i) w)) z := by
  rw [screenedField_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hz : z ∈ ball (X i) (ρ i)
  · rw [indicator_of_mem hz, indicator_of_mem hz]
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, map_zero]

/-- `∇ξ · E` is integrable for `ξ` of class `C¹` on `ℂ`. -/
theorem integrable_fderiv_apply_screenedField (hlam : 0 < lam) (hρ : ∀ i, 4 * lam ≤ ρ i)
    (hY : ∀ i, ‖Y i - X i‖ ≤ ρ i / 2) {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) :
    Integrable fun z => fderiv ℝ ξ z (screenedField lam ρ X Y z) := by
  simp_rw [fderiv_apply_screenedField]
  refine integrable_finsetSum _ fun i _ => ?_
  exact (integrable_indicator_iff measurableSet_ball).2
    (integrableOn_ball_fderiv_apply_neumannField hlam (hρ i) (hY i) isOpen_univ (subset_univ _)
      hξ.contDiffOn)

/-- **Eq. (divE)** in weak form (source l. 1697–1699): for `ξ` of class `C¹` on `ℂ`,
`∫ ∇ξ · E = 2π Σ_i (∫ ξ dδ_{x_i}^{(λ)} - ∫ ξ dδ_{y_i}^{(λ)})`, i.e.
`-div E = 2π Σ_i (δ_{x_i}^{(λ)} - δ_{y_i}^{(λ)})` in `ℝ²`. -/
theorem integral_fderiv_apply_screenedField (hlam : 0 < lam) (hρ : ∀ i, 4 * lam ≤ ρ i)
    (hY : ∀ i, ‖Y i - X i‖ ≤ ρ i / 2) {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) :
    ∫ z, fderiv ℝ ξ z (screenedField lam ρ X Y z) =
      2 * Real.pi *
        ∑ i, ((∫ w, ξ w ∂smearedCharge (X i) lam) - ∫ w, ξ w ∂smearedCharge (Y i) lam) := by
  simp_rw [fderiv_apply_screenedField]
  rw [integral_finsetSum _ fun i _ => (integrable_indicator_iff measurableSet_ball).2
    (integrableOn_ball_fderiv_apply_neumannField hlam (hρ i) (hY i) isOpen_univ (subset_univ _)
      hξ.contDiffOn), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_indicator measurableSet_ball]
  exact integral_ball_fderiv_neumannField hlam (hρ i) (hY i) isOpen_univ (subset_univ _)
    hξ.contDiffOn

/-- **Eq. (divE)**, `-div E = -Δh_λ` (source l. 1697–1699): for `ξ` of class `C¹` with compact
support, `∫ ∇ξ · E = ∫ ∇ξ · ∇h_λ`. -/
theorem integral_fderiv_apply_screenedField_eq_electricField (hlam : 0 < lam)
    (hρ : ∀ i, 4 * lam ≤ ρ i) (hY : ∀ i, ‖Y i - X i‖ ≤ ρ i / 2) {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) :
    ∫ z, fderiv ℝ ξ z (screenedField lam ρ X Y z) =
      ∫ z, fderiv ℝ ξ z (electricField charge (Sum.elim X Y) (fun _ => lam) z) := by
  rw [integral_fderiv_apply_screenedField hlam hρ hY hξ,
    integral_fderiv_apply_electricField hξ hc fun _ => hlam, Fintype.sum_sum_type]
  simp only [charge_inl, charge_inr, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
    Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  ring

/-! ### The projection inequality (hui) -/

/-- Disjoint discs: a point lies in at most one of the discs `B(x_i, ρ_i)`. -/
theorem notMem_ball_of_mem_ball_of_disjoint (hdisj : ∀ i j, i ≠ j → ρ i + ρ j ≤ ‖X i - X j‖)
    {i j : Fin N} (hij : j ≠ i) {z : ℂ} (hz : z ∈ ball (X i) (ρ i)) : z ∉ ball (X j) (ρ j) := by
  intro hz'
  rw [mem_ball] at hz hz'
  have h := hdisj j i hij
  have h' := dist_triangle_left (X j) (X i) z
  rw [← dist_eq_norm] at h
  linarith

/-- For disjoint discs, `|E|² = Σ_i 1_{B(x_i, ρ_i)} |∇u_i|²`. -/
theorem norm_sq_screenedField (hdisj : ∀ i j, i ≠ j → ρ i + ρ j ≤ ‖X i - X j‖) (z : ℂ) :
    ‖screenedField lam ρ X Y z‖ ^ 2 =
      ∑ i, (ball (X i) (ρ i)).indicator
        (fun w => ‖neumannField lam (ρ i) (X i) (Y i) w‖ ^ 2) z := by
  rw [screenedField_apply]
  by_cases h : ∃ i, z ∈ ball (X i) (ρ i)
  · obtain ⟨i, hi⟩ := h
    have hj : ∀ j ≠ i, z ∉ ball (X j) (ρ j) := fun j hj =>
      notMem_ball_of_mem_ball_of_disjoint hdisj hj hi
    rw [Finset.sum_eq_single i (fun j _ hji => indicator_of_notMem (hj j hji) _)
        (fun h => absurd (Finset.mem_univ i) h),
      Finset.sum_eq_single i (fun j _ hji => indicator_of_notMem (hj j hji) _)
        (fun h => absurd (Finset.mem_univ i) h),
      indicator_of_mem hi, indicator_of_mem hi]
  · simp only [not_exists] at h
    simp only [indicator_of_notMem (h _), Finset.sum_const_zero, norm_zero]
    norm_num

/-- For disjoint discs, `|E|²` is integrable. -/
theorem integrable_norm_sq_screenedField (hlam : 0 < lam) (hρ : ∀ i, 4 * lam ≤ ρ i)
    (hdisj : ∀ i j, i ≠ j → ρ i + ρ j ≤ ‖X i - X j‖) (hY : ∀ i, ‖Y i - X i‖ ≤ ρ i / 2) :
    Integrable fun z => ‖screenedField lam ρ X Y z‖ ^ 2 := by
  simp_rw [norm_sq_screenedField hdisj]
  exact integrable_finsetSum _ fun i _ => (integrable_indicator_iff measurableSet_ball).2
    (integrableOn_ball_norm_sq_neumannField hlam (hρ i) (hY i))

/-- For disjoint discs, `∫ |E|² = Σ_i ∫_{B(x_i, ρ_i)} |∇u_i|²`. -/
theorem integral_norm_sq_screenedField (hlam : 0 < lam) (hρ : ∀ i, 4 * lam ≤ ρ i)
    (hdisj : ∀ i j, i ≠ j → ρ i + ρ j ≤ ‖X i - X j‖) (hY : ∀ i, ‖Y i - X i‖ ≤ ρ i / 2) :
    ∫ z, ‖screenedField lam ρ X Y z‖ ^ 2 =
      ∑ i, ∫ z in ball (X i) (ρ i), ‖neumannField lam (ρ i) (X i) (Y i) z‖ ^ 2 := by
  simp_rw [norm_sq_screenedField hdisj]
  rw [integral_finsetSum _ fun i _ => (integrable_indicator_iff measurableSet_ball).2
    (integrableOn_ball_norm_sq_neumannField hlam (hρ i) (hY i))]
  exact Finset.sum_congr rfl fun i _ => integral_indicator measurableSet_ball

/-- `∫ ∇h_λ · E = ∫ |∇h_λ|²`: eq. (divE) tested against `h_λ` (source l. 1700–1705). -/
theorem integral_fderiv_electricPotential_apply_screenedField (hlam : 0 < lam)
    (hρ : ∀ i, 4 * lam ≤ ρ i) (hY : ∀ i, ‖Y i - X i‖ ≤ ρ i / 2) :
    ∫ z, fderiv ℝ (electricPotential charge (Sum.elim X Y) (fun _ => lam)) z
        (screenedField lam ρ X Y z) =
      ∫ x, ‖electricField charge (Sum.elim X Y) (fun _ => lam) x‖ ^ 2 := by
  have hα : ∀ _ : Fin N ⊕ Fin N, 0 < lam := fun _ => hlam
  rw [integral_fderiv_apply_screenedField hlam hρ hY (contDiff_electricPotential hα),
    integral_norm_sq_electricField hα (sum_charge_eq_zero N)]
  have hmean := integral_electricPotential_smearedCharge (d := charge) (z := Sum.elim X Y) hα
  have h2 : ∑ i, ((∫ w, electricPotential charge (Sum.elim X Y) (fun _ => lam) w
        ∂smearedCharge (X i) lam) -
        ∫ w, electricPotential charge (Sum.elim X Y) (fun _ => lam) w ∂smearedCharge (Y i) lam) =
      ∑ a, charge a * ∫ w, electricPotential charge (Sum.elim X Y) (fun _ => lam) w
        ∂smearedCharge (Sum.elim X Y a) lam := by
    rw [Fintype.sum_sum_type]
    simp only [charge_inl, charge_inr, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
      Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    ring
  rw [h2]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hmean a, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **Eq. (hui)** (source l. 1700–1707), the `L²` projection onto gradients: for disjoint discs,
`∫ |∇h_λ|² ≤ Σ_i ∫_{B(x_i, ρ_i)} |∇u_i|²`. -/
theorem integral_norm_sq_electricField_le_screened (hlam : 0 < lam) (X Y : Fin N → ℂ)
    (ρ : Fin N → ℝ) (hρ : ∀ i, 4 * lam ≤ ρ i)
    (hdisj : ∀ i j, i ≠ j → ρ i + ρ j ≤ ‖X i - X j‖) (hY : ∀ i, ‖Y i - X i‖ ≤ ρ i / 2) :
    ∫ x, ‖electricField charge (Sum.elim X Y) (fun _ => lam) x‖ ^ 2 ≤
      ∑ i, ∫ z in Metric.ball (X i) (ρ i), ‖neumannField lam (ρ i) (X i) (Y i) z‖ ^ 2 := by
  have hα : ∀ _ : Fin N ⊕ Fin N, 0 < lam := fun _ => hlam
  set h := electricPotential charge (Sum.elim X Y) (fun _ => lam) with hh
  set H := electricField charge (Sum.elim X Y) (fun _ => lam) with hH
  set E := screenedField lam ρ X Y with hE
  have iE := integrable_norm_sq_screenedField hlam hρ hdisj hY
  have eE := integral_norm_sq_screenedField hlam hρ hdisj hY
  have iH : Integrable fun x => ‖H x‖ ^ 2 :=
    integrable_norm_sq_electricField hα (sum_charge_eq_zero N)
  have iEH : Integrable fun z => fderiv ℝ h z (E z) :=
    integrable_fderiv_apply_screenedField hlam hρ hY (contDiff_electricPotential hα)
  have eEH := integral_fderiv_electricPotential_apply_screenedField hlam hρ hY (X := X) (Y := Y)
  rw [← hh, ← hH, ← hE] at eEH
  have hpt : ∀ z, 2 * fderiv ℝ h z (E z) - ‖H z‖ ^ 2 ≤ ‖E z‖ ^ 2 := by
    intro z
    have h0 := sq_nonneg ‖E z - H z‖
    rw [norm_sub_sq_real, real_inner_comm] at h0
    rw [hh, fderiv_electricPotential_apply hα, ← hH]
    linarith
  have hmono := integral_mono (f := fun z => 2 * fderiv ℝ h z (E z) - ‖H z‖ ^ 2)
    ((iEH.const_mul 2).sub iH) iE hpt
  rw [integral_sub (iEH.const_mul 2) iH, integral_const_mul, eEH, eE] at hmono
  linarith

end Pasted

end TwoComponentCoulomb

end
