/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import TwoComponentCoulomb.Frozen.Kappa
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.Potential.DiscField
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.Electric
import TwoComponentCoulomb.Potential.ElectricDecay
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# The screened dipole on a disc (Proposition 4.1, Step 1)

Source: Proposition 4.1, Step 1 (l. 1762–1825), as ruled in
R22. On the disc `B(c, ρ)` (source `B(x_i, ϱ(x_i))`) with a negative charge at `y`
(source `y_i`, `|y - c| ≤ ρ/2`) and smearing radius `λ` (`4λ ≤ ρ`), the source lets `u_i` solve the
Neumann problem `-Δu_i = 2π(δ_c^{(λ)} - δ_y^{(λ)})` in `B(c, ρ)`, `∂_ν u_i = 0` on `∂B(c, ρ)`
(l. 1779–1783), and decomposes `u_i = g*δ_c^{(λ)} - g*δ_y^{(λ)} + v_i` with `v_i` harmonic
(l. 1798–1806). Under ruling R22a, `u_i` is the explicit image-charge solution of this Neumann
problem: with `ζ = z - c` and `a = y - c`,
`v(z) = log |1 - ζ conj(a) / ρ²|`, the potential of the image of `y` in the circle `∂B(c, ρ)`
(the image point `c + ρ² / conj(a)` lies outside `B(c, 2ρ)`).

* `neumannCorrection`, `neumannCorrectionField` : `v` and `∇v = -a / (ρ² - conj(ζ) a)`.
* `neumannPotential`, `neumannField` : `u = g*δ_c^{(λ)} - g*δ_y^{(λ)} + v` and `∇u`; the disc
  potentials are the explicit `discPotential` of `Potential/DiscField.lean` (ruling R12b).
* `neumannCorrectionHolo`, `neumannHolo` : holomorphic functions whose conjugates are `∇v`
  (on all of `ℂ`) and `∇u` (outside `B(c, 3ρ/4)`, where both charges are point charges).

Main results (standing hypotheses `0 < λ`, `4λ ≤ ρ`, `|y - c| ≤ ρ/2`):

* `hasGradientAt_neumannCorrection`, `hasGradientAt_neumannPotential`,
  `contDiffOn_neumannPotential`, `continuousOn_neumannField`, `contDiffOn_neumannCorrectionField` :
  regularity on `B(c, 2ρ)`.
* `neumannField_eq_conj_neumannHolo`, `differentiableAt_neumannHolo`,
  `neumannCorrectionField_eq_conj`, `differentiableAt_neumannCorrectionHolo`,
  `contDiffOn_neumannField_annulus` : the holomorphic structure off the charges.
* `inner_neumannField_eq_zero` : the Neumann condition `∇u · (z - c) = 0` on `∂B(c, ρ)`
  (l. 1779–1783).
* `norm_neumannCorrectionField_le` : eq. (estimatesv) (l. 1804–1806), with the constant `2`:
  `|∇v| ≤ 2 |y - c| / ρ²` on `B(c, 3ρ/4)`; `norm_neumannCorrection_sub_le` is the resulting
  Lipschitz bound for `v` on `B(c, 3ρ/4)`.
* `abs_integral_neumannCorrection_sub_le` : `|∫ v d(δ_c^{(λ)} - δ_y^{(λ)})| ≤ 2 |y - c|² / ρ²`
  (l. 1807–1814), by translation of `δ_c^{(λ)}` to `δ_y^{(λ)}` and the mean value theorem.
* `integrable_neumannCorrection`, `integrable_neumannPotential`, `integral_neumannPotential_sub` :
  the pair-energy identity of l. 1807–1814,
  `∫ u d(δ_c^{(λ)} - δ_y^{(λ)}) = 2 (g(λ) + κ) - 2 g_λ(y - c) + ∫ v d(δ_c^{(λ)} - δ_y^{(λ)})`.

The weak form of the Neumann problem (`∫_B ∇ξ · ∇u = 2π ∫ ξ d(δ_c^{(λ)} - δ_y^{(λ)})`, by the
divergence theorem on a disc) is proved from this API in a later module.
-/

public section

open MeasureTheory Metric Set InnerProductSpace Filter Topology ComplexConjugate

namespace TwoComponentCoulomb

/-- The harmonic correction `v(z) = log |1 - (z - c) conj(y - c) / ρ²|` of the screened dipole
(source `v_i`, l. 1798–1806); it is `log` of the image-charge factor. -/
noncomputable def neumannCorrection (ρ : ℝ) (c y z : ℂ) : ℝ :=
  Real.log ‖1 - (z - c) * (starRingEnd ℂ) (y - c) / (ρ : ℂ) ^ 2‖

/-- `∇v(z) = -(y - c) / (ρ² - conj(z - c) (y - c))`. -/
noncomputable def neumannCorrectionField (ρ : ℝ) (c y z : ℂ) : ℂ :=
  -((y - c) / ((ρ : ℂ) ^ 2 - (starRingEnd ℂ) (z - c) * (y - c)))

/-- The holomorphic function `-conj(y - c) / (ρ² - (z - c) conj(y - c))` whose conjugate is `∇v`;
it is the complex derivative of `log (1 - (z - c) conj(y - c) / ρ²)`. -/
noncomputable def neumannCorrectionHolo (ρ : ℝ) (c y z : ℂ) : ℂ :=
  -((starRingEnd ℂ) (y - c) / ((ρ : ℂ) ^ 2 - (z - c) * (starRingEnd ℂ) (y - c)))

/-- The screened dipole `u = g*δ_c^{(λ)} - g*δ_y^{(λ)} + v` (source `u_i`, l. 1779–1783). -/
noncomputable def neumannPotential (lam ρ : ℝ) (c y z : ℂ) : ℝ :=
  discPotential lam (z - c) - discPotential lam (z - y) + neumannCorrection ρ c y z

/-- Its gradient `∇u`. -/
noncomputable def neumannField (lam ρ : ℝ) (c y z : ℂ) : ℂ :=
  discField lam (z - c) - discField lam (z - y) + neumannCorrectionField ρ c y z

/-- The holomorphic function `-1/(z - c) + 1/(z - y) - conj(y - c) / (ρ² - (z - c) conj(y - c))`
whose conjugate is `∇u` outside `B(c, 3ρ/4)`. -/
noncomputable def neumannHolo (ρ : ℝ) (c y z : ℂ) : ℂ :=
  -(z - c)⁻¹ + (z - y)⁻¹ + neumannCorrectionHolo ρ c y z

/-! ### Unfolding lemmas

The definitions are not exposed; later modules use these equations. -/

/-- Unfolding `neumannCorrection`. -/
theorem neumannCorrection_apply (ρ : ℝ) (c y z : ℂ) :
    neumannCorrection ρ c y z = Real.log ‖1 - (z - c) * (starRingEnd ℂ) (y - c) / (ρ : ℂ) ^ 2‖ := by
  rw [neumannCorrection]

/-- Unfolding `neumannCorrectionField`. -/
theorem neumannCorrectionField_apply (ρ : ℝ) (c y z : ℂ) :
    neumannCorrectionField ρ c y z =
      -((y - c) / ((ρ : ℂ) ^ 2 - (starRingEnd ℂ) (z - c) * (y - c))) := by
  rw [neumannCorrectionField]

/-- Unfolding `neumannCorrectionHolo`. -/
theorem neumannCorrectionHolo_apply (ρ : ℝ) (c y z : ℂ) :
    neumannCorrectionHolo ρ c y z =
      -((starRingEnd ℂ) (y - c) / ((ρ : ℂ) ^ 2 - (z - c) * (starRingEnd ℂ) (y - c))) := by
  rw [neumannCorrectionHolo]

/-- Unfolding `neumannPotential`. -/
theorem neumannPotential_apply (lam ρ : ℝ) (c y z : ℂ) :
    neumannPotential lam ρ c y z =
      discPotential lam (z - c) - discPotential lam (z - y) + neumannCorrection ρ c y z := by
  rw [neumannPotential]

/-- Unfolding `neumannField`. -/
theorem neumannField_apply (lam ρ : ℝ) (c y z : ℂ) :
    neumannField lam ρ c y z =
      discField lam (z - c) - discField lam (z - y) + neumannCorrectionField ρ c y z := by
  rw [neumannField]

/-- Unfolding `neumannHolo`. -/
theorem neumannHolo_apply (ρ : ℝ) (c y z : ℂ) :
    neumannHolo ρ c y z = -(z - c)⁻¹ + (z - y)⁻¹ + neumannCorrectionHolo ρ c y z := by
  rw [neumannHolo]

/-! ### Elementary bounds on the image-charge factor -/

section Elementary

variable {ρ : ℝ} {c y z : ℂ}

/-- On `B(c, 2ρ)`, `|(z - c) conj(y - c)| < ρ²`: the image charge stays outside `B(c, 2ρ)`. -/
theorem norm_mul_conj_lt_sq (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2) (hz : ‖z - c‖ < 2 * ρ) :
    ‖(z - c) * conj (y - c)‖ < ρ ^ 2 := by
  rw [norm_mul, Complex.norm_conj]
  calc ‖z - c‖ * ‖y - c‖ ≤ ‖z - c‖ * (ρ / 2) := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ < 2 * ρ * (ρ / 2) := mul_lt_mul_of_pos_right hz (by positivity)
    _ = ρ ^ 2 := by ring

/-- `ρ² - |(z - c) conj(y - c)| ≤ |ρ² - (z - c) conj(y - c)|`. -/
theorem sq_sub_norm_le_norm_sq_sub (ρ : ℝ) (c y z : ℂ) :
    ρ ^ 2 - ‖(z - c) * conj (y - c)‖ ≤ ‖(ρ : ℂ) ^ 2 - (z - c) * conj (y - c)‖ := by
  have h := norm_sub_norm_le ((ρ : ℂ) ^ 2) ((z - c) * conj (y - c))
  rwa [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h

/-- The denominator of `neumannCorrectionHolo` does not vanish on `B(c, 2ρ)`. -/
theorem sq_sub_mul_conj_ne_zero (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2) (hz : ‖z - c‖ < 2 * ρ) :
    (ρ : ℂ) ^ 2 - (z - c) * conj (y - c) ≠ 0 := by
  have h1 := norm_mul_conj_lt_sq hρ hy hz
  have h2 := sq_sub_norm_le_norm_sq_sub ρ c y z
  intro h
  rw [h, norm_zero] at h2
  linarith

/-- On `B(c, 2ρ)` the image-charge factor lies in the slit plane (its real part is positive). -/
theorem one_sub_mul_conj_div_mem_slitPlane (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2)
    (hz : ‖z - c‖ < 2 * ρ) :
    1 - (z - c) * conj (y - c) / (ρ : ℂ) ^ 2 ∈ Complex.slitPlane := by
  rw [sub_eq_add_neg]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_neg, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ.le,
    div_lt_one (by positivity)]
  exact norm_mul_conj_lt_sq hρ hy hz

end Elementary

/-! ### The gradient of the real part of a holomorphic function -/

/-- If `F` has complex derivative `F'` at `z`, then `Re F` has gradient `conj F'` at `z`. -/
theorem hasGradientAt_re_of_hasDerivAt {F : ℂ → ℂ} {F' z : ℂ} (h : HasDerivAt F F' z) :
    HasGradientAt (fun w => (F w).re) (conj F') z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (Complex.reCLM.hasFDerivAt.comp z (h.hasFDerivAt.restrictScalars ℝ)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp [Complex.inner]

/-! ### Regularity of the correction `v` on `B(c, 2ρ)` -/

section Correction

variable {ρ : ℝ} {c y z : ℂ}

/-- `∇v = conj h` with `h = neumannCorrectionHolo` holomorphic (everywhere). -/
theorem neumannCorrectionField_eq_conj (ρ : ℝ) (c y z : ℂ) :
    neumannCorrectionField ρ c y z = conj (neumannCorrectionHolo ρ c y z) := by
  simp only [neumannCorrectionField, neumannCorrectionHolo, map_neg, map_div₀, map_sub, map_mul,
    map_pow, Complex.conj_ofReal, Complex.conj_conj]

/-- `v` is the real part of `log (1 - (z - c) conj(y - c) / ρ²)` (everywhere). -/
theorem neumannCorrection_eq_re_log (ρ : ℝ) (c y : ℂ) :
    neumannCorrection ρ c y =
      fun z => (Complex.log (1 - (z - c) * conj (y - c) / (ρ : ℂ) ^ 2)).re := by
  funext z
  rw [Complex.log_re]
  rfl

/-- The complex derivative of `log (1 - (z - c) conj(y - c) / ρ²)` is `neumannCorrectionHolo`. -/
theorem hasDerivAt_log_one_sub_mul_conj_div (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2)
    (hz : ‖z - c‖ < 2 * ρ) :
    HasDerivAt (fun w => Complex.log (1 - (w - c) * conj (y - c) / (ρ : ℂ) ^ 2))
      (neumannCorrectionHolo ρ c y z) z := by
  have hf : HasDerivAt (fun w => 1 - (w - c) * conj (y - c) / (ρ : ℂ) ^ 2)
      (-(1 * conj (y - c) / (ρ : ℂ) ^ 2)) z :=
    ((((hasDerivAt_id' z).sub_const c).mul_const _).div_const _).const_sub 1
  refine (hf.clog (one_sub_mul_conj_div_mem_slitPlane hρ hy hz)).congr_deriv ?_
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hd := sq_sub_mul_conj_ne_zero hρ hy hz
  rw [neumannCorrectionHolo]
  field_simp

/-- `h = neumannCorrectionHolo` is holomorphic on `B(c, 2ρ)`. -/
theorem contDiffAt_neumannCorrectionHolo (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2)
    (hz : ‖z - c‖ < 2 * ρ) {n : WithTop ℕ∞} :
    ContDiffAt ℂ n (neumannCorrectionHolo ρ c y) z := by
  have hd := sq_sub_mul_conj_ne_zero hρ hy hz
  have hg : ContDiffAt ℂ n (fun w => (ρ : ℂ) ^ 2 - (w - c) * conj (y - c)) z :=
    contDiffAt_const.sub ((contDiffAt_id.sub contDiffAt_const).mul contDiffAt_const)
  exact (contDiffAt_const.div hg hd).neg

/-- `h = neumannCorrectionHolo` is complex differentiable on `B(c, 2ρ)`. -/
theorem differentiableAt_neumannCorrectionHolo (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2)
    (hz : ‖z - c‖ < 2 * ρ) : DifferentiableAt ℂ (neumannCorrectionHolo ρ c y) z :=
  (contDiffAt_neumannCorrectionHolo hρ hy hz (n := 1)).differentiableAt one_ne_zero

/-- `h = neumannCorrectionHolo` is holomorphic on `B(c, 2ρ)`. -/
theorem differentiableOn_neumannCorrectionHolo (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2) :
    DifferentiableOn ℂ (neumannCorrectionHolo ρ c y) (ball c (2 * ρ)) := fun _ hz =>
  (differentiableAt_neumannCorrectionHolo hρ hy (mem_ball_iff_norm.1 hz)).differentiableWithinAt

/-- **The gradient of the correction** `v` on `B(c, 2ρ)`. -/
theorem hasGradientAt_neumannCorrection (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2)
    (hz : z ∈ ball c (2 * ρ)) :
    HasGradientAt (neumannCorrection ρ c y) (neumannCorrectionField ρ c y z) z := by
  rw [neumannCorrection_eq_re_log, neumannCorrectionField_eq_conj]
  exact hasGradientAt_re_of_hasDerivAt
    (hasDerivAt_log_one_sub_mul_conj_div hρ hy (mem_ball_iff_norm.1 hz))

/-- `v` is of class `C¹` (indeed smooth) on `B(c, 2ρ)`. -/
theorem contDiffOn_neumannCorrection (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2) :
    ContDiffOn ℝ 1 (neumannCorrection ρ c y) (ball c (2 * ρ)) := by
  intro z hz
  have hz' := mem_ball_iff_norm.1 hz
  refine ContDiffAt.contDiffWithinAt ?_
  rw [neumannCorrection_eq_re_log]
  have hf : ContDiffAt ℂ 1 (fun w => 1 - (w - c) * conj (y - c) / (ρ : ℂ) ^ 2) z :=
    (contDiffAt_const.sub (((contDiffAt_id.sub contDiffAt_const).mul contDiffAt_const).div_const _))
  have hlog : ContDiffAt ℂ 1 (fun w => Complex.log (1 - (w - c) * conj (y - c) / (ρ : ℂ) ^ 2)) z :=
    ContDiffAt.comp (g := Complex.log) z
      (Complex.contDiffAt_log (one_sub_mul_conj_div_mem_slitPlane hρ hy hz')) hf
  exact Complex.reCLM.contDiff.contDiffAt.comp z (hlog.restrict_scalars ℝ)

/-- `v` is continuous on `B(c, 2ρ)`. -/
theorem continuousOn_neumannCorrection (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2) :
    ContinuousOn (neumannCorrection ρ c y) (ball c (2 * ρ)) :=
  (contDiffOn_neumannCorrection hρ hy).continuousOn

/-- `∇v` is of class `C¹` (indeed smooth) on `B(c, 2ρ)`. -/
theorem contDiffOn_neumannCorrectionField (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2) :
    ContDiffOn ℝ 1 (neumannCorrectionField ρ c y) (ball c (2 * ρ)) := by
  intro z hz
  refine ContDiffAt.contDiffWithinAt ?_
  have e : neumannCorrectionField ρ c y =
      fun w => Complex.conjCLE (neumannCorrectionHolo ρ c y w) :=
    funext fun w => neumannCorrectionField_eq_conj ρ c y w
  rw [e]
  exact Complex.conjCLE.contDiff.contDiffAt.comp z
    ((contDiffAt_neumannCorrectionHolo hρ hy (mem_ball_iff_norm.1 hz)).restrict_scalars ℝ)

/-- `∇v` is continuous on `B(c, 2ρ)`. -/
theorem continuousOn_neumannCorrectionField (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2) :
    ContinuousOn (neumannCorrectionField ρ c y) (ball c (2 * ρ)) :=
  (contDiffOn_neumannCorrectionField hρ hy).continuousOn

end Correction

/-! ### Regularity of the screened dipole `u` on `B(c, 2ρ)` -/

section Potential

variable {lam ρ : ℝ} {c y z : ℂ}

/-- **The gradient of the screened dipole** `u` on `B(c, 2ρ)`. -/
theorem hasGradientAt_neumannPotential (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) (hz : z ∈ ball c (2 * ρ)) :
    HasGradientAt (neumannPotential lam ρ c y) (neumannField lam ρ c y z) z := by
  have hρ0 : 0 < ρ := by linarith
  rw [hasGradientAt_iff_hasFDerivAt]
  have hs₁ : HasFDerivAt (fun w : ℂ => w - c) (ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).sub_const c
  have hs₂ : HasFDerivAt (fun w : ℂ => w - y) (ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).sub_const y
  have h1 := (hasFDerivAt_discPotential hlam (z - c)).comp z hs₁
  have h2 := (hasFDerivAt_discPotential hlam (z - y)).comp z hs₂
  have h3 := (hasGradientAt_neumannCorrection hρ0 hy hz).hasFDerivAt
  refine ((h1.sub h2).add h3).congr_fderiv ?_
  simp [neumannField, map_add, map_sub]

/-- `u` is of class `C¹` on `B(c, 2ρ)`. -/
theorem contDiffOn_neumannPotential (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) :
    ContDiffOn ℝ 1 (neumannPotential lam ρ c y) (ball c (2 * ρ)) := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : ContDiff ℝ 1 fun w => discPotential lam (w - c) :=
    (contDiff_discPotential hlam).comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ 1 fun w => discPotential lam (w - y) :=
    (contDiff_discPotential hlam).comp (contDiff_id.sub contDiff_const)
  exact (h1.contDiffOn.sub h2.contDiffOn).add (contDiffOn_neumannCorrection hρ0 hy)

/-- `∇u` is continuous on `B(c, 2ρ)`. -/
theorem continuousOn_neumannField (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) :
    ContinuousOn (neumannField lam ρ c y) (ball c (2 * ρ)) := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : Continuous fun w => discField lam (w - c) :=
    (continuous_discField hlam).comp (continuous_id.sub continuous_const)
  have h2 : Continuous fun w => discField lam (w - y) :=
    (continuous_discField hlam).comp (continuous_id.sub continuous_const)
  exact (h1.continuousOn.sub h2.continuousOn).add (continuousOn_neumannCorrectionField hρ0 hy)

end Potential

/-! ### Holomorphic structure off the charges -/

section Holomorphic

variable {lam ρ : ℝ} {c y z : ℂ}

/-- `|z - c| - |y - c| ≤ |z - y|`. -/
theorem norm_sub_sub_norm_le (c y z : ℂ) : ‖z - c‖ - ‖y - c‖ ≤ ‖z - y‖ := by
  have h := norm_sub_norm_le (z - c) (y - c)
  rwa [sub_sub_sub_cancel_right] at h

/-- Outside `B(c, 3ρ/4)` both charges are point charges, and `∇u = conj H` with
`H = neumannHolo`. -/
theorem neumannField_eq_conj_neumannHolo (hρ : 4 * lam ≤ ρ) (hy : ‖y - c‖ ≤ ρ / 2)
    (hz : 3 * ρ / 4 < ‖z - c‖) :
    neumannField lam ρ c y z = conj (neumannHolo ρ c y z) := by
  have hy0 := norm_nonneg (y - c)
  have hzc : lam ≤ ‖z - c‖ := by linarith
  have hzy : lam ≤ ‖z - y‖ := by linarith [norm_sub_sub_norm_le c y z]
  rw [neumannField, neumannHolo, discField_of_le hzc, discField_of_le hzy,
    gradLogKernel_eq_neg_conj_inv, gradLogKernel_eq_neg_conj_inv, neumannCorrectionField_eq_conj,
    map_add, map_add, map_neg]
  ring

/-- `H = neumannHolo` is holomorphic on the annulus `3ρ/4 < |z - c| < 2ρ`. -/
theorem contDiffAt_neumannHolo (hy : ‖y - c‖ ≤ ρ / 2) (hz₁ : 3 * ρ / 4 < ‖z - c‖)
    (hz₂ : ‖z - c‖ < 2 * ρ) {n : WithTop ℕ∞} :
    ContDiffAt ℂ n (neumannHolo ρ c y) z := by
  have hρ : 0 < ρ := by linarith
  have hy0 := norm_nonneg (y - c)
  have hzc : z - c ≠ 0 := norm_pos_iff.1 (by linarith)
  have hzy : z - y ≠ 0 := norm_pos_iff.1 (by linarith [norm_sub_sub_norm_le c y z])
  exact (((contDiffAt_id.sub contDiffAt_const).inv hzc).neg.add
    ((contDiffAt_id.sub contDiffAt_const).inv hzy)).add
    (contDiffAt_neumannCorrectionHolo hρ hy hz₂)

/-- `H = neumannHolo` is complex differentiable on the annulus `3ρ/4 < |z - c| < 2ρ`. -/
theorem differentiableAt_neumannHolo (hy : ‖y - c‖ ≤ ρ / 2) (hz₁ : 3 * ρ / 4 < ‖z - c‖)
    (hz₂ : ‖z - c‖ < 2 * ρ) : DifferentiableAt ℂ (neumannHolo ρ c y) z :=
  (contDiffAt_neumannHolo hy hz₁ hz₂ (n := 1)).differentiableAt one_ne_zero

/-- The annulus `3ρ/4 < |z - c| < 2ρ` is open. -/
theorem isOpen_neumannAnnulus (ρ : ℝ) (c : ℂ) :
    IsOpen {z : ℂ | 3 * ρ / 4 < ‖z - c‖ ∧ ‖z - c‖ < 2 * ρ} :=
  (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)

/-- `∇u` is of class `C¹` (indeed smooth) on the annulus `3ρ/4 < |z - c| < 2ρ`. -/
theorem contDiffOn_neumannField_annulus (hρ : 4 * lam ≤ ρ) (hy : ‖y - c‖ ≤ ρ / 2) :
    ContDiffOn ℝ 1 (neumannField lam ρ c y)
      {z : ℂ | 3 * ρ / 4 < ‖z - c‖ ∧ ‖z - c‖ < 2 * ρ} := by
  intro z hz
  have h : ContDiffAt ℝ 1 (fun w => Complex.conjCLE (neumannHolo ρ c y w)) z :=
    Complex.conjCLE.contDiff.contDiffAt.comp z
      ((contDiffAt_neumannHolo hy hz.1 hz.2).restrict_scalars ℝ)
  exact h.contDiffWithinAt.congr (fun w hw => neumannField_eq_conj_neumannHolo hρ hy hw.1)
    (neumannField_eq_conj_neumannHolo hρ hy hz.1)

end Holomorphic

/-! ### The Neumann boundary condition -/

/-- The algebraic identity behind the Neumann condition: if `ρ² = ζ conj ζ` then
`ζ (-1/ζ + 1/(ζ - a) - conj a / (ρ² - ζ conj a)) = w - conj w` with `w = a / (ζ - a)`. -/
theorem mul_neumannHolo_eq_sub_conj {ρ : ℝ} {ζ a : ℂ} (hζ : ζ ≠ 0) (hζa : ζ - a ≠ 0)
    (hρ : (ρ : ℂ) ^ 2 = ζ * conj ζ) :
    ζ * (-ζ⁻¹ + (ζ - a)⁻¹ + -(conj a / ((ρ : ℂ) ^ 2 - ζ * conj a))) =
      a / (ζ - a) - conj (a / (ζ - a)) := by
  have hc : conj ζ - conj a ≠ 0 := by
    rw [← map_sub]
    exact (map_ne_zero _).2 hζa
  have hd : ζ * conj ζ - ζ * conj a ≠ 0 := by
    rw [← mul_sub]
    exact mul_ne_zero hζ hc
  rw [hρ, map_div₀, map_sub]
  field_simp
  ring

/-- **The Neumann condition** (source l. 1779–1783): `∇u · (z - c) = 0` on `∂B(c, ρ)`. -/
theorem inner_neumannField_eq_zero {lam ρ : ℝ} {c y z : ℂ} (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) (hz : ‖z - c‖ = ρ) :
    inner ℝ (neumannField lam ρ c y z) (z - c) = 0 := by
  have hρ0 : 0 < ρ := by linarith
  have h34 : 3 * ρ / 4 < ‖z - c‖ := by rw [hz]; linarith
  have hζ : z - c ≠ 0 := norm_pos_iff.1 (by linarith)
  have hζa : (z - c) - (y - c) ≠ 0 := by
    rw [sub_sub_sub_cancel_right]
    exact norm_pos_iff.1 (by linarith [norm_sub_sub_norm_le c y z])
  have hρ2 : (ρ : ℂ) ^ 2 = (z - c) * conj (z - c) := by
    rw [RCLike.mul_conj, hz]
    rfl
  have key := mul_neumannHolo_eq_sub_conj hζ hζa hρ2
  rw [sub_sub_sub_cancel_right] at key
  rw [neumannField_eq_conj_neumannHolo hρ hy h34, Complex.inner, Complex.conj_conj,
    neumannHolo, neumannCorrectionHolo]
  rw [show z - y = (z - c) - (y - c) by ring] at key ⊢
  rw [key, RCLike.sub_conj]
  simp

/-! ### The estimate (estimatesv) and the coupling bound -/

section Estimate

variable {lam ρ : ℝ} {c y z : ℂ}

/-- **Eq. (estimatesv)** (l. 1804–1806): `|∇v| ≤ 2 |y - c| / ρ²` on `B(c, 3ρ/4)`. -/
theorem norm_neumannCorrectionField_le (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2)
    (hz : z ∈ ball c (3 * ρ / 4)) :
    ‖neumannCorrectionField ρ c y z‖ ≤ 2 * ‖y - c‖ / ρ ^ 2 := by
  have hz' := mem_ball_iff_norm.1 hz
  have hprod : ‖(z - c) * conj (y - c)‖ ≤ 3 * ρ ^ 2 / 8 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖z - c‖ * ‖y - c‖ ≤ (3 * ρ / 4) * (ρ / 2) :=
          mul_le_mul hz'.le hy (norm_nonneg _) (by positivity)
      _ = 3 * ρ ^ 2 / 8 := by ring
  have hden : ρ ^ 2 / 2 ≤ ‖(ρ : ℂ) ^ 2 - (z - c) * conj (y - c)‖ := by
    have := sq_sub_norm_le_norm_sq_sub ρ c y z
    nlinarith
  rw [neumannCorrectionField_eq_conj, Complex.norm_conj, neumannCorrectionHolo, norm_neg,
    norm_div, Complex.norm_conj]
  calc ‖y - c‖ / ‖(ρ : ℂ) ^ 2 - (z - c) * conj (y - c)‖ ≤ ‖y - c‖ / (ρ ^ 2 / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden
    _ = 2 * ‖y - c‖ / ρ ^ 2 := by field_simp

/-- `v` is `2 |y - c| / ρ²`-Lipschitz on `B(c, 3ρ/4)` (mean value theorem and (estimatesv)). -/
theorem norm_neumannCorrection_sub_le (hρ : 0 < ρ) (hy : ‖y - c‖ ≤ ρ / 2) {w w' : ℂ}
    (hw : w ∈ ball c (3 * ρ / 4)) (hw' : w' ∈ ball c (3 * ρ / 4)) :
    ‖neumannCorrection ρ c y w' - neumannCorrection ρ c y w‖ ≤
      2 * ‖y - c‖ / ρ ^ 2 * ‖w' - w‖ := by
  have hsub : ball c (3 * ρ / 4) ⊆ ball c (2 * ρ) := ball_subset_ball (by linarith)
  refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun x => toDual ℝ ℂ (neumannCorrectionField ρ c y x)) (fun x hx => ?_)
    (fun x hx => ?_) (convex_ball c _) hw hw'
  · exact (hasGradientAt_neumannCorrection hρ hy (hsub hx)).hasFDerivAt.hasFDerivWithinAt
  · rw [LinearIsometryEquiv.norm_map]
    exact norm_neumannCorrectionField_le hρ hy hx

/-- Continuous functions on a closed disc are integrable for the uniform measure on the disc. -/
theorem integrable_smearedCharge_of_continuousOn {f : ℂ → ℝ} {z : ℂ} {a : ℝ}
    (hf : ContinuousOn f (closedBall z a)) : Integrable f (smearedCharge z a) := by
  rcases le_or_gt a 0 with ha | ha
  · rw [smearedCharge_of_nonpos z ha]
    exact integrable_zero_measure
  have h : IntegrableOn f (ball z a) :=
    (hf.integrableOn_compact (isCompact_closedBall z a)).mono_set ball_subset_closedBall
  rw [smearedCharge_eq]
  exact h.smul_measure (ENNReal.inv_ne_top.2 (measure_ball_pos volume z ha).ne')

/-- A closed disc of radius `λ ≤ ρ/4` about a point of `B̄(c, ρ/2)` lies in `B(c, 2ρ)`. -/
theorem closedBall_subset_ball_of_norm_sub_le_half (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ) {w₀ : ℂ}
    (hw₀ : ‖w₀ - c‖ ≤ ρ / 2) : closedBall w₀ lam ⊆ ball c (2 * ρ) := by
  intro w hw
  rw [mem_closedBall_iff_norm] at hw
  rw [mem_ball_iff_norm]
  have := norm_add_le (w - w₀) (w₀ - c)
  rw [sub_add_sub_cancel] at this
  linarith

/-- `v` is integrable for `δ_{w₀}^{(λ)}` when `|w₀ - c| ≤ ρ/2` (e.g. `w₀ = c` or `w₀ = y`). -/
theorem integrable_neumannCorrection (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) {w₀ : ℂ} (hw₀ : ‖w₀ - c‖ ≤ ρ / 2) :
    Integrable (neumannCorrection ρ c y) (smearedCharge w₀ lam) :=
  integrable_smearedCharge_of_continuousOn ((continuousOn_neumannCorrection (by linarith) hy).mono
    (closedBall_subset_ball_of_norm_sub_le_half hlam hρ hw₀))

/-- `u` is integrable for `δ_{w₀}^{(λ)}` when `|w₀ - c| ≤ ρ/2` (e.g. `w₀ = c` or `w₀ = y`). -/
theorem integrable_neumannPotential (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) {w₀ : ℂ} (hw₀ : ‖w₀ - c‖ ≤ ρ / 2) :
    Integrable (neumannPotential lam ρ c y) (smearedCharge w₀ lam) :=
  integrable_smearedCharge_of_continuousOn
    ((contDiffOn_neumannPotential hlam hρ hy).continuousOn.mono
      (closedBall_subset_ball_of_norm_sub_le_half hlam hρ hw₀))

/-- **The coupling bound** (l. 1807–1814): `|∫ v d(δ_c^{(λ)} - δ_y^{(λ)})| ≤ 2 |y - c|² / ρ²`. -/
theorem abs_integral_neumannCorrection_sub_le (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) :
    |(∫ w, neumannCorrection ρ c y w ∂smearedCharge c lam) -
        ∫ w, neumannCorrection ρ c y w ∂smearedCharge y lam| ≤ 2 * ‖y - c‖ ^ 2 / ρ ^ 2 := by
  have hρ0 : 0 < ρ := by linarith
  have hc : ‖c - c‖ ≤ ρ / 2 := by rw [sub_self, norm_zero]; linarith
  have hmap : (smearedCharge c lam).map (· + (y - c)) = smearedCharge y lam := by
    rw [map_add_right_smearedCharge, add_sub_cancel]
  have hshift : ∫ w, neumannCorrection ρ c y w ∂smearedCharge y lam =
      ∫ w, neumannCorrection ρ c y (w + (y - c)) ∂smearedCharge c lam := by
    rw [← hmap]
    exact (measurableEmbedding_addRight (y - c)).integral_map _
  have hint₁ := integrable_neumannCorrection hlam hρ hy hc
  have hint₂ : Integrable (fun w => neumannCorrection ρ c y (w + (y - c)))
      (smearedCharge c lam) := by
    have h := integrable_neumannCorrection hlam hρ hy hy (lam := lam)
    rw [← hmap] at h
    exact ((measurableEmbedding_addRight (y - c)).integrable_map_iff).1 h
  have := isProbabilityMeasure_smearedCharge c hlam
  rw [hshift, ← integral_sub hint₁ hint₂, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := 2 * ‖y - c‖ / ρ ^ 2 * ‖y - c‖) ?_).trans ?_
  · filter_upwards [ae_mem_ball_smearedCharge c lam] with w hw
    rw [mem_ball_iff_norm] at hw
    have hw₁ : w ∈ ball c (3 * ρ / 4) := mem_ball_iff_norm.2 (by linarith)
    have hw₂ : w + (y - c) ∈ ball c (3 * ρ / 4) := by
      rw [mem_ball_iff_norm]
      have := norm_add_le (w - c) (y - c)
      rw [show w + (y - c) - c = w - c + (y - c) by ring]
      linarith
    rw [norm_sub_rev]
    have h := norm_neumannCorrection_sub_le hρ0 hy hw₁ hw₂
    rwa [add_sub_cancel_left] at h
  · rw [probReal_univ, mul_one]
    exact le_of_eq (by ring)

end Estimate

/-! ### The pair energy of the screened dipole -/

section Energy

variable {lam ρ : ℝ} {c y : ℂ}

/-- `∫ u dδ_{w₀}^{(λ)}` splits into the two disc potentials and the correction. -/
theorem integral_neumannPotential_eq (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) {w₀ : ℂ} (hw₀ : ‖w₀ - c‖ ≤ ρ / 2) :
    ∫ w, neumannPotential lam ρ c y w ∂smearedCharge w₀ lam =
      (∫ w, discPotential lam (w - c) ∂smearedCharge w₀ lam) -
        (∫ w, discPotential lam (w - y) ∂smearedCharge w₀ lam) +
        ∫ w, neumannCorrection ρ c y w ∂smearedCharge w₀ lam := by
  have i₁ := integrable_smearedCharge_of_continuous
    ((contDiff_discPotential hlam).continuous.comp (continuous_id.sub continuous_const)) w₀ lam
    (f := fun w => discPotential lam (w - c))
  have i₂ := integrable_smearedCharge_of_continuous
    ((contDiff_discPotential hlam).continuous.comp (continuous_id.sub continuous_const)) w₀ lam
    (f := fun w => discPotential lam (w - y))
  have i₃ := integrable_neumannCorrection hlam hρ hy hw₀
  have i₁₂ : Integrable (fun w => discPotential lam (w - c) - discPotential lam (w - y))
      (smearedCharge w₀ lam) := i₁.sub i₂
  rw [← integral_sub i₁ i₂, ← integral_add i₁₂ i₃]
  rfl

/-- `∫ (g * δ_w^{(λ)}) dδ_z^{(λ)} = g_λ(w - z)`. -/
theorem integral_discPotential_smearedCharge (hlam : 0 < lam) (z w : ℂ) :
    ∫ x, discPotential lam (x - w) ∂smearedCharge z lam = smearedKernel lam (w - z) := by
  rw [← pairInteraction_eq_integral_discPotential z w hlam, pairInteraction_eq_smearedKernel]

/-- **The pair energy of the screened dipole** (l. 1807–1814):
`∫ u d(δ_c^{(λ)} - δ_y^{(λ)}) = 2 (g(λ) + κ) - 2 g_λ(y - c) + ∫ v d(δ_c^{(λ)} - δ_y^{(λ)})`. -/
theorem integral_neumannPotential_sub (hlam : 0 < lam) (hρ : 4 * lam ≤ ρ)
    (hy : ‖y - c‖ ≤ ρ / 2) :
    (∫ w, neumannPotential lam ρ c y w ∂smearedCharge c lam) -
        (∫ w, neumannPotential lam ρ c y w ∂smearedCharge y lam) =
      2 * (logKernel (lam : ℂ) + kappa) - 2 * smearedKernel lam (y - c) +
        ((∫ w, neumannCorrection ρ c y w ∂smearedCharge c lam) -
          ∫ w, neumannCorrection ρ c y w ∂smearedCharge y lam) := by
  have hc : ‖c - c‖ ≤ ρ / 2 := by rw [sub_self, norm_zero]; linarith
  rw [integral_neumannPotential_eq hlam hρ hy hc, integral_neumannPotential_eq hlam hρ hy hy,
    integral_discPotential_smearedCharge hlam, integral_discPotential_smearedCharge hlam,
    integral_discPotential_smearedCharge hlam, integral_discPotential_smearedCharge hlam,
    sub_self, sub_self, smearedKernel_zero hlam, ← neg_sub y c, smearedKernel_neg]
  ring

end Energy

end TwoComponentCoulomb

end
