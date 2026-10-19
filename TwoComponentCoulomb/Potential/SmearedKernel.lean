/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Kappa
public import TwoComponentCoulomb.Frozen.LogKernel
public import TwoComponentCoulomb.Frozen.SmearedCharge
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.Potential.DiscPotentialMeasure

/-!
# Properties of the smeared kernel `g_λ`

The smeared kernel `g_λ = smearedKernel λ` is the pair interaction of two uniform discs of radius
`λ` (source eq. (eq:defgeta), l. 162–163) and `κ = kappa` is `g_1(0)` (eq. (defkappa), l. 149–150).
Here `g = logKernel`. The proofs combine Newton's theorem for the disc potential
(`integral_logKernel_sub_smearedCharge`) with Fubini (`smearedKernel_eq_integral_potential`).

* `smearedKernel_eq_logKernel` : `g_λ(z) = g(z)` for `|z| ≥ 2λ`.
* `kappa_eq` : `κ = 1/4`, and `smearedKernel_zero` : `g_λ(0) = g(λ) + κ` (eq. (geta0)).
* `smearedKernel_eq_logKernel_add` : `g_λ(z) = g(λ) + g_1(z / λ)` (eq. (approxgeta), first part).
* `continuous_smearedKernel` : `g_λ` is continuous.
* `exists_abs_smearedKernel_sub_logKernel_le` : `|g_λ(z) - g(max(|z|, λ))| ≤ C`, uniformly in
  `λ > 0` (eq. (approxgeta), second part), with the one-sided corollaries
  `exists_smearedKernel_le` and `exists_smearedKernel_ge`.
* `abs_smearedKernel_one_sub_kappa_le` and `exists_abs_smearedKernel_one_sub_kappa_le` :
  `|g_1(z) - κ| ≤ |z|²` (eq. (idg1)).

For (idg1) the potential `U` of the unit disc is split as `U(u) = (1 - |u|²) / 2 + ρ(max(1, |u|))`
with `ρ(t) = (t² - 1) / 2 - log t`. The quadratic part integrates exactly, to
`1/4 - |z|² / 2` against `δ_0^{(1)}` (`smearedKernel_one_eq`), while
`0 ≤ ρ(t) ≤ (3/2) (t - 1)²` (`rho_nonneg`, `rho_le`) controls the remainder by `(3/2) |z|²`
since `max(1, |x - z|) - 1 ≤ |z|` for `|x| < 1`.
-/

public section

open MeasureTheory Metric Set

namespace TwoComponentCoulomb

/-! ### `g_λ(z) = g(z)` for `|z| ≥ 2λ` -/

/-- `g_λ(z) = g(z)` for `|z| ≥ 2λ` (source l. 165, by Newton's theorem applied twice). -/
theorem smearedKernel_eq_logKernel {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 2 * lam ≤ ‖z‖) :
    smearedKernel lam z = logKernel z := by
  rw [smearedKernel_eq_integral_integral]
  have h1 : ∀ᵐ x ∂smearedCharge 0 lam,
      ∫ y, logKernel (x - y) ∂smearedCharge z lam = logKernel (x - z) := by
    filter_upwards [ae_mem_ball_smearedCharge 0 lam] with x hx
    refine integral_logKernel_sub_smearedCharge_of_le x z hlam ?_
    have h2 : ‖x‖ < lam := by simpa using hx
    have h3 := norm_sub_norm_le z x
    rw [norm_sub_rev x z]
    linarith
  rw [integral_congr_ae h1, integral_smearedCharge _ 0 hlam]
  have h4 := setIntegral_log_norm_sub_ball_of_le z 0 hlam
    (by simpa using (by linarith : lam ≤ ‖z‖))
  simp only [logKernel, integral_neg, smul_eq_mul]
  simp_rw [norm_sub_rev _ z]
  rw [h4]
  field_simp
  simp

/-! ### Scaling -/

/-- Scaling (source eq. (approxgeta), first part): `g_λ(z) = g(λ) + g_1(z / λ)`. -/
theorem smearedKernel_eq_logKernel_add {lam : ℝ} (hlam : 0 < lam) (z : ℂ) :
    smearedKernel lam z = logKernel (lam : ℂ) + smearedKernel 1 (z / lam) := by
  have hc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam.ne'
  have e0 : smearedCharge 0 lam = (smearedCharge 0 1).map (fun x => (lam : ℂ) * x) := by
    rw [map_ofReal_mul_smearedCharge 0 1 hlam]; simp
  have e1 : smearedCharge z lam = (smearedCharge (z / lam) 1).map (fun x => (lam : ℂ) * x) := by
    rw [map_ofReal_mul_smearedCharge _ 1 hlam, mul_one, mul_div_cancel₀ _ hc]
  have := isProbabilityMeasure_smearedCharge 0 one_pos
  have := isProbabilityMeasure_smearedCharge (z / lam) one_pos
  unfold smearedKernel
  rw [e0, e1, integral_prod_map_embedding (measurableEmbedding_mulLeft₀ hc)]
  have hae : ∀ᵐ p ∂(smearedCharge 0 1).prod (smearedCharge (z / lam) 1),
      logKernel ((lam : ℂ) * p.1 - (lam : ℂ) * p.2) =
        logKernel (lam : ℂ) + logKernel (p.1 - p.2) := by
    filter_upwards [ae_prod_smearedCharge_ne 0 (z / lam) 1 1] with p hp
    rw [← mul_sub, logKernel_ofReal_mul hlam (sub_ne_zero.2 hp)]
  rw [integral_congr_ae hae, integral_add (integrable_const _)
    (integrable_logKernel_prod_smearedCharge 0 (z / lam) 1 1)]
  simp

/-! ### Continuity -/

/-- `g_λ` is continuous for `λ > 0`. -/
theorem continuous_smearedKernel {lam : ℝ} (hlam : 0 < lam) : Continuous (smearedKernel lam) := by
  have hP := continuous_closedFormDiscPotential hlam
  have hfun : smearedKernel lam = fun z => ∫ x,
      (-Real.log (max lam ‖x - z‖) + (1 - min ‖x - z‖ lam ^ 2 / lam ^ 2) / 2)
        ∂smearedCharge 0 lam := funext (smearedKernel_eq_integral_potential hlam)
  rw [hfun]
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (lam + ‖z₀‖ + 1)).exists_bound_of_continuousOn
    hP.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
  · exact Filter.Eventually.of_forall fun z =>
      (hP.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    filter_upwards [ae_mem_ball_smearedCharge 0 lam] with x hx
    refine hB _ ?_
    rw [mem_closedBall_zero_iff]
    have h1 : ‖x‖ < lam := by simpa using hx
    have h2 : ‖z - z₀‖ < 1 := by rwa [mem_ball_iff_norm] at hz
    calc ‖x - z‖ = ‖x - z₀ - (z - z₀)‖ := by congr 1; ring
      _ ≤ ‖x - z₀‖ + ‖z - z₀‖ := norm_sub_le _ _
      _ ≤ ‖x‖ + ‖z₀‖ + ‖z - z₀‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ lam + ‖z₀‖ + 1 := by linarith
  · exact Filter.Eventually.of_forall fun x =>
      (hP.comp (continuous_const.sub continuous_id)).continuousAt

/-! ### Uniform comparison with `g(max(|z|, λ))` -/

/-- Source eq. (approxgeta), second part: `|g_λ(z) - g(max(|z|, λ))| ≤ C` with `C` independent of
`λ > 0` and `z`. -/
theorem exists_abs_smearedKernel_sub_logKernel_le :
    ∃ C : ℝ, ∀ lam : ℝ, 0 < lam → ∀ z : ℂ,
      |smearedKernel lam z - logKernel ((max ‖z‖ lam : ℝ) : ℂ)| ≤ C := by
  set h : ℂ → ℝ := fun w => smearedKernel 1 w + Real.log (max ‖w‖ 1) with hh
  have hcont : Continuous h :=
    (continuous_smearedKernel one_pos).add
      (Continuous.log (continuous_norm.max continuous_const)
        fun w => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne')
  have hsupp : HasCompactSupport h := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) fun w hw => ?_
    have hw2 : 2 ≤ ‖w‖ := by
      rw [mem_closedBall_zero_iff, not_le] at hw
      exact hw.le
    have h1 : smearedKernel 1 w = logKernel w :=
      smearedKernel_eq_logKernel one_pos (by linarith)
    simp only [hh, h1, logKernel, max_eq_left (by linarith : 1 ≤ ‖w‖)]
    ring
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  refine ⟨C, fun lam hlam z => ?_⟩
  have hmax : max ‖z‖ lam = lam * max ‖z / (lam : ℂ)‖ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hlam.le, mul_max_of_nonneg _ _ hlam.le,
      mul_div_cancel₀ _ hlam.ne', mul_one]
  have hpos : 0 < max ‖z / (lam : ℂ)‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have key : smearedKernel lam z - logKernel ((max ‖z‖ lam : ℝ) : ℂ) = h (z / lam) := by
    rw [smearedKernel_eq_logKernel_add hlam, logKernel_ofReal hlam,
      logKernel_ofReal (lt_of_lt_of_le hlam (le_max_right _ _)), hmax,
      Real.log_mul hlam.ne' hpos.ne']
    simp only [hh]
    ring
  rw [key]
  simpa [Real.norm_eq_abs] using hC (z / lam)

/-- Uniform upper bound: `g_λ(z) ≤ -log λ + C`. -/
theorem exists_smearedKernel_le :
    ∃ C : ℝ, ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, smearedKernel lam z ≤ -Real.log lam + C := by
  obtain ⟨C, hC⟩ := exists_abs_smearedKernel_sub_logKernel_le
  refine ⟨C, fun lam hlam z => ?_⟩
  have h1 := (abs_le.1 (hC lam hlam z)).2
  rw [logKernel_ofReal (lt_of_lt_of_le hlam (le_max_right _ _))] at h1
  have h2 : Real.log lam ≤ Real.log (max ‖z‖ lam) := Real.log_le_log hlam (le_max_right _ _)
  linarith

/-- Uniform lower bound: `g_λ(z) ≥ -log (max(|z|, λ)) - C`. -/
theorem exists_smearedKernel_ge :
    ∃ C : ℝ, ∀ lam : ℝ, 0 < lam → ∀ z : ℂ,
      -Real.log (max ‖z‖ lam) - C ≤ smearedKernel lam z := by
  obtain ⟨C, hC⟩ := exists_abs_smearedKernel_sub_logKernel_le
  refine ⟨C, fun lam hlam z => ?_⟩
  have h1 := (abs_le.1 (hC lam hlam z)).1
  rw [logKernel_ofReal (lt_of_lt_of_le hlam (le_max_right _ _))] at h1
  linarith

/-! ### Moments of the unit disc -/

/-- The second moment of the uniform measure on the unit disc is `1/2`. -/
theorem integral_norm_sq_smearedCharge :
    ∫ x, ‖x‖ ^ 2 ∂smearedCharge 0 1 = 1 / 2 := by
  rw [integral_smearedCharge _ 0 one_pos]
  have hF : Measurable fun x : ℂ => ‖x‖ ^ 2 := by fun_prop
  have hint : IntegrableOn (fun x : ℂ => ‖x‖ ^ 2) (ball (0 : ℂ) 1) :=
    ((by fun_prop : Continuous fun x : ℂ => ‖x‖ ^ 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall
  rw [setIntegral_ball_zero_eq_polar hF hint]
  have h1 : ∀ r ∈ Ioo (0 : ℝ) 1,
      r * ∫ θ in Ioo (-Real.pi) Real.pi, ‖circleMap 0 r θ‖ ^ 2 = 2 * Real.pi * r ^ 3 := by
    intro r hr
    have : ∀ θ, ‖circleMap 0 r θ‖ ^ 2 = r ^ 2 := fun θ => by
      rw [norm_circleMap_zero, abs_of_pos hr.1]
    simp_rw [this]
    rw [setIntegral_const, smul_eq_mul]
    simp only [Real.volume_real_Ioo, sub_neg_eq_add]
    rw [max_eq_left (by positivity : 0 ≤ Real.pi + Real.pi)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo h1, integral_Ioo_eq_intervalIntegral zero_le_one,
    intervalIntegral.integral_const_mul, integral_pow]
  simp only [smul_eq_mul]
  field_simp
  norm_num

/-- `∫ |x - z|² dδ_0^{(1)}(x) = 1/2 + |z|²`: the cross term vanishes by the symmetry `x ↦ -x`. -/
theorem integral_norm_sub_sq_smearedCharge (z : ℂ) :
    ∫ x, ‖x - z‖ ^ 2 ∂smearedCharge 0 1 = 1 / 2 + ‖z‖ ^ 2 := by
  have hI : ∫ x, inner ℝ x z ∂smearedCharge 0 1 = 0 := by
    have h := integral_comp_neg_smearedCharge (fun x : ℂ => inner ℝ x z) 1
    simp only [inner_neg_left, integral_neg] at h
    linarith
  have h1 : Integrable (fun x : ℂ => ‖x‖ ^ 2) (smearedCharge 0 1) :=
    integrable_smearedCharge_of_continuous (by fun_prop) 0 1
  have h2 : Integrable (fun x : ℂ => 2 * inner ℝ x z) (smearedCharge 0 1) :=
    (integrable_smearedCharge_of_continuous (by fun_prop) 0 1).const_mul 2
  have h3 : Integrable (fun x : ℂ => ‖x‖ ^ 2 - 2 * inner ℝ x z) (smearedCharge 0 1) := h1.sub h2
  have hprob := isProbabilityMeasure_smearedCharge 0 one_pos
  simp_rw [norm_sub_sq_real]
  rw [integral_add h3 (integrable_const _), integral_sub h1 h2, integral_const_mul, hI,
    integral_norm_sq_smearedCharge]
  simp

/-! ### The function `ρ(t) = (t² - 1) / 2 - log t` for `t ≥ 1` -/

theorem rho_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ (t ^ 2 - 1) / 2 - Real.log t := by
  have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < t)
  nlinarith [sq_nonneg (t - 1)]

theorem rho_le {t : ℝ} (ht : 1 ≤ t) : (t ^ 2 - 1) / 2 - Real.log t ≤ 3 / 2 * (t - 1) ^ 2 := by
  have h0 : 0 < t := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos h0
  have h2 : 3 / 2 * (t - 1) ^ 2 - ((t ^ 2 - 1) / 2 - (1 - t⁻¹)) = (t - 1) ^ 3 / t := by
    field_simp
    ring
  have h3 : 0 ≤ (t - 1) ^ 3 / t := div_nonneg (pow_nonneg (sub_nonneg.2 ht) 3) h0.le
  linarith

/-! ### `κ = 1/4` and the expansion of `g_1` near `0` -/

theorem continuous_rho_max (z : ℂ) :
    Continuous fun x : ℂ => ((max 1 ‖x - z‖) ^ 2 - 1) / 2 - Real.log (max 1 ‖x - z‖) := by
  have : Continuous fun x : ℂ => Real.log (max 1 ‖x - z‖) :=
    Continuous.log
      (continuous_const.max (continuous_norm.comp (continuous_id.sub continuous_const)))
      fun x => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  fun_prop

/-- Exact expansion of `g_1`: `g_1(z) = 1/4 - |z|² / 2 + ∫ ρ(max(1, |x - z|)) dδ_0^{(1)}(x)`. -/
theorem smearedKernel_one_eq (z : ℂ) :
    smearedKernel 1 z = 1 / 4 - ‖z‖ ^ 2 / 2 +
      ∫ x, (((max 1 ‖x - z‖) ^ 2 - 1) / 2 - Real.log (max 1 ‖x - z‖)) ∂smearedCharge 0 1 := by
  have hprob := isProbabilityMeasure_smearedCharge 0 one_pos
  have hfun : ∀ x : ℂ, -Real.log (max 1 ‖x - z‖) + (1 - min ‖x - z‖ 1 ^ 2 / 1 ^ 2) / 2 =
      (1 - ‖x - z‖ ^ 2) / 2 + (((max 1 ‖x - z‖) ^ 2 - 1) / 2 - Real.log (max 1 ‖x - z‖)) := by
    intro x
    rcases le_total ‖x - z‖ 1 with h | h
    · rw [max_eq_left h, min_eq_left h]
      simp
    · rw [max_eq_right h, min_eq_right h]
      ring
  have hc1 : Continuous fun x : ℂ => (1 - ‖x - z‖ ^ 2) / 2 := by fun_prop
  rw [smearedKernel_eq_integral_potential one_pos z]
  simp_rw [hfun]
  rw [integral_add (integrable_smearedCharge_of_continuous hc1 0 1)
    (integrable_smearedCharge_of_continuous (continuous_rho_max z) 0 1)]
  congr 1
  have h1 : Integrable (fun x : ℂ => ‖x - z‖ ^ 2) (smearedCharge 0 1) :=
    integrable_smearedCharge_of_continuous (by fun_prop) 0 1
  rw [integral_div, integral_sub (integrable_const _) h1, integral_norm_sub_sq_smearedCharge]
  simp
  ring

theorem integral_rho_nonneg (z : ℂ) :
    0 ≤ ∫ x, (((max 1 ‖x - z‖) ^ 2 - 1) / 2 - Real.log (max 1 ‖x - z‖)) ∂smearedCharge 0 1 :=
  integral_nonneg fun _ => rho_nonneg (le_max_left _ _)

theorem integral_rho_le (z : ℂ) :
    ∫ x, (((max 1 ‖x - z‖) ^ 2 - 1) / 2 - Real.log (max 1 ‖x - z‖)) ∂smearedCharge 0 1 ≤
      3 / 2 * ‖z‖ ^ 2 := by
  have hprob := isProbabilityMeasure_smearedCharge 0 one_pos
  calc ∫ x, (((max 1 ‖x - z‖) ^ 2 - 1) / 2 - Real.log (max 1 ‖x - z‖)) ∂smearedCharge 0 1
      ≤ ∫ _, 3 / 2 * ‖z‖ ^ 2 ∂smearedCharge 0 1 := by
        refine integral_mono_ae (integrable_smearedCharge_of_continuous (continuous_rho_max z) 0 1)
          (integrable_const _) ?_
        filter_upwards [ae_mem_ball_smearedCharge 0 1] with x hx
        have hx1 : ‖x‖ < 1 := by simpa using hx
        have h1 : max 1 ‖x - z‖ - 1 ≤ ‖z‖ := by
          have := norm_sub_le x z
          rw [sub_le_iff_le_add]
          exact max_le (by linarith [norm_nonneg z]) (by linarith)
        refine (rho_le (le_max_left _ _)).trans ?_
        have h2 : 0 ≤ max 1 ‖x - z‖ - 1 := sub_nonneg.2 (le_max_left _ _)
        gcongr
    _ = 3 / 2 * ‖z‖ ^ 2 := by simp

theorem kappa_eq_smearedKernel_one : kappa = smearedKernel 1 0 := rfl

/-- `κ = 1/4`. -/
theorem kappa_eq : kappa = 1 / 4 := by
  have h := smearedKernel_one_eq 0
  have h1 := integral_rho_nonneg 0
  have h2 := integral_rho_le 0
  simp only [norm_zero, sub_zero] at h h1 h2
  rw [kappa_eq_smearedKernel_one, h]
  norm_num at h2 ⊢
  linarith

/-- Source eq. (geta0): `g_λ(0) = g(λ) + κ`. -/
theorem smearedKernel_zero {lam : ℝ} (hlam : 0 < lam) :
    smearedKernel lam 0 = logKernel (lam : ℂ) + kappa := by
  rw [smearedKernel_eq_logKernel_add hlam, zero_div, kappa_eq_smearedKernel_one]

/-- Source eq. (idg1), in a form valid for every `z`: `|g_1(z) - κ| ≤ |z|²`. -/
theorem abs_smearedKernel_one_sub_kappa_le (z : ℂ) :
    |smearedKernel 1 z - kappa| ≤ ‖z‖ ^ 2 := by
  have h := smearedKernel_one_eq z
  have h1 := integral_rho_nonneg z
  have h2 := integral_rho_le z
  rw [kappa_eq, h, abs_le]
  constructor <;> nlinarith [sq_nonneg ‖z‖]

/-- Source eq. (idg1): `|g_1(z) - κ| ≤ C |z|²` for `|z| ≤ 1`. -/
theorem exists_abs_smearedKernel_one_sub_kappa_le :
    ∃ C : ℝ, ∀ z : ℂ, ‖z‖ ≤ 1 → |smearedKernel 1 z - kappa| ≤ C * ‖z‖ ^ 2 :=
  ⟨1, fun z _ => by simpa using abs_smearedKernel_one_sub_kappa_le z⟩

end TwoComponentCoulomb

end
