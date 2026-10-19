/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Energy
public import TwoComponentCoulomb.Potential.ElectricDecay
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedCharge

/-!
# The electric energy of a neutral configuration of disc charges

For a neutral configuration (`Σᵢ dᵢ = 0`) of disc charges with positive radii the Dirichlet energy
of the electric potential `h_α` is finite and (source l. 198-200, 503-509, 1973)

`(1 / 2π) ∫ |∇h_α|² = Σᵢⱼ dᵢ dⱼ P_{ij}`,   `P_{ij} = ∬ g(x - y) dδ_{zᵢ}^{(αᵢ)}(x) dδ_{zⱼ}^{(αⱼ)}(y)`.

* `integral_norm_sq_electricField` : the energy identity. It is obtained from the Green identity
  `integral_fderiv_apply_electricField` applied to `ξ = χ_R h_α` with a smooth cutoff `χ_R`, and
  letting `R → ∞` using the decay `exists_decay_electric_nonneg` (the cross term is `O(R⁻²)`).
* `sum_pairInteraction_nonneg` : positivity of the pair energy of a neutral configuration.
* `abs_sum_mul_integral_smearedCharge_le` : the fluctuation bound of Theorem 2, Step 1,
  `|Σᵢ dᵢ ∫ ξ dδ_{zᵢ}^{(αᵢ)}| ≤ (2π)⁻¹ ‖∇ξ‖_{L²} ‖∇h_α‖_{L²}`.
* `energy_eq_integral_norm_sq_electricField` : eq. (eq:rewrF),
  `F_λ = (1 / 4π) ∫ |∇h_λ|² - N (g(λ) + κ)`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology

namespace TwoComponentCoulomb

/-! ### Cutoff functions -/

/-- A family of smooth cutoffs `χ_R` (`R > 0`): equal to `1` on `B(0, R)`, supported in `B(0, 2R)`,
with `|∇χ_R| ≤ K / R`. -/
theorem exists_cutoff_family :
    ∃ (K : ℝ) (χ : ℝ → ℂ → ℝ), 0 ≤ K ∧ ∀ R : ℝ, 0 < R →
      ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧ (∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, ‖x‖ ≤ R → χ R x = 1) ∧ (∀ x, ‖x‖ < R → fderiv ℝ (χ R) x = 0) ∧
      (∀ x, 2 * R < ‖x‖ → fderiv ℝ (χ R) x = 0) ∧
      (∀ x v, |fderiv ℝ (χ R) x v| ≤ K / R * ‖v‖) := by
  let f : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hf : ContDiff ℝ 1 (f : ℂ → ℝ) := f.contDiff
  obtain ⟨K, hK⟩ := (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (f.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨max K 0, fun R x => f (R⁻¹ • x), le_max_right _ _, fun R hR => ?_⟩
  have hsm : ContDiff ℝ 1 (fun x : ℂ => R⁻¹ • x) := contDiff_id.const_smul R⁻¹
  have hnorm : ∀ x : ℂ, ‖R⁻¹ • x‖ = ‖x‖ / R := fun x => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), inv_mul_eq_div]
  have hzero : ∀ x : ℂ, 2 * R < ‖x‖ → f (R⁻¹ • x) = 0 := fun x hx => by
    refine f.zero_of_le_dist ?_
    rw [dist_zero_right, hnorm]
    show 2 ≤ ‖x‖ / R
    rw [le_div_iff₀ hR]
    linarith
  have hone : ∀ x : ℂ, ‖x‖ ≤ R → f (R⁻¹ • x) = 1 := fun x hx => by
    refine f.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right, hnorm]
    show ‖x‖ / R ≤ 1
    rw [div_le_one hR]
    exact hx
  refine ⟨hf.comp hsm, ?_, fun x => ⟨f.nonneg, f.le_one⟩, hone, fun x hx => ?_, fun x hx => ?_,
    fun x v => ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * R)) fun x hx => ?_
    simp only [mem_closedBall, dist_zero_right, not_le] at hx
    exact hzero x hx
  · have : (fun y : ℂ => f (R⁻¹ • y)) =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds (show x ∈ ball (0 : ℂ) R by simpa using hx)] with y hy
      exact hone y (by simpa using hy.out.le)
    rw [this.fderiv_eq]
    simp
  · have : (fun y : ℂ => f (R⁻¹ • y)) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {y : ℂ | 2 * R < ‖y‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hzero y hy
    rw [this.fderiv_eq]
    simp
  · have h1 : HasFDerivAt (fun y : ℂ => f (R⁻¹ • y))
        ((fderiv ℝ f (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ ℂ)) x :=
      (hf.differentiable one_ne_zero (R⁻¹ • x)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul R⁻¹)
    rw [h1.fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul,
      smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 hR)]
    have h2 : |fderiv ℝ f (R⁻¹ • x) v| ≤ max K 0 * ‖v‖ := by
      calc |fderiv ℝ f (R⁻¹ • x) v| = ‖fderiv ℝ f (R⁻¹ • x) v‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ f (R⁻¹ • x)‖ * ‖v‖ := (fderiv ℝ f _).le_opNorm v
        _ ≤ max K 0 * ‖v‖ :=
          mul_le_mul_of_nonneg_right ((hK _).trans (le_max_left _ _)) (norm_nonneg _)
    calc R⁻¹ * |fderiv ℝ f (R⁻¹ • x) v| ≤ R⁻¹ * (max K 0 * ‖v‖) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hR.le)
      _ = max K 0 / R * ‖v‖ := by ring

section Energy

variable {ι : Type*} [Fintype ι] {d : ι → ℝ} {z : ι → ℂ} {α : ι → ℝ}

/-! ### The Green identity with a cutoff -/

/-- The mean of the electric potential over the `i`-th disc is `Σⱼ dⱼ P_{ij}`. -/
theorem integral_electricPotential_smearedCharge (hα : ∀ i, 0 < α i) (i : ι) :
    ∫ y, electricPotential d z α y ∂smearedCharge (z i) (α i) =
      ∑ j, d j * pairInteraction (z i) (z j) (α i) (α j) := by
  unfold electricPotential
  have hint : ∀ j, Integrable (fun y : ℂ => d j * discPotential (α j) (y - z j))
      (smearedCharge (z i) (α i)) := fun j =>
    (integrable_smearedCharge_of_continuous
      ((contDiff_discPotential (hα j)).continuous.comp (continuous_id.sub continuous_const))
      _ _).const_mul (d j)
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, pairInteraction_eq_integral_discPotential (z i) (z j) (hα j)]

/-- **The Green identity for `ξ = χ h_α`**: if `χ` is a `C¹` compactly supported function equal to
`1` on a ball `B(0, R)` containing all the discs, then
`∫ χ |∇h_α|² + ∫ h_α ∇χ · ∇h_α = 2π Σᵢⱼ dᵢ dⱼ P_{ij}`. -/
theorem integral_cutoff_identity (hα : ∀ i, 0 < α i) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) {R : ℝ} (hχ1 : ∀ x, ‖x‖ ≤ R → χ x = 1)
    (hR : ∀ i, ‖z i‖ + α i ≤ R) :
    (∫ x, χ x * ‖electricField d z α x‖ ^ 2) +
        ∫ x, electricPotential d z α x * fderiv ℝ χ x (electricField d z α x) =
      2 * Real.pi * ∑ i, ∑ j, d i * d j * pairInteraction (z i) (z j) (α i) (α j) := by
  set h := electricPotential d z α with hh
  set E := electricField d z α with hE
  have hhc : ContDiff ℝ 1 h := contDiff_electricPotential hα
  have hξ : ContDiff ℝ 1 (fun x => χ x * h x) := hχ.mul hhc
  have hcξ : HasCompactSupport (fun x => χ x * h x) := hχc.mul_right
  have G := integral_fderiv_apply_electricField (d := d) (z := z) hξ hcξ hα
  have hpt : ∀ x, fderiv ℝ (fun y => χ y * h y) x (E x) =
      χ x * ‖E x‖ ^ 2 + h x * fderiv ℝ χ x (E x) := fun x => by
    rw [fderiv_fun_mul (hχ.differentiable one_ne_zero x) (hhc.differentiable one_ne_zero x)]
    simp [hh, hE, fderiv_electricPotential_apply hα]
  have hI1 : Integrable (fun x => χ x * ‖E x‖ ^ 2) :=
    Continuous.integrable_of_hasCompactSupport
      (hχ.continuous.mul ((continuous_electricField hα).norm.pow 2)) hχc.mul_right
  have hI : Integrable (fun x => fderiv ℝ (fun y => χ y * h y) x (E x)) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((hξ.continuous_fderiv one_ne_zero).clm_apply (continuous_electricField hα)) ?_
    refine (hcξ.fderiv (𝕜 := ℝ)).mono' fun x hx => subset_tsupport _ ?_
    intro h0
    exact hx (by simp [h0])
  have hI2 : Integrable (fun x => h x * fderiv ℝ χ x (E x)) := by
    refine (hI.sub hI1).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, hpt]
    ring
  rw [← hE] at G
  simp_rw [hpt] at G
  rw [← integral_add hI1 hI2, G]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hae : ∀ᵐ x ∂smearedCharge (z i) (α i), χ x * h x = h x := by
    filter_upwards [ae_mem_ball_smearedCharge (z i) (α i)] with x hx
    have hx' : ‖x‖ ≤ R := by
      have h1 : ‖x - z i‖ < α i := by simpa [dist_eq_norm] using hx
      have h2 : ‖x‖ ≤ ‖x - z i‖ + ‖z i‖ := by
        simpa using norm_add_le (x - z i) (z i)
      linarith [hR i]
    rw [hχ1 x hx', one_mul]
  rw [integral_congr_ae hae, integral_electricPotential_smearedCharge hα i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The energy identity -/

/-- The cross term `∫ h_α ∇χ_R · ∇h_α` is `O(R⁻²)`. -/
theorem tendsto_cross_term (hα : ∀ i, 0 < α i) (hn : ∑ i, d i = 0) {K : ℝ} (hK : 0 ≤ K)
    {χ : ℝ → ℂ → ℝ} (hχ : ∀ R : ℝ, 0 < R →
      (∀ x, ‖x‖ < R → fderiv ℝ (χ R) x = 0) ∧ (∀ x, 2 * R < ‖x‖ → fderiv ℝ (χ R) x = 0) ∧
      (∀ x v, |fderiv ℝ (χ R) x v| ≤ K / R * ‖v‖)) :
    Tendsto (fun R : ℝ => ∫ x, electricPotential d z α x *
      fderiv ℝ (χ R) x (electricField d z α x)) atTop (𝓝 0) := by
  obtain ⟨R₀, C, hR₀, hC, hdec⟩ := exists_decay_electric_nonneg (d := d) (z := z) hα hn
  have hbound : ∀ᶠ R : ℝ in atTop, ‖∫ x, electricPotential d z α x *
      fderiv ℝ (χ R) x (electricField d z α x)‖ ≤ 9 * Real.pi * (K * C ^ 2) / R ^ 2 := by
    filter_upwards [eventually_ge_atTop R₀] with R hR
    have hR0 : 0 < R := lt_of_lt_of_le hR₀ hR
    obtain ⟨h5, h6, h7⟩ := hχ R hR0
    set M : ℝ := K * C ^ 2 / R ^ 4 with hM
    have hM0 : 0 ≤ M := by positivity
    have hpt : ∀ x, ‖electricPotential d z α x * fderiv ℝ (χ R) x (electricField d z α x)‖ ≤
        (ball (0 : ℂ) (3 * R)).indicator (fun _ => M) x := by
      intro x
      have hind : 0 ≤ (ball (0 : ℂ) (3 * R)).indicator (fun _ => M) x :=
        Set.indicator_nonneg (fun _ _ => hM0) x
      by_cases hx1 : ‖x‖ < R
      · rw [h5 x hx1]
        simpa using hind
      by_cases hx2 : 2 * R < ‖x‖
      · rw [h6 x hx2]
        simpa using hind
      rw [not_lt] at hx1 hx2
      have hxball : x ∈ ball (0 : ℂ) (3 * R) := by
        rw [mem_ball_zero_iff]
        linarith
      rw [Set.indicator_of_mem hxball]
      have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hR0 hx1
      obtain ⟨hp, hf⟩ := hdec x (hR.trans hx1)
      have hp' : |electricPotential d z α x| ≤ C / R :=
        hp.trans (div_le_div_of_nonneg_left hC hR0 hx1)
      have hf' : ‖electricField d z α x‖ ≤ C / R ^ 2 :=
        hf.trans (div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ hR0.le hx1 2))
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |electricPotential d z α x| * |fderiv ℝ (χ R) x (electricField d z α x)|
          ≤ (C / R) * (K / R * (C / R ^ 2)) := by
            refine mul_le_mul hp' ((h7 x _).trans ?_) (abs_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left hf' (by positivity)
        _ = M := by
            rw [hM]
            field_simp
    have hint : Integrable ((ball (0 : ℂ) (3 * R)).indicator (fun _ => M)) :=
      (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
    calc ‖∫ x, electricPotential d z α x * fderiv ℝ (χ R) x (electricField d z α x)‖
        ≤ ∫ x, (ball (0 : ℂ) (3 * R)).indicator (fun _ => M) x :=
          norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)
      _ = Real.pi * (3 * R) ^ 2 * M := by
          rw [integral_indicator_const M measurableSet_ball,
            volume_real_ball_complex 0 (by positivity), smul_eq_mul]
      _ = 9 * Real.pi * (K * C ^ 2) / R ^ 2 := by
          rw [hM]
          field_simp
          ring
  have hlim : Tendsto (fun R : ℝ => 9 * Real.pi * (K * C ^ 2) / R ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  exact squeeze_zero_norm' hbound hlim

/-- **The energy identity** (source eq. (eq:rewrF), Lemma 2.4 and Theorem 2, Step 1): for a neutral
configuration of disc charges,
`∫ |∇h_α|² = 2π Σᵢⱼ dᵢ dⱼ P_{ij}`. -/
theorem integral_norm_sq_electricField (hα : ∀ i, 0 < α i) (hn : ∑ i, d i = 0) :
    ∫ x, ‖electricField d z α x‖ ^ 2 =
      2 * Real.pi * ∑ i, ∑ j, d i * d j * pairInteraction (z i) (z j) (α i) (α j) := by
  obtain ⟨R₀, C, hR₀, hC, hdec⟩ := exists_decay_electric_nonneg (d := d) (z := z) hα hn
  obtain ⟨K, χ, hK, hχ⟩ := exists_cutoff_family
  have hid : ∀ᶠ R : ℝ in atTop, (∫ x, χ R x * ‖electricField d z α x‖ ^ 2) +
      ∫ x, electricPotential d z α x * fderiv ℝ (χ R) x (electricField d z α x) =
        2 * Real.pi * ∑ i, ∑ j, d i * d j * pairInteraction (z i) (z j) (α i) (α j) := by
    filter_upwards [eventually_ge_atTop (max R₀ (∑ i, (‖z i‖ + α i)))] with R hR
    have hR0 : 0 < R := lt_of_lt_of_le hR₀ ((le_max_left _ _).trans hR)
    obtain ⟨h1, h2, -, h4, -, -, -⟩ := hχ R hR0
    refine integral_cutoff_identity hα h1 h2 h4 fun i => ?_
    exact (Finset.single_le_sum (f := fun j => ‖z j‖ + α j)
      (fun j _ => add_nonneg (norm_nonneg _) (hα j).le) (Finset.mem_univ i)).trans
      ((le_max_right _ _).trans hR)
  have hA : Tendsto (fun R : ℝ => ∫ x, χ R x * ‖electricField d z α x‖ ^ 2) atTop
      (𝓝 (∫ x, ‖electricField d z α x‖ ^ 2)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖electricField d z α x‖ ^ 2) ?_ ?_ (integrable_norm_sq_electricField hα hn) ?_
    · filter_upwards [eventually_gt_atTop 0] with R hR
      exact ((hχ R hR).1.continuous.mul
        ((continuous_electricField hα).norm.pow 2)).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with R hR
      refine Filter.Eventually.of_forall fun x => ?_
      obtain ⟨-, -, h3, -⟩ := hχ R hR
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h3 x).1 (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (h3 x).2
    · refine Filter.Eventually.of_forall fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (max ‖x‖ 1)] with R hR
      have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hR)
      obtain ⟨-, -, -, h4, -⟩ := hχ R hR0
      rw [h4 x ((le_max_left _ _).trans hR), one_mul]
  have hB := tendsto_cross_term (d := d) (z := z) hα hn hK
    (fun R hR => ⟨(hχ R hR).2.2.2.2.1, (hχ R hR).2.2.2.2.2.1, (hχ R hR).2.2.2.2.2.2⟩)
  have hsum := hA.add hB
  rw [add_zero] at hsum
  exact tendsto_nhds_unique hsum (tendsto_const_nhds.congr' (hid.mono fun R hR => hR.symm))

/-- **Positivity of the pair energy of a neutral configuration** (Lemma 2.4). -/
theorem sum_pairInteraction_nonneg (hα : ∀ i, 0 < α i) (hn : ∑ i, d i = 0) :
    0 ≤ ∑ i, ∑ j, d i * d j * pairInteraction (z i) (z j) (α i) (α j) := by
  have h := integral_norm_sq_electricField (d := d) (z := z) hα hn
  have h0 : 0 ≤ ∫ x, ‖electricField d z α x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [h] at h0
  exact nonneg_of_mul_nonneg_right h0 (by positivity)

/-! ### The fluctuation bound -/

/-- The Cauchy-Schwarz inequality for the integral of a product of nonnegative square-integrable
functions on `ℂ`. -/
theorem integral_mul_le_sqrt_mul_sqrt {f g : ℂ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : AEStronglyMeasurable f volume) (hgm : AEStronglyMeasurable g volume)
    (hf : Integrable fun x => f x ^ 2) (hg : Integrable fun x => g x ^ 2) :
    ∫ x, f x * g x ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  have hf2 : MemLp f (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hfm).2 hf
  have hg2 : MemLp g (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hgm).2 hg
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0) hf2 hg2
  simp only [Real.rpow_two] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h

/-- **The electric energy bounds the fluctuations** (Theorem 2, Step 1, source l. 1973-1976):
for `ξ` of class `C¹` with compact support and a neutral configuration,
`|Σᵢ dᵢ ∫ ξ dδ_{zᵢ}^{(αᵢ)}| ≤ (2π)⁻¹ ‖∇ξ‖_{L²} ‖∇h_α‖_{L²}`. -/
theorem abs_sum_mul_integral_smearedCharge_le (hα : ∀ i, 0 < α i) (hn : ∑ i, d i = 0)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) :
    |∑ i, d i * ∫ y, ξ y ∂smearedCharge (z i) (α i)| ≤
      (2 * Real.pi)⁻¹ * Real.sqrt (∫ x, ‖fderiv ℝ ξ x‖ ^ 2) *
        Real.sqrt (∫ x, ‖electricField d z α x‖ ^ 2) := by
  have hG := integral_fderiv_apply_electricField (d := d) (z := z) hξ hc hα
  have hfc : Continuous fun x => ‖fderiv ℝ ξ x‖ := (hξ.continuous_fderiv one_ne_zero).norm
  have hfcs : HasCompactSupport fun x => ‖fderiv ℝ ξ x‖ :=
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L => ‖L‖) norm_zero
  have hEc : Continuous fun x => ‖electricField d z α x‖ := (continuous_electricField hα).norm
  have hprod : Integrable fun x => ‖fderiv ℝ ξ x‖ * ‖electricField d z α x‖ :=
    Continuous.integrable_of_hasCompactSupport (hfc.mul hEc) hfcs.mul_right
  have hCS := integral_mul_le_sqrt_mul_sqrt (f := fun x => ‖fderiv ℝ ξ x‖)
    (g := fun x => ‖electricField d z α x‖) (fun x => norm_nonneg _) (fun x => norm_nonneg _)
    hfc.aestronglyMeasurable hEc.aestronglyMeasurable
    (Continuous.integrable_of_hasCompactSupport (hfc.pow 2) (hfcs.comp_left (g := fun t => t ^ 2)
      (by norm_num)))
    (by simpa using integrable_norm_sq_electricField hα hn)
  have hint : |∫ x, fderiv ℝ ξ x (electricField d z α x)| ≤
      ∫ x, ‖fderiv ℝ ξ x‖ * ‖electricField d z α x‖ := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hprod (Filter.Eventually.of_forall fun x => ?_)
    exact (fderiv ℝ ξ x).le_opNorm _
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hsum : ∑ i, d i * ∫ y, ξ y ∂smearedCharge (z i) (α i) =
      (2 * Real.pi)⁻¹ * ∫ x, fderiv ℝ ξ x (electricField d z α x) := by
    rw [hG]
    field_simp
  rw [hsum, abs_mul, abs_of_pos (inv_pos.2 h2pi), mul_assoc]
  exact mul_le_mul_of_nonneg_left (hint.trans hCS) (inv_nonneg.2 h2pi.le)

/-! ### The electric formulation of the energy -/

/-- The charges `charge : Fin N ⊕ Fin N → ℝ` of a two-component configuration are neutral. -/
theorem sum_charge_eq_zero (N : ℕ) : ∑ a : Fin N ⊕ Fin N, charge a = 0 := by
  simp [Fintype.sum_sum_type]

/-- **The energy as an electric energy** (source eq. (eq:rewrF), l. 198-200):
`F_λ = (1 / 4π) ∫ |∇h_λ|² - N (g(λ) + κ)`. -/
theorem energy_eq_integral_norm_sq_electricField {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ) {lam : ℝ}
    (hlam : 0 < lam) :
    energy lam Z = (1 / (4 * Real.pi)) *
      (∫ x, ‖electricField charge Z (fun _ => lam) x‖ ^ 2) - N * (logKernel lam + kappa) := by
  have h := integral_norm_sq_electricField (d := charge) (z := Z) (α := fun _ => lam)
    (fun _ => hlam) (sum_charge_eq_zero N)
  rw [h, energy_eq_sum_smearedKernel]
  simp_rw [pairInteraction_eq_smearedKernel]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end Energy

end TwoComponentCoulomb

end
