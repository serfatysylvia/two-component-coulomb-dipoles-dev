/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TwoComponentCoulomb.Frozen.Fluct
public import TwoComponentCoulomb.Potential.ElectricEnergy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import TwoComponentCoulomb.Fluctuations.Mollify
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.SmearedCharge

/-!
# Theorem 2, Step 1: the electric energy bounds the fluctuations

Source: proof of Theorem 2, Step 1 (l. 1844–1876), the final fluctuation estimate of Step 1: for a
neutral configuration, with `h_α` the electric potential of the smeared charges
`Σᵢ dᵢ δ_{zᵢ}^{(αᵢ)}`, and `ξ(x) = ξ₀(x / √N)` for a Lipschitz `ξ₀`,

`|Fluct_N(ξ)|² ≤ C ‖∇ξ₀‖²_{L^∞} (∫ |∇h_α|² + N⁻¹ (Σᵢ αᵢ)²)`,

where, following ruling R8, `‖∇ξ₀‖_{L^∞}` is any Lipschitz constant `L` of `ξ₀`.

The argument of the source is: take `ξ̃ = (ξ - ξ(0)) χ` with a cutoff `χ` equal to `1` on `Λ`
(so `Fluct_N(ξ̃) = Fluct_N(ξ)` by neutrality), write `Σᵢ dᵢ ξ̃(zᵢ)` as the sum of
`Σᵢ dᵢ ∫ ξ̃ dδ_{zᵢ}^{(αᵢ)}`, which Green's formula and Cauchy-Schwarz bound by
`(2π)⁻¹ ‖∇ξ̃‖_{L²} ‖∇h_α‖_{L²}` (`abs_sum_mul_integral_smearedCharge_le`), and the smearing error
`Σᵢ dᵢ (ξ̃(zᵢ) - ∫ ξ̃ dδ_{zᵢ}^{(αᵢ)})`, bounded by `‖∇ξ̃‖_∞ Σᵢ αᵢ`.

Green's formula is only available for `C¹` functions, so the Lipschitz test function is first
replaced by a smooth `K`-Lipschitz mollification (`exists_contDiff_lipschitz_approx`) within
`K ε` of it; the estimate is then passed to the limit `ε → 0`. The compact support of `ξ₀` is not
used.

* `abs_sub_integral_smearedCharge_le` : the smearing error `|f(z) - ∫ f dδ_z^{(a)}| ≤ A a` of an
  `A`-Lipschitz function (source l. 1855–1858).
* `norm_fderiv_cutoff_mul_le` : `‖∇((η - η(0)) χ)‖ ≤ (1 + 2 Kχ) K` for a `K`-Lipschitz `η` and a
  cutoff `χ` at scale `R` (source l. 1847–1850).
* `sq_sum_mul_le_core` : the estimate for a `C¹` `K`-Lipschitz test function.
* `exists_sq_sum_mul_le_of_lipschitz` : the estimate for a merely `K`-Lipschitz test function.
* `exists_fluct_sq_le` : the final fluctuation estimate of Step 1 for Fluctₙ.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ContDiff NNReal

namespace TwoComponentCoulomb

/-! ### Elementary Lipschitz facts -/

/-- A function satisfying `|f x - f y| ≤ K ‖x - y‖` with `K ≥ 0` is `K`-Lipschitz. -/
theorem lipschitzWith_of_abs_sub_le {f : ℂ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ x y, |f x - f y| ≤ K * ‖x - y‖) : LipschitzWith K.toNNReal f :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal K hK] using hf x y

/-- A `K`-Lipschitz `C¹` function has `‖∇f‖ ≤ K`. -/
theorem norm_fderiv_le_of_abs_sub_le {f : ℂ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ x y, |f x - f y| ≤ K * ‖x - y‖) (x : ℂ) : ‖fderiv ℝ f x‖ ≤ K := by
  have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (lipschitzWith_of_abs_sub_le hK hf)
  rwa [Real.coe_toNNReal K hK] at h

/-- A differentiable function with `‖∇f‖ ≤ A` satisfies `|f x - f y| ≤ A ‖x - y‖`. -/
theorem abs_sub_le_of_norm_fderiv_le {f : ℂ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hd : Differentiable ℝ f) (hf : ∀ x, ‖fderiv ℝ f x‖ ≤ A) (x y : ℂ) :
    |f x - f y| ≤ A * ‖x - y‖ := by
  have h : LipschitzWith A.toNNReal f := lipschitzWith_of_nnnorm_fderiv_le hd fun x => by
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal A hA]
    exact hf x
  have h2 := h.dist_le_mul x y
  rwa [Real.coe_toNNReal A hA, Real.dist_eq, dist_eq_norm] at h2

/-! ### The smearing error -/

/-- **The smearing error** (source l. 1855–1858): for an `A`-Lipschitz function `f`,
`|f(z) - ∫ f dδ_z^{(a)}| ≤ A a`. -/
theorem abs_sub_integral_smearedCharge_le {f : ℂ → ℝ} {A : ℝ}
    (hf : ∀ x y, |f x - f y| ≤ A * ‖x - y‖) (hc : Continuous f) (z : ℂ) {a : ℝ} (ha : 0 < a) :
    |f z - ∫ y, f y ∂smearedCharge z a| ≤ A * a := by
  have := isProbabilityMeasure_smearedCharge z ha
  have hA : 0 ≤ A := by
    have h := hf 1 0
    simp only [sub_zero, norm_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hint : Integrable f (smearedCharge z a) := integrable_smearedCharge_of_continuous hc z a
  have h1 : f z - ∫ y, f y ∂smearedCharge z a = ∫ y, (f z - f y) ∂smearedCharge z a := by
    rw [integral_sub (integrable_const _) hint]
    simp
  rw [h1, ← Real.norm_eq_abs]
  have h2 := norm_integral_le_of_norm_le_const (μ := smearedCharge z a)
    (f := fun y => f z - f y) (C := A * a) (by
      filter_upwards [ae_mem_ball_smearedCharge z a] with y hy
      rw [Real.norm_eq_abs]
      refine (hf z y).trans ?_
      have : ‖z - y‖ < a := by simpa [dist_eq_norm, norm_sub_rev] using hy
      exact mul_le_mul_of_nonneg_left this.le hA)
  simpa using h2

/-! ### The estimate for `C¹` Lipschitz functions -/

section Core

variable {ι : Type*} [Fintype ι] {d : ι → ℝ} {z : ι → ℂ} {α : ι → ℝ}

/-- The derivative of the localised function `(η - η(0)) χ`. -/
theorem norm_fderiv_cutoff_mul_le {η χ : ℂ → ℝ} {K Kχ R : ℝ} (hK : 0 ≤ K) (hKχ : 0 ≤ Kχ)
    (hR : 0 < R) (hη : ContDiff ℝ 1 η) (hηL : ∀ x y, |η x - η y| ≤ K * ‖x - y‖)
    (hχ : ContDiff ℝ 1 χ) (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (h0 : ∀ x, 2 * R ≤ ‖x‖ → χ x = 0)
    (hχd : ∀ x, ‖fderiv ℝ χ x‖ ≤ Kχ / R) (x : ℂ) :
    ‖fderiv ℝ (fun y => (η y - η 0) * χ y) x‖ ≤ (1 + 2 * Kχ) * K := by
  by_cases hx : 2 * R < ‖x‖
  · have hev : (fun y => (η y - η 0) * χ y) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {y : ℂ | 2 * R < ‖y‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hx] with y hy
      simp [h0 y (le_of_lt hy)]
    rw [hev.fderiv_eq]
    simp only [fderiv_fun_const, Pi.zero_apply, norm_zero]
    positivity
  · rw [not_lt] at hx
    rw [fderiv_fun_mul ((hη.differentiable one_ne_zero x).sub_const _)
      (hχ.differentiable one_ne_zero x), fderiv_sub_const]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |η x - η 0| ≤ K * (2 * R) := by
      refine (hηL x 0).trans ?_
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_left hx hK
    have h2 : ‖fderiv ℝ η x‖ ≤ K := norm_fderiv_le_of_abs_sub_le hK hηL x
    have h3 : |χ x| ≤ 1 := by
      rw [abs_of_nonneg (h01 x).1]
      exact (h01 x).2
    calc |η x - η 0| * ‖fderiv ℝ χ x‖ + |χ x| * ‖fderiv ℝ η x‖
        ≤ K * (2 * R) * (Kχ / R) + 1 * K := by
          refine add_le_add (mul_le_mul h1 (hχd x) (norm_nonneg _) (by positivity)) ?_
          exact mul_le_mul h3 h2 (norm_nonneg _) zero_le_one
      _ = (1 + 2 * Kχ) * K := by
          field_simp
          ring

/-- **The estimate for a `C¹` Lipschitz test function** (source l. 1847–1861): with universal
constant `1 + 2 Kχ` from the cutoff of `exists_cutoff`, for `η` of class `C¹` and `K`-Lipschitz,
a neutral configuration of charges `|dᵢ| ≤ 1` in `B̄(0, R)` and positive radii `αᵢ`,
`(Σᵢ dᵢ η(zᵢ))² ≤ 2 ((1 + 2Kχ) K)² (R² ∫ |∇h_α|² + (Σᵢ αᵢ)²)`. -/
theorem sq_sum_mul_le_core (hd : ∀ i, |d i| ≤ 1) (hn : ∑ i, d i = 0) (hα : ∀ i, 0 < α i)
    {η : ℂ → ℝ} (hη : ContDiff ℝ 1 η) {K : ℝ} (hK : 0 ≤ K)
    (hηL : ∀ x y, |η x - η y| ≤ K * ‖x - y‖) {χ : ℂ → ℝ} {Kχ R : ℝ} (hKχ : 0 ≤ Kχ) (hR : 0 < R)
    (hχ : ContDiff ℝ 1 χ) (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (h1 : ∀ x, ‖x‖ ≤ R → χ x = 1)
    (h0 : ∀ x, 2 * R ≤ ‖x‖ → χ x = 0) (hχd : ∀ x, ‖fderiv ℝ χ x‖ ≤ Kχ / R)
    (hz : ∀ i, ‖z i‖ ≤ R) :
    (∑ i, d i * η (z i)) ^ 2 ≤
      2 * ((1 + 2 * Kχ) * K) ^ 2 * (R ^ 2 * (∫ x, ‖electricField d z α x‖ ^ 2) + (∑ i, α i) ^ 2) := by
  set A : ℝ := (1 + 2 * Kχ) * K with hAdef
  have hA : 0 ≤ A := by positivity
  set T : ℂ → ℝ := fun y => (η y - η 0) * χ y with hT
  have hTd : ContDiff ℝ 1 T := (hη.sub contDiff_const).mul hχ
  have hT0 : ∀ x, 2 * R ≤ ‖x‖ → T x = 0 := fun x hx => by simp [hT, h0 x hx]
  have hTc : HasCompactSupport T := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * R)) fun x hx => hT0 x ?_
    simp only [mem_closedBall, dist_zero_right, not_le] at hx
    exact hx.le
  have hder : ∀ x, ‖fderiv ℝ T x‖ ≤ A := fun x =>
    norm_fderiv_cutoff_mul_le hK hKχ hR hη hηL hχ h01 h0 hχd x
  have hder0 : ∀ x, 2 * R < ‖x‖ → fderiv ℝ T x = 0 := fun x hx => by
    have hev : T =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {y : ℂ | 2 * R < ‖y‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hT0 y hy.le
    rw [hev.fderiv_eq]
    simp
  have hTL : ∀ x y, |T x - T y| ≤ A * ‖x - y‖ :=
    abs_sub_le_of_norm_fderiv_le hA (hTd.differentiable one_ne_zero) hder
  -- neutrality: the fluctuation of `T` is that of `η`
  have hsum : ∑ i, d i * T (z i) = ∑ i, d i * η (z i) := by
    have : ∀ i, T (z i) = η (z i) - η 0 := fun i => by simp [hT, h1 (z i) (hz i)]
    simp_rw [this, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hn, zero_mul, sub_zero]
  -- Green's formula and Cauchy-Schwarz
  set I : ℝ := ∫ x, ‖electricField d z α x‖ ^ 2 with hI
  set J : ℝ := ∫ x, ‖fderiv ℝ T x‖ ^ 2 with hJ
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hJ0 : 0 ≤ J := integral_nonneg fun x => sq_nonneg _
  have hG := abs_sum_mul_integral_smearedCharge_le (d := d) (z := z) hα hn hTd hTc
  -- the Dirichlet integral of `T`
  have hJle : J ≤ 9 * Real.pi * A ^ 2 * R ^ 2 := by
    set M : ℝ := A ^ 2 with hM
    have hpt : ∀ x, ‖fderiv ℝ T x‖ ^ 2 ≤ (ball (0 : ℂ) (3 * R)).indicator (fun _ => M) x := by
      intro x
      by_cases hx : 2 * R < ‖x‖
      · rw [hder0 x hx, norm_zero]
        exact (Set.indicator_nonneg (fun _ _ => sq_nonneg A) x).trans' (by simp)
      · rw [not_lt] at hx
        have hxb : x ∈ ball (0 : ℂ) (3 * R) := by
          rw [mem_ball_zero_iff]
          linarith
        rw [Set.indicator_of_mem hxb]
        exact pow_le_pow_left₀ (norm_nonneg _) (hder x) 2
    have hint : Integrable ((ball (0 : ℂ) (3 * R)).indicator (fun _ => M)) :=
      (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
    have hJint : Integrable fun x => ‖fderiv ℝ T x‖ ^ 2 := by
      refine Integrable.mono' hint
        ((hTd.continuous_fderiv one_ne_zero).norm.pow 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpt x
    calc J ≤ ∫ x, (ball (0 : ℂ) (3 * R)).indicator (fun _ => M) x :=
          integral_mono hJint hint hpt
      _ = Real.pi * (3 * R) ^ 2 * M := by
          rw [integral_indicator_const M measurableSet_ball,
            volume_real_ball_complex 0 (by positivity), smul_eq_mul]
      _ = 9 * Real.pi * A ^ 2 * R ^ 2 := by
          rw [hM]
          ring
  -- the first term
  have ha : ((2 * Real.pi)⁻¹ * Real.sqrt J * Real.sqrt I) ^ 2 ≤ A ^ 2 * R ^ 2 * I := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hpi3 : 3 < Real.pi := Real.pi_gt_three
    rw [mul_pow, mul_pow, Real.sq_sqrt hJ0, Real.sq_sqrt hI0]
    have hc : ((2 * Real.pi)⁻¹) ^ 2 * (9 * Real.pi * A ^ 2 * R ^ 2) ≤ A ^ 2 * R ^ 2 := by
      have : ((2 * Real.pi)⁻¹) ^ 2 * (9 * Real.pi * A ^ 2 * R ^ 2) =
          (9 / (4 * Real.pi)) * (A ^ 2 * R ^ 2) := by
        field_simp
        ring
      rw [this]
      refine mul_le_of_le_one_left (by positivity) ?_
      rw [div_le_one (by positivity)]
      linarith
    calc ((2 * Real.pi)⁻¹) ^ 2 * J * I
        ≤ ((2 * Real.pi)⁻¹) ^ 2 * (9 * Real.pi * A ^ 2 * R ^ 2) * I := by
          gcongr
      _ ≤ A ^ 2 * R ^ 2 * I := mul_le_mul_of_nonneg_right hc hI0
  -- the second term
  have hb : |∑ i, d i * (T (z i) - ∫ y, T y ∂smearedCharge (z i) (α i))| ≤ A * ∑ i, α i := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    calc |d i| * |T (z i) - ∫ y, T y ∂smearedCharge (z i) (α i)|
        ≤ 1 * (A * α i) := mul_le_mul (hd i) (abs_sub_integral_smearedCharge_le hTL hTd.continuous
          (z i) (hα i)) (abs_nonneg _) zero_le_one
      _ = A * α i := one_mul _
  -- combine
  have hsplit : ∑ i, d i * T (z i) =
      ∑ i, d i * ∫ y, T y ∂smearedCharge (z i) (α i) +
        ∑ i, d i * (T (z i) - ∫ y, T y ∂smearedCharge (z i) (α i)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have htri : |∑ i, d i * η (z i)| ≤
      (2 * Real.pi)⁻¹ * Real.sqrt J * Real.sqrt I + A * ∑ i, α i := by
    rw [← hsum, hsplit]
    exact (abs_add_le _ _).trans (add_le_add hG hb)
  have ha0 : 0 ≤ (2 * Real.pi)⁻¹ * Real.sqrt J * Real.sqrt I := by positivity
  calc (∑ i, d i * η (z i)) ^ 2 = |∑ i, d i * η (z i)| ^ 2 := (sq_abs _).symm
    _ ≤ ((2 * Real.pi)⁻¹ * Real.sqrt J * Real.sqrt I + A * ∑ i, α i) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) htri 2
    _ ≤ 2 * ((2 * Real.pi)⁻¹ * Real.sqrt J * Real.sqrt I) ^ 2 + 2 * (A * ∑ i, α i) ^ 2 :=
        add_sq_le.trans_eq (mul_add _ _ _)
    _ ≤ 2 * (A ^ 2 * R ^ 2 * I) + 2 * (A * ∑ i, α i) ^ 2 := by gcongr
    _ = 2 * A ^ 2 * (R ^ 2 * I + (∑ i, α i) ^ 2) := by ring

end Core

/-! ### The estimate for Lipschitz functions -/

universe u

/-- **The estimate for a Lipschitz test function** (source l. 1847–1866): there is a universal
constant `C₁` such that for every `K`-Lipschitz `η`, every neutral configuration of charges
`|dᵢ| ≤ 1` located in `B̄(0, R)` and all radii `αᵢ > 0`,
`(Σᵢ dᵢ η(zᵢ))² ≤ C₁ K² (R² ∫ |∇h_α|² + (Σᵢ αᵢ)²)`.
The proof applies `sq_sum_mul_le_core` to mollifications of `η` and lets the mollification
parameter tend to zero. -/
theorem exists_sq_sum_mul_le_of_lipschitz :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (ι : Type u) [Fintype ι] (d : ι → ℝ) (z : ι → ℂ) (α : ι → ℝ),
      (∀ i, |d i| ≤ 1) → ∑ i, d i = 0 → (∀ i, 0 < α i) → ∀ (η : ℂ → ℝ) (K R : ℝ), 0 ≤ K →
      0 < R → (∀ x y, |η x - η y| ≤ K * ‖x - y‖) → (∀ i, ‖z i‖ ≤ R) →
      (∑ i, d i * η (z i)) ^ 2 ≤
        C₁ * K ^ 2 * (R ^ 2 * (∫ x, ‖electricField d z α x‖ ^ 2) + (∑ i, α i) ^ 2) := by
  obtain ⟨Kχ, hKχ, hχ⟩ := exists_cutoff
  refine ⟨2 * (1 + 2 * Kχ) ^ 2, by positivity, ?_⟩
  intro ι _ d z α hd hn hα η K R hK hR hηL hz
  obtain ⟨χ, hχs, -, h01, h1, h0, hχd⟩ := hχ R hR
  set B : ℝ := 2 * (1 + 2 * Kχ) ^ 2 * K ^ 2 *
    (R ^ 2 * (∫ x, ‖electricField d z α x‖ ^ 2) + (∑ i, α i) ^ 2) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∫ x, ‖electricField d z α x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
    positivity
  have hc : 0 < (Fintype.card ι : ℝ) * K + 1 := by positivity
  have hmain : |∑ i, d i * η (z i)| ≤ Real.sqrt B := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨g, hg, hgL, hgη⟩ := exists_contDiff_lipschitz_approx hηL
      (div_pos hε hc)
    have hcore := sq_sum_mul_le_core (d := d) (z := z) (α := α) hd hn hα (hg.of_le (by simp))
      hK hgL hKχ hR (hχs.of_le (by simp)) h01 h1 h0 hχd hz
    have hcore' : (∑ i, d i * g (z i)) ^ 2 ≤ B := by
      refine hcore.trans (le_of_eq ?_)
      rw [hB]
      ring
    have h1' : |∑ i, d i * g (z i)| ≤ Real.sqrt B := Real.abs_le_sqrt hcore'
    have h2 : |∑ i, d i * η (z i) - ∑ i, d i * g (z i)| ≤ ε := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |d i * η (z i) - d i * g (z i)|
          ≤ ∑ _i : ι, K * (ε / ((Fintype.card ι : ℝ) * K + 1)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [← mul_sub, abs_mul]
            calc |d i| * |η (z i) - g (z i)| ≤ 1 * (K * (ε / ((Fintype.card ι : ℝ) * K + 1))) :=
                  mul_le_mul (hd i) (by rw [abs_sub_comm]; exact hgη (z i)) (abs_nonneg _)
                    zero_le_one
              _ = _ := one_mul _
        _ = (Fintype.card ι : ℝ) * K * ε / ((Fintype.card ι : ℝ) * K + 1) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
        _ ≤ ε := by
            rw [div_le_iff₀ hc]
            linarith only [hε]
    calc |∑ i, d i * η (z i)|
        = |(∑ i, d i * η (z i) - ∑ i, d i * g (z i)) + ∑ i, d i * g (z i)| := by ring_nf
      _ ≤ |∑ i, d i * η (z i) - ∑ i, d i * g (z i)| + |∑ i, d i * g (z i)| := abs_add_le _ _
      _ ≤ Real.sqrt B + ε := by linarith
  calc (∑ i, d i * η (z i)) ^ 2 = |∑ i, d i * η (z i)| ^ 2 := (sq_abs _).symm
    _ ≤ Real.sqrt B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hmain 2
    _ = B := Real.sq_sqrt hB0
    _ = _ := by rw [hB]

/-! ### Eq. the final fluctuation estimate of Step 1 for Fluctₙ -/

/-- **Theorem 2, Step 1: the electric energy bounds the fluctuations** (source l. 1844–1876,
the final fluctuation estimate of Step 1): there is an absolute constant `C` such that for every `N ≥ 1`, every Lipschitz
`ξ₀ : ℂ → ℝ` with Lipschitz constant `L` (ruling R8), every configuration `Z` in the box `Λ^{2N}`
and every positive radii `α`, writing `ξ(x) = ξ₀(x / √N)`,
`Fluct_N(ξ)² ≤ C L² (∫ |∇h_α|² + N⁻¹ (Σᵢ αᵢ)²)`. -/
theorem exists_fluct_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ ξ₀ : ℂ → ℝ, HasCompactSupport ξ₀ → ∀ L : ℝ≥0,
      LipschitzWith L ξ₀ → ∀ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) →
      ∀ α : Fin N ⊕ Fin N → ℝ, (∀ i, 0 < α i) →
        fluct (fun x => ξ₀ ((Real.sqrt N)⁻¹ • x)) Z ^ 2 ≤
          C * (L : ℝ) ^ 2 *
            ((∫ x, ‖electricField charge Z α x‖ ^ 2) + (∑ i, α i) ^ 2 / N) := by
  obtain ⟨C₁, hC₁, hlip⟩ := exists_sq_sum_mul_le_of_lipschitz.{0}
  refine ⟨4 * C₁, by positivity, ?_⟩
  intro N hN ξ₀ _ L hL Z hZ α hα
  set s : ℝ := Real.sqrt N with hs
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hs0 : 0 < s := Real.sqrt_pos.2 hN0
  have hs2 : s ^ 2 = N := Real.sq_sqrt hN0.le
  set ξ : ℂ → ℝ := fun x => ξ₀ (s⁻¹ • x) with hξ
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hξL : ∀ x y, |ξ x - ξ y| ≤ ((L : ℝ) / s) * ‖x - y‖ := fun x y => by
    have h := hL.dist_le_mul (s⁻¹ • x) (s⁻¹ • y)
    rw [Real.dist_eq, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hs0)] at h
    calc |ξ x - ξ y| ≤ (L : ℝ) * (s⁻¹ * ‖x - y‖) := h
      _ = ((L : ℝ) / s) * ‖x - y‖ := by ring
  have hZR : ∀ i, ‖Z i‖ ≤ 2 * s := fun i => by
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.1 (hZ i)
    refine (Complex.norm_le_abs_re_add_abs_im (Z i)).trans ?_
    rw [abs_of_nonneg h1.1, abs_of_nonneg h2.1]
    linarith [h1.2, h2.2]
  have hd : ∀ i : Fin N ⊕ Fin N, |charge i| ≤ 1 := fun i => by
    rcases i with i | i <;> simp [charge]
  have hfl : fluct ξ Z = ∑ i, charge i * ξ (Z i) := by
    unfold fluct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Set.indicator_of_mem (hZ i)]
  have h := hlip (Fin N ⊕ Fin N) charge Z α hd (sum_charge_eq_zero N) hα ξ ((L : ℝ) / s) (2 * s)
    (by positivity) (by positivity) hξL hZR
  rw [hfl]
  refine h.trans ?_
  set I : ℝ := ∫ x, ‖electricField charge Z α x‖ ^ 2 with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hsum0 : 0 ≤ (∑ i, α i) ^ 2 / N := by positivity
  have hrw : C₁ * ((L : ℝ) / s) ^ 2 * ((2 * s) ^ 2 * I + (∑ i, α i) ^ 2) =
      C₁ * (L : ℝ) ^ 2 * (4 * I + (∑ i, α i) ^ 2 / N) := by
    rw [← hs2]
    field_simp
    ring
  rw [hrw]
  have hCL : 0 ≤ C₁ * (L : ℝ) ^ 2 := by positivity
  linarith only [mul_nonneg hCL hsum0]

end TwoComponentCoulomb

end
