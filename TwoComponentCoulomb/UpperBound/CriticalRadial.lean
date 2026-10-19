/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.UpperBound.IsolatedRadial
import TwoComponentCoulomb.Gibbs.Measurability
import TwoComponentCoulomb.Integrals.GaussianMass
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Radial integrals of the critical case `β = 2` (Proposition 3.10, eq. (eq:critical upper))

Source: l. 1682--1697 (proof of Proposition 3.10, `β = 2`), with the integrals of Lemma 3.3
(`lem:critical radial`, l. 699--754). Write
`ℓ = |log λ|`, `g_λ = smearedKernel λ` and `a(u) = (|u|/4) ∨ λ` (`displacementScale λ u`).

Conditional on the retained coordinates, the displacement `u` of an isolated pair is confined to
the disc `|u| ≤ 4ρ`, where `ρ ≥ λ` is the radius of the pair (source l. 1670--1673). The source
bounds the integral of the pair weight over `u` by

* `T_R = J_λ(1/ℓ) + C + (e - 1)(J_λ(1/ℓ;R) + C)` for a neutral pair (l. 1693--1696), where
  `J_λ(1/ℓ) = ∫ e^{2 g_λ(u) - |u|²/ℓ} du = 2π (ℓ + ½ log ℓ) + O(1)` (eq:critical-B) and
  `J_λ(1/ℓ;R) = ∫_{|u| ≥ R} e^{2 g_λ(u) - |u|²/ℓ} du = 2π (log (1/R) + ½ log ℓ) + O(1)`
  (eq:critical-BR);
* `C` for a same-sign pair (l. 1697).

The pair weights are `TwoComponentCoulomb.critNeutralWeight` and
`TwoComponentCoulomb.critSameSignWeight`, functions of `(u, ρ)`. Here the same-sign weight is
`c · (|u| ∨ λ)² / ρ⁴` on `|u| ≤ 4ρ`: by `e^{-2 g_λ(u)} ≤ C (|u| ∨ λ)²` this dominates the source's
`e^{2 g_λ(u)} (a/ρ)⁴ ≤ C'` integrand (l. 1687, 1697) after the energy bound, and its integral is
bounded directly by `|u| ∨ λ ≤ 4ρ`. The quadratic correction of the neutral weight is
handled by the pointwise bound `e^{2 g_λ(u)} (a/ρ)² ≤ C/ρ²` on the disc (since
`a ≤ |u| ∨ λ`), which replaces the source's split at `2λ` (proof of (eq:critical-correction),
l. 750--753).

## Main results

* `TwoComponentCoulomb.integral_tail_gaussianMass_le`:
  `J_λ(1/ℓ;R) ≤ 2π (½ log ℓ + log (1/R) + ½)` for `2λ ≤ R ≤ 1` (the upper half of
  (eq:critical-BR)).
* `TwoComponentCoulomb.exists_lintegral_critNeutralWeight_le`: the neutral pair contributes at most
  `2π(ℓ + ½ log ℓ) + (e - 1) 2π(½ log ℓ + log (1/R) + ½) + C`, uniformly in `ρ ≥ λ`.
* `TwoComponentCoulomb.lintegral_critSameSignWeight_le`: the same-sign pair contributes at most
  `256 π c`, uniformly in `ρ ≥ λ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### The pair weights -/

/-- The weight of an isolated neutral pair with displacement `u` and radius `ρ` (source
l. 1689--1692): on the disc `|u| ≤ 4ρ`, `exp (2 g_λ(u) - |u|²/ℓ + c (a(u)/ρ)² + 1_{|u| > R})`,
where `a(u) = (|u|/4) ∨ λ`; the Gaussian factor comes from the packing bound and `1_{|u| > R}`
from the long-dipole count `D_R`. -/
noncomputable def critNeutralWeight (lam ℓ R c : ℝ) (p : ℂ × ℝ) : ℝ≥0∞ :=
  if ‖p.1‖ ≤ 4 * p.2 then
    ENNReal.ofReal (Real.exp (2 * smearedKernel lam p.1 - ‖p.1‖ ^ 2 / ℓ +
      c * (displacementScale lam p.1 / p.2) ^ 2 + (if R < ‖p.1‖ then 1 else 0)))
  else 0

/-- The weight of an isolated same-sign pair with displacement `u` and radius `ρ`: on the disc
`|u| ≤ 4ρ`, `c (|u| ∨ λ)² / ρ⁴` (source l. 1676--1680, 1697). -/
noncomputable def critSameSignWeight (lam c : ℝ) (p : ℂ × ℝ) : ℝ≥0∞ :=
  if ‖p.1‖ ≤ 4 * p.2 then ENNReal.ofReal (c * max ‖p.1‖ lam ^ 2 / p.2 ^ 4) else 0

theorem measurable_critNeutralWeight (lam ℓ R c : ℝ) :
    Measurable (critNeutralWeight lam ℓ R c) := by
  have hs : MeasurableSet {p : ℂ × ℝ | ‖p.1‖ ≤ 4 * p.2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hg : Measurable (smearedKernel lam) := measurable_smearedKernel lam
  have hR : MeasurableSet {p : ℂ × ℝ | R < ‖p.1‖} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hb : Measurable fun p : ℂ × ℝ => (if R < ‖p.1‖ then (1 : ℝ) else 0) :=
    Measurable.ite hR measurable_const measurable_const
  have hd : Measurable fun p : ℂ × ℝ => displacementScale lam p.1 :=
    (continuous_displacementScale lam).measurable.comp measurable_fst
  refine Measurable.ite hs ?_ measurable_const
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  refine Measurable.add (Measurable.add ?_ ?_) hb
  · exact ((hg.comp measurable_fst).const_mul 2).sub (by fun_prop)
  · exact ((hd.div measurable_snd).pow_const 2).const_mul c

theorem measurable_critSameSignWeight (lam c : ℝ) : Measurable (critSameSignWeight lam c) := by
  have hs : MeasurableSet {p : ℂ × ℝ | ‖p.1‖ ≤ 4 * p.2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  refine Measurable.ite hs ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

/-! ### Elementary bounds -/

/-- The volume of the closed disc of radius `4ρ`, times a constant `x/ρ²`. -/
theorem lintegral_indicator_closedBall_div_sq {ρ x : ℝ} (hρ : 0 < ρ) (hx : 0 ≤ x) :
    ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) (4 * ρ)).indicator
        (fun _ => ENNReal.ofReal (x / ρ ^ 2)) u = ENNReal.ofReal (16 * Real.pi * x) := by
  rw [lintegral_indicator_const Metric.isClosed_closedBall.measurableSet,
    Complex.volume_closedBall, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- From `|g_λ - g(|u| ∨ λ)| ≤ C₀`: `e^{2 g_λ(u)} ≤ e^{2 C₀} / (|u| ∨ λ)²`. -/
theorem exp_two_mul_smearedKernel_le_div {C₀ lam : ℝ}
    (hC₀ : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ,
      |smearedKernel lam z - logKernel ((max ‖z‖ lam : ℝ) : ℂ)| ≤ C₀)
    (hlam : 0 < lam) (u : ℂ) :
    Real.exp (2 * smearedKernel lam u) ≤ Real.exp (2 * C₀) / max ‖u‖ lam ^ 2 := by
  have hm : 0 < max ‖u‖ lam := lt_of_lt_of_le hlam (le_max_right _ _)
  have h1 := (abs_le.1 (hC₀ lam hlam u)).2
  rw [logKernel_ofReal hm] at h1
  rw [le_div_iff₀ (by positivity), ← Real.exp_log (pow_pos hm 2), ← Real.exp_add,
    Real.exp_le_exp, Real.log_pow]
  push_cast
  linarith

/-! ### The Gaussian tail `J_λ(1/ℓ;R)` -/

/-- **The tail `J_λ(1/ℓ;R)`** (eq:critical-BR, source l. 711--715, upper bound): for
`0 < λ ≤ e⁻¹` and `2λ ≤ R ≤ 1`,
`∫_{|u| > R} e^{2 g_λ(u) - |u|²/ℓ} du ≤ 2π (½ log ℓ + log (1/R) + ½)`, `ℓ = |log λ|`. -/
theorem integral_tail_gaussianMass_le {lam R : ℝ} (hlam : 0 < lam) (hle : lam ≤ Real.exp (-1))
    (hR : 2 * lam ≤ R) (hR1 : R ≤ 1) :
    ∫ u : ℂ, (if R < ‖u‖ then Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|)
        else 0) ≤
      2 * Real.pi * ((1 / 2) * Real.log |Real.log lam| + Real.log (1 / R) + 1 / 2) := by
  obtain ⟨h1, -⟩ := two_mul_le_sqrt_neg_log hlam hle
  have hab : |Real.log lam| = -Real.log lam := abs_of_neg (by linarith)
  set ℓ := -Real.log lam with hℓdef
  have hℓ : 0 < ℓ := by linarith
  have hR0 : 0 < R := by linarith
  have hRs : R ≤ Real.sqrt ℓ := hR1.trans (Real.one_le_sqrt.2 h1)
  have hf : ∀ u : ℂ, (if R < ‖u‖ then Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|)
      else 0) = (Ioi R).indicator (gaussianProfile lam ℓ) ‖u‖ := by
    intro u
    rw [hab, gaussianProfile_eq_comp_norm]
    by_cases hu : R < ‖u‖
    · rw [ite_eq_left hu, indicator_of_mem (mem_Ioi.2 hu)]
    · rw [ite_eq_right hu, indicator_of_notMem (by simpa using hu)]
  simp_rw [hf]
  rw [integral_comp_norm_complex]
  have h2 : ∀ y : ℝ, y * (Ioi R).indicator (gaussianProfile lam ℓ) y =
      (Ioi R).indicator (fun y => y * gaussianProfile lam ℓ y) y := by
    intro y
    by_cases hy : y ∈ Ioi R
    · rw [indicator_of_mem hy, indicator_of_mem hy]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
  simp_rw [h2]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hR0.le,
    setIntegral_congr_fun measurableSet_Ioi
      (fun y hy => mul_gaussianProfile_of_le hlam (hR.trans (mem_Ioi.1 hy).le)),
    ← Ioc_union_Ioi_eq_Ioi hRs,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_exp_neg_sq_div_Ioc ℓ hR0) (integrableOn_exp_neg_sq_div_Ioi hℓ)]
  have hmid := integral_exp_neg_sq_div_Ioc_le hℓ hR0 hRs
  have htail := integral_exp_neg_sq_div_Ioi_le hℓ
  rw [Real.log_sqrt hℓ.le] at hmid
  rw [one_div R, Real.log_inv, hab]
  have hpi : 0 < 2 * Real.pi := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith only [hmid, htail]) hpi.le

/-- The tail integrand of `J_λ(1/ℓ;R)` is integrable. -/
theorem integrable_tail_gaussianMass {lam R : ℝ} (hlam : 0 < lam) (hle : lam ≤ Real.exp (-1)) :
    Integrable fun u : ℂ =>
      (if R < ‖u‖ then Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|) else 0) := by
  have hi := integrable_gaussianMass hlam hle
  refine hi.mono' ?_ (ae_of_all _ fun u => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.ite (measurableSet_lt measurable_const measurable_norm) ?_ measurable_const
    have := measurable_smearedKernel lam
    fun_prop
  · by_cases hu : R < ‖u‖
    · rw [ite_eq_left hu, Real.norm_of_nonneg (Real.exp_pos _).le]
    · rw [ite_eq_right hu, norm_zero]
      exact (Real.exp_pos _).le

/-! ### The neutral pair -/

/-- **The neutral pair** (source l. 1689--1696, the bound
`T_R = J_λ(1/ℓ) + C + (e-1)(J_λ(1/ℓ;R) + C)`): for every `c ≥ 0` there is `C` such that for
`0 < λ ≤ e⁻¹`, `2λ ≤ R ≤ 1` and `ρ ≥ λ`,
`∫ critNeutralWeight ≤ 2π (ℓ + ½ log ℓ) + (e - 1) · 2π (½ log ℓ + log (1/R) + ½) + C`. -/
theorem exists_lintegral_critNeutralWeight_le {c : ℝ} (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam R ρ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → 2 * lam ≤ R → R ≤ 1 →
      lam ≤ ρ →
        ∫⁻ u, critNeutralWeight lam |Real.log lam| R c (u, ρ) ≤
          ENNReal.ofReal (2 * Real.pi * (|Real.log lam| + (1 / 2) * Real.log |Real.log lam|) +
            (Real.exp 1 - 1) * (2 * Real.pi *
              ((1 / 2) * Real.log |Real.log lam| + Real.log (1 / R) + 1 / 2)) + C) := by
  obtain ⟨CB, hCB⟩ := exists_abs_gaussianMass_sub_le
  obtain ⟨C₀, hC₀⟩ := exists_abs_smearedKernel_sub_logKernel_le
  set K : ℝ := Real.exp 1 * (Real.exp c - 1) * Real.exp (2 * C₀) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Real.exp c - 1 := by
      have := Real.one_le_exp hc
      linarith
    positivity
  have hCB0 : 0 ≤ CB := (abs_nonneg _).trans (hCB (Real.exp (-1)) (Real.exp_pos _) le_rfl)
  refine ⟨CB + 16 * Real.pi * K, by positivity, fun lam R ρ hlam hle hR hR1 hρ => ?_⟩
  obtain ⟨h1, -⟩ := two_mul_le_sqrt_neg_log hlam hle
  have hab : |Real.log lam| = -Real.log lam := abs_of_neg (by linarith)
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  set ℓ := |Real.log lam| with hℓdef
  have hℓ1 : 1 ≤ ℓ := by rw [hab]; exact h1
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hlogR : 0 ≤ Real.log (1 / R) := Real.log_nonneg (by
    rw [le_div_iff₀ (by linarith)]; linarith)
  set X : ℂ → ℝ := fun u => Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ) with hX
  set T : ℂ → ℝ := fun u => if R < ‖u‖ then X u else 0 with hT
  have hXm : Measurable X := by
    have := measurable_smearedKernel lam
    rw [hX]
    fun_prop
  have hTm : Measurable T :=
    Measurable.ite (measurableSet_lt measurable_const measurable_norm) hXm measurable_const
  -- pointwise bound
  have hpt : ∀ u : ℂ, critNeutralWeight lam ℓ R c (u, ρ) ≤
      ENNReal.ofReal (X u) + ENNReal.ofReal ((Real.exp 1 - 1) * T u) +
        (Metric.closedBall (0 : ℂ) (4 * ρ)).indicator (fun _ => ENNReal.ofReal (K / ρ ^ 2)) u := by
    intro u
    unfold critNeutralWeight
    dsimp only
    by_cases hu : ‖u‖ ≤ 4 * ρ
    · rw [ite_eq_left hu]
      have hmem : u ∈ Metric.closedBall (0 : ℂ) (4 * ρ) := by simpa using hu
      rw [indicator_of_mem hmem]
      have hXpos : 0 < X u := Real.exp_pos _
      have hTnn : 0 ≤ (Real.exp 1 - 1) * T u := by
        have : 0 ≤ T u := by
          rw [hT]
          dsimp only
          by_cases hRu : R < ‖u‖
          · rw [ite_eq_left hRu]; exact hXpos.le
          · rw [ite_eq_right hRu]
        have : 0 ≤ Real.exp 1 - 1 := by have := Real.one_le_exp zero_le_one; linarith
        positivity
      rw [← ENNReal.ofReal_add hXpos.le hTnn, ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      -- the real inequality
      set a := displacementScale lam u with ha
      have ha0 : 0 < a := displacementScale_pos hlam u
      have haρ : a ≤ ρ := displacementScale_le_of_norm_le hρ hu
      have hs1 : a / ρ ≤ 1 := (div_le_one hρ0).2 haρ
      have hs0 : 0 ≤ a / ρ := by positivity
      have hconv := exp_mul_sq_le (C := c) hs0 hs1
      have hm : 0 < max ‖u‖ lam := lt_of_lt_of_le hlam (le_max_right _ _)
      have ham : a ≤ max ‖u‖ lam := by
        rw [ha, displacementScale]
        exact max_le_max (by linarith [norm_nonneg u]) le_rfl
      -- `x · e^X ≤ e^{2C₀}/ρ²`
      have hxX : (a / ρ) ^ 2 * X u ≤ Real.exp (2 * C₀) / ρ ^ 2 := by
        have e1 : X u ≤ Real.exp (2 * smearedKernel lam u) := by
          rw [hX]
          exact Real.exp_le_exp.2 (by have : 0 ≤ ‖u‖ ^ 2 / ℓ := by positivity
                                      linarith)
        have e2 := exp_two_mul_smearedKernel_le_div hC₀ hlam u
        have e3 : (a / ρ) ^ 2 ≤ max ‖u‖ lam ^ 2 / ρ ^ 2 := by
          rw [div_pow]
          gcongr
        calc (a / ρ) ^ 2 * X u ≤ (max ‖u‖ lam ^ 2 / ρ ^ 2) *
              (Real.exp (2 * C₀) / max ‖u‖ lam ^ 2) :=
              mul_le_mul e3 (e1.trans e2) hXpos.le (by positivity)
          _ = Real.exp (2 * C₀) / ρ ^ 2 := by
              field_simp
      have hKρ : (Real.exp 1 * (Real.exp c - 1)) * ((a / ρ) ^ 2 * X u) ≤ K / ρ ^ 2 := by
        have : 0 ≤ Real.exp 1 * (Real.exp c - 1) := by
          exact mul_nonneg (Real.exp_pos 1).le (by linarith only [Real.one_le_exp hc])
        calc (Real.exp 1 * (Real.exp c - 1)) * ((a / ρ) ^ 2 * X u)
            ≤ (Real.exp 1 * (Real.exp c - 1)) * (Real.exp (2 * C₀) / ρ ^ 2) :=
              mul_le_mul_of_nonneg_left hxX this
          _ = K / ρ ^ 2 := by rw [hK]; ring
      have hec : 0 ≤ Real.exp c - 1 := by have := Real.one_le_exp hc; linarith
      have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
      have hxnn : 0 ≤ (a / ρ) ^ 2 * X u := by positivity
      have hexp : Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ + c * (a / ρ) ^ 2 +
          (if R < ‖u‖ then 1 else 0)) =
          X u * Real.exp (c * (a / ρ) ^ 2) * Real.exp (if R < ‖u‖ then 1 else 0) := by
        rw [Real.exp_add, Real.exp_add]
      rw [hexp]
      by_cases hRu : R < ‖u‖
      · have hTu : T u = X u := by rw [hT]; dsimp only; rw [ite_eq_left hRu]
        rw [ite_eq_left hRu, hTu]
        have := mul_le_mul_of_nonneg_left hconv hXpos.le
        have h3 : X u * Real.exp (c * (a / ρ) ^ 2) * Real.exp 1 ≤
            X u * (1 + (Real.exp c - 1) * (a / ρ) ^ 2) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos 1).le
        linarith only [h3, hKρ]
      · have hTu : T u = 0 := by rw [hT]; dsimp only; rw [ite_eq_right hRu]
        rw [ite_eq_right hRu, hTu, Real.exp_zero, mul_one, mul_zero, add_zero]
        have := mul_le_mul_of_nonneg_left hconv hXpos.le
        have h4 : (Real.exp c - 1) * ((a / ρ) ^ 2 * X u) ≤
            (Real.exp 1 * (Real.exp c - 1)) * ((a / ρ) ^ 2 * X u) := by
          have h5 : 0 ≤ (Real.exp c - 1) * ((a / ρ) ^ 2 * X u) := mul_nonneg hec hxnn
          linarith only [mul_le_mul_of_nonneg_right he1 h5]
        linarith only [this, h4, hKρ]
    · rw [ite_eq_right hu]
      exact zero_le
  -- integrate
  have hint : ∫⁻ u, critNeutralWeight lam ℓ R c (u, ρ) ≤
      (∫⁻ u, ENNReal.ofReal (X u)) + (∫⁻ u, ENNReal.ofReal ((Real.exp 1 - 1) * T u)) +
        ∫⁻ u, (Metric.closedBall (0 : ℂ) (4 * ρ)).indicator
          (fun _ => ENNReal.ofReal (K / ρ ^ 2)) u := by
    refine (lintegral_mono hpt).trans (le_of_eq ?_)
    rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop)]
  have hB : ∫⁻ u, ENNReal.ofReal (X u) ≤ ENNReal.ofReal
      (2 * Real.pi * (ℓ + (1 / 2) * Real.log ℓ) + CB) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianMass hlam hle)
      (ae_of_all _ fun u => (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_le.1 (hCB lam hlam hle)).2
    linarith
  have hBR : ∫⁻ u, ENNReal.ofReal ((Real.exp 1 - 1) * T u) ≤ ENNReal.ofReal
      ((Real.exp 1 - 1) * (2 * Real.pi * ((1 / 2) * Real.log ℓ + Real.log (1 / R) + 1 / 2))) := by
    have he1 : 0 ≤ Real.exp 1 - 1 := by have := Real.one_le_exp zero_le_one; linarith
    have hTi : Integrable T := integrable_tail_gaussianMass hlam hle
    have hTnn : ∀ u, 0 ≤ T u := fun u => by
      rw [hT]
      dsimp only
      by_cases hRu : R < ‖u‖
      · rw [ite_eq_left hRu]; exact (Real.exp_pos _).le
      · rw [ite_eq_right hRu]
    rw [← ofReal_integral_eq_lintegral_ofReal (hTi.const_mul _)
      (ae_of_all _ fun u => mul_nonneg he1 (hTnn u))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_tail_gaussianMass_le hlam hle hR hR1) he1
  have hball := lintegral_indicator_closedBall_div_sq hρ0 hK0
  refine hint.trans ?_
  rw [hball]
  have hlogs : 0 ≤ (1 / 2) * Real.log ℓ + Real.log (1 / R) + 1 / 2 := by positivity
  have he1 : 0 ≤ Real.exp 1 - 1 := by have := Real.one_le_exp zero_le_one; linarith
  calc (∫⁻ u, ENNReal.ofReal (X u)) + (∫⁻ u, ENNReal.ofReal ((Real.exp 1 - 1) * T u)) +
        ENNReal.ofReal (16 * Real.pi * K)
      ≤ ENNReal.ofReal (2 * Real.pi * (ℓ + (1 / 2) * Real.log ℓ) + CB) +
          ENNReal.ofReal ((Real.exp 1 - 1) *
            (2 * Real.pi * ((1 / 2) * Real.log ℓ + Real.log (1 / R) + 1 / 2))) +
          ENNReal.ofReal (16 * Real.pi * K) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-! ### The same-sign pair -/

/-- **The same-sign pair** (source l. 1697, "Its integral is at most `C`"): for `0 < λ ≤ ρ`
and `c ≥ 0`, `∫ critSameSignWeight ≤ 256 π c`. -/
theorem lintegral_critSameSignWeight_le {lam c ρ : ℝ} (hlam : 0 < lam) (hρ : lam ≤ ρ)
    (hc : 0 ≤ c) :
    ∫⁻ u, critSameSignWeight lam c (u, ρ) ≤ ENNReal.ofReal (256 * Real.pi * c) := by
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  have hpt : ∀ u : ℂ, critSameSignWeight lam c (u, ρ) ≤
      (Metric.closedBall (0 : ℂ) (4 * ρ)).indicator
        (fun _ => ENNReal.ofReal (16 * c / ρ ^ 2)) u := by
    intro u
    unfold critSameSignWeight
    dsimp only
    by_cases hu : ‖u‖ ≤ 4 * ρ
    · rw [ite_eq_left hu]
      have hmem : u ∈ Metric.closedBall (0 : ℂ) (4 * ρ) := by simpa using hu
      rw [indicator_of_mem hmem]
      refine ENNReal.ofReal_le_ofReal ?_
      have hm : max ‖u‖ lam ≤ 4 * ρ := max_le hu (by linarith)
      have hm0 : 0 ≤ max ‖u‖ lam := (norm_nonneg u).trans (le_max_left _ _)
      have hsq : max ‖u‖ lam ^ 2 ≤ 16 * ρ ^ 2 :=
        calc max ‖u‖ lam ^ 2 ≤ (4 * ρ) ^ 2 := pow_le_pow_left₀ hm0 hm 2
          _ = 16 * ρ ^ 2 := by ring
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : c * max ‖u‖ lam ^ 2 ≤ c * (16 * ρ ^ 2) := mul_le_mul_of_nonneg_left hsq hc
      linarith only [mul_le_mul_of_nonneg_right this (sq_nonneg ρ)]
    · rw [ite_eq_right hu]
      exact zero_le
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_indicator_closedBall_div_sq hρ0 (by positivity)]
  congr 1
  ring

end TwoComponentCoulomb

end
