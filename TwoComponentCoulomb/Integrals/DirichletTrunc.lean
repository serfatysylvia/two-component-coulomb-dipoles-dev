/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TwoComponentCoulomb.Integrals.Dirichlet
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Truncated Dirichlet-type integrals: the exponential Markov bound

Tools for integrals over the truncated simplex `{t ∈ ℝ^p | Σ t_i < s}`, used for the critical
weight `t⁻¹ 1_{t ≥ λ}` in `UpperBound/NearestNeighborModelCritical.lean`.

* `DirichletTrunc.lintegral_markov_prod` : the exponential Markov bound
  `1_{Σ t_i < s} ≤ e^{u (s - Σ t_i)}`, which also factorises the integral over `Fin p → ℝ`.
* `DirichletTrunc.lintegral_Ici_inv_exp` : the one-dimensional integral
  `∫_λ^∞ t⁻¹ e^{-u t} dt` for `λ ≤ 1/u`, bounded directly instead of by integration by parts.
* `DirichletTrunc.log_facts` : elementary facts about `ℓ ≥ log 2`.
-/

public section

namespace TwoComponentCoulomb

open MeasureTheory Set
open scoped ENNReal

namespace DirichletTrunc

/-! ### Exponential Markov bound and factorisation -/

/-- Measurability of the integration domain `{t | (∀ i, t i ∈ S) ∧ Σ t_i < s}`. -/
theorem measurableSet_pi_mem_sum_lt {S : Set ℝ} (hS : MeasurableSet S) (p : ℕ) (s : ℝ) :
    MeasurableSet {t : Fin p → ℝ | (∀ i, t i ∈ S) ∧ ∑ i, t i < s} := by
  have h1 : MeasurableSet {t : Fin p → ℝ | ∀ i, t i ∈ S} := by
    have : {t : Fin p → ℝ | ∀ i, t i ∈ S} = ⋂ i, (fun t : Fin p → ℝ => t i) ⁻¹' S := by
      ext; simp
    rw [this]
    exact MeasurableSet.iInter fun i => measurable_pi_apply i hS
  have h2 : MeasurableSet {t : Fin p → ℝ | ∑ i, t i < s} :=
    measurableSet_lt (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const
  exact h1.inter h2

/-- Exponential Markov bound combined with the factorisation of the product integral. -/
theorem lintegral_markov_prod (p : ℕ) {S : Set ℝ} (hS : MeasurableSet S) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) {u : ℝ} (hu : 0 ≤ u) (s : ℝ) :
    ∫⁻ t in {t : Fin p → ℝ | (∀ i, t i ∈ S) ∧ ∑ i, t i < s}, ∏ i, g (t i) ≤
      ENNReal.ofReal (Real.exp (u * s)) *
        (∫⁻ x in S, g x * ENNReal.ofReal (Real.exp (-(u * x)))) ^ p := by
  set T : Set (Fin p → ℝ) := {t | (∀ i, t i ∈ S) ∧ ∑ i, t i < s} with hT
  have hTm : MeasurableSet T := measurableSet_pi_mem_sum_lt hS p s
  set h : ℝ → ℝ≥0∞ := S.indicator fun x => g x * ENNReal.ofReal (Real.exp (-(u * x))) with hh
  have hhm : Measurable h := by
    refine Measurable.indicator ?_ hS
    exact hg.mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  rw [← lintegral_indicator hTm]
  calc ∫⁻ t, T.indicator (fun t => ∏ i, g (t i)) t
      ≤ ∫⁻ t : Fin p → ℝ, ENNReal.ofReal (Real.exp (u * s)) * ∏ i, h (t i) := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ T
        · rw [indicator_of_mem ht]
          have hprod : ∏ i, h (t i) =
              (∏ i, g (t i)) * ENNReal.ofReal (Real.exp (-(u * ∑ i, t i))) := by
            have : ∀ i, h (t i) = g (t i) * ENNReal.ofReal (Real.exp (-(u * t i))) := fun i =>
              indicator_of_mem (ht.1 i) _
            simp_rw [this, Finset.prod_mul_distrib]
            congr 1
            rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
            congr 2
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          rw [hprod, mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          calc ∏ i, g (t i) = (∏ i, g (t i)) * 1 := (mul_one _).symm
            _ ≤ _ := by
              gcongr
              rw [← ENNReal.ofReal_one]
              refine ENNReal.ofReal_le_ofReal ?_
              rw [Real.one_le_exp_iff]
              have : u * ∑ i, t i ≤ u * s := mul_le_mul_of_nonneg_left ht.2.le hu
              linarith
        · rw [indicator_of_notMem ht]; exact bot_le
    _ = ENNReal.ofReal (Real.exp (u * s)) *
          (∫⁻ x in S, g x * ENNReal.ofReal (Real.exp (-(u * x)))) ^ p := by
        rw [lintegral_const_mul _ (by fun_prop : Measurable fun t : Fin p → ℝ => ∏ i, h (t i)),
          Dirichlet.lintegral_pi_prod_fin p hhm, lintegral_indicator hS]

/-! ### One-dimensional integrals -/

/-- `exp (-(u x))` is integrable on `(c, ∞)` for `u > 0`. -/
theorem integrableOn_exp_neg_mul_Ioi {u : ℝ} (hu : 0 < u) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(u * x))) (Ioi c) := by
  simpa using integrableOn_exp_mul_Ioi (a := -u) (by linarith) c

/-- A `lintegral` over `(a, b]` of a nonnegative interval-integrable function is an interval
integral. -/
theorem lintegral_Ioc_ofReal_eq {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hnn : ∀ x ∈ Ioc a b, 0 ≤ f x) :
    ∫⁻ x in Ioc a b, ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x in a..b, f x) := by
  rw [intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
  · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hnn)

/-- Part of the integral for `δ = 0` over `[λ, 1/u]`: bounded by `log (X/λ)`. -/
theorem lintegral_partA_zero {lam X u : ℝ} (hlam : 0 < lam) (hX : lam ≤ X) (hu : 0 < u) :
    ∫⁻ x in Ioc lam X, ENNReal.ofReal (x⁻¹ * Real.exp (-(u * x))) ≤
      ENNReal.ofReal (Real.log (X / lam)) := by
  have hX0 : 0 < X := lt_of_lt_of_le hlam hX
  calc ∫⁻ x in Ioc lam X, ENNReal.ofReal (x⁻¹ * Real.exp (-(u * x)))
      ≤ ∫⁻ x in Ioc lam X, ENNReal.ofReal (x⁻¹) := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ENNReal.ofReal_le_ofReal ?_
        have hx0 : 0 < x := lt_trans hlam hx.1
        have : 0 ≤ x⁻¹ := inv_nonneg.2 hx0.le
        have h2 : Real.exp (-(u * x)) ≤ 1 :=
          Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_pos hu hx0).le)
        exact mul_le_of_le_one_right this h2
    _ = ENNReal.ofReal (∫ x in lam..X, x⁻¹) := by
        refine lintegral_Ioc_ofReal_eq hX ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hX]
          exact continuousOn_inv₀.mono fun x hx => (lt_of_lt_of_le hlam hx.1).ne'
        · intro x hx; exact inv_nonneg.2 (lt_trans hlam hx.1).le
    _ = ENNReal.ofReal (Real.log (X / lam)) := by rw [integral_inv_of_pos hlam hX0]

/-- Tail of the integral for `δ = 0` over `[1/u, ∞)`: bounded by `1`. -/
theorem lintegral_partB_zero {u : ℝ} (hu : 0 < u) :
    ∫⁻ x in Ioi u⁻¹, ENNReal.ofReal (x⁻¹ * Real.exp (-(u * x))) ≤ 1 := by
  have hint : IntegrableOn (fun x : ℝ => u * Real.exp (-(u * x))) (Ioi u⁻¹) :=
    (integrableOn_exp_neg_mul_Ioi hu _).const_mul u
  calc ∫⁻ x in Ioi u⁻¹, ENNReal.ofReal (x⁻¹ * Real.exp (-(u * x)))
      ≤ ∫⁻ x in Ioi u⁻¹, ENNReal.ofReal (u * Real.exp (-(u * x))) := by
        refine setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal ?_
        have h1 : x⁻¹ ≤ u := by
          have hx0 : 0 < x := lt_trans (inv_pos.2 hu) hx
          rw [inv_le_comm₀ hx0 hu]; exact hx.le
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = ENNReal.ofReal (∫ x in Ioi u⁻¹, u * Real.exp (-(u * x))) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        exact (ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall fun x _ => by positivity)
    _ ≤ 1 := by
        have := integral_exp_mul_Ioi (a := -u) (by linarith) u⁻¹
        simp only [neg_mul] at this
        rw [integral_const_mul, this]
        rw [show u * (-Real.exp (-(u * u⁻¹)) / -u) = Real.exp (-(u * u⁻¹)) by field_simp]
        rw [mul_inv_cancel₀ hu.ne', ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.exp_le_one_iff]; norm_num

/-- Splitting `[λ, ∞)` at `X ≥ λ`. -/
theorem lintegral_Ici_split {lam X : ℝ} (hlX : lam ≤ X) (F : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ici lam, F x = (∫⁻ x in Ioc lam X, F x) + ∫⁻ x in Ioi X, F x := by
  rw [← setLIntegral_congr Ioi_ae_eq_Ici, ← Ioc_union_Ioi_eq_Ioi hlX,
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]

/-- The one-dimensional integral for `δ = 0`. -/
theorem lintegral_Ici_inv_exp {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) (hlu : lam ≤ u⁻¹) :
    ∫⁻ x in Ici lam, ENNReal.ofReal (x⁻¹ * Real.exp (-(u * x))) ≤
      ENNReal.ofReal (Real.log (u⁻¹ / lam) + 1) := by
  have hm0 : 0 ≤ Real.log (u⁻¹ / lam) := Real.log_nonneg ((one_le_div hlam).2 hlu)
  rw [lintegral_Ici_split hlu]
  calc _ ≤ ENNReal.ofReal (Real.log (u⁻¹ / lam)) + 1 :=
        add_le_add (lintegral_partA_zero hlam hlu hu) (lintegral_partB_zero hu)
    _ = ENNReal.ofReal (Real.log (u⁻¹ / lam) + 1) := by
        rw [ENNReal.ofReal_add hm0 zero_le_one, ENNReal.ofReal_one]

/-! ### Elementary real estimates -/

/-- Elementary facts about `ℓ ≥ log 2`. -/
theorem log_facts {ℓ : ℝ} (hℓ : Real.log 2 ≤ ℓ) :
    2 / 3 ≤ ℓ ∧ 1 / 2 ≤ 1 + Real.log ℓ ∧ 1 + Real.log ℓ ≤ ℓ ∧
      0 ≤ Real.log (1 + ℓ) ∧ Real.log (1 + ℓ) ≤ 2 * (1 + Real.log ℓ) := by
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have hℓ0 : 0 < ℓ := by linarith
  have h1 : 2 / 3 ≤ ℓ := by linarith
  have h2l : 1 / 2 ≤ 1 + Real.log ℓ := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hℓ0)
    rw [Real.log_inv] at this
    have h3 : ℓ⁻¹ ≤ 3 / 2 := by
      rw [inv_le_comm₀ hℓ0 (by norm_num)]; linarith
    linarith
  have h3 : 1 + Real.log ℓ ≤ ℓ := by
    have := Real.log_le_sub_one_of_pos hℓ0; linarith
  have h4 : 0 ≤ Real.log (1 + ℓ) := Real.log_nonneg (by linarith)
  refine ⟨h1, h2l, h3, h4, ?_⟩
  rcases le_total ℓ 1 with h | h
  · have : Real.log (1 + ℓ) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
    linarith
  · have : Real.log (1 + ℓ) ≤ Real.log (2 * ℓ) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hℓ0.ne'] at this
    linarith

end DirichletTrunc

end TwoComponentCoulomb

end
