/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Beta
import TwoComponentCoulomb.Integrals.Stirling
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Dirichlet integrals (Lemma 3.1)

Source lines 608–643 (Lemma `lemdirichlet`).

* `lintegral_dirichlet`: the exact value (eq:ind I) of the Dirichlet integral
  `I_{k,s}(α₁, …, α_k) = ∫_{(ℝ⁺)^k} 1_{Σ t_i < s} ∏ t_i^{α_i - 1} dt`, as a `lintegral` over
  `Fin k → ℝ`. The proof peels off one coordinate (Fubini) and uses the scaled Beta integral.
* `dirichletTwoLevel` is `I_{k,s}` for the exponent vector `(α₀, …, α₀, 1, …, 1)` with `α₀`
  repeated `k₀` times. `dirichletTwoLevel_log_estimate` is the Stirling-type estimate
  (eq:estimate Dirichlet) and `dirichletTwoLevel_le` is the final upper bound of Lemma 3.1.
  The logarithmic estimate uses the factorial Stirling formula, extended to real arguments
  by monotonicity and log-convexity of Gamma. The final upper bound uses
  `(x/e)^x ≤ Γ(x+1)`, as in the manuscript.
* Generic tools (Fubini on `Fin (k+1) → ℝ`, factorisation of product integrals, scaling on `ℝ`)
  live in the sub-namespace `TwoComponentCoulomb.Integrals.Dirichlet`.

All "O(·)" terms of the source are explicit constants quantified before `k`, `k₀`, `s`.
-/

public section

namespace TwoComponentCoulomb

open MeasureTheory Set
open scoped ENNReal

/-- The open simplex `{t ∈ (0,∞)^k | t₁ + ⋯ + t_k < s}` (the domain of the Dirichlet integral
`I_{k,s}` of source the definition of the Dirichlet integral). -/
@[expose] def posSimplex (k : ℕ) (s : ℝ) : Set (Fin k → ℝ) :=
  {t | (∀ i, 0 < t i) ∧ ∑ i, t i < s}

/-- The open simplex is measurable. -/
theorem measurableSet_posSimplex (k : ℕ) (s : ℝ) : MeasurableSet (posSimplex k s) := by
  have h1 : MeasurableSet {t : Fin k → ℝ | ∀ i, 0 < t i} := by
    have : {t : Fin k → ℝ | ∀ i, 0 < t i} = ⋂ i, {t | 0 < t i} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
  have h2 : MeasurableSet {t : Fin k → ℝ | ∑ i, t i < s} :=
    measurableSet_lt (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const
  exact h1.inter h2

/-- The open simplex is empty for `s ≤ 0`. -/
theorem posSimplex_eq_empty_of_nonpos (k : ℕ) {s : ℝ} (hs : s ≤ 0) : posSimplex k s = ∅ := by
  refine eq_empty_of_forall_notMem fun t ht => ?_
  have : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i _ => (ht.1 i).le
  exact absurd (ht.2.trans_le hs) (not_lt.2 this)

/-- Membership in the simplex after peeling off the first coordinate. -/
theorem cons_mem_posSimplex_iff {k : ℕ} (x : ℝ) (t : Fin k → ℝ) (s : ℝ) :
    (Fin.cons x t : Fin (k + 1) → ℝ) ∈ posSimplex (k + 1) s ↔ 0 < x ∧ t ∈ posSimplex k (s - x) := by
  simp only [posSimplex, mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ]
  constructor
  · rintro ⟨⟨h0, h⟩, hs⟩
    exact ⟨h0, h, by linarith⟩
  · rintro ⟨h0, h, hs⟩
    exact ⟨⟨h0, h⟩, by linarith⟩

namespace Dirichlet

/-- **Fubini on `Fin (k+1) → ℝ`**: peel off the first coordinate. -/
theorem lintegral_fin_succ {k : ℕ} {F : (Fin (k + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ t, F t = ∫⁻ x : ℝ, ∫⁻ t' : Fin k → ℝ, F (Fin.cons x t') := by
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) F]
  rw [Measure.volume_eq_prod, lintegral_prod]
  · refine lintegral_congr fun x => lintegral_congr fun t' => ?_
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp [Fin.insertNthEquiv]
  · exact (hF.comp (MeasurableEquiv.measurable _)).aemeasurable

/-- The `lintegral` of a product of functions of the individual coordinates over `Fin p → ℝ`
is the `p`-th power of the one-dimensional `lintegral`. -/
theorem lintegral_pi_prod_fin (p : ℕ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t : Fin p → ℝ, ∏ i, g (t i) = (∫⁻ x, g x) ^ p := by
  induction p with
  | zero => simp [volume_pi]
  | succ p ih =>
    rw [lintegral_fin_succ (by fun_prop)]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [lintegral_const_mul _ (by fun_prop : Measurable fun t' : Fin p → ℝ => ∏ i, g (t' i)),
      ih]
    rw [lintegral_mul_const _ hg, pow_succ, mul_comm]

/-- Scaling on `ℝ`: `∫ H(y) dy = s ∫ H(s v) dv` for `s > 0`. -/
theorem lintegral_comp_mul_left_real {s : ℝ} (hs : 0 < s) (H : ℝ → ℝ≥0∞) :
    ∫⁻ y, H y = ENNReal.ofReal s * ∫⁻ v, H (s * v) := by
  have h := Real.map_volume_mul_left hs.ne'
  have h2 : ∫⁻ y, H y ∂(Measure.map (fun x => s * x) volume) = ∫⁻ v, H (s * v) :=
    (measurableEmbedding_mulLeft₀ hs.ne').lintegral_map H
  rw [h, lintegral_smul_measure] at h2
  rw [← h2, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hs.le, abs_of_pos (inv_pos.2 hs),
    mul_inv_cancel₀ hs.ne']
  simp

/-- The Beta integral `∫₀¹ x^{a-1}(1-x)^{b-1} dx = Γ(a)Γ(b)/Γ(a+b)` as a `lintegral`. -/
theorem lintegral_beta_Ioo {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      ENNReal.ofReal (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) := by
  have h1 := ProbabilityTheory.lintegral_betaPDF_eq_one ha hb
  rw [ProbabilityTheory.lintegral_betaPDF] at h1
  have hbeta := ProbabilityTheory.beta_pos ha hb
  have : ∀ x ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (1 / ProbabilityTheory.beta a b * x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      ENNReal.ofReal (1 / ProbabilityTheory.beta a b) *
        ENNReal.ofReal (x ^ (a - 1) * (1 - x) ^ (b - 1)) := by
    intro x hx
    rw [mul_assoc, ENNReal.ofReal_mul (by positivity)]
  rw [setLIntegral_congr_fun measurableSet_Ioo this,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
  have h2 : ENNReal.ofReal (1 / ProbabilityTheory.beta a b) *
      ENNReal.ofReal (ProbabilityTheory.beta a b) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hbeta.ne']; simp
  have h3 : ENNReal.ofReal (1 / ProbabilityTheory.beta a b) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  exact (ENNReal.mul_right_inj h3 ENNReal.ofReal_ne_top).1 (h1.trans h2.symm)

/-- The scaled Beta integral `∫₀ˢ x^{a-1}(s-x)^{b-1} dx = s^{a+b-1} Γ(a)Γ(b)/Γ(a+b)`. -/
theorem lintegral_Ioo_rpow_mul_rpow {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    ∫⁻ x in Ioo (0 : ℝ) s, ENNReal.ofReal (x ^ (a - 1) * (s - x) ^ (b - 1)) =
      ENNReal.ofReal (s ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b))) := by
  rw [← lintegral_indicator measurableSet_Ioo, lintegral_comp_mul_left_real hs]
  have key : ∀ v : ℝ, (Ioo (0 : ℝ) s).indicator
        (fun x => ENNReal.ofReal (x ^ (a - 1) * (s - x) ^ (b - 1))) (s * v) =
      (Ioo (0 : ℝ) 1).indicator
        (fun v => ENNReal.ofReal (s ^ (a + b - 2) * (v ^ (a - 1) * (1 - v) ^ (b - 1)))) v := by
    intro v
    by_cases hv : v ∈ Ioo (0 : ℝ) 1
    · have hv' : s * v ∈ Ioo (0 : ℝ) s := ⟨mul_pos hs hv.1, by nlinarith [hv.2]⟩
      rw [indicator_of_mem hv', indicator_of_mem hv]
      congr 1
      have h1 : s - s * v = s * (1 - v) := by ring
      rw [h1, Real.mul_rpow hs.le hv.1.le, Real.mul_rpow hs.le (by linarith [hv.2])]
      have : s ^ (a + b - 2) = s ^ (a - 1) * s ^ (b - 1) := by
        rw [← Real.rpow_add hs]; congr 1; ring
      rw [this]; ring
    · have hv' : s * v ∉ Ioo (0 : ℝ) s := by
        intro h
        exact hv ⟨pos_of_mul_pos_right h.1 hs.le, by nlinarith [h.2]⟩
      rw [indicator_of_notMem hv', indicator_of_notMem hv]
  simp_rw [key]
  rw [lintegral_indicator measurableSet_Ioo]
  have h2 : ∀ v : ℝ, ENNReal.ofReal (s ^ (a + b - 2) * (v ^ (a - 1) * (1 - v) ^ (b - 1))) =
      ENNReal.ofReal (s ^ (a + b - 2)) * ENNReal.ofReal (v ^ (a - 1) * (1 - v) ^ (b - 1)) := by
    intro v
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_beta_Ioo ha hb,
    ← mul_assoc, ← ENNReal.ofReal_mul hs.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : s ^ (a + b - 1) = s * s ^ (a + b - 2) := by
    conv_lhs => rw [show a + b - 1 = 1 + (a + b - 2) by ring, Real.rpow_add hs, Real.rpow_one]
  rw [this]

/-- The recursion for the Dirichlet integral: peel off the first coordinate. -/
theorem lintegral_posSimplex_succ {k : ℕ} (α : Fin (k + 1) → ℝ) (s : ℝ) :
    ∫⁻ t in posSimplex (k + 1) s, ENNReal.ofReal (∏ i, t i ^ (α i - 1)) =
      ∫⁻ x, (Ioi (0 : ℝ)).indicator (fun x => ENNReal.ofReal (x ^ (α 0 - 1))) x *
        ∫⁻ t in posSimplex k (s - x), ENNReal.ofReal (∏ i, t i ^ (α i.succ - 1)) := by
  rw [← lintegral_indicator (measurableSet_posSimplex _ _)]
  rw [lintegral_fin_succ (by
    refine Measurable.indicator ?_ (measurableSet_posSimplex _ _)
    fun_prop)]
  refine lintegral_congr fun x => ?_
  have hmeas : Measurable fun t : Fin k → ℝ =>
      (posSimplex k (s - x)).indicator
        (fun t => ENNReal.ofReal (∏ i, t i ^ (α i.succ - 1))) t := by
    refine Measurable.indicator ?_ (measurableSet_posSimplex _ _)
    fun_prop
  rw [← lintegral_indicator (measurableSet_posSimplex _ _), ← lintegral_const_mul _ hmeas]
  refine lintegral_congr fun t => ?_
  by_cases hx : 0 < x ∧ t ∈ posSimplex k (s - x)
  · rw [indicator_of_mem ((cons_mem_posSimplex_iff x t s).2 hx),
      indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx.1), indicator_of_mem hx.2]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hx.1.le _)]
  · rw [indicator_of_notMem (fun h => hx ((cons_mem_posSimplex_iff x t s).1 h))]
    by_cases hx0 : 0 < x
    · rw [indicator_of_notMem (fun h => hx ⟨hx0, h⟩), mul_zero]
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx0), zero_mul]

/-- **Dirichlet integrals of type 1**, in the form `s^A ∏ Γ(α_i) / Γ(A + 1)` valid for every
`k ≥ 0`. -/
theorem lintegral_posSimplex_eq_aux (k : ℕ) :
    ∀ (α : Fin k → ℝ), (∀ i, 0 < α i) → ∀ s : ℝ, 0 < s →
      ∫⁻ t in posSimplex k s, ENNReal.ofReal (∏ i, t i ^ (α i - 1)) =
        ENNReal.ofReal (s ^ (∑ i, α i) * (∏ i, Real.Gamma (α i)) / Real.Gamma (∑ i, α i + 1)) := by
  induction k with
  | zero =>
    intro α _ s hs
    have : posSimplex 0 s = univ := by
      ext t; simp [posSimplex, hs]
    simp [this, volume_pi]
  | succ k ih =>
    intro α hα s hs
    rw [lintegral_posSimplex_succ]
    set A := ∑ i : Fin k, α i.succ with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => (hα _).le
    have hinner : ∀ x : ℝ, (Ioi (0 : ℝ)).indicator (fun x => ENNReal.ofReal (x ^ (α 0 - 1))) x *
        ∫⁻ t in posSimplex k (s - x), ENNReal.ofReal (∏ i, t i ^ (α i.succ - 1)) =
        (Ioo 0 s).indicator (fun x => ENNReal.ofReal (
          x ^ (α 0 - 1) * (s - x) ^ (A + 1 - 1) *
            ((∏ i : Fin k, Real.Gamma (α i.succ)) / Real.Gamma (A + 1)))) x := by
      intro x
      by_cases hx : x ∈ Ioo 0 s
      · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx.1),
          ih (fun i => α i.succ) (fun i => hα _) (s - x) (by linarith [hx.2])]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.1.le _)]
        congr 1
        simp only [add_sub_cancel_right]
        ring
      · rw [indicator_of_notMem hx]
        by_cases hx0 : 0 < x
        · have : s - x ≤ 0 := by
            by_contra h
            exact hx ⟨hx0, by linarith⟩
          rw [posSimplex_eq_empty_of_nonpos k this]
          simp
        · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx0), zero_mul]
    simp_rw [hinner]
    rw [lintegral_indicator measurableSet_Ioo]
    have hc : ∀ x ∈ Ioo (0 : ℝ) s, ENNReal.ofReal (x ^ (α 0 - 1) * (s - x) ^ (A + 1 - 1) *
        ((∏ i : Fin k, Real.Gamma (α i.succ)) / Real.Gamma (A + 1))) =
        ENNReal.ofReal ((∏ i : Fin k, Real.Gamma (α i.succ)) / Real.Gamma (A + 1)) *
          ENNReal.ofReal (x ^ (α 0 - 1) * (s - x) ^ (A + 1 - 1)) := by
      intro x hx
      rw [mul_comm, ENNReal.ofReal_mul (div_nonneg
        (Finset.prod_nonneg fun i _ => (Real.Gamma_pos_of_pos (hα _)).le)
        (Real.Gamma_pos_of_pos (by linarith)).le)]
    rw [setLIntegral_congr_fun measurableSet_Ioo hc,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_Ioo_rpow_mul_rpow (hα 0) (by linarith) hs, ← ENNReal.ofReal_mul (div_nonneg
        (Finset.prod_nonneg fun i _ => (Real.Gamma_pos_of_pos (hα _)).le)
        (Real.Gamma_pos_of_pos (by linarith)).le)]
    congr 1
    have hΓ : 0 < Real.Gamma (A + 1) := Real.Gamma_pos_of_pos (by linarith)
    have hΓ2 : 0 < Real.Gamma (α 0 + (A + 1)) := Real.Gamma_pos_of_pos (by linarith [hα 0])
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ, ← hA,
      show α 0 + (A + 1) - 1 = α 0 + A by ring, show α 0 + A + 1 = α 0 + (A + 1) by ring]
    field_simp

end Dirichlet

open Dirichlet

/-- **Lemma 3.1, (eq:ind I)**: the Dirichlet integral
`I_{k,s}(α₁, …, α_k) = s^{Σα} ∏ Γ(α_i) / Γ(Σα) / Σα`. -/
theorem lintegral_dirichlet (k : ℕ) (hk : 1 ≤ k) (α : Fin k → ℝ) (hα : ∀ i, 0 < α i) {s : ℝ}
    (hs : 0 < s) :
    ∫⁻ t in {t : Fin k → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < s},
        ENNReal.ofReal (∏ i, t i ^ (α i - 1)) =
      ENNReal.ofReal (s ^ (∑ i, α i) * (∏ i, Real.Gamma (α i)) / Real.Gamma (∑ i, α i) /
        (∑ i, α i)) := by
  have hA : 0 < ∑ i, α i :=
    Finset.sum_pos (fun i _ => hα i) (Finset.univ_nonempty_iff.2 ⟨⟨0, hk⟩⟩)
  have := lintegral_posSimplex_eq_aux k α hα s hs
  rw [Real.Gamma_add_one hA.ne'] at this
  rw [show {t : Fin k → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < s} = posSimplex k s from rfl, this]
  congr 1
  have : 0 < Real.Gamma (∑ i, α i) := Real.Gamma_pos_of_pos hA
  field_simp

namespace Dirichlet

/-! ### Gamma bounds and Stirling interpolation -/


/-- `exp (-t)` is integrable on `(c, ∞)`. -/
theorem integrableOn_exp_neg_Ioi (c : ℝ) : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi c) := by
  simpa using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) c

/-- Lower bound `Γ(x+1) ≥ (x/e)^x = x^x e^{-x}` for `x > 0` (restrict the Gamma integral to
`(x, ∞)`, where `t^x ≥ x^x`); it is the bound quoted at the end of the proof of Lemma 3.1. -/
theorem rpow_mul_exp_neg_le_Gamma_add_one {x : ℝ} (hx : 0 < x) :
    x ^ x * Real.exp (-x) ≤ Real.Gamma (x + 1) := by
  have hint := Real.GammaIntegral_convergent (s := x + 1) (by linarith)
  simp only [add_sub_cancel_right] at hint
  rw [Real.Gamma_eq_integral (by linarith), add_sub_cancel_right]
  calc x ^ x * Real.exp (-x) = ∫ t in Ioi x, Real.exp (-t) * x ^ x := by
        rw [integral_mul_const, integral_exp_neg_Ioi]; ring
    _ ≤ ∫ t in Ioi x, Real.exp (-t) * t ^ x := by
        refine setIntegral_mono_on ?_ (hint.mono_set (Ioi_subset_Ioi hx.le)) measurableSet_Ioi ?_
        · exact (integrableOn_exp_neg_Ioi x).mul_const (x ^ x)
        · intro t ht
          have := Real.rpow_le_rpow hx.le (le_of_lt ht) hx.le
          gcongr
    _ ≤ ∫ t in Ioi 0, Real.exp (-t) * t ^ x := by
        refine setIntegral_mono_set hint ?_ ?_
        · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
          have := Real.rpow_nonneg (le_of_lt (show (0:ℝ) < t from ht)) x
          positivity
        · exact Filter.Eventually.of_forall (Ioi_subset_Ioi hx.le)

/-- The logarithmic real-Gamma Stirling estimate needed for the Dirichlet quotient.
For `x ≥ 1`, monotonicity interpolates the factorial Stirling bound at `ceil x`.
For `0 < x ≤ 1`, log-convexity between `Γ(1) = Γ(2) = 1` supplies the bound. -/
theorem log_Gamma_add_one_le_stirling {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma (x + 1)) ≤ x * Real.log x - x + 1 + 2 * Real.log (x + 1) := by
  have hlower : -1 ≤ x * Real.log x - x := by
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hx) hx.le
    rw [mul_sub, mul_inv_cancel₀ hx.ne'] at h
    linarith only [h]
  rcases le_or_gt x 1 with hx1 | hx1
  · have hconv := Real.convexOn_log_Gamma.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (show (2 : ℝ) ∈ Ioi 0 by norm_num) (sub_nonneg.2 hx1) hx.le (by ring : 1 - x + x = 1)
    have hid : (1 - x) * 1 + x * 2 = x + 1 := by ring
    simp only [smul_eq_mul, Function.comp_apply, hid, Real.Gamma_one, Real.Gamma_two,
      Real.log_one, mul_zero, add_zero] at hconv
    have hlog : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    linarith only [hconv, hlower, hlog]
  · let n := Nat.ceil x
    have hxn : x ≤ (n : ℝ) := Nat.le_ceil x
    have hnx : (n : ℝ) < x + 1 := Nat.ceil_lt_add_one hx.le
    have hn : 1 ≤ n := Nat.one_le_ceil_iff.2 hx
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hg : Real.log (Real.Gamma (x + 1)) ≤ Real.log (n.factorial : ℝ) := by
      rw [← Real.Gamma_nat_eq_factorial]
      apply Real.log_le_log (Real.Gamma_pos_of_pos (by linarith))
      exact Real.Gamma_strictMonoOn_Ici.monotoneOn (by change 2 ≤ x + 1; linarith)
        (by change 2 ≤ (n : ℝ) + 1; linarith) (by linarith)
    have hs := log_factorial_stirling_le hn
    have hlog : Real.log (n : ℝ) - Real.log x ≤ (n : ℝ) / x - 1 := by
      rw [← Real.log_div hn0.ne' hx.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hn0 hx)
    have hmul : x * (Real.log (n : ℝ) - Real.log x) ≤ (n : ℝ) - x := by
      have h := mul_le_mul_of_nonneg_left hlog hx.le
      have hid : x * ((n : ℝ) / x - 1) = (n : ℝ) - x := by field_simp
      linarith only [h, hid]
    have hln0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hdiff : ((n : ℝ) - x) * Real.log n ≤ Real.log n :=
      mul_le_of_le_one_left hln0 (by linarith only [hnx])
    have hln : Real.log (n : ℝ) ≤ Real.log (x + 1) := Real.log_le_log hn0 hnx.le
    have hlx : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    linarith only [hg, hs, hmul, hdiff, hln, hlx]

/-- Number of indices `i < k₀` in `Fin k`. -/
theorem card_filter_val_lt_fin (k k₀ : ℕ) (h : k₀ ≤ k) :
    (Finset.univ.filter (fun i : Fin k => (i : ℕ) < k₀)).card = k₀ := by
  rw [Fin.card_filter_val_lt]; exact min_eq_right h

/-- Number of indices `i ≥ k₀` in `Fin k`. -/
theorem card_filter_not_val_lt_fin (k k₀ : ℕ) (h : k₀ ≤ k) :
    (Finset.univ.filter (fun i : Fin k => ¬ (i : ℕ) < k₀)).card = k - k₀ := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (fun i : Fin k => (i : ℕ) < k₀)
  rw [card_filter_val_lt_fin k k₀ h, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- Sum of the two-level exponent vector. -/
theorem sum_ite_val_lt (α₀ : ℝ) (k k₀ : ℕ) (h : k₀ ≤ k) :
    ∑ i : Fin k, (if (i : ℕ) < k₀ then α₀ else 1) = α₀ * k₀ + (k - k₀ : ℕ) := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, card_filter_val_lt_fin k k₀ h,
    card_filter_not_val_lt_fin k k₀ h]
  simp [mul_comm]

/-- Product of a two-level family with second value `1`. -/
theorem prod_ite_val_lt (a : ℝ) (k k₀ : ℕ) (h : k₀ ≤ k) :
    ∏ i : Fin k, (if (i : ℕ) < k₀ then a else 1) = a ^ k₀ := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, card_filter_val_lt_fin k k₀ h]
  simp

/-- The Dirichlet integral for the two-level exponent vector, valid for every `k₀ ≤ k`. -/
theorem lintegral_dirichlet_two_level {α₀ : ℝ} (hα₀ : 0 < α₀) (k k₀ : ℕ) (hk₀ : k₀ ≤ k)
    {s : ℝ} (hs : 0 < s) :
    ∫⁻ t in {t : Fin k → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < s},
        ENNReal.ofReal (∏ i, t i ^ ((if (i : ℕ) < k₀ then α₀ else 1) - 1)) =
      ENNReal.ofReal (s ^ (α₀ * k₀ + ((k : ℝ) - k₀)) * Real.Gamma α₀ ^ k₀ /
        Real.Gamma (α₀ * k₀ + ((k : ℝ) - k₀) + 1)) := by
  have hpos : ∀ i : Fin k, 0 < (if (i : ℕ) < k₀ then α₀ else 1) := by
    intro i; split_ifs <;> [exact hα₀; exact one_pos]
  have hvalue : ∫⁻ t in posSimplex k s,
      ENNReal.ofReal (∏ i, t i ^ ((if (i : ℕ) < k₀ then α₀ else 1) - 1)) =
      ENNReal.ofReal (s ^ (∑ i : Fin k, if (i : ℕ) < k₀ then α₀ else 1) *
        (∏ i : Fin k, Real.Gamma (if (i : ℕ) < k₀ then α₀ else 1)) /
        Real.Gamma ((∑ i : Fin k, if (i : ℕ) < k₀ then α₀ else 1) + 1)) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact lintegral_posSimplex_eq_aux 0 _ hpos s hs
    · have h := lintegral_dirichlet k hk _ hpos hs
      have hsum : 0 < ∑ i : Fin k, if (i : ℕ) < k₀ then α₀ else 1 :=
        Finset.sum_pos (fun i _ => hpos i) (Finset.univ_nonempty_iff.2 ⟨⟨0, hk⟩⟩)
      rw [Real.Gamma_add_one hsum.ne', mul_comm (∑ i : Fin k, if (i : ℕ) < k₀ then α₀ else 1),
        ← div_div]
      exact h
  have hG : ∀ i : Fin k, Real.Gamma (if (i : ℕ) < k₀ then α₀ else 1) =
      if (i : ℕ) < k₀ then Real.Gamma α₀ else 1 := by
    intro i; split_ifs
    · rfl
    · exact Real.Gamma_one
  rw [show {t : Fin k → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < s} = posSimplex k s from rfl, hvalue]
  simp_rw [hG]
  rw [sum_ite_val_lt α₀ k k₀ hk₀, prod_ite_val_lt _ k k₀ hk₀, Nat.cast_sub hk₀]

end Dirichlet

/-! ### The two-level exponent vector and the estimates of Lemma 3.1 -/

/-- The Dirichlet integral `I_{k,s}(α₀, …, α₀, 1, …, 1)` of Lemma 3.1, with exponent `α₀` repeated
`k₀` times followed by `k - k₀` exponents equal to `1`. -/
@[expose] noncomputable def dirichletTwoLevel (α₀ : ℝ) (k k₀ : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in {t : Fin k → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < s},
    ENNReal.ofReal (∏ i, t i ^ ((if (i : ℕ) < k₀ then α₀ else 1) - 1))

/-- Closed form of `dirichletTwoLevel`: `s^A Γ(α₀)^{k₀} / Γ(A+1)` with `A = α₀ k₀ + k - k₀`. -/
theorem dirichletTwoLevel_eq {α₀ : ℝ} (hα₀ : 0 < α₀) (k k₀ : ℕ) (hk₀ : k₀ ≤ k) {s : ℝ}
    (hs : 0 < s) :
    dirichletTwoLevel α₀ k k₀ s =
      ENNReal.ofReal (s ^ (α₀ * k₀ + ((k : ℝ) - k₀)) * Real.Gamma α₀ ^ k₀ /
        Real.Gamma (α₀ * k₀ + ((k : ℝ) - k₀) + 1)) :=
  lintegral_dirichlet_two_level hα₀ k k₀ hk₀ hs

/-- The total exponent `A = α₀ k₀ + (k - k₀)` is positive when `k ≥ 1`. -/
theorem dirichletTwoLevel_exponent_pos {α₀ : ℝ} (hα₀ : 0 < α₀) {k k₀ : ℕ} (hk : 1 ≤ k)
    (hk₀ : k₀ ≤ k) :
    0 < α₀ * k₀ + ((k : ℝ) - k₀) := by
  have h1 : (k₀ : ℝ) ≤ k := by exact_mod_cast hk₀
  rcases Nat.eq_zero_or_pos k₀ with h | h
  · subst h; simp; exact_mod_cast hk
  · have : (0 : ℝ) < k₀ := by exact_mod_cast h
    nlinarith

/-- `I_{k,s}(α₀, …, α₀, 1, …, 1) > 0` for `s > 0`. -/
theorem dirichletTwoLevel_pos {α₀ : ℝ} (hα₀ : 0 < α₀) {k k₀ : ℕ} (hk : 1 ≤ k) (hk₀ : k₀ ≤ k)
    {s : ℝ} (hs : 0 < s) : 0 < dirichletTwoLevel α₀ k k₀ s := by
  rw [dirichletTwoLevel_eq hα₀ k k₀ hk₀ hs, ENNReal.ofReal_pos]
  have hA := dirichletTwoLevel_exponent_pos hα₀ hk hk₀
  have := Real.Gamma_pos_of_pos hα₀
  have := Real.Gamma_pos_of_pos (show 0 < α₀ * k₀ + ((k : ℝ) - k₀) + 1 by linarith)
  positivity

/-- `I_{k,s}(α₀, …, α₀, 1, …, 1) < ∞`. -/
theorem dirichletTwoLevel_lt_top {α₀ : ℝ} (hα₀ : 0 < α₀) {k k₀ : ℕ} (hk₀ : k₀ ≤ k)
    {s : ℝ} (hs : 0 < s) : dirichletTwoLevel α₀ k k₀ s < ⊤ := by
  rw [dirichletTwoLevel_eq hα₀ k k₀ hk₀ hs]
  exact ENNReal.ofReal_lt_top

/-- **Lemma 3.1, upper bound**: `I_{k,s} ≤ (s/A)^A e^k C_α^{k₀}` with `A = α k₀ + k - k₀`. -/
theorem dirichletTwoLevel_le {α₀ : ℝ} (hα₀ : 0 < α₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ k k₀ : ℕ, 1 ≤ k → k₀ ≤ k → ∀ s : ℝ, 0 < s →
      dirichletTwoLevel α₀ k k₀ s ≤
        ENNReal.ofReal ((s / (α₀ * k₀ + ((k : ℝ) - k₀))) ^ (α₀ * k₀ + ((k : ℝ) - k₀)) *
          Real.exp k * C ^ k₀) := by
  refine ⟨Real.exp (α₀ - 1) * Real.Gamma α₀, mul_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos hα₀),
    fun k k₀ hk hk₀ s hs => ?_⟩
  rw [dirichletTwoLevel_eq hα₀ k k₀ hk₀ hs]
  refine ENNReal.ofReal_le_ofReal ?_
  set A : ℝ := α₀ * k₀ + ((k : ℝ) - k₀) with hAdef
  have hA : 0 < A := dirichletTwoLevel_exponent_pos hα₀ hk hk₀
  have hG := rpow_mul_exp_neg_le_Gamma_add_one hA
  have hL : 0 < A ^ A * Real.exp (-A) := by positivity
  have hΓ := Real.Gamma_pos_of_pos hα₀
  have hexp : Real.exp (k : ℝ) * Real.exp (α₀ - 1) ^ k₀ = Real.exp A := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, hAdef]; congr 1; ring
  calc s ^ A * Real.Gamma α₀ ^ k₀ / Real.Gamma (A + 1)
      ≤ s ^ A * Real.Gamma α₀ ^ k₀ / (A ^ A * Real.exp (-A)) := by
        gcongr
    _ = (s / A) ^ A * Real.exp (k : ℝ) * (Real.exp (α₀ - 1) * Real.Gamma α₀) ^ k₀ := by
        rw [Real.div_rpow hs.le hA.le, mul_pow, Real.exp_neg]
        have : Real.exp (k : ℝ) * Real.exp (α₀ - 1) ^ k₀ = Real.exp A := hexp
        field_simp
        exact this.symm

/-- **Lemma 3.1, eq. (eq:estimate Dirichlet)**:
`log I_{k,s} = A (log s - log A) + k + O_α(k₀ + log (k+1))`, `A = α k₀ + k - k₀`. -/
theorem dirichletTwoLevel_log_estimate {α₀ : ℝ} (hα₀ : 0 < α₀) :
    ∃ C : ℝ, ∀ k k₀ : ℕ, 1 ≤ k → k₀ ≤ k → ∀ s : ℝ, 0 < s →
      |Real.log (dirichletTwoLevel α₀ k k₀ s).toReal -
          ((α₀ * k₀ + ((k : ℝ) - k₀)) *
            (Real.log s - Real.log (α₀ * k₀ + ((k : ℝ) - k₀))) + k)| ≤
        C * (k₀ + Real.log (k + 1)) := by
  set M : ℝ := max α₀ 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMα : α₀ ≤ M := le_max_left _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set q : ℝ := Real.log M / Real.log 2 with hq
  have hq0 : 0 ≤ q := div_nonneg (Real.log_nonneg hM1) hlog2.le
  obtain ⟨D, hD, hupper⟩ := dirichletTwoLevel_le hα₀
  set c₂ : ℝ := |Real.log D|
  set c₁ : ℝ := |Real.log (Real.Gamma α₀) + α₀ - 1| with hc₁
  refine ⟨c₁ + c₂ + 4 + 2 * q, fun k k₀ hk hk₀ s hs => ?_⟩
  set A : ℝ := α₀ * k₀ + ((k : ℝ) - k₀) with hAdef
  have hA : 0 < A := dirichletTwoLevel_exponent_pos hα₀ hk hk₀
  have hk₀' : (k₀ : ℝ) ≤ k := by exact_mod_cast hk₀
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk₀0 : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
  have hΓα := Real.Gamma_pos_of_pos hα₀
  have hΓA := Real.Gamma_pos_of_pos (show 0 < A + 1 by linarith)
  -- the closed form and its logarithm
  have hI : (dirichletTwoLevel α₀ k k₀ s).toReal =
      s ^ A * Real.Gamma α₀ ^ k₀ / Real.Gamma (A + 1) := by
    rw [dirichletTwoLevel_eq hα₀ k k₀ hk₀ hs, ENNReal.toReal_ofReal (by positivity)]
  have hlogI : Real.log (dirichletTwoLevel α₀ k k₀ s).toReal =
      A * Real.log s + k₀ * Real.log (Real.Gamma α₀) - Real.log (Real.Gamma (A + 1)) := by
    rw [hI, Real.log_div (by positivity) hΓA.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hs, Real.log_pow]
  have hupperReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hupper k k₀ hk hk₀ s hs)
  have hbase : 0 < (s / A) ^ A * Real.exp (k : ℝ) * D ^ k₀ := by positivity
  rw [ENNReal.toReal_ofReal hbase.le] at hupperReal
  have hlogUpper := Real.log_le_log
    (ENNReal.toReal_pos (dirichletTwoLevel_pos hα₀ hk hk₀ hs).ne'
      (dirichletTwoLevel_lt_top hα₀ hk₀ hs).ne) hupperReal
  change Real.log (dirichletTwoLevel α₀ k k₀ s).toReal ≤
    Real.log ((s / A) ^ A * Real.exp (k : ℝ) * D ^ k₀) at hlogUpper
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_rpow (by positivity),
    Real.log_div hs.ne' hA.ne', Real.log_exp, Real.log_pow, hlogI] at hlogUpper
  have hG2 := log_Gamma_add_one_le_stirling hA
  -- bounds on `log (A+1)`
  have hAM : A + 1 ≤ M * ((k : ℝ) + 1) := by
    have : A ≤ M * k := by
      have h1 : α₀ * k₀ ≤ M * k₀ := mul_le_mul_of_nonneg_right hMα hk₀0
      have h2 : (k : ℝ) - k₀ ≤ M * ((k : ℝ) - k₀) :=
        le_mul_of_one_le_left (sub_nonneg.2 hk₀') hM1
      have h3 : M * (k : ℝ) = M * k₀ + M * ((k : ℝ) - k₀) := by ring
      linarith only [h1, h2, h3, hAdef]
    linarith only [this, hM1]
  have hlogA : Real.log (A + 1) ≤ Real.log M + Real.log ((k : ℝ) + 1) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) hAM
  have hlogk : Real.log 2 ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogM : Real.log M ≤ q * Real.log ((k : ℝ) + 1) := by
    have : Real.log M = q * Real.log 2 := by
      rw [hq]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hlogk hq0
  have hlogkhalf : 1 ≤ 2 * Real.log ((k : ℝ) + 1) := by
    have hhalf := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hhalf
    linarith only [hlogk, hhalf]
  have hlk : 0 ≤ Real.log ((k : ℝ) + 1) := le_trans hlog2.le hlogk
  have hx2 : -(c₁ * k₀) ≤ (k₀ : ℝ) * (Real.log (Real.Gamma α₀) + α₀ - 1) := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log (Real.Gamma α₀) + α₀ - 1)) hk₀0
    linarith
  have hc₁0 : 0 ≤ c₁ := abs_nonneg _
  have hAk : A - k = (α₀ - 1) * k₀ := by rw [hAdef]; ring
  rw [hlogI, abs_le]
  have e1 : 0 ≤ c₁ * Real.log ((k : ℝ) + 1) := mul_nonneg hc₁0 hlk
  have e2 : 0 ≤ (k₀ : ℝ) * 2 := by positivity
  have e3 : 0 ≤ q * (k₀ : ℝ) := mul_nonneg hq0 hk₀0
  have e4 : 0 ≤ q * Real.log ((k : ℝ) + 1) := mul_nonneg hq0 hlk
  have e5 : 0 ≤ c₂ * k₀ := mul_nonneg (abs_nonneg _) hk₀0
  have e6 : 0 ≤ c₂ * Real.log ((k : ℝ) + 1) := mul_nonneg (abs_nonneg _) hlk
  have e7 : 0 ≤ c₁ * k₀ := mul_nonneg hc₁0 hk₀0
  have hxD : (k₀ : ℝ) * Real.log D ≤ c₂ * k₀ := by
    have h := mul_le_mul_of_nonneg_left (le_abs_self (Real.log D)) hk₀0
    linarith only [h]
  constructor
  · linarith only [hG2, hlogA, hlogk, hlogM, hx2, hAk, e1, e2, e3, e4, e5, e6, hlk, hc₁0, hlogkhalf]
  · linarith only [hlogUpper, hxD, e1, e2, e3, e4, e5, e6, e7, hlk]

end TwoComponentCoulomb

end
