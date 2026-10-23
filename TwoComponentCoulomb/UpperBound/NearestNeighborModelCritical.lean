/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.Integrals.Dirichlet
public import TwoComponentCoulomb.PhaseSpace.RadialSimplex
public import TwoComponentCoulomb.UpperBound.NearestNeighborModelCases
import TwoComponentCoulomb.Gibbs.Measurability
import TwoComponentCoulomb.Integrals.DirichletTrunc
import TwoComponentCoulomb.Integrals.LogFacts
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# The critical weight `exp (2 g_λ)`: integration under the packing constraint

Source: (Lemma 3.4, Step 3, `β = 2`) and l. 854–857 (Step 4,
`β = 4`), which use the Gaussian decoupling of Lemma 3.2 (`lem:gaussian decoupling`) and
(eq:critical-gaussian) of Lemma 3.3.

For `β = 2` the 2-cycle weight and for `β = 4` the tree weight is `exp (2 g_λ (u))`, which equals
`|u|^{-2}` exactly for `|u| ≥ 2λ` (Newton's theorem) and is at most `e^{2C} λ^{-2}` for
`|u| < 2λ`. The source removes the constraint `∑ |u_i|² ≤ s` by the exponential Markov bound of
Lemma 3.2 and evaluates the one-variable integral by (eq:critical-gaussian). We carry this out in
the variable `t = |u|²`, with the exponential Markov bound on the simplex `{∑ t_i < s}`
(`DirichletTrunc.lintegral_markov_prod`) applied to the weight `W_λ(t) = exp (2 g_λ (√t))`; the
inner region `|u| < 2λ` contributes an additive `O(1)` to the one-dimensional integral.

## Main results

* `TwoComponentCoulomb.lintegral_Ioi_critical_weight_le`: the one-dimensional integral
  `∫_0^∞ W_λ(t) e^{-ut} dt ≤ log (1/(4 λ² u)) + 1 + 4 e^{2C}`.
* `TwoComponentCoulomb.lintegral_posSimplex_critical_le`: the simplex integral of `∏ W_λ (t_i)`.
* `TwoComponentCoulomb.exists_lintegral_ball_critical_le`: the ball integral of
  `∏ exp (2 g_λ(u_i))` over `|U|² ≤ s`, in terms of `ℓ = log (s / (4 λ² m))`.
* `TwoComponentCoulomb.exists_lintegral_ball_tree_le_four`: the tree integral for `β = 4`
  (source l. 854–857).
* `TwoComponentCoulomb.exists_lintegral_ball_cycle_le_two`: the cycle integral for `β = 2`
  , including the uniformity in `K/N` (the error `K log log (N/(λK)) /
  log (N/(λK))` is bounded directly by `N log log (1/λ) / log (1/λ)`).
* `TwoComponentCoulomb.lintegral_cell_le_of_eq_two`, `TwoComponentCoulomb.lintegral_cell_le_of_eq_four`
  and `TwoComponentCoulomb.lintegral_cell_le_of_two_lt`: Lemma 3.4 for `β = 2` the critical clause of Lemma 3.4, `β = 4`
  the β = 4 clause of Lemma 3.4 and, in the single form of (eq:F(2)), for all `β > 2`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### The weight `exp (2 g_λ (√t))` -/

/-- For `t ≥ 4 λ²` one has `exp (2 g_λ (√t)) = 1/t` (`g_λ = g` outside `B(0, 2λ)`). -/
theorem exp_two_mul_smearedKernel_sqrt_of_le {lam t : ℝ} (hlam : 0 < lam) (ht : 4 * lam ^ 2 ≤ t) :
    Real.exp (2 * smearedKernel lam ((Real.sqrt t : ℝ) : ℂ)) = t⁻¹ := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have h2 : 2 * lam ≤ Real.sqrt t := by
    rw [Real.le_sqrt (by positivity) ht0.le]
    linarith only [ht]
  rw [smearedKernel_ofReal_of_le hlam h2, Real.log_sqrt ht0.le,
    show 2 * -(Real.log t / 2) = -Real.log t by ring, Real.exp_neg, Real.exp_log ht0]

/-- For all `t`, `exp (2 g_λ (√t)) ≤ e^{2C} / λ²`, where `g_λ ≤ -log λ + C`. -/
theorem exp_two_mul_smearedKernel_le {c : ℝ}
    (hc : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, smearedKernel lam z ≤ -Real.log lam + c) {lam : ℝ}
    (hlam : 0 < lam) (z : ℂ) :
    Real.exp (2 * smearedKernel lam z) ≤ Real.exp (2 * c) * (lam ^ 2)⁻¹ := by
  have h := hc lam hlam z
  calc Real.exp (2 * smearedKernel lam z) ≤ Real.exp (2 * (-Real.log lam + c)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (2 * c) * (lam ^ 2)⁻¹ := by
        rw [show 2 * (-Real.log lam + c) = -(2 * Real.log lam) + 2 * c by ring, Real.exp_add,
          Real.exp_neg, mul_comm, show 2 * Real.log lam = Real.log (lam ^ 2) by
            rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]

/-- The one-dimensional integral against `e^{-ut}`: with `λ' = 4 λ²` and `λ' ≤ 1/u`,
`∫_0^∞ exp (2 g_λ(√t)) e^{-ut} dt ≤ log (1/(u λ')) + 1 + 4 e^{2C}`. The region `t < 4 λ²`
contributes at most `4 e^{2C}`, the rest is the integral of `t^{-1} e^{-ut}` over `[4λ², ∞)`. -/
theorem lintegral_Ioi_critical_weight_le {c : ℝ}
    (hc : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, smearedKernel lam z ≤ -Real.log lam + c) {lam u : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (hlu : 4 * lam ^ 2 ≤ u⁻¹) :
    ∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (2 * smearedKernel lam ((Real.sqrt x : ℝ) : ℂ))) *
          ENNReal.ofReal (Real.exp (-(u * x))) ≤
      ENNReal.ofReal (Real.log (u⁻¹ / (4 * lam ^ 2)) + 1 + 4 * Real.exp (2 * c)) := by
  set lam' : ℝ := 4 * lam ^ 2 with hlam'
  have hlam'0 : 0 < lam' := by positivity
  have hm0 : 0 ≤ Real.log (u⁻¹ / lam') := Real.log_nonneg ((one_le_div hlam'0).2 hlu)
  rw [← Ioc_union_Ioi_eq_Ioi hlam'0.le,
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  have h1 : ∫⁻ x in Ioc (0 : ℝ) lam',
        ENNReal.ofReal (Real.exp (2 * smearedKernel lam ((Real.sqrt x : ℝ) : ℂ))) *
          ENNReal.ofReal (Real.exp (-(u * x))) ≤ ENNReal.ofReal (4 * Real.exp (2 * c)) := by
    calc _ ≤ ∫⁻ x in Ioc (0 : ℝ) lam', ENNReal.ofReal (Real.exp (2 * c) * (lam ^ 2)⁻¹) := by
          refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
          calc _ ≤ ENNReal.ofReal (Real.exp (2 * c) * (lam ^ 2)⁻¹) * 1 := by
                refine mul_le_mul' (ENNReal.ofReal_le_ofReal
                  (exp_two_mul_smearedKernel_le hc hlam _)) ?_
                rw [← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal
                  (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hu.le hx.1.le)))
            _ = _ := mul_one _
      _ = ENNReal.ofReal (4 * Real.exp (2 * c)) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hlam']
          field_simp
  have h2 : ∫⁻ x in Ioi lam',
        ENNReal.ofReal (Real.exp (2 * smearedKernel lam ((Real.sqrt x : ℝ) : ℂ))) *
          ENNReal.ofReal (Real.exp (-(u * x))) ≤ ENNReal.ofReal (Real.log (u⁻¹ / lam') + 1) := by
    calc _ = ∫⁻ x in Ioi lam', ENNReal.ofReal (x⁻¹ * Real.exp (-(u * x))) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
          rw [exp_two_mul_smearedKernel_sqrt_of_le hlam (le_of_lt hx),
            ENNReal.ofReal_mul (inv_nonneg.2 (by have := mem_Ioi.1 hx; linarith))]
      _ ≤ ∫⁻ x in Ici lam', ENNReal.ofReal (x⁻¹ * Real.exp (-(u * x))) :=
          lintegral_mono_set Ioi_subset_Ici_self
      _ ≤ _ := DirichletTrunc.lintegral_Ici_inv_exp hlam'0 hu hlu
  calc _ ≤ ENNReal.ofReal (4 * Real.exp (2 * c)) + ENNReal.ofReal (Real.log (u⁻¹ / lam') + 1) :=
        add_le_add h1 h2
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by linarith)]
        congr 1
        ring

/-! ### The simplex integral -/

/-- Real-variable estimate behind the critical case, with `ℓ = log (s/(λ' m)) ≥ log 2`:
`1/(1+ℓ) + log (ℓ + log (1+ℓ) + 1 + c₀) ≤ log ℓ + (6 + 2 c₀)(1 + log ℓ)/ℓ`. -/
theorem real_estimate_critical {ℓ c₀ : ℝ} (hℓ : Real.log 2 ≤ ℓ) (hc₀ : 0 ≤ c₀) :
    1 / (1 + ℓ) + Real.log (ℓ + Real.log (1 + ℓ) + 1 + c₀) ≤
      Real.log ℓ + (6 + 2 * c₀) * (1 + Real.log ℓ) / ℓ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := DirichletTrunc.log_facts hℓ
  have hℓ0 : 0 < ℓ := by linarith
  set w := Real.log (1 + ℓ) with hw
  set v := 1 + Real.log ℓ with hv
  have e1 : Real.log (ℓ + w + 1 + c₀) ≤ Real.log ℓ + (w + 1 + c₀) / ℓ := by
    have := Real.log_le_sub_one_of_pos (show 0 < (ℓ + w + 1 + c₀) / ℓ by positivity)
    rw [Real.log_div (by positivity) hℓ0.ne'] at this
    have h6 : (ℓ + w + 1 + c₀) / ℓ - 1 = (w + 1 + c₀) / ℓ := by field_simp; ring
    linarith
  have e2 : 1 / (1 + ℓ) ≤ 1 / ℓ := one_div_le_one_div_of_le hℓ0 (by linarith)
  have e3 : (1 : ℝ) / ℓ + (w + 1 + c₀) / ℓ ≤ (6 + 2 * c₀) * v / ℓ := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hℓ0.le
    linarith only [h2, h5, mul_nonneg hc₀ (sub_nonneg.2 h2)]
  linarith

/-- The simplex integral of the critical weight, by the exponential Markov bound
(Lemma 3.2 in the variables `t_i = |u_i|²`): with `ℓ = log (s / (4 λ² m)) ≥ log 2`,
`∫_{Σ t_i < s} ∏ exp (2 g_λ(√t_i)) dt ≤ exp (m (log ℓ + (6 + 8 e^{2C})(1 + log ℓ)/ℓ))`. -/
theorem lintegral_posSimplex_critical_le {c : ℝ}
    (hc : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, smearedKernel lam z ≤ -Real.log lam + c)
    {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s) {m : ℕ} (hm : 1 ≤ m)
    (h : 8 * lam ^ 2 * m ≤ s) {ℓ : ℝ} (hℓ : ℓ = Real.log (s / (4 * lam ^ 2 * m))) :
    ∫⁻ t in posSimplex m s,
        ∏ i, ENNReal.ofReal (Real.exp (2 * smearedKernel lam ((Real.sqrt (t i) : ℝ) : ℂ))) ≤
      ENNReal.ofReal (Real.exp (m * (Real.log ℓ +
        (6 + 2 * (4 * Real.exp (2 * c))) * (1 + Real.log ℓ) / ℓ))) := by
  have hp0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h4 : 0 < 4 * lam ^ 2 * m := by positivity
  have hratio : 2 ≤ s / (4 * lam ^ 2 * m) := by
    rw [le_div_iff₀ h4]
    linarith only [h]
  have hℓ2 : Real.log 2 ≤ ℓ := hℓ ▸ Real.log_le_log (by norm_num) hratio
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (Real.log_pos (by norm_num)) hℓ2
  have hexp : Real.exp ℓ = s / (4 * lam ^ 2 * m) := by rw [hℓ, Real.exp_log (by positivity)]
  set c₀ : ℝ := 4 * Real.exp (2 * c) with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = m / (s * (1 + ℓ)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have huinv : u⁻¹ = s * (1 + ℓ) / m := by rw [hu]; field_simp
  have hlu : 4 * lam ^ 2 ≤ u⁻¹ := by
    rw [huinv, le_div_iff₀ hp0]
    linarith only [h, mul_nonneg hs.le hℓ0.le, mul_nonneg (sq_nonneg lam) hp0.le]
  have hlog : Real.log (u⁻¹ / (4 * lam ^ 2)) = ℓ + Real.log (1 + ℓ) := by
    have : u⁻¹ / (4 * lam ^ 2) = (1 + ℓ) * Real.exp ℓ := by
      rw [hexp, huinv]; field_simp
    rw [this, Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]; ring
  have hus : u * s = m / (1 + ℓ) := by rw [hu]; field_simp
  set g : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (2 * smearedKernel lam ((Real.sqrt x : ℝ) : ℂ))) with hg
  have hgm : Measurable g := by
    have : Measurable fun x : ℝ => smearedKernel lam ((Real.sqrt x : ℝ) : ℂ) :=
      (measurable_smearedKernel lam).comp
        (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable)
    rw [hg]
    fun_prop
  have hmark := DirichletTrunc.lintegral_markov_prod m (S := Ioi (0 : ℝ)) measurableSet_Ioi hgm
    hu0.le s
  have h1d := lintegral_Ioi_critical_weight_le hc hlam hu0 hlu
  rw [hlog] at h1d
  change ∫⁻ t in {t : Fin m → ℝ | (∀ i, t i ∈ Ioi (0 : ℝ)) ∧ ∑ i, t i < s}, ∏ i, g (t i) ≤ _
  refine hmark.trans ?_
  have hB0 : 0 < ℓ + Real.log (1 + ℓ) + 1 + c₀ := by
    have : 0 ≤ Real.log (1 + ℓ) := Real.log_nonneg (by linarith)
    positivity
  calc ENNReal.ofReal (Real.exp (u * s)) *
        (∫⁻ x in Ioi (0 : ℝ), g x * ENNReal.ofReal (Real.exp (-(u * x)))) ^ m
      ≤ ENNReal.ofReal (Real.exp (u * s)) *
          (ENNReal.ofReal (ℓ + Real.log (1 + ℓ) + 1 + c₀)) ^ m := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (u * s) * (ℓ + Real.log (1 + ℓ) + 1 + c₀) ^ m) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow hB0.le]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (ℓ + Real.log (1 + ℓ) + 1 + c₀) ^ m =
            Real.exp (m * Real.log (ℓ + Real.log (1 + ℓ) + 1 + c₀)) := by
          rw [Real.exp_nat_mul, Real.exp_log hB0]
        rw [this, ← Real.exp_add, hus]
        refine Real.exp_le_exp.2 ?_
        have := real_estimate_critical hℓ2 hc₀0
        calc (m : ℝ) / (1 + ℓ) + m * Real.log (ℓ + Real.log (1 + ℓ) + 1 + c₀)
            = m * (1 / (1 + ℓ) + Real.log (ℓ + Real.log (1 + ℓ) + 1 + c₀)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [hc₀] using this) hp0.le

/-! ### The ball integral -/

/-- **Lemma 3.2 and (eq:critical-gaussian) applied to `exp (2 g_λ)`** : for `m ≥ 1` variables, `s > 0` and `8 λ² m ≤ s`, with `ℓ = log (s / (4 λ² m))`,
`∫_{|U|² ≤ s} ∏ exp (2 g_λ(u_i)) dU ≤ exp (m (log π + log ℓ + C (1 + log ℓ)/ℓ))`
(each variable contributes `π` from the polar change `t = |u|²`). -/
theorem exists_lintegral_ball_critical_le :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (lam s : ℝ) (m : ℕ), 0 < lam → 0 < s → 1 ≤ m → 8 * lam ^ 2 * m ≤ s →
      ∀ ℓ : ℝ, ℓ = Real.log (s / (4 * lam ^ 2 * m)) →
        ∫⁻ v in {v : Fin m → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s},
            ∏ i, ENNReal.ofReal (Real.exp (2 * smearedKernel lam (v i))) ≤
          ENNReal.ofReal (Real.exp (m * (Real.log Real.pi + Real.log ℓ +
            C₁ * (1 + Real.log ℓ) / ℓ))) := by
  obtain ⟨c, hc⟩ := exists_smearedKernel_le
  refine ⟨6 + 2 * (4 * Real.exp (2 * c)), by positivity, fun lam s m hlam hs hm h ℓ hℓ => ?_⟩
  have hp0 : (0 : ℝ) < m := by exact_mod_cast hm
  set gr : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (2 * smearedKernel lam (r : ℂ)))
    with hgr
  have hgrm : Measurable gr := by
    have : Measurable fun r : ℝ => smearedKernel lam (r : ℂ) :=
      (measurable_smearedKernel lam).comp Complex.measurable_ofReal
    rw [hgr]
    fun_prop
  have hpolar : ∫⁻ v in {v : Fin m → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s},
      ∏ i, ENNReal.ofReal (Real.exp (2 * smearedKernel lam (v i))) =
        ENNReal.ofReal Real.pi ^ m * ∫⁻ t in posSimplex m s, ∏ i, gr (Real.sqrt (t i)) := by
    rw [← lintegral_ball_prod_radial_eq_posSimplex hs (fun _ : Fin m => gr) (fun _ => hgrm)]
    refine lintegral_congr fun v => ?_
    simp only [hgr, ← smearedKernel_eq_norm]
  rw [hpolar]
  refine (mul_le_mul_right (lintegral_posSimplex_critical_le hc hlam hs hm h hℓ) _).trans ?_
  rw [← ENNReal.ofReal_pow Real.pi_pos.le, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have hπ : Real.pi ^ m = Real.exp (m * Real.log Real.pi) := by
    rw [Real.exp_nat_mul, Real.exp_log Real.pi_pos]
  rw [hπ, ← Real.exp_add]
  congr 1
  ring

/-! ### The tree integral for `β = 4` -/

/-- The function `x ↦ (1 + log x)/x` is nonincreasing on `[1, ∞)`. -/
theorem one_add_log_div_le_of_le {x y : ℝ} (hy : 1 ≤ y) (hxy : y ≤ x) :
    (1 + Real.log x) / x ≤ (1 + Real.log y) / y := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := by linarith
  rw [div_le_div_iff₀ hx0 hy0]
  have h1 : Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hx0.ne' hy0.ne'] at h1
  have h2 : y * (Real.log x - Real.log y) ≤ x - y := by
    calc y * (Real.log x - Real.log y) ≤ y * (x / y - 1) := mul_le_mul_of_nonneg_left h1 hy0.le
      _ = x - y := by field_simp
  have h3 : 0 ≤ Real.log y := Real.log_nonneg hy
  linarith only [h2, mul_le_mul_of_nonneg_right hxy h3]

/-- The Dirichlet parameter in the cases `β = 2, 4`: for `s = 36 N/π` and `m` variables,
`log (s / (4 λ² m)) = log (9 N/(π m)) + 2 |log λ|`. -/
theorem log_div_eq {N : ℕ} {lam : ℝ} {m : ℕ} (hN : 0 < N) (hlam : 0 < lam) (hm : 0 < m) :
    Real.log (36 * N / Real.pi / (4 * lam ^ 2 * m)) =
      Real.log (9 / Real.pi) + Real.log ((N : ℝ) / m) + 2 * (-Real.log lam) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h : 36 * (N : ℝ) / Real.pi / (4 * lam ^ 2 * m) =
      (9 / Real.pi) * ((N : ℝ) / m) * (lam ^ 2)⁻¹ := by
    field_simp
    ring
  rw [h, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_inv, Real.log_pow]
  push_cast
  ring

/-- `8 λ² m ≤ 36 N/π` for `λ ≤ 1/2` and `m ≤ 2N`. -/
theorem eight_mul_le {N m : ℕ} {lam : ℝ} (hlam : 0 < lam) (hlam2 : lam ≤ 1 / 2)
    (hm : m ≤ 2 * N) : 8 * lam ^ 2 * m ≤ 36 * N / Real.pi := by
  rw [le_div_iff₀ Real.pi_pos]
  have h1 : lam ^ 2 ≤ 1 / 4 := by
    calc lam ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hlam.le hlam2 2
      _ = 1 / 4 := by norm_num
  have h2 : (m : ℝ) ≤ 2 * N := by exact_mod_cast hm
  have h3 := Real.pi_le_four
  have h4 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h5 : 8 * lam ^ 2 * (m : ℝ) ≤ 4 * N := by
    linarith only [mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg m : (0 : ℝ) ≤ m), h2]
  linarith only [mul_le_mul_of_nonneg_right h5 Real.pi_pos.le,
    mul_le_mul_of_nonneg_left h3 h4, h4]

/-- **Lemma 3.4, Step 4, `β = 4`** (source l. 854–857): the tree integral over the ball of
`ℂ^{2q}` is at most `exp (2q log (|log λ| + log (N/q)) + C q)`, for `0 < λ ≤ e⁻¹`, `q ≤ N`. -/
theorem exists_lintegral_ball_tree_le_four {β : ℝ} (hβ : β = 4) :
    ∃ C : ℝ, ∀ (N q m : ℕ), 0 < N → q ≤ N → m = 2 * q → ∀ lam : ℝ, 0 < lam →
      lam ≤ Real.exp (-1) →
        ∫⁻ v in {v : Fin m → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ 36 * N / Real.pi},
            ∏ i, ENNReal.ofReal (Real.exp ((β / 2) * smearedKernel lam (v i))) ≤
          ENNReal.ofReal (Real.exp ((2 * q) * Real.log (|Real.log lam| + Real.log (N / q)) +
            C * q)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_lintegral_ball_critical_le
  have hpi4 := Real.pi_le_four
  set κ₀ : ℝ := Real.log (9 / Real.pi) - Real.log 2 with hκ₀
  have hκ₀0 : 0 ≤ κ₀ := by
    rw [hκ₀, sub_nonneg]
    exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ Real.pi_pos]; linarith)
  refine ⟨2 * (Real.log Real.pi + Real.log (2 + κ₀) + C₁), fun N q m hN hqN hm lam hlam hlam1 => ?_⟩
  subst hβ
  have hb : ((4 : ℝ) / 2) = 2 := by norm_num
  simp only [hb]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine (lintegral_ball_prod_le_one_of_eq_zero (m := m) (by omega) _
      (fun v => ENNReal.ofReal (Real.exp (2 * smearedKernel lam v)))).trans ?_
    simp
  have hx : (0 : ℝ) < q := by exact_mod_cast hq
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm1 : 1 ≤ m := by omega
  have hmq : (m : ℝ) = 2 * q := by rw [hm]; push_cast; ring
  have hlog1 : Real.log lam ≤ -1 := by
    have := Real.log_le_log hlam hlam1
    rwa [Real.log_exp] at this
  set L : ℝ := -Real.log lam with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  have habs : |Real.log lam| = L := by rw [abs_of_nonpos (by linarith), hL]
  have hlam2 : lam ≤ 1 / 2 := hlam1.trans exp_neg_one_le_half
  have h8 : 8 * lam ^ 2 * m ≤ 36 * N / Real.pi :=
    eight_mul_le hlam hlam2 (by omega)
  have hs : 0 < 36 * (N : ℝ) / Real.pi := by positivity
  set a : ℝ := Real.log ((N : ℝ) / q) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (by
    rw [le_div_iff₀ hx]; simpa using (by exact_mod_cast hqN : (q : ℝ) ≤ N))
  set ℓ : ℝ := Real.log (36 * N / Real.pi / (4 * lam ^ 2 * m)) with hℓdef
  have hNm : Real.log ((N : ℝ) / m) = a - Real.log 2 := by
    rw [hmq, ha, show (N : ℝ) / (2 * q) = ((N : ℝ) / q) / 2 by field_simp,
      Real.log_div (by positivity) (by norm_num)]
  have hℓ : ℓ = κ₀ + a + 2 * L := by
    rw [hℓdef, log_div_eq hN hlam (by omega : 0 < m), hNm, hκ₀, hL]
    ring
  have hℓ2 : 2 * L ≤ ℓ := by rw [hℓ]; linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hmain := hC₁ lam (36 * N / Real.pi) m hlam hs hm1 h8 ℓ hℓdef
  refine hmain.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have e1 : C₁ * (1 + Real.log ℓ) / ℓ ≤ C₁ := by
    rw [mul_div_assoc]
    have : (1 + Real.log ℓ) / ℓ ≤ 1 := by
      rw [div_le_one hℓ0]
      have := Real.log_le_sub_one_of_pos hℓ0
      linarith
    calc C₁ * ((1 + Real.log ℓ) / ℓ) ≤ C₁ * 1 := mul_le_mul_of_nonneg_left this hC₁0
      _ = C₁ := mul_one _
  have e2 : Real.log ℓ ≤ Real.log (2 + κ₀) + Real.log (L + a) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log hℓ0 ?_
    rw [hℓ]
    linarith only [mul_nonneg hκ₀0 (sub_nonneg.2 hL1),
      mul_nonneg (by linarith : 0 ≤ 1 + κ₀) ha0]
  rw [habs, hmq]
  have hq0 : (0 : ℝ) ≤ 2 * q := by positivity
  have := mul_le_mul_of_nonneg_left
    (show Real.log Real.pi + Real.log ℓ + C₁ * (1 + Real.log ℓ) / ℓ ≤
      Real.log Real.pi + (Real.log (2 + κ₀) + Real.log (L + a)) + C₁ by linarith) hq0
  linarith only [this]

/-! ### The cycle integral for `β = 2` -/

/-- The error per cycle in the case `β = 2`: for `L ≥ 2`,
`κ/(2L) + C₁ (1 + log 2 + log L)/(2L) ≤ C₂ log L / L`, with
`C₂ = (κ + C₁ (1 + log 2))/(2 log 2) + C₁/2` ( uniformity in `K`). -/
theorem critical_error_le {L κ C₁ : ℝ} (hL : 2 ≤ L) (hκ : 0 ≤ κ) (hC₁ : 0 ≤ C₁) :
    κ / (2 * L) + C₁ * (1 + Real.log 2 + Real.log L) / (2 * L) ≤
      ((κ + C₁ * (1 + Real.log 2)) / (2 * Real.log 2) + C₁ / 2) * (Real.log L / L) := by
  have hL0 : 0 < L := by linarith
  have hln2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogL : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) hL
  set M : ℝ := κ + C₁ * (1 + Real.log 2) with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ C₁ * (1 + Real.log 2) := by positivity
    linarith
  have key : M ≤ M / Real.log 2 * Real.log L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hln2]
    exact mul_le_mul_of_nonneg_left hlogL hM0
  have e1 : κ / (2 * L) + C₁ * (1 + Real.log 2 + Real.log L) / (2 * L) =
      (M + C₁ * Real.log L) / (2 * L) := by
    rw [hM]; field_simp; ring
  have e2 : ((κ + C₁ * (1 + Real.log 2)) / (2 * Real.log 2) + C₁ / 2) * (Real.log L / L) =
      (M / Real.log 2 * Real.log L + C₁ * Real.log L) / (2 * L) := by
    rw [← hM]; field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- **Lemma 3.4, Step 3, `β = 2`** : for `1 ≤ K ≤ N` and `0 < λ ≤ e⁻²`, the
cycle integral over the ball of `ℂ^K` satisfies
`log ∫ ∏ e^{2 g_λ(u_k)} ≤ K log 2π + K log (|log λ| + log (N/K)) + C N log|log λ| / |log λ|`. -/
theorem exists_lintegral_ball_cycle_le_two :
    ∃ C : ℝ, ∀ (N K : ℕ), 0 < N → 1 ≤ K → K ≤ N → ∀ lam : ℝ, 0 < lam →
      lam ≤ Real.exp (-2) →
        ∫⁻ v in {v : Fin K → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ 36 * N / Real.pi},
            ∏ i, ENNReal.ofReal (Real.exp (2 * smearedKernel lam (v i))) ≤
          ENNReal.ofReal (Real.exp (K * Real.log (2 * Real.pi) +
            K * Real.log (|Real.log lam| + Real.log (N / K)) +
            C * N * (Real.log |Real.log lam| / |Real.log lam|))) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_lintegral_ball_critical_le
  have hpi4 := Real.pi_le_four
  set κ₁ : ℝ := Real.log (9 / Real.pi) with hκ₁
  have hκ₁0 : 0 ≤ κ₁ := Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith)
  refine ⟨(κ₁ + C₁ * (1 + Real.log 2)) / (2 * Real.log 2) + C₁ / 2,
    fun N K hN hK1 hKN lam hlam hlam2 => ?_⟩
  have hln2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ (κ₁ + C₁ * (1 + Real.log 2)) / (2 * Real.log 2) + C₁ / 2 := by
    have : 0 ≤ C₁ * (1 + Real.log 2) := by positivity
    positivity
  have hx : (0 : ℝ) < K := by exact_mod_cast hK1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog2 : Real.log lam ≤ -2 := by
    have := Real.log_le_log hlam hlam2
    rwa [Real.log_exp] at this
  set L : ℝ := -Real.log lam with hL
  have hL2 : 2 ≤ L := by rw [hL]; linarith
  have habs : |Real.log lam| = L := by rw [abs_of_nonpos (by linarith), hL]
  have hlam1 : lam ≤ 1 / 2 := by
    refine hlam2.trans (le_trans ?_ exp_neg_one_le_half)
    exact Real.exp_le_exp.2 (by norm_num)
  have h8 : 8 * lam ^ 2 * K ≤ 36 * N / Real.pi := eight_mul_le hlam hlam1 (by omega)
  have hs : 0 < 36 * (N : ℝ) / Real.pi := by positivity
  set a : ℝ := Real.log ((N : ℝ) / K) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (by
    rw [le_div_iff₀ hx]; simpa using (by exact_mod_cast hKN : (K : ℝ) ≤ N))
  set ℓ : ℝ := Real.log (36 * N / Real.pi / (4 * lam ^ 2 * K)) with hℓdef
  have hℓ : ℓ = κ₁ + a + 2 * L := by
    rw [hℓdef, log_div_eq hN hlam (by omega : 0 < K), hκ₁, ha, hL]
  have hℓ2 : 2 * L ≤ ℓ := by rw [hℓ]; linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hL0 : 0 < L := by linarith
  have hmain := hC₁ lam (36 * N / Real.pi) K hlam hs hK1 h8 ℓ hℓdef
  rw [habs]
  refine hmain.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  -- Step A: `log ℓ ≤ log 2 + log (L + a) + κ₁/(2L)`
  have stepA : Real.log ℓ ≤ Real.log 2 + Real.log (L + a) + κ₁ / (2 * L) := by
    have h1 : ℓ ≤ 2 * (L + a) * (1 + κ₁ / (2 * L)) := by
      have : κ₁ ≤ κ₁ * ((L + a) / L) := by
        have : 1 ≤ (L + a) / L := by rw [le_div_iff₀ hL0]; linarith
        exact le_mul_of_one_le_right hκ₁0 this
      have e : 2 * (L + a) * (1 + κ₁ / (2 * L)) = 2 * (L + a) + κ₁ * ((L + a) / L) := by
        field_simp
      rw [e, hℓ]
      linarith
    calc Real.log ℓ ≤ Real.log (2 * (L + a) * (1 + κ₁ / (2 * L))) :=
          Real.log_le_log hℓ0 h1
      _ = Real.log 2 + Real.log (L + a) + Real.log (1 + κ₁ / (2 * L)) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num)
            (by positivity)]
      _ ≤ _ := by
          have := Real.log_le_sub_one_of_pos (show 0 < 1 + κ₁ / (2 * L) by positivity)
          linarith
  -- Step B: monotonicity of `(1 + log x)/x`
  have stepB : C₁ * (1 + Real.log ℓ) / ℓ ≤ C₁ * (1 + Real.log 2 + Real.log L) / (2 * L) := by
    have h := one_add_log_div_le_of_le (by linarith : (1 : ℝ) ≤ 2 * L) hℓ2
    rw [Real.log_mul (by norm_num) hL0.ne'] at h
    calc C₁ * (1 + Real.log ℓ) / ℓ = C₁ * ((1 + Real.log ℓ) / ℓ) := by ring
      _ ≤ C₁ * ((1 + (Real.log 2 + Real.log L)) / (2 * L)) :=
          mul_le_mul_of_nonneg_left h hC₁0
      _ = _ := by ring
  have stepC := critical_error_le hL2 hκ₁0 hC₁0
  set C₂ : ℝ := (κ₁ + C₁ * (1 + Real.log 2)) / (2 * Real.log 2) + C₁ / 2 with hC₂
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hper : Real.log Real.pi + Real.log ℓ + C₁ * (1 + Real.log ℓ) / ℓ ≤
      Real.log (2 * Real.pi) + Real.log (L + a) + C₂ * (Real.log L / L) := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne']
    linarith
  have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have herr : 0 ≤ C₂ * (Real.log L / L) := by positivity
  calc (K : ℝ) * (Real.log Real.pi + Real.log ℓ + C₁ * (1 + Real.log ℓ) / ℓ)
      ≤ K * (Real.log (2 * Real.pi) + Real.log (L + a) + C₂ * (Real.log L / L)) :=
        mul_le_mul_of_nonneg_left hper hx.le
    _ = K * Real.log (2 * Real.pi) + K * Real.log (L + a) + K * (C₂ * (Real.log L / L)) := by
        ring
    _ ≤ K * Real.log (2 * Real.pi) + K * Real.log (L + a) + N * (C₂ * (Real.log L / L)) := by
        have := mul_le_mul_of_nonneg_right hKN' herr
        linarith
    _ = _ := by ring

/-! ### Lemma 3.4 for `β = 4` and `β = 2` -/

section Cases

universe u

/-- **Lemma 3.4, case `β = 4`** (source l. 767–770). For `f` the nearest-neighbour map of a
configuration of `2p ≤ 2N` points in `Λ = [0, √N]²`, with `K` 2-cycles, and `0 < λ ≤ e⁻¹`,
`log J(f) ≤ K log N + (2-β) K log λ + K log 𝒵_β + (2p-2K) log (|log λ| + log (N/(p-K))) +
C_β (p-K)`. -/
theorem lintegral_cell_le_of_eq_four {β : ℝ} (hβ : β = 4) :
    ∃ C : ℝ, ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (N p K : ℕ) (f : ι → ι),
      0 < N → p ≤ N → Fintype.card ι = 2 * p → Fintype.card {i // i ∈ gpRefSet key f} = K →
      ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
            ENNReal.ofReal (Real.exp ((β / 2) *
              ∑ i, smearedKernel lam (z i - z (nnMap key z i)))) ≤
          ENNReal.ofReal (Real.exp (K * Real.log N + (2 - β) * K * Real.log lam +
            K * Real.log (dipoleConstant β (by rw [hβ]; norm_num)) +
            (2 * p - 2 * K) * Real.log (|Real.log lam| + Real.log (N / (p - K))) +
            C * (p - K))) := by
  have hβ2 : 2 < β := by rw [hβ]; norm_num
  obtain ⟨Ct, hCt⟩ := exists_lintegral_ball_tree_le_four hβ
  refine ⟨Ct, fun ι _ _ key N p K f hN hpN hcard hK lam hlam hlam1 => ?_⟩
  by_cases hf : ∃ z₀ : ι → ℂ, nnMap key z₀ = f
  swap
  · rw [lintegral_cell_eq_zero_of_not_exists key N f hf]
    exact zero_le
  obtain ⟨z₀, rfl⟩ := hf
  have hK2 : 2 * K ≤ 2 * p := by
    have := two_mul_card_gpRefSet_nnMap_le key z₀
    omega
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (show K ≤ p by omega)
  refine (lintegral_cell_le_cycle_mul_tree hcard key ⟨z₀, rfl⟩ hK β lam).trans ?_
  have hA := (lintegral_ball_prod_exp_le hβ2 hlam K (36 * N / Real.pi)).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq (dipoleConstant_mul_rpow_pow hβ2 hlam K)))
  have hB := hCt N q (2 * (K + q) - 2 * K) hN (by omega) (by omega) lam hlam hlam1
  refine (natCast_pow_mul_le hN hA hB).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  push_cast
  rw [add_sub_cancel_left, show 2 * ((K : ℝ) + q) - 2 * K = 2 * q by ring]
  refine le_of_eq ?_
  ring

/-- **Lemma 3.4, case `β = 2`** . For `f` the nearest-neighbour map of a
configuration of `2p ≤ 2N` points in `Λ = [0, √N]²`, with `K` 2-cycles, and `0 < λ ≤ e⁻²`,
`log J(f) ≤ K log N + K log (|log λ| + log (N/K)) + K log 2π + (1 - β/4)(2p-2K) log (N/(p-K)) +
C (p-K) + C N log|log λ| / |log λ|` (here `β = 2`; `C` is an absolute constant). -/
theorem lintegral_cell_le_of_eq_two {β : ℝ} (hβ : β = 2) :
    ∃ C : ℝ, ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (N p K : ℕ) (f : ι → ι),
      0 < N → p ≤ N → Fintype.card ι = 2 * p → Fintype.card {i // i ∈ gpRefSet key f} = K →
      ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-2) →
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
            ENNReal.ofReal (Real.exp ((β / 2) *
              ∑ i, smearedKernel lam (z i - z (nnMap key z i)))) ≤
          ENNReal.ofReal (Real.exp (K * Real.log N +
            K * Real.log (|Real.log lam| + Real.log (N / K)) + K * Real.log (2 * Real.pi) +
            (1 - β / 4) * (2 * p - 2 * K) * Real.log (N / (p - K)) + C * (p - K) +
            C * N * (Real.log |Real.log lam| / |Real.log lam|))) := by
  subst hβ
  obtain ⟨Ct, hCt⟩ := exists_lintegral_ball_tree_le (β := 2) le_rfl (by norm_num)
  obtain ⟨Cc, hCc⟩ := exists_lintegral_ball_cycle_le_two
  refine ⟨max Ct Cc, fun ι _ _ key N p K f hN hpN hcard hK lam hlam hlam2 => ?_⟩
  by_cases hf : ∃ z₀ : ι → ℂ, nnMap key z₀ = f
  swap
  · rw [lintegral_cell_eq_zero_of_not_exists key N f hf]
    exact zero_le
  obtain ⟨z₀, rfl⟩ := hf
  have hK1 : 1 ≤ K := hK ▸ one_le_card_gpRefSet_nnMap key z₀
  have hK2 : 2 * K ≤ 2 * p := by
    have := two_mul_card_gpRefSet_nnMap_le key z₀
    omega
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (show K ≤ p by omega)
  refine (lintegral_cell_le_cycle_mul_tree hcard key ⟨z₀, rfl⟩ hK 2 lam).trans ?_
  have hA := hCc N K hN hK1 (by omega) lam hlam hlam2
  have hB := hCt N q (2 * (K + q) - 2 * K) hN (by omega) lam hlam
  refine (natCast_pow_mul_le hN hA hB).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have hlog2 : Real.log lam ≤ -2 := by
    have := Real.log_le_log hlam hlam2
    rwa [Real.log_exp] at this
  have hL : 2 ≤ |Real.log lam| := by rw [abs_of_nonpos (by linarith)]; linarith
  have hlogL : 0 ≤ Real.log |Real.log lam| := Real.log_nonneg (by linarith)
  have hfrac : 0 ≤ (N : ℝ) * (Real.log |Real.log lam| / |Real.log lam|) := by
    have : 0 < |Real.log lam| := by linarith
    positivity
  have h1 : Cc * (N * (Real.log |Real.log lam| / |Real.log lam|)) ≤
      max Ct Cc * (N * (Real.log |Real.log lam| / |Real.log lam|)) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hfrac
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h2 : Ct * q ≤ max Ct Cc * q := mul_le_mul_of_nonneg_right (le_max_left _ _) hq0
  push_cast
  rw [add_sub_cancel_left, show 2 * ((K : ℝ) + q) - 2 * K = 2 * q by ring]
  linarith only [h1, h2]

/-- **Lemma 3.4 for `β > 2`** (source l. 761–776, the three cases `β ∈ (2,4)`, `β = 4`, `β > 4`
in the single form of (eq:F(2)), l. 1475–1481): for `0 < λ ≤ e⁻¹`,
`log J(f) ≤ K (log N + (2-β) log λ + log 𝒵_β) +
  (2p-2K) ((1 - β/4) log (N/(p-K)) 1_{β<4} + log (|log λ| + log (N/(p-K))) 1_{β=4} +
  (2 - β/2) log λ 1_{β>4}) + C_β (p-K)`. -/
theorem lintegral_cell_le_of_two_lt {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (N p K : ℕ) (f : ι → ι),
      0 < N → p ≤ N → Fintype.card ι = 2 * p → Fintype.card {i // i ∈ gpRefSet key f} = K →
      ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
            ENNReal.ofReal (Real.exp ((β / 2) *
              ∑ i, smearedKernel lam (z i - z (nnMap key z i)))) ≤
          ENNReal.ofReal (Real.exp (K * Real.log N + (2 - β) * K * Real.log lam +
            K * Real.log (dipoleConstant β hβ.le) +
            (2 * p - 2 * K) * ((if β < 4 then (1 - β / 4) * Real.log (N / (p - K)) else 0) +
              (if β = 4 then Real.log (|Real.log lam| + Real.log (N / (p - K))) else 0) +
              (if 4 < β then (2 - β / 2) * Real.log lam else 0)) + C * (p - K))) := by
  rcases lt_trichotomy β 4 with h | h | h
  · obtain ⟨C, hC⟩ := lintegral_cell_le_of_two_lt_of_lt_four hβ h
    refine ⟨C, fun ι _ _ key N p K f hN hpN hcard hK lam hlam hlam1 => ?_⟩
    refine (hC ι key N p K f hN hcard hK lam hlam).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq ?_)))
    rw [ite_eq_left h, ite_eq_right h.ne, ite_eq_right (not_lt.2 h.le)]
    ring
  · subst h
    obtain ⟨C, hC⟩ := lintegral_cell_le_of_eq_four (β := 4) rfl
    refine ⟨C, fun ι _ _ key N p K f hN hpN hcard hK lam hlam hlam1 => ?_⟩
    refine (hC ι key N p K f hN hpN hcard hK lam hlam hlam1).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq ?_)))
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, ite_eq_right (lt_irrefl _)]
    ring
  · obtain ⟨C, hC⟩ := lintegral_cell_le_of_four_lt h
    refine ⟨C, fun ι _ _ key N p K f hN hpN hcard hK lam hlam hlam1 => ?_⟩
    refine (hC ι key N p K f hN hcard hK lam hlam).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq ?_)))
    rw [ite_eq_right (not_lt.2 h.le), ite_eq_right h.ne', ite_eq_left h]
    ring

end Cases

end TwoComponentCoulomb

end
