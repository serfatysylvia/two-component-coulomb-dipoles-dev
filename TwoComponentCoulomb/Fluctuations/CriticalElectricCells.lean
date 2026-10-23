/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.UpperBound.CriticalRadial
public import TwoComponentCoulomb.Fluctuations.CriticalSameSignSplit
public import TwoComponentCoulomb.UpperBound.IsolatedRadial
import TwoComponentCoulomb.Gibbs.Measurability
import TwoComponentCoulomb.Integrals.GaussianMass
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# The pair weights of the electric moment at `β = 2` (Theorem 2, eq. (eq:critical electric))

Source `source/dipole-formation.tex`, l. 1910–1912 (proof of Theorem 2, Step 2, `β = 2`), repeating the
proof of (eq:critical upper) (l. 1595–1652) with the same retained coordinates.

Fix a nearest-neighbour graph `f = φ₁(Z)`. As in `UpperBound/CriticalCells.lean`, in each isolated
pair one endpoint `w_j` is retained (the non-retained endpoints form `S = isoSecondVerts f`), the
other is `w_j + u_j`, and `ρ_j` is the radius of `w_j` among the retained points; write
`a = (|u|/4) ∨ λ` and `ℓ = |log λ|`. This file bounds the radial integrals of the pair weights of
the electric moment. The cell integral and the sum over the graphs are those of the proof of
(eq:critical upper), for a general integrand (`UpperBound/CriticalCells.lean`,
`UpperBound/CriticalGraphSum.lean`); the energy bound of the electric moment and the assembly are
in `Fluctuations/CriticalElectric.lean`.

## Main results

* `elecNeutralWeight`, `elecSameSignWeight`: the literal pair weights with the Gaussian.
* `exists_lintegral_elecNeutralWeight_le`: the neutral mass is bounded by
  `J_λ(1/ℓ) + K J_λ(1/ℓ; γ) + C`, hence by `J_λ(1/ℓ) + CS`.
* `exists_lintegral_elecSameSignWeight_le`: the literal same-sign mass is at most `CS`.
  The proof uses the split into `(a/ρ)^4` and `min(a/γ,1)^4` from
  `Fluctuations/CriticalSameSignSplit.lean`, where the core estimates and Gaussian tail are proved.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace TwoComponentCoulomb


/-! ### The pair weights (source l. 1903–1912) -/

section Weights

/-- The weight of an isolated neutral pair with displacement `u` and radius `ρ` in the electric
moment : on the disc `|u| ≤ 4ρ`,
`exp (2 g_λ(u) - |u|²/ℓ + c ((a/ρ)² + ((a/γ)² ∧ 1)))`, `a = (|u|/4) ∨ λ`; the Gaussian factor comes
from the packing bound. -/
noncomputable def elecNeutralWeight (lam ℓ γ c : ℝ) (p : ℂ × ℝ) : ℝ≥0∞ :=
  if ‖p.1‖ ≤ 4 * p.2 then
    ENNReal.ofReal (Real.exp (2 * smearedKernel lam p.1 - ‖p.1‖ ^ 2 / ℓ +
      c * ((displacementScale lam p.1 / p.2) ^ 2 + min ((displacementScale lam p.1 / γ) ^ 2) 1)))
  else 0

/-- The weight of an isolated same-sign pair with displacement `u` and radius `ρ` in the electric
moment (source l. 1912): on the disc `|u| ≤ 4ρ`,
`c e^{2g_λ(u)-|u|²/ℓ} (a/((ρ ∧ γ) ∨ a))⁴`, `a = (|u|/4) ∨ λ`. -/
noncomputable def elecSameSignWeight (lam ℓ γ c : ℝ) (p : ℂ × ℝ) : ℝ≥0∞ :=
  if ‖p.1‖ ≤ 4 * p.2 then
    ENNReal.ofReal (c * (Real.exp (2 * smearedKernel lam p.1 - ‖p.1‖ ^ 2 / ℓ) *
      (displacementScale lam p.1 / max (min p.2 γ) (displacementScale lam p.1)) ^ 4))
  else 0

theorem measurable_elecNeutralWeight (lam ℓ γ c : ℝ) :
    Measurable (elecNeutralWeight lam ℓ γ c) := by
  have hs : MeasurableSet {p : ℂ × ℝ | ‖p.1‖ ≤ 4 * p.2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hg : Measurable (smearedKernel lam) := measurable_smearedKernel lam
  have hd : Measurable fun p : ℂ × ℝ => displacementScale lam p.1 :=
    (continuous_displacementScale lam).measurable.comp measurable_fst
  refine Measurable.ite hs ?_ measurable_const
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  refine Measurable.add ?_ ?_
  · exact ((hg.comp measurable_fst).const_mul 2).sub (by fun_prop)
  · refine Measurable.const_mul (Measurable.add ((hd.div measurable_snd).pow_const 2) ?_) c
    exact ((hd.div_const γ).pow_const 2).min measurable_const

theorem measurable_elecSameSignWeight (lam ℓ γ c : ℝ) :
    Measurable (elecSameSignWeight lam ℓ γ c) := by
  have hs : MeasurableSet {p : ℂ × ℝ | ‖p.1‖ ≤ 4 * p.2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hd : Measurable fun p : ℂ × ℝ => displacementScale lam p.1 :=
    (continuous_displacementScale lam).measurable.comp measurable_fst
  have hg := measurable_smearedKernel lam
  refine Measurable.ite hs ?_ measurable_const
  refine ENNReal.measurable_ofReal.comp ?_
  fun_prop

/-- `(a/r)² e^{2 g_λ(u) - |u|²/ℓ} ≤ e^{2 C₀} / r²` for `a ≤ |u| ∨ λ`. -/
theorem sq_div_mul_exp_le {C₀ lam ℓ r a : ℝ}
    (hC₀ : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ,
      |smearedKernel lam z - logKernel ((max ‖z‖ lam : ℝ) : ℂ)| ≤ C₀)
    (hlam : 0 < lam) (hℓ : 0 ≤ ℓ) (hr : 0 < r) (ha0 : 0 ≤ a) {u : ℂ} (ha : a ≤ max ‖u‖ lam) :
    (a / r) ^ 2 * Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ) ≤ Real.exp (2 * C₀) / r ^ 2 := by
  have hm : 0 < max ‖u‖ lam := lt_of_lt_of_le hlam (le_max_right _ _)
  have e1 : Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ) ≤
      Real.exp (2 * smearedKernel lam u) :=
    Real.exp_le_exp.2 (by have : 0 ≤ ‖u‖ ^ 2 / ℓ := by positivity
                          linarith)
  have e2 := exp_two_mul_smearedKernel_le_div hC₀ hlam u
  have e3 : (a / r) ^ 2 ≤ max ‖u‖ lam ^ 2 / r ^ 2 := by
    rw [div_pow]
    gcongr
  calc (a / r) ^ 2 * Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ)
      ≤ (max ‖u‖ lam ^ 2 / r ^ 2) * (Real.exp (2 * C₀) / max ‖u‖ lam ^ 2) :=
        mul_le_mul e3 (e1.trans e2) (Real.exp_pos _).le (by positivity)
    _ = Real.exp (2 * C₀) / r ^ 2 := by
        field_simp

/-- **The neutral pair** (source l. 1912, "splitting the radial integrals at `2λ` and `4γ`
gives masses at most `B + CS` for neutral pairs"): for every `c ≥ 0` there are `K, C ≥ 0` such that
for `0 < λ ≤ e⁻¹`, `2λ ≤ γ ≤ 1` and `ρ ≥ λ`,
`∫ elecNeutralWeight ≤ J_λ(1/ℓ) + K J_λ(1/ℓ; γ) + C`.
On `|u| ≤ 4γ` the correction `(a/γ)² ∧ 1` is at most `(a/γ)²`, which integrates against
`e^{2 g_λ}` to `O(1)`; on `|u| > 4γ` it is at most `1` and the Gaussian tail beyond `γ` is
`2π (½ log ℓ + log (1/γ) + O(1))`. -/
theorem exists_lintegral_elecNeutralWeight_le {c : ℝ} (hc : 0 ≤ c) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ lam γ ρ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → 2 * lam ≤ γ →
      γ ≤ 1 → lam ≤ ρ →
        ∫⁻ u, elecNeutralWeight lam |Real.log lam| γ c (u, ρ) ≤
          ENNReal.ofReal (criticalCycleMass lam + K * criticalTailMass lam γ + C) := by
  obtain ⟨C₀, hC₀⟩ := exists_abs_smearedKernel_sub_logKernel_le
  set Kc : ℝ := Real.exp c - 1 with hKc
  have hKc0 : 0 ≤ Kc := by have := Real.one_le_exp hc; rw [hKc]; linarith
  set K : ℝ := Kc + Kc ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set K₁ : ℝ := Kc * Real.exp (2 * C₀) with hK₁
  set K₃ : ℝ := K * Real.exp (2 * C₀) with hK₃
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₃0 : 0 ≤ K₃ := by positivity
  refine ⟨K, 16 * Real.pi * K₁ + 16 * Real.pi * K₃, hK0, by positivity,
    fun lam γ ρ hlam hle hγ hγ1 hρ => ?_⟩
  obtain ⟨h1, -⟩ := two_mul_le_sqrt_neg_log hlam hle
  have hab : |Real.log lam| = -Real.log lam := abs_of_neg (by linarith)
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  have hγ0 : 0 < γ := by linarith
  set ℓ := |Real.log lam| with hℓdef
  have hℓ1 : 1 ≤ ℓ := by rw [hab]; exact h1
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hlogγ : 0 ≤ Real.log (1 / γ) := Real.log_nonneg (by rw [le_div_iff₀ hγ0]; linarith)
  set X : ℂ → ℝ := fun u => Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ) with hX
  set T : ℂ → ℝ := fun u => if γ < ‖u‖ then X u else 0 with hT
  have hXm : Measurable X := by
    have := measurable_smearedKernel lam
    rw [hX]
    fun_prop
  have hTm : Measurable T :=
    Measurable.ite (measurableSet_lt measurable_const measurable_norm) hXm measurable_const
  have hTnn : ∀ u, 0 ≤ T u := fun u => by
    rw [hT]
    dsimp only
    by_cases hRu : γ < ‖u‖
    · rw [ite_eq_left hRu]; exact (Real.exp_pos _).le
    · rw [ite_eq_right hRu]
  -- pointwise bound
  have hpt : ∀ u : ℂ, elecNeutralWeight lam ℓ γ c (u, ρ) ≤
      ENNReal.ofReal (X u) + ENNReal.ofReal (K * T u) +
        (Metric.closedBall (0 : ℂ) (4 * ρ)).indicator (fun _ => ENNReal.ofReal (K₁ / ρ ^ 2)) u +
        (Metric.closedBall (0 : ℂ) (4 * γ)).indicator (fun _ => ENNReal.ofReal (K₃ / γ ^ 2)) u := by
    intro u
    unfold elecNeutralWeight
    dsimp only
    by_cases hu : ‖u‖ ≤ 4 * ρ
    · rw [ite_eq_left hu]
      have hmem : u ∈ Metric.closedBall (0 : ℂ) (4 * ρ) := by simpa using hu
      rw [Set.indicator_of_mem hmem]
      have hXpos : 0 < X u := Real.exp_pos _
      set a := displacementScale lam u with ha
      have ha0 : 0 < a := displacementScale_pos hlam u
      have haρ : a ≤ ρ := displacementScale_le_of_norm_le hρ hu
      have ham : a ≤ max ‖u‖ lam := by
        rw [ha, displacementScale]
        exact max_le_max (by linarith [norm_nonneg u]) le_rfl
      set x := (a / ρ) ^ 2 with hx
      set t := min ((a / γ) ^ 2) 1 with ht
      have hx0 : 0 ≤ x := sq_nonneg _
      have hx1 : x ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hρ0).2 haρ)
      have ht0 : 0 ≤ t := le_min (sq_nonneg _) zero_le_one
      have ht1 : t ≤ 1 := min_le_right _ _
      have hcx := exp_mul_le_one_add (c := c) hx0 hx1
      have hct := exp_mul_le_one_add (c := c) ht0 ht1
      rw [← hKc] at hcx hct
      have hprod : Real.exp (c * (x + t)) ≤ 1 + Kc * x + K * t := by
        rw [mul_add, Real.exp_add]
        calc Real.exp (c * x) * Real.exp (c * t) ≤ (1 + Kc * x) * (1 + Kc * t) :=
              mul_le_mul hcx hct (Real.exp_pos _).le (by positivity)
          _ ≤ 1 + Kc * x + K * t := by
              rw [hK]
              have : Kc * x * (Kc * t) ≤ Kc ^ 2 * t := by
                have h1 : Kc * x * (Kc * t) = Kc ^ 2 * t * x := by ring
                rw [h1]
                exact mul_le_of_le_one_right (by positivity) hx1
              linarith only [this]
      have hxX : x * X u ≤ Real.exp (2 * C₀) / ρ ^ 2 :=
        sq_div_mul_exp_le hC₀ hlam (by linarith) hρ0 ha0.le ham
      have htX : K * (t * X u) ≤ ENNReal.toReal ((Metric.closedBall (0 : ℂ) (4 * γ)).indicator
          (fun _ => ENNReal.ofReal (K₃ / γ ^ 2)) u) + K * T u := by
        by_cases hu4 : ‖u‖ ≤ 4 * γ
        · have hmem' : u ∈ Metric.closedBall (0 : ℂ) (4 * γ) := by simpa using hu4
          rw [Set.indicator_of_mem hmem', ENNReal.toReal_ofReal (by positivity)]
          have htle : t ≤ (a / γ) ^ 2 := min_le_left _ _
          have h2 : (a / γ) ^ 2 * X u ≤ Real.exp (2 * C₀) / γ ^ 2 :=
            sq_div_mul_exp_le hC₀ hlam (by linarith) hγ0 ha0.le ham
          have h3 : t * X u ≤ Real.exp (2 * C₀) / γ ^ 2 :=
            (mul_le_mul_of_nonneg_right htle hXpos.le).trans h2
          have h4 : K * (t * X u) ≤ K * (Real.exp (2 * C₀) / γ ^ 2) :=
            mul_le_mul_of_nonneg_left h3 hK0
          have h5 : K * (Real.exp (2 * C₀) / γ ^ 2) = K₃ / γ ^ 2 := by rw [hK₃]; ring
          have h6 : 0 ≤ K * T u := mul_nonneg hK0 (hTnn u)
          linarith
        · have hγu : γ < ‖u‖ := by have := lt_of_not_ge hu4; linarith
          have hTu : T u = X u := by rw [hT]; dsimp only; rw [ite_eq_left hγu]
          rw [hTu]
          have h3 : t * X u ≤ X u := mul_le_of_le_one_left hXpos.le ht1
          have h4 := mul_le_mul_of_nonneg_left h3 hK0
          have h5 : 0 ≤ ENNReal.toReal ((Metric.closedBall (0 : ℂ) (4 * γ)).indicator
              (fun _ => ENNReal.ofReal (K₃ / γ ^ 2)) u) := ENNReal.toReal_nonneg
          linarith
      -- assemble
      have hind_ne : (Metric.closedBall (0 : ℂ) (4 * γ)).indicator
          (fun _ => ENNReal.ofReal (K₃ / γ ^ 2)) u ≠ ⊤ := by
        by_cases hm : u ∈ Metric.closedBall (0 : ℂ) (4 * γ)
        · rw [Set.indicator_of_mem hm]; exact ENNReal.ofReal_ne_top
        · rw [Set.indicator_of_notMem hm]; exact ENNReal.zero_ne_top
      rw [← ENNReal.ofReal_toReal hind_ne, ← ENNReal.ofReal_add hXpos.le (by
          exact mul_nonneg hK0 (hTnn u)), ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp : Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ + c * (x + t)) =
          X u * Real.exp (c * (x + t)) := by
        rw [hX, ← Real.exp_add]
      rw [hexp]
      have hm1 := mul_le_mul_of_nonneg_left hprod hXpos.le
      have hKx : Kc * (x * X u) ≤ K₁ / ρ ^ 2 := by
        calc Kc * (x * X u) ≤ Kc * (Real.exp (2 * C₀) / ρ ^ 2) :=
              mul_le_mul_of_nonneg_left hxX hKc0
          _ = K₁ / ρ ^ 2 := by rw [hK₁]; ring
      linarith only [hm1, hKx, htX]
    · rw [ite_eq_right hu]
      exact zero_le
  -- integrate
  have hint : ∫⁻ u, elecNeutralWeight lam ℓ γ c (u, ρ) ≤
      (∫⁻ u, ENNReal.ofReal (X u)) + (∫⁻ u, ENNReal.ofReal (K * T u)) +
        (∫⁻ u, (Metric.closedBall (0 : ℂ) (4 * ρ)).indicator
          (fun _ => ENNReal.ofReal (K₁ / ρ ^ 2)) u) +
        ∫⁻ u, (Metric.closedBall (0 : ℂ) (4 * γ)).indicator
          (fun _ => ENNReal.ofReal (K₃ / γ ^ 2)) u := by
    refine (lintegral_mono hpt).trans (le_of_eq ?_)
    have hm1 : Measurable fun u => ENNReal.ofReal (X u) := ENNReal.measurable_ofReal.comp hXm
    have hm2 : Measurable fun u => ENNReal.ofReal (K * T u) :=
      ENNReal.measurable_ofReal.comp (hTm.const_mul K)
    have hm3 : Measurable fun u => (Metric.closedBall (0 : ℂ) (4 * ρ)).indicator
        (fun _ => ENNReal.ofReal (K₁ / ρ ^ 2)) u :=
      measurable_const.indicator Metric.isClosed_closedBall.measurableSet
    rw [lintegral_add_left (by exact (hm1.add hm2).add hm3),
      lintegral_add_left (by exact hm1.add hm2), lintegral_add_left (by exact hm1)]
  have hB : ∫⁻ u, ENNReal.ofReal (X u) = ENNReal.ofReal (criticalCycleMass lam) :=
    (ofReal_criticalCycleMass hlam hle).symm
  have hBR : ∫⁻ u, ENNReal.ofReal (K * T u) =
      ENNReal.ofReal (K * criticalTailMass lam γ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((integrable_tail_gaussianMass hlam hle).const_mul _) (ae_of_all _ fun u =>
        mul_nonneg hK0 (hTnn u)), integral_const_mul]
    rfl
  have hball1 := lintegral_indicator_closedBall_div_sq hρ0 hK₁0
  have hball3 := lintegral_indicator_closedBall_div_sq hγ0 hK₃0
  refine hint.trans ?_
  rw [hball1, hball3]
  rw [hB, hBR]
  have hj := (criticalCycleMass_pos hlam hle).le
  have ht := criticalTailMass_nonneg lam γ
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact le_of_eq (congrArg ENNReal.ofReal (by ring))

/-- **The same-sign pair** in the electric moment. The literal radial weight is
bounded by splitting the fourth-power cutoff into its `ρ` and `γ` contributions. -/
theorem exists_lintegral_elecSameSignWeight_le :
    ∃ C : ℝ, 0 < C ∧ ∀ lam γ ρ c : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      2 * lam ≤ γ → γ ≤ 1 → lam ≤ ρ → 0 ≤ c →
      ∫⁻ u, elecSameSignWeight lam |Real.log lam| γ c (u, ρ) ≤
        ENNReal.ofReal (C * c * (1 + Real.log |Real.log lam| + Real.log (1 / γ))) := by
  obtain ⟨C, hC, hsplit⟩ := exists_lintegral_critical_sameSign_split_le
  refine ⟨C, hC, fun lam γ ρ c hlam hle hγ hγ1 hρ hc => ?_⟩
  have hind : (fun u => elecSameSignWeight lam |Real.log lam| γ c (u, ρ)) =
      (Metric.closedBall (0 : ℂ) (4 * ρ)).indicator (fun u =>
        ENNReal.ofReal c * ENNReal.ofReal
          (Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|) *
            (displacementScale lam u / max (min ρ γ) (displacementScale lam u)) ^ 4)) := by
    funext u
    simp only [elecSameSignWeight, ENNReal.ofReal_mul hc,
      Metric.mem_closedBall, dist_zero_right, Set.indicator]
  rw [hind, lintegral_indicator Metric.isClosed_closedBall.measurableSet,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_right (hsplit lam γ ρ hlam hle hγ hγ1 hρ) _).trans_eq ?_
  rw [← ENNReal.ofReal_mul hc]
  congr 1
  ring

end Weights

end TwoComponentCoulomb

end
