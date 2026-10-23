/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.LowerBound.LabelSum
public import TwoComponentCoulomb.LowerBound.PairFactor
public import TwoComponentCoulomb.LowerBound.PartitionLower
import TwoComponentCoulomb.LowerBound.NeumannEnergy
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# Step 1 of Proposition 4.1 integrated: the lower bound (minz3) and the case `β = 2`

Source: Proposition 4.1, Step 1 (l. 1671–1734) and Step 2,
eq. (minz3) (l. 1738–1744). The proof follows the source (ruling R22): the energy of a
configuration of screened dipoles is bounded by eq. (majof),
`F_λ(X_N, Y_N) ≤ -Σ_i g_λ(x_i - y_i) + Σ_i |x_i - y_i|² / ϱ_i²`
(`energy_sum_elim_le_screened`, from the Neumann construction of `LowerBound/NeumannEnergy.lean`),
whenever the discs `B(x_i, ϱ_i)` are disjoint, `ϱ_i ≥ 4λ` and `|y_i - x_i| ≤ ϱ_i / 2`.
Multiplying by `-β ≤ 0`, the Boltzmann weight dominates a product of one-pair weights
`exp(β g_λ(u) - β |u|²/ϱ_i²)`; integrating over the annuli `a_i ≤ |y_i - x_i| ≤ b_i` (Tonelli)
and summing over the `N!` assignments of negative labels (`partitionFunction_ge_label_sum`) gives
the lower bound on `Z`. The constant of the correction is `A_β = β` (the constant of (majof) is
`1`).

* `integral_annulusSet_prod` : Tonelli over the annuli for a product of one-pair weights.
* `prod_integral_annulus_le_lintegral_exp_energy` : for fixed `X`, the product of the one-pair
  integrals `∫_{a_i ≤ |u| ≤ b_i} exp(β g_λ(u) - β|u|²/ϱ_i²) du` is at most the integral of
  `e^{-β F_λ(X, Y)}` over the annuli (eq. (majof) times `β`).
* `partitionFunction_ge_screened` : the integrated form
  `N! ∫_H ∏_i ∫_{a_i ≤ |u| ≤ b_i} exp(β g_λ(u) - β|u|²/ϱ_i²) du dX ≤ Z`.
* `partitionFunction_ge_pairFactor` : eq. (minz3), `N! ∫_H ∏_i J_β(ϱ(x_i)) dX ≤ Z` with
  `H = H(N, N, 4λ, 8λ)` and `J_β = pairFactor β β λ`.
* `partitionFunction_ge_placement_annulus` : the bound of l. 1730–1736 (stated for every
  `β ≥ 0`, used at `β = 2`): with the balls `B(x_i, t)`,
  `Z ≥ N! |H_t| (e^{-β t²} ∫_{2λ ≤ |u| ≤ t²} e^{β g_λ(u)} du)^N`, `H_t = H(N, N, t, 4t)`; the factor
  `e^{-β N t²}` is the energy error `Σ_i |x_i - y_i|²/t² ≤ N t²` of (majof).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### Tonelli over the annuli -/

/-- A closed annulus `a ≤ |y - x| ≤ b` is measurable. -/
theorem measurableSet_annulus (a b : ℝ) (x : ℂ) :
    MeasurableSet {y : ℂ | a ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ b} := by
  rw [Set.ofPred_and]
  exact (measurableSet_le measurable_const (measurable_id.sub_const x).norm).inter
    (measurableSet_le (measurable_id.sub_const x).norm measurable_const)

/-- A closed annulus `a ≤ |u| ≤ b` about `0` is measurable. -/
theorem measurableSet_annulus_zero (a b : ℝ) : MeasurableSet {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ ≤ b} := by
  rw [Set.ofPred_and]
  exact (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

/-- **Tonelli over the annuli**: for a product of functions of the individual displacements,
`∫_{a_i ≤ |Y_i - X_i| ≤ b_i} ∏_i h_i(Y_i - X_i) dY = ∏_i ∫_{a_i ≤ |u| ≤ b_i} h_i(u) du`. -/
theorem integral_annulusSet_prod (a b : Fin N → ℝ) (X : Fin N → ℂ) (h : Fin N → ℂ → ℝ) :
    ∫ Y in {Y : Fin N → ℂ | ∀ i, a i ≤ ‖Y i - X i‖ ∧ ‖Y i - X i‖ ≤ b i}, ∏ i, h i (Y i - X i) =
      ∏ i, ∫ u in {u : ℂ | a i ≤ ‖u‖ ∧ ‖u‖ ≤ b i}, h i u := by
  have hS : {Y : Fin N → ℂ | ∀ i, a i ≤ ‖Y i - X i‖ ∧ ‖Y i - X i‖ ≤ b i} =
      Set.univ.pi fun i => {y : ℂ | a i ≤ ‖y - X i‖ ∧ ‖y - X i‖ ≤ b i} := by
    ext Y
    simp
  rw [hS, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun i y => h i (y - X i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← integral_indicator (measurableSet_annulus (a i) (b i) (X i)),
    ← integral_indicator (measurableSet_annulus_zero (a i) (b i)),
    ← integral_sub_right_eq_self ({u : ℂ | a i ≤ ‖u‖ ∧ ‖u‖ ≤ b i}.indicator (h i)) (X i)]
  -- `y` lies in the annulus about `X i` iff `y - X i` lies in the annulus about `0`
  congr 1

/-! ### Eq. (majof) times `β`, integrated over the annuli -/

/-- The one-pair weight `exp(β g_λ(u) - β |u|²/ϱ²)` is continuous. -/
theorem continuous_exp_screenedWeight {lam : ℝ} (hlam : 0 < lam) (β ρ : ℝ) :
    Continuous fun u : ℂ => Real.exp (β * smearedKernel lam u - β * ‖u‖ ^ 2 / ρ ^ 2) :=
  (((continuous_smearedKernel hlam).const_mul β).sub
    (((continuous_norm.pow 2).const_mul β).div_const _)).rexp

/-- **Eq. (majof) times `β`, integrated over the annuli** (source l. 1726 and l. 1743–1744). Let
the discs `B(x_i, ϱ_i)` be disjoint with `ϱ_i ≥ 4λ`, and let `b_i ≤ ϱ_i / 2`. For `β ≥ 0`,
`∏_i ∫_{a_i ≤ |u| ≤ b_i} exp(β g_λ(u) - β|u|²/ϱ_i²) du ≤
  ∫_{a_i ≤ |y_i - x_i| ≤ b_i} e^{-β F_λ(X, Y)} dY`. -/
theorem prod_integral_annulus_le_lintegral_exp_energy {lam β : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ β)
    (X : Fin N → ℂ) (a b ρ : Fin N → ℝ) (hbρ : ∀ i, b i ≤ ρ i / 2) (hρ : ∀ i, 4 * lam ≤ ρ i)
    (hdisj : ∀ i j, i ≠ j → ρ i + ρ j ≤ ‖X i - X j‖) :
    ∏ i, ENNReal.ofReal (∫ u in {u : ℂ | a i ≤ ‖u‖ ∧ ‖u‖ ≤ b i},
        Real.exp (β * smearedKernel lam u - β * ‖u‖ ^ 2 / ρ i ^ 2)) ≤
      ∫⁻ Y in {Y : Fin N → ℂ | ∀ i, a i ≤ ‖Y i - X i‖ ∧ ‖Y i - X i‖ ≤ b i},
        ENNReal.ofReal (Real.exp (-β * energy lam (Sum.elim X Y))) := by
  set h : Fin N → ℂ → ℝ := fun i u =>
    Real.exp (β * smearedKernel lam u - β * ‖u‖ ^ 2 / ρ i ^ 2) with hh
  set S : Set (Fin N → ℂ) := {Y : Fin N → ℂ | ∀ i, a i ≤ ‖Y i - X i‖ ∧ ‖Y i - X i‖ ≤ b i}
    with hSdef
  have hSm : MeasurableSet S := by
    have : S = ⋂ i, (fun Y : Fin N → ℂ => Y i) ⁻¹'
        {y : ℂ | a i ≤ ‖y - X i‖ ∧ ‖y - X i‖ ≤ b i} := by
      ext Y
      simp [hSdef]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      measurable_pi_apply i (measurableSet_annulus (a i) (b i) (X i))
  -- integrability of the product of the one-pair weights on the annuli
  have hcont : Continuous fun Y : Fin N → ℂ => ∏ i, h i (Y i - X i) :=
    continuous_finsetProd _ fun i _ =>
      (continuous_exp_screenedWeight hlam β (ρ i)).comp ((continuous_apply i).sub continuous_const)
  have hK : IsCompact (Set.univ.pi fun i => Metric.closedBall (X i) (b i)) :=
    isCompact_univ_pi fun i => isCompact_closedBall _ _
  have hSK : S ⊆ Set.univ.pi fun i => Metric.closedBall (X i) (b i) := fun Y hY i _ => by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hY i).2
  have hint : IntegrableOn (fun Y : Fin N → ℂ => ∏ i, h i (Y i - X i)) S :=
    (hcont.continuousOn.integrableOn_compact hK).mono_set hSK
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ =>
      setIntegral_nonneg (measurableSet_annulus_zero (a i) (b i))
        fun u _ => (Real.exp_pos _).le,
    ← integral_annulusSet_prod a b X h,
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun Y => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)]
  refine setLIntegral_mono' hSm fun Y hY => ENNReal.ofReal_le_ofReal ?_
  -- the pointwise bound: eq. (majof) times `-β`
  have hY : ∀ i, ‖Y i - X i‖ ≤ ρ i / 2 := fun i => (hY i).2.trans (hbρ i)
  have hmajof := energy_sum_elim_le_screened hlam X Y ρ hρ hdisj hY
  have hprod : ∏ i, h i (Y i - X i) =
      Real.exp (-β * (-∑ i, smearedKernel lam (Y i - X i) +
        ∑ i, ‖Y i - X i‖ ^ 2 / ρ i ^ 2)) := by
    rw [hh, ← Real.exp_sum]
    congr 1
    rw [Finset.sum_sub_distrib]
    simp only [mul_div_assoc, ← Finset.mul_sum]
    ring
  rw [hprod]
  exact Real.exp_le_exp.2 (by nlinarith [hmajof])

/-- **Step 1 integrated** (source l. 1726–1744, with the correction constant `β`). Let `H` be
a measurable set of positions of the positive charges and `a, b, ϱ` radius functions, `a, b` measurable, such that, for `X ∈ H`, `b_i ≤ ϱ_i / 2`,
`ϱ_i ≥ 4λ`, the discs `B(x_i, ϱ_i)` are disjoint and the closed discs `B̄(x_i, b_i)` lie in `Λ`.
Then for `β ≥ 0`,
`N! ∫_H ∏_i ∫_{a_i ≤ |u| ≤ b_i} exp(β g_λ(u) - β|u|²/ϱ_i²) du dX ≤ Z_{N,β}^λ`. -/
theorem partitionFunction_ge_screened {lam β : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ β)
    {H : Set (Fin N → ℂ)} (hH : MeasurableSet H) {a b ρ : (Fin N → ℂ) → Fin N → ℝ}
    (ha : ∀ i, Measurable fun X => a X i) (hb : ∀ i, Measurable fun X => b X i)
    (hbρ : ∀ X ∈ H, ∀ i, b X i ≤ ρ X i / 2) (hρ : ∀ X ∈ H, ∀ i, 4 * lam ≤ ρ X i)
    (hdisj : ∀ X ∈ H, ∀ i j, i ≠ j → ρ X i + ρ X j ≤ ‖X i - X j‖)
    (hbox : ∀ X ∈ H, ∀ i, Metric.closedBall (X i) (b X i) ⊆ box N) :
    ENNReal.ofReal (N.factorial : ℝ) *
        ∫⁻ X in H, ∏ i, ENNReal.ofReal (∫ u in {u : ℂ | a X i ≤ ‖u‖ ∧ ‖u‖ ≤ b X i},
          Real.exp (β * smearedKernel lam u - β * ‖u‖ ^ 2 / ρ X i ^ 2)) ≤
      partitionFunction N β lam := by
  refine partitionFunction_ge_label_sum β lam hH ha hb hbox (fun X hX i j hij => ?_)
    (fun X hX => prod_integral_annulus_le_lintegral_exp_energy hlam hβ X (a X) (b X) (ρ X)
      (hbρ X hX) (hρ X hX) (hdisj X hX))
  have hi := hbρ X hX i
  have hj := hbρ X hX j
  have hρi := hρ X hX i
  have hρj := hρ X hX j
  have := hdisj X hX i j hij
  linarith

/-! ### Eq. (minz3) -/

/-- The closed ball about `0` as a closed annulus with inner radius `0`. -/
theorem setOf_zero_le_norm_le (b : ℝ) :
    {u : ℂ | 0 ≤ ‖u‖ ∧ ‖u‖ ≤ b} = Metric.closedBall (0 : ℂ) b := by
  ext u
  simp [norm_nonneg]

/-- `J_β(r) ≤ ∫_{B̄(0, r/2)} exp(β g_λ(u) - A|u|²/r²) du`: the pair factor is the integral over the
open disc. -/
theorem pairFactor_le_integral_closedBall {β A lam r : ℝ} (hlam : 0 < lam) :
    pairFactor β A lam r ≤ ∫ u in Metric.closedBall (0 : ℂ) (r / 2),
      Real.exp (β * smearedKernel lam u - A * ‖u‖ ^ 2 / r ^ 2) :=
  setIntegral_mono_set
    ((continuous_pairFactor_integrand hlam).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _))
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
    (Filter.Eventually.of_forall Metric.ball_subset_closedBall)

/-- **Eq. (minz3)** (source l. 1738–1744). For `β ≥ 0`, `0 < λ` and `4λ ≤ 1`, with
`H = H(N, N, 4λ, 8λ)` and `J_β(r) = ∫_{B(0, r/2)} exp(β g_λ(u) - β|u|²/r²) du`
(`pairFactor β β λ`), `N! ∫_H ∏_i J_β(ϱ(x_i)) dX ≤ Z`. -/
theorem partitionFunction_ge_pairFactor (hN : 2 ≤ N) {lam β : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ β)
    (h4 : 4 * lam ≤ 1) :
    ENNReal.ofReal (N.factorial : ℝ) *
        ∫⁻ X in placementSet N N (4 * lam) (8 * lam), ∏ i,
          ENNReal.ofReal (pairFactor β β lam (lowerRadius hN X i)) ≤
      partitionFunction N β lam := by
  have hH := measurableSet_placementSet N N (4 * lam) (8 * lam)
  have h := partitionFunction_ge_screened (N := N) hlam hβ hH (a := fun _ _ => 0)
    (b := fun X i => lowerRadius hN X i / 2) (ρ := fun X i => lowerRadius hN X i)
    (fun _ => measurable_const) (fun i => (measurable_lowerRadius hN i).div_const 2)
    (fun _ _ _ => le_rfl) (fun X hX i => four_mul_le_lowerRadius hN h4 hX i)
    (fun X _ i j hij => lowerRadius_add_lowerRadius_le hN X hij)
    (fun X hX i => closedBall_lowerRadius_div_two_subset_box hN hlam h4 hX i)
  simp only [setOf_zero_le_norm_le] at h
  refine le_trans (mul_le_mul_right (setLIntegral_mono' hH fun X _ => ?_) _) h
  exact Finset.prod_le_prod fun i _ => ENNReal.ofReal_le_ofReal (pairFactor_le_integral_closedBall hlam)

/-! ### The case `β = 2` -/

/-- **The lower bound of source l. 1730–1736** (stated for every `β ≥ 0`; the source uses it at
`β = 2`). Restrict the positive charges to `H_t = H(N, N, t, 4t)` and each displacement to
`2λ ≤ |x_i - y_i| ≤ t²`, with Neumann balls `B(x_i, t)` (disjoint since `|x_i - x_j| ≥ 4t`). For
`0 < t ≤ 1/2` and `2λ ≤ t²`, the energy error of (majof) is `Σ_i |x_i - y_i|²/t² ≤ N t²`, and
`Z ≥ N! · vol H_t · (e^{-β t²} ∫_{2λ ≤ |u| ≤ t²} e^{β g_λ(u)} du)^N`. -/
theorem partitionFunction_ge_placement_annulus {lam t β : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ β)
    (ht : 0 < t) (ht2 : 2 * t ≤ 1) (hlt : 2 * lam ≤ t ^ 2) :
    ENNReal.ofReal (N.factorial : ℝ) * volume (placementSet N N t (4 * t)) *
        (ENNReal.ofReal (Real.exp (-(β * t ^ 2)) *
          ∫ u in {u : ℂ | 2 * lam ≤ ‖u‖ ∧ ‖u‖ ≤ t ^ 2}, Real.exp (β * smearedKernel lam u))) ^ N ≤
      partitionFunction N β lam := by
  have htt : t ^ 2 ≤ t / 2 := by nlinarith
  have hH := measurableSet_placementSet N N t (4 * t)
  have h := partitionFunction_ge_screened (N := N) hlam hβ hH (a := fun _ _ => 2 * lam)
    (b := fun _ _ => t ^ 2) (ρ := fun _ _ => t) (fun _ => measurable_const)
    (fun _ => measurable_const) (fun _ _ _ => htt) (fun _ _ _ => by nlinarith)
    (fun X hX i j hij => by
      have := hX.2 i j hij
      linarith)
    (fun X hX i => closedBall_subset_box_of_mem_placementSet hX (by linarith) i)
  -- the energy error: on the annulus, `β |u|²/t² ≤ β t²`
  set A : Set ℂ := {u : ℂ | 2 * lam ≤ ‖u‖ ∧ ‖u‖ ≤ t ^ 2} with hAdef
  have hA : MeasurableSet A := measurableSet_annulus_zero (2 * lam) (t ^ 2)
  have hAK : A ⊆ Metric.closedBall (0 : ℂ) (t ^ 2) := fun u hu => by
    simpa using hu.2
  have hint : ∀ f : ℂ → ℝ, Continuous f → IntegrableOn f A := fun f hf =>
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set hAK
  have hfac : Real.exp (-(β * t ^ 2)) * ∫ u in A, Real.exp (β * smearedKernel lam u) ≤
      ∫ u in A, Real.exp (β * smearedKernel lam u - β * ‖u‖ ^ 2 / t ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on
      (hint _ ((((continuous_smearedKernel hlam).const_mul β).rexp).const_mul _))
      (hint _ (continuous_exp_screenedWeight hlam β t)) hA fun u hu => ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hu2 : ‖u‖ ^ 2 ≤ (t ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu.2 2
    have ht2' : 0 < t ^ 2 := by positivity
    have : ‖u‖ ^ 2 / t ^ 2 ≤ t ^ 2 := by
      rw [div_le_iff₀ ht2']
      nlinarith
    have := mul_le_mul_of_nonneg_left this hβ
    rw [mul_div_assoc]
    linarith
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, setLIntegral_const] at h
  calc ENNReal.ofReal (N.factorial : ℝ) * volume (placementSet N N t (4 * t)) *
        (ENNReal.ofReal (Real.exp (-(β * t ^ 2)) *
          ∫ u in A, Real.exp (β * smearedKernel lam u))) ^ N
      ≤ ENNReal.ofReal (N.factorial : ℝ) * volume (placementSet N N t (4 * t)) *
        (ENNReal.ofReal (∫ u in A,
          Real.exp (β * smearedKernel lam u - β * ‖u‖ ^ 2 / t ^ 2))) ^ N := by
        gcongr
    _ = ENNReal.ofReal (N.factorial : ℝ) * ((ENNReal.ofReal (∫ u in A,
          Real.exp (β * smearedKernel lam u - β * ‖u‖ ^ 2 / t ^ 2))) ^ N *
          volume (placementSet N N t (4 * t))) := by
        ring
    _ ≤ partitionFunction N β lam := h

end TwoComponentCoulomb

end
