/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Gibbs.Measurability
public import TwoComponentCoulomb.LowerBound.AngularAverage
public import TwoComponentCoulomb.LowerBound.PolarPi

/-!
# Jensen's inequality for the angular average of the Boltzmann weight, and the dipole lower bound

Source: Proposition 4.1, Step 1 (l. 1775--1818), by the
author-approved route of ruling R12a: Jensen's inequality over radially symmetric pair
displacements, together with Newton's theorem (the dipole--dipole interactions average to zero,
`averaged_energy_eq`). This replaces the Neumann problem, the estimate (estimatesv) and the
projection inequality (hui).

* `jensen_angles` : for fixed `λ`-separated radii `s_i`,
  `(2π)^N exp(β ∑ g_λ(s_i)) ≤ ∫_{(-π,π)^N} exp(-β F_λ) dθ`.
* `prod_radial_le_lintegral_exp_energy` : the lower bound
  `∏ ∫_{|u| ∈ R_i} exp(β g_λ(u)) du ≤ ∫_{|Y_i - X_i| ∈ R_i} exp(-β F_λ(X, Y)) dY`, obtained by
  integrating `jensen_angles` against the polar measure `∏ s_i ds_i`.
* `prod_annulus_le_lintegral_exp_energy` : the same for closed annuli.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

/-- **Jensen's inequality over the directions of the dipoles** (Prop. 4.1, Step 1, ruling R12a).
For `λ`-separated radii, `(2π)^{-N} ∫ exp(-β F_λ) dθ ≥ exp(-β ⟨F_λ⟩) = exp(β ∑ g_λ(s_i))`, where
the mean `⟨F_λ⟩ = -∑ g_λ(s_i)` is computed in `averaged_energy_eq`. -/
theorem jensen_angles {N : ℕ} {lam : ℝ} (hlam : 0 < lam) (β : ℝ) (X : Fin N → ℂ) (s : Fin N → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hsep : ∀ i j, i ≠ j → s i + s j + 2 * lam ≤ ‖X i - X j‖) :
    (2 * Real.pi) ^ N * Real.exp (β * ∑ i, smearedKernel lam (s i : ℂ)) ≤
      ∫ θ in Set.univ.pi fun _ : Fin N => Ioo (-Real.pi) Real.pi,
        Real.exp (-β * energy lam (Sum.elim X fun i => X i + circleMap 0 (s i) (θ i))) := by
  set F : (Fin N → ℝ) → ℝ := fun θ =>
    energy lam (Sum.elim X fun i => X i + circleMap 0 (s i) (θ i)) with hF
  have hFc : Continuous F := (continuous_energy hlam).comp (continuous_dipoleConfig X s)
  have hmean := averaged_energy_eq hlam X s hs hsep
  set m : ℝ := (2 * Real.pi) ^ N with hm
  set Fbar : ℝ := -∑ i, smearedKernel lam (s i : ℂ) with hFbar
  set c : ℝ := Real.exp (-β * Fbar) with hc
  have hcpos : 0 < c := Real.exp_pos _
  rw [setIntegral_pi_Ioo_eq] at hmean ⊢
  have hint : Integrable F (Measure.pi fun _ : Fin N => volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    integrable_pi_Ioo_of_continuous hFc
  have hint2 : Integrable (fun θ => Real.exp (-β * F θ))
      (Measure.pi fun _ : Fin N => volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    integrable_pi_Ioo_of_continuous (Real.continuous_exp.comp (continuous_const.mul hFc))
  have hpt : ∀ θ, c * (1 + β * Fbar) - c * β * F θ ≤ Real.exp (-β * F θ) := by
    intro θ
    have h1 := Real.add_one_le_exp (-β * (F θ - Fbar))
    have h2 : Real.exp (-β * F θ) = c * Real.exp (-β * (F θ - Fbar)) := by
      rw [hc, ← Real.exp_add]
      congr 1
      ring
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_left h1 hcpos.le]
  have hmean' : ∫ θ, F θ ∂(Measure.pi fun _ : Fin N => volume.restrict (Ioo (-Real.pi) Real.pi)) =
      m * Fbar := hmean
  have hI : ∫ θ, (c * (1 + β * Fbar) - c * β * F θ)
      ∂(Measure.pi fun _ : Fin N => volume.restrict (Ioo (-Real.pi) Real.pi)) = m * c := by
    rw [integral_sub (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul,
      hmean', measureReal_pi_Ioo_univ, smul_eq_mul]
    ring
  have hlow := integral_mono ((integrable_const (c * (1 + β * Fbar))).sub (hint.const_mul (c * β)))
    hint2 hpt
  have hc' : c = Real.exp (β * ∑ i, smearedKernel lam (s i : ℂ)) := by
    rw [hc, hFbar]
    congr 1
    ring
  rw [← hc']
  exact hI ▸ hlow

/-! ### The fibre bound: Jensen in `lintegral` form -/

/-- For fixed `λ`-separated radii `s_i`, the product of the radial weights `exp(β g_λ(s_i)) · 2π`
is bounded by the `lintegral` over the angles of the Boltzmann weight (Jensen's inequality,
`jensen_angles`). -/
theorem prod_exp_smearedKernel_le_lintegral_angles {N : ℕ} {lam : ℝ} (hlam : 0 < lam) (β : ℝ)
    (X : Fin N → ℂ) (s : Fin N → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hsep : ∀ i j, i ≠ j → s i + s j + 2 * lam ≤ ‖X i - X j‖) :
    ∏ i, (ENNReal.ofReal (Real.exp (β * smearedKernel lam (s i : ℂ))) *
        ENNReal.ofReal (2 * Real.pi)) ≤
      ∫⁻ θ in Set.univ.pi (fun _ : Fin N => Ioo (-Real.pi) Real.pi),
        ENNReal.ofReal (Real.exp (-β *
          energy lam (Sum.elim X fun i => X i + circleMap 0 (s i) (θ i)))) := by
  have hJ := jensen_angles hlam β X s hs hsep
  have hcont : Continuous fun θ : Fin N → ℝ => Real.exp (-β *
      energy lam (Sum.elim X fun i => X i + circleMap 0 (s i) (θ i))) :=
    Real.continuous_exp.comp (continuous_const.mul
      ((continuous_energy hlam).comp (continuous_dipoleConfig X s)))
  have hint : IntegrableOn (fun θ : Fin N → ℝ => Real.exp (-β *
      energy lam (Sum.elim X fun i => X i + circleMap 0 (s i) (θ i))))
      (Set.univ.pi fun _ : Fin N => Ioo (-Real.pi) Real.pi) := by
    rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi]
    exact integrable_pi_Ioo_of_continuous hcont
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun θ =>
    (Real.exp_pos _).le)]
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hJ)
  have h1 : ∀ i : Fin N, ENNReal.ofReal (Real.exp (β * smearedKernel lam (s i : ℂ))) *
      ENNReal.ofReal (2 * Real.pi) =
      ENNReal.ofReal (Real.exp (β * smearedKernel lam (s i : ℂ)) * (2 * Real.pi)) := fun i =>
    (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
  simp_rw [h1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, ← Finset.mul_sum,
    mul_comm]

/-! ### The radial weight of one dipole -/

/-- The radial profile `ρ(t) = exp(β g_λ(t))` of the weight of a dipole of length `t`, as an
extended nonnegative real. -/
noncomputable def dipoleWeight (lam β : ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (β * smearedKernel lam (t : ℂ)))

theorem measurable_dipoleWeight (lam β : ℝ) : Measurable (dipoleWeight lam β) := by
  unfold dipoleWeight
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul ((measurable_smearedKernel lam).comp Complex.measurable_ofReal)))

/-- The integral of `exp(β g_λ)` over a radial set `{u | |u| ∈ R}`, with `R ⊆ [0, b]`, in polar
coordinates. -/
theorem ofReal_setIntegral_exp_smearedKernel_eq {lam : ℝ} (hlam : 0 < lam) (β : ℝ) (R : Set ℝ)
    (hR : MeasurableSet R) {b : ℝ} (hRb : R ⊆ Icc 0 b) :
    ENNReal.ofReal (∫ u in {u : ℂ | ‖u‖ ∈ R}, Real.exp (β * smearedKernel lam u)) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t *
        (R.indicator (dipoleWeight lam β) t * ENNReal.ofReal (2 * Real.pi)) := by
  have hsub : {u : ℂ | ‖u‖ ∈ R} ⊆ Metric.closedBall (0 : ℂ) b := fun u hu => by
    simpa using (hRb hu).2
  have hcont : Continuous fun u : ℂ => Real.exp (β * smearedKernel lam u) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_smearedKernel hlam))
  have hint : IntegrableOn (fun u : ℂ => Real.exp (β * smearedKernel lam u))
      {u : ℂ | ‖u‖ ∈ R} :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 b)).mono_set hsub
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun u =>
    (Real.exp_pos _).le), ← lintegral_radial_set R hR _ (measurable_dipoleWeight lam β)]
  refine lintegral_congr fun u => ?_
  simp only [dipoleWeight]
  rw [smearedKernel_eq_norm lam u]

/-! ### The dipole lower bound -/

theorem measurable_sumElim {N : ℕ} (X : Fin N → ℂ) :
    Measurable fun Y : Fin N → ℂ => (Sum.elim X Y : Fin N ⊕ Fin N → ℂ) := by
  refine measurable_pi_iff.2 fun a => ?_
  rcases a with i | i
  · exact measurable_const
  · exact measurable_pi_apply i

/-- **The dipole lower bound** (Prop. 4.1, Steps 1--3 input; ruling R12a), for radial sets.
Let the positive charges sit at `X_i` and let the negative charge `Y_i` range over
`{Y_i | |Y_i - X_i| ∈ R_i}`, where `R_i ⊆ [0, b_i]` is measurable and the discs of radii `b_i` are
`2λ`-separated. Then the integral of the Boltzmann weight `exp(-β F_λ)` over the positions of the
negative charges is at least the product, over the dipoles, of the integrals of `exp(β g_λ)` over
the radial sets: Jensen's inequality over the directions replaces the energy by its angular
average `-∑ g_λ(s_i)`. -/
theorem prod_radial_le_lintegral_exp_energy {N : ℕ} {lam : ℝ} (hlam : 0 < lam) (β : ℝ)
    (X : Fin N → ℂ) (R : Fin N → Set ℝ) (b : Fin N → ℝ) (hR : ∀ i, MeasurableSet (R i))
    (hRb : ∀ i, R i ⊆ Icc 0 (b i))
    (hsep : ∀ i j, i ≠ j → b i + b j + 2 * lam ≤ ‖X i - X j‖) :
    ∏ i, ENNReal.ofReal (∫ u in {u : ℂ | ‖u‖ ∈ R i}, Real.exp (β * smearedKernel lam u)) ≤
      ∫⁻ Y in {Y : Fin N → ℂ | ∀ i, ‖Y i - X i‖ ∈ R i},
        ENNReal.ofReal (Real.exp (-β * energy lam (Sum.elim X Y))) := by
  classical
  set S : Set (Fin N → ℂ) := {Y | ∀ i, ‖Y i - X i‖ ∈ R i} with hSdef
  set W : (Fin N → ℂ) → ℝ≥0∞ := fun Y =>
    ENNReal.ofReal (Real.exp (-β * energy lam (Sum.elim X Y))) with hW
  have hS : MeasurableSet S := by
    have : S = ⋂ i, (fun Y : Fin N → ℂ => ‖Y i - X i‖) ⁻¹' R i := by
      ext Y
      simp [hSdef]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (by fun_prop : Measurable fun Y : Fin N → ℂ => ‖Y i - X i‖) (hR i)
  have hWm : Measurable W :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      ((measurable_energy lam).comp (measurable_sumElim X))))
  set Φ : (Fin N → ℂ) → ℝ≥0∞ := fun u => S.indicator W (X + u) with hΦdef
  have hΦm : Measurable Φ :=
    (hWm.indicator hS).comp (measurable_const.add measurable_id)
  -- translate to the origin
  have h1 : ∫⁻ Y in S, W Y = ∫⁻ u, Φ u := by
    rw [← lintegral_indicator hS]
    exact (lintegral_add_left_eq_self (S.indicator W) X).symm
  -- the weights of single dipoles
  set h : Fin N → ℝ → ℝ≥0∞ := fun i t =>
    ENNReal.ofReal t * ((R i).indicator (dipoleWeight lam β) t * ENNReal.ofReal (2 * Real.pi))
    with hh
  have hhm : ∀ i, Measurable (h i) := fun i =>
    ENNReal.measurable_ofReal.mul (((measurable_dipoleWeight lam β).indicator (hR i)).mul
      measurable_const)
  have hL : ∀ i, ENNReal.ofReal (∫ u in {u : ℂ | ‖u‖ ∈ R i}, Real.exp (β * smearedKernel lam u)) =
      ∫⁻ t in Ioi (0 : ℝ), h i t := fun i =>
    ofReal_setIntegral_exp_smearedKernel_eq hlam β (R i) (hR i) (hRb i)
  -- the fibre inequality
  have hfib : ∀ s ∈ Set.univ.pi (fun _ : Fin N => Ioi (0 : ℝ)), ∏ i, h i (s i) ≤
      ∫⁻ θ in Set.univ.pi (fun _ : Fin N => Ioo (-Real.pi) Real.pi),
        (∏ i, ENNReal.ofReal (s i)) * Φ (fun i => circleMap 0 (s i) (θ i)) := by
    intro s hs
    have hs0 : ∀ i, 0 < s i := fun i => by simpa using hs i (Set.mem_univ i)
    have hnorm : ∀ (i : Fin N) (θ : ℝ), ‖circleMap 0 (s i) θ‖ = s i := fun i θ => by
      rw [norm_circleMap_zero, abs_of_pos (hs0 i)]
    have hmeas : Measurable fun θ : Fin N → ℝ => Φ (fun i => circleMap 0 (s i) (θ i)) := by
      refine hΦm.comp (measurable_pi_iff.2 fun i => ?_)
      exact (continuous_circleMap 0 (s i)).measurable.comp (measurable_pi_apply i)
    rw [lintegral_const_mul _ hmeas, Finset.prod_mul_distrib]
    gcongr
    by_cases hall : ∀ i, s i ∈ R i
    · have hΦ : ∀ θ : Fin N → ℝ, Φ (fun i => circleMap 0 (s i) (θ i)) =
          ENNReal.ofReal (Real.exp (-β *
            energy lam (Sum.elim X fun i => X i + circleMap 0 (s i) (θ i)))) := by
        intro θ
        have hmem : (X + fun i => circleMap 0 (s i) (θ i)) ∈ S := by
          intro i
          simpa [hnorm] using hall i
        simp only [hΦdef, Set.indicator_of_mem hmem, hW]
        rfl
      simp_rw [hΦ]
      have hsR : ∀ i, 0 ≤ s i ∧ s i ≤ b i := fun i => hRb i (hall i)
      have := prod_exp_smearedKernel_le_lintegral_angles hlam β X s (fun i => (hsR i).1)
        (fun i j hij => by linarith [(hsR i).2, (hsR j).2, hsep i j hij])
      simpa [Set.indicator_of_mem, hall, dipoleWeight] using this
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (by simp [Set.indicator_of_notMem hi])).le.trans zero_le
  -- assemble
  rw [Finset.prod_congr rfl fun i _ => hL i, h1, lintegral_pi_complex_eq_polar Φ hΦm]
  have h2 : ∏ i, ∫⁻ t in Ioi (0 : ℝ), h i t =
      ∫⁻ s in Set.univ.pi (fun _ : Fin N => Ioi (0 : ℝ)), ∏ i, h i (s i) := by
    have hvol : (volume : Measure (Fin N → ℝ)).restrict
        (Set.univ.pi fun _ : Fin N => Ioi (0 : ℝ)) =
        Measure.pi fun _ : Fin N => volume.restrict (Ioi (0 : ℝ)) :=
      Measure.restrict_pi_pi _ _
    rw [hvol, lintegral_fin_prod_eq_prod _ h hhm]
  rw [h2]
  exact setLIntegral_mono' (MeasurableSet.univ_pi fun _ => measurableSet_Ioi) hfib

/-- **The dipole lower bound for annuli** (Prop. 4.1, Step 1, ruling R12a). If the negative charge
`Y_i` ranges over the closed annulus `a_i ≤ |Y_i - X_i| ≤ b_i` about the positive charge `X_i`,
and the discs of radii `b_i` about the `X_i` are `2λ`-separated, then
`∏ ∫_{a_i ≤ |u| ≤ b_i} exp(β g_λ(u)) du ≤ ∫ exp(-β F_λ(X, Y)) dY`. -/
theorem prod_annulus_le_lintegral_exp_energy {N : ℕ} {lam : ℝ} (hlam : 0 < lam) (β : ℝ)
    (X : Fin N → ℂ) (a b : Fin N → ℝ) (hab : ∀ i, 0 ≤ a i ∧ a i ≤ b i)
    (hsep : ∀ i j, i ≠ j → b i + b j + 2 * lam ≤ ‖X i - X j‖) :
    ∏ i, ENNReal.ofReal (∫ u in {u : ℂ | a i ≤ ‖u‖ ∧ ‖u‖ ≤ b i},
        Real.exp (β * smearedKernel lam u)) ≤
      ∫⁻ Y in {Y : Fin N → ℂ | ∀ i, a i ≤ ‖Y i - X i‖ ∧ ‖Y i - X i‖ ≤ b i},
        ENNReal.ofReal (Real.exp (-β * energy lam (Sum.elim X Y))) :=
  prod_radial_le_lintegral_exp_energy hlam β X (fun i => Icc (a i) (b i)) b
    (fun _ => measurableSet_Icc) (fun i => Icc_subset_Icc (hab i).1 le_rfl) hsep

end TwoComponentCoulomb

end
