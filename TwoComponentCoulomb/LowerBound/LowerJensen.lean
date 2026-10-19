/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.LowerBound.DiscFactor
public import TwoComponentCoulomb.LowerBound.RadiusTail

/-!
# Jensen over the placement set and the lower bound for `β > 2`

Source: Proposition 4.1, Steps 2--3 (l. 1829--1899), eqs.
(minz3), (align57), (eq:volume-lower), (eq:Jensen) and the conclusion before Stirling, by the
route of ruling R12a (the exponent of the disc factor has no `-C s²/r²` correction).

* `measureReal_mul_exp_neg_le_integral` : Jensen's inequality for `exp(-g)` on a finite measure
  (tangent-line proof).
* `lintegral_prod_disc_factor_ge` : `∫_H ∏_i J(r(x_i)) ≥ vol H · A^N · exp(-C Σ_i (1/vol H) ∫_H
  (λ/r(x_i))^{β-2})` with `A = 𝒵_β λ^{2-β}` (item 4).
* `partitionFunction_ge_of_two_lt` : the lower bound
  `Z ≥ N! N^N (𝒵_β λ^{2-β})^N exp(-C N ε_λ - C √N η_λ)` for `β > 2` (item 5; the inequality of
  the source before the use of Stirling's formula).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

/-- **Jensen's inequality** for the convex function `exp(-·)` on a finite measure space of positive
total mass `V`: `V exp(-(∫ g) / V) ≤ ∫ exp(-g)`. -/
theorem measureReal_mul_exp_neg_le_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (hV : 0 < μ.real Set.univ) {g : α → ℝ} (hg : Integrable g μ)
    (hge : Integrable (fun x => Real.exp (-g x)) μ) :
    μ.real Set.univ * Real.exp (-((∫ x, g x ∂μ) / μ.real Set.univ)) ≤
      ∫ x, Real.exp (-g x) ∂μ := by
  set V := μ.real Set.univ with hVdef
  set m := (∫ x, g x ∂μ) / V with hm
  have hgm : ∫ x, g x ∂μ = m * V := by
    rw [hm]; field_simp
  have hpt : ∀ x, Real.exp (-m) * (1 - (g x - m)) ≤ Real.exp (-g x) := by
    intro x
    have h := Real.add_one_le_exp (-(g x - m))
    have : Real.exp (-g x) = Real.exp (-m) * Real.exp (-(g x - m)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    linarith
  have hint0 : Integrable (fun x => g x - m) μ := hg.sub (integrable_const m)
  have hint : Integrable (fun x => Real.exp (-m) * (1 - (g x - m))) μ :=
    ((integrable_const 1).sub hint0).const_mul _
  have h1 := integral_mono hint hge hpt
  have h2 : ∫ x, Real.exp (-m) * (1 - (g x - m)) ∂μ = Real.exp (-m) * V := by
    have e1 : ∫ x, (1 - (g x - m)) ∂μ = V - (m * V - m * V) := by
      rw [integral_sub (integrable_const 1) hint0, integral_sub hg (integrable_const m),
        integral_const, integral_const, hgm]
      simp only [smul_eq_mul]
      rw [← hVdef]
      ring
    rw [integral_const_mul, e1]
    ring
  rw [h2] at h1
  linarith

/-- **Jensen over `H`** (source l. 1856--1860, eqs. (minz3), (align57), (eq:Jensen)): there is
`C > 0` (depending only on `β`) such that for `4λ ≤ 1`,
`∫_H ∏_i J(r(x_i)) dX ≥ vol H · (𝒵_β λ^{2-β})^N · exp(-C Σ_i (1/vol H) ∫_H (λ/r(x_i))^{β-2})`,
where `J(r) = ∫_{B̄(0, r/2)} e^{β g_λ}`. -/
theorem lintegral_prod_disc_factor_ge {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → 4 * lam ≤ 1 →
      ENNReal.ofReal ((volume (placementSet N N (4 * lam) (8 * lam))).toReal *
          (dipoleConstant β hβ.le * lam ^ (2 - β)) ^ N *
          Real.exp (-(C * (∑ i, ∫ X in placementSet N N (4 * lam) (8 * lam),
              (lam / lowerRadius hN X i) ^ (β - 2)) /
            (volume (placementSet N N (4 * lam) (8 * lam))).toReal))) ≤
        ∫⁻ X in placementSet N N (4 * lam) (8 * lam), ∏ i, ENNReal.ofReal
          (∫ u in Metric.closedBall (0 : ℂ) (lowerRadius hN X i / 2),
            Real.exp (β * smearedKernel lam u)) := by
  obtain ⟨C, hC, hdisc⟩ := disc_factor_ge hβ
  refine ⟨C, hC, fun N hN lam hlam h4 => ?_⟩
  set H := placementSet N N (4 * lam) (8 * lam) with hH
  have hHm : MeasurableSet H := measurableSet_placementSet _ _ _ _
  set V := (volume H).toReal with hV
  by_cases hV0 : V = 0
  · simp [hV0]
  have hVpos : 0 < V := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hV0)
  have hfin : volume H ≠ ⊤ := fun h => hV0 (by simp [hV, h])
  have : IsFiniteMeasure (volume.restrict H) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  set μ : Measure (Fin N → ℂ) := volume.restrict H with hμ
  have hμV : μ.real Set.univ = V := by
    rw [hμ, measureReal_def, Measure.restrict_apply_univ]
  set A : ℝ := dipoleConstant β hβ.le * lam ^ (2 - β) with hA
  have hApos : 0 < A := mul_pos (dipoleConstant_pos β hβ.le) (Real.rpow_pos_of_pos hlam _)
  set f : Fin N → (Fin N → ℂ) → ℝ := fun i X => (lam / lowerRadius hN X i) ^ (β - 2) with hf
  have hfmeas : ∀ i, Measurable (f i) := fun i =>
    (measurable_const.div (measurable_lowerRadius hN i)).pow_const _
  have hfb : ∀ i, ∀ X ∈ H, 0 ≤ f i X ∧ f i X ≤ 1 := by
    intro i X hX
    have h4r := four_mul_le_lowerRadius hN h4 hX i
    have hr0 : 0 < lowerRadius hN X i := by linarith
    refine ⟨by positivity, Real.rpow_le_one (by positivity) ?_ (by linarith)⟩
    rw [div_le_one hr0]
    linarith
  have hfae : ∀ i, ∀ᵐ X ∂μ, 0 ≤ f i X ∧ f i X ≤ 1 := fun i =>
    (ae_restrict_iff' hHm).2 (Filter.Eventually.of_forall (hfb i))
  have hfint : ∀ i, Integrable (f i) μ := fun i =>
    Integrable.of_bound (hfmeas i).aestronglyMeasurable 1
      ((hfae i).mono fun X hX => by
        rw [Real.norm_of_nonneg hX.1]; exact hX.2)
  set g : (Fin N → ℂ) → ℝ := fun X => C * ∑ i, f i X with hg
  have hgint : Integrable g μ := (integrable_finsetSum _ fun i _ => hfint i).const_mul C
  have hgnn : ∀ᵐ X ∂μ, 0 ≤ g X := by
    have : ∀ᵐ X ∂μ, ∀ i, 0 ≤ f i X ∧ f i X ≤ 1 := ae_all_iff.2 hfae
    exact this.mono fun X hX => mul_nonneg hC.le (Finset.sum_nonneg fun i _ => (hX i).1)
  have hgmeas : Measurable g := (Finset.measurable_sum _ fun i _ => hfmeas i).const_mul C
  have hegint : Integrable (fun X => Real.exp (-g X)) μ :=
    Integrable.of_bound (hgmeas.neg.exp).aestronglyMeasurable 1
      (hgnn.mono fun X hX => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_one_iff.2 (by linarith))
  have hJ := measureReal_mul_exp_neg_le_integral (hμV ▸ hVpos) hgint hegint
  rw [hμV] at hJ
  have hgsum : ∫ X, g X ∂μ = C * ∑ i, ∫ X in H, f i X := by
    simp only [hg]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hfint i]
  rw [hgsum] at hJ
  -- the pointwise bound
  have hpt : ∀ X ∈ H, ENNReal.ofReal (A ^ N * Real.exp (-g X)) ≤ ∏ i, ENNReal.ofReal
      (∫ u in Metric.closedBall (0 : ℂ) (lowerRadius hN X i / 2),
        Real.exp (β * smearedKernel lam u)) := by
    intro X hX
    have h1 : A ^ N * Real.exp (-g X) = ∏ i : Fin N, (A * Real.exp (-(C * f i X))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [h1, ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    refine Finset.prod_le_prod fun i _ => ENNReal.ofReal_le_ofReal ?_
    exact hdisc lam (lowerRadius hN X i) hlam (four_mul_le_lowerRadius hN h4 hX i)
  have hlow : ∫⁻ X in H, ENNReal.ofReal (A ^ N * Real.exp (-g X)) ≤
      ∫⁻ X in H, ∏ i, ENNReal.ofReal
        (∫ u in Metric.closedBall (0 : ℂ) (lowerRadius hN X i / 2),
          Real.exp (β * smearedKernel lam u)) :=
    lintegral_mono_ae ((ae_restrict_iff' hHm).2 (Filter.Eventually.of_forall hpt))
  refine le_trans ?_ hlow
  rw [← ofReal_integral_eq_lintegral_ofReal (hegint.const_mul _)
    (hgnn.mono fun X _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul]
  have hAN : 0 < A ^ N := by positivity
  calc V * A ^ N * Real.exp (-((C * ∑ i, ∫ X in H, f i X) / V))
      = A ^ N * (V * Real.exp (-((C * ∑ i, ∫ X in H, f i X) / V))) := by ring
    _ ≤ A ^ N * ∫ X, Real.exp (-g X) ∂μ := mul_le_mul_of_nonneg_left hJ hAN.le

/-- **The lower bound for `β > 2`** (source l. 1829--1899, the inequality before Stirling): there
are `λ₀, C > 0` such that for all `N ≥ 2` and `0 < λ < λ₀`,
`Z ≥ N! N^N (𝒵_β λ^{2-β})^N exp(-C N ε_λ - C √N η_λ)`. -/
theorem partitionFunction_ge_of_two_lt {β : ℝ} (hβ : 2 < β) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ENNReal.ofReal ((N.factorial : ℝ) * (N : ℝ) ^ N *
          (dipoleConstant β hβ.le * lam ^ (2 - β)) ^ N *
          Real.exp (-C * N * lowerEps β hβ lam - C * Real.sqrt N * lowerEta β hβ lam)) ≤
        partitionFunction N β lam := by
  obtain ⟨C₃, hC₃, hjen⟩ := lintegral_prod_disc_factor_ge hβ
  obtain ⟨lam₁, C₄, hlam₁, hC₄, hexp⟩ := expectation_lowerRadius_pow_le hβ
  refine ⟨min lam₁ (1 / 64), C₃ * C₄ + 256, lt_min hlam₁ (by norm_num), by positivity,
    fun N hN lam hlam hlam₀ => ?_⟩
  have hlam1 : lam < lam₁ := lt_of_lt_of_le hlam₀ (min_le_left _ _)
  have h64 : 64 * lam ≤ 1 := by
    have := lt_of_lt_of_le hlam₀ (min_le_right _ _)
    linarith
  have h4 : 4 * lam ≤ 1 := by linarith
  set H := placementSet N N (4 * lam) (8 * lam) with hH
  set V := (volume H).toReal with hV
  set A : ℝ := dipoleConstant β hβ.le * lam ^ (2 - β) with hA
  have hApos : 0 < A := mul_pos (dipoleConstant_pos β hβ.le) (Real.rpow_pos_of_pos hlam _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsqsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  -- the volume of `H`
  have hvol := volume_placementSet_ge (N := N) (a := 4 * lam) (b := 8 * lam) (by positivity)
    (by positivity) (placement_area_condition (by omega) hlam h64)
  have hvolfin : volume H ≠ ⊤ := (volume_placementSet_lt_top N N _ _).ne
  rw [ENNReal.ofReal_le_iff_le_toReal hvolfin] at hvol
  have hVlow : (N : ℝ) ^ N * Real.exp (-8 * (4 * lam) * Real.sqrt N -
      Real.pi * N * (8 * lam) ^ 2) ≤ V := hvol
  have hVpos : 0 < V := lt_of_lt_of_le (by positivity) hVlow
  -- the expectation
  set ε := lowerEps β hβ lam with hε
  set η := lowerEta β hβ lam with hη
  have hε0 : 0 ≤ ε := lowerEps_nonneg hβ hlam
  have hη0 : 0 ≤ η := lowerEta_nonneg hβ hlam
  have hsum : ∑ i : Fin N, ∫ X in H, (lam / lowerRadius hN X i) ^ (β - 2) ≤
      N * (C₄ * (ε + η / Real.sqrt N) * V) := by
    calc _ ≤ ∑ _i : Fin N, C₄ * (ε + η / Real.sqrt N) * V :=
          Finset.sum_le_sum fun i _ => hexp N hN lam hlam hlam1 i
      _ = _ := by simp
  have hm : C₃ * (∑ i : Fin N, ∫ X in H, (lam / lowerRadius hN X i) ^ (β - 2)) / V ≤
      C₃ * C₄ * (N * ε + Real.sqrt N * η) := by
    rw [div_le_iff₀ hVpos]
    have : C₃ * C₄ * (N * ε + Real.sqrt N * η) * V =
        C₃ * (N * (C₄ * (ε + η / Real.sqrt N) * V)) := by
      have hη' : Real.sqrt N * η = N * (η / Real.sqrt N) := by
        calc Real.sqrt N * η = (Real.sqrt N * Real.sqrt N) * (η / Real.sqrt N) := by
              field_simp
          _ = N * (η / Real.sqrt N) := by rw [hsqsq]
      linear_combination (C₃ * C₄ * V) * hη'
    rw [this]
    exact mul_le_mul_of_nonneg_left hsum hC₃.le
  -- the volume exponent
  have hlamη : lam ≤ η := le_lowerEta hβ hlam h64
  have hlamε : lam ^ 2 ≤ ε := sq_le_lowerEps hβ hlam h64
  have hc1 : 8 * (4 * lam) * Real.sqrt N + Real.pi * N * (8 * lam) ^ 2 ≤
      256 * (N * ε + Real.sqrt N * η) := by
    have hpi := Real.pi_le_four
    have h1 : 8 * (4 * lam) * Real.sqrt N ≤ 32 * (Real.sqrt N * η) := by
      have := mul_le_mul_of_nonneg_left hlamη hsqN.le
      linarith only [this]
    have h2 : Real.pi * N * (8 * lam) ^ 2 ≤ 256 * (N * ε) := by
      have : Real.pi * (8 * lam) ^ 2 ≤ 4 * (64 * lam ^ 2) := by
        have := mul_le_mul_of_nonneg_right hpi (sq_nonneg lam)
        linarith only [this]
      have h3 := mul_le_mul_of_nonneg_left this hNpos.le
      have h4' := mul_le_mul_of_nonneg_left hlamε hNpos.le
      linarith only [h3, h4']
    linarith only [h1, h2, mul_nonneg hsqN.le hη0]
  -- assemble
  have hjen' := hjen N hN lam hlam h4
  have hZ := partitionFunction_ge_lowerRadius hN hlam β h4
  refine le_trans ?_ hZ
  refine le_trans ?_ (mul_le_mul_right hjen' _)
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hX : 0 ≤ (N : ℝ) * ε + Real.sqrt N * η :=
    add_nonneg (mul_nonneg hNpos.le hε0) (mul_nonneg hsqN.le hη0)
  have hexp1 : Real.exp (-(C₃ * C₄ + 256) * N * ε - (C₃ * C₄ + 256) * Real.sqrt N * η) ≤
      Real.exp (-(8 * (4 * lam) * Real.sqrt N + Real.pi * N * (8 * lam) ^ 2)) *
        Real.exp (-(C₃ * (∑ i : Fin N, ∫ X in H, (lam / lowerRadius hN X i) ^ (β - 2)) / V)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith only [hc1, hm]
  have hVlow' : (N : ℝ) ^ N * Real.exp (-(8 * (4 * lam) * Real.sqrt N +
      Real.pi * N * (8 * lam) ^ 2)) ≤ V := by
    refine le_trans (le_of_eq ?_) hVlow
    congr 2
    ring
  have hANpos : 0 < A ^ N := by positivity
  have hfact : (0 : ℝ) ≤ N.factorial := Nat.cast_nonneg _
  calc (N.factorial : ℝ) * (N : ℝ) ^ N * A ^ N *
        Real.exp (-(C₃ * C₄ + 256) * N * ε - (C₃ * C₄ + 256) * Real.sqrt N * η)
      ≤ (N.factorial : ℝ) * (N : ℝ) ^ N * A ^ N *
        (Real.exp (-(8 * (4 * lam) * Real.sqrt N + Real.pi * N * (8 * lam) ^ 2)) *
          Real.exp (-(C₃ * (∑ i : Fin N, ∫ X in H, (lam / lowerRadius hN X i) ^ (β - 2)) / V))) :=
        mul_le_mul_of_nonneg_left hexp1 (by positivity)
    _ = (N.factorial : ℝ) * (A ^ N * ((N : ℝ) ^ N * Real.exp (-(8 * (4 * lam) * Real.sqrt N +
          Real.pi * N * (8 * lam) ^ 2))) *
          Real.exp (-(C₃ * (∑ i : Fin N, ∫ X in H, (lam / lowerRadius hN X i) ^ (β - 2)) / V))) := by
        ring
    _ ≤ (N.factorial : ℝ) * (A ^ N * V *
          Real.exp (-(C₃ * (∑ i : Fin N, ∫ X in H, (lam / lowerRadius hN X i) ^ (β - 2)) / V))) := by
        gcongr
    _ = (N.factorial : ℝ) * (V * A ^ N *
          Real.exp (-(C₃ * (∑ i : Fin N, ∫ X in H, (lam / lowerRadius hN X i) ^ (β - 2)) / V))) := by
        ring

end TwoComponentCoulomb

end
