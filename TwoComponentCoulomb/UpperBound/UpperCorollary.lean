/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.EnergySplit

/-!
# Separation for energies above the Corollary 2.3 expression

These internal comparison lemmas apply (gred3) to any energy above the expression in
(gre1). The Gibbs energy and the untruncated energy `G` in (eq:alt) use the same
separation, including the empty-block cases. The pinned source is
`source/dipole-formation.tex`, proof of Proposition 3.9.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace TwoComponentCoulomb.UpperCorollary

variable {N : ℕ}

/-- Internal separation for an energy above the Corollary 2.3 expression. -/
theorem lintegral_markedCell_le_mul {C : ℝ} (hC0 : 0 ≤ C)
    (hN : 2 ≤ N) {lam β : ℝ} (F : (Fin N ⊕ Fin N → ℂ) → ℝ)
    (hF : ∀ Z, (∀ i, Z i ∈ box N) → IsGeneric Z → corollary23Bound hN C lam Z ≤ F Z) (hβ : 0 ≤ β) {K p p₀ : ℕ}
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hγ : (φ, T) ∈ markedGraphs hN K p p₀) (A : Set (Fin N ⊕ Fin N → ℂ))
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}]
    (h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts φ}) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (-β * F Z)) ≤
      ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ((∫⁻ x in (Set.univ.pi fun _ : {i // i ∈ pairVerts φ} => box N) ∩
            {x | nnMap (subtypeKey (· ∈ pairVerts φ) (sumKey N)) x = pairRestrict φ},
            ENNReal.ofReal (Real.exp (-β * pairAssignedEnergy h3
              (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam C (markedSameSignIn φ T) x))) *
          ∫⁻ y in (Set.univ.pi fun _ : {i // i ∉ pairVerts φ} => box N) ∩
            {y | nnMap (subtypeKey (· ∉ pairVerts φ) (sumKey N)) y = complRestrict φ},
            ENNReal.ofReal (Real.exp (-β *
              nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam y))) := by
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ T)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (-β * F Z)) :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
          (ENNReal.ofReal (Real.exp (-β * pairAssignedEnergy h3
              (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam C (markedSameSignIn φ T)
              (fun j : {i // i ∈ pairVerts φ} => Z j))) *
            ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∉ pairVerts φ} => Z j)))) := by
        refine setLIntegral_mono' hmeas fun Z hZ => ?_
        obtain ⟨hZΛ, hZc⟩ := hZ
        have hK := numComponents_eq_of_mem_markedCell hγ hZc
        have h := (pairAssignedEnergy_add_nnEnergy_le_corollary23Bound hC0 hN lam
          hZc.2.1 hZc.2.2 h3).trans (hF Z (fun i => hZΛ i (Set.mem_univ i)) hZc.1)
        rw [hK] at h
        exact ofReal_exp_neg_mul_le_mul hβ h
    _ = ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
          ENNReal.ofReal (Real.exp (-β * pairAssignedEnergy h3
              (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam C (markedSameSignIn φ T)
              (fun j : {i // i ∈ pairVerts φ} => Z j))) *
            ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∉ pairVerts φ} => Z j))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        refine setLIntegral_subtype_mul_le (pairVerts φ) (box N) (markedCell hN φ T) _ _
          (fun Z hZ => ⟨nnMap_pairRestrict hZ.2.1, nnMap_complRestrict hZ.2.1⟩)
          (measurable_ofReal_exp_neg_mul (measurable_pairAssignedEnergy _ h3 lam C _) β)
          (measurable_ofReal_exp_neg_mul (measurable_nnEnergy _ lam) β)


/-- Internal separation for an energy above the Corollary 2.3 expression. -/
theorem lintegral_markedCell_le_mul_of_empty {C : ℝ}
    (hN : 2 ≤ N) {lam β : ℝ} (F : (Fin N ⊕ Fin N → ℂ) → ℝ)
    (hF : ∀ Z, (∀ i, Z i ∈ box N) → IsGeneric Z → corollary23Bound hN C lam Z ≤ F Z) (hβ : 0 ≤ β) {K p p₀ : ℕ}
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    (hγ : (φ, ∅) ∈ markedGraphs hN K p p₀) (A : Set (Fin N ⊕ Fin N → ℂ))
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}] :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (-β * F Z)) ≤
      ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ((∫⁻ x in (Set.univ.pi fun _ : {i // i ∈ pairVerts φ} => box N) ∩
            {x | nnMap (subtypeKey (· ∈ pairVerts φ) (sumKey N)) x = pairRestrict φ},
            ENNReal.ofReal (Real.exp (-β *
              nnEnergy (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam x))) *
          ∫⁻ y in (Set.univ.pi fun _ : {i // i ∉ pairVerts φ} => box N) ∩
            {y | nnMap (subtypeKey (· ∉ pairVerts φ) (sumKey N)) y = complRestrict φ},
            ENNReal.ofReal (Real.exp (-β *
              nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam y))) := by
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ ∅)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (-β * F Z)) :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
          (ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∈ pairVerts φ} => Z j))) *
            ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∉ pairVerts φ} => Z j)))) := by
        refine setLIntegral_mono' hmeas fun Z hZ => ?_
        obtain ⟨hZΛ, hZc⟩ := hZ
        have hK := numComponents_eq_of_mem_markedCell hγ hZc
        have h := hF Z (fun i => hZΛ i (Set.mem_univ i)) hZc.1
        rw [corollary23Bound_of_twiceIsolatedSet_eq_empty hN C lam hZc.2.2,
          neg_half_sum_smearedKernel_eq hZc.2.1 lam] at h
        rw [hK] at h
        exact ofReal_exp_neg_mul_le_mul hβ h
    _ = ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
          ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∈ pairVerts φ} => Z j))) *
            ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∉ pairVerts φ} => Z j))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        refine setLIntegral_subtype_mul_le (pairVerts φ) (box N) (markedCell hN φ ∅) _ _
          (fun Z hZ => ⟨nnMap_pairRestrict hZ.2.1, nnMap_complRestrict hZ.2.1⟩)
          (measurable_ofReal_exp_neg_mul (measurable_nnEnergy _ lam) β)
          (measurable_ofReal_exp_neg_mul (measurable_nnEnergy _ lam) β)


/-- Internal separation for an energy above the Corollary 2.3 expression. -/
theorem lintegral_markedCell_le_full_of_empty [Nontrivial (Fin N ⊕ Fin N)] {C : ℝ}
     (hN : 2 ≤ N) {lam β : ℝ} (F : (Fin N ⊕ Fin N → ℂ) → ℝ)
    (hF : ∀ Z, (∀ i, Z i ∈ box N) → IsGeneric Z → corollary23Bound hN C lam Z ≤ F Z) (hβ : 0 ≤ β)
    {K p p₀ : ℕ} {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    (hγ : (φ, ∅) ∈ markedGraphs hN K p p₀) (A : Set (Fin N ⊕ Fin N → ℂ)) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (-β * F Z)) ≤
      ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nnMap (sumKey N) Z = φ},
          ENNReal.ofReal (Real.exp (-β * nnEnergy (sumKey N) lam Z)) := by
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ ∅)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (-β * F Z)) :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
          ENNReal.ofReal (Real.exp (-β * nnEnergy (sumKey N) lam Z)) := by
        refine setLIntegral_mono' hmeas fun Z hZ => ?_
        obtain ⟨hZΛ, hZc⟩ := hZ
        have hK := numComponents_eq_of_mem_markedCell hγ hZc
        have h := hF Z (fun i => hZΛ i (Set.mem_univ i)) hZc.1
        rw [corollary23Bound_of_twiceIsolatedSet_eq_empty hN C lam hZc.2.2,
          ← nnEnergy_sumKey] at h
        rw [hK] at h
        exact ofReal_exp_neg_mul_le hβ h
    _ = ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
          ENNReal.ofReal (Real.exp (-β * nnEnergy (sumKey N) lam Z)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right (lintegral_mono_set ?_) _
        rintro Z ⟨hZΛ, hZc⟩
        exact ⟨hZΛ, (nearestNeighbor_eq_nnMap_fun Z).symm.trans hZc.2.1⟩


/-- Internal separation for an energy above the Corollary 2.3 expression. -/
theorem lintegral_markedCell_le_full [Nontrivial (Fin N ⊕ Fin N)] {C : ℝ} (hC0 : 0 ≤ C)
     (hN : 2 ≤ N) (h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N)) {lam β : ℝ}
    (F : (Fin N ⊕ Fin N → ℂ) → ℝ)
    (hF : ∀ Z, (∀ i, Z i ∈ box N) → IsGeneric Z → corollary23Bound hN C lam Z ≤ F Z) (hβ : 0 ≤ β) {K p p₀ : ℕ} {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    {T : Finset (Fin N ⊕ Fin N)} (hγ : (φ, T) ∈ markedGraphs hN K p p₀)
    (A : Set (Fin N ⊕ Fin N → ℂ)) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (-β * F Z)) ≤
      ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nnMap (sumKey N) Z = φ},
          ENNReal.ofReal (Real.exp (-β *
            pairAssignedEnergy h3 (sumKey N) lam C (markedSameSign φ T) Z)) := by
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ T)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (-β * F Z)) :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
          ENNReal.ofReal (Real.exp (-β *
            pairAssignedEnergy h3 (sumKey N) lam C (markedSameSign φ T) Z)) := by
        refine setLIntegral_mono' hmeas fun Z hZ => ?_
        obtain ⟨hZΛ, hZc⟩ := hZ
        have hK := numComponents_eq_of_mem_markedCell hγ hZc
        have h := (pairAssignedEnergy_le_corollary23Bound hC0 hN h3 lam
          hZc.2.1 hZc.2.2).trans (hF Z (fun i => hZΛ i (Set.mem_univ i)) hZc.1)
        rw [hK] at h
        exact ofReal_exp_neg_mul_le hβ h
    _ = ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
          ENNReal.ofReal (Real.exp (-β *
            pairAssignedEnergy h3 (sumKey N) lam C (markedSameSign φ T) Z)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right (lintegral_mono_set ?_) _
        rintro Z ⟨hZΛ, hZc⟩
        exact ⟨hZΛ, (nearestNeighbor_eq_nnMap_fun Z).symm.trans hZc.2.1⟩


end TwoComponentCoulomb.UpperCorollary

end
