/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.UpperAssembly
public import TwoComponentCoulomb.UpperBound.UpperRate

/-!
# The untruncated auxiliary energy of (eq:alt)

Subsection 3.4 of the paper drops the nonnegative quadratic correction
from the exponent in (gre1). The resulting energy `G` retains the untruncated second
neighbor radii. We apply the same block separation, isolated-pair estimate and graph
sum as for the Gibbs integral. The pinned source is
`source/dipole-formation.tex`, proof of Proposition 3.9.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal Classical

namespace TwoComponentCoulomb

/-- The energy `G` in (eq:alt), with its untruncated same-sign logarithmic term. -/
noncomputable def uncorrectedUpperEnergy {N : ℕ} (hN : 2 ≤ N) (lam C : ℝ)
    (Z : Fin N ⊕ Fin N → ℂ) : ℝ :=
  -(1 / 2) * ∑ i, smearedKernel lam (Z i - Z (nearestNeighbor Z i)) +
    ∑ i ∈ univ.filter (fun i => IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
      (Real.log (min (secondNeighborRadius hN lam Z i)
        (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) / firstNeighborRadius lam Z i) - C)

/-- Dropping the quadratic correction and the nonpositive graph error increases the energy. -/
theorem corollary23Bound_le_uncorrectedUpperEnergy {N : ℕ} (hN : 2 ≤ N) {C : ℝ}
    (hC : 0 ≤ C) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) :
    corollary23Bound hN C lam Z ≤ uncorrectedUpperEnergy hN lam C Z := by
  have hQ : 0 ≤ C * ∑ i ∈ univ.filter (fun i => IsIsolatedDipole Z i ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
      (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 :=
    mul_nonneg hC (sum_nonneg fun _ _ => sq_nonneg _)
  have hK : (numComponents Z : ℝ) ≤ N := by exact_mod_cast numComponents_le Z
  have hE := mul_nonneg hC (sub_nonneg.2 hK)
  unfold corollary23Bound uncorrectedUpperEnergy
  linarith only [hQ, hE]

/-- **Equation (eq:alt)**, with any of the rates admitted by the shared upper-bound
argument. The constants are uniform in `N` and `λ`, and may depend on `β`, `ω` and `C`. -/
theorem uncorrected_upper_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) (hω : UpperRateHyp β hβ ω)
    {C : ℝ} (hC : 0 < C) :
    ∃ lam₀ B : ℝ, 0 < lam₀ ∧ lam₀ ≤ Real.exp (-2) ∧ 0 < B ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam < lam₀ →
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
            ENNReal.ofReal (Real.exp (-β * uncorrectedUpperEnergy hN lam C Z)) ≤
          ENNReal.ofReal (Real.exp (2 * N * Real.log N +
            N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1) +
            B * N * ω lam + B * Real.log (N + 1))) := by
  obtain ⟨A, c, Cb, hc, hCb, hcell⟩ := UpperAssembly.exists_cellBound_of_corollary_lower_rate
    hβ ω hω C hC (fun _ hN lam Z => uncorrectedUpperEnergy hN lam C Z)
    (fun _ hN lam _ Z _ _ => corollary23Bound_le_uncorrectedUpperEnergy hN hC.le lam Z)
  obtain ⟨c', B, lam₁, hc', hB, hlam₁, hlam₁1, hsum⟩ :=
    UpperAssembly.lintegral_le_of_cellBound_rate hβ ω hω A c Cb hc hCb
  refine ⟨min lam₁ (Real.exp (-2)), B + 3, lt_min hlam₁ (Real.exp_pos _),
    min_le_right _ _, by positivity, fun N hN lam hlam hlamlt => ?_⟩
  have hlamlt₁ := hlamlt.trans_le (min_le_left _ _)
  have hlam1 := hlamlt₁.le.trans hlam₁1
  have h := hsum N hN lam hlam hlamlt₁ Set.univ
    (fun Z => ENNReal.ofReal (Real.exp (-β * uncorrectedUpperEnergy hN lam C Z))) 0 N le_rfl
    (fun K p p₀ φ T hγ => ⟨hcell N hN lam hlam hlam1 K p p₀ φ T hγ Set.univ, fun hlt => by
      obtain ⟨_, _, hKN, _⟩ := UpperCellBound.constraints_of_nonempty ⟨_, hγ⟩
      omega⟩)
  rw [Set.inter_univ] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have hω0 := hω.nonneg lam hlam
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h0 : c' * ((N : ℝ) - N) ^ 2 / N = 0 := by simp
  have h1 := mul_nonneg hN0 hω0
  linarith only [h0, h1]

/-- **Equation (eq:alt)** for the rate ω_λ `ω_λ`, also used in the paper. -/
theorem uncorrected_upper {β : ℝ} (hβ : 2 < β) {C : ℝ} (hC : 0 < C) :
    ∃ lam₀ B : ℝ, 0 < lam₀ ∧ lam₀ ≤ Real.exp (-2) ∧ 0 < B ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam < lam₀ →
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
            ENNReal.ofReal (Real.exp (-β * uncorrectedUpperEnergy hN lam C Z)) ≤
          ENNReal.ofReal (Real.exp (2 * N * Real.log N +
            N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1) +
            B * N * errorRate β hβ.le lam + B * Real.log (N + 1))) :=
  uncorrected_upper_rate hβ _ (upperRateHyp_errorRate β hβ) hC

end TwoComponentCoulomb

end
