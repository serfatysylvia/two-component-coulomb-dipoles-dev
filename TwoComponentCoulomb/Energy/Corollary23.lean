/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.Energy
public import TwoComponentCoulomb.Frozen.FirstNeighborRadius
public import TwoComponentCoulomb.Frozen.IsGeneric
public import TwoComponentCoulomb.Frozen.IsIsolatedDipole
public import TwoComponentCoulomb.Frozen.IsIsolatedPair
public import TwoComponentCoulomb.Frozen.NearestNeighbor
public import TwoComponentCoulomb.Frozen.NumComponents
public import TwoComponentCoulomb.Frozen.SecondNearestNeighbor
public import TwoComponentCoulomb.Frozen.SecondNeighborRadius
public import TwoComponentCoulomb.Frozen.SmearedKernel
import TwoComponentCoulomb.Energy.CorominoCompare
import TwoComponentCoulomb.Frozen.Proposition22

/-!
# Provider for the frozen anchor `TwoComponentCoulomb.corollary_2_3`

Registered implementation module of `TwoComponentCoulomb/Frozen/Corollary23.lean`. Its export
`TwoComponentCoulomb.Energy.corollary_2_3` states and proves exactly the frozen statement, from the
sealed `TwoComponentCoulomb.proposition_2_2` and the explicit comparison
`TwoComponentCoulomb.mino_rhs_ge_coromino_rhs` (proof of Cor 2.3, source l. 466–489).

The anchor is sealed (`by exact` this export); this module must never import the
anchor it provides.
-/

@[expose] public section

namespace TwoComponentCoulomb.Energy

open scoped Classical in
/-- **Corollary 2.3** (`coromino`, source l. 452–464). -/
theorem corollary_2_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam →
      ∀ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) → IsGeneric Z →
        -(1 / 2) * ∑ i, smearedKernel lam (Z i - Z (nearestNeighbor Z i))
          + ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
              (Real.log (min (secondNeighborRadius hN lam Z i)
                  (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) / firstNeighborRadius lam Z i)
                - C)
          - C * ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
              (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2
          - C * ((N : ℝ) - numComponents Z)
        ≤ energy lam Z := by
  obtain ⟨C₀, hC₀, h22⟩ := TwoComponentCoulomb.proposition_2_2
  obtain ⟨C', hC', hcmp⟩ := mino_rhs_ge_coromino_rhs C₀ hC₀
  exact ⟨C', hC', fun N hN lam hlam Z hZ hgen =>
    (hcmp N hN lam hlam Z hZ hgen).trans (h22 N hN lam hlam Z hZ hgen)⟩

end TwoComponentCoulomb.Energy

end
