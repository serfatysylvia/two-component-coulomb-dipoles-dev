-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
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
import TwoComponentCoulomb.Energy.Corollary23

/-!
# Frozen: `TwoComponentCoulomb.corollary_2_3`

Frozen statement, approved by the authors in this exact form (RULINGS.md R18, R19).
Source: l. 452–464.
-/

@[expose] public section

namespace TwoComponentCoulomb

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
        ≤ energy lam Z :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact TwoComponentCoulomb.Energy.corollary_2_3
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end TwoComponentCoulomb

end
-- FROZEN_ANCHOR_SUFFIX_END
