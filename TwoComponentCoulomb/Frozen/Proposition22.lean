-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.Frozen.Energy
public import TwoComponentCoulomb.Frozen.FirstNeighborRadius
public import TwoComponentCoulomb.Frozen.IsGeneric
public import TwoComponentCoulomb.Frozen.Kappa
public import TwoComponentCoulomb.Frozen.LogKernel
public import TwoComponentCoulomb.Frozen.NearestNeighbor
public import TwoComponentCoulomb.Frozen.SecondNeighborRadius
public import TwoComponentCoulomb.Frozen.SmearedKernel
import TwoComponentCoulomb.Energy.Proposition22

/-!
# Frozen: `TwoComponentCoulomb.proposition_2_2`

Frozen statement, approved by the authors in this exact form (RULINGS.md R18, R19).
Source: l. 440–449.
-/

@[expose] public section

namespace TwoComponentCoulomb

open scoped Classical in
/-- **Proposition 2.2** (`prop:mino2`, source l. 440–449). The sums over `i ∈ 𝒞_k` and over
`i ∈ ℐ_k ∖ 𝒞_k`, `k = 1, …, K`, are the sums over the vertices that lie on a 2-cycle of the
nearest-neighbour graph and over the remaining (tree) vertices. -/
theorem proposition_2_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam →
      ∀ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) → IsGeneric Z →
        (1 / 2) * (∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) = i,
            (charge i * charge (nearestNeighbor Z i) * smearedKernel lam (Z i - Z (nearestNeighbor Z i))
              - charge i * (charge i + charge (nearestNeighbor Z i)) *
                  (logKernel ((min (secondNeighborRadius hN lam Z i)
                    (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) : ℝ) : ℂ) + kappa)
              - C * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2)
          - ∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) ≠ i,
              (logKernel (secondNeighborRadius hN lam Z i) + kappa))
        ≤ energy lam Z :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact TwoComponentCoulomb.Energy.proposition_2_2
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end TwoComponentCoulomb

end
-- FROZEN_ANCHOR_SUFFIX_END
