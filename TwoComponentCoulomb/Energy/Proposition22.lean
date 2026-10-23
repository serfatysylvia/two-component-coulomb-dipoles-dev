/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
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
import TwoComponentCoulomb.Energy.MinoAssembly
import TwoComponentCoulomb.Energy.MinoPairs

/-!
# Provider for the frozen anchor `TwoComponentCoulomb.proposition_2_2`

Registered implementation module of `TwoComponentCoulomb/Frozen/Proposition22.lean`. Its export
`TwoComponentCoulomb.Energy.proposition_2_2` states and proves exactly the frozen statement, with
the constant `C = 32` (`TwoComponentCoulomb.energy_ge_mino`).

The anchor is sealed (`by exact` this export); this module must never import the
anchor it provides.
-/

@[expose] public section

namespace TwoComponentCoulomb.Energy

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
  ⟨32, by norm_num, fun _ hN _ hlam Z _ _ => energy_ge_mino hN hlam Z⟩

end TwoComponentCoulomb.Energy

end
