/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.Frozen.NearestNeighbor

/-!
# Frozen: `TwoComponentCoulomb.IsIsolatedDipole`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 207–215.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- `i` lies in an isolated neutral 2-cycle of the nearest-neighbour graph (an "isolated
dipole"): `{i, φ₁ i}` is a 2-cycle, no other vertex points into it, and its two charges have
opposite signs (source l. 207–215, ruling R5). -/
def IsIsolatedDipole {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) : Prop :=
  nearestNeighbor Z (nearestNeighbor Z i) = i ∧
    (∀ k, (nearestNeighbor Z k = i ∨ nearestNeighbor Z k = nearestNeighbor Z i) →
      k = i ∨ k = nearestNeighbor Z i) ∧
    charge i * charge (nearestNeighbor Z i) = -1

end TwoComponentCoulomb

end
