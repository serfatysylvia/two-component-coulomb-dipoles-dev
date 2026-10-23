/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import TwoComponentCoulomb.Frozen.NearestNeighbor

/-!
# Frozen: `TwoComponentCoulomb.IsIsolatedPair`

Frozen definition, approved by the authors in this exact form (RULINGS.md R18, R19).
Source: l. 378–388.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- `i ∈ I^pair` (eq. (defIdip), source l. 378–388): `{i, φ₁ i}` is a 2-cycle of the
nearest-neighbour graph into which no other vertex points, i.e. an isolated pair (ruling R5). -/
def IsIsolatedPair {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) : Prop :=
  nearestNeighbor Z (nearestNeighbor Z i) = i ∧
    ∀ k, (nearestNeighbor Z k = i ∨ nearestNeighbor Z k = nearestNeighbor Z i) →
      k = i ∨ k = nearestNeighbor Z i

end TwoComponentCoulomb

end
