/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import TwoComponentCoulomb.Frozen.IsIsolatedDipole
public import TwoComponentCoulomb.Frozen.NearestNeighbor

/-!
# Frozen: `TwoComponentCoulomb.isolatedDipoles`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 230, 259.
-/

@[expose] public section

namespace TwoComponentCoulomb

open scoped Classical in
/-- The set of isolated dipoles `{i, φ₁ i}` of a configuration (source l. 230, 259). -/
noncomputable def isolatedDipoles {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ) :
    Finset (Finset (Fin N ⊕ Fin N)) :=
  (Finset.univ.filter (IsIsolatedDipole Z)).image fun i => {i, nearestNeighbor Z i}

end TwoComponentCoulomb

end
