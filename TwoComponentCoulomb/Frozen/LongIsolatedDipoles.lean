/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import TwoComponentCoulomb.Frozen.IsIsolatedDipole
public import TwoComponentCoulomb.Frozen.NearestNeighbor

/-!
# Frozen: `TwoComponentCoulomb.longIsolatedDipoles`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 263.
-/

@[expose] public section

namespace TwoComponentCoulomb

open scoped Classical in
/-- The set of isolated dipoles of length larger than `R` (source l. 263). -/
noncomputable def longIsolatedDipoles {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ) (R : ℝ) :
    Finset (Finset (Fin N ⊕ Fin N)) :=
  (Finset.univ.filter fun i => IsIsolatedDipole Z i ∧ R < ‖Z i - Z (nearestNeighbor Z i)‖).image
    fun i => {i, nearestNeighbor Z i}

end TwoComponentCoulomb

end
