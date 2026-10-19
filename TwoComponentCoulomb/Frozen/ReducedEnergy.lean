/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.Frozen.NearestNeighbor
public import TwoComponentCoulomb.Frozen.SmearedKernel

/-!
# Frozen: `TwoComponentCoulomb.reducedEnergy`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 255–257.
-/

@[expose] public section

namespace TwoComponentCoulomb

open scoped Classical in
/-- `F̃_λ` (source l. 255–257). -/
noncomputable def reducedEnergy {N : ℕ} (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) : ℝ :=
  -(1 / 2) * ∑ i, if nearestNeighbor Z (nearestNeighbor Z i) = i ∧
      charge i * charge (nearestNeighbor Z i) = -1 then
    smearedKernel lam (Z i - Z (nearestNeighbor Z i)) else 0

end TwoComponentCoulomb

end
