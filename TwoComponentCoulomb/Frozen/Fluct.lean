/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.Charge

/-!
# Frozen: `TwoComponentCoulomb.fluct`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 298.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- `Fluct_N(ξ) = ∫_Λ ξ d(∑ᵢ (δ_{xᵢ} - δ_{yᵢ}))` (source l. 298). -/
noncomputable def fluct {N : ℕ} (ξ : ℂ → ℝ) (Z : Fin N ⊕ Fin N → ℂ) : ℝ :=
  ∑ i, charge i * (box N).indicator ξ (Z i)

end TwoComponentCoulomb

end
