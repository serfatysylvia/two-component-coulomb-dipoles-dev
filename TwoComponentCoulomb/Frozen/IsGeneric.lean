/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.Sum

/-!
# Frozen: `TwoComponentCoulomb.IsGeneric`

Frozen definition, approved by the authors in this exact form (RULINGS.md R18, R19).
Source: l. 217, 348.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- The configuration lies outside the Lebesgue-null set excluded at source l. 217 and
l. 348: no two points coincide, and distinct unordered pairs of points are at distinct
distances. -/
def IsGeneric {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ) : Prop :=
  Function.Injective Z ∧
    ∀ i j k l, i ≠ j → k ≠ l → ‖Z i - Z j‖ = ‖Z k - Z l‖ → (i = k ∧ j = l) ∨ (i = l ∧ j = k)

end TwoComponentCoulomb

end
