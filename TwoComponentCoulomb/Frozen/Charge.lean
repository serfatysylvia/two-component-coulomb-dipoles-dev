/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Frozen: `TwoComponentCoulomb.charge`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 216.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- The sign `d_i`: `+1` on the positive charges `x_i` (`inl`), `-1` on the negative charges
`y_i` (`inr`) (source l. 216). -/
def charge {N : ℕ} : Fin N ⊕ Fin N → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

end TwoComponentCoulomb

end
