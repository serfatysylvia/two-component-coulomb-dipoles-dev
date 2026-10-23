/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# Frozen: `TwoComponentCoulomb.box`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 110.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- The box `Λ = [0, √N]²` (source l. 110). -/
def box (N : ℕ) : Set ℂ := Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc 0 (Real.sqrt N))

end TwoComponentCoulomb

end
