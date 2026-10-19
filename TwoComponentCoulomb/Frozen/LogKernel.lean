/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Frozen: `TwoComponentCoulomb.logKernel`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 137–139.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- `g(x) = -log |x|` on `ℝ² = ℂ` (source l. 137–139). -/
noncomputable def logKernel (x : ℂ) : ℝ := -Real.log ‖x‖

end TwoComponentCoulomb

end
