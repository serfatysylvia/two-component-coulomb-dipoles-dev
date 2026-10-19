/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TwoComponentCoulomb.Frozen.M0

/-!
# Frozen: `TwoComponentCoulomb.errorRate`

Frozen definition, approved by the authors in this exact form (RULINGS.md R20). Source: l. 236–244.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- `ω_λ`, eq. (eq:defgammal) (source l. 236–244); defined for `β ≥ 2` only (ruling R6). -/
noncomputable def errorRate (β : ℝ) (_hβ : 2 ≤ β) (lam : ℝ) : ℝ :=
  if β = 2 then |Real.log lam| ^ (-(1 / 5 : ℝ))
  else if β < 4 then lam ^ (2 * (β - 2) / (12 - β + 2 * M0))
  else if β = 4 then (lam * |Real.log lam|) ^ (2 / (6 + M0))
  else lam ^ (2 / (4 + M0))

end TwoComponentCoulomb

end
