/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import TwoComponentCoulomb.Frozen.LogKernel
public import TwoComponentCoulomb.Frozen.SmearedCharge

/-!
# Frozen: `TwoComponentCoulomb.kappa`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 149–150.
-/

open MeasureTheory

@[expose] public section

namespace TwoComponentCoulomb

/-- `κ = ∬ g(x - y) dδ₀^{(1)}(x) dδ₀^{(1)}(y)` (source eq. (defkappa), l. 149–150). -/
noncomputable def kappa : ℝ :=
  ∫ p : ℂ × ℂ, logKernel (p.1 - p.2) ∂(smearedCharge 0 1).prod (smearedCharge 0 1)

end TwoComponentCoulomb

end
