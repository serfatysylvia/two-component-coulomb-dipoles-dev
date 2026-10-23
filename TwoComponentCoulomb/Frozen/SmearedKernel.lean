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
# Frozen: `TwoComponentCoulomb.smearedKernel`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 147–148.
-/

open MeasureTheory

@[expose] public section

namespace TwoComponentCoulomb

/-- `g_λ(z) = ∬ g(x - y) dδ₀^{(λ)}(x) dδ_z^{(λ)}(y)` (source eq. (eq:defgeta), l. 147–148). -/
noncomputable def smearedKernel (lam : ℝ) (z : ℂ) : ℝ :=
  ∫ p : ℂ × ℂ, logKernel (p.1 - p.2) ∂(smearedCharge 0 lam).prod (smearedCharge z lam)

end TwoComponentCoulomb

end
