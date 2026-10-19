/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.Frozen.Kappa
public import TwoComponentCoulomb.Frozen.LogKernel
public import TwoComponentCoulomb.Frozen.SmearedCharge

/-!
# Frozen: `TwoComponentCoulomb.energy`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 155–158.
-/

open MeasureTheory

@[expose] public section

namespace TwoComponentCoulomb

/-- `F_λ`, eq. (eq:F3) (source l. 155–158), as the bilinear expansion of the double integral
against `∑ᵢ (δ_{xᵢ}^{(λ)} - δ_{yᵢ}^{(λ)})` (ruling R3). -/
noncomputable def energy {N : ℕ} (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) : ℝ :=
  (1 / 2) * ∑ a, ∑ b, charge a * charge b *
      ∫ p : ℂ × ℂ, logKernel (p.1 - p.2) ∂(smearedCharge (Z a) lam).prod (smearedCharge (Z b) lam)
    - N * (logKernel lam + kappa)

end TwoComponentCoulomb

end
