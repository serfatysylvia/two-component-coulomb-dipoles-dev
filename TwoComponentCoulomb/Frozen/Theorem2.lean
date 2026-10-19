-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TwoComponentCoulomb.Frozen.ErrorRate
public import TwoComponentCoulomb.Frozen.Fluct
public import TwoComponentCoulomb.Frozen.GibbsMeasure
import TwoComponentCoulomb.Main.Theorem2

/-!
# Frozen: `TwoComponentCoulomb.theorem_2`

Frozen statement, approved by the authors in this exact form (RULINGS.md R20). Source: l. 297–305.
-/

open scoped NNReal

@[expose] public section

namespace TwoComponentCoulomb

/-- **Theorem 2** (`prop:linear`, source l. 297–305). -/
theorem theorem_2 (β : ℝ) (hβ : 2 ≤ β) :
    ∃ lamβ Mβ Cβ : ℝ, 0 < lamβ ∧ lamβ < Real.exp (-1) ∧ 0 < Mβ ∧ 0 < Cβ ∧
      ∀ M : ℝ, Mβ < M → ∃ c : ℝ, 0 < c ∧
        ∀ ξ₀ : ℂ → ℝ, HasCompactSupport ξ₀ → ∀ L : ℝ≥0, LipschitzWith L ξ₀ →
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
          gibbsMeasure N β lam
              {Z | M * N * Real.sqrt (errorRate β hβ lam) * (L : ℝ) ^ 2
                < fluct (fun x => ξ₀ ((Real.sqrt N)⁻¹ • x)) Z ^ 2}
            ≤ ENNReal.ofReal (Cβ * Real.exp (-c * Real.sqrt N * errorRate β hβ lam)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact TwoComponentCoulomb.Main.theorem_2
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end TwoComponentCoulomb

end
-- FROZEN_ANCHOR_SUFFIX_END
