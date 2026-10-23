-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.PartitionFunction
import TwoComponentCoulomb.LowerBound.Proposition41

/-!
# Frozen: `TwoComponentCoulomb.proposition_4_1`

Frozen statement, approved by the authors in this exact form (RULINGS.md R18, R19).
Source: l. 1657–1668.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- **Proposition 4.1** (`prop:lower bound`, source l. 1657–1668). -/
theorem proposition_4_1 (β : ℝ) (hβ : 2 ≤ β) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ENNReal.ofReal (Real.exp (2 * N * Real.log N
            + N * ((if β = 2 then Real.log |Real.log lam| else (2 - β) * Real.log lam)
              + (Real.log (dipoleConstant β hβ) - 1))
            - C * N * (if β = 2 then |Real.log lam| ^ (-(1 / 5 : ℝ))
                else if β < 4 then lam ^ (β - 2)
                else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
                else lam ^ 2 * |Real.log lam|)))
          ≤ partitionFunction N β lam :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact TwoComponentCoulomb.LowerBound.proposition_4_1
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end TwoComponentCoulomb

end
-- FROZEN_ANCHOR_SUFFIX_END
