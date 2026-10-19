-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.ReducedPartitionFunction
import TwoComponentCoulomb.UpperBound.Lemma36

/-!
# Frozen: `TwoComponentCoulomb.lemma_3_6`

Frozen statement, approved by the authors in this exact form (RULINGS.md R18, R19).
Source: l. 922–946.
-/

open scoped ENNReal

@[expose] public section

namespace TwoComponentCoulomb

/-- **Lemma 3.6** (`lemma:part nn`, source l. 922–946). -/
theorem lemma_3_6 (β : ℝ) (hβ : 2 ≤ β) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        0 < reducedPartitionFunction N β lam ∧ reducedPartitionFunction N β lam < ∞ ∧
        |Real.log (reducedPartitionFunction N β lam).toReal
            - (2 * N * Real.log N
              + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0)
                + (Real.log (dipoleConstant β hβ) - 1)))|
          ≤ C * (N * (if β = 2 then |Real.log lam| ^ (-(1 / 2 : ℝ)) else lam ^ min ((β - 2) / 2) 1)
            + Real.log (N + 1)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact TwoComponentCoulomb.UpperBound.lemma_3_6
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end TwoComponentCoulomb

end
-- FROZEN_ANCHOR_SUFFIX_END
