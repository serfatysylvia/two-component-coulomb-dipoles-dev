/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.ReducedPartitionFunction
import TwoComponentCoulomb.UpperBound.ReducedAssembly

/-!
# Proof of the frozen statement `TwoComponentCoulomb.lemma_3_6`

Implementation module of `TwoComponentCoulomb/Frozen/Lemma36.lean` (registered in
`manifest/frozen_anchors.json`). Its theorem `TwoComponentCoulomb.UpperBound.lemma_3_6` states and
proves exactly the frozen statement (Lemma 3.6, `lemma:part nn`, source l. 922--1003): the
two-sided logarithmic expansion of the partition function `𝒦_{N,β}^λ` of the reduced dipole
model. The binders `β` and `hβ` are implicit here, since the frozen statement binds them before
the colon and is proved by `exact`.

The proof is by cases `β = 2` (`lemma_3_6_two`) and `β > 2` (`lemma_3_6_of_two_lt`), both proved in
`UpperBound/ReducedAssembly.lean` from the matching upper bounds and the placement lower bounds.

The frozen file proves its statement by `exact TwoComponentCoulomb.UpperBound.lemma_3_6`, so this
module must never import it.
-/

open scoped ENNReal

@[expose] public section

namespace TwoComponentCoulomb.UpperBound

/-- **Lemma 3.6** (`lemma:part nn`, source l. 922--1003), exactly the frozen statement
`TwoComponentCoulomb.lemma_3_6`. -/
theorem lemma_3_6 {β : ℝ} {hβ : 2 ≤ β} :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        0 < reducedPartitionFunction N β lam ∧ reducedPartitionFunction N β lam < ∞ ∧
        |Real.log (reducedPartitionFunction N β lam).toReal
            - (2 * N * Real.log N
              + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0)
                + (Real.log (dipoleConstant β hβ) - 1)))|
          ≤ C * (N * (if β = 2 then |Real.log lam| ^ (-(1 / 2 : ℝ)) else lam ^ min ((β - 2) / 2) 1)
            + Real.log (N + 1)) := by
  rcases hβ.eq_or_lt with h | h
  · subst h
    exact TwoComponentCoulomb.lemma_3_6_two hβ
  · exact TwoComponentCoulomb.lemma_3_6_of_two_lt h

end TwoComponentCoulomb.UpperBound

end
