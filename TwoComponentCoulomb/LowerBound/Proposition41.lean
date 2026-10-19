/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.PartitionFunction
import TwoComponentCoulomb.LowerBound.CriticalLower
import TwoComponentCoulomb.LowerBound.LowerAssembly

/-!
# Provider for the frozen anchor `TwoComponentCoulomb.proposition_4_1`

Registered implementation module of `TwoComponentCoulomb/Frozen/Proposition41.lean`. Its export
`TwoComponentCoulomb.LowerBound.proposition_4_1` states and proves exactly the frozen statement
(Proposition 4.1, source l. 1745--1759): the case `β = 2` is
`partitionFunction_two_ge_frozen_form` (`CriticalLower`), and the case `β > 2` is
`proposition_4_1_of_two_lt` (`LowerAssembly`).

The anchor is sealed with `by exact TwoComponentCoulomb.LowerBound.proposition_4_1`. This module
must never import the anchor.
-/

@[expose] public section

namespace TwoComponentCoulomb.LowerBound

/-- **Proposition 4.1** (`prop:lower bound`, source l. 1745--1759), with exactly the type of the
frozen `TwoComponentCoulomb.proposition_4_1`. -/
theorem proposition_4_1 {β : ℝ} {hβ : 2 ≤ β} :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ENNReal.ofReal (Real.exp (2 * N * Real.log N
            + N * ((if β = 2 then Real.log |Real.log lam| else (2 - β) * Real.log lam)
              + (Real.log (dipoleConstant β hβ) - 1))
            - C * N * (if β = 2 then |Real.log lam| ^ (-(1 / 5 : ℝ))
                else if β < 4 then lam ^ (β - 2)
                else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
                else lam ^ 2 * |Real.log lam|)))
          ≤ partitionFunction N β lam := by
  rcases hβ.eq_or_lt with h | h
  · subst h
    exact partitionFunction_two_ge_frozen_form hβ
  · exact proposition_4_1_of_two_lt β h

end TwoComponentCoulomb.LowerBound

end
