/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.Energy
public import TwoComponentCoulomb.Frozen.ErrorRate
public import TwoComponentCoulomb.Frozen.GibbsMeasure
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.Frozen.PartitionFunction
public import TwoComponentCoulomb.Frozen.ReducedEnergy
import TwoComponentCoulomb.Frozen.Lemma35
import TwoComponentCoulomb.Frozen.Proposition39And310
import TwoComponentCoulomb.Main.Theorem1Assembly

/-!
# Provider for the frozen anchor `TwoComponentCoulomb.theorem_1`

Registered implementation module of `TwoComponentCoulomb/Frozen/Theorem1.lean`. Its export
`TwoComponentCoulomb.Main.theorem_1` states and proves exactly the frozen statement (Theorem 1,
source l. 220–266) by applying the assembly `theorem_1_of_gates` (`Main/Theorem1Assembly.lean`;
proof of Theorem 1, l. 1808–1837) to the sealed anchors `TwoComponentCoulomb.lemma_3_5`
(Lemma 3.5) and `TwoComponentCoulomb.proposition_3_9_and_3_10` (Propositions 3.9 and 3.10).

This module must never import the anchor.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace TwoComponentCoulomb.Main

/-- **Theorem 1** (`theorem:th1`), the provider of the frozen
`TwoComponentCoulomb.theorem_1`. -/
theorem theorem_1 {β : ℝ} {hβ : 2 ≤ β} :
    ∃ lamβ : ℝ, 0 < lamβ ∧ lamβ < Real.exp (-1) ∧
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
          0 < partitionFunction N β lam ∧ partitionFunction N β lam < ∞ ∧
          |Real.log (partitionFunction N β lam).toReal
              - (2 * N * Real.log N
                + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                  + (if β = 2 then Real.log |Real.log lam| else 0)
                  + (Real.log (dipoleConstant β hβ) - 1)))|
            ≤ C * (N * errorRate β hβ lam + Real.log (N + 1)) ∧
          ∫⁻ Z, ENNReal.ofReal (Real.exp (β * (energy lam Z - reducedEnergy lam Z)))
              ∂gibbsMeasure N β lam
            ≤ ENNReal.ofReal (Real.exp (C * N * errorRate β hβ lam + C * Real.log (N + 1))) ∧
          ∀ p₀ : ℕ, p₀ ≤ N →
            gibbsMeasure N β lam {Z | (isolatedDipoles Z).card = p₀}
              ≤ ENNReal.ofReal (Real.exp (-c * N * (1 - (p₀ : ℝ) / N) ^ 2
                + C * N * errorRate β hβ lam + C * Real.log (N + 1)))) ∧
      (2 < β → ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, p₀' ≤ N →
          C₁ * (lam / R) ^ (β - 2) ≤ (p₀' : ℝ) / N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (Real.exp
                (-c * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) / (lam / R) ^ (β - 2))
                  + C₂ * N * errorRate β hβ lam + C₂ * Real.log (N + 1)))) ∧
      (β = 2 → ∃ C : ℝ, 0 < C ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
        ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 → ∀ p₀' : ℕ, p₀' ≤ N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (((N : ℝ) + 1) ^ C * Real.exp (-(p₀' : ℝ) + C * N *
                (errorRate β hβ lam + Real.log (1 / R) / |Real.log lam|)))) :=
  theorem_1_of_gates β hβ (lemma_3_5 β hβ) (proposition_3_9_and_3_10 β hβ)

end TwoComponentCoulomb.Main

end
