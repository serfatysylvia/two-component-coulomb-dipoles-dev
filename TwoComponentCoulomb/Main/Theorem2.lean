/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TwoComponentCoulomb.Frozen.ErrorRate
public import TwoComponentCoulomb.Frozen.Fluct
public import TwoComponentCoulomb.Frozen.GibbsMeasure
import TwoComponentCoulomb.Frozen.Theorem1
import TwoComponentCoulomb.Fluctuations.Moment
import TwoComponentCoulomb.Fluctuations.Theorem2Assembly
import TwoComponentCoulomb.Fluctuations.Theorem2RateInstance

/-!
# Provider for the frozen anchor `TwoComponentCoulomb.theorem_2`

Registered implementation module of `TwoComponentCoulomb/Frozen/Theorem2.lean`. Its export
`TwoComponentCoulomb.Main.theorem_2` states and proves exactly the frozen statement (Theorem 2,
source l. 294–302; proof l. 1842–2121) by applying the rate-generic assembly
`theorem_2_of_moment_rate` (`Fluctuations/Theorem2Assembly.lean`) at the rate
`ω = errorRate β hβ`, with

* the rate properties `theorem2RateHyp_errorRate` (`Fluctuations/Theorem2RateInstance.lean`);
* the Theorem 1 input `theorem1ShapeRate_of_theorem_1` applied to the sealed
  `TwoComponentCoulomb.theorem_1`;
* the exponential moment of the electric energy `momentBound` (`Fluctuations/Moment.lean`).

This module must never import the anchor.
-/

open scoped NNReal

@[expose] public section

namespace TwoComponentCoulomb.Main

/-- **Theorem 2** (`prop:linear`), the provider of the frozen
`TwoComponentCoulomb.theorem_2`. -/
theorem theorem_2 {β : ℝ} {hβ : 2 ≤ β} :
    ∃ lamβ Mβ Cβ : ℝ, 0 < lamβ ∧ lamβ < Real.exp (-1) ∧ 0 < Mβ ∧ 0 < Cβ ∧
      ∀ M : ℝ, Mβ < M → ∃ c : ℝ, 0 < c ∧
        ∀ ξ₀ : ℂ → ℝ, HasCompactSupport ξ₀ → ∀ L : ℝ≥0, LipschitzWith L ξ₀ →
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
          gibbsMeasure N β lam
              {Z | M * N * Real.sqrt (errorRate β hβ lam) * (L : ℝ) ^ 2
                < fluct (fun x => ξ₀ ((Real.sqrt N)⁻¹ • x)) Z ^ 2}
            ≤ ENNReal.ofReal (Cβ * Real.exp (-c * Real.sqrt N * errorRate β hβ lam)) :=
  theorem_2_of_moment_rate β hβ (errorRate β hβ) (theorem2RateHyp_errorRate β hβ)
    (theorem1ShapeRate_of_theorem_1 β hβ (theorem_1 β hβ)) (momentBound β hβ)

end TwoComponentCoulomb.Main

end
