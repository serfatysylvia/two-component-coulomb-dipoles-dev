/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Probability.ConditionalProbability

/-!
# Frozen: `TwoComponentCoulomb.smearedCharge`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 148.
-/

open MeasureTheory

@[expose] public section

namespace TwoComponentCoulomb

/-- `δ_z^{(a)}`: the uniform probability measure on `B(z, a)` for `a > 0` (source l. 148); the
zero measure for `a ≤ 0` (ruling R16). -/
noncomputable def smearedCharge (z : ℂ) (a : ℝ) : Measure ℂ :=
  ProbabilityTheory.cond volume (Metric.ball z a)

end TwoComponentCoulomb

end
