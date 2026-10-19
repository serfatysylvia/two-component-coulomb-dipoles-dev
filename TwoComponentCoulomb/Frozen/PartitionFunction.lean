/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Constructions.Pi
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.Energy

/-!
# Frozen: `TwoComponentCoulomb.partitionFunction`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 176–177.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace TwoComponentCoulomb

/-- `Z_{N,β}^λ`, eq. (eq:ZRV) (source l. 176–177), in `[0, ∞]` (ruling R10). -/
noncomputable def partitionFunction (N : ℕ) (β lam : ℝ) : ℝ≥0∞ :=
  ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
    ENNReal.ofReal (Real.exp (-β * energy lam Z))

end TwoComponentCoulomb

end
