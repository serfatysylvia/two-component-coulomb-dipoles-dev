/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import TwoComponentCoulomb.Frozen.SmearedKernel

/-!
# Frozen: `TwoComponentCoulomb.dipoleConstant`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 208–213.
-/

open MeasureTheory

@[expose] public section

namespace TwoComponentCoulomb

/-- `𝒵_β`, eq. (def:Cbeta) (source l. 208–213); defined for `β ≥ 2` only (ruling R6). -/
noncomputable def dipoleConstant (β : ℝ) (_hβ : 2 ≤ β) : ℝ :=
  if β = 2 then 2 * Real.pi
  else 2 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), Real.exp (β * smearedKernel 1 r) * r

end TwoComponentCoulomb

end
