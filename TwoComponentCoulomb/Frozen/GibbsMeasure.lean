/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.Energy
public import TwoComponentCoulomb.Frozen.PartitionFunction

/-!
# Frozen: `TwoComponentCoulomb.gibbsMeasure`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 172–174.
-/

open MeasureTheory

@[expose] public section

namespace TwoComponentCoulomb

/-- The Gibbs measure `ℙ_{N,β}^λ`, eq. (defP) (source l. 172–174). -/
noncomputable def gibbsMeasure (N : ℕ) (β lam : ℝ) : Measure (Fin N ⊕ Fin N → ℂ) :=
  (partitionFunction N β lam)⁻¹ •
    (volume.restrict (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N)).withDensity
      fun Z => ENNReal.ofReal (Real.exp (-β * energy lam Z))

end TwoComponentCoulomb

end
