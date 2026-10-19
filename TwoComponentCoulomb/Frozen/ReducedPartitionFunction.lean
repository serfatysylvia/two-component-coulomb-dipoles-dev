/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Constructions.Pi
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.ReducedEnergy

/-!
# Frozen: `TwoComponentCoulomb.reducedPartitionFunction`

Frozen definition, approved by the authors in this exact form (RULINGS.md R18, R19).
Source: l. 922–930.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace TwoComponentCoulomb

/-- `𝒦_{N,β}^λ = ∫_{Λ^{2N}} exp(−β F̃_λ)`, the partition function of the reduced dipole model
(Lemma 3.6, source l. 922–930), in `[0, ∞]`. -/
noncomputable def reducedPartitionFunction (N : ℕ) (β lam : ℝ) : ℝ≥0∞ :=
  ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
    ENNReal.ofReal (Real.exp (-β * reducedEnergy lam Z))

end TwoComponentCoulomb

end
