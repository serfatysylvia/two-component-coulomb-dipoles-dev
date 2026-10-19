/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.Sum

/-!
# Frozen: `TwoComponentCoulomb.firstNeighborRadius`

Frozen definition, approved by the authors in this exact form (RULINGS.md R18, R19).
Source: l. 365.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- `r₁(z_i) = (¼ min_{j ≠ i} |z_i − z_j|) ∨ λ`, eq. (nn2) (source l. 365). -/
noncomputable def firstNeighborRadius {N : ℕ} (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : ℝ :=
  max ((Finset.univ.erase i).inf' (by
      cases i with
      | inl a => exact ⟨.inr a, by simp⟩
      | inr a => exact ⟨.inl a, by simp⟩) (fun j => ‖Z i - Z j‖) / 4) lam

end TwoComponentCoulomb

end
