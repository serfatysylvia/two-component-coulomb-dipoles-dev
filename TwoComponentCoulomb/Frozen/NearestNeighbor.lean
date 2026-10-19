/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Frozen: `TwoComponentCoulomb.nearestNeighbor`

Frozen definition, approved by the authors in this exact form (RULINGS.md R17, R19).
Source: l. 217.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- `φ₁(i)`: the nearest neighbour of `z_i` among the other points, ties broken by the smallest
index in the source numbering `x₁, …, x_N, y₁, …, y_N` (source l. 217, ruling R4). -/
noncomputable def nearestNeighbor {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    Fin N ⊕ Fin N :=
  finSumFinEquiv.symm <|
    (((Finset.univ.erase i).filter fun j =>
        ∀ k ∈ Finset.univ.erase i, ‖Z i - Z j‖ ≤ ‖Z i - Z k‖).map
      finSumFinEquiv.toEmbedding).min' <| by
      obtain ⟨j, hj, hmin⟩ := (Finset.univ.erase i).exists_min_image (fun j => ‖Z i - Z j‖)
        (by
          cases i with
          | inl a => exact ⟨.inr a, by simp⟩
          | inr a => exact ⟨.inl a, by simp⟩)
      exact ⟨finSumFinEquiv j, Finset.mem_map_of_mem _ (Finset.mem_filter.2 ⟨hj, hmin⟩)⟩

end TwoComponentCoulomb

end
