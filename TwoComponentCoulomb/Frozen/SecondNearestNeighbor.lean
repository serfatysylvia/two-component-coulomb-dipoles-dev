/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import TwoComponentCoulomb.Frozen.NearestNeighbor

/-!
# Frozen: `TwoComponentCoulomb.secondNearestNeighbor`

Frozen definition, approved by the authors in this exact form (RULINGS.md R18, R19).
Source: l. 367–368.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- `φ₂(i)`: the nearest neighbour of `z_i` among the points other than `z_i` and
`z_{φ₁(i)}`, ties broken by the smallest index in the source numbering `x₁, …, x_N, y₁, …,
y_N` (source l. 367–368, ruling R4). It needs at least three points, hence `2 ≤ N`. -/
noncomputable def secondNearestNeighbor {N : ℕ} (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : Fin N ⊕ Fin N :=
  finSumFinEquiv.symm <|
    ((((Finset.univ.erase i).erase (nearestNeighbor Z i)).filter fun j =>
        ∀ k ∈ (Finset.univ.erase i).erase (nearestNeighbor Z i), ‖Z i - Z j‖ ≤ ‖Z i - Z k‖).map
      finSumFinEquiv.toEmbedding).min' <| by
      have hcard : 0 < ((Finset.univ.erase i).erase (nearestNeighbor Z i)).card := by
        have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.erase i) (a := nearestNeighbor Z i)
        have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset (Fin N ⊕ Fin N))) (a := i)
        simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at h2
        omega
      obtain ⟨j, hj, hmin⟩ := ((Finset.univ.erase i).erase (nearestNeighbor Z i)).exists_min_image
        (fun j => ‖Z i - Z j‖) (Finset.card_pos.1 hcard)
      exact ⟨finSumFinEquiv j, Finset.mem_map_of_mem _ (Finset.mem_filter.2 ⟨hj, hmin⟩)⟩

end TwoComponentCoulomb

end
