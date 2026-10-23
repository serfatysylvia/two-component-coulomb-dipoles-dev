/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import TwoComponentCoulomb.Frozen.NearestNeighbor

/-!
# Frozen: `TwoComponentCoulomb.secondNeighborRadius`

Frozen definition, approved by the authors in this exact form (RULINGS.md R18, R19).
Source: l. 370.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- `r₂(z_i) = (¼ min_{j ∉ {i, φ₁(i)}} |z_i − z_j|) ∨ λ`, eq. (nn3) with `p = 2` (source
l. 370). It needs at least three points, hence `2 ≤ N`. -/
noncomputable def secondNeighborRadius {N : ℕ} (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : ℝ :=
  max (((Finset.univ.erase i).erase (nearestNeighbor Z i)).inf' (by
      have hcard : 0 < ((Finset.univ.erase i).erase (nearestNeighbor Z i)).card := by
        have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.erase i) (a := nearestNeighbor Z i)
        have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset (Fin N ⊕ Fin N))) (a := i)
        simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at h2
        omega
      exact Finset.card_pos.1 hcard) (fun j => ‖Z i - Z j‖) / 4) lam

end TwoComponentCoulomb

end
