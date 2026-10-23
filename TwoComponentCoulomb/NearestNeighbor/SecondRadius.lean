/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.SecondNeighborRadius
public import TwoComponentCoulomb.NearestNeighbor.Radius

/-!
# The second-neighbour radius of a configuration on a general index set

Source: eq. (nn3) with `p = 2` (l. 370): `r̃₂(z_i) = (¼ min_{j ≠ i, φ₁(i)} |z_i - z_j|) ∨ λ`.
The frozen `TwoComponentCoulomb.secondNeighborRadius` is indexed by `Fin N ⊕ Fin N`; Propositions
3.8 and 3.9 use it for sub-configurations ("the distances are computed within `I`", l. 1446),
so we define the same quantity over an arbitrary finite index type with at least three elements,
with the nearest neighbour `nnMap key z i` of `NearestNeighbor/General.lean`.

## Main definitions and results

* `TwoComponentCoulomb.nnRadius2 h3 key lam z i`: `(¼ min_{j ≠ i, nnMap key z i} ‖z i - z j‖) ∨ λ`.
* `TwoComponentCoulomb.secondNeighborRadius_eq_nnRadius2`: the bridge to the frozen definition.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

section Definition

variable {ι : Type*} [Fintype ι] [Nontrivial ι]

omit [Nontrivial ι] in
open scoped Classical in
/-- With at least three indices, removing two of them leaves a nonempty set. -/
theorem erase_erase_nonempty (h3 : 3 ≤ Fintype.card ι) (i j : ι) :
    ((Finset.univ.erase i).erase j).Nonempty := by
  rw [← Finset.card_pos]
  have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.erase i) (a := j)
  have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset ι)) (a := i)
  rw [Finset.card_univ] at h2
  omega

open scoped Classical in
/-- The second-neighbour radius `r̃₂(z_i) = (¼ min_{j ≠ i, φ₁(i)} |z_i - z_j|) ∨ λ` of eq. (nn3)
with `p = 2` (source l. 370), for a configuration `z : ι → ℂ` indexed by a finite type with at
least three elements, where `φ₁(i) = nnMap key z i`. -/
noncomputable def nnRadius2 (h3 : 3 ≤ Fintype.card ι) (key : ι ↪ ℕ) (lam : ℝ) (z : ι → ℂ)
    (i : ι) : ℝ :=
  max (((Finset.univ.erase i).erase (nnMap key z i)).inf' (erase_erase_nonempty h3 i _)
    (fun j => ‖z i - z j‖) / 4) lam

variable (h3 : 3 ≤ Fintype.card ι) (key : ι ↪ ℕ)

theorem le_nnRadius2 (lam : ℝ) (z : ι → ℂ) (i : ι) : lam ≤ nnRadius2 h3 key lam z i :=
  le_max_right _ _

/-- `r̃₂(z_i) ≤ ¼ |z_i - z_j| ∨ λ` for every `j` other than `i` and its nearest neighbour. -/
theorem nnRadius2_le (lam : ℝ) (z : ι → ℂ) {i j : ι} (hji : j ≠ i) (hjφ : j ≠ nnMap key z i) :
    nnRadius2 h3 key lam z i ≤ max (‖z i - z j‖ / 4) lam := by
  classical
  unfold nnRadius2
  refine max_le_max ?_ le_rfl
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  exact Finset.inf'_le _ (Finset.mem_erase.2 ⟨hjφ, Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩⟩)

/-- `¼ |z_i - z_j| ≥ r̃₂(z_i)` fails only below `λ`: for `j ≠ i, φ₁(i)`, if every such distance is
at least `4 ρ`, then `ρ ∨ λ ≤ r̃₂(z_i)`. -/
theorem le_nnRadius2_of_forall (lam : ℝ) (z : ι → ℂ) (i : ι) {ρ : ℝ}
    (h : ∀ j, j ≠ i → j ≠ nnMap key z i → 4 * ρ ≤ ‖z i - z j‖) :
    max ρ lam ≤ nnRadius2 h3 key lam z i := by
  classical
  unfold nnRadius2
  refine max_le_max ?_ le_rfl
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
  refine Finset.le_inf' _ _ fun j hj => ?_
  have hj' := Finset.mem_erase.1 hj
  have hj'' := Finset.mem_erase.1 hj'.2
  linarith [h j hj''.1 hj'.1]

end Definition

section Bridge

variable {N : ℕ}

/-- Bridge to the frozen definition: on `Fin N ⊕ Fin N`, with the key `sumKey N` of ruling R4,
`nnRadius2` is the frozen `secondNeighborRadius` of eq. (nn3). -/
theorem secondNeighborRadius_eq_nnRadius2 [Nontrivial (Fin N ⊕ Fin N)] (hN : 2 ≤ N)
    (h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N)) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) :
    secondNeighborRadius hN lam Z i = nnRadius2 h3 (sumKey N) lam Z i := by
  have h := nearestNeighbor_eq_nnMap Z i
  unfold secondNeighborRadius nnRadius2
  congr 2
  rw [Finset.inf'_congr]
  · rw [h]
    ext j
    simp
  · intro j hj
    rfl

end Bridge

end TwoComponentCoulomb

end
