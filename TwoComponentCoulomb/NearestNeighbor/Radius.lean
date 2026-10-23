/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import TwoComponentCoulomb.Frozen.FirstNeighborRadius
public import TwoComponentCoulomb.NearestNeighbor.General

/-!
# The first-neighbour radius of a configuration on a general index set

Source: eq. (nn2) (l. 368) and the proof of Proposition 3.6
(l. 986: "`r(z_i) = ¼ min_{j ≠ i} |z_i - z_j|` and `r̃₁(z_i) = r(z_i) ∨ λ`"). The frozen
`TwoComponentCoulomb.firstNeighborRadius` is indexed by `Fin N ⊕ Fin N`; Proposition 3.6 applies
it to `p` points, so we define the same quantity over an arbitrary finite index type with at
least two elements.

## Main definitions and results

* `TwoComponentCoulomb.nnRadius lam z i`: `¼ min_{j ≠ i} ‖z i - z j‖ ∨ λ`.
* `TwoComponentCoulomb.nnRadius_eq`: the minimum is attained at the nearest neighbour
  `nnMap key z i` for every tie-break key.
* `TwoComponentCoulomb.measurable_nnRadius`: `z ↦ nnRadius lam z i` is measurable.
* `TwoComponentCoulomb.firstNeighborRadius_eq_nnRadius`: the bridge to the frozen definition.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

section Definition

variable {ι : Type*} [Fintype ι] [Nontrivial ι]

open scoped Classical in
/-- The set of indices different from `i` is nonempty as soon as the index type is nontrivial. -/
theorem erase_nonempty (i : ι) : (Finset.univ.erase i).Nonempty := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact ⟨j, by simp [hj]⟩

open scoped Classical in
/-- The first-neighbour radius `r̃₁(z_i) = (¼ min_{j ≠ i} |z_i - z_j|) ∨ λ` of eq. (nn2)
(source l. 368), for a configuration `z : ι → ℂ` indexed by a finite type with at least two
elements. -/
noncomputable def nnRadius (lam : ℝ) (z : ι → ℂ) (i : ι) : ℝ :=
  max ((Finset.univ.erase i).inf' (erase_nonempty i) (fun j => ‖z i - z j‖) / 4) lam

/-- The minimum distance to the other points is attained at the nearest neighbour `nnMap key z i`,
whichever tie-break key is used. -/
theorem nnRadius_eq (key : ι ↪ ℕ) (lam : ℝ) (z : ι → ℂ) (i : ι) :
    nnRadius lam z i = max (‖z i - z (nnMap key z i)‖ / 4) lam := by
  classical
  have h : (Finset.univ.erase i).inf' (erase_nonempty i) (fun j => ‖z i - z j‖) =
      ‖z i - z (nnMap key z i)‖ := by
    refine le_antisymm (Finset.inf'_le _ (Finset.mem_erase.2 ⟨nnMap_ne key z i, mem_univ _⟩)) ?_
    refine Finset.le_inf' _ _ fun j hj => ?_
    exact norm_sub_nnMap_le key z (Finset.mem_erase.1 hj).1
  unfold nnRadius
  rw [h]

theorem le_nnRadius (lam : ℝ) (z : ι → ℂ) (i : ι) : lam ≤ nnRadius lam z i :=
  le_max_right _ _

/-- The first-neighbour radius is a measurable function of the configuration. -/
theorem measurable_nnRadius (lam : ℝ) (i : ι) :
    Measurable fun z : ι → ℂ => nnRadius lam z i := by
  classical
  have h : Measurable ((Finset.univ.erase i).inf' (erase_nonempty i)
      fun (j : ι) (z : ι → ℂ) => ‖z i - z j‖) :=
    Finset.inf'_induction (erase_nonempty i) _ (fun f hf g hg => hf.inf hg)
      fun j _ => by fun_prop
  have h' : Measurable fun z : ι → ℂ => (Finset.univ.erase i).inf' (erase_nonempty i)
      (fun j => ‖z i - z j‖) := by
    convert h using 1
    ext z
    rw [Finset.inf'_apply]
  exact Measurable.max (h'.div_const _) measurable_const

end Definition

section Bridge

variable {N : ℕ}

/-- Bridge to the frozen definition: on `Fin N ⊕ Fin N` the radius `nnRadius` is the frozen
`firstNeighborRadius` of eq. (nn2). -/
theorem firstNeighborRadius_eq_nnRadius [Nontrivial (Fin N ⊕ Fin N)] (lam : ℝ)
    (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    firstNeighborRadius lam Z i = nnRadius lam Z i := by
  unfold firstNeighborRadius nnRadius
  congr
  exact Subsingleton.elim _ _

end Bridge

end TwoComponentCoulomb

end
