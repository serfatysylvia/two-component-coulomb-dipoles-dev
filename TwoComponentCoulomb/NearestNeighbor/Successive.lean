/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.NearestNeighbor.Second
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-!
# Successive nearest neighbours

For each centre we order the other labels by distance, breaking ties by the source
index (ruling R4). Rank `k : Fin (2 * N - 1)` represents the manuscript's `φ_{k+1}`.
The least remaining distance defines the radius in (nn3). Its minimum is attained
at the corresponding successive neighbour, as asserted immediately after (nn3).
-/

@[expose] public section

open Finset

namespace TwoComponentCoulomb

variable {N : ℕ}

/-- Distance and source index, in lexicographic order. -/
noncomputable def neighborKey (Z : Fin N ⊕ Fin N → ℂ) (i j : Fin N ⊕ Fin N) :
    ℝ ×ₗ Fin (N + N) := toLex (‖Z i - Z j‖, finSumFinEquiv j)

private theorem neighborKey_injective (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    Function.Injective (neighborKey Z i) := by
  intro j k h
  exact finSumFinEquiv.injective (congrArg (fun p => (ofLex p).2) h)

/-- The distance-index keys of all labels other than the centre. -/
noncomputable def neighborKeys (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    Finset (ℝ ×ₗ Fin (N + N)) := (univ.erase i).image (neighborKey Z i)

theorem card_neighborKeys (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    (neighborKeys Z i).card = 2 * N - 1 := by
  classical
  rw [neighborKeys, card_image_of_injective _ (neighborKey_injective Z i), card_erase_of_mem
    (mem_univ i)]
  simp [two_mul]

/-- The `(k+1)`-st nearest neighbour, with the smallest source index breaking a distance tie. -/
noncomputable def successiveNeighbor (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N)
    (k : Fin (2 * N - 1)) : Fin N ⊕ Fin N :=
  finSumFinEquiv.symm (ofLex ((neighborKeys Z i).orderEmbOfFin (card_neighborKeys Z i) k)).2

private theorem successiveNeighbor_key (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N)
    (k : Fin (2 * N - 1)) :
    neighborKey Z i (successiveNeighbor Z i k) =
      (neighborKeys Z i).orderEmbOfFin (card_neighborKeys Z i) k := by
  classical
  obtain ⟨j, hj, he⟩ := mem_image.mp
    ((neighborKeys Z i).orderEmbOfFin_mem (card_neighborKeys Z i) k)
  rw [successiveNeighbor, ← he]
  simp only [neighborKey, ofLex_toLex, Equiv.symm_apply_apply]

/-- Every successive neighbour differs from the centre. -/
theorem successiveNeighbor_ne (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N)
    (k : Fin (2 * N - 1)) : successiveNeighbor Z i k ≠ i := by
  classical
  have h := (neighborKeys Z i).orderEmbOfFin_mem (card_neighborKeys Z i) k
  rw [← successiveNeighbor_key] at h
  obtain ⟨j, hj, he⟩ := mem_image.mp h
  have heq := neighborKey_injective Z i he
  exact heq ▸ (mem_erase.mp hj).1

/-- Successive neighbours have distinct labels. -/
theorem successiveNeighbor_injective (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    Function.Injective (successiveNeighbor Z i) := by
  intro k l h
  apply (neighborKeys Z i).orderEmbOfFin (card_neighborKeys Z i) |>.injective
  rw [← successiveNeighbor_key, ← successiveNeighbor_key, h]

/-- Every other label occurs at one rank. -/
theorem exists_successiveNeighbor_eq (Z : Fin N ⊕ Fin N → ℂ) {i j : Fin N ⊕ Fin N}
    (hj : j ≠ i) : ∃ k, successiveNeighbor Z i k = j := by
  classical
  have hm : neighborKey Z i j ∈ neighborKeys Z i := mem_image_of_mem _ (mem_erase.mpr
    ⟨hj, mem_univ j⟩)
  obtain ⟨k, hk⟩ := (neighborKeys Z i).orderIsoOfFin (card_neighborKeys Z i) |>.surjective ⟨_, hm⟩
  refine ⟨k, neighborKey_injective Z i ?_⟩
  rw [successiveNeighbor_key]
  exact congrArg Subtype.val hk

/-- Each successive neighbour minimizes distance among the labels not previously selected.
The second conclusion records the source-index tie-break. -/
theorem successiveNeighbor_min (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N)
    (k : Fin (2 * N - 1)) {j : Fin N ⊕ Fin N} (hj : j ≠ i)
    (hprev : ∀ l, l < k → successiveNeighbor Z i l ≠ j) :
    ‖Z i - Z (successiveNeighbor Z i k)‖ ≤ ‖Z i - Z j‖ ∧
      (‖Z i - Z (successiveNeighbor Z i k)‖ = ‖Z i - Z j‖ →
        finSumFinEquiv (successiveNeighbor Z i k) ≤ finSumFinEquiv j) := by
  obtain ⟨l, rfl⟩ := exists_successiveNeighbor_eq Z hj
  have hkl : k ≤ l := le_of_not_gt fun h => hprev l h rfl
  have h := ((neighborKeys Z i).orderEmbOfFin (card_neighborKeys Z i)).monotone hkl
  rw [← successiveNeighbor_key, ← successiveNeighbor_key] at h
  exact Prod.Lex.toLex_le_toLex'.mp h

/-- The first rank agrees with the frozen nearest-neighbour map. -/
theorem successiveNeighbor_zero (hN : 1 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    successiveNeighbor Z i ⟨0, by omega⟩ = nearestNeighbor Z i := by
  symm
  apply (nearestNeighbor_eq_iff Z i _).mpr
  refine ⟨successiveNeighbor_ne Z i _, fun j hj => ?_, fun j hj he => ?_⟩
  · exact (successiveNeighbor_min Z i ⟨0, by omega⟩ hj (fun l hl => by
      change l.val < 0 at hl
      omega)).1
  · exact (successiveNeighbor_min Z i ⟨0, by omega⟩ hj (fun l hl => by
      change l.val < 0 at hl
      omega)).2 he.symm

/-- The second rank agrees with the frozen map on the generic configurations of Section 2. -/
theorem successiveNeighbor_one (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) (hZ : IsGeneric Z)
    (i : Fin N ⊕ Fin N) :
    successiveNeighbor Z i ⟨1, by omega⟩ = secondNearestNeighbor hN Z i := by
  let k : Fin (2 * N - 1) := ⟨1, by omega⟩
  have hzero := successiveNeighbor_zero (by omega : 1 ≤ N) Z i
  have hne : successiveNeighbor Z i k ≠ nearestNeighbor Z i := by
    rw [← hzero]
    exact fun h => (show k ≠ ⟨0, by omega⟩ by intro he; have := congrArg Fin.val he; simp [k] at this)
      (successiveNeighbor_injective Z i h)
  have hmin := successiveNeighbor_min Z i k (secondNearestNeighbor_ne_self hN Z i)
    (fun l hl => by
      have hl0 : l = ⟨0, by omega⟩ := by
        apply Fin.ext
        change l.val = 0
        change l.val < 1 at hl
        omega
      rw [hl0, hzero]
      exact (secondNearestNeighbor_ne_nearestNeighbor hN Z i).symm)
  have he := le_antisymm hmin.1
    (norm_sub_secondNearestNeighbor_le hN Z (successiveNeighbor_ne Z i k) hne)
  rcases hZ.2 i (successiveNeighbor Z i k) i (secondNearestNeighbor hN Z i)
    (successiveNeighbor_ne Z i k).symm (secondNearestNeighbor_ne_self hN Z i).symm he with h | h
  · exact h.2
  · exact False.elim ((secondNearestNeighbor_ne_self hN Z i) h.1.symm)

/-- The labels remaining before the `(k+1)`-st choice. -/
noncomputable def successiveCandidates (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N)
    (k : Fin (2 * N - 1)) : Finset (Fin N ⊕ Fin N) :=
  (univ.erase i).filter fun j => ∀ l, l < k → successiveNeighbor Z i l ≠ j

theorem successiveNeighbor_mem_candidates (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) (k : Fin (2 * N - 1)) :
    successiveNeighbor Z i k ∈ successiveCandidates Z i k := by
  classical
  exact mem_filter.mpr ⟨mem_erase.mpr ⟨successiveNeighbor_ne Z i k, mem_univ _⟩,
    fun l hl h => (ne_of_lt hl) (successiveNeighbor_injective Z i h)⟩

/-- The radius defined by the least distance among the remaining labels, as in (nn3). -/
noncomputable def successiveNeighborRadius (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) (k : Fin (2 * N - 1)) : ℝ :=
  max ((successiveCandidates Z i k).inf'
    ⟨_, successiveNeighbor_mem_candidates Z i k⟩ (fun j => ‖Z i - Z j‖) / 4) lam

/-- The radius-neighbour identity for every rank in (nn2)–(nn3). -/
theorem successiveNeighborRadius_eq (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) (k : Fin (2 * N - 1)) :
    successiveNeighborRadius lam Z i k = max (‖Z i - Z (successiveNeighbor Z i k)‖ / 4) lam := by
  classical
  unfold successiveNeighborRadius
  congr 2
  apply le_antisymm (inf'_le _ (successiveNeighbor_mem_candidates Z i k))
  apply le_inf'
  intro j hj
  obtain ⟨hj, hprev⟩ := mem_filter.mp hj
  exact (successiveNeighbor_min Z i k (mem_erase.mp hj).1 hprev).1

/-- At the first rank the general radius is the frozen `r₁`. -/
theorem successiveNeighborRadius_zero (hN : 1 ≤ N) (lam : ℝ)
    (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    successiveNeighborRadius lam Z i ⟨0, by omega⟩ = firstNeighborRadius lam Z i := by
  rw [successiveNeighborRadius_eq, successiveNeighbor_zero hN, firstNeighborRadius_eq]

/-- At the second rank the general radius is the frozen `r₂`. -/
theorem successiveNeighborRadius_one (hN : 2 ≤ N) (lam : ℝ)
    (Z : Fin N ⊕ Fin N → ℂ) (hZ : IsGeneric Z) (i : Fin N ⊕ Fin N) :
    successiveNeighborRadius lam Z i ⟨1, by omega⟩ = secondNeighborRadius hN lam Z i := by
  rw [successiveNeighborRadius_eq, successiveNeighbor_one hN Z hZ, secondNeighborRadius_eq]

end TwoComponentCoulomb

end
