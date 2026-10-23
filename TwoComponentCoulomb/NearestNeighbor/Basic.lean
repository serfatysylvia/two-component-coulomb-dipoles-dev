/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.Complex.Basic
public import TwoComponentCoulomb.Frozen.NearestNeighbor
public import TwoComponentCoulomb.Frozen.IsIsolatedDipole

/-!
# Basic properties of the nearest-neighbour map

Basic API for `TwoComponentCoulomb.nearestNeighbor` (source l. 199–215): `φ₁ i` is never `i`, is
at least as close to `z_i` as any other point, and is the smallest index among the points at
that distance (the tie-break of ruling R4). We also prove a characterization by these three
properties, a sufficient criterion when the nearest neighbour is strict, and the measurability
of the events `{φ₁ i = j}` and `{i is in an isolated dipole}` on the configuration space
`(Fin N ⊕ Fin N → ℂ)`.
-/

public section

namespace TwoComponentCoulomb

open Finset

variable {N : ℕ}

/-- The defining three properties of `nearestNeighbor Z i`, in the form produced by the
`Finset.min'` definition. -/
theorem nearestNeighbor_spec (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    nearestNeighbor Z i ≠ i ∧
      (∀ k, k ≠ i → ‖Z i - Z (nearestNeighbor Z i)‖ ≤ ‖Z i - Z k‖) ∧
      ∀ j, j ≠ i → (∀ k, k ≠ i → ‖Z i - Z j‖ ≤ ‖Z i - Z k‖) →
        finSumFinEquiv (nearestNeighbor Z i) ≤ finSumFinEquiv j := by
  unfold nearestNeighbor
  generalize_proofs hne
  have hmem := Finset.min'_mem _ hne
  obtain ⟨a, ha, hax⟩ := Finset.mem_map.1 hmem
  rw [Finset.mem_filter, Finset.mem_erase] at ha
  have hax' : finSumFinEquiv a = _ := hax
  rw [← hax']
  simp only [Equiv.symm_apply_apply]
  refine ⟨ha.1.1, fun k hk => ha.2 k (Finset.mem_erase.2 ⟨hk, Finset.mem_univ _⟩), ?_⟩
  intro j hj hjk
  refine hax'.le.trans (Finset.min'_le _ _ ?_)
  exact Finset.mem_map.2 ⟨j, Finset.mem_filter.2
    ⟨Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩, fun k hk => hjk k (Finset.mem_erase.1 hk).1⟩, rfl⟩

theorem nearestNeighbor_ne (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    nearestNeighbor Z i ≠ i :=
  (nearestNeighbor_spec Z i).1

theorem norm_sub_nearestNeighbor_le (Z : Fin N ⊕ Fin N → ℂ) {i k : Fin N ⊕ Fin N} (hk : k ≠ i) :
    ‖Z i - Z (nearestNeighbor Z i)‖ ≤ ‖Z i - Z k‖ :=
  (nearestNeighbor_spec Z i).2.1 k hk

theorem finSumFinEquiv_nearestNeighbor_le (Z : Fin N ⊕ Fin N → ℂ) {i k : Fin N ⊕ Fin N}
    (hk : k ≠ i) (h : ‖Z i - Z k‖ = ‖Z i - Z (nearestNeighbor Z i)‖) :
    finSumFinEquiv (nearestNeighbor Z i) ≤ finSumFinEquiv k :=
  (nearestNeighbor_spec Z i).2.2 k hk fun _ hl =>
    h ▸ norm_sub_nearestNeighbor_le Z hl

/-- Characterization of `nearestNeighbor Z i = j`: `j ≠ i` is a nearest point to `z_i` among
the other points, and has the smallest index among all such nearest points. -/
theorem nearestNeighbor_eq_iff (Z : Fin N ⊕ Fin N → ℂ) (i j : Fin N ⊕ Fin N) :
    nearestNeighbor Z i = j ↔
      j ≠ i ∧ (∀ k, k ≠ i → ‖Z i - Z j‖ ≤ ‖Z i - Z k‖) ∧
        ∀ k, k ≠ i → ‖Z i - Z k‖ = ‖Z i - Z j‖ → finSumFinEquiv j ≤ finSumFinEquiv k := by
  constructor
  · rintro rfl
    exact ⟨nearestNeighbor_ne Z i, fun k hk => norm_sub_nearestNeighbor_le Z hk,
      fun k hk h => finSumFinEquiv_nearestNeighbor_le Z hk h⟩
  · rintro ⟨hji, h₂, h₃⟩
    have hφ := nearestNeighbor_ne Z i
    have h_eq : ‖Z i - Z (nearestNeighbor Z i)‖ = ‖Z i - Z j‖ :=
      le_antisymm (norm_sub_nearestNeighbor_le Z hji) (h₂ _ hφ)
    have h1 := finSumFinEquiv_nearestNeighbor_le Z hji h_eq.symm
    have h2 := h₃ _ hφ h_eq
    exact finSumFinEquiv.injective (le_antisymm h1 h2)

/-- If `z_j` is strictly closer to `z_i` than every other point `z_k` (`k ≠ i, j`), then `j` is the
nearest neighbour of `i`, regardless of the tie-break. -/
theorem nearestNeighbor_eq_of_forall_lt (Z : Fin N ⊕ Fin N → ℂ) {i j : Fin N ⊕ Fin N}
    (hji : j ≠ i) (h : ∀ k, k ≠ i → k ≠ j → ‖Z i - Z j‖ < ‖Z i - Z k‖) :
    nearestNeighbor Z i = j := by
  rw [nearestNeighbor_eq_iff]
  refine ⟨hji, fun k hk => ?_, fun k hk hkj => ?_⟩
  · by_cases hkj : k = j
    · rw [hkj]
    · exact (h k hk hkj).le
  · by_cases hkj' : k = j
    · rw [hkj']
    · exact absurd hkj (h k hk hkj').ne'

section Measurability

open MeasureTheory

theorem measurableSet_nearestNeighbor_eq (i j : Fin N ⊕ Fin N) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | nearestNeighbor Z i = j} := by
  simp_rw [nearestNeighbor_eq_iff]
  refine Measurable.setOf ?_
  have hn : ∀ k l : Fin N ⊕ Fin N,
      Measurable fun Z : Fin N ⊕ Fin N → ℂ => ‖Z i - Z k‖ ≤ ‖Z i - Z l‖ := by
    intro k l
    exact (measurableSet_le (f := fun Z : Fin N ⊕ Fin N → ℂ => ‖Z i - Z k‖)
      (g := fun Z : Fin N ⊕ Fin N → ℂ => ‖Z i - Z l‖) (by fun_prop) (by fun_prop)).mem
  refine measurable_const.and (Measurable.and ?_ ?_)
  · exact Measurable.forall fun k => measurable_const.imp (hn j k)
  · refine Measurable.forall fun k => measurable_const.imp ?_
    refine Measurable.imp ?_ measurable_const
    exact Measurable.eq (by fun_prop) (by fun_prop)

/-- The nearest-neighbour map `Z ↦ φ₁ Z` is a measurable function of the configuration, valued in
the finite set of self-maps of the index set. -/
theorem measurable_nearestNeighbor :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => nearestNeighbor Z := by
  refine measurable_pi_iff.2 fun i => measurable_to_countable' fun j => ?_
  exact measurableSet_nearestNeighbor_eq i j

theorem measurableSet_isIsolatedDipole (i : Fin N ⊕ Fin N) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | IsIsolatedDipole Z i} := by
  have : MeasurableSingletonClass (Fin N ⊕ Fin N) := ⟨fun x => by
    rcases x with a | a <;> simp [measurableSet_sum_iff]⟩
  have hS : MeasurableSet {f : Fin N ⊕ Fin N → Fin N ⊕ Fin N |
      f (f i) = i ∧ (∀ k, (f k = i ∨ f k = f i) → k = i ∨ k = f i) ∧
        charge i * charge (f i) = -1} :=
    (Set.toFinite _).measurableSet
  exact hS.preimage measurable_nearestNeighbor

end Measurability

end TwoComponentCoulomb

end
