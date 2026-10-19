/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
public import TwoComponentCoulomb.Frozen.NearestNeighbor
public import TwoComponentCoulomb.NearestNeighbor.Basic

/-!
# The nearest-neighbour map of an arbitrary finite configuration

Source l. 642--644 (Gunson--Panta change of variables): "We use the notation introduced already
in Section 2, but we can apply it more generally to `p` points, and not necessarily an even number
of points." The frozen `TwoComponentCoulomb.nearestNeighbor` is indexed by `Fin N ⊕ Fin N`; this
file defines the same notion over an arbitrary finite index type `ι` with at least two elements,
with the tie-break of ruling R4 expressed through an injective *key* `key : ι ↪ ℕ` (the point
with the smallest key wins among the nearest points). We prove the same basic API as
`NearestNeighbor/Basic.lean`, identify the new definition with the frozen one on `Fin N ⊕ Fin N`
(`TwoComponentCoulomb.nearestNeighbor_eq_nnMap`), and show that the nearest-neighbour map of a
sub-configuration agrees with the global one whenever the global nearest neighbour lies in the
sub-configuration (`TwoComponentCoulomb.nnMap_restrict`).

## Main definitions and results

* `TwoComponentCoulomb.nnMap key z i`: the `j ≠ i` minimizing `‖z i - z j‖`, ties broken by the
  smallest `key j`.
* `TwoComponentCoulomb.nnMap_eq_iff`: characterization of `nnMap key z i = j`.
* `TwoComponentCoulomb.measurable_nnMap`: measurability as a map `(ι → ℂ) → (ι → ι)`.
* `TwoComponentCoulomb.sumKey`, `TwoComponentCoulomb.nearestNeighbor_eq_nnMap`: the bridge to the
  frozen definition.
* `TwoComponentCoulomb.nnMap_restrict`: restriction to a sub-configuration.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The nearest neighbour of `z i` among the *other* points `z j`, `j ≠ i`, of a configuration
`z : ι → ℂ` indexed by a finite type `ι` with at least two elements (source l. 642--644,
generalizing l. 217). Ties are broken by the smallest value of the injective key
`key : ι ↪ ℕ` (ruling R4); the key is pulled back along `Function.invFun`, which is only ever
evaluated at a value in the range of `key`. -/
noncomputable def nnMap [Nontrivial ι] (key : ι ↪ ℕ) (z : ι → ℂ) (i : ι) : ι :=
  Function.invFun key <|
    (((Finset.univ.erase i).filter fun j =>
        ∀ k ∈ Finset.univ.erase i, ‖z i - z j‖ ≤ ‖z i - z k‖).map key).min' <| by
      obtain ⟨j, hj, hmin⟩ := (Finset.univ.erase i).exists_min_image (fun j => ‖z i - z j‖)
        (by
          obtain ⟨j, hj⟩ := exists_ne i
          exact ⟨j, by simp [hj]⟩)
      exact ⟨key j, Finset.mem_map_of_mem _ (Finset.mem_filter.2 ⟨hj, hmin⟩)⟩

variable [Nontrivial ι] (key : ι ↪ ℕ) (z : ι → ℂ)

/-- The defining three properties of `nnMap key z i`, in the form produced by the `Finset.min'`
definition. -/
theorem nnMap_spec (i : ι) :
    nnMap key z i ≠ i ∧
      (∀ k, k ≠ i → ‖z i - z (nnMap key z i)‖ ≤ ‖z i - z k‖) ∧
      ∀ j, j ≠ i → (∀ k, k ≠ i → ‖z i - z j‖ ≤ ‖z i - z k‖) →
        key (nnMap key z i) ≤ key j := by
  classical
  unfold nnMap
  generalize_proofs hI hne
  have hmem := Finset.min'_mem _ hne
  obtain ⟨a, ha, hax⟩ := Finset.mem_map.1 hmem
  rw [Finset.mem_filter, Finset.mem_erase] at ha
  have hax' : key a = _ := hax
  rw [← hax', Function.leftInverse_invFun key.injective a]
  refine ⟨ha.1.1, fun k hk => ha.2 k (Finset.mem_erase.2 ⟨hk, Finset.mem_univ _⟩), ?_⟩
  intro j hj hjk
  refine hax'.le.trans (Finset.min'_le _ _ ?_)
  exact Finset.mem_map.2 ⟨j, Finset.mem_filter.2
    ⟨Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩, fun k hk => hjk k (Finset.mem_erase.1 hk).1⟩, rfl⟩

theorem nnMap_ne (i : ι) : nnMap key z i ≠ i :=
  (nnMap_spec key z i).1

theorem norm_sub_nnMap_le {i k : ι} (hk : k ≠ i) :
    ‖z i - z (nnMap key z i)‖ ≤ ‖z i - z k‖ :=
  (nnMap_spec key z i).2.1 k hk

theorem key_nnMap_le {i k : ι} (hk : k ≠ i) (h : ‖z i - z k‖ = ‖z i - z (nnMap key z i)‖) :
    key (nnMap key z i) ≤ key k :=
  (nnMap_spec key z i).2.2 k hk fun _ hl => h ▸ norm_sub_nnMap_le key z hl

/-- Characterization of `nnMap key z i = j`: `j ≠ i` is a nearest point to `z i` among the other
points, and has the smallest key among all such nearest points. -/
theorem nnMap_eq_iff (i j : ι) :
    nnMap key z i = j ↔
      j ≠ i ∧ (∀ k, k ≠ i → ‖z i - z j‖ ≤ ‖z i - z k‖) ∧
        ∀ k, k ≠ i → ‖z i - z k‖ = ‖z i - z j‖ → key j ≤ key k := by
  constructor
  · rintro rfl
    exact ⟨nnMap_ne key z i, fun k hk => norm_sub_nnMap_le key z hk,
      fun k hk h => key_nnMap_le key z hk h⟩
  · rintro ⟨hji, h₂, h₃⟩
    have hφ := nnMap_ne key z i
    have h_eq : ‖z i - z (nnMap key z i)‖ = ‖z i - z j‖ :=
      le_antisymm (norm_sub_nnMap_le key z hji) (h₂ _ hφ)
    have h1 := key_nnMap_le key z hji h_eq.symm
    have h2 := h₃ _ hφ h_eq
    exact key.injective (le_antisymm h1 h2)

section Measurability

open MeasureTheory

theorem measurableSet_nnMap_eq (i j : ι) :
    MeasurableSet {z : ι → ℂ | nnMap key z i = j} := by
  simp_rw [nnMap_eq_iff]
  refine Measurable.setOf ?_
  have hn : ∀ k l : ι, Measurable fun z : ι → ℂ => ‖z i - z k‖ ≤ ‖z i - z l‖ := by
    intro k l
    exact (measurableSet_le (f := fun z : ι → ℂ => ‖z i - z k‖)
      (g := fun z : ι → ℂ => ‖z i - z l‖) (by fun_prop) (by fun_prop)).mem
  refine measurable_const.and (Measurable.and ?_ ?_)
  · exact Measurable.forall fun k => measurable_const.imp (hn j k)
  · refine Measurable.forall fun k => measurable_const.imp ?_
    refine Measurable.imp ?_ measurable_const
    exact Measurable.eq (by fun_prop) (by fun_prop)

/-- The nearest-neighbour map `z ↦ nnMap key z` is a measurable function of the configuration,
valued in the finite set of self-maps of the index set. -/
theorem measurable_nnMap [MeasurableSpace ι] :
    Measurable fun z : ι → ℂ => nnMap key z := by
  refine measurable_pi_iff.2 fun i => measurable_to_countable' fun j => ?_
  exact measurableSet_nnMap_eq key i j

end Measurability

section Restriction

/-- Restriction to a sub-configuration (source l. 642--644): let `e : κ ↪ ι` select a
sub-configuration `z ∘ e` of `z` (for instance a subset of the indices), with the induced
tie-break key `e.trans key`. If the global nearest neighbour of `e k` lies in the sub-configuration,
it is the image of the nearest neighbour of `k` computed inside the sub-configuration. -/
theorem nnMap_restrict {κ : Type*} [Fintype κ] [Nontrivial κ] (e : κ ↪ ι) (k : κ)
    (h : nnMap key z (e k) ∈ Set.range e) :
    e (nnMap (e.trans key) (z ∘ e) k) = nnMap key z (e k) := by
  obtain ⟨j, hj⟩ := h
  have hjk : j ≠ k := fun hjk => nnMap_ne key z (e k) (hj.symm.trans (congrArg e hjk))
  have hjeq : nnMap (e.trans key) (z ∘ e) k = j := by
    rw [nnMap_eq_iff]
    refine ⟨hjk, fun l hl => ?_, fun l hl hlj => ?_⟩
    · have hl' : e l ≠ e k := fun h => hl (e.injective h)
      simpa only [Function.comp_apply, hj] using norm_sub_nnMap_le key z hl'
    · have hl' : e l ≠ e k := fun h => hl (e.injective h)
      have := key_nnMap_le key z hl' (by simpa only [Function.comp_apply, hj] using hlj)
      simpa only [Function.Embedding.trans_apply, hj] using this
  rw [hjeq, hj]

end Restriction

section Bridge

variable {N : ℕ}

/-- The tie-break key of the source numbering `x₁, …, x_N, y₁, …, y_N` of `Fin N ⊕ Fin N`
(ruling R4): the index in `Fin (N + N)` given by `finSumFinEquiv`. -/
def sumKey (N : ℕ) : (Fin N ⊕ Fin N) ↪ ℕ :=
  ⟨fun i => (finSumFinEquiv i : ℕ), Fin.val_injective.comp finSumFinEquiv.injective⟩

/-- The index type `Fin N ⊕ Fin N` of an `N`-pair configuration has at least two elements as soon
as `N ≠ 0`. -/
instance nontrivial_sum_fin [NeZero N] : Nontrivial (Fin N ⊕ Fin N) :=
  ⟨⟨Sum.inl 0, Sum.inr 0, by simp⟩⟩

/-- Bridge to the frozen definition: on `Fin N ⊕ Fin N` the map `nnMap` with the source numbering
`sumKey N` as tie-break key is the frozen `nearestNeighbor` (source l. 217, ruling R4). -/
theorem nearestNeighbor_eq_nnMap [Nontrivial (Fin N ⊕ Fin N)] (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : nearestNeighbor Z i = nnMap (sumKey N) Z i := by
  obtain ⟨h1, h2, h3⟩ := (nnMap_eq_iff (sumKey N) Z i _).1 rfl
  exact (nearestNeighbor_eq_iff Z i _).2 ⟨h1, h2, h3⟩

/-- Function form of `nearestNeighbor_eq_nnMap`. -/
theorem nearestNeighbor_eq_nnMap_fun [Nontrivial (Fin N ⊕ Fin N)] (Z : Fin N ⊕ Fin N → ℂ) :
    nearestNeighbor Z = nnMap (sumKey N) Z :=
  funext (nearestNeighbor_eq_nnMap Z)

end Bridge

end TwoComponentCoulomb

end
