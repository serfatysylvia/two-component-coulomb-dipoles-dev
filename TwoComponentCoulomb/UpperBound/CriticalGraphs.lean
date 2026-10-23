/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.CriticalCells
public import TwoComponentCoulomb.UpperBound.MarkedGraphCover
import TwoComponentCoulomb.UpperBound.MarkedGraphCount

/-!
# Critical graphs and the count before normalization

The unordered cycle count and the geometric constraint `h ≤ 2d` used in
(eq:critical-fixed-graph) and the critical electric moment.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal Nat

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### The graphs with given `(K, m, p₀)` and their number -/

open scoped Classical in
/-- The nearest-neighbour graphs `f = φ₁(Z)` with `K` components, `m` isolated pairs and `p₀`
isolated neutral pairs . -/
noncomputable def critGraphs (N K m p₀ : ℕ) : Finset (Fin N ⊕ Fin N → Fin N ⊕ Fin N) :=
  univ.filter fun f => ∃ Z : Fin N ⊕ Fin N → ℂ, nearestNeighbor Z = f ∧ numComponents Z = K ∧
    numIsolatedPairs Z = m ∧ (isolatedDipoles Z).card = p₀

theorem mem_critGraphs {K m p₀ : ℕ} {f : Fin N ⊕ Fin N → Fin N ⊕ Fin N} :
    f ∈ critGraphs N K m p₀ ↔ ∃ Z : Fin N ⊕ Fin N → ℂ, nearestNeighbor Z = f ∧
      numComponents Z = K ∧ numIsolatedPairs Z = m ∧ (isolatedDipoles Z).card = p₀ := by
  simp [critGraphs]

/-- The isolated pairs of `φ₁(Z)`, marked: a marked involution in the sense of Step 1. -/
theorem isMarkedInvolution_isolatedPairSet (Z : Fin N ⊕ Fin N → ℂ) :
    IsMarkedInvolution (numComponents Z) (numIsolatedPairs Z) (isolatedDipoles Z).card
      (cycleInvolution Z) (isolatedPairSet Z) := by
  classical
  have hT : ∀ i ∈ isolatedPairSet Z, i ∈ cycleVerts Z := fun i hi =>
    isolatedPairSet_subset_cycleVerts hi
  refine ⟨cycleInvolution_involutive Z, ?_, ?_, ?_, card_isolatedPairSet, ?_⟩
  · rw [movedPoints_cycleInvolution]
    exact card_cycleVerts_eq_two_mul_numComponents Z
  · rw [movedPoints_cycleInvolution]
    exact hT
  · intro i hi
    rw [cycleInvolution_of_mem_cycleVerts (hT i hi)]
    exact (mem_isolatedPairSet Z).2 (isIsolatedPair_nearestNeighbor ((mem_isolatedPairSet Z).1 hi))
  · rw [← card_filter_isIsolatedDipole Z]
    congr 1
    ext i
    rw [Finset.mem_filter, Finset.mem_filter, ← charge_mul_eq_neg_one_iff, isIsolatedDipole_iff,
      mem_isolatedPairSet]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi, h2⟩
      rw [cycleInvolution_of_mem_cycleVerts (mem_cycleVerts_of_isIsolatedPair hi)] at h2
      exact ⟨hi, h2⟩
    · rintro ⟨hi, h2⟩
      rw [cycleInvolution_of_mem_cycleVerts (mem_cycleVerts_of_isIsolatedPair hi)]
      exact ⟨hi, h2⟩

theorem critGraphs_subset (K m p₀ : ℕ) :
    critGraphs N K m p₀ ⊆ (markedCover N K m p₀).biUnion fun γ =>
      Fintype.piFinset fun i => if γ.1 i ≠ i then ({γ.1 i} : Finset (Fin N ⊕ Fin N)) else univ := by
  intro f hf
  obtain ⟨Z, hf, hK, hm, hp₀⟩ := mem_critGraphs.1 hf
  have hmi := isMarkedInvolution_isolatedPairSet Z
  rw [hK, hm, hp₀] at hmi
  refine Finset.mem_biUnion.2 ⟨(cycleInvolution Z, isolatedPairSet Z), mem_markedCover hmi, ?_⟩
  rw [Fintype.mem_piFinset]
  intro i
  by_cases hi : i ∈ cycleVerts Z
  · have hne : cycleInvolution Z i ≠ i := by
      rw [cycleInvolution_of_mem_cycleVerts hi]
      exact nearestNeighbor_ne Z i
    simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte, Finset.mem_singleton]
    rw [cycleInvolution_of_mem_cycleVerts hi, ← hf]
  · have : ¬ (cycleInvolution Z i ≠ i) := by
      rw [cycleInvolution_of_not_mem_cycleVerts hi]
      exact fun h' => h' rfl
    simp only [this, ↓reduceIte, Finset.mem_univ]

/-- **The critical graph count** in subsection 3.5, with unordered cycle pairs. -/
theorem card_critGraphs_le_sharp (K m p₀ : ℕ) (hp₀K : p₀ ≤ K) (hKN : K ≤ N) :
    (critGraphs N K m p₀).card ≤ N.choose p₀ * N.descFactorial p₀ *
      ((2 * N - 2 * p₀)! / ((2 * N - 2 * K)! * 2 ^ (K - p₀) * (K - p₀)!)) * (K - p₀).choose (m - p₀) *
      (2 * N) ^ (2 * N - 2 * K) := by
  refine (Finset.card_le_card (critGraphs_subset K m p₀)).trans (Finset.card_biUnion_le.trans ?_)
  have hfib : ∀ γ ∈ markedCover N K m p₀,
      (Fintype.piFinset fun i => if γ.1 i ≠ i then ({γ.1 i} : Finset (Fin N ⊕ Fin N))
        else univ).card = (2 * N) ^ (2 * N - 2 * K) := by
    intro γ hγ
    rw [card_piFinset_unmoved, card_moved_of_mem_markedCover hγ]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const]
  exact Nat.mul_le_mul_right _ (card_markedCover_le_sharp hp₀K hKN)

/-- **The critical graph count in factorial form**, retaining `2^{K-p₀}`. -/
theorem card_critGraphs_mul_pow_le {K m p₀ : ℕ} (hp₀ : p₀ ≤ m) (hmK : m ≤ K) (hKN : K ≤ N) :
    (critGraphs N K m p₀).card *
      (p₀ ! * ((N - p₀)!) ^ 2 * (2 * N - 2 * K)! * (m - p₀)! * (K - m)! * 2 ^ (K - p₀)) ≤
      (N !) ^ 2 * (2 * N - 2 * p₀)! * (2 * N) ^ (2 * N - 2 * K) :=
  sharp_count_mul_le hp₀ hmK hKN (card_critGraphs_le_sharp K m p₀ (hp₀.trans hmK) hKN)

/-- The admissible critical counts, including `h ≤ 2d`. -/
theorem critGraphs_constraints {K m p₀ : ℕ} (hne : (critGraphs N K m p₀).Nonempty) :
    p₀ ≤ m ∧ m ≤ K ∧ K ≤ N ∧ K - m ≤ 2 * (N - K) := by
  obtain ⟨f, hf⟩ := hne
  obtain ⟨Z, -, hK, hm, hp₀⟩ := mem_critGraphs.1 hf
  have hp₀m : p₀ ≤ m := by
    classical
    rw [← hp₀, ← hm]
    have h1 := card_filter_isIsolatedDipole Z
    have h2 := card_isolatedPairSet (Z := Z)
    have h3 : (univ.filter (IsIsolatedDipole Z)).card ≤ (isolatedPairSet Z).card := by
      refine Finset.card_le_card fun i hi => ?_
      exact (mem_isolatedPairSet Z).2 (Finset.mem_filter.1 hi).2.isIsolatedPair
    omega
  have hmK : m ≤ K := hm ▸ hK ▸ numIsolatedPairs_le_numComponents Z
  have hKN : K ≤ N := hK ▸ numComponents_le Z
  have hr2 : K - m ≤ 2 * (N - K) := by
    have := numComponents_le_numIsolatedPairs_add Z
    rw [hK, hm] at this
    omega
  exact ⟨hp₀m, hmK, hKN, hr2⟩

end TwoComponentCoulomb

end
