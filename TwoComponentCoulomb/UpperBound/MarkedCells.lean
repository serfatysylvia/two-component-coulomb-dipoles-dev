/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Gibbs.Generic
public import TwoComponentCoulomb.UpperBound.MarkedGraphCover

/-!
# The cell decomposition of Proposition 3.10 by marked graphs

Source: proof of Proposition 3.10, Step 2 (l. 1513--1517), which defines, for
`p₀ ≤ p ≤ K ≤ N`, `I(K,p,p₀) := max_{γ ∈ D_{2N,K,p,p₀}} log ∫_{γ_{2N} = γ} e^{-β F_λ}` (the
source writes `p̂₀`), together with the splitting of the phase space according to the
nearest-neighbour graph announced at l. 1459 ("we split the phase-space according to the nearest
neighbor graph `γ_{2N}` of the points"). Up to the Lebesgue-null set of non-generic configurations
(l. 217, 348; `TwoComponentCoulomb.lintegral_restrict_inter_isGeneric`), the box `Λ^{2N}` is the
disjoint union of the cells `{γ_{2N} = γ}` of the marked graphs `γ = (φ₁, T) ∈ D_{2N,K,p,p₀}`
(`TwoComponentCoulomb.markedGraphs`), `K, p, p₀ ≤ N`.

## Main definitions

* `TwoComponentCoulomb.markedCell hN f T`: the cell `{γ_{2N} = (f, T)}` of the generic
  configurations whose nearest-neighbour map is `f` and whose twice-isolated vertices form `T`.

## Main results

* `TwoComponentCoulomb.secondNearestNeighbor_eq_iff`: characterization of the second nearest
  neighbour `φ₂`.
* `TwoComponentCoulomb.measurableSet_twiceIsolatedSet_eq`,
  `TwoComponentCoulomb.measurableSet_markedCell`.
* `TwoComponentCoulomb.numComponents_eq_of_mem_markedCell` (and its companions for `p`, `p₀`): the
  numbers `K, p, p₀` are constant on the cell of a marked graph of `D_{2N,K,p,p₀}`.
* `TwoComponentCoulomb.lintegral_eq_sum_markedCell`: for every event `A` and every integrand `F`,
  `∫_{Λ^{2N} ∩ A} F = ∑_{K,p,p₀ ≤ N} ∑_{γ ∈ D_{2N,K,p,p₀}} ∫_{Λ^{2N} ∩ A ∩ {γ_{2N} = γ}} F`.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset MeasureTheory
open scoped ENNReal

variable {N : ℕ}

/-! ### The second nearest neighbour: characterization and measurability -/

section Second

/-- The tie-break property of `secondNearestNeighbor hN Z i`: among the points other than `z_i` and
`z_{φ₁ i}` at minimal distance from `z_i`, it has the smallest index (ruling R4). -/
theorem finSumFinEquiv_secondNearestNeighbor_le (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ)
    {i j : Fin N ⊕ Fin N} (hji : j ≠ i) (hjφ : j ≠ nearestNeighbor Z i)
    (hj : ∀ k, k ≠ i → k ≠ nearestNeighbor Z i → ‖Z i - Z j‖ ≤ ‖Z i - Z k‖) :
    finSumFinEquiv (secondNearestNeighbor hN Z i) ≤ finSumFinEquiv j := by
  unfold secondNearestNeighbor
  rw [Equiv.apply_symm_apply]
  refine Finset.min'_le _ _ (Finset.mem_map.2 ⟨j, Finset.mem_filter.2
    ⟨Finset.mem_erase.2 ⟨hjφ, Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩⟩, fun k hk => ?_⟩, rfl⟩)
  obtain ⟨hk1, hk2⟩ := Finset.mem_erase.1 hk
  exact hj k (Finset.mem_erase.1 hk2).1 hk1

/-- Characterization of `secondNearestNeighbor hN Z i = j`: `j ∉ {i, φ₁ i}` is a nearest point to
`z_i` among the points other than `z_i, z_{φ₁ i}`, with the smallest index among all such nearest
points (source l. 367--368, ruling R4). -/
theorem secondNearestNeighbor_eq_iff (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) (i j : Fin N ⊕ Fin N) :
    secondNearestNeighbor hN Z i = j ↔
      j ≠ i ∧ j ≠ nearestNeighbor Z i ∧
        (∀ k, k ≠ i → k ≠ nearestNeighbor Z i → ‖Z i - Z j‖ ≤ ‖Z i - Z k‖) ∧
        ∀ k, k ≠ i → k ≠ nearestNeighbor Z i → ‖Z i - Z k‖ = ‖Z i - Z j‖ →
          finSumFinEquiv j ≤ finSumFinEquiv k := by
  constructor
  · rintro rfl
    refine ⟨secondNearestNeighbor_ne_self hN Z i, secondNearestNeighbor_ne_nearestNeighbor hN Z i,
      fun k hk hk' => norm_sub_secondNearestNeighbor_le hN Z hk hk', fun k hk hk' hkeq => ?_⟩
    refine finSumFinEquiv_secondNearestNeighbor_le hN Z hk hk' fun l hl hl' => ?_
    rw [hkeq]
    exact norm_sub_secondNearestNeighbor_le hN Z hl hl'
  · rintro ⟨hji, hjφ, h₂, h₃⟩
    have hs := secondNearestNeighbor_ne_self hN Z i
    have hs' := secondNearestNeighbor_ne_nearestNeighbor hN Z i
    have h_eq : ‖Z i - Z (secondNearestNeighbor hN Z i)‖ = ‖Z i - Z j‖ :=
      le_antisymm (norm_sub_secondNearestNeighbor_le hN Z hji hjφ) (h₂ _ hs hs')
    exact finSumFinEquiv.injective (le_antisymm
      (finSumFinEquiv_secondNearestNeighbor_le hN Z hji hjφ h₂) (h₃ _ hs hs' h_eq))

theorem measurableSet_secondNearestNeighbor_eq (hN : 2 ≤ N) (i j : Fin N ⊕ Fin N) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | secondNearestNeighbor hN Z i = j} := by
  have hset : {Z : Fin N ⊕ Fin N → ℂ | secondNearestNeighbor hN Z i = j} =
      ⋃ a, {Z | nearestNeighbor Z i = a} ∩ {Z | j ≠ i ∧ j ≠ a ∧
        (∀ k, k ≠ i → k ≠ a → ‖Z i - Z j‖ ≤ ‖Z i - Z k‖) ∧
        ∀ k, k ≠ i → k ≠ a → ‖Z i - Z k‖ = ‖Z i - Z j‖ → finSumFinEquiv j ≤ finSumFinEquiv k} := by
    ext Z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [secondNearestNeighbor_eq_iff]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨a, rfl, h⟩
      exact h
  rw [hset]
  refine MeasurableSet.iUnion fun a => (measurableSet_nearestNeighbor_eq i a).inter ?_
  refine Measurable.setOf ?_
  have hn : ∀ k l : Fin N ⊕ Fin N,
      Measurable fun Z : Fin N ⊕ Fin N → ℂ => ‖Z i - Z k‖ ≤ ‖Z i - Z l‖ := by
    intro k l
    exact (measurableSet_le (f := fun Z : Fin N ⊕ Fin N → ℂ => ‖Z i - Z k‖)
      (g := fun Z : Fin N ⊕ Fin N → ℂ => ‖Z i - Z l‖) (by fun_prop) (by fun_prop)).mem
  refine measurable_const.and (measurable_const.and (Measurable.and ?_ ?_))
  · exact Measurable.forall fun k => measurable_const.imp (measurable_const.imp (hn j k))
  · refine Measurable.forall fun k => measurable_const.imp (measurable_const.imp ?_)
    exact Measurable.imp (Measurable.eq (by fun_prop) (by fun_prop)) measurable_const

end Second

/-! ### Measurability of the twice-isolated set -/

section TwiceIsolated

theorem measurableSet_isIsolatedPair_secondNearestNeighbor (hN : 2 ≤ N) (i : Fin N ⊕ Fin N) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | IsIsolatedPair Z (secondNearestNeighbor hN Z i)} := by
  have hset : {Z : Fin N ⊕ Fin N → ℂ | IsIsolatedPair Z (secondNearestNeighbor hN Z i)} =
      ⋃ j, {Z | secondNearestNeighbor hN Z i = j} ∩ {Z | IsIsolatedPair Z j} := by
    ext Z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨j, hj, h⟩ => hj ▸ h⟩
  rw [hset]
  exact MeasurableSet.iUnion fun j =>
    (measurableSet_secondNearestNeighbor_eq hN i j).inter (measurableSet_isIsolatedPair j)

theorem measurableSet_isIsolatedPair_secondNearestNeighbor_nearestNeighbor (hN : 2 ≤ N)
    (i : Fin N ⊕ Fin N) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ |
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))} := by
  have hset : {Z : Fin N ⊕ Fin N → ℂ |
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))} =
      ⋃ a, ⋃ j, {Z | nearestNeighbor Z i = a} ∩ {Z | secondNearestNeighbor hN Z a = j} ∩
        {Z | IsIsolatedPair Z j} := by
    ext Z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩, fun ⟨a, j, ⟨ha, hj⟩, h⟩ => ha ▸ hj ▸ h⟩
  rw [hset]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun j =>
    ((measurableSet_nearestNeighbor_eq i a).inter
      (measurableSet_secondNearestNeighbor_eq hN a j)).inter (measurableSet_isIsolatedPair j)

theorem measurableSet_isTwiceIsolated (hN : 2 ≤ N) (i : Fin N ⊕ Fin N) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | IsTwiceIsolated hN Z i} :=
  (measurableSet_isIsolatedPair i).inter
    ((measurableSet_isIsolatedPair_secondNearestNeighbor hN i).inter
      (measurableSet_isIsolatedPair_secondNearestNeighbor_nearestNeighbor hN i))

/-- The event that the twice-isolated vertices form a given set `T` is measurable. -/
theorem measurableSet_twiceIsolatedSet_eq (hN : 2 ≤ N) (T : Finset (Fin N ⊕ Fin N)) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | twiceIsolatedSet hN Z = T} := by
  have hset : {Z : Fin N ⊕ Fin N → ℂ | twiceIsolatedSet hN Z = T} =
      ⋂ i, {Z | IsTwiceIsolated hN Z i ↔ i ∈ T} := by
    ext Z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.ext_iff, mem_twiceIsolatedSet]
  rw [hset]
  refine MeasurableSet.iInter fun i => ?_
  by_cases hi : i ∈ T
  · simpa only [hi, iff_true] using measurableSet_isTwiceIsolated hN i
  · simp only [hi, iff_false]
    exact (measurableSet_isTwiceIsolated hN i).compl

end TwiceIsolated

/-! ### The cells of the marked graphs -/

section Cells

/-- The cell `{γ_{2N} = (f, T)}` of a marked graph (source l. 1515--1517): the generic
configurations whose nearest-neighbour map is `f` and whose twice-isolated vertices (the marked
vertices, source l. 1219, 1421) form the set `T`. -/
def markedCell (hN : 2 ≤ N) (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (T : Finset (Fin N ⊕ Fin N)) :
    Set (Fin N ⊕ Fin N → ℂ) :=
  {Z | IsGeneric Z ∧ nearestNeighbor Z = f ∧ twiceIsolatedSet hN Z = T}

theorem measurableSet_nearestNeighbor_eq_fun (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | nearestNeighbor Z = f} := by
  have hset : {Z : Fin N ⊕ Fin N → ℂ | nearestNeighbor Z = f} =
      ⋂ i, {Z | nearestNeighbor Z i = f i} := by
    ext Z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
  rw [hset]
  exact MeasurableSet.iInter fun i => measurableSet_nearestNeighbor_eq i (f i)

theorem measurableSet_markedCell (hN : 2 ≤ N) (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N)
    (T : Finset (Fin N ⊕ Fin N)) : MeasurableSet (markedCell hN f T) :=
  measurableSet_isGeneric.inter
    ((measurableSet_nearestNeighbor_eq_fun f).inter (measurableSet_twiceIsolatedSet_eq hN T))

/-- `K = numComponents Z` only depends on the nearest-neighbour map. -/
theorem numComponents_congr {Z Z' : Fin N ⊕ Fin N → ℂ}
    (h : nearestNeighbor Z = nearestNeighbor Z') : numComponents Z = numComponents Z' := by
  unfold numComponents
  rw [h]

/-- `p = numTwiceIsolated hN Z` only depends on the marked graph. -/
theorem numTwiceIsolated_congr (hN : 2 ≤ N) {Z Z' : Fin N ⊕ Fin N → ℂ}
    (h : nearestNeighbor Z = nearestNeighbor Z')
    (hT : twiceIsolatedSet hN Z = twiceIsolatedSet hN Z') :
    numTwiceIsolated hN Z = numTwiceIsolated hN Z' := by
  unfold numTwiceIsolated twiceIsolatedCycles
  rw [h, hT]

/-- The neutral twice-isolated vertices are the twice-isolated vertices with opposite charges at
the two ends of their pair. -/
theorem neutralTwiceIsolatedSet_eq_filter (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) :
    neutralTwiceIsolatedSet hN Z =
      (twiceIsolatedSet hN Z).filter fun i => charge i * charge (nearestNeighbor Z i) = -1 := by
  ext i
  rw [mem_neutralTwiceIsolatedSet_iff, mem_filter]

/-- `p₀ = numNeutralTwiceIsolated hN Z` only depends on the marked graph. -/
theorem numNeutralTwiceIsolated_congr (hN : 2 ≤ N) {Z Z' : Fin N ⊕ Fin N → ℂ}
    (h : nearestNeighbor Z = nearestNeighbor Z')
    (hT : twiceIsolatedSet hN Z = twiceIsolatedSet hN Z') :
    numNeutralTwiceIsolated hN Z = numNeutralTwiceIsolated hN Z' := by
  unfold numNeutralTwiceIsolated neutralTwiceIsolatedCycles
  rw [neutralTwiceIsolatedSet_eq_filter, neutralTwiceIsolatedSet_eq_filter, h, hT]

variable {hN : 2 ≤ N} {K p p₀ : ℕ} {f : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
  {T : Finset (Fin N ⊕ Fin N)} {Z : Fin N ⊕ Fin N → ℂ}

/-- On the cell of a marked graph of `D_{2N,K,p,p₀}`, the number of components is `K`. -/
theorem numComponents_eq_of_mem_markedCell (hγ : (f, T) ∈ markedGraphs hN K p p₀)
    (hZ : Z ∈ markedCell hN f T) : numComponents Z = K := by
  obtain ⟨Z', -, -, hf, -, hK, -, -⟩ := mem_markedGraphs.1 hγ
  rw [numComponents_congr (hZ.2.1.trans hf.symm), hK]

/-- On the cell of a marked graph of `D_{2N,K,p,p₀}`, there are `p` twice-isolated pairs. -/
theorem numTwiceIsolated_eq_of_mem_markedCell (hγ : (f, T) ∈ markedGraphs hN K p p₀)
    (hZ : Z ∈ markedCell hN f T) : numTwiceIsolated hN Z = p := by
  obtain ⟨Z', -, -, hf, hT, -, hp, -⟩ := mem_markedGraphs.1 hγ
  rw [numTwiceIsolated_congr hN (hZ.2.1.trans hf.symm) (hZ.2.2.trans hT.symm), hp]

/-- On the cell of a marked graph of `D_{2N,K,p,p₀}`, there are `p₀` neutral twice-isolated
pairs. -/
theorem numNeutralTwiceIsolated_eq_of_mem_markedCell (hγ : (f, T) ∈ markedGraphs hN K p p₀)
    (hZ : Z ∈ markedCell hN f T) : numNeutralTwiceIsolated hN Z = p₀ := by
  obtain ⟨Z', -, -, hf, hT, -, -, hp₀⟩ := mem_markedGraphs.1 hγ
  rw [numNeutralTwiceIsolated_congr hN (hZ.2.1.trans hf.symm) (hZ.2.2.trans hT.symm), hp₀]

end Cells

/-! ### The decomposition -/

section Decomposition

/-- `p ≤ N`: the twice-isolated vertices are at most the `2N` vertices. -/
theorem numTwiceIsolated_le (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) : numTwiceIsolated hN Z ≤ N := by
  have h1 := card_le_univ (twiceIsolatedSet hN Z)
  have h2 := card_twiceIsolatedSet (hN := hN) (Z := Z)
  simp only [Fintype.card_sum, Fintype.card_fin] at h1
  omega

/-- **Cell decomposition** (source l. 1459, 1515--1517). For every event `A` and every integrand
`F`, the integral over `Λ^{2N} ∩ A` is the sum, over `K, p, p₀ ≤ N` and the marked graphs
`γ ∈ D_{2N,K,p,p₀}`, of the integrals over `Λ^{2N} ∩ A ∩ {γ_{2N} = γ}`. The non-generic
configurations, which lie in no cell, form a null set. -/
theorem lintegral_eq_sum_markedCell (hN : 2 ≤ N) (A : Set (Fin N ⊕ Fin N → ℂ))
    (F : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A, F Z =
      ∑ K ∈ range (N + 1), ∑ p ∈ range (N + 1), ∑ p₀ ∈ range (N + 1),
        ∑ γ ∈ markedGraphs hN K p p₀,
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A ∩ markedCell hN γ.1 γ.2,
            F Z := by
  classical
  set S := (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A with hS
  set idx := (range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1)).sigma
    fun t => markedGraphs hN t.1 t.2.1 t.2.2 with hidx
  set cell : (Σ _ : ℕ × ℕ × ℕ, (Fin N ⊕ Fin N → Fin N ⊕ Fin N) × Finset (Fin N ⊕ Fin N)) →
    Set (Fin N ⊕ Fin N → ℂ) := fun b => markedCell hN b.2.1 b.2.2 with hcell
  have hmeas : ∀ b ∈ idx, MeasurableSet (cell b) :=
    fun b _ => measurableSet_markedCell hN _ _
  have hcov : S ∩ {Z | IsGeneric Z} = (⋃ b ∈ idx, cell b) ∩ S := by
    ext Z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hZS, hgen⟩
      refine ⟨⟨⟨(numComponents Z, numTwiceIsolated hN Z, numNeutralTwiceIsolated hN Z),
        (nearestNeighbor Z, twiceIsolatedSet hN Z)⟩, ?_, hgen, rfl, rfl⟩, hZS⟩
      refine mem_sigma.2 ⟨?_, ?_⟩
      · refine mem_product.2 ⟨mem_range.2 (Nat.lt_succ_of_le (numComponents_le Z)),
          mem_product.2 ⟨mem_range.2 (Nat.lt_succ_of_le (numTwiceIsolated_le hN Z)),
            mem_range.2 (Nat.lt_succ_of_le ((numNeutralTwiceIsolated_le_numTwiceIsolated).trans
              (numTwiceIsolated_le hN Z)))⟩⟩
      · have hbox : ∀ i, Z i ∈ box N := fun i => hZS.1 i (Set.mem_univ i)
        exact mem_markedGraphs.2 ⟨Z, hbox, hgen, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨⟨b, -, hZb⟩, hZS⟩
      exact ⟨hZS, hZb.1⟩
  have hdisj : Set.PairwiseDisjoint (↑idx) cell := by
    intro b hb b' hb' hne
    refine Set.disjoint_left.2 fun Z hZ hZ' => hne ?_
    have hb2 : b.2 = b'.2 := Prod.ext (hZ.2.1.symm.trans hZ'.2.1) (hZ.2.2.symm.trans hZ'.2.2)
    have hγ := (mem_sigma.1 (Finset.mem_coe.1 hb)).2
    have hγ' := (mem_sigma.1 (Finset.mem_coe.1 hb')).2
    have hb1 : b.1 = b'.1 := by
      have e1 := numComponents_eq_of_mem_markedCell hγ hZ
      have e2 := numTwiceIsolated_eq_of_mem_markedCell hγ hZ
      have e3 := numNeutralTwiceIsolated_eq_of_mem_markedCell hγ hZ
      have e1' := numComponents_eq_of_mem_markedCell hγ' hZ'
      have e2' := numTwiceIsolated_eq_of_mem_markedCell hγ' hZ'
      have e3' := numNeutralTwiceIsolated_eq_of_mem_markedCell hγ' hZ'
      exact Prod.ext (e1.symm.trans e1') (Prod.ext (e2.symm.trans e2') (e3.symm.trans e3'))
    exact Sigma.ext hb1 (heq_of_eq hb2)
  rw [lintegral_restrict_inter_isGeneric, hcov,
    ← Measure.restrict_restrict (Finset.measurableSet_biUnion idx hmeas),
    lintegral_biUnion_finset hdisj hmeas, Finset.sum_sigma, Finset.sum_product]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p₀ _ =>
    Finset.sum_congr rfl fun γ _ => ?_
  rw [Measure.restrict_restrict (measurableSet_markedCell hN _ _), Set.inter_comm]

end Decomposition

end TwoComponentCoulomb

end
