/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.IsGeneric
public import TwoComponentCoulomb.Frozen.IsIsolatedPair
public import TwoComponentCoulomb.Frozen.NumComponents
public import TwoComponentCoulomb.Frozen.SecondNearestNeighbor
public import TwoComponentCoulomb.NearestNeighbor.Isolated
public import TwoComponentCoulomb.NearestNeighbor.Second

/-!
# Counting the exceptional indices in Corollary 2.3

Source l. 472–476 (proof of Corollary 2.3). Write `I^pair` for the set of indices in an isolated
pair (`IsIsolatedPair`), `K` for the number of components (`numComponents`) and `φ₂` for the second
nearest neighbour. There are at most `6 (N - K)` indices outside `I^pair`
(`card_not_isIsolatedPair_le`); a point is the second nearest neighbour of at most twelve points
(Lemma 2.1); and an isolated pair is exchanged by `φ₁`, so passing to partners at most doubles a
count. Consequently, for a generic configuration (in fact for any configuration of distinct
points), the number of indices `i` such that `i ∉ I^pair`, or `φ₂ i ∉ I^pair`, or
`φ₂ (φ₁ i) ∉ I^pair`, is at most `150 (N - K)`.

* `card_filter_secondNearestNeighbor_mem_le`: `#{j | φ₂ j ∈ S} ≤ 12 #S`.
* `card_not_isolated_and_second_le`: the same bound with the extra exceptional indices
  `i ∉ I^pair`.
-/

public section

namespace TwoComponentCoulomb

open Finset

variable {N : ℕ}

open scoped Classical in
/-- Each index is the second nearest neighbour of at most twelve points, hence at most `12 #S`
points have their second nearest neighbour in `S`. -/
theorem card_filter_secondNearestNeighbor_mem_le (hN : 2 ≤ N) {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : Function.Injective Z) (S : Finset (Fin N ⊕ Fin N)) :
    (univ.filter fun j => secondNearestNeighbor hN Z j ∈ S).card ≤ 12 * S.card := by
  have hsub : (univ.filter fun j => secondNearestNeighbor hN Z j ∈ S) ⊆
      S.biUnion fun o => univ.filter fun j => secondNearestNeighbor hN Z j = o := by
    intro j hj
    exact Finset.mem_biUnion.2 ⟨_, (Finset.mem_filter.1 hj).2,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ o ∈ S, (univ.filter fun j => secondNearestNeighbor hN Z j = o).card
      ≤ ∑ _o ∈ S, 12 :=
        Finset.sum_le_sum fun o _ =>
          card_filter_secondNearestNeighbor_eq_le_twelve_of_injective hN hZ o
    _ = 12 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

open scoped Classical in
/-- At most `72 (N - K)` indices have their second nearest neighbour outside `I^pair`. -/
theorem card_filter_not_isIsolatedPair_secondNearestNeighbor_le (hN : 2 ≤ N)
    {Z : Fin N ⊕ Fin N → ℂ} (hZ : Function.Injective Z) :
    (univ.filter fun i => ¬ IsIsolatedPair Z (secondNearestNeighbor hN Z i)).card ≤
      72 * (N - numComponents Z) := by
  have h1 := card_filter_secondNearestNeighbor_mem_le hN hZ
    (univ.filter fun i => ¬ IsIsolatedPair Z i)
  have h2 := card_not_isIsolatedPair_le Z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
  omega

open scoped Classical in
/-- At most `72 (N - K)` indices `i ∈ I^pair` have `φ₂ (φ₁ i) ∉ I^pair`. The partner map
`i ↦ φ₁ i` is injective on `I^pair` since `φ₁ (φ₁ i) = i` there. -/
theorem card_filter_isIsolatedPair_not_secondNearestNeighbor_nearestNeighbor_le (hN : 2 ≤ N)
    {Z : Fin N ⊕ Fin N → ℂ} (hZ : Function.Injective Z) :
    (univ.filter fun i => IsIsolatedPair Z i ∧
      ¬ IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))).card ≤
        72 * (N - numComponents Z) := by
  refine le_trans (Finset.card_le_card_of_injOn (nearestNeighbor Z) ?_ ?_)
    (card_filter_not_isIsolatedPair_secondNearestNeighbor_le hN hZ)
  · intro i hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2.2⟩
  · intro i hi j hj hij
    have hi' := (Finset.mem_filter.1 hi).2.1.nearestNeighbor_nearestNeighbor
    have hj' := (Finset.mem_filter.1 hj).2.1.nearestNeighbor_nearestNeighbor
    have hij' : nearestNeighbor Z i = nearestNeighbor Z j := hij
    rw [← hi', hij', hj']

open scoped Classical in
/-- Counting the exceptional indices of the proof of Corollary 2.3 (source l. 476): at most
`150 (N - K)` indices fail to satisfy `i ∈ I^pair`, `φ₂ i ∈ I^pair`, `φ₂ (φ₁ i) ∈ I^pair`. -/
theorem card_not_isolated_and_second_le (hN : 2 ≤ N) {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : IsGeneric Z) :
    (univ.filter fun i => ¬ (IsIsolatedPair Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)))).card ≤
        150 * (N - numComponents Z) := by
  have h1 := card_not_isIsolatedPair_le Z
  have h2 := card_filter_not_isIsolatedPair_secondNearestNeighbor_le hN hZ.1
  have h3 := card_filter_isIsolatedPair_not_secondNearestNeighbor_nearestNeighbor_le hN hZ.1
  have hsub : (univ.filter fun i => ¬ (IsIsolatedPair Z i ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)))) ⊆
      ((univ.filter fun i => ¬ IsIsolatedPair Z i) ∪
        (univ.filter fun i => ¬ IsIsolatedPair Z (secondNearestNeighbor hN Z i))) ∪
        (univ.filter fun i => IsIsolatedPair Z i ∧
          ¬ IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    by_cases hp : IsIsolatedPair Z i
    · by_cases hq : IsIsolatedPair Z (secondNearestNeighbor hN Z i)
      · exact Or.inr ⟨hp, fun hr => hi ⟨hp, hq, hr⟩⟩
      · exact Or.inl (Or.inr hq)
    · exact Or.inl (Or.inl hp)
  have := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  omega

end TwoComponentCoulomb

end
