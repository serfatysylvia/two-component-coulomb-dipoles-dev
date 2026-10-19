/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.Frozen.IsGeneric
public import TwoComponentCoulomb.Frozen.IsIsolatedDipole
public import TwoComponentCoulomb.Frozen.IsIsolatedPair
public import TwoComponentCoulomb.Frozen.M0
public import TwoComponentCoulomb.Frozen.SecondNearestNeighbor
public import TwoComponentCoulomb.NearestNeighbor.Cone
public import TwoComponentCoulomb.NearestNeighbor.Isolated
public import TwoComponentCoulomb.NearestNeighbor.Second

/-!
# Twice-isolated pairs and the geometric constraint of Proposition 3.10, Step 1

Source: l. 1219 (definition of twice-isolated cycles), l. 1495--1506
(eqs. (eq:r1), (eq:r2), (eq:K-p)), together with Remark 2.1 (l. 388--397).

An isolated 2-cycle `{i, φ₁ i}` is *twice isolated* if `φ₂ i` and `φ₂ (φ₁ i)` each lie in some
isolated 2-cycle, i.e. in `I^pair`.

## Main definitions

* `TwoComponentCoulomb.IsTwiceIsolated hN Z i`: `i ∈ I^pair`, `φ₂ i ∈ I^pair`, `φ₂ (φ₁ i) ∈ I^pair`.
* `TwoComponentCoulomb.twiceIsolatedSet hN Z`: the set of vertices of twice-isolated cycles.
* `TwoComponentCoulomb.numIsolatedPairs Z` (`m`), `TwoComponentCoulomb.numTwiceIsolated hN Z` (`p`),
  `TwoComponentCoulomb.numNeutralTwiceIsolated hN Z` (`p₀`): the numbers of isolated, twice-isolated
  and neutral twice-isolated 2-cycles.

## Main results

* `TwoComponentCoulomb.card_twiceIsolatedSet`: the twice-isolated vertices are twice as many as the
  twice-isolated cycles.
* `TwoComponentCoulomb.card_filter_secondNearestNeighbor_eq_le_six`: among vertices no two of which
  form a nearest-neighbour pair, at most six have a given point as second nearest neighbour
  (Remark 2.1, second paragraph).
* `TwoComponentCoulomb.numIsolatedPairs_le_add_six_mul_compl` and
  `TwoComponentCoulomb.numIsolatedPairs_le_add_twelve_mul` (eq. (eq:r1)),
  `TwoComponentCoulomb.numComponents_le_numIsolatedPairs_add` (eq. (eq:r2)),
  `TwoComponentCoulomb.numIsolatedPairs_le_numTwiceIsolated_add` and
  `TwoComponentCoulomb.numComponents_le_numTwiceIsolated_add` (eq. (eq:K-p)):
  `m - p ≤ 36 (N - K)` and `K - p ≤ 38 (N - K)`. These need only the injectivity of `Z`.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

variable {N : ℕ}

/-! ### Definitions -/

/-- `i` lies in a *twice-isolated* 2-cycle (source l. 1219): `{i, φ₁ i}` is an isolated pair and
`φ₂ i`, `φ₂ (φ₁ i)` each lie in some isolated 2-cycle, that is, in `I^pair`. -/
def IsTwiceIsolated (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) : Prop :=
  IsIsolatedPair Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
    IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))

open scoped Classical in
/-- The vertices `I^pair` of the isolated 2-cycles. -/
noncomputable def isolatedPairSet (Z : Fin N ⊕ Fin N → ℂ) : Finset (Fin N ⊕ Fin N) :=
  univ.filter (IsIsolatedPair Z)

open scoped Classical in
/-- The vertices of the twice-isolated 2-cycles. -/
noncomputable def twiceIsolatedSet (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) :
    Finset (Fin N ⊕ Fin N) :=
  univ.filter (IsTwiceIsolated hN Z)

open scoped Classical in
/-- The vertices of the neutral twice-isolated 2-cycles: the twice-isolated vertices whose pair is
an isolated dipole (opposite charges). -/
noncomputable def neutralTwiceIsolatedSet (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) :
    Finset (Fin N ⊕ Fin N) :=
  univ.filter fun i => IsTwiceIsolated hN Z i ∧ IsIsolatedDipole Z i

open scoped Classical in
/-- The isolated 2-cycles `{i, φ₁ i}` of the nearest-neighbour graph. -/
noncomputable def isolatedPairs (Z : Fin N ⊕ Fin N → ℂ) : Finset (Finset (Fin N ⊕ Fin N)) :=
  (isolatedPairSet Z).image fun i => {i, nearestNeighbor Z i}

open scoped Classical in
/-- The twice-isolated 2-cycles `{i, φ₁ i}`. -/
noncomputable def twiceIsolatedCycles (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) :
    Finset (Finset (Fin N ⊕ Fin N)) :=
  (twiceIsolatedSet hN Z).image fun i => {i, nearestNeighbor Z i}

open scoped Classical in
/-- The neutral twice-isolated 2-cycles `{i, φ₁ i}`. -/
noncomputable def neutralTwiceIsolatedCycles (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) :
    Finset (Finset (Fin N ⊕ Fin N)) :=
  (neutralTwiceIsolatedSet hN Z).image fun i => {i, nearestNeighbor Z i}

/-- `m`: the number of isolated 2-cycles. -/
noncomputable def numIsolatedPairs (Z : Fin N ⊕ Fin N → ℂ) : ℕ := (isolatedPairs Z).card

/-- `p`: the number of twice-isolated 2-cycles. -/
noncomputable def numTwiceIsolated (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) : ℕ :=
  (twiceIsolatedCycles hN Z).card

/-- `p₀`: the number of neutral twice-isolated 2-cycles. -/
noncomputable def numNeutralTwiceIsolated (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) : ℕ :=
  (neutralTwiceIsolatedCycles hN Z).card

/-! ### Basic facts -/

section Basic

variable (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ)

theorem mem_isolatedPairSet {i : Fin N ⊕ Fin N} : i ∈ isolatedPairSet Z ↔ IsIsolatedPair Z i := by
  simp [isolatedPairSet]

theorem mem_twiceIsolatedSet {i : Fin N ⊕ Fin N} :
    i ∈ twiceIsolatedSet hN Z ↔ IsTwiceIsolated hN Z i := by
  simp [twiceIsolatedSet]

theorem mem_neutralTwiceIsolatedSet {i : Fin N ⊕ Fin N} :
    i ∈ neutralTwiceIsolatedSet hN Z ↔ IsTwiceIsolated hN Z i ∧ IsIsolatedDipole Z i := by
  simp [neutralTwiceIsolatedSet]

variable {hN Z}

/-- If `i` lies in a twice-isolated 2-cycle, so does `φ₁ i`. -/
theorem IsTwiceIsolated.nearestNeighbor {i : Fin N ⊕ Fin N} (h : IsTwiceIsolated hN Z i) :
    IsTwiceIsolated hN Z (nearestNeighbor Z i) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨isIsolatedPair_nearestNeighbor h1, h3, ?_⟩
  rw [h1.nearestNeighbor_nearestNeighbor]
  exact h2

theorem isolatedPairSet_subset_cycleVerts : isolatedPairSet Z ⊆ cycleVerts Z := fun _ hi =>
  mem_cycleVerts_of_isIsolatedPair ((mem_isolatedPairSet Z).1 hi)

variable (hN Z)

theorem twiceIsolatedSet_subset_isolatedPairSet : twiceIsolatedSet hN Z ⊆ isolatedPairSet Z :=
  fun _ hi => (mem_isolatedPairSet Z).2 ((mem_twiceIsolatedSet hN Z).1 hi).1

theorem neutralTwiceIsolatedSet_subset_twiceIsolatedSet :
    neutralTwiceIsolatedSet hN Z ⊆ twiceIsolatedSet hN Z :=
  fun _ hi => (mem_twiceIsolatedSet hN Z).2 ((mem_neutralTwiceIsolatedSet hN Z).1 hi).1

variable {hN Z}

theorem nearestNeighbor_mem_twiceIsolatedSet {i : Fin N ⊕ Fin N}
    (hi : i ∈ twiceIsolatedSet hN Z) : nearestNeighbor Z i ∈ twiceIsolatedSet hN Z :=
  (mem_twiceIsolatedSet hN Z).2 ((mem_twiceIsolatedSet hN Z).1 hi).nearestNeighbor

theorem nearestNeighbor_nearestNeighbor_of_mem_twiceIsolatedSet {i : Fin N ⊕ Fin N}
    (hi : i ∈ twiceIsolatedSet hN Z) : nearestNeighbor Z (nearestNeighbor Z i) = i :=
  ((mem_twiceIsolatedSet hN Z).1 hi).1.nearestNeighbor_nearestNeighbor

/-- The vertices of the isolated pairs are twice as many as the isolated pairs. -/
theorem card_isolatedPairSet : (isolatedPairSet Z).card = 2 * numIsolatedPairs Z := by
  classical
  unfold numIsolatedPairs isolatedPairs isolatedPairSet
  exact card_filter_isIsolatedPair Z

/-- The vertices of the twice-isolated pairs are twice as many as the twice-isolated pairs. -/
theorem card_twiceIsolatedSet : (twiceIsolatedSet hN Z).card = 2 * numTwiceIsolated hN Z := by
  classical
  unfold numTwiceIsolated twiceIsolatedCycles twiceIsolatedSet
  convert card_filter_eq_two_mul_card_image_pair Z (IsTwiceIsolated hN Z) fun i hi =>
    ⟨hi.1.nearestNeighbor_nearestNeighbor, hi.nearestNeighbor⟩ using 3

/-- The vertices of the neutral twice-isolated pairs are twice as many as these pairs. -/
theorem card_neutralTwiceIsolatedSet :
    (neutralTwiceIsolatedSet hN Z).card = 2 * numNeutralTwiceIsolated hN Z := by
  classical
  unfold numNeutralTwiceIsolated neutralTwiceIsolatedCycles neutralTwiceIsolatedSet
  convert card_filter_eq_two_mul_card_image_pair Z (fun i => IsTwiceIsolated hN Z i ∧
    IsIsolatedDipole Z i) fun i hi =>
    ⟨hi.1.1.nearestNeighbor_nearestNeighbor, hi.1.nearestNeighbor,
      isIsolatedDipole_nearestNeighbor hi.2⟩ using 3

theorem numTwiceIsolated_le_numIsolatedPairs : numTwiceIsolated hN Z ≤ numIsolatedPairs Z := by
  have h1 := card_le_card (twiceIsolatedSet_subset_isolatedPairSet hN Z)
  have h2 := card_isolatedPairSet (Z := Z)
  have h3 := card_twiceIsolatedSet (hN := hN) (Z := Z)
  omega

theorem numNeutralTwiceIsolated_le_numTwiceIsolated :
    numNeutralTwiceIsolated hN Z ≤ numTwiceIsolated hN Z := by
  have h1 := card_le_card (neutralTwiceIsolatedSet_subset_twiceIsolatedSet hN Z)
  have h2 := card_neutralTwiceIsolatedSet (hN := hN) (Z := Z)
  have h3 := card_twiceIsolatedSet (hN := hN) (Z := Z)
  omega

/-- The vertices of the neutral twice-isolated pairs are the twice-isolated vertices with
opposite charges on the two ends of their pair. -/
theorem mem_neutralTwiceIsolatedSet_iff {i : Fin N ⊕ Fin N} :
    i ∈ neutralTwiceIsolatedSet hN Z ↔
      i ∈ twiceIsolatedSet hN Z ∧ charge i * charge (nearestNeighbor Z i) = -1 := by
  rw [mem_neutralTwiceIsolatedSet, mem_twiceIsolatedSet, isIsolatedDipole_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, h1.1, h3⟩

end Basic

/-! ### The six-bound (Remark 2.1, second paragraph) -/

/-- Source l. 388--397 (Remark 2.1, second paragraph). If `S` is a set of vertices no two of
which form a nearest-neighbour pair (`φ₁ i ∉ S` for `i ∈ S`; for instance, `S` contains at most
one vertex of each isolated pair), then at most six vertices of `S` have a given point `o` as
second nearest neighbour. Two such vertices in one `π/3`-cone around `z_o`, the closer one `A` and
the farther one `B`, satisfy `|AB| < |oB|`, and `A ≠ φ₁ B`; this contradicts `φ₂ B = o`. Only the
injectivity of `Z` is used. -/
theorem card_filter_secondNearestNeighbor_eq_le_six (hN : 2 ≤ N) {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : Function.Injective Z) (S : Finset (Fin N ⊕ Fin N))
    (hS : ∀ i ∈ S, nearestNeighbor Z i ∉ S) (o : Fin N ⊕ Fin N) :
    (S.filter fun i => secondNearestNeighbor hN Z i = o).card ≤ 6 := by
  classical
  obtain ⟨s, hs⟩ := exists_sector
  have key : ∀ j ∈ S.filter (fun i => secondNearestNeighbor hN Z i = o),
      ∀ k ∈ S.filter (fun i => secondNearestNeighbor hN Z i = o),
      j ≠ k → s (Z j - Z o) = s (Z k - Z o) → ‖Z j - Z o‖ ≤ ‖Z k - Z o‖ → False := by
    intro j hj k hk hjk hsjk hle
    obtain ⟨hjS, hjo⟩ := mem_filter.1 hj
    obtain ⟨hkS, hko⟩ := mem_filter.1 hk
    have hjo' : j ≠ o := fun h => secondNearestNeighbor_ne_self hN Z j (hjo.trans h.symm)
    have hko' : k ≠ o := fun h => secondNearestNeighbor_ne_self hN Z k (hko.trans h.symm)
    have hlt := norm_sub_lt_of_mul_conj_re (o := Z o) (a := Z j) (b := Z k) hle
      (hs _ _ (sub_ne_zero.2 (hZ.ne hjo')) (sub_ne_zero.2 (hZ.ne hko')) hsjk)
    have hjφ : j ≠ nearestNeighbor Z k := fun h => hS k hkS (h ▸ hjS)
    have h2 := norm_sub_secondNearestNeighbor_le hN Z (i := k) (k := j) hjk hjφ
    rw [hko, norm_sub_rev (Z k) (Z j)] at h2
    exact absurd h2 (not_le.2 hlt)
  refine (Finset.card_le_card_of_injOn (fun j => s (Z j - Z o)) (fun _ _ => mem_univ _) ?_).trans
    (by simp)
  intro j hj k hk hsjk
  by_contra hne
  rcases le_total ‖Z j - Z o‖ ‖Z k - Z o‖ with h | h
  · exact key j hj k hk hne hsjk h
  · exact key k hk j hj (Ne.symm hne) hsjk.symm h

/-! ### The geometric constraint `K - p ≤ (M₀ + 2) (N - K)` -/

section Constraint

variable {Z : Fin N ⊕ Fin N → ℂ}

theorem numIsolatedPairs_le_numComponents (Z : Fin N ⊕ Fin N → ℂ) :
    numIsolatedPairs Z ≤ numComponents Z := by
  have h1 := card_le_card (isolatedPairSet_subset_cycleVerts (Z := Z))
  have h2 := card_cycleVerts_eq_two_mul_numComponents Z
  have h3 := card_isolatedPairSet (Z := Z)
  omega

theorem numIsolatedPairs_le (Z : Fin N ⊕ Fin N → ℂ) : numIsolatedPairs Z ≤ N :=
  (numIsolatedPairs_le_numComponents Z).trans (numComponents_le Z)

/-- The number of vertices outside `I^pair` is `2 (N - m)`. -/
theorem card_compl_isolatedPairSet (Z : Fin N ⊕ Fin N → ℂ) :
    ((isolatedPairSet Z)ᶜ).card = 2 * (N - numIsolatedPairs Z) := by
  have h1 := card_compl_add_card (isolatedPairSet Z)
  have h2 := card_isolatedPairSet (Z := Z)
  have h3 := numIsolatedPairs_le Z
  have h4 : Fintype.card (Fin N ⊕ Fin N) = 2 * N := by simp [two_mul]
  omega

/-- Equation (eq:r2) (source l. 1499--1502): `K - m ≤ 2 (N - K)`. Each of the nonisolated
components contains a tree vertex adjacent to its 2-cycle, and there are `2 (N - K)` tree
vertices. -/
theorem numComponents_le_numIsolatedPairs_add (Z : Fin N ⊕ Fin N → ℂ) :
    numComponents Z ≤ numIsolatedPairs Z + 2 * (N - numComponents Z) := by
  classical
  set Tr : Finset (Fin N ⊕ Fin N) :=
    univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) ≠ i with hTr
  have hsub : cycleVerts Z \ isolatedPairSet Z ⊆
      Tr.image (nearestNeighbor Z) ∪
        Tr.image (fun k => nearestNeighbor Z (nearestNeighbor Z k)) := by
    intro c hc
    rw [mem_sdiff, mem_cycleVerts, mem_isolatedPairSet] at hc
    obtain ⟨h2, hc'⟩ := hc
    obtain ⟨k, hk1, hk2⟩ : ∃ k, (nearestNeighbor Z k = c ∨ nearestNeighbor Z k =
        nearestNeighbor Z c) ∧ ¬ (k = c ∨ k = nearestNeighbor Z c) := by
      by_contra hcon
      exact hc' ⟨h2, fun k hk => by
        by_contra hnk
        exact hcon ⟨k, hk, hnk⟩⟩
    have hkT : k ∈ Tr := by
      rw [hTr, mem_filter]
      refine ⟨mem_univ _, fun hkk => ?_⟩
      rcases hk1 with h | h
      · rw [h] at hkk
        exact hk2 (Or.inr hkk.symm)
      · rw [h, h2] at hkk
        exact hk2 (Or.inl hkk.symm)
    rcases hk1 with h | h
    · exact mem_union_left _ (mem_image.2 ⟨k, hkT, h⟩)
    · exact mem_union_right _ (mem_image.2 ⟨k, hkT, by rw [h, h2]⟩)
  have h1 := card_le_card hsub
  have h2 := card_union_le (Tr.image (nearestNeighbor Z))
    (Tr.image (fun k => nearestNeighbor Z (nearestNeighbor Z k)))
  have h3 : (Tr.image (nearestNeighbor Z)).card ≤ Tr.card := card_image_le
  have h4 : (Tr.image (fun k => nearestNeighbor Z (nearestNeighbor Z k))).card ≤ Tr.card :=
    card_image_le
  have h5 : Tr.card = 2 * (N - numComponents Z) := card_tree_vertices Z
  have h6 := card_sdiff_of_subset (isolatedPairSet_subset_cycleVerts (Z := Z))
  have h7 := card_cycleVerts_eq_two_mul_numComponents Z
  have h8 := card_isolatedPairSet (Z := Z)
  have h9 := numComponents_le Z
  omega

/-- Equation (eq:r1), first half (source l. 1495--1498): `m - p ≤ 6 |(I^pair)^c|`. For each
isolated pair that is not twice isolated, one vertex whose second nearest neighbour lies outside
`I^pair` is selected (the one with the smaller index if both qualify); by the six-bound, at most
six selected vertices have a given exterior point as second nearest neighbour. -/
theorem numIsolatedPairs_le_add_six_mul_compl (hN : 2 ≤ N) {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : Function.Injective Z) :
    numIsolatedPairs Z ≤ numTwiceIsolated hN Z + 6 * ((isolatedPairSet Z)ᶜ).card := by
  classical
  set I := isolatedPairSet Z with hI
  set B : Finset (Fin N ⊕ Fin N) :=
    I.filter fun i => secondNearestNeighbor hN Z i ∉ I with hB
  set S : Finset (Fin N ⊕ Fin N) :=
    B.filter fun i => nearestNeighbor Z i ∈ B →
      finSumFinEquiv i < finSumFinEquiv (nearestNeighbor Z i) with hSdef
  have hIφ : ∀ i ∈ I, nearestNeighbor Z (nearestNeighbor Z i) = i := fun i hi =>
    ((mem_isolatedPairSet Z).1 hi).nearestNeighbor_nearestNeighbor
  have hIcl : ∀ i ∈ I, nearestNeighbor Z i ∈ I := fun i hi =>
    (mem_isolatedPairSet Z).2 (isIsolatedPair_nearestNeighbor ((mem_isolatedPairSet Z).1 hi))
  have hSfree : ∀ i ∈ S, nearestNeighbor Z i ∉ S := by
    intro i hi hφi
    obtain ⟨hiB, hi'⟩ := mem_filter.1 hi
    obtain ⟨hφB, hφ'⟩ := mem_filter.1 hφi
    have hiI : i ∈ I := (mem_filter.1 hiB).1
    have h1 := hi' hφB
    have h2 := hφ' (by rw [hIφ i hiI]; exact hiB)
    rw [hIφ i hiI] at h2
    exact lt_asymm h1 h2
  have hSsub : ∀ i ∈ S, secondNearestNeighbor hN Z i ∈ Iᶜ := by
    intro i hi
    exact mem_compl.2 (mem_filter.1 (mem_filter.1 hi).1).2
  have hS6 : S.card ≤ 6 * (Iᶜ).card :=
    card_le_mul_card_image_of_maps_to (f := secondNearestNeighbor hN Z) hSsub 6 fun o _ =>
      card_filter_secondNearestNeighbor_eq_le_six hN hZ S hSfree o
  set W := I \ twiceIsolatedSet hN Z with hW
  have hWcard : W.card = 2 * numIsolatedPairs Z - 2 * numTwiceIsolated hN Z := by
    rw [hW, card_sdiff_of_subset (twiceIsolatedSet_subset_isolatedPairSet hN Z),
      card_isolatedPairSet, card_twiceIsolatedSet]
  have hψ : ∀ i ∈ W, (if i ∈ S then i else nearestNeighbor Z i) ∈ S := by
    intro i hiW
    obtain ⟨hiI, hiT⟩ := mem_sdiff.1 hiW
    have hbad : i ∈ B ∨ nearestNeighbor Z i ∈ B := by
      rw [mem_twiceIsolatedSet] at hiT
      have hiI' := (mem_isolatedPairSet Z).1 hiI
      by_contra hcon
      push Not at hcon
      apply hiT
      refine ⟨hiI', ?_, ?_⟩
      · by_contra hnot
        exact hcon.1 (mem_filter.2 ⟨hiI, fun h => hnot ((mem_isolatedPairSet Z).1 h)⟩)
      · by_contra hnot
        exact hcon.2 (mem_filter.2 ⟨hIcl i hiI, fun h => hnot ((mem_isolatedPairSet Z).1 h)⟩)
    by_cases hiS : i ∈ S
    · simp [hiS]
    · simp only [hiS, ↓reduceIte]
      rcases em (i ∈ B) with hiB | hiB
      · have hφB : nearestNeighbor Z i ∈ B ∧
            ¬ finSumFinEquiv i < finSumFinEquiv (nearestNeighbor Z i) := by
          by_contra hcon
          exact hiS (mem_filter.2 ⟨hiB, fun h => by_contra fun hn => hcon ⟨h, hn⟩⟩)
        refine mem_filter.2 ⟨hφB.1, fun _ => ?_⟩
        rw [hIφ i hiI]
        have hne : finSumFinEquiv i ≠ finSumFinEquiv (nearestNeighbor Z i) :=
          fun h => nearestNeighbor_ne Z i (finSumFinEquiv.injective h).symm
        exact lt_of_le_of_ne (not_lt.1 hφB.2) hne.symm
      · have hφB : nearestNeighbor Z i ∈ B := hbad.resolve_left hiB
        refine mem_filter.2 ⟨hφB, fun h => ?_⟩
        rw [hIφ i hiI] at h
        exact absurd h hiB
  have hfib : ∀ s ∈ S,
      (W.filter fun i => (if i ∈ S then i else nearestNeighbor Z i) = s).card ≤ 2 := by
    intro s _
    refine (card_le_card (t := {s, nearestNeighbor Z s}) fun i hi => ?_).trans card_le_two
    obtain ⟨hiW, hψi⟩ := mem_filter.1 hi
    have hiI := (mem_sdiff.1 hiW).1
    by_cases hiS : i ∈ S
    · simp only [hiS, ↓reduceIte] at hψi
      exact mem_insert.2 (Or.inl hψi)
    · simp only [hiS, ↓reduceIte] at hψi
      exact mem_insert.2 (Or.inr (mem_singleton.2 (by rw [← hψi, hIφ i hiI])))
  have hW2 := card_le_mul_card_image_of_maps_to hψ 2 hfib
  omega

/-- Source l. 1503: `|(I^pair)^c| = 2 (N - K) + 2 (K - m) ≤ 6 (N - K)`. -/
theorem card_compl_isolatedPairSet_le (Z : Fin N ⊕ Fin N → ℂ) :
    ((isolatedPairSet Z)ᶜ).card ≤ 6 * (N - numComponents Z) := by
  have h1 := card_compl_isolatedPairSet Z
  have h2 := numComponents_le_numIsolatedPairs_add Z
  have h3 := numComponents_le Z
  omega

/-- Equation (eq:r1) (source l. 1496--1498): `m - p ≤ 6 |(I^pair)^c| = 12 (N - m)`. -/
theorem numIsolatedPairs_le_add_twelve_mul (hN : 2 ≤ N) {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : Function.Injective Z) :
    numIsolatedPairs Z ≤ numTwiceIsolated hN Z + 12 * (N - numIsolatedPairs Z) := by
  have h1 := numIsolatedPairs_le_add_six_mul_compl hN hZ
  have h2 := card_compl_isolatedPairSet Z
  omega

/-- Source l. 1503: `m - p ≤ M₀ (N - K)` with `M₀ = 36`, in natural numbers. -/
theorem numIsolatedPairs_le_numTwiceIsolated_add (hN : 2 ≤ N) {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : Function.Injective Z) :
    numIsolatedPairs Z ≤ numTwiceIsolated hN Z + 36 * (N - numComponents Z) := by
  have h1 := numIsolatedPairs_le_add_six_mul_compl hN hZ
  have h2 := card_compl_isolatedPairSet_le Z
  omega

/-- Equation (eq:K-p) (source l. 1504--1506): `K - p ≤ (M₀ + 2) (N - K)` with `M₀ = 36`, in natural
numbers. -/
theorem numComponents_le_numTwiceIsolated_add (hN : 2 ≤ N) {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : Function.Injective Z) :
    numComponents Z ≤ numTwiceIsolated hN Z + 38 * (N - numComponents Z) := by
  have h1 := numIsolatedPairs_le_numTwiceIsolated_add hN hZ
  have h2 := numComponents_le_numIsolatedPairs_add Z
  omega

/-- Source l. 1503 in real numbers: `m - p ≤ M₀ (N - K)`. -/
theorem numIsolatedPairs_sub_le_M0_mul (hN : 2 ≤ N) {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : Function.Injective Z) :
    (numIsolatedPairs Z : ℝ) - numTwiceIsolated hN Z ≤ M0 * ((N : ℝ) - numComponents Z) := by
  have h := numIsolatedPairs_le_numTwiceIsolated_add hN hZ
  have hc : ((N - numComponents Z : ℕ) : ℝ) = (N : ℝ) - numComponents Z :=
    Nat.cast_sub (numComponents_le Z)
  have h' : (numIsolatedPairs Z : ℝ) ≤
      numTwiceIsolated hN Z + 36 * ((N - numComponents Z : ℕ) : ℝ) := by exact_mod_cast h
  rw [hc] at h'
  simp only [M0]
  linarith

/-- Equation (eq:K-p) in real numbers: `K - p ≤ (M₀ + 2) (N - K)`. -/
theorem numComponents_sub_le_M0_add_two_mul (hN : 2 ≤ N) {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : Function.Injective Z) :
    (numComponents Z : ℝ) - numTwiceIsolated hN Z ≤ (M0 + 2) * ((N : ℝ) - numComponents Z) := by
  have h := numComponents_le_numTwiceIsolated_add hN hZ
  have hc : ((N - numComponents Z : ℕ) : ℝ) = (N : ℝ) - numComponents Z :=
    Nat.cast_sub (numComponents_le Z)
  have h' : (numComponents Z : ℝ) ≤
      numTwiceIsolated hN Z + 38 * ((N - numComponents Z : ℕ) : ℝ) := by exact_mod_cast h
  rw [hc] at h'
  simp only [M0]
  linarith

end Constraint

end TwoComponentCoulomb

end
