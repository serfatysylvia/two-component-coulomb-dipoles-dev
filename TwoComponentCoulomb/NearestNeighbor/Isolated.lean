/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import TwoComponentCoulomb.Frozen.IsIsolatedDipole
public import TwoComponentCoulomb.Frozen.IsIsolatedPair
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.NearestNeighbor.Components

/-!
# Isolated pairs and isolated dipoles

An *isolated pair* is a 2-cycle `{i, φ₁ i}` of the nearest-neighbour graph into which no other
vertex points; an *isolated dipole* is an isolated pair of opposite charges (source l. 207–215, 376–388, ruling R5). This file proves the structural facts needed for the counting of dipoles:

* `TwoComponentCoulomb.isIsolatedPair_iff_component` (ruling R5): `i` is in an isolated pair iff
  its connected component in the nearest-neighbour graph is exactly `{i, φ₁ i}`.
* `TwoComponentCoulomb.isIsolatedDipole_iff`.
* `TwoComponentCoulomb.card_filter_isIsolatedDipole`: the isolated-dipole vertices are twice as
  many as the isolated dipoles; `TwoComponentCoulomb.isolatedDipoles_card_le` bounds the number
  of dipoles by `N`.
* `TwoComponentCoulomb.card_not_isIsolatedPair_le`: `|(I^pair)^c| ≤ 6 (N - K)` (source
  l. 472–476: there are `2 (N - K)` tree vertices and at most `2 (N - K)` nonisolated
  components, each containing at most two vertices on its 2-cycle).
* Measurability of the events `{i ∈ I^pair}`, `{#dipoles = p}` and `{p ≤ #long dipoles}`.

All statements hold for every configuration `Z`, thanks to the index tie-break (ruling R4).
-/

public section

namespace TwoComponentCoulomb

open Finset

variable {N : ℕ}

/-! ### Characterizations of isolated pairs and dipoles -/

theorem isIsolatedDipole_iff (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    IsIsolatedDipole Z i ↔
      IsIsolatedPair Z i ∧ charge i * charge (nearestNeighbor Z i) = -1 := by
  unfold IsIsolatedDipole IsIsolatedPair
  exact and_assoc.symm

theorem IsIsolatedDipole.isIsolatedPair {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (h : IsIsolatedDipole Z i) : IsIsolatedPair Z i :=
  ((isIsolatedDipole_iff Z i).1 h).1

theorem IsIsolatedPair.nearestNeighbor_nearestNeighbor {Z : Fin N ⊕ Fin N → ℂ}
    {i : Fin N ⊕ Fin N} (h : IsIsolatedPair Z i) :
    nearestNeighbor Z (nearestNeighbor Z i) = i :=
  h.1

/-- If `i` is in an isolated pair, so is `φ₁ i`; it is the same pair. -/
theorem isIsolatedPair_nearestNeighbor {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (h : IsIsolatedPair Z i) : IsIsolatedPair Z (nearestNeighbor Z i) := by
  obtain ⟨h2, hk⟩ := h
  refine ⟨by rw [h2], fun k hk' => ?_⟩
  rw [h2] at hk'
  rcases hk (k := k) hk'.symm with h | h
  · exact Or.inr (by rw [h2]; exact h)
  · exact Or.inl h

/-- The vertices of an isolated pair lie on a 2-cycle. -/
theorem mem_cycleVerts_of_isIsolatedPair {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (h : IsIsolatedPair Z i) : i ∈ cycleVerts Z :=
  mem_cycleVerts.2 h.1

/-- If `i` is in an isolated dipole, so is `φ₁ i`; it is the same dipole. -/
theorem isIsolatedDipole_nearestNeighbor {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (h : IsIsolatedDipole Z i) : IsIsolatedDipole Z (nearestNeighbor Z i) := by
  rw [isIsolatedDipole_iff] at h ⊢
  refine ⟨isIsolatedPair_nearestNeighbor h.1, ?_⟩
  rw [h.1.1, mul_comm]
  exact h.2

/-- Ruling R5: `i` is in an isolated pair (`{i, φ₁ i}` is a 2-cycle into which no other vertex
points) iff the connected component of `i` in the nearest-neighbour graph is exactly
`{i, φ₁ i}`. This holds for every configuration. -/
theorem isIsolatedPair_iff_component (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    IsIsolatedPair Z i ↔
      ∀ j, (SimpleGraph.fromRel fun a b => nearestNeighbor Z a = b).Reachable j i ↔
        (j = i ∨ j = nearestNeighbor Z i) := by
  constructor
  · intro h j
    obtain ⟨h2, hk⟩ := h
    have hback : ∀ (n : ℕ) (j : Fin N ⊕ Fin N),
        ((nearestNeighbor Z)^[n] j = i ∨ (nearestNeighbor Z)^[n] j = nearestNeighbor Z i) →
          j = i ∨ j = nearestNeighbor Z i := by
      intro n
      induction n with
      | zero => exact fun j hj => hj
      | succ n ih =>
        intro j hj
        rw [Function.iterate_succ_apply] at hj
        exact hk j (ih _ hj)
    constructor
    · intro hr
      have hi : i ∈ cycleVerts Z := mem_cycleVerts.2 h2
      have hr' := (reachable_iff_cycleEdge_eq Z j i).1 hr
      rw [cycleEdge_of_mem_cycleVerts hi] at hr'
      unfold cycleEdge at hr'
      rcases Sym2.eq_iff.1 hr' with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hback (2 * N) j (Or.inl h1)
      · exact hback (2 * N) j (Or.inr h1)
    · rintro (rfl | rfl)
      · exact SimpleGraph.Reachable.refl _
      · exact (reachable_nearestNeighbor Z i).symm
  · intro H
    have hφ : (nearestNeighborGraph Z).Reachable (nearestNeighbor Z i) i :=
      (H _).2 (Or.inr rfl)
    have h2 : nearestNeighbor Z (nearestNeighbor Z i) = i := by
      have : (nearestNeighborGraph Z).Reachable (nearestNeighbor Z (nearestNeighbor Z i)) i :=
        (reachable_nearestNeighbor Z _).symm.trans hφ
      rcases (H _).1 this with h | h
      · exact h
      · exact absurd h (nearestNeighbor_ne Z _)
    refine ⟨h2, fun k hk => ?_⟩
    refine (H k).1 ?_
    refine (reachable_nearestNeighbor Z k).trans ?_
    rcases hk with hk | hk
    · rw [hk]
    · rw [hk]
      exact hφ

/-! ### Counting isolated pairs and dipoles -/

/-- Double counting of vertices of 2-cycles: if `P` is a predicate on vertices closed under `φ₁`,
holding only on 2-cycle vertices, then the vertices satisfying `P` are twice as many as the
2-cycles `{i, φ₁ i}` they form. -/
theorem card_filter_eq_two_mul_card_image_pair (Z : Fin N ⊕ Fin N → ℂ)
    (P : Fin N ⊕ Fin N → Prop) [DecidablePred P]
    (hP : ∀ i, P i → nearestNeighbor Z (nearestNeighbor Z i) = i ∧ P (nearestNeighbor Z i)) :
    (univ.filter P).card =
      2 * ((univ.filter P).image fun i => ({i, nearestNeighbor Z i} : Finset (Fin N ⊕ Fin N))).card := by
  rw [Finset.card_eq_sum_card_image (fun i => ({i, nearestNeighbor Z i} : Finset (Fin N ⊕ Fin N)))
    (univ.filter P)]
  have hfib : ∀ a ∈ (univ.filter P).image
      (fun i => ({i, nearestNeighbor Z i} : Finset (Fin N ⊕ Fin N))),
      ({x ∈ univ.filter P | ({x, nearestNeighbor Z x} : Finset (Fin N ⊕ Fin N)) = a}).card = 2 := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
    have hiP : P i := (Finset.mem_filter.1 hi).2
    have : ({x ∈ univ.filter P | ({x, nearestNeighbor Z x} : Finset (Fin N ⊕ Fin N)) =
        {i, nearestNeighbor Z i}}) = {i, nearestNeighbor Z i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨_, hjeq⟩
        have hj : j ∈ ({i, nearestNeighbor Z i} : Finset (Fin N ⊕ Fin N)) := by
          rw [← hjeq]
          exact Finset.mem_insert_self _ _
        simpa using hj
      · rintro (h | h)
        · subst h
          exact ⟨hiP, rfl⟩
        · subst h
          obtain ⟨h2, hPφ⟩ := hP i hiP
          exact ⟨hPφ, by rw [h2, Finset.pair_comm]⟩
    rw [this, Finset.card_pair (nearestNeighbor_ne Z i).symm]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  ring

/-- Source l. 378–388 (set `I^pair`): the vertices of isolated pairs are twice as many as the
isolated pairs `{i, φ₁ i}`. -/
theorem card_filter_isIsolatedPair (Z : Fin N ⊕ Fin N → ℂ) [DecidablePred (IsIsolatedPair Z)] :
    (univ.filter (IsIsolatedPair Z)).card =
      2 * ((univ.filter (IsIsolatedPair Z)).image
        fun i => ({i, nearestNeighbor Z i} : Finset (Fin N ⊕ Fin N))).card :=
  card_filter_eq_two_mul_card_image_pair Z _ fun _ h => ⟨h.1, isIsolatedPair_nearestNeighbor h⟩

/-- The vertices of isolated dipoles are twice as many as the isolated dipoles. -/
theorem card_filter_isIsolatedDipole (Z : Fin N ⊕ Fin N → ℂ) [DecidablePred (IsIsolatedDipole Z)] :
    (univ.filter (IsIsolatedDipole Z)).card = 2 * (isolatedDipoles Z).card := by
  classical
  unfold isolatedDipoles
  convert card_filter_eq_two_mul_card_image_pair Z (IsIsolatedDipole Z)
    fun _ h => ⟨h.1, isIsolatedDipole_nearestNeighbor h⟩

theorem filter_isIsolatedDipole_subset_cycleVerts (Z : Fin N ⊕ Fin N → ℂ)
    [DecidablePred (IsIsolatedDipole Z)] :
    univ.filter (IsIsolatedDipole Z) ⊆ cycleVerts Z := fun _ hi =>
  mem_cycleVerts_of_isIsolatedPair (Finset.mem_filter.1 hi).2.isIsolatedPair

/-- The number of isolated dipoles is at most the number `K` of components. -/
theorem isolatedDipoles_card_le_numComponents (Z : Fin N ⊕ Fin N → ℂ) :
    (isolatedDipoles Z).card ≤ numComponents Z := by
  classical
  have h1 := card_filter_isIsolatedDipole Z
  have h2 := Finset.card_le_card (filter_isIsolatedDipole_subset_cycleVerts Z)
  have h3 := card_cycleVerts_eq_two_mul_numComponents Z
  omega

/-- There are at most `N` isolated dipoles. -/
theorem isolatedDipoles_card_le (Z : Fin N ⊕ Fin N → ℂ) : (isolatedDipoles Z).card ≤ N :=
  (isolatedDipoles_card_le_numComponents Z).trans (numComponents_le Z)

open scoped Classical in
theorem longIsolatedDipoles_subset (Z : Fin N ⊕ Fin N → ℂ) (R : ℝ) :
    longIsolatedDipoles Z R ⊆ isolatedDipoles Z := by
  intro s hs
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hs
  exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _,
    (Finset.mem_filter.1 hi).2.1⟩, rfl⟩

theorem longIsolatedDipoles_card_le (Z : Fin N ⊕ Fin N → ℂ) (R : ℝ) :
    (longIsolatedDipoles Z R).card ≤ N :=
  (Finset.card_le_card (longIsolatedDipoles_subset Z R)).trans (isolatedDipoles_card_le Z)

/-- Source l. 472–476 (proof of Corollary 2.3): there are `2 (N - K)` tree vertices and at most
`2 (N - K)` nonisolated components, each of which has at most two vertices on its 2-cycle, so
`|(I^pair)^c| ≤ 6 (N - K)`. -/
theorem card_not_isIsolatedPair_le (Z : Fin N ⊕ Fin N → ℂ) [DecidablePred (IsIsolatedPair Z)] :
    (univ.filter fun i => ¬ IsIsolatedPair Z i).card ≤ 6 * (N - numComponents Z) := by
  set T : Finset (Fin N ⊕ Fin N) :=
    univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) ≠ i with hT
  have hsub : (univ.filter fun i => ¬ IsIsolatedPair Z i) ⊆
      T ∪ T.biUnion fun k => ({nearestNeighbor Z k, nearestNeighbor Z (nearestNeighbor Z k)} :
        Finset (Fin N ⊕ Fin N)) := by
    intro i hi
    have hi' : ¬ IsIsolatedPair Z i := (Finset.mem_filter.1 hi).2
    by_cases h2 : nearestNeighbor Z (nearestNeighbor Z i) = i
    · refine Finset.mem_union_right _ ?_
      obtain ⟨k, hk1, hk2⟩ : ∃ k, (nearestNeighbor Z k = i ∨ nearestNeighbor Z k =
          nearestNeighbor Z i) ∧ ¬ (k = i ∨ k = nearestNeighbor Z i) := by
        by_contra hcon
        exact hi' ⟨h2, fun k hk => by
          by_contra hnk
          exact hcon ⟨k, hk, hnk⟩⟩
      have hkT : k ∈ T := by
        rw [hT, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun hkk => ?_⟩
        rcases hk1 with h | h
        · rw [h] at hkk
          exact hk2 (Or.inr hkk.symm)
        · rw [h, h2] at hkk
          exact hk2 (Or.inl hkk.symm)
      refine Finset.mem_biUnion.2 ⟨k, hkT, ?_⟩
      rcases hk1 with h | h
      · rw [h]
        exact Finset.mem_insert_self _ _
      · rw [h, h2]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩)
  have hTcard : T.card = 2 * (N - numComponents Z) := card_tree_vertices Z
  calc (univ.filter fun i => ¬ IsIsolatedPair Z i).card
      ≤ (T ∪ T.biUnion fun k => ({nearestNeighbor Z k, nearestNeighbor Z (nearestNeighbor Z k)} :
          Finset (Fin N ⊕ Fin N))).card := Finset.card_le_card hsub
    _ ≤ T.card + (T.biUnion fun k => ({nearestNeighbor Z k,
          nearestNeighbor Z (nearestNeighbor Z k)} : Finset (Fin N ⊕ Fin N))).card :=
        Finset.card_union_le _ _
    _ ≤ T.card + ∑ k ∈ T, ({nearestNeighbor Z k, nearestNeighbor Z (nearestNeighbor Z k)} :
          Finset (Fin N ⊕ Fin N)).card := Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ T.card + ∑ _k ∈ T, 2 :=
        Nat.add_le_add_left (Finset.sum_le_sum fun _ _ => Finset.card_le_two) _
    _ = 3 * T.card := by rw [Finset.sum_const, smul_eq_mul]; ring
    _ = 6 * (N - numComponents Z) := by rw [hTcard]; ring

/-! ### Measurability -/

section Measurability

open MeasureTheory

private theorem measurableSingletonClass_index :
    MeasurableSingletonClass (Fin N ⊕ Fin N) :=
  ⟨fun x => by rcases x with a | a <;> simp [measurableSet_sum_iff]⟩

/-- A set that is a union of fibres of a measurable map into a finite measurable space with
measurable singletons is measurable. -/
private theorem measurableSet_of_factor {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Finite α] {Ψ : Ω → α} (hΨ : Measurable Ψ) {S : Set Ω}
    (hS : ∀ x y, Ψ x = Ψ y → x ∈ S → y ∈ S) : MeasurableSet S := by
  have h : S = Ψ ⁻¹' (Ψ '' S) := by
    ext x
    refine ⟨fun hx => ⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨y, hy, hxy⟩
    exact hS y x hxy hy
  rw [h]
  exact hΨ (Set.toFinite _).measurableSet

theorem isIsolatedPair_congr {Z Z' : Fin N ⊕ Fin N → ℂ}
    (h : nearestNeighbor Z = nearestNeighbor Z') (i : Fin N ⊕ Fin N) :
    IsIsolatedPair Z i ↔ IsIsolatedPair Z' i := by
  unfold IsIsolatedPair
  rw [h]

theorem isIsolatedDipole_congr {Z Z' : Fin N ⊕ Fin N → ℂ}
    (h : nearestNeighbor Z = nearestNeighbor Z') (i : Fin N ⊕ Fin N) :
    IsIsolatedDipole Z i ↔ IsIsolatedDipole Z' i := by
  unfold IsIsolatedDipole
  rw [h]

theorem isolatedDipoles_congr {Z Z' : Fin N ⊕ Fin N → ℂ}
    (h : nearestNeighbor Z = nearestNeighbor Z') : isolatedDipoles Z = isolatedDipoles Z' := by
  ext s
  simp only [isolatedDipoles, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    isIsolatedDipole_congr h, h]

theorem longIsolatedDipoles_congr {Z Z' : Fin N ⊕ Fin N → ℂ} (R : ℝ)
    (h : nearestNeighbor Z = nearestNeighbor Z')
    (hb : ∀ i, R < ‖Z i - Z (nearestNeighbor Z i)‖ ↔ R < ‖Z' i - Z' (nearestNeighbor Z' i)‖) :
    longIsolatedDipoles Z R = longIsolatedDipoles Z' R := by
  have hb' : ∀ i, R < ‖Z i - Z (nearestNeighbor Z' i)‖ ↔
      R < ‖Z' i - Z' (nearestNeighbor Z' i)‖ := fun i => by
    rw [← hb i, h]
  ext s
  simp only [longIsolatedDipoles, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    isIsolatedDipole_congr h, h, hb']

theorem measurableSet_isIsolatedPair (i : Fin N ⊕ Fin N) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | IsIsolatedPair Z i} := by
  have := measurableSingletonClass_index (N := N)
  exact measurableSet_of_factor measurable_nearestNeighbor fun x y h hx =>
    (isIsolatedPair_congr h i).1 hx

theorem measurable_card_isolatedDipoles :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => (isolatedDipoles Z).card := by
  have := measurableSingletonClass_index (N := N)
  refine measurable_to_countable' fun p => ?_
  exact measurableSet_of_factor measurable_nearestNeighbor fun x y h hx => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    rwa [← isolatedDipoles_congr h]

theorem measurableSet_isolatedDipoles_card_eq (p : ℕ) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | (isolatedDipoles Z).card = p} :=
  measurable_card_isolatedDipoles (measurableSet_singleton p)

/-- The event that the nearest neighbour of `i` is at distance larger than `R`. -/
theorem measurableSet_lt_norm_sub_nearestNeighbor (R : ℝ) (i : Fin N ⊕ Fin N) :
    MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | R < ‖Z i - Z (nearestNeighbor Z i)‖} := by
  have h : {Z : Fin N ⊕ Fin N → ℂ | R < ‖Z i - Z (nearestNeighbor Z i)‖} =
      ⋃ j, ({Z | nearestNeighbor Z i = j} ∩ {Z | R < ‖Z i - Z j‖}) := by
    ext Z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    refine ⟨fun hZ => ⟨_, rfl, hZ⟩, ?_⟩
    rintro ⟨j, hj, hZ⟩
    rw [hj]
    exact hZ
  rw [h]
  exact MeasurableSet.iUnion fun j => (measurableSet_nearestNeighbor_eq i j).inter
    (measurableSet_lt measurable_const (by fun_prop))

theorem measurable_card_longIsolatedDipoles (R : ℝ) :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => (longIsolatedDipoles Z R).card := by
  have := measurableSingletonClass_index (N := N)
  have hΨ : Measurable fun Z : Fin N ⊕ Fin N → ℂ =>
      (nearestNeighbor Z, fun i => decide (R < ‖Z i - Z (nearestNeighbor Z i)‖)) := by
    refine measurable_nearestNeighbor.prodMk (measurable_pi_iff.2 fun i => measurable_to_bool ?_)
    convert measurableSet_lt_norm_sub_nearestNeighbor R i using 1
    ext Z
    simp
  refine measurable_to_countable' fun p => ?_
  refine measurableSet_of_factor hΨ fun x y hxy hx => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hxy
  rw [← hx]
  refine congrArg Finset.card (longIsolatedDipoles_congr R h1 fun i => ?_).symm
  have := congrFun h2 i
  simpa using this

end Measurability

end TwoComponentCoulomb

end
