/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import TwoComponentCoulomb.Frozen.NumComponents
public import TwoComponentCoulomb.NearestNeighbor.Cycles

/-!
# Connected components of the nearest-neighbour graph

The nearest-neighbour graph `γ_{2N}(Z)` of a configuration `Z` (source l. 202–207 and l. 376–378)
has an edge between `i` and `φ₁ i`. Its connected components are 2-cycles with trees attached
(source l. 202–207, 378–388): since every orbit of `φ = nearestNeighbor Z` reaches a 2-cycle
(`TwoComponentCoulomb.exists_iterate_nearestNeighbor_two_cycle`), and every cycle is a 2-cycle
(`TwoComponentCoulomb.nearestNeighbor_nearestNeighbor_of_iterate_eq_self`), each component
contains exactly one 2-cycle. Because of the index tie-break of the frozen definition (ruling R4)
all statements here hold for *every* configuration `Z`.

## Main definitions and results

* `TwoComponentCoulomb.nearestNeighborGraph Z`: the graph `SimpleGraph.fromRel (φ · = ·)` whose
  connected components are counted by `numComponents Z`.
* `TwoComponentCoulomb.cycleVerts Z`: the vertices lying on a 2-cycle, i.e. `φ (φ i) = i`.
* `TwoComponentCoulomb.cycleOf Z i := φ^[2 N] i`: the cycle vertex that the orbit of `i` reaches.
* `TwoComponentCoulomb.reachable_iff_cycleOf`: `i` and `j` lie in the same component iff
  `cycleOf Z i = cycleOf Z j ∨ cycleOf Z i = φ (cycleOf Z j)`, i.e. iff their orbits reach the
  same 2-cycle.
* `TwoComponentCoulomb.card_cycleVerts_eq_two_mul_numComponents`: `|cycleVerts Z| = 2 K`.
* `TwoComponentCoulomb.numComponents_le`.
* `TwoComponentCoulomb.card_tree_vertices`: the `2 (N - K)` tree vertices (source l. 472–476).
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

variable {N : ℕ}

/-- The nearest-neighbour graph `γ_{2N}(Z_{2N})` on the index set (source l. 202–207, 378): `i`
and `j` are adjacent iff `φ₁ i = j` or `φ₁ j = i`. This is the graph whose connected components
are counted by `numComponents`. -/
abbrev nearestNeighborGraph (Z : Fin N ⊕ Fin N → ℂ) : SimpleGraph (Fin N ⊕ Fin N) :=
  SimpleGraph.fromRel fun i j => nearestNeighbor Z i = j

theorem numComponents_eq_nat_card (Z : Fin N ⊕ Fin N → ℂ) :
    numComponents Z = Nat.card (nearestNeighborGraph Z).ConnectedComponent :=
  rfl

theorem nearestNeighborGraph_adj (Z : Fin N ⊕ Fin N → ℂ) (a b : Fin N ⊕ Fin N) :
    (nearestNeighborGraph Z).Adj a b ↔ nearestNeighbor Z a = b ∨ nearestNeighbor Z b = a := by
  rw [nearestNeighborGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun h => h.2, ?_⟩
  rintro (h | h)
  · exact ⟨fun hab => nearestNeighbor_ne Z a (h.trans hab.symm), Or.inl h⟩
  · exact ⟨fun hab => nearestNeighbor_ne Z b (h.trans hab), Or.inr h⟩

theorem adj_nearestNeighbor (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    (nearestNeighborGraph Z).Adj i (nearestNeighbor Z i) :=
  (nearestNeighborGraph_adj Z _ _).2 (Or.inl rfl)

theorem reachable_nearestNeighbor (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    (nearestNeighborGraph Z).Reachable i (nearestNeighbor Z i) :=
  (adj_nearestNeighbor Z i).reachable

theorem reachable_iterate_nearestNeighbor (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N)
    (n : ℕ) : (nearestNeighborGraph Z).Reachable i ((nearestNeighbor Z)^[n] i) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl i
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (reachable_nearestNeighbor Z _)

/-! ### Vertices on 2-cycles -/

/-- The vertices lying on a 2-cycle of the nearest-neighbour graph: `φ₁ (φ₁ i) = i`. By
`nearestNeighbor_nearestNeighbor_of_iterate_eq_self` these are exactly the periodic points of
`φ₁`. The other `2 (N - K)` vertices are the "tree vertices" (source l. 472–476). -/
noncomputable def cycleVerts (Z : Fin N ⊕ Fin N → ℂ) : Finset (Fin N ⊕ Fin N) :=
  univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) = i

theorem mem_cycleVerts {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N} :
    i ∈ cycleVerts Z ↔ nearestNeighbor Z (nearestNeighbor Z i) = i := by
  simp [cycleVerts]

theorem nearestNeighbor_mem_cycleVerts {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (h : i ∈ cycleVerts Z) : nearestNeighbor Z i ∈ cycleVerts Z := by
  rw [mem_cycleVerts] at h ⊢
  rw [h]

theorem iterate_nearestNeighbor_mem_cycleVerts {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (h : i ∈ cycleVerts Z) (n : ℕ) : (nearestNeighbor Z)^[n] i ∈ cycleVerts Z := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact nearestNeighbor_mem_cycleVerts ih

theorem iterate_two_mul_of_mem_cycleVerts {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (h : i ∈ cycleVerts Z) (n : ℕ) : (nearestNeighbor Z)^[2 * n] i = i := by
  have h2 : Function.IsPeriodicPt (nearestNeighbor Z) 2 i := mem_cycleVerts.1 h
  exact (h2.mul_const n).eq

/-- The vertex of a 2-cycle which the orbit of `i` reaches after `2 N` steps. By
`exists_iterate_nearestNeighbor_two_cycle`, `cycleOf Z i ∈ cycleVerts Z`. -/
noncomputable def cycleOf (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) : Fin N ⊕ Fin N :=
  (nearestNeighbor Z)^[2 * N] i

theorem cycleOf_mem_cycleVerts (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    cycleOf Z i ∈ cycleVerts Z := by
  obtain ⟨m, hm, hmem⟩ := exists_iterate_nearestNeighbor_two_cycle Z i
  have h := iterate_nearestNeighbor_mem_cycleVerts (Z := Z) (mem_cycleVerts.2 hmem) (2 * N - m)
  rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hm] at h

theorem cycleOf_nearestNeighbor (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    cycleOf Z (nearestNeighbor Z i) = nearestNeighbor Z (cycleOf Z i) := by
  unfold cycleOf
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

theorem cycleOf_of_mem_cycleVerts {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (h : i ∈ cycleVerts Z) : cycleOf Z i = i :=
  iterate_two_mul_of_mem_cycleVerts h N

theorem reachable_cycleOf (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    (nearestNeighborGraph Z).Reachable i (cycleOf Z i) :=
  reachable_iterate_nearestNeighbor Z i _

/-- The (unordered) 2-cycle `{c, φ₁ c}` which the orbit of `i` reaches. -/
noncomputable def cycleEdge (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) : Sym2 (Fin N ⊕ Fin N) :=
  s(cycleOf Z i, nearestNeighbor Z (cycleOf Z i))

theorem cycleEdge_nearestNeighbor (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    cycleEdge Z (nearestNeighbor Z i) = cycleEdge Z i := by
  have h := mem_cycleVerts.1 (cycleOf_mem_cycleVerts Z i)
  unfold cycleEdge
  rw [cycleOf_nearestNeighbor, h, Sym2.eq_swap]

theorem cycleEdge_of_mem_cycleVerts {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (h : i ∈ cycleVerts Z) : cycleEdge Z i = s(i, nearestNeighbor Z i) := by
  rw [cycleEdge, cycleOf_of_mem_cycleVerts h]

/-- Two vertices lie in the same connected component of the nearest-neighbour graph iff their
orbits reach the same 2-cycle `{c, φ₁ c}`. -/
theorem reachable_iff_cycleEdge_eq (Z : Fin N ⊕ Fin N → ℂ) (i j : Fin N ⊕ Fin N) :
    (nearestNeighborGraph Z).Reachable i j ↔ cycleEdge Z i = cycleEdge Z j := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ hadj ih =>
      refine ih.trans ?_
      rcases (nearestNeighborGraph_adj Z _ _).1 hadj with h | h
      · rw [← h, cycleEdge_nearestNeighbor]
      · rw [← h, cycleEdge_nearestNeighbor]
  · intro h
    unfold cycleEdge at h
    have key : cycleOf Z i = cycleOf Z j ∨ cycleOf Z i = nearestNeighbor Z (cycleOf Z j) := by
      rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr h1
    refine (reachable_cycleOf Z i).trans ?_
    rcases key with key | key
    · rw [key]
      exact (reachable_cycleOf Z j).symm
    · rw [key]
      exact (reachable_nearestNeighbor Z _).symm.trans (reachable_cycleOf Z j).symm

/-- Two vertices lie in the same connected component of the nearest-neighbour graph iff their
orbits reach the same 2-cycle, i.e. iff `cycleOf Z i = cycleOf Z j` or
`cycleOf Z i = φ₁ (cycleOf Z j)`. -/
theorem reachable_iff_cycleOf (Z : Fin N ⊕ Fin N → ℂ) (i j : Fin N ⊕ Fin N) :
    (nearestNeighborGraph Z).Reachable i j ↔
      cycleOf Z i = cycleOf Z j ∨ cycleOf Z i = nearestNeighbor Z (cycleOf Z j) := by
  rw [reachable_iff_cycleEdge_eq]
  unfold cycleEdge
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨h, by rw [h]⟩
    · refine Or.inr ⟨h, ?_⟩
      rw [h]
      exact mem_cycleVerts.1 (cycleOf_mem_cycleVerts Z j)

/-- Two vertices of 2-cycles in the same component belong to the same 2-cycle. -/
theorem eq_or_eq_nearestNeighbor_of_reachable {Z : Fin N ⊕ Fin N → ℂ} {c d : Fin N ⊕ Fin N}
    (hc : c ∈ cycleVerts Z) (hd : d ∈ cycleVerts Z)
    (h : (nearestNeighborGraph Z).Reachable c d) : c = d ∨ c = nearestNeighbor Z d := by
  have := (reachable_iff_cycleOf Z c d).1 h
  rwa [cycleOf_of_mem_cycleVerts hc, cycleOf_of_mem_cycleVerts hd] at this

/-! ### Counting components -/

/-- Each connected component of the nearest-neighbour graph contains exactly one 2-cycle, so
that the number of vertices on 2-cycles is twice the number `K` of components (source l. 202–207, 378–388). -/
theorem card_cycleVerts_eq_two_mul_numComponents (Z : Fin N ⊕ Fin N → ℂ) :
    (cycleVerts Z).card = 2 * numComponents Z := by
  classical
  have : Fintype (nearestNeighborGraph Z).ConnectedComponent := Fintype.ofFinite _
  let f : Fin N ⊕ Fin N → (nearestNeighborGraph Z).ConnectedComponent := fun i =>
    (nearestNeighborGraph Z).connectedComponentMk i
  rw [Finset.card_eq_sum_card_image f (cycleVerts Z)]
  have himg : (cycleVerts Z).image f = univ := by
    ext X
    induction X using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      simp only [mem_image, mem_univ, iff_true]
      exact ⟨cycleOf Z v, cycleOf_mem_cycleVerts Z v,
        SimpleGraph.ConnectedComponent.eq.2 (reachable_cycleOf Z v).symm⟩
  have hfib : ∀ X ∈ (cycleVerts Z).image f, ({a ∈ cycleVerts Z | f a = X}).card = 2 := by
    intro X hX
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.1 hX
    have : ({a ∈ cycleVerts Z | f a = f c₀} : Finset _) = {c₀, nearestNeighbor Z c₀} := by
      ext c
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hc, hcc⟩
        exact eq_or_eq_nearestNeighbor_of_reachable hc hc₀ (SimpleGraph.ConnectedComponent.eq.1 hcc)
      · rintro (h | h)
        · exact ⟨h ▸ hc₀, h ▸ rfl⟩
        · exact ⟨h ▸ nearestNeighbor_mem_cycleVerts hc₀,
            h ▸ SimpleGraph.ConnectedComponent.eq.2 (reachable_nearestNeighbor Z c₀).symm⟩
    rw [this, Finset.card_pair (nearestNeighbor_ne Z c₀).symm]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, himg, card_univ,
    numComponents_eq_nat_card, Nat.card_eq_fintype_card]
  ring

theorem card_cycleVerts_le (Z : Fin N ⊕ Fin N → ℂ) : (cycleVerts Z).card ≤ 2 * N := by
  calc (cycleVerts Z).card ≤ Fintype.card (Fin N ⊕ Fin N) := Finset.card_le_univ _
    _ = 2 * N := by simp [two_mul]

/-- The number `K` of components is at most `N`. -/
theorem numComponents_le (Z : Fin N ⊕ Fin N → ℂ) : numComponents Z ≤ N := by
  have h1 := card_cycleVerts_eq_two_mul_numComponents Z
  have h2 := card_cycleVerts_le Z
  omega

/-- There are `2 (N - K)` tree vertices, i.e. vertices not on a 2-cycle (source l. 472–476). -/
theorem card_tree_vertices (Z : Fin N ⊕ Fin N → ℂ) :
    (univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) ≠ i).card =
      2 * (N - numComponents Z) := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin N ⊕ Fin N)))
    (fun i => nearestNeighbor Z (nearestNeighbor Z i) = i)
  have h1 := card_cycleVerts_eq_two_mul_numComponents Z
  have h2 := numComponents_le Z
  have h3 : (univ : Finset (Fin N ⊕ Fin N)).card = 2 * N := by simp [two_mul]
  have h4 : (univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) ≠ i).card +
      (cycleVerts Z).card = (univ : Finset (Fin N ⊕ Fin N)).card := by
    rw [add_comm]
    exact h
  omega

section Measurability

open MeasureTheory

end Measurability

end TwoComponentCoulomb

end
