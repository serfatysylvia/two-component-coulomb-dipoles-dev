/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Prod.Lex
public import Mathlib.Dynamics.PeriodicPts.Defs
public import TwoComponentCoulomb.Frozen.NumComponents
public import TwoComponentCoulomb.NearestNeighbor.General

/-!
# Structure of the nearest-neighbour graph of an arbitrary finite configuration

Source l. 642--644 and l. 217--222, 373--385: the cycle structure of the nearest-neighbour
graph proved for `Fin N ⊕ Fin N` in `NearestNeighbor/Cycles.lean` and
`NearestNeighbor/Components.lean`, redone for the map `TwoComponentCoulomb.nnMap key z` of an
arbitrary finite configuration `z : ι → ℂ` with tie-break key `key : ι ↪ ℕ` (ruling R4). Thanks
to the key, all statements hold for *every* configuration.

## Main definitions and results

* `TwoComponentCoulomb.nnMap_nnMap_of_iterate_eq_self`: all cycles are 2-cycles.
* `TwoComponentCoulomb.exists_iterate_nnMap_two_cycle`: every orbit reaches a 2-cycle within
  `Fintype.card ι` steps.
* `TwoComponentCoulomb.nnGraph key z`: the graph `SimpleGraph.fromRel (nnMap key z · = ·)`.
* `TwoComponentCoulomb.nnCycleVerts key z`: the vertices on a 2-cycle.
* `TwoComponentCoulomb.card_nnCycleVerts_eq_two_mul_card_components`: their number is twice the
  number of connected components of `nnGraph key z`.
* Bridge to the frozen definition on `Fin N ⊕ Fin N`:
  `TwoComponentCoulomb.numComponents_eq_nat_card_nnGraph`.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

variable {ι : Type*} [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (z : ι → ℂ)

/-! ### All cycles are 2-cycles -/

/-- The edge lengths of the nearest-neighbour graph do not increase along an orbit. -/
theorem norm_sub_nnMap_nnMap_le (i : ι) :
    ‖z (nnMap key z i) - z (nnMap key z (nnMap key z i))‖ ≤ ‖z i - z (nnMap key z i)‖ := by
  rw [norm_sub_rev (z i)]
  exact norm_sub_nnMap_le key z (nnMap_ne key z i).symm

/-- Tie-break step: if two consecutive edges have equal length and the orbit does not return
after two steps, the key strictly drops two steps later. -/
theorem key_nnMap_nnMap_lt {a : ι}
    (hd : ‖z (nnMap key z a) - z (nnMap key z (nnMap key z a))‖ = ‖z a - z (nnMap key z a)‖)
    (hne : nnMap key z (nnMap key z a) ≠ a) :
    key (nnMap key z (nnMap key z a)) < key a := by
  refine lt_of_le_of_ne (key_nnMap_le key z (nnMap_ne key z a).symm ?_)
    (fun h => hne (key.injective h))
  rw [norm_sub_rev, hd]

/-- Lexicographic key (edge length, tie-break key) of a vertex of the nearest-neighbour graph. -/
private noncomputable def lexKey (a : ι) : ℝ ×ₗ ℕ :=
  toLex (‖z a - z (nnMap key z a)‖, key a)

/-- Either `a` is in a 2-cycle, or two steps of the map strictly decrease the lexicographic
key. -/
private theorem nnMap_nnMap_eq_or_lexKey_lt (a : ι) :
    nnMap key z (nnMap key z a) = a ∨
      lexKey key z (nnMap key z (nnMap key z a)) < lexKey key z a := by
  by_cases hc : nnMap key z (nnMap key z a) = a
  · exact Or.inl hc
  right
  have h1 := norm_sub_nnMap_nnMap_le key z a
  have h2 := norm_sub_nnMap_nnMap_le key z (nnMap key z a)
  unfold lexKey
  rw [Prod.Lex.toLex_lt_toLex]
  by_cases hlt : ‖z (nnMap key z (nnMap key z a)) -
      z (nnMap key z (nnMap key z (nnMap key z a)))‖ < ‖z a - z (nnMap key z a)‖
  · exact Or.inl hlt
  right
  have hd1 : ‖z (nnMap key z (nnMap key z a)) -
      z (nnMap key z (nnMap key z (nnMap key z a)))‖ = ‖z a - z (nnMap key z a)‖ := by
    refine le_antisymm ?_ (not_lt.1 hlt)
    exact h2.trans h1
  have hd2 : ‖z (nnMap key z a) - z (nnMap key z (nnMap key z a))‖ =
      ‖z a - z (nnMap key z a)‖ := by
    refine le_antisymm h1 ?_
    rw [← hd1]
    exact h2
  exact ⟨hd1, key_nnMap_nnMap_lt key z hd2 hc⟩

/-- All cycles of the nearest-neighbour map are 2-cycles: a periodic point `i` of `nnMap key z`
satisfies `nnMap key z (nnMap key z i) = i`. This holds for every configuration, thanks to the
tie-break key (source l. 217--222, ruling R4). -/
theorem nnMap_nnMap_of_iterate_eq_self {i : ι} {n : ℕ} (hn : 0 < n)
    (h : (nnMap key z)^[n] i = i) : nnMap key z (nnMap key z i) = i := by
  have hper : Function.IsPeriodicPt (nnMap key z) n i := h
  -- the key attains its minimum on the cycle at some `φ^[k] i`
  obtain ⟨k, hk, hmin⟩ := (Finset.range n).exists_min_image
    (fun k => lexKey key z ((nnMap key z)^[k] i)) ⟨0, Finset.mem_range.2 hn⟩
  set a := (nnMap key z)^[k] i with ha
  -- the minimizer lies in a 2-cycle
  have ha2 : nnMap key z (nnMap key z a) = a := by
    refine (nnMap_nnMap_eq_or_lexKey_lt key z a).resolve_right (not_lt.2 ?_)
    have hmem : (k + 2) % n ∈ Finset.range n := Finset.mem_range.2 (Nat.mod_lt _ hn)
    have := hmin _ hmem
    rw [hper.iterate_mod_apply] at this
    have e : (nnMap key z)^[k + 2] i = nnMap key z (nnMap key z a) := by
      rw [add_comm, Function.iterate_add_apply]
      rfl
    rwa [e] at this
  -- `i` is in the forward orbit of `a`, hence also lies in this 2-cycle
  have hper2 : Function.IsPeriodicPt (nnMap key z) 2 a := ha2
  have hi : (nnMap key z)^[(n - 1) * k] a = i := by
    rw [ha, ← Function.iterate_add_apply]
    have : (n - 1) * k + k = n * k := by
      cases n with
      | zero => omega
      | succ m => simp [Nat.succ_mul]
    rw [this]
    exact (hper.mul_const k).eq
  rw [← hper2.iterate_mod_apply] at hi
  rw [← hi]
  have e : nnMap key z (nnMap key z ((nnMap key z)^[(n - 1) * k % 2] a)) =
      (nnMap key z)^[(n - 1) * k % 2] (nnMap key z (nnMap key z a)) := by
    have comm : ∀ (x : ι) (r : ℕ), (nnMap key z)^[2] ((nnMap key z)^[r] x) =
        (nnMap key z)^[r] ((nnMap key z)^[2] x) := fun x r => by
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, add_comm]
    exact comm a _
  rw [e, ha2]

/-- Every orbit of the nearest-neighbour map reaches a 2-cycle after at most `Fintype.card ι`
steps. -/
theorem exists_iterate_nnMap_two_cycle (i : ι) :
    ∃ m ≤ Fintype.card ι, nnMap key z (nnMap key z ((nnMap key z)^[m] i)) =
      (nnMap key z)^[m] i := by
  have hcard : Fintype.card ι < Fintype.card (Fin (Fintype.card ι + 1)) := by simp
  obtain ⟨p, q, hpq, hfpq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (Fintype.card ι + 1) => (nnMap key z)^[(k : ℕ)] i) hcard
  -- WLOG `p < q`
  have aux : ∀ p q : Fin (Fintype.card ι + 1), (p : ℕ) < q →
      (nnMap key z)^[(p : ℕ)] i = (nnMap key z)^[(q : ℕ)] i →
        ∃ m ≤ Fintype.card ι, nnMap key z (nnMap key z ((nnMap key z)^[m] i)) =
          (nnMap key z)^[m] i := by
    intro p q hlt heq
    refine ⟨p, Nat.lt_succ_iff.1 p.2, ?_⟩
    refine nnMap_nnMap_of_iterate_eq_self key z (n := (q : ℕ) - p)
      (Nat.sub_pos_of_lt hlt) ?_
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact heq.symm
  rcases lt_trichotomy (p : ℕ) q with hlt | heq | hgt
  · exact aux p q hlt hfpq
  · exact absurd (Fin.ext heq) hpq
  · exact aux q p hgt hfpq.symm

/-! ### The nearest-neighbour graph and its components -/

/-- The nearest-neighbour graph of a configuration (source l. 217--222, 375, 642--644): `i` and
`j` are adjacent iff `nnMap key z i = j` or `nnMap key z j = i`. -/
abbrev nnGraph : SimpleGraph ι :=
  SimpleGraph.fromRel fun i j => nnMap key z i = j

theorem nnGraph_adj (a b : ι) :
    (nnGraph key z).Adj a b ↔ nnMap key z a = b ∨ nnMap key z b = a := by
  rw [nnGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun h => h.2, ?_⟩
  rintro (h | h)
  · exact ⟨fun hab => nnMap_ne key z a (h.trans hab.symm), Or.inl h⟩
  · exact ⟨fun hab => nnMap_ne key z b (h.trans hab), Or.inr h⟩

theorem adj_nnMap (i : ι) : (nnGraph key z).Adj i (nnMap key z i) :=
  (nnGraph_adj key z _ _).2 (Or.inl rfl)

theorem reachable_nnMap (i : ι) : (nnGraph key z).Reachable i (nnMap key z i) :=
  (adj_nnMap key z i).reachable

theorem reachable_iterate_nnMap (i : ι) (n : ℕ) :
    (nnGraph key z).Reachable i ((nnMap key z)^[n] i) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl i
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (reachable_nnMap key z _)

section Cycles

open scoped Classical in
/-- The vertices lying on a 2-cycle of the nearest-neighbour graph: `nnMap key z (nnMap key z i) =
i`. By `nnMap_nnMap_of_iterate_eq_self` these are exactly the periodic points of `nnMap key z`.
The other vertices are the "tree vertices" (source l. 466--470). -/
noncomputable def nnCycleVerts : Finset ι :=
  univ.filter fun i => nnMap key z (nnMap key z i) = i

variable {key z}

theorem mem_nnCycleVerts {i : ι} :
    i ∈ nnCycleVerts key z ↔ nnMap key z (nnMap key z i) = i := by
  simp [nnCycleVerts]

theorem nnMap_mem_nnCycleVerts {i : ι} (h : i ∈ nnCycleVerts key z) :
    nnMap key z i ∈ nnCycleVerts key z := by
  rw [mem_nnCycleVerts] at h ⊢
  rw [h]

theorem iterate_nnMap_mem_nnCycleVerts {i : ι} (h : i ∈ nnCycleVerts key z) (n : ℕ) :
    (nnMap key z)^[n] i ∈ nnCycleVerts key z := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact nnMap_mem_nnCycleVerts ih

theorem iterate_two_mul_of_mem_nnCycleVerts {i : ι} (h : i ∈ nnCycleVerts key z) (n : ℕ) :
    (nnMap key z)^[2 * n] i = i := by
  have h2 : Function.IsPeriodicPt (nnMap key z) 2 i := mem_nnCycleVerts.1 h
  exact (h2.mul_const n).eq

variable (key z)

/-- The vertex of a 2-cycle which the orbit of `i` reaches after `2 * Fintype.card ι` steps (an
even number of steps, at least `Fintype.card ι`, so that cycle vertices are fixed). By
`exists_iterate_nnMap_two_cycle`, `nnCycleOf key z i ∈ nnCycleVerts key z`. -/
noncomputable def nnCycleOf (i : ι) : ι :=
  (nnMap key z)^[2 * Fintype.card ι] i

theorem nnCycleOf_mem_nnCycleVerts (i : ι) : nnCycleOf key z i ∈ nnCycleVerts key z := by
  obtain ⟨m, hm, hmem⟩ := exists_iterate_nnMap_two_cycle key z i
  have h := iterate_nnMap_mem_nnCycleVerts (mem_nnCycleVerts.2 hmem) (2 * Fintype.card ι - m)
  rwa [← Function.iterate_add_apply, Nat.sub_add_cancel (hm.trans (by omega))] at h

theorem nnCycleOf_nnMap (i : ι) :
    nnCycleOf key z (nnMap key z i) = nnMap key z (nnCycleOf key z i) := by
  unfold nnCycleOf
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

theorem nnCycleOf_of_mem_nnCycleVerts {i : ι} (h : i ∈ nnCycleVerts key z) :
    nnCycleOf key z i = i :=
  iterate_two_mul_of_mem_nnCycleVerts h _

theorem reachable_nnCycleOf (i : ι) : (nnGraph key z).Reachable i (nnCycleOf key z i) :=
  reachable_iterate_nnMap key z i _

/-- The (unordered) 2-cycle `{c, nnMap key z c}` which the orbit of `i` reaches. -/
noncomputable def nnCycleEdge (i : ι) : Sym2 ι :=
  s(nnCycleOf key z i, nnMap key z (nnCycleOf key z i))

theorem nnCycleEdge_nnMap (i : ι) :
    nnCycleEdge key z (nnMap key z i) = nnCycleEdge key z i := by
  have h := mem_nnCycleVerts.1 (nnCycleOf_mem_nnCycleVerts key z i)
  unfold nnCycleEdge
  rw [nnCycleOf_nnMap, h, Sym2.eq_swap]

/-- Two vertices lie in the same connected component of the nearest-neighbour graph iff their
orbits reach the same 2-cycle `{c, nnMap key z c}`. -/
theorem reachable_iff_nnCycleEdge_eq (i j : ι) :
    (nnGraph key z).Reachable i j ↔ nnCycleEdge key z i = nnCycleEdge key z j := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ hadj ih =>
      refine ih.trans ?_
      rcases (nnGraph_adj key z _ _).1 hadj with h | h
      · rw [← h, nnCycleEdge_nnMap]
      · rw [← h, nnCycleEdge_nnMap]
  · intro h
    unfold nnCycleEdge at h
    have hkey : nnCycleOf key z i = nnCycleOf key z j ∨
        nnCycleOf key z i = nnMap key z (nnCycleOf key z j) := by
      rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr h1
    refine (reachable_nnCycleOf key z i).trans ?_
    rcases hkey with hkey | hkey
    · rw [hkey]
      exact (reachable_nnCycleOf key z j).symm
    · rw [hkey]
      exact (reachable_nnMap key z _).symm.trans (reachable_nnCycleOf key z j).symm

/-- Two vertices lie in the same connected component of the nearest-neighbour graph iff their
orbits reach the same 2-cycle, i.e. iff `nnCycleOf key z i = nnCycleOf key z j` or
`nnCycleOf key z i = nnMap key z (nnCycleOf key z j)`. -/
theorem reachable_iff_nnCycleOf (i j : ι) :
    (nnGraph key z).Reachable i j ↔
      nnCycleOf key z i = nnCycleOf key z j ∨
        nnCycleOf key z i = nnMap key z (nnCycleOf key z j) := by
  rw [reachable_iff_nnCycleEdge_eq]
  unfold nnCycleEdge
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨h, by rw [h]⟩
    · refine Or.inr ⟨h, ?_⟩
      rw [h]
      exact mem_nnCycleVerts.1 (nnCycleOf_mem_nnCycleVerts key z j)

variable {key z}

/-- Two vertices of 2-cycles in the same component belong to the same 2-cycle. -/
theorem eq_or_eq_nnMap_of_reachable {c d : ι}
    (hc : c ∈ nnCycleVerts key z) (hd : d ∈ nnCycleVerts key z)
    (h : (nnGraph key z).Reachable c d) : c = d ∨ c = nnMap key z d := by
  have := (reachable_iff_nnCycleOf key z c d).1 h
  rwa [nnCycleOf_of_mem_nnCycleVerts key z hc, nnCycleOf_of_mem_nnCycleVerts key z hd] at this

variable (key z)

/-! ### Counting components -/

/-- Each connected component of the nearest-neighbour graph contains exactly one 2-cycle, so
that the number of vertices on 2-cycles is twice the number of components (source l. 217--222,
375--385). -/
theorem card_nnCycleVerts_eq_two_mul_card_components :
    (nnCycleVerts key z).card = 2 * Nat.card (nnGraph key z).ConnectedComponent := by
  have : Fintype (nnGraph key z).ConnectedComponent := Fintype.ofFinite _
  classical
  let f : ι → (nnGraph key z).ConnectedComponent := fun i =>
    (nnGraph key z).connectedComponentMk i
  rw [Finset.card_eq_sum_card_image f (nnCycleVerts key z)]
  have himg : (nnCycleVerts key z).image f = univ := by
    ext X
    induction X using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      simp only [mem_image, mem_univ, iff_true]
      exact ⟨nnCycleOf key z v, nnCycleOf_mem_nnCycleVerts key z v,
        SimpleGraph.ConnectedComponent.eq.2 (reachable_nnCycleOf key z v).symm⟩
  have hfib : ∀ X ∈ (nnCycleVerts key z).image f,
      ({a ∈ nnCycleVerts key z | f a = X}).card = 2 := by
    intro X hX
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.1 hX
    have : ({a ∈ nnCycleVerts key z | f a = f c₀} : Finset _) = {c₀, nnMap key z c₀} := by
      ext c
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hc, hcc⟩
        exact eq_or_eq_nnMap_of_reachable hc hc₀ (SimpleGraph.ConnectedComponent.eq.1 hcc)
      · rintro (h | h)
        · exact ⟨h ▸ hc₀, h ▸ rfl⟩
        · exact ⟨h ▸ nnMap_mem_nnCycleVerts hc₀,
            h ▸ SimpleGraph.ConnectedComponent.eq.2 (reachable_nnMap key z c₀).symm⟩
    rw [this, Finset.card_pair (nnMap_ne key z c₀).symm]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, himg, card_univ,
    Nat.card_eq_fintype_card]
  ring

end Cycles

/-! ### Bridge to the frozen definition on `Fin N ⊕ Fin N` -/

section Bridge

variable {N : ℕ} [Nontrivial (Fin N ⊕ Fin N)] (Z : Fin N ⊕ Fin N → ℂ)

/-- Bridge to the frozen `numComponents`: the number of connected components of the
nearest-neighbour graph `γ_{2N}(Z)` is the number of components of `nnGraph (sumKey N) Z`. -/
theorem numComponents_eq_nat_card_nnGraph :
    numComponents Z = Nat.card (nnGraph (sumKey N) Z).ConnectedComponent := by
  unfold numComponents
  rw [nearestNeighbor_eq_nnMap_fun]

end Bridge

end TwoComponentCoulomb

end
