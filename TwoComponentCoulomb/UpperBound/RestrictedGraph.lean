/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Logic.Relation
public import TwoComponentCoulomb.NearestNeighbor.GeneralStructure

/-!
# The restricted nearest-neighbour graph and its count (Proposition 3.7, Step 1)

Source: proof of Proposition 3.7 (`prop:auxk`), l. 1035--1077 (Step 1,
"counting graphs") and l. 1122--1125 (the cruder count used in Step 3).

For `p` points `z₁, …, z_p` with nearest-neighbour map `φ = nnMap key z` and a selected set
`S = {i : i < k}`, the *restricted graph* `γ'_p` has an edge `i → φ i` exactly for `i ∈ S`
(l. 1041). It is determined by the restriction `g : Fin k → Fin p` of `φ` to `S`. We identify
vertices with their values in `ℕ`, so that the selected vertices are the `v : Fin p` with
`v < k` and `g` is a map on `Fin k`; no hypothesis `k ≤ p` is needed for the definitions.

## Main definitions and results

* `TwoComponentCoulomb.restrictedEdge g`: the edge relation of the restricted graph of
  `g : Fin k → Fin p`; the vertices without outgoing edge are the `v ≥ k`.
* `TwoComponentCoulomb.twoCyclesIn g`: the `2`-cycles of `g` inside `S`, as pairs `i < j` of
  selected vertices with `g i = j` and `g j = i`; their number is `k₀` of the source.
* `TwoComponentCoulomb.rootsOf g`: the vertices `v ≥ k` outside `S` that are the target of a
  selected vertex, i.e. the roots of the nontrivial tree components; their number is `k₁`.
* `TwoComponentCoulomb.IsAdmissibleRestriction g`: `g` has no fixed point, and every directed
  cycle of its graph is a `2`-cycle (the structure inherited from `φ`).
* `TwoComponentCoulomb.restrictedGraphs p k k₀ k₁`: the set `D(k₀, k₁)` of source l. 1054 of
  admissible restricted graphs with `k₀` two-cycles and `k₁` roots.
* `TwoComponentCoulomb.exists_reach_root_or_twoCycle`: in an admissible restricted graph every
  forward path reaches a vertex outside `S` or a vertex on a `2`-cycle inside `S` (the component
  structure of source l. 1041--1044).
* `TwoComponentCoulomb.two_mul_card_twoCyclesIn_add_card_rootsOf_le`: `2 k₀ + k₁ ≤ k` (source
  l. 1054, used at l. 1127, 1134; `k₁ ≤ k` is a consequence).
* `TwoComponentCoulomb.card_restrictedGraphs_mul_le`,
  `TwoComponentCoulomb.card_restrictedGraphs_le`: the count
  `|D(k₀, k₁)| ≤ 2 ^ k k ^ k p ^ {k₁} / (k₀ ! k₁ !)` (source l. 1122--1125).
* `TwoComponentCoulomb.restrictedNnMap hk key z`: the restriction of `nnMap key z` to `S`;
  `TwoComponentCoulomb.restriction_mem_restrictedGraphs` shows that it lies in
  `D(k₀(z), k₁(z))` for the numbers `restrictedCycleCount`, `restrictedRootCount` computed
  from `z`; `TwoComponentCoulomb.two_mul_k0_add_k1_le` is `2 k₀(z) + k₁(z) ≤ k`; and
  `TwoComponentCoulomb.measurableSet_restrictedNnMap_eq` shows that the events
  `{z | restrictedNnMap hk key z = g}` are measurable.

The component structure of the source claim (l. 1041--1044) is encoded by the two conditions of
`IsAdmissibleRestriction` together with the definition of the roots: the vertices without
outgoing edge are exactly those outside `S`, a directed cycle can only be a `2`-cycle, and hence
every orbit starting in `S` leaves `S` (reaches a root) or ends in a `2`-cycle inside `S`.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset
open scoped Nat

section Definitions

variable {p k : ℕ}

/-- The edge relation of the restricted graph `γ'` of `g : Fin k → Fin p` (source l. 1041): there is
an edge `u → v` iff `u` is selected (`u < k`) and `g u = v`. The vertices without an outgoing
edge are exactly the `v ≥ k`. -/
def restrictedEdge (g : Fin k → Fin p) (u v : Fin p) : Prop :=
  ∃ h : (u : ℕ) < k, g ⟨u, h⟩ = v

open scoped Classical in
/-- The `2`-cycles of the restricted graph of `g` lying inside the selected set (source l. 1041):
the pairs `i < j` of selected vertices with `g i = j` and `g j = i`. Their number is the number
`k₀` of two-cycles of the source. -/
noncomputable def twoCyclesIn (g : Fin k → Fin p) : Finset (Fin k × Fin k) :=
  univ.filter fun e => e.1 < e.2 ∧ (g e.1 : ℕ) = e.2 ∧ (g e.2 : ℕ) = e.1

open scoped Classical in
/-- The roots of the nontrivial tree components of the restricted graph of `g` (source l. 1054):
the vertices `v ≥ k` outside the selected set that are the target of a selected vertex. Their
number is the number `k₁` of the source. -/
noncomputable def rootsOf (g : Fin k → Fin p) : Finset (Fin p) :=
  univ.filter fun v => k ≤ (v : ℕ) ∧ ∃ i, g i = v

/-- A map `g : Fin k → Fin p` is an *admissible restriction* if it has no fixed point and every
directed cycle of its restricted graph is a `2`-cycle: if `u → v` is an edge and `v` can reach
`u`, then `v → u` is an edge. These are the properties of `φ = nnMap key z` that survive
restriction to the selected set (source l. 1044: the nearest-neighbour graph has only
`2`-cycles). -/
def IsAdmissibleRestriction (g : Fin k → Fin p) : Prop :=
  (∀ i : Fin k, (g i : ℕ) ≠ i) ∧
    ∀ u v : Fin p, restrictedEdge g u v → Relation.ReflTransGen (restrictedEdge g) v u →
      restrictedEdge g v u

open scoped Classical in
/-- The set `D(k₀, k₁)` of source l. 1054: the admissible restricted graphs on `p` vertices with
`k` selected ones, having `k₀` two-cycles inside the selected set and `k₁` roots outside it. -/
noncomputable def restrictedGraphs (p k k₀ k₁ : ℕ) : Finset (Fin k → Fin p) :=
  univ.filter fun g => IsAdmissibleRestriction g ∧ (twoCyclesIn g).card = k₀ ∧
    (rootsOf g).card = k₁

end Definitions

section Basic

variable {p k : ℕ} {g : Fin k → Fin p}

theorem mem_twoCyclesIn {e : Fin k × Fin k} :
    e ∈ twoCyclesIn g ↔ e.1 < e.2 ∧ (g e.1 : ℕ) = e.2 ∧ (g e.2 : ℕ) = e.1 := by
  simp [twoCyclesIn]

theorem mem_rootsOf {v : Fin p} : v ∈ rootsOf g ↔ k ≤ (v : ℕ) ∧ ∃ i, g i = v := by
  simp [rootsOf]

theorem mem_restrictedGraphs {k₀ k₁ : ℕ} :
    g ∈ restrictedGraphs p k k₀ k₁ ↔
      IsAdmissibleRestriction g ∧ (twoCyclesIn g).card = k₀ ∧ (rootsOf g).card = k₁ := by
  simp [restrictedGraphs]

/-- Two distinct `2`-cycles share no vertex: the first vertex of a pair is not the second vertex
of a pair. -/
theorem fst_ne_snd_of_mem_twoCyclesIn {e e' : Fin k × Fin k} (he : e ∈ twoCyclesIn g)
    (he' : e' ∈ twoCyclesIn g) : e.1 ≠ e'.2 := by
  intro h
  rw [mem_twoCyclesIn] at he he'
  obtain ⟨h1, h2, -⟩ := he
  obtain ⟨h1', -, h3'⟩ := he'
  have h4 : (e.2 : ℕ) = e'.1 := by rw [← h2, h, h3']
  rw [Fin.lt_def] at h1 h1'
  rw [h] at h1
  omega

theorem fst_injOn_twoCyclesIn : Set.InjOn Prod.fst (twoCyclesIn g : Set (Fin k × Fin k)) := by
  intro e he e' he' h
  rw [mem_coe, mem_twoCyclesIn] at he he'
  have h2 : (e.2 : ℕ) = e'.2 := by rw [← he.2.1, ← he'.2.1, h]
  exact Prod.ext h (Fin.ext h2)

theorem snd_injOn_twoCyclesIn : Set.InjOn Prod.snd (twoCyclesIn g : Set (Fin k × Fin k)) := by
  intro e he e' he' h
  rw [mem_coe, mem_twoCyclesIn] at he he'
  have h2 : (e.1 : ℕ) = e'.1 := by rw [← he.2.2, ← he'.2.2, h]
  exact Prod.ext (Fin.ext h2) h

variable (g) in
/-- The selected vertices lying on a `2`-cycle inside the selected set. -/
noncomputable def restrictedCycleVerts : Finset (Fin k) :=
  (twoCyclesIn g).image Prod.fst ∪ (twoCyclesIn g).image Prod.snd

theorem mem_restrictedCycleVerts {i : Fin k} :
    i ∈ restrictedCycleVerts g ↔ ∃ e ∈ twoCyclesIn g, e.1 = i ∨ e.2 = i := by
  classical
  simp only [restrictedCycleVerts, mem_union, mem_image]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, he, Or.inl rfl⟩
    · exact ⟨e, he, Or.inr rfl⟩
  · rintro ⟨e, he, rfl | rfl⟩
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr ⟨e, he, rfl⟩

/-- A vertex on a `2`-cycle inside the selected set points into the selected set. -/
theorem val_lt_of_mem_restrictedCycleVerts {i : Fin k} (hi : i ∈ restrictedCycleVerts g) : (g i : ℕ) < k := by
  rw [mem_restrictedCycleVerts] at hi
  obtain ⟨e, he, rfl | rfl⟩ := hi
  · rw [(mem_twoCyclesIn.1 he).2.1]
    exact e.2.2
  · rw [(mem_twoCyclesIn.1 he).2.2]
    exact e.1.2

variable (g) in
theorem card_restrictedCycleVerts : (restrictedCycleVerts g).card = 2 * (twoCyclesIn g).card := by
  classical
  have hd : Disjoint ((twoCyclesIn g).image Prod.fst) ((twoCyclesIn g).image Prod.snd) := by
    rw [disjoint_left]
    intro i hi hi'
    obtain ⟨e, he, rfl⟩ := mem_image.1 hi
    obtain ⟨e', he', h⟩ := mem_image.1 hi'
    exact fst_ne_snd_of_mem_twoCyclesIn he he' h.symm
  rw [restrictedCycleVerts, card_union_of_disjoint hd, card_image_of_injOn fst_injOn_twoCyclesIn,
    card_image_of_injOn snd_injOn_twoCyclesIn]
  ring

/-- Source l. 1054 and l. 1127, 1134: `2 k₀ + k₁ ≤ k`. Every `2`-cycle inside the selected set uses
two selected vertices pointing into the selected set, and every root is the image of a selected
vertex pointing outside of it; these selected vertices are all distinct. -/
theorem two_mul_card_twoCyclesIn_add_card_rootsOf_le (g : Fin k → Fin p) :
    2 * (twoCyclesIn g).card + (rootsOf g).card ≤ k := by
  classical
  set W : Finset (Fin k) := univ.filter fun i => k ≤ (g i : ℕ) with hW
  have hR : (rootsOf g).card ≤ W.card := by
    have hsub : rootsOf g ⊆ W.image g := by
      intro v hv
      obtain ⟨hv1, i, rfl⟩ := mem_rootsOf.1 hv
      exact mem_image.2 ⟨i, by simp [hW, hv1], rfl⟩
    exact (card_le_card hsub).trans card_image_le
  have hd : Disjoint (restrictedCycleVerts g) W := by
    rw [disjoint_left]
    intro i hi hiW
    have h1 := val_lt_of_mem_restrictedCycleVerts hi
    have h2 : k ≤ (g i : ℕ) := by simpa [hW] using hiW
    omega
  have := card_le_univ (restrictedCycleVerts g ∪ W)
  rw [card_union_of_disjoint hd, card_restrictedCycleVerts, Fintype.card_fin] at this
  omega

theorem two_mul_add_le_of_mem_restrictedGraphs {k₀ k₁ : ℕ}
    (hg : g ∈ restrictedGraphs p k k₀ k₁) : 2 * k₀ + k₁ ≤ k := by
  obtain ⟨-, h0, h1⟩ := mem_restrictedGraphs.1 hg
  have := two_mul_card_twoCyclesIn_add_card_rootsOf_le g
  omega

end Basic

section Structure

variable {p k : ℕ}

/-- Source l. 1041--1044: in an admissible restricted graph, the forward path from any vertex
reaches either a vertex outside the selected set (a vertex without outgoing edge: the root of a
tree component) or a vertex on a `2`-cycle inside the selected set. Together with the absence of
fixed points, this says that every nontrivial component contains either a `2`-cycle inside the
selected set and no vertex outside it, or is a tree rooted at a vertex outside it. -/
theorem exists_reach_root_or_twoCycle {g : Fin k → Fin p} (hg : IsAdmissibleRestriction g)
    (u : Fin p) :
    ∃ w : Fin p, Relation.ReflTransGen (restrictedEdge g) u w ∧
      (k ≤ (w : ℕ) ∨ ∃ x, restrictedEdge g w x ∧ restrictedEdge g x w) := by
  classical
  set f : Fin p → Fin p := fun w => if h : (w : ℕ) < k then g ⟨w, h⟩ else w with hfdef
  have hf : ∀ w v, restrictedEdge g w v ↔ (w : ℕ) < k ∧ f w = v := by
    intro w v
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, by simp [hfdef, h]⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h, by simp [hfdef, h]⟩
  have hpath : ∀ (x : Fin p) (m : ℕ), (∀ j < m, ((f^[j] x : Fin p) : ℕ) < k) →
      Relation.ReflTransGen (restrictedEdge g) x (f^[m] x) := by
    intro x m
    induction m with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ m ih =>
      intro h
      rw [Function.iterate_succ_apply']
      exact (ih fun j hj => h j (by omega)).tail ((hf _ _).2 ⟨h m (by omega), rfl⟩)
  by_cases hex : ∃ j : ℕ, k ≤ ((f^[j] u : Fin p) : ℕ)
  · refine ⟨f^[Nat.find hex] u, hpath _ _ fun j hj => ?_, Or.inl (Nat.find_spec hex)⟩
    exact not_le.1 (Nat.find_min hex hj)
  · push Not at hex
    obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite fun n : ℕ => f^[n] u
    have key : ∀ a b : ℕ, a < b → f^[a] u = f^[b] u →
        ∃ w : Fin p, Relation.ReflTransGen (restrictedEdge g) u w ∧
          (k ≤ (w : ℕ) ∨ ∃ x, restrictedEdge g w x ∧ restrictedEdge g x w) := by
      intro a b hlt hfeq
      refine ⟨f^[a] u, hpath _ _ fun j _ => hex j, Or.inr ⟨f (f^[a] u), ?_, ?_⟩⟩
      · exact (hf _ _).2 ⟨hex a, rfl⟩
      · have hcyc : f^[(b - a - 1) + 1] (f^[a] u) = f^[a] u := by
          rw [← Function.iterate_add_apply, show b - a - 1 + 1 + a = b by omega]
          exact hfeq.symm
        have hpath' : Relation.ReflTransGen (restrictedEdge g) (f (f^[a] u)) (f^[a] u) := by
          have := hpath (f (f^[a] u)) (b - a - 1) fun j _ => by
            rw [← Function.iterate_succ_apply, ← Function.iterate_add_apply]
            exact hex _
          rwa [← Function.iterate_succ_apply, hcyc] at this
        exact hg.2 _ _ ((hf _ _).2 ⟨hex a, rfl⟩) hpath'
    rcases lt_or_gt_of_ne hab with h | h
    · exact key a b h hfab
    · exact key b a h hfab.symm

end Structure

section Counting

variable {p k : ℕ}

/-- The fibre of the pair `(roots, two-cycles)` through `g₀` is small: on the selected vertices
that are not on a `2`-cycle, a map with the same roots and the same `2`-cycles takes values in
the `≤ k + k₁` vertices of the selected set and of the set of roots, and on the vertices of a
`2`-cycle it is determined by the cycles (source l. 1069--1073). -/
theorem card_fiber_le (g₀ : Fin k → Fin p) :
    (univ.filter fun g : Fin k → Fin p =>
        twoCyclesIn g = twoCyclesIn g₀ ∧ rootsOf g = rootsOf g₀).card ≤
      (k + (rootsOf g₀).card) ^ (k - 2 * (twoCyclesIn g₀).card) := by
  classical
  set T : Finset (Fin p) := (univ.filter fun v : Fin p => (v : ℕ) < k) ∪ rootsOf g₀ with hT
  have hTcard : T.card ≤ k + (rootsOf g₀).card := by
    refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    calc (univ.filter fun v : Fin p => (v : ℕ) < k).card ≤ (range k).card :=
          card_le_card_of_injOn (fun v => (v : ℕ)) (by intro v hv; simpa using hv)
            (fun a _ b _ h => Fin.ext h)
      _ = k := card_range k
  set C := restrictedCycleVerts g₀ with hC
  have hsub : (univ.filter fun g : Fin k → Fin p =>
        twoCyclesIn g = twoCyclesIn g₀ ∧ rootsOf g = rootsOf g₀) ⊆
      Fintype.piFinset (fun i : Fin k => if i ∈ C then ({g₀ i} : Finset (Fin p)) else T) := by
    intro g hg
    obtain ⟨-, hP, hR⟩ := mem_filter.1 hg
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i ∈ C
    · simp only [hi, ↓reduceIte, mem_singleton]
      obtain ⟨e, he, hei⟩ := mem_restrictedCycleVerts.1 hi
      have he' : e ∈ twoCyclesIn g := hP ▸ he
      rw [mem_twoCyclesIn] at he he'
      apply Fin.ext
      rcases hei with rfl | rfl
      · rw [he'.2.1, he.2.1]
      · rw [he'.2.2, he.2.2]
    · simp only [hi, ↓reduceIte]
      rw [hT, mem_union, mem_filter]
      by_cases hlt : (g i : ℕ) < k
      · exact Or.inl ⟨mem_univ _, hlt⟩
      · right
        rw [← hR]
        exact mem_rootsOf.2 ⟨not_lt.1 hlt, i, rfl⟩
  refine (card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  have h1 : ∀ i : Fin k, (if i ∈ C then ({g₀ i} : Finset (Fin p)) else T).card =
      if i ∈ C then 1 else T.card := fun i => by
    by_cases hi : i ∈ C <;> simp [hi]
  simp_rw [h1]
  rw [prod_ite, prod_const_one, one_mul, prod_const]
  have h2 : (univ.filter fun i : Fin k => ¬ i ∈ C).card = k - 2 * (twoCyclesIn g₀).card := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin k))) (fun i => i ∈ C)
    rw [filter_mem_eq_inter, univ_inter, hC, card_restrictedCycleVerts, card_univ, Fintype.card_fin] at this
    rw [hC]
    omega
  rw [h2]
  exact Nat.pow_le_pow_left hTcard _

/-- The count of source l. 1056--1073 and 1122--1125, in multiplied form:
`|D(k₀, k₁)| k₀ ! k₁ ! ≤ 2 ^ k k ^ k p ^ {k₁}`. The roots are chosen among the `≤ p` vertices
outside the selected set (`p ^ {k₁} / k₁ !` choices), the `2`-cycles among the pairs of selected
vertices (`k ^ {2 k₀} / k₀ !` choices), and each of the remaining `k - 2 k₀` selected vertices has
one of `k + k₁ ≤ 2 k` targets. -/
theorem card_restrictedGraphs_mul_le (p k k₀ k₁ : ℕ) :
    (restrictedGraphs p k k₀ k₁).card * (k₀ ! * k₁ !) ≤ 2 ^ k * k ^ k * p ^ k₁ := by
  classical
  set D := restrictedGraphs p k k₀ k₁ with hD
  rcases D.eq_empty_or_nonempty with h | ⟨g₀, hg₀⟩
  · simp [h]
  have hle : 2 * k₀ + k₁ ≤ k := two_mul_add_le_of_mem_restrictedGraphs hg₀
  set O : Finset (Fin p) := univ.filter fun v => k ≤ (v : ℕ) with hO
  set idx : Finset (Finset (Fin p) × Finset (Fin k × Fin k)) :=
    powersetCard k₁ O ×ˢ powersetCard k₀ (univ : Finset (Fin k × Fin k)) with hidx
  have hmaps : Set.MapsTo (fun g : Fin k → Fin p => (rootsOf g, twoCyclesIn g)) D idx := by
    intro g hg
    obtain ⟨-, h0, h1⟩ := mem_restrictedGraphs.1 (mem_coe.1 hg)
    rw [mem_coe, hidx, mem_product, mem_powersetCard, mem_powersetCard]
    refine ⟨⟨fun v hv => ?_, h1⟩, subset_univ _, h0⟩
    simpa [hO] using (mem_rootsOf.1 hv).1
  have hsum := card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ b ∈ idx, (D.filter fun g => (rootsOf g, twoCyclesIn g) = b).card ≤
      (k + k₁) ^ (k - 2 * k₀) := by
    intro b hb
    rcases (D.filter fun g => (rootsOf g, twoCyclesIn g) = b).eq_empty_or_nonempty with h | ⟨g₁, hg₁⟩
    · rw [h, card_empty]
      exact Nat.zero_le _
    · obtain ⟨hg₁D, hg₁b⟩ := mem_filter.1 hg₁
      obtain ⟨-, h0, h1⟩ := mem_restrictedGraphs.1 hg₁D
      have hsub : (D.filter fun g => (rootsOf g, twoCyclesIn g) = b) ⊆
          univ.filter fun g : Fin k → Fin p =>
            twoCyclesIn g = twoCyclesIn g₁ ∧ rootsOf g = rootsOf g₁ := by
        intro g hg
        obtain ⟨-, hgb⟩ := mem_filter.1 hg
        refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
        · exact (Prod.ext_iff.1 (hgb.trans hg₁b.symm)).2
        · exact (Prod.ext_iff.1 (hgb.trans hg₁b.symm)).1
      have := (card_le_card hsub).trans (card_fiber_le g₁)
      rwa [h0, h1] at this
  have hidxcard : idx.card ≤ p.choose k₁ * (k * k).choose k₀ := by
    rw [hidx, card_product, card_powersetCard, card_powersetCard, card_univ, Fintype.card_prod,
      Fintype.card_fin]
    refine Nat.mul_le_mul (Nat.choose_le_choose _ ?_) le_rfl
    calc O.card ≤ (univ : Finset (Fin p)).card := card_le_univ O
      _ = p := by rw [card_univ, Fintype.card_fin]
  have hcard : D.card ≤ p.choose k₁ * (k * k).choose k₀ * (k + k₁) ^ (k - 2 * k₀) := by
    rw [hsum]
    calc ∑ b ∈ idx, (D.filter fun g => (rootsOf g, twoCyclesIn g) = b).card
        ≤ ∑ _b ∈ idx, (k + k₁) ^ (k - 2 * k₀) := sum_le_sum hfib
      _ = idx.card * (k + k₁) ^ (k - 2 * k₀) := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul hidxcard le_rfl
  -- arithmetic
  have hk₁ : k₁ ≤ k := by omega
  have e1 : k₁ ! * p.choose k₁ ≤ p ^ k₁ := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow p k₁
  have e0 : k₀ ! * (k * k).choose k₀ ≤ (k * k) ^ k₀ := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow (k * k) k₀
  have e2 : (k + k₁) ^ (k - 2 * k₀) ≤ (2 * k) ^ (k - 2 * k₀) :=
    Nat.pow_le_pow_left (by omega) _
  calc D.card * (k₀ ! * k₁ !)
      ≤ (p.choose k₁ * (k * k).choose k₀ * (k + k₁) ^ (k - 2 * k₀)) * (k₀ ! * k₁ !) :=
        Nat.mul_le_mul_right _ hcard
    _ = (k₁ ! * p.choose k₁) * (k₀ ! * (k * k).choose k₀) * (k + k₁) ^ (k - 2 * k₀) := by ring
    _ ≤ p ^ k₁ * (k * k) ^ k₀ * (2 * k) ^ (k - 2 * k₀) :=
        Nat.mul_le_mul (Nat.mul_le_mul e1 e0) e2
    _ = 2 ^ (k - 2 * k₀) * k ^ k * p ^ k₁ := by
        have : k ^ k = k ^ (2 * k₀) * k ^ (k - 2 * k₀) := by
          rw [← pow_add, Nat.add_sub_cancel' (by omega)]
        rw [this, mul_pow, pow_mul, sq]
        ring
    _ ≤ 2 ^ k * k ^ k * p ^ k₁ := by
        gcongr
        exact Nat.sub_le _ _

/-- The count of source l. 1122--1125: `|D(k₀, k₁)| ≤ 2 ^ k k ^ k p ^ {k₁} / (k₀ ! k₁ !)`. -/
theorem card_restrictedGraphs_le (p k k₀ k₁ : ℕ) :
    ((restrictedGraphs p k k₀ k₁).card : ℝ) ≤
      2 ^ k * (k : ℝ) ^ k * (p : ℝ) ^ k₁ / ((k₀ ! : ℝ) * (k₁ ! : ℝ)) := by
  rw [le_div_iff₀ (by positivity)]
  exact_mod_cast card_restrictedGraphs_mul_le p k k₀ k₁

end Counting

section NearestNeighbor

variable {p k : ℕ} [Nontrivial (Fin p)] (hk : k ≤ p) (key : Fin p ↪ ℕ) (z : Fin p → ℂ)

/-- The restriction of the nearest-neighbour map `φ = nnMap key z` of `p` points to the selected
vertices `{i : i < k}` (source l. 1041: the edges `i → φ i` of `γ'_p` are those with `i` among the first `k` indices). -/
noncomputable def restrictedNnMap : Fin k → Fin p := fun i => nnMap key z (Fin.castLE hk i)

/-- The number `k₀` of `2`-cycles of `φ = nnMap key z` contained in the selected set
`{i : i < k}`. -/
noncomputable def restrictedCycleCount : ℕ := (twoCyclesIn (restrictedNnMap hk key z)).card

/-- The number `k₁` of roots of `γ'_p`: the vertices `v ≥ k` outside the selected set that are the
nearest neighbour of some selected vertex. -/
noncomputable def restrictedRootCount : ℕ := (rootsOf (restrictedNnMap hk key z)).card

theorem restrictedEdge_restrictedNnMap_iff (u v : Fin p) :
    restrictedEdge (restrictedNnMap hk key z) u v ↔ (u : ℕ) < k ∧ nnMap key z u = v := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, rfl⟩

/-- The edges of the restricted graph follow the nearest-neighbour map: a directed path from `a`
to `b` in the restricted graph gives `b = φ^[m] a` for some `m`. -/
theorem exists_iterate_nnMap_of_reflTransGen {a b : Fin p}
    (h : Relation.ReflTransGen (restrictedEdge (restrictedNnMap hk key z)) a b) :
    ∃ m : ℕ, (nnMap key z)^[m] a = b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 1, ?_⟩
    rw [Function.iterate_succ_apply', hm]
    exact ((restrictedEdge_restrictedNnMap_iff hk key z _ _).1 hbc).2

/-- The restriction of the nearest-neighbour map is an admissible restricted graph: it has no
fixed point, and, since all cycles of `φ` are `2`-cycles (`nnMap_nnMap_of_iterate_eq_self`), all
directed cycles of `γ'_p` are `2`-cycles (source l. 1044). -/
theorem isAdmissibleRestriction_restrictedNnMap :
    IsAdmissibleRestriction (restrictedNnMap hk key z) := by
  refine ⟨fun i h => nnMap_ne key z (Fin.castLE hk i) (Fin.ext h), ?_⟩
  intro u v huv hvu
  obtain ⟨hu, rfl⟩ := (restrictedEdge_restrictedNnMap_iff hk key z _ _).1 huv
  rcases hvu.cases_head with h | ⟨c, hvc, hcu⟩
  · exact absurd h (nnMap_ne key z u)
  · obtain ⟨hv, rfl⟩ := (restrictedEdge_restrictedNnMap_iff hk key z _ _).1 hvc
    obtain ⟨m, hm⟩ := exists_iterate_nnMap_of_reflTransGen hk key z hcu
    have hcyc : (nnMap key z)^[m + 2] u = u := by
      rw [Function.iterate_add_apply]
      exact hm
    refine (restrictedEdge_restrictedNnMap_iff hk key z _ _).2 ⟨hv, ?_⟩
    exact nnMap_nnMap_of_iterate_eq_self key z (n := m + 2) (by omega) hcyc

/-- Source l. 1041--1054: the restriction of the nearest-neighbour map of `z` to the selected set
`{i : i < k}` lies in `D(k₀(z), k₁(z))`, where `k₀(z)` is the number of `2`-cycles of `φ` inside
the selected set and `k₁(z)` the number of roots. -/
theorem restriction_mem_restrictedGraphs :
    restrictedNnMap hk key z ∈
      restrictedGraphs p k (restrictedCycleCount hk key z) (restrictedRootCount hk key z) :=
  mem_restrictedGraphs.2 ⟨isAdmissibleRestriction_restrictedNnMap hk key z, rfl, rfl⟩

/-- Source l. 1054, 1127, 1134: `2 k₀(z) + k₁(z) ≤ k`. -/
theorem two_mul_k0_add_k1_le :
    2 * restrictedCycleCount hk key z + restrictedRootCount hk key z ≤ k :=
  two_mul_card_twoCyclesIn_add_card_rootsOf_le _

/-- Source l. 1054: `k₁(z) ≤ k`. -/
theorem restrictedRootCount_le : restrictedRootCount hk key z ≤ k := by
  have := two_mul_k0_add_k1_le hk key z
  omega

/-- Every configuration has a type `(k₀, k₁)` of restricted graph, with `2 k₀ + k₁ ≤ k`
(source l. 1054). -/
theorem exists_restriction_mem_restrictedGraphs :
    ∃ k₀ k₁ : ℕ, 2 * k₀ + k₁ ≤ k ∧ restrictedNnMap hk key z ∈ restrictedGraphs p k k₀ k₁ :=
  ⟨_, _, two_mul_k0_add_k1_le hk key z,
    restriction_mem_restrictedGraphs hk key z⟩

end NearestNeighbor

section Measurability

open MeasureTheory

variable {p k : ℕ} [Nontrivial (Fin p)] (hk : k ≤ p) (key : Fin p ↪ ℕ)

/-- The restriction of the nearest-neighbour map is a measurable function of the configuration,
valued in the finite set of maps `Fin k → Fin p`. -/
theorem measurable_restrictedNnMap : Measurable fun z : Fin p → ℂ => restrictedNnMap hk key z := by
  refine measurable_pi_iff.2 fun i => ?_
  exact (measurable_nnMap key).eval

/-- The event `{γ'_p = g}` of source l. 1081--1086 is measurable for each graph `g`. -/
theorem measurableSet_restrictedNnMap_eq (g : Fin k → Fin p) :
    MeasurableSet {z : Fin p → ℂ | restrictedNnMap hk key z = g} :=
  (measurable_restrictedNnMap hk key) (measurableSet_singleton g)

end Measurability

end TwoComponentCoulomb

end
