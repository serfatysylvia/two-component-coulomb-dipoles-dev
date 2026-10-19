/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Fin.Basic
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.Frozen.IsGeneric
public import TwoComponentCoulomb.NearestNeighbor.TwiceIsolated
public import TwoComponentCoulomb.UpperBound.InvolutionCover

/-!
# The set of marked graphs and its combinatorial cover

Source: l. 1219, 1421 (twice-isolated cycles and the definition of `D_{2N,K,p,p₀}`, written
`D_{2N,K,p,p̂₀}` in the source) and Step 1 of the proof of Proposition 3.10, l. 1462--1488
(enumeration of the graphs).

`TwoComponentCoulomb.markedGraphs hN K p p₀` is the set `D_{2N,K,p,p₀}`: the pairs `(f, T)` of a
nearest-neighbour map `f = φ₁(Z)` of a generic configuration `Z` in the box and the set `T` of
vertices of its twice-isolated 2-cycles, where `Z` has `K` connected components, `p` twice-isolated
cycles and `p₀` neutral twice-isolated cycles.

The enumeration of Step 1 is carried out as follows. The involution `h` which agrees with `f` on
the vertices of 2-cycles and fixes the tree vertices is built from

* the `p₀` neutral twice-isolated pairs (an injective partial map from positive to negative
  vertices),
* the other `K - p₀` pairs (a set of representatives and an injection into the remaining vertices),
* the marking of `p - p₀` of the latter pairs,

and `f` is then an arbitrary map on the `2N - 2K` tree vertices. This gives
`TwoComponentCoulomb.card_markedGraphs_le`:
`|D_{2N,K,p,p₀}| ≤ C(N,p₀) (N)_{p₀} · C(2N-2p₀, K-p₀) (2N-p₀-K)_{K-p₀} · C(K-p₀, p-p₀) ·
(2N)^{2N-2K}` (with falling factorials `(n)_k`). The counting uses
`TwoComponentCoulomb.involutionCover` (`UpperBound/InvolutionCover.lean`).

* `TwoComponentCoulomb.markedGraphs hN K p p₀`: the set `D_{2N,K,p,p₀}`.
* `TwoComponentCoulomb.cycleInvolution Z`: the involution of the 2-cycles of `φ₁(Z)`.
* `TwoComponentCoulomb.IsMarkedInvolution`,
  `TwoComponentCoulomb.isMarkedInvolution_cycleInvolution`.
* `TwoComponentCoulomb.markedCover`, `TwoComponentCoulomb.mem_markedCover`,
  `TwoComponentCoulomb.card_markedCover_le`.
* `TwoComponentCoulomb.markedGraphs_subset`, `TwoComponentCoulomb.card_markedGraphs_le`.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

section Definitions

variable {N : ℕ}

open scoped Classical in
/-- `D_{2N,K,p,p₀}` (source l. 1421): the nearest-neighbour graphs `φ₁(Z)` of generic
configurations `Z` of the box `Λ`, marked at their twice-isolated 2-cycles, with `K` connected
components, `p` marked cycles and `p₀` neutral marked cycles. A marked graph is a pair `(f, T)`
of the map `f = φ₁` and the set `T` of vertices of the marked 2-cycles. -/
noncomputable def markedGraphs (hN : 2 ≤ N) (K p p₀ : ℕ) :
    Finset ((Fin N ⊕ Fin N → Fin N ⊕ Fin N) × Finset (Fin N ⊕ Fin N)) :=
  univ.filter fun γ => ∃ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) ∧ IsGeneric Z ∧
    nearestNeighbor Z = γ.1 ∧ twiceIsolatedSet hN Z = γ.2 ∧ numComponents Z = K ∧
    numTwiceIsolated hN Z = p ∧ numNeutralTwiceIsolated hN Z = p₀

theorem mem_markedGraphs {hN : 2 ≤ N} {K p p₀ : ℕ}
    {γ : (Fin N ⊕ Fin N → Fin N ⊕ Fin N) × Finset (Fin N ⊕ Fin N)} :
    γ ∈ markedGraphs hN K p p₀ ↔ ∃ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) ∧ IsGeneric Z ∧
      nearestNeighbor Z = γ.1 ∧ twiceIsolatedSet hN Z = γ.2 ∧ numComponents Z = K ∧
      numTwiceIsolated hN Z = p ∧ numNeutralTwiceIsolated hN Z = p₀ := by
  simp [markedGraphs]

/-- The involution which agrees with `φ₁` on the vertices of 2-cycles and is the identity on the
tree vertices. -/
noncomputable def cycleInvolution (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) : Fin N ⊕ Fin N :=
  if nearestNeighbor Z (nearestNeighbor Z i) = i then nearestNeighbor Z i else i

theorem cycleInvolution_of_mem_cycleVerts {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (hi : i ∈ cycleVerts Z) : cycleInvolution Z i = nearestNeighbor Z i := by
  unfold cycleInvolution
  simp [mem_cycleVerts.1 hi]

theorem cycleInvolution_of_not_mem_cycleVerts {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (hi : i ∉ cycleVerts Z) : cycleInvolution Z i = i := by
  unfold cycleInvolution
  simp [mem_cycleVerts.not.1 hi]

theorem cycleInvolution_involutive (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    cycleInvolution Z (cycleInvolution Z i) = i := by
  by_cases hi : i ∈ cycleVerts Z
  · rw [cycleInvolution_of_mem_cycleVerts hi,
      cycleInvolution_of_mem_cycleVerts (nearestNeighbor_mem_cycleVerts hi)]
    exact mem_cycleVerts.1 hi
  · rw [cycleInvolution_of_not_mem_cycleVerts hi, cycleInvolution_of_not_mem_cycleVerts hi]

theorem movedPoints_cycleInvolution (Z : Fin N ⊕ Fin N → ℂ) :
    movedPoints (cycleInvolution Z) = cycleVerts Z := by
  ext i
  rw [mem_movedPoints]
  by_cases hi : i ∈ cycleVerts Z
  · simp only [hi, iff_true]
    rw [cycleInvolution_of_mem_cycleVerts hi]
    exact nearestNeighbor_ne Z i
  · simp only [hi, iff_false, not_not]
    exact cycleInvolution_of_not_mem_cycleVerts hi

/-- The data of a marked involution: `h` is an involution with `2 K` moved points, `T` is an
`h`-closed set of `2 p` moved points, `2 p₀` of which are joined to a vertex of the other sign
(neutral pairs). -/
def IsMarkedInvolution (K p p₀ : ℕ) (h : Fin N ⊕ Fin N → Fin N ⊕ Fin N)
    (T : Finset (Fin N ⊕ Fin N)) : Prop :=
  (∀ i, h (h i) = i) ∧ (movedPoints h).card = 2 * K ∧ T ⊆ movedPoints h ∧
    (∀ i ∈ T, h i ∈ T) ∧ T.card = 2 * p ∧
    (T.filter fun i => i.isLeft ≠ (h i).isLeft).card = 2 * p₀

theorem charge_mul_eq_neg_one_iff (i j : Fin N ⊕ Fin N) :
    charge i * charge j = -1 ↔ i.isLeft ≠ j.isLeft := by
  rcases i with a | a <;> rcases j with b | b <;> simp [charge] <;> norm_num

/-- A realizable marked graph yields a marked involution. -/
theorem isMarkedInvolution_cycleInvolution (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) :
    IsMarkedInvolution (numComponents Z) (numTwiceIsolated hN Z) (numNeutralTwiceIsolated hN Z)
      (cycleInvolution Z) (twiceIsolatedSet hN Z) := by
  classical
  have hT : ∀ i ∈ twiceIsolatedSet hN Z, i ∈ cycleVerts Z := fun i hi =>
    isolatedPairSet_subset_cycleVerts (twiceIsolatedSet_subset_isolatedPairSet hN Z hi)
  refine ⟨cycleInvolution_involutive Z, ?_, ?_, ?_, card_twiceIsolatedSet, ?_⟩
  · rw [movedPoints_cycleInvolution]
    exact card_cycleVerts_eq_two_mul_numComponents Z
  · rw [movedPoints_cycleInvolution]
    exact hT
  · intro i hi
    rw [cycleInvolution_of_mem_cycleVerts (hT i hi)]
    exact nearestNeighbor_mem_twiceIsolatedSet hi
  · rw [← card_neutralTwiceIsolatedSet (hN := hN) (Z := Z)]
    congr 1
    ext i
    rw [mem_filter, mem_neutralTwiceIsolatedSet_iff, ← charge_mul_eq_neg_one_iff]
    constructor
    · rintro ⟨hi, h2⟩
      rw [cycleInvolution_of_mem_cycleVerts (hT i hi)] at h2
      exact ⟨hi, h2⟩
    · rintro ⟨hi, h2⟩
      rw [cycleInvolution_of_mem_cycleVerts (hT i hi)]
      exact ⟨hi, h2⟩

end Definitions

/-! ### The cover -/

section Cover

variable {N : ℕ}

/-- The positive vertices `x₁, …, x_N`. -/
def posVerts (N : ℕ) : Finset (Fin N ⊕ Fin N) := univ.map Function.Embedding.inl

/-- The negative vertices `y₁, …, y_N`. -/
def negVerts (N : ℕ) : Finset (Fin N ⊕ Fin N) := univ.map Function.Embedding.inr

theorem card_posVerts (N : ℕ) : (posVerts N).card = N := by simp [posVerts]

theorem card_negVerts (N : ℕ) : (negVerts N).card = N := by simp [negVerts]

theorem mem_posVerts {i : Fin N ⊕ Fin N} : i ∈ posVerts N ↔ i.isLeft = true := by
  rcases i with a | a <;> simp [posVerts]

theorem mem_negVerts {i : Fin N ⊕ Fin N} : i ∈ negVerts N ↔ i.isLeft = false := by
  rcases i with a | a <;> simp [negVerts]

/-- The involution which is `h₀` on the points moved by `h₀` and `h₁` elsewhere. -/
def combineInv (h₀ h₁ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (i : Fin N ⊕ Fin N) : Fin N ⊕ Fin N :=
  if h₀ i ≠ i then h₀ i else h₁ i

open scoped Classical in
/-- The involutions on the `p₀` neutral twice-isolated pairs: representatives among the positive
vertices, embedded in the negative vertices. -/
noncomputable def neutralCover (N p₀ : ℕ) : Finset (Fin N ⊕ Fin N → Fin N ⊕ Fin N) :=
  (involutionCover (posVerts N) (fun _ => negVerts N) p₀).filter fun h₀ =>
    (∀ i, h₀ (h₀ i) = i) ∧ (movedPoints h₀).card = 2 * p₀

open scoped Classical in
/-- The involutions on the other `K - p₀` pairs, supported outside the neutral ones. -/
noncomputable def otherCover (N K p₀ : ℕ) (h₀ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) :
    Finset (Fin N ⊕ Fin N → Fin N ⊕ Fin N) :=
  (involutionCover (univ \ movedPoints h₀) (fun A => (univ \ movedPoints h₀) \ A) (K - p₀)).filter
    fun h₁ => (∀ i, h₁ (h₁ i) = i) ∧ (movedPoints h₁).card = 2 * (K - p₀) ∧
      (movedPoints (combineInv h₀ h₁)).card = 2 * K

open scoped Classical in
/-- The cover of the marked involutions: neutral pairs, other pairs, and the marking of
`p - p₀` of the other pairs. -/
noncomputable def markedCover (N K p p₀ : ℕ) :
    Finset ((Fin N ⊕ Fin N → Fin N ⊕ Fin N) × Finset (Fin N ⊕ Fin N)) :=
  (neutralCover N p₀).biUnion fun h₀ => (otherCover N K p₀ h₀).biUnion fun h₁ =>
    (pairClosures (minRep (finSumFinEquiv : Fin N ⊕ Fin N → Fin (N + N)) h₁) h₁ (p - p₀)).image
      fun T₁ => (combineInv h₀ h₁, movedPoints h₀ ∪ T₁)

theorem isLeft_eq_false_of_ne {i j : Fin N ⊕ Fin N} (h : i.isLeft ≠ j.isLeft)
    (hi : i.isLeft = true) : j.isLeft = false := by
  cases hj : j.isLeft
  · rfl
  · exact absurd (hi.trans hj.symm) h

theorem isLeft_eq_true_of_ne {i j : Fin N ⊕ Fin N} (h : i.isLeft ≠ j.isLeft)
    (hi : i.isLeft = false) : j.isLeft = true := by
  cases hj : j.isLeft
  · exact absurd (hi.trans hj.symm) h
  · rfl

/-- Every marked involution lies in the cover. -/
theorem mem_markedCover {K p p₀ : ℕ} {h : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    {T : Finset (Fin N ⊕ Fin N)} (hm : IsMarkedInvolution K p p₀ h T) :
    (h, T) ∈ markedCover N K p p₀ := by
  classical
  obtain ⟨hinv, hK, hTm, hcl, hp, hp₀⟩ := hm
  set T₀ : Finset (Fin N ⊕ Fin N) := T.filter fun i => i.isLeft ≠ (h i).isLeft with hT₀
  have hT₀T : T₀ ⊆ T := filter_subset _ _
  have hT₀m : T₀ ⊆ movedPoints h := hT₀T.trans hTm
  have hT₀cl : ∀ i ∈ T₀, h i ∈ T₀ := by
    intro i hi
    obtain ⟨hiT, hne⟩ := mem_filter.1 hi
    refine mem_filter.2 ⟨hcl i hiT, ?_⟩
    rw [hinv]
    exact hne.symm
  have hpp₀ : p₀ ≤ p := by
    have := card_le_card hT₀T
    omega
  have hpK : p ≤ K := by
    have := card_le_card hTm
    omega
  -- the neutral part
  set h₀ : Fin N ⊕ Fin N → Fin N ⊕ Fin N := fun i => if i ∈ T₀ then h i else i with hh₀
  have h₀_of_mem : ∀ i ∈ T₀, h₀ i = h i := fun i hi => by simp [hh₀, hi]
  have h₀_of_not : ∀ i, i ∉ T₀ → h₀ i = i := fun i hi => by simp [hh₀, hi]
  have hinv₀ : ∀ i, h₀ (h₀ i) = i := by
    intro i
    by_cases hi : i ∈ T₀
    · rw [h₀_of_mem i hi, h₀_of_mem _ (hT₀cl i hi), hinv]
    · rw [h₀_of_not i hi, h₀_of_not i hi]
  have hmoved₀ : movedPoints h₀ = T₀ := by
    ext i
    rw [mem_movedPoints]
    by_cases hi : i ∈ T₀
    · rw [h₀_of_mem i hi]
      simp only [hi, iff_true]
      exact mem_movedPoints.1 (hT₀m hi)
    · rw [h₀_of_not i hi]
      simp [hi]
  have hcard₀ : (movedPoints h₀).card = 2 * p₀ := by rw [hmoved₀]; exact hp₀
  set A₀ : Finset (Fin N ⊕ Fin N) := T₀.filter fun i => i.isLeft = true with hA₀
  have hA₀rep : IsRepSet h₀ A₀ := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [← mem_movedPoints, hmoved₀]
      exact (mem_filter.1 hi).1
    · intro i hi hhi
      obtain ⟨hiT₀, hil⟩ := mem_filter.1 hi
      obtain ⟨-, hhl⟩ := mem_filter.1 hhi
      rw [h₀_of_mem i hiT₀] at hhl
      have := isLeft_eq_false_of_ne (mem_filter.1 hiT₀).2 hil
      rw [this] at hhl
      exact absurd hhl (by simp)
    · intro i hne
      rw [← mem_movedPoints, hmoved₀] at hne
      by_cases hil : i.isLeft = true
      · exact Or.inl (mem_filter.2 ⟨hne, hil⟩)
      · right
        have hil' : i.isLeft = false := by simpa using hil
        have := isLeft_eq_true_of_ne (mem_filter.1 hne).2 hil'
        rw [h₀_of_mem i hne]
        exact mem_filter.2 ⟨hT₀cl i hne, this⟩
  have hA₀card : A₀.card = p₀ := by
    have := hA₀rep.card_movedPoints hinv₀
    omega
  have hh₀mem : h₀ ∈ neutralCover N p₀ := by
    refine mem_filter.2 ⟨?_, hinv₀, hcard₀⟩
    refine mem_involutionCover_of_isRepSet hinv₀ hA₀rep ?_ hA₀card ?_
    · intro i hi
      exact mem_posVerts.2 (mem_filter.1 hi).2
    · intro i hi
      obtain ⟨hiT₀, hil⟩ := mem_filter.1 hi
      rw [h₀_of_mem i hiT₀]
      exact mem_negVerts.2 (isLeft_eq_false_of_ne (mem_filter.1 hiT₀).2 hil)
  -- the other pairs
  set h₁ : Fin N ⊕ Fin N → Fin N ⊕ Fin N := fun i =>
    if i ∈ movedPoints h \ T₀ then h i else i with hh₁
  have h₁_of_mem : ∀ i ∈ movedPoints h \ T₀, h₁ i = h i := fun i hi => by
    simp only [hh₁, hi, ↓reduceIte]
  have h₁_of_not : ∀ i, i ∉ movedPoints h \ T₀ → h₁ i = i := fun i hi => by
    simp only [hh₁, hi, ↓reduceIte]
  have hcl₁ : ∀ i ∈ movedPoints h \ T₀, h i ∈ movedPoints h \ T₀ := by
    intro i hi
    obtain ⟨him, hiT₀⟩ := mem_sdiff.1 hi
    refine mem_sdiff.2 ⟨?_, fun hh => hiT₀ ?_⟩
    · rw [mem_movedPoints] at him ⊢
      rw [hinv]
      exact him.symm
    · have := hT₀cl _ hh
      rwa [hinv] at this
  have hinv₁ : ∀ i, h₁ (h₁ i) = i := by
    intro i
    by_cases hi : i ∈ movedPoints h \ T₀
    · rw [h₁_of_mem i hi, h₁_of_mem _ (hcl₁ i hi), hinv]
    · rw [h₁_of_not i hi, h₁_of_not i hi]
  have hmoved₁ : movedPoints h₁ = movedPoints h \ T₀ := by
    ext i
    rw [mem_movedPoints]
    by_cases hi : i ∈ movedPoints h \ T₀
    · rw [h₁_of_mem i hi]
      simp only [hi, iff_true]
      exact mem_movedPoints.1 (mem_sdiff.1 hi).1
    · rw [h₁_of_not i hi]
      simp [hi]
  have hcard₁ : (movedPoints h₁).card = 2 * (K - p₀) := by
    rw [hmoved₁, card_sdiff_of_subset hT₀m]
    omega
  have hcomb : combineInv h₀ h₁ = h := by
    funext i
    unfold combineInv
    by_cases hi : i ∈ T₀
    · have hne : h₀ i ≠ i := by
        rw [h₀_of_mem i hi]
        exact mem_movedPoints.1 (hT₀m hi)
      simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
      exact h₀_of_mem i hi
    · have hne : ¬ (h₀ i ≠ i) := by
        rw [h₀_of_not i hi]
        exact fun h' => h' rfl
      simp only [hne, ↓reduceIte]
      by_cases him : i ∈ movedPoints h
      · exact h₁_of_mem i (mem_sdiff.2 ⟨him, hi⟩)
      · rw [h₁_of_not i (fun h' => him (mem_sdiff.1 h').1)]
        exact (not_not.1 (mem_movedPoints.not.1 him)).symm
  have hA₁rep := isRepSet_minRep (finSumFinEquiv (m := N) (n := N)).injective hinv₁
  have hA₁card : (minRep (finSumFinEquiv : Fin N ⊕ Fin N → Fin (N + N)) h₁).card = K - p₀ := by
    have := hA₁rep.card_movedPoints hinv₁
    omega
  have hh₁mem : h₁ ∈ otherCover N K p₀ h₀ := by
    refine mem_filter.2 ⟨?_, hinv₁, hcard₁, by rw [hcomb]; exact hK⟩
    refine mem_involutionCover_of_isRepSet hinv₁ hA₁rep ?_ hA₁card ?_
    · intro i hi
      have := hA₁rep.subset_movedPoints hi
      rw [hmoved₁] at this
      rw [hmoved₀]
      exact mem_sdiff.2 ⟨mem_univ _, (mem_sdiff.1 this).2⟩
    · intro i hi
      have him : h₁ i ∈ movedPoints h₁ := by
        rw [mem_movedPoints, hinv₁]
        exact (mem_movedPoints.1 (hA₁rep.subset_movedPoints hi)).symm
      rw [hmoved₁] at him
      rw [hmoved₀]
      exact mem_sdiff.2 ⟨mem_sdiff.2 ⟨mem_univ _, (mem_sdiff.1 him).2⟩, hA₁rep.2.1 i hi⟩
  -- the marking
  have hT₁sub : T \ T₀ ⊆ movedPoints h₁ := by
    intro i hi
    rw [hmoved₁]
    exact mem_sdiff.2 ⟨hTm (mem_sdiff.1 hi).1, (mem_sdiff.1 hi).2⟩
  have hT₁cl : ∀ i ∈ T \ T₀, h₁ i ∈ T \ T₀ := by
    intro i hi
    obtain ⟨hiT, hiT₀⟩ := mem_sdiff.1 hi
    rw [h₁_of_mem i (mem_sdiff.2 ⟨hTm hiT, hiT₀⟩)]
    refine mem_sdiff.2 ⟨hcl i hiT, fun hh => hiT₀ ?_⟩
    have := hT₀cl _ hh
    rwa [hinv] at this
  have hT₁card : (T \ T₀).card = 2 * (p - p₀) := by
    rw [card_sdiff_of_subset hT₀T]
    omega
  have hT₁mem := hA₁rep.mem_pairClosures hinv₁ hT₁sub hT₁cl hT₁card
  refine mem_biUnion.2 ⟨h₀, hh₀mem, mem_biUnion.2 ⟨h₁, hh₁mem, mem_image.2 ⟨T \ T₀, hT₁mem, ?_⟩⟩⟩
  refine Prod.ext hcomb ?_
  show movedPoints h₀ ∪ (T \ T₀) = T
  rw [hmoved₀]
  exact union_sdiff_of_subset hT₀T

end Cover

/-! ### Counting -/

section Counting

variable {N : ℕ}

theorem card_moved_of_mem_markedCover {K p p₀ : ℕ}
    {γ : (Fin N ⊕ Fin N → Fin N ⊕ Fin N) × Finset (Fin N ⊕ Fin N)}
    (hγ : γ ∈ markedCover N K p p₀) : (movedPoints γ.1).card = 2 * K := by
  unfold markedCover at hγ
  obtain ⟨h₀, -, h1⟩ := mem_biUnion.1 hγ
  obtain ⟨h₁, hh₁, h2⟩ := mem_biUnion.1 h1
  obtain ⟨T₁, -, rfl⟩ := mem_image.1 h2
  exact (mem_filter.1 hh₁).2.2.2

/-- The size of the cover: the count of Step 1 (source l. 1464--1481), before the application of
Stirling's formula. -/
theorem card_markedCover_le {K p p₀ : ℕ} :
    (markedCover N K p p₀).card ≤ N.choose p₀ * N.descFactorial p₀ *
      ((2 * N - 2 * p₀).choose (K - p₀) *
        (2 * N - 2 * p₀ - (K - p₀)).descFactorial (K - p₀)) * (K - p₀).choose (p - p₀) := by
  classical
  have hB₀ : (neutralCover N p₀).card ≤ N.choose p₀ * N.descFactorial p₀ := by
    refine (card_le_card (filter_subset _ _)).trans ?_
    have := card_involutionCover_le (posVerts N) (fun _ => negVerts N) p₀ N
      (fun A _ _ => card_negVerts N)
    rwa [card_posVerts] at this
  have hB₁ : ∀ h₀ ∈ neutralCover N p₀, (otherCover N K p₀ h₀).card ≤
      (2 * N - 2 * p₀).choose (K - p₀) *
        (2 * N - 2 * p₀ - (K - p₀)).descFactorial (K - p₀) := by
    intro h₀ hh₀
    have hcard₀ : (movedPoints h₀).card = 2 * p₀ := (mem_filter.1 hh₀).2.2
    have hS : ((univ : Finset (Fin N ⊕ Fin N)) \ movedPoints h₀).card = 2 * N - 2 * p₀ := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, hcard₀]
      simp [two_mul]
    refine (card_le_card (filter_subset _ _)).trans ?_
    have := card_involutionCover_le ((univ : Finset (Fin N ⊕ Fin N)) \ movedPoints h₀)
      (fun A => ((univ : Finset (Fin N ⊕ Fin N)) \ movedPoints h₀) \ A) (K - p₀)
      (2 * N - 2 * p₀ - (K - p₀)) (fun A hA hAk => by
        rw [card_sdiff_of_subset hA, hS, hAk])
    rwa [hS] at this
  have hc₂ : ∀ h₀ ∈ neutralCover N p₀, ∀ h₁ ∈ otherCover N K p₀ h₀,
      ((pairClosures (minRep (finSumFinEquiv : Fin N ⊕ Fin N → Fin (N + N)) h₁) h₁
        (p - p₀)).image fun T₁ => (combineInv h₀ h₁, movedPoints h₀ ∪ T₁)).card ≤
        (K - p₀).choose (p - p₀) := by
    intro h₀ _ h₁ hh₁
    obtain ⟨-, hinv₁, hcard₁, -⟩ := mem_filter.1 hh₁
    have hrep := isRepSet_minRep (finSumFinEquiv (m := N) (n := N)).injective hinv₁
    have hA : (minRep (finSumFinEquiv : Fin N ⊕ Fin N → Fin (N + N)) h₁).card = K - p₀ := by
      have := hrep.card_movedPoints hinv₁
      omega
    refine card_image_le.trans ?_
    have := card_pairClosures_le (minRep (finSumFinEquiv : Fin N ⊕ Fin N → Fin (N + N)) h₁) h₁
      (p - p₀)
    rwa [hA] at this
  unfold markedCover
  calc _ ≤ ∑ h₀ ∈ neutralCover N p₀, ((otherCover N K p₀ h₀).biUnion fun h₁ =>
        (pairClosures (minRep (finSumFinEquiv : Fin N ⊕ Fin N → Fin (N + N)) h₁) h₁
          (p - p₀)).image fun T₁ => (combineInv h₀ h₁, movedPoints h₀ ∪ T₁)).card :=
        card_biUnion_le
    _ ≤ ∑ h₀ ∈ neutralCover N p₀, ((2 * N - 2 * p₀).choose (K - p₀) *
        (2 * N - 2 * p₀ - (K - p₀)).descFactorial (K - p₀)) * (K - p₀).choose (p - p₀) := by
        refine sum_le_sum fun h₀ hh₀ => card_biUnion_le.trans ?_
        calc _ ≤ ∑ h₁ ∈ otherCover N K p₀ h₀, (K - p₀).choose (p - p₀) :=
              sum_le_sum fun h₁ hh₁ => hc₂ h₀ hh₀ h₁ hh₁
          _ = (otherCover N K p₀ h₀).card * (K - p₀).choose (p - p₀) := by
              rw [sum_const]; rfl
          _ ≤ _ := Nat.mul_le_mul_right _ (hB₁ h₀ hh₀)
    _ = (neutralCover N p₀).card * (((2 * N - 2 * p₀).choose (K - p₀) *
        (2 * N - 2 * p₀ - (K - p₀)).descFactorial (K - p₀)) * (K - p₀).choose (p - p₀)) := by
        rw [sum_const]; rfl
    _ ≤ _ := (Nat.mul_le_mul_right _ hB₀).trans_eq (mul_assoc _ _ _).symm

/-- The map `f` is determined by `h` on the vertices moved by `h`. -/
theorem card_piFinset_unmoved (h : Fin N ⊕ Fin N → Fin N ⊕ Fin N) :
    (Fintype.piFinset fun i => if h i ≠ i then ({h i} : Finset (Fin N ⊕ Fin N)) else univ).card =
      (2 * N) ^ (2 * N - (movedPoints h).card) := by
  rw [Fintype.card_piFinset]
  have h1 : ∀ i : Fin N ⊕ Fin N, (if h i ≠ i then ({h i} : Finset (Fin N ⊕ Fin N)) else univ).card =
      if h i ≠ i then 1 else 2 * N := by
    intro i
    by_cases hi : h i ≠ i
    · simp [hi]
    · simp [hi, two_mul]
  simp_rw [h1]
  rw [prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  have h2 := card_filter_add_card_filter_not (s := (univ : Finset (Fin N ⊕ Fin N)))
    (fun i => h i ≠ i)
  have h3 : (univ.filter fun i : Fin N ⊕ Fin N => h i ≠ i) = movedPoints h := rfl
  rw [h3, card_univ] at h2
  have h4 : Fintype.card (Fin N ⊕ Fin N) = 2 * N := by simp [two_mul]
  omega

theorem markedGraphs_subset (hN : 2 ≤ N) (K p p₀ : ℕ) :
    markedGraphs hN K p p₀ ⊆ (markedCover N K p p₀).biUnion fun γ =>
      (Fintype.piFinset fun i => if γ.1 i ≠ i then ({γ.1 i} : Finset (Fin N ⊕ Fin N)) else univ)
        ×ˢ {γ.2} := by
  intro γ hγ
  obtain ⟨Z, -, -, hf, hT, hK, hp, hp₀⟩ := mem_markedGraphs.1 hγ
  have hm := isMarkedInvolution_cycleInvolution hN Z
  rw [hK, hp, hp₀, hT] at hm
  refine mem_biUnion.2 ⟨(cycleInvolution Z, γ.2), mem_markedCover hm, ?_⟩
  refine mem_product.2 ⟨?_, mem_singleton_self _⟩
  rw [Fintype.mem_piFinset]
  intro i
  by_cases hi : i ∈ cycleVerts Z
  · have hne : cycleInvolution Z i ≠ i := by
      rw [cycleInvolution_of_mem_cycleVerts hi]
      exact nearestNeighbor_ne Z i
    simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte, mem_singleton]
    rw [cycleInvolution_of_mem_cycleVerts hi, ← hf]
  · have : ¬ (cycleInvolution Z i ≠ i) := by
      rw [cycleInvolution_of_not_mem_cycleVerts hi]
      exact fun h' => h' rfl
    simp only [this, ↓reduceIte, mem_univ]

/-- **The graph count of Step 1** (source l. 1462--1488), before Stirling's formula:
`|D_{2N,K,p,p₀}| ≤ C(N,p₀) (N)_{p₀} · C(2N-2p₀, K-p₀) (2N-p₀-K)_{K-p₀} · C(K-p₀, p-p₀) ·
(2N)^{2N-2K}` (falling factorials `(n)_k`). -/
theorem card_markedGraphs_le (hN : 2 ≤ N) {K p p₀ : ℕ} :
    (markedGraphs hN K p p₀).card ≤ N.choose p₀ * N.descFactorial p₀ *
      ((2 * N - 2 * p₀).choose (K - p₀) *
        (2 * N - 2 * p₀ - (K - p₀)).descFactorial (K - p₀)) * (K - p₀).choose (p - p₀) *
      (2 * N) ^ (2 * N - 2 * K) := by
  refine (card_le_card (markedGraphs_subset hN K p p₀)).trans (card_biUnion_le.trans ?_)
  have hfib : ∀ γ ∈ markedCover N K p p₀,
      ((Fintype.piFinset fun i => if γ.1 i ≠ i then ({γ.1 i} : Finset (Fin N ⊕ Fin N)) else univ)
        ×ˢ ({γ.2} : Finset (Finset (Fin N ⊕ Fin N)))).card = (2 * N) ^ (2 * N - 2 * K) := by
    intro γ hγ
    rw [card_product, card_singleton, mul_one, card_piFinset_unmoved,
      card_moved_of_mem_markedCover hγ]
  rw [sum_congr rfl hfib, sum_const]
  exact Nat.mul_le_mul_right _ card_markedCover_le

end Counting

end TwoComponentCoulomb

end
