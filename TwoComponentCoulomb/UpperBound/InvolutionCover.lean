/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Covering involutions by embeddings of representatives

Counting device for the enumeration of nearest-neighbour graphs in Step 1 of the proof of
Proposition 3.9 (source l. 1370–1396). A *partial involution* of a finite
type `α` is a map `h : α → α` with `h (h i) = i`; its *moved points* are the `i` with `h i ≠ i`,
which are grouped into 2-cycles `{i, h i}`. A set `A` of *representatives* contains exactly one
vertex of every 2-cycle (`IsRepSet`). The involution `h` is then determined by the embedding
`a ↦ h a` of `A` into any set `Y` containing `h '' A`.

## Main definitions and results

* `TwoComponentCoulomb.movedPoints h`, `TwoComponentCoulomb.IsRepSet h A`.
* `TwoComponentCoulomb.minRep κ h`, `TwoComponentCoulomb.isRepSet_minRep`: with an injective key
  `κ`, the 2-cycle vertices with `κ i < κ (h i)` form a set of representatives.
* `TwoComponentCoulomb.IsRepSet.card_eq_two_mul`: a `h`-closed subset `T` of the moved points is
  the union of `T ∩ A` and its image under `h`, so `|T| = 2 |T ∩ A|`.
* `TwoComponentCoulomb.involutionCover X Y k`: the involutions obtained from `k`-subsets `A ⊆ X` and
  embeddings `A ↪ Y A`. Its cardinality is at most `C(|X|, k) · descFactorial c k` when all `Y A`
  (`A ⊆ X`, `|A| = k`) have `c` elements (`card_involutionCover_le`).
* `TwoComponentCoulomb.mem_involutionCover_of_isRepSet`: every involution with a set of
  representatives of the right size and right range lies in the cover.
* `TwoComponentCoulomb.pairClosures A h m`: the `h`-closed unions of `m` pairs `{a, h a}`, `a ∈ A`.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

section Involutions

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The points moved by `h`. -/
def movedPoints (h : α → α) : Finset α := univ.filter fun i => h i ≠ i

theorem mem_movedPoints {h : α → α} {i : α} : i ∈ movedPoints h ↔ h i ≠ i := by
  simp [movedPoints]

/-- `A` contains exactly one vertex of every 2-cycle `{i, h i}` of `h` (for an involution `h`):
its elements are moved, `h` maps `A` outside `A`, and every moved point is in `A` or is the image of
a point of `A`. -/
def IsRepSet (h : α → α) (A : Finset α) : Prop :=
  (∀ i ∈ A, h i ≠ i) ∧ (∀ i ∈ A, h i ∉ A) ∧ ∀ i, h i ≠ i → i ∈ A ∨ h i ∈ A

variable {h : α → α}

theorem IsRepSet.subset_movedPoints {A : Finset α} (hA : IsRepSet h A) : A ⊆ movedPoints h :=
  fun _ hi => mem_movedPoints.2 (hA.1 _ hi)

/-- The canonical set of representatives of a map `h` with respect to a key `κ`: the moved points
`i` with `κ i < κ (h i)`. -/
def minRep {β : Type*} [LinearOrder β] (κ : α → β) (h : α → α) : Finset α :=
  (movedPoints h).filter fun i => κ i < κ (h i)

/-- With an injective key `κ`, the moved points `i` with `κ i < κ (h i)` form a set of
representatives of an involution `h`. -/
theorem isRepSet_minRep {β : Type*} [LinearOrder β] {κ : α → β} (hκ : Function.Injective κ)
    (hinv : ∀ i, h (h i) = i) : IsRepSet h (minRep κ h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact mem_movedPoints.1 (mem_filter.1 hi).1
  · intro i hi hhi
    obtain ⟨-, hi2⟩ := mem_filter.1 hi
    obtain ⟨-, hh2⟩ := mem_filter.1 hhi
    rw [hinv] at hh2
    exact lt_asymm hi2 hh2
  · intro i hne
    rcases lt_trichotomy (κ i) (κ (h i)) with hlt | heq | hgt
    · exact Or.inl (mem_filter.2 ⟨mem_movedPoints.2 hne, hlt⟩)
    · exact absurd (hκ heq) (Ne.symm hne)
    · refine Or.inr (mem_filter.2 ⟨mem_movedPoints.2 ?_, ?_⟩)
      · rw [hinv]
        exact hne.symm
      · rw [hinv]
        exact hgt

/-- A `h`-closed set `T` of moved points is the union of `T ∩ A` and its image under `h`, where `A`
is a set of representatives; these two sets are disjoint and have the same cardinality. -/
theorem IsRepSet.eq_union_image (hinv : ∀ i, h (h i) = i) {A : Finset α} (hA : IsRepSet h A)
    {T : Finset α} (hT : T ⊆ movedPoints h) (hcl : ∀ i ∈ T, h i ∈ T) :
    T = (T ∩ A) ∪ (T ∩ A).image h := by
  ext i
  simp only [mem_union, mem_inter, mem_image]
  constructor
  · intro hiT
    by_cases hiA : i ∈ A
    · exact Or.inl ⟨hiT, hiA⟩
    · rcases hA.2.2 i (mem_movedPoints.1 (hT hiT)) with h1 | h1
      · exact absurd h1 hiA
      · exact Or.inr ⟨h i, ⟨hcl i hiT, h1⟩, hinv i⟩
  · rintro (⟨hiT, -⟩ | ⟨a, ⟨haT, -⟩, rfl⟩)
    · exact hiT
    · exact hcl a haT

theorem IsRepSet.card_eq_two_mul (hinv : ∀ i, h (h i) = i) {A : Finset α} (hA : IsRepSet h A)
    {T : Finset α} (hT : T ⊆ movedPoints h) (hcl : ∀ i ∈ T, h i ∈ T) :
    T.card = 2 * (T ∩ A).card := by
  have hinj : Function.Injective h := Function.Involutive.injective hinv
  have hdisj : Disjoint (T ∩ A) ((T ∩ A).image h) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hx'
    exact hA.2.1 a (mem_inter.1 ha).2 (mem_inter.1 hx).2
  conv_lhs => rw [hA.eq_union_image hinv hT hcl]
  rw [card_union_of_disjoint hdisj, card_image_of_injective _ hinj]
  omega

theorem IsRepSet.card_movedPoints (hinv : ∀ i, h (h i) = i) {A : Finset α} (hA : IsRepSet h A) :
    (movedPoints h).card = 2 * A.card := by
  have hcl : ∀ i ∈ movedPoints h, h i ∈ movedPoints h := fun i hi => by
    rw [mem_movedPoints] at hi ⊢
    rw [hinv]
    exact hi.symm
  have := hA.card_eq_two_mul hinv (subset_refl _) hcl
  rwa [inter_eq_right.2 hA.subset_movedPoints] at this

/-! ### The cover -/

/-- The involution determined by an embedding `e` of the representatives `A` into `Y`: it sends
`i ∈ A` to `e i`, the point `e a` to `a`, and fixes the other points. -/
noncomputable def involutionOfEmb (A Y : Finset α) (e : A ↪ Y) (i : α) : α :=
  if hi : i ∈ A then ((e ⟨i, hi⟩ : Y) : α)
  else if hex : ∃ a : A, ((e a : Y) : α) = i then ((Classical.choose hex : A) : α) else i

/-- The involutions obtained from `k`-element subsets `A ⊆ X` and embeddings `A ↪ Y A`. -/
noncomputable def involutionCover (X : Finset α) (Y : Finset α → Finset α) (k : ℕ) :
    Finset (α → α) :=
  (X.powersetCard k).biUnion fun A =>
    (univ : Finset (A ↪ Y A)).image (involutionOfEmb A (Y A))

/-- Cardinality of the cover: `C(|X|, k) · descFactorial c k` if all `Y A` have `c` elements. -/
theorem card_involutionCover_le (X : Finset α) (Y : Finset α → Finset α) (k c : ℕ)
    (hY : ∀ A ⊆ X, A.card = k → (Y A).card = c) :
    (involutionCover X Y k).card ≤ X.card.choose k * c.descFactorial k := by
  unfold involutionCover
  refine card_biUnion_le.trans ?_
  have hterm : ∀ A ∈ X.powersetCard k,
      ((univ : Finset (A ↪ Y A)).image (involutionOfEmb A (Y A))).card ≤ c.descFactorial k := by
    intro A hA
    rw [mem_powersetCard] at hA
    refine card_image_le.trans ?_
    rw [card_univ, Fintype.card_embedding_eq]
    simp [Fintype.card_coe, hA.2, hY A hA.1 hA.2]
  calc _ ≤ ∑ A ∈ X.powersetCard k, c.descFactorial k := sum_le_sum hterm
    _ = _ := by rw [sum_const, card_powersetCard]; rfl

/-- Every involution with a set of representatives `A ⊆ X` of size `k` and `h '' A ⊆ Y A` lies in
the cover `involutionCover X Y k`. -/
theorem mem_involutionCover_of_isRepSet {X : Finset α} {Y : Finset α → Finset α} {k : ℕ}
    (hinv : ∀ i, h (h i) = i) {A : Finset α} (hA : IsRepSet h A) (hAX : A ⊆ X)
    (hAk : A.card = k) (hY : ∀ i ∈ A, h i ∈ Y A) : h ∈ involutionCover X Y k := by
  obtain ⟨e, he⟩ : ∃ e : A ↪ Y A, ∀ a, ((e a : Y A) : α) = h a := by
    refine ⟨⟨fun a => ⟨h a, hY a a.2⟩, ?_⟩, fun a => rfl⟩
    intro a b hab
    have h1 : h a = h b := congrArg Subtype.val hab
    exact Subtype.ext (by rw [← hinv a, ← hinv b, h1])
  refine mem_biUnion.2 ⟨A, mem_powersetCard.2 ⟨hAX, hAk⟩, mem_image.2 ⟨e, mem_univ _, ?_⟩⟩
  funext i
  unfold involutionOfEmb
  split_ifs with hi hex
  · exact he ⟨i, hi⟩
  · have hc := Classical.choose_spec hex
    rw [he] at hc
    have h2 := hinv ((Classical.choose hex : A) : α)
    rw [hc] at h2
    exact h2.symm
  · by_contra hne
    have hne' : h i ≠ i := fun h' => hne h'.symm
    rcases hA.2.2 i hne' with h1 | h1
    · exact hi h1
    · exact hex ⟨⟨h i, h1⟩, by rw [he]; exact hinv i⟩

/-! ### Closed unions of pairs -/

/-- The `h`-closed unions of `m` pairs `{a, h a}` with `a ∈ A`. -/
def pairClosures (A : Finset α) (h : α → α) (m : ℕ) : Finset (Finset α) :=
  (A.powersetCard m).image fun B => B ∪ B.image h

omit [Fintype α] in
theorem card_pairClosures_le (A : Finset α) (h : α → α) (m : ℕ) :
    (pairClosures A h m).card ≤ A.card.choose m :=
  card_image_le.trans (card_powersetCard m A).le

/-- A `h`-closed set `T` of `2 m` moved points lies in `pairClosures A h m` for every set `A` of
representatives. -/
theorem IsRepSet.mem_pairClosures (hinv : ∀ i, h (h i) = i) {A : Finset α} (hA : IsRepSet h A)
    {T : Finset α} (hT : T ⊆ movedPoints h) (hcl : ∀ i ∈ T, h i ∈ T) {m : ℕ}
    (hm : T.card = 2 * m) : T ∈ pairClosures A h m := by
  refine mem_image.2 ⟨T ∩ A, mem_powersetCard.2 ⟨inter_subset_right, ?_⟩, ?_⟩
  · have := hA.card_eq_two_mul hinv hT hcl
    omega
  · exact (hA.eq_union_image hinv hT hcl).symm

end Involutions

end TwoComponentCoulomb

end
