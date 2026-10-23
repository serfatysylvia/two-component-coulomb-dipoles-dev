/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact enumeration of ordered disjoint unordered pairs

The paper, `prop:auxk`, lines 1005–1025, chooses an ordered collection
of disjoint unordered pairs. An ordering of each pair gives an embedding of `2m`
vertices. Forgetting these orientations divides the count by `2^m`.
-/

@[expose] public section

namespace TwoComponentCoulomb.PairEnumeration

/-- Flip the endpoints independently in each pair. -/
def flip {m : ℕ} (s : Fin m → Bool) : (Fin m × Bool) ≃ (Fin m × Bool) where
  toFun v := (v.1, Bool.xor v.2 (s v.1))
  invFun v := (v.1, Bool.xor v.2 (s v.1))
  left_inv := by rintro ⟨i, b⟩; simp
  right_inv := by rintro ⟨i, b⟩; simp

/-- An ordered collection of disjoint unordered pairs, represented with the smaller
endpoint first. The embedding enforces disjointness on all endpoints. -/
def OrderedPairs (k m : ℕ) :=
  {f : (Fin m × Bool) ↪ Fin k // ∀ i, f (i, false) < f (i, true)}

noncomputable instance (k m : ℕ) : Fintype (OrderedPairs k m) := inferInstanceAs
  (Fintype {f : (Fin m × Bool) ↪ Fin k // ∀ i, f (i, false) < f (i, true)})

/-- Orient each pair according to a mask. -/
def orient {k m : ℕ} (f : (Fin m × Bool) ↪ Fin k) (s : Fin m → Bool) :
    (Fin m × Bool) ↪ Fin k := (flip s).toEmbedding.trans f

/-- The mask which puts the smaller endpoint first. -/
def mask {k m : ℕ} (f : (Fin m × Bool) ↪ Fin k) (i : Fin m) : Bool :=
  decide (f (i, true) < f (i, false))

/-- Sorting each pair gives an ordered collection of unordered pairs. -/
def sorted {k m : ℕ} (f : (Fin m × Bool) ↪ Fin k) : OrderedPairs k m :=
  ⟨orient f (mask f), by
    intro i
    have hne : f (i, false) ≠ f (i, true) := fun h => Bool.false_ne_true
      (congrArg Prod.snd (f.injective h))
    by_cases h : f (i, true) < f (i, false)
    · simp [orient, flip, mask, h]
    · simpa [orient, flip, mask, h] using lt_of_le_of_ne (not_lt.1 h) hne⟩

/-- Reversing the same orientations twice recovers the embedding. -/
theorem orient_orient {k m : ℕ} (f : (Fin m × Bool) ↪ Fin k) (s : Fin m → Bool) :
    orient (orient f s) s = f := by
  ext ⟨i, b⟩
  cases b <;> cases h : s i <;> simp [orient, flip, h]

/-- The sorting mask of an oriented, sorted collection is its orientation mask. -/
theorem mask_orient {k m : ℕ} (f : OrderedPairs k m) (s : Fin m → Bool) :
    mask (orient f.val s) = s := by
  funext i
  have hi := f.property i
  cases h : s i
  · simp [mask, orient, flip, h, not_lt.2 hi.le]
  · simp [mask, orient, flip, h, hi]

/-- Each unordered pair has exactly two orientations, independently of the other pairs. -/
def orientationEquiv (k m : ℕ) :
    ((Fin m × Bool) ↪ Fin k) ≃ OrderedPairs k m × (Fin m → Bool) where
  toFun f := (sorted f, mask f)
  invFun v := orient v.1.val v.2
  left_inv f := orient_orient f (mask f)
  right_inv := by
    rintro ⟨f, s⟩
    have hm := mask_orient f s
    apply Prod.ext
    · apply Subtype.ext
      change orient (orient f.val s) (mask (orient f.val s)) = f.val
      rw [hm, orient_orient]
    · exact hm

/-- The exact ordered disjoint-pair count, in multiplied form:
`number · 2^m = k! / (k - 2m)!`. This includes the empty collection. -/
theorem card_orderedPairs (k m : ℕ) :
    Fintype.card (OrderedPairs k m) * 2 ^ m = k.descFactorial (2 * m) := by
  have h := Fintype.card_congr (orientationEquiv k m)
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, Nat.mul_comm m 2] at h
  exact h.symm

/-- The endpoint map of an unordered pair. -/
def endpoint {k : ℕ} (e : Fin k × Fin k) (b : Bool) : Fin k :=
  if b then e.2 else e.1

/-- An unordered collection of disjoint unordered pairs. -/
def PairSets (k m : ℕ) := {M : Finset (Fin k × Fin k) // M.card = m ∧
  (∀ e ∈ M, e.1 < e.2) ∧ Function.Injective
    (fun v : M × Bool => endpoint v.1.val v.2)}

noncomputable instance (k m : ℕ) : Fintype (PairSets k m) := by
  classical
  exact inferInstanceAs (Fintype {M : Finset (Fin k × Fin k) // M.card = m ∧
    (∀ e ∈ M, e.1 < e.2) ∧ Function.Injective
      (fun v : M × Bool => endpoint v.1.val v.2)})

/-- Forget the ordering of the pairs. -/
def pairsImage {k m : ℕ} (f : OrderedPairs k m) : Finset (Fin k × Fin k) :=
  Finset.univ.image fun i => (f.val (i, false), f.val (i, true))

/-- Distinct pairs of an ordered collection are distinct. -/
theorem pair_injective {k m : ℕ} (f : OrderedPairs k m) :
    Function.Injective (fun i => (f.val (i, false), f.val (i, true))) := by
  intro i j h
  exact congrArg Prod.fst (f.val.injective (congrArg Prod.fst h))

/-- The image of an ordered collection is a disjoint pair set of the same size. -/
def toPairSet {k m : ℕ} (f : OrderedPairs k m) : PairSets k m :=
  ⟨pairsImage f, by
    refine ⟨?_, ?_, ?_⟩
    · rw [pairsImage, Finset.card_image_of_injective _ (pair_injective f),
        Finset.card_univ, Fintype.card_fin]
    · intro e he
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 he
      exact f.property i
    · rintro ⟨⟨e, he⟩, b⟩ ⟨⟨e', he'⟩, b'⟩ h
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 he'
      have h' : f.val (i, b) = f.val (j, b') := by
        cases b <;> cases b' <;> exact h
      have hij := f.val.injective h'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
      rfl⟩

/-- Enumerate the pair set in the order induced by `Fin k × Fin k ≃ Fin (k * k)`.
This fixes the enumeration used to count the possible component orders. -/
noncomputable def enumerate {k m : ℕ} (M : PairSets k m) : Fin m ≃ M.val := by
  letI : LinearOrder (Fin k × Fin k) :=
    LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
  exact (M.val.orderIsoOfFin M.property.1).toEquiv

/-- Order a pair set by a permutation of its enumeration. -/
noncomputable def fromPairSet {k m : ℕ} (M : PairSets k m) (σ : Equiv.Perm (Fin m)) :
    OrderedPairs k m :=
  ⟨⟨fun v => endpoint (enumerate M (σ v.1)).val v.2, by
    intro v w h
    have he : (enumerate M (σ v.1), v.2) = (enumerate M (σ w.1), w.2) :=
      M.property.2.2 h
    exact Prod.ext (σ.injective ((enumerate M).injective (congrArg Prod.fst he)))
      (congrArg (fun z : M.val × Bool => z.2) he)⟩,
    fun i => by simpa [endpoint] using M.property.2.1 _ (enumerate M (σ i)).property⟩

/-- Ordering a pair set leaves its underlying set unchanged. -/
theorem pairsImage_fromPairSet {k m : ℕ} (M : PairSets k m) (σ : Equiv.Perm (Fin m)) :
    pairsImage (fromPairSet M σ) = M.val := by
  ext e
  constructor
  · intro he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 he
    simp [fromPairSet, endpoint]
  · intro he
    obtain ⟨i, hi⟩ := (enumerate M).surjective ⟨e, he⟩
    refine Finset.mem_image.2 ⟨σ.symm i, Finset.mem_univ _, ?_⟩
    simp [fromPairSet, endpoint, hi]

/-- Permuting the list of components is the only redundancy in an ordered collection. -/
theorem fromPairSet_bijective (k m : ℕ) : Function.Bijective
    (fun v : PairSets k m × Equiv.Perm (Fin m) => fromPairSet v.1 v.2) := by
  constructor
  · rintro ⟨M, σ⟩ ⟨M', τ⟩ h
    have hM : M = M' := by
      apply Subtype.ext
      simpa only [pairsImage_fromPairSet] using congrArg pairsImage h
    subst M'
    suffices hστ : σ = τ by rw [hστ]
    apply Equiv.ext
    intro i
    have h₁ := congrArg (fun f : OrderedPairs k m => f.val (i, false)) h
    have h₂ := congrArg (fun f : OrderedPairs k m => f.val (i, true)) h
    apply (enumerate M).injective
    apply Subtype.ext
    exact Prod.ext (by simpa [fromPairSet, endpoint] using h₁)
      (by simpa [fromPairSet, endpoint] using h₂)
  · intro f
    let M := toPairSet f
    let e : Fin m ≃ M.val := Equiv.ofBijective
      (fun i => ⟨(f.val (i, false), f.val (i, true)), Finset.mem_image.2
        ⟨i, Finset.mem_univ _, rfl⟩⟩)
      ⟨fun i j h => pair_injective f (congrArg Subtype.val h), by
        rintro ⟨x, hx⟩
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
        exact ⟨i, rfl⟩⟩
    refine ⟨(M, e.trans (enumerate M).symm), ?_⟩
    apply Subtype.ext
    apply Function.Embedding.ext
    rintro ⟨i, b⟩
    change endpoint (enumerate M ((e.trans (enumerate M).symm) i)).val b = f.val (i, b)
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    cases b <;> rfl

/-- Dividing by `m!` forgets the order of the cycle components. -/
theorem card_pairSets_mul_factorial (k m : ℕ) :
    Fintype.card (PairSets k m) * m.factorial = Fintype.card (OrderedPairs k m) := by
  have h := Fintype.card_congr (Equiv.ofBijective _ (fromPairSet_bijective k m))
  simpa only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin] using h

/-- Exact disjoint-pair enumeration with both component orders and endpoint
orientations removed: `number · m! · 2^m = k! / (k - 2m)!`. -/
theorem card_pairSets (k m : ℕ) :
    Fintype.card (PairSets k m) * m.factorial * 2 ^ m = k.descFactorial (2 * m) := by
  rw [card_pairSets_mul_factorial, card_orderedPairs]

end TwoComponentCoulomb.PairEnumeration

end
