/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.InvolutionCover
import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Unordered cycle pairings

Subsections 3.4 and 3.5 count unordered pairs. A permutation with `k` disjoint
transpositions has `2^k k !` orderings of its endpoints. The cycle-type counting
formula retains both symmetry factors, including when `k = 0`.

The paper uses this count before applying Stirling's formula.
The pinned source is `source/dipole-formation.tex`.
-/

@[expose] public section

open Finset
open scoped Classical Nat

namespace TwoComponentCoulomb

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The partial pairings with `k` unordered pairs, supported on `S`. -/
noncomputable def partialPairings (S : Finset α) (k : ℕ) : Finset (α → α) :=
  univ.filter fun h => (∀ i, h (h i) = i) ∧ movedPoints h ⊆ S ∧ (movedPoints h).card = 2 * k

private def pairingPerm (S : Finset α) (k : ℕ) (h : partialPairings S k) : Equiv.Perm S where
  toFun i := ⟨h.1 i, by
    have hh := (mem_filter.1 h.2).2
    by_cases hi : h.1 i = i
    · simpa only [hi] using i.2
    · exact hh.2.1 (mem_movedPoints.2 (by rw [hh.1]; exact Ne.symm hi))⟩
  invFun i := ⟨h.1 i, by
    have hh := (mem_filter.1 h.2).2
    by_cases hi : h.1 i = i
    · simpa only [hi] using i.2
    · exact hh.2.1 (mem_movedPoints.2 (by rw [hh.1]; exact Ne.symm hi))⟩
  left_inv i := Subtype.ext ((mem_filter.1 h.2).2.1 i)
  right_inv i := Subtype.ext ((mem_filter.1 h.2).2.1 i)

private theorem pairingPerm_injective (S : Finset α) (k : ℕ) :
    Function.Injective (pairingPerm S k) := by
  intro h g he
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ S
  · exact congrArg Subtype.val (Equiv.congr_fun he ⟨i, hi⟩)
  · have hfix : h.1 i = i := by
      by_contra hh
      exact hi ((mem_filter.1 h.2).2.2.1 (mem_movedPoints.2 hh))
    have gfix : g.1 i = i := by
      by_contra hg
      exact hi ((mem_filter.1 g.2).2.2.1 (mem_movedPoints.2 hg))
    exact hfix.trans gfix.symm

private theorem pairingPerm_cycleType (S : Finset α) (k : ℕ) (h : partialPairings S k) :
    (pairingPerm S k h).cycleType = Multiset.replicate k 2 := by
  let σ := pairingPerm S k h
  have hσ : σ ^ 2 = 1 := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    change h.1 (h.1 i) = i
    exact (mem_filter.1 h.2).2.1 i
  have ht := Equiv.Perm.cycleType_of_pow_prime_eq_one hσ
  have hs : σ.support.card = 2 * k := by
    have he : σ.support = (movedPoints h.1).subtype (· ∈ S) := by
      ext i
      simp [Equiv.Perm.mem_support, movedPoints, σ, pairingPerm, Subtype.ext_iff]
    rw [he, Finset.card_subtype,
      filter_eq_self.2 (fun i hi => (mem_filter.1 h.2).2.2.1 hi)]

    exact (mem_filter.1 h.2).2.2.2
  have hcard : σ.cycleType.card = k := by
    have he : σ.cycleType.sum = σ.cycleType.card * 2 := by
      simpa only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] using congrArg Multiset.sum ht
    rw [σ.sum_cycleType, hs] at he
    omega
  simpa only [hcard] using ht

/-- The pairing constructed from representatives fixes every point outside their support. -/
theorem movedPoints_involutionOfEmb_subset (A Y : Finset α) (e : A ↪ Y) :
    movedPoints (involutionOfEmb A Y e) ⊆ A ∪ Y := by
  intro i hi
  by_contra h
  have hiA : i ∉ A := fun hi => h (mem_union_left Y hi)
  have hiY : i ∉ Y := fun hi => h (mem_union_right A hi)
  have hex : ¬ ∃ a : A, ((e a : Y) : α) = i := by
    rintro ⟨a, ha⟩
    exact hiY (ha ▸ (e a).2)
  have hfix : involutionOfEmb A Y e i = i := by
    simp only [involutionOfEmb, dite_eq_right hiA, dite_eq_right hex]
  exact (mem_movedPoints.1 hi) hfix

/-- Every map in the representative cover is supported on `S` when its target is in `S`. -/
theorem movedPoints_subset_of_mem_involutionCover {S : Finset α} {k : ℕ} {h : α → α}
    (hh : h ∈ involutionCover S (fun A => S \ A) k) : movedPoints h ⊆ S := by
  obtain ⟨A, hA, h⟩ := mem_biUnion.1 hh
  obtain ⟨e, -, rfl⟩ := mem_image.1 h
  exact (movedPoints_involutionOfEmb_subset A (S \ A) e).trans
    (union_subset (mem_powersetCard.1 hA).1 sdiff_subset)

/-- **The unordered pairing count**. Multiplication by `(n-2k)! 2^k k !` removes
the denominator in `n! / ((n-2k)! 2^k k !)`. In particular the orientation factor
`2^k` is retained, as in both graph counts of the paper. -/
theorem card_partialPairings_mul_le (S : Finset α) (k : ℕ) :
    (partialPairings S k).card * ((S.card - 2 * k)! * 2 ^ k * k !) ≤ S.card ! := by
  let F : partialPairings S k → {σ : Equiv.Perm S // σ.cycleType = Multiset.replicate k 2} :=
    fun h => ⟨pairingPerm S k h, pairingPerm_cycleType S k h⟩
  have hinj : Function.Injective F := fun _ _ he =>
    pairingPerm_injective S k (congrArg Subtype.val he)
  have hc := Fintype.card_le_of_injective F hinj
  rw [Fintype.card_coe, Fintype.card_subtype] at hc
  have hcount := Equiv.Perm.card_of_cycleType_mul_eq S (Multiset.replicate k 2)
  have hprod : (∏ n ∈ (Multiset.replicate k 2).toFinset,
      ((Multiset.replicate k 2).count n) !) = k ! := by
    cases k with
    | zero => simp
    | succ k => simp only [Multiset.toFinset_replicate, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ite_false, Finset.prod_singleton, Multiset.count_replicate_self]
  simp only [Fintype.card_coe, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm k 2,
    Multiset.prod_replicate, hprod] at hcount
  refine (Nat.mul_le_mul_right _ hc).trans ?_
  rw [hcount]
  split_ifs <;> omega

/-- **The exact unordered pairing count**. For `2k ≤ |S|`, multiplying
`|S|! / ((|S|-2k)! 2^k k!)` by its denominator gives `|S|!`. Thus ordering the
`k` pairs gives exactly the endpoint count used in subsection 3.4. -/
theorem card_partialPairings_mul_eq (S : Finset α) (k : ℕ) (hk : 2 * k ≤ S.card) :
    (partialPairings S k).card * ((S.card - 2 * k)! * 2 ^ k * k !) = S.card ! := by
  let T := {σ : Equiv.Perm S // σ.cycleType = Multiset.replicate k 2}
  let F : partialPairings S k → T := fun h => ⟨pairingPerm S k h, pairingPerm_cycleType S k h⟩
  have hF : Function.Injective F := fun _ _ he =>
    pairingPerm_injective S k (congrArg Subtype.val he)
  let G : T → partialPairings S k := fun σ => ⟨Equiv.Perm.ofSubtype σ.1, by
    have hpow : (Equiv.Perm.ofSubtype σ.1) ^ 2 = 1 := by
      apply Equiv.Perm.pow_prime_eq_one_iff.2
      rw [Equiv.Perm.cycleType_ofSubtype, σ.2]
      intro a ha
      exact (Multiset.mem_replicate.1 ha).2
    refine mem_filter.2 ⟨mem_univ _, ?_, ?_, ?_⟩
    · intro i
      have h := Equiv.congr_fun hpow i
      simpa only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h
    · intro i hi
      by_contra hiS
      exact (mem_movedPoints.1 hi) (Equiv.Perm.ofSubtype_apply_of_not_mem _ hiS)
    · change (Equiv.Perm.ofSubtype σ.1).support.card = 2 * k
      rw [← Equiv.Perm.sum_cycleType, Equiv.Perm.cycleType_ofSubtype, σ.2,
        Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm k 2]⟩
  have hG : Function.Injective G := by
    intro σ τ he
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Subtype.ext
    have h := congrArg (fun h : partialPairings S k => h.1 i) he
    change (Equiv.Perm.ofSubtype σ.1) i = (Equiv.Perm.ofSubtype τ.1) i at h
    simpa only [Equiv.Perm.ofSubtype_apply_of_mem _ i.2] using h
  have hc := le_antisymm (Fintype.card_le_of_injective F hF) (Fintype.card_le_of_injective G hG)
  rw [Fintype.card_coe, Fintype.card_subtype] at hc
  rw [hc]
  have hcount := Equiv.Perm.card_of_cycleType_mul_eq S (Multiset.replicate k 2)
  have hprod : (∏ n ∈ (Multiset.replicate k 2).toFinset,
      ((Multiset.replicate k 2).count n)!) = k ! := by
    cases k with
    | zero => simp
    | succ k => simp only [Multiset.toFinset_replicate, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ite_false, Finset.prod_singleton, Multiset.count_replicate_self]
  have hcond : (Multiset.replicate k 2).sum ≤ Fintype.card S ∧
      ∀ a ∈ Multiset.replicate k 2, 2 ≤ a := by
    constructor
    · simpa only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_coe,
        Nat.mul_comm k 2] using hk
    · intro a ha
      obtain ⟨_, rfl⟩ := Multiset.mem_replicate.1 ha
      exact le_rfl
  rw [ite_eq_left hcond] at hcount
  simpa only [Fintype.card_coe, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    Nat.mul_comm k 2, Multiset.prod_replicate, hprod] using hcount

/-- The exact endpoint count for `k` ordered unordered pairs, as used in the
labelling of the other cycles in subsection 3.4 of the paper. -/
theorem card_orderedPairings_mul_eq (S : Finset α) (k : ℕ) (hk : 2 * k ≤ S.card) :
    ((partialPairings S k).card * k !) * ((S.card - 2 * k)! * 2 ^ k) = S.card ! := by
  calc _ = (partialPairings S k).card * ((S.card - 2 * k)! * 2 ^ k * k !) := by ring
    _ = _ := card_partialPairings_mul_eq S k hk

end TwoComponentCoulomb

end
