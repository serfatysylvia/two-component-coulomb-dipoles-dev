/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import TwoComponentCoulomb.Frozen.Corollary23
public import TwoComponentCoulomb.Gibbs.Basic
public import TwoComponentCoulomb.UpperBound.PairBlocks

/-!
# The energy split and the separation of variables in Proposition 3.9, Step 2

Source: proof of Proposition 3.9, Step 2, l. 1421–1459: the insertion of
Corollary 2.3 (gre1), the energies `F⁽¹⁾` the definition of F⁽¹⁾ and `F⁽²⁾` the definition of F⁽²⁾, the lower bound
`F_λ ≥ F⁽¹⁾ + F⁽²⁾ - C(N - K)` and the separation of variables (gred3).

Fix a marked graph `γ = (φ, T)`, with `I = I^pair` the vertices of the isolated 2-cycles of `φ`
(`TwoComponentCoulomb.pairVerts φ`, `|I| = 2m`) and `I'` the vertices of the marked same-sign pairs
(`TwoComponentCoulomb.markedSameSign φ T`). The blocks `I`, `Iᶜ`, the restricted graphs
`γ¹, γ²` and the restriction lemmas are in `UpperBound/PairBlocks.lean`. For a generic
configuration `Z` of the box with `γ_{2N}(Z) = γ`:

* the index sets of the two sums of Corollary 2.3 are the marked same-sign vertices `I'` and the
  marked neutral vertices (`TwoComponentCoulomb.filter_corollary23_sameSign_eq`,
  `TwoComponentCoulomb.filter_corollary23_neutral_eq`);
* `F^nn(Z) = F^nn(Z|_I) + F^nn(Z|_{Iᶜ})`, and the radii `r̃₁, r̃₂` computed within `I` agree with
  the global ones at the marked vertices;
* the additional quadratic terms `-C (r̃₁/r̃₂)²` of `F⁽¹⁾` on the unmarked isolated vertices are
  nonpositive (l. 1450, `TwoComponentCoulomb.pairAssignedEnergy_le`).

`F⁽¹⁾` is `TwoComponentCoulomb.pairAssignedEnergy` on the index type `I` with `S = I'` and `C` the
constant of Corollary 2.3, and `F⁽²⁾` is `TwoComponentCoulomb.nnEnergy` on `Iᶜ`.

## Main definitions

* `TwoComponentCoulomb.corollary23Bound hN C lam Z`: the left side of Corollary 2.3;
  `TwoComponentCoulomb.Corollary23Holds C`: Corollary 2.3 holds with the constant `C`
  (`TwoComponentCoulomb.exists_corollary23Holds`, from the frozen statement
  `TwoComponentCoulomb.corollary_2_3`).

## Main results

* `TwoComponentCoulomb.le_energy_split` (`F_λ ≥ F⁽¹⁾ + F⁽²⁾ - C(N - K)`, `m ≥ 2`, `Iᶜ ≠ ∅`),
  `TwoComponentCoulomb.le_energy_split_of_empty` (no marked pair, e.g. `m ≤ 1`: only the
  nearest-neighbour terms), `TwoComponentCoulomb.le_energy_full` and
  `TwoComponentCoulomb.le_energy_full_of_empty` (the same bounds on the whole index set, used when
  `Iᶜ = ∅` or `I = ∅`).
* `TwoComponentCoulomb.setLIntegral_subtype_mul_le`: separation of variables for a product
  integrand.
* `TwoComponentCoulomb.lintegral_markedCell_le_mul` (gred3) and its variants
  `TwoComponentCoulomb.lintegral_markedCell_le_mul_of_empty`,
  `TwoComponentCoulomb.lintegral_markedCell_le_full`,
  `TwoComponentCoulomb.lintegral_markedCell_le_full_of_empty`.
* The energy split: the lower bound and (gred3) packaged with
  the constant of Corollary 2.3.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset MeasureTheory
open scoped ENNReal

/-! ### The index sets of Corollary 2.3 are the marked pairs -/

section MarkedIndex

variable {N : ℕ}

open scoped Classical in
/-- The first sum of Corollary 2.3 runs over the marked same-sign vertices `I'` (source
l. 1429–1438). -/
theorem filter_corollary23_sameSign_eq (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) :
    Finset.univ.filter (fun i => IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) =
      markedSameSign (nearestNeighbor Z) (twiceIsolatedSet hN Z) := by
  ext i
  rw [mem_filter, mem_markedSameSign, mem_twiceIsolatedSet, isIsolatedDipole_iff]
  unfold IsTwiceIsolated
  constructor
  · rintro ⟨-, h1, h2, h3, h4⟩
    exact ⟨⟨h1, h3, h4⟩, fun h => h2 ⟨h1, h⟩⟩
  · rintro ⟨⟨h1, h3, h4⟩, h2⟩
    exact ⟨mem_univ _, h1, fun h => h2 h.2, h3, h4⟩

open scoped Classical in
/-- The second sum of Corollary 2.3 runs over the marked neutral vertices (source
l. 1429–1438). -/
theorem filter_corollary23_neutral_eq (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) :
    Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) =
      (twiceIsolatedSet hN Z).filter fun i => charge i * charge (nearestNeighbor Z i) = -1 := by
  ext i
  rw [mem_filter, mem_filter, mem_twiceIsolatedSet, isIsolatedDipole_iff]
  unfold IsTwiceIsolated
  constructor
  · rintro ⟨-, ⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h3, h4⟩, h2⟩
  · rintro ⟨⟨h1, h3, h4⟩, h2⟩
    exact ⟨mem_univ _, ⟨h1, h2⟩, h3, h4⟩

/-- A marked vertex is twice isolated. -/
theorem isTwiceIsolated_of_mem {hN : 2 ≤ N} {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N}
    (hi : i ∈ twiceIsolatedSet hN Z) : IsTwiceIsolated hN Z i :=
  (mem_twiceIsolatedSet hN Z).1 hi

end MarkedIndex

/-! ### Corollary 2.3 -/

section Corollary

variable {N : ℕ}

open scoped Classical in
/-- The left side of Corollary 2.3 (coromino, source l. 458–470), with constant `C`: the
nearest-neighbour energy, the logarithmic terms of the marked same-sign vertices, the quadratic
terms of the marked neutral vertices and `-C(N - K)`. -/
noncomputable def corollary23Bound (hN : 2 ≤ N) (C lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) : ℝ :=
  -(1 / 2) * ∑ i, smearedKernel lam (Z i - Z (nearestNeighbor Z i))
    + ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
        (Real.log (min (secondNeighborRadius hN lam Z i)
            (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) / firstNeighborRadius lam Z i)
          - C)
    - C * ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
        (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2
    - C * ((N : ℝ) - numComponents Z)

/-- Corollary 2.3 holds with the constant `C`. -/
def Corollary23Holds (C : ℝ) : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam →
    ∀ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) → IsGeneric Z →
      corollary23Bound hN C lam Z ≤ energy lam Z

/-- Corollary 2.3 (the frozen statement `TwoComponentCoulomb.corollary_2_3`). -/
theorem exists_corollary23Holds : ∃ C : ℝ, 0 < C ∧ Corollary23Holds C :=
  corollary_2_3

end Corollary

/-! ### The lower bound `F_λ ≥ F⁽¹⁾ + F⁽²⁾ - C(N - K)` -/

section Split

/-- The quadratic terms of the pair-assigned energy are nonpositive: dropping those of the
vertices outside a set `U ⊆ Sᶜ` can only increase the energy. -/
theorem pairAssignedEnergy_le {ι : Type*} [Fintype ι] [Nontrivial ι] (h3 : 3 ≤ Fintype.card ι)
    (key : ι ↪ ℕ) (lam : ℝ) {C : ℝ} (hC : 0 ≤ C) (S U : Finset ι) (hU : ∀ i ∈ U, i ∉ S)
    (z : ι → ℂ) :
    pairAssignedEnergy h3 key lam C S z ≤ nnEnergy key lam z
      + ∑ i ∈ S, (Real.log (min (nnRadius2 h3 key lam z i) (nnRadius2 h3 key lam z (nnMap key z i))
          / nnRadius lam z i) - C)
      - C * ∑ i ∈ U, (nnRadius lam z i / nnRadius2 h3 key lam z i) ^ 2 := by
  classical
  unfold pairAssignedEnergy
  have h : ∑ i ∈ U, (nnRadius lam z i / nnRadius2 h3 key lam z i) ^ 2 ≤
      ∑ i ∈ Sᶜ, (nnRadius lam z i / nnRadius2 h3 key lam z i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => mem_compl.2 (hU i hi))
      fun i _ _ => sq_nonneg _
  have := mul_le_mul_of_nonneg_left h hC
  linarith

variable {N : ℕ}

/-- The marked vertices lie in `I = I^pair`. -/
theorem mem_pairVerts_of_mem_twiceIsolatedSet {hN : 2 ≤ N} {Z : Fin N ⊕ Fin N → ℂ}
    {i : Fin N ⊕ Fin N} (hi : i ∈ twiceIsolatedSet hN Z) : i ∈ pairVerts (nearestNeighbor Z) :=
  mem_pairVerts_nearestNeighbor.2 (isTwiceIsolated_of_mem hi).1

/-- The marked vertices have their second nearest neighbour in `I = I^pair`. -/
theorem secondNearestNeighbor_mem_pairVerts {hN : 2 ≤ N} {Z : Fin N ⊕ Fin N → ℂ}
    {i : Fin N ⊕ Fin N} (hi : i ∈ twiceIsolatedSet hN Z) :
    secondNearestNeighbor hN Z i ∈ pairVerts (nearestNeighbor Z) :=
  mem_pairVerts_nearestNeighbor.2 (isTwiceIsolated_of_mem hi).2.1

/-- The partners of the marked vertices have their second nearest neighbour in `I = I^pair`. -/
theorem secondNearestNeighbor_nearestNeighbor_mem_pairVerts {hN : 2 ≤ N}
    {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N} (hi : i ∈ twiceIsolatedSet hN Z) :
    secondNearestNeighbor hN Z (nearestNeighbor Z i) ∈ pairVerts (nearestNeighbor Z) :=
  mem_pairVerts_nearestNeighbor.2 (isTwiceIsolated_of_mem hi).2.2

/-! Algebraic comparison with the Corollary 2.3 expression. -/

theorem pairAssignedEnergy_add_nnEnergy_le_corollary23Bound {C : ℝ} (hC0 : 0 ≤ C) (hN : 2 ≤ N) (lam : ℝ) {Z : Fin N ⊕ Fin N → ℂ}
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hφ : nearestNeighbor Z = φ) (hT : twiceIsolatedSet hN Z = T)
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}]
    (h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts φ}) :
    pairAssignedEnergy h3 (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam C (markedSameSignIn φ T)
        (fun j : {i // i ∈ pairVerts φ} => Z j)
      + nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
          (fun j : {i // i ∉ pairVerts φ} => Z j)
      - C * ((N : ℝ) - numComponents Z) ≤ corollary23Bound hN C lam Z := by
  classical
  subst hφ hT
  unfold corollary23Bound
  rw [filter_corollary23_sameSign_eq, filter_corollary23_neutral_eq,
    neg_half_sum_smearedKernel_eq rfl lam]
  set P := pairVerts (nearestNeighbor Z) with hPdef
  set key := subtypeKey (· ∈ P) (sumKey N) with hkey
  set z : {i // i ∈ P} → ℂ := fun j => Z j with hz
  have hp : ∀ i, i ∈ P → nearestNeighbor Z i ∈ P := fun _ hi => apply_mem_pairVerts hi
  set U := ((twiceIsolatedSet hN Z).filter
    fun i => charge i * charge (nearestNeighbor Z i) = -1).subtype (· ∈ P) with hU
  have hUS : ∀ i ∈ U, i ∉ markedSameSignIn (nearestNeighbor Z) (twiceIsolatedSet hN Z) := by
    intro i hi h
    exact (mem_markedSameSignIn.1 h).2 (mem_filter.1 (mem_subtype.1 hi)).2
  have h1 := pairAssignedEnergy_le h3 key lam hC0 _ U hUS z
  have hA : ∑ i ∈ markedSameSignIn (nearestNeighbor Z) (twiceIsolatedSet hN Z),
      (Real.log (min (nnRadius2 h3 key lam z i) (nnRadius2 h3 key lam z (nnMap key z i))
        / nnRadius lam z i) - C) =
      ∑ i ∈ markedSameSign (nearestNeighbor Z) (twiceIsolatedSet hN Z),
        (Real.log (min (secondNeighborRadius hN lam Z i)
          (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) / firstNeighborRadius lam Z i)
          - C) := by
    rw [← Finset.sum_subtype_of_mem (p := (· ∈ P)) _
      (fun x hx => mem_pairVerts_of_mem_twiceIsolatedSet (mem_markedSameSign.1 hx).1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiT := (mem_markedSameSign.1 (mem_subtype.1 hi)).1
    have hj : (nnMap key z i).1 = nearestNeighbor Z i := nnMap_subtype_val rfl hp i
    rw [nnRadius2_subtype_eq hN h3 rfl hp lam i (secondNearestNeighbor_mem_pairVerts hiT),
      nnRadius2_subtype_eq hN h3 rfl hp lam _
        (by rw [hj]; exact secondNearestNeighbor_nearestNeighbor_mem_pairVerts hiT),
      hj, nnRadius_subtype_eq rfl hp lam i]
  have hB : ∑ i ∈ (twiceIsolatedSet hN Z).filter
      (fun i => charge i * charge (nearestNeighbor Z i) = -1),
      (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 =
      ∑ i ∈ U, (nnRadius lam z i / nnRadius2 h3 key lam z i) ^ 2 := by
    rw [hU, ← Finset.sum_subtype_of_mem (p := (· ∈ P)) _
      (fun x hx => mem_pairVerts_of_mem_twiceIsolatedSet (mem_filter.1 hx).1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiT := (mem_filter.1 (mem_subtype.1 hi)).1
    rw [nnRadius2_subtype_eq hN h3 rfl hp lam i (secondNearestNeighbor_mem_pairVerts hiT),
      nnRadius_subtype_eq rfl hp lam i]
  rw [hA] at h1
  rw [hB]
  linarith

/-- **The lower bound `F_λ ≥ F⁽¹⁾ + F⁽²⁾ - C(N - K)`** (source l. 1440–1453), for `m ≥ 2` and
`Iᶜ ≠ ∅`. Here `F⁽¹⁾` the definition of F⁽¹⁾ is the pair-assigned energy of `Z|_I`, `I = I^pair`, with the
logarithmic terms on the marked same-sign vertices `I'`, the quadratic terms on `I ∖ I'` and the
radii computed within `I`, and `F⁽²⁾` the definition of F⁽²⁾ is the nearest-neighbour energy of `Z|_{Iᶜ}`;
`C` is any constant for which Corollary 2.3 holds. -/
theorem le_energy_split {C : ℝ} (hC0 : 0 ≤ C) (hC : Corollary23Holds C) (hN : 2 ≤ N) {lam : ℝ}
    (hlam : 0 < lam) {Z : Fin N ⊕ Fin N → ℂ} (hZ : ∀ i, Z i ∈ box N) (hgen : IsGeneric Z)
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hφ : nearestNeighbor Z = φ) (hT : twiceIsolatedSet hN Z = T)
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}]
    (h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts φ}) :
    pairAssignedEnergy h3 (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam C (markedSameSignIn φ T)
        (fun j : {i // i ∈ pairVerts φ} => Z j)
      + nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
          (fun j : {i // i ∉ pairVerts φ} => Z j)
      - C * ((N : ℝ) - numComponents Z) ≤ energy lam Z := by
  exact (pairAssignedEnergy_add_nnEnergy_le_corollary23Bound hC0 hN lam hφ hT h3).trans
    (hC N hN lam hlam Z hZ hgen)

/-- Without marked pairs (`T = ∅`, which is the case when `m ≤ 1`), Corollary 2.3 is the bound
`F_λ ≥ F^nn - C(N - K)`. -/
theorem corollary23Bound_of_twiceIsolatedSet_eq_empty (hN : 2 ≤ N) (C lam : ℝ)
    {Z : Fin N ⊕ Fin N → ℂ} (hT : twiceIsolatedSet hN Z = ∅) :
    corollary23Bound hN C lam Z =
      -(1 / 2) * ∑ i, smearedKernel lam (Z i - Z (nearestNeighbor Z i))
        - C * ((N : ℝ) - numComponents Z) := by
  classical
  unfold corollary23Bound
  rw [filter_corollary23_sameSign_eq, filter_corollary23_neutral_eq, hT]
  have h : markedSameSign (nearestNeighbor Z) (∅ : Finset (Fin N ⊕ Fin N)) = ∅ := by
    unfold markedSameSign
    exact filter_empty _
  rw [h, filter_empty, sum_empty, sum_empty]
  ring

/-- **The lower bound without marked pairs** (source l. 1450, "If `m ≤ 1`, there are no marked
pairs [...]. We then use only the nearest-neighbor term in `F⁽¹⁾`"): if there is no twice-isolated
pair, then
`F_λ ≥ F^nn(Z|_I) + F^nn(Z|_{Iᶜ}) - C(N - K)`. -/
theorem le_energy_split_of_empty {C : ℝ} (hC : Corollary23Holds C) (hN : 2 ≤ N) {lam : ℝ}
    (hlam : 0 < lam) {Z : Fin N ⊕ Fin N → ℂ} (hZ : ∀ i, Z i ∈ box N) (hgen : IsGeneric Z)
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} (hφ : nearestNeighbor Z = φ)
    (hT : twiceIsolatedSet hN Z = ∅)
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}] :
    nnEnergy (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam (fun j : {i // i ∈ pairVerts φ} => Z j)
      + nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
          (fun j : {i // i ∉ pairVerts φ} => Z j)
      - C * ((N : ℝ) - numComponents Z) ≤ energy lam Z := by
  have h := hC N hN lam hlam Z hZ hgen
  rw [corollary23Bound_of_twiceIsolatedSet_eq_empty hN C lam hT,
    neg_half_sum_smearedKernel_eq hφ lam] at h
  exact h

/-- The nearest-neighbour energy of the whole configuration is
`F^nn = -½ ∑ g_λ(z_i - z_{φ₁(i)})`. -/
theorem nnEnergy_sumKey [Nontrivial (Fin N ⊕ Fin N)] (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) :
    nnEnergy (sumKey N) lam Z =
      -(1 / 2) * ∑ i, smearedKernel lam (Z i - Z (nearestNeighbor Z i)) := by
  unfold nnEnergy
  rw [nearestNeighbor_eq_nnMap_fun]

/-- **The lower bound without marked pairs, on all indices**: if there is no twice-isolated pair
(for instance when `m = 0`, `I = ∅`), then `F_λ ≥ F^nn - C(N - K)`. -/
theorem le_energy_full_of_empty [Nontrivial (Fin N ⊕ Fin N)] {C : ℝ} (hC : Corollary23Holds C)
    (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) {Z : Fin N ⊕ Fin N → ℂ} (hZ : ∀ i, Z i ∈ box N)
    (hgen : IsGeneric Z) (hT : twiceIsolatedSet hN Z = ∅) :
    nnEnergy (sumKey N) lam Z - C * ((N : ℝ) - numComponents Z) ≤ energy lam Z := by
  have h := hC N hN lam hlam Z hZ hgen
  rw [corollary23Bound_of_twiceIsolatedSet_eq_empty hN C lam hT] at h
  rw [nnEnergy_sumKey]
  exact h

/-! Algebraic comparison with the Corollary 2.3 expression. -/

theorem pairAssignedEnergy_le_corollary23Bound [Nontrivial (Fin N ⊕ Fin N)] {C : ℝ} (hC0 : 0 ≤ C)
    (hN : 2 ≤ N) (h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N)) (lam : ℝ) {Z : Fin N ⊕ Fin N → ℂ}
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hφ : nearestNeighbor Z = φ) (hT : twiceIsolatedSet hN Z = T) :
    pairAssignedEnergy h3 (sumKey N) lam C (markedSameSign φ T) Z
      - C * ((N : ℝ) - numComponents Z) ≤ corollary23Bound hN C lam Z := by
  classical
  subst hφ hT
  unfold corollary23Bound
  rw [filter_corollary23_sameSign_eq, filter_corollary23_neutral_eq, ← nnEnergy_sumKey]
  set U := (twiceIsolatedSet hN Z).filter
    fun i => charge i * charge (nearestNeighbor Z i) = -1 with hU
  have hUS : ∀ i ∈ U, i ∉ markedSameSign (nearestNeighbor Z) (twiceIsolatedSet hN Z) := by
    intro i hi h
    exact (mem_markedSameSign.1 h).2 (mem_filter.1 hi).2
  have h1 := pairAssignedEnergy_le h3 (sumKey N) lam hC0 _ U hUS Z
  simp only [← nearestNeighbor_eq_nnMap, ← secondNeighborRadius_eq_nnRadius2 hN h3,
    ← firstNeighborRadius_eq_nnRadius] at h1
  linarith

/-- **The lower bound on all indices** (source l. 1440–1453 with `I` the whole index set, the case
`Iᶜ = ∅`): `F_λ ≥ F⁽¹⁾ - C(N - K)`, where `F⁽¹⁾` is the pair-assigned energy of the whole
configuration with the logarithmic terms on the marked same-sign vertices. It holds for every
generic configuration of the box. -/
theorem le_energy_full [Nontrivial (Fin N ⊕ Fin N)] {C : ℝ} (hC0 : 0 ≤ C)
    (hC : Corollary23Holds C) (hN : 2 ≤ N) (h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N)) {lam : ℝ}
    (hlam : 0 < lam) {Z : Fin N ⊕ Fin N → ℂ} (hZ : ∀ i, Z i ∈ box N) (hgen : IsGeneric Z)
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hφ : nearestNeighbor Z = φ) (hT : twiceIsolatedSet hN Z = T) :
    pairAssignedEnergy h3 (sumKey N) lam C (markedSameSign φ T) Z
      - C * ((N : ℝ) - numComponents Z) ≤ energy lam Z := by
  exact (pairAssignedEnergy_le_corollary23Bound hC0 hN h3 lam hφ hT).trans
    (hC N hN lam hlam Z hZ hgen)

end Split

/-! ### Separation of variables -/

section Separation

/-- **Separation of variables** (source l. 1454–1459): if the domain `S` forces `Z|_P ∈ E₁` and
`Z|_{Pᶜ} ∈ E₂`, the integral over `Λ^ι ∩ S` of a product `g₁(Z|_P) g₂(Z|_{Pᶜ})` is at most the
product of the integrals over `Λ^P ∩ E₁` and `Λ^{Pᶜ} ∩ E₂` ("Enlarging the integration domain
now separates the variables"). -/
theorem setLIntegral_subtype_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset ι)
    (B : Set ℂ) (S : Set (ι → ℂ)) (E₁ : Set ({i // i ∈ P} → ℂ)) (E₂ : Set ({i // i ∉ P} → ℂ))
    (hS : ∀ Z ∈ S, (fun i : {i // i ∈ P} => Z i) ∈ E₁ ∧ (fun i : {i // i ∉ P} => Z i) ∈ E₂)
    {g₁ : ({i // i ∈ P} → ℂ) → ℝ≥0∞} {g₂ : ({i // i ∉ P} → ℂ) → ℝ≥0∞}
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) :
    ∫⁻ Z in (Set.univ.pi fun _ : ι => B) ∩ S,
        g₁ (fun i : {i // i ∈ P} => Z i) * g₂ (fun i : {i // i ∉ P} => Z i) ≤
      (∫⁻ x in (Set.univ.pi fun _ : {i // i ∈ P} => B) ∩ E₁, g₁ x) *
        ∫⁻ y in (Set.univ.pi fun _ : {i // i ∉ P} => B) ∩ E₂, g₂ y := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (· ∈ P) with he
  have hmp : MeasurePreserving e (volume : Measure (ι → ℂ))
      ((volume : Measure ({i // i ∈ P} → ℂ)).prod (volume : Measure ({i // i ∉ P} → ℂ))) := by
    have := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (· ∈ P)
    rw [Measure.volume_eq_prod] at this
    convert this using 5
  set W₁ := (Set.univ.pi fun _ : {i // i ∈ P} => B) ∩ E₁ with hW₁
  set W₂ := (Set.univ.pi fun _ : {i // i ∉ P} => B) ∩ E₂ with hW₂
  have hsub : (Set.univ.pi fun _ : ι => B) ∩ S ⊆ e ⁻¹' (W₁ ×ˢ W₂) := by
    intro Z hZ
    obtain ⟨hZB, hZS⟩ := hZ
    exact ⟨⟨fun i _ => hZB i (Set.mem_univ _), (hS Z hZS).1⟩,
      ⟨fun i _ => hZB i (Set.mem_univ _), (hS Z hZS).2⟩⟩
  refine (lintegral_mono_set hsub).trans (le_of_eq ?_)
  have h1 := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun w => g₁ w.1 * g₂ w.2) (W₁ ×ˢ W₂)
  refine h1.trans ?_
  rw [← Measure.prod_restrict]
  exact lintegral_prod_mul hg₁.aemeasurable hg₂.aemeasurable

/-- The pointwise bound `e^{-β F_λ} ≤ e^{β c} e^{-β F⁽¹⁾} e^{-β F⁽²⁾}` from
`F_λ ≥ F⁽¹⁾ + F⁽²⁾ - c`, `β ≥ 0`. -/
theorem ofReal_exp_neg_mul_le_mul {β E F₁ F₂ c : ℝ} (hβ : 0 ≤ β) (h : F₁ + F₂ - c ≤ E) :
    ENNReal.ofReal (Real.exp (-β * E)) ≤ ENNReal.ofReal (Real.exp (β * c)) *
      (ENNReal.ofReal (Real.exp (-β * F₁)) * ENNReal.ofReal (Real.exp (-β * F₂))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := mul_le_mul_of_nonneg_left h hβ
  linarith

/-- The pointwise bound `e^{-β F_λ} ≤ e^{β c} e^{-β F⁽¹⁾}` from `F_λ ≥ F⁽¹⁾ - c`, `β ≥ 0`. -/
theorem ofReal_exp_neg_mul_le {β E F c : ℝ} (hβ : 0 ≤ β) (h : F - c ≤ E) :
    ENNReal.ofReal (Real.exp (-β * E)) ≤
      ENNReal.ofReal (Real.exp (β * c)) * ENNReal.ofReal (Real.exp (-β * F)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := mul_le_mul_of_nonneg_left h hβ
  linarith

end Separation

/-! ### The cell integrals (gred3) -/

section CellIntegrals

variable {N : ℕ}

/-- **Separation of variables (gred3)** (source l. 1454–1459), for `m ≥ 2` and `Iᶜ ≠ ∅`: for a
marked graph `γ = (φ, T) ∈ D_{2N,K,p,p₀}` and any event `A`,
`∫_{Λ^{2N} ∩ A ∩ {γ_{2N} = γ}} e^{-β F_λ} ≤ e^{β C (N - K)} ·
∫_{Λ^{2m} ∩ {γ_{2m} = γ¹}} e^{-β F⁽¹⁾} · ∫_{Λ^{2N-2m} ∩ {γ_{2N-2m} = γ²}} e^{-β F⁽²⁾}`,
where `I = I^pair` is determined by `φ`, `γ¹, γ²` are the restrictions of `φ` to `I` and `Iᶜ`, and
`C` is any constant for which Corollary 2.3 holds. -/
theorem lintegral_markedCell_le_mul {C : ℝ} (hC0 : 0 ≤ C) (hC : Corollary23Holds C)
    (hN : 2 ≤ N) {lam β : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ β) {K p p₀ : ℕ}
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hγ : (φ, T) ∈ markedGraphs hN K p p₀) (A : Set (Fin N ⊕ Fin N → ℂ))
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}]
    (h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts φ}) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) ≤
      ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ((∫⁻ x in (Set.univ.pi fun _ : {i // i ∈ pairVerts φ} => box N) ∩
            {x | nnMap (subtypeKey (· ∈ pairVerts φ) (sumKey N)) x = pairRestrict φ},
            ENNReal.ofReal (Real.exp (-β * pairAssignedEnergy h3
              (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam C (markedSameSignIn φ T) x))) *
          ∫⁻ y in (Set.univ.pi fun _ : {i // i ∉ pairVerts φ} => box N) ∩
            {y | nnMap (subtypeKey (· ∉ pairVerts φ) (sumKey N)) y = complRestrict φ},
            ENNReal.ofReal (Real.exp (-β *
              nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam y))) := by
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ T)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
          (ENNReal.ofReal (Real.exp (-β * pairAssignedEnergy h3
              (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam C (markedSameSignIn φ T)
              (fun j : {i // i ∈ pairVerts φ} => Z j))) *
            ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∉ pairVerts φ} => Z j)))) := by
        refine setLIntegral_mono' hmeas fun Z hZ => ?_
        obtain ⟨hZΛ, hZc⟩ := hZ
        have hK := numComponents_eq_of_mem_markedCell hγ hZc
        have h := le_energy_split hC0 hC hN hlam (fun i => hZΛ i (Set.mem_univ i)) hZc.1 hZc.2.1
          hZc.2.2 h3
        rw [hK] at h
        exact ofReal_exp_neg_mul_le_mul hβ h
    _ = ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
          ENNReal.ofReal (Real.exp (-β * pairAssignedEnergy h3
              (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam C (markedSameSignIn φ T)
              (fun j : {i // i ∈ pairVerts φ} => Z j))) *
            ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∉ pairVerts φ} => Z j))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        refine setLIntegral_subtype_mul_le (pairVerts φ) (box N) (markedCell hN φ T) _ _
          (fun Z hZ => ⟨nnMap_pairRestrict hZ.2.1, nnMap_complRestrict hZ.2.1⟩)
          (measurable_ofReal_exp_neg_mul (measurable_pairAssignedEnergy _ h3 lam C _) β)
          (measurable_ofReal_exp_neg_mul (measurable_nnEnergy _ lam) β)

/-- **Separation of variables without marked pairs** (source l. 1450, 1454–1459; the case `m ≤ 1`,
where `F⁽¹⁾` is only the nearest-neighbour term): if `T = ∅`, the cell integral is at most
`e^{β C (N - K)} · ∫_{Λ^{2m} ∩ {γ_{2m} = γ¹}} e^{-β F^nn} ·
∫_{Λ^{2N-2m} ∩ {γ_{2N-2m} = γ²}} e^{-β F⁽²⁾}`. -/
theorem lintegral_markedCell_le_mul_of_empty {C : ℝ} (hC : Corollary23Holds C)
    (hN : 2 ≤ N) {lam β : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ β) {K p p₀ : ℕ}
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    (hγ : (φ, ∅) ∈ markedGraphs hN K p p₀) (A : Set (Fin N ⊕ Fin N → ℂ))
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}] :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) ≤
      ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ((∫⁻ x in (Set.univ.pi fun _ : {i // i ∈ pairVerts φ} => box N) ∩
            {x | nnMap (subtypeKey (· ∈ pairVerts φ) (sumKey N)) x = pairRestrict φ},
            ENNReal.ofReal (Real.exp (-β *
              nnEnergy (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam x))) *
          ∫⁻ y in (Set.univ.pi fun _ : {i // i ∉ pairVerts φ} => box N) ∩
            {y | nnMap (subtypeKey (· ∉ pairVerts φ) (sumKey N)) y = complRestrict φ},
            ENNReal.ofReal (Real.exp (-β *
              nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam y))) := by
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ ∅)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
          (ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∈ pairVerts φ} => Z j))) *
            ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∉ pairVerts φ} => Z j)))) := by
        refine setLIntegral_mono' hmeas fun Z hZ => ?_
        obtain ⟨hZΛ, hZc⟩ := hZ
        have hK := numComponents_eq_of_mem_markedCell hγ hZc
        have h := le_energy_split_of_empty hC hN hlam (fun i => hZΛ i (Set.mem_univ i)) hZc.1
          hZc.2.1 hZc.2.2
        rw [hK] at h
        exact ofReal_exp_neg_mul_le_mul hβ h
    _ = ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
          ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∈ pairVerts φ} => Z j))) *
            ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
              (fun j : {i // i ∉ pairVerts φ} => Z j))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        refine setLIntegral_subtype_mul_le (pairVerts φ) (box N) (markedCell hN φ ∅) _ _
          (fun Z hZ => ⟨nnMap_pairRestrict hZ.2.1, nnMap_complRestrict hZ.2.1⟩)
          (measurable_ofReal_exp_neg_mul (measurable_nnEnergy _ lam) β)
          (measurable_ofReal_exp_neg_mul (measurable_nnEnergy _ lam) β)

/-- **The cell integral without marked pairs, on all indices** (the case `m = 0`, `I = ∅`): if
`T = ∅`, the cell integral is at most `e^{β C (N - K)} ∫_{Λ^{2N} ∩ {γ_{2N} = φ}} e^{-β F^nn}`. -/
theorem lintegral_markedCell_le_full_of_empty [Nontrivial (Fin N ⊕ Fin N)] {C : ℝ}
    (hC : Corollary23Holds C) (hN : 2 ≤ N) {lam β : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ β)
    {K p p₀ : ℕ} {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    (hγ : (φ, ∅) ∈ markedGraphs hN K p p₀) (A : Set (Fin N ⊕ Fin N → ℂ)) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) ≤
      ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nnMap (sumKey N) Z = φ},
          ENNReal.ofReal (Real.exp (-β * nnEnergy (sumKey N) lam Z)) := by
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ ∅)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
        ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
          ENNReal.ofReal (Real.exp (-β * nnEnergy (sumKey N) lam Z)) := by
        refine setLIntegral_mono' hmeas fun Z hZ => ?_
        obtain ⟨hZΛ, hZc⟩ := hZ
        have hK := numComponents_eq_of_mem_markedCell hγ hZc
        have h := le_energy_full_of_empty hC hN hlam (fun i => hZΛ i (Set.mem_univ i)) hZc.1
          hZc.2.2
        rw [hK] at h
        exact ofReal_exp_neg_mul_le hβ h
    _ = ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ ∅,
          ENNReal.ofReal (Real.exp (-β * nnEnergy (sumKey N) lam Z)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right (lintegral_mono_set ?_) _
        rintro Z ⟨hZΛ, hZc⟩
        exact ⟨hZΛ, (nearestNeighbor_eq_nnMap_fun Z).symm.trans hZc.2.1⟩

/-- **The cell integral on all indices** (the case `Iᶜ = ∅`, where `I` is the whole index set):
the cell integral is at most `e^{β C (N - K)} ∫_{Λ^{2N} ∩ {γ_{2N} = φ}} e^{-β F⁽¹⁾}`, with `F⁽¹⁾`
the pair-assigned energy of the whole configuration with the logarithmic terms on the marked
same-sign vertices. -/
theorem lintegral_markedCell_le_full [Nontrivial (Fin N ⊕ Fin N)] {C : ℝ} (hC0 : 0 ≤ C)
    (hC : Corollary23Holds C) (hN : 2 ≤ N) (h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N)) {lam β : ℝ}
    (hlam : 0 < lam) (hβ : 0 ≤ β) {K p p₀ : ℕ} {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    {T : Finset (Fin N ⊕ Fin N)} (hγ : (φ, T) ∈ markedGraphs hN K p p₀)
    (A : Set (Fin N ⊕ Fin N → ℂ)) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) ≤
      ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nnMap (sumKey N) Z = φ},
          ENNReal.ofReal (Real.exp (-β *
            pairAssignedEnergy h3 (sumKey N) lam C (markedSameSign φ T) Z)) := by
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ T)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
          ENNReal.ofReal (Real.exp (-β *
            pairAssignedEnergy h3 (sumKey N) lam C (markedSameSign φ T) Z)) := by
        refine setLIntegral_mono' hmeas fun Z hZ => ?_
        obtain ⟨hZΛ, hZc⟩ := hZ
        have hK := numComponents_eq_of_mem_markedCell hγ hZc
        have h := le_energy_full hC0 hC hN h3 hlam (fun i => hZΛ i (Set.mem_univ i)) hZc.1
          hZc.2.1 hZc.2.2
        rw [hK] at h
        exact ofReal_exp_neg_mul_le hβ h
    _ = ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
          ENNReal.ofReal (Real.exp (-β *
            pairAssignedEnergy h3 (sumKey N) lam C (markedSameSign φ T) Z)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right (lintegral_mono_set ?_) _
        rintro Z ⟨hZΛ, hZc⟩
        exact ⟨hZΛ, (nearestNeighbor_eq_nnMap_fun Z).symm.trans hZc.2.1⟩

end CellIntegrals

/-! ### The packaged statement -/

section Packaged

end Packaged

end TwoComponentCoulomb

end
