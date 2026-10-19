/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Gibbs.Measurability
public import TwoComponentCoulomb.UpperBound.MarkedCells
public import TwoComponentCoulomb.UpperBound.PairAssignedEnergy

/-!
# The blocks `I = I^pair` and `Iᶜ` of Proposition 3.10, Step 2

Source: proof of Proposition 3.10, Step 2, l. 1532--1566. Fix a marked
graph `γ = (φ, T)`. Let `I = I^pair` be the vertices of the isolated 2-cycles of `φ`, with
`|I| = 2m`, and `I'` the vertices of the `p - p₀` marked same-sign pairs. This file sets up the two
blocks `I` and `Iᶜ` on which the energies `F⁽¹⁾` (def:F(1)) and `F⁽²⁾` (def:F(2)) live.

* Each vertex has its nearest neighbour in its own block (isolated pairs are mutual nearest
  neighbours and no other vertex points into them), so the restrictions `γ¹, γ²` of `φ` to `I`
  and `Iᶜ` are self-maps of the blocks.
* For a configuration `Z` with `φ₁(Z) = φ`, the nearest-neighbour map of the sub-configuration
  `Z|_I` (resp. `Z|_{Iᶜ}`), with the induced tie-break key, is `γ¹` (resp. `γ²`)
  (`TwoComponentCoulomb.nnMap_pairRestrict`, `TwoComponentCoulomb.nnMap_complRestrict`), and
  `F^nn(Z) = F^nn(Z|_I) + F^nn(Z|_{Iᶜ})` (`TwoComponentCoulomb.neg_half_sum_smearedKernel_eq`).
* The radius `r̃₁` computed within a block is the global one, and so is `r̃₂` at a vertex whose
  second nearest neighbour lies in the block (`TwoComponentCoulomb.nnRadius_subtype_eq`,
  `TwoComponentCoulomb.nnRadius2_subtype_eq`): "At marked vertices, the second neighbor also lies
  in `I`, so `r̃₂` is unchanged there" (l. 1542).

## Main definitions

* `TwoComponentCoulomb.pairVerts f`: the vertices `I^pair` of the isolated 2-cycles of `f`.
* `TwoComponentCoulomb.pairRestrict f`, `TwoComponentCoulomb.complRestrict f`: the restrictions
  `γ¹`, `γ²` of `f` to `I` and to `Iᶜ`.
* `TwoComponentCoulomb.subtypeKey p key`: the tie-break key induced on a subtype.
* `TwoComponentCoulomb.markedSameSign f T`, `TwoComponentCoulomb.markedSameSignIn f T`: the vertices
  `I'` of the marked same-sign pairs, in `Fin N ⊕ Fin N` and in `I`.

## Bookkeeping (source l. 1532--1566)

For a configuration `Z` with `φ₁(Z) = φ` and twice-isolated set `T`:
`γ¹` is a fixed-point-free involution of `I` (a perfect matching of the `m` isolated pairs);
`|I| = 2m` and `|Iᶜ| = 2(N - m)` (`TwoComponentCoulomb.card_pairVerts_subtype`,
`TwoComponentCoulomb.card_compl_pairVerts_subtype`); the 2-cycle vertices of `γ²` are
`2(K - m)`, so `γ²` has `K - m` components (`TwoComponentCoulomb.card_cycle_complRestrict`);
`I'` is a union of pairs of `γ¹` with `|I'| = 2(p - p₀)`
(`TwoComponentCoulomb.pairRestrict_mem_markedSameSignIn`,
`TwoComponentCoulomb.card_markedSameSignIn`); and there is no marked pair when `m ≤ 1`
(`TwoComponentCoulomb.twiceIsolatedSet_eq_empty_of_numIsolatedPairs_le_one`).

We also record that the energies `F^nn` and the pair-assigned energy are measurable functions of
the configuration (`TwoComponentCoulomb.measurable_nnEnergy`,
`TwoComponentCoulomb.measurable_pairAssignedEnergy`).
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset MeasureTheory
open scoped ENNReal

/-! ### Graph-level definitions -/

section Graph

variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The vertices `I^pair` of the isolated 2-cycles of a self-map `f` (source l. 375--385, ruling
R5): `{i, f i}` is a 2-cycle into which no other vertex maps. -/
noncomputable def pairVerts (f : ι → ι) : Finset ι :=
  univ.filter fun i => f (f i) = i ∧ ∀ k, (f k = i ∨ f k = f i) → k = i ∨ k = f i

theorem mem_pairVerts {f : ι → ι} {i : ι} :
    i ∈ pairVerts f ↔ f (f i) = i ∧ ∀ k, (f k = i ∨ f k = f i) → k = i ∨ k = f i := by
  classical
  unfold pairVerts
  rw [mem_filter]
  exact and_iff_right (mem_univ i)

/-- The partner of a vertex of an isolated 2-cycle lies in the same isolated 2-cycle. -/
theorem apply_mem_pairVerts {f : ι → ι} {i : ι} (h : i ∈ pairVerts f) : f i ∈ pairVerts f := by
  obtain ⟨h2, hk⟩ := mem_pairVerts.1 h
  refine mem_pairVerts.2 ⟨by rw [h2], fun k hk' => ?_⟩
  rw [h2] at hk'
  rcases hk k hk'.symm with h | h
  · exact Or.inr (by rw [h2]; exact h)
  · exact Or.inl h

/-- A vertex outside `I^pair` is not mapped into `I^pair`. -/
theorem apply_not_mem_pairVerts {f : ι → ι} {i : ι} (h : i ∉ pairVerts f) : f i ∉ pairVerts f := by
  intro hfi
  obtain ⟨-, hk⟩ := mem_pairVerts.1 hfi
  rcases hk i (Or.inl rfl) with h' | h'
  · exact h (h' ▸ hfi)
  · exact h (h' ▸ apply_mem_pairVerts hfi)

/-- The restriction `γ¹` of `f` to `I^pair` (source l. 1546). -/
def pairRestrict (f : ι → ι) (i : {i // i ∈ pairVerts f}) : {i // i ∈ pairVerts f} :=
  ⟨f i, apply_mem_pairVerts i.2⟩

/-- The restriction `γ²` of `f` to the complement of `I^pair` (source l. 1546). -/
def complRestrict (f : ι → ι) (i : {i // i ∉ pairVerts f}) : {i // i ∉ pairVerts f} :=
  ⟨f i, apply_not_mem_pairVerts i.2⟩

theorem pairRestrict_val (f : ι → ι) (i : {i // i ∈ pairVerts f}) :
    (pairRestrict f i : ι) = f i :=
  rfl

theorem complRestrict_val (f : ι → ι) (i : {i // i ∉ pairVerts f}) :
    (complRestrict f i : ι) = f i :=
  rfl

/-- `γ¹` is an involution: the isolated pairs are 2-cycles. -/
theorem pairRestrict_pairRestrict (f : ι → ι) (i : {i // i ∈ pairVerts f}) :
    pairRestrict f (pairRestrict f i) = i :=
  Subtype.ext (mem_pairVerts.1 i.2).1

/-- `γ¹` has no fixed point when `f` has none: it is a perfect matching of `I^pair`. -/
theorem pairRestrict_ne {f : ι → ι} (hf : ∀ i, f i ≠ i) (i : {i // i ∈ pairVerts f}) :
    pairRestrict f i ≠ i :=
  fun h => hf i (congrArg Subtype.val h)

/-- The tie-break key induced on a subtype by a key of the ambient index type. -/
def subtypeKey (p : ι → Prop) (key : ι ↪ ℕ) : {i // p i} ↪ ℕ :=
  (Function.Embedding.subtype p).trans key

end Graph

section Marks

variable {N : ℕ}

theorem mem_pairVerts_nearestNeighbor {Z : Fin N ⊕ Fin N → ℂ} {i : Fin N ⊕ Fin N} :
    i ∈ pairVerts (nearestNeighbor Z) ↔ IsIsolatedPair Z i :=
  mem_pairVerts

theorem isolatedPairSet_eq_pairVerts (Z : Fin N ⊕ Fin N → ℂ) :
    isolatedPairSet Z = pairVerts (nearestNeighbor Z) := by
  ext i
  rw [mem_isolatedPairSet, mem_pairVerts_nearestNeighbor]

open scoped Classical in
/-- The vertices `I'` of the marked same-sign pairs (source l. 1532): the marked vertices `i ∈ T`
whose pair `{i, f i}` is not neutral. -/
noncomputable def markedSameSign (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (T : Finset (Fin N ⊕ Fin N)) :
    Finset (Fin N ⊕ Fin N) :=
  T.filter fun i => charge i * charge (f i) ≠ -1

open scoped Classical in
/-- The set `I'` as a set of vertices of `I = I^pair`. -/
noncomputable def markedSameSignIn (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N)
    (T : Finset (Fin N ⊕ Fin N)) : Finset {i // i ∈ pairVerts f} :=
  (markedSameSign f T).subtype (· ∈ pairVerts f)

theorem mem_markedSameSign {f : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    {i : Fin N ⊕ Fin N} : i ∈ markedSameSign f T ↔ i ∈ T ∧ charge i * charge (f i) ≠ -1 := by
  unfold markedSameSign
  rw [mem_filter]

theorem mem_markedSameSignIn {f : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    {i : {i // i ∈ pairVerts f}} :
    i ∈ markedSameSignIn f T ↔
      (i : Fin N ⊕ Fin N) ∈ T ∧ charge (i : Fin N ⊕ Fin N) * charge (f i) ≠ -1 := by
  unfold markedSameSignIn
  rw [mem_subtype, mem_markedSameSign]

end Marks

/-! ### Restriction to a block closed under the nearest-neighbour map -/

section Restriction

variable {N : ℕ}

/-- The ambient index type is nontrivial as soon as one of its subtypes is. -/
theorem nontrivial_of_subtype {p : Fin N ⊕ Fin N → Prop} [Nontrivial {i // p i}] :
    Nontrivial (Fin N ⊕ Fin N) :=
  (Subtype.val_injective (p := p)).nontrivial

variable {p : Fin N ⊕ Fin N → Prop} [Fintype {i // p i}] [Nontrivial {i // p i}]
  {Z : Fin N ⊕ Fin N → ℂ}
  {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}

/-- On a block of indices closed under `φ = φ₁(Z)`, the nearest neighbour computed within the
block, with the induced tie-break key, is `φ` (source l. 1542--1546). -/
theorem nnMap_subtype_val (hφ : nearestNeighbor Z = φ) (hp : ∀ i, p i → p (φ i))
    (i : {i // p i}) :
    (nnMap (subtypeKey p (sumKey N)) (fun j : {i // p i} => Z j) i).1 = φ i := by
  have := nontrivial_of_subtype (p := p)
  have hmem : nnMap (sumKey N) Z (Function.Embedding.subtype p i) ∈
      Set.range (Function.Embedding.subtype p) := by
    rw [← nearestNeighbor_eq_nnMap, hφ]
    exact ⟨⟨φ i, hp i i.2⟩, rfl⟩
  have h := nnMap_restrict (sumKey N) Z (Function.Embedding.subtype p) i hmem
  rw [← nearestNeighbor_eq_nnMap, hφ] at h
  exact h

/-- The first radius `r̃₁` computed within a block closed under `φ₁` is the global one. -/
theorem nnRadius_subtype_eq (hφ : nearestNeighbor Z = φ) (hp : ∀ i, p i → p (φ i)) (lam : ℝ)
    (i : {i // p i}) :
    nnRadius lam (fun j : {i // p i} => Z j) i = firstNeighborRadius lam Z i := by
  rw [nnRadius_eq (subtypeKey p (sumKey N)), nnMap_subtype_val hφ hp i, firstNeighborRadius_eq, hφ]

/-- A vertex whose second nearest neighbour lies in the block keeps its second radius `r̃₂` when the
distances are computed within the block (source l. 1538, 1542, "At marked vertices, the second
neighbor also lies in `I`, so `r̃₂` is unchanged there"). -/
theorem nnRadius2_subtype_eq (hN : 2 ≤ N) (h3 : 3 ≤ Fintype.card {i // p i})
    (hφ : nearestNeighbor Z = φ) (hp : ∀ i, p i → p (φ i)) (lam : ℝ) (i : {i // p i})
    (h2 : p (secondNearestNeighbor hN Z i)) :
    nnRadius2 h3 (subtypeKey p (sumKey N)) lam (fun j : {i // p i} => Z j) i =
      secondNeighborRadius hN lam Z i := by
  rw [secondNeighborRadius_eq]
  refine le_antisymm ?_ ?_
  · refine nnRadius2_le h3 _ lam _ (j := ⟨secondNearestNeighbor hN Z i, h2⟩) ?_ ?_
    · intro h
      exact secondNearestNeighbor_ne_self hN Z i (congrArg Subtype.val h)
    · intro h
      have h' := congrArg Subtype.val h
      rw [nnMap_subtype_val hφ hp i, ← hφ] at h'
      exact secondNearestNeighbor_ne_nearestNeighbor hN Z i h'
  · refine le_nnRadius2_of_forall h3 _ lam _ i fun j hji hjφ => ?_
    have hji' : (j : Fin N ⊕ Fin N) ≠ i := fun h => hji (Subtype.ext h)
    have hjφ' : (j : Fin N ⊕ Fin N) ≠ nearestNeighbor Z i := by
      intro h
      apply hjφ
      apply Subtype.ext
      rw [nnMap_subtype_val hφ hp i, ← hφ, h]
    have := norm_sub_secondNearestNeighbor_le hN Z hji' hjφ'
    show 4 * (‖Z i - Z (secondNearestNeighbor hN Z i)‖ / 4) ≤ ‖Z i - Z j‖
    linarith

omit [Fintype {i // p i}] [Nontrivial {i // p i}] in
/-- **Restricted graphs** (source l. 1546, `γ¹`): the nearest-neighbour map of `Z|_I` is the
restriction of `φ₁(Z)` to `I = I^pair`. -/
theorem nnMap_pairRestrict (hφ : nearestNeighbor Z = φ) [Nontrivial {i // i ∈ pairVerts φ}] :
    nnMap (subtypeKey (· ∈ pairVerts φ) (sumKey N)) (fun j : {i // i ∈ pairVerts φ} => Z j) =
      pairRestrict φ :=
  funext fun i => Subtype.ext
    (nnMap_subtype_val (p := (· ∈ pairVerts φ)) hφ (fun _ hi => apply_mem_pairVerts hi) i)

omit [Fintype {i // p i}] [Nontrivial {i // p i}] in
/-- **Restricted graphs** (source l. 1546, `γ²`): the nearest-neighbour map of `Z|_{Iᶜ}` is the
restriction of `φ₁(Z)` to the complement of `I^pair`. -/
theorem nnMap_complRestrict (hφ : nearestNeighbor Z = φ) [Nontrivial {i // i ∉ pairVerts φ}] :
    nnMap (subtypeKey (· ∉ pairVerts φ) (sumKey N)) (fun j : {i // i ∉ pairVerts φ} => Z j) =
      complRestrict φ :=
  funext fun i => Subtype.ext
    (nnMap_subtype_val (p := (· ∉ pairVerts φ)) hφ (fun _ hi => apply_not_mem_pairVerts hi) i)

omit [Fintype {i // p i}] [Nontrivial {i // p i}] in
/-- `F^nn(Z) = F^nn(Z|_I) + F^nn(Z|_{Iᶜ})`: each vertex has its nearest neighbour in its own block
(isolated pairs are mutual nearest neighbours, and no other vertex points into them). -/
theorem neg_half_sum_smearedKernel_eq (hφ : nearestNeighbor Z = φ) (lam : ℝ)
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}] :
    -(1 / 2) * ∑ i, smearedKernel lam (Z i - Z (nearestNeighbor Z i)) =
      nnEnergy (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam (fun j : {i // i ∈ pairVerts φ} => Z j)
        + nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
          (fun j : {i // i ∉ pairVerts φ} => Z j) := by
  classical
  unfold nnEnergy
  rw [← Finset.sum_add_sum_compl (pairVerts φ),
    Finset.sum_subtype (pairVerts φ) (p := (· ∈ pairVerts φ)) (fun _ => Iff.rfl),
    Finset.sum_subtype (pairVerts φ)ᶜ (p := (· ∉ pairVerts φ)) (fun _ => mem_compl)]
  have h1 : ∀ i : {i // i ∈ pairVerts φ},
      smearedKernel lam (Z i - Z (nearestNeighbor Z i)) =
        smearedKernel lam (Z i - Z (nnMap (subtypeKey (· ∈ pairVerts φ) (sumKey N))
          (fun j : {i // i ∈ pairVerts φ} => Z j) i).1) := by
    intro i
    rw [nnMap_subtype_val (p := (· ∈ pairVerts φ)) hφ (fun _ hi => apply_mem_pairVerts hi) i, hφ]
  have h2 : ∀ i : {i // i ∉ pairVerts φ},
      smearedKernel lam (Z i - Z (nearestNeighbor Z i)) =
        smearedKernel lam (Z i - Z (nnMap (subtypeKey (· ∉ pairVerts φ) (sumKey N))
          (fun j : {i // i ∉ pairVerts φ} => Z j) i).1) := by
    intro i
    rw [nnMap_subtype_val (p := (· ∉ pairVerts φ)) hφ (fun _ hi => apply_not_mem_pairVerts hi) i,
      hφ]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_congr rfl fun i _ => h2 i]
  ring

end Restriction

/-! ### Measurability of `F⁽¹⁾` and `F⁽²⁾` -/

section Measurability

variable {ι : Type*} [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ)

/-- A function of the configuration that depends on it through its nearest-neighbour map and,
for each fixed map, measurably, is measurable. -/
theorem measurable_of_nnMap {γ : Type*} [MeasurableSpace γ] {F : (ι → ι) → (ι → ℂ) → γ}
    (hF : ∀ f, Measurable (F f)) : Measurable fun z => F (nnMap key z) z := by
  classical
  let _ : MeasurableSpace (ι → ι) := ⊤
  have _ : MeasurableSingletonClass (ι → ι) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have h1 : Measurable fun z : ι → ℂ => nnMap key z := by
    refine measurable_to_countable' fun f => ?_
    have hset : (fun z : ι → ℂ => nnMap key z) ⁻¹' {f} = ⋂ i, {z | nnMap key z i = f i} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq,
        funext_iff]
    rw [hset]
    exact MeasurableSet.iInter fun i => measurableSet_nnMap_eq key i (f i)
  have h2 : Measurable fun q : (ι → ℂ) × (ι → ι) => F q.2 q.1 :=
    measurable_from_prod_countable_left fun f => hF f
  exact h2.comp (measurable_id.prodMk h1)

/-- The second-neighbour radius `r̃₂` is a measurable function of the configuration. -/
theorem measurable_nnRadius2 (h3 : 3 ≤ Fintype.card ι) (lam : ℝ) (i : ι) :
    Measurable fun z : ι → ℂ => nnRadius2 h3 key lam z i := by
  classical
  refine measurable_of_nnMap key (F := fun f z => max (((Finset.univ.erase i).erase (f i)).inf'
    (erase_erase_nonempty h3 i (f i)) (fun j => ‖z i - z j‖) / 4) lam) fun f => ?_
  have h : Measurable (((Finset.univ.erase i).erase (f i)).inf' (erase_erase_nonempty h3 i (f i))
      fun (j : ι) (z : ι → ℂ) => ‖z i - z j‖) :=
    Finset.inf'_induction (erase_erase_nonempty h3 i (f i)) _ (fun f hf g hg => hf.inf hg)
      fun j _ => by fun_prop
  have h' : Measurable fun z : ι → ℂ => ((Finset.univ.erase i).erase (f i)).inf'
      (erase_erase_nonempty h3 i (f i)) (fun j => ‖z i - z j‖) := by
    convert h using 1
    ext z
    rw [Finset.inf'_apply]
  exact Measurable.max (h'.div_const _) measurable_const

theorem measurable_apply_nnMap (i : ι) : Measurable fun z : ι → ℂ => z (nnMap key z i) :=
  measurable_of_nnMap key (F := fun f z => z (f i)) fun f => measurable_pi_apply (f i)

/-- The nearest-neighbour energy `F^nn` is a measurable function of the configuration. -/
theorem measurable_nnEnergy (lam : ℝ) : Measurable fun z : ι → ℂ => nnEnergy key lam z := by
  unfold nnEnergy
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  exact (measurable_smearedKernel lam).comp
    ((measurable_pi_apply i).sub (measurable_apply_nnMap key i))

/-- The pair-assigned energy is a measurable function of the configuration. -/
theorem measurable_pairAssignedEnergy (h3 : 3 ≤ Fintype.card ι) (lam C : ℝ) (S : Finset ι) :
    Measurable fun z : ι → ℂ => pairAssignedEnergy h3 key lam C S z := by
  classical
  have hr2 : ∀ i, Measurable fun z : ι → ℂ => nnRadius2 h3 key lam z (nnMap key z i) := fun i =>
    measurable_of_nnMap key (F := fun f z => nnRadius2 h3 key lam z (f i)) fun f =>
      measurable_nnRadius2 key h3 lam (f i)
  unfold pairAssignedEnergy
  refine ((measurable_nnEnergy key lam).add (Finset.measurable_sum _ fun i _ => ?_)).sub
    (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_))
  · exact ((((measurable_nnRadius2 key h3 lam i).min (hr2 i)).div
      (measurable_nnRadius lam i)).log).sub measurable_const
  · exact ((measurable_nnRadius lam i).div (measurable_nnRadius2 key h3 lam i)).pow_const 2

omit [Fintype ι] [Nontrivial ι] in
/-- The Boltzmann factor `e^{-β F}` of a measurable energy is measurable. -/
theorem measurable_ofReal_exp_neg_mul {F : (ι → ℂ) → ℝ} (hF : Measurable F) (β : ℝ) :
    Measurable fun z => ENNReal.ofReal (Real.exp (-β * F z)) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hF))

end Measurability

/-! ### Bookkeeping -/

section Bookkeeping

variable {N : ℕ} {hN : 2 ≤ N} {Z : Fin N ⊕ Fin N → ℂ} {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
  {T : Finset (Fin N ⊕ Fin N)}

/-- `γ¹` has no fixed point: it is a perfect matching of the `m` isolated pairs. -/
theorem pairRestrict_ne_of_nearestNeighbor (hφ : nearestNeighbor Z = φ)
    (i : {i // i ∈ pairVerts φ}) : pairRestrict φ i ≠ i :=
  pairRestrict_ne (fun j => hφ ▸ nearestNeighbor_ne Z j) i

/-- `γ²` has no fixed point. -/
theorem complRestrict_ne_of_nearestNeighbor (hφ : nearestNeighbor Z = φ)
    (i : {i // i ∉ pairVerts φ}) : complRestrict φ i ≠ i := by
  intro h
  have h' := congrArg Subtype.val h
  rw [complRestrict_val] at h'
  exact nearestNeighbor_ne Z i (hφ ▸ h')

/-- `|I| = 2m`. -/
theorem card_pairVerts_subtype (hφ : nearestNeighbor Z = φ) [Fintype {i // i ∈ pairVerts φ}] :
    Fintype.card {i // i ∈ pairVerts φ} = 2 * numIsolatedPairs Z := by
  rw [Fintype.card_of_subtype (pairVerts φ) (fun _ => Iff.rfl), ← hφ,
    ← isolatedPairSet_eq_pairVerts, card_isolatedPairSet]

/-- `|Iᶜ| = 2(N - m)`. -/
theorem card_compl_pairVerts_subtype (hφ : nearestNeighbor Z = φ)
    [Fintype {i // i ∉ pairVerts φ}] :
    Fintype.card {i // i ∉ pairVerts φ} = 2 * (N - numIsolatedPairs Z) := by
  rw [Fintype.card_of_subtype (pairVerts φ)ᶜ (fun _ => mem_compl), ← hφ,
    ← isolatedPairSet_eq_pairVerts, card_compl_isolatedPairSet]

/-- The 2-cycle vertices of `γ²` are the 2-cycle vertices of `φ` outside `I`: there are
`2(K - m)` of them, so `γ²` has `K - m` components (source l. 1566). -/
theorem card_cycle_complRestrict (hφ : nearestNeighbor Z = φ)
    [Fintype {i : {i // i ∉ pairVerts φ} // complRestrict φ (complRestrict φ i) = i}] :
    Fintype.card {i : {i // i ∉ pairVerts φ} // complRestrict φ (complRestrict φ i) = i} =
      2 * (numComponents Z - numIsolatedPairs Z) := by
  classical
  have e : {i : {i // i ∉ pairVerts φ} // complRestrict φ (complRestrict φ i) = i} ≃
      {i // i ∉ pairVerts φ ∧ φ (φ i) = i} :=
    (Equiv.subtypeEquivRight fun i => by
      rw [Subtype.ext_iff, complRestrict_val, complRestrict_val]).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (· ∉ pairVerts φ) fun i => φ (φ i) = i)
  rw [Fintype.card_congr e, Fintype.card_of_subtype (cycleVerts Z \ isolatedPairSet Z) ?_,
    card_sdiff_of_subset isolatedPairSet_subset_cycleVerts,
    card_cycleVerts_eq_two_mul_numComponents, card_isolatedPairSet]
  · omega
  · intro i
    rw [mem_sdiff, mem_cycleVerts, isolatedPairSet_eq_pairVerts, hφ]
    exact and_comm

/-- `I'` is a union of pairs of `γ¹`. -/
theorem pairRestrict_mem_markedSameSignIn (hφ : nearestNeighbor Z = φ)
    (hT : twiceIsolatedSet hN Z = T) {i : {i // i ∈ pairVerts φ}}
    (hi : i ∈ markedSameSignIn φ T) : pairRestrict φ i ∈ markedSameSignIn φ T := by
  subst hφ hT
  rw [mem_markedSameSignIn] at hi ⊢
  rw [pairRestrict_val]
  refine ⟨nearestNeighbor_mem_twiceIsolatedSet hi.1, ?_⟩
  rw [nearestNeighbor_nearestNeighbor_of_mem_twiceIsolatedSet hi.1, mul_comm]
  exact hi.2

/-- `|I'| = 2(p - p₀)`. -/
theorem card_markedSameSignIn (hφ : nearestNeighbor Z = φ) (hT : twiceIsolatedSet hN Z = T) :
    (markedSameSignIn φ T).card =
      2 * (numTwiceIsolated hN Z - numNeutralTwiceIsolated hN Z) := by
  classical
  subst hφ hT
  have h1 : (markedSameSignIn (nearestNeighbor Z) (twiceIsolatedSet hN Z)).card =
      (markedSameSign (nearestNeighbor Z) (twiceIsolatedSet hN Z)).card := by
    unfold markedSameSignIn
    rw [card_subtype, filter_true_of_mem fun x hx =>
      (isolatedPairSet_eq_pairVerts Z) ▸ twiceIsolatedSet_subset_isolatedPairSet hN Z
        (mem_markedSameSign.1 hx).1]
  have h2 := card_filter_add_card_filter_not (s := twiceIsolatedSet hN Z)
    (fun i => charge i * charge (nearestNeighbor Z i) = -1)
  have h3 : (twiceIsolatedSet hN Z).filter
      (fun i => charge i * charge (nearestNeighbor Z i) = -1) = neutralTwiceIsolatedSet hN Z :=
    (neutralTwiceIsolatedSet_eq_filter hN Z).symm
  have h4 : (twiceIsolatedSet hN Z).filter
      (fun i => ¬ charge i * charge (nearestNeighbor Z i) = -1) =
      markedSameSign (nearestNeighbor Z) (twiceIsolatedSet hN Z) := by
    ext i
    rw [mem_filter, mem_markedSameSign]
  rw [h3, h4, card_neutralTwiceIsolatedSet, card_twiceIsolatedSet] at h2
  rw [h1]
  omega

/-- There is no marked pair when `m ≤ 1`: a twice-isolated vertex `i`, its partner `φ₁ i` and its
second nearest neighbour `φ₂ i` are three distinct vertices of `I^pair`. -/
theorem twiceIsolatedSet_eq_empty_of_numIsolatedPairs_le_one (hN : 2 ≤ N)
    (h : numIsolatedPairs Z ≤ 1) : twiceIsolatedSet hN Z = ∅ := by
  classical
  refine eq_empty_of_forall_notMem fun i hi => ?_
  have hT := (mem_twiceIsolatedSet hN Z).1 hi
  have hsub : ({i, nearestNeighbor Z i, secondNearestNeighbor hN Z i} : Finset _) ⊆
      isolatedPairSet Z := by
    intro j hj
    rw [mem_insert, mem_insert, mem_singleton] at hj
    rw [mem_isolatedPairSet]
    rcases hj with rfl | rfl | rfl
    · exact hT.1
    · exact isIsolatedPair_nearestNeighbor hT.1
    · exact hT.2.1
  have h3 : ({i, nearestNeighbor Z i, secondNearestNeighbor hN Z i} : Finset _).card = 3 :=
    card_eq_three.2 ⟨_, _, _, (nearestNeighbor_ne Z i).symm,
      (secondNearestNeighbor_ne_self hN Z i).symm,
      (secondNearestNeighbor_ne_nearestNeighbor hN Z i).symm, rfl⟩
  have h4 := card_le_card hsub
  rw [h3, card_isolatedPairSet] at h4
  omega

end Bookkeeping

end TwoComponentCoulomb

end
