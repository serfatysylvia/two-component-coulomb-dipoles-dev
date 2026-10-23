/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TwoComponentCoulomb.NearestNeighbor.GeneralStructure

/-!
# The Gunson--Panta map

Source l. 657–671 (definition of the Gunson--Panta change of variables `Φ^GP_p`) and l. 740–743
(its unit Jacobian on a nearest-neighbour cell). Fix a finite index type `ι`, a self-map
`f : ι → ι` (the nearest-neighbour map of a configuration) and a set `R ⊆ ι` of *reference
vertices* (one vertex of each 2-cycle of `f`; the source calls them m′ₖ). The Gunson--Panta map
is the `ℝ`-linear map of `ι → ℂ` given by
`(GP z)_i = z_i` for `i ∈ R` and `(GP z)_i = z_i - z_{f i}` for `i ∉ R`.

The paper, Section 3.1, orders parents before children after removing the
outgoing edges of reference vertices. We use the first hitting time of the reference set as
the depth of a vertex. The matrix is block triangular in this depth order, with identity
diagonal blocks. Its determinant is therefore one, so the map is invertible and preserves
Lebesgue measure.

## Main definitions and results

* `TwoComponentCoulomb.gpMap f R`: the Gunson--Panta map, with `gpMap_apply_of_mem` and
  `gpMap_apply_of_not_mem`.
* `TwoComponentCoulomb.gpMap_bijective`, `TwoComponentCoulomb.det_gpMap`,
  `TwoComponentCoulomb.measurePreserving_gpMap`: invertibility, determinant `1`, and measure
  preservation, under the hypothesis `∀ i, ∃ n, f^[n] i ∈ R`.
* `TwoComponentCoulomb.gpLinearEquiv f R hR`: the resulting linear equivalence; its inverse is
  computed by `gpLinearEquiv_symm_apply_of_not_mem` (and `z_i = u_i` on reference vertices)
  (`z_i = u_i + z_{f i}`, i.e. descending the tree towards the reference vertices).
* `TwoComponentCoulomb.gpRefSet key f`: the reference set `{i | f (f i) = i ∧ key i < key (f i)}`
  consisting of the smaller-key vertex of each 2-cycle; for `f = nnMap key z` it meets every orbit
  (`TwoComponentCoulomb.exists_iterate_nnMap_mem_gpRefSet`) and exactly one vertex of each
  2-cycle.
-/

@[expose] public section

namespace TwoComponentCoulomb

open MeasureTheory Function

section Definition

variable {ι : Type*} (f : ι → ι) (R : Set ι) [DecidablePred (· ∈ R)]

/-- The **Gunson--Panta map** (source l. 645–660): `(GP z)_i = z_i` for a reference vertex
`i ∈ R` and `(GP z)_i = z_i - z_{f i}` otherwise. -/
def gpMap : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) where
  toFun z i := if i ∈ R then z i else z i - z (f i)
  map_add' z w := by
    funext i
    by_cases h : i ∈ R
    · simp [h]
    · simp only [h, ite_false, Pi.add_apply]
      ring
  map_smul' c z := by
    funext i
    by_cases h : i ∈ R
    · simp [h]
    · simp [h, smul_sub]

variable {f R}

theorem gpMap_apply_of_mem (z : ι → ℂ) {i : ι} (hi : i ∈ R) : gpMap f R z i = z i := by
  simp [gpMap, hi]

theorem gpMap_apply_of_not_mem (z : ι → ℂ) {i : ι} (hi : i ∉ R) :
    gpMap f R z i = z i - z (f i) := by
  simp [gpMap, hi]

variable (f R)

variable [Fintype ι]

omit [Fintype ι] in
/-- A parent has smaller depth than a nonreference child. Depth is the first time
its orbit reaches the reference set. -/
private theorem gp_parent_depth_lt (hR : ∀ i, ∃ n, f^[n] i ∈ R) {i : ι} (hi : i ∉ R) :
    Nat.find (hR (f i)) < Nat.find (hR i) := by
  have hzero : Nat.find (hR i) ≠ 0 := by
    intro h
    have hmem := Nat.find_spec (hR i)
    rw [h, Function.iterate_zero_apply] at hmem
    exact hi hmem
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  have hmem : f^[n] (f i) ∈ R := by
    rw [← Function.iterate_succ_apply, ← hn]
    exact Nat.find_spec (hR i)
  have hle := Nat.find_min' (hR (f i)) hmem
  omega

/-- The Gunson--Panta map has determinant `1`: ordering the rooted forest by depth
makes the matrix triangular with identity diagonal blocks (`source/dipole-formation.tex` l. 662). -/
theorem det_gpMap (hR : ∀ i, ∃ n, f^[n] i ∈ R) : LinearMap.det (gpMap f R) = 1 := by
  classical
  let b := Pi.basis (fun _ : ι => Complex.basisOneI)
  let M := LinearMap.toMatrix b b (gpMap f R)
  let depth : (Σ _ : ι, Fin 2) → ℕ := fun i => Nat.find (hR i.1)
  have hentry : ∀ i j, depth i ≤ depth j → M i j = (1 : Matrix _ _ ℝ) i j := by
    intro i j hij
    dsimp only [M]
    rw [LinearMap.toMatrix_apply, Pi.basis_repr]
    have hb : ∀ k, Complex.basisOneI.repr ((b j) k) =
        if k = j.1 then Finsupp.single j.2 1 else 0 := by
      intro k
      by_cases hk : k = j.1
      · simp only [b, Pi.basis_apply, Pi.single_apply, hk, ite_true, Module.Basis.repr_self]
      · simp only [b, Pi.basis_apply, Pi.single_apply, hk, ite_false, map_zero]
    by_cases hi : i.1 ∈ R
    · rw [gpMap_apply_of_mem _ hi, hb]
      by_cases hij' : i.1 = j.1 <;>
        simp [hij', Matrix.one_apply, Sigma.ext_iff, Finsupp.single_apply, eq_comm]
    · have hparent : f i.1 ≠ j.1 := by
        intro h
        have hlt := gp_parent_depth_lt f R hR hi
        change Nat.find (hR i.1) ≤ Nat.find (hR j.1) at hij
        rw [← h] at hij
        omega
      rw [gpMap_apply_of_not_mem _ hi, map_sub, hb, hb, ite_eq_right hparent, sub_zero]
      by_cases hij' : i.1 = j.1 <;>
        simp [hij', Matrix.one_apply, Sigma.ext_iff, Finsupp.single_apply, eq_comm]
  have htri : M.BlockTriangular (fun i => OrderDual.toDual (depth i)) := by
    intro i j hij
    have hlt : depth i < depth j := hij
    rw [hentry i j hlt.le, Matrix.one_apply_ne]
    intro heq
    subst j
    exact (lt_irrefl _ hlt)
  have hblocks : ∀ d, M.toSquareBlock (fun i => OrderDual.toDual (depth i)) d = 1 := by
    intro d
    ext i j
    change M i.1 j.1 = _
    rw [hentry i.1 j.1 (le_of_eq (i.2.trans j.2.symm))]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [← LinearMap.det_toMatrix b]
  change M.det = 1
  rw [htri.det]
  simp_rw [hblocks, Matrix.det_one]
  simp

/-- The Gunson--Panta map is bijective since its triangular matrix has determinant one. -/
theorem gpMap_bijective (hR : ∀ i, ∃ n, f^[n] i ∈ R) : Function.Bijective (gpMap f R) := by
  apply (Module.End.isUnit_iff _).1
  apply (LinearMap.isUnit_iff_isUnit_det _).2
  rw [det_gpMap f R hR]
  exact isUnit_one

/-- The Gunson--Panta map preserves Lebesgue measure on `ι → ℂ`. -/
theorem measurePreserving_gpMap (hR : ∀ i, ∃ n, f^[n] i ∈ R) :
    MeasurePreserving (gpMap f R) volume volume := by
  refine ⟨(gpMap f R).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (by rw [det_gpMap f R hR]; exact one_ne_zero), det_gpMap f R hR]
  simp

/-- The Gunson--Panta map as a linear equivalence of `ι → ℂ`. -/
noncomputable def gpLinearEquiv (hR : ∀ i, ∃ n, f^[n] i ∈ R) : (ι → ℂ) ≃ₗ[ℝ] (ι → ℂ) :=
  LinearEquiv.ofBijective (gpMap f R) (gpMap_bijective f R hR)

variable {f R}

theorem gpLinearEquiv_apply (hR : ∀ i, ∃ n, f^[n] i ∈ R) (z : ι → ℂ) :
    gpLinearEquiv f R hR z = gpMap f R z :=
  rfl

theorem measurePreserving_gpLinearEquiv (hR : ∀ i, ∃ n, f^[n] i ∈ R) :
    MeasurePreserving (gpLinearEquiv f R hR) volume volume :=
  measurePreserving_gpMap f R hR

theorem measurableEmbedding_gpLinearEquiv (hR : ∀ i, ∃ n, f^[n] i ∈ R) :
    MeasurableEmbedding (gpLinearEquiv f R hR) :=
  (gpLinearEquiv f R hR).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

/-- The inverse of the Gunson--Panta map away from the reference set: `z_i = u_i + z_{f i}`
(descending the tree towards the reference vertices). -/
theorem gpLinearEquiv_symm_apply_of_not_mem (hR : ∀ i, ∃ n, f^[n] i ∈ R) (u : ι → ℂ) {i : ι}
    (hi : i ∉ R) :
    (gpLinearEquiv f R hR).symm u i = u i + (gpLinearEquiv f R hR).symm u (f i) := by
  have h := congrFun ((gpLinearEquiv f R hR).apply_symm_apply u) i
  rw [gpLinearEquiv_apply, gpMap_apply_of_not_mem _ hi] at h
  rw [← h]
  ring

end Definition

section ReferenceSet

variable {ι : Type*} (key : ι ↪ ℕ)

/-- The **reference set** of a self-map `f` of the index set, relative to the tie-break key `key`:
the vertices `i` lying on a 2-cycle `{i, f i}` that have the smaller key of the two
(these are the vertices m′ₖ of source l. 645–660 that keep their absolute coordinate). -/
def gpRefSet (f : ι → ι) : Set ι :=
  {i | f (f i) = i ∧ key i < key (f i)}

open scoped Classical in
/-- Membership in `gpRefSet` is decidable (classically). -/
noncomputable instance (f : ι → ι) : DecidablePred (· ∈ gpRefSet key f) :=
  Classical.decPred _

variable {key}

/-- If `f` has no fixed point and every orbit reaches a 2-cycle, then every orbit reaches the
reference set. -/
theorem gpRefSet_reaches {f : ι → ι} (hf0 : ∀ i, f i ≠ i)
    (hf : ∀ i, ∃ n, f (f (f^[n] i)) = f^[n] i) (i : ι) : ∃ n, f^[n] i ∈ gpRefSet key f := by
  obtain ⟨m, hm⟩ := hf i
  by_cases hlt : key (f^[m] i) < key (f (f^[m] i))
  · exact ⟨m, hm, hlt⟩
  · refine ⟨m + 1, ?_⟩
    rw [Function.iterate_succ_apply']
    have hne : key (f (f^[m] i)) ≠ key (f^[m] i) := fun h => hf0 _ (key.injective h)
    refine ⟨by rw [hm], ?_⟩
    rw [hm]
    exact lt_of_le_of_ne (not_lt.1 hlt) hne

/-- The reference set contains exactly one vertex of each 2-cycle `{i, f i}` (`f i ≠ i`). -/
theorem gpRefSet_mem_iff_not_mem {f : ι → ι} {i : ι} (h2 : f (f i) = i) (h0 : f i ≠ i) :
    i ∈ gpRefSet key f ↔ f i ∉ gpRefSet key f := by
  have hne : key i ≠ key (f i) := fun h => h0 (key.injective h).symm
  simp only [gpRefSet, Set.mem_ofPred_eq, h2, true_and, not_lt]
  exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h hne⟩

end ReferenceSet

section NearestNeighbor

variable {ι : Type*} [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ)

/-- Every orbit of the nearest-neighbour map `nnMap key z` reaches its reference set. -/
theorem exists_iterate_nnMap_mem_gpRefSet (z : ι → ℂ) (i : ι) :
    ∃ n, (nnMap key z)^[n] i ∈ gpRefSet key (nnMap key z) :=
  gpRefSet_reaches (nnMap_ne key z)
    (fun i => (exists_iterate_nnMap_two_cycle key z i).imp fun _ h => h.2) i

end NearestNeighbor

end TwoComponentCoulomb

end
