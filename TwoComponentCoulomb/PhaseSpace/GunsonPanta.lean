/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Nilpotent.Basic
public import TwoComponentCoulomb.NearestNeighbor.GeneralStructure

/-!
# The Gunson--Panta map

Source l. 641--658 (definition of the Gunson--Panta change of variables `Φ^GP_p`) and l. 822--826
(its unit Jacobian on a nearest-neighbour cell). Fix a finite index type `ι`, a self-map
`f : ι → ι` (the nearest-neighbour map of a configuration) and a set `R ⊆ ι` of *reference
vertices* (one vertex of each 2-cycle of `f`; the source calls them `m_k'`). The Gunson--Panta map
is the `ℝ`-linear map of `ι → ℂ` given by
`(GP z)_i = z_i` for `i ∈ R` and `(GP z)_i = z_i - z_{f i}` for `i ∉ R`.

The source performs the change of variables `Z ↦ U = Φ^GP(Z)` without proving that it is
injective with unit Jacobian. It is: if every `f`-orbit reaches `R`, then `GP = 1 - N` where
`(N z)_i = 0` for `i ∈ R` and `(N z)_i = z_{f i}` for `i ∉ R` is nilpotent, so `GP` is invertible
with determinant `1` (`det (1 - N) = χ_N(1) = 1`), hence preserves Lebesgue measure.

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

/-- The **Gunson--Panta map** (source l. 641--658): `(GP z)_i = z_i` for a reference vertex
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

/-- The nilpotent part of the Gunson--Panta map: `(N z)_i = 0` for `i ∈ R` and
`(N z)_i = z_{f i}` otherwise, so that `gpMap f R = 1 - gpNil f R`. -/
def gpNil : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) where
  toFun z i := if i ∈ R then 0 else z (f i)
  map_add' z w := by
    funext i
    by_cases h : i ∈ R <;> simp [h]
  map_smul' c z := by
    funext i
    by_cases h : i ∈ R <;> simp [h]

theorem gpMap_eq_one_sub_gpNil : gpMap f R = 1 - gpNil f R := by
  refine LinearMap.ext fun z => funext fun i => ?_
  by_cases h : i ∈ R <;> simp [gpMap, gpNil, h]

/-- Powers of the nilpotent part: `(N^k z)_i = z_{f^k i}` provided the first `k` points of the
orbit of `i` are not reference vertices, and `0` otherwise. -/
theorem gpNil_pow_apply (k : ℕ) (z : ι → ℂ) (i : ι) :
    ((gpNil f R) ^ k) z i = if ∀ j < k, f^[j] i ∉ R then z (f^[k] i) else 0 := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    have hN : ∀ (w : ι → ℂ) (j : ι), gpNil f R w j = if j ∈ R then 0 else w (f j) :=
      fun _ _ => rfl
    rw [pow_succ', Module.End.mul_apply, hN]
    by_cases hi : i ∈ R
    · rw [ite_eq_left hi, ite_eq_right]
      exact fun h => h 0 (Nat.succ_pos k) hi
    · rw [ite_eq_right hi, ih (f i)]
      have hiff : (∀ j < k + 1, f^[j] i ∉ R) ↔ ∀ j < k, f^[j] (f i) ∉ R := by
        rw [Nat.forall_lt_succ_left]
        simp [hi, Function.iterate_succ_apply]
      by_cases h : ∀ j < k, f^[j] (f i) ∉ R
      · rw [ite_eq_left h, ite_eq_left (hiff.2 h), Function.iterate_succ_apply]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.1 h'))]

variable [Fintype ι]

/-- If every `f`-orbit reaches `R`, the nilpotent part `gpNil f R` is nilpotent. -/
theorem isNilpotent_gpNil (hR : ∀ i, ∃ n, f^[n] i ∈ R) : IsNilpotent (gpNil f R) := by
  choose n hn using hR
  refine ⟨Finset.univ.sup n + 1, LinearMap.ext fun z => funext fun i => ?_⟩
  rw [gpNil_pow_apply]
  have hlt : n i < Finset.univ.sup n + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := n) (Finset.mem_univ i))
  have : ¬ ∀ j < Finset.univ.sup n + 1, f^[j] i ∉ R := fun h => h (n i) hlt (hn i)
  rw [ite_eq_right this]
  rfl

/-- The Gunson--Panta map is bijective as soon as every `f`-orbit reaches `R`
(source l. 822--826, "injective on the cell"). -/
theorem gpMap_bijective (hR : ∀ i, ∃ n, f^[n] i ∈ R) : Function.Bijective (gpMap f R) := by
  have h : IsUnit (gpMap f R) := by
    rw [gpMap_eq_one_sub_gpNil]
    exact (isNilpotent_gpNil f R hR).isUnit_one_sub
  exact (Module.End.isUnit_iff _).1 h

/-- The Gunson--Panta map has determinant `1` (source l. 822--826, "unit Jacobian"). -/
theorem det_gpMap (hR : ∀ i, ∃ n, f^[n] i ∈ R) : LinearMap.det (gpMap f R) = 1 := by
  have h := LinearMap.eval_charpoly (gpNil f R) 1
  rw [(isNilpotent_gpNil f R hR).charpoly_eq_X_pow_finrank] at h
  rw [gpMap_eq_one_sub_gpNil]
  simpa using h.symm

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
(these are the vertices `m_k'` of source l. 641--658 that keep their absolute coordinate). -/
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
