/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TwoComponentCoulomb.Frozen.IsGeneric

/-!
# Non-generic configurations form a null set

Source: l. 202 and l. 351 ("We exclude the Lebesgue null set"): the set of
configurations `Z : Fin N ⊕ Fin N → ℂ` that are not `IsGeneric` (two coinciding points, or two
distinct unordered pairs of points at the same distance) has Lebesgue measure zero.

The argument is carried out for an arbitrary finite index type `ι`, so that it also applies to
sub-configurations.

* `volume_eq_zero_of_slice` : if every one-coordinate slice of a measurable `S ⊆ (ι → ℂ)` is
  null, then so is `S` (Fubini along one coordinate).
* `volume_setOf_apply_eq_apply` : `{z | z i = z j}` is null for `i ≠ j`.
* `volume_setOf_norm_sub_eq_norm_sub` : `{z | ‖z i - z j‖ = ‖z k - z l‖}` is null for
  `i ≠ j`, `k ≠ l` and distinct unordered pairs.
* `volume_setOf_not_injective`, `volume_setOf_exists_norm_sub_eq_norm_sub` : the two families of
  bad sets are null.
* `measurableSet_isGeneric` : `{Z | IsGeneric Z}` is measurable.
* `volume_not_isGeneric`, `ae_isGeneric`, `ae_restrict_isGeneric`,
  `ae_isGeneric_of_absolutelyContinuous`, `restrict_isGeneric_eq`, `restrict_inter_isGeneric_eq`,
  `lintegral_restrict_inter_isGeneric` : the almost-everywhere and integral forms.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### Slicing along one coordinate -/

section Slice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A measurable set `S ⊆ (ι → ℂ)` all of whose one-coordinate slices
`{w | Function.update z a w ∈ S}` (through any `z`) are Lebesgue-null is itself null. -/
theorem volume_eq_zero_of_slice (a : ι) {S : Set (ι → ℂ)} (hS : MeasurableSet S)
    (h : ∀ z : ι → ℂ, volume {w : ℂ | Function.update z a w ∈ S} = 0) : volume S = 0 := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i = a)
  have he := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i = a)
  have hT : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable hS
  have hS' : S = e ⁻¹' (e.symm ⁻¹' S) := by
    ext z; simp
  rw [hS', he.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_apply_symm hT]
  refine (lintegral_congr fun y => ?_).trans lintegral_zero
  let z : ι → ℂ := e.symm (0, y)
  have hset : (fun x : {i // i = a} → ℂ => (x, y)) ⁻¹' (e.symm ⁻¹' S) =
      (MeasurableEquiv.funUnique {i // i = a} ℂ) ⁻¹' {w : ℂ | Function.update z a w ∈ S} := by
    ext x
    have : e.symm (x, y) = Function.update z a (MeasurableEquiv.funUnique {i // i = a} ℂ x) := by
      funext i
      by_cases hi : i = a
      · subst hi
        simp only [e, z, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, Function.update_self,
          MeasurableEquiv.funUnique]
        simp
        exact congrArg x (Subsingleton.elim _ _)
      · simp [e, z, hi, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
    change e.symm (x, y) ∈ S ↔ Function.update z a (MeasurableEquiv.funUnique {i // i = a} ℂ x) ∈ S
    rw [this]
  rw [hset]
  convert ((volume_preserving_funUnique {i // i = a} ℂ).measure_preimage_equiv _).trans (h z)

end Slice

/-! ### The bad sets for a finite index type -/

section BadSets

variable {ι : Type*} [Fintype ι]

/-- Two distinct coordinates coincide only on a null set. -/
theorem volume_setOf_apply_eq_apply {i j : ι} (hij : i ≠ j) :
    volume {z : ι → ℂ | z i = z j} = 0 := by
  classical
  refine volume_eq_zero_of_slice i (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet
    fun z => ?_
  have : {w : ℂ | Function.update z i w i = Function.update z i w j} = {z j} := by
    ext w
    simp [Function.update_of_ne hij.symm]
  change volume {w : ℂ | Function.update z i w i = Function.update z i w j} = 0
  rw [this]
  exact measure_singleton _

/-- If the coordinate `i` is distinct from `j`, `k` and `l`, the set where `‖z i - z j‖` equals
`‖z k - z l‖` is null: in the coordinate `i` it is a circle. -/
theorem volume_setOf_norm_sub_eq_norm_sub_of_ne {i j k l : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) : volume {z : ι → ℂ | ‖z i - z j‖ = ‖z k - z l‖} = 0 := by
  classical
  refine volume_eq_zero_of_slice i (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet
    fun z => ?_
  refine measure_mono_null ?_ (Measure.addHaar_sphere volume (z j) ‖z k - z l‖)
  intro w hw
  simp only [Set.mem_ofPred_eq, Function.update_self, Function.update_of_ne hij.symm,
    Function.update_of_ne hik.symm, Function.update_of_ne hil.symm] at hw
  simpa [Metric.mem_sphere, dist_eq_norm] using hw

/-- Two distinct unordered pairs of coordinates are at the same distance only on a null set. -/
theorem volume_setOf_norm_sub_eq_norm_sub {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ¬((i = k ∧ j = l) ∨ (i = l ∧ j = k))) :
    volume {z : ι → ℂ | ‖z i - z j‖ = ‖z k - z l‖} = 0 := by
  by_cases hi : i = k ∨ i = l
  · by_cases hj : j = k ∨ j = l
    · exfalso
      refine hne ?_
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact (hij rfl).elim
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact (hij rfl).elim
    · obtain ⟨hjk, hjl⟩ := not_or.1 hj
      have := volume_setOf_norm_sub_eq_norm_sub_of_ne (i := j) (j := i) hij.symm hjk hjl
      simpa only [norm_sub_rev (_ : ℂ) _] using this
  · obtain ⟨hik, hil⟩ := not_or.1 hi
    exact volume_setOf_norm_sub_eq_norm_sub_of_ne hij hik hil

/-- A finite configuration has two coinciding points only on a null set. -/
theorem volume_setOf_not_injective : volume {z : ι → ℂ | ¬ Function.Injective z} = 0 := by
  have hsub : {z : ι → ℂ | ¬ Function.Injective z} ⊆
      ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {z : ι → ℂ | z i = z j} := by
    intro z hz
    have : ∃ i j, z i = z j ∧ i ≠ j := by
      by_contra hcon
      exact hz fun i j hij => by_contra fun hne => hcon ⟨i, j, hij, hne⟩
    obtain ⟨i, j, hzij, hij⟩ := this
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hij, hzij⟩⟩⟩
  exact measure_mono_null hsub <| measure_iUnion_null fun i => measure_iUnion_null fun j =>
    measure_iUnion_null fun hij => volume_setOf_apply_eq_apply hij

/-- A finite configuration has two distinct unordered pairs of points at the same distance only on
a null set. -/
theorem volume_setOf_exists_norm_sub_eq_norm_sub :
    volume {z : ι → ℂ | ∃ i j k l, i ≠ j ∧ k ≠ l ∧ ¬((i = k ∧ j = l) ∨ (i = l ∧ j = k)) ∧
      ‖z i - z j‖ = ‖z k - z l‖} = 0 := by
  have hsub : {z : ι → ℂ | ∃ i j k l, i ≠ j ∧ k ≠ l ∧ ¬((i = k ∧ j = l) ∨ (i = l ∧ j = k)) ∧
      ‖z i - z j‖ = ‖z k - z l‖} ⊆
      ⋃ i, ⋃ j, ⋃ k, ⋃ l, ⋃ (_ : i ≠ j ∧ k ≠ l ∧ ¬((i = k ∧ j = l) ∨ (i = l ∧ j = k))),
        {z : ι → ℂ | ‖z i - z j‖ = ‖z k - z l‖} := by
    rintro z ⟨i, j, k, l, hij, hkl, hne, hz⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2
      ⟨l, Set.mem_iUnion.2 ⟨⟨hij, hkl, hne⟩, hz⟩⟩⟩⟩⟩
  exact measure_mono_null hsub <| measure_iUnion_null fun i => measure_iUnion_null fun j =>
    measure_iUnion_null fun k => measure_iUnion_null fun l =>
      measure_iUnion_null fun h => volume_setOf_norm_sub_eq_norm_sub h.1 h.2.1 h.2.2

end BadSets

/-! ### Generic configurations -/

section Generic

variable {N : ℕ}

/-- The set of generic configurations is measurable. -/
theorem measurableSet_isGeneric : MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | IsGeneric Z} := by
  refine measurableSet_setOfPred.2 ?_
  unfold IsGeneric Function.Injective
  fun_prop

/-- The non-generic configurations form a Lebesgue-null set (source l. 202 and l. 351). -/
theorem volume_not_isGeneric :
    volume {Z : Fin N ⊕ Fin N → ℂ | ¬ IsGeneric Z} = 0 := by
  have hsub : {Z : Fin N ⊕ Fin N → ℂ | ¬ IsGeneric Z} ⊆
      {Z : Fin N ⊕ Fin N → ℂ | ¬ Function.Injective Z} ∪
        {Z : Fin N ⊕ Fin N → ℂ | ∃ i j k l, i ≠ j ∧ k ≠ l ∧
          ¬((i = k ∧ j = l) ∨ (i = l ∧ j = k)) ∧ ‖Z i - Z j‖ = ‖Z k - Z l‖} := by
    intro Z hZ
    by_cases hinj : Function.Injective Z
    · refine Or.inr ?_
      by_contra hcon
      exact hZ ⟨hinj, fun i j k l hij hkl hnorm =>
        by_contra fun hne => hcon ⟨i, j, k, l, hij, hkl, hne, hnorm⟩⟩
    · exact Or.inl hinj
  exact measure_mono_null hsub
    (measure_union_null volume_setOf_not_injective volume_setOf_exists_norm_sub_eq_norm_sub)

/-- Lebesgue-almost every configuration is generic. -/
theorem ae_isGeneric : ∀ᵐ Z ∂(volume : Measure (Fin N ⊕ Fin N → ℂ)), IsGeneric Z :=
  ae_iff.2 volume_not_isGeneric

/-- Almost-everywhere genericity, for Lebesgue measure restricted to any set. -/
theorem ae_restrict_isGeneric (S : Set (Fin N ⊕ Fin N → ℂ)) :
    ∀ᵐ Z ∂(volume : Measure (Fin N ⊕ Fin N → ℂ)).restrict S, IsGeneric Z :=
  ae_restrict_of_ae ae_isGeneric

/-- Almost-everywhere genericity, for any measure absolutely continuous with respect to
Lebesgue measure (for instance the Gibbs measure and its unnormalised version). -/
theorem ae_isGeneric_of_absolutelyContinuous {μ : Measure (Fin N ⊕ Fin N → ℂ)}
    (hμ : μ ≪ volume) : ∀ᵐ Z ∂μ, IsGeneric Z :=
  hμ.ae_le ae_isGeneric

/-- Restricting Lebesgue measure to the generic configurations changes nothing. -/
theorem restrict_isGeneric_eq :
    (volume : Measure (Fin N ⊕ Fin N → ℂ)).restrict {Z | IsGeneric Z} = volume :=
  Measure.restrict_eq_self_of_ae_mem ae_isGeneric

/-- Intersecting the domain with the generic configurations does not change the restriction of
Lebesgue measure. -/
theorem restrict_inter_isGeneric_eq (S : Set (Fin N ⊕ Fin N → ℂ)) :
    (volume : Measure (Fin N ⊕ Fin N → ℂ)).restrict (S ∩ {Z | IsGeneric Z}) =
      volume.restrict S := by
  rw [Set.inter_comm, ← Measure.restrict_restrict measurableSet_isGeneric]
  exact Measure.restrict_eq_self_of_ae_mem (ae_restrict_isGeneric S)

/-- Integrals over a set of Lebesgue measure may be restricted to the generic configurations. -/
theorem lintegral_restrict_inter_isGeneric (S : Set (Fin N ⊕ Fin N → ℂ))
    (f : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) :
    ∫⁻ Z in S, f Z = ∫⁻ Z in S ∩ {Z | IsGeneric Z}, f Z := by
  rw [restrict_inter_isGeneric_eq]

end Generic

end TwoComponentCoulomb

end
