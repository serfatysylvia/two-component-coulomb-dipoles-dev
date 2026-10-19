/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.ElectricLower
public import TwoComponentCoulomb.UpperBound.UpperAssembly
import TwoComponentCoulomb.Frozen.Proposition41
import TwoComponentCoulomb.Gibbs.Basic

/-!
# Theorem 2, Step 3: the exponential moment of `A₂` (eq. (eq:A2)), `β > 2`

Source: proof of Theorem 2 (`prop:linear`), l. 2117--2124: "To bound `A₂`, we repeat Steps 2
and 3 of Proposition 3.10 with a larger coefficient in the neutral quadratic term." For `β > 2`,
`N ≥ 2` and `λ` small,

`𝔼_ℙ[e^{A₂}] ≤ exp (C N ω_λ + C log (N+1))`,  `A₂ = linearA2`.

## Structure

The weight `e^{A₂ - β F_λ}` is bounded on the cell `{γ_{2N} = γ}` of a marked graph
`γ = (φ, T) ∈ D_{2N,K,p,p₀}` as in Steps 2--3 of the proof of Proposition 3.10
(`UpperBound/UpperAssembly.lean`), with the following changes.

* The quadratic sum of `A₂` runs over a subset of the marked neutral vertices, and with the
  constant `C' = C + 1/β` in place of `C` in `F⁽¹⁾` the extra quadratic energy `(1/β) ∑ (r̃₁/r̃₂)²`
  of `F⁽¹⁾_{C'}` absorbs it (`MomentA2.le_energy_split_add`, `MomentA2.le_energy_full_add`; the bridge from
  the global radii to the radii of the block `I` is `MomentA2.sum_dip_le_split`).
* The linear part `N - ½|I^dip|` of `A₂` is at most `(M₀ + 3)(N - K) + (p - p₀)` on the cell
  (l. 2118--2120, `MomentA2.deficit_le`). The part `(M₀ + 3)(N - K)` is absorbed in the per-cell
  constant `A`, and the part `(p - p₀)` is absorbed in the allowance `C₀ (p - p₀)` of
  (eq:representative-bound) (Proposition 3.9), taken with `C₀ = 61` instead of `C₀ = 60`
  (l. 2121).
* The per-cell bound `CellBoundRate` obtained this way (`MomentA2.exists_cellBound_energy_rate`)
  feeds the generic summation `UpperAssembly.lintegral_le_of_cellBound_rate`, and the division by
  `Z` is Proposition 4.1.

The bounds are stated for a rate function `ω` satisfying `UpperRateHyp` in place of `ω_λ`; the
rate `ω_λ = errorRate β λ` satisfies it (`upperRateHyp_errorRate`), and the instance is taken in
`momentBound_of_two_lt` (`Fluctuations/Moment.lean`).

## Main results

* `MomentA2.entropy_mul_le_main_sixty_one_rate`: (eq:F(1)) with the extra factor `e^{p - p₀}`.
* `MomentA2.exists_cellBound_energy_rate`: the per-cell bound `CellBoundRate` for the integrand
  `e^{A₂} e^{-β F_λ}`.
* `momentA2_le_rate` (eq:A2): `∫ e^{A₂} dℙ ≤ exp (C N ω(λ) + C log (N+1))`.
-/

@[expose] public section

namespace TwoComponentCoulomb

namespace MomentA2

open Finset MeasureTheory
open scoped ENNReal

variable {N : ℕ}

/-! ### The deficit `N - ½|I^dip|` (source l. 2118--2121) -/

open scoped Classical in
/-- **The deficit count** (source l. 2118--2121): on the cell of a marked graph of
`D_{2N,K,p,p₀}`, `N - ½|I^dip| ≤ N - p₀ ≤ (M₀ + 3)(N - K) + (p - p₀)`. -/
theorem deficit_le {hN : 2 ≤ N} {K p p₀ : ℕ} {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    {T : Finset (Fin N ⊕ Fin N)} (hγ : (φ, T) ∈ markedGraphs hN K p p₀)
    {Z : Fin N ⊕ Fin N → ℂ} (hZ : Z ∈ markedCell hN φ T) :
    (N : ℝ) - (1 / 2) * ((Finset.univ.filter (IsIsolatedDipole Z)).card : ℝ) ≤
      (M0 + 3) * ((N : ℝ) - K) + ((p : ℝ) - p₀) := by
  obtain ⟨hp₀p, hpK, hKN, hKp⟩ := UpperCellBound.constraints_of_nonempty ⟨_, hγ⟩
  have h1 := UpperAssembly.numNeutralTwiceIsolated_le_card_isolatedDipoles hN Z
  rw [numNeutralTwiceIsolated_eq_of_mem_markedCell hγ hZ] at h1
  have h2 : ((Finset.univ.filter (IsIsolatedDipole Z)).card : ℝ) =
      2 * ((isolatedDipoles Z).card : ℝ) := by
    rw [card_filter_isIsolatedDipole Z]
    push_cast
    rfl
  have h3 : (p₀ : ℝ) ≤ (isolatedDipoles Z).card := by exact_mod_cast h1
  rw [h2]
  linarith only [h3, hKp]

/-! ### The quadratic sum of `A₂` -/

open scoped Classical in
/-- The quadratic sum of `A₂` (source l. 2088):
`∑_{i ∈ I^dip, φ₂ i ∈ I^dip, φ₂ (φ₁ i) ∈ I^pair} (r̃₁(zᵢ) / r̃₂(zᵢ))²`. -/
noncomputable def dipSum (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
      IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
    (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2

open scoped Classical in
/-- `A₂ = (quadratic sum) + (N - ½ |I^dip|)`. -/
theorem linearA2_eq (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) :
    linearA2 hN lam Z = dipSum hN lam Z +
      ((N : ℝ) - (1 / 2) * ((Finset.univ.filter (IsIsolatedDipole Z)).card : ℝ)) :=
  rfl

/-! ### The quadratic sum of `A₂` is dominated by the neutral quadratic term of `F⁽¹⁾` -/

open scoped Classical in
/-- **The quadratic sum of `A₂` in the block `I`** (source l. 2117--2121): the indices of the sum
of `A₂` (`i ∈ I^dip`, `φ₂ i ∈ I^dip`, `φ₂ (φ₁ i) ∈ I^pair`) are marked neutral vertices, and for
them `r̃₁, r̃₂` computed within `I` are the global ones; hence the sum is at most the quadratic term
`∑_{i ∈ I ∖ I'} (r̃₁/r̃₂)²` of `F⁽¹⁾` (`pairAssignedEnergy`). -/
theorem sum_dip_le_split (hN : 2 ≤ N) (lam : ℝ) {Z : Fin N ⊕ Fin N → ℂ}
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hφ : nearestNeighbor Z = φ) (hT : twiceIsolatedSet hN Z = T)
    [Nontrivial {i // i ∈ pairVerts φ}] (h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts φ}) :
    dipSum hN lam Z ≤
      ∑ i ∈ (markedSameSignIn φ T)ᶜ,
        (nnRadius lam (fun j : {i // i ∈ pairVerts φ} => Z j) i /
          nnRadius2 h3 (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam
            (fun j : {i // i ∈ pairVerts φ} => Z j) i) ^ 2 := by
  classical
  subst hφ hT
  unfold dipSum
  set P := pairVerts (nearestNeighbor Z) with hPdef
  set key := subtypeKey (· ∈ P) (sumKey N) with hkey
  set z : {i // i ∈ P} → ℂ := fun j => Z j with hz
  have hp : ∀ i, i ∈ P → nearestNeighbor Z i ∈ P := fun _ hi => apply_mem_pairVerts hi
  set U := ((twiceIsolatedSet hN Z).filter
    fun i => charge i * charge (nearestNeighbor Z i) = -1).subtype (· ∈ P) with hU
  have hUS : ∀ i ∈ U, i ∉ markedSameSignIn (nearestNeighbor Z) (twiceIsolatedSet hN Z) := by
    intro i hi h
    exact (mem_markedSameSignIn.1 h).2 (mem_filter.1 (mem_subtype.1 hi)).2
  have hsub : Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
      IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) ⊆
        (twiceIsolatedSet hN Z).filter
          (fun i => charge i * charge (nearestNeighbor Z i) = -1) := by
    rw [← filter_corollary23_neutral_eq]
    intro i hi
    obtain ⟨-, h1, h2, h3'⟩ := Finset.mem_filter.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2.isIsolatedPair, h3'⟩
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
  calc _ ≤ ∑ i ∈ (twiceIsolatedSet hN Z).filter
        (fun i => charge i * charge (nearestNeighbor Z i) = -1),
        (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ = _ := hB
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => mem_compl.2 (hUS i hi))
        fun _ _ _ => sq_nonneg _

open scoped Classical in
/-- **The quadratic sum of `A₂` on all indices** (the case `Iᶜ = ∅`, `I` the whole index set). -/
theorem sum_dip_le_full [Nontrivial (Fin N ⊕ Fin N)] (hN : 2 ≤ N) (lam : ℝ)
    {Z : Fin N ⊕ Fin N → ℂ} {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hφ : nearestNeighbor Z = φ) (hT : twiceIsolatedSet hN Z = T)
    (h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N)) :
    dipSum hN lam Z ≤
      ∑ i ∈ (markedSameSign φ T)ᶜ,
        (nnRadius lam Z i / nnRadius2 h3 (sumKey N) lam Z i) ^ 2 := by
  classical
  subst hφ hT
  unfold dipSum
  set U := (twiceIsolatedSet hN Z).filter
    fun i => charge i * charge (nearestNeighbor Z i) = -1 with hU
  have hUS : ∀ i ∈ U, i ∉ markedSameSign (nearestNeighbor Z) (twiceIsolatedSet hN Z) := by
    intro i hi h
    exact (mem_markedSameSign.1 h).2 (mem_filter.1 hi).2
  have hsub : Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
      IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) ⊆ U := by
    rw [hU, ← filter_corollary23_neutral_eq]
    intro i hi
    obtain ⟨-, h1, h2, h3'⟩ := Finset.mem_filter.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2.isIsolatedPair, h3'⟩
  have hB : ∑ i ∈ U, (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 =
      ∑ i ∈ U, (nnRadius lam Z i / nnRadius2 h3 (sumKey N) lam Z i) ^ 2 := by
    simp only [← secondNeighborRadius_eq_nnRadius2 hN h3, ← firstNeighborRadius_eq_nnRadius]
  calc _ ≤ ∑ i ∈ U, (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ = _ := hB
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => mem_compl.2 (hUS i hi))
        fun _ _ _ => sq_nonneg _

/-! ### The energy bounds with the extra quadratic term -/

/-- The pair-assigned energy with the complement `Sᶜ` taken for an arbitrary decidable equality
(the definition uses the classical one; the two agree since `DecidableEq` is a subsingleton). -/
theorem pairAssignedEnergy_eq {ι : Type*} [Fintype ι] [Nontrivial ι] [DecidableEq ι]
    (h3 : 3 ≤ Fintype.card ι) (key : ι ↪ ℕ) (lam C : ℝ) (S : Finset ι) (z : ι → ℂ) :
    pairAssignedEnergy h3 key lam C S z =
      nnEnergy key lam z
        + ∑ i ∈ S, (Real.log (min (nnRadius2 h3 key lam z i)
            (nnRadius2 h3 key lam z (nnMap key z i)) / nnRadius lam z i) - C)
        - C * ∑ i ∈ Sᶜ, (nnRadius lam z i / nnRadius2 h3 key lam z i) ^ 2 := by
  unfold pairAssignedEnergy
  congr
  exact Subsingleton.elim _ _

/-- The pair-assigned energy is affine in the constant `C`: moving `C` to `C + δ` costs
`δ (|S| + ∑_{i ∉ S} (r̃₁/r̃₂)²)`. -/
theorem pairAssignedEnergy_add {ι : Type*} [Fintype ι] [Nontrivial ι] [DecidableEq ι]
    (h3 : 3 ≤ Fintype.card ι) (key : ι ↪ ℕ) (lam C δ : ℝ) (S : Finset ι) (z : ι → ℂ) :
    pairAssignedEnergy h3 key lam C S z =
      pairAssignedEnergy h3 key lam (C + δ) S z +
        δ * ((S.card : ℝ) + ∑ i ∈ Sᶜ, (nnRadius lam z i / nnRadius2 h3 key lam z i) ^ 2) := by
  rw [pairAssignedEnergy_eq, pairAssignedEnergy_eq]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- **The lower bound `F_λ ≥ F⁽¹⁾_{C+δ} + F⁽²⁾ - C(N - K) + δ ∑ (r̃₁/r̃₂)²`** (source l. 1532--1545,
2117--2121), for `m ≥ 2` and `Iᶜ ≠ ∅`: Proposition 3.10, Step 2, with the neutral quadratic
coefficient enlarged from `C` to `C + δ`; the gain is the quadratic sum of `A₂`. -/
theorem le_energy_split_add {C δ : ℝ} (hC0 : 0 ≤ C) (hδ : 0 ≤ δ) (hC : Corollary23Holds C)
    (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) {Z : Fin N ⊕ Fin N → ℂ} (hZ : ∀ i, Z i ∈ box N)
    (hgen : IsGeneric Z) {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hφ : nearestNeighbor Z = φ) (hT : twiceIsolatedSet hN Z = T)
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}]
    (h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts φ}) :
    pairAssignedEnergy h3 (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam (C + δ)
        (markedSameSignIn φ T) (fun j : {i // i ∈ pairVerts φ} => Z j)
      + nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
          (fun j : {i // i ∉ pairVerts φ} => Z j)
      - C * ((N : ℝ) - numComponents Z) + δ * dipSum hN lam Z ≤ energy lam Z := by
  have h := _root_.TwoComponentCoulomb.le_energy_split hC0 hC hN hlam hZ hgen hφ hT h3
  rw [pairAssignedEnergy_add h3 (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam C δ] at h
  have h1 := sum_dip_le_split hN lam hφ hT h3
  have h2 := mul_le_mul_of_nonneg_left h1 hδ
  have h4 : 0 ≤ δ * ((markedSameSignIn φ T).card : ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
  linarith

/-- **The lower bound on all indices** (the case `Iᶜ = ∅`) with the extra quadratic term. -/
theorem le_energy_full_add [Nontrivial (Fin N ⊕ Fin N)] {C δ : ℝ} (hC0 : 0 ≤ C) (hδ : 0 ≤ δ)
    (hC : Corollary23Holds C) (hN : 2 ≤ N) (h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N)) {lam : ℝ}
    (hlam : 0 < lam) {Z : Fin N ⊕ Fin N → ℂ} (hZ : ∀ i, Z i ∈ box N) (hgen : IsGeneric Z)
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hφ : nearestNeighbor Z = φ) (hT : twiceIsolatedSet hN Z = T) :
    pairAssignedEnergy h3 (sumKey N) lam (C + δ) (markedSameSign φ T) Z
      - C * ((N : ℝ) - numComponents Z) + δ * dipSum hN lam Z ≤ energy lam Z := by
  have h := _root_.TwoComponentCoulomb.le_energy_full hC0 hC hN h3 hlam hZ hgen hφ hT
  rw [pairAssignedEnergy_add h3 (sumKey N) lam C δ] at h
  have h1 := sum_dip_le_full hN lam hφ hT h3
  have h2 := mul_le_mul_of_nonneg_left h1 hδ
  have h4 : 0 ≤ δ * ((markedSameSign φ T).card : ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
  linarith

/-- Without marked pairs the quadratic sum of `A₂` is empty. -/
theorem dipSum_eq_zero_of_twiceIsolatedSet_eq_empty (hN : 2 ≤ N) (lam : ℝ)
    {Z : Fin N ⊕ Fin N → ℂ} (hT : twiceIsolatedSet hN Z = ∅) : dipSum hN lam Z = 0 := by
  classical
  unfold dipSum
  refine Finset.sum_eq_zero fun i hi => ?_
  obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hi
  have : i ∈ twiceIsolatedSet hN Z :=
    (mem_twiceIsolatedSet hN Z).2 ⟨h1.isIsolatedPair, h2.isIsolatedPair, h3⟩
  rw [hT] at this
  exact absurd this (Finset.notMem_empty i)

/-! ### The cell integrals (gred3) for a general weight -/

section Cells

/-- **Separation of variables (gred3) for a general weight** (source l. 1546--1551): if on the
cell of a marked graph `γ = (φ, T)` (in the box) the weight satisfies
`W(Z) ≤ c · g₁(Z|_I) g₂(Z|_{Iᶜ})`, then the cell integral of `W` is at most
`c ∫_{Λ^{2m} ∩ {γ_{2m} = γ¹}} g₁ · ∫_{Λ^{2N-2m} ∩ {γ_{2N-2m} = γ²}} g₂`. -/
theorem lintegral_markedCell_le_mul_gen (hN : 2 ≤ N) {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    {T : Finset (Fin N ⊕ Fin N)} [Nontrivial {i // i ∈ pairVerts φ}]
    [Nontrivial {i // i ∉ pairVerts φ}] (W : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) {c : ℝ≥0∞}
    (hc : c ≠ ∞) {g₁ : ({i // i ∈ pairVerts φ} → ℂ) → ℝ≥0∞}
    {g₂ : ({i // i ∉ pairVerts φ} → ℂ) → ℝ≥0∞} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (hW : ∀ Z ∈ markedCell hN φ T, (∀ i, Z i ∈ box N) →
      W Z ≤ c * (g₁ (fun j : {i // i ∈ pairVerts φ} => Z j) *
        g₂ (fun j : {i // i ∉ pairVerts φ} => Z j)))
    (E : Set (Fin N ⊕ Fin N → ℂ)) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T, W Z ≤
      c * ((∫⁻ x in (Set.univ.pi fun _ : {i // i ∈ pairVerts φ} => box N) ∩
            {x | nnMap (subtypeKey (· ∈ pairVerts φ) (sumKey N)) x = pairRestrict φ}, g₁ x) *
        ∫⁻ y in (Set.univ.pi fun _ : {i // i ∉ pairVerts φ} => box N) ∩
          {y | nnMap (subtypeKey (· ∉ pairVerts φ) (sumKey N)) y = complRestrict φ}, g₂ y) := by
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
      markedCell hN φ T) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ T)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T, W Z :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        c * (g₁ (fun j : {i // i ∈ pairVerts φ} => Z j) *
          g₂ (fun j : {i // i ∉ pairVerts φ} => Z j)) :=
        setLIntegral_mono' hmeas fun Z hZ => hW Z hZ.2 fun i => hZ.1 i (Set.mem_univ i)
    _ = c * ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        g₁ (fun j : {i // i ∈ pairVerts φ} => Z j) * g₂ (fun j : {i // i ∉ pairVerts φ} => Z j) :=
        lintegral_const_mul' _ _ hc
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        refine setLIntegral_subtype_mul_le (pairVerts φ) (box N) (markedCell hN φ T) _ _
          (fun Z hZ => ⟨nnMap_pairRestrict hZ.2.1, nnMap_complRestrict hZ.2.1⟩) hg₁ hg₂

/-- **The cell integral for a general weight, on all indices** (the case `Iᶜ = ∅`, or `I = ∅`):
if on the cell (in the box) `W(Z) ≤ c · g(Z)`, then the cell integral of `W` is at most
`c ∫_{Λ^{2N} ∩ {γ_{2N} = φ}} g`. -/
theorem lintegral_markedCell_le_full_gen [Nontrivial (Fin N ⊕ Fin N)] (hN : 2 ≤ N)
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (W g : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hW : ∀ Z ∈ markedCell hN φ T, (∀ i, Z i ∈ box N) → W Z ≤ c * g Z)
    (E : Set (Fin N ⊕ Fin N → ℂ)) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T, W Z ≤
      c * ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nnMap (sumKey N) Z = φ},
        g Z := by
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
      markedCell hN φ T) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ T)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T, W Z :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T, c * g Z :=
        setLIntegral_mono' hmeas fun Z hZ => hW Z hZ.2 fun i => hZ.1 i (Set.mem_univ i)
    _ = c * ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T, g Z :=
        lintegral_const_mul' _ _ hc
    _ ≤ _ := by
        refine mul_le_mul_right (lintegral_mono_set ?_) _
        rintro Z ⟨hZΛ, hZc⟩
        exact ⟨hZΛ, (nearestNeighbor_eq_nnMap_fun Z).symm.trans hZc.2.1⟩

end Cells

/-! ### The pointwise bound of the weight `e^{A₂ - β F_λ}` -/

section Weight

/-- The exponent bookkeeping of the weight: from `P + F₂ - C (N - K) + (1/β) Q ≤ F`
(the energy bound with the enlarged coefficient) and `D ≤ (M₀ + 3)(N - K) + q`
(the deficit count), the exponent `(Q + D) - β F` of `e^{A₂ - β F}` is at most
`(β C + M₀ + 3)(N - K) + q - β (P + F₂)`. -/
theorem exponent_le {β Cc q NK X E dip D : ℝ} (hβ : 0 < β)
    (hE : X - Cc * NK + (1 / β) * dip ≤ E) (hD : D ≤ (M0 + 3) * NK + q) :
    (dip + D) + -β * E ≤ ((β * Cc + (M0 + 3)) * NK + q) + -β * X := by
  have h := mul_le_mul_of_nonneg_left hE hβ.le
  have e : β * (1 / β * dip) = dip := by field_simp
  linarith only [h, e, hD]

theorem ofReal_exp_mul_le {a b c x : ℝ} (h : a + b ≤ c + x) :
    ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) ≤
      ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (Real.exp x) := by
  rw [UpperCellBound.ofReal_exp_mul_ofReal_exp, UpperCellBound.ofReal_exp_mul_ofReal_exp]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 h)

theorem ofReal_exp_mul_le₃ {a b c x y : ℝ} (h : a + b ≤ c + x + y) :
    ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) ≤
      ENNReal.ofReal (Real.exp c) * (ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (Real.exp y)) := by
  rw [UpperCellBound.ofReal_exp_mul_ofReal_exp, UpperCellBound.ofReal_exp_mul_ofReal_exp,
    UpperCellBound.ofReal_exp_mul_ofReal_exp]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))

end Weight

/-! ### The entropy with `C₀ = 61` (source l. 2121: "the allowance `C₀ (p - p₀)`") -/

section Entropy

open UpperCellBound

/-- **(eq:F(1)), main form, with the extra factor `e^{p - p₀}`, generic rate** (source
l. 1553--1565, 2117--2121): the entropy bound (eq:F(1)) with `C₀ = 61`, with an error rate
`r ≤ ω(λ)` for an arbitrary `ω : ℝ → ℝ` (no property of `ω` is used). -/
theorem entropy_mul_le_main_sixty_one_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) {c Cb r X : ℝ}
    (hc : 0 ≤ c) (hCb : 0 ≤ Cb) {N m p p₀ p₀' : ℕ} (hm : 0 < m) (hmN : m ≤ N) (hp₀ : p₀ ≤ p)
    (hpm : p ≤ m) (hp₀' : p₀' + p = p₀ + m) {lam : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ ω lam)
    {Y : ℝ≥0∞}
    (hY : ENNReal.ofReal (Real.exp (m * Real.log m - p₀' * Real.log p₀'
        - ((m : ℝ) - p₀') * Real.log ((m : ℝ) - p₀') + 61 * ((m : ℝ) - p₀'))) * Y ≤
      ENNReal.ofReal (Real.exp (m * (Real.log N + (2 - β) * Real.log lam
        + Real.log (dipoleConstant β hβ.le)) - c * m * (((m : ℝ) - p₀') / m) ^ 2
        + Cb * m * r + Cb * Real.log (N + 1) + X))) :
    ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
        - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + 60 * ((p : ℝ) - p₀))) *
      (ENNReal.ofReal (Real.exp ((p : ℝ) - p₀)) * Y) ≤
      ENNReal.ofReal (Real.exp (m * (Real.log N + (2 - β) * Real.log lam
        + Real.log (dipoleConstant β hβ.le)) - c * ((p : ℝ) - p₀) ^ 2 / N
        + Cb * N * ω lam + Cb * Real.log (N + 1) + X)) := by
  have hcast : (p₀' : ℝ) = p₀ + m - p := by
    have : ((p₀' + p : ℕ) : ℝ) = ((p₀ + m : ℕ) : ℝ) := by rw [hp₀']
    push_cast at this
    linarith
  have hq : (m : ℝ) - p₀' = (p : ℝ) - p₀ := by rw [hcast]; ring
  refine entropy_mul_le_main_rate hβ ω hc hCb hm hmN hp₀ hpm hp₀' hr0 hr ?_
  have e : ENNReal.ofReal (Real.exp (m * Real.log m - p₀' * Real.log p₀'
        - ((m : ℝ) - p₀') * Real.log ((m : ℝ) - p₀') + 60 * ((m : ℝ) - p₀'))) *
      (ENNReal.ofReal (Real.exp ((p : ℝ) - p₀)) * Y) =
      ENNReal.ofReal (Real.exp (m * Real.log m - p₀' * Real.log p₀'
        - ((m : ℝ) - p₀') * Real.log ((m : ℝ) - p₀') + 61 * ((m : ℝ) - p₀'))) * Y := by
    rw [← mul_assoc, ofReal_exp_mul_ofReal_exp]
    congr 3
    rw [← hq]
    ring
  rw [e]
  exact hY

/-- **(eq:F(1)), crude form, with the extra factor `e^{p - p₀}`**. -/
theorem entropy_mul_le_crude_sixty_one {m p p₀ p₀' : ℕ} (hp₀ : p₀ ≤ p) (hpm : p ≤ m)
    (hp₀' : p₀' + p = p₀ + m) {B : ℝ} {Y : ℝ≥0∞}
    (hY : ENNReal.ofReal (Real.exp (m * Real.log m - p₀' * Real.log p₀'
        - ((m : ℝ) - p₀') * Real.log ((m : ℝ) - p₀') + 61 * ((m : ℝ) - p₀'))) * Y ≤
      ENNReal.ofReal (Real.exp B)) :
    ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
        - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + 60 * ((p : ℝ) - p₀))) *
      (ENNReal.ofReal (Real.exp ((p : ℝ) - p₀)) * Y) ≤ ENNReal.ofReal (Real.exp B) := by
  have hcast : (p₀' : ℝ) = p₀ + m - p := by
    have : ((p₀' + p : ℕ) : ℝ) = ((p₀ + m : ℕ) : ℝ) := by rw [hp₀']
    push_cast at this
    linarith
  have hq : (m : ℝ) - p₀' = (p : ℝ) - p₀ := by rw [hcast]; ring
  refine entropy_mul_le_crude hp₀ hpm hp₀' ?_
  have e : ENNReal.ofReal (Real.exp (m * Real.log m - p₀' * Real.log p₀'
        - ((m : ℝ) - p₀') * Real.log ((m : ℝ) - p₀') + 60 * ((m : ℝ) - p₀'))) *
      (ENNReal.ofReal (Real.exp ((p : ℝ) - p₀)) * Y) =
      ENNReal.ofReal (Real.exp (m * Real.log m - p₀' * Real.log p₀'
        - ((m : ℝ) - p₀') * Real.log ((m : ℝ) - p₀') + 61 * ((m : ℝ) - p₀'))) * Y := by
    rw [← mul_assoc, ofReal_exp_mul_ofReal_exp]
    congr 3
    rw [← hq]
    ring
  rw [e]
  exact hY

/-- Regrouping of the constants: `e^{b + q} Y = e^b (e^q Y)`. -/
theorem ofReal_exp_add_mul (b q : ℝ) (Y : ℝ≥0∞) :
    ENNReal.ofReal (Real.exp (b + q)) * Y =
      ENNReal.ofReal (Real.exp b) * (ENNReal.ofReal (Real.exp q) * Y) := by
  rw [← ofReal_exp_mul_ofReal_exp, mul_assoc]

/-- Regrouping of the constants: `e^{b + q} (Y₁ Y₂) = e^b ((e^q Y₁) Y₂)`. -/
theorem ofReal_exp_add_mul_mul (b q : ℝ) (Y₁ Y₂ : ℝ≥0∞) :
    ENNReal.ofReal (Real.exp (b + q)) * (Y₁ * Y₂) =
      ENNReal.ofReal (Real.exp b) * ((ENNReal.ofReal (Real.exp q) * Y₁) * Y₂) := by
  rw [← ofReal_exp_mul_ofReal_exp]
  ring

end Entropy

/-! ### The per-cell bound for the weight `e^{A₂} e^{-β F_λ}` (source l. 2117--2124) -/

section CellBoundEnergy

open UpperCellBound UpperAssembly

/-- **The per-cell bound for the weight `e^{A₂ - β F_λ}`, generic rate** (source l. 2117--2124):
for a rate `ω` satisfying `UpperRateHyp` in place of `ω_λ`, the integral of `e^{A₂} e^{-β F_λ}`
over one marked cell satisfies `CellBoundRate`. The constants depend only on `β` and `ω`. -/
theorem exists_cellBound_energy_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ)
    (hω : UpperRateHyp β hβ ω) :
    ∃ A c Cb : ℝ, 0 < c ∧ 0 ≤ Cb ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam ≤ Real.exp (-1) →
      ∀ (K p p₀ : ℕ) (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (T : Finset (Fin N ⊕ Fin N)),
        (φ, T) ∈ markedGraphs hN K p p₀ → ∀ E : Set (Fin N ⊕ Fin N → ℂ),
        CellBoundRate β hβ ω A c Cb N K p p₀ lam 0
          (∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T,
            ENNReal.ofReal (Real.exp (linearA2 hN lam Z)) *
              ENNReal.ofReal (Real.exp (-β * energy lam Z))) := by
  have hβ0 : 0 < β := by linarith
  obtain ⟨Cc, hCc0, hCc⟩ := exists_corollary23Holds
  have hδ : 0 ≤ 1 / β := by positivity
  have hC'0 : 0 ≤ Cc + 1 / β := by positivity
  obtain ⟨C₁, c₁, hC₁, hc₁, hconvH⟩ := isolated_n_neutral_conv.{0} hβ.le hC'0 61
  obtain ⟨C₂, hC₂, hcrudeH⟩ := isolated_crude.{0} hβ.le hC'0 61
  obtain ⟨C₄, hF2⟩ := exists_lintegral_nnEnergy_le hβ
  set L := Real.log (dipoleConstant β hβ.le) with hL
  refine ⟨β * Cc + (M0 + 3) + C₄, c₁, C₁ + C₂ + |L|, hc₁, by positivity, ?_⟩
  intro N hN lam hlam hlam1 K p p₀ φ T hγ E
  obtain ⟨Z₀, -, hgen, hφ, hT, hK, hp, hp₀⟩ := mem_markedGraphs.1 hγ
  subst hφ hT hK
  set m := numIsolatedPairs Z₀ with hm
  have hmK : m ≤ numComponents Z₀ := numIsolatedPairs_le_numComponents Z₀
  have hKN : numComponents Z₀ ≤ N := numComponents_le Z₀
  have hpm : p ≤ m := hp ▸ numTwiceIsolated_le_numIsolatedPairs
  have hp₀p : p₀ ≤ p := hp ▸ hp₀ ▸ numNeutralTwiceIsolated_le_numTwiceIsolated
  have hNpos : 0 < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hβ0' : 0 ≤ β := by linarith
  obtain ⟨hr0, hr⟩ := isolatedRate_le_rate hβ ω hω hlam hlam1
  have hω0 : 0 ≤ ω lam := hr0.trans hr
  have hlogN : 0 ≤ Real.log (N + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  have hNω : 0 ≤ (N : ℝ) * ω lam := mul_nonneg hN0.le hω0
  have hCb : 0 ≤ C₁ + C₂ + |L| := by positivity
  obtain ⟨hF2c, hF2f⟩ := hF2 N Z₀ (nearestNeighbor Z₀) hNpos rfl lam hlam hlam1
  have hnt : Nontrivial (Fin N ⊕ Fin N) :=
    ⟨⟨Sum.inl ⟨0, hNpos⟩, Sum.inr ⟨0, hNpos⟩, Sum.inl_ne_inr⟩⟩
  set c₀ : ℝ := (β * Cc + (M0 + 3)) * ((N : ℝ) - numComponents Z₀) with hc₀
  set q : ℝ := (p : ℝ) - p₀ with hq
  rcases Nat.eq_zero_or_pos p with hp0 | hp1
  · -- no marked pair: Lemma 3.5 on all points
    have hp₀0 : p₀ = 0 := by omega
    have hT0 : twiceIsolatedSet hN Z₀ = ∅ := by
      have h := card_twiceIsolatedSet (hN := hN) (Z := Z₀)
      rw [hp, hp0] at h
      exact Finset.card_eq_zero.1 h
    rw [hT0] at hγ ⊢
    have hcell := lintegral_markedCell_le_full_gen hN
      (fun Z => ENNReal.ofReal (Real.exp (linearA2 hN lam Z)) *
        ENNReal.ofReal (Real.exp (-β * energy lam Z)))
      (fun Z => ENNReal.ofReal (Real.exp (-β * nnEnergy (sumKey N) lam Z)))
      (c := ENNReal.ofReal (Real.exp (c₀ + q))) ENNReal.ofReal_ne_top
      (fun Z hZc hZΛ => by
        have hE := le_energy_full_of_empty hCc hN hlam hZΛ hZc.1 hZc.2.2
        rw [numComponents_eq_of_mem_markedCell hγ hZc] at hE
        have hD := deficit_le hγ hZc
        have hdip := dipSum_eq_zero_of_twiceIsolatedSet_eq_empty hN lam hZc.2.2
        have h := exponent_le hβ0 (X := nnEnergy (sumKey N) lam Z) (q := q) (E := energy lam Z) (Cc := Cc)
          (dip := dipSum hN lam Z) (by rw [hdip]; linarith) hD
        exact ofReal_exp_mul_le (by rw [linearA2_eq]; exact h)) E
    refine Or.inl (hcell.trans ((mul_le_mul_right hF2f _).trans ?_))
    rw [ofReal_exp_mul_ofReal_exp]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have e1 : (p : ℝ) = 0 := by exact_mod_cast hp0
    have e2 : (p₀ : ℝ) = 0 := by exact_mod_cast hp₀0
    have hq0 : q = 0 := by rw [hq, e1, e2]; ring
    rw [hq0, e1, e2]
    have h1 : 0 ≤ (C₁ + C₂ + |L|) * N * ω lam := by
      rw [mul_assoc]; exact mul_nonneg hCb hNω
    have h2 : 0 ≤ (C₁ + C₂ + |L|) * Real.log (N + 1) := mul_nonneg hCb hlogN
    have h3 : c₁ * (0 : ℝ) ^ 2 / N = 0 := by simp
    simp only [mul_zero, Real.log_zero, sub_self]
    rw [← hL, hc₀]
    linarith
  -- at least one marked pair: `m ≥ 2`
  have hm2 : 2 ≤ m := by
    by_contra h
    have h' := twiceIsolatedSet_eq_empty_of_numIsolatedPairs_le_one hN (Z := Z₀) (by omega)
    have h2 := card_twiceIsolatedSet (hN := hN) (Z := Z₀)
    rw [h', hp] at h2
    simp at h2
    omega
  have hmN : m ≤ N := hmK.trans hKN
  have hcardI : Fintype.card {i // i ∈ pairVerts (nearestNeighbor Z₀)} = 2 * m :=
    card_pairVerts_subtype rfl
  have h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts (nearestNeighbor Z₀)} := by omega
  have : Nontrivial {i // i ∈ pairVerts (nearestNeighbor Z₀)} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hScard : (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)).card =
      2 * (m - (p₀ + m - p)) := by
    rw [card_markedSameSignIn (hN := hN) rfl rfl, hp, hp₀]
    congr 1
    omega
  have hSinv : ∀ i, pairRestrict (nearestNeighbor Z₀) i ∈
      markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) ↔
        i ∈ markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) := by
    intro i
    refine ⟨fun h => ?_, fun h => pairRestrict_mem_markedSameSignIn rfl rfl h⟩
    have := pairRestrict_mem_markedSameSignIn (hN := hN) rfl rfl h
    rwa [pairRestrict_pairRestrict] at this
  have hp₀' : p₀ + m - p + p = p₀ + m := by omega
  by_cases hmN' : m = N
  · -- `Iᶜ = ∅`: Proposition 3.9 on all points
    have hKeq : numComponents Z₀ = N := by omega
    have h3' : 3 ≤ Fintype.card (Fin N ⊕ Fin N) := by simp; omega
    have huniv : pairVerts (nearestNeighbor Z₀) = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      have hc := card_isolatedPairSet (Z := Z₀)
      rw [isolatedPairSet_eq_pairVerts] at hc
      rw [hc]
      simp
      omega
    have hφ2 : ∀ i, nearestNeighbor Z₀ (nearestNeighbor Z₀ i) = i := fun i =>
      (mem_pairVerts.1 (huniv ▸ Finset.mem_univ i)).1
    have hφ0 : ∀ i, nearestNeighbor Z₀ i ≠ i := nearestNeighbor_ne Z₀
    have hSinv' : ∀ i, nearestNeighbor Z₀ i ∈
        markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) ↔
          i ∈ markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) := by
      intro i
      simp only [mem_markedSameSign]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' := nearestNeighbor_mem_twiceIsolatedSet h1
        rw [hφ2] at h1' h2
        exact ⟨h1', by rwa [mul_comm] at h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨nearestNeighbor_mem_twiceIsolatedSet h1, ?_⟩
        rwa [hφ2, mul_comm]
    have hScard' : (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)).card =
        2 * (N - (p₀ + N - p)) := by
      rw [card_markedSameSign hN Z₀, hp, hp₀]
      congr 1
      omega
    have hcard2 : Fintype.card (Fin N ⊕ Fin N) = 2 * N := by simp [two_mul]
    have hcell := lintegral_markedCell_le_full_gen hN
      (fun Z => ENNReal.ofReal (Real.exp (linearA2 hN lam Z)) *
        ENNReal.ofReal (Real.exp (-β * energy lam Z)))
      (fun Z => ENNReal.ofReal (Real.exp (-(β * pairAssignedEnergy h3' (sumKey N) lam (Cc + 1 / β)
        (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) Z))))
      (c := ENNReal.ofReal (Real.exp (c₀ + q))) ENNReal.ofReal_ne_top
      (fun Z hZc hZΛ => by
        have hE := le_energy_full_add hCc0.le hδ hCc hN h3' hlam hZΛ hZc.1 hZc.2.1 hZc.2.2
        rw [numComponents_eq_of_mem_markedCell hγ hZc] at hE
        have hD := deficit_le hγ hZc
        have h := exponent_le hβ0 (X := pairAssignedEnergy h3' (sumKey N) lam (Cc + 1 / β)
          (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) Z) (q := q)
          (E := energy lam Z) (Cc := Cc) (dip := dipSum hN lam Z) (by linarith) hD
        exact ofReal_exp_mul_le (by rw [linearA2_eq]; linarith [h, hc₀])) E
    have h := hconvH (Fin N ⊕ Fin N) (sumKey N) (nearestNeighbor Z₀) hφ2 hφ0 h3'
      (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) hSinv' N N (p₀ + N - p)
      hcard2 (by omega) le_rfl (by linarith) (by omega) hScard' lam hlam hlam1
    have hF1 := entropy_mul_le_main_sixty_one_rate hβ ω (X := 0) hc₁.le hC₁.le (N := N) (m := N)
      (p := p) (p₀ := p₀) (p₀' := p₀ + N - p) hNpos le_rfl hp₀p (hmN' ▸ hpm) (by omega) hr0 hr
      (h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq (by
        rw [ite_eq_left hβ, ite_eq_right hβ.ne']
        ring)))))
    rw [ofReal_exp_add_mul] at hcell
    refine Or.inl (le_ofReal_exp_of_le_mul_one hcell hF1 ?_)
    rw [hKeq] at hc₀ ⊢
    have h1 : C₁ * N * ω lam ≤ (C₁ + C₂ + |L|) * N * ω lam := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) hNω
    have h2 : C₁ * Real.log (N + 1) ≤ (C₁ + C₂ + |L|) * Real.log (N + 1) :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) hlogN
    rw [hc₀]
    linarith
  -- `m < N`: the separation (gred3)
  have hcardIc : Fintype.card {i // i ∉ pairVerts (nearestNeighbor Z₀)} = 2 * (N - m) :=
    card_compl_pairVerts_subtype rfl
  have : Nontrivial {i // i ∉ pairVerts (nearestNeighbor Z₀)} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hcell := lintegral_markedCell_le_mul_gen hN
    (fun Z => ENNReal.ofReal (Real.exp (linearA2 hN lam Z)) *
      ENNReal.ofReal (Real.exp (-β * energy lam Z)))
    (c := ENNReal.ofReal (Real.exp (c₀ + q))) ENNReal.ofReal_ne_top
    (g₁ := fun x => ENNReal.ofReal (Real.exp (-(β * pairAssignedEnergy h3
      (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) lam (Cc + 1 / β)
      (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) x))))
    (g₂ := fun y => ENNReal.ofReal (Real.exp (-β *
      nnEnergy (subtypeKey (· ∉ pairVerts (nearestNeighbor Z₀)) (sumKey N)) lam y)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_pairAssignedEnergy _ h3 lam _ _).const_mul β).neg)))
    (measurable_ofReal_exp_neg_mul (measurable_nnEnergy _ lam) β)
    (fun Z hZc hZΛ => by
      have hE := le_energy_split_add hCc0.le hδ hCc hN hlam hZΛ hZc.1 hZc.2.1 hZc.2.2 h3
      rw [numComponents_eq_of_mem_markedCell hγ hZc] at hE
      have hD := deficit_le hγ hZc
      have h := exponent_le hβ0 (X := pairAssignedEnergy h3
        (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) lam (Cc + 1 / β)
        (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀))
        (fun j : {i // i ∈ pairVerts (nearestNeighbor Z₀)} => Z j) +
        nnEnergy (subtypeKey (· ∉ pairVerts (nearestNeighbor Z₀)) (sumKey N)) lam
          (fun j : {i // i ∉ pairVerts (nearestNeighbor Z₀)} => Z j)) (q := q)
        (E := energy lam Z) (Cc := Cc) (dip := dipSum hN lam Z) (by linarith) hD
      exact ofReal_exp_mul_le₃ (by rw [linearA2_eq]; linarith)) E
  have hY₂ := @hF2c inferInstance
  have hf2 := pairRestrict_pairRestrict (nearestNeighbor Z₀)
  have hf0 := pairRestrict_ne_of_nearestNeighbor (Z := Z₀) rfl
  rw [ofReal_exp_add_mul_mul] at hcell
  by_cases hNm : (N : ℝ) ≤ 2 * m
  · have h := hconvH {i // i ∈ pairVerts (nearestNeighbor Z₀)}
      (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) (pairRestrict (nearestNeighbor Z₀))
      hf2 hf0 h3 (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) hSinv N m
      (p₀ + m - p) hcardI hm2 hmN hNm (by omega) hScard lam hlam hlam1
    have hF1 := entropy_mul_le_main_sixty_one_rate hβ ω (X := 0) hc₁.le hC₁.le (N := N) (m := m)
      (p := p) (p₀ := p₀) (p₀' := p₀ + m - p) (by omega) hmN hp₀p hpm hp₀' hr0 hr
      (h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq (by
        rw [ite_eq_left hβ, ite_eq_right hβ.ne']
        ring)))))
    refine Or.inl (le_ofReal_exp_of_le_mul hcell hF1 hY₂ ?_)
    have h1 : C₁ * N * ω lam ≤ (C₁ + C₂ + |L|) * N * ω lam := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) hNω
    have h2 : C₁ * Real.log (N + 1) ≤ (C₁ + C₂ + |L|) * Real.log (N + 1) :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) hlogN
    rw [hc₀]
    linarith
  · replace hNm := not_le.1 hNm
    have h := hcrudeH {i // i ∈ pairVerts (nearestNeighbor Z₀)}
      (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) (pairRestrict (nearestNeighbor Z₀))
      hf2 hf0 h3 (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) hSinv N m
      (p₀ + m - p) hcardI hm2 hmN (by omega) lam hlam hlam1
    have hF1 := entropy_mul_le_crude_sixty_one (m := m) (p := p) (p₀ := p₀) (p₀' := p₀ + m - p)
      hp₀p hpm hp₀' h
    have hpN : (p : ℝ) < N / 2 := by
      have : (p : ℝ) ≤ m := by exact_mod_cast hpm
      linarith
    refine Or.inr ⟨hpN, le_ofReal_exp_of_le_mul hcell hF1 hY₂ ?_⟩
    rw [ite_eq_left hβ, ite_eq_right hβ.ne']
    have hmN'' : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have h1 : -((m : ℝ) * L) ≤ |L| * N := by
      have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have h1a : (m : ℝ) * -L ≤ m * |L| := mul_le_mul_of_nonneg_left (neg_le_abs L) h0
      have h1b : (m : ℝ) * |L| ≤ N * |L| := mul_le_mul_of_nonneg_right hmN'' (abs_nonneg L)
      linarith only [h1a, h1b]
    have hmr : (m : ℝ) = numIsolatedPairs Z₀ := rfl
    rw [← hL, ← hmr, hc₀]
    have h2 := mul_pos hC₁ hN0
    linarith

end CellBoundEnergy

end MomentA2

/-! ### The exponential moment of `A₂` (eq. (eq:A2)) -/

open MeasureTheory
open scoped ENNReal

/-- **Theorem 2, eq. (eq:A2), generic rate** (source l. 2117--2124), for a rate `ω` satisfying
`UpperRateHyp` in place of `ω_λ`: for `β > 2` there are
`C, λ₁ > 0`, depending only on `β` and `ω`, such that for `N ≥ 2` and `0 < λ < λ₁`,
`𝔼_ℙ[e^{A₂}] ≤ exp (C N ω(λ) + C log (N+1))`. The division by the partition function uses
Proposition 4.1, whose error rate for `β > 2` is that of Proposition 3.9, bounded by `ω(λ)` by the
field `UpperRateHyp.isolated_le`. -/
theorem momentA2_le_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) (hω : UpperRateHyp β hβ ω) :
    ∃ C lam₁ : ℝ, 0 < C ∧ 0 < lam₁ ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam < lam₁ →
      ∫⁻ Z, ENNReal.ofReal (Real.exp (linearA2 hN lam Z)) ∂gibbsMeasure N β lam ≤
        ENNReal.ofReal (Real.exp (C * N * ω lam + C * Real.log (N + 1))) := by
  obtain ⟨A, c, Cb, hc, hCb, hcell⟩ := MomentA2.exists_cellBound_energy_rate hβ ω hω
  obtain ⟨c', C', lam₀, hc', hC', hlam₀, hlam₀1, hsum⟩ :=
    UpperAssembly.lintegral_le_of_cellBound_rate hβ ω hω A c Cb hc hCb
  obtain ⟨lam₄, C₄, h4, hC4, hlow⟩ := proposition_4_1 β hβ.le
  refine ⟨C' + C₄ + 3, min lam₀ lam₄, by positivity, lt_min hlam₀ h4, ?_⟩
  intro N hN lam hlam hlamlt
  have hlam₀' : lam < lam₀ := hlamlt.trans_le (min_le_left _ _)
  have hlam₄ : lam < lam₄ := hlamlt.trans_le (min_le_right _ _)
  have hlam1 : lam ≤ Real.exp (-1) := hlam₀'.le.trans hlam₀1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : 0 ≤ Real.log (N + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  have hrate := hω.isolated_le lam hlam hlam1
  -- the upper bound on the Boltzmann integral
  have hU := hsum N hN lam hlam hlam₀' Set.univ
    (fun Z => ENNReal.ofReal (Real.exp (linearA2 hN lam Z)) *
      ENNReal.ofReal (Real.exp (-β * energy lam Z))) 0 N le_rfl
    (fun K p p₀ φ T hγ => ⟨hcell N hN lam hlam hlam1 K p p₀ φ T hγ Set.univ, fun hlt => by
      obtain ⟨h1, h2, h3, -⟩ := UpperCellBound.constraints_of_nonempty ⟨_, hγ⟩
      omega⟩)
  rw [Set.inter_univ] at hU
  -- the lower bound on the partition function (Proposition 4.1)
  have hL := hlow N hN lam hlam hlam₄
  simp only [ite_eq_right hβ.ne'] at hL
  set rate := (if β < 4 then lam ^ (β - 2) else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
    else lam ^ 2 * |Real.log lam|) with hratedef
  set lower := 2 * N * Real.log N + N * ((2 - β) * Real.log lam
    + (Real.log (dipoleConstant β hβ.le) - 1)) - C₄ * N * rate with hlower
  set upper := 2 * N * Real.log N
    + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1)
    - c' * ((N : ℝ) - N) ^ 2 / N + C' * N * ω lam
    + (C' + 3) * Real.log (N + 1) + 0 with hupper
  rw [lintegral_gibbsMeasure']
  have hZinv : (partitionFunction N β lam)⁻¹ ≤ ENNReal.ofReal (Real.exp (-lower)) := by
    rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]
    exact ENNReal.inv_le_inv.2 hL
  calc (partitionFunction N β lam)⁻¹ *
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
          ENNReal.ofReal (Real.exp (linearA2 hN lam Z)) *
            ENNReal.ofReal (Real.exp (-β * energy lam Z))
      ≤ ENNReal.ofReal (Real.exp (-lower)) * ENNReal.ofReal (Real.exp upper) :=
        mul_le_mul' hZinv hU
    _ = ENNReal.ofReal (Real.exp (upper - lower)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_eq_sub]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have hω0 : 0 ≤ ω lam := (by positivity : 0 ≤ rate).trans hrate
        have h0 : c' * ((N : ℝ) - N) ^ 2 / N = 0 := by simp
        have h1 : C₄ * N * rate ≤ C₄ * N * ω lam :=
          mul_le_mul_of_nonneg_left hrate (by positivity)
        have h2 : (C' + C₄ + 3) * N * ω lam =
            C' * N * ω lam + C₄ * N * ω lam +
              3 * N * ω lam := by ring
        have h3 : 0 ≤ 3 * N * ω lam := by positivity
        have h4 : (C' + 3) * Real.log (N + 1) ≤ (C' + C₄ + 3) * Real.log (N + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) hlogN
        rw [hupper, hlower]
        linarith

end TwoComponentCoulomb

end
