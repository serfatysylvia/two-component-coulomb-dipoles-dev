/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.ElectricLower
public import TwoComponentCoulomb.Fluctuations.TiltedEnergy
public import TwoComponentCoulomb.Frozen.GibbsMeasure
public import TwoComponentCoulomb.UpperBound.UpperAssembly
import TwoComponentCoulomb.Frozen.Proposition41
import TwoComponentCoulomb.Gibbs.Basic

/-!
# Theorem 2, Steps 3--4: the per-cell splits of the `A₁` and `A₃` integrands

Source: proof of Theorem 2 (`prop:linear`), Step 3 (l. 1969–1994) and Step 4 (l. 2003–2056),
for `β > 2`. Both steps repeat Steps 2--3 of the proof of Proposition 3.9
on the marked graphs `γ = (φ, T) ∈ D_{2N,K,p,p₀}`. This file contains the parts shared by the two
steps: the identification of the integrands on one cell with the block integrands of
`Fluctuations/TiltedEnergy.lean`, the separation of variables, and the passage from per-cell bounds
to a bound on the Gibbs expectation (the sum over the marked graphs and the division by the
partition function).

Write `I = I^pair` (`pairVerts φ`, `|I| = 2m`), `I'` for the vertices of the marked same-sign pairs
(`markedSameSign φ T`, or `markedSameSignIn φ T` as a set of vertices of `I`), `Z|_I` and
`Z|_{Iᶜ}` for the restrictions, and `α_i = alphaRadius hN λ γ Z i`.

## The `A₁` integrand (Step 3, l. 1969–1978)

`A₁ - F_λ` cancels `F_λ` (`linearA1`): `β A₁ - β F_λ = -β G_α` with
`G_α = -½ ∑_i g_λ(z_i - z_{φ₁ i}) + ∑_{i ∈ I'} (log (α_i / r̃₁(z_i)) - C)`. On a marked cell,

* `alphaPairRadius_subtype_eq`: for a vertex `i ∈ I` whose second neighbours `φ₂(i)`,
  `φ₂(φ₁ i)` lie in `I` (every marked vertex), the radius `α^I_i` computed within `I`
  (`alphaPairRadius`) is `α_i` ("at marked vertices, the second neighbor also lies in `I`",
  l. 1450);
* `linearA1_sub_energy_eq_split`: `A₁ - F_λ = -(G⁽¹⁾_γ(Z|_I) + F⁽²⁾(Z|_{Iᶜ}))` exactly, with
  `G⁽¹⁾_γ = alphaBlockEnergy` and `F⁽²⁾ = nnEnergy` (no energy lower bound such as Corollary 2.3
  is used: "the `F_λ` term of `A₁` cancels exactly", l. 1970);
* `linearA1_sub_energy_eq_full`: the same on all indices (used when `Iᶜ = ∅` or `T = ∅`).

## The `A₃` integrand (Step 4, l. 2011–2020)

* `linearA3_le_sum_pairVerts`: `A₃ ≤ ∑_{i ∈ I} ((r̃₁(z_i)/γ)² ∧ 1)` (the summands of `A₃` are
  nonnegative and indexed by isolated dipoles); `linearA3_eq_zero_of_twiceIsolatedSet_eq_empty`:
  `A₃ = 0` when there is no marked pair (every index of `A₃` is twice isolated);
* `ofReal_exp_linearA3_mul_le_split`, `ofReal_exp_linearA3_mul_le_full`: on a marked cell,
  `e^{t A₃ - β F_λ} ≤ e^{β C (N - K)} e^{t ∑_{i ∈ I} ((r̃₁(z_i)/γ)² ∧ 1) - β F⁽¹⁾(Z|_I)}
  e^{-β F⁽²⁾(Z|_{Iᶜ})}` (from (gred3), i.e. Corollary 2.3, with the distances computed within `I`).

## Generic layer

* `lintegral_markedCell_le_mul_of_le`, `lintegral_markedCell_le_full_of_le`: the separation of
  variables (gred3) for an arbitrary integrand bounded on the cell by a product of block integrands.
* `exists_lintegral_gibbsMeasure_le_of_cellBound_rate`: for a rate `ω` satisfying `UpperRateHyp`
  (`UpperBound/UpperOptimization.lean`) in place of `ω_λ`, the graph sum of Proposition 3.9
  (`UpperAssembly.lintegral_le_of_cellBound_rate`) and the lower bound of Proposition 4.1 give
  `𝔼_ℙ[f] ≤ exp (C N ω(λ) + C log (N + 1) + X)` for any `f` whose cell integrals
  `∫_{cell} f e^{-β F_λ}` satisfy `CellBoundRate` with extra exponent `X`
  ("Subtracting the lower bound of Proposition 4.1", l. 1990–1994, 2051–2056). The rate
  `ω_λ = errorRate β λ` satisfies `UpperRateHyp` (`upperRateHyp_errorRate`).
-/

@[expose] public section

open Finset MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

namespace MomentCells

open UpperCellBound UpperAssembly

variable {N : ℕ}

/-! ### The radii `α` within the isolated-pair block -/

section Bridge

/-- **The radii `α` within `I`** (source l. 1450, 1970): for a vertex `i` of `I = I^pair` whose
second nearest neighbours `φ₂(i)` and `φ₂(φ₁ i)` lie in `I`, the radius `α^I_i` computed within
`I` (`alphaPairRadius`) is the radius `α_i` of Theorem 2, Step 2 (`alphaRadius`). -/
theorem alphaPairRadius_subtype_eq (hN : 2 ≤ N) {Z : Fin N ⊕ Fin N → ℂ}
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} (hφ : nearestNeighbor Z = φ)
    [Nontrivial {i // i ∈ pairVerts φ}] (h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts φ})
    (lam γ : ℝ) (i : {i // i ∈ pairVerts φ})
    (h2 : secondNearestNeighbor hN Z i ∈ pairVerts φ)
    (h2' : secondNearestNeighbor hN Z (nearestNeighbor Z i) ∈ pairVerts φ) :
    alphaPairRadius h3 (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam γ
        (fun j : {i // i ∈ pairVerts φ} => Z j) i = alphaRadius hN lam γ Z i := by
  have hp : ∀ j, j ∈ pairVerts φ → φ j ∈ pairVerts φ := fun _ hj => apply_mem_pairVerts hj
  have hj : (nnMap (subtypeKey (· ∈ pairVerts φ) (sumKey N))
      (fun j : {i // i ∈ pairVerts φ} => Z j) i).1 = nearestNeighbor Z i := by
    rw [nnMap_subtype_val hφ hp i, hφ]
  have hcyc : nearestNeighbor Z (nearestNeighbor Z i) = i := by
    rw [hφ]
    exact (mem_pairVerts.1 i.2).1
  unfold alphaPairRadius alphaRadius
  rw [tau_of_twoCycle hN lam Z hcyc, nnRadius2_subtype_eq hN h3 hφ hp lam i h2,
    nnRadius2_subtype_eq hN h3 hφ hp lam _ (by rw [hj]; exact h2'), hj,
    nnRadius_subtype_eq hφ hp lam i]

/-- **The radii `α` on all indices**: with the key `sumKey N`, `α^I_i = α_i` at every vertex `i` of
a 2-cycle. -/
theorem alphaPairRadius_sumKey_eq [Nontrivial (Fin N ⊕ Fin N)] (hN : 2 ≤ N)
    (h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N)) (lam γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    {i : Fin N ⊕ Fin N} (hi : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    alphaPairRadius h3 (sumKey N) lam γ Z i = alphaRadius hN lam γ Z i := by
  unfold alphaPairRadius alphaRadius
  rw [tau_of_twoCycle hN lam Z hi, ← nearestNeighbor_eq_nnMap,
    ← secondNeighborRadius_eq_nnRadius2 hN h3, ← secondNeighborRadius_eq_nnRadius2 hN h3,
    ← firstNeighborRadius_eq_nnRadius]

end Bridge

/-! ### The `A₁` integrand on a marked cell (source l. 1969–1978) -/

section LinearA1

open scoped Classical in
/-- **`A₁ - F_λ` on a marked cell** (source l. 1969–1978, with (gred3)): if `φ₁(Z) = φ` and the
marked vertices of `Z` are `T`, then
`A₁ - F_λ = -(G⁽¹⁾_γ(Z|_I) + F⁽²⁾(Z|_{Iᶜ}))`, where `G⁽¹⁾_γ = alphaBlockEnergy` on `I = I^pair`
with the logarithmic terms on the marked same-sign vertices, and `F⁽²⁾ = nnEnergy` on `Iᶜ`. -/
theorem linearA1_sub_energy_eq_split (hN : 2 ≤ N) (lam γ C : ℝ) {Z : Fin N ⊕ Fin N → ℂ}
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hφ : nearestNeighbor Z = φ) (hT : twiceIsolatedSet hN Z = T)
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}]
    (h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts φ}) :
    linearA1 hN lam γ C Z - energy lam Z =
      -(alphaBlockEnergy h3 (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam γ C
          (markedSameSignIn φ T) (fun j : {i // i ∈ pairVerts φ} => Z j)
        + nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
          (fun j : {i // i ∉ pairVerts φ} => Z j)) := by
  subst hφ hT
  set P := pairVerts (nearestNeighbor Z) with hPdef
  have hp : ∀ i, i ∈ P → nearestNeighbor Z i ∈ P := fun _ hi => apply_mem_pairVerts hi
  have hsplit := neg_half_sum_smearedKernel_eq (Z := Z) rfl lam
  have hA : ∑ i ∈ markedSameSignIn (nearestNeighbor Z) (twiceIsolatedSet hN Z),
      (Real.log (alphaPairRadius h3 (subtypeKey (· ∈ P) (sumKey N)) lam γ
          (fun j : {i // i ∈ P} => Z j) i / nnRadius lam (fun j : {i // i ∈ P} => Z j) i) - C) =
      ∑ i ∈ markedSameSign (nearestNeighbor Z) (twiceIsolatedSet hN Z),
        (Real.log (alphaRadius hN lam γ Z i / firstNeighborRadius lam Z i) - C) := by
    rw [← Finset.sum_subtype_of_mem (p := (· ∈ P)) _
      (fun x hx => mem_pairVerts_of_mem_twiceIsolatedSet (mem_markedSameSign.1 hx).1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiT := (mem_markedSameSign.1 (mem_subtype.1 hi)).1
    rw [alphaPairRadius_subtype_eq hN rfl h3 lam γ i (secondNearestNeighbor_mem_pairVerts hiT)
      (secondNearestNeighbor_nearestNeighbor_mem_pairVerts hiT), nnRadius_subtype_eq rfl hp lam i]
  unfold linearA1 alphaBlockEnergy
  rw [filter_corollary23_sameSign_eq, hA]
  linarith

open scoped Classical in
/-- **`A₁ - F_λ` on all indices**: for every configuration,
`A₁ - F_λ = -G⁽¹⁾_γ(Z)`, where `G⁽¹⁾_γ = alphaBlockEnergy` is computed on all indices with the key
`sumKey N` and the logarithmic terms on the marked same-sign vertices. -/
theorem linearA1_sub_energy_eq_full [Nontrivial (Fin N ⊕ Fin N)] (hN : 2 ≤ N)
    (h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N)) (lam γ C : ℝ) (Z : Fin N ⊕ Fin N → ℂ) :
    linearA1 hN lam γ C Z - energy lam Z =
      -alphaBlockEnergy h3 (sumKey N) lam γ C
        (markedSameSign (nearestNeighbor Z) (twiceIsolatedSet hN Z)) Z := by
  have hA : ∑ i ∈ markedSameSign (nearestNeighbor Z) (twiceIsolatedSet hN Z),
      (Real.log (alphaPairRadius h3 (sumKey N) lam γ Z i / nnRadius lam Z i) - C) =
      ∑ i ∈ markedSameSign (nearestNeighbor Z) (twiceIsolatedSet hN Z),
        (Real.log (alphaRadius hN lam γ Z i / firstNeighborRadius lam Z i) - C) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hcyc : nearestNeighbor Z (nearestNeighbor Z i) = i :=
      (isTwiceIsolated_of_mem (mem_markedSameSign.1 hi).1).1.nearestNeighbor_nearestNeighbor
    rw [alphaPairRadius_sumKey_eq hN h3 lam γ Z hcyc, firstNeighborRadius_eq_nnRadius]
  unfold linearA1 alphaBlockEnergy
  rw [filter_corollary23_sameSign_eq, nnEnergy_sumKey, hA]
  ring

/-- Without marked vertices there is no marked same-sign vertex. -/
theorem markedSameSign_empty (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) :
    markedSameSign f (∅ : Finset (Fin N ⊕ Fin N)) = ∅ := by
  unfold markedSameSign
  exact filter_empty _

/-- Without marked pairs, `G⁽¹⁾_γ` is the nearest-neighbour energy. -/
theorem alphaBlockEnergy_empty {ι : Type*} [Fintype ι] [Nontrivial ι] (h3 : 3 ≤ Fintype.card ι)
    (key : ι ↪ ℕ) (lam γ C : ℝ) (z : ι → ℂ) :
    alphaBlockEnergy h3 key lam γ C ∅ z = nnEnergy key lam z := by
  simp [alphaBlockEnergy]

/-- The Boltzmann form of the `A₁` integrand: `e^{β A₁} e^{-β F_λ} = e^{β (A₁ - F_λ)}`. -/
theorem ofReal_exp_linearA1_mul (hN : 2 ≤ N) (β lam γ C : ℝ) (Z : Fin N ⊕ Fin N → ℂ) :
    ENNReal.ofReal (Real.exp (β * linearA1 hN lam γ C Z)) *
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) =
      ENNReal.ofReal (Real.exp (β * (linearA1 hN lam γ C Z - energy lam Z))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- `G⁽¹⁾_γ` is a measurable function of the configuration. -/
theorem measurable_alphaBlockEnergy {ι : Type*} [Fintype ι] [Nontrivial ι]
    (h3 : 3 ≤ Fintype.card ι) (key : ι ↪ ℕ) (lam γ C : ℝ) (S : Finset ι) :
    Measurable fun z : ι → ℂ => alphaBlockEnergy h3 key lam γ C S z := by
  classical
  have hr2 : ∀ i, Measurable fun z : ι → ℂ => nnRadius2 h3 key lam z (nnMap key z i) := fun i =>
    measurable_of_nnMap key (F := fun f z => nnRadius2 h3 key lam z (f i)) fun f =>
      measurable_nnRadius2 key h3 lam (f i)
  unfold alphaBlockEnergy alphaPairRadius
  refine (measurable_nnEnergy key lam).add (Finset.measurable_sum _ fun i _ => ?_)
  exact (((((measurable_nnRadius2 key h3 lam i).min (hr2 i)).min measurable_const).max
    (measurable_nnRadius lam i)).div (measurable_nnRadius lam i)).log.sub measurable_const

end LinearA1

/-! ### The `A₃` integrand on a marked cell (source l. 2011–2020) -/

section LinearA3

open scoped Classical in
/-- `A₃ ≤ ∑_{i ∈ I^pair} ((r̃₁(z_i)/γ)² ∧ 1)` (source l. 2012–2015): the summands of `A₃` are
nonnegative, and its indices are vertices of isolated dipoles. -/
theorem linearA3_le_sum_pairVerts (hN : 2 ≤ N) (lam γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ) :
    linearA3 hN lam γ Z ≤ ∑ i ∈ pairVerts (nearestNeighbor Z),
      min ((firstNeighborRadius lam Z i / γ) ^ 2) 1 := by
  unfold linearA3
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_)
    fun i _ _ => le_min (sq_nonneg _) zero_le_one
  exact mem_pairVerts_nearestNeighbor.2 (Finset.mem_filter.1 hi).2.1.isIsolatedPair

open scoped Classical in
/-- `A₃ = 0` without marked pairs: every index of `A₃` is twice isolated. -/
theorem linearA3_eq_zero_of_twiceIsolatedSet_eq_empty (hN : 2 ≤ N) (lam γ : ℝ)
    {Z : Fin N ⊕ Fin N → ℂ} (hT : twiceIsolatedSet hN Z = ∅) : linearA3 hN lam γ Z = 0 := by
  unfold linearA3
  refine Finset.sum_eq_zero fun i hi => ?_
  obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hi
  have hiT : i ∈ twiceIsolatedSet hN Z :=
    (mem_twiceIsolatedSet hN Z).2 ⟨h1.isIsolatedPair, h2.isIsolatedPair, h3⟩
  rw [hT] at hiT
  exact absurd hiT (Finset.notMem_empty i)

/-- The first radii within `I = I^pair` are the global ones:
`∑_{i ∈ I} ((r̃₁(z_i)/γ)² ∧ 1)` is the same sum computed within `I`. -/
theorem sum_pairVerts_eq_sum_subtype {Z : Fin N ⊕ Fin N → ℂ} {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    (hφ : nearestNeighbor Z = φ) [Nontrivial {i // i ∈ pairVerts φ}] (lam γ : ℝ) :
    ∑ i ∈ pairVerts φ, min ((firstNeighborRadius lam Z i / γ) ^ 2) 1 =
      ∑ i : {i // i ∈ pairVerts φ},
        min ((nnRadius lam (fun j : {i // i ∈ pairVerts φ} => Z j) i / γ) ^ 2) 1 := by
  rw [Finset.sum_subtype (pairVerts φ) (p := (· ∈ pairVerts φ)) (fun _ => Iff.rfl)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nnRadius_subtype_eq hφ (fun _ hj => apply_mem_pairVerts hj) lam i]

/-- **The `A₃` integrand on a marked cell** (source l. 2011–2020): for `m ≥ 2`, `Iᶜ ≠ ∅`, `t ≥ 0`
and `β ≥ 0`, on the cell of `γ = (φ, T) ∈ D_{2N,K,p,p₀}`,
`e^{t A₃} e^{-β F_λ} ≤ e^{β C (N - K)} e^{t ∑_{i ∈ I} ((r̃₁(z_i)/γ)² ∧ 1) - β F⁽¹⁾(Z|_I)}
e^{-β F⁽²⁾(Z|_{Iᶜ})}`, with the radii computed within `I` and `C` the constant of Corollary 2.3. -/
theorem ofReal_exp_linearA3_mul_le_split {C : ℝ} (hC0 : 0 ≤ C) (hC : Corollary23Holds C)
    (hN : 2 ≤ N) {lam β t : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ β) (ht : 0 ≤ t) (γ : ℝ)
    {K p p₀ : ℕ} {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hγ : (φ, T) ∈ markedGraphs hN K p p₀)
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}]
    (h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts φ}) {Z : Fin N ⊕ Fin N → ℂ}
    (hZc : Z ∈ markedCell hN φ T) (hZ : ∀ i, Z i ∈ box N) :
    ENNReal.ofReal (Real.exp (t * linearA3 hN lam γ Z)) *
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) ≤
      ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        (ENNReal.ofReal (Real.exp (t * ∑ i : {i // i ∈ pairVerts φ},
            min ((nnRadius lam (fun j : {i // i ∈ pairVerts φ} => Z j) i / γ) ^ 2) 1
            - β * pairAssignedEnergy h3 (subtypeKey (· ∈ pairVerts φ) (sumKey N)) lam C
              (markedSameSignIn φ T) (fun j : {i // i ∈ pairVerts φ} => Z j))) *
          ENNReal.ofReal (Real.exp (-β * nnEnergy (subtypeKey (· ∉ pairVerts φ) (sumKey N)) lam
            (fun j : {i // i ∉ pairVerts φ} => Z j)))) := by
  have hE := le_energy_split hC0 hC hN hlam hZ hZc.1 hZc.2.1 hZc.2.2 h3
  rw [numComponents_eq_of_mem_markedCell hγ hZc] at hE
  have hA := linearA3_le_sum_pairVerts hN lam γ Z
  rw [hZc.2.1, sum_pairVerts_eq_sum_subtype hZc.2.1] at hA
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h1 := mul_le_mul_of_nonneg_left hA ht
  have h2 := mul_le_mul_of_nonneg_left hE hβ
  linarith

/-- **The `A₃` integrand on a marked cell, on all indices** (the case `Iᶜ = ∅`): on the cell of
`γ = (φ, T) ∈ D_{2N,K,p,p₀}`, `e^{t A₃} e^{-β F_λ} ≤ e^{β C (N - K)}
e^{t ∑_i ((r̃₁(z_i)/γ)² ∧ 1) - β F⁽¹⁾(Z)}`, with `F⁽¹⁾` the pair-assigned energy on all indices. -/
theorem ofReal_exp_linearA3_mul_le_full [Nontrivial (Fin N ⊕ Fin N)] {C : ℝ} (hC0 : 0 ≤ C)
    (hC : Corollary23Holds C) (hN : 2 ≤ N) (h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N))
    {lam β t : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ β) (ht : 0 ≤ t) (γ : ℝ) {K p p₀ : ℕ}
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hγ : (φ, T) ∈ markedGraphs hN K p p₀) {Z : Fin N ⊕ Fin N → ℂ}
    (hZc : Z ∈ markedCell hN φ T) (hZ : ∀ i, Z i ∈ box N) :
    ENNReal.ofReal (Real.exp (t * linearA3 hN lam γ Z)) *
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) ≤
      ENNReal.ofReal (Real.exp (β * (C * ((N : ℝ) - K)))) *
        ENNReal.ofReal (Real.exp (t * ∑ i, min ((nnRadius lam Z i / γ) ^ 2) 1
          - β * pairAssignedEnergy h3 (sumKey N) lam C (markedSameSign φ T) Z)) := by
  have hE := le_energy_full hC0 hC hN h3 hlam hZ hZc.1 hZc.2.1 hZc.2.2
  rw [numComponents_eq_of_mem_markedCell hγ hZc] at hE
  have hA : linearA3 hN lam γ Z ≤ ∑ i, min ((nnRadius lam Z i / γ) ^ 2) 1 := by
    refine (linearA3_le_sum_pairVerts hN lam γ Z).trans ?_
    simp_rw [firstNeighborRadius_eq_nnRadius]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => le_min (sq_nonneg _) zero_le_one
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h1 := mul_le_mul_of_nonneg_left hA ht
  have h2 := mul_le_mul_of_nonneg_left hE hβ
  linarith

end LinearA3

/-! ### The separation of variables for an arbitrary integrand (gred3) -/

section Separation

/-- **(gred3) for an arbitrary integrand** (source l. 1454–1459): if on the cell of
`γ = (φ, T)` the integrand satisfies `F(Z) ≤ e^b g₁(Z|_I) g₂(Z|_{Iᶜ})`, then
`∫_{Λ^{2N} ∩ E ∩ {γ_{2N} = γ}} F ≤ e^b ∫_{Λ^{2m} ∩ {γ_{2m} = γ¹}} g₁
  ∫_{Λ^{2N-2m} ∩ {γ_{2N-2m} = γ²}} g₂`. -/
theorem lintegral_markedCell_le_mul_of_le (hN : 2 ≤ N) {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    {T : Finset (Fin N ⊕ Fin N)}
    [Nontrivial {i // i ∈ pairVerts φ}] [Nontrivial {i // i ∉ pairVerts φ}]
    (E : Set (Fin N ⊕ Fin N → ℂ)) (F : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) (b : ℝ)
    {g₁ : ({i // i ∈ pairVerts φ} → ℂ) → ℝ≥0∞} {g₂ : ({i // i ∉ pairVerts φ} → ℂ) → ℝ≥0∞}
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (hF : ∀ Z ∈ markedCell hN φ T, (∀ i, Z i ∈ box N) →
      F Z ≤ ENNReal.ofReal (Real.exp b) * (g₁ (fun j : {i // i ∈ pairVerts φ} => Z j) *
        g₂ (fun j : {i // i ∉ pairVerts φ} => Z j))) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T, F Z ≤
      ENNReal.ofReal (Real.exp b) *
        ((∫⁻ x in (Set.univ.pi fun _ : {i // i ∈ pairVerts φ} => box N) ∩
            {x | nnMap (subtypeKey (· ∈ pairVerts φ) (sumKey N)) x = pairRestrict φ}, g₁ x) *
          ∫⁻ y in (Set.univ.pi fun _ : {i // i ∉ pairVerts φ} => box N) ∩
            {y | nnMap (subtypeKey (· ∉ pairVerts φ) (sumKey N)) y = complRestrict φ}, g₂ y) := by
  classical
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ T)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T, F Z :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp b) * (g₁ (fun j : {i // i ∈ pairVerts φ} => Z j) *
          g₂ (fun j : {i // i ∉ pairVerts φ} => Z j)) :=
        setLIntegral_mono' hmeas fun Z hZ => hF Z hZ.2 fun i => hZ.1 i (Set.mem_univ i)
    _ = ENNReal.ofReal (Real.exp b) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
          g₁ (fun j : {i // i ∈ pairVerts φ} => Z j) *
            g₂ (fun j : {i // i ∉ pairVerts φ} => Z j) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (setLIntegral_subtype_mul_le (pairVerts φ) (box N)
          (markedCell hN φ T) _ _
          (fun Z hZ => ⟨nnMap_pairRestrict hZ.2.1, nnMap_complRestrict hZ.2.1⟩) hg₁ hg₂) _

/-- **The cell integral of an arbitrary integrand, on all indices**: if on the cell of
`γ = (φ, T)` the integrand satisfies `F(Z) ≤ e^b g(Z)`, then
`∫_{Λ^{2N} ∩ E ∩ {γ_{2N} = γ}} F ≤ e^b ∫_{Λ^{2N} ∩ {γ_{2N} = φ}} g`. -/
theorem lintegral_markedCell_le_full_of_le [Nontrivial (Fin N ⊕ Fin N)] (hN : 2 ≤ N)
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (E : Set (Fin N ⊕ Fin N → ℂ)) (F g : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) (b : ℝ)
    (hF : ∀ Z ∈ markedCell hN φ T, (∀ i, Z i ∈ box N) → F Z ≤ ENNReal.ofReal (Real.exp b) * g Z) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T, F Z ≤
      ENNReal.ofReal (Real.exp b) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nnMap (sumKey N) Z = φ},
          g Z := by
  have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T) :=
    (measurableSet_pi_box N).inter (measurableSet_markedCell hN φ T)
  calc _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T, F Z :=
        lintegral_mono_set (Set.inter_subset_inter_left _ Set.inter_subset_left)
    _ ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T,
        ENNReal.ofReal (Real.exp b) * g Z :=
        setLIntegral_mono' hmeas fun Z hZ => hF Z hZ.2 fun i => hZ.1 i (Set.mem_univ i)
    _ = ENNReal.ofReal (Real.exp b) *
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ markedCell hN φ T, g Z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right (lintegral_mono_set ?_) _
        rintro Z ⟨hZΛ, hZc⟩
        exact ⟨hZΛ, (nearestNeighbor_eq_nnMap_fun Z).symm.trans hZc.2.1⟩

end Separation

/-! ### The per-cell bound and the Gibbs expectation -/

section Gibbs

/-- **From the per-cell bounds to the Gibbs expectation, generic rate** (source l. 1990–2002, 2045–2056), for a rate `ω` satisfying `UpperRateHyp` in place of `ω_λ`, with cell integrals
satisfying `CellBoundRate`. For `β > 2` and constants `A`, `c > 0`, `C_b ≥ 0` there are `C > 0` and
`0 < λ₁ ≤ e⁻¹`, depending only on `β, ω, A, c, C_b`, such that for `N ≥ 2`, `0 < λ < λ₁`, every
integrand `f ≥ 0` and every extra exponent `X`: if for every marked graph `γ ∈ D_{2N,K,p,p₀}` the
cell integral `∫_{Λ^{2N} ∩ {γ_{2N} = γ}} f e^{-β F_λ}` satisfies `CellBoundRate` with the extra
exponent `X`, then `𝔼_ℙ[f] ≤ exp (C N ω(λ) + C log (N + 1) + X)`.

The division by the partition function uses the lower bound of Proposition 4.1. For `β > 2` its
error rate (`λ^{β-2}`, `λ² ℓ²`, `λ² ℓ` for `2 < β < 4`, `β = 4`, `β > 4`) is the error rate of
Proposition 3.8, which the field `UpperRateHyp.isolated_le` bounds by `ω(λ)` for `0 < λ ≤ e⁻¹`
; no further property of `ω` is used. -/
theorem exists_lintegral_gibbsMeasure_le_of_cellBound_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ)
    (hω : UpperRateHyp β hβ ω) (A c Cb : ℝ) (hc : 0 < c) (hCb : 0 ≤ Cb) :
    ∃ C lam₁ : ℝ, 0 < C ∧ 0 < lam₁ ∧ lam₁ ≤ Real.exp (-1) ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam < lam₁ →
      ∀ (f : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) (X : ℝ),
      (∀ (K p p₀ : ℕ) (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (T : Finset (Fin N ⊕ Fin N)),
        (φ, T) ∈ markedGraphs hN K p p₀ →
          CellBoundRate β hβ ω A c Cb N K p p₀ lam X
            (∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ Set.univ ∩ markedCell hN φ T,
              f Z * ENNReal.ofReal (Real.exp (-β * energy lam Z)))) →
      ∫⁻ Z, f Z ∂gibbsMeasure N β lam ≤
        ENNReal.ofReal (Real.exp (C * N * ω lam + C * Real.log (N + 1) + X)) := by
  obtain ⟨c', C', lam₀, hc', hC', hlam₀, hlam₀1, hsum⟩ :=
    lintegral_le_of_cellBound_rate hβ ω hω A c Cb hc hCb
  obtain ⟨lam₂, C₂, hlam₂, hC₂, hlow⟩ := proposition_4_1 β hβ.le
  refine ⟨C' + C₂ + 3, min lam₀ lam₂, by positivity, lt_min hlam₀ hlam₂,
    (min_le_left _ _).trans hlam₀1, ?_⟩
  intro N hN lam hlam hlamlt f X hcell
  have hlam0 : lam < lam₀ := hlamlt.trans_le (min_le_left _ _)
  have hlam2 : lam < lam₂ := hlamlt.trans_le (min_le_right _ _)
  have hlam1 : lam ≤ Real.exp (-1) := hlam0.le.trans hlam₀1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- the graph sum
  have hU := hsum N hN lam hlam hlam0 Set.univ
    (fun Z => f Z * ENNReal.ofReal (Real.exp (-β * energy lam Z))) X N le_rfl
    (fun K p p₀ φ T hγ => ⟨hcell K p p₀ φ T hγ, fun hlt => by
      obtain ⟨h1, h2, h3, -⟩ := constraints_of_nonempty ⟨_, hγ⟩
      omega⟩)
  rw [Set.inter_univ] at hU
  -- the lower bound of Proposition 4.1
  have hL := hlow N hN lam hlam hlam2
  rw [ite_eq_right hβ.ne', ite_eq_right hβ.ne'] at hL
  obtain ⟨hr0, hr⟩ := isolatedRate_le_rate hβ ω hω hlam hlam1
  rw [ite_eq_right hβ.ne'] at hr0 hr
  set rate := (if β < 4 then lam ^ (β - 2) else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
    else lam ^ 2 * |Real.log lam|) with hrate
  set lower := 2 * N * Real.log N + N * ((2 - β) * Real.log lam
    + (Real.log (dipoleConstant β hβ.le) - 1)) - C₂ * N * rate with hlower
  have hZinv : (partitionFunction N β lam)⁻¹ ≤ ENNReal.ofReal (Real.exp (-lower)) := by
    rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]
    exact ENNReal.inv_le_inv.2 hL
  rw [lintegral_gibbsMeasure']
  refine (mul_le_mul' hZinv hU).trans ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hω0 : 0 ≤ ω lam := hr0.trans hr
  have hlogN : 0 ≤ Real.log (N + 1) := Real.log_nonneg (le_add_of_nonneg_left hN0.le)
  have e1 : C₂ * N * rate ≤ C₂ * N * ω lam :=
    mul_le_mul_of_nonneg_left hr (by positivity)
  have e2 : c' * ((N : ℝ) - N) ^ 2 / N = 0 := by simp
  have e3 : 0 ≤ (N : ℝ) * ω lam := mul_nonneg hN0.le hω0
  have e4 : (C' + 3) * Real.log (N + 1) ≤ (C' + C₂ + 3) * Real.log (N + 1) :=
    mul_le_mul_of_nonneg_right (by linarith only [hC₂]) hlogN
  rw [hlower]
  linarith only [e1, e2, e3, e4]

end Gibbs

end MomentCells

end TwoComponentCoulomb

end
