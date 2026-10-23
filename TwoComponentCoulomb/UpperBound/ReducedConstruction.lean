/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.NearestNeighbor
public import TwoComponentCoulomb.Frozen.ReducedEnergy
public import TwoComponentCoulomb.Frozen.ReducedPartitionFunction
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.NearestNeighbor.Basic
public import TwoComponentCoulomb.PhaseSpace.Placement
public import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Gibbs.Measurability
import TwoComponentCoulomb.Integrals.PiProduct
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# The lower-bound construction for the reduced partition function

Source: l. 920–923 (`β = 2`) and 982--1001 (`β > 2`): proof of the lower
bound in Lemma 3.5. Fix `t > 0`. Restrict the positive charges `X` to the set
`H = placementSet N N t (4 t)` (boundary distance at least `t`, mutual distances at least `4 t`),
let `σ` be a permutation of the labels of the negative charges, and put
`Y (σ i) = X i + u_i` with `a ≤ |u_i| ≤ b ≤ t`. Then all points lie on `N` neutral `2`-cycles
`{x_i, y_{σ i}}`, so that `F̃_λ = -∑ᵢ g_λ(x_i - y_{σ i})`; the regions for distinct `σ` are
disjoint; and Fubini gives the contribution `vol(H) (∫_{a ≤ |u| ≤ b} e^{β g_λ(u)} du)^N` of each
`σ`. The positive and negative charges are separated with the measure-preserving equivalence
`(Fin N ⊕ Fin N → ℂ) ≃ (Fin N → ℂ) × (Fin N → ℂ)`.

* `nearestNeighbor_inl_paired`, `nearestNeighbor_inr_paired` : the nearest neighbour of `x_i` is
  `y_{σ i}` and conversely (strictly, so no tie-break is involved).
* `reducedEnergy_paired` : `F̃_λ(x, y) = -∑ᵢ g_λ(x_i - y_{σ i})`.
* `mem_box_of_norm_sub_le` : the negative charges lie in the box `Λ`.
* `pairingRegion`, `measurableSet_pairingRegion`, `pairwise_disjoint_pairingRegion` : the regions
  `A_σ`, which are measurable and pairwise disjoint.
* `lintegral_pairingRegion` : the Boltzmann integral over `A_σ` is
  `vol(H) (∫ pairWeight)^N` (Fubini over `X` then `Y`).
* `reducedPartitionFunction_ge_construction_lintegral`,
  `reducedPartitionFunction_ge_construction` : the lower bound
  `N! · vol(H) · (∫_{a ≤ |u| ≤ b} e^{β g_λ(u)} du)^N ≤ 𝒦_{N,β}^λ`, in `[0, ∞]` and with the real
  annulus integral.
* `integral_annulus_exp_two_smearedKernel` and `reducedPartitionFunction_two_ge_construction` :
  the case `β = 2`, `a = 2λ`, `b = t²` (`t ≤ 1`), where the annulus integral is exactly
  `2π log (t² / (2λ))`.
* `reducedPartitionFunction_ge_construction_of_two_lt` : the case `β > 2`, `a = 0`, `b = t`, with
  the lower bound `𝒵_β λ^{2-β} (1 - C (λ/t)^{β-2})` for the annulus integral.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Nat

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### The nearest-neighbour graph of a paired configuration -/

/-- The nearest neighbour of `x_i` is `y_{σ i}` (strictly, so no tie-break is involved). -/
theorem nearestNeighbor_inl_paired {X Y : Fin N → ℂ} {σ : Equiv.Perm (Fin N)} {t : ℝ}
    (ht : 0 < t) (hX : X ∈ placementSet N N t (4 * t)) (hY : ∀ i, ‖Y (σ i) - X i‖ ≤ t)
    (i : Fin N) :
    nearestNeighbor (Sum.elim X Y) (Sum.inl i) = Sum.inr (σ i) := by
  refine nearestNeighbor_eq_of_forall_lt _ (by simp) ?_
  rintro (j | m) hk1 hk2
  · have hji : j ≠ i := fun h => hk1 (by rw [h])
    simp only [Sum.elim_inl, Sum.elim_inr]
    have h1 := hX.2 i j hji.symm
    have h2 := hY i
    rw [norm_sub_rev] at h2
    linarith
  · obtain ⟨j, rfl⟩ := σ.surjective m
    have hji : j ≠ i := fun h => hk2 (by rw [h])
    simp only [Sum.elim_inl, Sum.elim_inr]
    have h1 := hX.2 i j hji.symm
    have h2 := hY j
    have h3 := hY i
    rw [norm_sub_rev] at h3
    have h4 := norm_sub_le_norm_sub_add_norm_sub (X i) (Y (σ j)) (X j)
    linarith

/-- The nearest neighbour of `y_{σ i}` is `x_i` (strictly, so no tie-break is involved). -/
theorem nearestNeighbor_inr_paired {X Y : Fin N → ℂ} {σ : Equiv.Perm (Fin N)} {t : ℝ}
    (ht : 0 < t) (hX : X ∈ placementSet N N t (4 * t)) (hY : ∀ i, ‖Y (σ i) - X i‖ ≤ t)
    (i : Fin N) :
    nearestNeighbor (Sum.elim X Y) (Sum.inr (σ i)) = Sum.inl i := by
  refine nearestNeighbor_eq_of_forall_lt _ (by simp) ?_
  rintro (j | m) hk1 hk2
  · have hji : j ≠ i := fun h => hk2 (by rw [h])
    simp only [Sum.elim_inl, Sum.elim_inr]
    have h1 := hX.2 i j hji.symm
    have h2 := hY i
    have h4 := norm_sub_le_norm_sub_add_norm_sub (X i) (Y (σ i)) (X j)
    rw [norm_sub_rev (X i) (Y (σ i))] at h4
    linarith
  · obtain ⟨j, rfl⟩ := σ.surjective m
    have hji : j ≠ i := fun h => hk1 (by rw [h])
    simp only [Sum.elim_inl, Sum.elim_inr]
    have h1 := hX.2 i j hji.symm
    have h2 := hY j
    have h3 := hY i
    have e : X i - X j = (X i - Y (σ i)) + (Y (σ i) - Y (σ j)) + (Y (σ j) - X j) := by ring
    have h4 := norm_add₃_le (a := X i - Y (σ i)) (b := Y (σ i) - Y (σ j)) (c := Y (σ j) - X j)
    rw [← e, norm_sub_rev (X i) (Y (σ i))] at h4
    linarith

/-- **Energy of a paired configuration** : all `2N` points lie on `N`
neutral `2`-cycles, so `F̃_λ(x, y) = -∑ᵢ g_λ(x_i - y_{σ i})`. -/
theorem reducedEnergy_paired (lam : ℝ) {X Y : Fin N → ℂ} {σ : Equiv.Perm (Fin N)} {t : ℝ}
    (ht : 0 < t) (hX : X ∈ placementSet N N t (4 * t)) (hY : ∀ i, ‖Y (σ i) - X i‖ ≤ t) :
    reducedEnergy lam (Sum.elim X Y) = -∑ i, smearedKernel lam (X i - Y (σ i)) := by
  unfold reducedEnergy
  rw [Fintype.sum_sum_type]
  have hl : ∀ i : Fin N, (if nearestNeighbor (Sum.elim X Y)
        (nearestNeighbor (Sum.elim X Y) (Sum.inl i)) = Sum.inl i ∧
      charge (Sum.inl i : Fin N ⊕ Fin N) *
        charge (nearestNeighbor (Sum.elim X Y) (Sum.inl i)) = -1 then
      smearedKernel lam (Sum.elim X Y (Sum.inl i) -
        Sum.elim X Y (nearestNeighbor (Sum.elim X Y) (Sum.inl i))) else 0)
      = smearedKernel lam (X i - Y (σ i)) := by
    intro i
    rw [nearestNeighbor_inl_paired ht hX hY, nearestNeighbor_inr_paired ht hX hY, ite_eq_left]
    · rfl
    · simp [charge_inl, charge_inr]
  have hr : ∀ j : Fin N, (if nearestNeighbor (Sum.elim X Y)
        (nearestNeighbor (Sum.elim X Y) (Sum.inr j)) = Sum.inr j ∧
      charge (Sum.inr j : Fin N ⊕ Fin N) *
        charge (nearestNeighbor (Sum.elim X Y) (Sum.inr j)) = -1 then
      smearedKernel lam (Sum.elim X Y (Sum.inr j) -
        Sum.elim X Y (nearestNeighbor (Sum.elim X Y) (Sum.inr j))) else 0)
      = smearedKernel lam (X (σ.symm j) - Y j) := by
    intro j
    obtain ⟨i, rfl⟩ := σ.surjective j
    rw [nearestNeighbor_inr_paired ht hX hY, nearestNeighbor_inl_paired ht hX hY, ite_eq_left]
    · simp only [Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply]
      rw [← smearedKernel_neg lam, neg_sub]
    · simp [charge_inl, charge_inr]
  simp only [hl, hr]
  rw [← Equiv.sum_comp σ (fun j => smearedKernel lam (X (σ.symm j) - Y j))]
  simp only [Equiv.symm_apply_apply]
  ring

/-- The negative charge `Y (σ i)` lies in the box `Λ` as soon as it is within `t` of `X i`, for
`X` in the placement set with boundary distance `t`. -/
theorem mem_box_of_norm_sub_le {X : Fin N → ℂ} {t : ℝ} {b : ℝ}
    (hX : X ∈ placementSet N N t b) {y : ℂ} {i : Fin N} (hy : ‖y - X i‖ ≤ t) :
    y ∈ box N := by
  have h := hX.1 i
  rw [Complex.mem_reProdIm] at h
  have hre := (Complex.abs_re_le_norm (y - X i)).trans hy
  have him := (Complex.abs_im_le_norm (y - X i)).trans hy
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  rw [box, Complex.mem_reProdIm]
  exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩, ⟨by linarith [h.2.1], by linarith [h.2.2]⟩⟩

/-! ### The weight of one dipole -/

/-- The annulus `{a ≤ |u| ≤ b}` is closed. -/
private theorem isClosed_annulus (a b : ℝ) : IsClosed {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ ≤ b} :=
  (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

/-- The annulus `{a ≤ |u| ≤ b}` is measurable. -/
private theorem measurableSet_annulus (a b : ℝ) : MeasurableSet {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ ≤ b} :=
  (isClosed_annulus a b).measurableSet

/-- The Boltzmann weight `e^{β g_λ(u)}` of one dipole of displacement `u`, restricted to the
annulus `a ≤ |u| ≤ b` and valued in `[0, ∞]`. -/
noncomputable def pairWeight (β lam a b : ℝ) : ℂ → ℝ≥0∞ :=
  {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ ≤ b}.indicator fun u => ENNReal.ofReal (Real.exp (β * smearedKernel lam u))

theorem measurable_pairWeight (β lam a b : ℝ) : Measurable (pairWeight β lam a b) :=
  (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_smearedKernel lam).const_mul β))).indicator (measurableSet_annulus a b)

theorem lintegral_pairWeight (β lam a b : ℝ) :
    ∫⁻ u, pairWeight β lam a b u =
      ∫⁻ u in {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ ≤ b}, ENNReal.ofReal (Real.exp (β * smearedKernel lam u)) :=
  lintegral_indicator (measurableSet_annulus a b) _

/-! ### The regions `A_σ` -/

/-- The region `A_σ` of the pair space `(Fin N → ℂ) × (Fin N → ℂ)`: the positive charges `X` lie
in `H = placementSet N N t (4 t)` and each negative charge `Y (σ i)` is at distance between `a`
and `b` of `X i` (source l. 920, 932). -/
def pairingRegion (N : ℕ) (t a b : ℝ) (σ : Equiv.Perm (Fin N)) :
    Set ((Fin N → ℂ) × (Fin N → ℂ)) :=
  {p | p.1 ∈ placementSet N N t (4 * t) ∧ ∀ i, a ≤ ‖p.2 (σ i) - p.1 i‖ ∧ ‖p.2 (σ i) - p.1 i‖ ≤ b}

theorem measurableSet_pairingRegion (N : ℕ) (t a b : ℝ) (σ : Equiv.Perm (Fin N)) :
    MeasurableSet (pairingRegion N t a b σ) := by
  have h1 : MeasurableSet {p : (Fin N → ℂ) × (Fin N → ℂ) |
      p.1 ∈ placementSet N N t (4 * t)} := measurable_fst (measurableSet_placementSet N N t _)
  have h2 : MeasurableSet {p : (Fin N → ℂ) × (Fin N → ℂ) |
      ∀ i, a ≤ ‖p.2 (σ i) - p.1 i‖ ∧ ‖p.2 (σ i) - p.1 i‖ ≤ b} := by
    simp_rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i => ?_
    have hm : Measurable fun p : (Fin N → ℂ) × (Fin N → ℂ) => ‖p.2 (σ i) - p.1 i‖ := by
      fun_prop
    exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  exact h1.inter h2

/-- The regions `A_σ` are disjoint for distinct `σ` : each `y` lies
within `t` of at most one `x_i`, the discs `B(x_i, t)` being disjoint. -/
theorem pairwise_disjoint_pairingRegion {t a b : ℝ} (ht : 0 < t) (hb : b ≤ t) :
    Pairwise (Function.onFun Disjoint (pairingRegion N t a b)) := by
  intro σ τ hστ
  refine Set.disjoint_left.2 fun p hσ hτ => hστ ?_
  ext i
  -- `p.2 (σ i)` is within `t` of `p.1 i` and `p.2 (τ j)` is within `t` of `p.1 j`
  obtain ⟨j, hj⟩ := τ.surjective (σ i)
  by_cases hji : j = i
  · rw [← hj, hji]
  · exfalso
    have h1 := (hσ.2 i).2
    have h2 := (hτ.2 j).2
    rw [hj] at h2
    have h3 := hσ.1.2 i j (Ne.symm hji)
    have h4 := norm_sub_le_norm_sub_add_norm_sub (p.1 i) (p.2 (σ i)) (p.1 j)
    rw [norm_sub_rev (p.1 i) (p.2 (σ i))] at h4
    linarith

/-! ### The integral over `A_σ` -/

/-- On the fibre over `X ∈ H`, the Boltzmann weight restricted to `A_σ` is the product of the
weights of the `N` dipoles . -/
theorem indicator_pairingRegion_eq_prod {β lam t a b : ℝ} {σ : Equiv.Perm (Fin N)}
    (ht : 0 < t) (hb : b ≤ t) {X : Fin N → ℂ} (hX : X ∈ placementSet N N t (4 * t))
    (Y : Fin N → ℂ) :
    (pairingRegion N t a b σ).indicator
        (fun p : (Fin N → ℂ) × (Fin N → ℂ) =>
          ENNReal.ofReal (Real.exp (-β * reducedEnergy lam (Sum.elim p.1 p.2)))) (X, Y) =
      ∏ i, pairWeight β lam a b (Y (σ i) - X i) := by
  by_cases h : (X, Y) ∈ pairingRegion N t a b σ
  · have hY : ∀ i, ‖Y (σ i) - X i‖ ≤ t := fun i => (h.2 i).2.trans hb
    rw [Set.indicator_of_mem h]
    simp only
    rw [reducedEnergy_paired lam ht hX hY]
    have h1 : ∀ i, pairWeight β lam a b (Y (σ i) - X i) =
        ENNReal.ofReal (Real.exp (β * smearedKernel lam (X i - Y (σ i)))) := by
      intro i
      rw [pairWeight, Set.indicator_of_mem
        (show Y (σ i) - X i ∈ {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ ≤ b} from h.2 i),
        ← smearedKernel_neg lam, neg_sub]
    simp_rw [h1]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
      ← Finset.mul_sum]
    congr 2
    ring
  · rw [Set.indicator_of_notMem h]
    symm
    have h2 : ¬ ∀ i, a ≤ ‖Y (σ i) - X i‖ ∧ ‖Y (σ i) - X i‖ ≤ b := fun h' => h ⟨hX, h'⟩
    push Not at h2
    obtain ⟨i, hi⟩ := h2
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [pairWeight, Set.indicator_of_notMem]
    intro hmem
    exact absurd (hi hmem.1) (not_lt.2 hmem.2)

/-- The inner integral over the negative charges: for fixed `X`, the product of the dipole
weights integrates to `(∫ pairWeight)^N` (Fubini, source ). -/
theorem lintegral_prod_pairWeight (β lam a b : ℝ) (σ : Equiv.Perm (Fin N)) (X : Fin N → ℂ) :
    ∫⁻ Y : Fin N → ℂ, ∏ i, pairWeight β lam a b (Y (σ i) - X i) =
      (∫⁻ u, pairWeight β lam a b u) ^ N := by
  have h1 : ∀ Y : Fin N → ℂ, ∏ i, pairWeight β lam a b (Y (σ i) - X i) =
      ∏ j, pairWeight β lam a b (Y j - X (σ.symm j)) := by
    intro Y
    rw [← Equiv.prod_comp σ (fun j => pairWeight β lam a b (Y j - X (σ.symm j)))]
    simp only [Equiv.symm_apply_apply]
  simp_rw [h1]
  rw [volume_pi, lintegral_fintype_pi_prod volume
    (fun j v => pairWeight β lam a b (v - X (σ.symm j)))
    (fun j => (measurable_pairWeight β lam a b).comp (measurable_sub_const _))]
  simp_rw [lintegral_sub_right_eq_self (pairWeight β lam a b)]
  simp

/-- The Boltzmann weight on the pair space `(Fin N → ℂ) × (Fin N → ℂ)` is measurable. -/
theorem measurable_weight_pair (β lam : ℝ) :
    Measurable fun p : (Fin N → ℂ) × (Fin N → ℂ) =>
      ENNReal.ofReal (Real.exp (-β * reducedEnergy lam (Sum.elim p.1 p.2))) := by
  have hZ : Measurable fun p : (Fin N → ℂ) × (Fin N → ℂ) => (Sum.elim p.1 p.2 : Fin N ⊕ Fin N → ℂ) := by
    refine measurable_pi_iff.2 fun k => ?_
    cases k with
    | inl i => exact (measurable_pi_apply i).comp measurable_fst
    | inr i => exact (measurable_pi_apply i).comp measurable_snd
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((measurable_reducedEnergy lam).comp hZ).const_mul (-β)))

/-- **The contribution of one permutation** : the Boltzmann integral over
`A_σ` equals `vol(H) (∫ pairWeight)^N`. -/
theorem lintegral_pairingRegion {β lam t a b : ℝ} (σ : Equiv.Perm (Fin N)) (ht : 0 < t)
    (hb : b ≤ t) :
    ∫⁻ p in pairingRegion N t a b σ,
        ENNReal.ofReal (Real.exp (-β * reducedEnergy lam (Sum.elim p.1 p.2))) =
      volume (placementSet N N t (4 * t)) * (∫⁻ u, pairWeight β lam a b u) ^ N := by
  rw [← lintegral_indicator (measurableSet_pairingRegion N t a b σ), Measure.volume_eq_prod,
    lintegral_prod _
      ((measurable_weight_pair β lam).indicator (measurableSet_pairingRegion N t a b σ)).aemeasurable]
  have h : ∀ X : Fin N → ℂ, ∫⁻ Y : Fin N → ℂ, (pairingRegion N t a b σ).indicator
      (fun p : (Fin N → ℂ) × (Fin N → ℂ) =>
        ENNReal.ofReal (Real.exp (-β * reducedEnergy lam (Sum.elim p.1 p.2)))) (X, Y) =
      (placementSet N N t (4 * t)).indicator (fun _ => (∫⁻ u, pairWeight β lam a b u) ^ N) X := by
    intro X
    by_cases hX : X ∈ placementSet N N t (4 * t)
    · rw [Set.indicator_of_mem hX]
      simp_rw [indicator_pairingRegion_eq_prod ht hb hX]
      exact lintegral_prod_pairWeight β lam a b σ X
    · rw [Set.indicator_of_notMem hX]
      have : ∀ Y : Fin N → ℂ, (pairingRegion N t a b σ).indicator
          (fun p : (Fin N → ℂ) × (Fin N → ℂ) =>
            ENNReal.ofReal (Real.exp (-β * reducedEnergy lam (Sum.elim p.1 p.2)))) (X, Y) = 0 :=
        fun Y => Set.indicator_of_notMem (fun h => hX h.1) _
      simp_rw [this]
      simp
  simp_rw [h]
  rw [lintegral_indicator_const (measurableSet_placementSet N N t _), mul_comm]

/-! ### The lower bound -/

/-- Every point of a configuration in `A_σ` lies in the box `Λ`. -/
theorem sumElim_mem_pi_box_of_mem_pairingRegion {t a b : ℝ} {σ : Equiv.Perm (Fin N)}
    (ht : 0 < t) (hb : b ≤ t) {p : (Fin N → ℂ) × (Fin N → ℂ)}
    (hp : p ∈ pairingRegion N t a b σ) :
    (Sum.elim p.1 p.2 : Fin N ⊕ Fin N → ℂ) ∈ Set.univ.pi fun _ : Fin N ⊕ Fin N => box N := by
  rintro (i | m) -
  · exact placementSet_subset_box ht.le p.1 hp.1 i
  · obtain ⟨i, rfl⟩ := σ.surjective m
    exact mem_box_of_norm_sub_le hp.1 ((hp.2 i).2.trans hb)

/-- **Lemma 3.5, lower bound, construction** (source l. 920–923, 932–945), in `[0, ∞]`:
for `t > 0` and `b ≤ t`,
`N! · vol(H) · (∫_{a ≤ |u| ≤ b} e^{β g_λ(u)} du)^N ≤ 𝒦_{N,β}^λ`, where
`H = placementSet N N t (4 t)`. The `N!` assignments of negative labels give disjoint regions. -/
theorem reducedPartitionFunction_ge_construction_lintegral (β lam : ℝ) {t a b : ℝ}
    (ht : 0 < t) (hb : b ≤ t) :
    (N ! : ℝ≥0∞) * volume (placementSet N N t (4 * t)) *
        (∫⁻ u in {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ ≤ b},
          ENNReal.ofReal (Real.exp (β * smearedKernel lam u))) ^ N ≤
      reducedPartitionFunction N β lam := by
  set Φ := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin N => ℂ)).symm with hΦ
  have hΦp : ∀ p : (Fin N → ℂ) × (Fin N → ℂ), Φ p = Sum.elim p.1 p.2 := fun p =>
    funext fun k => by cases k <;> rfl
  have hmp : MeasurePreserving Φ volume volume :=
    volume_measurePreserving_sumPiEquivProdPi_symm _
  have e1 := hmp.setLIntegral_comp_preimage_emb Φ.measurableEmbedding
    (fun Z => ENNReal.ofReal (Real.exp (-β * reducedEnergy lam Z)))
    (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N)
  unfold reducedPartitionFunction
  rw [← e1]
  simp_rw [hΦp]
  calc (N ! : ℝ≥0∞) * volume (placementSet N N t (4 * t)) *
        (∫⁻ u in {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ ≤ b},
          ENNReal.ofReal (Real.exp (β * smearedKernel lam u))) ^ N
      = ∑ σ : Equiv.Perm (Fin N), ∫⁻ p in pairingRegion N t a b σ,
          ENNReal.ofReal (Real.exp (-β * reducedEnergy lam (Sum.elim p.1 p.2))) := by
        simp_rw [lintegral_pairingRegion _ ht hb, ← lintegral_pairWeight β lam a b]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
          mul_assoc]
    _ = ∫⁻ p in ⋃ σ, pairingRegion N t a b σ,
          ENNReal.ofReal (Real.exp (-β * reducedEnergy lam (Sum.elim p.1 p.2))) := by
        rw [lintegral_iUnion (fun σ => measurableSet_pairingRegion N t a b σ)
          (pairwise_disjoint_pairingRegion ht hb), tsum_fintype]
    _ ≤ _ := by
        refine lintegral_mono_set fun p hp => ?_
        obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 hp
        rw [Set.mem_preimage, hΦp]
        exact sumElim_mem_pi_box_of_mem_pairingRegion ht hb hσ

/-- For `λ > 0`, `e^{β g_λ}` is integrable on every annulus `{a ≤ |u| ≤ b}`: it is continuous
and the annulus is compact. -/
theorem integrableOn_annulus_exp_smearedKernel (β : ℝ) {lam : ℝ} (hlam : 0 < lam) (a b : ℝ) :
    IntegrableOn (fun u : ℂ => Real.exp (β * smearedKernel lam u))
      {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ ≤ b} := by
  have hK : IsCompact {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ ≤ b} := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_annulus a b) ?_
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := b)).subset fun u hu => ?_
    simpa using hu.2
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_smearedKernel hlam))).continuousOn.integrableOn_compact hK

/-- **Lemma 3.5, lower bound, construction** (source l. 920–923, 932–945): for `λ > 0`,
`t > 0` and `b ≤ t`,
`N! · vol(H) · (∫_{a ≤ |u| ≤ b} e^{β g_λ(u)} du)^N ≤ 𝒦_{N,β}^λ`, where
`H = placementSet N N t (4 t)` is the set of `t`-interior, `4t`-separated positions of the
positive charges. -/
theorem reducedPartitionFunction_ge_construction {β lam t a b : ℝ} (hlam : 0 < lam)
    (ht : 0 < t) (hb : b ≤ t) :
    ENNReal.ofReal (N ! : ℝ) * volume (placementSet N N t (4 * t)) *
        (ENNReal.ofReal (∫ u in {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ ≤ b},
          Real.exp (β * smearedKernel lam u))) ^ N ≤
      reducedPartitionFunction N β lam := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_annulus_exp_smearedKernel β hlam a b)
    (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le), ENNReal.ofReal_natCast]
  exact reducedPartitionFunction_ge_construction_lintegral β lam ht hb

/-! ### Explicit instances -/

/-- **The `β = 2` dipole mass** : for `λ > 0` and `b ≥ 2λ`,
`∫_{2λ ≤ |u| ≤ b} e^{2 g_λ(u)} du = 2π log (b / (2λ))`, since `g_λ = g = -log |·|` on
`|u| ≥ 2λ`. -/
theorem integral_annulus_exp_two_smearedKernel {lam b : ℝ} (hlam : 0 < lam) (hb : 2 * lam ≤ b) :
    ∫ u in {u : ℂ | 2 * lam ≤ ‖u‖ ∧ ‖u‖ ≤ b}, Real.exp (2 * smearedKernel lam u) =
      2 * Real.pi * Real.log (b / (2 * lam)) := by
  set h : ℝ → ℝ := (Set.Icc (2 * lam) b).indicator fun y => (y ^ 2)⁻¹ with hh
  have h1 : ∀ u : ℂ, {u : ℂ | 2 * lam ≤ ‖u‖ ∧ ‖u‖ ≤ b}.indicator
      (fun u => Real.exp (2 * smearedKernel lam u)) u = h ‖u‖ := by
    intro u
    by_cases hu : u ∈ {u : ℂ | 2 * lam ≤ ‖u‖ ∧ ‖u‖ ≤ b}
    · have hu' : ‖u‖ ∈ Set.Icc (2 * lam) b := hu
      rw [Set.indicator_of_mem hu, hh, Set.indicator_of_mem hu', smearedKernel_eq_logKernel hlam hu.1]
      have hr : 0 < ‖u‖ := by linarith [hu.1]
      simp only [logKernel]
      rw [show 2 * -Real.log ‖u‖ = -Real.log (‖u‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
        Real.exp_neg, Real.exp_log (by positivity)]
    · have hu' : ‖u‖ ∉ Set.Icc (2 * lam) b := hu
      rw [Set.indicator_of_notMem hu, hh, Set.indicator_of_notMem hu']
  rw [← integral_indicator (measurableSet_annulus _ _)]
  simp_rw [h1]
  rw [integral_comp_norm_complex]
  have h2 : ∀ y : ℝ, y * h y = (Set.Icc (2 * lam) b).indicator (fun y => y⁻¹) y := by
    intro y
    by_cases hy : y ∈ Set.Icc (2 * lam) b
    · have hy0 : 0 < y := by linarith [hy.1]
      rw [hh, Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      field_simp
    · rw [hh, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  simp_rw [h2]
  rw [setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_right.2 (show Set.Icc (2 * lam) b ⊆ Set.Ioi 0 from fun y hy =>
      lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * lam) hy.1),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb,
    integral_inv_of_pos (by linarith) (by linarith)]

/-- **Lemma 3.5, lower bound, `β = 2`** (source l. 920–923): for `λ > 0`, `0 < t ≤ 1` and
`2λ ≤ t²`, the displacements `2λ ≤ |u| ≤ t²` give
`N! · vol(H) · (2π log (t² / (2λ)))^N ≤ 𝒦_{N,2}^λ`, with `H = placementSet N N t (4 t)`. -/
theorem reducedPartitionFunction_two_ge_construction {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (ht1 : t ≤ 1) (h2 : 2 * lam ≤ t ^ 2) :
    ENNReal.ofReal (N ! : ℝ) * volume (placementSet N N t (4 * t)) *
        (ENNReal.ofReal (2 * Real.pi * Real.log (t ^ 2 / (2 * lam)))) ^ N ≤
      reducedPartitionFunction N 2 lam := by
  have h := reducedPartitionFunction_ge_construction (N := N) (β := 2) (a := 2 * lam) (b := t ^ 2)
    hlam ht (by nlinarith)
  rwa [integral_annulus_exp_two_smearedKernel hlam h2] at h

/-- **Lemma 3.5, lower bound, `β > 2`** (source l. 932–945): there is `C > 0`, depending only on
`β`, such that for `λ > 0` and `t ≥ 2λ`, the displacements `|u| ≤ t` give
`N! · vol(H) · (𝒵_β λ^{2-β} (1 - C (λ/t)^{β-2}))^N ≤ 𝒦_{N,β}^λ`, with
`H = placementSet N N t (4 t)`. -/
theorem reducedPartitionFunction_ge_construction_of_two_lt {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (lam t : ℝ), 0 < lam → 2 * lam ≤ t →
      ENNReal.ofReal (N ! : ℝ) * volume (placementSet N N t (4 * t)) *
          ENNReal.ofReal (dipoleConstant β hβ.le * lam ^ (2 - β) *
            (1 - C * (lam / t) ^ (β - 2))) ^ N ≤
        reducedPartitionFunction N β lam := by
  obtain ⟨C, hC, hball⟩ := exists_integral_ball_exp_smearedKernel_ge hβ
  refine ⟨C, hC, fun N lam t hlam ht => ?_⟩
  have ht0 : 0 < t := by linarith
  refine le_trans ?_ (reducedPartitionFunction_ge_construction (N := N) (β := β) (a := 0) (b := t)
    hlam ht0 le_rfl)
  gcongr
  refine (hball lam t hlam ht).trans ?_
  refine setIntegral_mono_set (integrableOn_annulus_exp_smearedKernel β hlam 0 t)
    (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le) (Filter.Eventually.of_forall ?_)
  intro u hu
  exact ⟨norm_nonneg u, (mem_ball_zero_iff.1 hu).le⟩

end TwoComponentCoulomb

end
