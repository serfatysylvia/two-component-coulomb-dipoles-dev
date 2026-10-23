/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TwoComponentCoulomb.Frozen.FirstNeighborRadius
public import TwoComponentCoulomb.Frozen.IsGeneric
public import TwoComponentCoulomb.Frozen.SecondNearestNeighbor
public import TwoComponentCoulomb.Frozen.SecondNeighborRadius
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.NearestNeighbor.Cone

/-!
# Second nearest neighbours and the radii `r₁`, `r₂`

API for `TwoComponentCoulomb.secondNearestNeighbor`, `TwoComponentCoulomb.firstNeighborRadius` and
`TwoComponentCoulomb.secondNeighborRadius` (source l. 366–373, eqs. (nn2), (nn3)), together with
the second-neighbour half of Lemma 2.1 (source l. 391–403).

* `secondNearestNeighbor_ne_self`, `secondNearestNeighbor_ne_nearestNeighbor`,
  `norm_sub_secondNearestNeighbor_le`: `φ₂ i` is a closest point to `z_i` among the points other
  than `z_i` and `z_{φ₁ i}`.
* `firstNeighborRadius_eq`, `secondNeighborRadius_eq`: the minima in (nn2), (nn3) are attained at
  `φ₁ i` and `φ₂ i` respectively (the "radius-phi identity" of the source, l. 366–373).
* `lam_le_firstNeighborRadius`, `firstNeighborRadius_le_secondNeighborRadius`: `λ ≤ r₁ ≤ r₂`.
* `smearedKernel_add_log_firstNeighborRadius_ge`: source the nonneutral-pair comparison in Corollary 2.3, `g_λ(z_i - z_{φ₁ i}) +
  log r₁(z_i) ≥ -C`.
* `firstNeighborRadius_nearestNeighbor_eq`, `firstNeighborRadius_le_min_secondNeighborRadius`: for a
  2-cycle `φ₁ (φ₁ i) = i` one has `r₁(z_{φ₁ i}) = r₁(z_i) ≤ r₂(z_i) ∧ r₂(z_{φ₁ i})`.
* `card_filter_secondNearestNeighbor_eq_le_twelve`: a point is the second nearest neighbour of at
  most twelve points (Lemma 2.1).
-/

public section

namespace TwoComponentCoulomb

open Finset

variable {N : ℕ}

/-! ### The second nearest neighbour -/

/-- The defining properties of `secondNearestNeighbor hN Z i`: it is different from `i` and from
`φ₁ i`, and it is at least as close to `z_i` as any point other than `z_i` and `z_{φ₁ i}`. -/
theorem secondNearestNeighbor_spec (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    secondNearestNeighbor hN Z i ≠ i ∧ secondNearestNeighbor hN Z i ≠ nearestNeighbor Z i ∧
      ∀ k, k ≠ i → k ≠ nearestNeighbor Z i →
        ‖Z i - Z (secondNearestNeighbor hN Z i)‖ ≤ ‖Z i - Z k‖ := by
  unfold secondNearestNeighbor
  generalize_proofs hne
  have hmem := Finset.min'_mem _ hne
  obtain ⟨a, ha, hax⟩ := Finset.mem_map.1 hmem
  rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_erase] at ha
  have hax' : finSumFinEquiv a = _ := hax
  rw [← hax']
  simp only [Equiv.symm_apply_apply]
  exact ⟨ha.1.2.1, ha.1.1, fun k hk hk' => ha.2 k
    (Finset.mem_erase.2 ⟨hk', Finset.mem_erase.2 ⟨hk, Finset.mem_univ _⟩⟩)⟩

theorem secondNearestNeighbor_ne_self (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : secondNearestNeighbor hN Z i ≠ i :=
  (secondNearestNeighbor_spec hN Z i).1

theorem secondNearestNeighbor_ne_nearestNeighbor (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : secondNearestNeighbor hN Z i ≠ nearestNeighbor Z i :=
  (secondNearestNeighbor_spec hN Z i).2.1

theorem norm_sub_secondNearestNeighbor_le (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ)
    {i k : Fin N ⊕ Fin N} (hk : k ≠ i) (hk' : k ≠ nearestNeighbor Z i) :
    ‖Z i - Z (secondNearestNeighbor hN Z i)‖ ≤ ‖Z i - Z k‖ :=
  (secondNearestNeighbor_spec hN Z i).2.2 k hk hk'

/-- The second neighbour is at least as far as the first one. -/
theorem norm_sub_nearestNeighbor_le_norm_sub_secondNearestNeighbor (hN : 2 ≤ N)
    (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    ‖Z i - Z (nearestNeighbor Z i)‖ ≤ ‖Z i - Z (secondNearestNeighbor hN Z i)‖ :=
  norm_sub_nearestNeighbor_le Z (secondNearestNeighbor_ne_self hN Z i)

/-! ### The radii `r₁` and `r₂` -/

/-- The minimum in (nn2) is attained at `φ₁ i`: `r₁(z_i) = (¼ |z_i - z_{φ₁ i}|) ∨ λ`. -/
theorem firstNeighborRadius_eq (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    firstNeighborRadius lam Z i = max (‖Z i - Z (nearestNeighbor Z i)‖ / 4) lam := by
  unfold firstNeighborRadius
  generalize_proofs hne
  congr 2
  refine le_antisymm (Finset.inf'_le _ (Finset.mem_erase.2 ⟨nearestNeighbor_ne Z i,
    Finset.mem_univ _⟩)) (Finset.le_inf' _ _ fun j hj => ?_)
  exact norm_sub_nearestNeighbor_le Z (Finset.mem_erase.1 hj).1

/-- The minimum in (nn3) with `p = 2` is attained at `φ₂ i`:
`r₂(z_i) = (¼ |z_i - z_{φ₂ i}|) ∨ λ`. -/
theorem secondNeighborRadius_eq (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) :
    secondNeighborRadius hN lam Z i =
      max (‖Z i - Z (secondNearestNeighbor hN Z i)‖ / 4) lam := by
  unfold secondNeighborRadius
  generalize_proofs hne
  congr 2
  refine le_antisymm (Finset.inf'_le _ (Finset.mem_erase.2 ⟨secondNearestNeighbor_ne_nearestNeighbor
    hN Z i, Finset.mem_erase.2 ⟨secondNearestNeighbor_ne_self hN Z i, Finset.mem_univ _⟩⟩))
    (Finset.le_inf' _ _ fun j hj => ?_)
  obtain ⟨hj1, hj2⟩ := Finset.mem_erase.1 hj
  exact norm_sub_secondNearestNeighbor_le hN Z (Finset.mem_erase.1 hj2).1 hj1

theorem lam_le_firstNeighborRadius (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    lam ≤ firstNeighborRadius lam Z i := by
  rw [firstNeighborRadius_eq]
  exact le_max_right _ _

/-- Source the nonneutral-pair comparison in Corollary 2.3 (l. 478–481): `g_λ(z_i - z_{φ₁ i}) + log r₁(z_i) ≥ -C`, uniformly in `λ`. -/
theorem smearedKernel_add_log_firstNeighborRadius_ge {Cg : ℝ}
    (hCg : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, -Real.log (max ‖z‖ lam) - Cg ≤ smearedKernel lam z)
    {lam : ℝ} (hlam : 0 < lam) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    -Cg - Real.log 4 ≤
      smearedKernel lam (Z i - Z (nearestNeighbor Z i)) +
        Real.log (firstNeighborRadius lam Z i) := by
  have hr : 0 < firstNeighborRadius lam Z i := hlam.trans_le (lam_le_firstNeighborRadius lam Z i)
  have h1 : max ‖Z i - Z (nearestNeighbor Z i)‖ lam ≤ 4 * firstNeighborRadius lam Z i := by
    have h2 := lam_le_firstNeighborRadius lam Z i
    have h3 : ‖Z i - Z (nearestNeighbor Z i)‖ / 4 ≤ firstNeighborRadius lam Z i := by
      rw [firstNeighborRadius_eq]
      exact le_max_left _ _
    refine max_le (by linarith) (by linarith)
  have h4 : Real.log (max ‖Z i - Z (nearestNeighbor Z i)‖ lam) ≤
      Real.log 4 + Real.log (firstNeighborRadius lam Z i) := by
    rw [← Real.log_mul (by norm_num) hr.ne']
    exact Real.log_le_log (lt_max_of_lt_right hlam) h1
  have h5 := hCg lam hlam (Z i - Z (nearestNeighbor Z i))
  linarith

theorem lam_le_secondNeighborRadius (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : lam ≤ secondNeighborRadius hN lam Z i := by
  rw [secondNeighborRadius_eq]
  exact le_max_right _ _

/-- `r₁(z_i) ≤ r₂(z_i)` (source l. 368–370). -/
theorem firstNeighborRadius_le_secondNeighborRadius (hN : 2 ≤ N) (lam : ℝ)
    (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    firstNeighborRadius lam Z i ≤ secondNeighborRadius hN lam Z i := by
  rw [firstNeighborRadius_eq, secondNeighborRadius_eq]
  exact max_le_max (div_le_div_of_nonneg_right
    (norm_sub_nearestNeighbor_le_norm_sub_secondNearestNeighbor hN Z i) (by norm_num)) le_rfl

/-- In a 2-cycle `φ₁ (φ₁ i) = i`, the two vertices have the same first radius. -/
theorem firstNeighborRadius_nearestNeighbor_eq (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    {i : Fin N ⊕ Fin N} (h : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    firstNeighborRadius lam Z (nearestNeighbor Z i) = firstNeighborRadius lam Z i := by
  rw [firstNeighborRadius_eq, firstNeighborRadius_eq, h, norm_sub_rev]

/-- In a 2-cycle `φ₁ (φ₁ i) = i`, `r₁(z_i) ≤ r₂(z_i) ∧ r₂(z_{φ₁ i})` (source l. 478–479). -/
theorem firstNeighborRadius_le_min_secondNeighborRadius (hN : 2 ≤ N) (lam : ℝ)
    (Z : Fin N ⊕ Fin N → ℂ) {i : Fin N ⊕ Fin N} (h : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    firstNeighborRadius lam Z i ≤
      min (secondNeighborRadius hN lam Z i) (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) := by
  refine le_min (firstNeighborRadius_le_secondNeighborRadius hN lam Z i) ?_
  rw [← firstNeighborRadius_nearestNeighbor_eq lam Z h]
  exact firstNeighborRadius_le_secondNeighborRadius hN lam Z _

/-! ### Lemma 2.1: a point is the second nearest neighbour of at most twelve points -/

/-- If `φ₂ j = o`, then at most one index `k ∉ {j, o}` has `z_k` strictly closer to `z_j` than
`z_o`, namely `k = φ₁ j`. -/
theorem card_filter_lt_secondNearestNeighbor_le_one (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ)
    {j o : Fin N ⊕ Fin N} (h : secondNearestNeighbor hN Z j = o) :
    (univ.filter fun k => k ≠ j ∧ k ≠ o ∧ ‖Z j - Z k‖ < ‖Z j - Z o‖).card ≤ 1 := by
  refine (Finset.card_le_card (t := {nearestNeighbor Z j}) fun k hk => ?_).trans (by simp)
  obtain ⟨hkj, -, hlt⟩ := (Finset.mem_filter.1 hk).2
  rw [Finset.mem_singleton]
  by_contra hkφ
  have := norm_sub_secondNearestNeighbor_le hN Z hkj hkφ
  rw [h] at this
  exact absurd hlt (not_lt.2 this)

/-- Lemma 2.1 (source l. 391–403): a point `o` is the second nearest neighbour of at most
twelve points. Only the injectivity of `Z` is used. -/
theorem card_filter_secondNearestNeighbor_eq_le_twelve_of_injective (hN : 2 ≤ N)
    {Z : Fin N ⊕ Fin N → ℂ} (hZ : Function.Injective Z) (o : Fin N ⊕ Fin N) :
    (univ.filter fun j => secondNearestNeighbor hN Z j = o).card ≤ 12 := by
  refine le_trans (Finset.card_le_card fun j hj => ?_)
    (card_filter_card_filter_lt_le_one_le_twelve hZ o)
  have hj' : secondNearestNeighbor hN Z j = o := (Finset.mem_filter.1 hj).2
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hj' ▸ (secondNearestNeighbor_ne_self hN Z j).symm,
    card_filter_lt_secondNearestNeighbor_le_one hN Z hj'⟩

/-- Lemma 2.1 for generic configurations. -/
theorem card_filter_secondNearestNeighbor_eq_le_twelve (hN : 2 ≤ N) {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : IsGeneric Z) (o : Fin N ⊕ Fin N) :
    (univ.filter fun j => secondNearestNeighbor hN Z j = o).card ≤ 12 :=
  card_filter_secondNearestNeighbor_eq_le_twelve_of_injective hN hZ.1 o

end TwoComponentCoulomb

end
