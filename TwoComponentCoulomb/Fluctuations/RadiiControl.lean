/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.FirstNeighborRadius
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Pi.Bounds
import TwoComponentCoulomb.NearestNeighbor.Isolated
import TwoComponentCoulomb.NearestNeighbor.Second
import TwoComponentCoulomb.PhaseSpace.Packing

/-!
# Theorem 2, Step 5: control on the radii (deterministic part)

Source: proof of Theorem 2, Step 5 (l. 2073–2082). Write
`r̃₁ = firstNeighborRadius λ Z`.

* `sum_firstNeighborRadius_sq_le` : the packing bound `Σᵢ r̃₁(zᵢ)² ≤ C' N` (l. 2073): the balls
  `B(zᵢ, |zᵢ - z_{φ₁ i}|/2)` are disjoint in `[-√N, 2√N]²` and `r̃₁ ≤ |zᵢ - z_{φ₁ i}|/4 + λ`.
* `sq_sum_firstNeighborRadius_le` : (eq:sumrr1) in the form
  `(Σᵢ r̃₁(zᵢ))² ≤ 8 N² R² + 12 N T`, whenever `N - ½|I^dip| + D_R ≤ T` (so that at most `2T`
  particles lie outside the isolated dipoles of length at most `R`, and `2λ ≤ R`). With
  `R = R₀`, `T = M N √ω_λ` and `R₀² ≤ √ω_λ` this is `≤ (8 + 12 M) N² √ω_λ`
  (eq. (eq:sumrr1), l. 2080).
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

variable {N : ℕ}

/-! ### The packing bound for `r̃₁` -/

/-- **Packing bound** (source l. 2073): for a configuration in the box and `0 ≤ λ ≤ 1`,
`Σᵢ r̃₁(zᵢ)² ≤ 3 N`. -/
theorem sum_firstNeighborRadius_sq_le {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Z : Fin N ⊕ Fin N → ℂ) (hZ : ∀ i, Z i ∈ box N) :
    ∑ i, firstNeighborRadius lam Z i ^ 2 ≤ 3 * N := by
  have hpack := sum_sq_norm_sub_nearestNeighbor_le Z hZ
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hterm : ∀ i : Fin N ⊕ Fin N, firstNeighborRadius lam Z i ^ 2 ≤
      ‖Z i - Z (nearestNeighbor Z i)‖ ^ 2 / 16 + lam ^ 2 := fun i => by
    rw [firstNeighborRadius_eq]
    have hd : 0 ≤ ‖Z i - Z (nearestNeighbor Z i)‖ := norm_nonneg _
    rcases le_total (‖Z i - Z (nearestNeighbor Z i)‖ / 4) lam with h | h
    · rw [max_eq_right h]
      linarith only [sq_nonneg ‖Z i - Z (nearestNeighbor Z i)‖]
    · rw [max_eq_left h]
      linarith only [sq_nonneg lam]
  calc ∑ i, firstNeighborRadius lam Z i ^ 2
      ≤ ∑ i : Fin N ⊕ Fin N, (‖Z i - Z (nearestNeighbor Z i)‖ ^ 2 / 16 + lam ^ 2) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, ‖Z i - Z (nearestNeighbor Z i)‖ ^ 2) / 16 + 2 * N * lam ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
          Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (36 * N / Real.pi) / 16 + 2 * N * 1 := by
        have hlam2 : lam ^ 2 ≤ 1 := pow_le_one₀ h0 h1
        exact add_le_add (by linarith only [hpack])
          (mul_le_mul_of_nonneg_left hlam2 (by positivity))
    _ ≤ 3 * N := by
        have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have : 36 * (N : ℝ) / Real.pi ≤ 12 * N := by
          rw [div_le_iff₀ (by linarith only [hpi])]
          linarith only [mul_le_mul_of_nonneg_left hpi.le hN]
        linarith only [this, hN]

/-! ### Particles outside the short isolated dipoles -/

open scoped Classical in
/-- The vertices of the isolated dipoles of length larger than `R` are twice as many as these
dipoles. -/
theorem card_filter_isIsolatedDipole_lt_norm (Z : Fin N ⊕ Fin N → ℂ) (R : ℝ) :
    (univ.filter fun i => IsIsolatedDipole Z i ∧ R < ‖Z i - Z (nearestNeighbor Z i)‖).card =
      2 * (longIsolatedDipoles Z R).card := by
  have hP : ∀ i, (IsIsolatedDipole Z i ∧ R < ‖Z i - Z (nearestNeighbor Z i)‖) →
      nearestNeighbor Z (nearestNeighbor Z i) = i ∧
        (IsIsolatedDipole Z (nearestNeighbor Z i) ∧
          R < ‖Z (nearestNeighbor Z i) - Z (nearestNeighbor Z (nearestNeighbor Z i))‖) := by
    intro i hi
    refine ⟨hi.1.1, isIsolatedDipole_nearestNeighbor hi.1, ?_⟩
    rw [hi.1.1, norm_sub_rev]
    exact hi.2
  exact card_filter_eq_two_mul_card_image_pair Z
    (fun i => IsIsolatedDipole Z i ∧ R < ‖Z i - Z (nearestNeighbor Z i)‖) hP

open scoped Classical in
/-- **Source l. 2073**: if `N - ½|I^dip| + D_R ≤ T`, then at most `2 T` particles lie outside the
isolated dipoles of length at most `R`. -/
theorem card_not_short_isolatedDipole_le (Z : Fin N ⊕ Fin N → ℂ) (R T : ℝ)
    (hA : (N : ℝ) - (isolatedDipoles Z).card + (longIsolatedDipoles Z R).card ≤ T) :
    (((univ.filter fun i => IsIsolatedDipole Z i ∧ ‖Z i - Z (nearestNeighbor Z i)‖ ≤ R)ᶜ).card : ℝ)
      ≤ 2 * T := by
  set V : Finset (Fin N ⊕ Fin N) := univ.filter (IsIsolatedDipole Z) with hV
  have hVc : V.card = 2 * (isolatedDipoles Z).card := card_filter_isIsolatedDipole Z
  have hVl := card_filter_isIsolatedDipole_lt_norm Z R
  have hsplit := Finset.card_filter_add_card_filter_not (s := V)
    (fun i => ‖Z i - Z (nearestNeighbor Z i)‖ ≤ R)
  have hG : (univ.filter fun i => IsIsolatedDipole Z i ∧
      ‖Z i - Z (nearestNeighbor Z i)‖ ≤ R) = V.filter fun i =>
        ‖Z i - Z (nearestNeighbor Z i)‖ ≤ R := by
    rw [hV, Finset.filter_filter]
  have hL : (univ.filter fun i => IsIsolatedDipole Z i ∧ R < ‖Z i - Z (nearestNeighbor Z i)‖) =
      V.filter fun i => ¬ ‖Z i - Z (nearestNeighbor Z i)‖ ≤ R := by
    rw [hV, Finset.filter_filter]
    simp only [not_le]
  rw [hL] at hVl
  rw [Finset.card_compl, hG]
  have hle : (V.filter fun i => ‖Z i - Z (nearestNeighbor Z i)‖ ≤ R).card ≤
      Fintype.card (Fin N ⊕ Fin N) := Finset.card_le_univ _
  have hcard : Fintype.card (Fin N ⊕ Fin N) = 2 * N := by
    rw [Fintype.card_sum, Fintype.card_fin]; ring
  rw [Nat.cast_sub hle, hcard]
  have h1 : ((V.filter fun i => ‖Z i - Z (nearestNeighbor Z i)‖ ≤ R).card : ℝ) =
      2 * (isolatedDipoles Z).card - 2 * (longIsolatedDipoles Z R).card := by
    have : (V.filter fun i => ‖Z i - Z (nearestNeighbor Z i)‖ ≤ R).card +
        2 * (longIsolatedDipoles Z R).card = 2 * (isolatedDipoles Z).card := by omega
    have h2 : (((V.filter fun i => ‖Z i - Z (nearestNeighbor Z i)‖ ≤ R).card : ℕ) : ℝ) +
        2 * ((longIsolatedDipoles Z R).card : ℝ) = 2 * ((isolatedDipoles Z).card : ℝ) := by
      exact_mod_cast this
    linarith only [h2]
  rw [h1]
  push_cast
  linarith only [hA]

open scoped Classical in
/-- **(eq:sumrr1), source l. 2073–2081**: for a configuration in the box, `0 < λ ≤ 1`, `2λ ≤ R`
and `N - ½|I^dip| + D_R ≤ T`,
`(Σᵢ r̃₁(zᵢ))² ≤ 8 N² R² + 12 N T`.
The particles in isolated dipoles of length at most `R` have `r̃₁ ≤ R`; the at most `2 T` others
are controlled by the Cauchy--Schwarz inequality and the packing bound `Σ r̃₁² ≤ 3 N`. -/
theorem sq_sum_firstNeighborRadius_le {lam R T : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hR : 2 * lam ≤ R) (Z : Fin N ⊕ Fin N → ℂ) (hZ : ∀ i, Z i ∈ box N)
    (hA : (N : ℝ) - (isolatedDipoles Z).card + (longIsolatedDipoles Z R).card ≤ T) :
    (∑ i, firstNeighborRadius lam Z i) ^ 2 ≤ 8 * (N : ℝ) ^ 2 * R ^ 2 + 12 * N * T := by
  set r : Fin N ⊕ Fin N → ℝ := fun i => firstNeighborRadius lam Z i with hr
  set G : Finset (Fin N ⊕ Fin N) :=
    univ.filter fun i => IsIsolatedDipole Z i ∧ ‖Z i - Z (nearestNeighbor Z i)‖ ≤ R with hG
  have hR0 : 0 ≤ R := by linarith only [hR, h0]
  have hr0 : ∀ i, 0 ≤ r i := fun i => (h0.trans_le (lam_le_firstNeighborRadius lam Z i)).le
  have hcard : Fintype.card (Fin N ⊕ Fin N) = 2 * N := by
    rw [Fintype.card_sum, Fintype.card_fin]; ring
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- the particles in short isolated dipoles
  have hGr : ∀ i ∈ G, r i ≤ R := by
    intro i hi
    have hd : ‖Z i - Z (nearestNeighbor Z i)‖ ≤ R := (Finset.mem_filter.1 hi).2.2
    simp only [hr]
    rw [firstNeighborRadius_eq]
    exact max_le (by linarith only [hd, hR0]) (by linarith only [hR, h0])
  have hGsum : ∑ i ∈ G, r i ≤ 2 * N * R := by
    calc ∑ i ∈ G, r i ≤ ∑ _i ∈ G, R := Finset.sum_le_sum hGr
      _ = G.card * R := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * N) * R := by
          refine mul_le_mul_of_nonneg_right ?_ hR0
          have : G.card ≤ 2 * N := by
            rw [← hcard]; exact Finset.card_le_univ _
          exact_mod_cast this
  -- the other particles
  have hGc : ((Gᶜ).card : ℝ) ≤ 2 * T := card_not_short_isolatedDipole_le Z R T hA
  have hT0 : 0 ≤ T := by
    have h1' : ((isolatedDipoles Z).card : ℝ) ≤ N := by exact_mod_cast isolatedDipoles_card_le Z
    have h2' : (0 : ℝ) ≤ (longIsolatedDipoles Z R).card := Nat.cast_nonneg _
    linarith only [h1', h2', hA]
  have hsq := sum_firstNeighborRadius_sq_le h0.le h1 Z hZ
  have hCS : (∑ i ∈ Gᶜ, r i) ^ 2 ≤ 6 * N * T := by
    calc (∑ i ∈ Gᶜ, r i) ^ 2 ≤ (Gᶜ).card * ∑ i ∈ Gᶜ, r i ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (2 * T) * (3 * N) := by
          refine mul_le_mul hGc ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _) (by linarith)
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun i _ _ => sq_nonneg _) ?_
          exact hsq
      _ = 6 * N * T := by ring
  have hsplit : ∑ i, r i = ∑ i ∈ G, r i + ∑ i ∈ Gᶜ, r i := (Finset.sum_add_sum_compl G r).symm
  have hGnn : 0 ≤ ∑ i ∈ G, r i := Finset.sum_nonneg fun i _ => hr0 i
  show (∑ i, r i) ^ 2 ≤ _
  rw [hsplit]
  linarith only [sq_nonneg (∑ i ∈ G, r i - ∑ i ∈ Gᶜ, r i),
    mul_le_mul hGsum hGsum hGnn
      (mul_nonneg (mul_nonneg zero_le_two hN0) hR0 : (0 : ℝ) ≤ 2 * N * R), hCS]

end TwoComponentCoulomb

end
