/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Energy.BallGrowth
public import TwoComponentCoulomb.Energy.MinoPairs
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# Assembly of Proposition 2.2

The ball-growth inequality (`energy_ge_ballGrowth_overlap`) with the enlarged radii `τ`
(`TwoComponentCoulomb.tau`, source (deftau)) is reduced to the vertices of the 2-cycles of the
nearest-neighbour graph and then to the per-vertex estimates of Proposition 2.2
(source l. 512–593).

* `energy_ge_cycle_sum` : the ordered pairs of overlapping enlarged discs, with `max τ > λ`,
  are exactly the ordered pairs of mutual nearest neighbours (up to terms that vanish), so that
  `F_λ ≥ -½ Σᵢ (g(τᵢ) + κ) + ½ Σ_{i : φ(φ i) = i} dᵢ d_{φ i}
    [g_λ(z_{φ i} - zᵢ) - g(τᵢ) - g₁((z_{φ i} - zᵢ) / τᵢ)]`.
* `cycle_vertex_ge` : the estimate `|g₁(w) - κ| ≤ |w|²` and the displacement ratio
  (`sq_norm_div_tau_le`) bound the bracket from below by
  `dᵢ d_{φ i} g_λ(zᵢ - z_{φ i}) - dᵢ d_{φ i} (g(τᵢ) + κ) - 64 (r₁ i / r₂ i)²`.
* `energy_ge_mino` : the inequality of Proposition 2.2 with the constant `C = 64`.
-/

@[expose] public section

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### Reduction of the ball-growth inequality to the vertices of 2-cycles -/

section CycleSum

/-- The bracket `g_λ(z_j - zᵢ) - P(zᵢ, τᵢ; z_j, τ_j)` of a 2-cycle pair is `g_λ(z_j - zᵢ) - g(τᵢ)
- g₁((z_j - zᵢ) / τᵢ)`. -/
theorem bracket_twoCycle (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (Z : Fin N ⊕ Fin N → ℂ)
    {i : Fin N ⊕ Fin N} (hi : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    smearedKernel lam (Z (nearestNeighbor Z i) - Z i) -
        pairInteraction (Z i) (Z (nearestNeighbor Z i)) (tau hN lam Z i)
          (tau hN lam Z (nearestNeighbor Z i)) =
      smearedKernel lam (Z (nearestNeighbor Z i) - Z i) - logKernel (tau hN lam Z i : ℂ) -
        smearedKernel 1 ((Z (nearestNeighbor Z i) - Z i) / (tau hN lam Z i : ℂ)) := by
  rw [tau_eq_of_twoCycle hN lam Z hi, pairInteraction_eq_scaling _ _ (tau_pos hN hlam Z i)]
  ring

/-- If the enlarged discs of two points do not overlap (`τᵢ + τ_j ≤ |zᵢ - z_j|`), the bracket
`g_λ(z_j - zᵢ) - P(zᵢ, τᵢ; z_j, τ_j)` vanishes (Newton's theorem). -/
theorem bracket_eq_zero_of_add_le (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (Z : Fin N ⊕ Fin N → ℂ) {i j : Fin N ⊕ Fin N}
    (hd : tau hN lam Z i + tau hN lam Z j ≤ ‖Z i - Z j‖) :
    smearedKernel lam (Z j - Z i) -
      pairInteraction (Z i) (Z j) (tau hN lam Z i) (tau hN lam Z j) = 0 := by
  rw [pairInteraction_eq_logKernel_of_add_le (tau_pos hN hlam Z i) (tau_pos hN hlam Z j) hd]
  have h2 : 2 * lam ≤ ‖Z j - Z i‖ := by
    rw [norm_sub_rev]
    have := lam_le_tau hN lam Z i
    have := lam_le_tau hN lam Z j
    linarith
  have hneg : logKernel (Z j - Z i) = logKernel (Z i - Z j) := by
    rw [← logKernel_neg, neg_sub]
  rw [smearedKernel_eq_logKernel hlam h2, hneg, sub_self]

/-- **The pair sum is a sum over 2-cycle vertices.** For the enlarged radii `τ` the sum of the
pair brackets over the ordered pairs of overlapping enlarged discs equals the sum over the
ordered pairs `(i, φ i)` with `φ (φ i) = i`. -/
theorem sum_overlap_eq_sum_twoCycle (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (Z : Fin N ⊕ Fin N → ℂ) :
    ∑ p ∈ Finset.univ.filter (fun p : (Fin N ⊕ Fin N) × (Fin N ⊕ Fin N) =>
          p.1 ≠ p.2 ∧ ‖Z p.1 - Z p.2‖ < tau hN lam Z p.1 + tau hN lam Z p.2),
        charge p.1 * charge p.2 *
          (smearedKernel lam (Z p.2 - Z p.1) -
            pairInteraction (Z p.1) (Z p.2) (tau hN lam Z p.1) (tau hN lam Z p.2)) =
      ∑ i ∈ Finset.univ.filter (fun i => nearestNeighbor Z (nearestNeighbor Z i) = i),
        charge i * charge (nearestNeighbor Z i) *
          (smearedKernel lam (Z (nearestNeighbor Z i) - Z i) - logKernel (tau hN lam Z i : ℂ) -
            smearedKernel 1 ((Z (nearestNeighbor Z i) - Z i) / (tau hN lam Z i : ℂ))) := by
  classical
  set S := Finset.univ.filter (fun p : (Fin N ⊕ Fin N) × (Fin N ⊕ Fin N) =>
      p.1 ≠ p.2 ∧ ‖Z p.1 - Z p.2‖ < tau hN lam Z p.1 + tau hN lam Z p.2) with hS
  set A := Finset.univ.filter (fun i => nearestNeighbor Z (nearestNeighbor Z i) = i) with hA
  set S' := A.image (fun i => (i, nearestNeighbor Z i)) with hS'
  set T : (Fin N ⊕ Fin N) × (Fin N ⊕ Fin N) → ℝ := fun p => charge p.1 * charge p.2 *
    (smearedKernel lam (Z p.2 - Z p.1) -
      pairInteraction (Z p.1) (Z p.2) (tau hN lam Z p.1) (tau hN lam Z p.2)) with hT
  have hmemS' : ∀ p ∈ S', nearestNeighbor Z (nearestNeighbor Z p.1) = p.1 ∧
      p.2 = nearestNeighbor Z p.1 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨(Finset.mem_filter.1 hi).2, rfl⟩
  -- the terms of `S' \ S` vanish
  have hz1 : ∀ p ∈ S', p ∉ S → T p = 0 := by
    intro p hp hpS
    obtain ⟨hcyc, hp2⟩ := hmemS' p hp
    have hne : p.1 ≠ p.2 := by rw [hp2]; exact (nearestNeighbor_ne Z p.1).symm
    have hnot : ¬ ‖Z p.1 - Z p.2‖ < tau hN lam Z p.1 + tau hN lam Z p.2 := fun h =>
      hpS (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne, h⟩)
    rw [not_lt] at hnot
    have key := bracket_eq_zero_of_add_le hN hlam Z hnot
    simp only [hT]
    rw [key, mul_zero]
  -- the terms of `S \ S'` vanish
  have hz2 : ∀ p ∈ S, p ∉ S' → T p = 0 := by
    intro p hp hpS'
    obtain ⟨-, hne, hd⟩ := Finset.mem_filter.1 hp
    by_cases hτ : lam < tau hN lam Z p.1 ∨ lam < tau hN lam Z p.2
    · exfalso
      obtain ⟨h1, h2⟩ := isTwoCycle_of_overlap hN hlam Z hne hd hτ
      refine hpS' (Finset.mem_image.2 ⟨p.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩)
      · rw [h1, h2]
      · exact Prod.ext rfl h1
    · rw [not_or, not_lt, not_lt] at hτ
      simp only [hT]
      rw [bracket_eq_zero_of_tau_le hN Z hτ.1 hτ.2, mul_zero]
  have e1 : ∑ p ∈ S, T p = ∑ p ∈ S ∪ S', T p := by
    refine Finset.sum_subset Finset.subset_union_left fun p hp hpS => ?_
    exact hz1 p ((Finset.mem_union.1 hp).resolve_left hpS) hpS
  have e2 : ∑ p ∈ S', T p = ∑ p ∈ S ∪ S', T p := by
    refine Finset.sum_subset Finset.subset_union_right fun p hp hpS' => ?_
    exact hz2 p ((Finset.mem_union.1 hp).resolve_right hpS') hpS'
  have e3 : ∑ p ∈ S', T p = ∑ i ∈ A, T (i, nearestNeighbor Z i) := by
    rw [hS']
    exact Finset.sum_image fun i _ j _ h => (Prod.ext_iff.1 h).1
  rw [e1, ← e2, e3]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hcyc := (Finset.mem_filter.1 hi).2
  simp only [hT]
  rw [bracket_twoCycle hN hlam Z hcyc]

/-- **The ball-growth inequality reduced to the 2-cycle vertices** (source l. 521–557,
(peq)–(trcomp) and the two-cycle contribution):
`F_λ ≥ -½ Σᵢ (g(τᵢ) + κ) + ½ Σ_{i : φ(φ i) = i} dᵢ d_{φ i}
  [g_λ(z_{φ i} - zᵢ) - g(τᵢ) - g₁((z_{φ i} - zᵢ) / τᵢ)]`. -/
theorem energy_ge_cycle_sum (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (Z : Fin N ⊕ Fin N → ℂ) :
    energy lam Z ≥ -(1 / 2) * ∑ i, (logKernel (tau hN lam Z i : ℂ) + kappa) +
      (1 / 2) * ∑ i ∈ Finset.univ.filter (fun i => nearestNeighbor Z (nearestNeighbor Z i) = i),
        charge i * charge (nearestNeighbor Z i) *
          (smearedKernel lam (Z (nearestNeighbor Z i) - Z i) - logKernel (tau hN lam Z i : ℂ) -
            smearedKernel 1 ((Z (nearestNeighbor Z i) - Z i) / (tau hN lam Z i : ℂ))) := by
  have h := energy_ge_ballGrowth_overlap Z hlam (tau hN lam Z) (lam_le_tau hN lam Z)
  rwa [sum_overlap_eq_sum_twoCycle hN hlam Z] at h

end CycleSum

/-! ### The per-vertex estimate of a 2-cycle -/

section Vertex

/-- **The per-vertex estimate** (source l. 555–574, using `|g₁(w) - κ| ≤ |w|²` and the
displacement ratio `sq_norm_div_tau_le`): at a vertex `i` of a 2-cycle,
`dᵢ d_{φ i} g_λ(zᵢ - z_{φ i}) - dᵢ d_{φ i} (g(τᵢ) + κ) - 64 (r₁ i / r₂ i)² ≤
  dᵢ d_{φ i} [g_λ(z_{φ i} - zᵢ) - g(τᵢ) - g₁((z_{φ i} - zᵢ) / τᵢ)]`. -/
theorem cycle_vertex_ge (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (Z : Fin N ⊕ Fin N → ℂ)
    {i : Fin N ⊕ Fin N} (hi : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    charge i * charge (nearestNeighbor Z i) * smearedKernel lam (Z i - Z (nearestNeighbor Z i)) -
        charge i * charge (nearestNeighbor Z i) * (logKernel (tau hN lam Z i : ℂ) + kappa) -
        64 * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 ≤
      charge i * charge (nearestNeighbor Z i) *
        (smearedKernel lam (Z (nearestNeighbor Z i) - Z i) - logKernel (tau hN lam Z i : ℂ) -
          smearedKernel 1 ((Z (nearestNeighbor Z i) - Z i) / (tau hN lam Z i : ℂ))) := by
  have hτ := tau_pos hN hlam Z i
  have hsq := sq_norm_div_tau_le hN hlam Z hi
  have hnorm : ‖(Z (nearestNeighbor Z i) - Z i) / (tau hN lam Z i : ℂ)‖ ^ 2 =
      ‖Z (nearestNeighbor Z i) - Z i‖ ^ 2 / tau hN lam Z i ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hτ.le, div_pow]
  have hg1 := abs_smearedKernel_one_sub_kappa_le
    ((Z (nearestNeighbor Z i) - Z i) / (tau hN lam Z i : ℂ))
  rw [hnorm] at hg1
  have hg1' := (abs_le.1 (hg1.trans hsq))
  have hneg : smearedKernel lam (Z i - Z (nearestNeighbor Z i)) =
      smearedKernel lam (Z (nearestNeighbor Z i) - Z i) := by
    rw [← smearedKernel_neg lam (Z (nearestNeighbor Z i) - Z i), neg_sub]
  rw [hneg]
  rcases charge_eq_one_or_neg_one i with h1 | h1 <;>
    rcases charge_eq_one_or_neg_one (nearestNeighbor Z i) with h2 | h2 <;>
    · rw [h1, h2]
      nlinarith [hg1'.1, hg1'.2]

end Vertex

/-! ### Proposition 2.2 with the constant `64` -/

section Assembly

/-- **Proposition 2.2** (`prop:mino2`, source l. 434–443, proved in l. 512–593) in the form
proved here: with the constant `C = 64` and the sums over the vertices of the 2-cycles of the
nearest-neighbour graph and over the remaining vertices,
`F_λ ≥ ½ (Σ_{φ(φ i) = i} [dᵢ d_{φ i} g_λ(zᵢ - z_{φ i}) - dᵢ (dᵢ + d_{φ i}) (g(min (r₂ i, r₂ (φ i)))
  + κ) - 64 (r₁ i / r₂ i)²] - Σ_{φ(φ i) ≠ i} (g(r₂ i) + κ))`. -/
theorem energy_ge_mino (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (Z : Fin N ⊕ Fin N → ℂ) :
    (1 / 2) * (∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) = i,
        (charge i * charge (nearestNeighbor Z i) *
            smearedKernel lam (Z i - Z (nearestNeighbor Z i))
          - charge i * (charge i + charge (nearestNeighbor Z i)) *
              (logKernel ((min (secondNeighborRadius hN lam Z i)
                (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) : ℝ) : ℂ) + kappa)
          - 64 * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2)
      - ∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) ≠ i,
          (logKernel (secondNeighborRadius hN lam Z i : ℂ) + kappa))
      ≤ energy lam Z := by
  have hmain := energy_ge_cycle_sum hN hlam Z
  have hvert : ∀ i ∈ Finset.univ.filter (fun i => nearestNeighbor Z (nearestNeighbor Z i) = i),
      charge i * charge (nearestNeighbor Z i) * smearedKernel lam (Z i - Z (nearestNeighbor Z i))
          - charge i * (charge i + charge (nearestNeighbor Z i)) *
              (logKernel ((min (secondNeighborRadius hN lam Z i)
                (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) : ℝ) : ℂ) + kappa)
          - 64 * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 ≤
        -(logKernel (tau hN lam Z i : ℂ) + kappa) + charge i * charge (nearestNeighbor Z i) *
          (smearedKernel lam (Z (nearestNeighbor Z i) - Z i) - logKernel (tau hN lam Z i : ℂ) -
            smearedKernel 1 ((Z (nearestNeighbor Z i) - Z i) / (tau hN lam Z i : ℂ))) := by
    intro i hi
    have hcyc := (Finset.mem_filter.1 hi).2
    have h := cycle_vertex_ge hN hlam Z hcyc
    rw [← tau_of_twoCycle hN lam Z hcyc,
      show charge i * (charge i + charge (nearestNeighbor Z i)) =
        1 + charge i * charge (nearestNeighbor Z i) by rw [mul_add, charge_mul_self]]
    linarith
  have hsum := Finset.sum_le_sum hvert
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hsum
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => nearestNeighbor Z (nearestNeighbor Z i) = i)
    (fun i => logKernel (tau hN lam Z i : ℂ) + kappa)
  have hB : ∑ i ∈ Finset.univ.filter (fun i => ¬ nearestNeighbor Z (nearestNeighbor Z i) = i),
      (logKernel (tau hN lam Z i : ℂ) + kappa) =
      ∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) ≠ i,
        (logKernel (secondNeighborRadius hN lam Z i : ℂ) + kappa) :=
    Finset.sum_congr rfl fun i hi => by
      rw [tau_of_not_twoCycle hN lam Z (Finset.mem_filter.1 hi).2]
  linarith

end Assembly

end TwoComponentCoulomb

end
