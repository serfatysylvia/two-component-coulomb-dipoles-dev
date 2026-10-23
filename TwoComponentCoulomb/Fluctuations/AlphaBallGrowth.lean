/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Energy.BallGrowth
public import TwoComponentCoulomb.Fluctuations.AlphaRadii
import TwoComponentCoulomb.Energy.MinoAssembly
import TwoComponentCoulomb.Potential.ElectricEnergy
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# The ball-growth inequality keeping the electric energy (Theorem 2, Step 2)

Source `source/dipole-formation.tex`, l. 1872–1899. The proof of Proposition 2.2 (source l. 517–598) is
repeated with the radii `αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)` (`alphaRadius`) in place of `τᵢ`, and the
electric energy `∫ |∇h_α|²` of the grown discs is kept instead of being dropped.

Write `P_{ij}(a, b) = pairInteraction zᵢ zⱼ a b` and `E_α = electricField charge Z α`. The polarized
change-of-radii identity (`energy_eq_ballGrowth`, Lemma 2.4) shows that
`F_λ = ½ Σᵢⱼ dᵢ dⱼ P_{ij}(λ, λ) - N (g(λ) + κ)` becomes

`F_λ = (1/4π) ∫ |E_α|² + ½ Σᵢⱼ dᵢ dⱼ [P_{ij}(λ, λ) - P_{ij}(αᵢ, αⱼ)] - N (g(λ) + κ)`.

The second term is then reduced exactly as in Proposition 2.2. Only `λ ≤ αᵢ ≤ τᵢ` and
`α_{φ₁ i} = αᵢ` on 2-cycles are used for this reduction; the per-vertex quadratic error uses
`(r̃₂ ∧ γ) ∨ r̃₁ ≤ 2 αᵢ` on 2-cycles.

* `energy_eq_electric_add_sum_pairInteraction_sub` : the identity above, for any radii `αᵢ > 0`.
* `energy_eq_electric_cycle_sum_of_le_tau` : for radii `λ ≤ αᵢ ≤ τᵢ`, symmetric on 2-cycles,
  the exact identity
  `F_λ = (1/4π) ∫ |E_α|² - ½ Σᵢ (g(αᵢ) + κ)
    + ½ Σ_{φ₁(φ₁ i) = i} dᵢ d_{φ₁ i} [g_λ(z_{φ₁ i} - zᵢ) - g(αᵢ) - g₁((z_{φ₁ i} - zᵢ) / αᵢ)]`.
* `energy_ge_electric_alphaRadius` : the ball-growth inequality of Step 2, in the form
  `F_λ ≥ (1/4π) ∫ |E_α|² + ½ (Σ_{𝒞} [dᵢ d_{φ₁ i} g_λ(zᵢ - z_{φ₁ i}) - dᵢ (dᵢ + d_{φ₁ i}) (g(αᵢ) + κ)
    - 64 (r̃₁ / ((r̃₂ ∧ γ) ∨ r̃₁))²] - Σ_{ℐ ∖ 𝒞} (g(αᵢ) + κ))`.
* `integral_norm_sq_electricField_ge_alphaRadius` : the same inequality in the form displayed in
  the source (l. 1891–1899), for `∫ |∇h_λ|²`, with the diagonal term `4Nπ g_λ(0)`.
-/

@[expose] public section

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### Keeping the electric energy -/

section Electric

/-- **The energy with the electric energy of grown discs** (source l. 1891, Lemma 2.4 and
eq. (eq:rewrF)): for radii `αᵢ > 0`,
`F_λ = (1/4π) ∫ |∇h_α|² + ½ Σᵢⱼ dᵢ dⱼ [P_{ij}(λ, λ) - P_{ij}(αᵢ, αⱼ)] - N (g(λ) + κ)`. -/
theorem energy_eq_electric_add_sum_pairInteraction_sub (Z : Fin N ⊕ Fin N → ℂ) (lam : ℝ)
    (α : Fin N ⊕ Fin N → ℝ) (hα : ∀ i, 0 < α i) :
    energy lam Z = (1 / (4 * Real.pi)) * (∫ x, ‖electricField charge Z α x‖ ^ 2) +
      (1 / 2) * ∑ i, ∑ j, charge i * charge j *
        (pairInteraction (Z i) (Z j) lam lam - pairInteraction (Z i) (Z j) (α i) (α j)) -
      N * (logKernel (lam : ℂ) + kappa) := by
  by_cases hlam : 0 < lam
  · exact energy_eq_ballGrowth Z hlam α hα
  -- The statement is total in `lam`. The source only uses the positive-radius branch.
  rw [integral_norm_sq_electricField (d := charge) (z := Z) hα (sum_charge_eq_zero N),
    energy_eq_half_sum_pairInteraction Z]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Reduction to the overlapping grown discs** (source l. 532–550, (peq)–(disz)): for radii
`αᵢ ≥ λ > 0`, the diagonal terms of `½ Σᵢⱼ dᵢ dⱼ [P_{ij}(λ, λ) - P_{ij}(αᵢ, αⱼ)]` contribute
`½ Σᵢ (g(λ) - g(αᵢ))`, and the pairs of disjoint grown discs cancel by Newton's theorem. -/
theorem half_sum_pairInteraction_sub_eq_overlap (Z : Fin N ⊕ Fin N → ℂ) {lam : ℝ}
    (hlam : 0 < lam) (α : Fin N ⊕ Fin N → ℝ) (hα : ∀ i, lam ≤ α i) :
    (1 / 2) * ∑ i, ∑ j, charge i * charge j *
        (pairInteraction (Z i) (Z j) lam lam - pairInteraction (Z i) (Z j) (α i) (α j)) -
      N * (logKernel (lam : ℂ) + kappa) =
    -(1 / 2) * ∑ i, (logKernel (α i : ℂ) + kappa) +
      (1 / 2) * ∑ p ∈ Finset.univ.filter (fun p : (Fin N ⊕ Fin N) × (Fin N ⊕ Fin N) =>
          p.1 ≠ p.2 ∧ ‖Z p.1 - Z p.2‖ < α p.1 + α p.2),
        charge p.1 * charge p.2 *
          (smearedKernel lam (Z p.2 - Z p.1) -
            pairInteraction (Z p.1) (Z p.2) (α p.1) (α p.2)) := by
  have hpos : ∀ i, 0 < α i := fun i => hlam.trans_le (hα i)
  rw [sum_sum_eq_sum_diag_add_sum_filter _ (fun i j => ‖Z i - Z j‖ < α i + α j)]
  · have hdiag : ∀ i, charge i * charge i *
        (pairInteraction (Z i) (Z i) lam lam - pairInteraction (Z i) (Z i) (α i) (α i)) =
        logKernel (lam : ℂ) - logKernel (α i : ℂ) := fun i => by
      rw [charge_mul_self, pairInteraction_self _ hlam, pairInteraction_self _ (hpos i)]
      ring
    have hcard : (Finset.univ : Finset (Fin N ⊕ Fin N)).card = 2 * N := by
      simp [two_mul]
    have hS : ∀ p ∈ Finset.univ.filter (fun p : (Fin N ⊕ Fin N) × (Fin N ⊕ Fin N) =>
          p.1 ≠ p.2 ∧ ‖Z p.1 - Z p.2‖ < α p.1 + α p.2),
        charge p.1 * charge p.2 *
          (pairInteraction (Z p.1) (Z p.2) lam lam -
            pairInteraction (Z p.1) (Z p.2) (α p.1) (α p.2))
        = charge p.1 * charge p.2 *
          (smearedKernel lam (Z p.2 - Z p.1) -
            pairInteraction (Z p.1) (Z p.2) (α p.1) (α p.2)) := fun p _ => by
      rw [pairInteraction_eq_smearedKernel]
    have e1 : ∑ i, charge i * charge i *
        (pairInteraction (Z i) (Z i) lam lam - pairInteraction (Z i) (Z i) (α i) (α i)) =
        ∑ i, (logKernel (lam : ℂ) - logKernel (α i : ℂ)) := Finset.sum_congr rfl fun i _ => hdiag i
    rw [e1, Finset.sum_congr rfl hS, Finset.sum_sub_distrib,
      Finset.sum_const, hcard, Finset.sum_add_distrib, Finset.sum_const, hcard]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  · intro i j _ hP
    rw [not_lt] at hP
    have h1 : lam + lam ≤ ‖Z i - Z j‖ := by linarith [hα i, hα j]
    rw [pairInteraction_eq_logKernel_of_add_le hlam hlam h1,
      pairInteraction_eq_logKernel_of_add_le (hpos i) (hpos j) hP, sub_self, mul_zero]

end Electric

/-! ### Reduction to the 2-cycles for radii `λ ≤ α ≤ τ` -/

section CycleSum

variable (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (Z : Fin N ⊕ Fin N → ℂ)
  {α : Fin N ⊕ Fin N → ℝ}

include hlam in
/-- If the grown discs of two points do not overlap (`αᵢ + α_j ≤ |zᵢ - z_j|`, `α ≥ λ`), the
bracket `g_λ(z_j - zᵢ) - P(zᵢ, αᵢ; z_j, α_j)` vanishes (Newton's theorem). -/
theorem bracket_eq_zero_of_add_le_of_le (hα : ∀ i, lam ≤ α i) {i j : Fin N ⊕ Fin N}
    (hd : α i + α j ≤ ‖Z i - Z j‖) :
    smearedKernel lam (Z j - Z i) - pairInteraction (Z i) (Z j) (α i) (α j) = 0 := by
  rw [pairInteraction_eq_logKernel_of_add_le (hlam.trans_le (hα i)) (hlam.trans_le (hα j)) hd]
  have h2 : 2 * lam ≤ ‖Z j - Z i‖ := by
    rw [norm_sub_rev]
    linarith [hα i, hα j]
  have hneg : logKernel (Z j - Z i) = logKernel (Z i - Z j) := by
    rw [← logKernel_neg, neg_sub]
  rw [smearedKernel_eq_logKernel hlam h2, hneg, sub_self]

include hN hlam in
/-- **The pair sum is a sum over 2-cycle vertices**, for radii `λ ≤ αᵢ ≤ τᵢ` with
`α_{φ₁ i} = αᵢ` on 2-cycles (source l. 532–562, (disz)–(trcomp), repeated with `α`). -/
theorem sum_overlap_eq_sum_twoCycle_of_le_tau (hα : ∀ i, lam ≤ α i)
    (hατ : ∀ i, α i ≤ tau hN lam Z i)
    (hsym : ∀ i, nearestNeighbor Z (nearestNeighbor Z i) = i → α (nearestNeighbor Z i) = α i) :
    ∑ p ∈ Finset.univ.filter (fun p : (Fin N ⊕ Fin N) × (Fin N ⊕ Fin N) =>
          p.1 ≠ p.2 ∧ ‖Z p.1 - Z p.2‖ < α p.1 + α p.2),
        charge p.1 * charge p.2 *
          (smearedKernel lam (Z p.2 - Z p.1) -
            pairInteraction (Z p.1) (Z p.2) (α p.1) (α p.2)) =
      ∑ i ∈ Finset.univ.filter (fun i => nearestNeighbor Z (nearestNeighbor Z i) = i),
        charge i * charge (nearestNeighbor Z i) *
          (smearedKernel lam (Z (nearestNeighbor Z i) - Z i) - logKernel (α i : ℂ) -
            smearedKernel 1 ((Z (nearestNeighbor Z i) - Z i) / (α i : ℂ))) := by
  classical
  set S := Finset.univ.filter (fun p : (Fin N ⊕ Fin N) × (Fin N ⊕ Fin N) =>
      p.1 ≠ p.2 ∧ ‖Z p.1 - Z p.2‖ < α p.1 + α p.2) with hS
  set A := Finset.univ.filter (fun i => nearestNeighbor Z (nearestNeighbor Z i) = i) with hA
  set S' := A.image (fun i => (i, nearestNeighbor Z i)) with hS'
  set T : (Fin N ⊕ Fin N) × (Fin N ⊕ Fin N) → ℝ := fun p => charge p.1 * charge p.2 *
    (smearedKernel lam (Z p.2 - Z p.1) -
      pairInteraction (Z p.1) (Z p.2) (α p.1) (α p.2)) with hT
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
    have hnot : ¬ ‖Z p.1 - Z p.2‖ < α p.1 + α p.2 := fun h =>
      hpS (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne, h⟩)
    rw [not_lt] at hnot
    simp only [hT]
    rw [bracket_eq_zero_of_add_le_of_le hlam Z hα hnot, mul_zero]
  -- the terms of `S \ S'` vanish
  have hz2 : ∀ p ∈ S, p ∉ S' → T p = 0 := by
    intro p hp hpS'
    obtain ⟨-, hne, hd⟩ := Finset.mem_filter.1 hp
    by_cases hα' : lam < α p.1 ∨ lam < α p.2
    · exfalso
      obtain ⟨h1, h2⟩ := isTwoCycle_of_overlap hN hlam Z hne
        (hd.trans_le (add_le_add (hατ p.1) (hατ p.2)))
        (hα'.imp (fun h => h.trans_le (hατ p.1)) (fun h => h.trans_le (hατ p.2)))
      refine hpS' (Finset.mem_image.2 ⟨p.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩)
      · rw [h1, h2]
      · exact Prod.ext rfl h1
    · rw [not_or, not_lt, not_lt] at hα'
      have e1 : α p.1 = lam := le_antisymm hα'.1 (hα p.1)
      have e2 : α p.2 = lam := le_antisymm hα'.2 (hα p.2)
      simp only [hT]
      rw [e1, e2, pairInteraction_eq_smearedKernel, sub_self, mul_zero]
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
  rw [hsym i hcyc, pairInteraction_eq_scaling _ _ (hlam.trans_le (hα i))]
  ring

include hN hlam in
/-- **The ball-growth identity keeping the electric energy** (source l. 1891–1899), for radii
`λ ≤ αᵢ ≤ τᵢ` with `α_{φ₁ i} = αᵢ` on 2-cycles:
`F_λ = (1/4π) ∫ |∇h_α|² - ½ Σᵢ (g(αᵢ) + κ)
  + ½ Σ_{φ₁(φ₁ i) = i} dᵢ d_{φ₁ i} [g_λ(z_{φ₁ i} - zᵢ) - g(αᵢ) - g₁((z_{φ₁ i} - zᵢ) / αᵢ)]`. -/
theorem energy_eq_electric_cycle_sum_of_le_tau (hα : ∀ i, lam ≤ α i)
    (hατ : ∀ i, α i ≤ tau hN lam Z i)
    (hsym : ∀ i, nearestNeighbor Z (nearestNeighbor Z i) = i → α (nearestNeighbor Z i) = α i) :
    energy lam Z = (1 / (4 * Real.pi)) * (∫ x, ‖electricField charge Z α x‖ ^ 2) -
      (1 / 2) * ∑ i, (logKernel (α i : ℂ) + kappa) +
      (1 / 2) * ∑ i ∈ Finset.univ.filter (fun i => nearestNeighbor Z (nearestNeighbor Z i) = i),
        charge i * charge (nearestNeighbor Z i) *
          (smearedKernel lam (Z (nearestNeighbor Z i) - Z i) - logKernel (α i : ℂ) -
            smearedKernel 1 ((Z (nearestNeighbor Z i) - Z i) / (α i : ℂ))) := by
  rw [energy_eq_electric_add_sum_pairInteraction_sub Z lam α fun i => hlam.trans_le (hα i),
    add_sub_assoc, half_sum_pairInteraction_sub_eq_overlap Z hlam α hα,
    sum_overlap_eq_sum_twoCycle_of_le_tau hN hlam Z hα hατ hsym]
  ring

end CycleSum

/-! ### The per-vertex estimate with the radii `α` -/

section Vertex

/-- **The per-vertex estimate with the radii `α`** (source l. 1897, using `|g₁(w) - κ| ≤ |w|²`
and the displacement ratio `sq_norm_div_alphaRadius_le`): at a vertex `i` of a 2-cycle,
`dᵢ d_{φ₁ i} g_λ(zᵢ - z_{φ₁ i}) - dᵢ d_{φ₁ i} (g(αᵢ) + κ) - 64 (r̃₁ / ((r̃₂ ∧ γ) ∨ r̃₁))² ≤
  dᵢ d_{φ₁ i} [g_λ(z_{φ₁ i} - zᵢ) - g(αᵢ) - g₁((z_{φ₁ i} - zᵢ) / αᵢ)]`. -/
theorem cycle_vertex_ge_alphaRadius (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (γ : ℝ)
    (Z : Fin N ⊕ Fin N → ℂ) {i : Fin N ⊕ Fin N}
    (hi : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    charge i * charge (nearestNeighbor Z i) * smearedKernel lam (Z i - Z (nearestNeighbor Z i)) -
        charge i * charge (nearestNeighbor Z i) *
          (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa) -
        64 * (firstNeighborRadius lam Z i /
          max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i)) ^ 2 ≤
      charge i * charge (nearestNeighbor Z i) *
        (smearedKernel lam (Z (nearestNeighbor Z i) - Z i) -
          logKernel (alphaRadius hN lam γ Z i : ℂ) -
          smearedKernel 1 ((Z (nearestNeighbor Z i) - Z i) / (alphaRadius hN lam γ Z i : ℂ))) := by
  have ha := alphaRadius_pos hN hlam γ Z i
  have hsq := sq_norm_div_alphaRadius_le hN hlam γ Z hi
  have hnorm : ‖(Z (nearestNeighbor Z i) - Z i) / (alphaRadius hN lam γ Z i : ℂ)‖ ^ 2 =
      ‖Z (nearestNeighbor Z i) - Z i‖ ^ 2 / alphaRadius hN lam γ Z i ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le, div_pow]
  have hg1 := abs_smearedKernel_one_sub_kappa_le
    ((Z (nearestNeighbor Z i) - Z i) / (alphaRadius hN lam γ Z i : ℂ))
  rw [hnorm] at hg1
  have hg1' := abs_le.1 (hg1.trans hsq)
  have hneg : smearedKernel lam (Z i - Z (nearestNeighbor Z i)) =
      smearedKernel lam (Z (nearestNeighbor Z i) - Z i) := by
    rw [← smearedKernel_neg lam (Z (nearestNeighbor Z i) - Z i), neg_sub]
  rw [hneg]
  rcases charge_eq_one_or_neg_one i with h1 | h1 <;>
    rcases charge_eq_one_or_neg_one (nearestNeighbor Z i) with h2 | h2 <;>
    · rw [h1, h2]
      nlinarith [hg1'.1, hg1'.2]

end Vertex

/-! ### The ball-growth inequality of Theorem 2, Step 2 -/

section Assembly

/-- **The ball-growth inequality keeping the electric energy** (Theorem 2, Step 2, source
l. 1891–1899), with the constant `64` in the quadratic error: for the radii
`αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)`,
`F_λ ≥ (1/4π) ∫ |∇h_α|² + ½ (Σ_{φ₁(φ₁ i) = i} [dᵢ d_{φ₁ i} g_λ(zᵢ - z_{φ₁ i})
    - dᵢ (dᵢ + d_{φ₁ i}) (g(αᵢ) + κ) - 64 (r̃₁(zᵢ) / ((r̃₂(zᵢ) ∧ γ) ∨ r̃₁(zᵢ)))²]
    - Σ_{φ₁(φ₁ i) ≠ i} (g(αᵢ) + κ))`.
The sums over `𝒞_k` and `ℐ_k ∖ 𝒞_k`, `k = 1, …, K`, are the sums over the 2-cycle vertices and
over the remaining (tree) vertices. -/
theorem energy_ge_electric_alphaRadius (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (γ : ℝ)
    (Z : Fin N ⊕ Fin N → ℂ) :
    (1 / (4 * Real.pi)) * (∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2) +
      (1 / 2) * (∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) = i,
          (charge i * charge (nearestNeighbor Z i) *
              smearedKernel lam (Z i - Z (nearestNeighbor Z i))
            - charge i * (charge i + charge (nearestNeighbor Z i)) *
                (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa)
            - 64 * (firstNeighborRadius lam Z i /
                max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i)) ^ 2)
        - ∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) ≠ i,
            (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa))
      ≤ energy lam Z := by
  have hmain := energy_eq_electric_cycle_sum_of_le_tau hN hlam Z (α := alphaRadius hN lam γ Z)
    (lam_le_alphaRadius hN lam γ Z) (alphaRadius_le_tau hN lam γ Z)
    (fun i hi => alphaRadius_nearestNeighbor_eq hN lam γ Z hi)
  have hvert : ∀ i ∈ Finset.univ.filter (fun i => nearestNeighbor Z (nearestNeighbor Z i) = i),
      charge i * charge (nearestNeighbor Z i) * smearedKernel lam (Z i - Z (nearestNeighbor Z i))
          - charge i * (charge i + charge (nearestNeighbor Z i)) *
              (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa)
          - 64 * (firstNeighborRadius lam Z i /
              max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i)) ^ 2 ≤
        -(logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa) +
          charge i * charge (nearestNeighbor Z i) *
            (smearedKernel lam (Z (nearestNeighbor Z i) - Z i) -
              logKernel (alphaRadius hN lam γ Z i : ℂ) -
              smearedKernel 1 ((Z (nearestNeighbor Z i) - Z i) /
                (alphaRadius hN lam γ Z i : ℂ))) := by
    intro i hi
    have h := cycle_vertex_ge_alphaRadius hN hlam γ Z (Finset.mem_filter.1 hi).2
    rw [show charge i * (charge i + charge (nearestNeighbor Z i)) =
        1 + charge i * charge (nearestNeighbor Z i) by rw [mul_add, charge_mul_self]]
    linarith
  have hsum := Finset.sum_le_sum hvert
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hsum
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => nearestNeighbor Z (nearestNeighbor Z i) = i)
    (fun i => logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa)
  have hB : ∑ i ∈ Finset.univ.filter (fun i => ¬ nearestNeighbor Z (nearestNeighbor Z i) = i),
      (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa) =
      ∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) ≠ i,
        (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa) := rfl
  linarith

/-- **The ball-growth inequality of Theorem 2, Step 2, in the form of the source**
(l. 1891–1899): with `h_λ`, `h_α` the potentials of the discs of radii `λ` and `αᵢ`,
`∫ |∇h_λ|² ≥ ∫ |∇h_α|² + 2π (Σ_{φ₁(φ₁ i) = i} [dᵢ d_{φ₁ i} g_λ(zᵢ - z_{φ₁ i})
    - dᵢ (dᵢ + d_{φ₁ i}) (g(αᵢ) + κ) - 64 (r̃₁(zᵢ) / ((r̃₂(zᵢ) ∧ γ) ∨ r̃₁(zᵢ)))²]
    - Σ_{φ₁(φ₁ i) ≠ i} (g(αᵢ) + κ)) + 4Nπ g_λ(0)`. -/
theorem integral_norm_sq_electricField_ge_alphaRadius (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ) :
    (∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2) +
      2 * Real.pi * (∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) = i,
          (charge i * charge (nearestNeighbor Z i) *
              smearedKernel lam (Z i - Z (nearestNeighbor Z i))
            - charge i * (charge i + charge (nearestNeighbor Z i)) *
                (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa)
            - 64 * (firstNeighborRadius lam Z i /
                max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i)) ^ 2)
        - ∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) ≠ i,
            (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa)) +
      4 * N * Real.pi * smearedKernel lam 0
      ≤ ∫ x, ‖electricField charge Z (fun _ => lam) x‖ ^ 2 := by
  have h := energy_ge_electric_alphaRadius hN hlam γ Z
  rw [energy_eq_integral_norm_sq_electricField Z hlam] at h
  rw [smearedKernel_zero hlam]
  have key : ∀ A B S c : ℝ, (1 / (4 * Real.pi)) * A + (1 / 2) * S ≤
      (1 / (4 * Real.pi)) * B - N * c → A + 2 * Real.pi * S + 4 * N * Real.pi * c ≤ B := by
    intro A B S c hh
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have h4 : 0 ≤ 4 * Real.pi := by positivity
    have h' := mul_le_mul_of_nonneg_left hh h4
    have e1 : 4 * Real.pi * ((1 / (4 * Real.pi)) * A + (1 / 2) * S) = A + 2 * Real.pi * S := by
      field_simp
      ring
    have e2 : 4 * Real.pi * ((1 / (4 * Real.pi)) * B - N * c) = B - 4 * N * Real.pi * c := by
      field_simp
    rw [e1, e2] at h'
    linarith
  exact key _ _ _ _ h

end Assembly

end TwoComponentCoulomb

end
