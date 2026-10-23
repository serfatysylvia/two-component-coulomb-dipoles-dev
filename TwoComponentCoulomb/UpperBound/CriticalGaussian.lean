/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.NearestNeighborModelCases
import TwoComponentCoulomb.Gibbs.Measurability
import TwoComponentCoulomb.Integrals.GaussianMass
import TwoComponentCoulomb.UpperBound.ReducedMatching

/-!
# A common Gaussian cutoff for the critical cycles

The proof of (eq:critical-fixed-graph) in subsection 3.5 of the paper uses
the parameter `1 / ℓ` for every cycle, including the nonisolated components. This differs
from the critical nearest-neighbor estimate in the pinned source
`source/dipole-formation.tex`, which optimizes the parameter in the cycle count.

We keep the Gaussian in the integrand during the Gunson--Panta change of variables.
The cycle integral then factors into copies of `J_λ(1/ℓ)`, while the tree variables
retain the packing constraint and are bounded by the Dirichlet integral.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal Classical

namespace TwoComponentCoulomb

section Gaussian

variable {ι : Type*} [Fintype ι]

/-- The squared cycle displacements, with one endpoint per cycle. -/
noncomputable def cycleDisplacementSq (key : ι ↪ ℕ) (f : ι → ι) (z : ι → ℂ) : ℝ :=
  ∑ j : CycIdx key f, ‖z j.1.1 - z (f j.1.1)‖ ^ 2

/-- The cycle displacements become the cycle coordinates under Gunson--Panta. -/
theorem cycleDisplacementSq_gp_symm (key : ι ↪ ℕ) (f : ι → ι)
    (hR : ∀ i, ∃ n, f^[n] i ∈ gpRefSet key f) (u : ι → ℂ) :
    cycleDisplacementSq key f ((gpLinearEquiv f (gpRefSet key f) hR).symm u) =
      ∑ j : CycIdx key f, ‖u j.1.1‖ ^ 2 := by
  unfold cycleDisplacementSq
  exact sum_congr rfl fun j _ => by rw [gp_symm_sub_of_notMem hR u j.1.2]

/-- The packing bound applies to the cycle variables alone. -/
theorem cycleDisplacementSq_le [Nontrivial ι] {N : ℕ} (key : ι ↪ ℕ) (z : ι → ℂ)
    (hz : ∀ i, z i ∈ box N) :
    cycleDisplacementSq key (nnMap key z) z ≤ 36 * N / Real.pi := by
  have hpack := sum_sq_le_of_separated z (fun i => ‖z i - z (nnMap key z i)‖) hz
    (fun _ => norm_nonneg _) (fun i => norm_sub_le_of_mem_box (hz i) (hz _))
    (fun i j hij => norm_sub_nnMap_le key z hij.symm)
  refine le_trans ?_ hpack
  unfold cycleDisplacementSq
  have h₁ := Fintype.sum_subtype_add_sum_subtype
    (fun j : NonRef key (nnMap key z) => nnMap key z (nnMap key z j) = j)
    (fun j => ‖z j.1 - z (nnMap key z j.1)‖ ^ 2)
  have h₂ := Fintype.sum_subtype_add_sum_subtype
    (fun i => i ∈ gpRefSet key (nnMap key z)) (fun i => ‖z i - z (nnMap key z i)‖ ^ 2)
  have ht : 0 ≤ ∑ j : TreeIdx key (nnMap key z), ‖z j.1.1 - z (nnMap key z j.1.1)‖ ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hr : 0 ≤ ∑ j : {i // i ∈ gpRefSet key (nnMap key z)}, ‖z j - z (nnMap key z j)‖ ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  linarith only [h₁, h₂, ht, hr]

/-- **Critical integration of the cycle and tree variables** (`source/dipole-formation.tex`,
subsection 3.5, Step 2). With the common Gaussian cutoff already inserted, each cycle
contributes exactly the same mass. Only the tree variables retain a packing constraint. -/
theorem lintegral_cell_gaussian_le_cycle_mul_tree [Nontrivial ι] {N p K : ℕ}
    (hcard : Fintype.card ι = 2 * p) (key : ι ↪ ℕ) {f : ι → ι}
    (hf : ∃ z₀ : ι → ℂ, nnMap key z₀ = f)
    (hK : Fintype.card {i // i ∈ gpRefSet key f} = K) (lam ℓ : ℝ) :
    ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
        ENNReal.ofReal (Real.exp ((∑ i, smearedKernel lam (z i - z (f i))) -
          cycleDisplacementSq key f z / ℓ)) ≤
      (N : ℝ≥0∞) ^ K *
        ((∫⁻ u : ℂ, ENNReal.ofReal (Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ))) ^ K *
          ∫⁻ v in {v : Fin (2 * p - 2 * K) → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ 36 * N / Real.pi},
            ∏ i, ENNReal.ofReal (Real.exp (smearedKernel lam (v i)))) := by
  obtain ⟨z₀, rfl⟩ := hf
  set f := nnMap key z₀
  have hf0 : ∀ i, f i ≠ i := nnMap_ne key z₀
  have hR : ∀ i, ∃ n, f^[n] i ∈ gpRefSet key f := exists_iterate_nnMap_mem_gpRefSet key z₀
  let G₁ : ℂ → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ))
  let G₂ : ℂ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (smearedKernel lam u))
  have hg := measurable_smearedKernel lam
  have hG₁ : Measurable G₁ := by dsimp [G₁]; fun_prop
  have hG₂ : Measurable G₂ := by dsimp [G₂]; fun_prop
  let H₁ : (CycIdx key f → ℂ) → ℝ≥0∞ := fun v => ∏ j, G₁ (v j)
  let H₂ : (TreeIdx key f → ℂ) → ℝ≥0∞ := fun v => ∏ j, G₂ (v j)
  have hH₁ : Measurable H₁ := Finset.measurable_prod _ fun j _ =>
    hG₁.comp (measurable_pi_apply j)
  have hH₂ : Measurable H₂ := Finset.measurable_prod _ fun j _ =>
    hG₂.comp (measurable_pi_apply j)
  let H : (NonRef key f → ℂ) → ℝ≥0∞ := fun v =>
    H₁ (fun j => v j) * H₂ (fun j => v j)
  have hH : Measurable H := (hH₁.comp (measurable_pi_iff.2 fun _ => measurable_pi_apply _)).mul
    (hH₂.comp (measurable_pi_iff.2 fun _ => measurable_pi_apply _))
  have hmain := lintegral_cell_le_comp (N := N) key (gpRefSet key f) hR
    (fun z => ENNReal.ofReal (Real.exp ((∑ i, smearedKernel lam (z i - z (f i))) -
      cycleDisplacementSq key f z / ℓ))) H hH (fun u => by
        rw [sum_smearedKernel_gp_symm lam hR u hf0, cycleDisplacementSq_gp_symm]
        have he : 2 * ∑ j : CycIdx key f, smearedKernel lam (u j.1.1) +
            ∑ j : TreeIdx key f, smearedKernel lam (u j.1.1) -
            (∑ j : CycIdx key f, ‖u j.1.1‖ ^ 2) / ℓ =
            (∑ j : CycIdx key f, (2 * smearedKernel lam (u j.1.1) - ‖u j.1.1‖ ^ 2 / ℓ)) +
              ∑ j : TreeIdx key f, smearedKernel lam (u j.1.1) := by
          rw [sum_sub_distrib, ← mul_sum, sum_div]
          ring
        rw [he, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
          Real.exp_sum, Real.exp_sum,
          ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
          ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)])
  refine hmain.trans ?_
  rw [hK]
  gcongr
  refine (lintegral_ball_mul_le (fun j : NonRef key f => f (f j) = j) _ H₁ H₂ hH₁ hH₂).trans ?_
  have eC : CycIdx key f ≃ Fin K := Fintype.equivFinOfCardEq ((card_cycIdx hf0).trans hK)
  have eT : TreeIdx key f ≃ Fin (2 * p - 2 * K) := Fintype.equivFinOfCardEq (by
    rw [card_treeIdx hf0, hK, hcard])
  have hcycle : ∫⁻ v in {v : CycIdx key f → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ 36 * N / Real.pi}, H₁ v ≤
      (∫⁻ u, G₁ u) ^ K := by
    change (∫⁻ v in {v : CycIdx key f → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ 36 * N / Real.pi},
      ∏ j, G₁ (v j)) ≤ _
    rw [lintegral_ball_prod_equiv eC _ G₁]
    calc _ ≤ ∫⁻ v : Fin K → ℂ, ∏ j, G₁ (v j) := setLIntegral_le_lintegral _ _
      _ = (∫⁻ u, G₁ u) ^ K := by
        calc _ = ∏ _ : Fin K, ∫⁻ u, G₁ u :=
                lintegral_fin_nat_prod_eq_prod (μ := fun _ => volume) _ (fun _ => hG₁)
          _ = _ := by simp
  exact mul_le_mul' hcycle (le_of_eq (lintegral_ball_prod_equiv eT _ G₂))

/-- **The nonisolated components in (eq:critical-fixed-graph)**. If the graph has
`K` cycles and `2d` tree vertices, its Gaussian-regularized integral is at most
`N^K J_λ(1/ℓ)^K exp(d log(N/d) + Cd)`. The tree bound includes `d = 0`. -/
theorem exists_lintegral_cell_gaussian_le :
    ∃ C : ℝ, ∀ {ι : Type} [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ)
      (N p K : ℕ) (f : ι → ι), 0 < N → K ≤ p → Fintype.card ι = 2 * p →
      (∃ z₀ : ι → ℂ, nnMap key z₀ = f) →
      Fintype.card {i // i ∈ gpRefSet key f} = K → ∀ lam ℓ : ℝ, 0 < lam →
      ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
          ENNReal.ofReal (Real.exp ((∑ i, smearedKernel lam (z i - z (f i))) -
            cycleDisplacementSq key f z / ℓ)) ≤
        (N : ℝ≥0∞) ^ K *
          ((∫⁻ u : ℂ, ENNReal.ofReal (Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ))) ^ K *
            ENNReal.ofReal (Real.exp ((p - K : ℕ) * Real.log (N / (p - K : ℕ)) + C * (p - K : ℕ)))) := by
  obtain ⟨C, htree⟩ := exists_lintegral_ball_tree_le (β := 2) le_rfl (by norm_num)
  refine ⟨C, fun key N p K f hN hKp hcard hf hK lam ℓ hlam => ?_⟩
  refine (lintegral_cell_gaussian_le_cycle_mul_tree hcard key hf hK lam ℓ).trans ?_
  gcongr
  have h := htree N (p - K) (2 * p - 2 * K) hN (by omega) lam hlam
  norm_num at h
  convert h using 1
  congr 2
  ring

/-- **Gaussian decoupling of all cycle variables** (`source/dipole-formation.tex`, subsection 3.5,
Step 2). The common cutoff is inserted at cost `exp (36N/(πℓ))`. -/
theorem lintegral_cell_le_common_gaussian [Nontrivial ι] {N : ℕ} (key : ι ↪ ℕ)
    {f : ι → ι} {lam ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
        ENNReal.ofReal (Real.exp (∑ i, smearedKernel lam (z i - z (f i)))) ≤
      ENNReal.ofReal (Real.exp (36 * N / (Real.pi * ℓ))) *
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
          ENNReal.ofReal (Real.exp ((∑ i, smearedKernel lam (z i - z (f i))) -
            cycleDisplacementSq key f z / ℓ)) := by
  have hm : MeasurableSet ((Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f}) := by
    refine (MeasurableSet.univ_pi fun _ => measurableSet_box N).inter ?_
    have he : {z : ι → ℂ | nnMap key z = f} = ⋂ i, {z | nnMap key z i = f i} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    rw [he]
    exact MeasurableSet.iInter fun i => measurableSet_nnMap_eq key i (f i)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hm fun z hz => ?_
  have hp := cycleDisplacementSq_le key z (fun i => hz.1 i (Set.mem_univ i))
  rw [hz.2] at hp
  have hd : cycleDisplacementSq key f z / ℓ ≤ 36 * N / (Real.pi * ℓ) := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hp hℓ.le
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith only [hd]))

/-- **The nonisolated-component contribution** in (eq:critical-fixed-graph), before
integrating isolated pairs. At `ℓ = |log λ|`, the mass of each of the `K` remaining
cycles is `J_λ(1/ℓ)`. No cycle-count-dependent Gaussian parameter is used. -/
theorem exists_lintegral_cell_common_cutoff_le :
    ∃ C : ℝ, ∀ {ι : Type} [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ)
      (N p K : ℕ) (f : ι → ι), 0 < N → K ≤ p → Fintype.card ι = 2 * p →
      (∃ z₀ : ι → ℂ, nnMap key z₀ = f) →
      Fintype.card {i // i ∈ gpRefSet key f} = K → ∀ lam ℓ : ℝ, 0 < lam → 0 < ℓ →
      ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
          ENNReal.ofReal (Real.exp (∑ i, smearedKernel lam (z i - z (f i)))) ≤
        ENNReal.ofReal (Real.exp (36 * N / (Real.pi * ℓ))) *
          ((N : ℝ≥0∞) ^ K *
            ((∫⁻ u : ℂ, ENNReal.ofReal (Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ))) ^ K *
              ENNReal.ofReal (Real.exp ((p - K : ℕ) * Real.log (N / (p - K : ℕ)) +
                C * (p - K : ℕ))))) := by
  obtain ⟨C, h⟩ := exists_lintegral_cell_gaussian_le
  refine ⟨C, fun key N p K f hN hKp hcard hf hK lam ℓ hlam hℓ => ?_⟩
  exact (lintegral_cell_le_common_gaussian key hℓ).trans
    (mul_le_mul_right (h key N p K f hN hKp hcard hf hK lam ℓ hlam) _)

end Gaussian

end TwoComponentCoulomb

end
