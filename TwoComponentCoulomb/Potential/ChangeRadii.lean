/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Potential.ElectricEnergy
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.PairIntegral

/-!
# The polarized change-of-radii identity

Lemma 2.4, source `source/dipole-formation.tex`, l. 499–515. Newton's theorem makes
`h_τ - h_α` compactly supported. We use this difference as a test function in the
Poisson equations for `h_τ` and `h_α`, add the two Green identities, and identify
`∇(h_τ - h_α) · ∇(h_τ + h_α)` with `|∇h_τ|² - |∇h_α|²`.
Expanding the potentials gives the full two-radius formula. Symmetry then cancels
the mixed interactions, as in (peq).
-/

public section

open MeasureTheory InnerProductSpace

namespace TwoComponentCoulomb

section
variable {ι : Type*} [Fintype ι] {d : ι → ℝ} {z : ι → ℂ} {τ α : ι → ℝ}

/-- Integration by parts with the compactly supported difference of two potentials. -/
theorem integral_norm_sq_sub_electricField_eq_potential (hτ : ∀ i, 0 < τ i)
    (hα : ∀ i, 0 < α i) :
    (∫ x, ‖electricField d z τ x‖ ^ 2 - ‖electricField d z α x‖ ^ 2) =
      2 * Real.pi * ∑ j, d j *
        ((∫ x, (electricPotential d z τ x - electricPotential d z α x)
          ∂smearedCharge (z j) (τ j)) +
         ∫ x, (electricPotential d z τ x - electricPotential d z α x)
          ∂smearedCharge (z j) (α j)) := by
  let ξ : ℂ → ℝ := fun x => electricPotential d z τ x - electricPotential d z α x
  have hξ : ContDiff ℝ 1 ξ :=
    (contDiff_electricPotential hτ).sub (contDiff_electricPotential hα)
  have hc : HasCompactSupport ξ := hasCompactSupport_electricPotential_sub hτ hα
  have hI : ∀ β : ι → ℝ, (∀ i, 0 < β i) →
      Integrable (fun x => fderiv ℝ ξ x (electricField d z β x)) := by
    intro β hβ
    apply Continuous.integrable_of_hasCompactSupport
      ((hξ.continuous_fderiv one_ne_zero).clm_apply (continuous_electricField hβ))
    exact (hc.fderiv (𝕜 := ℝ)).mono' fun x hx => subset_tsupport _ fun h => hx (by simp [h])
  have hgrad : ∀ x v, fderiv ℝ ξ x v =
      inner ℝ (electricField d z τ x - electricField d z α x) v := by
    intro x v
    rw [fderiv_fun_sub (differentiable_electricPotential hτ x)
      (differentiable_electricPotential hα x)]
    simp only [sub_apply, fderiv_electricPotential_apply hτ,
      fderiv_electricPotential_apply hα, inner_sub_left]
  calc
    _ = ∫ x, inner ℝ (electricField d z τ x - electricField d z α x)
        (electricField d z τ x + electricField d z α x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq]
        rw [real_inner_comm (electricField d z α x) (electricField d z τ x)]
        ring
    _ = ∫ x, fderiv ℝ ξ x (electricField d z τ x) +
        fderiv ℝ ξ x (electricField d z α x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp only [hgrad, inner_add_right]
    _ = _ := by
      rw [integral_add (hI τ hτ) (hI α hα),
        integral_fderiv_apply_electricField hξ hc hτ,
        integral_fderiv_apply_electricField hξ hc hα]
      simp only [Finset.sum_add_distrib, mul_add]
      ring

/-- The mean of a difference of potentials, expanded into its individual disc charges. -/
private theorem integral_potential_sub (hτ : ∀ i, 0 < τ i) (hα : ∀ i, 0 < α i)
    (w : ℂ) (b : ℝ) :
    (∫ x, (electricPotential d z τ x - electricPotential d z α x) ∂smearedCharge w b) =
      ∑ i, d i * ∫ x, (discPotential (τ i) (x - z i) - discPotential (α i) (x - z i))
        ∂smearedCharge w b := by
  have hI : ∀ i, Integrable (fun x => discPotential (τ i) (x - z i) -
      discPotential (α i) (x - z i)) (smearedCharge w b) := fun i =>
    integrable_smearedCharge_of_continuous
      (((contDiff_discPotential (hτ i)).continuous.comp (continuous_id.sub continuous_const)).sub
        ((contDiff_discPotential (hα i)).continuous.comp (continuous_id.sub continuous_const))) w b
  have he : ∀ x, electricPotential d z τ x - electricPotential d z α x =
      ∑ i, d i * (discPotential (τ i) (x - z i) - discPotential (α i) (x - z i)) := by
    intro x
    simp only [electricPotential, mul_sub, Finset.sum_sub_distrib]
  simp_rw [he]
  rw [integral_finsetSum _ fun i _ => (hI i).const_mul (d i)]
  simp only [integral_const_mul]

/-- Lemma 2.4 in full: the difference of Dirichlet energies is the potential difference
paired with the sum of the two radius-vector charge measures. -/
theorem integral_norm_sq_sub_electricField (hτ : ∀ i, 0 < τ i) (hα : ∀ i, 0 < α i) :
    (∫ x, ‖electricField d z τ x‖ ^ 2 - ‖electricField d z α x‖ ^ 2) =
      2 * Real.pi * ∑ i, ∑ j, d i * d j *
        ((∫ x, (discPotential (τ i) (x - z i) - discPotential (α i) (x - z i))
          ∂smearedCharge (z j) (τ j)) +
         ∫ x, (discPotential (τ i) (x - z i) - discPotential (α i) (x - z i))
          ∂smearedCharge (z j) (α j)) := by
  rw [integral_norm_sq_sub_electricField_eq_potential hτ hα]
  simp_rw [integral_potential_sub hτ hα]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Symmetry of the interaction of two disc charges. -/
theorem pairInteraction_comm (z w : ℂ) (a b : ℝ) :
    pairInteraction z w a b = pairInteraction w z b a := by
  unfold pairInteraction
  rw [← integral_prod_swap (fun p : ℂ × ℂ => logKernel (p.1 - p.2))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    simp only [Prod.swap, ← neg_sub p.1 p.2, logKernel_neg]

/-- The mixed interactions in Lemma 2.4 cancel by exchanging `i` and `j`, giving (peq). -/
theorem integral_norm_sq_electricField_sub (hτ : ∀ i, 0 < τ i) (hα : ∀ i, 0 < α i)
    (hn : ∑ i, d i = 0) :
    (∫ x, ‖electricField d z τ x‖ ^ 2) - (∫ x, ‖electricField d z α x‖ ^ 2) =
      2 * Real.pi * ∑ i, ∑ j, d i * d j *
        (pairInteraction (z i) (z j) (τ i) (τ j) -
          pairInteraction (z i) (z j) (α i) (α j)) := by
  have hI : ∀ β : ι → ℝ, (∀ i, 0 < β i) → ∀ i w b,
      Integrable (fun x => discPotential (β i) (x - z i)) (smearedCharge w b) := by
    intro β hβ i w b
    exact integrable_smearedCharge_of_continuous
      ((contDiff_discPotential (hβ i)).continuous.comp (continuous_id.sub continuous_const)) w b
  have he : ∀ i j,
      ((∫ x, (discPotential (τ i) (x - z i) - discPotential (α i) (x - z i))
        ∂smearedCharge (z j) (τ j)) +
       ∫ x, (discPotential (τ i) (x - z i) - discPotential (α i) (x - z i))
        ∂smearedCharge (z j) (α j)) =
      pairInteraction (z i) (z j) (τ i) (τ j) - pairInteraction (z i) (z j) (α i) (τ j) +
      pairInteraction (z i) (z j) (τ i) (α j) - pairInteraction (z i) (z j) (α i) (α j) := by
    intro i j
    rw [integral_sub (hI τ hτ i _ _) (hI α hα i _ _),
      integral_sub (hI τ hτ i _ _) (hI α hα i _ _)]
    simp_rw [← pairInteraction_eq_integral_discPotential _ _ (hτ i),
      ← pairInteraction_eq_integral_discPotential _ _ (hα i)]
    rw [pairInteraction_comm (z j) (z i) (τ j) (τ i),
      pairInteraction_comm (z j) (z i) (τ j) (α i),
      pairInteraction_comm (z j) (z i) (α j) (τ i),
      pairInteraction_comm (z j) (z i) (α j) (α i)]
    ring
  have hm : (∑ i, ∑ j, d i * d j * pairInteraction (z i) (z j) (α i) (τ j)) =
      ∑ i, ∑ j, d i * d j * pairInteraction (z i) (z j) (τ i) (α j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [pairInteraction_comm (z i) (z j) (α i) (τ j)]
    ring
  rw [← integral_sub (integrable_norm_sq_electricField hτ hn)
    (integrable_norm_sq_electricField hα hn), integral_norm_sq_sub_electricField hτ hα]
  simp only [he, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hm]
  ring

end

end TwoComponentCoulomb

end
