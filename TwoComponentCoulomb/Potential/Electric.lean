/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.LogKernel
public import TwoComponentCoulomb.Frozen.SmearedCharge
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.Potential.DiscField
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.PairIntegral

/-!
# The electric potential and field of a configuration of disc charges

For a finite family of real charges `d i`, centres `z i` and radii `α i > 0`, the electric potential
`h_α = g * Σᵢ dᵢ δ_{zᵢ}^{(αᵢ)}` (source eq. (eq:heta) l. 177 and eq. (defhalpha) l. 364) is
implemented through the explicit radial disc potentials of `Potential/DiscField.lean`
(ruling R12b): `h_α(x) = Σᵢ dᵢ discPotential αᵢ (x - zᵢ)` and its gradient
`∇h_α(x) = Σᵢ dᵢ discField αᵢ (x - zᵢ)`.

* `electricPotential`, `electricField` : the potential and its (claimed) gradient.
* `pairInteraction z w a b` : the interaction `∬ g(x - y) dδ_z^{(a)}(x) dδ_w^{(b)}(y)` of two
  uniform discs.
* `hasGradientAt_electricPotential`, `contDiff_electricPotential`, `continuous_electricField` :
  `∇ h_α = electricField`, `h_α` is `C¹`, and the field is continuous.
* `pairInteraction_eq_integral_discPotential`, `pairInteraction_eq_smearedKernel` : the pair
  interaction as the integral of a disc potential against a disc (Fubini and Newton's theorem),
  and its relation to `g_λ`.
* `integral_fderiv_apply_electricField` : the Green identity
  `∫ ∇ξ · ∇h_α = 2π Σᵢ dᵢ ∫ ξ dδ_{zᵢ}^{(αᵢ)}` for `C¹` compactly supported `ξ`.
-/

@[expose] public section

open MeasureTheory InnerProductSpace

namespace TwoComponentCoulomb

/-- `h_α(x) = Σ_i d_i (g * δ_{z_i}^{(α_i)})(x)` (eq. defhalpha / eq:heta). -/
noncomputable def electricPotential {ι : Type*} [Fintype ι] (d : ι → ℝ) (z : ι → ℂ) (α : ι → ℝ)
    (x : ℂ) : ℝ :=
  ∑ i, d i * discPotential (α i) (x - z i)

/-- `∇h_α(x)`. -/
noncomputable def electricField {ι : Type*} [Fintype ι] (d : ι → ℝ) (z : ι → ℂ) (α : ι → ℝ)
    (x : ℂ) : ℂ :=
  ∑ i, d i • discField (α i) (x - z i)

/-- The pair interaction `∬ g(x − y) dδ_z^{(a)}(x) dδ_w^{(b)}(y)` of two uniform discs. -/
noncomputable def pairInteraction (z w : ℂ) (a b : ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, logKernel (p.1 - p.2) ∂(smearedCharge z a).prod (smearedCharge w b)

section Regularity

variable {ι : Type*} [Fintype ι] {d : ι → ℝ} {z : ι → ℂ} {α : ι → ℝ}

/-- **The gradient of the electric potential** : `∇ h_α = electricField`. -/
theorem hasGradientAt_electricPotential (hα : ∀ i, 0 < α i) (x : ℂ) :
    HasGradientAt (electricPotential d z α) (electricField d z α x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : ∀ i ∈ Finset.univ, HasFDerivAt (fun y => d i * discPotential (α i) (y - z i))
      (d i • toDual ℝ ℂ (discField (α i) (x - z i))) x := fun i _ => by
    have := (hasFDerivAt_discPotential (hα i) (x - z i)).comp x
      ((hasFDerivAt_id x).sub_const (z i))
    simpa using this.const_mul (d i)
  have h2 := HasFDerivAt.fun_sum h
  have e2 : toDual ℝ ℂ (electricField d z α x) =
      ∑ i, d i • toDual ℝ ℂ (discField (α i) (x - z i)) := by
    rw [electricField, map_sum]
    simp_rw [map_smul]
  rw [e2]
  exact h2

/-- The electric potential is differentiable. -/
theorem differentiable_electricPotential (hα : ∀ i, 0 < α i) :
    Differentiable ℝ (electricPotential d z α) := fun x =>
  (hasGradientAt_electricPotential hα x).differentiableAt

/-- The electric field is continuous. -/
theorem continuous_electricField (hα : ∀ i, 0 < α i) : Continuous (electricField d z α) := by
  unfold electricField
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_const (y := d i)).smul
    ((continuous_discField (hα i)).comp (continuous_id.sub continuous_const))

/-- The electric potential is of class `C¹`. -/
theorem contDiff_electricPotential (hα : ∀ i, 0 < α i) : ContDiff ℝ 1 (electricPotential d z α) := by
  refine contDiff_one_iff_fderiv.2 ⟨differentiable_electricPotential hα, ?_⟩
  have : fderiv ℝ (electricPotential d z α) =
      fun x => toDual ℝ ℂ (electricField d z α x) :=
    funext fun x => (hasGradientAt_electricPotential hα x).hasFDerivAt.fderiv
  rw [this]
  exact (toDual ℝ ℂ).continuous.comp (continuous_electricField hα)

/-- `∇ h_α(x) · v = ⟪electricField x, v⟫_ℝ`. -/
theorem fderiv_electricPotential_apply (hα : ∀ i, 0 < α i) (x v : ℂ) :
    fderiv ℝ (electricPotential d z α) x v = ⟪electricField d z α x, v⟫_ℝ := by
  rw [(hasGradientAt_electricPotential hα x).hasFDerivAt.fderiv, toDual_apply_apply]

/-- The field is globally Lipschitz for positive radii. Together with
`contDiff_electricPotential`, this gives the local `C^{1,1}` regularity used in Lemma 2.4. -/
theorem lipschitzWith_electricField (hα : ∀ i, 0 < α i) :
    LipschitzWith (∑ i, |d i| * (α i ^ 2)⁻¹).toNNReal (electricField d z α) := by
  have hK : 0 ≤ ∑ i, |d i| * (α i ^ 2)⁻¹ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (inv_nonneg.2 (sq_nonneg _))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK, electricField, electricField,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  simpa only [Real.coe_toNNReal _ (inv_nonneg.2 (sq_nonneg _)),
    sub_sub_sub_cancel_right] using
    (lipschitzWith_discField (hα i)).norm_sub_le (x - z i) (y - z i)

/-- By Newton's theorem the difference of potentials with two positive radius vectors
has compact support (Lemma 2.4). Neutrality is not needed for this step. -/
theorem hasCompactSupport_electricPotential_sub {τ : ι → ℝ}
    (hτ : ∀ i, 0 < τ i) (hα : ∀ i, 0 < α i) :
    HasCompactSupport (fun x => electricPotential d z τ x - electricPotential d z α x) := by
  classical
  let R : ℝ := ∑ i, (‖z i‖ + max (τ i) (α i))
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R)
  intro x hx
  have hxR : R < ‖x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hx
  have hfar : ∀ i, max (τ i) (α i) ≤ ‖x - z i‖ := by
    intro i
    have hi : ‖z i‖ + max (τ i) (α i) ≤ R :=
      Finset.single_le_sum (fun j _ => add_nonneg (norm_nonneg _)
        ((hτ j).le.trans (le_max_left _ _))) (Finset.mem_univ i)
    have hn : ‖x‖ ≤ ‖x - z i‖ + ‖z i‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - z i) (z i)
    linarith
  apply sub_eq_zero.mpr
  unfold electricPotential
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← integral_logKernel_sub_smearedCharge_eq_discPotential (hτ i) x (z i),
    integral_logKernel_sub_smearedCharge_of_le x (z i) (hτ i)
      ((le_max_left _ _).trans (hfar i)),
    ← integral_logKernel_sub_smearedCharge_eq_discPotential (hα i) x (z i),
    integral_logKernel_sub_smearedCharge_of_le x (z i) (hα i)
      ((le_max_right _ _).trans (hfar i))]

end Regularity

section PairInteraction

/-- The pair interaction as the integral of the potential of one disc against the other disc:
`∬ g(x - y) dδ_z^{(a)}(x) dδ_w^{(b)}(y) = ∫ (g * δ_w^{(b)})(x) dδ_z^{(a)}(x)` (Fubini and
Newton's theorem; the radius `a` may be arbitrary since the measure vanishes for `a ≤ 0`). -/
theorem pairInteraction_eq_integral_discPotential (z w : ℂ) {a b : ℝ} (hb : 0 < b) :
    pairInteraction z w a b = ∫ x, discPotential b (x - w) ∂smearedCharge z a := by
  unfold pairInteraction
  rw [integral_prod _ (integrable_logKernel_prod_smearedCharge z w a b)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    integral_logKernel_sub_smearedCharge_eq_discPotential hb x w)

/-- For equal radii the pair interaction is `g_λ` at the difference of the centres. -/
theorem pairInteraction_eq_smearedKernel (z w : ℂ) (lam : ℝ) :
    pairInteraction z w lam lam = smearedKernel lam (w - z) :=
  integral_logKernel_prod_smearedCharge z w lam

end PairInteraction

section Green

variable {ι : Type*} [Fintype ι] {d : ι → ℝ} {z : ι → ℂ} {α : ι → ℝ}

/-- **The Green identity for a configuration of disc charges** (no neutrality needed):
`∫ ∇ξ · ∇h_α = 2π Σᵢ dᵢ ∫ ξ dδ_{zᵢ}^{(αᵢ)}` for `ξ` of class `C¹` with compact support
(source l. 1842–1866, Theorem 2, Step 1). -/
theorem integral_fderiv_apply_electricField {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport ξ) (hα : ∀ i, 0 < α i) :
    ∫ x, fderiv ℝ ξ x (electricField d z α x) =
      2 * Real.pi * ∑ i, d i * ∫ y, ξ y ∂smearedCharge (z i) (α i) := by
  have h1 : ∀ x : ℂ, fderiv ℝ ξ x (electricField d z α x) =
      ∑ i, d i * fderiv ℝ ξ x (discField (α i) (x - z i)) := fun x => by
    rw [electricField, map_sum]
    simp_rw [map_smul, smul_eq_mul]
  have hint : ∀ i, Integrable (fun x : ℂ => fderiv ℝ ξ x (discField (α i) (x - z i))) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hξ.continuous_fderiv one_ne_zero)).clm_apply
        ((continuous_discField (hα i)).comp (continuous_id.sub continuous_const))
    · refine (hc.fderiv (𝕜 := ℝ)).mono' fun x hx => subset_tsupport _ ?_
      intro h0
      exact hx (by simp [h0])
  simp_rw [h1]
  rw [integral_finsetSum _ fun i _ => (hint i).const_mul (d i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_fderiv_apply_discField hξ hc (hα i) (z i)]
  ring

end Green

end TwoComponentCoulomb

end
