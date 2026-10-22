/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Energy
public import TwoComponentCoulomb.LowerBound.ScreenedField
import TwoComponentCoulomb.Potential.ElectricEnergy

/-!
# The energy of the screened dipoles and eq. (majof) (Proposition 4.1, Step 1)

Source: Proposition 4.1, Step 1 (l. 1762–1825), as ruled in
R22. The source decomposes `u_i = g*δ_{x_i}^{(λ)} - g*δ_{y_i}^{(λ)} + v_i` with `v_i` harmonic and
eq. (estimatesv) `|∇v_i| ≤ C |x_i - y_i| / ϱ(x_i)²` on `B(x_i, 3ϱ(x_i)/4)` (l. 1798–1806), computes
the energy of each ball (l. 1807–1814),
`∫_{B(x_i, ϱ(x_i))} |∇u_i|² = 2π ∫ u_i d(δ_{x_i}^{(λ)} - δ_{y_i}^{(λ)})
  = 4π (g(λ) + κ) - 4π g_λ(x_i - y_i) + O(|x_i - y_i|² / ϱ(x_i)²)`,
and inserts it into eq. (hui) and eq. (eq:rewrF) to obtain eq. (majof) (l. 1815–1816). Under ruling
R22a, `u_i` is the explicit image-charge solution `neumannPotential` of
`LowerBound/NeumannDipole.lean`, and the `O(·)` is explicit.

* `integral_ball_norm_sq_neumannField` : the energy of one ball (l. 1807–1814), with the error term
  `2π (∫ v dδ_c^{(λ)} - ∫ v dδ_y^{(λ)})` kept exact. It is the weak Neumann problem
  `integral_ball_fderiv_neumannField` tested against `ξ = u` (which is `C¹` on `B(c, 2ρ)`), together
  with the pair-energy identity `integral_neumannPotential_sub`.
* `energy_sum_elim_le_screened` : eq. (majof) with the explicit constant `1`: by eq. (eq:rewrF)
  (`energy_eq_integral_norm_sq_electricField`), eq. (hui)
  (`integral_norm_sq_electricField_le_screened`), the energy of each ball, and the coupling bound
  `|∫ v d(δ_c^{(λ)} - δ_y^{(λ)})| ≤ 2 |y - c|² / ρ²` (`abs_integral_neumannCorrection_sub_le`, from
  eq. (estimatesv)), the error is `(1 / 4π) · 2π · 2 |y_i - x_i|² / ϱ_i² = |y_i - x_i|² / ϱ_i²`.
  The source writes `g_λ(x_i - y_i)`; `g_λ` is even (`smearedKernel_neg`).
-/

public section

open MeasureTheory Metric Set InnerProductSpace

namespace TwoComponentCoulomb

/-- **The energy of one ball** (source l. 1807–1814): with `v = neumannCorrection ρ c y`,
`∫_{B(c,ρ)} |∇u|² = 4π (g(λ) + κ) - 4π g_λ(y - c) + 2π (∫ v dδ_c^{(λ)} - ∫ v dδ_y^{(λ)})`. -/
theorem integral_ball_norm_sq_neumannField {lam ρ : ℝ} {c y : ℂ} (hlam : 0 < lam)
    (hρ : 4 * lam ≤ ρ) (hy : ‖y - c‖ ≤ ρ / 2) :
    ∫ z in Metric.ball c ρ, ‖neumannField lam ρ c y z‖ ^ 2 =
      4 * Real.pi * (logKernel (lam : ℂ) + kappa) - 4 * Real.pi * smearedKernel lam (y - c) +
        2 * Real.pi * ((∫ w, neumannCorrection ρ c y w ∂smearedCharge c lam) -
          ∫ w, neumannCorrection ρ c y w ∂smearedCharge y lam) := by
  have hρ0 : 0 < ρ := by linarith
  have hsub : ball c ρ ⊆ ball c (2 * ρ) := ball_subset_ball (by linarith)
  have hpt : ∀ z ∈ ball c ρ, fderiv ℝ (neumannPotential lam ρ c y) z (neumannField lam ρ c y z) =
      ‖neumannField lam ρ c y z‖ ^ 2 := by
    intro z hz
    rw [(hasGradientAt_neumannPotential hlam hρ hy (hsub hz)).hasFDerivAt.fderiv,
      toDual_apply_apply, real_inner_self_eq_norm_sq]
  rw [← setIntegral_congr_fun measurableSet_ball hpt,
    integral_ball_fderiv_neumannField hlam hρ hy isOpen_ball
      (closedBall_subset_ball (by linarith)) (contDiffOn_neumannPotential hlam hρ hy),
    integral_neumannPotential_sub hlam hρ hy]
  ring

/-- **Eq. (majof)** (source l. 1815–1816): for disjoint discs `B(x_i, ρ_i)` with `4λ ≤ ρ_i` and
`|y_i - x_i| ≤ ρ_i / 2`, `F_λ(X_N, Y_N) ≤ -Σ_i g_λ(y_i - x_i) + Σ_i |y_i - x_i|² / ρ_i²`. The
constant is `(1 / 4π) · 2π · 2 = 1`. -/
theorem energy_sum_elim_le_screened {N : ℕ} {lam : ℝ} (hlam : 0 < lam) (X Y : Fin N → ℂ)
    (ρ : Fin N → ℝ) (hρ : ∀ i, 4 * lam ≤ ρ i)
    (hdisj : ∀ i j, i ≠ j → ρ i + ρ j ≤ ‖X i - X j‖) (hY : ∀ i, ‖Y i - X i‖ ≤ ρ i / 2) :
    energy lam (Sum.elim X Y) ≤
      -∑ i, smearedKernel lam (Y i - X i) + ∑ i, ‖Y i - X i‖ ^ 2 / ρ i ^ 2 := by
  set D : Fin N → ℝ := fun i =>
    (∫ w, neumannCorrection (ρ i) (X i) (Y i) w ∂smearedCharge (X i) lam) -
      ∫ w, neumannCorrection (ρ i) (X i) (Y i) w ∂smearedCharge (Y i) lam with hDdef
  have hD : ∀ i, D i ≤ 2 * (‖Y i - X i‖ ^ 2 / ρ i ^ 2) := fun i => by
    rw [mul_div_assoc']
    exact (le_abs_self _).trans (abs_integral_neumannCorrection_sub_le hlam (hρ i) (hY i))
  have hui := integral_norm_sq_electricField_le_screened hlam X Y ρ hρ hdisj hY
  have hball : ∀ i, ∫ z in ball (X i) (ρ i), ‖neumannField lam (ρ i) (X i) (Y i) z‖ ^ 2 =
      4 * Real.pi * (logKernel (lam : ℂ) + kappa) -
        4 * Real.pi * smearedKernel lam (Y i - X i) + 2 * Real.pi * D i := fun i =>
    integral_ball_norm_sq_neumannField hlam (hρ i) (hY i)
  simp_rw [hball] at hui
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum] at hui
  have hsumD : ∑ i, D i ≤ 2 * ∑ i, ‖Y i - X i‖ ^ 2 / ρ i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hD i
  rw [energy_eq_integral_norm_sq_electricField (Sum.elim X Y) hlam]
  have h4pi : 0 < 1 / (4 * Real.pi) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hui h4pi.le
  have hexp : 1 / (4 * Real.pi) * (N * (4 * Real.pi * (logKernel (lam : ℂ) + kappa)) -
      4 * Real.pi * ∑ i, smearedKernel lam (Y i - X i) + 2 * Real.pi * ∑ i, D i) =
      N * (logKernel (lam : ℂ) + kappa) - ∑ i, smearedKernel lam (Y i - X i) +
        (1 / 2) * ∑ i, D i := by
    field_simp
    ring
  rw [hexp] at hmul
  linarith

end TwoComponentCoulomb

end
