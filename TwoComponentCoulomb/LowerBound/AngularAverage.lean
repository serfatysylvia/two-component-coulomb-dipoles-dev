/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.Frozen.Energy
public import TwoComponentCoulomb.Potential.DiscPotential
public import TwoComponentCoulomb.Potential.PairIntegral
public import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# The angular average of the energy of dipole configurations

Source: Proposition 4.1, Step 1, replaced by the author-approved
route of ruling R12a (Newton's theorem and Jensen's inequality, in place of the Neumann problem,
l. 1775--1818).

Positive charges sit at `x_i`, negative charges at `y_i = x_i + s_i e^{iθ_i}`. We prove that
the energy `F_λ`, averaged over the angles `θ ∈ (-π, π)^N`, is exactly `-∑ g_λ(s_i)` as soon as
the discs `B(x_i, s_i + λ)` are `λ`-separated, i.e. `s_i + s_j + 2λ ≤ |x_i - x_j|`.

* `circleAverage_smearedKernel` : if `|v| ≥ s + 2λ` then
  `∫_{-π}^{π} g_λ(v - s e^{iθ}) dθ = 2π g_λ(v)` (Newton's theorem on the circle).
* `dipoleInteraction` : the interaction `T_ij` of two dipoles;
  `integral_dipoleInteraction_eq_zero` : it averages to zero over the direction of either dipole
  as soon as the dipoles are `2λ`-separated.
* `energy_sum_elim_eq` : `F_λ(x, y) = -∑ g_λ(y_i - x_i) + ½ ∑_{i ≠ j} T_ij`.
* `integral_pi_eq_zero_of_integral_update_eq_zero` : Fubini in one coordinate of a product
  measure.
* `averaged_energy_eq` : `∫_{(-π,π)^N} F_λ dθ = -(2π)^N ∑ g_λ(s_i)`.
-/

public section

open MeasureTheory Set

namespace TwoComponentCoulomb

/-! ### The circle average of `g_λ` -/

section CircleAverage

/-- A point of the circle of radius `s` about `0` has norm `s`. -/
theorem norm_circleMap_zero_of_nonneg {s : ℝ} (hs : 0 ≤ s) (θ : ℝ) :
    ‖circleMap 0 s θ‖ = s := by
  rw [norm_circleMap_zero, abs_of_nonneg hs]

/-- `g_λ` is continuous along any circle. -/
theorem continuous_smearedKernel_sub_circleMap {lam : ℝ} (hlam : 0 < lam) (v : ℂ) (s : ℝ) :
    Continuous fun θ : ℝ => smearedKernel lam (v - circleMap 0 s θ) :=
  (continuous_smearedKernel hlam).comp (continuous_const.sub (continuous_circleMap 0 s))

/-- Integrability of `g_λ` along a circle. -/
theorem integrableOn_smearedKernel_sub_circleMap {lam : ℝ} (hlam : 0 < lam) (v : ℂ) (s : ℝ) :
    IntegrableOn (fun θ : ℝ => smearedKernel lam (v - circleMap 0 s θ))
      (Ioo (-Real.pi) Real.pi) :=
  ((continuous_smearedKernel_sub_circleMap hlam v s).integrableOn_Icc).mono_set Ioo_subset_Icc_self

/-- Newton's theorem on the circle (source l. 165 and Step 1 of Prop. 4.1, ruling R12a):
if `|v| ≥ s + 2λ`, the average of `g_λ(v - s e^{iθ})` over `θ` is `g_λ(v)`. -/
theorem circleAverage_smearedKernel {lam s : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) {v : ℂ}
    (hv : s + 2 * lam ≤ ‖v‖) :
    ∫ θ in Ioo (-Real.pi) Real.pi, smearedKernel lam (v - circleMap 0 s θ) =
      2 * Real.pi * smearedKernel lam v := by
  have hv2 : 2 * lam ≤ ‖v‖ := by linarith
  have hpt : ∀ θ : ℝ, smearedKernel lam (v - circleMap 0 s θ) =
      -Real.log ‖v - circleMap 0 s θ‖ := by
    intro θ
    refine smearedKernel_eq_logKernel hlam ?_
    have h1 := norm_sub_norm_le v (circleMap 0 s θ)
    rw [norm_circleMap_zero_of_nonneg hs] at h1
    linarith
  rw [smearedKernel_eq_logKernel hlam hv2]
  simp_rw [hpt]
  rw [integral_neg]
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    have h1 : ∀ θ : ℝ, circleMap 0 0 θ = 0 := fun θ => by simp [circleMap]
    simp only [h1, sub_zero, setIntegral_const, Real.volume_real_Ioo, smul_eq_mul]
    rw [max_eq_left (by linarith [Real.pi_pos])]
    simp only [logKernel]
    ring
  · rw [integral_Ioo_log_norm_sub_circleMap v hpos, max_eq_right (by linarith)]
    simp [logKernel]

end CircleAverage

/-! ### The interaction of two dipoles -/

section Interaction

/-- The interaction `g_λ(x_j - x_i) - g_λ(y_j - x_i) - g_λ(x_j - y_i) + g_λ(y_j - y_i)` between
the dipole `(x_i, y_i)` and the dipole `(x_j, y_j)`, with positive charges at the `x`'s and
negative charges at the `y`'s. -/
noncomputable def dipoleInteraction (lam : ℝ) (xi xj yi yj : ℂ) : ℝ :=
  smearedKernel lam (xj - xi) - smearedKernel lam (yj - xi) - smearedKernel lam (xj - yi) +
    smearedKernel lam (yj - yi)

/-- If `y_i` is within `s_i` of `x_i` and the discs of radii `s_i` about `x_i` and `s_j` about `x_j`
are `2λ`-separated, the interaction of the dipoles averages to zero over the direction `φ` of the
second dipole. This is Newton's theorem (`circleAverage_smearedKernel`) applied to the two terms
that involve `y_j`. -/
theorem integral_dipoleInteraction_eq_zero {lam si sj : ℝ} (hlam : 0 < lam) (hsj : 0 ≤ sj)
    {xi xj yi : ℂ} (hyi : ‖yi - xi‖ ≤ si) (hsep : si + sj + 2 * lam ≤ ‖xi - xj‖) :
    ∫ φ in Ioo (-Real.pi) Real.pi,
        dipoleInteraction lam xi xj yi (xj + circleMap 0 sj φ) = 0 := by
  have hv1 : sj + 2 * lam ≤ ‖xi - xj‖ := by
    have : 0 ≤ si := (norm_nonneg _).trans hyi
    linarith
  have hv2 : sj + 2 * lam ≤ ‖yi - xj‖ := by
    have h1 : ‖xi - xj‖ ≤ ‖xi - yi‖ + ‖yi - xj‖ := norm_sub_le_norm_sub_add_norm_sub xi yi xj
    rw [norm_sub_rev xi yi] at h1
    linarith
  have e1 : ∀ φ : ℝ, smearedKernel lam (xj + circleMap 0 sj φ - xi) =
      smearedKernel lam (xi - xj - circleMap 0 sj φ) := fun φ => by
    rw [← smearedKernel_neg]
    congr 1
    ring
  have e2 : ∀ φ : ℝ, smearedKernel lam (xj + circleMap 0 sj φ - yi) =
      smearedKernel lam (yi - xj - circleMap 0 sj φ) := fun φ => by
    rw [← smearedKernel_neg]
    congr 1
    ring
  have i1 := integrableOn_smearedKernel_sub_circleMap hlam (xi - xj) sj
  have i2 := integrableOn_smearedKernel_sub_circleMap hlam (yi - xj) sj
  have iC : ∀ c : ℝ, IntegrableOn (fun _ : ℝ => c) (Ioo (-Real.pi) Real.pi) := fun c =>
    integrableOn_const (by simp)
  unfold dipoleInteraction
  simp_rw [e1, e2]
  have key := integral_add (μ := volume.restrict (Ioo (-Real.pi) Real.pi))
    (f := fun φ => smearedKernel lam (xj - xi) -
      smearedKernel lam (xi - xj - circleMap 0 sj φ) - smearedKernel lam (xj - yi))
    (g := fun φ => smearedKernel lam (yi - xj - circleMap 0 sj φ))
    (((iC _).sub i1).sub (iC _)) i2
  have key2 := integral_sub (μ := volume.restrict (Ioo (-Real.pi) Real.pi))
    (f := fun φ => smearedKernel lam (xj - xi) - smearedKernel lam (xi - xj - circleMap 0 sj φ))
    (g := fun _ => smearedKernel lam (xj - yi)) ((iC _).sub i1) (iC _)
  have key3 := integral_sub (μ := volume.restrict (Ioo (-Real.pi) Real.pi))
    (f := fun _ => smearedKernel lam (xj - xi))
    (g := fun φ => smearedKernel lam (xi - xj - circleMap 0 sj φ)) (iC _) i1
  rw [key, key2, key3, circleAverage_smearedKernel hlam hsj hv1,
    circleAverage_smearedKernel hlam hsj hv2]
  have hm : volume.real (Ioo (-Real.pi) Real.pi) = 2 * Real.pi := by
    rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    ring
  have n1 : smearedKernel lam (yi - xj) = smearedKernel lam (xj - yi) := by
    rw [← smearedKernel_neg, neg_sub]
  have n2 : smearedKernel lam (xi - xj) = smearedKernel lam (xj - xi) := by
    rw [← smearedKernel_neg, neg_sub]
  simp only [setIntegral_const, hm, smul_eq_mul, n1, n2]
  ring

end Interaction

/-! ### The energy of a dipole configuration -/

section Energy

/-- The self-interaction of a dipole: `T_ii = 2 g_λ(0) - 2 g_λ(y_i - x_i)`. -/
theorem dipoleInteraction_self (lam : ℝ) (x y : ℂ) :
    dipoleInteraction lam x x y y = 2 * smearedKernel lam 0 - 2 * smearedKernel lam (y - x) := by
  have : smearedKernel lam (x - y) = smearedKernel lam (y - x) := by
    rw [← smearedKernel_neg, neg_sub]
  unfold dipoleInteraction
  simp only [sub_self, this]
  ring

/-- The energy `F_λ` of a configuration of `N` dipoles, `x_i` positive and `y_i` negative:
the self-interactions of the dipoles contribute `-∑ g_λ(y_i - x_i)`, and the remaining terms
are the interactions `T_ij` of distinct dipoles. -/
theorem energy_sum_elim_eq {N : ℕ} {lam : ℝ} (hlam : 0 < lam) (X Y : Fin N → ℂ) :
    energy lam (Sum.elim X Y) = -∑ i, smearedKernel lam (Y i - X i) +
      (1 / 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, dipoleInteraction lam (X i) (X j) (Y i) (Y j) := by
  classical
  rw [energy_eq_sum_smearedKernel]
  have hsum : ∑ a : Fin N ⊕ Fin N, ∑ b : Fin N ⊕ Fin N, charge a * charge b *
      smearedKernel lam (Sum.elim X Y b - Sum.elim X Y a) =
      ∑ i, ∑ j, dipoleInteraction lam (X i) (X j) (Y i) (Y j) := by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, charge_inl, charge_inr,
      dipoleInteraction]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∀ i, ∑ j, dipoleInteraction lam (X i) (X j) (Y i) (Y j) =
      dipoleInteraction lam (X i) (X i) (Y i) (Y i) +
        ∑ j ∈ Finset.univ.erase i, dipoleInteraction lam (X i) (X j) (Y i) (Y j) := fun i =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [hsum]
  simp only [hsplit, dipoleInteraction_self, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    smearedKernel_zero hlam, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  ring

end Energy

/-! ### The average over the angles -/

section Average

/-- Fubini in one coordinate: if `H` integrates to zero over each fibre of the `j`-th coordinate,
it integrates to zero over a product measure. -/
theorem integral_pi_eq_zero_of_integral_update_eq_zero {N : ℕ} (ν : Measure ℝ) [SigmaFinite ν]
    (j : Fin N) (H : (Fin N → ℝ) → ℝ) (hH : Integrable H (Measure.pi fun _ : Fin N => ν))
    (h : ∀ θ : Fin N → ℝ, ∫ φ, H (Function.update θ j φ) ∂ν = 0) :
    ∫ θ, H θ ∂(Measure.pi fun _ : Fin N => ν) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := j.pos; omega⟩
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) j
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j with he
  have h1 : ∫ θ, H θ ∂(Measure.pi fun _ : Fin (n + 1) => ν) =
      ∫ q, H (e.symm q) ∂(ν.prod (Measure.pi fun k : Fin n => ν)) := by
    rw [← hmp.integral_comp' (g := fun q => H (e.symm q))]
    simp
  have hint : Integrable (fun q => H (e.symm q)) (ν.prod (Measure.pi fun k : Fin n => ν)) :=
    ((hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hH
  rw [h1, integral_prod_symm _ hint]
  have h2 : ∀ y : Fin n → ℝ, ∫ x, H (e.symm (x, y)) ∂ν = 0 := by
    intro y
    have := h (e.symm (0, y))
    convert this using 3 with x
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
    show H (Fin.insertNth (α := fun _ => ℝ) j x y) =
      H (Function.update (Fin.insertNth (α := fun _ => ℝ) j (0 : ℝ) y) j x)
    rw [Fin.update_insertNth]
  simp [h2]

/-- A set integral over a box `(a, b)^N` is the integral against the product of the restrictions
of Lebesgue measure to `(a, b)`. -/
theorem setIntegral_pi_Ioo_eq {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (f : (Fin N → ℝ) → E) :
    ∫ θ in Set.univ.pi fun _ : Fin N => Ioo a b, f θ =
      ∫ θ, f θ ∂(Measure.pi fun _ : Fin N => volume.restrict (Ioo a b)) := by
  rw [← Measure.restrict_pi_pi]
  rfl

/-- A continuous function is integrable on the box `(-π, π)^N`. -/
theorem integrable_pi_Ioo_of_continuous {N : ℕ} {f : (Fin N → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f (Measure.pi fun _ : Fin N => volume.restrict (Ioo (-Real.pi) Real.pi)) := by
  rw [← Measure.restrict_pi_pi]
  have hK : IsCompact (Set.univ.pi fun _ : Fin N => Icc (-Real.pi) Real.pi) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact (hf.continuousOn.integrableOn_compact hK).mono_set
    (Set.pi_mono fun _ _ => Ioo_subset_Icc_self)

/-- The box `(-π, π)^N` has volume `(2π)^N`. -/
theorem measureReal_pi_Ioo_univ (N : ℕ) :
    (Measure.pi fun _ : Fin N => volume.restrict (Ioo (-Real.pi) Real.pi)).real univ =
      (2 * Real.pi) ^ N := by
  rw [Measure.real, Measure.pi_univ]
  simp only [Measure.restrict_apply_univ, Real.volume_Ioo, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- `F_λ` is continuous for `λ > 0`. -/
theorem continuous_energy {N : ℕ} {lam : ℝ} (hlam : 0 < lam) :
    Continuous (energy (N := N) lam) := by
  have hk := continuous_smearedKernel hlam
  have h : energy (N := N) lam = fun Z => (1 / 2) * ∑ a, ∑ b, charge a * charge b *
      smearedKernel lam (Z b - Z a) - N * (logKernel lam + kappa) :=
    funext (energy_eq_sum_smearedKernel lam)
  rw [h]
  fun_prop

/-- The configuration with positive charges at `X i` and negative charges at
`X i + s i e^{iθ_i}` depends continuously on the angles. -/
theorem continuous_dipoleConfig {N : ℕ} (X : Fin N → ℂ) (s : Fin N → ℝ) :
    Continuous fun θ : Fin N → ℝ =>
      (Sum.elim X fun i => X i + circleMap 0 (s i) (θ i) : Fin N ⊕ Fin N → ℂ) := by
  refine continuous_pi fun a => ?_
  rcases a with i | i
  · exact continuous_const
  · simp only [Sum.elim_inr]
    exact continuous_const.add ((continuous_circleMap 0 (s i)).comp (continuous_apply i))

/-- **The averaged energy** (Prop. 4.1, Step 1, ruling R12a). If the discs of radii `s_i + λ`
about the `x_i` are separated, `s_i + s_j + 2λ ≤ |x_i - x_j|`, then the energy of the dipole
configuration `(x_i, x_i + s_i e^{iθ_i})`, integrated over the angles `θ ∈ (-π, π)^N`, equals
`-(2π)^N ∑ g_λ(s_i)`: the interactions between distinct dipoles average out exactly. -/
theorem averaged_energy_eq {N : ℕ} {lam : ℝ} (hlam : 0 < lam) (X : Fin N → ℂ) (s : Fin N → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hsep : ∀ i j, i ≠ j → s i + s j + 2 * lam ≤ ‖X i - X j‖) :
    ∫ θ in Set.univ.pi fun _ : Fin N => Ioo (-Real.pi) Real.pi,
        energy lam (Sum.elim X fun i => X i + circleMap 0 (s i) (θ i)) =
      (2 * Real.pi) ^ N * -∑ i, smearedKernel lam (s i : ℂ) := by
  classical
  have hk := continuous_smearedKernel hlam
  set H : Fin N → Fin N → (Fin N → ℝ) → ℝ := fun i j θ =>
    dipoleInteraction lam (X i) (X j) (X i + circleMap 0 (s i) (θ i))
      (X j + circleMap 0 (s j) (θ j)) with hH
  have hHc : ∀ i j, Continuous (H i j) := fun i j => by
    simp only [hH, dipoleInteraction]
    fun_prop
  have hrad : ∀ (i : Fin N) (θ : ℝ),
      smearedKernel lam (circleMap 0 (s i) θ) = smearedKernel lam (s i : ℂ) := fun i θ =>
    smearedKernel_eq_of_norm_eq lam (by
      rw [norm_circleMap_zero_of_nonneg (hs i), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hs i)])
  have hdec : ∀ θ : Fin N → ℝ,
      energy lam (Sum.elim X fun i => X i + circleMap 0 (s i) (θ i)) =
        -∑ i, smearedKernel lam (s i : ℂ) + (1 / 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, H i j θ := by
    intro θ
    rw [energy_sum_elim_eq hlam]
    simp only [add_sub_cancel_left, hrad]
    rfl
  have hzero : ∀ i j, i ≠ j → ∫ θ, H i j θ ∂(Measure.pi fun _ : Fin N =>
      volume.restrict (Ioo (-Real.pi) Real.pi)) = 0 := by
    intro i j hij
    refine integral_pi_eq_zero_of_integral_update_eq_zero _ j _
      (integrable_pi_Ioo_of_continuous (hHc i j)) fun θ => ?_
    simp only [hH, Function.update_self, Function.update_of_ne hij]
    exact integral_dipoleInteraction_eq_zero hlam (hs j) (si := s i)
      (by simp [norm_circleMap_zero_of_nonneg (hs i)]) (hsep i j hij)
  rw [setIntegral_pi_Ioo_eq]
  simp_rw [hdec]
  rw [integral_add (integrable_const _), integral_const, integral_const_mul, integral_finsetSum,
    measureReal_pi_Ioo_univ]
  · have : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∫ θ, ∑ j ∈ Finset.univ.erase i, H i j θ ∂(
        Measure.pi fun _ : Fin N => volume.restrict (Ioo (-Real.pi) Real.pi)) = 0 := by
      intro i _
      rw [integral_finsetSum]
      · exact Finset.sum_eq_zero fun j hj => hzero i j (Finset.ne_of_mem_erase hj).symm
      · exact fun j _ => integrable_pi_Ioo_of_continuous (hHc i j)
    rw [Finset.sum_eq_zero this]
    simp
  · exact fun i _ => integrable_finsetSum _ fun j _ => integrable_pi_Ioo_of_continuous (hHc i j)
  · exact (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_pi_Ioo_of_continuous (hHc i j)).const_mul _


end Average

end TwoComponentCoulomb

end
