/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Potential.Electric
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Decay of the electric potential and field of a neutral configuration

For a *neutral* configuration (`Σᵢ dᵢ = 0`) of disc charges the electric potential and field decay
like a dipole at infinity :

* `exists_decay_electric_nonneg` : there are `R₀, C ≥ 0` with `|h_α(x)| ≤ C / |x|` and
  `|∇h_α(x)| ≤ C / |x|²` for `|x| ≥ R₀`. Outside all discs `h_α(x) = -Σᵢ dᵢ log |x - zᵢ|` and
  `∇h_α(x) = -Σᵢ dᵢ (x - zᵢ) / |x - zᵢ|²`; neutrality allows to subtract the monopole terms
  `-log |x|` and `-x / |x|²`.
* `integrable_norm_sq_electricField` : hence the Dirichlet energy `∫ |∇h_α|²` is finite.
* `integrable_of_decay` : an integrability criterion for continuous functions decaying like
  `|x|⁻⁴` on `ℂ = ℝ²`.
-/

@[expose] public section

open MeasureTheory Metric

namespace TwoComponentCoulomb

/-! ### The disc potential and field outside the disc -/

/-- Outside the disc, the potential `g * δ_0^{(a)}` is the potential `g` of the centre. -/
theorem discPotential_of_le {a : ℝ} (ha : 0 < a) {u : ℂ} (h : a ≤ ‖u‖) :
    discPotential a u = -Real.log ‖u‖ := by
  unfold discPotential
  rw [max_eq_right h, min_eq_right h, div_self (by positivity)]
  simp

/-- Outside the disc, the field of the disc is the field `-u / |u|²` of its centre. -/
theorem discField_of_le {a : ℝ} {u : ℂ} (h : a ≤ ‖u‖) :
    discField a u = -((‖u‖ ^ 2)⁻¹ : ℝ) • u := by
  unfold discField
  rw [max_eq_right h]

/-- The potential of a disc outside it differs from the monopole potential `-log |x|` by at most
`2 |z| / |x|` for `|z| ≤ |x| / 2`. -/
theorem abs_discPotential_add_log_le {a : ℝ} (ha : 0 < a) {x z : ℂ} (hz : 2 * ‖z‖ ≤ ‖x‖)
    (hx : 0 < ‖x‖) (h : a ≤ ‖x - z‖) :
    |discPotential a (x - z) + Real.log ‖x‖| ≤ 2 * ‖z‖ / ‖x‖ := by
  rw [discPotential_of_le ha h]
  have hzx : |‖x - z‖ - ‖x‖| ≤ ‖z‖ := by
    have := abs_norm_sub_norm_le (x - z) x
    simpa using this
  have hs : ‖x‖ ≤ 2 * ‖x - z‖ := by
    have := norm_sub_norm_le x z
    linarith
  have hspos : 0 < ‖x - z‖ := by linarith
  have h1 : Real.log (‖x‖ / ‖x - z‖) ≤ ‖x‖ / ‖x - z‖ - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hx hspos)
  have h2 : Real.log (‖x - z‖ / ‖x‖) ≤ ‖x - z‖ / ‖x‖ - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hspos hx)
  rw [Real.log_div hx.ne' hspos.ne'] at h1
  rw [Real.log_div hspos.ne' hx.ne'] at h2
  have h3 : ‖x‖ / ‖x - z‖ - 1 ≤ 2 * ‖z‖ / ‖x‖ := by
    rw [div_sub_one hspos.ne', div_le_div_iff₀ hspos hx]
    have := (abs_le.1 hzx).1
    nlinarith [norm_nonneg z]
  have h4 : ‖x - z‖ / ‖x‖ - 1 ≤ 2 * ‖z‖ / ‖x‖ := by
    rw [div_sub_one hx.ne', div_le_div_iff_of_pos_right hx]
    have := (abs_le.1 hzx).2
    nlinarith [norm_nonneg z]
  rw [abs_le]
  constructor <;> linarith

/-- The field of a disc outside it differs from the monopole field `-x / |x|²` by at most
`2 |z| / |x|²` for `|z| ≤ |x| / 2`. -/
theorem norm_discField_sub_le {a : ℝ} {x z : ℂ} (hz : 2 * ‖z‖ ≤ ‖x‖) (hx : 0 < ‖x‖)
    (h : a ≤ ‖x - z‖) :
    ‖discField a (x - z) - (-((‖x‖ ^ 2)⁻¹ : ℝ) • x)‖ ≤ 2 * ‖z‖ / ‖x‖ ^ 2 := by
  have hs : ‖x‖ ≤ 2 * ‖x - z‖ := by
    have := norm_sub_norm_le x z
    linarith
  have hspos : 0 < ‖x - z‖ := by linarith
  have hx0 : x ≠ 0 := norm_pos_iff.1 hx
  have hxz : x - z ≠ 0 := norm_pos_iff.1 hspos
  rw [discField_of_le h, gradLogKernel_eq_neg_conj_inv, gradLogKernel_eq_neg_conj_inv]
  have e : -(starRingEnd ℂ) (x - z)⁻¹ - -(starRingEnd ℂ) x⁻¹ =
      (starRingEnd ℂ) (x⁻¹ - (x - z)⁻¹) := by
    rw [map_sub]
    ring
  rw [e, RCLike.norm_conj, inv_sub_inv hx0 hxz, norm_div, norm_mul, sub_sub_cancel_left, norm_neg,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ ‖z‖ := norm_nonneg z
  nlinarith [mul_nonneg this (norm_nonneg x)]

/-! ### Decay of the potential and the field -/

section Decay

variable {ι : Type*} [Fintype ι] {d : ι → ℝ} {z : ι → ℂ} {α : ι → ℝ}

/-- **Decay of a neutral configuration**, with a nonnegative constant: for `|x|` large the
potential is `O(1/|x|)` and the field is `O(1/|x|²)`. -/
theorem exists_decay_electric_nonneg (hα : ∀ i, 0 < α i) (hn : ∑ i, d i = 0) :
    ∃ R₀ C : ℝ, 0 < R₀ ∧ 0 ≤ C ∧ ∀ x : ℂ, R₀ ≤ ‖x‖ →
      |electricPotential d z α x| ≤ C / ‖x‖ ∧ ‖electricField d z α x‖ ≤ C / ‖x‖ ^ 2 := by
  set S : ℝ := ∑ j, (‖z j‖ + α j) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => add_nonneg (norm_nonneg _) (hα j).le
  have hSi : ∀ i, ‖z i‖ + α i ≤ S := fun i =>
    Finset.single_le_sum (f := fun j => ‖z j‖ + α j)
      (fun j _ => add_nonneg (norm_nonneg _) (hα j).le) (Finset.mem_univ i)
  refine ⟨2 * S + 1, ∑ i, |d i| * (2 * ‖z i‖), by linarith,
    Finset.sum_nonneg fun i _ => by positivity, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := by linarith
  have hzx : ∀ i, 2 * ‖z i‖ ≤ ‖x‖ := fun i => by
    have := hSi i
    have := hα i
    linarith
  have hax : ∀ i, α i ≤ ‖x - z i‖ := fun i => by
    have := hSi i
    have := norm_sub_norm_le x (z i)
    have := hzx i
    linarith
  constructor
  · have e : electricPotential d z α x =
        ∑ i, d i * (discPotential (α i) (x - z i) + Real.log ‖x‖) := by
      have : ∑ i, d i * Real.log ‖x‖ = 0 := by rw [← Finset.sum_mul, hn, zero_mul]
      simp only [mul_add, Finset.sum_add_distrib, this, add_zero]
      rfl
    rw [e, Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (abs_discPotential_add_log_le (hα i) (hzx i) hxpos (hax i))
      (abs_nonneg _)
  · have e : electricField d z α x =
        ∑ i, d i • (discField (α i) (x - z i) - (-((‖x‖ ^ 2)⁻¹ : ℝ) • x)) := by
      have : ∑ i, d i • (-((‖x‖ ^ 2)⁻¹ : ℝ) • x) = 0 := by rw [← Finset.sum_smul, hn, zero_smul]
      simp only [smul_sub, Finset.sum_sub_distrib, this, sub_zero]
      rfl
    rw [e, Finset.sum_div]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (norm_discField_sub_le (hzx i) hxpos (hax i)) (abs_nonneg _)

end Decay

/-! ### Integrability -/

/-- A continuous function on `ℂ = ℝ²` with `|f(x)| ≤ C / |x|⁴` for `|x| ≥ R₀` is integrable. -/
theorem integrable_of_decay {f : ℂ → ℝ} (hf : Continuous f) {R₀ C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : ℂ, R₀ ≤ ‖x‖ → |f x| ≤ C / ‖x‖ ^ 4) : Integrable f := by
  set R : ℝ := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hbd : Integrable (fun x : ℂ => (16 * C) * (1 + ‖x‖) ^ (-(4 : ℝ))) := by
    refine Integrable.const_mul (integrable_one_add_norm ?_) _
    simp [Complex.finrank_real_complex]
    norm_num
  rw [← integrableOn_univ, ← Set.union_compl_self (closedBall (0 : ℂ) R)]
  refine IntegrableOn.union ?_ ?_
  · exact hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)
  · refine hbd.integrableOn.mono' hf.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_closedBall.compl).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hxR : R < ‖x‖ := by simpa using hx
    have hx1 : 1 < ‖x‖ := lt_of_le_of_lt hR1 hxR
    have hxR₀ : R₀ ≤ ‖x‖ := (le_max_left _ _).trans hxR.le
    have hxpos : 0 < ‖x‖ := by linarith
    rw [Real.norm_eq_abs]
    refine (h x hxR₀).trans ?_
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : (1 + ‖x‖) ^ 4 ≤ (2 * ‖x‖) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    nlinarith [mul_le_mul_of_nonneg_left h2 hC, pow_pos hxpos 4]

variable {ι : Type*} [Fintype ι] {d : ι → ℝ} {z : ι → ℂ} {α : ι → ℝ}

/-- **Finite Dirichlet energy**: for a neutral configuration `|∇h_α|²` is integrable. -/
theorem integrable_norm_sq_electricField (hα : ∀ i, 0 < α i) (hn : ∑ i, d i = 0) :
    Integrable fun x => ‖electricField d z α x‖ ^ 2 := by
  obtain ⟨R₀, C, hR₀, hC, hdec⟩ := exists_decay_electric_nonneg (d := d) (z := z) hα hn
  refine integrable_of_decay ((continuous_electricField hα).norm.pow 2) (R₀ := R₀) (C := C ^ 2)
    (sq_nonneg C) fun x hx => ?_
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := (hdec x hx).2
  calc ‖electricField d z α x‖ ^ 2 ≤ (C / ‖x‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = C ^ 2 / ‖x‖ ^ 4 := by rw [div_pow, ← pow_mul]

end TwoComponentCoulomb

end
