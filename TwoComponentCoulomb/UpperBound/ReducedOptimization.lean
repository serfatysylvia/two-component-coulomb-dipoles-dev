/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Convex.Deriv

/-!
# The entropy optimization by differentiation

Source: `source/dipole-formation.tex`, subsection 3.1, (eq:sup-inequality), l. 747–751.
On the positive half-line, `δ (A + B log (1/δ))` is concave. Its derivative vanishes at
`exp (A/B - 1)`, where its value is `B exp (A/B - 1)`.
-/

public section

open Set

namespace TwoComponentCoulomb

/-- The derivative appearing in the manuscript's elementary optimization. -/
theorem hasDerivAt_entropy {A B x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y * (A - B * Real.log y)) (A - B - B * Real.log x) x := by
  convert (hasDerivAt_id x).mul
    ((hasDerivAt_const x A).sub ((Real.hasDerivAt_log hx.ne').const_mul B)) using 1
  · rfl
  · simp only [id_eq, Pi.sub_apply]
    field_simp
    ring

/-- The entropy function is concave on the positive half-line since its derivative
is decreasing. -/
theorem concaveOn_entropy {A B : ℝ} (hB : 0 < B) :
    ConcaveOn ℝ (Ioi 0) (fun x : ℝ => x * (A - B * Real.log x)) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_entropy hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_entropy (show 0 < x from interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [(hasDerivAt_entropy (show 0 < x from interior_subset hx)).deriv,
      (hasDerivAt_entropy (show 0 < y from interior_subset hy)).deriv]
    have hlog := mul_le_mul_of_nonneg_left (Real.log_le_log (interior_subset hx) hxy) hB.le
    linarith only [hlog]

/-- The bound `eq:sup-inequality`, proved by concavity, the stationary point and its
value. It holds for all nonnegative `δ`, hence in particular for `0 < δ ≤ 1`. -/
theorem mul_add_mul_log_inv_le_calculus {A B δ : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ) :
    δ * (A + B * Real.log (1 / δ)) ≤ B * Real.exp (A / B - 1) := by
  rcases hδ.eq_or_lt with rfl | hδ
  · simp only [zero_mul]
    positivity
  let t := Real.exp (A / B - 1)
  have ht : 0 < t := Real.exp_pos _
  have hlogt : Real.log t = A / B - 1 := Real.log_exp _
  have hstat : HasDerivAt (fun x : ℝ => x * (A - B * Real.log x)) 0 t := by
    convert hasDerivAt_entropy (A := A) (B := B) ht using 1
    rw [hlogt]
    field_simp
    ring
  have hmax : δ * (A - B * Real.log δ) ≤ t * (A - B * Real.log t) := by
    rcases lt_trichotomy δ t with hlt | rfl | hlt
    · have h := (concaveOn_entropy (A := A) hB).le_slope_of_hasDerivAt hδ ht hlt hstat
      rw [slope_def_field] at h
      have := (le_div_iff₀ (sub_pos.2 hlt)).1 h
      linarith only [this]
    · exact le_rfl
    · have h := (concaveOn_entropy (A := A) hB).slope_le_of_hasDerivAt ht hδ hlt hstat
      rw [slope_def_field] at h
      have := (div_le_iff₀ (sub_pos.2 hlt)).1 h
      linarith only [this]
  rw [one_div, Real.log_inv]
  have hvalue : t * (A - B * Real.log t) = B * t := by
    rw [hlogt]
    field_simp
    ring
  simpa only [← sub_eq_add_neg, mul_neg, hvalue] using hmax

end TwoComponentCoulomb

end
