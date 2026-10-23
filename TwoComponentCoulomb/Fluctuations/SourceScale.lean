/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.IsolatedRadial
public import TwoComponentCoulomb.Main.ErrorRateBounds

/-!
# The four scales in the conclusion of Theorem 2

Source `source/dipole-formation.tex`, proof of Theorem 2, Step 6.
The paper uses `θ` for the parameter called `γ` in these modules.
At `β = 4` its choice is `√λ ℓ^{1/4}`. The correction plus the square of this
scale is `O(ω_λ)`, the stronger comparison stated in the manuscript.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- The four-case choice of the paper, with its logarithmic factor at `β = 4`. -/
noncomputable def manuscriptGammaChoice (β lam : ℝ) : ℝ :=
  if β = 2 then |Real.log lam| ^ (-(1 / 2 : ℝ))
  else if β < 4 then lam ^ ((β - 2) / β)
  else if β = 4 then Real.sqrt lam * |Real.log lam| ^ (1 / 4 : ℝ)
  else Real.sqrt lam

/-- **The critical scale comparison**: `(2 + ½ log ℓ)/ℓ ≤ 3 ℓ^{-1/5}`. -/
theorem sourceScale_two {lam : ℝ} (h0 : 0 < lam) (h1 : lam < Real.exp (-4)) :
    isolatedPhi 2 le_rfl lam (manuscriptGammaChoice 2 lam) +
      manuscriptGammaChoice 2 lam ^ 2 ≤ 3 * errorRate 2 le_rfl lam := by
  have hL1 : 1 ≤ |Real.log lam| := (one_lt_abs_log h0
    (h1.trans (Real.exp_lt_exp.2 (by norm_num)))).le
  have hL0 : 0 < |Real.log lam| := by linarith
  let L := |Real.log lam|
  have hpow : 1 ≤ L ^ (4 / 5 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hlog := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 4 / 5)
  have hγ : manuscriptGammaChoice 2 lam = L ^ (-(1 / 2 : ℝ)) := by
    simp [manuscriptGammaChoice, L]
  have hγlog : |Real.log (L ^ (-(1 / 2 : ℝ)))| = (1 / 2) * Real.log L := by
    rw [Real.log_rpow hL0, abs_of_nonpos (by
      have := Real.log_nonneg hL1
      nlinarith)]
    ring
  have hγsq : (L ^ (-(1 / 2 : ℝ))) ^ 2 = L⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num [Real.rpow_neg_one, L]
  rw [hγ, isolatedPhi_of_eq_two le_rfl rfl, hγlog, hγsq,
    errorRate_of_eq_two le_rfl rfl]
  change (1 + (1 / 2) * Real.log L) / L + L⁻¹ ≤ 3 * L ^ (-(1 / 5 : ℝ))
  have hid : L ^ (4 / 5 : ℝ) / L = L ^ (-(1 / 5 : ℝ)) := by
    calc L ^ (4 / 5 : ℝ) / L = L ^ (4 / 5 : ℝ) / L ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = L ^ (-(1 / 5 : ℝ)) := by rw [← Real.rpow_sub hL0]; norm_num [L]
  rw [← hid]
  have he : (1 + (1 / 2) * Real.log L) / L + L⁻¹ =
      (2 + (1 / 2) * Real.log L) / L := by field_simp; ring
  rw [he, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by nlinarith only [hpow, hlog]) hL0.le

/-- **The subcritical scale comparison**, `2 < β < 4`: both terms equal
`λ^{2(β-2)/β}`, whose exponent exceeds the exponent defining `ω_λ`. -/
theorem sourceScale_lt_four {β lam : ℝ} (hβ : 2 < β) (h4 : β < 4)
    (h0 : 0 < lam) (h1 : lam ≤ 1) :
    isolatedPhi β hβ.le lam (manuscriptGammaChoice β lam) +
      manuscriptGammaChoice β lam ^ 2 ≤ 3 * errorRate β hβ.le lam := by
  have hβ0 : 0 < β := by linarith
  have hγ : manuscriptGammaChoice β lam = lam ^ ((β - 2) / β) := by
    simp [manuscriptGammaChoice, hβ.ne', h4]
  rw [hγ]
  have hφ : isolatedPhi β hβ.le lam (lam ^ ((β - 2) / β)) =
      lam ^ (2 * (β - 2) / β) := by
    simp only [isolatedPhi, hβ.ne', h4, ite_false, ite_true]
    have hdiv : lam / lam ^ ((β - 2) / β) = lam ^ (1 - (β - 2) / β) := by
      rw [Real.rpow_sub h0, Real.rpow_one]
    rw [hdiv, ← Real.rpow_mul h0.le]
    congr 1
    field_simp
    ring
  have hsq : (lam ^ ((β - 2) / β)) ^ 2 = lam ^ (2 * (β - 2) / β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]
    congr 1
    push_cast
    ring
  rw [hφ, hsq, errorRate_of_lt_four hβ.le hβ.ne' h4]
  have he : 2 * (β - 2) / (84 - β) ≤ 2 * (β - 2) / β := by
    apply div_le_div_of_nonneg_left (by linarith) hβ0
    linarith
  have hp := Real.rpow_le_rpow_of_exponent_ge h0 h1 he
  linarith [Real.rpow_nonneg h0.le (2 * (β - 2) / (84 - β))]

/-- The square of the manuscript's scale at `β = 4`. -/
theorem sourceScale_four_sq {lam : ℝ} (h0 : 0 < lam) :
    manuscriptGammaChoice 4 lam ^ 2 = lam * Real.sqrt |Real.log lam| := by
  simp only [manuscriptGammaChoice, show (4 : ℝ) ≠ 2 by norm_num,
    lt_self_iff_false, ite_false, ite_true, mul_pow, Real.sq_sqrt h0.le]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), Real.sqrt_eq_rpow]
  congr 2
  norm_num

/-- **The scale comparison at `β = 4`**, including the factor `ℓ^{1/4}`.
The correction and `θ²` are bounded by `3λℓ ≤ 3ω_λ`. -/
theorem sourceScale_four {lam : ℝ} (h0 : 0 < lam) (h1 : lam < Real.exp (-4)) :
    isolatedPhi 4 (by norm_num) lam (manuscriptGammaChoice 4 lam) +
      manuscriptGammaChoice 4 lam ^ 2 ≤ 3 * errorRate 4 (by norm_num) lam := by
  have hlam1 : lam < 1 := h1.trans (Real.exp_lt_one_iff.2 (by norm_num))
  let L := |Real.log lam|
  have hL1 : 1 ≤ L := (one_lt_abs_log h0
    (h1.trans (Real.exp_lt_exp.2 (by norm_num)))).le
  have hL0 : 0 < L := by linarith
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.2 h0
  have hq : 0 < L ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hγ : manuscriptGammaChoice 4 lam = Real.sqrt lam * L ^ (1 / 4 : ℝ) := by
    norm_num [manuscriptGammaChoice, L]
  have hlog : Real.log (manuscriptGammaChoice 4 lam / lam) = L / 2 + Real.log L / 4 := by
    rw [hγ, Real.log_div (mul_pos hs hq).ne' h0.ne', Real.log_mul hs.ne' hq.ne',
      Real.log_sqrt h0.le, Real.log_rpow hL0]
    have hab : L = -Real.log lam := abs_of_neg (Real.log_neg h0 hlam1)
    rw [hab]
    ring
  have hγsq := sourceScale_four_sq h0
  have hroot0 : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hroot1 : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL1
  have hrootL : Real.sqrt L ≤ L := by
    rw [Real.sqrt_le_left hL0.le]
    nlinarith only [hL1]
  have hratio : (lam / manuscriptGammaChoice 4 lam) ^ 2 = lam / Real.sqrt L := by
    rw [div_pow, hγsq, ← div_div, sq, mul_div_cancel_left₀ lam h0.ne']
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hnum : 1 + (L / 2 + Real.log L / 4) ≤ 2 * L := by linarith
  have hφ : isolatedPhi 4 (by norm_num) lam (manuscriptGammaChoice 4 lam) ≤
      2 * lam * Real.sqrt L := by
    simp only [isolatedPhi, show (4 : ℝ) ≠ 2 by norm_num,
      lt_self_iff_false, ite_false, ite_true]
    rw [hratio, hlog]
    calc _ ≤ lam / Real.sqrt L * (2 * L) := by gcongr
      _ = 2 * lam * Real.sqrt L := by
        have hsL := Real.sq_sqrt hL0.le
        field_simp
        nlinarith only [hsL]
  rw [hγsq, errorRate_of_eq_four (by norm_num) rfl]
  have hp : lam * L ≤ (lam * L) ^ (1 / 21 : ℝ) :=
    Real.self_le_rpow_of_le_one (by positivity) (mul_abs_log_lt_one h0 hlam1).le (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hrootL h0.le
  change _ ≤ 3 * (lam * L) ^ (1 / 21 : ℝ)
  linarith

/-- **The four-case `O(ω_λ)` claim in Step 6** of the paper.
The constant is uniform in `λ`, and the estimate uses the rate ω_λ. -/
theorem manuscriptGammaChoice_rate (β : ℝ) (hβ : 2 ≤ β) {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam < Real.exp (-4)) :
    isolatedPhi β hβ lam (manuscriptGammaChoice β lam) + manuscriptGammaChoice β lam ^ 2 ≤
      3 * errorRate β hβ lam := by
  by_cases h2 : β = 2
  · subst h2
    exact sourceScale_two h0 h1
  by_cases h4 : β < 4
  · exact sourceScale_lt_four (lt_of_le_of_ne hβ (Ne.symm h2)) h4 h0
      (h1.trans (Real.exp_lt_one_iff.2 (by norm_num))).le
  by_cases hfour : β = 4
  · subst hfour
    exact sourceScale_four h0 h1
  have hγ : manuscriptGammaChoice β lam = Real.sqrt lam := by
    simp [manuscriptGammaChoice, h2, h4, hfour]
  simp only [isolatedPhi, h2, h4, hfour, ite_false]
  rw [hγ, div_pow, Real.sq_sqrt h0.le,
    sq, mul_div_cancel_left₀ lam h0.ne', errorRate_of_four_lt hβ (lt_of_le_of_ne (not_lt.1 h4) (Ne.symm hfour))]
  have hp : lam ≤ lam ^ (1 / 20 : ℝ) := Real.self_le_rpow_of_le_one h0.le
    (h1.trans (Real.exp_lt_one_iff.2 (by norm_num))).le (by norm_num)
  linarith [Real.rpow_nonneg h0.le (1 / 20 : ℝ)]

/-- The manuscript's four scales satisfy the required range `2λ ≤ θ ≤ 1`. -/
theorem manuscriptGammaChoice_bounds (β : ℝ) (hβ : 2 ≤ β) {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam < Real.exp (-4)) :
    2 * lam ≤ manuscriptGammaChoice β lam ∧ manuscriptGammaChoice β lam ≤ 1 := by
  by_cases h2 : β = 2
  · have hlam1 : lam < 1 := h1.trans (Real.exp_lt_one_iff.2 (by norm_num))
    have hL4 : 4 < |Real.log lam| := by
      have : Real.log lam < -4 := by
        rw [Real.log_lt_iff_lt_exp h0]
        exact h1
      rw [abs_of_neg (by linarith)]
      linarith
    have hlamL := mul_abs_log_lt_one h0 hlam1
    have hγ : manuscriptGammaChoice β lam = (Real.sqrt |Real.log lam|)⁻¹ := by
      simp only [manuscriptGammaChoice, h2, ite_true]
      rw [Real.rpow_neg (abs_nonneg _), Real.sqrt_eq_rpow]
    rw [hγ]
    generalize hLdef : |Real.log lam| = L at hL4 hlamL ⊢
    have hL0 : 0 < L := by linarith
    set t := Real.sqrt L with ht
    have ht2 : t ^ 2 = L := Real.sq_sqrt hL0.le
    have ht0 : 0 < t := Real.sqrt_pos.2 hL0
    have ht2' : 2 ≤ t := by
      rw [ht]
      exact Real.le_sqrt_of_sq_le (by linarith)
    refine ⟨?_, inv_le_one_of_one_le₀ (by linarith)⟩
    -- `2 λ ≤ 1/t`
    rw [← one_div, le_div_iff₀ ht0]
    have hlt2 : lam * t ^ 2 < 1 := by rw [ht2]; exact hlamL
    have hm := mul_le_mul_of_nonneg_left ht2' (mul_nonneg h0.le ht0.le)
    linarith only [hm, hlt2]
  have hlam4 : lam ≤ 1 / 4 := by
    have hexp : Real.exp (-4) ≤ 1 / 4 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num)
        (by linarith only [Real.add_one_le_exp (4 : ℝ)])
    exact (h1.trans_le hexp).le
  by_cases h4 : β < 4
  · have hβ2 : 2 < β := lt_of_le_of_ne hβ (Ne.symm h2)
    have hlam1 : lam ≤ 1 := by linarith only [hlam4]
    have hγ : manuscriptGammaChoice β lam = lam ^ ((β - 2) / β) := by
      simp only [manuscriptGammaChoice, hβ2.ne', h4, ite_false, ite_true]
    have hβ0 : 0 < β := by linarith
    set e : ℝ := (β - 2) / β with he
    have he0 : 0 ≤ e := div_nonneg (by linarith) hβ0.le
    have he1 : 2 / β + e = 1 := by rw [he]; field_simp; ring
    have hsplit : lam = lam ^ (2 / β) * lam ^ e := by
      rw [← Real.rpow_add h0, he1, Real.rpow_one]
    rw [hγ]
    refine ⟨?_, Real.rpow_le_one h0.le hlam1 he0⟩
    -- `2 λ ≤ λ^e`
    have hq : lam ^ (2 / β) ≤ 1 / 2 := by
      calc lam ^ (2 / β) ≤ (1 / 4 : ℝ) ^ (2 / β) :=
            Real.rpow_le_rpow h0.le hlam4 (by positivity)
        _ ≤ (1 / 4 : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by
              rw [div_le_div_iff₀ (by norm_num) hβ0]
              linarith)
        _ = 1 / 2 := by
            rw [← Real.sqrt_eq_rpow, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
    have hpos : 0 ≤ lam ^ e := Real.rpow_nonneg h0.le _
    calc 2 * lam = 2 * (lam ^ (2 / β) * lam ^ e) := by rw [← hsplit]
      _ ≤ 2 * ((1 / 2) * lam ^ e) := by gcongr
      _ = lam ^ e := by ring
  have hs0 : 0 < Real.sqrt lam := Real.sqrt_pos.2 h0
  have hs2 : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt h0.le
  have hs1 : Real.sqrt lam ≤ 1 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith only [hlam4]
  have hlower : 2 * lam ≤ Real.sqrt lam := by
    have hm := mul_le_mul_of_nonneg_left
      (show 2 * Real.sqrt lam ≤ 1 by linarith only [hs1]) hs0.le
    linarith only [hm, hs2]
  by_cases hfour : β = 4
  · subst hfour
    have hL1 : 1 ≤ |Real.log lam| := (one_lt_abs_log h0
      (h1.trans (Real.exp_lt_exp.2 (by norm_num)))).le
    have hq : 1 ≤ |Real.log lam| ^ (1 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hγ : manuscriptGammaChoice 4 lam = Real.sqrt lam * |Real.log lam| ^ (1 / 4 : ℝ) := by
      norm_num [manuscriptGammaChoice]
    have hroot : Real.sqrt |Real.log lam| ≤ |Real.log lam| := by
      rw [Real.sqrt_le_left (abs_nonneg _)]
      nlinarith only [hL1]
    have hγ0 : 0 ≤ manuscriptGammaChoice 4 lam := by rw [hγ]; positivity
    have hsq : manuscriptGammaChoice 4 lam ^ 2 < 1 := by
      rw [sourceScale_four_sq h0]
      exact (mul_le_mul_of_nonneg_left hroot h0.le).trans_lt
        (mul_abs_log_lt_one h0 (h1.trans (Real.exp_lt_one_iff.2 (by norm_num))))
    constructor
    · rw [hγ]
      exact hlower.trans (le_mul_of_one_le_right (Real.sqrt_nonneg _) hq)
    · nlinarith only [hsq, hγ0]
  · simp only [manuscriptGammaChoice, h2, h4, hfour, ite_false]
    exact ⟨hlower, by linarith only [hs1]⟩

/-- **The complete scale regime stated in Step 6** of the paper. -/
theorem manuscriptGammaChoice_regime (β : ℝ) (hβ : 2 ≤ β) {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam < Real.exp (-4)) :
    2 * lam ≤ manuscriptGammaChoice β lam ∧ manuscriptGammaChoice β lam ≤ 1 ∧
      isolatedPhi β hβ lam (manuscriptGammaChoice β lam) + manuscriptGammaChoice β lam ^ 2 ≤
        3 * errorRate β hβ lam :=
  ⟨(manuscriptGammaChoice_bounds β hβ h0 h1).1,
    (manuscriptGammaChoice_bounds β hβ h0 h1).2, manuscriptGammaChoice_rate β hβ h0 h1⟩

end TwoComponentCoulomb

end
