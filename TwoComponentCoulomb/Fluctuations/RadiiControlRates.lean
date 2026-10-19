/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.M0
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TwoComponentCoulomb.Main.Theorem1AssemblyBounds

/-!
# The radius `R₀` (Theorem 2, Step 5)

Source: proof of Theorem 2, Step 5 (l. 2182--2194): the radius is

`R₀ = ω_λ^{1/4}` (`β = 2`),  `R₀ = λ ω_λ^{-1/(2(β-2))} ∨ 2λ` (`β > 2`).

The source states "for `λ` small, `2λ ≤ R₀ ≤ ω_λ^{1/4}`", with `(λ/R₀)^{β-2} ≤ ω_λ^{1/2}` for
`β > 2`, and, at `β = 2`, `log (1/R₀) / |log λ| = o(ω_λ)`. This file proves these elementary
comparisons for a general rate function `ω` in place of `ω_λ`, from the rate properties `0 < ω`,
`ω ≤ λ^a`, `λ^{4(β-2)/β} ≤ ω` (`β > 2`) and the two `β = 2` comparisons; for
`ω_λ = errorRate β hβ λ` they are supplied by `theorem2RateHyp_errorRate`
(`Fluctuations/Theorem2RateInstance.lean`).

* `R0Rate`, `R0Rate_of_eq_two`, `R0Rate_of_two_lt` : the radius `R₀` for a rate `ω`.
* `exists_R0Rate_regime_of_two_lt`, `exists_R0Rate_regime` : for `λ` small,
  `2λ ≤ R₀ ≤ ω(λ)^{1/4}`, `(λ/R₀)^{β-2} = ω(λ)^{1/2}` (`β > 2`) and, at `β = 2`,
  `(1 + log |log λ| + log (1/R₀)) / |log λ| ≤ 5 ω(λ)`.
* `sq_le_sqrt_of_le_rpow_quarter`, `le_one_of_le_rpow_quarter` : `R ≤ ω^{1/4}` gives
  `R² ≤ √ω` and (for `ω ≤ 1`) `R ≤ 1`.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-! ### The radius `R₀` -/

/-- The radius `R₀` of Step 5 for a general rate function `ω` in place of `ω_λ`:
`ω(λ)^{1/4}` if `β = 2`, and `λ ω(λ)^{-1/(2(β-2))}` if `β > 2`. The source (l. 2184--2187)
writes `λ ω_λ^{-1/(2(β-2))} ∨ 2λ` for `β > 2`; the maximum with `2λ` is not needed, because
`2λ ≤ λ ω^{-1/(2(β-2))}` for `λ` small (`exists_R0Rate_regime_of_two_lt`). -/
noncomputable def R0Rate (β : ℝ) (ω : ℝ → ℝ) (lam : ℝ) : ℝ :=
  if β = 2 then ω lam ^ (1 / 4 : ℝ)
  else lam * ω lam ^ (-(1 / (2 * (β - 2))))

theorem R0Rate_of_eq_two {β : ℝ} (h : β = 2) (ω : ℝ → ℝ) (lam : ℝ) :
    R0Rate β ω lam = ω lam ^ (1 / 4 : ℝ) := by
  simp [R0Rate, h]

theorem R0Rate_of_two_lt {β : ℝ} (h : 2 < β) (ω : ℝ → ℝ) (lam : ℝ) :
    R0Rate β ω lam = lam * ω lam ^ (-(1 / (2 * (β - 2)))) := by
  simp [R0Rate, h.ne']

/-- The regime `R₀` at `β > 2` for small `λ`, for a general rate function `ω` with `0 < ω(λ)`,
`ω(λ) ≤ λ^a` (some `a > 0`) and `λ^{4(β-2)/β} ≤ ω(λ)` on `(0, e⁻¹)`:
`2λ ≤ R₀ ≤ ω(λ)^{1/4}` and `(λ/R₀)^{β-2} = √ω(λ)`. -/
theorem exists_R0Rate_regime_of_two_lt {β : ℝ} (h2 : 2 < β) {ω : ℝ → ℝ}
    (hpos : ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) → 0 < ω lam)
    (hle : ∃ a : ℝ, 0 < a ∧ ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) → ω lam ≤ lam ^ a)
    (hge : ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) → lam ^ (4 * (β - 2) / β) ≤ ω lam) :
    ∃ lamR : ℝ, 0 < lamR ∧ lamR ≤ Real.exp (-1) ∧ ∀ lam : ℝ, 0 < lam → lam < lamR →
      2 * lam ≤ R0Rate β ω lam ∧ R0Rate β ω lam ≤ ω lam ^ (1 / 4 : ℝ) ∧
        (lam / R0Rate β ω lam) ^ (β - 2) = Real.sqrt (ω lam) := by
  obtain ⟨a, ha, hωa⟩ := hle
  set ε : ℝ := (2 : ℝ) ^ (-(2 * (β - 2))) with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨min (Real.exp (-1)) (ε ^ a⁻¹), lt_min (Real.exp_pos _) (Real.rpow_pos_of_pos hε0 _),
    min_le_left _ _, fun lam h0 hlt => ?_⟩
  have h1 : lam < Real.exp (-1) := lt_of_lt_of_le hlt (min_le_left _ _)
  have h1' : lam < ε ^ a⁻¹ := lt_of_lt_of_le hlt (min_le_right _ _)
  have hω0 : 0 < ω lam := hpos lam h0 h1
  set w := ω lam with hw
  have hβ2 : 0 < β - 2 := by linarith
  set s : ℝ := 1 / (2 * (β - 2)) with hs
  have hs0 : 0 < s := by positivity
  -- `w ≤ ε`
  have hωε : w ≤ ε := by
    calc w ≤ lam ^ a := hωa lam h0 h1
      _ ≤ (ε ^ a⁻¹) ^ a := Real.rpow_le_rpow h0.le h1'.le ha.le
      _ = ε := Real.rpow_inv_rpow hε0.le ha.ne'
  -- `2 ≤ w^{-s}`
  have hs2 : (2 : ℝ) ≤ w ^ (-s) := by
    have h3 : ε ^ (-s) ≤ w ^ (-s) := Real.rpow_le_rpow_of_nonpos hω0 hωε (by linarith)
    have h4 : ε ^ (-s) = 2 := by
      rw [hε, ← Real.rpow_mul (by norm_num)]
      have : -(2 * (β - 2)) * -s = 1 := by
        rw [hs]
        field_simp
      rw [this, Real.rpow_one]
    linarith
  have hR : R0Rate β ω lam = lam * w ^ (-s) := R0Rate_of_two_lt h2 ω lam
  refine ⟨?_, ?_, ?_⟩
  · rw [hR]
    nlinarith
  · -- `R₀ ≤ w^{1/4}`
    rw [hR]
    set t : ℝ := 1 / 4 + s with ht
    have ht0 : 0 < t := by positivity
    have htθ : (4 * (β - 2) / β) * t = 1 := by
      rw [ht, hs]
      field_simp
      ring
    have h5 : lam ≤ w ^ t := by
      have h6 : lam ^ (4 * (β - 2) / β) ≤ w := hge lam h0 h1
      calc lam = (lam ^ (4 * (β - 2) / β)) ^ t := by
            rw [← Real.rpow_mul h0.le, htθ, Real.rpow_one]
        _ ≤ w ^ t := Real.rpow_le_rpow (Real.rpow_nonneg h0.le _) h6 ht0.le
    have h7 : w ^ (1 / 4 : ℝ) = w ^ t * w ^ (-s) := by
      rw [← Real.rpow_add hω0, ht]
      congr 1
      ring
    rw [h7]
    exact mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hω0.le _)
  · -- `(λ/R₀)^{β-2} = √w`
    rw [hR]
    have h8 : lam / (lam * w ^ (-s)) = w ^ s := by
      rw [Real.rpow_neg hω0.le]
      field_simp
    rw [h8, ← Real.rpow_mul hω0.le, Real.sqrt_eq_rpow]
    congr 1
    rw [hs]
    field_simp

/-- **The range of `R₀` for a general rate function `ω`** (source l. 2191--2194): for `λ` small,
`2λ ≤ R₀ ≤ ω(λ)^{1/4}`; for `β > 2`, `(λ/R₀)^{β-2} = √ω(λ)`; for `β = 2`,
`(1 + log |log λ| + log (1/R₀)) / |log λ| ≤ 5 ω(λ)`. The hypotheses are elementary
properties of the rate `ω` on `(0, e⁻¹)` (resp. `(0, e⁻⁴)` for the `β = 2` comparisons). -/
theorem exists_R0Rate_regime {β : ℝ} (hβ : 2 ≤ β) {ω : ℝ → ℝ}
    (hpos : ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) → 0 < ω lam)
    (hle : 2 < β → ∃ a : ℝ, 0 < a ∧ ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) → ω lam ≤ lam ^ a)
    (hge : 2 < β → ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) → lam ^ (4 * (β - 2) / β) ≤ ω lam)
    (htwo : β = 2 → ∀ lam : ℝ, 0 < lam → lam < Real.exp (-4) → 2 * lam ≤ ω lam ^ (1 / 4 : ℝ))
    (hlog : β = 2 → ∀ lam : ℝ, 0 < lam → lam < Real.exp (-4) →
      (1 + Real.log |Real.log lam| + Real.log (1 / ω lam ^ (1 / 4 : ℝ))) / |Real.log lam|
        ≤ 5 * ω lam) :
    ∃ lamR : ℝ, 0 < lamR ∧ lamR ≤ Real.exp (-1) ∧ ∀ lam : ℝ, 0 < lam → lam < lamR →
      2 * lam ≤ R0Rate β ω lam ∧ R0Rate β ω lam ≤ ω lam ^ (1 / 4 : ℝ) ∧
      (2 < β → (lam / R0Rate β ω lam) ^ (β - 2) = Real.sqrt (ω lam)) ∧
      (β = 2 → (1 + Real.log |Real.log lam| + Real.log (1 / R0Rate β ω lam)) / |Real.log lam|
        ≤ 5 * ω lam) := by
  by_cases h : β = 2
  · refine ⟨Real.exp (-4), Real.exp_pos _, Real.exp_le_exp.2 (by norm_num),
      fun lam h0 h1 => ?_⟩
    rw [R0Rate_of_eq_two h ω lam]
    exact ⟨htwo h lam h0 h1, le_rfl, fun h2 => absurd h (by linarith), fun _ => hlog h lam h0 h1⟩
  · have h2 : 2 < β := lt_of_le_of_ne hβ (Ne.symm h)
    obtain ⟨lamR, hlamR, hle', hreg⟩ := exists_R0Rate_regime_of_two_lt h2 hpos (hle h2) (hge h2)
    refine ⟨lamR, hlamR, hle', fun lam h0 h1 => ?_⟩
    obtain ⟨ha, hb, hc⟩ := hreg lam h0 h1
    exact ⟨ha, hb, fun _ => hc, fun h' => absurd h' h⟩

/-- `R ≤ ω^{1/4}` gives `R² ≤ √ω`. -/
theorem sq_le_sqrt_of_le_rpow_quarter {R ω : ℝ} (hR : 0 ≤ R) (hω : 0 ≤ ω)
    (h : R ≤ ω ^ (1 / 4 : ℝ)) : R ^ 2 ≤ Real.sqrt ω := by
  calc R ^ 2 ≤ (ω ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hR h 2
    _ = Real.sqrt ω := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hω, Real.sqrt_eq_rpow]
        norm_num

/-- `R ≤ ω^{1/4}` with `ω ≤ 1` gives `R ≤ 1`. -/
theorem le_one_of_le_rpow_quarter {R ω : ℝ} (hω : 0 ≤ ω) (hω1 : ω ≤ 1)
    (h : R ≤ ω ^ (1 / 4 : ℝ)) : R ≤ 1 :=
  h.trans (Real.rpow_le_one hω hω1 (by norm_num))

end TwoComponentCoulomb

end
