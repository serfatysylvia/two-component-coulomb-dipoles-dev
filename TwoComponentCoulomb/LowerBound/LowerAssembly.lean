/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.PartitionFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Integrals.Stirling
import TwoComponentCoulomb.LowerBound.LowerJensen
import TwoComponentCoulomb.LowerBound.RadiusTail

/-!
# Assembly of Proposition 4.1 for `β > 2`

Source: Proposition 4.1, end of the proof (l. 1793–1803): the
bound `Z ≥ N! N^N (𝒵_β λ^{2-β})^N exp(-C N ε_λ - C √N η_λ)` of `partitionFunction_ge_of_two_lt`
is turned, by Stirling's formula and the arithmetic--geometric mean inequality
`C √N η ≤ C N ε + C η² / (4 ε)` together with `η_λ² / ε_λ → 0`, into the frozen form of the
proposition.

* the definition of ε_λ : `ε_λ` is, literally, the error term of the frozen statement for `β > 2`.
* the small-λ comparison : for every `K > 0` and small `λ`, `K η_λ² ≤ ε_λ`
  (that is, `η_λ² / ε_λ → 0`, in each range of `β`).
* `proposition_4_1_of_two_lt` : the frozen expression of Proposition 4.1 for `β > 2`.

The definitions `lowerEps` and `lowerEta` (exposed in `LowerBound/RadiusTail.lean`) are unfolded
here; the lemmas that mention them are `private`.
-/

public section

open Filter Topology

namespace TwoComponentCoulomb

/-- A property that holds eventually as `λ → 0⁺` holds on some interval `(0, λ₁)`. -/
private theorem exists_pos_forall_lt_of_eventually_nhdsGT {P : ℝ → Prop}
    (h : ∀ᶠ lam in 𝓝[>] (0 : ℝ), P lam) :
    ∃ lam₁ : ℝ, 0 < lam₁ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₁ → P lam := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨u, hu, fun lam h0 h1 => hsub ⟨h0, h1⟩⟩

/-- The quantity `ε_λ` is the error term of the frozen statement of Proposition 4.1 for `β > 2`. -/
private theorem lowerEps_eq_ite (β : ℝ) (hβ : 2 < β) (lam : ℝ) :
    lowerEps β hβ lam =
      if β < 4 then lam ^ (β - 2)
      else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
      else lam ^ 2 * |Real.log lam| := rfl

private theorem mul_sq_le_of_mul_le_one {K x : ℝ} (hx : 0 ≤ x) (h : K * x ≤ 1) :
    K * x ^ 2 ≤ x := by
  calc K * x ^ 2 = (K * x) * x := by ring
    _ ≤ 1 * x := mul_le_mul_of_nonneg_right h hx
    _ = x := one_mul x

/-- `λ^s → 0` as `λ → 0⁺` for `s > 0`. -/
private theorem tendsto_rpow_nhdsGT_zero_zero {s : ℝ} (hs : 0 < s) :
    Tendsto (fun lam : ℝ => lam ^ s) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 s (Or.inr hs.le)).tendsto
  rw [Real.zero_rpow hs.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- For `K > 0` and `λ` small enough, `K η_λ² ≤ ε_λ`: the ratio `η_λ² / ε_λ` tends to `0`
(`λ^{β-2}` for `β < 3`, `λ |log λ|²` for `β = 3`, `λ^{4-β}` for `3 < β < 4`, `|log λ|^{-2}` for
`β = 4`, `|log λ|^{-1}` for `β > 4`). -/
private theorem exists_mul_lowerEta_sq_le_lowerEps (β : ℝ) (hβ : 2 < β) {K : ℝ} (hK : 0 < K) :
    ∃ lam₁ : ℝ, 0 < lam₁ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₁ →
      K * lowerEta β hβ lam ^ 2 ≤ lowerEps β hβ lam := by
  refine exists_pos_forall_lt_of_eventually_nhdsGT ?_
  have hpos : ∀ᶠ lam : ℝ in 𝓝[>] 0, 0 < lam := eventually_mem_nhdsWithin
  have hlog : ∀ᶠ lam : ℝ in 𝓝[>] 0, K + 1 ≤ |Real.log lam| := by
    filter_upwards [tendsto_atBot.1 Real.tendsto_log_nhdsGT_zero (-(K + 1))] with lam h
    have := neg_le_abs (Real.log lam)
    linarith
  by_cases h3 : β < 3
  · have h4 : β < 4 := by linarith only [h3]
    have ht : Tendsto (fun lam : ℝ => K * lam ^ (β - 2)) (𝓝[>] 0) (𝓝 (K * 0)) :=
      (tendsto_rpow_nhdsGT_zero_zero (by linarith only [hβ])).const_mul K
    rw [mul_zero] at ht
    filter_upwards [hpos, (tendsto_order.1 ht).2 1 one_pos] with lam h0 h1
    simp only [lowerEta, lowerEps, h3, h4, ite_true]
    exact mul_sq_le_of_mul_le_one (Real.rpow_nonneg h0.le _) h1.le
  by_cases h3e : β = 3
  · subst h3e
    have hsq : Tendsto (fun lam : ℝ => Real.log lam * lam ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_log_mul_rpow_nhdsGT_zero (by norm_num)
    have ht : Tendsto (fun lam : ℝ => K * (Real.log lam * lam ^ (1 / 2 : ℝ)) ^ 2) (𝓝[>] 0)
        (𝓝 (K * 0 ^ 2)) := (hsq.pow 2).const_mul K
    rw [zero_pow two_ne_zero, mul_zero] at ht
    filter_upwards [hpos, (tendsto_order.1 ht).2 1 one_pos] with lam h0 h1
    have hs : (lam ^ (1 / 2 : ℝ)) ^ 2 = lam := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt h0.le
    have e : K * (lam * |Real.log lam| ^ 2) = K * (Real.log lam * lam ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [mul_pow, hs, sq_abs]
      ring
    have h1' : K * (lam * |Real.log lam| ^ 2) ≤ 1 := by rw [e]; exact h1.le
    have h34 : lowerEps 3 hβ lam = lam := by
      rw [lowerEps_eq_ite]
      norm_num
    have h3η : lowerEta 3 hβ lam = lam * |Real.log lam| := by
      norm_num [lowerEta]
    rw [h34, h3η]
    calc K * (lam * |Real.log lam|) ^ 2 = (K * (lam * |Real.log lam| ^ 2)) * lam := by ring
      _ ≤ 1 * lam := mul_le_mul_of_nonneg_right h1' h0.le
      _ = lam := one_mul lam
  have h3' : 3 < β := lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h3e)
  have hη : ∀ lam : ℝ, lowerEta β hβ lam = lam := by
    intro lam
    simp [lowerEta, h3, h3e]
  by_cases h4 : β < 4
  · have ht : Tendsto (fun lam : ℝ => K * lam ^ (4 - β)) (𝓝[>] 0) (𝓝 (K * 0)) :=
      (tendsto_rpow_nhdsGT_zero_zero (by linarith only [h4])).const_mul K
    rw [mul_zero] at ht
    filter_upwards [hpos, (tendsto_order.1 ht).2 1 one_pos] with lam h0 h1
    have e : lam ^ 2 = lam ^ (4 - β) * lam ^ (β - 2) := by
      rw [← Real.rpow_add h0, show (4 - β) + (β - 2) = (2 : ℝ) by ring, Real.rpow_two]
    rw [hη, lowerEps_eq_ite]
    simp only [h4, ↓reduceIte]
    rw [e]
    calc K * (lam ^ (4 - β) * lam ^ (β - 2)) = (K * lam ^ (4 - β)) * lam ^ (β - 2) := by ring
      _ ≤ 1 * lam ^ (β - 2) :=
        mul_le_mul_of_nonneg_right h1.le (Real.rpow_nonneg h0.le _)
      _ = lam ^ (β - 2) := one_mul _
  by_cases h4e : β = 4
  · subst h4e
    filter_upwards [hpos, hlog] with lam h0 hL
    have e : lowerEps 4 hβ lam = lam ^ 2 * |Real.log lam| ^ 2 := by
      rw [lowerEps_eq_ite]
      norm_num
    rw [hη, e]
    have hK1 : K ≤ |Real.log lam| ^ 2 := by
      have h1 : 1 * |Real.log lam| ≤ |Real.log lam| * |Real.log lam| :=
        mul_le_mul_of_nonneg_right (by linarith only [hL, hK]) (abs_nonneg _)
      linarith only [h1, hL]
    calc K * lam ^ 2 = lam ^ 2 * K := mul_comm _ _
      _ ≤ lam ^ 2 * |Real.log lam| ^ 2 := mul_le_mul_of_nonneg_left hK1 (sq_nonneg lam)
  · filter_upwards [hpos, hlog] with lam h0 hL
    rw [hη, lowerEps_eq_ite]
    simp only [h4, h4e, ↓reduceIte]
    calc K * lam ^ 2 = lam ^ 2 * K := mul_comm _ _
      _ ≤ lam ^ 2 * |Real.log lam| :=
        mul_le_mul_of_nonneg_left (by linarith only [hL, hK]) (sq_nonneg lam)

/-- **Proposition 4.1 for `β > 2`, in the form of the frozen statement** (source l. 1796–1803):
the expressions of `proposition_4_1` for `β ≠ 2`, with the `if β = 2` branches resolved.
The constant is `2 C` for the constant `C` of `partitionFunction_ge_of_two_lt`. -/
theorem proposition_4_1_of_two_lt (β : ℝ) (hβ : 2 < β) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ENNReal.ofReal (Real.exp (2 * N * Real.log N
            + N * ((if β = 2 then Real.log |Real.log lam| else (2 - β) * Real.log lam)
              + (Real.log (dipoleConstant β hβ.le) - 1))
            - C * N * (if β = 2 then |Real.log lam| ^ (-(1 / 5 : ℝ))
                else if β < 4 then lam ^ (β - 2)
                else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
                else lam ^ 2 * |Real.log lam|)))
          ≤ partitionFunction N β lam := by
  obtain ⟨lam₀, C, hlam₀, hC, hZ⟩ := partitionFunction_ge_of_two_lt hβ
  obtain ⟨lam₁, hlam₁, hηε⟩ := exists_mul_lowerEta_sq_le_lowerEps β hβ (K := C / 4) (by positivity)
  refine ⟨min lam₀ lam₁, 2 * C, lt_min hlam₀ hlam₁, by positivity, fun N hN lam hlam hlt => ?_⟩
  have hβ2 : β ≠ 2 := hβ.ne'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hZ' := hZ N hN lam hlam (lt_of_lt_of_le hlt (min_le_left _ _))
  have hηε' := hηε lam hlam (lt_of_lt_of_le hlt (min_le_right _ _))
  simp only [hβ2, ↓reduceIte]
  rw [← lowerEps_eq_ite β hβ lam]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hZ'
  set ε := lowerEps β hβ lam with hε
  set η := lowerEta β hβ lam with hη
  set x := Real.sqrt N with hx
  have hx2 : x ^ 2 = N := Real.sq_sqrt hNpos.le
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hZpos : 0 < dipoleConstant β hβ.le := dipoleConstant_pos β hβ.le
  have hApos : 0 < dipoleConstant β hβ.le * lam ^ (2 - β) := mul_pos hZpos (Real.rpow_pos_of_pos hlam _)
  have hRpos : 0 < (N.factorial : ℝ) * (N : ℝ) ^ N * (dipoleConstant β hβ.le * lam ^ (2 - β)) ^ N *
      Real.exp (-C * N * ε - C * x * η) := by positivity
  rw [← Real.le_log_iff_exp_le hRpos]
  have hlogA : Real.log (dipoleConstant β hβ.le * lam ^ (2 - β)) =
      Real.log (dipoleConstant β hβ.le) + (2 - β) * Real.log lam := by
    rw [Real.log_mul hZpos.ne' (Real.rpow_pos_of_pos hlam _).ne', Real.log_rpow hlam]
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul hfac.ne' (by positivity), Real.log_pow, Real.log_pow, Real.log_exp, hlogA]
  have hst := log_factorial_ge (N := N) (by omega)
  -- the arithmetic--geometric mean step: `C x η ≤ C N ε + 1`
  have hamgm : C * x * η ≤ C * N * ε + 1 := by
    have hη4 : C * η ^ 2 ≤ 4 * ε := by linarith only [hηε']
    have h1 : C * x ^ 2 * (C * η ^ 2) ≤ C * x ^ 2 * (4 * ε) :=
      mul_le_mul_of_nonneg_left hη4 (by positivity)
    have e1 : (C * x * η) ^ 2 = C * x ^ 2 * (C * η ^ 2) := by ring
    have e2 : C * (N : ℝ) * ε = C * x ^ 2 * ε := by rw [hx2]
    linarith only [h1, e1, e2, sq_nonneg (C * x * η - 2)]
  linarith only [hst, hamgm]

end TwoComponentCoulomb
