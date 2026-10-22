/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.PartitionFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TwoComponentCoulomb.Integrals.Stirling
import TwoComponentCoulomb.LowerBound.ScreenedLower
import TwoComponentCoulomb.PhaseSpace.Placement
import TwoComponentCoulomb.UpperBound.ReducedConstruction

/-!
# Proposition 4.1 for `β = 2`: the critical lower bound

Source: Proposition 4.1, eq. (eq:lbz2) (l. 1755--1757),
proved at l. 1820--1826 with `ℓ = |log λ|` and `t = ℓ^{-1/5}`. The proof follows the source
(ruling R22): the positive charges are restricted to `H_t = H(N, N, t, 4t)`, the dipole lengths to
`2λ ≤ |x_i - y_i| ≤ t²`, and the energy is bounded by the Neumann construction on the disjoint
balls `B(x_i, t)` (eq. (majof)), with energy error `Σ_i |x_i - y_i|²/t² ≤ N t²`.

* `partitionFunction_two_ge` : there are `λ₀, C > 0` such that for all `N ≥ 2` and `0 < λ < λ₀`,
  `exp (2 N log N + N (log ℓ + (log (2π) - 1)) - C N ℓ^{-1/5}) ≤ Z_{N,2}^λ`.
* `partitionFunction_two_ge_frozen_form` : the same statement written with the expressions of the
  frozen `proposition_4_1` at `β = 2` (`dipoleConstant 2 _ = 2π`, the `if β = 2` branches
  resolved).

Proof. Put `s = ℓ^{1/5}` and `t = 1/s`, so that `s^5 = ℓ`. For `λ` small (`s > 16`) one has
`t ≤ 1/16`, `2λ ≤ t²` and `4t√N + Nπ(4t)² ≤ N/2`, uniformly in `N ≥ 1`. Then
`partitionFunction_ge_placement_annulus` (`LowerBound/ScreenedLower.lean`) bounds `Z` below by
`N! · vol H_t · A^N` with `A = e^{-2t²} · 2π log (t²/(2λ))`, where `e^{-2t²}` is the energy error
of (majof) and `2π log (t²/(2λ)) = 2π R` with `R = s⁵ - 2 log s - log 2`
(`integral_annulus_exp_two_smearedKernel`); and `vol H_t ≥ N^N e^{-E}`
(`volume_placementSet_ge`), `E = 8t√N + 16πNt² ≤ (8 + 16π) N t`.
Since `log R ≥ log s⁵ - 4/s` (`log_sub_le_log_critical`) and `2t² ≤ 2t`, the assembly step
`ofReal_exp_le_of_factorial_mul` (from `log N! ≥ N log N - N + 1`) gives the claim with
`C = 14 + 16π`.
-/
public section

open MeasureTheory
open scoped ENNReal Nat

namespace TwoComponentCoulomb

/-! ### The annulus mass in the variable `s = ℓ^{1/5}` -/

/-- The logarithm of the annulus ratio `t² / (2λ)` with `t = 1/s` and `λ = e^{-s⁵}`:
`R(s) = s⁵ - 2 log s - log 2`. -/
theorem criticalRadius_ge {s : ℝ} (hs : 16 ≤ s) :
    s ^ 5 - 2 * s ≤ s ^ 5 - 2 * Real.log s - Real.log 2 := by
  have hs0 : 0 < s := by linarith
  have h1 := Real.log_le_sub_one_of_pos hs0
  have h2 := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
  linarith

/-- `s⁵ - 2s > 0` for `s ≥ 16` (the polynomial part of `R(s)` is positive). -/
private theorem criticalRadius_lower_pos {s : ℝ} (hs : 16 ≤ s) : 0 < s ^ 5 - 2 * s := by
  have hs0 : 0 < s := by linarith
  have hs4 : (16 : ℝ) ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ (by norm_num) hs 4
  have h : s ^ 5 - 2 * s = s * (s ^ 4 - 2) := by ring
  rw [h]
  exact mul_pos hs0 (by norm_num at hs4; linarith)

/-- `log R(s) ≥ log s⁵ - 4/s` for `s ≥ 16`. -/
theorem log_sub_le_log_critical {s : ℝ} (hs : 16 ≤ s) :
    Real.log (s ^ 5) - 4 / s ≤ Real.log (s ^ 5 - 2 * Real.log s - Real.log 2) := by
  have hs0 : 0 < s := by linarith
  have hR := criticalRadius_ge hs
  have hRpos : 0 < s ^ 5 - 2 * Real.log s - Real.log 2 := by
    linarith [criticalRadius_lower_pos hs]
  set R := s ^ 5 - 2 * Real.log s - Real.log 2 with hRdef
  have h1 : Real.log (s ^ 5 / R) ≤ s ^ 5 / R - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) hRpos.ne'] at h1
  have h2 : s ^ 5 / R - 1 ≤ 4 / s := by
    rw [sub_le_iff_le_add, div_le_iff₀ hRpos]
    have : (4 / s + 1) * R = R + 4 * R / s := by ring
    have h3 : 4 * R / s ≥ 4 * (s ^ 5 - 2 * s) / s := by gcongr
    have h4 : 4 * (s ^ 5 - 2 * s) / s = 4 * s ^ 4 - 8 := by field_simp; ring
    have hs3 : (16 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs 3
    have hs4' : 16 * s ≤ s ^ 4 := by
      calc 16 * s ≤ s ^ 3 * s :=
            mul_le_mul_of_nonneg_right (by norm_num at hs3; linarith) hs0.le
        _ = s ^ 4 := by ring
    rw [this]
    linarith
  linarith

/-! ### The assembly -/

/-- **Proposition 4.1 for `β = 2`** (source l. 1820--1826, eq. (eq:lbz2)). -/
theorem partitionFunction_two_ge :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ENNReal.ofReal (Real.exp (2 * N * Real.log N
            + N * (Real.log |Real.log lam| + (Real.log (2 * Real.pi) - 1))
            - C * N * |Real.log lam| ^ (-(1 / 5 : ℝ)))) ≤ partitionFunction N 2 lam := by
  refine ⟨Real.exp (-(16 : ℝ) ^ 5), 14 + 16 * Real.pi, Real.exp_pos _, by positivity, ?_⟩
  intro N hN lam hlam hlt
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlog : Real.log lam < -(16 : ℝ) ^ 5 := (Real.log_lt_iff_lt_exp hlam).2 hlt
  have h16 : (0 : ℝ) < 16 ^ 5 := by positivity
  have hℓeq : |Real.log lam| = -Real.log lam := abs_of_neg (by linarith)
  set ℓ := |Real.log lam| with hℓ
  have hℓ0 : 0 < ℓ := by linarith
  set s := ℓ ^ (1 / 5 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hℓ0 _
  have hs5 : s ^ 5 = ℓ := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le]
    norm_num
  have hs16 : 16 ≤ s := by
    by_contra h
    have h' := not_le.1 h
    have := pow_le_pow_left₀ hs0.le h'.le 5
    linarith
  have htdef : ℓ ^ (-(1 / 5 : ℝ)) = s⁻¹ := Real.rpow_neg hℓ0.le _
  rw [htdef]
  set t := s⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 hs0
  have hts : t * s = 1 := inv_mul_cancel₀ hs0.ne'
  have ht16 : t ≤ 1 / 16 := by
    rw [ht]; rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hs16
  have ht1 : t ≤ 1 := by linarith
  -- the annulus ratio
  have hratio : Real.log (t ^ 2 / (2 * lam)) = s ^ 5 - 2 * Real.log s - Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_mul (by norm_num)
      hlam.ne', ht, Real.log_inv, hs5]
    have : Real.log lam = -ℓ := by rw [hℓeq]; ring
    rw [this]
    push_cast
    ring
  have hRge := criticalRadius_ge hs16
  have hRpos : 0 < s ^ 5 - 2 * Real.log s - Real.log 2 := by
    linarith [criticalRadius_lower_pos hs16]
  have hlt2 : 2 * lam ≤ t ^ 2 := by
    have h0 : 0 ≤ Real.log (t ^ 2 / (2 * lam)) := by rw [hratio]; exact hRpos.le
    rw [Real.log_nonneg_iff (by positivity), one_le_div (by positivity)] at h0
    exact h0
  -- the volume of the placement set
  have hsqrt : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_iff]
    exact ⟨hN0.le, by rw [sq]; exact le_mul_of_one_le_right hN0.le hN1'⟩
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hcond : 4 * t * Real.sqrt N + N * Real.pi * (4 * t) ^ 2 ≤ N / 2 := by
    have e1 : 4 * t * Real.sqrt N ≤ 4 * t * N := by gcongr
    have e2 : 4 * t * N ≤ N / 4 := by
      have := mul_le_mul_of_nonneg_right (show 4 * t ≤ 1 / 4 by linarith) hN0.le
      linarith
    have e3 : (N : ℝ) * Real.pi * (4 * t) ^ 2 ≤ (N : ℝ) * 4 * (1 / 4) ^ 2 := by
      have : (4 * t) ^ 2 ≤ (1 / 4) ^ 2 := by gcongr; linarith
      calc (N : ℝ) * Real.pi * (4 * t) ^ 2 ≤ (N : ℝ) * 4 * (4 * t) ^ 2 := by gcongr
        _ ≤ (N : ℝ) * 4 * (1 / 4) ^ 2 := by gcongr
    linarith
  have hvol := volume_placementSet_ge (N := N) (a := t) (b := 4 * t) ht0.le (by positivity) hcond
  have hint := integral_annulus_exp_two_smearedKernel hlam hlt2
  have hcore := partitionFunction_ge_placement_annulus (N := N) hlam (by norm_num : (0 : ℝ) ≤ 2)
    ht0 (by linarith) hlt2
  rw [hint, hratio] at hcore
  set R := s ^ 5 - 2 * Real.log s - Real.log 2 with hRdef
  set A := Real.exp (-(2 * t ^ 2)) * (2 * Real.pi * R) with hA
  have hApos : 0 < A := by positivity
  have htt : t ^ 2 ≤ t := pow_le_of_le_one ht0.le ht1 (by norm_num)
  set E := 8 * t * Real.sqrt N + Real.pi * N * (4 * t) ^ 2 with hE
  have hEneg : -8 * t * Real.sqrt N - Real.pi * N * (4 * t) ^ 2 = -E := by rw [hE]; ring
  rw [hEneg] at hvol
  -- the exponent comparison
  have hEle : E ≤ (8 + 16 * Real.pi) * N * t := by
    have e1 : 8 * t * Real.sqrt N ≤ 8 * t * N := by gcongr
    have e3 : Real.pi * N * (4 * t) ^ 2 ≤ 16 * Real.pi * N * t := by
      calc Real.pi * N * (4 * t) ^ 2 = 16 * (Real.pi * N) * t ^ 2 := by ring
        _ ≤ 16 * (Real.pi * N) * t := by gcongr
        _ = 16 * Real.pi * N * t := by ring
    rw [hE]
    linarith [e1, e3]
  have hlogA : Real.log (2 * Real.pi) + (Real.log (s ^ 5) - 4 * t) - 2 * t ^ 2 ≤
      Real.log A := by
    rw [hA, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
      Real.log_mul (by positivity) hRpos.ne']
    have := log_sub_le_log_critical hs16
    have h4 : 4 / s = 4 * t := by rw [ht]; ring
    rw [h4] at this
    linarith
  have hexp : 2 * N * Real.log N + N * (Real.log ℓ + (Real.log (2 * Real.pi) - 1))
        - (14 + 16 * Real.pi) * N * t ≤
      2 * N * Real.log N + N * (Real.log A - 1) - E := by
    have hl5 : Real.log (s ^ 5) = Real.log ℓ := by rw [hs5]
    rw [hl5] at hlogA
    have h1 : (N : ℝ) * (Real.log ℓ + (Real.log (2 * Real.pi) - 1) - 6 * t) ≤
        N * (Real.log A - 1) := mul_le_mul_of_nonneg_left (by linarith) hN0.le
    linarith [h1, hEle]
  calc ENNReal.ofReal (Real.exp (2 * N * Real.log N
            + N * (Real.log ℓ + (Real.log (2 * Real.pi) - 1)) - (14 + 16 * Real.pi) * N * t))
      ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N + N * (Real.log A - 1) - E)) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hexp)
    _ ≤ ENNReal.ofReal ((N ! : ℝ) * (N : ℝ) ^ N * A ^ N * Real.exp (-E)) :=
        ofReal_exp_le_of_factorial_mul hN1 hApos E
    _ = ENNReal.ofReal (N ! : ℝ) *
          ENNReal.ofReal ((N : ℝ) ^ N * Real.exp (-E)) * (ENNReal.ofReal A) ^ N := by
        have : (N ! : ℝ) * (N : ℝ) ^ N * A ^ N * Real.exp (-E) =
            (N ! : ℝ) * ((N : ℝ) ^ N * Real.exp (-E)) * A ^ N := by ring
        rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow hApos.le]
    _ ≤ ENNReal.ofReal (N ! : ℝ) * volume (placementSet N N t (4 * t)) *
          (ENNReal.ofReal A) ^ N := by gcongr
    _ ≤ partitionFunction N 2 lam := hcore

/-- **Proposition 4.1 for `β = 2`, in the form of the frozen statement** (source l. 1755--1757):
the expressions of `proposition_4_1` at `β = 2`, with `dipoleConstant 2 _ = 2π` and the
`if β = 2` branches resolved. -/
theorem partitionFunction_two_ge_frozen_form (hβ : (2 : ℝ) ≤ 2) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ENNReal.ofReal (Real.exp (2 * N * Real.log N
            + N * ((if (2 : ℝ) = 2 then Real.log |Real.log lam| else (2 - 2) * Real.log lam)
              + (Real.log (dipoleConstant 2 hβ) - 1))
            - C * N * (if (2 : ℝ) = 2 then |Real.log lam| ^ (-(1 / 5 : ℝ))
                else if (2 : ℝ) < 4 then lam ^ ((2 : ℝ) - 2)
                else if (2 : ℝ) = 4 then lam ^ 2 * |Real.log lam| ^ 2
                else lam ^ 2 * |Real.log lam|)))
          ≤ partitionFunction N 2 lam := by
  obtain ⟨lam₀, C, hlam₀, hC, h⟩ := partitionFunction_two_ge
  refine ⟨lam₀, C, hlam₀, hC, fun N hN lam hlam hlt => ?_⟩
  have := h N hN lam hlam hlt
  simpa [dipoleConstant] using this

end TwoComponentCoulomb

end
