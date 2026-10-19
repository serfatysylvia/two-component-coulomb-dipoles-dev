/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.Integrals.LogFacts
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Radial integrals for the pair displacements of Proposition 3.9

Source: Step 2 of the proof of Proposition 3.9, l. 1280--1332
(`align1`, `defvarphi`, `align2`, `pred3`), and the analogous tilt factors in Steps 3 and 4 of the
proof of Theorem 2, l. 2092--2100 and 2143--2150.

Throughout `g_λ = smearedKernel λ`, `a(u) = (|u|/4) ∨ λ` is `displacementScale λ u`, `ℓ = |log λ|`,
and `𝒵_β = dipoleConstant β`.

* `isolatedScale β λ = λ^{2-β} 1_{β>2} + ℓ 1_{β=2}`, `isolatedPhi β λ x = φ_β(x)` (`defvarphi`) and
  `isolatedTail β λ ρ = ℓ^{-1} 1_{β=2} + (λ/ρ)^{β-2} 1_{β>2}` (the normalised same-sign factor
  of `pred3`), with `isolatedPhi_nonneg`, `isolatedPhi_anti` (for `β > 2`),
  `isolatedScale_mul_isolatedTail`.
* `setIntegral_closedBall_comp_norm` : polar coordinates for the integral of a radial function
  over a closed disc.
* `exists_integral_closedBall_exp_mul_pow_le` : the master estimate
  `∫_{|u| ≤ 4ρ} e^{β g_λ(u)} (a(u)/ρ)^κ du ≤ K λ^{2-β} (λ/ρ)^κ + 2π ρ^{-κ} ∫_{2λ}^{4ρ} y^{1-β+κ} dy`,
  from which all the radial estimates below are read off (core `|u| ≤ 2λ` by
  `g_λ ≤ -log λ + C`; annulus by `g_λ = -log` outside `B(0, 2λ)`).
* `exists_integral_closedBall_exp_mul_sq_le` : the quadratic correction
  `∫_{|u| ≤ 4ρ} e^{β g_λ} (a/ρ)² ≤ C (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}) φ_β(ρ)`.
* `lintegral_neutralPair_le` : `align1`, the neutral-pair radial integral
  `≤ 𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}) (1 + C' φ_β(ρ))`.
* `lintegral_sameSignPair_le`, `lintegral_sameSignPair_le_normalized` : `align2`,
  `≤ C ρ^{2-β}`, and its normalised form used in `pred3`.
* `lintegral_sameSignPair_cutoff_le` (with the plane version
  `lintegral_sameSignPair_cutoff_le_univ`) : Theorem 2, Step 3, the same-sign factor with the cutoff
  `γ`, for `β > 2`.
* `lintegral_neutralTilt_le` : Theorem 2, Step 4, the tilt factor of a pair in `I ∖ I'`,
  for `β > 2`, over the whole plane.

All integrals are over `ℂ` with respect to Lebesgue measure, and the bounds are stated as
lintegrals (`∫⁻` of `ENNReal.ofReal`) so that they compose with products over the pairs. The
constants depend only on `β` (and on the constant `C` of `align1`), uniformly in `λ`, `ρ`, `γ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### Definitions -/

/-- The scale `a(u) = (|u|/4) ∨ λ` of a displacement `u` (source l. 1266). -/
noncomputable def displacementScale (lam : ℝ) (u : ℂ) : ℝ :=
  max (‖u‖ / 4) lam

/-- The normalisation `λ^{2-β} 1_{β>2} + ℓ 1_{β=2}` of the leading term of the radial integrals
(source `align1`, l. 1284--1289); defined for `β ≥ 2` only (ruling R6). -/
noncomputable def isolatedScale (β : ℝ) (_hβ : 2 ≤ β) (lam : ℝ) : ℝ :=
  if β = 2 then |Real.log lam| else lam ^ (2 - β)

/-- The correction profile `φ_β(x)` (source `defvarphi`, l. 1290--1298), with `ℓ = |log λ|`;
defined for `β ≥ 2` only (ruling R6). -/
noncomputable def isolatedPhi (β : ℝ) (_hβ : 2 ≤ β) (lam x : ℝ) : ℝ :=
  if β = 2 then (1 + |Real.log x|) / |Real.log lam|
  else if β < 4 then (lam / x) ^ (β - 2)
  else if β = 4 then (lam / x) ^ 2 * (1 + Real.log (x / lam))
  else (lam / x) ^ 2

/-- The normalised same-sign radial factor `ℓ^{-1} 1_{β=2} + (λ/ρ)^{β-2} 1_{β>2}` of `pred3`
(source l. 1329--1331); defined for `β ≥ 2` only (ruling R6). -/
noncomputable def isolatedTail (β : ℝ) (_hβ : 2 ≤ β) (lam ρ : ℝ) : ℝ :=
  if β = 2 then |Real.log lam|⁻¹ else (lam / ρ) ^ (β - 2)

theorem continuous_displacementScale (lam : ℝ) : Continuous (displacementScale lam) :=
  (continuous_norm.div_const 4).max continuous_const

theorem displacementScale_pos {lam : ℝ} (hlam : 0 < lam) (u : ℂ) :
    0 < displacementScale lam u :=
  lt_of_lt_of_le hlam (le_max_right _ _)

theorem displacementScale_le_of_norm_le {lam ρ : ℝ} {u : ℂ} (hρ : lam ≤ ρ) (hu : ‖u‖ ≤ 4 * ρ) :
    displacementScale lam u ≤ ρ :=
  max_le (by linarith) hρ

theorem isolatedPhi_of_eq_two {β : ℝ} (hβ : 2 ≤ β) (h : β = 2) (lam x : ℝ) :
    isolatedPhi β hβ lam x = (1 + |Real.log x|) / |Real.log lam| := by
  simp [isolatedPhi, h]

/-! ### Polar coordinates on a closed disc -/

/-- Polar coordinates for a radial function on a closed disc of `ℂ`:
`∫_{|u| ≤ T} Φ(|u|) du = 2π ∫_{(0, T]} y Φ(y) dy`. -/
theorem setIntegral_closedBall_comp_norm (Φ : ℝ → ℝ) (T : ℝ) :
    ∫ u in Metric.closedBall (0 : ℂ) T, Φ ‖u‖ = 2 * Real.pi * ∫ y in Ioc 0 T, y * Φ y := by
  have h1 : ∀ u : ℂ, (Metric.closedBall (0 : ℂ) T).indicator (fun u => Φ ‖u‖) u =
      (Iic T).indicator Φ ‖u‖ := by
    intro u
    by_cases hu : ‖u‖ ≤ T
    · rw [indicator_of_mem (by simpa using hu), indicator_of_mem (mem_Iic.2 hu)]
    · rw [indicator_of_notMem (by simpa using hu), indicator_of_notMem (by simpa using hu)]
  rw [← integral_indicator Metric.isClosed_closedBall.measurableSet]
  simp_rw [h1]
  rw [integral_comp_norm_complex]
  congr 1
  have h2 : ∀ y : ℝ, y * (Iic T).indicator Φ y = (Iic T).indicator (fun y => y * Φ y) y := by
    intro y
    by_cases hy : y ∈ Iic T
    · rw [indicator_of_mem hy, indicator_of_mem hy]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
  simp_rw [h2]
  rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]

/-! ### Elementary bounds -/

/-- Uniform bound `e^{β g_λ(z)} ≤ K λ^{-β}` for `β ≥ 0` (from `g_λ ≤ -log λ + C`). -/
theorem exists_exp_mul_smearedKernel_le {β : ℝ} (hβ : 0 ≤ β) :
    ∃ K : ℝ, 0 < K ∧ ∀ lam : ℝ, 0 < lam → ∀ z : ℂ,
      Real.exp (β * smearedKernel lam z) ≤ K * lam ^ (-β) := by
  obtain ⟨C, hC⟩ := exists_smearedKernel_le
  refine ⟨Real.exp (β * C), Real.exp_pos _, fun lam hlam z => ?_⟩
  have h1 : β * smearedKernel lam z ≤ β * (-Real.log lam + C) :=
    mul_le_mul_of_nonneg_left (hC lam hlam z) hβ
  calc Real.exp (β * smearedKernel lam z) ≤ Real.exp (β * (-Real.log lam + C)) :=
        Real.exp_le_exp.2 h1
    _ = Real.exp (β * C) * lam ^ (-β) := by
      rw [Real.rpow_def_of_pos hlam, ← Real.exp_add]
      congr 1
      ring

theorem intervalIntegral_rpow_le_of_neg_one_lt {p s t : ℝ} (hp : -1 < p) (hs : 0 ≤ s) :
    ∫ y in s..t, y ^ p ≤ t ^ (p + 1) / (p + 1) := by
  rw [integral_rpow (Or.inl hp)]
  have h1 : 0 < p + 1 := by linarith
  have h2 : 0 ≤ s ^ (p + 1) := Real.rpow_nonneg hs _
  rw [div_le_div_iff_of_pos_right h1]
  linarith

theorem intervalIntegral_rpow_le_of_lt_neg_one {p s t : ℝ} (hp : p < -1) (hs : 0 < s)
    (hst : s ≤ t) : ∫ y in s..t, y ^ p ≤ s ^ (p + 1) / (-(p + 1)) := by
  have h0 : (0 : ℝ) ∉ uIcc s t := by
    rw [uIcc_of_le hst]
    exact fun h => by linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
  have h1 : 0 < -(p + 1) := by linarith
  have h2 : 0 ≤ t ^ (p + 1) := Real.rpow_nonneg (by linarith) _
  rw [← neg_div_neg_eq, neg_sub]
  rw [div_le_div_iff_of_pos_right h1]
  linarith

theorem intervalIntegral_rpow_neg_one {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ∫ y in s..t, y ^ (-1 : ℝ) = Real.log (t / s) := by
  simp_rw [Real.rpow_neg_one]
  exact integral_inv_of_pos hs ht

/-! ### The master estimate on a disc -/

/-- **Master radial estimate.** For `β, κ ≥ 0` there is `K > 0` such that for `0 < λ ≤ ρ`
`∫_{|u| ≤ 4ρ} e^{β g_λ(u)} (a(u)/ρ)^κ du ≤ K λ^{2-β} (λ/ρ)^κ + 2π ρ^{-κ} ∫_{2λ}^{4ρ} y^{1-β+κ} dy`.
The first term bounds the core `|u| ≤ 2λ`, where `a = λ` and `e^{β g_λ} ≤ K λ^{-β}`; the second is
the annulus, where `e^{β g_λ(y)} y = y^{1-β}` and `a(y) ≤ y`. -/
theorem exists_integral_closedBall_exp_mul_pow_le {β κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ lam ρ : ℝ, 0 < lam → lam ≤ ρ →
      ∫ u in Metric.closedBall (0 : ℂ) (4 * ρ),
          Real.exp (β * smearedKernel lam u) * (displacementScale lam u / ρ) ^ κ ≤
        K * lam ^ (2 - β) * (lam / ρ) ^ κ +
          2 * Real.pi * ρ ^ (-κ) * ∫ y in (2 * lam)..(4 * ρ), y ^ (1 - β + κ) := by
  obtain ⟨K0, hK0, hK⟩ := exists_exp_mul_smearedKernel_le hβ
  refine ⟨4 * Real.pi * K0, by positivity, fun lam ρ hlam hρ => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
  have hl2 : lam ≤ 2 * lam := le_mul_of_one_le_left hlam.le one_le_two
  have h2l : 0 < 2 * lam := mul_pos two_pos hlam
  set Φ : ℝ → ℝ := fun y => Real.exp (β * smearedKernel lam (y : ℂ)) *
    (max (y / 4) lam / ρ) ^ κ with hΦ
  have hint : (fun u : ℂ => Real.exp (β * smearedKernel lam u) *
      (displacementScale lam u / ρ) ^ κ) = fun u => Φ ‖u‖ := by
    funext u
    simp only [hΦ, displacementScale]
    rw [exp_smearedKernel_eq_comp_norm lam β u]
  have hΦc : Continuous Φ := by
    refine (((continuous_smearedKernel hlam).comp Complex.continuous_ofReal).const_mul β).rexp.mul
      (Continuous.rpow_const ?_ fun y => Or.inr hκ)
    exact ((continuous_id.div_const 4).max continuous_const).div_const ρ
  have hcont : Continuous fun y : ℝ => y * Φ y := continuous_id.mul hΦc
  have hII : ∀ a b : ℝ, IntervalIntegrable (fun y : ℝ => y * Φ y) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  rw [hint, setIntegral_closedBall_comp_norm,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 4 * ρ),
    ← intervalIntegral.integral_add_adjacent_intervals (hII 0 (2 * lam)) (hII (2 * lam) (4 * ρ))]
  have hcore : ∫ y in (0 : ℝ)..(2 * lam), y * Φ y ≤
      K0 * lam ^ (-β) * (lam / ρ) ^ κ * (2 * lam ^ 2) := by
    calc ∫ y in (0 : ℝ)..(2 * lam), y * Φ y
        ≤ ∫ y in (0 : ℝ)..(2 * lam), y * (K0 * lam ^ (-β) * (lam / ρ) ^ κ) := by
          refine intervalIntegral.integral_mono_on (by positivity) (hII _ _)
            ((continuous_id.mul continuous_const).intervalIntegrable _ _) ?_
          intro y hy
          have hy0 : 0 ≤ y := hy.1
          have hmax : max (y / 4) lam = lam :=
            max_eq_right ((div_le_iff₀' four_pos).2
              (hy.2.trans (mul_le_mul_of_nonneg_right (by norm_num) hlam.le)))
          calc y * Φ y = y * (Real.exp (β * smearedKernel lam (y : ℂ)) * (lam / ρ) ^ κ) := by
                simp only [hΦ, hmax]
            _ ≤ y * (K0 * lam ^ (-β) * (lam / ρ) ^ κ) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (hK lam hlam y) (by positivity)) hy0
      _ = K0 * lam ^ (-β) * (lam / ρ) ^ κ * (2 * lam ^ 2) := by
          rw [intervalIntegral.integral_mul_const, integral_id]
          ring
  have hann : ∫ y in (2 * lam)..(4 * ρ), y * Φ y ≤
      ρ ^ (-κ) * ∫ y in (2 * lam)..(4 * ρ), y ^ (1 - β + κ) := by
    rw [← intervalIntegral.integral_const_mul]
    have h24 : 2 * lam ≤ 4 * ρ :=
      (mul_le_mul_of_nonneg_left hρ zero_le_two).trans
        (mul_le_mul_of_nonneg_right (by norm_num) hρ0.le)
    refine intervalIntegral.integral_mono_on h24 (hII _ _) ?_ ?_
    · exact (intervalIntegral.intervalIntegrable_rpow
        (Or.inr (by
          rw [uIcc_of_le h24]
          exact fun h => not_le.2 h2l h.1))).const_mul _
    · intro y hy
      have hy2 : 2 * lam ≤ y := hy.1
      have hy0 : 0 < y := lt_of_lt_of_le h2l hy2
      have e1 := exp_mul_smearedKernel_mul_of_le β hlam hy2
      have h2 : max (y / 4) lam / ρ ≤ y / ρ :=
        div_le_div_of_nonneg_right
          (max_le (div_le_self hy0.le (by norm_num)) (hl2.trans hy2)) hρ0.le
      have h3 : (max (y / 4) lam / ρ) ^ κ ≤ (y / ρ) ^ κ :=
        Real.rpow_le_rpow (by positivity) h2 hκ
      calc y * Φ y = (Real.exp (β * smearedKernel lam (y : ℂ)) * y) *
            (max (y / 4) lam / ρ) ^ κ := by
            simp only [hΦ]
            ring
        _ ≤ y ^ (1 - β) * (y / ρ) ^ κ := by
            rw [e1]
            exact mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = ρ ^ (-κ) * y ^ (1 - β + κ) := by
            rw [Real.div_rpow hy0.le hρ0.le, Real.rpow_add hy0, Real.rpow_neg hρ0.le]
            ring
  have e2 : lam ^ (2 - β) = lam ^ 2 * lam ^ (-β) := by
    rw [sub_eq_add_neg, Real.rpow_add hlam, Real.rpow_two]
  calc 2 * Real.pi * ((∫ y in (0 : ℝ)..(2 * lam), y * Φ y) +
        ∫ y in (2 * lam)..(4 * ρ), y * Φ y)
      ≤ 2 * Real.pi * (K0 * lam ^ (-β) * (lam / ρ) ^ κ * (2 * lam ^ 2) +
        ρ ^ (-κ) * ∫ y in (2 * lam)..(4 * ρ), y ^ (1 - β + κ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hcore hann) (by positivity)
    _ = 4 * Real.pi * K0 * lam ^ (2 - β) * (lam / ρ) ^ κ +
        2 * Real.pi * ρ ^ (-κ) * ∫ y in (2 * lam)..(4 * ρ), y ^ (1 - β + κ) := by
        rw [e2]
        ring

/-! ### Algebra of the profiles -/

theorem rpow_neg_mul_div_rpow {lam ρ : ℝ} (hlam : 0 < lam) (hρ : 0 < ρ) (s : ℝ) :
    lam ^ (-s) * (lam / ρ) ^ s = ρ ^ (-s) := by
  rw [Real.div_rpow hlam.le hρ.le, Real.rpow_neg hlam.le, Real.rpow_neg hρ.le]
  have : lam ^ s ≠ 0 := (Real.rpow_pos_of_pos hlam s).ne'
  field_simp

theorem log_eq_neg_abs_log {lam : ℝ} (hlam : 0 < lam) (h : lam ≤ Real.exp (-1)) :
    Real.log lam = -|Real.log lam| := by
  rw [abs_of_nonpos (by linarith [log_le_neg_one hlam h])]
  ring

theorem isolatedScale_pos {β : ℝ} (hβ : 2 ≤ β) {lam : ℝ} (hlam : 0 < lam)
    (h : lam ≤ Real.exp (-1)) : 0 < isolatedScale β hβ lam := by
  unfold isolatedScale
  split_ifs
  · exact lt_of_lt_of_le one_pos (one_le_abs_log hlam h)
  · exact Real.rpow_pos_of_pos hlam _

theorem isolatedPhi_nonneg {β : ℝ} (hβ : 2 ≤ β) {lam x : ℝ} (hlam : 0 < lam) (hx : lam ≤ x) :
    0 ≤ isolatedPhi β hβ lam x := by
  have hx0 : 0 < x := lt_of_lt_of_le hlam hx
  have hlog : 0 ≤ Real.log (x / lam) := Real.log_nonneg ((one_le_div hlam).2 hx)
  unfold isolatedPhi
  split_ifs
  · positivity
  · positivity
  · exact mul_nonneg (by positivity) (by linarith)
  · positivity

theorem isolatedTail_nonneg {β : ℝ} (hβ : 2 ≤ β) {lam ρ : ℝ} (hlam : 0 < lam) (hρ : 0 < ρ) :
    0 ≤ isolatedTail β hβ lam ρ := by
  unfold isolatedTail
  split_ifs
  · positivity
  · positivity

/-- For `β > 2` and `ρ ≥ λ`, `(λ/ρ)^{β-2} ≤ φ_β(ρ)`. -/
theorem rpow_div_le_isolatedPhi {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) {lam ρ : ℝ} (hlam : 0 < lam)
    (hρ : lam ≤ ρ) : (lam / ρ) ^ (β - 2) ≤ isolatedPhi β hβ lam ρ := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
  have hq0 : 0 < lam / ρ := by positivity
  have hq1 : lam / ρ ≤ 1 := (div_le_one hρ0).2 hρ
  have hlog : 0 ≤ Real.log (ρ / lam) := Real.log_nonneg ((one_le_div hlam).2 hρ)
  unfold isolatedPhi
  split_ifs with h h4 h4'
  · exact absurd h h2.ne'
  · exact le_rfl
  · subst h4'
    rw [show (4 : ℝ) - 2 = 2 by norm_num, Real.rpow_two]
    exact le_mul_of_one_le_right (sq_nonneg _) (le_add_of_nonneg_right hlog)
  · calc (lam / ρ) ^ (β - 2) ≤ (lam / ρ) ^ (2 : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_ge hq0 hq1 ?_
          linarith [not_lt.1 h4]
      _ = (lam / ρ) ^ 2 := Real.rpow_two _

/-- Algebraic core of `isolatedPhi_anti` at `β = 4`, with the two logarithms abstracted to `L` and
`M`. -/
private theorem isolatedPhi_anti_aux {lam x y L M : ℝ} (hx0 : 0 < x) (hxy : x ≤ y)
    (hL : 0 ≤ L) (hM : M ≤ y / x - 1) :
    (lam / y) ^ 2 * (1 + (L + M)) ≤ (lam / x) ^ 2 * (1 + L) := by
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hM' : x * M ≤ y - x := by
    have := mul_le_mul_of_nonneg_left hM hx0.le
    rwa [mul_sub, mul_div_cancel₀ _ hx0.ne', mul_one] at this
  have key : x ^ 2 * (1 + L + M) ≤ y ^ 2 * (1 + L) := by
    linarith only [mul_le_mul_of_nonneg_left hM' hx0.le,
      mul_nonneg (sub_nonneg.2 hxy) hy0.le,
      mul_nonneg (mul_nonneg (sub_nonneg.2 hxy) (add_pos hx0 hy0).le) hL]
  rw [div_pow, div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith only [mul_le_mul_of_nonneg_left key (sq_nonneg lam)]

/-- For `β > 2` the profile `φ_β` is nonincreasing on `[λ, ∞)`. (This fails for `β = 2`, where
`φ_2(x) = (1 + |log x|)/ℓ` increases for `x > 1`.) -/
theorem isolatedPhi_anti {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) {lam x y : ℝ} (hlam : 0 < lam)
    (hx : lam ≤ x) (hxy : x ≤ y) : isolatedPhi β hβ lam y ≤ isolatedPhi β hβ lam x := by
  have hx0 : 0 < x := lt_of_lt_of_le hlam hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hq : lam / y ≤ lam / x := div_le_div_of_nonneg_left hlam.le hx0 hxy
  have hq0 : 0 ≤ lam / y := by positivity
  unfold isolatedPhi
  split_ifs with h h4 h4'
  · exact absurd h h2.ne'
  · exact Real.rpow_le_rpow hq0 hq (sub_nonneg.2 hβ)
  · subst h4'
    have hL : 0 ≤ Real.log (x / lam) := Real.log_nonneg ((one_le_div hlam).2 hx)
    have hM : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hlog : Real.log (y / lam) = Real.log (x / lam) + Real.log (y / x) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      exact congrArg Real.log (by field_simp)
    rw [hlog]
    exact isolatedPhi_anti_aux hx0 hxy hL hM
  · exact pow_le_pow_left₀ hq0 hq 2

/-! ### The quadratic correction -/

/-- **Quadratic correction** (source l. 1305--1309): for `β ≥ 2`, `0 < λ ≤ e^{-1}`, `ρ ≥ λ`,
`∫_{|u| ≤ 4ρ} e^{β g_λ(u)} (a(u)/ρ)² du ≤ C (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}) φ_β(ρ)`. -/
theorem exists_integral_closedBall_exp_mul_sq_le {β : ℝ} (hβ : 2 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ρ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → lam ≤ ρ →
      ∫ u in Metric.closedBall (0 : ℂ) (4 * ρ),
          Real.exp (β * smearedKernel lam u) * (displacementScale lam u / ρ) ^ 2 ≤
        C * isolatedScale β hβ lam * isolatedPhi β hβ lam ρ := by
  obtain ⟨K, hK0, hK⟩ := exists_integral_closedBall_exp_mul_pow_le (β := β) (κ := 2)
    (zero_le_two.trans hβ) zero_le_two
  have hK' : ∀ lam ρ : ℝ, 0 < lam → lam ≤ ρ →
      ∫ u in Metric.closedBall (0 : ℂ) (4 * ρ),
          Real.exp (β * smearedKernel lam u) * (displacementScale lam u / ρ) ^ 2 ≤
        K * lam ^ (2 - β) * (lam / ρ) ^ 2 +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ (3 - β) := by
    intro lam ρ hlam hρ
    have h := hK lam ρ hlam hρ
    simp only [Real.rpow_two, Real.rpow_neg (lt_of_lt_of_le hlam hρ).le] at h
    rwa [show (1 : ℝ) - β + 2 = 3 - β by ring] at h
  rcases hβ.eq_or_lt with h2 | h2
  · -- `β = 2`
    subst h2
    refine ⟨K + 16 * Real.pi, by positivity, fun lam ρ hlam hl1 hρ => ?_⟩
    have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
    have hℓ : 0 < |Real.log lam| := lt_of_lt_of_le one_pos (one_le_abs_log hlam hl1)
    have hq1 : (lam / ρ) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hρ0).2 hρ)
    have hI : ∫ y in (2 * lam)..(4 * ρ), y ^ ((3 : ℝ) - 2) ≤ 8 * ρ ^ 2 := by
      rw [show (3 : ℝ) - 2 = 1 by norm_num]
      simp_rw [Real.rpow_one]
      rw [integral_id, show ((4 * ρ) ^ 2 - (2 * lam) ^ 2) / 2 = 8 * ρ ^ 2 - 2 * lam ^ 2 by ring]
      exact sub_le_self _ (by positivity)
    have hs : isolatedScale 2 hβ lam = |Real.log lam| := by simp [isolatedScale]
    have hp : isolatedPhi 2 hβ lam ρ = (1 + |Real.log ρ|) / |Real.log lam| := by
      simp [isolatedPhi]
    rw [hs, hp]
    calc _ ≤ K * lam ^ ((2 : ℝ) - 2) * (lam / ρ) ^ 2 +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ ((3 : ℝ) - 2) :=
          hK' lam ρ hlam hρ
      _ ≤ K + 16 * Real.pi := by
          have h1 : K * lam ^ ((2 : ℝ) - 2) * (lam / ρ) ^ 2 ≤ K := by
            rw [sub_self, Real.rpow_zero, mul_one]
            exact mul_le_of_le_one_right hK0.le hq1
          have h2 : 2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ ((3 : ℝ) - 2) ≤
              16 * Real.pi := by
            calc _ ≤ 2 * Real.pi * (ρ ^ 2)⁻¹ * (8 * ρ ^ 2) :=
                  mul_le_mul_of_nonneg_left hI (by positivity)
              _ = 16 * Real.pi := by field_simp; ring
          exact add_le_add h1 h2
      _ ≤ (K + 16 * Real.pi) * |Real.log lam| * ((1 + |Real.log ρ|) / |Real.log lam|) := by
          rw [mul_assoc, mul_div_cancel₀ _ hℓ.ne']
          exact le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (abs_nonneg _))
  rcases lt_or_ge β 4 with h4 | h4
  · -- `2 < β < 4`
    refine ⟨K + 2 * Real.pi * 4 ^ (4 - β) / (4 - β), by
      have : 0 < 4 - β := sub_pos.2 h4
      positivity, fun lam ρ hlam hl1 hρ => ?_⟩
    have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
    have hq0 : 0 < lam / ρ := by positivity
    have hq1 : lam / ρ ≤ 1 := (div_le_one hρ0).2 hρ
    have hs : isolatedScale β hβ lam = lam ^ (2 - β) := by simp [isolatedScale, h2.ne']
    have hp : isolatedPhi β hβ lam ρ = (lam / ρ) ^ (β - 2) := by
      simp [isolatedPhi, h2.ne', h4]
    rw [hs, hp]
    have i1 : (lam / ρ) ^ 2 ≤ (lam / ρ) ^ (β - 2) := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (by linarith only [h4])
    have i2 : ∫ y in (2 * lam)..(4 * ρ), y ^ (3 - β) ≤ (4 * ρ) ^ (4 - β) / (4 - β) := by
      have := intervalIntegral_rpow_le_of_neg_one_lt (p := 3 - β) (s := 2 * lam) (t := 4 * ρ)
        (by linarith only [h4]) (by positivity)
      rwa [show 3 - β + 1 = 4 - β by ring] at this
    have i3 : (ρ ^ 2)⁻¹ * (4 * ρ) ^ (4 - β) = 4 ^ (4 - β) * ρ ^ (2 - β) := by
      rw [Real.mul_rpow (by norm_num) hρ0.le, show 4 - β = 2 + (2 - β) by ring,
        Real.rpow_add hρ0, Real.rpow_two]
      field_simp
    have i4 : lam ^ (2 - β) * (lam / ρ) ^ (β - 2) = ρ ^ (2 - β) := by
      have := rpow_neg_mul_div_rpow hlam hρ0 (β - 2)
      rwa [neg_sub] at this
    calc _ ≤ K * lam ^ (2 - β) * (lam / ρ) ^ 2 +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ (3 - β) := hK' lam ρ hlam hρ
      _ ≤ K * lam ^ (2 - β) * (lam / ρ) ^ (β - 2) +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ((4 * ρ) ^ (4 - β) / (4 - β)) :=
          add_le_add (mul_le_mul_of_nonneg_left i1 (by positivity))
            (mul_le_mul_of_nonneg_left i2 (by positivity))
      _ = (K + 2 * Real.pi * 4 ^ (4 - β) / (4 - β)) * (lam ^ (2 - β) * (lam / ρ) ^ (β - 2)) := by
          linear_combination (2 * Real.pi / (4 - β)) * i3 -
            (2 * Real.pi * 4 ^ (4 - β) / (4 - β)) * i4
      _ = _ := by ring
  rcases h4.eq_or_lt with h4 | h4
  · -- `β = 4`
    subst h4
    refine ⟨K + 2 * Real.pi, by positivity, fun lam ρ hlam hl1 hρ => ?_⟩
    have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
    have hL : 0 ≤ Real.log (ρ / lam) := Real.log_nonneg ((one_le_div hlam).2 hρ)
    have hs : isolatedScale 4 hβ lam = lam ^ ((2 : ℝ) - 4) := by
      simp [isolatedScale]
    have hp : isolatedPhi 4 hβ lam ρ = (lam / ρ) ^ 2 * (1 + Real.log (ρ / lam)) := by
      simp [isolatedPhi]
    have hlog : ∫ y in (2 * lam)..(4 * ρ), y ^ ((3 : ℝ) - 4) ≤ 1 + Real.log (ρ / lam) := by
      rw [show (3 : ℝ) - 4 = -1 by norm_num, intervalIntegral_rpow_neg_one (by positivity)
        (by positivity), show 4 * ρ / (2 * lam) = 2 * (ρ / lam) by field_simp; ring,
        Real.log_mul (by norm_num) (by positivity)]
      exact add_le_add_left ((Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)) _
    have e1 : lam ^ ((2 : ℝ) - 4) = (lam ^ 2)⁻¹ := by
      rw [show (2 : ℝ) - 4 = -(2 : ℝ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_two]
    have e2 : (ρ ^ 2)⁻¹ = (lam ^ 2)⁻¹ * (lam / ρ) ^ 2 := by field_simp
    rw [hs, hp]
    calc _ ≤ K * lam ^ ((2 : ℝ) - 4) * (lam / ρ) ^ 2 +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ ((3 : ℝ) - 4) :=
          hK' lam ρ hlam hρ
      _ ≤ K * lam ^ ((2 : ℝ) - 4) * ((lam / ρ) ^ 2 * (1 + Real.log (ρ / lam))) +
          2 * Real.pi * (ρ ^ 2)⁻¹ * (1 + Real.log (ρ / lam)) := by
          have hA : 0 ≤ K * lam ^ ((2 : ℝ) - 4) * (lam / ρ) ^ 2 := by positivity
          have : K * lam ^ ((2 : ℝ) - 4) * (lam / ρ) ^ 2 ≤
              K * lam ^ ((2 : ℝ) - 4) * ((lam / ρ) ^ 2 * (1 + Real.log (ρ / lam))) := by
            rw [← mul_assoc]
            exact le_mul_of_one_le_right hA (le_add_of_nonneg_right hL)
          have h2 : 2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ ((3 : ℝ) - 4) ≤
              2 * Real.pi * (ρ ^ 2)⁻¹ * (1 + Real.log (ρ / lam)) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
          exact add_le_add this h2
      _ = (K + 2 * Real.pi) * lam ^ ((2 : ℝ) - 4) * ((lam / ρ) ^ 2 * (1 + Real.log (ρ / lam))) := by
          rw [e1, e2]
          ring
  · -- `β > 4`
    have hb : 0 < β - 4 := sub_pos.2 h4
    refine ⟨K + 2 * Real.pi * 2 ^ (4 - β) / (β - 4), by positivity, fun lam ρ hlam hl1 hρ => ?_⟩
    have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
    have hs : isolatedScale β hβ lam = lam ^ (2 - β) := by simp [isolatedScale, h2.ne']
    have hp : isolatedPhi β hβ lam ρ = (lam / ρ) ^ 2 := by
      simp [isolatedPhi, h2.ne', not_lt.2 h4.le, h4.ne']
    rw [hs, hp]
    have i2 : ∫ y in (2 * lam)..(4 * ρ), y ^ (3 - β) ≤ (2 * lam) ^ (4 - β) / (β - 4) := by
      have := intervalIntegral_rpow_le_of_lt_neg_one (p := 3 - β) (s := 2 * lam) (t := 4 * ρ)
        (by linarith only [h4]) (by positivity) (by linarith only [hlam, hρ])
      rwa [show 3 - β + 1 = 4 - β by ring, show -(4 - β) = β - 4 by ring] at this
    have i3 : (ρ ^ 2)⁻¹ * (2 * lam) ^ (4 - β) = 2 ^ (4 - β) * (lam ^ (2 - β) * (lam / ρ) ^ 2) := by
      rw [Real.mul_rpow (by norm_num) hlam.le, show 4 - β = 2 + (2 - β) by ring,
        Real.rpow_add hlam, Real.rpow_two]
      field_simp
    calc _ ≤ K * lam ^ (2 - β) * (lam / ρ) ^ 2 +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ∫ y in (2 * lam)..(4 * ρ), y ^ (3 - β) := hK' lam ρ hlam hρ
      _ ≤ K * lam ^ (2 - β) * (lam / ρ) ^ 2 +
          2 * Real.pi * (ρ ^ 2)⁻¹ * ((2 * lam) ^ (4 - β) / (β - 4)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left i2 (by positivity))
      _ = (K + 2 * Real.pi * 2 ^ (4 - β) / (β - 4)) * (lam ^ (2 - β) * (lam / ρ) ^ 2) := by
          linear_combination (2 * Real.pi / (β - 4)) * i3
      _ = _ := by ring

/-! ### From Bochner integrals on a disc to lintegrals -/

theorem continuous_exp_mul_smearedKernel {β lam : ℝ} (hlam : 0 < lam) :
    Continuous fun u : ℂ => Real.exp (β * smearedKernel lam u) :=
  ((continuous_smearedKernel hlam).const_mul β).rexp

theorem continuous_exp_mul_smearedKernel_mul_rpow {β κ lam ρ : ℝ} (hlam : 0 < lam)
    (hκ : 0 ≤ κ) :
    Continuous fun u : ℂ =>
      Real.exp (β * smearedKernel lam u) * (displacementScale lam u / ρ) ^ κ :=
  (continuous_exp_mul_smearedKernel hlam).mul
    (Continuous.rpow_const ((continuous_displacementScale lam).div_const ρ) fun _ => Or.inr hκ)

theorem lintegral_closedBall_ofReal_eq {f : ℂ → ℝ} (hf : Continuous f) (hf0 : ∀ u, 0 ≤ f u)
    (T : ℝ) :
    ∫⁻ u in Metric.closedBall (0 : ℂ) T, ENNReal.ofReal (f u) =
      ENNReal.ofReal (∫ u in Metric.closedBall (0 : ℂ) T, f u) :=
  (ofReal_integral_eq_lintegral_ofReal
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) T))
    (ae_of_all _ hf0)).symm

/-! ### `align2`: the same-sign pair -/

/-- Real form of `align2` (source l. 1317--1321): for `β ≥ 0` there is `C` with
`∫_{|u| ≤ 4ρ} e^{β g_λ(u)} (a(u)/ρ)^{2β} du ≤ C ρ^{2-β}` for all `0 < λ ≤ ρ`. -/
theorem exists_integral_closedBall_exp_mul_pow_two_mul_le {β : ℝ} (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ρ : ℝ, 0 < lam → lam ≤ ρ →
      ∫ u in Metric.closedBall (0 : ℂ) (4 * ρ),
          Real.exp (β * smearedKernel lam u) * (displacementScale lam u / ρ) ^ (2 * β) ≤
        C * ρ ^ (2 - β) := by
  obtain ⟨K, hK0, hK⟩ := exists_integral_closedBall_exp_mul_pow_le (β := β) (κ := 2 * β) hβ
    (by linarith)
  refine ⟨K + 2 * Real.pi * 4 ^ (2 + β) / (2 + β), by positivity, fun lam ρ hlam hρ => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
  have i2 : ∫ y in (2 * lam)..(4 * ρ), y ^ (1 - β + 2 * β) ≤ (4 * ρ) ^ (2 + β) / (2 + β) := by
    have := intervalIntegral_rpow_le_of_neg_one_lt (p := 1 - β + 2 * β) (s := 2 * lam)
      (t := 4 * ρ) (by linarith) (by positivity)
    rwa [show 1 - β + 2 * β + 1 = 2 + β by ring] at this
  have i1 : lam ^ (2 - β) * (lam / ρ) ^ (2 * β) ≤ ρ ^ (2 - β) := by
    have e1 : lam ^ (2 - β) * (lam / ρ) ^ (2 * β) = lam ^ (2 + β) / ρ ^ (2 * β) := by
      rw [Real.div_rpow hlam.le hρ0.le, ← mul_div_assoc, ← Real.rpow_add hlam,
        show 2 - β + 2 * β = 2 + β by ring]
    have e2 : ρ ^ (2 - β) = ρ ^ (2 + β) / ρ ^ (2 * β) := by
      rw [← Real.rpow_sub hρ0, show 2 + β - 2 * β = 2 - β by ring]
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hlam.le hρ (by positivity))
      (Real.rpow_nonneg hρ0.le _)
  have i3 : ρ ^ (-(2 * β)) * (4 * ρ) ^ (2 + β) = 4 ^ (2 + β) * ρ ^ (2 - β) := by
    rw [Real.mul_rpow (by norm_num) hρ0.le, mul_left_comm, ← Real.rpow_add hρ0,
      show -(2 * β) + (2 + β) = 2 - β by ring]
  calc _ ≤ K * lam ^ (2 - β) * (lam / ρ) ^ (2 * β) +
        2 * Real.pi * ρ ^ (-(2 * β)) * ∫ y in (2 * lam)..(4 * ρ), y ^ (1 - β + 2 * β) :=
        hK lam ρ hlam hρ
    _ ≤ K * ρ ^ (2 - β) +
        2 * Real.pi * ρ ^ (-(2 * β)) * ((4 * ρ) ^ (2 + β) / (2 + β)) := by
        rw [mul_assoc K]
        exact add_le_add (mul_le_mul_of_nonneg_left i1 hK0.le)
          (mul_le_mul_of_nonneg_left i2 (by positivity))
    _ = _ := by
        linear_combination (2 * Real.pi / (2 + β)) * i3

/-- `align2` (source l. 1317--1321), as a lintegral: for `β ≥ 2` there is `C` with
`∫_{|u| ≤ 4ρ} e^{β g_λ(u)} (a(u)/ρ)^{2β} du ≤ C ρ^{2-β}` for all `0 < λ ≤ ρ`. -/
theorem lintegral_sameSignPair_le {β : ℝ} (hβ : 2 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ρ : ℝ, 0 < lam → lam ≤ ρ →
      ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal
          (Real.exp (β * smearedKernel lam u) * (displacementScale lam u / ρ) ^ (2 * β)) ≤
        ENNReal.ofReal (C * ρ ^ (2 - β)) := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_closedBall_exp_mul_pow_two_mul_le (β := β) (by linarith)
  refine ⟨C, hC0, fun lam ρ hlam hρ => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
  rw [lintegral_closedBall_ofReal_eq
    (continuous_exp_mul_smearedKernel_mul_rpow hlam (by linarith))
    (fun u => mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (div_nonneg (displacementScale_pos hlam u).le hρ0.le) _))]
  exact ENNReal.ofReal_le_ofReal (hC lam ρ hlam hρ)

theorem isolatedScale_mul_isolatedTail {β : ℝ} (hβ : 2 ≤ β) {lam ρ : ℝ} (hlam : 0 < lam)
    (hl1 : lam ≤ Real.exp (-1)) (hρ : 0 < ρ) :
    isolatedScale β hβ lam * isolatedTail β hβ lam ρ = ρ ^ (2 - β) := by
  unfold isolatedScale isolatedTail
  split_ifs with h
  · subst h
    have := one_le_abs_log hlam hl1
    rw [sub_self, Real.rpow_zero]
    field_simp
  · have := rpow_neg_mul_div_rpow hlam hρ (β - 2)
    rwa [neg_sub] at this

/-- `align2` in the normalised form used in `pred3` (source l. 1317--1329): for `β ≥ 2` there is
`C` with, for `0 < λ ≤ e^{-1}` and `ρ ≥ λ`,
`∫_{|u| ≤ 4ρ} e^{β g_λ(u)} (a(u)/ρ)^{2β} du ≤ C 𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2})
  (ℓ^{-1} 1_{β=2} + (λ/ρ)^{β-2} 1_{β>2})`. -/
theorem lintegral_sameSignPair_le_normalized {β : ℝ} (hβ : 2 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ρ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → lam ≤ ρ →
      ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal
          (Real.exp (β * smearedKernel lam u) * (displacementScale lam u / ρ) ^ (2 * β)) ≤
        ENNReal.ofReal (C * dipoleConstant β hβ * isolatedScale β hβ lam *
          isolatedTail β hβ lam ρ) := by
  obtain ⟨C, hC0, hC⟩ := lintegral_sameSignPair_le hβ
  have hZ := dipoleConstant_pos β hβ
  refine ⟨C / dipoleConstant β hβ, by positivity, fun lam ρ hlam hl1 hρ => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
  refine (hC lam ρ hlam hρ).trans (le_of_eq ?_)
  congr 1
  rw [mul_assoc (C / dipoleConstant β hβ * dipoleConstant β hβ),
    isolatedScale_mul_isolatedTail hβ hlam hl1 hρ0, div_mul_cancel₀ _ hZ.ne']

/-! ### `align1`: the neutral pair -/

/-- The convexity bound `e^{C s²} ≤ 1 + (e^C - 1) s²` for `0 ≤ s ≤ 1` (source l. 1282). -/
theorem exp_mul_sq_le {C s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (C * s ^ 2) ≤ 1 + (Real.exp C - 1) * s ^ 2 := by
  have ht0 : 0 ≤ s ^ 2 := sq_nonneg s
  have ht1 : s ^ 2 ≤ 1 := pow_le_one₀ hs0 hs1
  have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ C) (sub_nonneg.2 ht1) ht0
    (by ring : 1 - s ^ 2 + s ^ 2 = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [mul_comm C]
  linarith only [h]

/-- The leading term of `align1`: for `β ≥ 2` there is `c > 0` with
`∫_{|u| ≤ 4ρ} e^{β g_λ(u)} du ≤ 𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}) (1 + c φ_β(ρ))`
(source l. 1283--1289 and 1299--1304: (3.20b) for `β > 2`, the explicit radial integral for
`β = 2`). -/
theorem exists_integral_closedBall_exp_le {β : ℝ} (hβ : 2 ≤ β) :
    ∃ c : ℝ, 0 < c ∧ ∀ lam ρ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → lam ≤ ρ →
      ∫ u in Metric.closedBall (0 : ℂ) (4 * ρ), Real.exp (β * smearedKernel lam u) ≤
        dipoleConstant β hβ * isolatedScale β hβ lam * (1 + c * isolatedPhi β hβ lam ρ) := by
  rcases hβ.eq_or_lt with h2 | h2
  · -- `β = 2`
    subst h2
    obtain ⟨K, hK0, hK⟩ := exists_integral_closedBall_exp_mul_pow_le (β := 2) (κ := 0)
      (by norm_num) le_rfl
    refine ⟨(K + 4 * Real.pi) / (2 * Real.pi), by positivity, fun lam ρ hlam hl1 hρ => ?_⟩
    have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
    have hℓ1 := one_le_abs_log hlam hl1
    have hℓ : 0 < |Real.log lam| := lt_of_lt_of_le one_pos hℓ1
    have hlog := log_eq_neg_abs_log hlam hl1
    have h := hK lam ρ hlam hρ
    simp only [Real.rpow_zero, mul_one, sub_self, neg_zero] at h
    rw [show (1 : ℝ) - 2 + 0 = -1 by norm_num,
      intervalIntegral_rpow_neg_one (by positivity) (by positivity)] at h
    have hl2 : Real.log (4 * ρ / (2 * lam)) ≤ 1 + |Real.log ρ| + |Real.log lam| := by
      rw [show 4 * ρ / (2 * lam) = 2 * (ρ / lam) by field_simp; ring,
        Real.log_mul (by norm_num) (by positivity), Real.log_div hρ0.ne' hlam.ne']
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2),
        le_abs_self (Real.log ρ), hlog]
    have hs : isolatedScale 2 hβ lam = |Real.log lam| := by simp [isolatedScale]
    have hp : isolatedPhi 2 hβ lam ρ = (1 + |Real.log ρ|) / |Real.log lam| := by
      simp [isolatedPhi]
    have hZ : dipoleConstant 2 hβ = 2 * Real.pi := by simp [dipoleConstant]
    rw [hs, hp, hZ]
    have hρ' := abs_nonneg (Real.log ρ)
    calc _ ≤ K + 2 * Real.pi * Real.log (4 * ρ / (2 * lam)) := h
      _ ≤ K + 2 * Real.pi * (1 + |Real.log ρ| + |Real.log lam|) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hl2 (by positivity))
      _ ≤ 2 * Real.pi * |Real.log lam| *
          (1 + (K + 4 * Real.pi) / (2 * Real.pi) * ((1 + |Real.log ρ|) / |Real.log lam|)) := by
          have e : 2 * Real.pi * |Real.log lam| *
              (1 + (K + 4 * Real.pi) / (2 * Real.pi) * ((1 + |Real.log ρ|) / |Real.log lam|)) =
              2 * Real.pi * |Real.log lam| + (K + 4 * Real.pi) * (1 + |Real.log ρ|) := by
            field_simp
          rw [e]
          linarith only [mul_nonneg hK0.le hρ', mul_nonneg Real.pi_pos.le hρ', Real.pi_pos]
  · -- `β > 2`
    refine ⟨1, one_pos, fun lam ρ hlam hl1 hρ => ?_⟩
    have hs : isolatedScale β hβ lam = lam ^ (2 - β) := by simp [isolatedScale, h2.ne']
    have hZ := dipoleConstant_pos β hβ
    have hφ := isolatedPhi_nonneg hβ hlam hρ
    calc ∫ u in Metric.closedBall (0 : ℂ) (4 * ρ), Real.exp (β * smearedKernel lam u)
        ≤ ∫ u : ℂ, Real.exp (β * smearedKernel lam u) :=
          setIntegral_le_integral (integrable_exp_smearedKernel h2 hlam)
            (ae_of_all _ fun u => (Real.exp_pos _).le)
      _ = dipoleConstant β hβ * isolatedScale β hβ lam := by
          rw [integral_exp_smearedKernel h2 hlam, hs]
      _ ≤ dipoleConstant β hβ * isolatedScale β hβ lam *
          (1 + 1 * isolatedPhi β hβ lam ρ) := by
          have : 0 ≤ dipoleConstant β hβ * isolatedScale β hβ lam := by
            rw [hs]
            positivity
          exact le_mul_of_one_le_right this (by linarith only [hφ])

theorem continuous_exp_mul_smearedKernel_mul_exp {β C lam ρ : ℝ} (hlam : 0 < lam) :
    Continuous fun u : ℂ => Real.exp (β * smearedKernel lam u) *
      Real.exp (C * (displacementScale lam u / ρ) ^ 2) :=
  (continuous_exp_mul_smearedKernel hlam).mul
    (((continuous_displacementScale lam).div_const ρ).pow 2 |>.const_mul C).rexp

/-- Real form of `align1` (source l. 1284--1289): for `β ≥ 2` and `C ≥ 0` there is `C' > 0` with,
for `0 < λ ≤ e^{-1}` and `ρ ≥ λ`,
`∫_{|u| ≤ 4ρ} e^{β g_λ(u)} e^{C (a(u)/ρ)²} du ≤ 𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}) (1 + C' φ_β(ρ))`. -/
theorem exists_integral_closedBall_exp_mul_exp_le {β : ℝ} (hβ : 2 ≤ β) {C : ℝ} (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ lam ρ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → lam ≤ ρ →
      ∫ u in Metric.closedBall (0 : ℂ) (4 * ρ), Real.exp (β * smearedKernel lam u) *
          Real.exp (C * (displacementScale lam u / ρ) ^ 2) ≤
        dipoleConstant β hβ * isolatedScale β hβ lam * (1 + C' * isolatedPhi β hβ lam ρ) := by
  obtain ⟨c, hc0, hc⟩ := exists_integral_closedBall_exp_le hβ
  obtain ⟨Cq, hq0, hq⟩ := exists_integral_closedBall_exp_mul_sq_le hβ
  have hZ := dipoleConstant_pos β hβ
  have hE : 0 ≤ Real.exp C - 1 := sub_nonneg.2 (Real.one_le_exp hC)
  refine ⟨c + (Real.exp C - 1) * Cq / dipoleConstant β hβ, by positivity, fun lam ρ hlam hl1 hρ => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
  have hsc := isolatedScale_pos hβ hlam hl1
  have hφ := isolatedPhi_nonneg hβ hlam hρ
  have hi1 : IntegrableOn (fun u : ℂ => Real.exp (β * smearedKernel lam u))
      (Metric.closedBall (0 : ℂ) (4 * ρ)) :=
    (continuous_exp_mul_smearedKernel hlam).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  have hi2 : IntegrableOn (fun u : ℂ => Real.exp (β * smearedKernel lam u) *
      (displacementScale lam u / ρ) ^ 2) (Metric.closedBall (0 : ℂ) (4 * ρ)) := by
    have : IntegrableOn (fun u : ℂ => Real.exp (β * smearedKernel lam u) *
        (displacementScale lam u / ρ) ^ (2 : ℝ)) (Metric.closedBall (0 : ℂ) (4 * ρ)) :=
      (continuous_exp_mul_smearedKernel_mul_rpow (β := β) (κ := 2) (ρ := ρ) hlam
        (by norm_num)).continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) (4 * ρ))
    simpa only [Real.rpow_two] using this
  have hi3 : IntegrableOn (fun u : ℂ => Real.exp (β * smearedKernel lam u) *
      Real.exp (C * (displacementScale lam u / ρ) ^ 2)) (Metric.closedBall (0 : ℂ) (4 * ρ)) :=
    (continuous_exp_mul_smearedKernel_mul_exp hlam).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  have step1 : ∫ u in Metric.closedBall (0 : ℂ) (4 * ρ), Real.exp (β * smearedKernel lam u) *
        Real.exp (C * (displacementScale lam u / ρ) ^ 2) ≤
      (∫ u in Metric.closedBall (0 : ℂ) (4 * ρ), Real.exp (β * smearedKernel lam u)) +
        (Real.exp C - 1) * ∫ u in Metric.closedBall (0 : ℂ) (4 * ρ),
          Real.exp (β * smearedKernel lam u) * (displacementScale lam u / ρ) ^ 2 := by
    rw [← integral_const_mul, ← integral_add hi1 (hi2.const_mul _)]
    refine setIntegral_mono_on hi3 (hi1.add (hi2.const_mul _)) measurableSet_closedBall ?_
    intro u hu
    have hu' : ‖u‖ ≤ 4 * ρ := by simpa using hu
    have hs0 : 0 ≤ displacementScale lam u / ρ :=
      div_nonneg (displacementScale_pos hlam u).le hρ0.le
    have hs1 : displacementScale lam u / ρ ≤ 1 :=
      (div_le_one hρ0).2 (displacementScale_le_of_norm_le hρ hu')
    have := exp_mul_sq_le (C := C) hs0 hs1
    have hex := Real.exp_pos (β * smearedKernel lam u)
    calc Real.exp (β * smearedKernel lam u) * Real.exp (C * (displacementScale lam u / ρ) ^ 2)
        ≤ Real.exp (β * smearedKernel lam u) *
          (1 + (Real.exp C - 1) * (displacementScale lam u / ρ) ^ 2) :=
        mul_le_mul_of_nonneg_left this hex.le
      _ = _ := by ring
  have m1 := hc lam ρ hlam hl1 hρ
  have m2 := hq lam ρ hlam hl1 hρ
  calc _ ≤ _ := step1
    _ ≤ dipoleConstant β hβ * isolatedScale β hβ lam * (1 + c * isolatedPhi β hβ lam ρ) +
        (Real.exp C - 1) * (Cq * isolatedScale β hβ lam * isolatedPhi β hβ lam ρ) :=
        add_le_add m1 (mul_le_mul_of_nonneg_left m2 hE)
    _ = _ := by
        field_simp
        ring

/-- **`align1`** (source l. 1284--1289): the radial integral of a neutral pair. For `β ≥ 2` and
`C ≥ 0` there is `C' > 0`, depending only on `β` and `C`, such that for `0 < λ ≤ e^{-1}` and
`ρ ≥ λ`,
`∫_{|u| ≤ 4ρ} e^{β g_λ(u)} e^{C (a(u)/ρ)²} du ≤ 𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}) (1 + C' φ_β(ρ))`
with `a(u) = (|u|/4) ∨ λ`. -/
theorem lintegral_neutralPair_le {β : ℝ} (hβ : 2 ≤ β) {C : ℝ} (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ lam ρ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → lam ≤ ρ →
      ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal
          (Real.exp (β * smearedKernel lam u) *
            Real.exp (C * (displacementScale lam u / ρ) ^ 2)) ≤
        ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam *
          (1 + C' * isolatedPhi β hβ lam ρ)) := by
  obtain ⟨C', hC'0, hC'⟩ := exists_integral_closedBall_exp_mul_exp_le hβ hC
  refine ⟨C', hC'0, fun lam ρ hlam hl1 hρ => ?_⟩
  rw [lintegral_closedBall_ofReal_eq (continuous_exp_mul_smearedKernel_mul_exp hlam)
    (fun u => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (hC' lam ρ hlam hl1 hρ)

/-! ### Weights with a cutoff: the tail beyond a disc -/

/-- For `β > 2`, `t ≥ 2λ` and a continuous weight `0 ≤ w ≤ 1`, the integral of `e^{β g_λ} w` over
`ℂ` is at most its integral over `B̄(0, t)` plus the exact tail `2π t^{2-β}/(β-2)` of `e^{β g_λ}`
outside the disc (source l. 2100, "we integrate the second over `ℝ²`"). -/
theorem lintegral_le_closedBall_add_tail {β lam t : ℝ} (hβ : 2 < β) (hlam : 0 < lam)
    (ht : 2 * lam ≤ t) {w : ℂ → ℝ} (hwc : Continuous w) (hw0 : ∀ u, 0 ≤ w u)
    (hw1 : ∀ u, w u ≤ 1) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (β * smearedKernel lam u) * w u) ≤
      ENNReal.ofReal (∫ u in Metric.closedBall (0 : ℂ) t,
        Real.exp (β * smearedKernel lam u) * w u) +
        ENNReal.ofReal (2 * Real.pi * (t ^ (2 - β) / (β - 2))) := by
  rw [← lintegral_add_compl _ (Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := t)).measurableSet]
  refine add_le_add (le_of_eq (lintegral_closedBall_ofReal_eq
    ((continuous_exp_mul_smearedKernel hlam).mul hwc)
    (fun u => mul_nonneg (Real.exp_pos _).le (hw0 u)) t)) ?_
  calc ∫⁻ u in (Metric.closedBall (0 : ℂ) t)ᶜ,
        ENNReal.ofReal (Real.exp (β * smearedKernel lam u) * w u)
      ≤ ∫⁻ u in (Metric.closedBall (0 : ℂ) t)ᶜ,
        ENNReal.ofReal (Real.exp (β * smearedKernel lam u)) :=
        lintegral_mono fun u => ENNReal.ofReal_le_ofReal
          (mul_le_of_le_one_right (Real.exp_pos _).le (hw1 u))
    _ ≤ ∫⁻ u in (Metric.ball (0 : ℂ) t)ᶜ, ENNReal.ofReal (Real.exp (β * smearedKernel lam u)) :=
        lintegral_mono_set (compl_subset_compl.2 Metric.ball_subset_closedBall)
    _ = ENNReal.ofReal (∫ u in (Metric.ball (0 : ℂ) t)ᶜ, Real.exp (β * smearedKernel lam u)) :=
        (ofReal_integral_eq_lintegral_ofReal
          (integrable_exp_smearedKernel hβ hlam).integrableOn
          (ae_of_all _ fun u => (Real.exp_pos _).le)).symm
    _ = _ := by rw [integral_compl_ball_exp_smearedKernel hβ hlam ht]

theorem continuous_displacementScale_div_max {lam : ℝ} (m : ℝ) (hlam : 0 < lam) :
    Continuous fun u : ℂ => displacementScale lam u / max m (displacementScale lam u) :=
  (continuous_displacementScale lam).div (continuous_const.max (continuous_displacementScale lam))
    fun u => (lt_of_lt_of_le (displacementScale_pos hlam u) (le_max_right _ _)).ne'

/-- The cut-off same-sign factor (source l. 2092--2100) over the whole plane: for `β > 2` there is
`C` with, for `0 < λ ≤ m`,
`∫_{ℂ} e^{β g_λ(u)} (a(u) / (m ∨ a(u)))^{2β} du ≤ C m^{2-β}`. -/
theorem lintegral_sameSignPair_cutoff_le_univ {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam m : ℝ, 0 < lam → lam ≤ m →
      ∫⁻ u : ℂ, ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
          (displacementScale lam u / max m (displacementScale lam u)) ^ (2 * β)) ≤
        ENNReal.ofReal (C * m ^ (2 - β)) := by
  obtain ⟨C0, hC0, h0⟩ := exists_integral_closedBall_exp_mul_pow_two_mul_le (β := β) (by linarith)
  refine ⟨C0 + 2 * Real.pi * 4 ^ (2 - β) / (β - 2), by
    have : 0 < β - 2 := by linarith
    positivity, fun lam m hlam hm => ?_⟩
  have hm0 : 0 < m := lt_of_lt_of_le hlam hm
  have hb : 0 ≤ 2 * β := by linarith
  have hbase0 : ∀ u : ℂ, 0 ≤ displacementScale lam u / max m (displacementScale lam u) :=
    fun u => div_nonneg (displacementScale_pos hlam u).le (le_trans (displacementScale_pos hlam u).le
      (le_max_right _ _))
  have hbase1 : ∀ u : ℂ, displacementScale lam u / max m (displacementScale lam u) ≤ 1 :=
    fun u => (div_le_one (lt_of_lt_of_le (displacementScale_pos hlam u) (le_max_right _ _))).2
      (le_max_right _ _)
  have hsplit := lintegral_le_closedBall_add_tail (β := β) (lam := lam) (t := 4 * m) hβ hlam
    (by linarith)
    (w := fun u => (displacementScale lam u / max m (displacementScale lam u)) ^ (2 * β))
    ((continuous_displacementScale_div_max m hlam).rpow_const fun _ => Or.inr hb)
    (fun u => Real.rpow_nonneg (hbase0 u) _)
    (fun u => Real.rpow_le_one (hbase0 u) (hbase1 u) hb)
  refine hsplit.trans ?_
  have hball : ∫ u in Metric.closedBall (0 : ℂ) (4 * m), Real.exp (β * smearedKernel lam u) *
      (displacementScale lam u / max m (displacementScale lam u)) ^ (2 * β) =
      ∫ u in Metric.closedBall (0 : ℂ) (4 * m), Real.exp (β * smearedKernel lam u) *
        (displacementScale lam u / m) ^ (2 * β) := by
    refine setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet fun u hu => ?_
    have hu' : ‖u‖ ≤ 4 * m := by simpa using hu
    rw [max_eq_left (displacementScale_le_of_norm_le hm hu')]
  have htail : 2 * Real.pi * ((4 * m) ^ (2 - β) / (β - 2)) =
      2 * Real.pi * 4 ^ (2 - β) / (β - 2) * m ^ (2 - β) := by
    rw [Real.mul_rpow (by norm_num) hm0.le]
    ring
  rw [hball, htail, ← ENNReal.ofReal_add]
  · refine ENNReal.ofReal_le_ofReal ?_
    have := h0 lam m hlam hm
    linarith
  · exact integral_nonneg fun u => mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (div_nonneg (displacementScale_pos hlam u).le hm0.le) _)
  · have : 0 < β - 2 := by linarith
    positivity

/-- **Theorem 2, Step 3** (source l. 2092--2100): the cut-off same-sign radial factor. For `β > 2`
there is `C` with, for `0 < λ ≤ ρ` and `λ ≤ γ`,
`∫_{|u| ≤ 4ρ} e^{β g_λ(u)} (a(u) / ((ρ ∧ γ) ∨ a(u)))^{2β} du
  ≤ C 𝒵_β λ^{2-β} ((λ/ρ)^{β-2} + (λ/γ)^{β-2})`. -/
theorem lintegral_sameSignPair_cutoff_le {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ρ γ : ℝ, 0 < lam → lam ≤ ρ → lam ≤ γ →
      ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal
          (Real.exp (β * smearedKernel lam u) *
            (displacementScale lam u / max (min ρ γ) (displacementScale lam u)) ^ (2 * β)) ≤
        ENNReal.ofReal (C * dipoleConstant β hβ.le * lam ^ (2 - β) *
          ((lam / ρ) ^ (β - 2) + (lam / γ) ^ (β - 2))) := by
  obtain ⟨C, hC0, hC⟩ := lintegral_sameSignPair_cutoff_le_univ hβ
  have hZ := dipoleConstant_pos β hβ.le
  refine ⟨C / dipoleConstant β hβ.le, by positivity, fun lam ρ γ hlam hρ hγ => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
  have hγ0 : 0 < γ := lt_of_lt_of_le hlam hγ
  have hm : lam ≤ min ρ γ := le_min hρ hγ
  have hm0 : 0 < min ρ γ := lt_of_lt_of_le hlam hm
  refine (setLIntegral_le_lintegral _ _).trans ((hC lam (min ρ γ) hlam hm).trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  have e : lam ^ (2 - β) * (lam / min ρ γ) ^ (β - 2) = (min ρ γ) ^ (2 - β) := by
    have := rpow_neg_mul_div_rpow hlam hm0 (β - 2)
    rwa [neg_sub] at this
  have hle : (lam / min ρ γ) ^ (β - 2) ≤ (lam / ρ) ^ (β - 2) + (lam / γ) ^ (β - 2) := by
    rcases min_choice ρ γ with h | h
    · rw [h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
    · rw [h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
  calc C * min ρ γ ^ (2 - β) = C / dipoleConstant β hβ.le * dipoleConstant β hβ.le *
        (lam ^ (2 - β) * (lam / min ρ γ) ^ (β - 2)) := by
        rw [e, div_mul_cancel₀ _ hZ.ne']
    _ ≤ C / dipoleConstant β hβ.le * dipoleConstant β hβ.le *
        (lam ^ (2 - β) * ((lam / ρ) ^ (β - 2) + (lam / γ) ^ (β - 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by positivity)) (by positivity)
    _ = _ := by ring

/-- **Theorem 2, Step 4** (source l. 2143--2150): the radial contribution of the tilt for a pair
in `I ∖ I'`. For `β > 2` there is `C` with, for `0 < λ ≤ e^{-1}` and `λ ≤ γ`,
`∫_{ℂ} e^{β g_λ(u)} ((a(u)/γ)² ∧ 1) du ≤ C 𝒵_β λ^{2-β} φ_β(γ)`.
The source assumes `2λ ≤ γ ≤ 1`; only `λ ≤ γ` is needed. -/
theorem lintegral_neutralTilt_le {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam γ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → lam ≤ γ →
      ∫⁻ u : ℂ, ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
          min ((displacementScale lam u / γ) ^ 2) 1) ≤
        ENNReal.ofReal (C * dipoleConstant β hβ.le * isolatedScale β hβ.le lam *
          isolatedPhi β hβ.le lam γ) := by
  obtain ⟨Cq, hq0, hq⟩ := exists_integral_closedBall_exp_mul_sq_le hβ.le
  have hZ := dipoleConstant_pos β hβ.le
  have hb : 0 < β - 2 := by linarith
  refine ⟨(Cq + 2 * Real.pi * 4 ^ (2 - β) / (β - 2)) / dipoleConstant β hβ.le, by positivity,
    fun lam γ hlam hl1 hγ => ?_⟩
  have hγ0 : 0 < γ := lt_of_lt_of_le hlam hγ
  have hs : isolatedScale β hβ.le lam = lam ^ (2 - β) := by simp [isolatedScale, hβ.ne']
  have hφ := isolatedPhi_nonneg hβ.le hlam hγ
  have hw0 : ∀ u : ℂ, 0 ≤ min ((displacementScale lam u / γ) ^ 2) 1 :=
    fun u => le_min (sq_nonneg _) zero_le_one
  have hsplit := lintegral_le_closedBall_add_tail (β := β) (lam := lam) (t := 4 * γ) hβ hlam
    (by linarith) (w := fun u => min ((displacementScale lam u / γ) ^ 2) 1)
    (((continuous_displacementScale lam).div_const γ).pow 2 |>.min continuous_const)
    hw0 (fun u => min_le_right _ _)
  refine hsplit.trans ?_
  have hball : ∫ u in Metric.closedBall (0 : ℂ) (4 * γ), Real.exp (β * smearedKernel lam u) *
      min ((displacementScale lam u / γ) ^ 2) 1 =
      ∫ u in Metric.closedBall (0 : ℂ) (4 * γ), Real.exp (β * smearedKernel lam u) *
        (displacementScale lam u / γ) ^ 2 := by
    refine setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet fun u hu => ?_
    have hu' : ‖u‖ ≤ 4 * γ := by simpa using hu
    have h1 : displacementScale lam u / γ ≤ 1 :=
      (div_le_one hγ0).2 (displacementScale_le_of_norm_le hγ hu')
    have h2 : 0 ≤ displacementScale lam u / γ := div_nonneg (displacementScale_pos hlam u).le hγ0.le
    simp only [min_eq_left (pow_le_one₀ h2 h1)]
  have e : lam ^ (2 - β) * (lam / γ) ^ (β - 2) = γ ^ (2 - β) := by
    have := rpow_neg_mul_div_rpow hlam hγ0 (β - 2)
    rwa [neg_sub] at this
  have htail : 2 * Real.pi * ((4 * γ) ^ (2 - β) / (β - 2)) =
      2 * Real.pi * 4 ^ (2 - β) / (β - 2) * (lam ^ (2 - β) * (lam / γ) ^ (β - 2)) := by
    rw [e, Real.mul_rpow (by norm_num) hγ0.le]
    ring
  have hq' := hq lam γ hlam hl1 hγ
  have hphi := rpow_div_le_isolatedPhi hβ.le hβ hlam hγ
  rw [hball, htail, ← ENNReal.ofReal_add]
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [hs] at hq' ⊢
    have hl : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
    calc _ ≤ Cq * lam ^ (2 - β) * isolatedPhi β hβ.le lam γ +
          2 * Real.pi * 4 ^ (2 - β) / (β - 2) * (lam ^ (2 - β) * isolatedPhi β hβ.le lam γ) :=
          add_le_add hq' (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hphi hl.le)
            (by positivity))
      _ = _ := by
          field_simp
  · exact integral_nonneg fun u => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  · positivity

end TwoComponentCoulomb

end
