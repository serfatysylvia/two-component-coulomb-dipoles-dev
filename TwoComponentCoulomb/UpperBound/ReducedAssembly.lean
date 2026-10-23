/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.ReducedPartitionFunction
public import TwoComponentCoulomb.PhaseSpace.Placement
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TwoComponentCoulomb.Integrals.GaussianMass
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Integrals.Stirling
import TwoComponentCoulomb.UpperBound.ReducedConstruction
import TwoComponentCoulomb.UpperBound.ReducedMatching

/-!
# Assembly of Lemma 3.5 (free energy of the reduced dipole model)

Source: Lemma 3.5 (`lemma:part nn`, l. 870–952). The matching upper bounds
(`UpperBound/ReducedMatching.lean`) and the placement lower bounds
(`UpperBound/ReducedConstruction.lean`) are turned, by Stirling's formula and elementary
estimates, into the two-sided logarithmic expansion of the statement: positivity and finiteness of
`𝒦_{N,β}^λ`, and `|log 𝒦 - M| ≤ C (N ω̄_λ + log (N + 1))` with
`M = 2 N log N + N ((2 - β) log λ 1_{β > 2} + log |log λ| 1_{β = 2} + log 𝒵_β - 1)`,
`ω̄_λ = |log λ|^{-1/2}` for `β = 2` and `ω̄_λ = λ^{min ((β - 2)/2, 1)}` for `β > 2`.

* `log_factorial_le` : the upper Stirling bound `log N! ≤ N log N - N + 1 + log N`.
* `ReducedAssembly.sandwich_log_toReal` : a two-sided bound `e^{M - C₂ W} ≤ 𝒦 ≤ e^{M + C₁ W}`
  gives positivity, finiteness and `|log 𝒦 - M| ≤ (C₁ + C₂) W`.
* `ReducedAssembly.factorial_mul_pow_mul_pow_mul_exp_le` and
  `ReducedAssembly.ofReal_exp_le_of_construction` : the upper and lower Stirling assembly steps
  (the latter for the placement construction with `t ≤ 1/16`).
* `ReducedAssembly.reducedPartitionFunction_le_exp_of_two_lt`,
  `ReducedAssembly.exp_le_reducedPartitionFunction_of_two_lt` : the two bounds for `β > 2`
  (source l. 926–951), with `t = λ^{(β-2)/β}` for the lower one.
* `ReducedAssembly.reducedPartitionFunction_two_le_exp`,
  `ReducedAssembly.exp_le_reducedPartitionFunction_two` : the two bounds for `β = 2`
  (source l. 899–923), with `ℓ = |log λ|` and `t = ℓ^{-1/2}` for the lower one.
* `lemma_3_5_of_two_lt` : the frozen expression of Lemma 3.5 for `β > 2`.
* `lemma_3_5_two` : the frozen expression of Lemma 3.5 for `β = 2`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Nat

namespace TwoComponentCoulomb

/-! ### Elementary estimates -/

/-- **Stirling upper bound**: for `N ≥ 1`, `log N! ≤ N log N - N + 1 + log N`. -/
theorem log_factorial_le {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N ! : ℝ) ≤ N * Real.log N - N + 1 + Real.log N := by
  have h := log_factorial_stirling_le hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  linarith only [h, hlog]

/-- `log (N + 1) ≥ 1` for `N ≥ 2`. -/
theorem one_le_log_add_one {N : ℕ} (hN : 2 ≤ N) : 1 ≤ Real.log ((N : ℝ) + 1) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.le_log_iff_exp_le (by linarith only [hN'])]
  have := Real.exp_one_lt_d9
  linarith only [this, hN']

/-- `log N ≤ log (N + 1)` for `N ≥ 1`. -/
theorem log_le_log_add_one {N : ℕ} (hN : 1 ≤ N) : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact Real.log_le_log (by linarith only [hN']) (by linarith only [hN'])

/-! ### Helper lemmas -/

namespace ReducedAssembly

/-- The sandwich step: if `e^{M - C₂ W} ≤ 𝒦 ≤ e^{M + C₁ W}` then `𝒦` is positive and finite and
`|log 𝒦 - M| ≤ (C₁ + C₂) W`. -/
theorem sandwich_log_toReal {K : ℝ≥0∞} {M W C₁ C₂ : ℝ} (hW : 0 ≤ W) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h1 : ENNReal.ofReal (Real.exp (M - C₂ * W)) ≤ K)
    (h2 : K ≤ ENNReal.ofReal (Real.exp (M + C₁ * W))) :
    0 < K ∧ K < ∞ ∧ |Real.log K.toReal - M| ≤ (C₁ + C₂) * W := by
  have hpos : 0 < K := lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos _)) h1
  have hfin : K < ∞ := lt_of_le_of_lt h2 ENNReal.ofReal_lt_top
  refine ⟨hpos, hfin, ?_⟩
  have hKne : K ≠ ∞ := hfin.ne
  have ha : Real.exp (M - C₂ * W) ≤ K.toReal := by
    have := ENNReal.toReal_mono hKne h1
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have hb : K.toReal ≤ Real.exp (M + C₁ * W) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have hKpos : 0 < K.toReal := lt_of_lt_of_le (Real.exp_pos _) ha
  have hlo := Real.log_le_log (Real.exp_pos _) ha
  have hhi := Real.log_le_log hKpos hb
  rw [Real.log_exp] at hlo hhi
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi, mul_nonneg hC₁ hW, mul_nonneg hC₂ hW]

/-- For `a, δ > 0` there is `μ > 0` with `λ^a ≤ δ` for all `0 < λ < μ` (namely `μ = δ^{1/a}`). -/
theorem exists_pos_rpow_le {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ lam : ℝ, 0 < lam → lam < μ → lam ^ a ≤ δ := by
  refine ⟨δ ^ (1 / a), Real.rpow_pos_of_pos hδ _, fun lam hlam hlt => ?_⟩
  calc lam ^ a ≤ (δ ^ (1 / a)) ^ a := Real.rpow_le_rpow hlam.le hlt.le ha.le
    _ = δ := by rw [← Real.rpow_mul hδ.le, one_div_mul_cancel ha.ne', Real.rpow_one]

/-! ### The upper-bound assembly -/

/-- The factorial, `N^N`, `A^N` and the exponential factor of the matching bound are at most the
exponential of `2 N log N + N (log A - 1) + (1 + log N) + F`. -/
theorem factorial_mul_pow_mul_pow_mul_exp_le {N : ℕ} (hN : 1 ≤ N) {A : ℝ} (hA : 0 < A) (F : ℝ) :
    (N ! : ℝ) * (N : ℝ) ^ N * A ^ N * Real.exp F ≤
      Real.exp (2 * N * Real.log N + N * (Real.log A - 1) + (1 + Real.log N) + F) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hfpos : (0 : ℝ) < (N ! : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have h1 : (N ! : ℝ) ≤ Real.exp ((N : ℝ) * Real.log N - N + 1 + Real.log N) := by
    calc (N ! : ℝ) = Real.exp (Real.log (N ! : ℝ)) := (Real.exp_log hfpos).symm
      _ ≤ _ := Real.exp_le_exp.2 (log_factorial_le hN)
  have h2 : Real.exp ((N : ℝ) * Real.log N) = (N : ℝ) ^ N := by
    rw [Real.exp_nat_mul, Real.exp_log hN0]
  have h3 : Real.exp ((N : ℝ) * Real.log A) = A ^ N := by
    rw [Real.exp_nat_mul, Real.exp_log hA]
  have h4 : Real.exp (2 * N * Real.log N + N * (Real.log A - 1) + (1 + Real.log N) + F) =
      Real.exp ((N : ℝ) * Real.log N - N + 1 + Real.log N) * Real.exp ((N : ℝ) * Real.log N) *
        Real.exp ((N : ℝ) * Real.log A) * Real.exp F := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h4, h2, h3]
  gcongr

/-! ### The lower-bound assembly -/

/-- The assembly step for a placement construction: if
`N! · vol(H) · A^N ≤ 𝒦` with `H = placementSet N N t (4 t)`, `0 < t ≤ 1/16`, then
`exp (2 N log N + N (log A - 1) - E) ≤ 𝒦` whenever `E ≥ 8 t √N + 16 π N t²`. -/
theorem ofReal_exp_le_of_construction {N : ℕ} (hN : 1 ≤ N) {t A E : ℝ} {K : ℝ≥0∞} (ht : 0 < t)
    (ht16 : t ≤ 1 / 16) (hA : 0 < A) (hE : 8 * t * Real.sqrt N + 16 * Real.pi * N * t ^ 2 ≤ E)
    (hcons : ENNReal.ofReal (N ! : ℝ) * volume (placementSet N N t (4 * t)) *
      ENNReal.ofReal A ^ N ≤ K) :
    ENNReal.ofReal (Real.exp (2 * N * Real.log N + N * (Real.log A - 1) - E)) ≤ K := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_iff]
    refine ⟨hN0.le, ?_⟩
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact le_self_pow₀ this two_ne_zero
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  set E₀ := 8 * t * Real.sqrt N + Real.pi * N * (4 * t) ^ 2 with hE₀
  have hE₀E : E₀ ≤ E := by
    have : E₀ = 8 * t * Real.sqrt N + 16 * Real.pi * N * t ^ 2 := by rw [hE₀]; ring
    linarith only [this, hE]
  have hcond : 4 * t * Real.sqrt N + N * Real.pi * (4 * t) ^ 2 ≤ N / 2 := by
    have e1 : 4 * t * Real.sqrt N ≤ 4 * t * N := by gcongr
    have e2 : 4 * t * N ≤ N / 4 := by
      linarith only [mul_le_mul_of_nonneg_right ht16 hN0.le]
    have e3 : (N : ℝ) * Real.pi * (4 * t) ^ 2 ≤ (N : ℝ) * 4 * (1 / 4) ^ 2 := by
      have : (4 * t) ^ 2 ≤ (1 / 4) ^ 2 := by gcongr; linarith only [ht16]
      calc (N : ℝ) * Real.pi * (4 * t) ^ 2 ≤ (N : ℝ) * 4 * (4 * t) ^ 2 := by gcongr
        _ ≤ (N : ℝ) * 4 * (1 / 4) ^ 2 := by gcongr
    linarith only [e1, e2, e3]
  have hvol := volume_placementSet_ge (N := N) (a := t) (b := 4 * t) ht.le (by positivity) hcond
  have hEneg : -8 * t * Real.sqrt N - Real.pi * N * (4 * t) ^ 2 = -E₀ := by rw [hE₀]; ring
  rw [hEneg] at hvol
  refine le_trans ?_ hcons
  calc ENNReal.ofReal (Real.exp (2 * N * Real.log N + N * (Real.log A - 1) - E))
      ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N + N * (Real.log A - 1) - E₀)) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith only [hE₀E]))
    _ ≤ ENNReal.ofReal ((N ! : ℝ) * (N : ℝ) ^ N * A ^ N * Real.exp (-E₀)) :=
        ofReal_exp_le_of_factorial_mul hN hA E₀
    _ = ENNReal.ofReal (N ! : ℝ) * ENNReal.ofReal ((N : ℝ) ^ N * Real.exp (-E₀)) *
          ENNReal.ofReal A ^ N := by
        have : (N ! : ℝ) * (N : ℝ) ^ N * A ^ N * Real.exp (-E₀) =
            (N ! : ℝ) * ((N : ℝ) ^ N * Real.exp (-E₀)) * A ^ N := by ring
        rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow hA.le]
    _ ≤ ENNReal.ofReal (N ! : ℝ) * volume (placementSet N N t (4 * t)) *
          ENNReal.ofReal A ^ N := by gcongr

/-! ### The case `β > 2` -/

/-- `log (1 - y) ≥ -2 y` for `0 ≤ y ≤ 1/2`. -/
theorem neg_two_mul_le_log_one_sub {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) :
    -(2 * y) ≤ Real.log (1 - y) := by
  have h := exp_neg_two_mul_le_one_sub h0 h1
  have := Real.log_le_log (Real.exp_pos _) h
  rwa [Real.log_exp] at this

/-- For `β > 2`: `min ((β - 2)/2) 1 ≤ 2 (β - 2) / β`, so that `t² = λ^{2(β-2)/β} ≤ λ^{ω}`. -/
theorem min_le_two_mul_sub_div {β : ℝ} (hβ : 2 < β) :
    min ((β - 2) / 2) 1 ≤ 2 * (β - 2) / β := by
  have hβ0 : 0 < β := by linarith
  rcases le_total β 4 with h | h
  · refine (min_le_left _ _).trans ?_
    rw [le_div_iff₀ hβ0]
    linarith only [mul_nonneg (by linarith : (0 : ℝ) ≤ β - 2) (by linarith : (0 : ℝ) ≤ 4 - β)]
  · refine (min_le_right _ _).trans ?_
    rw [le_div_iff₀ hβ0]
    linarith only [h]

/-- **Lemma 3.5, upper bound for `β > 2`** (source l. 907–911, 926–931), in the form of the
frozen statement: `𝒦 ≤ exp (M + C (N λ^{min((β-2)/2, 1)} + log (N+1)))`. -/
theorem reducedPartitionFunction_le_exp_of_two_lt {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      reducedPartitionFunction N β lam ≤ ENNReal.ofReal (Real.exp (
        2 * N * Real.log N + N * ((2 - β) * Real.log lam
          + (Real.log (dipoleConstant β hβ.le) - 1))
        + C * (N * lam ^ min ((β - 2) / 2) 1 + Real.log (N + 1)))) := by
  have hZ : 0 < dipoleConstant β hβ.le := dipoleConstant_pos β hβ.le
  set Z := dipoleConstant β hβ.le with hZdef
  have hsZ : 0 < Real.sqrt Z := Real.sqrt_pos.2 hZ
  refine ⟨2 + 2 / Real.sqrt Z, by positivity, fun N hN lam hlam hle1 => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hA : 0 < Z * lam ^ (2 - β) := mul_pos hZ (Real.rpow_pos_of_pos hlam _)
  refine (reducedPartitionFunction_le_of_gt_two hβ hlam).trans (ENNReal.ofReal_le_ofReal ?_)
  refine (factorial_mul_pow_mul_pow_mul_exp_le hN1 hA _).trans (Real.exp_le_exp.2 ?_)
  have hlogA : Real.log (Z * lam ^ (2 - β)) = Real.log Z + (2 - β) * Real.log lam := by
    rw [Real.log_mul hZ.ne' (Real.rpow_pos_of_pos hlam _).ne', Real.log_rpow hlam]
  -- the exponential factor
  have hsA : Real.sqrt (Z * lam ^ (2 - β)) = Real.sqrt Z * (lam ^ ((β - 2) / 2))⁻¹ := by
    rw [Real.sqrt_mul hZ.le, Real.sqrt_eq_rpow (lam ^ (2 - β)), ← Real.rpow_mul hlam.le,
      ← Real.rpow_neg hlam.le]
    congr 2
    ring
  have hpw : 0 < lam ^ ((β - 2) / 2) := Real.rpow_pos_of_pos hlam _
  have hF : 2 * (N : ℝ) / Real.sqrt (Z * lam ^ (2 - β)) =
      2 / Real.sqrt Z * (N * lam ^ ((β - 2) / 2)) := by
    rw [hsA]
    field_simp
  have hlam_le : lam ^ ((β - 2) / 2) ≤ lam ^ min ((β - 2) / 2) 1 :=
    Real.rpow_le_rpow_of_exponent_ge hlam hle1 (min_le_left _ _)
  have hP : 0 ≤ (N : ℝ) * lam ^ min ((β - 2) / 2) 1 := by positivity
  have hF' : 2 * (N : ℝ) / Real.sqrt (Z * lam ^ (2 - β)) ≤
      2 / Real.sqrt Z * ((N : ℝ) * lam ^ min ((β - 2) / 2) 1) := by
    rw [hF]
    gcongr
  have hlog1 := one_le_log_add_one hN
  have hlog2 := log_le_log_add_one hN1
  have hQ : 0 ≤ Real.log ((N : ℝ) + 1) := by linarith only [hlog1]
  have hcoef : 0 ≤ 2 / Real.sqrt Z := by positivity
  rw [hlogA]
  have e1 : 2 / Real.sqrt Z * ((N : ℝ) * lam ^ min ((β - 2) / 2) 1) ≤
      2 / Real.sqrt Z * ((N : ℝ) * lam ^ min ((β - 2) / 2) 1 + Real.log ((N : ℝ) + 1)) := by
    gcongr
    linarith only [hQ]
  have e2 : 1 + Real.log (N : ℝ) ≤
      2 * ((N : ℝ) * lam ^ min ((β - 2) / 2) 1 + Real.log ((N : ℝ) + 1)) := by
    linarith only [hlog1, hlog2, hP]
  have e3 : N * (Real.log Z + (2 - β) * Real.log lam - 1) =
      N * ((2 - β) * Real.log lam + (Real.log Z - 1)) := by ring
  have e4 : (2 + 2 / Real.sqrt Z) * ((N : ℝ) * lam ^ min ((β - 2) / 2) 1 + Real.log ((N : ℝ) + 1)) =
      2 * ((N : ℝ) * lam ^ min ((β - 2) / 2) 1 + Real.log ((N : ℝ) + 1)) +
        2 / Real.sqrt Z * ((N : ℝ) * lam ^ min ((β - 2) / 2) 1 + Real.log ((N : ℝ) + 1)) := by
    ring
  rw [e4]
  linarith only [hF', e1, e2, e3]

/-- The radii of the `β > 2` construction (source l. 936, 946): for `t = λ^{(β-2)/β}` one has
`t² = (λ/t)^{β-2} = λ^{2(β-2)/β}`, and `2λ ≤ t` as soon as `λ^{2/β} ≤ 1/2`. -/
theorem radius_rpow_identities {β lam : ℝ} (hβ : 2 < β) (hlam : 0 < lam)
    (h2 : lam ^ (2 / β) ≤ 1 / 2) :
    2 * lam ≤ lam ^ ((β - 2) / β) ∧ (lam ^ ((β - 2) / β)) ^ 2 = lam ^ (2 * (β - 2) / β) ∧
      (lam / lam ^ ((β - 2) / β)) ^ (β - 2) = lam ^ (2 * (β - 2) / β) := by
  have hβ0 : 0 < β := by linarith
  have h1 : lam / lam ^ ((β - 2) / β) = lam ^ (2 / β) := by
    calc lam / lam ^ ((β - 2) / β) = lam ^ (1 : ℝ) / lam ^ ((β - 2) / β) := by rw [Real.rpow_one]
      _ = lam ^ ((1 : ℝ) - (β - 2) / β) := (Real.rpow_sub hlam 1 _).symm
      _ = lam ^ (2 / β) := by
        congr 1
        field_simp
        ring
  refine ⟨?_, ?_, ?_⟩
  · have h3 : lam = lam ^ (2 / β) * lam ^ ((β - 2) / β) := by
      rw [← Real.rpow_add hlam]
      conv_lhs => rw [← Real.rpow_one lam]
      congr 1
      field_simp
      ring
    have h4 : 0 < lam ^ ((β - 2) / β) := Real.rpow_pos_of_pos hlam _
    linarith only [mul_le_mul_of_nonneg_right h2 h4.le, h3]
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    congr 1
    push_cast
    ring
  · rw [h1, ← Real.rpow_mul hlam.le]
    congr 1
    field_simp

/-- The elementary estimate `8 t √N ≤ 4 (N t² + 1)` for the volume error of the placement. -/
theorem placement_error_le (N : ℕ) {t x : ℝ} (hx : t ^ 2 = x) :
    8 * t * Real.sqrt N + 16 * Real.pi * N * x ≤ (4 + 16 * Real.pi) * N * x + 4 := by
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have h := sq_nonneg (Real.sqrt N * t - 1)
  have h2 : Real.sqrt N ^ 2 * t ^ 2 = N * t ^ 2 := by rw [hsq]
  subst hx
  linarith only [h, h2]

/-- The arithmetic of the exponent in the `β > 2` lower bound. -/
theorem two_lt_lower_arith {N β L lZ C₀ x y Q lA : ℝ} (hN : 0 < N) (hC₀ : 0 < C₀) (hx0 : 0 ≤ x)
    (hxy : x ≤ y) (hQ : 1 ≤ Q) (hlogA : lZ + (2 - β) * L - 2 * C₀ * x ≤ lA) :
    N * ((2 - β) * L + (lZ - 1)) - (2 * C₀ + 16 * Real.pi + 8) * (N * y + Q) ≤
      N * (lA - 1) - ((4 + 16 * Real.pi) * N * x + 4) := by
  have h1 : N * (lZ + (2 - β) * L - 2 * C₀ * x) ≤ N * lA := mul_le_mul_of_nonneg_left hlogA hN.le
  have hcpos : 0 ≤ 2 * C₀ + 16 * Real.pi + 4 := by positivity
  have h2 : (2 * C₀ + 16 * Real.pi + 4) * (N * x) ≤ (2 * C₀ + 16 * Real.pi + 4) * (N * y) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxy hN.le) hcpos
  have h3 : 0 ≤ N * y := mul_nonneg hN.le (hx0.trans hxy)
  have h4 : (2 * C₀ + 16 * Real.pi + 8) * 1 ≤ (2 * C₀ + 16 * Real.pi + 8) * Q :=
    mul_le_mul_of_nonneg_left hQ (by positivity)
  linarith [Real.pi_pos]

/-- **Lemma 3.5, lower bound for `β > 2`** (source l. 932–951), in the form of the frozen
statement, with `t = λ^{(β-2)/β}`. -/
theorem exp_le_reducedPartitionFunction_of_two_lt {β : ℝ} (hβ : 2 < β) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ENNReal.ofReal (Real.exp (
        2 * N * Real.log N + N * ((2 - β) * Real.log lam
          + (Real.log (dipoleConstant β hβ.le) - 1))
        - C * (N * lam ^ min ((β - 2) / 2) 1 + Real.log (N + 1)))) ≤
        reducedPartitionFunction N β lam := by
  have hZ : 0 < dipoleConstant β hβ.le := dipoleConstant_pos β hβ.le
  obtain ⟨C₀, hC₀, hcons⟩ := reducedPartitionFunction_ge_construction_of_two_lt hβ
  have hβ0 : 0 < β := by linarith
  have hs0 : 0 < 2 * (β - 2) / β := div_pos (by linarith) hβ0
  have hb0 : 0 < 2 / β := div_pos two_pos hβ0
  obtain ⟨μ₁, hμ₁, hμ₁'⟩ := exists_pos_rpow_le hs0 (show 0 < min (1 / 256) (1 / (2 * C₀)) from
    lt_min (by norm_num) (by positivity))
  obtain ⟨μ₂, hμ₂, hμ₂'⟩ := exists_pos_rpow_le hb0 (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨min 1 (min μ₁ μ₂), 2 * C₀ + 16 * Real.pi + 8, lt_min one_pos (lt_min hμ₁ hμ₂),
    by positivity, fun N hN lam hlam hlt => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlam1 : lam ≤ 1 := (hlt.trans_le (min_le_left _ _)).le
  have hx : lam ^ (2 * (β - 2) / β) ≤ min (1 / 256) (1 / (2 * C₀)) :=
    hμ₁' lam hlam (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨h2lam, ht2, hratio_pow⟩ := radius_rpow_identities hβ hlam
    (hμ₂' lam hlam (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))))
  have hσ : lam ^ (2 * (β - 2) / β) ≤ lam ^ min ((β - 2) / 2) 1 :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (min_le_two_mul_sub_div hβ)
  have hx0 : 0 ≤ lam ^ (2 * (β - 2) / β) := (Real.rpow_pos_of_pos hlam _).le
  generalize lam ^ (2 * (β - 2) / β) = x at hx ht2 hratio_pow hσ hx0
  generalize lam ^ ((β - 2) / β) = t at h2lam ht2 hratio_pow
  generalize lam ^ min ((β - 2) / 2) 1 = y at hσ ⊢
  -- the radius `t`
  have ht0 : 0 < t := by linarith only [h2lam, hlam]
  have hxle : x ≤ 1 / 256 := hx.trans (min_le_left _ _)
  have hCx : C₀ * x ≤ 1 / 2 := by
    have h1 : x ≤ 1 / (2 * C₀) := hx.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith only [h1]
  have ht16 : t ≤ 1 / 16 := by
    by_contra h
    push Not at h
    have := pow_lt_pow_left₀ h (by norm_num) (two_ne_zero)
    linarith only [this, ht2, hxle]
  -- the construction
  have hbase := hcons N lam t hlam h2lam
  rw [hratio_pow] at hbase
  have h1sub : 0 < 1 - C₀ * x := by linarith only [hCx]
  have hpos : 0 < dipoleConstant β hβ.le * lam ^ (2 - β) := mul_pos hZ (Real.rpow_pos_of_pos hlam _)
  have hA : 0 < dipoleConstant β hβ.le * lam ^ (2 - β) * (1 - C₀ * x) := mul_pos hpos h1sub
  have hEle : 8 * t * Real.sqrt N + 16 * Real.pi * N * t ^ 2 ≤ (4 + 16 * Real.pi) * N * x + 4 := by
    rw [ht2]
    exact placement_error_le N ht2
  have hmain := ofReal_exp_le_of_construction hN1 ht0 ht16 hA hEle hbase
  refine le_trans ?_ hmain
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hlogA : Real.log (dipoleConstant β hβ.le * lam ^ (2 - β) * (1 - C₀ * x)) =
      Real.log (dipoleConstant β hβ.le) + (2 - β) * Real.log lam + Real.log (1 - C₀ * x) := by
    rw [Real.log_mul hpos.ne' h1sub.ne', Real.log_mul hZ.ne' (Real.rpow_pos_of_pos hlam _).ne',
      Real.log_rpow hlam]
  have hlog1 := neg_two_mul_le_log_one_sub (mul_nonneg hC₀.le hx0) hCx
  have hQ := one_le_log_add_one hN
  have harith := two_lt_lower_arith (N := N) hN0 hC₀ hx0 hσ hQ
    (lA := Real.log (dipoleConstant β hβ.le * lam ^ (2 - β) * (1 - C₀ * x)))
    (L := Real.log lam) (β := β) (lZ := Real.log (dipoleConstant β hβ.le))
    (by rw [hlogA]; linarith only [hlog1])
  linarith only [harith]

/-! ### The case `β = 2` -/

/-- For `ℓ ≥ 0`: `ℓ^{-1/2} = (√ℓ)⁻¹`. -/
theorem rpow_neg_half_eq_inv_sqrt {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ℓ ^ (-(1 / 2 : ℝ)) = (Real.sqrt ℓ)⁻¹ := by
  rw [Real.rpow_neg hℓ, Real.sqrt_eq_rpow]

/-- `log (r²) ≤ 2 r` for `r > 0` (from `log r ≤ r - 1`). -/
theorem log_sq_le_two_mul {r : ℝ} (hr : 0 < r) : Real.log (r ^ 2) ≤ 2 * r := by
  have := Real.log_le_sub_one_of_pos hr
  rw [Real.log_pow]
  push_cast
  linarith

/-- Taking the logarithm of the mass expansion by `log (1+x) ≤ x`. -/
private theorem log_gaussianMass_le_ratio {B ℓ C : ℝ} (hℓ : 0 < ℓ) (hB0 : 0 < B)
    (hB : |B - 2 * Real.pi * (ℓ + 1 / 2 * Real.log ℓ)| ≤ C) :
    Real.log B ≤ Real.log (2 * Real.pi * ℓ) +
      (Real.pi * Real.log ℓ + |C|) / (2 * Real.pi * ℓ) := by
  have hp : 0 < 2 * Real.pi * ℓ := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hB0 hp)
  rw [Real.log_div hB0.ne' hp.ne'] at hlog
  have hnum : B - 2 * Real.pi * ℓ ≤ Real.pi * Real.log ℓ + |C| := by
    linarith only [(abs_le.1 hB).2, le_abs_self C]
  have hratio := div_le_div_of_nonneg_right hnum hp.le
  have hid : B / (2 * Real.pi * ℓ) - 1 = (B - 2 * Real.pi * ℓ) / (2 * Real.pi * ℓ) := by
    field_simp
  linarith only [hlog, hratio, hid]

/-- The sharp logarithmic estimate in `eq:critical-B`, obtained from the mass
expansion by `log (1+x) ≤ x`. -/
theorem log_gaussianMass_le_sharp {B ℓ C : ℝ} (hℓ : 1 ≤ ℓ) (hB0 : 0 < B)
    (hB : |B - 2 * Real.pi * (ℓ + 1 / 2 * Real.log ℓ)| ≤ C) :
    Real.log B ≤ Real.log (2 * Real.pi * ℓ) +
      (1 + |C|) * (1 + Real.log ℓ) / ℓ := by
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hlog := log_gaussianMass_le_ratio hℓ0 hB0 hB
  have hl0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hnum : Real.pi * Real.log ℓ + |C| ≤
      2 * Real.pi * ((1 + |C|) * (1 + Real.log ℓ)) := by
    have hp : 1 ≤ Real.pi := le_trans (by norm_num) Real.pi_gt_three.le
    have h1 : Real.pi * Real.log ℓ ≤ Real.pi * ((1 + |C|) * (1 + Real.log ℓ)) := by
      gcongr
      nlinarith only [abs_nonneg C, hl0, mul_nonneg (abs_nonneg C) hl0]
    have h2 : |C| ≤ Real.pi * ((1 + |C|) * (1 + Real.log ℓ)) := by
      calc |C| ≤ (1 + |C|) * (1 + Real.log ℓ) := by
            nlinarith only [abs_nonneg C, hl0, mul_nonneg (abs_nonneg C) hl0]
        _ ≤ _ := le_mul_of_one_le_left (by positivity) hp
    linarith only [h1, h2]
  have hratio : (Real.pi * Real.log ℓ + |C|) / (2 * Real.pi * ℓ) ≤
      (1 + |C|) * (1 + Real.log ℓ) / ℓ := by
    rw [← div_div]
    apply div_le_div_of_nonneg_right _ hℓ0.le
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    linarith only [hnum]
  linarith only [hlog, hratio]

/-- The full sharp bound on `log J_λ(1/ℓ)`, with a universal positive constant
and the manuscript's range `0 < λ ≤ e⁻¹`. -/
theorem exists_log_gaussianMass_le_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      Real.log (∫ u : ℂ, Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|)) ≤
        Real.log (2 * Real.pi * |Real.log lam|) +
          C * (1 + Real.log |Real.log lam|) / |Real.log lam| := by
  obtain ⟨C, hC⟩ := exists_abs_gaussianMass_sub_le
  refine ⟨1 + |C|, by positivity, fun lam hlam hle => ?_⟩
  obtain ⟨hℓ, h2⟩ := two_mul_le_sqrt_neg_log hlam hle
  have hab : |Real.log lam| = -Real.log lam := abs_of_neg (by linarith)
  apply log_gaussianMass_le_sharp
  · rwa [hab]
  · apply integral_gaussianMass_pos hlam
    · rw [hab]; linarith
    · rwa [hab]
  · exact hC lam hlam hle

/-- The two-sided control of the Gaussian mass `B = 2π(ℓ + ½ log ℓ + O(1))` that is used in the
upper bound: with `ℓ = r²` and `ω = r⁻¹`, `ℓ ≤ B` and `log B ≤ log (2π) + log ℓ + (1 + |C₁|) ω`. -/
theorem log_gaussianMass_le {B ℓ r ω C₁ : ℝ} (hr1 : 1 ≤ r) (hr2 : r ^ 2 = ℓ) (hωℓ : ω * ℓ = r)
    (hC : |C₁| < r) (hB : |B - 2 * Real.pi * (ℓ + 1 / 2 * Real.log ℓ)| ≤ C₁) :
    ℓ ≤ B ∧ Real.log B ≤ Real.log (2 * Real.pi) + Real.log ℓ + (1 + |C₁|) * ω := by
  have hr0 : 0 < r := by linarith
  have hℓ1 : 1 ≤ ℓ := by rw [← hr2]; exact one_le_pow₀ hr1
  have hℓ0 : 0 < ℓ := by linarith
  have hrℓ : r ≤ ℓ := by rw [← hr2]; exact le_self_pow₀ hr1 two_ne_zero
  have hpi3 := Real.pi_gt_three
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hlogℓ : Real.log ℓ ≤ 2 * r := by
    have := log_sq_le_two_mul hr0
    rwa [hr2] at this
  have hC₁ : C₁ ≤ |C₁| := le_abs_self C₁
  have hBlow : ℓ ≤ B := by
    have h1 := (abs_le.1 hB).1
    have : 0 ≤ Real.pi * Real.log ℓ := by positivity
    linarith only [h1, this, mul_le_mul_of_nonneg_right hpi3.le hℓ0.le, hC₁, hC, hrℓ, hℓ0]
  have hBpos : 0 < B := by linarith
  refine ⟨hBlow, ?_⟩
  have hpℓ : 0 < 2 * Real.pi * ℓ := by positivity
  have h1 := log_gaussianMass_le_ratio hℓ0 hBpos hB
  rw [Real.log_mul (by positivity) hℓ0.ne'] at h1
  have h2 : (Real.pi * Real.log ℓ + |C₁|) / (2 * Real.pi * ℓ) ≤ (1 + |C₁|) * ω := by
    rw [div_le_iff₀ hpℓ]
    have e : (1 + |C₁|) * ω * (2 * Real.pi * ℓ) =
        2 * Real.pi * (1 + |C₁|) * r := by
      linear_combination (2 * Real.pi * (1 + |C₁|)) * hωℓ
    rw [e]
    have : Real.pi * Real.log ℓ + |C₁| ≤ 2 * Real.pi * (1 + |C₁|) * r := by
      have h3 : Real.pi * Real.log ℓ ≤ Real.pi * (2 * r) :=
        mul_le_mul_of_nonneg_left hlogℓ Real.pi_pos.le
      have h4 : |C₁| ≤ 2 * Real.pi * |C₁| * r := by
        have : 1 ≤ 2 * Real.pi * r := by
          linarith only [mul_le_mul_of_nonneg_right hpi3.le hr0.le, hr1]
        linarith only [mul_le_mul_of_nonneg_left this (abs_nonneg C₁)]
      linarith only [h3, h4]
    exact this
  linarith only [h1, h2]

/-- **Lemma 3.5, upper bound for `β = 2`** . -/
theorem reducedPartitionFunction_two_le_exp :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      reducedPartitionFunction N 2 lam ≤ ENNReal.ofReal (Real.exp (
        2 * N * Real.log N + N * (Real.log |Real.log lam| + (Real.log (2 * Real.pi) - 1))
        + C * (N * |Real.log lam| ^ (-(1 / 2 : ℝ)) + Real.log (N + 1)))) := by
  obtain ⟨C₁, hC₁⟩ := exists_abs_gaussianMass_sub_le
  set R₀ : ℝ := 1 + |C₁| with hR₀
  have hR₀1 : 1 ≤ R₀ := by rw [hR₀]; linarith only [abs_nonneg C₁]
  refine ⟨Real.exp (-R₀ ^ 2), 11 + |C₁|, Real.exp_pos _, by positivity, fun N hN lam hlam hlt => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlog : Real.log lam < -R₀ ^ 2 := (Real.log_lt_iff_lt_exp hlam).2 hlt
  have hℓeq : |Real.log lam| = -Real.log lam := abs_of_neg (by linarith only [hlog, sq_nonneg R₀])
  have hle : lam ≤ Real.exp (-1) := by
    rw [← Real.log_le_iff_le_exp hlam]
    linarith only [hlog, one_le_pow₀ (n := 2) hR₀1]
  have h := reducedPartitionFunction_two_le_abs_log (N := N) hlam hle
  have hB := hC₁ lam hlam hle
  set ℓ := |Real.log lam| with hℓ
  set B := ∫ u : ℂ, Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ) with hBdef
  have hℓR : R₀ ^ 2 < ℓ := by rw [hℓeq]; linarith only [hlog]
  have hℓ0 : 0 < ℓ := by linarith only [hℓR, one_le_pow₀ (n := 2) hR₀1]
  set r := Real.sqrt ℓ with hr
  have hr2 : r ^ 2 = ℓ := Real.sq_sqrt hℓ0.le
  have hrR : R₀ < r := (Real.lt_sqrt (by linarith only [hR₀1])).2 hℓR
  have hr1 : 1 ≤ r := by linarith only [hR₀1, hrR]
  have hr0 : 0 < r := by linarith only [hr1]
  set ω := r⁻¹ with hω
  have hω0 : 0 < ω := inv_pos.2 hr0
  have hωr : ω * r = 1 := inv_mul_cancel₀ hr0.ne'
  have hωℓ : ω * ℓ = r := by rw [← hr2]; linear_combination r * hωr
  have hωeq : ℓ ^ (-(1 / 2 : ℝ)) = ω := rpow_neg_half_eq_inv_sqrt hℓ0.le
  rw [hωeq]
  obtain ⟨hBlow, hlogB⟩ := log_gaussianMass_le hr1 hr2 hωℓ (by linarith only [hrR, hR₀]) hB
  have hBpos : 0 < B := by linarith only [hBlow, hℓ0]
  -- the pieces of the exponent
  have hF : 2 * (N : ℝ) / Real.sqrt B ≤ 2 * N * ω := by
    have hsq : r ≤ Real.sqrt B := Real.sqrt_le_sqrt hBlow
    calc 2 * (N : ℝ) / Real.sqrt B ≤ 2 * N / r :=
          div_le_div_of_nonneg_left (by positivity) hr0 hsq
      _ = 2 * N * ω := by rw [hω, div_eq_mul_inv]
  have hc : 18 * (N : ℝ) / (Real.pi * ℓ) ≤ 6 * N * ω := by
    rw [div_le_iff₀ (by positivity)]
    have e : 6 * (N : ℝ) * ω * (Real.pi * ℓ) = 6 * N * (Real.pi * r) := by
      linear_combination (6 * (N : ℝ) * Real.pi) * hωℓ
    rw [e]
    have : 3 ≤ Real.pi * r := by
      linarith only [mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ Real.pi), Real.pi_gt_three]
    have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 6 * (N : ℝ))
    linarith only [this]
  have hlog1 := one_le_log_add_one hN
  have hlog2 := log_le_log_add_one hN1
  have hNω : 0 ≤ (N : ℝ) * ω := by positivity
  have hQ : 0 ≤ Real.log ((N : ℝ) + 1) := by linarith only [hlog1]
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hmain := factorial_mul_pow_mul_pow_mul_exp_le hN1 hBpos (2 * (N : ℝ) / Real.sqrt B)
  calc Real.exp (18 * (N : ℝ) / (Real.pi * ℓ)) *
        ((N ! : ℝ) * (N : ℝ) ^ N * B ^ N * Real.exp (2 * N / Real.sqrt B))
      ≤ Real.exp (18 * (N : ℝ) / (Real.pi * ℓ)) *
        Real.exp (2 * N * Real.log N + N * (Real.log B - 1) + (1 + Real.log N) +
          2 * N / Real.sqrt B) := by gcongr
    _ = Real.exp (18 * (N : ℝ) / (Real.pi * ℓ) + (2 * N * Real.log N + N * (Real.log B - 1) +
          (1 + Real.log N) + 2 * N / Real.sqrt B)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      refine Real.exp_le_exp.2 ?_
      have h1 : (N : ℝ) * Real.log B ≤
          N * (Real.log (2 * Real.pi) + Real.log ℓ + (1 + |C₁|) * ω) :=
        mul_le_mul_of_nonneg_left hlogB hN0.le
      have h2 : (11 + |C₁|) * Real.log ((N : ℝ) + 1) ≥ 2 * Real.log ((N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith only [abs_nonneg C₁]) hQ
      have h3 : (11 + |C₁|) * ((N : ℝ) * ω) ≥ (9 + |C₁|) * ((N : ℝ) * ω) :=
        mul_le_mul_of_nonneg_right (by linarith only []) hNω
      linarith only [hc, hF, h1, hlog1, hlog2, h2, h3]

/-- The critical radius: with `ℓ = r²`, `ω = r⁻¹` and `r ≥ 16`, the quantity
`R = ℓ - log ℓ - log 2` is positive and `log (2π R) ≥ log (2π) + log ℓ - 6 ω`. -/
theorem critical_radius_bounds {ℓ r ω : ℝ} (hr : 16 ≤ r) (hr2 : r ^ 2 = ℓ) (hωℓ : ω * ℓ = r)
    (hω : ω ≤ 1 / 16) (hω0 : 0 < ω) :
    0 < ℓ - Real.log ℓ - Real.log 2 ∧
      Real.log (2 * Real.pi) + Real.log ℓ - 6 * ω ≤
        Real.log (2 * Real.pi * (ℓ - Real.log ℓ - Real.log 2)) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hℓ0 : 0 < ℓ := by rw [← hr2]; positivity
  have hlogℓ : Real.log ℓ ≤ 2 * r := by
    have := log_sq_le_two_mul hr0
    rwa [hr2] at this
  have hlogℓ0 : 0 ≤ Real.log ℓ :=
    Real.log_nonneg (by rw [← hr2]; exact one_le_pow₀ (by linarith only [hr]))
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith only [this]
  have hlog20 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set y : ℝ := (Real.log ℓ + Real.log 2) / ℓ with hy
  have hy0 : 0 ≤ y := by positivity
  have hy3 : y ≤ 3 * ω := by
    rw [hy, div_le_iff₀ hℓ0]
    have : 3 * ω * ℓ = 3 * r := by linear_combination 3 * hωℓ
    rw [this]
    linarith only [hlogℓ, hlog2, hr]
  have hy2 : y ≤ 1 / 2 := by
    have h3ω : 0 < 3 * ω := mul_pos three_pos hω0
    linarith only [hy3, hω, h3ω]
  have hR : ℓ - Real.log ℓ - Real.log 2 = ℓ * (1 - y) := by
    rw [hy]
    field_simp
    ring
  have h1y : 0 < 1 - y := by linarith only [hy2]
  refine ⟨by rw [hR]; positivity, ?_⟩
  rw [hR, Real.log_mul (by positivity : 2 * Real.pi ≠ 0) (by positivity : ℓ * (1 - y) ≠ 0),
    Real.log_mul hℓ0.ne' h1y.ne']
  have := neg_two_mul_le_log_one_sub hy0 hy2
  linarith only [this, hy3]

/-- **Lemma 3.5, lower bound for `β = 2`** (source l. 920–923). -/
theorem exp_le_reducedPartitionFunction_two :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ENNReal.ofReal (Real.exp (
        2 * N * Real.log N + N * (Real.log |Real.log lam| + (Real.log (2 * Real.pi) - 1))
        - C * (N * |Real.log lam| ^ (-(1 / 2 : ℝ)) + Real.log (N + 1)))) ≤
        reducedPartitionFunction N 2 lam := by
  refine ⟨Real.exp (-256), 14 + 16 * Real.pi, Real.exp_pos _, by positivity,
    fun N hN lam hlam hlt => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlog : Real.log lam < -256 := (Real.log_lt_iff_lt_exp hlam).2 hlt
  have hℓeq : |Real.log lam| = -Real.log lam := abs_of_neg (by linarith only [hlog])
  set ℓ := |Real.log lam| with hℓ
  have hℓR : (16 : ℝ) ^ 2 < ℓ := by rw [hℓeq]; linarith only [hlog]
  have hℓ0 : 0 < ℓ := by linarith only [hℓR]
  set r := Real.sqrt ℓ with hr
  have hr2 : r ^ 2 = ℓ := Real.sq_sqrt hℓ0.le
  have hr16 : 16 ≤ r := ((Real.lt_sqrt (by norm_num)).2 hℓR).le
  have hr0 : 0 < r := by linarith only [hr16]
  set ω := r⁻¹ with hω
  have hω0 : 0 < ω := inv_pos.2 hr0
  have hωr : ω * r = 1 := inv_mul_cancel₀ hr0.ne'
  have hωℓ : ω * ℓ = r := by rw [← hr2]; linear_combination r * hωr
  have hω16 : ω ≤ 1 / 16 := by
    rw [hω, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hr16
  have hωeq : ℓ ^ (-(1 / 2 : ℝ)) = ω := rpow_neg_half_eq_inv_sqrt hℓ0.le
  rw [hωeq]
  obtain ⟨hRpos, hlogA⟩ := critical_radius_bounds hr16 hr2 hωℓ hω16 hω0
  -- the annulus ratio
  have hratio : Real.log (ω ^ 2 / (2 * lam)) = ℓ - Real.log ℓ - Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_mul (by norm_num)
      hlam.ne', hω, Real.log_inv, ← hr2, Real.log_pow]
    have : Real.log lam = -ℓ := by rw [hℓeq]; ring
    rw [this]
    push_cast
    linear_combination (-1 : ℝ) * hr2
  have hlt2 : 2 * lam ≤ ω ^ 2 := by
    have h0 : 0 ≤ Real.log (ω ^ 2 / (2 * lam)) := by rw [hratio]; exact hRpos.le
    rw [Real.log_nonneg_iff (by positivity), one_le_div (by positivity)] at h0
    exact h0
  have hω1 : ω ≤ 1 := by linarith only [hω16]
  have hcore := reducedPartitionFunction_two_ge_construction (N := N) hlam hω0 hω1 hlt2
  rw [hratio] at hcore
  set A : ℝ := 2 * Real.pi * (ℓ - Real.log ℓ - Real.log 2) with hA
  have hApos : 0 < A := by positivity
  have hsqrt : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_iff]
    refine ⟨hN0.le, ?_⟩
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact le_self_pow₀ this two_ne_zero
  have hEle : 8 * ω * Real.sqrt N + 16 * Real.pi * N * ω ^ 2 ≤ (8 + 16 * Real.pi) * N * ω := by
    have e1 : 8 * ω * Real.sqrt N ≤ 8 * ω * N := by gcongr
    have e2 : ω ^ 2 ≤ ω := pow_le_of_le_one hω0.le hω1 two_ne_zero
    have e3 : 16 * Real.pi * N * ω ^ 2 ≤ 16 * Real.pi * N * ω := by gcongr
    linarith only [e1, e3]
  have hmain := ofReal_exp_le_of_construction hN1 hω0 hω16 hApos hEle hcore
  refine le_trans ?_ hmain
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hlogA' : Real.log (2 * Real.pi) + Real.log ℓ - 6 * ω ≤ Real.log A := hlogA
  have h1 : (N : ℝ) * (Real.log (2 * Real.pi) + Real.log ℓ - 6 * ω) ≤ N * Real.log A :=
    mul_le_mul_of_nonneg_left hlogA' hN0.le
  have hlog1 := one_le_log_add_one hN
  have hNω : 0 ≤ (N : ℝ) * ω := by positivity
  have hQ : 0 ≤ (14 + 16 * Real.pi) * Real.log ((N : ℝ) + 1) := by
    have : 0 ≤ Real.log ((N : ℝ) + 1) := by linarith only [hlog1]
    positivity
  linarith only [h1, hQ]

end ReducedAssembly

open ReducedAssembly

/-! ### The statements of Lemma 3.5 -/

/-- **Lemma 3.5 for `β > 2`** (source l. 870–952), in the form of the frozen statement. -/
theorem lemma_3_5_of_two_lt {β : ℝ} (hβ : 2 < β) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        0 < reducedPartitionFunction N β lam ∧ reducedPartitionFunction N β lam < ∞ ∧
        |Real.log (reducedPartitionFunction N β lam).toReal
            - (2 * N * Real.log N
              + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0)
                + (Real.log (dipoleConstant β hβ.le) - 1)))|
          ≤ C * (N * (if β = 2 then |Real.log lam| ^ (-(1 / 2 : ℝ))
              else lam ^ min ((β - 2) / 2) 1)
            + Real.log (N + 1)) := by
  obtain ⟨C₁, hC₁, hup⟩ := reducedPartitionFunction_le_exp_of_two_lt hβ
  obtain ⟨lam₀, C₂, hlam₀, hC₂, hlo⟩ := exp_le_reducedPartitionFunction_of_two_lt hβ
  refine ⟨min lam₀ 1, C₁ + C₂, lt_min hlam₀ one_pos, by positivity, fun N hN lam hlam hlt => ?_⟩
  have hlt₀ : lam < lam₀ := hlt.trans_le (min_le_left _ _)
  have hle1 : lam ≤ 1 := (hlt.trans_le (min_le_right _ _)).le
  have hW : 0 ≤ (N : ℝ) * lam ^ min ((β - 2) / 2) 1 + Real.log ((N : ℝ) + 1) := by
    have := one_le_log_add_one hN
    positivity
  have h := sandwich_log_toReal hW hC₁.le hC₂.le (hlo N hN lam hlam hlt₀) (hup N hN lam hlam hle1)
  simp only [hβ, hβ.ne', ↓reduceIte, add_zero]
  exact h

/-- **Lemma 3.5 for `β = 2`** (source l. 870–952), in the form of the frozen statement. -/
theorem lemma_3_5_two (hβ : (2 : ℝ) ≤ 2) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        0 < reducedPartitionFunction N 2 lam ∧ reducedPartitionFunction N 2 lam < ∞ ∧
        |Real.log (reducedPartitionFunction N 2 lam).toReal
            - (2 * N * Real.log N
              + N * ((if 2 < (2 : ℝ) then (2 - 2) * Real.log lam else 0)
                + (if (2 : ℝ) = 2 then Real.log |Real.log lam| else 0)
                + (Real.log (dipoleConstant 2 hβ) - 1)))|
          ≤ C * (N * (if (2 : ℝ) = 2 then |Real.log lam| ^ (-(1 / 2 : ℝ))
              else lam ^ min (((2 : ℝ) - 2) / 2) 1)
            + Real.log (N + 1)) := by
  obtain ⟨lam₁, C₁, hlam₁, hC₁, hup⟩ := reducedPartitionFunction_two_le_exp
  obtain ⟨lam₂, C₂, hlam₂, hC₂, hlo⟩ := exp_le_reducedPartitionFunction_two
  refine ⟨min lam₁ lam₂, C₁ + C₂, lt_min hlam₁ hlam₂, by positivity, fun N hN lam hlam hlt => ?_⟩
  have hZ : dipoleConstant 2 hβ = 2 * Real.pi := by simp [dipoleConstant]
  have hW : 0 ≤ (N : ℝ) * |Real.log lam| ^ (-(1 / 2 : ℝ)) + Real.log ((N : ℝ) + 1) := by
    have := one_le_log_add_one hN
    positivity
  have h := sandwich_log_toReal hW hC₁.le hC₂.le
    (hlo N hN lam hlam (hlt.trans_le (min_le_right _ _)))
    (hup N hN lam hlam (hlt.trans_le (min_le_left _ _)))
  simp only [lt_self_iff_false, ↓reduceIte, zero_add, hZ]
  exact h

end TwoComponentCoulomb

end
