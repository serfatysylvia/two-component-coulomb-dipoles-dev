/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.AlphaBallGrowth
public import TwoComponentCoulomb.Fluctuations.CriticalElectricCells
public import TwoComponentCoulomb.Fluctuations.Theorem2Assembly
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TwoComponentCoulomb.Frozen.M0
public import TwoComponentCoulomb.Frozen.ErrorRate
public import TwoComponentCoulomb.Frozen.GibbsMeasure
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.NumComponents
public import TwoComponentCoulomb.UpperBound.CriticalGraphSum
public import TwoComponentCoulomb.UpperBound.IsolatedRadial
import Mathlib.Analysis.Real.Pi.Bounds
import TwoComponentCoulomb.Frozen.Proposition41
import TwoComponentCoulomb.Gibbs.Basic
import TwoComponentCoulomb.Integrals.GaussianMass
import TwoComponentCoulomb.NearestNeighbor.General
import TwoComponentCoulomb.NearestNeighbor.Radius
import TwoComponentCoulomb.NearestNeighbor.Second
import TwoComponentCoulomb.NearestNeighbor.SecondRadius
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel
import TwoComponentCoulomb.UpperBound.PairBlocks

/-!
# Theorem 2 at `β = 2`: the exponential moment of the electric energy (eq. (eq:critical electric))

Source l. 2023--2060 (proof of Theorem 2, Step 2, `β = 2`).

Write `ℓ = |log λ|`, `S = 1 + log ℓ + log (1/γ)` and `αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)` (`alphaRadius`,
source (eq:def alphai)). The source uses the ball-growth inequality of Step 2 directly, with the
retained coordinates of the proof of (eq:critical upper), so that the electric energy
`(1/4π) ∫ |∇h_α|²` is kept. For `0 < c ≤ 1/(2π)` the factor `e^{c ∫ |∇h_α|²}` is absorbed by it, the
neutral pair error is `C ((a/ρ)² + min {a/γ, 1}²)` and the same-sign correction is at least
`2 log (((ρ ∧ γ) ∨ a)/a) - C`; the neutral and same-sign masses are `J_λ(1/ℓ) + CS` and `CS`
(`Fluctuations/CriticalElectricCells.lean`). The cell integral and the sum over the graphs are those
of the proof of (eq:critical upper), proved for a general integrand in
`UpperBound/CriticalCells.lean` and `UpperBound/CriticalGraphSum.lean` (with a same-sign mass
`Mₛ ≤ C S` instead of a constant). The lower bound (eq:lbz2) of Proposition 4.1 then gives
(eq:critical electric):

`log 𝔼_ℙ[e^{c ∫ |∇h_α|²}] ≤ C N (ℓ^{-1/5} + S/ℓ) + C log (N+1) ≤ C N (ω_λ + φ₂(γ)) + C log (N+1)`.

Here `ω_λ = errorRate 2 _ λ = ℓ^{-1/5}` (source l. 2055, "`ℓ^{-1/5} = ω_λ`"), and, for `γ ≤ 1`,
`S/ℓ = φ₂(γ) + log ℓ/ℓ` with `log ℓ/ℓ ≤ (5/4) ℓ^{-1/5}`.

## Main results

* `exists_neg_two_mul_energy_add_electric_le` (source l. 2014--2023, 2038): for `c ≤ 1/(2π)`,
  `-2 F_λ + c ∫ |∇h_α|² ≤ ∑_{i ∉ I^pair} (g_λ(zᵢ - z_{φ₁ i}) + c₁) + ∑_{s ∈ S} E_s`, from the
  ball-growth inequality of Step 2 (`energy_ge_electric_alphaRadius`).
* `exists_lintegral_cell_electric_le` (source l. 2038--2044): the integral of
  `e^{-2F_λ + c ∫ |∇h_α|²}` over one cell (by `exists_lintegral_cell_le_pairCellExponent`).
* `exists_lintegral_exp_electric_le` (source l. 2045--2055):
  `∫_{Λ^{2N}} e^{-2F_λ + c ∫ |∇h_α|²} ≤
  exp (2N log N + N (log (2πℓ) - 1) + C N (ℓ^{-1/5} + S/ℓ) + C log (N+1))`, the sum over the graphs
  (by `exists_lintegral_pi_box_le_of_cell_le`).
* `measurable_integral_norm_sq_electricField_alphaRadius`: `Z ↦ ∫ |∇h_α|²` is measurable.
* `critical_electric` (eq:critical electric): there are `C, λ₁ > 0` such that for `c ≤ 1/(2π)`,
  `N ≥ 2`, `0 < λ < λ₁` and `2λ ≤ γ ≤ 1`,
  `𝔼_ℙ[e^{c ∫ |∇h_α|²}] ≤ exp (C N (φ₂(γ) + ω_λ) + C log (N+1))`, with `ω_λ = errorRate 2 _ λ`.
* `exists_momentBound_two`: the same, in the form of items (ii)--(iii) of
  `MomentBoundRate 2 _ (errorRate 2 _)` (`Fluctuations/Theorem2Assembly.lean`), with `c = 1/(2π)`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### The energy bound keeping the electric energy (source l. 2014--2023, 2038) -/

section Energy

/-- The 2-cycle term of the ball-growth inequality of Step 2 at the vertex `i` (source l. 2014--2022,
`energy_ge_electric_alphaRadius`):
`dᵢ d_{φ₁ i} g_λ(zᵢ - z_{φ₁ i}) - dᵢ (dᵢ + d_{φ₁ i}) (g(αᵢ) + κ) - 64 (r̃₁ / ((r̃₂ ∧ γ) ∨ r̃₁))²`. -/
noncomputable def alphaCycleTerm (hN : 2 ≤ N) (lam γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : ℝ :=
  charge i * charge (nearestNeighbor Z i) * smearedKernel lam (Z i - Z (nearestNeighbor Z i))
    - charge i * (charge i + charge (nearestNeighbor Z i)) *
        (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa)
    - 64 * (firstNeighborRadius lam Z i /
        max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i)) ^ 2

/-- The tree term with the radii `α`: `g(αᵢ) + κ ≤ g_λ(zᵢ - z_{φ₁ i}) + C`, since `αᵢ ≥ r̃₁(zᵢ)`
(source eq. (gr2r1)). -/
theorem alpha_tree_term_le (hN : 2 ≤ N) {Cg : ℝ}
    (hCg : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, -Real.log (max ‖z‖ lam) - Cg ≤ smearedKernel lam z)
    {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa ≤
      smearedKernel lam (Z i - Z (nearestNeighbor Z i)) + (|Cg| + Real.log 4 + |kappa|) := by
  have hr1 : 0 < firstNeighborRadius lam Z i := hlam.trans_le (lam_le_firstNeighborRadius lam Z i)
  have hα := firstNeighborRadius_le_alphaRadius hN lam γ Z i
  rw [logKernel_ofReal (hr1.trans_le hα)]
  have := Real.log_le_log hr1 hα
  have := smearedKernel_add_log_firstNeighborRadius_ge hCg hlam Z i
  have := le_abs_self Cg
  have := le_abs_self kappa
  linarith

/-- The term of a vertex on a 2-cycle (not necessarily isolated), with the radii `α`:
`-T_i ≤ g_λ(zᵢ - z_{φ₁ i}) + C`. -/
theorem neg_alphaCycleTerm_le (hN : 2 ≤ N) {Cg : ℝ}
    (hCg : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, -Real.log (max ‖z‖ lam) - Cg ≤ smearedKernel lam z)
    {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    -alphaCycleTerm hN lam γ Z i ≤
      smearedKernel lam (Z i - Z (nearestNeighbor Z i)) +
        (2 * |Cg| + 2 * Real.log 4 + 2 * |kappa| + 64) := by
  have hr1 : 0 < firstNeighborRadius lam Z i := hlam.trans_le (lam_le_firstNeighborRadius lam Z i)
  have hα := firstNeighborRadius_le_alphaRadius hN lam γ Z i
  have hq1 := sq_div_max_min_le_one hr1 (secondNeighborRadius hN lam Z i) γ
  have hq0 := sq_nonneg (firstNeighborRadius lam Z i /
    max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i))
  have hlogα := Real.log_le_log hr1 hα
  have hG := smearedKernel_add_log_firstNeighborRadius_ge hCg hlam Z i
  have := le_abs_self Cg
  have := le_abs_self kappa
  have := abs_nonneg Cg
  have := abs_nonneg kappa
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold alphaCycleTerm
  rw [logKernel_ofReal (hr1.trans_le hα)]
  rcases charge_eq_one_or_neg_one i with h | h <;>
    rcases charge_eq_one_or_neg_one (nearestNeighbor Z i) with h' | h' <;>
    · rw [h, h']
      norm_num
      linarith

variable {Z : Fin N ⊕ Fin N → ℂ}

/-- The two cycle terms of an isolated neutral pair, with the radii `α` (source l. 2023,
"the neutral pair error is bounded by `C((a/ρ)² + min{a/γ, 1}²)`"):
`-T_s - T_{φ₁ s} ≤ 2 g_λ(u_s) + 832 ((a/ρ)² + ((a/γ)² ∧ 1))`, using
`(r̃₁ / ((r̃₂ ∧ γ) ∨ r̃₁))² ≤ (r̃₁/r̃₂)² + ((r̃₁/γ)² ∧ 1)` and `ρ ≤ 3 r̃₂` at both endpoints. -/
theorem neg_alphaCycleTerm_neutral_pair_le (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) {γ : ℝ}
    (hγ : 0 < γ) (s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)})
    (hn : charge (s : Fin N ⊕ Fin N) * charge (nearestNeighbor Z s) = -1) :
    -alphaCycleTerm hN lam γ Z s - alphaCycleTerm hN lam γ Z (nearestNeighbor Z s) ≤
      2 * smearedKernel lam (Z s - Z (nearestNeighbor Z s)) +
        832 * ((displacementScale lam (Z s - Z (nearestNeighbor Z s)) /
            isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s)) ^ 2 +
          min ((displacementScale lam (Z s - Z (nearestNeighbor Z s)) / γ) ^ 2) 1) := by
  have hs := s.2
  have h2 : nearestNeighbor Z (nearestNeighbor Z s) = s := (mem_isoSecondVerts.1 hs).1.1
  unfold alphaCycleTerm
  rw [h2]
  set ρ := isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s) with hρdef
  have hρ0 : 0 < ρ := hlam.trans_le (lam_le_isoRadius hN lam _ _)
  have hρs := isoRadius_le_three_mul_secondNeighborRadius rfl hN hlam s
  have hρr := isoRadius_le_two_mul_secondNeighborRadius rfl hN hlam s
  rw [← hρdef] at hρs hρr
  set a := displacementScale lam (Z s - Z (nearestNeighbor Z s)) with ha
  have ha0 : 0 < a := displacementScale_pos hlam _
  have hr1s : firstNeighborRadius lam Z s = a := by
    rw [firstNeighborRadius_eq, ha, displacementScale]
  have hr1r : firstNeighborRadius lam Z (nearestNeighbor Z s) = a := by
    rw [firstNeighborRadius_eq, h2, ha, displacementScale, norm_sub_rev]
  have hgr : smearedKernel lam (Z (nearestNeighbor Z s) - Z s) =
      smearedKernel lam (Z s - Z (nearestNeighbor Z s)) := by
    rw [← neg_sub, smearedKernel_neg]
  have hr2s : 0 < secondNeighborRadius hN lam Z s :=
    hlam.trans_le (lam_le_secondNeighborRadius hN lam Z s)
  have hr2r : 0 < secondNeighborRadius hN lam Z (nearestNeighbor Z s) :=
    hlam.trans_le (lam_le_secondNeighborRadius hN lam Z (nearestNeighbor Z s))
  have hr12s := firstNeighborRadius_le_secondNeighborRadius hN lam Z s
  have hr12r := firstNeighborRadius_le_secondNeighborRadius hN lam Z (nearestNeighbor Z s)
  rw [hr1s] at hr12s
  rw [hr1r] at hr12r
  have hqs := sq_div_max_min_le ha0 hr12s hγ
  have hqr := sq_div_max_min_le ha0 hr12r hγ
  have hqs' := sq_div_le_of_le_mul ha0.le hρ0 hr2s hρs
  have hqr' := sq_div_le_of_le_mul ha0.le hρ0 hr2r hρr
  have ht0 : 0 ≤ min ((a / γ) ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
  rw [hr1s, hr1r, hgr]
  have hsum : charge (s : Fin N ⊕ Fin N) + charge (nearestNeighbor Z s) = 0 := by
    rcases charge_eq_one_or_neg_one (s : Fin N ⊕ Fin N) with h | h <;>
      rcases charge_eq_one_or_neg_one (nearestNeighbor Z s) with h' | h' <;>
      (rw [h, h'] at hn ⊢; first | (norm_num at hn; done) | norm_num)
  have hn' : charge (nearestNeighbor Z s) * charge (s : Fin N ⊕ Fin N) = -1 := by
    rw [mul_comm]; exact hn
  have hsum' : charge (nearestNeighbor Z s) + charge (s : Fin N ⊕ Fin N) = 0 := by
    rw [add_comm]; exact hsum
  rw [hn, hn', hsum, hsum', mul_zero, mul_zero, zero_mul, zero_mul]
  linarith only [hqs, hqr, hqs', hqr', ht0]

/-- `αₛ ≥ ((ρ ∧ γ) ∨ a)/3` at the non-retained endpoint `s` of an isolated pair: `τₛ ≥ ρ/3` since
`ρ ≤ 3 r̃₂` at both endpoints, and `r̃₁(zₛ) = a`. -/
theorem max_min_isoRadius_le_three_mul_alphaRadius (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (γ : ℝ) (s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)}) :
    max (min (isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s)) γ)
        (displacementScale lam (Z s - Z (nearestNeighbor Z s))) ≤
      3 * alphaRadius hN lam γ Z s := by
  have hs := s.2
  have h2 : nearestNeighbor Z (nearestNeighbor Z s) = s := (mem_isoSecondVerts.1 hs).1.1
  have hρs := isoRadius_le_three_mul_secondNeighborRadius rfl hN hlam s
  have hρr := isoRadius_le_two_mul_secondNeighborRadius rfl hN hlam s
  have hr2r : 0 < secondNeighborRadius hN lam Z (nearestNeighbor Z s) :=
    hlam.trans_le (lam_le_secondNeighborRadius hN lam Z (nearestNeighbor Z s))
  have hr1s : firstNeighborRadius lam Z s = displacementScale lam (Z s - Z (nearestNeighbor Z s)) := by
    rw [firstNeighborRadius_eq, displacementScale]
  unfold alphaRadius
  rw [tau_of_twoCycle hN lam Z h2, hr1s]
  set ρ := isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s)
  set a := displacementScale lam (Z s - Z (nearestNeighbor Z s))
  set r := secondNeighborRadius hN lam Z s
  set r' := secondNeighborRadius hN lam Z (nearestNeighbor Z s)
  have h3 := le_max_left (min (min r r') γ) a
  have h4 := le_max_right (min (min r r') γ) a
  have ha0 : 0 < a := displacementScale_pos hlam _
  refine max_le ?_ (by linarith)
  rcases le_or_gt (min ρ γ) 0 with h | h
  · linarith
  · have hm1 : min ρ γ / 3 ≤ min (min r r') γ := by
      refine le_min (le_min ?_ ?_) ?_
      · have := min_le_left ρ γ; linarith
      · have := min_le_left ρ γ; linarith
      · have := min_le_right ρ γ; linarith
    linarith

/-- The two cycle terms of an isolated same-sign pair, with the radii `α` (source l. 2023, "the
same-sign correction is at least `2 log (((ρ ∧ γ) ∨ a)/a) - C`"):
`-T_s - T_{φ₁ s} ≤ 2 log (|u_s| ∨ λ) - 4 log ((ρ ∧ γ) ∨ a) + C`, using `-g_λ(u) ≤ log (|u| ∨ λ) + C`,
`α_{φ₁ s} = αₛ` and `αₛ ≥ ((ρ ∧ γ) ∨ a)/3`. -/
theorem neg_alphaCycleTerm_sameSign_pair_le (hN : 2 ≤ N) {Cg : ℝ}
    (hCg : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, -Real.log (max ‖z‖ lam) - Cg ≤ smearedKernel lam z)
    {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) (s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)})
    (hn : ¬ charge (s : Fin N ⊕ Fin N) * charge (nearestNeighbor Z s) = -1) :
    -alphaCycleTerm hN lam γ Z s - alphaCycleTerm hN lam γ Z (nearestNeighbor Z s) ≤
      2 * Real.log (max ‖Z s - Z (nearestNeighbor Z s)‖ lam) -
        4 * Real.log (max (min (isoRadius (nearestNeighbor Z) hN lam (fun k => Z k)
          (isoPartner s)) γ) (displacementScale lam (Z s - Z (nearestNeighbor Z s)))) +
        (2 * |Cg| + 4 * Real.log 3 + 4 * |kappa| + 128) := by
  have hs := s.2
  have h2 : nearestNeighbor Z (nearestNeighbor Z s) = s := (mem_isoSecondVerts.1 hs).1.1
  have hαM := max_min_isoRadius_le_three_mul_alphaRadius hN hlam γ s
  have hαr : alphaRadius hN lam γ Z (nearestNeighbor Z s) = alphaRadius hN lam γ Z s :=
    alphaRadius_nearestNeighbor_eq hN lam γ Z h2
  have hα0 := alphaRadius_pos hN hlam γ Z s
  set M := max (min (isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s)) γ)
    (displacementScale lam (Z s - Z (nearestNeighbor Z s))) with hM
  have hM0 : 0 < M := (displacementScale_pos hlam _).trans_le (le_max_right _ _)
  have hlogα : Real.log M - Real.log 3 ≤ Real.log (alphaRadius hN lam γ Z s) := by
    rw [← Real.log_div hM0.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hq : ∀ i, 64 * (firstNeighborRadius lam Z i /
      max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i)) ^ 2 ≤ 64 := by
    intro i
    have hr1 : 0 < firstNeighborRadius lam Z i :=
      hlam.trans_le (lam_le_firstNeighborRadius lam Z i)
    have := sq_div_max_min_le_one hr1 (secondNeighborRadius hN lam Z i) γ
    linarith
  have hq0 : ∀ i, 0 ≤ 64 * (firstNeighborRadius lam Z i /
      max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i)) ^ 2 :=
    fun i => by positivity
  have hqs := hq s
  have hqr := hq (nearestNeighbor Z s)
  have hgs := hCg lam hlam (Z s - Z (nearestNeighbor Z s))
  have hgr := hCg lam hlam (Z (nearestNeighbor Z s) - Z s)
  rw [norm_sub_rev (Z (nearestNeighbor Z s)) (Z s)] at hgr
  have hss : charge (s : Fin N ⊕ Fin N) * charge (nearestNeighbor Z s) = 1 := by
    rcases charge_eq_one_or_neg_one (s : Fin N ⊕ Fin N) with h | h <;>
      rcases charge_eq_one_or_neg_one (nearestNeighbor Z s) with h' | h' <;>
      (rw [h, h'] at hn ⊢; first | (norm_num at hn; done) | norm_num)
  have hss' : charge (nearestNeighbor Z s) * charge (s : Fin N ⊕ Fin N) = 1 := by
    rw [mul_comm]; exact hss
  have hD : charge (s : Fin N ⊕ Fin N) *
      (charge (s : Fin N ⊕ Fin N) + charge (nearestNeighbor Z s)) = 2 := by
    rw [mul_add, charge_mul_self, hss]; norm_num
  have hD' : charge (nearestNeighbor Z s) *
      (charge (nearestNeighbor Z s) + charge (s : Fin N ⊕ Fin N)) = 2 := by
    rw [mul_add, charge_mul_self, hss']; norm_num
  unfold alphaCycleTerm
  rw [h2, hαr, hss, hss', hD, hD', logKernel_ofReal hα0]
  have := le_abs_self Cg
  have := le_abs_self kappa
  linarith

variable (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) in
/-- The exponent `E_s` of the isolated pair of the non-retained endpoint `s` in the electric moment
(source l. 2023): with `u = z_s - z_{f s}`, `ρ = ρ_s` and `a = (|u|/4) ∨ λ`,
`2 g_λ(u) + c₂ ((a/ρ)² + ((a/γ)² ∧ 1))` for a neutral pair and
`2 log (|u| ∨ λ) - 4 log ((ρ ∧ γ) ∨ a) + c₃` for a same-sign pair. -/
noncomputable def elecPairExponent (hN : 2 ≤ N) (lam γ c₂ c₃ : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (s : {s // s ∈ isoSecondVerts f}) : ℝ :=
  if charge (s : Fin N ⊕ Fin N) * charge (f s) = -1 then
    2 * smearedKernel lam (Z s - Z (f s)) +
      c₂ * ((displacementScale lam (Z s - Z (f s)) /
          isoRadius f hN lam (fun k => Z k) (isoPartner s)) ^ 2 +
        min ((displacementScale lam (Z s - Z (f s)) / γ) ^ 2) 1)
  else
    2 * Real.log (max ‖Z s - Z (f s)‖ lam) -
      4 * Real.log (max (min (isoRadius f hN lam (fun k => Z k) (isoPartner s)) γ)
        (displacementScale lam (Z s - Z (f s)))) + c₃

/-- **The energy bound keeping the electric energy** (source l. 2014--2023 and 2038, from the
ball-growth inequality of Step 2 used directly). There are constants `c₁, c₂ ≥ 0` and `c₃` such
that for `N ≥ 2`, `λ > 0`, `γ > 0`, `c ≤ 1/(2π)` and every configuration `Z`, with `f = φ₁(Z)`,
`-2 F_λ(Z) + c ∫ |∇h_α|² ≤ ∑_{i ∉ I^pair} (g_λ(z_i - z_{f i}) + c₁) + ∑_{s ∈ S} E_s`,
where `E_s` is `elecPairExponent`. The factor `e^{c ∫ |∇h_α|²}` is absorbed by the electric energy
term `(1/4π) ∫ |∇h_α|²` of the ball-growth inequality, since `c ≤ 2/(4π)`. -/
theorem exists_neg_two_mul_energy_add_electric_le :
    ∃ c₁ c₂ c₃ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam →
      ∀ γ : ℝ, 0 < γ → ∀ c : ℝ, c ≤ 1 / (2 * Real.pi) → ∀ Z : Fin N ⊕ Fin N → ℂ,
        -2 * energy lam Z + c * ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2 ≤
          ∑ i ∈ (isoPairVerts (nearestNeighbor Z))ᶜ,
              (smearedKernel lam (Z i - Z (nearestNeighbor Z i)) + c₁) +
            ∑ s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)},
              elecPairExponent (nearestNeighbor Z) hN lam γ c₂ c₃ Z s := by
  obtain ⟨Cg, hCg⟩ := exists_smearedKernel_ge
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨2 * |Cg| + 2 * Real.log 4 + 2 * |kappa| + 64, 832,
    2 * |Cg| + 4 * Real.log 3 + 4 * |kappa| + 128, by positivity, by norm_num,
    fun N hN lam hlam γ hγ c hc Z => ?_⟩
  classical
  set f := nearestNeighbor Z with hf
  have hf0 : ∀ i, f i ≠ i := nearestNeighbor_ne Z
  set I := ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2 with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hcI : c * I ≤ 2 * ((1 / (4 * Real.pi)) * I) := by
    have e : 2 * ((1 / (4 * Real.pi)) * I) = (1 / (2 * Real.pi)) * I := by
      field_simp
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hc hI0
  set W : Fin N ⊕ Fin N → ℝ := fun i =>
    if f (f i) = i then -alphaCycleTerm hN lam γ Z i
    else logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa with hW
  -- Step 1: the ball-growth inequality
  have hstep1 : -2 * energy lam Z + c * I ≤ ∑ i, W i := by
    have hmain := energy_ge_electric_alphaRadius hN hlam γ Z
    simp only [ne_eq] at hmain
    have e : ∑ i, W i = -∑ i ∈ univ.filter (fun i => f (f i) = i),
          alphaCycleTerm hN lam γ Z i +
        ∑ i ∈ univ.filter (fun i => ¬ f (f i) = i),
          (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa) := by
      rw [hW, Finset.sum_ite, Finset.sum_neg_distrib]
    have e2 : ∑ i ∈ univ.filter (fun i => f (f i) = i), alphaCycleTerm hN lam γ Z i =
        ∑ i ∈ univ.filter (fun i => f (f i) = i),
          (charge i * charge (f i) * smearedKernel lam (Z i - Z (f i))
            - charge i * (charge i + charge (f i)) *
                (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa)
            - 64 * (firstNeighborRadius lam Z i /
                max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i)) ^ 2) :=
      rfl
    rw [e, e2]
    rw [← hIdef] at hmain
    linarith
  -- Step 2: the vertices outside `I^pair`
  have hstep3 : ∀ i ∈ (isoPairVerts f)ᶜ, W i ≤
      smearedKernel lam (Z i - Z (f i)) + (2 * |Cg| + 2 * Real.log 4 + 2 * |kappa| + 64) := by
    intro i _
    rw [hW]
    dsimp only
    by_cases hcyc : f (f i) = i
    · rw [ite_eq_left hcyc]
      exact neg_alphaCycleTerm_le hN hCg hlam γ Z i
    · rw [ite_eq_right hcyc]
      have := alpha_tree_term_le hN hCg hlam γ Z i
      have := abs_nonneg Cg
      have := abs_nonneg kappa
      linarith
  -- Step 3: the isolated pairs
  have hstep4 : ∀ s : {s // s ∈ isoSecondVerts f}, W s + W (f s) ≤
      elecPairExponent f hN lam γ 832 (2 * |Cg| + 4 * Real.log 3 + 4 * |kappa| + 128) Z s := by
    intro s
    have hs := s.2
    have h2 : f (f s) = s := (mem_isoSecondVerts.1 hs).1.1
    have hWs : W s = -alphaCycleTerm hN lam γ Z s := by rw [hW]; dsimp only; rw [ite_eq_left h2]
    have hWr : W (f s) = -alphaCycleTerm hN lam γ Z (f s) := by
      rw [hW]; dsimp only; rw [ite_eq_left (by rw [h2])]
    rw [hWs, hWr]
    unfold elecPairExponent
    by_cases hn : charge (s : Fin N ⊕ Fin N) * charge (f s) = -1
    · rw [ite_eq_left hn]
      have := neg_alphaCycleTerm_neutral_pair_le hN hlam hγ s hn
      linarith
    · rw [ite_eq_right hn]
      have := neg_alphaCycleTerm_sameSign_pair_le hN hCg hlam γ s hn
      linarith
  -- assembly
  have hsplit : ∑ i, W i = ∑ i ∈ (isoPairVerts f)ᶜ, W i +
      ∑ s : {s // s ∈ isoSecondVerts f}, (W s + W (f s)) := by
    rw [← Finset.sum_compl_add_sum (isoPairVerts f), sum_isoPairVerts hf0,
      Finset.sum_coe_sort (isoSecondVerts f) (fun s => W s + W (f s))]
  have hle1 := Finset.sum_le_sum hstep3
  have hle2 := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hstep4 s)
  have e3 : ∑ i ∈ (isoPairVerts f)ᶜ,
      (smearedKernel lam (Z i - Z (f i)) + (2 * |Cg| + 2 * Real.log 4 + 2 * |kappa| + 64)) =
      ∑ i ∈ (isoPairVerts f)ᶜ, (smearedKernel lam (Z i - Z (nearestNeighbor Z i)) +
        (2 * |Cg| + 2 * Real.log 4 + 2 * |kappa| + 64)) := rfl
  linarith [hstep1, hsplit, hle1, hle2]

end Energy

/-! ### The cell bound of the electric moment -/

section Cell

variable (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) in
/-- The radial weight of the isolated pair of the non-retained endpoint `s` in the electric moment:
neutral or same-sign. -/
noncomputable def elecPairWeight (lam ℓ γ c₂ c₃ : ℝ) (s : {s // s ∈ isoSecondVerts f}) :
    ℂ × ℝ → ℝ≥0∞ :=
  if charge (s : Fin N ⊕ Fin N) * charge (f s) = -1 then elecNeutralWeight lam ℓ γ c₂
  else elecSameSignWeight lam ℓ γ (Real.exp c₃)

theorem measurable_elecPairWeight (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (lam ℓ γ c₂ c₃ : ℝ)
    (s : {s // s ∈ isoSecondVerts f}) : Measurable (elecPairWeight f lam ℓ γ c₂ c₃ s) := by
  unfold elecPairWeight
  split_ifs
  · exact measurable_elecNeutralWeight lam ℓ γ c₂
  · exact measurable_elecSameSignWeight lam ℓ γ (Real.exp c₃)

/-- The pair weight dominates `e^{E_s - |u_s|²/ℓ}` (source l. 1672, 1682): `|u_s| ≤ 4ρ_s`, and
`e^{2 log (|u| ∨ λ) - 4 log M + c₃} = e^{c₃} (|u| ∨ λ)² / M⁴`. -/
theorem ofReal_exp_elecPairExponent_le (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (γ c₂ c₃ : ℝ)
    {Z : Fin N ⊕ Fin N → ℂ} (s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)}) :
    ENNReal.ofReal (Real.exp (elecPairExponent (nearestNeighbor Z) hN lam γ c₂ c₃ Z s -
        ‖Z s - Z (nearestNeighbor Z s)‖ ^ 2 / |Real.log lam|)) ≤
      elecPairWeight (nearestNeighbor Z) lam |Real.log lam| γ c₂ c₃ s
        (Z s - Z (nearestNeighbor Z s),
          isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s)) := by
  have hu4 := norm_sub_le_four_mul_isoRadius rfl hN lam s
  have hρ0 : 0 < isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s) :=
    hlam.trans_le (lam_le_isoRadius hN lam _ _)
  unfold elecPairWeight elecPairExponent
  by_cases hn : charge (s : Fin N ⊕ Fin N) * charge (nearestNeighbor Z s) = -1
  · rw [ite_eq_left hn, ite_eq_left hn]
    unfold elecNeutralWeight
    dsimp only
    rw [ite_eq_left hu4]
    refine le_of_eq (congrArg ENNReal.ofReal (congrArg Real.exp ?_))
    ring
  · rw [ite_eq_right hn, ite_eq_right hn]
    unfold elecSameSignWeight
    dsimp only
    rw [ite_eq_left hu4]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    have hM0 : 0 < max (min (isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s)) γ)
        (displacementScale lam (Z s - Z (nearestNeighbor Z s))) :=
      (displacementScale_pos hlam _).trans_le (le_max_right _ _)
    rw [sub_eq_add_neg, Real.exp_add,
      exp_two_mul_log_sub_four_mul_log (lt_max_of_lt_right hlam) hM0]

/-- **The cell bound of the electric moment** (source l. 2038--2044, repeating l. 1682--1706).
There are constants such that for `N ≥ 2`, `0 < λ ≤ e⁻²`, `2λ ≤ γ ≤ 1`, `c ≤ 1/(2π)` and every
nearest-neighbour graph `f = φ₁(Z₀)`, the integral of `e^{-2F_λ + c ∫ |∇h_α|²}` over the cell
`Λ^{2N} ∩ {φ₁ = f}` is at most `exp (pairCellExponent …)` evaluated at the numbers of components,
isolated pairs and isolated neutral pairs of `f`, with the neutral mass `neutralMass λ γ K C`
("`J_λ(1/ℓ) + CS`") and the same-sign mass `elecSameSignMass` ("`CS`"). -/
theorem exists_lintegral_cell_electric_le :
    ∃ c₁ CJ K Cn c₃ : ℝ, 0 ≤ c₁ ∧ 0 ≤ CJ ∧ 0 ≤ K ∧ 0 ≤ Cn ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam ≤ Real.exp (-2) →
      ∀ γ : ℝ, 2 * lam ≤ γ → γ ≤ 1 → ∀ c : ℝ, c ≤ 1 / (2 * Real.pi) →
      ∀ (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (Z₀ : Fin N ⊕ Fin N → ℂ), nearestNeighbor Z₀ = f →
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f},
            ENNReal.ofReal (Real.exp (-2 * energy lam Z +
              c * ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2)) ≤
          ENNReal.ofReal (Real.exp (pairCellExponent c₁ CJ lam (neutralMass lam γ K Cn)
            (elecSameSignMass lam γ (Real.exp c₃)) N (numComponents Z₀) (numIsolatedPairs Z₀)
            (isolatedDipoles Z₀).card)) := by
  obtain ⟨c₁, c₂, c₃, hc₁, hc₂, hE⟩ := exists_neg_two_mul_energy_add_electric_le
  obtain ⟨K, Cn, hK, hCn, hNW⟩ := exists_lintegral_elecNeutralWeight_le hc₂
  obtain ⟨CJ, hCJ, hcell⟩ := exists_lintegral_cell_le_pairCellExponent
  refine ⟨c₁, CJ, K, Cn, c₃, hc₁, hCJ, hK, hCn, ?_⟩
  intro N hN lam hlam hlam2 γ hγ hγ1 c hc f Z₀ hf₀
  have hle1 : lam ≤ Real.exp (-1) := hlam2.trans (Real.exp_le_exp.2 (by norm_num))
  have hℓ1 := one_le_abs_log hlam hle1
  have hγ0 : 0 < γ := by linarith only [hγ, hlam]
  refine hcell N hN lam hlam hlam2 c₁ _ _ (neutralMass_pos hK hCn hℓ1 hγ0 hγ1)
    (elecSameSignMass_pos (Real.exp_pos _) hℓ1 hγ0 hγ1) f Z₀ hf₀ _
    (elecPairWeight f lam |Real.log lam| γ c₂ c₃)
    (measurable_elecPairWeight f lam |Real.log lam| γ c₂ c₃) ?_ ?_
  · intro s ρ hρ
    unfold elecPairWeight
    split_ifs
    · exact hNW lam γ ρ hlam hle1 hγ hγ1 hρ
    · exact lintegral_elecSameSignWeight_le hlam hle1 hγ hγ1 hρ (Real.exp_pos _).le
  · intro Z hbox _ hZf
    subst hZf
    exact ofReal_exp_le_cell_of_exponent hN hlam hle1 (nearestNeighbor Z) hbox rfl _ _
      (hE N hN lam hlam γ hγ0 c hc Z)
      (fun s => ofReal_exp_elecPairExponent_le hN hlam γ c₂ c₃ s)

end Cell

/-! ### The sum over the graphs (source l. 1709--1739, 2045--2055) -/

section Sum

/-- **The integral of `e^{-2F_λ + c ∫ |∇h_α|²}` over `Λ^{2N}`** (source l. 2045--2055, before the
division by the partition function). There is `C > 0` such that for `N ≥ 2`,
`0 < λ ≤ e⁻²`, `2λ ≤ γ ≤ 1` and `c ≤ 1/(2π)`, with `ℓ = |log λ|`,
`∫_{Λ^{2N}} e^{-2F_λ + c ∫ |∇h_α|²} ≤ exp (2N log N + N (log (2πℓ) - 1)
  + C N (ℓ^{-1/5} + (1 + log ℓ + log (1/γ))/ℓ) + C log (N+1))`. This is the graph sum
(`exists_lintegral_pi_box_le_of_cell_le`); here `ℓ^{-1/5} = ω_λ = errorRate 2 _ λ`. -/
theorem exists_lintegral_exp_electric_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam ≤ Real.exp (-2) →
      ∀ γ : ℝ, 2 * lam ≤ γ → γ ≤ 1 → ∀ c : ℝ, c ≤ 1 / (2 * Real.pi) →
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
            ENNReal.ofReal (Real.exp (-2 * energy lam Z +
              c * ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2)) ≤
          ENNReal.ofReal (Real.exp (2 * N * Real.log N
            + N * (Real.log (2 * Real.pi * |Real.log lam|) - 1)
            + C * N * (|Real.log lam| ^ (-(1 / 5 : ℝ))
              + (1 + Real.log |Real.log lam| + Real.log (1 / γ)) / |Real.log lam|)
            + C * Real.log (N + 1))) := by
  obtain ⟨c₁, CJ, K, Cn, c₃, hc₁, hCJ, hK, hCn, hcell⟩ := exists_lintegral_cell_electric_le
  obtain ⟨C, hC, hsum⟩ := exists_lintegral_pi_box_le_of_cell_le (Cm := 1 + K + Cn)
    (C₀ := 512 * Real.pi * Real.exp c₃) hc₁ hCJ (by positivity) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro N hN lam hlam hlam2 γ hγ hγ1 c hc
  have hle1 : lam ≤ Real.exp (-1) := hlam2.trans (Real.exp_le_exp.2 (by norm_num))
  have hℓ1 := one_le_abs_log hlam hle1
  have hγ0 : 0 < γ := by linarith only [hγ, hlam]
  have hlogγ : 0 ≤ Real.log (1 / γ) := Real.log_nonneg (by rw [le_div_iff₀ hγ0]; linarith only [hγ1])
  exact hsum N hN lam _ _ _ hlam hlam2 (by linarith only [hlogγ])
    (log_neutralMass_le hK hCn hℓ1 hγ0 hγ1) (elecSameSignMass_pos (Real.exp_pos _) hℓ1 hγ0 hγ1)
    (elecSameSignMass_le (Real.exp_pos _).le hℓ1 hγ0 hγ1) _
    (fun f Z₀ hf₀ => hcell N hN lam hlam hlam2 γ hγ hγ1 c hc f Z₀ hf₀)

end Sum

/-! ### Measurability of the electric energy -/

section Measurability

/-- The enlarged radius `τᵢ` of Proposition 2.2 is a measurable function of the configuration. -/
theorem measurable_tau (hN : 2 ≤ N) (lam : ℝ) (i : Fin N ⊕ Fin N) :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => tau hN lam Z i := by
  have hNpos : 0 < N := by omega
  have : Nontrivial (Fin N ⊕ Fin N) :=
    ⟨⟨Sum.inl ⟨0, hNpos⟩, Sum.inr ⟨0, hNpos⟩, Sum.inl_ne_inr⟩⟩
  have h3 : 3 ≤ Fintype.card (Fin N ⊕ Fin N) := by
    rw [Fintype.card_sum, Fintype.card_fin]; omega
  have hr2 : ∀ j, Measurable fun Z : Fin N ⊕ Fin N → ℂ => secondNeighborRadius hN lam Z j := by
    intro j
    have e : (fun Z : Fin N ⊕ Fin N → ℂ => secondNeighborRadius hN lam Z j) =
        fun Z => nnRadius2 h3 (sumKey N) lam Z j :=
      funext fun Z => secondNeighborRadius_eq_nnRadius2 hN h3 lam Z j
    rw [e]
    exact measurable_nnRadius2 (sumKey N) h3 lam j
  have e : (fun Z : Fin N ⊕ Fin N → ℂ => tau hN lam Z i) = fun Z =>
      (fun (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (Z : Fin N ⊕ Fin N → ℂ) =>
        if f (f i) = i then
          min (secondNeighborRadius hN lam Z i) (secondNeighborRadius hN lam Z (f i))
        else secondNeighborRadius hN lam Z i) (nnMap (sumKey N) Z) Z := by
    funext Z
    rw [← nearestNeighbor_eq_nnMap_fun]
    rfl
  rw [e]
  refine measurable_of_nnMap (sumKey N) (γ := ℝ)
    (F := fun (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (Z : Fin N ⊕ Fin N → ℂ) =>
      if f (f i) = i then
        min (secondNeighborRadius hN lam Z i) (secondNeighborRadius hN lam Z (f i))
      else secondNeighborRadius hN lam Z i) fun f => ?_
  by_cases h : f (f i) = i
  · simp only [h, ↓reduceIte]
    exact (hr2 i).min (hr2 (f i))
  · simp only [h, ↓reduceIte]
    exact hr2 i

/-- The first-neighbour radius `r̃₁(zᵢ)` is a measurable function of the configuration. -/
theorem measurable_firstNeighborRadius_apply (hN : 2 ≤ N) (lam : ℝ) (i : Fin N ⊕ Fin N) :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => firstNeighborRadius lam Z i := by
  have hNpos : 0 < N := by omega
  have : Nontrivial (Fin N ⊕ Fin N) :=
    ⟨⟨Sum.inl ⟨0, hNpos⟩, Sum.inr ⟨0, hNpos⟩, Sum.inl_ne_inr⟩⟩
  have e : (fun Z : Fin N ⊕ Fin N → ℂ => firstNeighborRadius lam Z i) =
      fun Z => nnRadius lam Z i := funext fun Z => firstNeighborRadius_eq_nnRadius lam Z i
  rw [e]
  exact measurable_nnRadius lam i

/-- The radius `αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)` is a measurable function of the configuration. -/
theorem measurable_alphaRadius (hN : 2 ≤ N) (lam γ : ℝ) (i : Fin N ⊕ Fin N) :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => alphaRadius hN lam γ Z i :=
  ((measurable_tau hN lam i).min measurable_const).max
    (measurable_firstNeighborRadius_apply hN lam i)

/-- **The electric energy `∫ |∇h_α|²` of the grown discs is a measurable function of the
configuration**: the field `∇h_α(x) = ∑ᵢ dᵢ discField (αᵢ) (x - zᵢ)` is jointly measurable in the
configuration and the point. -/
theorem measurable_integral_norm_sq_electricField_alphaRadius (hN : 2 ≤ N) (lam γ : ℝ) :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ =>
      ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2 := by
  have hE : Measurable fun p : (Fin N ⊕ Fin N → ℂ) × ℂ =>
      ‖electricField charge p.1 (alphaRadius hN lam γ p.1) p.2‖ ^ 2 := by
    unfold electricField discField
    refine (Measurable.norm (Finset.measurable_sum _ fun i _ => ?_)).pow_const 2
    have hα : Measurable fun p : (Fin N ⊕ Fin N → ℂ) × ℂ => alphaRadius hN lam γ p.1 i :=
      (measurable_alphaRadius hN lam γ i).comp measurable_fst
    have hu : Measurable fun p : (Fin N ⊕ Fin N → ℂ) × ℂ => p.2 - p.1 i :=
      measurable_snd.sub ((measurable_pi_apply i).comp measurable_fst)
    exact (((hα.max hu.norm).pow_const 2).inv.neg.smul hu).const_smul (charge i)
  exact (hE.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

end Measurability

/-! ### The exponential moment of the electric energy (eq. (eq:critical electric)) -/

section Moment

/-- `log ℓ / ℓ ≤ (5/4) ℓ^{-1/5}` for `ℓ ≥ 1` (`ℓ^{-1/5} = errorRate 2 _ λ` for `ℓ = |log λ|`). -/
private theorem log_div_le_rpow_neg_fifth {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    Real.log ℓ / ℓ ≤ (5 / 4) * ℓ ^ (-(1 / 5 : ℝ)) := by
  have hℓ0 : 0 < ℓ := by linarith only [hℓ]
  have h1 := Real.log_le_rpow_div hℓ0.le (show (0 : ℝ) < 4 / 5 by norm_num)
  have e : ℓ ^ (4 / 5 : ℝ) = ℓ ^ (-(1 / 5 : ℝ)) * ℓ := by
    rw [← Real.rpow_add_one hℓ0.ne']
    norm_num
  rw [div_le_iff₀ hℓ0]
  rw [e] at h1
  have : ℓ ^ (-(1 / 5 : ℝ)) * ℓ / (4 / 5) = (5 / 4) * ℓ ^ (-(1 / 5 : ℝ)) * ℓ := by ring
  linarith only [h1, this]

/-- **Theorem 2, eq. (eq:critical electric)** (source l. 2023--2060, which states
"`ℓ^{-1/5} = ω_λ`"): there are `C, λ₁ > 0` such that for every `c ≤ 1/(2π)`, `N ≥ 2`,
`0 < λ < λ₁` and `2λ ≤ γ ≤ 1`, with the radii `αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)` (`alphaRadius`),
`𝔼_ℙ[e^{c ∫ |∇h_α|²}] ≤ exp (C N (φ₂(γ) + ω_λ) + C log (N+1))`
for the Gibbs measure `ℙ = ℙ_{N,2}^λ`. Here `φ₂(γ) = (1 + |log γ|)/|log λ|` (`isolatedPhi`) and
`ω_λ = errorRate 2 _ λ = ℓ^{-1/5}`. -/
theorem critical_electric :
    ∃ C lam₁ : ℝ, 0 < C ∧ 0 < lam₁ ∧ ∀ c : ℝ, c ≤ 1 / (2 * Real.pi) →
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam γ : ℝ), 0 < lam → lam < lam₁ → 2 * lam ≤ γ → γ ≤ 1 →
        ∫⁻ Z, ENNReal.ofReal (Real.exp
            (c * ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2))
            ∂gibbsMeasure N 2 lam
          ≤ ENNReal.ofReal (Real.exp (C * N *
              (isolatedPhi 2 le_rfl lam γ + errorRate 2 le_rfl lam) + C * Real.log (N + 1))) := by
  obtain ⟨C₁, hC₁, hup⟩ := exists_lintegral_exp_electric_le
  obtain ⟨lam₀, C₂, hlam₀, hC₂, hlow⟩ := proposition_4_1 2 le_rfl
  refine ⟨3 * C₁ + C₂, min lam₀ (Real.exp (-2)), by positivity,
    lt_min hlam₀ (Real.exp_pos _), ?_⟩
  intro c hc N hN lam γ hlam hlam1 hγ hγ1
  have hlam2 : lam ≤ Real.exp (-2) := (hlam1.trans_le (min_le_right _ _)).le
  have hlam0 : lam < lam₀ := hlam1.trans_le (min_le_left _ _)
  have hlog : Real.log lam ≤ -2 := by
    have := Real.log_le_log hlam hlam2
    rwa [Real.log_exp] at this
  set ℓ := |Real.log lam| with hℓdef
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef, abs_of_neg (by linarith)]; linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hγ0 : 0 < γ := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN1 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  -- the rates
  have hω : errorRate 2 le_rfl lam = ℓ ^ (-(1 / 5 : ℝ)) := by simp [errorRate, hℓdef]
  have hφ : isolatedPhi 2 le_rfl lam γ = (1 + Real.log (1 / γ)) / ℓ := by
    rw [isolatedPhi_of_eq_two le_rfl rfl, one_div, Real.log_inv,
      abs_of_nonpos (Real.log_nonpos hγ0.le hγ1)]
  rw [hω, hφ]
  -- the upper bound
  have hU := hup N hN lam hlam hlam2 γ hγ hγ1 c hc
  -- the lower bound on the partition function (Proposition 4.1 at `β = 2`)
  have hL := hlow N hN lam hlam hlam0
  simp only [ite_true] at hL
  have hdc : Real.log (dipoleConstant 2 le_rfl) = Real.log (2 * Real.pi) := by
    simp [dipoleConstant]
  rw [hdc] at hL
  set lower := 2 * N * Real.log N + N * (Real.log ℓ + (Real.log (2 * Real.pi) - 1))
    - C₂ * N * ℓ ^ (-(1 / 5 : ℝ)) with hlower
  set upper := 2 * N * Real.log N + N * (Real.log (2 * Real.pi * ℓ) - 1)
    + C₁ * N * (ℓ ^ (-(1 / 5 : ℝ)) + (1 + Real.log ℓ + Real.log (1 / γ)) / ℓ)
    + C₁ * Real.log (N + 1) with hupper
  -- the expectation
  rw [lintegral_gibbsMeasure']
  have hint : ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
      ENNReal.ofReal (Real.exp (c * ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2)) *
        ENNReal.ofReal (Real.exp (-2 * energy lam Z)) =
      ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
        ENNReal.ofReal (Real.exp (-2 * energy lam Z +
          c * ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2)) := by
    refine lintegral_congr fun Z => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_comm]
  rw [hint]
  have hZinv : (partitionFunction N 2 lam)⁻¹ ≤ ENNReal.ofReal (Real.exp (-lower)) := by
    rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]
    exact ENNReal.inv_le_inv.2 hL
  calc (partitionFunction N 2 lam)⁻¹ *
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
          ENNReal.ofReal (Real.exp (-2 * energy lam Z +
            c * ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2))
      ≤ ENNReal.ofReal (Real.exp (-lower)) * ENNReal.ofReal (Real.exp upper) :=
        mul_le_mul' hZinv hU
    _ = ENNReal.ofReal (Real.exp (upper - lower)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_eq_sub]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        -- the comparison of the rates
        have h2πℓ : Real.log (2 * Real.pi * ℓ) = Real.log (2 * Real.pi) + Real.log ℓ :=
          Real.log_mul (by positivity) hℓ0.ne'
        have hω0 : 0 ≤ ℓ ^ (-(1 / 5 : ℝ)) := by positivity
        have hlogℓℓ := log_div_le_rpow_neg_fifth hℓ1
        have hS : (1 + Real.log ℓ + Real.log (1 / γ)) / ℓ =
            (1 + Real.log (1 / γ)) / ℓ + Real.log ℓ / ℓ := by ring
        have hφ0 : 0 ≤ (1 + Real.log (1 / γ)) / ℓ := by
          have : 0 ≤ Real.log (1 / γ) := Real.log_nonneg (by rw [le_div_iff₀ hγ0]; linarith)
          positivity
        have hA : C₁ * N * (ℓ ^ (-(1 / 5 : ℝ)) + (1 + Real.log ℓ + Real.log (1 / γ)) / ℓ) ≤
            3 * C₁ * N * ((1 + Real.log (1 / γ)) / ℓ + ℓ ^ (-(1 / 5 : ℝ))) := by
          rw [hS]
          have hCN : 0 ≤ C₁ * N := by positivity
          have : ℓ ^ (-(1 / 5 : ℝ)) + ((1 + Real.log (1 / γ)) / ℓ + Real.log ℓ / ℓ) ≤
              3 * ((1 + Real.log (1 / γ)) / ℓ + ℓ ^ (-(1 / 5 : ℝ))) := by linarith
          have := mul_le_mul_of_nonneg_left this hCN
          linarith
        have hB : C₂ * N * ℓ ^ (-(1 / 5 : ℝ)) ≤
            C₂ * N * ((1 + Real.log (1 / γ)) / ℓ + ℓ ^ (-(1 / 5 : ℝ))) := by
          have hCN : 0 ≤ C₂ * N := by positivity
          exact mul_le_mul_of_nonneg_left (by linarith) hCN
        have hD : C₁ * Real.log (N + 1) ≤ (3 * C₁ + C₂) * Real.log (N + 1) := by
          have h2 := mul_nonneg hC₂.le hlogN1
          have h1 := mul_nonneg hC₁.le hlogN1
          linarith only [h1, h2]
        have e : (3 * C₁ + C₂) * N * ((1 + Real.log (1 / γ)) / ℓ + ℓ ^ (-(1 / 5 : ℝ))) =
            3 * C₁ * N * ((1 + Real.log (1 / γ)) / ℓ + ℓ ^ (-(1 / 5 : ℝ))) +
              C₂ * N * ((1 + Real.log (1 / γ)) / ℓ + ℓ ^ (-(1 / 5 : ℝ))) := by ring
        have hN2 : (N : ℝ) * (Real.log (2 * Real.pi * ℓ) - 1) =
            N * (Real.log ℓ + (Real.log (2 * Real.pi) - 1)) := by rw [h2πℓ]; ring
        rw [hupper, hlower, e]
        linarith

/-- **The β = 2 instance of items (ii)--(iii) of `MomentBoundRate 2 _ (errorRate 2 _)`** (source
l. 2023--2060): `critical_electric` with `ω_λ = errorRate 2 _ λ = ℓ^{-1/5}`. With `c = 1/(2π)`
and the radii `αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)` (`alphaRadius`; item (i) is `alphaRadius_pos` and
`alphaRadius_le_max`), there are `C, λ₁ > 0` such that for `N ≥ 2`, `0 < λ < λ₁` and
`2λ ≤ γ ≤ 1`, `Z ↦ ∫ |∇h_α|²` is almost-everywhere measurable for the Gibbs measure and
`𝔼[exp (c ∫ |∇h_α|²)] ≤ exp (C N (φ₂(γ) + ω_λ) + C log (N+1))`. -/
theorem exists_momentBound_two :
    ∃ (c C lam₁ : ℝ), 0 < c ∧ 0 < C ∧ 0 < lam₁ ∧
      (∀ (N : ℕ) (hN : 2 ≤ N) (lam γ : ℝ), 0 < lam → lam < lam₁ → 2 * lam ≤ γ → γ ≤ 1 →
        AEMeasurable (fun Z : Fin N ⊕ Fin N → ℂ =>
          ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2) (gibbsMeasure N 2 lam)) ∧
      (∀ (N : ℕ) (hN : 2 ≤ N) (lam γ : ℝ), 0 < lam → lam < lam₁ → 2 * lam ≤ γ → γ ≤ 1 →
        ∫⁻ Z, ENNReal.ofReal (Real.exp
            (c * ∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2))
            ∂gibbsMeasure N 2 lam
          ≤ ENNReal.ofReal (Real.exp (C * N *
              (isolatedPhi 2 le_rfl lam γ + errorRate 2 le_rfl lam)
            + C * Real.log (N + 1)))) := by
  obtain ⟨C, lam₁, hC, hlam₁, h⟩ := critical_electric
  exact ⟨1 / (2 * Real.pi), C, lam₁, by positivity, hC, hlam₁,
    fun N hN lam γ _ _ _ _ =>
      (measurable_integral_norm_sq_electricField_alphaRadius hN lam γ).aemeasurable,
    fun N hN lam γ hlam hlam1 hγ hγ1 => h _ le_rfl N hN lam γ hlam hlam1 hγ hγ1⟩

end Moment

end TwoComponentCoulomb

end
