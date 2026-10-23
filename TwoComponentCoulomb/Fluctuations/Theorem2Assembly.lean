/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.FluctElectric
public import TwoComponentCoulomb.Fluctuations.RadiiControlProb
public import TwoComponentCoulomb.Fluctuations.Theorem2AssemblyRates
public import TwoComponentCoulomb.Fluctuations.Theorem2Rate
public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.Energy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TwoComponentCoulomb.Frozen.M0
public import TwoComponentCoulomb.Frozen.FirstNeighborRadius
public import TwoComponentCoulomb.Frozen.Fluct
public import TwoComponentCoulomb.Frozen.GibbsMeasure
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.Frozen.PartitionFunction
public import TwoComponentCoulomb.Frozen.ReducedEnergy
public import TwoComponentCoulomb.Potential.Electric
import TwoComponentCoulomb.Fluctuations.RadiiControl
import TwoComponentCoulomb.Gibbs.Basic
import TwoComponentCoulomb.Main.Theorem1AssemblyBounds
import TwoComponentCoulomb.NearestNeighbor.Second

/-!
# Theorem 2, Steps 5--6: conclusion, as a conditional helper

Source: proof of Theorem 2, Steps 5--6 (l. 2060–2121); the statement is l. 294–302.

`theorem_2_of_moment_rate` is a *conditional helper*, stated for a rate function `ω` in place of
`ω_λ`: it takes the rate properties `Theorem2RateHyp β hβ ω` (`Fluctuations/Theorem2Rate.lean`),
the statement of Theorem 1 with `ω` (`Theorem1ShapeRate β hβ ω`) and the exponential moment bound
of Steps 2--4 with `ω` (`MomentBoundRate β hβ ω`), and concludes the statement of Theorem 2 with
`ω`. It is not a frozen statement and never stands in for one; the proof of `theorem_2`
(`Main/Theorem2.lean`) applies it at `ω = errorRate β hβ`.

`MomentBoundRate β hβ ω` records the output of Steps 2--4 (l. 1872–2058, and Step 6 l. 2086–2093,
Hölder combination of (eq:A1), (eq:A2), (eq:finalA3)) in the weak form used by Steps 5--6: radii
`αᵢ` (in the source `αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)`, so `0 < αᵢ ≤ γ ∨ r̃₁(zᵢ)`) for which the electric
energy `∫ |∇h_α|²` has an exponential moment
`𝔼[exp(c ∫ |∇h_α|²)] ≤ exp(C N (φ_β(γ) + ω(λ)) + C log (N+1))`.

The assembly follows the source:

* Step 5: the event `A_M` and `ℙ(A_Mᶜ) ≤ C (N+1)^C e^{-c M N ω}` (eq. (eq:PAM),
  `exists_gibbsMeasure_eventARate_compl_le`); on `A_M`, `(Σ r̃₁)² ≤ (8 + 12 M) N² √ω`
  (eq. (eq:sumrr1), `sq_sum_firstNeighborRadius_le`).
* Step 6: Markov's inequality gives the event `B_M = {∫ |∇h_α|² ≤ (2/c) M N (φ_β(γ) + ω)}` with
  `ℙ(B_Mᶜ) ≤ (N+1)^C e^{-M N ω}` (the electric-energy tail bound of Step 6, `gibbsMeasure_electric_compl_le`); Step 1 and
  `α_i ≤ γ + r̃₁(z_i)` give `Fluct² ≤ C M L² N (γ² + √ω + φ_β(γ))` on `A_M ∩ B_M`
  (eq. (eq:f), `exists_fluct_sq_le_of_good_rate`); the choice of `γ` (`gammaChoice`) makes
  `φ_β(γ) + γ² ≤ 3 √ω`; finally the polynomial prefactor is absorbed
  (`exists_min_one_le_exp`) and `M` is rescaled.

Main declarations: `MomentBoundRate`, `exists_fluct_sq_le_of_good_rate`,
`theorem_2_of_moment_rate`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace TwoComponentCoulomb

/-! ### The exponential moment bound of Steps 3--4 -/

/-- **The moment bound of Steps 2--4 for a general rate function `ω`** (source l. 1872–2093):
there are radii `αᵢ` and `c, C, λ₁ > 0` such that, for `N ≥ 2`, `0 < λ < λ₁` and `2λ ≤ γ ≤ 1`,
(i) `0 < αᵢ ≤ γ ∨ r̃₁(zᵢ)`, (ii) `Z ↦ ∫ |∇h_α|²` is almost-everywhere measurable for the Gibbs
measure, and (iii) `𝔼[exp(c ∫ |∇h_α|²)] ≤ exp(C N (φ_β(γ) + ω(λ)) + C log (N+1))`.
For `ω = errorRate β hβ` it is proved in `momentBound` (`Fluctuations/Moment.lean`). This is a
hypothesis of the conditional helper `theorem_2_of_moment_rate` only. -/
def MomentBoundRate (β : ℝ) (hβ : 2 ≤ β) (ω : ℝ → ℝ) : Prop :=
  ∃ (α : ∀ N : ℕ, ℝ → ℝ → (Fin N ⊕ Fin N → ℂ) → Fin N ⊕ Fin N → ℝ) (c C lam₁ : ℝ),
    0 < c ∧ 0 < C ∧ 0 < lam₁ ∧
    (∀ N : ℕ, 2 ≤ N → ∀ lam γ : ℝ, 0 < lam → lam < lam₁ → 2 * lam ≤ γ → γ ≤ 1 →
      ∀ (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N),
        0 < α N lam γ Z i ∧ α N lam γ Z i ≤ max γ (firstNeighborRadius lam Z i)) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ lam γ : ℝ, 0 < lam → lam < lam₁ → 2 * lam ≤ γ → γ ≤ 1 →
      AEMeasurable (fun Z : Fin N ⊕ Fin N → ℂ =>
        ∫ x, ‖electricField charge Z (α N lam γ Z) x‖ ^ 2) (gibbsMeasure N β lam)) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ lam γ : ℝ, 0 < lam → lam < lam₁ → 2 * lam ≤ γ → γ ≤ 1 →
      ∫⁻ Z, ENNReal.ofReal (Real.exp (c * ∫ x, ‖electricField charge Z (α N lam γ Z) x‖ ^ 2))
          ∂gibbsMeasure N β lam
        ≤ ENNReal.ofReal (Real.exp (C * N * (isolatedPhi β hβ lam γ + ω lam)
          + C * Real.log (N + 1))))

/-! ### Markov's inequality and the support of the Gibbs measure -/

/-- Exponential Markov inequality: if `𝔼[e^{c f}] ≤ e^E` then `ℙ(f > T) ≤ e^{E - c T}`. -/
theorem measure_lt_le_of_lintegral_exp_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : AEMeasurable f μ) {c T E : ℝ} (hc : 0 < c)
    (h : ∫⁻ x, ENNReal.ofReal (Real.exp (c * f x)) ∂μ ≤ ENNReal.ofReal (Real.exp E)) :
    μ {x | T < f x} ≤ ENNReal.ofReal (Real.exp (E - c * T)) := by
  have hg : AEMeasurable (fun x => ENNReal.ofReal (Real.exp (c * f x))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.measurable_exp.comp_aemeasurable (hf.const_mul c))
  have hε0 : ENNReal.ofReal (Real.exp (c * T)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hsub : {x | T < f x} ⊆ {x | ENNReal.ofReal (Real.exp (c * T)) ≤
      ENNReal.ofReal (Real.exp (c * f x))} := fun x hx =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_of_lt hx) hc.le))
  calc μ {x | T < f x}
      ≤ μ {x | ENNReal.ofReal (Real.exp (c * T)) ≤ ENNReal.ofReal (Real.exp (c * f x))} :=
        measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal (Real.exp (c * f x)) ∂μ) / ENNReal.ofReal (Real.exp (c * T)) :=
        meas_ge_le_lintegral_div hg hε0 ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp E) / ENNReal.ofReal (Real.exp (c * T)) :=
        ENNReal.div_le_div_right h _
    _ = ENNReal.ofReal (Real.exp (E - c * T)) := by
        rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]

/-- The Gibbs measure is supported on the box `Λ^{2N}`. -/
theorem gibbsMeasure_compl_pi_box (N : ℕ) (β lam : ℝ) :
    gibbsMeasure N β lam (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N)ᶜ = 0 := by
  rw [gibbsMeasure_apply', Set.inter_compl_self, Measure.restrict_empty, lintegral_zero_measure,
    mul_zero]

/-! ### The deterministic combination (eq:f) -/

/-- The algebra behind (eq:f), source l. 2101–2104: from
`F ≤ C_F L² (I + S²/N)`, `I ≤ (2/c) M N (φ + ω)`, `S ≤ 2 N γ + S₁`, `S₁² ≤ (8 + 12 M) N² √ω`,
`φ + γ² ≤ K √ω` and `ω ≤ √ω`, `M ≥ 1`, one gets `F ≤ C_F ((2/c)(K+1) + 8K + 40) M L² N √ω`. -/
theorem fluct_algebra {F CF L2 I S S₁ N M c φ ω γ K : ℝ} (hCF : 0 ≤ CF) (hL2 : 0 ≤ L2)
    (hN : 0 < N) (hc : 0 < c) (hM : 1 ≤ M) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hφ : 0 ≤ φ)
    (hK : 0 ≤ K) (hF : F ≤ CF * L2 * (I + S ^ 2 / N)) (hI : I ≤ 2 / c * M * N * (φ + ω))
    (hS0 : 0 ≤ S) (hS : S ≤ 2 * N * γ + S₁)
    (hS₁ : S₁ ^ 2 ≤ (8 + 12 * M) * N ^ 2 * Real.sqrt ω) (hφγ : φ + γ ^ 2 ≤ K * Real.sqrt ω) :
    F ≤ CF * (2 / c * (K + 1) + 8 * K + 40) * M * L2 * N * Real.sqrt ω := by
  have hs0 : 0 ≤ Real.sqrt ω := Real.sqrt_nonneg ω
  have hsω : ω ≤ Real.sqrt ω := by
    calc ω = Real.sqrt ω * Real.sqrt ω := (Real.mul_self_sqrt hω0).symm
      _ ≤ Real.sqrt ω * 1 := by
          have : Real.sqrt ω ≤ 1 := by
            rw [Real.sqrt_le_one]
            exact hω1
          gcongr
      _ = Real.sqrt ω := mul_one _
  set s := Real.sqrt ω with hs
  have hM0 : 0 ≤ M := by linarith
  have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg γ
  have hφK : φ ≤ K * s := by linarith
  have hγK : γ ^ 2 ≤ K * s := by linarith
  -- the square of `S`
  have hSsq : S ^ 2 ≤ 8 * N ^ 2 * γ ^ 2 + 2 * ((8 + 12 * M) * N ^ 2 * s) := by
    have h1 : S ^ 2 ≤ (2 * N * γ + S₁) ^ 2 := pow_le_pow_left₀ hS0 hS 2
    linarith only [h1, sq_nonneg (2 * N * γ - S₁), hS₁]
  have hSN : S ^ 2 / N ≤ 8 * N * γ ^ 2 + (16 + 24 * M) * N * s := by
    rw [div_le_iff₀ hN]
    have : (8 * N * γ ^ 2 + (16 + 24 * M) * N * s) * N =
        8 * N ^ 2 * γ ^ 2 + 2 * ((8 + 12 * M) * N ^ 2 * s) := by ring
    rw [this]
    exact hSsq
  have hIs : I ≤ 2 / c * M * N * (φ + s) := by
    refine hI.trans ?_
    have : 0 ≤ 2 / c * M * N := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  have hB : I + S ^ 2 / N ≤ (2 / c * (K + 1) + 8 * K + 40) * M * N * s := by
    have h1 : 2 / c * M * N * (φ + s) ≤ 2 / c * M * N * ((K + 1) * s) := by
      have : 0 ≤ 2 / c * M * N := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith only [hφK]) this
    have h2 : 8 * N * γ ^ 2 ≤ 8 * N * (K * s) := by
      exact mul_le_mul_of_nonneg_left hγK (by positivity)
    have h3 : 8 * N * (K * s) ≤ 8 * K * M * N * s := by
      have : 0 ≤ 8 * K * N * s := by positivity
      linarith only [mul_nonneg (sub_nonneg.2 hM) this]
    have h4 : (16 + 24 * M) * N * s ≤ 40 * M * N * s := by
      have : 0 ≤ N * s := by positivity
      linarith only [mul_nonneg (sub_nonneg.2 hM) this]
    linarith only [hIs, h1, hSN, h2, h3, h4]
  have hCL : 0 ≤ CF * L2 := mul_nonneg hCF hL2
  calc F ≤ CF * L2 * (I + S ^ 2 / N) := hF
    _ ≤ CF * L2 * ((2 / c * (K + 1) + 8 * K + 40) * M * N * s) :=
        mul_le_mul_of_nonneg_left hB hCL
    _ = _ := by ring

/-- **(eq:f) for a general rate function `ω`**, source l. 2101–2104: there
is an absolute constant `C_F` such that, for `0 < ω(λ) ≤ 1`, a configuration `Z` in the box lying
in `A_M` (`eventARate`), radii `0 < αᵢ ≤ γ ∨ r̃₁(zᵢ)` whose electric energy satisfies
`∫ |∇h_α|² ≤ (2/c) M N (φ_β(γ) + ω(λ))` and `φ_β(γ) + γ² ≤ K √ω(λ)`,
`Fluct_N(ξ₀(·/√N))² ≤ C_F ((2/c)(K+1) + 8K + 40) M L² N √ω(λ)`. -/
theorem exists_fluct_sq_le_of_good_rate :
    ∃ CF : ℝ, 0 < CF ∧ ∀ (β : ℝ) (hβ : 2 ≤ β) (ω : ℝ → ℝ) {c K : ℝ}, 0 < c → 0 ≤ K →
      ∀ {N : ℕ}, 2 ≤ N → ∀ {lam γ M : ℝ}, 0 < lam → lam < Real.exp (-1) → 0 < ω lam →
      ω lam ≤ 1 → 1 ≤ M → lam ≤ γ →
      2 * lam ≤ R0Rate β ω lam → R0Rate β ω lam ≤ ω lam ^ (1 / 4 : ℝ) →
      isolatedPhi β hβ lam γ + γ ^ 2 ≤ K * Real.sqrt (ω lam) →
      ∀ {ξ₀ : ℂ → ℝ}, HasCompactSupport ξ₀ → ∀ {L : ℝ≥0}, LipschitzWith L ξ₀ →
      ∀ {Z : Fin N ⊕ Fin N → ℂ}, (∀ i, Z i ∈ box N) → Z ∈ eventARate β ω N lam M →
      ∀ {α : Fin N ⊕ Fin N → ℝ}, (∀ i, 0 < α i) →
        (∀ i, α i ≤ max γ (firstNeighborRadius lam Z i)) →
        (∫ x, ‖electricField charge Z α x‖ ^ 2) ≤
          2 / c * M * N * (isolatedPhi β hβ lam γ + ω lam) →
        fluct (fun x => ξ₀ ((Real.sqrt N)⁻¹ • x)) Z ^ 2 ≤
          CF * (2 / c * (K + 1) + 8 * K + 40) * M * (L : ℝ) ^ 2 * N * Real.sqrt (ω lam) := by
  obtain ⟨CF, hCF, hstep1⟩ := exists_fluct_sq_le
  refine ⟨CF, hCF, fun β hβ ω c K hc hK N hN lam γ M h0 hle hω0 hω1 hM hlγ hR2 hR4 hφγ ξ₀ hξ₀ L hL
    Z hZ hA α hα0 hαle hI => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam1 : lam < 1 := hle.trans (Real.exp_lt_one_iff.2 (by norm_num))
  have hγ0 : 0 ≤ γ := h0.le.trans hlγ
  have hφ0 : 0 ≤ isolatedPhi β hβ lam γ := isolatedPhi_nonneg hβ h0 hlγ
  have hstep := hstep1 N (by omega) ξ₀ hξ₀ L hL Z hZ α hα0
  -- the sum of the radii
  have hr0 : ∀ i, 0 ≤ firstNeighborRadius lam Z i := fun i =>
    (h0.trans_le (lam_le_firstNeighborRadius lam Z i)).le
  have hcard : Fintype.card (Fin N ⊕ Fin N) = 2 * N := by
    rw [Fintype.card_sum, Fintype.card_fin]; ring
  have hS : ∑ i, α i ≤ 2 * N * γ + ∑ i, firstNeighborRadius lam Z i := by
    calc ∑ i, α i ≤ ∑ i, (γ + firstNeighborRadius lam Z i) :=
          Finset.sum_le_sum fun i _ => (hαle i).trans (max_le (by linarith [hr0 i])
            (by linarith))
      _ = 2 * N * γ + ∑ i, firstNeighborRadius lam Z i := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
          push_cast
          ring
  have hS0 : 0 ≤ ∑ i, α i := Finset.sum_nonneg fun i _ => (hα0 i).le
  -- the sum of the first-neighbour radii on `A_M`
  have hR0 : 0 ≤ R0Rate β ω lam := by linarith
  have hS₁ := sq_sum_firstNeighborRadius_le h0 hlam1.le hR2 Z hZ hA
  have hR0sq := sq_le_sqrt_of_le_rpow_quarter hR0 hω0.le hR4
  have hS₁' : (∑ i, firstNeighborRadius lam Z i) ^ 2 ≤
      (8 + 12 * M) * (N : ℝ) ^ 2 * Real.sqrt (ω lam) := by
    refine hS₁.trans ?_
    have h1 : 8 * (N : ℝ) ^ 2 * R0Rate β ω lam ^ 2 ≤ 8 * (N : ℝ) ^ 2 * Real.sqrt (ω lam) :=
      mul_le_mul_of_nonneg_left hR0sq (by positivity)
    linarith only [h1]
  have := fluct_algebra (F := fluct (fun x => ξ₀ ((Real.sqrt N)⁻¹ • x)) Z ^ 2) (CF := CF)
    (L2 := (L : ℝ) ^ 2) (I := ∫ x, ‖electricField charge Z α x‖ ^ 2) (S := ∑ i, α i)
    (S₁ := ∑ i, firstNeighborRadius lam Z i) (N := N) (M := M) (c := c)
    (φ := isolatedPhi β hβ lam γ) (ω := ω lam) (γ := γ) (K := K) hCF.le
    (sq_nonneg _) hN0 hc hM hω0.le hω1 hφ0 hK hstep hI hS0 hS hS₁' hφγ
  linarith

/-! ### The event `B_M` (the electric-energy tail bound of Step 6) -/

/-- **the electric-energy tail bound of Step 6, source l. 2094–2100**: Markov's inequality for the electric energy. If
`𝔼[exp(c f)] ≤ exp(C N (φ + ω) + C log (N+1))`, `φ, ω ≥ 0` and `M ≥ C`, then
`ℙ(f > (2/c) M N (φ + ω)) ≤ (N+1)^C e^{-M N ω}`. -/
theorem gibbsMeasure_electric_compl_le {N : ℕ} {β lam : ℝ}
    {f : (Fin N ⊕ Fin N → ℂ) → ℝ} (hf : AEMeasurable f (gibbsMeasure N β lam))
    {c C φ ω M : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hM : C ≤ M) (hφ : 0 ≤ φ) (hω : 0 ≤ ω)
    (h : ∫⁻ Z, ENNReal.ofReal (Real.exp (c * f Z)) ∂gibbsMeasure N β lam
      ≤ ENNReal.ofReal (Real.exp (C * N * (φ + ω) + C * Real.log (N + 1)))) :
    gibbsMeasure N β lam {Z | 2 / c * M * N * (φ + ω) < f Z}
      ≤ ENNReal.ofReal (Real.exp (C * Real.log (N + 1) - M * N * ω)) := by
  refine (measure_lt_le_of_lintegral_exp_le hf hc h).trans ?_
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : c * (2 / c * M * N * (φ + ω)) = 2 * (M * N * (φ + ω)) := by
    field_simp
  rw [h1]
  have h2 : 0 ≤ N * (φ + ω) := by positivity
  have h3 : N * ω ≤ N * (φ + ω) := mul_le_mul_of_nonneg_left (by linarith only [hφ]) hN
  have hM0 : 0 ≤ M := hC.trans hM
  linarith only [mul_nonneg (sub_nonneg.2 hM) h2, mul_le_mul_of_nonneg_left h3 hM0]

/-! ### Set-theoretic and measure-theoretic bookkeeping -/

/-- The bad event is contained in `A_Mᶜ ∪ B_Mᶜ ∪ (Λ^{2N})ᶜ`, because on `Λ^{2N} ∩ A_M ∩ B_M` the
fluctuation is controlled. -/
theorem bad_subset_union {N : ℕ} {Fl f : (Fin N ⊕ Fin N → ℂ) → ℝ}
    {A : Set (Fin N ⊕ Fin N → ℂ)} {T b : ℝ}
    (hgood : ∀ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) → Z ∈ A → f Z ≤ T → Fl Z ≤ b) :
    {Z | b < Fl Z} ⊆
      (Aᶜ ∪ {Z | T < f Z}) ∪ (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N)ᶜ := by
  intro Z hZ
  by_contra hcon
  simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_ofPred_eq,
    not_lt] at hcon
  obtain ⟨⟨hZA, hZB⟩, hZbox⟩ := hcon
  have := hgood Z (Set.mem_univ_pi.1 hZbox) hZA hZB
  simp only [Set.mem_ofPred_eq] at hZ
  linarith

/-- A probability bound from the three exceptional events, capped at `1`. -/
theorem measure_le_min_one_of_subset {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {bad A B T : Set X} (hbad : bad ⊆ (Aᶜ ∪ B) ∪ T) (hT : μ T = 0)
    {a₁ a₂ e : ℝ} (hA : μ Aᶜ ≤ ENNReal.ofReal (2 * Real.exp a₁))
    (hB : μ B ≤ ENNReal.ofReal (Real.exp a₂)) (h1 : a₁ ≤ e) (h2 : a₂ ≤ e) :
    μ bad ≤ ENNReal.ofReal (min 1 (3 * Real.exp e)) := by
  have e1 := Real.exp_le_exp.2 h1
  have e2 := Real.exp_le_exp.2 h2
  have hsum : μ bad ≤ ENNReal.ofReal (3 * Real.exp e) := by
    calc μ bad ≤ μ ((Aᶜ ∪ B) ∪ T) := measure_mono hbad
      _ ≤ (μ Aᶜ + μ B) + μ T := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ (ENNReal.ofReal (2 * Real.exp a₁) + ENNReal.ofReal (Real.exp a₂)) + 0 := by
          rw [hT]
          exact add_le_add (add_le_add hA hB) le_rfl
      _ = ENNReal.ofReal (2 * Real.exp a₁ + Real.exp a₂) := by
          rw [add_zero, ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (3 * Real.exp e) := ENNReal.ofReal_le_ofReal (by linarith)
  rw [ENNReal.ofReal_min]
  refine le_min ?_ hsum
  rw [ENNReal.ofReal_one]
  exact prob_le_one

/-- Comparison of the exponents of `A_Mᶜ` and `B_Mᶜ` with a common one. -/
theorem exponent_le_common {CA C cA L P : ℝ} (hL : 0 ≤ L) (hP : 0 ≤ P) :
    CA * L - cA * P ≤ max CA C * L - min cA 1 * P ∧ C * L - P ≤ max CA C * L - min cA 1 * P := by
  have a1 : CA ≤ max CA C := le_max_left _ _
  have a2 : min cA 1 ≤ cA := min_le_left _ _
  have a3 : C ≤ max CA C := le_max_right _ _
  have a4 : min cA 1 ≤ 1 := min_le_right _ _
  constructor
  · nlinarith [mul_nonneg hL (sub_nonneg.2 a1), mul_nonneg hP (sub_nonneg.2 a2)]
  · nlinarith [mul_nonneg hL (sub_nonneg.2 a3), mul_nonneg hP (sub_nonneg.2 a4)]

/-! ### Theorem 2 from the moment bound -/

/-- **Theorem 2 from Steps 3--4, for a general rate function `ω` (conditional helper).** The
hypothesis `hω` collects the elementary properties of `ω` used in Steps 5--6
(`Theorem2RateHyp`), `h1` is the statement of Theorem 1 with `ω` in place of `ω_λ`
(`Theorem1ShapeRate`) and `hm` is the exponential moment bound of Steps 3--4 with `ω`
(`MomentBoundRate`). The conclusion is the statement of Theorem 2 (`prop:linear`) with `ω` in
place of `ω_λ`; for `ω = errorRate β hβ` it is the statement of the frozen `theorem_2`. This is
not a frozen statement: it only records the assembly of Steps 5--6 of the proof of Theorem 2
(source l. 2060–2121). -/
theorem theorem_2_of_moment_rate (β : ℝ) (hβ : 2 ≤ β) (ω : ℝ → ℝ) (hω : Theorem2RateHyp β hβ ω)
    (h1 : Theorem1ShapeRate β hβ ω) (hm : MomentBoundRate β hβ ω) :
    ∃ lamβ Mβ Cβ : ℝ, 0 < lamβ ∧ lamβ < Real.exp (-1) ∧ 0 < Mβ ∧ 0 < Cβ ∧
      ∀ M : ℝ, Mβ < M → ∃ c : ℝ, 0 < c ∧
        ∀ ξ₀ : ℂ → ℝ, HasCompactSupport ξ₀ → ∀ L : ℝ≥0, LipschitzWith L ξ₀ →
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
          gibbsMeasure N β lam
              {Z | M * N * Real.sqrt (ω lam) * (L : ℝ) ^ 2
                < fluct (fun x => ξ₀ ((Real.sqrt N)⁻¹ • x)) Z ^ 2}
            ≤ ENNReal.ofReal (Cβ * Real.exp (-c * Real.sqrt N * ω lam)) := by
  classical
  obtain ⟨lamT, hlamT0, hlamTe, ⟨Cb, cb, hCb, hcb, hmain⟩, hb2, hb3⟩ := h1
  have hb1 : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamT → ∀ p₀ : ℕ, p₀ ≤ N →
        gibbsMeasure N β lam {Z | (isolatedDipoles Z).card = p₀}
          ≤ ENNReal.ofReal (Real.exp (-c * N * (1 - (p₀ : ℝ) / N) ^ 2
            + C * N * ω lam + C * Real.log (N + 1))) :=
    ⟨Cb, cb, hCb, hcb, fun N hN lam h0 h1 p hp => (hmain N hN lam h0 h1).2.2.2.2 p hp⟩
  obtain ⟨lamA, MA, CA, cA, hlamA0, hlamAe, hMA, hCA, hcA, hA⟩ :=
    exists_gibbsMeasure_eventARate_compl_le β hβ ω hω hlamT0 hb1 hb2 hb3
  obtain ⟨α, c, C, lam₁, hc, hC, hlam₁, hα, hmeas, hmom'⟩ := hm
  obtain ⟨CF, hCF, hfl⟩ := exists_fluct_sq_le_of_good_rate
  obtain ⟨lamR, hlamR, hlamRe, hreg⟩ := exists_R0Rate_regime hβ hω.pos hω.le_rpow hω.rpow_le
    hω.two_mul_le_rpow_quarter hω.log_div_le
  obtain ⟨lamG, hlamG, hlamGe, hγreg⟩ := exists_gammaChoice_regime_rate β hβ hω.gammaChoice_le
  -- the constants
  set Q : ℝ := 2 / c * (3 + 1) + 8 * 3 + 40 with hQ
  have hQ0 : 0 < Q := by positivity
  set Ktot : ℝ := CF * Q with hKtot
  have hKtot0 : 0 < Ktot := by positivity
  set M₁ : ℝ := max (max 1 MA) C with hM₁
  have hM₁1 : 1 ≤ M₁ := (le_max_left _ _).trans (le_max_left _ _)
  set Cg : ℝ := max CA C with hCg
  set cg : ℝ := min cA 1 with hcg
  obtain ⟨C', c', hC', hc', habs⟩ := exists_min_one_le_exp (K := 3) (C := Cg) (c := cg)
    (by norm_num) (le_max_of_le_right hC.le) (lt_min hcA one_pos)
  refine ⟨min (min (min lamT lamA) (min lam₁ lamG)) (min lamR (Real.exp (-1) / 2)),
    Ktot * M₁, C', ?_, ?_, mul_pos hKtot0 (by linarith), hC', ?_⟩
  · exact lt_min (lt_min (lt_min hlamT0 hlamA0) (lt_min hlam₁ hlamG))
      (lt_min hlamR (by positivity))
  · exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _))
      (by linarith [Real.exp_pos (-1)])
  intro M hM
  have hM₀ : M₁ ≤ M / Ktot := by
    rw [le_div_iff₀ hKtot0]
    linarith
  set M₀ : ℝ := M / Ktot with hM₀def
  have hKM : Ktot * M₀ = M := by
    rw [hM₀def]
    field_simp
  have hM₀0 : 0 < M₀ := lt_of_lt_of_le (by linarith) hM₀
  refine ⟨c' * M₀, mul_pos hc' hM₀0, ?_⟩
  intro ξ₀ hξ₀ L hL N hN lam h0 hlt
  have hl1 : lam < lamT :=
    lt_of_lt_of_le hlt (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hl2 : lam < lamA :=
    lt_of_lt_of_le hlt (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hl3 : lam < lam₁ :=
    lt_of_lt_of_le hlt (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hl4 : lam < lamG :=
    lt_of_lt_of_le hlt (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hl5 : lam < lamR :=
    lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
  have hle : lam < Real.exp (-1) :=
    lt_of_lt_of_le hl4 hlamGe
  have hω0 := hω.pos lam h0 hle
  have hω1 := hω.le_one lam h0 hle
  have hprob : IsProbabilityMeasure (gibbsMeasure N β lam) :=
    isProbabilityMeasure_gibbsMeasure (hmain N hN lam h0 hl1).2.1.ne (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hγ1, hγ2, hγ3⟩ := hγreg lam h0 hl4
  obtain ⟨hR2, hR4, -, -⟩ := hreg lam h0 hl5
  set γ : ℝ := gammaChoice β lam with hγ
  have hlγ : lam ≤ γ := by linarith
  -- the event `B_M`
  have hφ0 : 0 ≤ isolatedPhi β hβ lam γ := isolatedPhi_nonneg hβ h0 hlγ
  have hCM : C ≤ M₀ := (le_max_right (max 1 MA) C).trans hM₀
  have hMAM : MA ≤ M₀ := ((le_max_right 1 MA).trans (le_max_left (max 1 MA) C)).trans hM₀
  have hBprob : gibbsMeasure N β lam
      {Z | 2 / c * M₀ * N * (isolatedPhi β hβ lam γ + ω lam) <
        ∫ x, ‖electricField charge Z (α N lam γ Z) x‖ ^ 2}
      ≤ ENNReal.ofReal (Real.exp (C * Real.log (N + 1) - M₀ * N * ω lam)) :=
    gibbsMeasure_electric_compl_le (hmeas N hN lam γ h0 hl3 hγ1 hγ2) hc hC.le hCM hφ0 hω0.le
      (hmom' N hN lam γ h0 hl3 hγ1 hγ2)
  have hAprob := hA M₀ hMAM N hN lam h0 hl2
  rw [show cA * M₀ * N * ω lam = cA * (M₀ * N * ω lam) by ring]
    at hAprob
  have hαN := hα N hN lam γ h0 hl3 hγ1 hγ2
  clear hmain hb1 hb2 hb3 hA hmom' hmeas hα hγreg hreg
  -- on `Λ^{2N} ∩ A_M ∩ B_M` the fluctuation is controlled (eq:f)
  have hgood : ∀ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) → Z ∈ eventARate β ω N lam M₀ →
      (∫ x, ‖electricField charge Z (α N lam γ Z) x‖ ^ 2) ≤
        2 / c * M₀ * N * (isolatedPhi β hβ lam γ + ω lam) →
      fluct (fun x => ξ₀ ((Real.sqrt N)⁻¹ • x)) Z ^ 2 ≤
        M * N * Real.sqrt (ω lam) * (L : ℝ) ^ 2 := by
    intro Z hZbox hZA hZB
    have hbound := hfl β hβ ω hc (K := 3) (by norm_num) hN h0 hle hω0 hω1 (le_trans hM₁1 hM₀) hlγ
      hR2 hR4
      hγ3 hξ₀ hL hZbox hZA (fun i => (hαN Z i).1) (fun i => (hαN Z i).2) hZB
    have heq : CF * (2 / c * (3 + 1) + 8 * 3 + 40) * M₀ * (L : ℝ) ^ 2 * N *
        Real.sqrt (ω lam) =
        M * N * Real.sqrt (ω lam) * (L : ℝ) ^ 2 := by
      rw [← hKM, hKtot, hQ]
      ring
    exact hbound.trans_eq heq
  have hL0 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hP0 : 0 ≤ M₀ * N * ω lam := by positivity
  obtain ⟨hex1, hex2⟩ := exponent_le_common (CA := CA) (C := C) (cA := cA) hL0 hP0
  have hmeasure := measure_le_min_one_of_subset (gibbsMeasure N β lam)
    (bad_subset_union hgood) (gibbsMeasure_compl_pi_box N β lam) hAprob hBprob hex1 hex2
  have hx0 : 0 ≤ M₀ * ω lam := by positivity
  have hcg : cg * N * (M₀ * ω lam) = cg * (M₀ * N * ω lam) := by ring
  have habs' := habs N (by omega) (M₀ * ω lam) hx0
  rw [hcg] at habs'
  calc gibbsMeasure N β lam
        {Z | M * N * Real.sqrt (ω lam) * (L : ℝ) ^ 2 <
          fluct (fun x => ξ₀ ((Real.sqrt N)⁻¹ • x)) Z ^ 2}
      ≤ ENNReal.ofReal (min 1 (3 * Real.exp (Cg * Real.log (N + 1) -
          cg * (M₀ * N * ω lam)))) := hmeasure
    _ ≤ ENNReal.ofReal (C' * Real.exp (-(c' * Real.sqrt N * (M₀ * ω lam)))) :=
        ENNReal.ofReal_le_ofReal habs'
    _ = ENNReal.ofReal (C' * Real.exp (-(c' * M₀) * Real.sqrt N * ω lam)) := by
        congr 3
        ring

end TwoComponentCoulomb

end
