/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.Energy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TwoComponentCoulomb.Frozen.M0
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.Frozen.NumComponents
public import TwoComponentCoulomb.NearestNeighbor.TwiceIsolated
public import TwoComponentCoulomb.UpperBound.CriticalCells
public import TwoComponentCoulomb.UpperBound.CriticalFixedGraph
public import TwoComponentCoulomb.UpperBound.CriticalEnergy
public import TwoComponentCoulomb.UpperBound.CriticalGraphSum
public import TwoComponentCoulomb.UpperBound.CriticalRadial
public import TwoComponentCoulomb.UpperBound.MarkedGraphCover

/-!
# Proposition 3.10 at `β = 2`: the bound (eq:critical upper)

Source: `source/dipole-formation.tex`, l. 1575–1582 (statement) and
l. 1586–1652 (proof).

Write `ℓ = |log λ|`. The cell integral and the sum over the nearest-neighbour graphs are proved for a
general integrand in `UpperBound/CriticalCells.lean` and `UpperBound/CriticalGraphSum.lean`; this
file supplies the integrand `e^{-2 F_λ + N - |I^dip|/2 + D_R}`. By the energy bound
(`TwoComponentCoulomb.exists_neg_two_mul_energy_le`, source l. 1605–1610) it is dominated on a
cell by the pair weights `critNeutralWeight` and `critSameSignWeight` , whose radial integrals are at most `neutralMass λ R (e - 1) C`
(`T_R = J_λ(1/ℓ) + C + (e-1)(J_λ(1/ℓ;R) + C)`) and the constant `256 π e^{c₃}` (source l. 1625).

## Main results

* `TwoComponentCoulomb.exists_lintegral_cell_critical_le` (source l. 1618–1620): the integral of
  `e^{-2F_λ + N - |I^dip|/2 + D_R}` over a cell is at most `exp (criticalCellExponent …)`, with the
  neutral mass `neutralMass λ R (e - 1) C` and the same-sign mass `256 π e^{c₃}`.
* `TwoComponentCoulomb.critical_upper` (eq:critical upper; source l. 1575–1582, proof
  l. 1595–1650): there is `C > 0` such that for `N ≥ 2`, `0 < λ < e⁻²` and `2λ ≤ R ≤ 1`,
  `∫_{Λ^{2N}} e^{-2F_λ + N - |I^dip|/2 + D_R} ≤ exp (2N log N + N (log (2πℓ) - 1)
    + C N (ℓ^{-1/5} + log (1/R)/ℓ) + C log (N+1))`; here `ℓ^{-1/5}` is `errorRate 2 _ λ`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### The pair weights -/

/-- The radial weight of the isolated pair of the non-retained endpoint `s`: neutral or
same-sign. -/
noncomputable def critPairWeight (lam ℓ R c₂ c₃ : ℝ) (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N)
    (s : {s // s ∈ isoSecondVerts f}) : ℂ × ℝ → ℝ≥0∞ :=
  if charge (s : Fin N ⊕ Fin N) * charge (f s) = -1 then critNeutralWeight lam ℓ R c₂
  else critSameSignWeight lam (Real.exp c₃)

theorem measurable_critPairWeight (lam ℓ R c₂ c₃ : ℝ) (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N)
    (s : {s // s ∈ isoSecondVerts f}) : Measurable (critPairWeight lam ℓ R c₂ c₃ f s) := by
  unfold critPairWeight
  split_ifs
  · exact measurable_critNeutralWeight lam ℓ R c₂
  · exact measurable_critSameSignWeight lam (Real.exp c₃)

/-- The pair weight dominates `e^{E_s - |u_s|²/ℓ}` (source l. 1622–1639): `|u_s| ≤ 4ρ_s`, and
`e^{2 log (|u| ∨ λ) - 4 log ρ + c₃} = e^{c₃} (|u| ∨ λ)² / ρ⁴`. -/
theorem ofReal_exp_critPairExponent_le (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (R c₂ c₃ : ℝ)
    {Z : Fin N ⊕ Fin N → ℂ} (s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)}) :
    ENNReal.ofReal (Real.exp (critPairExponent hN lam R c₂ c₃ Z s -
        ‖Z s - Z (nearestNeighbor Z s)‖ ^ 2 / |Real.log lam|)) ≤
      critPairWeight lam |Real.log lam| R c₂ c₃ (nearestNeighbor Z) s
        (Z s - Z (nearestNeighbor Z s),
          isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s)) := by
  have hu4 := norm_sub_le_four_mul_isoRadius rfl hN lam s
  have hρ0 : 0 < isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s) :=
    hlam.trans_le (lam_le_isoRadius hN lam _ _)
  unfold critPairWeight critPairExponent
  by_cases hn : charge (s : Fin N ⊕ Fin N) * charge (nearestNeighbor Z s) = -1
  · rw [ite_eq_left hn, ite_eq_left hn]
    unfold critNeutralWeight
    dsimp only
    rw [ite_eq_left hu4]
    refine le_of_eq (congrArg ENNReal.ofReal (congrArg Real.exp ?_))
    ring
  · rw [ite_eq_right hn, ite_eq_right hn]
    unfold critSameSignWeight
    dsimp only
    rw [ite_eq_left hu4]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← exp_two_mul_log_sub_four_mul_log (lt_max_of_lt_right hlam) hρ0]
    refine Real.exp_le_exp.2 ?_
    have : 0 ≤ ‖Z s - Z (nearestNeighbor Z s)‖ ^ 2 / |Real.log lam| := by positivity
    linarith only [this]

/-! ### The cell bound -/

/-- **The cell bound of the critical case** (source l. 1605–1620). There are constants such that
for `N ≥ 2`, `0 < λ ≤ e⁻²`, `2λ ≤ R ≤ 1` and every nearest-neighbour graph `f = φ₁(Z₀)`, the
integral of `e^{-2F_λ + N - |I^dip|/2 + D_R}` over the cell `Λ^{2N} ∩ {φ₁ = f}` is at most
`exp (criticalCellExponent …)` evaluated at the number `K` of components, `m` of isolated pairs and
`p₀` of isolated neutral pairs of `f`, with the neutral mass `neutralMass λ R (e - 1) C` and the
same-sign mass `256 π e^{c₃}`. -/
theorem exists_lintegral_cell_critical_le :
    ∃ c₁ c₃ Cn CJ : ℝ, 0 ≤ c₁ ∧ 0 ≤ Cn ∧ 0 ≤ CJ ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-2) → ∀ R : ℝ, 2 * lam ≤ R →
        R ≤ 1 → ∀ (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (Z₀ : Fin N ⊕ Fin N → ℂ),
          nearestNeighbor Z₀ = f →
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f},
              ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card +
                (longIsolatedDipoles Z R).card)) ≤
            ENNReal.ofReal (Real.exp (criticalCellExponent c₁ CJ lam
              (neutralMass lam R (Real.exp 1 - 1) Cn) (256 * Real.pi * Real.exp c₃) N
              (numComponents Z₀) (numIsolatedPairs Z₀) (isolatedDipoles Z₀).card)) := by
  obtain ⟨c₁, c₂, c₃, hc₁, hc₂, hE⟩ := exists_neg_two_mul_energy_le
  obtain ⟨Cn, hCn, hNW⟩ := exists_lintegral_critNeutralWeight_le hc₂
  obtain ⟨CJ, hCJ, hcell⟩ := exists_lintegral_cell_le_criticalCellExponent
  refine ⟨c₁, c₃, Cn, CJ, hc₁, hCn, hCJ, fun N hN lam hlam hlam2 R hR hR1 f Z₀ hf₀ => ?_⟩
  have hle1 : lam ≤ Real.exp (-1) := hlam2.trans (Real.exp_le_exp.2 (by norm_num))
  have hℓ := one_le_abs_log hlam hle1
  have he : 0 ≤ Real.exp 1 - 1 := by have := Real.one_le_exp zero_le_one; linarith only [this]
  refine hcell N hN lam hlam hlam2 c₁ _ _
    (neutralMass_pos hlam hle1 he hCn) (by positivity) f Z₀ hf₀ _
    (critPairWeight lam |Real.log lam| R c₂ c₃ f) (measurable_critPairWeight _ _ _ _ _ f) ?_ ?_
  · intro s ρ hρ
    unfold critPairWeight
    split_ifs
    · exact hNW lam R ρ hlam hle1 hR hR1 hρ
    · exact lintegral_critSameSignWeight_le hlam hρ (Real.exp_pos _).le
  · intro Z hbox hgen hZf
    subst hZf
    exact ofReal_exp_le_cell_of_exponent hN hlam hle1 (nearestNeighbor Z) hbox rfl _ _
      (hE N hN lam hlam R Z hbox hgen) (fun s => ofReal_exp_critPairExponent_le hN hlam R c₂ c₃ s)

/-- **The full-energy fixed-graph bound** (eq:critical-fixed-graph). Here `T_R`
is `neutralMass`, with the exact common Gaussian mass and its tail. -/
theorem critical_fixed_graph :
    ∃ C Cn : ℝ, 0 < C ∧ 0 ≤ Cn ∧ ∀ (N : ℕ), 2 ≤ N → ∀ lam : ℝ,
      0 < lam → lam ≤ Real.exp (-2) → ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 →
      ∀ (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (Z₀ : Fin N ⊕ Fin N → ℂ),
      nearestNeighbor Z₀ = f →
      let K := numComponents Z₀
      let m := numIsolatedPairs Z₀
      let p₀ := (isolatedDipoles Z₀).card
      ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f},
          ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card +
            (longIsolatedDipoles Z R).card)) ≤
        ENNReal.ofReal (Real.exp (C * ((m - p₀ : ℕ) + (N - K : ℕ)) +
            ((N - p₀ : ℕ) : ℝ) + C * N / |Real.log lam|) * (N : ℝ) ^ K *
          neutralMass lam R (Real.exp 1 - 1) Cn ^ p₀ * criticalCycleMass lam ^ (K - m) *
          (C * N / (N - K : ℕ)) ^ (N - K)) := by
  obtain ⟨c₁, c₃, Cn, CJ, hc₁, hCn, hCJ, hcell⟩ := exists_lintegral_cell_critical_le
  obtain ⟨C₀, hC₀, henv⟩ := exists_critical_fixedGraphEnvelope (CJ := CJ) hc₁
  let Ms := 256 * Real.pi * Real.exp c₃
  let C := C₀ + |Real.log Ms| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCC : C₀ ≤ C := by dsimp [C]; linarith only [abs_nonneg (Real.log Ms)]
  have hMs : Real.log Ms ≤ C := (le_abs_self _).trans (by dsimp [C]; linarith only [hC₀])
  refine ⟨C, Cn, hC, hCn, fun N hN lam hlam hlam2 R hR hR1 f Z₀ hf => ?_⟩
  dsimp only
  have hle := hlam2.trans (Real.exp_le_exp.2 (by norm_num : (-2 : ℝ) ≤ -1))
  have hn : 0 < N := by omega
  have hcounts := critGraphs_constraints
    (show (critGraphs N (numComponents Z₀) (numIsolatedPairs Z₀) (isolatedDipoles Z₀).card).Nonempty
      from ⟨f, mem_critGraphs.2 ⟨Z₀, hf, rfl, rfl, rfl⟩⟩)
  obtain ⟨hp₀, hmK, hKN, hr2⟩ := hcounts
  have hneu := neutralMass_pos (R := R) hlam hle
    (show 0 ≤ Real.exp 1 - 1 by linarith only [Real.one_le_exp zero_le_one]) hCn
  refine (hcell N hN lam hlam hlam2 R hR hR1 f Z₀ hf).trans
    ((henv N _ _ _ hn hp₀ hmK hKN hr2 lam _ Ms hlam hle hneu (by dsimp [Ms]; positivity)).trans ?_)
  have hp : Ms ^ ((numIsolatedPairs Z₀) - (isolatedDipoles Z₀).card) =
      Real.exp (((numIsolatedPairs Z₀) - (isolatedDipoles Z₀).card : ℕ) * Real.log Ms) := by
    rw [Real.exp_nat_mul, Real.exp_log (show 0 < Ms by dsimp [Ms]; positivity)]
  rw [hp]
  apply ENNReal.ofReal_le_ofReal
  have hj := (criticalCycleMass_pos hlam hle).le
  calc _ = Real.exp (C₀ * (N - numComponents Z₀ : ℕ) + C₀ * N / |Real.log lam| +
          ((numIsolatedPairs Z₀ - (isolatedDipoles Z₀).card : ℕ) : ℝ) * Real.log Ms) *
        (N : ℝ) ^ numComponents Z₀ * neutralMass lam R (Real.exp 1 - 1) Cn ^ (isolatedDipoles Z₀).card *
        criticalCycleMass lam ^ (numComponents Z₀ - numIsolatedPairs Z₀) *
        (C₀ * N / (N - numComponents Z₀ : ℕ)) ^ (N - numComponents Z₀) := by
        simp only [Real.exp_add]
        ring
    _ ≤ _ := by
        have hExp : C₀ * (N - numComponents Z₀ : ℕ) + C₀ * N / |Real.log lam| +
              ((numIsolatedPairs Z₀ - (isolatedDipoles Z₀).card : ℕ) : ℝ) * Real.log Ms ≤
            C * ((numIsolatedPairs Z₀ - (isolatedDipoles Z₀).card : ℕ) +
              (N - numComponents Z₀ : ℕ)) + ((N - (isolatedDipoles Z₀).card : ℕ) : ℝ) +
                C * N / |Real.log lam| := by
          have h1 := mul_le_mul_of_nonneg_right hCC
            (Nat.cast_nonneg (N - numComponents Z₀) : (0 : ℝ) ≤ (N - numComponents Z₀ : ℕ))
          have h2 := mul_le_mul_of_nonneg_right hCC
            (show 0 ≤ (N : ℝ) / |Real.log lam| by positivity)
          have h3 := mul_le_mul_of_nonneg_left hMs
            (Nat.cast_nonneg (numIsolatedPairs Z₀ - (isolatedDipoles Z₀).card) :
              (0 : ℝ) ≤ (numIsolatedPairs Z₀ - (isolatedDipoles Z₀).card : ℕ))
          have h4 := Nat.cast_nonneg (N - (isolatedDipoles Z₀).card) (α := ℝ)
          linear_combination h1 + h2 + h3 + h4
        have hTree : (C₀ * N / (N - numComponents Z₀ : ℕ)) ^ (N - numComponents Z₀) ≤
            (C * N / (N - numComponents Z₀ : ℕ)) ^ (N - numComponents Z₀) := by
          gcongr
        have hPrefix := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.2 hExp) (show 0 ≤ (N : ℝ) ^ numComponents Z₀ by positivity))
            (show 0 ≤ neutralMass lam R (Real.exp 1 - 1) Cn ^ (isolatedDipoles Z₀).card by positivity))
          (show 0 ≤ criticalCycleMass lam ^ (numComponents Z₀ - numIsolatedPairs Z₀) by positivity)
        exact mul_le_mul hPrefix hTree (by positivity) (by positivity)

/-! ### The bound (eq:critical upper) -/

namespace CriticalUpper

/-- `(1 + log ℓ) / ℓ ≤ 3 ℓ^{-1/5}` for `ℓ ≥ 1` (the final absorption of source ). -/
theorem one_add_log_div_le_fifth {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    (1 + Real.log ℓ) / ℓ ≤ 3 * ℓ ^ (-(1 / 5 : ℝ)) := by
  have hpos : 0 < ℓ := by linarith only [hℓ]
  have h1 : Real.log ℓ ≤ ℓ ^ (4 / 5 : ℝ) / (4 / 5) :=
    Real.log_le_rpow_div hpos.le (by norm_num)
  have h2 : 1 ≤ ℓ ^ (4 / 5 : ℝ) := Real.one_le_rpow hℓ (by norm_num)
  have h3 : ℓ ^ (-(1 / 5 : ℝ)) = ℓ ^ (4 / 5 : ℝ) / ℓ := by
    rw [show -(1 / 5 : ℝ) = 4 / 5 + (-1) by norm_num, Real.rpow_add hpos, Real.rpow_neg_one]
    exact (div_eq_mul_inv _ _).symm
  rw [h3, mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ hpos.le
  nlinarith only [h1, h2]

end CriticalUpper

open CriticalUpper in
/-- **Proposition 3.10, critical case `β = 2`** (`eq:critical upper`, source, proof
l. 1595–1650). There is `C > 0` such that for all `N ≥ 2`, `0 < λ < e⁻²` and
`2λ ≤ R ≤ 1`, with `ℓ = |log λ|`,
`∫_{Λ^{2N}} e^{-2F_λ + N - |I^dip|/2 + D_R} ≤
  exp (2N log N + N (log (2πℓ) - 1) + C N (ℓ^{-1/5} + log (1/R)/ℓ) + C log (N+1))`,
where `|I^dip|/2` is the number of isolated dipoles and `D_R` the number of isolated dipoles of
length `> R`. The rate is `ℓ^{-1/5} = ω_λ`, the value of `errorRate` at `β = 2`: the graph sum
(`exists_lintegral_pi_box_le_of_cell_le`) gives `ℓ^{-1/5} + (1 + log ℓ + log (1/R))/ℓ`, and
`(1 + log ℓ)/ℓ ≤ 3 ℓ^{-1/5}` absorbs the logarithmic term . -/
theorem critical_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < Real.exp (-2) →
      ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 →
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
            ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
              + (longIsolatedDipoles Z R).card))
          ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
              + N * (Real.log (2 * Real.pi * |Real.log lam|) - 1)
              + C * N * (|Real.log lam| ^ (-(1 / 5 : ℝ))
                + Real.log (1 / R) / |Real.log lam|)
              + C * Real.log (N + 1))) := by
  obtain ⟨c₁, c₃, Cn, CJ, hc₁, hCn, hCJ, hcell⟩ := exists_lintegral_cell_critical_le
  have he : 0 ≤ Real.exp 1 - 1 := by have := Real.one_le_exp zero_le_one; linarith only [this]
  obtain ⟨CB, hCB, hB⟩ := exists_criticalCycleMass_le
  obtain ⟨C, hC, hsum⟩ := exists_lintegral_pi_box_le_of_cell_le (Cm := 1 + (Real.exp 1 - 1) + (Cn + CB))
    (C₀ := 256 * Real.pi * Real.exp c₃) hc₁ hCJ (by positivity) (by positivity)
  refine ⟨4 * C, by positivity, fun N hN lam hlam hlam1 R hR hR1 => ?_⟩
  have hℓ1 := one_le_abs_log hlam (hlam1.le.trans (Real.exp_le_exp.2 (by norm_num)))
  have hR0 : 0 < R := by linarith only [hR, hlam]
  have hlogR : 0 ≤ Real.log (1 / R) :=
    Real.log_nonneg (by rw [le_div_iff₀ hR0]; linarith only [hR1])
  have hlogℓ : 0 ≤ Real.log |Real.log lam| := Real.log_nonneg hℓ1
  -- the same-sign mass is a constant: `Mₛ ≤ Mₛ E` since `E ≥ 1`
  refine (hsum N hN lam _ _ (1 + Real.log |Real.log lam| + Real.log (1 / R)) hlam hlam1.le
    (by linarith only [hlogR]) (log_neutralMass_le hlam (hlam1.le.trans (Real.exp_le_exp.2 (by norm_num))) hCB
      (hB lam hlam (hlam1.le.trans (Real.exp_le_exp.2 (by norm_num)))) hR he hCn hℓ1 hR0 hR1) (by positivity)
    (le_mul_of_one_le_right (by positivity) (by linarith only [hlogℓ, hlogR])) _
    fun f Z₀ hf₀ => hcell N hN lam hlam hlam1.le R hR hR1 f Z₀ hf₀).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  generalize |Real.log lam| = ℓ at hℓ1 hlogℓ ⊢
  have hℓ0 : 0 < ℓ := by linarith only [hℓ1]
  have hX := one_add_log_div_le_fifth hℓ1
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlogN : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by linarith only [hN0])
  have hω0 : 0 ≤ ℓ ^ (-(1 / 5 : ℝ)) := by positivity
  have hRℓ : 0 ≤ Real.log (1 / R) / ℓ := div_nonneg hlogR hℓ0.le
  have e : (1 + Real.log ℓ + Real.log (1 / R)) / ℓ
      = (1 + Real.log ℓ) / ℓ + Real.log (1 / R) / ℓ := by ring
  have key : ℓ ^ (-(1 / 5 : ℝ)) + (1 + Real.log ℓ + Real.log (1 / R)) / ℓ
      ≤ 4 * (ℓ ^ (-(1 / 5 : ℝ)) + Real.log (1 / R) / ℓ) := by
    rw [e]
    linarith only [hX, hω0, hRℓ]
  have h1 := mul_le_mul_of_nonneg_left key (show 0 ≤ C * N by positivity)
  have h2 := mul_nonneg hC.le hlogN
  nlinarith only [h1, h2]

end TwoComponentCoulomb

end
