/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.Energy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TwoComponentCoulomb.Frozen.M0
public import TwoComponentCoulomb.Frozen.ErrorRate
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.Frozen.PartitionFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TwoComponentCoulomb.Gibbs.Basic
import TwoComponentCoulomb.Integrals.LogFacts
import TwoComponentCoulomb.NearestNeighbor.Isolated
import TwoComponentCoulomb.UpperBound.CriticalUpper

/-!
# Consequences of Proposition 3.10 at `β = 2`

Source: `source/dipole-formation.tex`, l. 1575–1584.
Taking `R = 1` in (eq:critical upper) bounds the partition function and the integral
on a prescribed dipole-count event. The frozen `proposition_3_9_and_3_10` bundles these
consequences with Proposition 3.9 and the critical bound itself.
-/

@[expose] public section

namespace TwoComponentCoulomb

open MeasureTheory
open scoped ENNReal

namespace Prop310Critical

/-- `errorRate 2 _ λ = |log λ|^{-1/5}`. -/
theorem errorRate_two (hβ : (2 : ℝ) ≤ 2) (lam : ℝ) :
    errorRate 2 hβ lam = |Real.log lam| ^ (-(1 / 5 : ℝ)) := by
  simp [errorRate]

/-- (eq:critical upper) with `R = 1` for the rate `ω_λ = errorRate 2 _ λ = ℓ^{-1/5}` and
`log (2πℓ)` split as `log (2π) + log ℓ`, for all `0 < λ < e⁻²`. -/
theorem exists_critical_bound_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < Real.exp (-2) →
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
            ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
              + (longIsolatedDipoles Z 1).card))
          ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
              + N * (Real.log (2 * Real.pi) + Real.log |Real.log lam| - 1)
              + C * N * errorRate 2 le_rfl lam + C * Real.log (N + 1))) := by
  obtain ⟨C, hC, h⟩ := critical_upper
  refine ⟨C, hC, fun N hN lam hlam hlt => ?_⟩
  have hR : 2 * lam ≤ 1 := by
    have : Real.exp (-2) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by norm_num)
    linarith only [exp_neg_one_le_half, hlt, this]
  have hℓ := one_le_abs_log hlam (hlt.le.trans (Real.exp_le_exp.2 (by norm_num)))
  refine (h N hN lam hlam hlt 1 hR le_rfl).trans (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.2 (le_of_eq ?_)))
  rw [errorRate_two, div_one, Real.log_one, zero_div, add_zero,
    Real.log_mul (by positivity) (by linarith only [hℓ])]

/-- **The deduction of (ubz) and (eq:neutral bound) at `β = 2` from the `R = 1` bound**
, independent of the rate. An internal lemma: its hypothesis `hG` is the bound
(eq:critical upper) at `R = 1`, proved in `critical_upper`, with the value `ωl = ω_λ` of the rate
left abstract; it is instantiated in `proposition_3_10_main_two`. The conclusion is the first
block of the joint frozen statement of Propositions 3.9 and 3.10 with `c = 1`, `if`s kept, and
`C * errorRate β hβ lam` replaced by `C * ωl`. -/
theorem main_two_of_critical_bound_one {β : ℝ} (hβ : 2 ≤ β) (hβ2 : β = 2) {N : ℕ} (hN : 2 ≤ N)
    {lam C ωl : ℝ}
    (hG : ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
            ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
              + (longIsolatedDipoles Z 1).card))
          ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
              + N * (Real.log (2 * Real.pi) + Real.log |Real.log lam| - 1)
              + C * N * ωl + C * Real.log (N + 1)))) :
    partitionFunction N β lam
        ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
          + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
            + (if β = 2 then Real.log |Real.log lam| else 0)
            + Real.log (dipoleConstant β hβ) - 1 + C * ωl)
          + C * Real.log (N + 1))) ∧
      ∀ p₀ : ℕ, p₀ ≤ N →
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
            {Z | (isolatedDipoles Z).card = p₀},
            ENNReal.ofReal (Real.exp (-β * energy lam Z))
          ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
            + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
              + (if β = 2 then Real.log |Real.log lam| else 0))
            + N * (Real.log (dipoleConstant β hβ) - 1)
            - 1 * N * (((p₀ : ℝ) - N) / N) ^ 2
            + C * N * ωl + C * Real.log (N + 1))) := by
  subst hβ2
  have hdc : Real.log (dipoleConstant 2 hβ) = Real.log (2 * Real.pi) := by
    simp [dipoleConstant]
  have e1 : (if (2 : ℝ) < 2 then (2 - 2) * Real.log lam else 0) = 0 := by simp
  have e2 : (if (2 : ℝ) = 2 then Real.log |Real.log lam| else 0) = Real.log |Real.log lam| := by
    simp
  refine ⟨?_, fun p₀ hp₀ => ?_⟩
  · unfold partitionFunction
    refine (lintegral_mono fun Z => ?_).trans (hG.trans (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 ?_)))
    · refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have h1 : ((isolatedDipoles Z).card : ℝ) ≤ N := by exact_mod_cast isolatedDipoles_card_le Z
      have h2 : (0 : ℝ) ≤ (longIsolatedDipoles Z 1).card := Nat.cast_nonneg _
      linarith
    · rw [e1, e2, hdc]
      linarith
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hmeas : MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
        {Z | (isolatedDipoles Z).card = p₀}) :=
      (MeasurableSet.univ_pi fun _ => measurableSet_box N).inter
        (measurableSet_isolatedDipoles_card_eq p₀)
    calc ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
            {Z | (isolatedDipoles Z).card = p₀},
            ENNReal.ofReal (Real.exp (-2 * energy lam Z))
        ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
            {Z | (isolatedDipoles Z).card = p₀},
            ENNReal.ofReal (Real.exp (-((N : ℝ) - p₀))) *
              ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
                + (longIsolatedDipoles Z 1).card)) := by
          refine setLIntegral_mono' hmeas fun Z hZ => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have hc : ((isolatedDipoles Z).card : ℝ) = p₀ := by exact_mod_cast hZ.2
          have h2 : (0 : ℝ) ≤ (longIsolatedDipoles Z 1).card := Nat.cast_nonneg _
          linarith
      _ = ENNReal.ofReal (Real.exp (-((N : ℝ) - p₀))) *
            ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
              {Z | (isolatedDipoles Z).card = p₀},
              ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
                + (longIsolatedDipoles Z 1).card)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) - p₀))) *
            ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
              ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
                + (longIsolatedDipoles Z 1).card)) := by
          gcongr
          exact Set.inter_subset_left
      _ ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) - p₀))) *
            ENNReal.ofReal (Real.exp (2 * N * Real.log N
              + N * (Real.log (2 * Real.pi) + Real.log |Real.log lam| - 1)
              + C * N * ωl + C * Real.log (N + 1))) := by
          gcongr
      _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have e3 : (N : ℝ) * (((p₀ : ℝ) - N) / N) ^ 2 = ((N : ℝ) - p₀) ^ 2 / N := by
            field_simp
            ring
          have hp : (p₀ : ℝ) ≤ N := by exact_mod_cast hp₀
          have hq : ((N : ℝ) - p₀) ^ 2 / N ≤ (N : ℝ) - p₀ := by
            rw [div_le_iff₀ hN0]
            nlinarith [mul_nonneg (sub_nonneg.2 hp) (Nat.cast_nonneg (α := ℝ) p₀)]
          rw [e1, e2, hdc]
          have e4 : (1 : ℝ) * N * (((p₀ : ℝ) - N) / N) ^ 2 = (N : ℝ) * (((p₀ : ℝ) - N) / N) ^ 2 := by
            ring
          rw [e4, e3]
          linarith

end Prop310Critical

open Prop310Critical in
open Prop310Critical in
/-- **Consequences of Proposition 3.10: the partition-function and dipole-count bounds.** The first
block of the frozen `proposition_3_9_and_3_10` for `β = 2` (with the `if`s kept) for the rate
`ω_λ = errorRate β hβ λ = ℓ^{-1/5}`, with the threshold `λ₀ = e⁻²`: there are `C, c > 0` such
that for `N ≥ 2`, `0 < λ < e⁻²` the partition function is at most
`exp (2N log N + N (log |log λ| + log (2π) - 1 + C ω_λ) + C log (N+1))`, and for `p₀ ≤ N`,
`∫_{Λ^{2N} ∩ {|I^dip| = p₀}} e^{-2 F_λ} ≤ exp (2N log N + N log |log λ| + N (log (2π) - 1)
- c N ((p₀ - N)/N)² + C N ω_λ + C log (N+1))` (with `c = 1`). -/
theorem proposition_3_10_main_two (β : ℝ) (hβ : 2 ≤ β) (hβ2 : β = 2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < Real.exp (-2) →
        partitionFunction N β lam
            ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
              + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0)
                + Real.log (dipoleConstant β hβ) - 1 + C * errorRate β hβ lam)
              + C * Real.log (N + 1))) ∧
        ∀ p₀ : ℕ, p₀ ≤ N →
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
              {Z | (isolatedDipoles Z).card = p₀},
              ENNReal.ofReal (Real.exp (-β * energy lam Z))
            ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
              + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0))
              + N * (Real.log (dipoleConstant β hβ) - 1)
              - c * N * (((p₀ : ℝ) - N) / N) ^ 2
              + C * N * errorRate β hβ lam + C * Real.log (N + 1))) := by
  subst hβ2
  obtain ⟨C, hC, h⟩ := exists_critical_bound_one
  exact ⟨C, 1, hC, one_pos, fun N hN lam hlam hlt =>
    main_two_of_critical_bound_one hβ rfl hN (h N hN lam hlam hlt)⟩

open Prop310Critical in
/-- **Proposition 3.10: (eq:critical upper)** (source l. 1575–1584, proof
l. 1595–1650). The critical block of the frozen
`proposition_3_9_and_3_10` for `β = 2`, with the threshold `λ₀ = e⁻²` (the shared threshold of the frozen
statement, `λ₀ ≤ e⁻²`): there is `C > 0` such that for `N ≥ 2`, `0 < λ < e⁻²` and `2λ ≤ R ≤ 1`,
`∫_{Λ^{2N}} e^{-2F_λ + N - |I^dip|/2 + D_R} ≤ exp (2N log N + N (log (2π |log λ|) - 1)
  + C N (ω_λ + log (1/R)/|log λ|) + C log (N+1))`, with `ω_λ = errorRate β hβ λ`. -/
theorem proposition_3_10_critical (β : ℝ) (hβ : 2 ≤ β) (hβ2 : β = 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < Real.exp (-2) →
      ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 →
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
            ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
              + (longIsolatedDipoles Z R).card))
          ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
              + N * (Real.log (2 * Real.pi * |Real.log lam|) - 1)
              + C * N * (errorRate β hβ lam + Real.log (1 / R) / |Real.log lam|)
              + C * Real.log (N + 1))) := by
  subst hβ2
  obtain ⟨C, hC, h⟩ := critical_upper
  exact ⟨C, hC, fun N hN lam hlam hlt R hR hR1 => by
    rw [errorRate_two]
    exact h N hN lam hlam hlt R hR hR1⟩

end TwoComponentCoulomb

end
