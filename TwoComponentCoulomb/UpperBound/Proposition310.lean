/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.Energy
public import TwoComponentCoulomb.Frozen.ErrorRate
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.Frozen.PartitionFunction
public import TwoComponentCoulomb.Frozen.SmearedKernel
import TwoComponentCoulomb.UpperBound.Proposition310Critical
import TwoComponentCoulomb.UpperBound.UpperRate

/-!
# Proof of the frozen statement `TwoComponentCoulomb.proposition_3_10`

Implementation module of `TwoComponentCoulomb/Frozen/Proposition310.lean` (registered in
`manifest/frozen_anchors.json`). Its theorem `TwoComponentCoulomb.UpperBound.proposition_3_10`
states and proves exactly the frozen statement (Proposition 3.10, `prop:upper bound`, source
l. 1423–1455), by cases on `β`:

* `β > 2`: (ubz) and (eq:neutral bound) are `UpperAssembly.proposition_3_10_main_of_two_lt`, and
  (eq:u bound) is `LongDipoles.proposition_3_10_long_of_two_lt`; the threshold is the minimum of
  their two thresholds and `e⁻²`;
* `β = 2`: the threshold is `e⁻²`; (ubz) and (eq:neutral bound) are
  `proposition_3_10_main_two`, and (eq:critical upper) is `proposition_3_10_critical`.

This module must never import the frozen file, which proves its statement by `exact` this
theorem.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace TwoComponentCoulomb.UpperBound

/-- **Proposition 3.10** (`prop:upper bound`, source l. 1423–1455), exactly the frozen statement
`TwoComponentCoulomb.proposition_3_10`. -/
theorem proposition_3_10 {β : ℝ} {hβ : 2 ≤ β} :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ Real.exp (-2) ∧
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
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
                + C * N * errorRate β hβ lam + C * Real.log (N + 1)))) ∧
      (2 < β → ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, 1 ≤ p₀' → p₀' ≤ N →
          C₁ * (2 * Real.pi / dipoleConstant β hβ *
              ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r) ≤ (p₀' : ℝ) / N →
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
              {Z | p₀' ≤ (longIsolatedDipoles Z R).card},
              ENNReal.ofReal (Real.exp (-β * energy lam Z))
            ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ) - 1)
                - c * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) /
                    (2 * Real.pi / dipoleConstant β hβ *
                      ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r))
                + C₂ * N * errorRate β hβ lam + C₂ * Real.log (N + 1)))) ∧
      (β = 2 → ∃ C : ℝ, 0 < C ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 →
          ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
              ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
                + (longIsolatedDipoles Z R).card))
            ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * (Real.log (2 * Real.pi * |Real.log lam|) - 1)
                + C * N * (errorRate β hβ lam + Real.log (1 / R) / |Real.log lam|)
                + C * Real.log (N + 1)))) := by
  rcases hβ.eq_or_lt with h | h2
  · have hβ2 : β = 2 := h.symm
    obtain ⟨C, c, hC, hc, hmain⟩ := proposition_3_10_main_two β hβ hβ2
    obtain ⟨C', hC', hcrit⟩ := proposition_3_10_critical β hβ hβ2
    exact ⟨Real.exp (-2), Real.exp_pos _, le_rfl, ⟨C, c, hC, hc, hmain⟩,
      fun h2 => absurd (hβ2 ▸ h2) (lt_irrefl 2), fun _ => ⟨C', hC', hcrit⟩⟩
  · obtain ⟨l₁, hl₁, C, c, hC, hc, h1⟩ := UpperAssembly.proposition_3_10_main_of_two_lt h2
    obtain ⟨l₂, hl₂, c', C₁, C₂, hc', hC₁, hC₂, h2'⟩ :=
      LongDipoles.proposition_3_10_long_of_two_lt h2
    refine ⟨min (min l₁ l₂) (Real.exp (-2)), lt_min (lt_min hl₁ hl₂) (Real.exp_pos _),
      min_le_right _ _, ⟨C, c, hC, hc, fun N hN lam hlam hlt => ?_⟩,
      fun _ => ⟨c', C₁, C₂, hc', hC₁, hC₂, fun N hN lam hlam hlt =>
        h2' N hN lam hlam (lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_right _ _)))⟩,
      fun h => absurd h h2.ne'⟩
    simp only [ite_eq_left h2, ite_eq_right h2.ne', add_zero]
    exact h1 N hN lam hlam (lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_left _ _)))

end TwoComponentCoulomb.UpperBound

end
