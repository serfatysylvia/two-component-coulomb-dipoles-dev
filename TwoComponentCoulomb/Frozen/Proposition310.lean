-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
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
import TwoComponentCoulomb.UpperBound.Proposition310

/-!
# Frozen: `TwoComponentCoulomb.proposition_3_10`

Frozen statement, approved by the authors in this exact form (RULINGS.md R20). Source: l. 1423–1455.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace TwoComponentCoulomb

/-- **Proposition 3.10** (`prop:upper bound`, source l. 1423–1455). -/
theorem proposition_3_10 (β : ℝ) (hβ : 2 ≤ β) :
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
                + C * Real.log (N + 1)))) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact TwoComponentCoulomb.UpperBound.proposition_3_10
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end TwoComponentCoulomb

end
-- FROZEN_ANCHOR_SUFFIX_END
