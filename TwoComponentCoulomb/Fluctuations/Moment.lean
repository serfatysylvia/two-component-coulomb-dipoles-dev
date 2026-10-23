/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.Theorem2Assembly
public import TwoComponentCoulomb.Frozen.ErrorRate
import TwoComponentCoulomb.Fluctuations.AlphaRadii
import TwoComponentCoulomb.Fluctuations.CriticalElectric
import TwoComponentCoulomb.Fluctuations.MomentCombine
import TwoComponentCoulomb.UpperBound.UpperRate

/-!
# Theorem 2, Steps 2--4 and the moment bound

Source: proof of Theorem 2 (`prop:linear`), Steps 2--4 (l. 1872–2058) and the moment bound of
Step 6 (l. 2086–2093): for the radii `αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)` there are `c, C > 0` and `λ₁ > 0`
such that, for `N ≥ 2`, `0 < λ < λ₁` and `2λ ≤ γ ≤ 1`,

`log 𝔼_ℙ[exp (c ∫ |∇h_α|²)] ≤ C N (φ_β(γ) + ω_λ) + C log (N + 1)`,

with `ω_λ = errorRate β λ` (eq:defgammal). In Lean this is
`MomentBoundRate β hβ (errorRate β hβ)` (`Fluctuations/Theorem2Assembly.lean`), the moment input
of the assembly `theorem_2_of_moment_rate` at `ω = errorRate β hβ`.

* `β > 2`: the rate-generic chain of Steps 3--4 and the Hölder combination of Step 6
  (`momentBound_of_two_lt_rate`, `Fluctuations/MomentCombine.lean`) at `ω = errorRate β`, which
  satisfies the rate hypotheses of the upper bound (`upperRateHyp_errorRate`,
  `UpperBound/UpperRate.lean`). The lower bound of Proposition 4.1 used in the division by the
  partition function has, for `β > 2`, the error rate of Proposition 3.8, which these hypotheses
  bound by `ω_λ` .
* `β = 2`: (eq:critical electric) with `ℓ^{-1/5} = ω_λ` (source l. 1903–1938,
  `exists_momentBound_two`, `Fluctuations/CriticalElectric.lean`), in the shape of
  `MomentBoundRate` (`momentBound_two`).

## Main results

* `momentBound_of_two_lt`: `MomentBoundRate β hβ.le (errorRate β hβ.le)` for `β > 2`.
* `momentBound_two`: `MomentBoundRate 2 le_rfl (errorRate 2 le_rfl)`.
* `momentBound`: `MomentBoundRate β hβ (errorRate β hβ)` for every `β ≥ 2`.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- **The moment bound for `β > 2`** (Theorem 2, Steps 2--4 and Step 6; source
l. 1872–2093): `MomentBoundRate` at `ω_λ = errorRate β λ`. It is `momentBound_of_two_lt_rate`
at `ω = errorRate β`, which satisfies `UpperRateHyp` (`upperRateHyp_errorRate`). -/
theorem momentBound_of_two_lt {β : ℝ} (hβ : 2 < β) :
    MomentBoundRate β hβ.le (errorRate β hβ.le) :=
  momentBound_of_two_lt_rate hβ _ (upperRateHyp_errorRate β hβ)

/-- **The moment bound at `β = 2`** (Theorem 2, Step 2 at `β = 2`, (eq:critical
electric), source l. 1903–1938, with `ℓ^{-1/5} = ω_λ`): `MomentBoundRate` at
`ω_λ = errorRate 2 λ`. The radii are `αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)` (`alphaRadius`) for `N ≥ 2`;
`MomentBoundRate` quantifies over all `N`, and its three items only concern `N ≥ 2`, so the radii
for `N < 2` are irrelevant (they are taken to be `γ`). The bounds are those of
`exists_momentBound_two`. -/
theorem momentBound_two : MomentBoundRate 2 le_rfl (errorRate 2 le_rfl) := by
  obtain ⟨c, C, lam₁, hc, hC, hlam₁, hmeas, hmom⟩ := exists_momentBound_two
  have hα : ∀ (N : ℕ) (hN : 2 ≤ N) (lam γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ),
      (fun i => if h : 2 ≤ N then alphaRadius h lam γ Z i else γ) = alphaRadius hN lam γ Z :=
    fun N hN lam γ Z => funext fun i => dite_eq_left hN
  refine ⟨fun N lam γ Z i => if h : 2 ≤ N then alphaRadius h lam γ Z i else γ, c, C, lam₁, hc, hC,
    hlam₁, ?_, ?_, ?_⟩
  · intro N hN lam γ hlam _ _ _ Z i
    simp only [dite_eq_left hN]
    exact ⟨alphaRadius_pos hN hlam γ Z i, alphaRadius_le_max hN lam γ Z i⟩
  · intro N hN lam γ hlam hlam1 hγ hγ1
    simp only [hα N hN]
    exact hmeas N hN lam γ hlam hlam1 hγ hγ1
  · intro N hN lam γ hlam hlam1 hγ hγ1
    simp only [hα N hN]
    exact hmom N hN lam γ hlam hlam1 hγ hγ1

/-- **The moment bound of Theorem 2, Steps 2--4** (source l. 1872–2093): for every
`β ≥ 2`, `MomentBoundRate β hβ (errorRate β hβ)`, i.e. there are radii `0 < αᵢ ≤ γ ∨ r̃₁(zᵢ)`
and `c, C, λ₁ > 0` such that, for `N ≥ 2`, `0 < λ < λ₁` and `2λ ≤ γ ≤ 1`,
`𝔼_ℙ[exp (c ∫ |∇h_α|²)] ≤ exp (C N (φ_β(γ) + ω_λ) + C log (N + 1))` with
`ω_λ = errorRate β λ`. It is `momentBound_two` at `β = 2` and `momentBound_of_two_lt`
for `β > 2` (the proof of `2 ≤ β` is irrelevant: `MomentBoundRate` is a proposition). -/
theorem momentBound (β : ℝ) (hβ : 2 ≤ β) : MomentBoundRate β hβ (errorRate β hβ) := by
  rcases hβ.eq_or_lt with h2 | h2
  · subst h2
    exact momentBound_two
  · exact momentBound_of_two_lt h2

end TwoComponentCoulomb

end
