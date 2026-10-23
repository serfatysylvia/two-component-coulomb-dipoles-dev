/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Energy.MinoPairs

/-!
# The radii `αᵢ` of the ball-growth method in Theorem 2, Step 2

Source: l. 1872–1883, 1941–1946. Write `φ₁ = nearestNeighbor Z`,
`r̃₁ = firstNeighborRadius λ Z`, `r̃₂ = secondNeighborRadius hN λ Z`, and let `τᵢ = tau hN λ Z i`
be the enlarged radii of Proposition 2.2 (source (deftau)). For a parameter `γ` (in the source
`2λ ≤ γ ≤ 1`) the radii of Theorem 2, Step 2 are

`αᵢ := (τᵢ ∧ γ) ∨ r̃₁(zᵢ)`   (source the definition of αᵢ in Step 2, l. 1882–1883).

* `alphaRadius` : the radii `αᵢ`.
* `firstNeighborRadius_le_alphaRadius`, `alphaRadius_le_tau`, `alphaRadius_nearestNeighbor_eq` :
  `λ ≤ r̃₁(zᵢ) ≤ αᵢ ≤ τᵢ`, and `α_{φ₁ i} = αᵢ` on a 2-cycle. These are the only properties of the
  radii used by the ball-growth argument of Proposition 2.2.
* `cutoffRadius_le_two_mul_alphaRadius`, `sq_norm_div_alphaRadius_le` : the displacement ratio on a
  2-cycle (source l. 1897, which writes the error with `r̃₂(zᵢ)` in place of `τᵢ`),
  `|z_{φ₁ i} - zᵢ|² / αᵢ² ≤ 64 (r̃₁ / ((r̃₂ ∧ γ) ∨ r̃₁))²`.
* `sq_div_max_min_le` : (source l. 1941–1945) for `0 < r̃₁ ≤ r̃₂` and `γ > 0`,
  `(r̃₁ / ((r̃₂ ∧ γ) ∨ r̃₁))² ≤ (r̃₁ / r̃₂)² + ((r̃₁ / γ)² ∧ 1)`.
-/

@[expose] public section

namespace TwoComponentCoulomb

variable {N : ℕ}

/-- The radii of the ball-growth method in Theorem 2, Step 2 (source the definition of αᵢ in Step 2,
l. 1882–1883): `αᵢ = (τᵢ ∧ γ) ∨ r̃₁(zᵢ)`, where `τᵢ = tau hN lam Z i` are the enlarged radii of
Proposition 2.2 (source (deftau)) and `γ` is a parameter (`2λ ≤ γ ≤ 1` in the source). -/
noncomputable def alphaRadius (hN : 2 ≤ N) (lam γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : ℝ :=
  max (min (tau hN lam Z i) γ) (firstNeighborRadius lam Z i)

/-! ### Basic inequalities (`λ ≤ r̃₁ ≤ α ≤ τ`) -/

section Basic

variable (hN : 2 ≤ N) (lam γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ)

/-- `r̃₁(zᵢ) ≤ τᵢ`: on a 2-cycle `r̃₁(zᵢ) = r̃₁(z_{φ₁ i}) ≤ r̃₂(zᵢ) ∧ r̃₂(z_{φ₁ i})`. -/
theorem firstNeighborRadius_le_tau (i : Fin N ⊕ Fin N) :
    firstNeighborRadius lam Z i ≤ tau hN lam Z i := by
  by_cases h : nearestNeighbor Z (nearestNeighbor Z i) = i
  · rw [tau_of_twoCycle hN lam Z h]
    exact firstNeighborRadius_le_min_secondNeighborRadius hN lam Z h
  · rw [tau_of_not_twoCycle hN lam Z h]
    exact firstNeighborRadius_le_secondNeighborRadius hN lam Z i

/-- `r̃₁(zᵢ) ≤ αᵢ`. -/
theorem firstNeighborRadius_le_alphaRadius (i : Fin N ⊕ Fin N) :
    firstNeighborRadius lam Z i ≤ alphaRadius hN lam γ Z i :=
  le_max_right _ _

/-- `λ ≤ αᵢ`. -/
theorem lam_le_alphaRadius (i : Fin N ⊕ Fin N) : lam ≤ alphaRadius hN lam γ Z i :=
  (lam_le_firstNeighborRadius lam Z i).trans (firstNeighborRadius_le_alphaRadius hN lam γ Z i)

/-- `αᵢ ≤ τᵢ`. -/
theorem alphaRadius_le_tau (i : Fin N ⊕ Fin N) : alphaRadius hN lam γ Z i ≤ tau hN lam Z i :=
  max_le (min_le_left _ _) (firstNeighborRadius_le_tau hN lam Z i)

/-- `αᵢ ≤ γ ∨ r̃₁(zᵢ)`. -/
theorem alphaRadius_le_max (i : Fin N ⊕ Fin N) :
    alphaRadius hN lam γ Z i ≤ max γ (firstNeighborRadius lam Z i) :=
  max_le_max (min_le_right _ _) le_rfl

/-- On a 2-cycle `{i, φ₁ i}`: `α_{φ₁ i} = αᵢ`. -/
theorem alphaRadius_nearestNeighbor_eq {i : Fin N ⊕ Fin N}
    (hi : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    alphaRadius hN lam γ Z (nearestNeighbor Z i) = alphaRadius hN lam γ Z i := by
  unfold alphaRadius
  rw [tau_eq_of_twoCycle hN lam Z hi, firstNeighborRadius_nearestNeighbor_eq lam Z hi]

end Basic

theorem alphaRadius_pos (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : 0 < alphaRadius hN lam γ Z i :=
  hlam.trans_le (lam_le_alphaRadius hN lam γ Z i)

/-! ### The displacement ratio (source l. 1897) -/

section Displacement

/-- On a 2-cycle the cut-off second radius `(r̃₂(zᵢ) ∧ γ) ∨ r̃₁(zᵢ)` is at most `2 αᵢ`. This uses
`τᵢ ≥ r̃₂(zᵢ) - r̃₁(zᵢ)`, from `|r̃₂(zᵢ) - r̃₂(z_{φ₁ i})| ≤ ¼ |zᵢ - z_{φ₁ i}| ≤ r̃₁(zᵢ)`
(source (rrj)). -/
theorem cutoffRadius_le_two_mul_alphaRadius (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (γ : ℝ)
    (Z : Fin N ⊕ Fin N → ℂ) {i : Fin N ⊕ Fin N}
    (hi : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i) ≤
      2 * alphaRadius hN lam γ Z i := by
  have hrr := abs_secondNeighborRadius_sub_le hN lam Z (i := i) rfl hi
  have hd := norm_sub_nearestNeighbor_le_four_mul lam Z i
  have hr1 := lam_le_firstNeighborRadius lam Z i
  unfold alphaRadius
  rw [tau_of_twoCycle hN lam Z hi]
  have hR' := (abs_le.1 hrr).2
  generalize secondNeighborRadius hN lam Z i = R at *
  generalize secondNeighborRadius hN lam Z (nearestNeighbor Z i) = R' at *
  generalize firstNeighborRadius lam Z i = ρ at *
  generalize ‖Z i - Z (nearestNeighbor Z i)‖ = d at *
  have hm := le_max_right (min (min R R') γ) ρ
  rcases le_total (min R γ) (2 * ρ) with h | h
  · exact max_le (by linarith) (by linarith)
  · have h1 := min_le_left R γ
    have h2 := min_le_right R γ
    have h3 : min R γ / 2 ≤ min (min R R') γ :=
      le_min (le_min (by linarith) (by linarith)) (by linarith)
    have h4 := le_max_left (min (min R R') γ) ρ
    exact max_le (by linarith) (by linarith)

/-- **The displacement ratio** with the radii `α` (source l. 1897): at a vertex `i` of a 2-cycle,
`|z_{φ₁ i} - zᵢ|² / αᵢ² ≤ 64 (r̃₁(zᵢ) / ((r̃₂(zᵢ) ∧ γ) ∨ r̃₁(zᵢ)))²`. -/
theorem sq_norm_div_alphaRadius_le (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (γ : ℝ)
    (Z : Fin N ⊕ Fin N → ℂ) {i : Fin N ⊕ Fin N}
    (hi : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    ‖Z (nearestNeighbor Z i) - Z i‖ ^ 2 / alphaRadius hN lam γ Z i ^ 2 ≤
      64 * (firstNeighborRadius lam Z i /
        max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i)) ^ 2 := by
  have hρ := cutoffRadius_le_two_mul_alphaRadius hN hlam γ Z hi
  have hd : ‖Z (nearestNeighbor Z i) - Z i‖ ≤ 4 * firstNeighborRadius lam Z i := by
    rw [norm_sub_rev]
    exact norm_sub_nearestNeighbor_le_four_mul lam Z i
  have ha := alphaRadius_pos hN hlam γ Z i
  have hr1 : 0 < firstNeighborRadius lam Z i :=
    hlam.trans_le (lam_le_firstNeighborRadius lam Z i)
  have hρpos : 0 < max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i) :=
    hr1.trans_le (le_max_right _ _)
  have hd0 := norm_nonneg (Z (nearestNeighbor Z i) - Z i)
  generalize max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i) = ρ at *
  generalize alphaRadius hN lam γ Z i = a at *
  generalize firstNeighborRadius lam Z i = r at *
  generalize ‖Z (nearestNeighbor Z i) - Z i‖ = d at *
  have hmain : d * ρ ≤ 8 * r * a := by
    have h1 := mul_le_mul_of_nonneg_left hρ hd0
    have h2 := mul_le_mul_of_nonneg_left hd ha.le
    nlinarith
  have hfrac : d / a ≤ 8 * (r / ρ) := by
    rw [div_le_iff₀ ha]
    have : 8 * (r / ρ) * a = 8 * r * a / ρ := by ring
    rw [this, le_div_iff₀ hρpos]
    exact hmain
  calc d ^ 2 / a ^ 2 = (d / a) ^ 2 := by rw [div_pow]
    _ ≤ (8 * (r / ρ)) ^ 2 := pow_le_pow_left₀ (div_nonneg hd0 ha.le) hfrac 2
    _ = 64 * (r / ρ) ^ 2 := by ring

end Displacement

/-! ### Splitting the quadratic error (source l. 1941–1945) -/

section Split

/-- For `0 < r₁ ≤ r₂` and `γ > 0`:
`(r₁ / ((r₂ ∧ γ) ∨ r₁))² ≤ (r₁ / r₂)² + ((r₁ / γ)² ∧ 1)` (source l. 1941–1945). -/
theorem sq_div_max_min_le {r₁ r₂ γ : ℝ} (h1 : 0 < r₁) (h12 : r₁ ≤ r₂) (hγ : 0 < γ) :
    (r₁ / max (min r₂ γ) r₁) ^ 2 ≤ (r₁ / r₂) ^ 2 + min ((r₁ / γ) ^ 2) 1 := by
  have hs := sq_nonneg (r₁ / r₂)
  rcases le_total r₂ γ with h | h
  · rw [min_eq_left h, max_eq_left h12]
    have := le_min (sq_nonneg (r₁ / γ)) zero_le_one
    linarith
  · rw [min_eq_right h]
    rcases le_total γ r₁ with h' | h'
    · rw [max_eq_right h', div_self h1.ne', one_pow]
      have : 1 ≤ (r₁ / γ) ^ 2 := one_le_pow₀ ((one_le_div hγ).2 h')
      rw [min_eq_right this]
      linarith
    · rw [max_eq_left h']
      have : (r₁ / γ) ^ 2 ≤ 1 := pow_le_one₀ (div_nonneg h1.le hγ.le) ((div_le_one hγ).2 h')
      rw [min_eq_left this]
      linarith

/-- For `0 < r₁`: `(r₁ / ((r₂ ∧ γ) ∨ r₁))² ≤ 1`. -/
theorem sq_div_max_min_le_one {r₁ : ℝ} (h1 : 0 < r₁) (r₂ γ : ℝ) :
    (r₁ / max (min r₂ γ) r₁) ^ 2 ≤ 1 := by
  have hρ : 0 < max (min r₂ γ) r₁ := h1.trans_le (le_max_right _ _)
  exact pow_le_one₀ (div_nonneg h1.le hρ.le) ((div_le_one hρ).2 (le_max_right _ _))

end Split

end TwoComponentCoulomb

end
