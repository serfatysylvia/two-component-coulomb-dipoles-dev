/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.TiltedEnergy
import TwoComponentCoulomb.UpperBound.Isolated

/-!
# Theorem 2, Steps 3--4: the crude bounds for the tilted isolated-pair blocks

Source: proof of Theorem 2 (`prop:linear`), Step 3 (l. 1990: "For
`p < N/2`, the same crude bound applies, including `m ≤ 1`") and Step 4 (l. 2045: "For `p < N/2`,
the crude bound suffices as in Step 3 of the upper-bound proof"). These are the analogues of
(eq:crude) (`isolated_crude`) for the two tilted block integrands of `Fluctuations/TiltedEnergy.lean`.

Both follow from `isolated_crude` itself:

* for the `A₁`-block energy `G⁽¹⁾_γ = alphaBlockEnergy`, the logarithmic terms satisfy
  `log (α^I_i / r̃₁(z_i)) ≥ 0`, so `G⁽¹⁾_γ ≥ F^nn - C |S|`, and `F^nn` is the energy of
  Proposition 3.8 with no assigned pair and `C = 0` (`isolated_crude` does not tie `S` to `p₀`);
* for the `A₃`-tilt, `t ∑_i ((r̃₁(z_i)/γ)² ∧ 1) ≤ 2 t p`.

The extra costs `e^{2βC p}` and `e^{2tp}` are absorbed into `C_β N`
(`TiltedReduction.ofReal_exp_mul_lintegral_le`).

## Main results

* `alphaBlock_crude`: (eq:crude) for `∫_{cell} e^{-β G⁽¹⁾_γ}`.
* `tiltedBlock_crude`: (eq:crude) for `∫_{cell} exp (t ∑_i ((r̃₁(z_i)/γ)² ∧ 1) - β F⁽¹⁾)`.

Both hold for every `β ≥ 2`, every `2 ≤ p ≤ N` and every `γ` (no restriction `p < N/2`, as for
`isolated_crude`).
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

universe u

namespace TwoComponentCoulomb

open IsolatedAssembly

/-- `F^nn` is the pair-assigned energy with no assigned pair and `C = 0`. -/
theorem TiltedReduction.pairAssignedEnergy_zero_empty {ι : Type*} [Fintype ι] [Nontrivial ι]
    (h3 : 3 ≤ Fintype.card ι) (key : ι ↪ ℕ) (lam : ℝ) (z : ι → ℂ) :
    pairAssignedEnergy h3 key lam 0 ∅ z = nnEnergy key lam z := by
  simp [pairAssignedEnergy]

/-- **Absorbing a pointwise factor into (eq:crude)**: if `F ≤ e^{a p} G` pointwise with `a ≥ 0` and
`p ≤ N`, then a bound `e^E ∫ G ≤ e^{X + C N}` gives `e^E ∫ F ≤ e^{X + (C + a) N}`. -/
theorem TiltedReduction.ofReal_exp_mul_lintegral_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {F G : α → ℝ≥0∞} {E X a Cc : ℝ} {p N : ℕ} (ha : 0 ≤ a)
    (hpN : p ≤ N) (hF : ∀ z, F z ≤ ENNReal.ofReal (Real.exp (a * p)) * G z)
    (hG : ENNReal.ofReal (Real.exp E) * ∫⁻ z in s, G z ∂μ ≤
      ENNReal.ofReal (Real.exp (X + Cc * N))) :
    ENNReal.ofReal (Real.exp E) * ∫⁻ z in s, F z ∂μ ≤
      ENNReal.ofReal (Real.exp (X + (Cc + a) * N)) := by
  calc ENNReal.ofReal (Real.exp E) * ∫⁻ z in s, F z ∂μ
      ≤ ENNReal.ofReal (Real.exp E) *
          (ENNReal.ofReal (Real.exp (a * p)) * ∫⁻ z in s, G z ∂μ) :=
        mul_le_mul_right ((lintegral_mono hF).trans_eq
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)) _
    _ = ENNReal.ofReal (Real.exp (a * p)) *
          (ENNReal.ofReal (Real.exp E) * ∫⁻ z in s, G z ∂μ) := mul_left_comm _ _ _
    _ ≤ ENNReal.ofReal (Real.exp (a * p)) * ENNReal.ofReal (Real.exp (X + Cc * N)) :=
        mul_le_mul_right hG _
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have : a * (p : ℝ) ≤ a * N := mul_le_mul_of_nonneg_left (by exact_mod_cast hpN) ha
        linarith

/-- **Theorem 2, Step 3: (eq:crude) for the `A₁`-block** (source l. 1990). For `β ≥ 2`, `C ≥ 0` and
`C₀ ∈ ℝ` there is `C_β > 0` (depending only on `β`, `C`, `C₀`) such that for every finite index
type `ι` with `|ι| = 2p`, tie-break key, graph `γ ∈ G_{p,p₀}` (a fixed-point-free involution `f`),
every `f`-invariant `S`, every `2 ≤ p ≤ N`, `p₀ ≤ p`, `0 < λ ≤ e^{-1}` and every `γ`:
`f(p₀) ≤ p (log N + (2-β) log λ 1_{β>2} + log |log λ| 1_{β=2}) + C_β N` for the integrand
`e^{-β G⁽¹⁾_γ}` (`alphaBlockEnergy`), stated for each graph as `e^{entropy} I(γ) ≤ e^{…}`
(ruling R10). -/
theorem alphaBlock_crude {β : ℝ} (hβ : 2 ≤ β) {C : ℝ} (hC : 0 ≤ C) (C₀ : ℝ) :
    ∃ Cβ : ℝ, 0 < Cβ ∧
      ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (f : ι → ι),
        (∀ i, f (f i) = i) → (∀ i, f i ≠ i) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
        (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N p p₀ : ℕ), Fintype.card ι = 2 * p → 2 ≤ p → p ≤ N →
        p₀ ≤ p → ∀ lam γ : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
          ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
              - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀))) *
            ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
              ENNReal.ofReal (Real.exp (-(β * alphaBlockEnergy h3 key lam γ C S z))) ≤
          ENNReal.ofReal (Real.exp (p * (Real.log N
                + (if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0))
              + Cβ * N)) := by
  obtain ⟨Cc, hCc, hcrude⟩ := isolated_crude.{u} hβ (C := 0) le_rfl C₀
  have hβ0 : 0 ≤ β := by linarith
  refine ⟨Cc + 2 * β * C, by positivity, ?_⟩
  intro ι _ _ key f hf2 hf0 h3 S _ N p p₀ hcard hp2 hpN hp₀ lam γ hlam hl1
  -- `isolated_crude` for `F^nn` (no assigned pair, `C = 0`), and `G⁽¹⁾_γ ≥ F^nn - C |S|`
  refine TiltedReduction.ofReal_exp_mul_lintegral_le (by positivity) hpN (fun z => ?_)
    (hcrude ι key f hf2 hf0 h3 ∅ (by simp) N p p₀ hcard hp2 hpN hp₀ lam hlam hl1)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    TiltedReduction.pairAssignedEnergy_zero_empty]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hS2 : (S.card : ℝ) ≤ 2 * p := by
    have := Finset.card_le_univ S
    rw [hcard] at this
    exact_mod_cast this
  have h1 := mul_le_mul_of_nonneg_left (nnEnergy_sub_le_alphaBlockEnergy h3 key hlam γ C S z) hβ0
  have h2 : β * C * S.card ≤ β * C * (2 * p) := mul_le_mul_of_nonneg_left hS2 (mul_nonneg hβ0 hC)
  linarith

/-- **Theorem 2, Step 4: (eq:crude) with the `A₃` tilt** (source l. 2045). For `β ≥ 2`, `C ≥ 0`,
`C₀ ∈ ℝ` and `t ≥ 0` there is `C_{β,t} > 0` (depending only on `β`, `C`, `C₀`, `t`) such that for
every finite index type `ι` with `|ι| = 2p`, tie-break key, graph `γ ∈ G_{p,p₀}`, every
`f`-invariant `S`, every `2 ≤ p ≤ N`, `p₀ ≤ p`, `0 < λ ≤ e^{-1}` and every `γ`:
`f(p₀) ≤ p (log N + (2-β) log λ 1_{β>2} + log |log λ| 1_{β=2}) + C_{β,t} N` for the integrand
`exp (t ∑_i ((r̃₁(z_i)/γ)² ∧ 1) - β F⁽¹⁾)`, `F⁽¹⁾ = pairAssignedEnergy`, stated for each graph as
`e^{entropy} I(γ) ≤ e^{…}` (ruling R10). -/
theorem tiltedBlock_crude {β : ℝ} (hβ : 2 ≤ β) {C : ℝ} (hC : 0 ≤ C) (C₀ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∃ Cβ : ℝ, 0 < Cβ ∧
      ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (f : ι → ι),
        (∀ i, f (f i) = i) → (∀ i, f i ≠ i) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
        (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N p p₀ : ℕ), Fintype.card ι = 2 * p → 2 ≤ p → p ≤ N →
        p₀ ≤ p → ∀ lam γ : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
          ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
              - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀))) *
            ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
              ENNReal.ofReal (Real.exp (t * ∑ i, min ((nnRadius lam z i / γ) ^ 2) 1
                - β * pairAssignedEnergy h3 key lam C S z)) ≤
          ENNReal.ofReal (Real.exp (p * (Real.log N
                + (if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0))
              + Cβ * N)) := by
  obtain ⟨Cc, hCc, hcrude⟩ := isolated_crude.{u} hβ hC C₀
  refine ⟨Cc + 2 * t, by positivity, ?_⟩
  intro ι _ _ key f hf2 hf0 h3 S hS N p p₀ hcard hp2 hpN hp₀ lam γ hlam hl1
  -- `isolated_crude`, and the tilt is at most `2tp`
  refine TiltedReduction.ofReal_exp_mul_lintegral_le (by positivity) hpN (fun z => ?_)
    (hcrude ι key f hf2 hf0 h3 S hS N p p₀ hcard hp2 hpN hp₀ lam hlam hl1)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hsum : ∑ i, min ((nnRadius lam z i / γ) ^ 2) 1 ≤ 2 * p := by
    calc ∑ i, min ((nnRadius lam z i / γ) ^ 2) 1 ≤ ∑ _i : ι, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => min_le_right _ _
      _ = 2 * p := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one]
          push_cast
          ring
  have := mul_le_mul_of_nonneg_left hsum ht
  linarith

end TwoComponentCoulomb

end
