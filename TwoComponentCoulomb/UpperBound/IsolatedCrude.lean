/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.NearestNeighbor.Radius
public import TwoComponentCoulomb.UpperBound.IsolatedRadial
public import Mathlib.MeasureTheory.Constructions.Pi
import TwoComponentCoulomb.Gibbs.Basic
import TwoComponentCoulomb.PhaseSpace.Packing

/-!
# Proposition 3.9, the crude case: the integral over the representatives

Source: proof of Proposition 3.9 (`prop:isolated`), l. 1410--1415 (the
case `p < N/2`). After Steps 1--2 (`(pred3)`, which holds for every
`p ≤ N`), the cell integral `I(γ, S)` is bounded by `(𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}))^p` times
the integral over the representatives `W_p ∈ Λ^p` of
`∏_{j neutral} (1 + C' φ_β(ρ_j)) ∏_{j same-sign} C' (ℓ^{-1} 1_{β=2} + (λ/ρ_j)^{β-2} 1_{β>2})`.
This file bounds that integral by `N^p (1 + 2C')^p e^{2N}`, as in the source:

* for `β > 2` every factor is at most `1 + C'` (`φ_β ≤ 1` and `(λ/ρ)^{β-2} ≤ 1` on `[λ, ∞)`;
  l. 1410);
* for `β = 2` the factor `1 + C' (1 + |log ρ|)/ℓ` is at most `(1 + 2C') e^{log⁺ ρ}` (l. 1410), and
  the packing bound `∑_j ρ_j² ≤ 2N` (the representatives lie in `Λ`), with
  `log⁺ ρ ≤ (p/(2N)) ρ² + ½ log (N/p)` and `p log (N/p) ≤ N` (l. 1411--1414), gives
  `∑_j log⁺ ρ_j ≤ (p/(2N)) ∑_j ρ_j² + (p/2) log (N/p) ≤ 2N`.

## Main results

* `IsolatedCrude.factor_le`: each factor of `(pred3)` is at most `(1 + 2C') e^{max (log ρ) 0}`.
* `IsolatedCrude.sum_nnRadius_sq_le`: the packing bound `∑_j r̃₁(w_j)² ≤ N + p λ²`.
* `IsolatedCrude.lintegral_ref_le_crude`: `∫_{Λ^p} ∏_j (factor) ≤ N^p (1 + 2C')^p e^{2N}` for
  `p ≤ N`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace TwoComponentCoulomb

namespace IsolatedCrude

variable {β lam : ℝ}

/-! ### The factors of `(pred3)` -/

/-- For `β > 2` the neutral profile satisfies `φ_β ≤ 1` on `[λ, ∞)`. -/
theorem isolatedPhi_le_one (hβ : 2 ≤ β) (h2 : 2 < β) (hlam : 0 < lam) {ρ : ℝ} (hρ : lam ≤ ρ) :
    isolatedPhi β hβ lam ρ ≤ 1 := by
  refine (isolatedPhi_anti hβ h2 hlam le_rfl hρ).trans (le_of_eq ?_)
  unfold isolatedPhi
  split_ifs with h <;> first | (exfalso; linarith) | simp [div_self hlam.ne']

/-- The normalized same-sign factor satisfies `ℓ^{-1} 1_{β=2} + (λ/ρ)^{β-2} 1_{β>2} ≤ 1` on
`[λ, ∞)`. -/
theorem isolatedTail_le_one (hβ : 2 ≤ β) (hlam : 0 < lam) (hl1 : lam ≤ Real.exp (-1)) {ρ : ℝ}
    (hρ : lam ≤ ρ) : isolatedTail β hβ lam ρ ≤ 1 := by
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  unfold isolatedTail
  split_ifs with h
  · exact inv_le_one_of_one_le₀ (one_le_abs_log hlam hl1)
  · exact Real.rpow_le_one (by positivity) ((div_le_one hρ0).2 hρ) (by linarith)

/-- `|log ρ| ≤ ℓ + max (log ρ) 0` for `ρ ≥ λ`, `ℓ = |log λ|`. -/
theorem abs_log_le (hlam : 0 < lam) (hl1 : lam ≤ Real.exp (-1)) {ρ : ℝ} (hρ : lam ≤ ρ) :
    |Real.log ρ| ≤ |Real.log lam| + max (Real.log ρ) 0 := by
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  have hl := log_le_neg_one hlam hl1
  rw [abs_of_neg (by linarith : Real.log lam < 0)]
  rcases le_total 0 (Real.log ρ) with h | h
  · rw [abs_of_nonneg h, max_eq_left h]
    linarith
  · rw [abs_of_nonpos h, max_eq_right h]
    have := Real.log_le_log hlam hρ
    linarith

/-- **Each factor of `(pred3)` is at most `(1 + 2C') e^{log⁺ ρ}`** (source l. 1410): for
`β > 2` the factors are at most `1 + C'`; for `β = 2`,
`1 + C' (1 + |log ρ|)/ℓ ≤ 1 + 2C' + C' log⁺ ρ ≤ (1 + 2C') (1 + log⁺ ρ)`. -/
theorem factor_le (hβ : 2 ≤ β) (hlam : 0 < lam) (hl1 : lam ≤ Real.exp (-1)) {C' : ℝ}
    (hC' : 0 ≤ C') {ρ : ℝ} (hρ : lam ≤ ρ) (P : Prop) [Decidable P] :
    (if P then C' * isolatedTail β hβ lam ρ else 1 + C' * isolatedPhi β hβ lam ρ) ≤
      (1 + 2 * C') * Real.exp (max (Real.log ρ) 0) := by
  set u := max (Real.log ρ) 0 with hu
  have hu0 : 0 ≤ u := le_max_right _ _
  have hexp : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hK : 1 + 2 * C' ≤ (1 + 2 * C') * Real.exp u := by
    have : 1 ≤ Real.exp u := Real.one_le_exp hu0
    nlinarith
  have hφ : 1 + C' * isolatedPhi β hβ lam ρ ≤ (1 + 2 * C') * (1 + u) := by
    rcases hβ.eq_or_lt with h2 | h2
    · rw [isolatedPhi_of_eq_two hβ h2.symm]
      have hℓ := one_le_abs_log hlam hl1
      have ha := abs_log_le hlam hl1 hρ
      rw [← hu] at ha
      have hdiv : (1 + |Real.log ρ|) / |Real.log lam| ≤ 2 + u := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hdiv hC']
    · have := isolatedPhi_le_one hβ h2 hlam hρ
      nlinarith [mul_le_mul_of_nonneg_left this hC']
  split_ifs
  · have := isolatedTail_le_one hβ hlam hl1 hρ
    nlinarith [mul_le_mul_of_nonneg_left this hC']
  · calc 1 + C' * isolatedPhi β hβ lam ρ ≤ (1 + 2 * C') * (1 + u) := hφ
      _ ≤ (1 + 2 * C') * Real.exp u := mul_le_mul_of_nonneg_left hexp (by positivity)

/-! ### The packing bound and the sum of the logarithms -/

/-- **Packing** (source l. 1410): for points `w_j` of the box,
`∑_j r̃₁(w_j)² ≤ 2N + p λ²` (the open discs of radius half the nearest-neighbour distance are
disjoint, `sum_sq_le_of_separated`). -/
theorem sum_nnRadius_sq_le {κ : Type*} [Fintype κ] [Nontrivial κ] {N : ℕ} (w : κ → ℂ)
    (hw : ∀ j, w j ∈ box N) (lam : ℝ) :
    ∑ j, nnRadius lam w j ^ 2 ≤ 2 * N + Fintype.card κ * lam ^ 2 := by
  classical
  set d : κ → ℝ := fun j => (Finset.univ.erase j).inf' (erase_nonempty j)
    (fun l => ‖w j - w l‖) with hd
  have hd0 : ∀ j, 0 ≤ d j := fun j => Finset.le_inf' _ _ fun l _ => norm_nonneg _
  have hdd : ∀ j, d j ≤ Real.sqrt (2 * N) := by
    intro j
    obtain ⟨l, hl⟩ := erase_nonempty j
    exact (Finset.inf'_le _ hl).trans (norm_sub_le_of_mem_box (hw j) (hw l))
  have hsep : ∀ i j, i ≠ j → d i ≤ ‖w i - w j‖ := fun i j hij =>
    Finset.inf'_le _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ _⟩)
  have hpack := sum_sq_le_of_separated w d hw hd0 hdd hsep
  have hrad : ∀ j, nnRadius lam w j = max (d j / 4) lam := fun j => rfl
  have hsq : ∀ j, nnRadius lam w j ^ 2 ≤ d j ^ 2 / 16 + lam ^ 2 := by
    intro j
    rw [hrad]
    rcases max_choice (d j / 4) lam with h | h <;> rw [h]
    · have := sq_nonneg lam
      nlinarith
    · have := sq_nonneg (d j)
      nlinarith
  have hpi : 36 * (N : ℝ) / Real.pi / 16 ≤ 2 * N := by
    rw [div_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.two_le_pi, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  calc ∑ j, nnRadius lam w j ^ 2 ≤ ∑ j, (d j ^ 2 / 16 + lam ^ 2) := Finset.sum_le_sum fun j _ => hsq j
    _ = (∑ j, d j ^ 2) / 16 + Fintype.card κ * lam ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 * N + Fintype.card κ * lam ^ 2 := by
        have : (∑ j, d j ^ 2) / 16 ≤ 36 * (N : ℝ) / Real.pi / 16 :=
          div_le_div_of_nonneg_right hpack (by norm_num)
        linarith

/-- `log⁺ ρ ≤ (P/(2N)) ρ² + ½ log (N/P)` for `ρ > 0` and `0 < P ≤ N` (source l. 1411--1413). -/
theorem max_log_le {ρ P N : ℝ} (hρ : 0 < ρ) (hP : 0 < P) (hPN : P ≤ N) :
    max (Real.log ρ) 0 ≤ P / N * ρ ^ 2 / 2 + Real.log (N / P) / 2 := by
  have hN : 0 < N := hP.trans_le hPN
  have hlog : 0 ≤ Real.log (N / P) := Real.log_nonneg ((one_le_div hP).2 hPN)
  refine max_le ?_ (by positivity)
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < P / N * ρ ^ 2)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_div hP.ne' hN.ne', Real.log_pow,
    Nat.cast_ofNat] at h
  rw [Real.log_div hN.ne' hP.ne']
  linarith

/-- **The sum of the logarithms** (source l. 1410--1414): for `p ≤ N` points of the box,
`∑_j log⁺ r̃₁(w_j) ≤ 2N` (for `λ ≤ 1`). -/
theorem sum_max_log_le {κ : Type*} [Fintype κ] [Nontrivial κ] {N : ℕ}
    (hpN : Fintype.card κ ≤ N) (w : κ → ℂ) (hw : ∀ j, w j ∈ box N) {lam : ℝ} (hlam : 0 < lam)
    (hl1 : lam ≤ 1) :
    ∑ j, max (Real.log (nnRadius lam w j)) 0 ≤ 2 * N := by
  set P : ℝ := (Fintype.card κ : ℝ) with hPdef
  have hP : 0 < P := by rw [hPdef]; exact_mod_cast Fintype.card_pos
  have hPN : P ≤ N := by rw [hPdef]; exact_mod_cast hpN
  have hN : (0 : ℝ) < N := hP.trans_le hPN
  have hpack := sum_nnRadius_sq_le w hw lam
  rw [← hPdef] at hpack
  have hl2 : lam ^ 2 ≤ 1 := by nlinarith
  have h1 : ∀ j, max (Real.log (nnRadius lam w j)) 0 ≤
      P / N * nnRadius lam w j ^ 2 / 2 + Real.log (N / P) / 2 := fun j =>
    max_log_le (hlam.trans_le (le_nnRadius lam w j)) hP hPN
  have h2 : P * Real.log (N / P) ≤ N - P := by
    have := Real.log_le_sub_one_of_pos (div_pos hN hP)
    have e : P * (N / P - 1) = N - P := by field_simp
    nlinarith
  calc ∑ j, max (Real.log (nnRadius lam w j)) 0
      ≤ ∑ j, (P / N * nnRadius lam w j ^ 2 / 2 + Real.log (N / P) / 2) :=
        Finset.sum_le_sum fun j _ => h1 j
    _ = P / N * (∑ j, nnRadius lam w j ^ 2) / 2 + P * Real.log (N / P) / 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, ← hPdef]
        ring
    _ ≤ P / N * (2 * N + P * 1) / 2 + (N - P) / 2 := by
        gcongr
        · exact hpack.trans (by gcongr)
    _ ≤ 2 * N := by
        have : P / N * (2 * N + P * 1) ≤ 3 * P := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hN]
          nlinarith
        linarith

/-! ### The integral over the representatives -/

/-- **The crude bound of the integral over the representatives** (source l. 1410--1415): for
`p = |κ| ≤ N`, `0 < λ ≤ e^{-1}` and `C' ≥ 0`, the integral over `Λ^κ` of the product of `(pred3)`
(with any assignment `a` of the representatives to the same-sign type) is at most
`N^p (1 + 2C')^p e^{2N}`. -/
theorem lintegral_ref_le_crude {κ : Type*} [Fintype κ] [Nontrivial κ] {N : ℕ}
    (hpN : Fintype.card κ ≤ N) (hlam : 0 < lam) (hl1 : lam ≤ Real.exp (-1)) {C' : ℝ}
    (hC' : 0 ≤ C') (g : κ → ℝ → ℝ)
    (hg : ∀ j ρ, lam ≤ ρ → g j ρ ≤ (1 + 2 * C') * Real.exp (max (Real.log ρ) 0)) :
    ∫⁻ w in Set.univ.pi (fun _ : κ => box N), ∏ j, ENNReal.ofReal (g j (nnRadius lam w j)) ≤
      (N : ℝ≥0∞) ^ Fintype.card κ *
        ENNReal.ofReal ((1 + 2 * C') ^ Fintype.card κ * Real.exp (2 * N)) := by
  have hl1' : lam ≤ 1 := hl1.trans (by rw [Real.exp_le_one_iff]; norm_num)
  have hmeas : MeasurableSet (Set.univ.pi (fun _ : κ => box N)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_box N
  have hpt : ∀ w ∈ Set.univ.pi (fun _ : κ => box N),
      ∏ j, ENNReal.ofReal (g j (nnRadius lam w j)) ≤
        ENNReal.ofReal ((1 + 2 * C') ^ Fintype.card κ * Real.exp (2 * N)) := by
    intro w hw
    have hw' : ∀ j, w j ∈ box N := fun j => hw j (Set.mem_univ j)
    calc ∏ j, ENNReal.ofReal (g j (nnRadius lam w j))
        ≤ ∏ j, ENNReal.ofReal ((1 + 2 * C') *
            Real.exp (max (Real.log (nnRadius lam w j)) 0)) :=
          Finset.prod_le_prod fun j _ =>
            ENNReal.ofReal_le_ofReal (hg j _ (le_nnRadius lam w j))
      _ = ENNReal.ofReal (∏ j, (1 + 2 * C') *
            Real.exp (max (Real.log (nnRadius lam w j)) 0)) :=
          (ENNReal.ofReal_prod_of_nonneg fun j _ => by positivity).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
          gcongr
          exact sum_max_log_le hpN w hw' hlam hl1'
  calc ∫⁻ w in Set.univ.pi (fun _ : κ => box N), ∏ j, ENNReal.ofReal (g j (nnRadius lam w j))
      ≤ ∫⁻ _ in Set.univ.pi (fun _ : κ => box N),
          ENNReal.ofReal ((1 + 2 * C') ^ Fintype.card κ * Real.exp (2 * N)) :=
        setLIntegral_mono measurable_const hpt
    _ = _ := by
        rw [setLIntegral_const, volume_pi_pi]
        simp only [volume_box, Finset.prod_const, Finset.card_univ]
        rw [mul_comm]

end IsolatedCrude

end TwoComponentCoulomb

end
