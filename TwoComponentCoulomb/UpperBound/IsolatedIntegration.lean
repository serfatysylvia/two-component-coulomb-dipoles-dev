/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.NearestNeighbor.Radius
public import TwoComponentCoulomb.UpperBound.AuxIntegrationVolume
public import TwoComponentCoulomb.UpperBound.AuxOptimization
public import TwoComponentCoulomb.UpperBound.IsolatedRadial
public import Mathlib.MeasureTheory.Constructions.Pi
import TwoComponentCoulomb.Gibbs.Basic

/-!
# Proposition 3.8, Step 3: integration of the representatives

Source: proof of Proposition 3.8 (`prop:isolated`), Step 3, l. 1269–1314.
After Steps 1--2 (`UpperBound/IsolatedReduction.lean`, `(pred3)`), the cell integral `I(γ)` is bounded by
`(𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}))^p` times the integral over the representatives
`W_p ∈ Λ^p` of
`∏_{j neutral} (1 + C' φ_β(ρ_j)) ∏_{j same-sign} C' (ℓ^{-1} 1_{β=2} + (λ/ρ_j)^{β-2} 1_{β>2})`,
with `ρ_j = r̃₁(w_j)` computed among the representatives. This file expands the first product,
with `k` selected neutral factors, and reduces each term to an integral of Proposition 3.6 or 3.7
type over `Λ^p` with the `k + q` selected points as marked points
(source l. 1275–1314).

## Main results

* `IsolatedIntegration.lintegral_pi_box_comp_equiv`, `IsolatedIntegration.nnRadius_comp_relabel`:
  relabelling the representatives by `Fin p` (Lebesgue measure, the box and `r̃₁` are invariant).
* `IsolatedIntegration.two_mul_card_filter_ref`: a set `S` of vertices invariant under the
  pairing contains exactly `|S|/2` representatives.
* `IsolatedIntegration.exists_relabel_ref`: the integral over the representatives of `(pred3)`
  equals an integral over `Λ^p` in which the same-sign representatives form a set `T ⊆ Fin p`
  with `|T| = q`.
* `IsolatedIntegration.lintegral_prod_ite_le`: the expansion
  `∏_{j ∈ T} b(ρ_j) ∏_{j ∉ T} (1 + a(ρ_j)) ≤ ∑_{A ⊆ Tᶜ} M₁^{|A|} M₂^{|T|} ∏_{j ∈ A} w₁(ρ_j) ∏_{j ∈ T} w₂(ρ_j)`
  integrated over `Λ^p`, with the sum over `A` grouped by `k = |A|` (binomial multiplicity).
* The comparison of the factors of `(pred3)` with the weights of Propositions 3.6 and 3.7 in the
  four ranges of `β` (`ofReal_isolatedPhi_le_of_eq_two`, …), and the bounds of `γ_{β, k}` with
  `p ≤ N` (`gammaBeta_le_of_lt_four`, `gammaBeta_four_le`, …).
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace TwoComponentCoulomb

namespace IsolatedIntegration

open AuxIntegration

/-! ### Relabelling the representatives -/

/-- The first-neighbour radius is equivariant under a relabelling `e : κ' ≃ κ`. -/
theorem nnRadius_comp_relabel {κ κ' : Type*} [Fintype κ] [Nontrivial κ] [Fintype κ']
    [Nontrivial κ'] (lam : ℝ) (z : κ → ℂ) (e : κ' ≃ κ) (j : κ') :
    nnRadius lam (z ∘ e) j = nnRadius lam z (e j) := by
  classical
  unfold nnRadius
  congr 2
  apply le_antisymm
  · refine Finset.le_inf' _ _ fun i hi => ?_
    have hne := (Finset.mem_erase.1 hi).1
    have hi' : e.symm i ∈ Finset.univ.erase j :=
      Finset.mem_erase.2 ⟨fun h => hne (by rw [← h]; simp), Finset.mem_univ _⟩
    exact (Finset.inf'_le _ hi').trans (le_of_eq (by simp))
  · refine Finset.le_inf' _ _ fun j' hj' => ?_
    have hne := (Finset.mem_erase.1 hj').1
    have hj'' : e j' ∈ Finset.univ.erase (e j) :=
      Finset.mem_erase.2 ⟨fun h => hne (e.injective h), Finset.mem_univ _⟩
    exact Finset.inf'_le (fun i => ‖z (e j) - z i‖) hj''

/-- Relabelling the coordinates of `Λ^κ` by `e : Fin p ≃ κ` preserves Lebesgue measure and the
box. -/
theorem lintegral_pi_box_comp_equiv {κ : Type*} [Fintype κ] {p : ℕ} (e : Fin p ≃ κ) (N : ℕ)
    (F : (κ → ℂ) → ℝ≥0∞) :
    ∫⁻ w in Set.univ.pi (fun _ : κ => box N), F w =
      ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), F (z ∘ e.symm) := by
  set E := MeasurableEquiv.piCongrLeft (fun _ : κ => ℂ) e with hE
  have hEapp : ∀ (z : Fin p → ℂ) (b : κ), E z b = z (e.symm b) := fun z b => by
    rw [hE, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp
  have hmp : MeasurePreserving E volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : κ => ℂ) e
  have hpre : E ⁻¹' (Set.univ.pi fun _ : κ => box N) = Set.univ.pi fun _ : Fin p => box N := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, hEapp]
    exact (e.forall_congr_left (p := fun i => z i ∈ box N)).symm
  have h := hmp.setLIntegral_comp_preimage_emb E.measurableEmbedding F
    (Set.univ.pi fun _ : κ => box N)
  rw [hpre] at h
  rw [← h]
  refine lintegral_congr fun z => ?_
  congr 1
  ext b
  exact hEapp z b

/-! ### Counting the same-sign representatives -/

/-- A set `S` of vertices invariant under the pairing `f` contains as many representatives as
non-representatives, so `2 |S ∩ R| = |S|`. -/
theorem two_mul_card_filter_ref {ι : Type*} {f : ι → ι} {R : Set ι} [DecidablePred (· ∈ R)]
    (hf2 : ∀ i, f (f i) = i) (hRf : ∀ i, i ∈ R ↔ f i ∉ R) {S : Finset ι}
    (hS : ∀ i, f i ∈ S ↔ i ∈ S) : 2 * (S.filter (· ∈ R)).card = S.card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := S) (fun i => i ∈ R)
  have h2 : (S.filter (fun i => ¬ i ∈ R)).card = (S.filter (· ∈ R)).card := by
    refine Finset.card_bij (fun i _ => f i) ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨(hS i).2 hi.1, (hRf (f i)).2 (by rw [hf2]; exact hi.2)⟩
    · intro i _ j _ h
      rw [← hf2 i, ← hf2 j, h]
    · intro j hj
      rw [Finset.mem_filter] at hj
      refine ⟨f j, ?_, hf2 j⟩
      rw [Finset.mem_filter]
      exact ⟨(hS j).2 hj.1, (hRf j).1 hj.2⟩
  omega

open scoped Classical in
/-- **Relabelling the representatives by `Fin p`** (Lebesgue measure, the box and `r̃₁` are
invariant): the same-sign representatives `R ∩ S` become a set `T ⊆ Fin p` with `|T| = q` when
`|S| = 2q`. -/
theorem exists_relabel_ref {ι : Type*} [Fintype ι] {f : ι → ι} {R : Set ι}
    [DecidablePred (· ∈ R)] [Nontrivial {i // i ∈ R}] (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) {S : Finset ι} (hS : ∀ i, f i ∈ S ↔ i ∈ S) {p q : ℕ}
    [Nontrivial (Fin p)] (hR : Fintype.card {i // i ∈ R} = p) (hSq : S.card = 2 * q) (N : ℕ)
    (lam : ℝ) :
    ∃ T : Finset (Fin p), T.card = q ∧ ∀ g h : ℝ → ℝ≥0∞,
      ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
          ∏ j : {i // i ∈ R}, (if (j : ι) ∈ S then g (nnRadius lam w j)
            else h (nnRadius lam w j)) =
        ∫⁻ z in Set.univ.pi fun _ : Fin p => box N,
          ∏ i, (if i ∈ T then g (nnRadius lam z i) else h (nnRadius lam z i)) := by
  classical
  set e : Fin p ≃ {i // i ∈ R} := (Fintype.equivFinOfCardEq hR).symm with he
  set T : Finset (Fin p) := Finset.univ.filter (fun i => ((e i : {i // i ∈ R}) : ι) ∈ S)
    with hTdef
  have hT : T.card = q := by
    have h1 := two_mul_card_filter_ref hf2 hRf hS
    have h2 : T.card = (S.filter (· ∈ R)).card := by
      refine Finset.card_bij (fun i _ => ((e i : {i // i ∈ R}) : ι)) ?_ ?_ ?_
      · intro i hi
        rw [hTdef, Finset.mem_filter] at hi
        exact Finset.mem_filter.2 ⟨hi.2, (e i).2⟩
      · intro i _ j _ h
        exact e.injective (Subtype.ext h)
      · intro x hx
        rw [Finset.mem_filter] at hx
        refine ⟨e.symm ⟨x, hx.2⟩, ?_, by simp⟩
        rw [hTdef, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by simpa using hx.1⟩
    omega
  refine ⟨T, hT, fun g h => ?_⟩
  rw [lintegral_pi_box_comp_equiv e N]
  refine lintegral_congr fun z => ?_
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [nnRadius_comp_relabel lam z e.symm (e i), e.symm_apply_apply]
  by_cases hi : ((e i : {i // i ∈ R}) : ι) ∈ S
  · have hiT : i ∈ T := by rw [hTdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩
    rw [ite_eq_left hi, ite_eq_left hiT]
  · have hiT : i ∉ T := by rw [hTdef, Finset.mem_filter]; exact fun h' => hi h'.2
    rw [ite_eq_right hi, ite_eq_right hiT]

/-! ### Expansion of the neutral product -/

/-- **Expansion of the neutral product** (source l. 1275). Let `T ⊆ Fin p` (the same-sign
representatives) and suppose `a ≤ M₁ w₁`, `b ≤ M₂ w₂` on `[λ, ∞)`. Then
`∫_{Λ^p} ∏_{j ∈ T} b(ρ_j) ∏_{j ∉ T} (1 + a(ρ_j)) ≤ ∑_{k ≤ |Tᶜ|} C(|Tᶜ|, k) M₁^k M₂^{|T|} B(k)`
whenever `B(|A|)` bounds the integral of `∏_{j ∈ A} w₁(ρ_j) ∏_{j ∈ T} w₂(ρ_j)` for every
`A ⊆ Tᶜ` (the `k = |A|` selected neutral factors). -/
theorem lintegral_prod_ite_le {p : ℕ} [Nontrivial (Fin p)] (N : ℕ) (lam : ℝ) (T : Finset (Fin p))
    {a b w₁ w₂ : ℝ → ℝ≥0∞} {M₁ M₂ : ℝ≥0∞} (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (ha : ∀ ρ, lam ≤ ρ → a ρ ≤ M₁ * w₁ ρ) (hb : ∀ ρ, lam ≤ ρ → b ρ ≤ M₂ * w₂ ρ)
    (B : ℕ → ℝ≥0∞)
    (hB : ∀ A ⊆ Tᶜ, ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
        (∏ i ∈ A, w₁ (nnRadius lam z i)) * ∏ i ∈ T, w₂ (nnRadius lam z i) ≤ B A.card) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
        ∏ i, (if i ∈ T then b (nnRadius lam z i) else 1 + a (nnRadius lam z i)) ≤
      ∑ k ∈ range (Tᶜ.card + 1), (Tᶜ.card.choose k : ℝ≥0∞) * (M₁ ^ k * M₂ ^ T.card * B k) := by
  set G : Finset (Fin p) → (Fin p → ℂ) → ℝ≥0∞ := fun A z =>
    (∏ i ∈ A, w₁ (nnRadius lam z i)) * ∏ i ∈ T, w₂ (nnRadius lam z i) with hGdef
  have hG : ∀ A, Measurable (G A) := fun A =>
    (Finset.measurable_prod _ fun i _ => hw₁.comp (measurable_nnRadius lam i)).mul
      (Finset.measurable_prod _ fun i _ => hw₂.comp (measurable_nnRadius lam i))
  have hpt : ∀ z : Fin p → ℂ,
      ∏ i, (if i ∈ T then b (nnRadius lam z i) else 1 + a (nnRadius lam z i)) ≤
        ∑ A ∈ Tᶜ.powerset, M₁ ^ A.card * M₂ ^ T.card * G A z := by
    intro z
    have hT1 : Finset.univ.filter (fun i => i ∈ T) = T := by ext i; simp
    have hT2 : Finset.univ.filter (fun i => ¬ i ∈ T) = Tᶜ := by ext i; simp
    rw [Finset.prod_ite, hT1, hT2]
    have h1 : ∏ i ∈ T, b (nnRadius lam z i) ≤ M₂ ^ T.card * ∏ i ∈ T, w₂ (nnRadius lam z i) := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod fun i _ => hb _ (le_nnRadius lam z i)
    have h2 : ∏ i ∈ Tᶜ, (1 + a (nnRadius lam z i)) ≤
        ∑ A ∈ Tᶜ.powerset, M₁ ^ A.card * ∏ i ∈ A, w₁ (nnRadius lam z i) := by
      calc ∏ i ∈ Tᶜ, (1 + a (nnRadius lam z i))
          ≤ ∏ i ∈ Tᶜ, (1 + M₁ * w₁ (nnRadius lam z i)) :=
            Finset.prod_le_prod fun i _ => by gcongr; exact ha _ (le_nnRadius lam z i)
        _ = ∑ A ∈ Tᶜ.powerset, ∏ i ∈ A, M₁ * w₁ (nnRadius lam z i) := Finset.prod_one_add _
        _ = _ := by
            refine Finset.sum_congr rfl fun A _ => ?_
            rw [Finset.prod_mul_distrib, Finset.prod_const]
    calc (∏ i ∈ T, b (nnRadius lam z i)) * ∏ i ∈ Tᶜ, (1 + a (nnRadius lam z i))
        ≤ (M₂ ^ T.card * ∏ i ∈ T, w₂ (nnRadius lam z i)) *
            ∑ A ∈ Tᶜ.powerset, M₁ ^ A.card * ∏ i ∈ A, w₁ (nnRadius lam z i) := by
          gcongr
      _ = ∑ A ∈ Tᶜ.powerset, M₁ ^ A.card * M₂ ^ T.card * G A z := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun A _ => ?_
          simp only [hGdef]
          ring
  calc ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
        ∏ i, (if i ∈ T then b (nnRadius lam z i) else 1 + a (nnRadius lam z i))
      ≤ ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
          ∑ A ∈ Tᶜ.powerset, M₁ ^ A.card * M₂ ^ T.card * G A z := lintegral_mono hpt
    _ = ∑ A ∈ Tᶜ.powerset, M₁ ^ A.card * M₂ ^ T.card *
          ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), G A z := by
        rw [lintegral_finsetSum _ fun A _ => (hG A).const_mul _]
        exact Finset.sum_congr rfl fun A _ => lintegral_const_mul _ (hG A)
    _ ≤ ∑ A ∈ Tᶜ.powerset, M₁ ^ A.card * M₂ ^ T.card * B A.card := by
        gcongr with A hA
        exact hB A (Finset.mem_powerset.1 hA)
    _ = _ := by
        rw [Finset.sum_powerset_apply_card (fun k => M₁ ^ k * M₂ ^ T.card * B k)]
        simp only [nsmul_eq_mul]

/-! ### The factors of `(pred3)` against the weights of Propositions 3.6 and 3.7 -/

section Weights

variable {lam : ℝ}

theorem isolatedPhi_of_eq_four {β : ℝ} (hβ : 2 ≤ β) (h4 : β = 4) (x : ℝ) :
    isolatedPhi β hβ lam x = (lam / x) ^ 2 * (1 + Real.log (x / lam)) := by
  subst h4
  norm_num [isolatedPhi]

theorem isolatedPhi_of_four_lt {β : ℝ} (hβ : 2 ≤ β) (h4 : 4 < β) (x : ℝ) :
    isolatedPhi β hβ lam x = (lam / x) ^ 2 := by
  have h2 : β ≠ 2 := by intro h; rw [h] at h4; norm_num at h4
  simp [isolatedPhi, h2, not_lt.2 h4.le, h4.ne']

theorem isolatedTail_of_two_lt {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) (ρ : ℝ) :
    isolatedTail β hβ lam ρ = (lam / ρ) ^ (β - 2) := by
  simp [isolatedTail, h2.ne']

theorem sourceWeight_zero_zero (β : ℝ) (lam ρ : ℝ) :
    sourceWeight β 0 0 lam ρ = ENNReal.ofReal (ρ ^ (-(β / 2))) := by
  simp [sourceWeight]

/-- `(λ/ρ)^s = λ^s ρ^{-s}`. -/
theorem div_rpow_eq_mul_rpow_neg (hlam : 0 < lam) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    (lam / ρ) ^ s = lam ^ s * ρ ^ (-s) := by
  rw [Real.div_rpow hlam.le hρ.le, Real.rpow_neg hρ.le, div_eq_mul_inv]

/-- **`β = 2`** : `C' φ_2(ρ) = (C'/ℓ)(1 + |log ρ|)` is the weight of
Proposition 3.6 with `β = 0`, `δ' = 1`, with the constant `C'/ℓ`. -/
theorem ofReal_isolatedPhi_le_of_eq_two {β : ℝ} (hβ : 2 ≤ β) (h : β = 2) {C' : ℝ} (hC' : 0 ≤ C')
    (ρ : ℝ) :
    ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ) ≤
      ENNReal.ofReal (C' / |Real.log lam|) * sourceWeight 0 0 1 lam ρ := by
  rw [isolatedPhi_of_eq_two hβ h, sourceWeight, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  simp only [neg_zero, zero_div, Real.rpow_zero, pow_zero, pow_one, one_mul]
  ring

/-- **`β = 2`** : the same-sign factor `C' ℓ^{-1} ≤ (C'/ℓ)(1 + |log ρ|)`. -/
theorem ofReal_isolatedTail_le_of_eq_two {β : ℝ} (hβ : 2 ≤ β) (h : β = 2) {C' : ℝ}
    (hC' : 0 ≤ C') (ρ : ℝ) :
    ENNReal.ofReal (C' * isolatedTail β hβ lam ρ) ≤
      ENNReal.ofReal (C' / |Real.log lam|) * sourceWeight 0 0 1 lam ρ := by
  rw [sourceWeight, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [isolatedTail, h, ite_true, neg_zero, zero_div, Real.rpow_zero, pow_zero, pow_one,
    one_mul]
  have : 0 ≤ C' / |Real.log lam| := by positivity
  rw [← div_eq_mul_inv]
  nlinarith [abs_nonneg (Real.log ρ)]

/-- **`β > 2`, the same-sign factor** (source l. 1291, 1307): `C' (λ/ρ)^{β-2}` is the weight of
Proposition 3.6 (for `2 < β < 4`, l. 1291) or of the second species of Proposition 3.7 (for
`β > 4`, l. 1307) with parameter `2(β - 2)`, with the constant `C' λ^{β-2}`. -/
theorem ofReal_isolatedTail_le_of_two_lt {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) (hlam : 0 < lam)
    {C' : ℝ} (hC' : 0 ≤ C') {ρ : ℝ} (hρ : lam ≤ ρ) :
    ENNReal.ofReal (C' * isolatedTail β hβ lam ρ) ≤
      ENNReal.ofReal (C' * lam ^ (β - 2)) * sourceWeight (2 * (β - 2)) 0 0 lam ρ := by
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  rw [sourceWeight_zero_zero, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [isolatedTail_of_two_lt hβ h2, div_rpow_eq_mul_rpow_neg hlam hρ0,
    show 2 * (β - 2) / 2 = β - 2 by ring]
  ring

/-- **`2 < β < 4`, the neutral factor** (source l. 1291): `C' φ_β(ρ) = C' (λ/ρ)^{β-2}`. -/
theorem ofReal_isolatedPhi_le_of_two_lt_of_lt_four {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β)
    (h4 : β < 4) (hlam : 0 < lam) {C' : ℝ} (hC' : 0 ≤ C') {ρ : ℝ} (hρ : lam ≤ ρ) :
    ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ) ≤
      ENNReal.ofReal (C' * lam ^ (β - 2)) * sourceWeight (2 * (β - 2)) 0 0 lam ρ := by
  have hφ : isolatedPhi β hβ lam ρ = isolatedTail β hβ lam ρ := by
    simp [isolatedPhi, isolatedTail, h2.ne', h4]
  rw [hφ]
  exact ofReal_isolatedTail_le_of_two_lt hβ h2 hlam hC' hρ

/-- **`β = 4`, the neutral factor** (source l. 1301–1302): `C' φ_4(ρ) = C' λ² ρ^{-2} (1 + log (ρ/λ))`
is the weight of Proposition 3.6 with parameter `4`, `δ = 1`, with the constant `C' λ²`. -/
theorem ofReal_isolatedPhi_le_of_eq_four {β : ℝ} (hβ : 2 ≤ β) (h4 : β = 4) (hlam : 0 < lam)
    {C' : ℝ} (hC' : 0 ≤ C') {ρ : ℝ} (hρ : lam ≤ ρ) :
    ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ) ≤
      ENNReal.ofReal (C' * lam ^ 2) * sourceWeight 4 1 0 lam ρ := by
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  rw [sourceWeight, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [isolatedPhi_of_eq_four hβ h4, pow_one, pow_zero, mul_one,
    show -((4 : ℝ) / 2) = -2 by norm_num, Real.rpow_neg hρ0.le, Real.rpow_two, div_pow]
  field_simp

/-- **`β = 4`, the same-sign factor** (source l. 1301): `C' (λ/ρ)² ≤ C' (λ/ρ)² (1 + log (ρ/λ))`,
the weight of Proposition 3.6 with parameter `4`, `δ = 1`. -/
theorem ofReal_isolatedTail_le_of_eq_four {β : ℝ} (hβ : 2 ≤ β) (h4 : β = 4) (hlam : 0 < lam)
    {C' : ℝ} (hC' : 0 ≤ C') {ρ : ℝ} (hρ : lam ≤ ρ) :
    ENNReal.ofReal (C' * isolatedTail β hβ lam ρ) ≤
      ENNReal.ofReal (C' * lam ^ 2) * sourceWeight 4 1 0 lam ρ := by
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  have hlog : 0 ≤ Real.log (ρ / lam) := Real.log_nonneg ((one_le_div hlam).2 hρ)
  rw [sourceWeight, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [isolatedTail_of_two_lt hβ (by rw [h4]; norm_num), pow_one, pow_zero, mul_one]
  rw [h4, show (4 : ℝ) - 2 = 2 by norm_num, show -((4 : ℝ) / 2) = -2 by norm_num,
    Real.rpow_neg hρ0.le, Real.rpow_two, Real.rpow_two, div_pow]
  have e : C' * (lam ^ 2 / ρ ^ 2) = C' * lam ^ 2 * ((ρ ^ 2)⁻¹ * 1) := by field_simp
  rw [e]
  gcongr
  linarith

/-- **`β > 4`, the neutral factor** (source l. 1307): `C' φ_β(ρ) = C' λ² ρ^{-2}` is the weight of
the first species of Proposition 3.7 (parameter `4`, `δ = 0`), with the constant `C' λ²`. -/
theorem ofReal_isolatedPhi_le_of_four_lt {β : ℝ} (hβ : 2 ≤ β) (h4 : 4 < β) (hlam : 0 < lam)
    {C' : ℝ} (hC' : 0 ≤ C') {ρ : ℝ} (hρ : lam ≤ ρ) :
    ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ) ≤
      ENNReal.ofReal (C' * lam ^ 2) * sourceWeight 4 0 0 lam ρ := by
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  rw [sourceWeight_zero_zero, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [isolatedPhi_of_four_lt hβ h4, show -((4 : ℝ) / 2) = -2 by norm_num, Real.rpow_neg hρ0.le, Real.rpow_two, div_pow]
  field_simp

end Weights

/-! ### The exponents `γ` with `p ≤ N` (source l. 1300, 1305, 1310–1312) -/

section Gamma

variable {lam : ℝ}

/-- The fractions `k/N ≤ k/p` for `p ≤ N` (source l. 1300, "we used `p/N ≤ 1`"). -/
theorem div_le_div_of_le_nat {k p N : ℕ} (hp : 0 < p) (hpN : p ≤ N) :
    (k : ℝ) / N ≤ (k : ℝ) / p := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg k) hP (by exact_mod_cast hpN)

/-- `ℓ = |log λ| ≤ λ^{-1}`. -/
theorem abs_log_le_inv (hlam : 0 < lam) (hl1 : lam ≤ Real.exp (-1)) :
    |Real.log lam| ≤ lam⁻¹ := by
  rw [abs_of_nonpos (by linarith [log_le_neg_one hlam hl1])]
  have h := Real.log_le_sub_one_of_pos (inv_pos.2 hlam)
  rw [Real.log_inv] at h
  linarith

/-- The cycle scale in the three subcritical regimes of the paper,
lines 1293–1299. For `β < 3` the correction is zero and `k/p ≤ 1`. -/
noncomputable def subcriticalCycleScale (β lam : ℝ) : ℝ :=
  if β < 3 then 1 else if β = 3 then |Real.log lam| else lam ^ (6 - 2 * β)

/-- The three subcritical cycle scales are positive. -/
theorem subcriticalCycleScale_pos (β : ℝ) (hlam : 0 < lam)
    (hl1 : lam ≤ Real.exp (-1)) : 0 < subcriticalCycleScale β lam := by
  have := one_le_abs_log hlam hl1
  unfold subcriticalCycleScale
  split_ifs <;> positivity

/-- Keep the three regimes `b < 1`, `b = 1`, `b > 1`, where `b = β - 2`,
through the representative integral. Only `p/N ≤ 1` is used here. -/
theorem gammaBeta_le_of_lt_four {β : ℝ} (h4 : β < 4)
    (hb : 0 ≤ 2 * (β - 2)) (hlam : 0 < lam) {k p N : ℕ} (hp : 0 < p)
    (hpN : p ≤ N) :
    gammaBeta (2 * (β - 2)) hb 0 lam k N ≤
      Real.log (max (subcriticalCycleScale β lam * ((k : ℝ) / p)) (1 ^ 2)) := by
  have hkN := div_le_div_of_le_nat (k := k) hp hpN
  by_cases h3 : β < 3
  · rw [gammaBeta_of_lt_two (by linarith)]
    exact Real.log_nonneg (le_max_of_le_right (by norm_num))
  by_cases he : β = 3
  · have hpar : 2 * (β - 2) = 2 := by rw [he]; norm_num
    simp only [gammaBeta, hpar, lt_self_iff_false, ite_false, ite_true]
    rw [subcriticalCycleScale, ite_eq_right h3, ite_eq_left he, mul_div_assoc]
    exact Real.log_le_log (lt_max_of_lt_right one_pos)
      (max_le_max (mul_le_mul_of_nonneg_left hkN (abs_nonneg _)) (by norm_num))
  · have hgt : 3 < β := lt_of_le_of_ne (not_lt.1 h3) (Ne.symm he)
    rw [gammaBeta_of_two_lt_of_lt_four (by linarith) (by linarith)]
    rw [subcriticalCycleScale, ite_eq_right h3, ite_eq_right he,
      show 2 - 2 * (β - 2) = 6 - 2 * β by ring, mul_div_assoc]
    exact Real.log_le_log (lt_max_of_lt_right one_pos)
      (max_le_max (mul_le_mul_of_nonneg_left hkN (Real.rpow_pos_of_pos hlam _).le)
        (by norm_num))

/-- The second branch after optimization is `λ² ℓ` at `β = 3` and `λ²`
for `3 < β < 4`. These are the sharper contributions of manuscript lines 1365–1367. -/
theorem subcriticalCycleScale_mul_sq {β : ℝ} (h3 : 3 ≤ β) (hlam : 0 < lam) :
    subcriticalCycleScale β lam * (lam ^ (β - 2)) ^ 2 =
      if β = 3 then lam ^ 2 * |Real.log lam| else lam ^ 2 := by
  rw [subcriticalCycleScale, ite_eq_right (not_lt.2 h3)]
  split_ifs with he
  · rw [he]
    norm_num [mul_comm]
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le, ← Real.rpow_add hlam]
    norm_num
    ring_nf
    rw [Real.rpow_two]

/-- Absorb the sharper branch contributions only after optimization.
The zero-correction regime also allows `λ^{2b} ≤ λ^b`. -/
theorem subcriticalCycleScale_mul_sq_le {β : ℝ} (h2 : 2 < β) (h4 : β < 4)
    (hlam : 0 < lam) (hl1 : lam ≤ Real.exp (-1)) :
    subcriticalCycleScale β lam * (lam ^ (β - 2)) ^ 2 ≤ lam ^ (β - 2) := by
  have hl : lam ≤ 1 := hl1.trans (by rw [Real.exp_le_one_iff]; norm_num)
  by_cases h3 : β < 3
  · rw [subcriticalCycleScale, ite_eq_left h3, one_mul, ← Real.rpow_natCast,
      ← Real.rpow_mul hlam.le]
    exact Real.rpow_le_rpow_of_exponent_ge hlam hl (by norm_num; linarith)
  · rw [subcriticalCycleScale_mul_sq (not_lt.1 h3) hlam]
    split_ifs with he
    · rw [he]
      norm_num
      calc lam ^ 2 * |Real.log lam| ≤ lam ^ 2 * lam⁻¹ :=
            mul_le_mul_of_nonneg_left (abs_log_le_inv hlam hl1) (sq_nonneg lam)
        _ = lam := by field_simp
    · rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_ge hlam hl (by linarith)

/-- **`β = 4`** (source l. 1305): for `p ≤ N`,
`γ_{4, k} = log (max (λ^{-2} k/N) ℓ^4) ≤ log (max (λ^{-2} k/p) (ℓ²)²)` (`δ = 1`). -/
theorem gammaBeta_four_le (h : 0 ≤ (4 : ℝ)) (hlam : 0 < lam) (hl1 : lam ≤ Real.exp (-1))
    {k p N : ℕ} (hp : 0 < p) (hpN : p ≤ N) :
    gammaBeta 4 h 1 lam k N ≤
      Real.log (max ((lam ^ 2)⁻¹ * ((k : ℝ) / p)) ((|Real.log lam| ^ 2) ^ 2)) := by
  rw [gammaBeta_four]
  have hkN := div_le_div_of_le_nat (k := k) hp hpN
  have hℓ : 0 < (|Real.log lam| ^ 2) ^ 2 := by
    have := one_le_abs_log hlam hl1
    positivity
  rw [show |Real.log lam| ^ (2 * (1 + 1)) = (|Real.log lam| ^ 2) ^ 2 by ring, mul_div_assoc]
  exact Real.log_le_log (lt_max_of_lt_right hℓ)
    (max_le_max (mul_le_mul_of_nonneg_left hkN (by positivity)) le_rfl)

/-- **`β > 4`, the first species** (source l. 1312, `δ = 0`): for `p ≤ N`,
`γ_{4, k} = log (max (λ^{-2} k/N) ℓ²) ≤ log (max (λ^{-2} k/p) ℓ²)`. -/
theorem gammaBeta_four_zero_le (h : 0 ≤ (4 : ℝ)) (hlam : 0 < lam) (hl1 : lam ≤ Real.exp (-1))
    {k p N : ℕ} (hp : 0 < p) (hpN : p ≤ N) :
    gammaBeta 4 h 0 lam k N ≤ Real.log (max ((lam ^ 2)⁻¹ * ((k : ℝ) / p)) (|Real.log lam| ^ 2)) := by
  rw [gammaBeta_four]
  have hkN := div_le_div_of_le_nat (k := k) hp hpN
  have hℓ : 0 < |Real.log lam| ^ 2 := by
    have := one_le_abs_log hlam hl1
    positivity
  rw [show (2 * (1 + 0) : ℕ) = 2 by norm_num, mul_div_assoc]
  exact Real.log_le_log (lt_max_of_lt_right hℓ)
    (max_le_max (mul_le_mul_of_nonneg_left hkN (by positivity)) le_rfl)

/-- **`β > 4`, the second species** (source l. 1310–1311): for `β' = 2(β - 2) > 4` and `p ≤ N`,
`γ_{β', q} = log (max (λ^{2-β'} q/N) λ^{4-β'}) ≤ log (max (λ^{2-β'} q/p) (λ^{4-β})²)`. -/
theorem gammaBeta_four_lt_le {β : ℝ} (h4 : 4 < β) (hb : 0 ≤ 2 * (β - 2)) (hlam : 0 < lam)
    {q p N : ℕ} (hp : 0 < p) (hpN : p ≤ N) :
    gammaBeta (2 * (β - 2)) hb 0 lam q N ≤
      Real.log (max (lam ^ (2 - 2 * (β - 2)) * ((q : ℝ) / p)) ((lam ^ (4 - β)) ^ 2)) := by
  rw [gammaBeta_of_four_lt (by linarith)]
  have hkN := div_le_div_of_le_nat (k := q) hp hpN
  have e : lam ^ (4 - 2 * (β - 2)) = (lam ^ (4 - β)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
    ring_nf
  rw [e, mul_div_assoc]
  exact Real.log_le_log (lt_max_of_lt_right (by positivity))
    (max_le_max (mul_le_mul_of_nonneg_left hkN (by positivity)) le_rfl)

end Gamma

end IsolatedIntegration

end TwoComponentCoulomb

end
