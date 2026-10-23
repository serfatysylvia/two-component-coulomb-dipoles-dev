/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.PartitionFunction
public import TwoComponentCoulomb.UpperBound.Isolated
public import TwoComponentCoulomb.UpperBound.UpperCellBound
import TwoComponentCoulomb.UpperBound.UpperCorollary
import TwoComponentCoulomb.Integrals.Radial

/-!
# Proposition 3.9 for `β > 2`: assembly of Steps 2--3 (ubz and eq:neutral bound)

Source: proof of Proposition 3.9, l. 1421–1532.

## Structure

The generic part, valid for any family of cell integrals, is

* `TwoComponentCoulomb.UpperCellBound.CellBoundRate` and
  `TwoComponentCoulomb.UpperCellBound.exists_card_mul_le_of_cellBound_rate`
  (`UpperBound/UpperCellBound.lean`): from the per-cell bound to (eq:quadra x3) for one graph;
* `TwoComponentCoulomb.UpperAssembly.lintegral_le_of_card_mul_le` (l. 1526): the sum over
  `K, p, p₀` and the graphs costs `3 log (N + 1)`;
* `TwoComponentCoulomb.UpperAssembly.lintegral_le_of_cellBound_rate`: the two combined, with an
  extra exponent `X`, for an arbitrary integrand whose cell integrals satisfy `CellBoundRate`.

The energy-specific part is `TwoComponentCoulomb.UpperAssembly.exists_cellBound_energy_rate`: for the
Gibbs integrand `e^{-β F_λ}`, (gred3) (`UpperBound/EnergySplit.lean`), (eq:F(1)) from Proposition 3.8
(`TwoComponentCoulomb.isolated_n_neutral_conv`, `TwoComponentCoulomb.isolated_crude`) and
(eq:F(2)) from Lemma 3.4 give `UpperCellBound.CellBoundRate`. The cases follow the isolated block: `m = 0`
(empty block), `m = 1` (direct pair integration), `m = N` (`Iᶜ = ∅`) and `2 ≤ m < N`.
For every `m ≥ 2`, unmarked pairs receive the assigned quadratic correction, including
graphs with no marked pair.

## Main results

* `TwoComponentCoulomb.UpperAssembly.exists_anchor_conv`,
  `TwoComponentCoulomb.UpperAssembly.exists_anchor_crude`: Proposition 3.8, Steps 3--4
  (eq:n neutral conv and eq:crude) for the integral over the representatives on the right side of
  `(pred3)`, for every constant `C' > 0` (used by Step 4 of Proposition 3.9, l. 1548–1553, where
  only the radial factors of prescribed pairs change): the `β > 2` forms of
  `TwoComponentCoulomb.IsolatedAssembly.refSetIntegral_conv` and `refSetIntegral_crude`.
* `TwoComponentCoulomb.UpperAssembly.numNeutralTwiceIsolated_le_card_isolatedDipoles`: marked
  neutral pairs are isolated dipoles (l. 1526–1528).
* `TwoComponentCoulomb.UpperAssembly.proposition_3_9_main_of_two_lt_rate`: **(ubz) and
  (eq:neutral bound) for `β > 2`** (l. 1346–1355), in the form of the first block of the frozen
  statement of Proposition 3.9 with its `if`s resolved for `β > 2`.

## Generic rate

`lintegral_le_of_cellBound_rate`, `isolatedRate_le_rate`, `exists_cellBound_energy_rate` and
`proposition_3_9_main_of_two_lt_rate` are stated for a rate function `ω` satisfying
`TwoComponentCoulomb.UpperRateHyp` in place of `ω_λ`; they are instantiated at `errorRate` in
`UpperBound/UpperRate.lean` (`TwoComponentCoulomb.UpperAssembly.proposition_3_9_main_of_two_lt`).
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset MeasureTheory
open scoped ENNReal

namespace UpperAssembly

open UpperCellBound

/-! ### Summation over the marked graphs (source l. 1526) -/

/-- If `|D| · F γ ≤ B` for every `γ ∈ D`, then `∑_{γ ∈ D} F γ ≤ B` (the passage from the cell
integrals to `I(K, p, p₀)`, the maximum over `D`). -/
theorem sum_le_of_card_mul_le {α : Type*} (D : Finset α) (F : α → ℝ≥0∞) (B : ℝ≥0∞)
    (h : ∀ γ ∈ D, (D.card : ℝ≥0∞) * F γ ≤ B) : ∑ γ ∈ D, F γ ≤ B := by
  rcases D.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨γ₀, hγ₀, hsup⟩ := Finset.exists_mem_eq_sup D hne F
  calc ∑ γ ∈ D, F γ ≤ D.card • D.sup F :=
        Finset.sum_le_card_nsmul _ _ _ fun γ hγ => Finset.le_sup hγ
    _ = (D.card : ℝ≥0∞) * F γ₀ := by rw [nsmul_eq_mul, hsup]
    _ ≤ B := h γ₀ hγ₀

/-- **Summation over `K, p, p₀`** (source l. 1526, "Summing over `K, p, p̂₀` costs at most
`3 log (N + 1)`"): if for every marked graph `γ = (φ, T) ∈ D_{2N,K,p,p₀}` the cell integral over
`Λ^{2N} ∩ A ∩ {γ_{2N} = γ}` satisfies `|D_{2N,K,p,p₀}| · ∫ F ≤ B`, then
`∫_{Λ^{2N} ∩ A} F ≤ (N + 1)³ B`. -/
theorem lintegral_le_of_card_mul_le {N : ℕ} (hN : 2 ≤ N) (A : Set (Fin N ⊕ Fin N → ℂ))
    (F : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) (B : ℝ≥0∞)
    (h : ∀ (K p p₀ : ℕ) (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (T : Finset (Fin N ⊕ Fin N)),
      (φ, T) ∈ markedGraphs hN K p p₀ →
        ((markedGraphs hN K p p₀).card : ℝ≥0∞) *
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A ∩ markedCell hN φ T, F Z ≤
            B) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ A, F Z ≤
      ((N : ℝ≥0∞) + 1) ^ 3 * B := by
  rw [lintegral_eq_sum_markedCell hN A F]
  calc _ ≤ ∑ K ∈ range (N + 1), ∑ p ∈ range (N + 1), ∑ p₀ ∈ range (N + 1), B := by
        gcongr with K _ p _ p₀ _
        exact sum_le_of_card_mul_le _ _ B fun γ hγ => h K p p₀ γ.1 γ.2 hγ
    _ = _ := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

/-- `(N + 1)³ e^t = e^{t + 3 log (N + 1)}`. -/
theorem natCast_add_one_pow_mul_ofReal_exp (N : ℕ) (t : ℝ) :
    ((N : ℝ≥0∞) + 1) ^ 3 * ENNReal.ofReal (Real.exp t) =
      ENNReal.ofReal (Real.exp (t + 3 * Real.log (N + 1))) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm,
    show 3 * Real.log ((N : ℝ) + 1) = Real.log (((N : ℝ) + 1) ^ 3) by rw [Real.log_pow]; norm_num,
    Real.exp_log (by positivity), ENNReal.ofReal_pow hN.le, ENNReal.ofReal_add (by positivity)
      zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]

/-- **The summed bound for an arbitrary integrand, generic rate** (source l. 1524–1532): for a
rate `ω` satisfying `UpperRateHyp` in place of `ω_λ` and cell integrals satisfying `CellBoundRate`,
the per-graph bound `exists_card_mul_le_of_cellBound_rate` summed by `lintegral_le_of_card_mul_le`.
The constants depend only on `β, ω, A, c, C_b`. -/
theorem lintegral_le_of_cellBound_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) (hω : UpperRateHyp β hβ ω)
    (A c Cb : ℝ) (hc : 0 < c) (hCb : 0 ≤ Cb) :
    ∃ c' C' lam₀ : ℝ, 0 < c' ∧ 0 < C' ∧ 0 < lam₀ ∧ lam₀ ≤ Real.exp (-1) ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam < lam₀ →
      ∀ (E : Set (Fin N ⊕ Fin N → ℂ)) (F : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) (X : ℝ) (p₁ : ℕ),
      p₁ ≤ N →
      (∀ (K p p₀ : ℕ) (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (T : Finset (Fin N ⊕ Fin N)),
        (φ, T) ∈ markedGraphs hN K p p₀ →
          CellBoundRate β hβ ω A c Cb N K p p₀ lam X
            (∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T,
              F Z) ∧
          (p₁ < p₀ →
            ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T,
              F Z = 0)) →
      ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E, F Z ≤
        ENNReal.ofReal (Real.exp (2 * N * Real.log N
          + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1)
          - c' * ((N : ℝ) - p₁) ^ 2 / N + C' * N * ω lam
          + (C' + 3) * Real.log (N + 1) + X)) := by
  obtain ⟨c', C', lam₀, hc', hC', hlam₀, hlam₀1, hgraph⟩ :=
    exists_card_mul_le_of_cellBound_rate hβ ω hω A c Cb hc hCb
  refine ⟨c', C', lam₀, hc', hC', hlam₀, hlam₀1, ?_⟩
  intro N hN lam hlam hlamlt E F X p₁ hp₁ hcell
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set t : ℝ := 2 * N * Real.log N
    + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1)
    - c' * ((N : ℝ) - p₁) ^ 2 / N + C' * N * ω lam
    + C' * Real.log (N + 1) + X with ht
  refine (lintegral_le_of_card_mul_le hN E F (ENNReal.ofReal (Real.exp t)) ?_).trans
    (le_of_eq ?_)
  · intro K p p₀ φ T hγ
    obtain ⟨hcb, hzero⟩ := hcell K p p₀ φ T hγ
    by_cases hp₀ : p₁ < p₀
    · rw [hzero hp₀, mul_zero]
      exact zero_le
    · replace hp₀ := not_lt.1 hp₀
      refine (hgraph N hN K p p₀ lam hlam hlamlt ⟨_, hγ⟩ X _ hcb).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
      have h1 : (p₀ : ℝ) ≤ p₁ := by exact_mod_cast hp₀
      have h2 : (p₁ : ℝ) ≤ N := by exact_mod_cast hp₁
      have h3 : ((N : ℝ) - p₁) ^ 2 ≤ ((N : ℝ) - p₀) ^ 2 :=
        pow_le_pow_left₀ (sub_nonneg.2 h2) (sub_le_sub_left h1 _) 2
      have h4 : c' * ((N : ℝ) - p₁) ^ 2 / N ≤ c' * ((N : ℝ) - p₀) ^ 2 / N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hc'.le) hN0.le
      rw [ht]
      linarith
  · rw [natCast_add_one_pow_mul_ofReal_exp]
    congr 2
    rw [ht]
    ring

/-! ### Marked neutral pairs are isolated dipoles (source l. 1526–1528) -/

/-- The number `p₀` of marked neutral pairs is at most the number of isolated dipoles. -/
theorem numNeutralTwiceIsolated_le_card_isolatedDipoles {N : ℕ} (hN : 2 ≤ N)
    (Z : Fin N ⊕ Fin N → ℂ) : numNeutralTwiceIsolated hN Z ≤ (isolatedDipoles Z).card := by
  classical
  unfold numNeutralTwiceIsolated neutralTwiceIsolatedCycles isolatedDipoles
  refine card_le_card (image_subset_image fun i hi => ?_)
  rw [mem_filter]
  exact ⟨mem_univ _, ((mem_neutralTwiceIsolatedSet hN Z).1 hi).2⟩

/-! ### Proposition 3.8, Steps 3--4, for the integral over the representatives

Step 4 of Proposition 3.9 (l. 1548–1553) changes the radial factor of a prescribed long pair and
keeps the same integral over the representatives (the bounds (eq:representative-bound) "apply
uniformly to every prescribed set of long pairs"). We therefore record Steps 3--4 of
Proposition 3.8 (source l. 1269–1330) for the right side of `(pred3)` itself: the integral
`W = ∫_{Λ^R} ∏_{j ∈ R} (1_{j ∈ S} C' τ_β(ρ_j) + 1_{j ∉ S} (1 + C' φ_β(ρ_j)))` over the
representatives, for every constant `C' > 0`. These are the bounds
`TwoComponentCoulomb.IsolatedAssembly.refSetIntegral_conv` and
`TwoComponentCoulomb.IsolatedAssembly.refSetIntegral_crude` (`UpperBound/Isolated.lean`), from which
Proposition 3.8 itself is derived, with their `if`s resolved for `β > 2`. -/

section Anchor

open IsolatedAssembly

open scoped Classical in
/-- **(eq:n neutral conv) for the representative integral**, `β > 2` (source l. 1188–1189, 1269–1330): for every `C' > 0` and `C₀` there are `C_β, c_β > 0` such that for every set `R` of
representatives (`|R| = p`, `2 ≤ p ≤ N ≤ 2p`) of a fixed-point-free involution `f`, every
`f`-invariant `S` with `|S| = 2(p - p₀)` and `0 < λ ≤ e⁻¹`,
`e^{entropy} (𝒵_β λ^{2-β})^p W ≤ exp (p (log N + (2-β) log λ + log 𝒵_β) - c_β p ((p-p₀)/p)²
  + C_β p r_β(λ) + C_β log (N + 1))`,
where `W` is the integral over the representatives of the right side of `(pred3)` with the constant
`C'`, and `r_β(λ)` is `λ^{β-2}`, `λ² ℓ²`, `λ² ℓ` for `2 < β < 4`, `β = 4`, `β > 4`. -/
theorem exists_anchor_conv {β : ℝ} (hβ : 2 < β) {C' : ℝ} (hC' : 0 < C') (C₀ : ℝ) :
    ∃ Cβ cβ : ℝ, 0 < Cβ ∧ 0 < cβ ∧ ∀ (ι : Type) [Fintype ι] (f : ι → ι) (R : Set ι)
      [DecidablePred (· ∈ R)] [Nontrivial {i // i ∈ R}], (∀ i, f (f i) = i) →
      (∀ i, i ∈ R ↔ f i ∉ R) → ∀ (S : Finset ι), (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N p p₀ : ℕ),
      Fintype.card {i // i ∈ R} = p → 2 ≤ p → p ≤ N → (N : ℝ) ≤ 2 * p → p₀ ≤ p →
      S.card = 2 * (p - p₀) → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
            - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀))) *
          (ENNReal.ofReal (dipoleConstant β hβ.le * isolatedScale β hβ.le lam) ^ p *
            ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
              ∏ j : {i // i ∈ R}, ENNReal.ofReal (if (j : ι) ∈ S then
                C' * isolatedTail β hβ.le lam (nnRadius lam w j)
                else 1 + C' * isolatedPhi β hβ.le lam (nnRadius lam w j))) ≤
        ENNReal.ofReal (Real.exp (p * (Real.log N + (2 - β) * Real.log lam
            + Real.log (dipoleConstant β hβ.le)) - cβ * p * (((p : ℝ) - p₀) / p) ^ 2
          + Cβ * p * (if β < 4 then lam ^ (β - 2) else if β = 4 then
              lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|)
          + Cβ * Real.log (N + 1))) := by
  obtain ⟨Cβ, cβ, hCβ, hcβ, h⟩ := refSetIntegral_conv.{0} hβ.le hC' C₀
  refine ⟨Cβ, cβ, hCβ, hcβ, fun ι _ f R _ _ hf2 hRf S hS N p p₀ hR hp2 hpN hN hp₀ hSq lam hlam
    hl1 => ?_⟩
  have h' := h ι f R hf2 hRf S hS N p p₀ hR hp2 hpN hN hp₀ hSq lam hlam hl1
  rwa [ite_eq_left hβ, ite_eq_right hβ.ne', ite_eq_right hβ.ne', add_zero] at h'

open scoped Classical in
/-- **(eq:crude) for the representative integral**, `β > 2` :
for every `C' > 0` and `C₀` there is `C_β > 0` such that for every set `R` of `p ≤ N`
representatives, every `S` and `0 < λ ≤ e⁻¹`,
`e^{entropy} (𝒵_β λ^{2-β})^p W ≤ exp (p (log N + (2-β) log λ) + C_β N)`, `W` the integral over the
representatives of the right side of `(pred3)` with the constant `C'`. -/
theorem exists_anchor_crude {β : ℝ} (hβ : 2 < β) {C' : ℝ} (hC' : 0 < C') (C₀ : ℝ) :
    ∃ Cβ : ℝ, 0 < Cβ ∧ ∀ (ι : Type) [Fintype ι] (R : Set ι) [DecidablePred (· ∈ R)]
      [Nontrivial {i // i ∈ R}] (S : Finset ι) (N p p₀ : ℕ),
      Fintype.card {i // i ∈ R} = p → p ≤ N → p₀ ≤ p → ∀ lam : ℝ, 0 < lam →
      lam ≤ Real.exp (-1) →
        ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
            - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀))) *
          (ENNReal.ofReal (dipoleConstant β hβ.le * isolatedScale β hβ.le lam) ^ p *
            ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
              ∏ j : {i // i ∈ R}, ENNReal.ofReal (if (j : ι) ∈ S then
                C' * isolatedTail β hβ.le lam (nnRadius lam w j)
                else 1 + C' * isolatedPhi β hβ.le lam (nnRadius lam w j))) ≤
        ENNReal.ofReal (Real.exp (p * (Real.log N + (2 - β) * Real.log lam) + Cβ * N)) := by
  obtain ⟨Cβ, hCβ, h⟩ := refSetIntegral_crude.{0} hβ.le hC' C₀
  refine ⟨Cβ, hCβ, fun ι _ R _ _ S N p p₀ hR hpN hp₀ lam hlam hl1 => ?_⟩
  have h' := h ι R S N p p₀ hR hpN hp₀ lam hlam hl1
  rwa [ite_eq_left hβ, ite_eq_right hβ.ne', add_zero] at h'

end Anchor

/-! ### The per-cell bound for the Gibbs integrand (source l. 1421–1503) -/

section Energy

variable {N : ℕ}

/-- The two sign conventions of the Boltzmann factor agree. -/
theorem lintegral_ofReal_exp_neg_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (β : ℝ) (E : α → ℝ) :
    ∫⁻ x in s, ENNReal.ofReal (Real.exp (-β * E x)) ∂μ =
      ∫⁻ x in s, ENNReal.ofReal (Real.exp (-(β * E x))) ∂μ := by
  simp_rw [neg_mul]

/-- The error rate of Proposition 3.8 for `β > 2` is nonnegative and at most `ω(λ)`, for a rate
`ω` satisfying `UpperRateHyp` (source l. 1183–1189, `0 < λ ≤ e⁻¹`). -/
theorem isolatedRate_le_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) (hω : UpperRateHyp β hβ ω)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ Real.exp (-1)) :
    0 ≤ (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
        else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|) ∧
      (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
        else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|) ≤
        ω lam := by
  refine ⟨IsolatedAssembly.rate_nonneg β hlam.le, ?_⟩
  rw [ite_eq_right hβ.ne']
  exact hω.isolated_le lam hlam hlam1

/-- `|I'| = 2(p - p₀)` for the set `I'` of the marked same-sign vertices in `Fin N ⊕ Fin N`. -/
theorem card_markedSameSign (hN : 2 ≤ N) (Z : Fin N ⊕ Fin N → ℂ) :
    (markedSameSign (nearestNeighbor Z) (twiceIsolatedSet hN Z)).card =
      2 * (numTwiceIsolated hN Z - numNeutralTwiceIsolated hN Z) := by
  classical
  rw [← card_markedSameSignIn (hN := hN) rfl rfl]
  unfold markedSameSignIn
  rw [card_subtype, filter_true_of_mem fun x hx =>
    (isolatedPairSet_eq_pairVerts Z) ▸ twiceIsolatedSet_subset_isolatedPairSet hN Z
      (mem_markedSameSign.1 hx).1]

/-- Internal cell argument for an energy above the Corollary 2.3 expression. It uses
the separation (gred3), with direct integration when `m ≤ 1` and assigned quadratic
corrections whenever `m ≥ 2`, including graphs with no marked pair. -/
theorem exists_cellBound_of_corollary_lower_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ)
    (hω : UpperRateHyp β hβ ω) (Cc : ℝ) (hCc0 : 0 < Cc)
    (F : ∀ (N : ℕ), 2 ≤ N → ℝ → (Fin N ⊕ Fin N → ℂ) → ℝ)
    (hF : ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam →
      ∀ Z, (∀ i, Z i ∈ box N) → IsGeneric Z → corollary23Bound hN Cc lam Z ≤ F N hN lam Z) :
    ∃ A c Cb : ℝ, 0 < c ∧ 0 ≤ Cb ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam ≤ Real.exp (-1) →
      ∀ (K p p₀ : ℕ) (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (T : Finset (Fin N ⊕ Fin N)),
        (φ, T) ∈ markedGraphs hN K p p₀ → ∀ E : Set (Fin N ⊕ Fin N → ℂ),
        CellBoundRate β hβ ω A c Cb N K p p₀ lam 0
          (∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T,
            ENNReal.ofReal (Real.exp (-β * F N hN lam Z))) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hconvH⟩ := isolated_n_neutral_conv.{0} hβ.le hCc0.le 60
  obtain ⟨C₂, hC₂, hcrudeH⟩ := isolated_crude.{0} hβ.le hCc0.le 60
  obtain ⟨C₄, hF2⟩ := exists_lintegral_nnEnergy_le hβ
  set L := Real.log (dipoleConstant β hβ.le) with hL
  refine ⟨β * Cc + C₄, c₁, C₁ + C₂ + |L|, hc₁, by positivity, ?_⟩
  intro N hN lam hlam hlam1 K p p₀ φ T hγ E
  obtain ⟨Z₀, -, hgen, hφ, hT, hK, hp, hp₀⟩ := mem_markedGraphs.1 hγ
  subst hφ hT hK
  set m := numIsolatedPairs Z₀ with hm
  have hmK : m ≤ numComponents Z₀ := numIsolatedPairs_le_numComponents Z₀
  have hKN : numComponents Z₀ ≤ N := numComponents_le Z₀
  have hpm : p ≤ m := hp ▸ numTwiceIsolated_le_numIsolatedPairs
  have hp₀p : p₀ ≤ p := hp ▸ hp₀ ▸ numNeutralTwiceIsolated_le_numTwiceIsolated
  have hNpos : 0 < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨hr0, hr⟩ := isolatedRate_le_rate hβ ω hω hlam hlam1
  have hω0 : 0 ≤ ω lam := hr0.trans hr
  have hlogN : 0 ≤ Real.log (N + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  have hNω : 0 ≤ (N : ℝ) * ω lam := mul_nonneg hN0.le hω0
  have hCb : 0 ≤ C₁ + C₂ + |L| := by positivity
  obtain ⟨hF2c, hF2f⟩ := hF2 N Z₀ (nearestNeighbor Z₀) hNpos rfl lam hlam hlam1
  have hnt : Nontrivial (Fin N ⊕ Fin N) :=
    ⟨⟨Sum.inl ⟨0, hNpos⟩, Sum.inr ⟨0, hNpos⟩, Sum.inl_ne_inr⟩⟩
  by_cases hmSmall : m ≤ 1
  · have hm1 : m ≤ 1 := hmSmall
    have hT0 := twiceIsolatedSet_eq_empty_of_numIsolatedPairs_le_one hN (Z := Z₀) hm1
    have hp0 : p = 0 := by
      have h := card_twiceIsolatedSet (hN := hN) (Z := Z₀)
      rw [hT0, hp] at h
      simp at h
      omega
    have hp₀0 : p₀ = 0 := by omega
    by_cases hm0 : m = 0
    · -- `I = ∅`: only the complementary block remains.
      rw [hT0] at hγ ⊢
      have hcell := UpperCorollary.lintegral_markedCell_le_full_of_empty hN (F N hN lam)
        (hF N hN lam hlam) hβ0 hγ E
      refine Or.inl (hcell.trans ((mul_le_mul_right hF2f _).trans ?_))
      rw [ofReal_exp_mul_ofReal_exp]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have e1 : (p : ℝ) = 0 := by exact_mod_cast hp0
      have e2 : (p₀ : ℝ) = 0 := by exact_mod_cast hp₀0
      rw [e1, e2]
      have h1 : 0 ≤ (C₁ + C₂ + |L|) * N * ω lam := by
        rw [mul_assoc]; exact mul_nonneg hCb hNω
      have h2 : 0 ≤ (C₁ + C₂ + |L|) * Real.log (N + 1) := mul_nonneg hCb hlogN
      have h3 : c₁ * (0 : ℝ) ^ 2 / N = 0 := by simp
      simp only [mul_zero, Real.log_zero, sub_self]
      rw [← hL]
      linarith
    · -- `m = 1`: separate the pair before integrating its displacement.
      have hmEq : m = 1 := by omega
      have hcardI : Fintype.card {i // i ∈ pairVerts (nearestNeighbor Z₀)} = 2 := by
        rw [card_pairVerts_subtype rfl, show numIsolatedPairs Z₀ = 1 from hmEq]
      have hcardIc : Fintype.card {i // i ∉ pairVerts (nearestNeighbor Z₀)} = 2 * (N - 1) := by
        rw [card_compl_pairVerts_subtype rfl, show numIsolatedPairs Z₀ = 1 from hmEq]
      have : Nontrivial {i // i ∈ pairVerts (nearestNeighbor Z₀)} :=
        Fintype.one_lt_card_iff_nontrivial.1 (by omega)
      have : Nontrivial {i // i ∉ pairVerts (nearestNeighbor Z₀)} :=
        Fintype.one_lt_card_iff_nontrivial.1 (by omega)
      rw [hT0] at hγ ⊢
      have hcell := UpperCorollary.lintegral_markedCell_le_mul_of_empty hN (F N hN lam)
        (hF N hN lam hlam) hβ0 hγ E
      have hpair := lintegral_nnEnergy_pair_le hβ
        (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) hcardI
        (pairRestrict_ne_of_nearestNeighbor rfl)
        (pairRestrict_pairRestrict (nearestNeighbor Z₀)) hNpos hlam hlam1
      have hpair' : ENNReal.ofReal (Real.exp 0) *
          (∫⁻ x in (Set.univ.pi fun _ : {i // i ∈ pairVerts (nearestNeighbor Z₀)} => box N) ∩
            {x | nnMap (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) x =
              pairRestrict (nearestNeighbor Z₀)},
            ENNReal.ofReal (Real.exp (-β * nnEnergy
              (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) lam x))) ≤
          ENNReal.ofReal (Real.exp (Real.log N + (2 - β) * Real.log lam +
            Real.log (dipoleConstant β hβ.le))) := by
        simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using hpair
      refine Or.inl (le_ofReal_exp_of_le_mul hcell hpair' (@hF2c inferInstance) ?_)
      have h1 : 0 ≤ (C₁ + C₂ + |L|) * N * ω lam := by positivity
      have h2 : 0 ≤ (C₁ + C₂ + |L|) * Real.log (N + 1) := by positivity
      simp only [hp0, hp₀0, Nat.cast_zero, sub_zero, Real.log_zero, mul_zero,
        zero_add, zero_pow (by norm_num : 2 ≠ 0), zero_div]
      rw [show numIsolatedPairs Z₀ = 1 from hmEq, ← hL]
      push_cast
      nlinarith only [h1, h2]
  have hm2 : 2 ≤ m := by omega
  have hmN : m ≤ N := hmK.trans hKN
  have hcardI : Fintype.card {i // i ∈ pairVerts (nearestNeighbor Z₀)} = 2 * m :=
    card_pairVerts_subtype rfl
  have h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts (nearestNeighbor Z₀)} := by omega
  have : Nontrivial {i // i ∈ pairVerts (nearestNeighbor Z₀)} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hScard : (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)).card =
      2 * (m - (p₀ + m - p)) := by
    rw [card_markedSameSignIn (hN := hN) rfl rfl, hp, hp₀]
    congr 1
    omega
  have hSinv : ∀ i, pairRestrict (nearestNeighbor Z₀) i ∈
      markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) ↔
        i ∈ markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) := by
    intro i
    refine ⟨fun h => ?_, fun h => pairRestrict_mem_markedSameSignIn rfl rfl h⟩
    have := pairRestrict_mem_markedSameSignIn (hN := hN) rfl rfl h
    rwa [pairRestrict_pairRestrict] at this
  have hp₀' : p₀ + m - p + p = p₀ + m := by omega
  by_cases hmN' : m = N
  · -- `Iᶜ = ∅`: Proposition 3.8 on all points
    have hKeq : numComponents Z₀ = N := by omega
    have h3' : 3 ≤ Fintype.card (Fin N ⊕ Fin N) := by simp; omega
    have hcell := UpperCorollary.lintegral_markedCell_le_full hCc0.le hN h3' (F N hN lam)
      (hF N hN lam hlam) hβ0 hγ E
    rw [lintegral_ofReal_exp_neg_mul volume _ β (pairAssignedEnergy h3' (sumKey N) lam Cc
      (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)))] at hcell
    have huniv : pairVerts (nearestNeighbor Z₀) = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      have hc := card_isolatedPairSet (Z := Z₀)
      rw [isolatedPairSet_eq_pairVerts] at hc
      rw [hc]
      simp
      omega
    have hφ2 : ∀ i, nearestNeighbor Z₀ (nearestNeighbor Z₀ i) = i := fun i =>
      (mem_pairVerts.1 (huniv ▸ Finset.mem_univ i)).1
    have hφ0 : ∀ i, nearestNeighbor Z₀ i ≠ i := nearestNeighbor_ne Z₀
    have hSinv' : ∀ i, nearestNeighbor Z₀ i ∈
        markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) ↔
          i ∈ markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) := by
      intro i
      simp only [mem_markedSameSign]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' := nearestNeighbor_mem_twiceIsolatedSet h1
        rw [hφ2] at h1' h2
        exact ⟨h1', by rwa [mul_comm] at h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨nearestNeighbor_mem_twiceIsolatedSet h1, ?_⟩
        rwa [hφ2, mul_comm]
    have hScard' : (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)).card =
        2 * (N - (p₀ + N - p)) := by
      rw [card_markedSameSign hN Z₀, hp, hp₀]
      congr 1
      omega
    have hcard2 : Fintype.card (Fin N ⊕ Fin N) = 2 * N := by simp [two_mul]
    have h := hconvH (Fin N ⊕ Fin N) (sumKey N) (nearestNeighbor Z₀) hφ2 hφ0 h3'
      (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) hSinv' N N (p₀ + N - p)
      hcard2 (by omega) le_rfl (by linarith) (by omega) hScard' lam hlam hlam1
    have hF1 := entropy_mul_le_main_rate hβ ω (X := 0) hc₁.le hC₁.le (N := N) (m := N) (p := p)
      (p₀ := p₀) (p₀' := p₀ + N - p) hNpos le_rfl hp₀p (hmN' ▸ hpm) (by omega) hr0 hr
      (h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq (by
        rw [ite_eq_left hβ, ite_eq_right hβ.ne']
        ring)))))
    refine Or.inl (le_ofReal_exp_of_le_mul_one hcell hF1 ?_)
    rw [hKeq]
    have h1 : C₁ * N * ω lam ≤ (C₁ + C₂ + |L|) * N * ω lam := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) hNω
    have h2 : C₁ * Real.log (N + 1) ≤ (C₁ + C₂ + |L|) * Real.log (N + 1) :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) hlogN
    linarith
  -- `m < N`: the separation (gred3)
  have hcardIc : Fintype.card {i // i ∉ pairVerts (nearestNeighbor Z₀)} = 2 * (N - m) :=
    card_compl_pairVerts_subtype rfl
  have : Nontrivial {i // i ∉ pairVerts (nearestNeighbor Z₀)} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hcell := UpperCorollary.lintegral_markedCell_le_mul hCc0.le hN (F N hN lam)
    (hF N hN lam hlam) hβ0 hγ E h3
  rw [lintegral_ofReal_exp_neg_mul volume _ β
    (pairAssignedEnergy h3 (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) lam Cc
      (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)))] at hcell
  have hY₂ := @hF2c inferInstance
  have hf2 := pairRestrict_pairRestrict (nearestNeighbor Z₀)
  have hf0 := pairRestrict_ne_of_nearestNeighbor (Z := Z₀) rfl
  by_cases hNm : (N : ℝ) ≤ 2 * m
  · have h := hconvH {i // i ∈ pairVerts (nearestNeighbor Z₀)}
      (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) (pairRestrict (nearestNeighbor Z₀))
      hf2 hf0 h3 (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) hSinv N m
      (p₀ + m - p) hcardI hm2 hmN hNm (by omega) hScard lam hlam hlam1
    have hF1 := entropy_mul_le_main_rate hβ ω (X := 0) hc₁.le hC₁.le (N := N) (m := m) (p := p)
      (p₀ := p₀) (p₀' := p₀ + m - p) (by omega) hmN hp₀p hpm hp₀' hr0 hr
      (h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq (by
        rw [ite_eq_left hβ, ite_eq_right hβ.ne']
        ring)))))
    refine Or.inl (le_ofReal_exp_of_le_mul hcell hF1 hY₂ ?_)
    have h1 : C₁ * N * ω lam ≤ (C₁ + C₂ + |L|) * N * ω lam := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) hNω
    have h2 : C₁ * Real.log (N + 1) ≤ (C₁ + C₂ + |L|) * Real.log (N + 1) :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) hlogN
    linarith
  · replace hNm := not_le.1 hNm
    have h := hcrudeH {i // i ∈ pairVerts (nearestNeighbor Z₀)}
      (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) (pairRestrict (nearestNeighbor Z₀))
      hf2 hf0 h3 (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) hSinv N m
      (p₀ + m - p) hcardI hm2 hmN (by omega) lam hlam hlam1
    have hF1 := entropy_mul_le_crude (m := m) (p := p) (p₀ := p₀) (p₀' := p₀ + m - p) hp₀p hpm hp₀' h
    have hpN : (p : ℝ) < N / 2 := by
      have : (p : ℝ) ≤ m := by exact_mod_cast hpm
      linarith
    refine Or.inr ⟨hpN, le_ofReal_exp_of_le_mul hcell hF1 hY₂ ?_⟩
    rw [ite_eq_left hβ, ite_eq_right hβ.ne']
    have hmN'' : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have h1 : -((m : ℝ) * L) ≤ |L| * N := by
      have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have e1 := mul_le_mul_of_nonneg_left (neg_le_abs L) h0
      have e2 := mul_le_mul_of_nonneg_left hmN'' (abs_nonneg L)
      linarith only [e1, e2]
    have hmr : (m : ℝ) = numIsolatedPairs Z₀ := rfl
    rw [← hL, ← hmr]
    have h2 := mul_pos hC₁ hN0
    linarith

/-- The Gibbs instance of the cell argument above. -/
theorem exists_cellBound_energy_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ)
    (hω : UpperRateHyp β hβ ω) :
    ∃ A c Cb : ℝ, 0 < c ∧ 0 ≤ Cb ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam ≤ Real.exp (-1) →
      ∀ (K p p₀ : ℕ) (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (T : Finset (Fin N ⊕ Fin N)),
        (φ, T) ∈ markedGraphs hN K p p₀ → ∀ E : Set (Fin N ⊕ Fin N → ℂ),
        CellBoundRate β hβ ω A c Cb N K p p₀ lam 0
          (∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T,
            ENNReal.ofReal (Real.exp (-β * energy lam Z))) := by
  obtain ⟨Cc, hCc0, hCc⟩ := exists_corollary23Holds
  exact exists_cellBound_of_corollary_lower_rate hβ ω hω Cc hCc0
    (fun _ _ lam Z => energy lam Z) hCc

end Energy

/-! ### (ubz) and (eq:neutral bound) for `β > 2` -/

section Main

variable {N : ℕ}

/-- On the cell of a graph with `p₀` marked neutral pairs, the event `{|I^dip| = 2p₁}` is empty when
`p₁ < p₀` (marked neutral pairs are isolated dipoles, source l. 1526–1528). -/
theorem lintegral_markedCell_isolatedDipoles_eq_zero (hN : 2 ≤ N) {K p p₀ p₁ : ℕ}
    {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {T : Finset (Fin N ⊕ Fin N)}
    (hγ : (φ, T) ∈ markedGraphs hN K p p₀) (hp : p₁ < p₀) (F : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | (isolatedDipoles Z).card = p₁} ∩
        markedCell hN φ T, F Z = 0 := by
  have hempty : (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
      {Z | (isolatedDipoles Z).card = p₁} ∩ markedCell hN φ T = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun Z hZ => ?_
    have h1 := numNeutralTwiceIsolated_eq_of_mem_markedCell hγ hZ.2
    have h2 := numNeutralTwiceIsolated_le_card_isolatedDipoles hN Z
    have h3 : (isolatedDipoles Z).card = p₁ := hZ.1.2
    omega
  rw [hempty, Measure.restrict_empty, lintegral_zero_measure]

/-- **(ubz) and (eq:neutral bound) for `β > 2`, generic rate** (`prop:upper bound`, source
l. 1340–1355, proof l. 1367–1532), for a rate `ω` satisfying `UpperRateHyp` in place of `ω_λ`;
the constants and the threshold depend only on `β` and `ω`. Instantiated at `errorRate` in
`proposition_3_9_main_of_two_lt` (`UpperBound/UpperRate.lean`). -/
theorem proposition_3_9_main_of_two_lt_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ)
    (hω : UpperRateHyp β hβ ω) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          partitionFunction N β lam
              ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1
                  + C * ω lam)
                + C * Real.log (N + 1))) ∧
          ∀ p₀ : ℕ, p₀ ≤ N →
            ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
                {Z | (isolatedDipoles Z).card = p₀},
                ENNReal.ofReal (Real.exp (-β * energy lam Z))
              ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam)
                + N * (Real.log (dipoleConstant β hβ.le) - 1)
                - c * N * (((p₀ : ℝ) - N) / N) ^ 2
                + C * N * ω lam + C * Real.log (N + 1))) := by
  obtain ⟨A, c, Cb, hc, hCb, hcell⟩ := exists_cellBound_energy_rate hβ ω hω
  obtain ⟨c', C', lam₀, hc', hC', hlam₀, hlam₀1, hsum⟩ :=
    lintegral_le_of_cellBound_rate hβ ω hω A c Cb hc hCb
  refine ⟨lam₀, hlam₀, C' + 3, c', by positivity, hc', fun N hN lam hlam hlamlt =>
    ⟨?_, fun p₁ hp₁ => ?_⟩⟩
  · have hlam1 : lam ≤ Real.exp (-1) := hlamlt.le.trans hlam₀1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h := hsum N hN lam hlam hlamlt Set.univ
      (fun Z => ENNReal.ofReal (Real.exp (-β * energy lam Z))) 0 N le_rfl
      (fun K p p₀ φ T hγ => ⟨hcell N hN lam hlam hlam1 K p p₀ φ T hγ Set.univ, fun hlt => by
        obtain ⟨h1, h2, h3, -⟩ := constraints_of_nonempty ⟨_, hγ⟩
        omega⟩)
    unfold partitionFunction
    rw [← Set.inter_univ (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N)]
    refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have hω0 : 0 ≤ ω lam := hω.nonneg lam hlam
    have h0 : c' * ((N : ℝ) - N) ^ 2 / N = 0 := by simp
    have h1 := mul_nonneg hN0.le hω0
    linarith only [h0, h1]
  · have hlam1 : lam ≤ Real.exp (-1) := hlamlt.le.trans hlam₀1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h := hsum N hN lam hlam hlamlt {Z | (isolatedDipoles Z).card = p₁}
      (fun Z => ENNReal.ofReal (Real.exp (-β * energy lam Z))) 0 p₁ hp₁
      (fun K p p₀ φ T hγ => ⟨hcell N hN lam hlam hlam1 K p p₀ φ T hγ _,
        fun hlt => lintegral_markedCell_isolatedDipoles_eq_zero hN hγ hlt _⟩)
    refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have hω0 : 0 ≤ ω lam := hω.nonneg lam hlam
    have e : c' * N * (((p₁ : ℝ) - N) / N) ^ 2 = c' * ((N : ℝ) - p₁) ^ 2 / N := by
      field_simp
      ring
    have h1 := mul_nonneg hN0.le hω0
    rw [e]
    linarith only [h1]

end Main

end UpperAssembly

end TwoComponentCoulomb

end
