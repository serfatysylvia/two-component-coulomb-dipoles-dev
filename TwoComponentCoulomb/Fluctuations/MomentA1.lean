/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.MomentCells
import TwoComponentCoulomb.Fluctuations.TiltedIsolated
import TwoComponentCoulomb.Fluctuations.TiltedIsolatedCrude

/-!
# Theorem 2, Step 3: the exponential moment of `A₁` (eq:A1)

Source: proof of Theorem 2 (`prop:linear`), Step 3, l. 1969–1994, for `β > 2`:
`log 𝔼_ℙ[e^{β A₁}] ≤ C_β N (ω_λ + φ_β(γ)) + C_β log (N + 1)`   (eq:A1),
where `A₁ = F_λ + ½ ∑_i g_λ(z_i - z_{φ₁ i}) - ∑_{i ∈ I'} (log (α_i / r̃₁(z_i)) - C)`
(`linearA1`, with `I'` the marked same-sign vertices and `α_i = (τ_i ∧ γ) ∨ r̃₁(z_i)`).

## Proof

`𝔼_ℙ[e^{β A₁}] = Z⁻¹ ∫_Λ e^{β (A₁ - F_λ)}`, and `A₁ - F_λ` cancels `F_λ`. The integral is split
along the marked graphs `γ = (φ, T) ∈ D_{2N,K,p,p₀}` of Proposition 3.9, Step 2; on one cell
(`MomentCells.linearA1_sub_energy_eq_split`, `MomentCells.linearA1_sub_energy_eq_full`)
`β (A₁ - F_λ) = -β (G⁽¹⁾_γ(Z|_I) + F⁽²⁾(Z|_{Iᶜ}))` exactly, where `G⁽¹⁾_γ` is the block energy of
`Fluctuations/TiltedEnergy.lean` ("We repeat the proof of (eq:alt), keeping `γ` in the same-sign
term"). The three cases are those of `UpperAssembly.exists_cellBound_energy_rate`:

* no marked pair (`p = 0`): `β (A₁ - F_λ) = -β F^nn`, and Lemma 3.4 on all points;
* `m = N` (`Iᶜ = ∅`): the tilted (eq:n neutral conv) `alphaBlock_n_neutral_conv` on all points;
* `2 ≤ m < N`: the separation of variables, `alphaBlock_n_neutral_conv` (if `N ≤ 2m`) or the
  crude bound `alphaBlock_crude` (if `2m < N`, hence `p < N/2`; source l. 1990, "For `p < N/2`,
  the same crude bound applies") on `I`, and (eq:F(2)) on `Iᶜ`.

This gives the per-cell bound `CellBoundRate` with the extra exponent `C_β N φ_β(γ)`
(`MomentA1.exists_cellBound_rate`). The graph sum and the lower bound of Proposition 4.1
(`MomentCells.exists_lintegral_gibbsMeasure_le_of_cellBound_rate`) give (eq:A1).

Since `A₁` is nondecreasing in its constant `C` (`linearA1_le_linearA1`), the bound for `C ≥ 0`
gives it for every `C`.

The bounds are stated for a rate function `ω` satisfying `UpperRateHyp` in place of `ω_λ`; the
rate `ω_λ = errorRate β λ` satisfies it (`upperRateHyp_errorRate`), and the instance is taken in
`momentBound_of_two_lt` (`Fluctuations/Moment.lean`).

## Main results

* `MomentA1.exists_cellBound_rate`: the per-cell bound `CellBoundRate` for
  `∫_{cell} e^{β A₁} e^{-β F_λ}`.
* `momentA1_le_rate`: **(eq:A1)**, for a rate `ω` satisfying `UpperRateHyp`.
-/

@[expose] public section

open Finset MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

namespace MomentA1

open UpperCellBound UpperAssembly MomentCells

/-- **The per-cell bound for the `A₁` integrand, generic rate** (source l. 1969–1990): for a rate
`ω` satisfying `UpperRateHyp` in place of `ω_λ`, the integral of `e^{β A₁} e^{-β F_λ}` over one
marked cell satisfies `CellBoundRate` with an extra exponent `Cx N φ_β(γ)`. The constants depend
only on `β`, `ω` and `C`. -/
theorem exists_cellBound_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) (hω : UpperRateHyp β hβ ω) {C : ℝ}
    (hC : 0 ≤ C) :
    ∃ A c Cb Cx : ℝ, 0 < c ∧ 0 ≤ Cb ∧ 0 ≤ Cx ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam γ : ℝ), 0 < lam → lam ≤ Real.exp (-1) → lam ≤ γ →
      ∀ (K p p₀ : ℕ) (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (T : Finset (Fin N ⊕ Fin N)),
        (φ, T) ∈ markedGraphs hN K p p₀ → ∀ E : Set (Fin N ⊕ Fin N → ℂ),
        CellBoundRate β hβ ω A c Cb N K p p₀ lam (Cx * N * isolatedPhi β hβ.le lam γ)
          (∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ E ∩ markedCell hN φ T,
            ENNReal.ofReal (Real.exp (β * linearA1 hN lam γ C Z)) *
              ENNReal.ofReal (Real.exp (-β * energy lam Z))) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hconvH⟩ := alphaBlock_n_neutral_conv.{0} hβ.le hβ C 60
  obtain ⟨C₂, hC₂, hcrudeH⟩ := alphaBlock_crude.{0} hβ.le hC 60
  obtain ⟨C₄, hF2⟩ := exists_lintegral_nnEnergy_le hβ
  set L := Real.log (dipoleConstant β hβ.le) with hL
  refine ⟨C₄, c₁, C₁ + C₂ + |L|, C₁, hc₁, by positivity, hC₁.le, ?_⟩
  intro N hN lam γ hlam hlam1 hγ K p p₀ φ T hγ' E
  obtain ⟨Z₀, -, hgen, hφ, hT, hK, hp, hp₀⟩ := mem_markedGraphs.1 hγ'
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
  have hφγ : 0 ≤ isolatedPhi β hβ.le lam γ := isolatedPhi_nonneg hβ.le hlam hγ
  have hX : 0 ≤ C₁ * N * isolatedPhi β hβ.le lam γ := by positivity
  obtain ⟨hF2c, hF2f⟩ := hF2 N Z₀ (nearestNeighbor Z₀) hNpos rfl lam hlam hlam1
  have hnt : Nontrivial (Fin N ⊕ Fin N) :=
    ⟨⟨Sum.inl ⟨0, hNpos⟩, Sum.inr ⟨0, hNpos⟩, Sum.inl_ne_inr⟩⟩
  rcases Nat.eq_zero_or_pos p with hp0 | hp1
  · -- no marked pair: `β (A₁ - F_λ) = -β F^nn`, and Lemma 3.4 on all points
    have hp₀0 : p₀ = 0 := by omega
    have hT0 : twiceIsolatedSet hN Z₀ = ∅ := by
      have h := card_twiceIsolatedSet (hN := hN) (Z := Z₀)
      rw [hp, hp0] at h
      exact Finset.card_eq_zero.1 h
    have h3' : 3 ≤ Fintype.card (Fin N ⊕ Fin N) := by simp; omega
    have hcell := lintegral_markedCell_le_full_of_le hN (φ := nearestNeighbor Z₀)
      (T := twiceIsolatedSet hN Z₀) E
      (fun Z => ENNReal.ofReal (Real.exp (β * linearA1 hN lam γ C Z)) *
        ENNReal.ofReal (Real.exp (-β * energy lam Z)))
      (fun Z => ENNReal.ofReal (Real.exp (-β * nnEnergy (sumKey N) lam Z))) 0
      (fun Z hZc _ => le_of_eq (by
        rw [Real.exp_zero, ENNReal.ofReal_one, one_mul, ofReal_exp_linearA1_mul,
          linearA1_sub_energy_eq_full hN h3' lam γ C Z, hZc.2.2.trans hT0, markedSameSign_empty,
          alphaBlockEnergy_empty, mul_neg, neg_mul]))
    rw [Real.exp_zero, ENNReal.ofReal_one, one_mul] at hcell
    refine Or.inl (hcell.trans (hF2f.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))))
    have e1 : (p : ℝ) = 0 := by exact_mod_cast hp0
    have e2 : (p₀ : ℝ) = 0 := by exact_mod_cast hp₀0
    rw [e1, e2]
    have h1 : 0 ≤ (C₁ + C₂ + |L|) * N * ω lam := by
      rw [mul_assoc]; exact mul_nonneg hCb hNω
    have h2 : 0 ≤ (C₁ + C₂ + |L|) * Real.log (N + 1) := mul_nonneg hCb hlogN
    simp only [mul_zero, Real.log_zero, sub_self]
    rw [← hL]
    have h3 : c₁ * (0 : ℝ) ^ 2 / N = 0 := by simp
    linarith
  -- at least one marked pair: `m ≥ 2`
  have hm2 : 2 ≤ m := by
    by_contra h
    have h' := twiceIsolatedSet_eq_empty_of_numIsolatedPairs_le_one hN (Z := Z₀) (by omega)
    have h2 := card_twiceIsolatedSet (hN := hN) (Z := Z₀)
    rw [h', hp] at h2
    simp at h2
    omega
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
  · -- `Iᶜ = ∅`: the tilted Proposition 3.8 on all points
    have hKeq : numComponents Z₀ = N := by omega
    have h3' : 3 ≤ Fintype.card (Fin N ⊕ Fin N) := by simp; omega
    have hcell := lintegral_markedCell_le_full_of_le hN (φ := nearestNeighbor Z₀)
      (T := twiceIsolatedSet hN Z₀) E
      (fun Z => ENNReal.ofReal (Real.exp (β * linearA1 hN lam γ C Z)) *
        ENNReal.ofReal (Real.exp (-β * energy lam Z)))
      (fun Z => ENNReal.ofReal (Real.exp (-(β * alphaBlockEnergy h3' (sumKey N) lam γ C
        (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) Z)))) 0
      (fun Z hZc _ => le_of_eq (by
        rw [Real.exp_zero, ENNReal.ofReal_one, one_mul, ofReal_exp_linearA1_mul,
          linearA1_sub_energy_eq_full hN h3' lam γ C Z, hZc.2.1, hZc.2.2, mul_neg]))
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
      hcard2 (by omega) le_rfl (by linarith) (by omega) hScard' lam γ hlam hlam1 hγ
    have hF1 := entropy_mul_le_main_rate hβ ω (X := C₁ * N * isolatedPhi β hβ.le lam γ) hc₁.le
      hC₁.le
      (N := N) (m := N) (p := p) (p₀ := p₀) (p₀' := p₀ + N - p) hNpos le_rfl hp₀p (hmN' ▸ hpm)
      (by omega) hr0 hr
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
  -- `2 ≤ m < N`: the separation of variables
  have hcardIc : Fintype.card {i // i ∉ pairVerts (nearestNeighbor Z₀)} = 2 * (N - m) :=
    card_compl_pairVerts_subtype rfl
  have : Nontrivial {i // i ∉ pairVerts (nearestNeighbor Z₀)} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hg₁ : Measurable fun x : {i // i ∈ pairVerts (nearestNeighbor Z₀)} → ℂ =>
      ENNReal.ofReal (Real.exp (-(β * alphaBlockEnergy h3
        (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) lam γ C
        (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_alphaBlockEnergy h3 _ lam γ C _).const_mul β).neg)
  have hcell := lintegral_markedCell_le_mul_of_le hN (φ := nearestNeighbor Z₀)
    (T := twiceIsolatedSet hN Z₀) E
    (fun Z => ENNReal.ofReal (Real.exp (β * linearA1 hN lam γ C Z)) *
        ENNReal.ofReal (Real.exp (-β * energy lam Z))) 0 hg₁
    (measurable_ofReal_exp_neg_mul (measurable_nnEnergy
      (subtypeKey (· ∉ pairVerts (nearestNeighbor Z₀)) (sumKey N)) lam) β)
    (fun Z hZc _ => le_of_eq (by
      rw [Real.exp_zero, ENNReal.ofReal_one, one_mul, ofReal_exp_linearA1_mul,
        linearA1_sub_energy_eq_split hN lam γ C hZc.2.1 hZc.2.2 h3,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring))
  have hY₂ := @hF2c inferInstance
  have hf2 := pairRestrict_pairRestrict (nearestNeighbor Z₀)
  have hf0 := pairRestrict_ne_of_nearestNeighbor (Z := Z₀) rfl
  by_cases hNm : (N : ℝ) ≤ 2 * m
  · have h := hconvH {i // i ∈ pairVerts (nearestNeighbor Z₀)}
      (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N))
      (pairRestrict (nearestNeighbor Z₀)) hf2 hf0 h3
      (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) hSinv N m
      (p₀ + m - p) hcardI hm2 hmN hNm (by omega) hScard lam γ hlam hlam1 hγ
    have hF1 := entropy_mul_le_main_rate hβ ω (X := C₁ * N * isolatedPhi β hβ.le lam γ) hc₁.le
      hC₁.le
      (N := N) (m := m) (p := p) (p₀ := p₀) (p₀' := p₀ + m - p) (by omega) hmN hp₀p hpm hp₀'
      hr0 hr
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
      (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N))
      (pairRestrict (nearestNeighbor Z₀)) hf2 hf0 h3
      (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) hSinv N m
      (p₀ + m - p) hcardI hm2 hmN (by omega) lam γ hlam hlam1
    have hF1 := entropy_mul_le_crude (m := m) (p := p) (p₀ := p₀) (p₀' := p₀ + m - p) hp₀p hpm
      hp₀' h
    have hpN : (p : ℝ) < N / 2 := by
      have : (p : ℝ) ≤ m := by exact_mod_cast hpm
      linarith
    refine Or.inr ⟨hpN, le_ofReal_exp_of_le_mul hcell hF1 hY₂ ?_⟩
    rw [ite_eq_left hβ, ite_eq_right hβ.ne']
    have hmN'' : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have h1 : -((m : ℝ) * L) ≤ |L| * N := by
      have := neg_abs_le L
      have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have m1 := mul_le_mul_of_nonneg_left this h0
      have m2 := mul_le_mul_of_nonneg_left hmN'' (abs_nonneg L)
      linarith only [m1, m2]
    have hmr : (m : ℝ) = numIsolatedPairs Z₀ := rfl
    rw [← hL, ← hmr]
    have h2 := mul_pos hC₁ hN0
    linarith

end MomentA1

open MomentCells

/-- **Theorem 2, eq. (eq:A1), generic rate** (`prop:linear`, Step 3, source l. 1969–1994), for a
rate `ω` satisfying `UpperRateHyp` in place of `ω_λ`: for `β > 2` and every constant `C_A` there
are `C, λ₁ > 0`, depending only on `β`, `ω` and `C_A`, such that for `N ≥ 2`, `0 < λ < λ₁` and
`2λ ≤ γ ≤ 1`, `𝔼_ℙ[e^{β A₁}] ≤ exp (C N (φ_β(γ) + ω(λ)) + C log (N + 1))`. -/
theorem momentA1_le_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ) (hω : UpperRateHyp β hβ ω)
    (C_A : ℝ) :
    ∃ C lam₁ : ℝ, 0 < C ∧ 0 < lam₁ ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam < lam₁ →
      ∀ γ : ℝ, 2 * lam ≤ γ → γ ≤ 1 →
        ∫⁻ Z, ENNReal.ofReal (Real.exp (β * linearA1 hN lam γ C_A Z)) ∂gibbsMeasure N β lam ≤
          ENNReal.ofReal (Real.exp (C * N * (isolatedPhi β hβ.le lam γ + ω lam)
            + C * Real.log (N + 1))) := by
  obtain ⟨A, c, Cb, Cx, hc, hCb, hCx, hcell⟩ :=
    MomentA1.exists_cellBound_rate hβ ω hω (le_max_right C_A 0)
  obtain ⟨C, lam₁, hC, hlam₁, hlam₁1, hgibbs⟩ :=
    exists_lintegral_gibbsMeasure_le_of_cellBound_rate hβ ω hω A c Cb hc hCb
  refine ⟨C + Cx, lam₁, by positivity, hlam₁, ?_⟩
  intro N hN lam hlam hlamlt γ hγ hγ1
  have hlam1 : lam ≤ Real.exp (-1) := hlamlt.le.trans hlam₁1
  have hγl : lam ≤ γ := by linarith
  have hβ0 : 0 ≤ β := by linarith
  have h := hgibbs N hN lam hlam hlamlt
    (fun Z => ENNReal.ofReal (Real.exp (β * linearA1 hN lam γ (max C_A 0) Z)))
    (Cx * N * isolatedPhi β hβ.le lam γ)
    (fun K p p₀ φ T hγ' => hcell N hN lam γ hlam hlam1 hγl K p p₀ φ T hγ' Set.univ)
  refine (lintegral_mono fun Z => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left (linearA1_le_linearA1 hN lam γ (le_max_left C_A 0) Z) hβ0))).trans
    (h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)))
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hω0 : 0 ≤ ω lam := hω.nonneg lam hlam
  have hφ0 : 0 ≤ isolatedPhi β hβ.le lam γ := isolatedPhi_nonneg hβ.le hlam hγl
  have hlogN : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by linarith)
  have e1 : 0 ≤ C * N * isolatedPhi β hβ.le lam γ := by positivity
  have e2 : 0 ≤ Cx * N * ω lam := by positivity
  have e3 : 0 ≤ Cx * Real.log (N + 1) := by positivity
  have e : (C + Cx) * N * (isolatedPhi β hβ.le lam γ + ω lam)
      + (C + Cx) * Real.log (N + 1) =
      C * N * ω lam + C * Real.log (N + 1) + Cx * N * isolatedPhi β hβ.le lam γ
        + (C * N * isolatedPhi β hβ.le lam γ + Cx * N * ω lam
          + Cx * Real.log (N + 1)) := by ring
  rw [e]
  linarith

end TwoComponentCoulomb

end
