/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.TiltedEnergy
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Integrals.LogFacts
import TwoComponentCoulomb.Gibbs.Measurability

/-!
# The same-sign radial split of Theorem 2, Step 3

Source `source/dipole-formation.tex`, proof of Theorem 2, Step 3.
The paper splits the factor into the `ρ` correction and the cutoff correction.
The first integral is (align2). The second is extended to the whole plane and split at `4γ`.
The resulting representative reduction is used by `Fluctuations/TiltedIsolated.lean`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

universe u

namespace TwoComponentCoulomb
namespace SourcePairRadial

/-- The cutoff fraction is `min (a/γ) 1`. -/
theorem div_max_eq_min {a γ : ℝ} (ha : 0 < a) (hγ : 0 < γ) :
    a / max γ a = min (a / γ) 1 := by
  rcases le_total a γ with h | h
  · rw [max_eq_left h, min_eq_left ((div_le_one hγ).2 h)]
  · rw [max_eq_right h, div_self ha.ne', min_eq_right ((one_le_div hγ).2 h)]

/-- **The written same-sign split**, valid for the critical power `4` and the
supercritical power `2β`. -/
theorem cutoff_rpow_le {a ρ γ b : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hγ : 0 < γ)
    (hb : 0 ≤ b) :
    (a / max (min ρ γ) a) ^ b ≤ (a / ρ) ^ b + (min (a / γ) 1) ^ b := by
  rcases le_total ρ γ with h | h
  · rw [min_eq_left h]
    refine le_trans ?_ (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))
    exact Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_left ha.le hρ (le_max_left _ _)) hb
  · rw [min_eq_right h, div_max_eq_min ha hγ]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)

/-- **Theorem 2, Step 3**, the same-sign radial estimate: split the two corrections,
apply (align2) at `ρ`, and extend only the cutoff correction to the whole plane. -/
theorem lintegral_sameSignPair_cutoff_le {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ρ γ : ℝ, 0 < lam → lam ≤ ρ → lam ≤ γ →
      ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal
          (Real.exp (β * smearedKernel lam u) *
            (displacementScale lam u / max (min ρ γ) (displacementScale lam u)) ^ (2 * β)) ≤
        ENNReal.ofReal (C * dipoleConstant β hβ.le * lam ^ (2 - β) *
          ((lam / ρ) ^ (β - 2) + (lam / γ) ^ (β - 2))) := by
  obtain ⟨Cρ, hCρ, hρint⟩ := TwoComponentCoulomb.lintegral_sameSignPair_le hβ.le
  obtain ⟨Cγ, hCγ, hγint⟩ := lintegral_sameSignPair_cutoff_le_univ hβ
  have hZ := dipoleConstant_pos β hβ.le
  refine ⟨max Cρ Cγ / dipoleConstant β hβ.le, by positivity, ?_⟩
  intro lam ρ γ hlam hρ hγ
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  have hγ0 : 0 < γ := hlam.trans_le hγ
  let F : ℂ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
    (displacementScale lam u / ρ) ^ (2 * β))
  let G : ℂ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
    min (displacementScale lam u / γ) 1 ^ (2 * β))
  have hm : Measurable F := by
    have := measurable_smearedKernel lam
    have := (continuous_displacementScale lam).measurable
    unfold F
    fun_prop
  have hG : (∫⁻ u, G u) ≤ ENNReal.ofReal (Cγ * γ ^ (2 - β)) := by
    convert hγint lam γ hlam hγ using 1
    apply lintegral_congr
    intro u
    rw [div_max_eq_min (displacementScale_pos hlam u) hγ0]
  calc _ ≤ ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), F u + G u := by
        refine lintegral_mono fun u => ?_
        have ha0 := displacementScale_pos hlam u
        dsimp only [F, G]
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_left
          (cutoff_rpow_le (displacementScale_pos hlam u) hρ0 hγ0 (by linarith : 0 ≤ 2 * β))
          (Real.exp_pos (β * smearedKernel lam u)).le
        simpa only [mul_add] using this
    _ = (∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), F u) +
        ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), G u := lintegral_add_left hm _
    _ ≤ ENNReal.ofReal (Cρ * ρ ^ (2 - β)) + ENNReal.ofReal (Cγ * γ ^ (2 - β)) :=
        add_le_add (hρint lam ρ hlam hρ) ((setLIntegral_le_lintegral _ _).trans hG)
    _ ≤ _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have eρ := rpow_neg_mul_div_rpow hlam hρ0 (β - 2)
        have eγ := rpow_neg_mul_div_rpow hlam hγ0 (β - 2)
        rw [neg_sub] at eρ eγ
        rw [div_mul_cancel₀ _ hZ.ne', mul_assoc, mul_add, eρ, eγ]
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left Cρ Cγ)
          (Real.rpow_nonneg hρ0.le (2 - β)))
          (mul_le_mul_of_nonneg_right (le_max_right Cρ Cγ)
            (Real.rpow_nonneg hγ0.le (2 - β)))

end SourcePairRadial

open IsolatedReduction TiltedReduction

open scoped Classical in
/-- The representative reduction for `A₁`, with the written same-sign radial split.
The displacement reduction and the neutral integral are those of Proposition 3.7. -/
theorem lintegral_alphaBlockCell_le_source {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) (C : ℝ) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (f : ι → ι)
      (R : Set ι) [DecidablePred (· ∈ R)] [Nontrivial {i // i ∈ R}],
      (∀ i, f (f i) = i) → (∀ i, i ∈ R ↔ f i ∉ R) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
      (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N : ℕ) (lam γ : ℝ), 0 < lam → lam ≤ Real.exp (-1) → lam ≤ γ →
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
            ENNReal.ofReal (Real.exp (-(β * alphaBlockEnergy h3 key lam γ C S z))) ≤
          ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^
              Fintype.card {i // i ∈ R} *
            ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
              ∏ j : {i // i ∈ R}, (if (j : ι) ∈ S then
                ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam w j)
                  + C' * (lam / γ) ^ (β - 2))
                else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam w j))) := by
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨Cn, hCn0, hCn⟩ := lintegral_neutralPair_le hβ (C := 0) le_rfl
  obtain ⟨Cc, hCc0, hCc⟩ := SourcePairRadial.lintegral_sameSignPair_cutoff_le h2
  set C₂ : ℝ := Real.exp (2 * β * C) * 3 ^ (2 * β) with hC₂def
  have hC₂ : 0 ≤ C₂ := by positivity
  set C' : ℝ := max Cn (C₂ * Cc) with hC'def
  refine ⟨C', lt_max_of_lt_left hCn0, ?_⟩
  intro ι _ _ key f R _ _ hf2 hRf h3 S hS N lam γ hlam hl1 hγ
  have hZ := dipoleConstant_pos β hβ
  have hscale := isolatedScale_pos hβ hlam hl1
  have hC'0 : 0 < C' := lt_max_of_lt_left hCn0
  have hs : isolatedScale β hβ lam = lam ^ (2 - β) := by simp [isolatedScale, h2.ne']
  have hsc : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hγ0 : 0 < γ := hlam.trans_le hγ
  have hx : 0 ≤ (lam / γ) ^ (β - 2) := Real.rpow_nonneg (by positivity) _
  -- Step 1: the integrand bound
  refine (setLIntegral_mono' (measurableSet_pairCell key f N) fun z hz =>
    ofReal_exp_neg_mul_alphaBlockEnergy_le hz.2 hf2 hRf h3 hS hβ0 hlam γ).trans ?_
  -- Step 2: displacement reduction
  have hg : Measurable (smearedKernel lam) := measurable_smearedKernel lam
  have hd : Measurable (displacementScale lam) := (continuous_displacementScale lam).measurable
  have e1 : Measurable fun p : ℂ × ℝ => Real.exp (β * smearedKernel lam p.1) :=
    Real.measurable_exp.comp ((hg.comp measurable_fst).const_mul β)
  have e2 : Measurable fun p : ℂ × ℝ => displacementScale lam p.1 /
      max (min p.2 γ) (displacementScale lam p.1) :=
    (hd.comp measurable_fst).div ((measurable_snd.min measurable_const).max
      (hd.comp measurable_fst))
  have hΦ : ∀ j : {i // i ∈ R}, Measurable fun p : ℂ × ℝ =>
      alphaPairWeight β C lam γ S j p.1 p.2 := by
    intro j
    by_cases hj : (j : ι) ∈ S
    · simp only [alphaPairWeight, hj, ↓reduceIte]
      exact (ENNReal.measurable_ofReal.comp (e1.mul (e2.pow_const (2 * β)))).const_mul _
    · simp only [alphaPairWeight, hj, ↓reduceIte]
      exact ENNReal.measurable_ofReal.comp e1
  refine (lintegral_cell_le_lintegral_ref key hf2 hRf lam
    (fun j u ρ => alphaPairWeight β C lam γ S j u ρ) hΦ).trans ?_
  -- Step 3: the radial integrals
  have hinner : ∀ (w : {i // i ∈ R} → ℂ) (j : {i // i ∈ R}),
      ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j),
          alphaPairWeight β C lam γ S j u (nnRadius lam w j) ≤
        ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) *
          (if (j : ι) ∈ S then
            ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam w j)
              + C' * (lam / γ) ^ (β - 2))
            else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam w j))) := by
    intro w j
    have hρ : lam ≤ nnRadius lam w j := le_nnRadius lam w j
    have hρ0 : 0 < nnRadius lam w j := lt_of_lt_of_le hlam hρ
    by_cases hj : (j : ι) ∈ S
    · simp only [alphaPairWeight, hj, ↓reduceIte]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have h1 := hCc lam (nnRadius lam w j) γ hlam hρ hγ
      have ht : isolatedTail β hβ lam (nnRadius lam w j) = (lam / nnRadius lam w j) ^ (β - 2) :=
        by simp [isolatedTail, h2.ne']
      have hy : 0 ≤ (lam / nnRadius lam w j) ^ (β - 2) := Real.rpow_nonneg (by positivity) _
      calc ENNReal.ofReal C₂ * ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j),
            ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
              (displacementScale lam u / max (min (nnRadius lam w j) γ)
                (displacementScale lam u)) ^ (2 * β))
          ≤ ENNReal.ofReal C₂ * ENNReal.ofReal (Cc * dipoleConstant β h2.le * lam ^ (2 - β) *
              ((lam / nnRadius lam w j) ^ (β - 2) + (lam / γ) ^ (β - 2))) := by gcongr
        _ = ENNReal.ofReal (C₂ * (Cc * dipoleConstant β hβ * lam ^ (2 - β) *
              ((lam / nnRadius lam w j) ^ (β - 2) + (lam / γ) ^ (β - 2)))) :=
            (ENNReal.ofReal_mul hC₂).symm
        _ ≤ _ := by
            rw [← ENNReal.ofReal_mul (mul_pos hZ hscale).le, hs, ht]
            refine ENNReal.ofReal_le_ofReal ?_
            have hq : 0 ≤ dipoleConstant β hβ * lam ^ (2 - β) *
                ((lam / nnRadius lam w j) ^ (β - 2) + (lam / γ) ^ (β - 2)) := by positivity
            have hle : C₂ * Cc ≤ C' := le_max_right _ _
            have e1 : C₂ * (Cc * dipoleConstant β hβ * lam ^ (2 - β) *
                ((lam / nnRadius lam w j) ^ (β - 2) + (lam / γ) ^ (β - 2))) =
                (C₂ * Cc) * (dipoleConstant β hβ * lam ^ (2 - β) *
                ((lam / nnRadius lam w j) ^ (β - 2) + (lam / γ) ^ (β - 2))) := by ring
            have e2 : dipoleConstant β hβ * lam ^ (2 - β) *
                (C' * (lam / nnRadius lam w j) ^ (β - 2) + C' * (lam / γ) ^ (β - 2)) =
                C' * (dipoleConstant β hβ * lam ^ (2 - β) *
                ((lam / nnRadius lam w j) ^ (β - 2) + (lam / γ) ^ (β - 2))) := by ring
            rw [e1, e2]
            exact mul_le_mul_of_nonneg_right hle hq
    · simp only [alphaPairWeight, hj, ↓reduceIte]
      have h1 := hCn lam (nnRadius lam w j) hlam hl1 hρ
      simp only [zero_mul, Real.exp_zero, mul_one] at h1
      have hφ := isolatedPhi_nonneg hβ hlam hρ
      calc _ ≤ ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam *
              (1 + Cn * isolatedPhi β hβ lam (nnRadius lam w j))) := h1
        _ ≤ _ := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (mul_nonneg hC'0.le hφ),
              ← ENNReal.ofReal_mul (mul_pos hZ hscale).le]
            refine ENNReal.ofReal_le_ofReal ?_
            have : Cn ≤ C' := le_max_left _ _
            have hq : 0 ≤ dipoleConstant β hβ * isolatedScale β hβ lam := (mul_pos hZ hscale).le
            gcongr
  calc ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
        ∏ j : {i // i ∈ R}, ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j),
          alphaPairWeight β C lam γ S j u (nnRadius lam w j)
      ≤ ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
          ∏ j : {i // i ∈ R}, (ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) *
            (if (j : ι) ∈ S then
              ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam w j)
                + C' * (lam / γ) ^ (β - 2))
              else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam w j)))) :=
        lintegral_mono fun w => Finset.prod_le_prod fun j _ => hinner w j
    _ = _ := by
        simp_rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
        exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

end TwoComponentCoulomb

end
