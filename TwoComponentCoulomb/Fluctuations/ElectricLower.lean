/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.AlphaBallGrowth
public import TwoComponentCoulomb.Frozen.IsGeneric
public import TwoComponentCoulomb.Frozen.IsIsolatedDipole
public import TwoComponentCoulomb.Frozen.IsIsolatedPair
public import TwoComponentCoulomb.Frozen.NumComponents
public import TwoComponentCoulomb.Frozen.SecondNearestNeighbor
import TwoComponentCoulomb.Energy.CorominoCount
import TwoComponentCoulomb.NearestNeighbor.Components
import TwoComponentCoulomb.NearestNeighbor.Isolated
import TwoComponentCoulomb.NearestNeighbor.Second
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# The energy bounds the electric energy of the grown discs (Theorem 2, Step 2)

Source: l. 2062–2090 (the case `β > 2` of Step 2; the inequalities below
hold for every configuration and do not involve `β`). Write `I^pair` for the indices in an
isolated pair (`IsIsolatedPair`), `I^dip` for the indices in an isolated dipole
(`IsIsolatedDipole`), `K = numComponents Z`, `φ₂ = secondNearestNeighbor hN Z`, and
`αᵢ = alphaRadius hN λ γ Z i`.

* `exists_energy_ge_electric_alphaRadius` : (l. 2062–2078) arguing as in the proof of
  Corollary 2.3, for `2λ ≤ γ ≤ 1` and generic `Z`,
  `F_λ ≥ (1/4π) ∫ |∇h_α|² - ½ Σᵢ g_λ(zᵢ - z_{φ₁ i})
    + Σ_{i ∈ I^pair ∖ I^dip, φ₂ i, φ₂ (φ₁ i) ∈ I^pair} (log (αᵢ / r̃₁(zᵢ)) - C)
    - C Σ_{i ∈ I^dip, φ₂ i, φ₂ (φ₁ i) ∈ I^pair} [(r̃₁ / r̃₂)² + ((r̃₁ / γ)² ∧ 1)] - C (N - K)`.
* `linearA1`, `linearA2`, `linearA3` : the quantities `A₁`, `A₂`, `A₃` of l. 2084–2089.
* `exists_integral_norm_sq_electricField_le_linearA` : (l. 2079–2090)
  `(1/4π) ∫ |∇h_α|² ≤ A₁ + C (A₂ + A₃)`, using Remark 2.1 (a point is the second nearest
  neighbour of at most twelve points), `|I^pair ∖ I^dip| ≤ 2N - |I^dip|` and `|I^dip| / 2 ≤ K`.

The constants are absolute.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

variable {N : ℕ}

/-! ### The termwise comparison (proof of Corollary 2.3 with the radii `α`) -/

section Termwise

open scoped Classical in
/-- The termwise comparison of the proof of Corollary 2.3, repeated with the radii `α`
(source l. 2062–2078). The left-hand side is the term of index `i` of the lower bound of
`exists_energy_ge_electric_alphaRadius` (the term `C' (N - K)` and the electric energy aside),
minus the cost `c` charged to an exceptional index (`i ∉ I^pair`, or `φ₂ i ∉ I^pair`, or
`φ₂ (φ₁ i) ∉ I^pair`); the right-hand side is the term of index `i` of the lower bound of
`energy_ge_electric_alphaRadius`. -/
private theorem termwise_le_alphaRadius (hN : 2 ≤ N) {Cg c C' : ℝ}
    (hCg : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, -Real.log (max ‖z‖ lam) - Cg ≤ smearedKernel lam z)
    (hc : |Cg| + Real.log 4 + |kappa| + 32 ≤ c) (hcC' : c ≤ C') {lam γ : ℝ} (hlam : 0 < lam)
    (hγ : 0 < γ) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    (-(1 / 2) * smearedKernel lam (Z i - Z (nearestNeighbor Z i))
        + (if IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
              IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
              IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)) then
            Real.log (alphaRadius hN lam γ Z i / firstNeighborRadius lam Z i) - C'
          else 0)
        - C' * (if IsIsolatedDipole Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
              IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)) then
            (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2
              + min ((firstNeighborRadius lam Z i / γ) ^ 2) 1
          else 0)
        - (if IsIsolatedPair Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
              IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)) then 0 else c))
      ≤ (1 / 2) * ((if nearestNeighbor Z (nearestNeighbor Z i) = i then
            charge i * charge (nearestNeighbor Z i) *
                smearedKernel lam (Z i - Z (nearestNeighbor Z i))
              - charge i * (charge i + charge (nearestNeighbor Z i)) *
                  (logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa)
              - 64 * (firstNeighborRadius lam Z i /
                  max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i)) ^ 2
          else 0)
        - (if nearestNeighbor Z (nearestNeighbor Z i) ≠ i then
            logKernel (alphaRadius hN lam γ Z i : ℂ) + kappa
          else 0)) := by
  -- basic facts about the radii
  have hr1 : 0 < firstNeighborRadius lam Z i := hlam.trans_le (lam_le_firstNeighborRadius lam Z i)
  have hr12 := firstNeighborRadius_le_secondNeighborRadius hN lam Z i
  have hα1 := firstNeighborRadius_le_alphaRadius hN lam γ Z i
  have hαpos : 0 < alphaRadius hN lam γ Z i := hr1.trans_le hα1
  have hq0 := sq_nonneg (firstNeighborRadius lam Z i /
    max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i))
  have hq1 := sq_div_max_min_le_one hr1 (secondNeighborRadius hN lam Z i) γ
  have hqs := sq_div_max_min_le hr1 hr12 hγ
  have hs0 : 0 ≤ (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2
      + min ((firstNeighborRadius lam Z i / γ) ^ 2) 1 :=
    add_nonneg (sq_nonneg _) (le_min (sq_nonneg _) zero_le_one)
  set q := (firstNeighborRadius lam Z i /
    max (min (secondNeighborRadius hN lam Z i) γ) (firstNeighborRadius lam Z i)) ^ 2 with hq
  set s := (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2
    + min ((firstNeighborRadius lam Z i / γ) ^ 2) 1 with hs
  have hG := smearedKernel_add_log_firstNeighborRadius_ge hCg hlam Z i
  set g := smearedKernel lam (Z i - Z (nearestNeighbor Z i)) with hg
  have hlogα := Real.log_le_log hr1 hα1
  have hκ := le_abs_self kappa
  have hCg' := le_abs_self Cg
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hCg0 := abs_nonneg Cg
  have hκ0 := abs_nonneg (kappa)
  rw [logKernel_ofReal hαpos]
  by_cases hcyc : nearestNeighbor Z (nearestNeighbor Z i) = i
  · -- the vertex `i` is on a 2-cycle
    simp only [hcyc, ne_eq, not_true_eq_false, ite_true, ite_false, sub_zero]
    have hii : charge i * charge i = 1 := by
      rcases charge_eq_one_or_neg_one i with h | h <;> simp [h]
    by_cases hsg : charge i * charge (nearestNeighbor Z i) = 1
    · -- same-sign 2-cycle
      have hD : charge i * (charge i + charge (nearestNeighbor Z i)) = 2 := by
        rw [mul_add, hii, hsg]
        norm_num
      have hnd : ¬ IsIsolatedDipole Z i := fun h => by
        have := ((isIsolatedDipole_iff Z i).1 h).2
        rw [hsg] at this
        norm_num at this
      rw [hsg, hD]
      have hB : ¬ (IsIsolatedDipole Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) := fun h => hnd h.1
      rw [ite_eq_right hB]
      by_cases hE : IsIsolatedPair Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))
      · rw [ite_eq_left ⟨hE.1, hnd, hE.2.1, hE.2.2⟩, ite_eq_left hE,
          Real.log_div hαpos.ne' hr1.ne']
        linarith
      · have hA : ¬ (IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
            IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
            IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) :=
          fun h => hE ⟨h.1, h.2.2.1, h.2.2.2⟩
        rw [ite_eq_right hA, ite_eq_right hE]
        linarith
    · -- neutral 2-cycle
      have hn : charge i * charge (nearestNeighbor Z i) = -1 := by
        rcases charge_eq_one_or_neg_one i with h | h <;>
          rcases charge_eq_one_or_neg_one (nearestNeighbor Z i) with h' | h' <;>
          simp_all
      have hD : charge i * (charge i + charge (nearestNeighbor Z i)) = 0 := by
        rw [mul_add, hii, hn]
        norm_num
      rw [hn, hD]
      by_cases hE : IsIsolatedPair Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))
      · have hdip : IsIsolatedDipole Z i := (isIsolatedDipole_iff Z i).2 ⟨hE.1, hn⟩
        rw [ite_eq_left (⟨hdip, hE.2.1, hE.2.2⟩ : IsIsolatedDipole Z i ∧ _ ∧ _), ite_eq_left hE]
        have hA : ¬ (IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
            IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
            IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) :=
          fun h => h.2.1 hdip
        rw [ite_eq_right hA]
        have h3 : 32 * s ≤ C' * s := mul_le_mul_of_nonneg_right (by linarith) hs0
        linarith
      · have hB : ¬ (IsIsolatedDipole Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
            IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) :=
          fun h => hE ⟨h.1.isIsolatedPair, h.2.1, h.2.2⟩
        have hA : ¬ (IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
            IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
            IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) :=
          fun h => h.2.1 ((isIsolatedDipole_iff Z i).2 ⟨h.1, hn⟩)
        rw [ite_eq_right hB, ite_eq_right hA, ite_eq_right hE]
        linarith
  · -- the vertex `i` is a tree vertex
    have hE : ¬ (IsIsolatedPair Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) :=
      fun h => hcyc h.1.nearestNeighbor_nearestNeighbor
    have hA : ¬ (IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) :=
      fun h => hE ⟨h.1, h.2.2.1, h.2.2.2⟩
    have hB : ¬ (IsIsolatedDipole Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) :=
      fun h => hE ⟨h.1.isIsolatedPair, h.2.1, h.2.2⟩
    rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right hE, ite_eq_right hcyc, ite_eq_left hcyc]
    linarith

end Termwise

/-! ### The energy lower bound with the electric energy (source l. 2062–2078) -/

section Lower

open scoped Classical in
/-- **The energy bounds the electric energy of the grown discs** (Theorem 2, Step 2, source
l. 2062–2078, the form of Corollary 2.3 with the radii `α` and the electric energy kept): there is
an absolute constant `C` such that for `N ≥ 2`, `0 < λ`, `2λ ≤ γ ≤ 1` and generic `Z`,
`F_λ ≥ (1/4π) ∫ |∇h_α|² - ½ Σᵢ g_λ(zᵢ - z_{φ₁ i})
  + Σ_{i ∈ I^pair ∖ I^dip, φ₂ i, φ₂ (φ₁ i) ∈ I^pair} (log (αᵢ / r̃₁(zᵢ)) - C)
  - C Σ_{i ∈ I^dip, φ₂ i, φ₂ (φ₁ i) ∈ I^pair} [(r̃₁(zᵢ) / r̃₂(zᵢ))² + ((r̃₁(zᵢ) / γ)² ∧ 1)]
  - C (N - K)`. -/
theorem exists_energy_ge_electric_alphaRadius :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam γ : ℝ), 0 < lam → 2 * lam ≤ γ → γ ≤ 1 →
      ∀ Z : Fin N ⊕ Fin N → ℂ, IsGeneric Z →
        (1 / (4 * Real.pi)) * (∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2)
          - (1 / 2) * ∑ i, smearedKernel lam (Z i - Z (nearestNeighbor Z i))
          + ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
              (Real.log (alphaRadius hN lam γ Z i / firstNeighborRadius lam Z i) - C)
          - C * ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
              ((firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2
                + min ((firstNeighborRadius lam Z i / γ) ^ 2) 1)
          - C * ((N : ℝ) - numComponents Z)
        ≤ energy lam Z := by
  obtain ⟨Cg, hCg⟩ := exists_smearedKernel_ge
  set c : ℝ := |Cg| + Real.log 4 + |kappa| + 32 with hc
  have hc0 : 0 < c := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    positivity
  refine ⟨151 * c, by positivity, ?_⟩
  intro N hN lam γ hlam hγ _ Z hZ
  have hγ0 : 0 < γ := by linarith
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N ⊕ Fin N)))
    (fun i _ => termwise_le_alphaRadius hN hCg hc.ge (by linarith : c ≤ 151 * c) hlam hγ0 Z i)
  -- the cost of the exceptional indices
  have hcard := card_not_isolated_and_second_le hN hZ
  have hcardR : (((Finset.univ.filter fun i => ¬ (IsIsolatedPair Z i ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)))).card : ℕ) : ℝ) ≤
      150 * ((N : ℝ) - numComponents Z) := by
    have h := (Nat.cast_le (α := ℝ)).2 hcard
    rw [Nat.cast_mul, Nat.cast_sub (numComponents_le Z)] at h
    simpa using h
  have hNK : 0 ≤ (N : ℝ) - numComponents Z := sub_nonneg.2 (Nat.cast_le.2 (numComponents_le Z))
  have hE : ∑ i, (if IsIsolatedPair Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)) then (0 : ℝ) else c) =
      c * (((Finset.univ.filter fun i => ¬ (IsIsolatedPair Z i ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)))).card : ℕ) : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hmain := energy_ge_electric_alphaRadius hN hlam γ Z
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hE] at hsum
  simp only [Finset.sum_filter] at hmain ⊢
  have h1 := mul_le_mul_of_nonneg_left hcardR hc0.le
  have h2 := mul_nonneg hc0.le hNK
  linarith

end Lower

/-! ### The decomposition `(1/4π) ∫ |∇h_α|² ≤ A₁ + C (A₂ + A₃)` (source l. 2079–2090) -/

section Decomposition

open scoped Classical in
/-- `A₁` of Theorem 2, Step 2 (source l. 2085–2086), with the constant `C` of the energy lower
bound as a parameter:
`A₁ = F_λ(Z) + ½ Σᵢ g_λ(zᵢ - z_{φ₁ i})
  - Σ_{i ∈ I^pair ∖ I^dip, φ₂ i ∈ I^pair, φ₂ (φ₁ i) ∈ I^pair} (log (αᵢ / r̃₁(zᵢ)) - C)`. -/
noncomputable def linearA1 (hN : 2 ≤ N) (lam γ C : ℝ) (Z : Fin N ⊕ Fin N → ℂ) : ℝ :=
  energy lam Z + (1 / 2) * ∑ i, smearedKernel lam (Z i - Z (nearestNeighbor Z i)) -
    ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
        IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
      (Real.log (alphaRadius hN lam γ Z i / firstNeighborRadius lam Z i) - C)

open scoped Classical in
/-- `A₂` of Theorem 2, Step 2 (source l. 2088):
`A₂ = Σ_{i ∈ I^dip, φ₂ i ∈ I^dip, φ₂ (φ₁ i) ∈ I^pair} (r̃₁(zᵢ) / r̃₂(zᵢ))² + (N - ½ |I^dip|)`. -/
noncomputable def linearA2 (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
      IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
    (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 +
  ((N : ℝ) - (1 / 2) * ((Finset.univ.filter (IsIsolatedDipole Z)).card : ℝ))

open scoped Classical in
/-- `A₃` of Theorem 2, Step 2 (source l. 2089):
`A₃ = Σ_{i ∈ I^dip, φ₂ i ∈ I^dip, φ₂ (φ₁ i) ∈ I^pair} ((r̃₁(zᵢ) / γ)² ∧ 1)`. -/
noncomputable def linearA3 (hN : 2 ≤ N) (lam γ : ℝ) (Z : Fin N ⊕ Fin N → ℂ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
      IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
    min ((firstNeighborRadius lam Z i / γ) ^ 2) 1

open scoped Classical in
/-- `|I^dip| ≤ 2K`: an isolated dipole is a whole component. -/
theorem card_filter_isIsolatedDipole_le_two_mul_numComponents (Z : Fin N ⊕ Fin N → ℂ) :
    (Finset.univ.filter (IsIsolatedDipole Z)).card ≤ 2 * numComponents Z := by
  rw [card_filter_isIsolatedDipole Z]
  exact Nat.mul_le_mul_left 2 (isolatedDipoles_card_le_numComponents Z)

open scoped Classical in
/-- `N - K ≤ N - ½ |I^dip|` and `0 ≤ N - ½ |I^dip|`. -/
theorem sub_numComponents_le_sub_half_card_isIsolatedDipole (Z : Fin N ⊕ Fin N → ℂ) :
    (N : ℝ) - numComponents Z ≤
        (N : ℝ) - (1 / 2) * ((Finset.univ.filter (IsIsolatedDipole Z)).card : ℝ) ∧
      0 ≤ (N : ℝ) - (1 / 2) * ((Finset.univ.filter (IsIsolatedDipole Z)).card : ℝ) := by
  have h1 : ((Finset.univ.filter (IsIsolatedDipole Z)).card : ℝ) ≤ 2 * (numComponents Z : ℝ) := by
    exact_mod_cast card_filter_isIsolatedDipole_le_two_mul_numComponents Z
  have h2 : (numComponents Z : ℝ) ≤ N := by exact_mod_cast numComponents_le Z
  constructor <;> linarith

open scoped Classical in
/-- **Remark 2.1 in the decomposition** (source l. 2079): the indices `i ∈ I^dip` with
`φ₂ i ∈ I^pair ∖ I^dip` are at most `12 |I^pair ∖ I^dip| ≤ 12 (2N - |I^dip|)`, and their summands
`(r̃₁ / r̃₂)² + ((r̃₁ / γ)² ∧ 1)` are at most `2`. -/
theorem sum_isIsolatedDipole_le_sum_add (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (γ : ℝ)
    {Z : Fin N ⊕ Fin N → ℂ} (hZ : IsGeneric Z) :
    ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
        ((firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2
          + min ((firstNeighborRadius lam Z i / γ) ^ 2) 1) ≤
      ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
          IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
        (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 +
      ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
          IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
        min ((firstNeighborRadius lam Z i / γ) ^ 2) 1 +
      48 * ((N : ℝ) - (1 / 2) * ((Finset.univ.filter (IsIsolatedDipole Z)).card : ℝ)) := by
  set S₂ := Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
    IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
    IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) with hS₂
  set S₃ := Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
    IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
    IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) with hS₃
  set T := Finset.univ.filter (fun i => IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i) with hT
  set f : Fin N ⊕ Fin N → ℝ := fun i => (firstNeighborRadius lam Z i /
    secondNeighborRadius hN lam Z i) ^ 2 + min ((firstNeighborRadius lam Z i / γ) ^ 2) 1 with hf
  have hsub : S₃ ⊆ S₂ := fun i hi => by
    obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2.isIsolatedPair, h3⟩
  -- every summand is at most `2`
  have hf2 : ∀ i, f i ≤ 2 := fun i => by
    have hr1 : 0 < firstNeighborRadius lam Z i :=
      hlam.trans_le (lam_le_firstNeighborRadius lam Z i)
    have hr12 := firstNeighborRadius_le_secondNeighborRadius hN lam Z i
    have hq1 : (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 ≤ 1 :=
      pow_le_one₀ (div_nonneg hr1.le (hr1.trans_le hr12).le)
        ((div_le_one (hr1.trans_le hr12)).2 hr12)
    have hq2 := min_le_right ((firstNeighborRadius lam Z i / γ) ^ 2) 1
    simp only [hf]
    linarith
  -- the exceptional indices have their second nearest neighbour in `I^pair ∖ I^dip`
  have hexc : S₂ \ S₃ ⊆ Finset.univ.filter fun j => secondNearestNeighbor hN Z j ∈ T := by
    intro i hi
    obtain ⟨hi2, hi3⟩ := Finset.mem_sdiff.1 hi
    obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hi2
    have h4 : ¬ IsIsolatedDipole Z (secondNearestNeighbor hN Z i) := fun h =>
      hi3 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h, h3⟩)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2, h4⟩⟩
  have hTcard : T.card + (Finset.univ.filter (IsIsolatedDipole Z)).card ≤ 2 * N := by
    have h1 : T.card ≤ (Finset.univ.filter fun i => ¬ IsIsolatedDipole Z i).card :=
      Finset.card_le_card fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _,
        (Finset.mem_filter.1 hi).2.2⟩
    have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (IsIsolatedDipole Z)
    have h3 : (Finset.univ : Finset (Fin N ⊕ Fin N)).card = 2 * N := by simp [two_mul]
    omega
  have hcard : (S₂ \ S₃).card ≤ 12 * (2 * N - (Finset.univ.filter (IsIsolatedDipole Z)).card) := by
    have h1 := (Finset.card_le_card hexc).trans (card_filter_secondNearestNeighbor_mem_le hN hZ.1 T)
    omega
  have hcardR : ((S₂ \ S₃).card : ℝ) ≤
      24 * ((N : ℝ) - (1 / 2) * ((Finset.univ.filter (IsIsolatedDipole Z)).card : ℝ)) := by
    have hle : (Finset.univ.filter (IsIsolatedDipole Z)).card ≤ 2 * N := by omega
    have h1 : ((S₂ \ S₃).card : ℝ) ≤
        12 * ((2 * N : ℕ) - (Finset.univ.filter (IsIsolatedDipole Z)).card : ℕ) := by
      exact_mod_cast hcard
    rw [Nat.cast_sub hle] at h1
    push_cast at h1
    linarith
  have hexcsum : ∑ i ∈ S₂ \ S₃, f i ≤ 2 * ((S₂ \ S₃).card : ℝ) := by
    have := Finset.sum_le_card_nsmul (S₂ \ S₃) f 2 fun i _ => hf2 i
    rw [nsmul_eq_mul] at this
    linarith
  have hsplit := Finset.sum_sdiff (f := f) hsub
  have hS₃sum : ∑ i ∈ S₃, f i = ∑ i ∈ S₃, (firstNeighborRadius lam Z i /
      secondNeighborRadius hN lam Z i) ^ 2 +
        ∑ i ∈ S₃, min ((firstNeighborRadius lam Z i / γ) ^ 2) 1 :=
    Finset.sum_add_distrib
  linarith

open scoped Classical in
/-- `A₁` is nondecreasing in its constant. -/
theorem linearA1_le_linearA1 (hN : 2 ≤ N) (lam γ : ℝ) {C C' : ℝ} (h : C ≤ C')
    (Z : Fin N ⊕ Fin N → ℂ) : linearA1 hN lam γ C Z ≤ linearA1 hN lam γ C' Z := by
  unfold linearA1
  have := Finset.sum_le_sum (s := Finset.univ.filter (fun i => IsIsolatedPair Z i ∧
      ¬ IsIsolatedDipole Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))))
    (f := fun i => Real.log (alphaRadius hN lam γ Z i / firstNeighborRadius lam Z i) - C')
    (g := fun i => Real.log (alphaRadius hN lam γ Z i / firstNeighborRadius lam Z i) - C)
    fun i _ => by linarith
  linarith

/-- **The decomposition of the electric energy** (Theorem 2, Step 2, source l. 2079–2090): there is
an absolute constant `C` such that for `N ≥ 2`, `0 < λ`, `2λ ≤ γ ≤ 1` and generic `Z`,
`(1/4π) ∫ |∇h_α|² ≤ A₁ + C (A₂ + A₃)`, where `A₁ = linearA1 hN λ γ C Z` carries the same
constant. -/
theorem exists_integral_norm_sq_electricField_le_linearA :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam γ : ℝ), 0 < lam → 2 * lam ≤ γ → γ ≤ 1 →
      ∀ Z : Fin N ⊕ Fin N → ℂ, IsGeneric Z →
        (1 / (4 * Real.pi)) * (∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2) ≤
          linearA1 hN lam γ C Z + C * (linearA2 hN lam Z + linearA3 hN lam γ Z) := by
  classical
  obtain ⟨C, hC, h3⟩ := exists_energy_ge_electric_alphaRadius
  refine ⟨49 * C, by positivity, ?_⟩
  intro N hN lam γ hlam hγ hγ1 Z hZ
  have hmain := h3 N hN lam γ hlam hγ hγ1 Z hZ
  have hcount := sum_isIsolatedDipole_le_sum_add hN hlam γ hZ
  obtain ⟨hNK, hD0⟩ := sub_numComponents_le_sub_half_card_isIsolatedDipole Z
  have hA1 := linearA1_le_linearA1 hN lam γ (by linarith : C ≤ 49 * C) Z
  have hq0 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
      IsIsolatedDipole Z (secondNearestNeighbor hN Z i) ∧
      IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
        (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA3 : 0 ≤ linearA3 hN lam γ Z :=
    Finset.sum_nonneg fun i _ => le_min (sq_nonneg _) zero_le_one
  have key : (1 / (4 * Real.pi)) *
        (∫ x, ‖electricField charge Z (alphaRadius hN lam γ Z) x‖ ^ 2) ≤
      linearA1 hN lam γ C Z + C * ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
        ((firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2
          + min ((firstNeighborRadius lam Z i / γ) ^ 2) 1) +
      C * ((N : ℝ) - numComponents Z) := by
    unfold linearA1
    linarith
  unfold linearA2
  unfold linearA3 at hA3 ⊢
  have e1 := mul_le_mul_of_nonneg_left hcount hC.le
  have e2 := mul_le_mul_of_nonneg_left hNK hC.le
  have e3 := mul_nonneg hC.le hq0
  have e4 := mul_nonneg hC.le hA3
  have e5 := mul_nonneg hC.le hD0
  linarith

end Decomposition

end TwoComponentCoulomb

end
