/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.Frozen.FirstNeighborRadius
public import TwoComponentCoulomb.Frozen.IsGeneric
public import TwoComponentCoulomb.Frozen.IsIsolatedDipole
public import TwoComponentCoulomb.Frozen.IsIsolatedPair
public import TwoComponentCoulomb.Frozen.Kappa
public import TwoComponentCoulomb.Frozen.LogKernel
public import TwoComponentCoulomb.Frozen.NearestNeighbor
public import TwoComponentCoulomb.Frozen.NumComponents
public import TwoComponentCoulomb.Frozen.SecondNearestNeighbor
public import TwoComponentCoulomb.Frozen.SecondNeighborRadius
public import TwoComponentCoulomb.Frozen.SmearedKernel
import TwoComponentCoulomb.Energy.CorominoCount
import TwoComponentCoulomb.NearestNeighbor.Components
import TwoComponentCoulomb.NearestNeighbor.Isolated
import TwoComponentCoulomb.NearestNeighbor.Second
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# From the right-hand side of Proposition 2.2 to that of Corollary 2.3

Source l. 466--489 (proof of Corollary 2.3). The theorem `mino_rhs_ge_coromino_rhs` is a pure
inequality between the explicit sums that bound the energy in Proposition 2.2 (from below) and
in Corollary 2.3: for every constant `C₀` of Proposition 2.2 there is a constant `C'` such that,
for every generic configuration, the right-hand side of Corollary 2.3 (with constant `C'`) is at
most the right-hand side of Proposition 2.2 (with constant `C₀`). Chaining it with Proposition 2.2
gives Corollary 2.3.

The proof compares the two sums index by index, with an exceptional set of indices (those `i`
with `i ∉ I^pair`, or `φ₂ i ∉ I^pair`, or `φ₂ (φ₁ i) ∉ I^pair`) whose total cost is at most
`c * 150 * (N - K)` (`card_not_isolated_and_second_le`):

* a neutral 2-cycle contributes `-g_λ(z_i - z_{φ₁ i}) - C₀ (r₁/r₂)²`, and `(r₁/r₂)² ≤ 1`;
* a same-sign 2-cycle contributes `g_λ - 2 (g(τ) + κ) - C₀ (r₁/r₂)²`, which is at least
  `-g_λ + 2 log (τ / r₁) - C` because `τ = r₂ ∧ r₂' ≥ r₁` and
  `g_λ(u) + log r₁ ≥ -C` (eq. (gr2r1), source l. 472--476);
* a tree vertex contributes `-(g(r₂) + κ) ≥ -g_λ(z_i - z_{φ₁ i}) - C` as `r₂ ≥ r₁`.
-/

public section

namespace TwoComponentCoulomb

open Finset

variable {N : ℕ}

/-! ### The termwise comparison -/

open scoped Classical in
/-- The termwise comparison. The left-hand side is the term of index `i` in the right-hand side of
Corollary 2.3 (the constant `C' * (N - K)` aside), minus the cost `c` charged to an exceptional
index (`i ∉ I^pair`, or `φ₂ i ∉ I^pair`, or `φ₂ (φ₁ i) ∉ I^pair`); the right-hand side is the term
of index `i` in the right-hand side of Proposition 2.2 (source l. 466--489). -/
private theorem termwise_le (hN : 2 ≤ N) {C₀ Cg c C' : ℝ} (hC₀ : 0 < C₀)
    (hCg : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, -Real.log (max ‖z‖ lam) - Cg ≤ smearedKernel lam z)
    (hc : |Cg| + Real.log 4 + |kappa| + C₀ / 2 ≤ c) (hcC' : c ≤ C') {lam : ℝ} (hlam : 0 < lam)
    (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    (-(1 / 2) * smearedKernel lam (Z i - Z (nearestNeighbor Z i))
        + (if IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
              IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
              IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)) then
            Real.log (min (secondNeighborRadius hN lam Z i)
              (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) / firstNeighborRadius lam Z i)
              - C'
          else 0)
        - C' * (if IsIsolatedDipole Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
              IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)) then
            (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2
          else 0)
        - (if IsIsolatedPair Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
              IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i)) then 0 else c))
      ≤ (1 / 2) * ((if nearestNeighbor Z (nearestNeighbor Z i) = i then
            charge i * charge (nearestNeighbor Z i) *
                smearedKernel lam (Z i - Z (nearestNeighbor Z i))
              - charge i * (charge i + charge (nearestNeighbor Z i)) *
                  (logKernel ((min (secondNeighborRadius hN lam Z i)
                    (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) : ℝ) : ℂ) + kappa)
              - C₀ * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2
          else 0)
        - (if nearestNeighbor Z (nearestNeighbor Z i) ≠ i then
            logKernel (secondNeighborRadius hN lam Z i) + kappa
          else 0)) := by
  -- basic facts about the radii
  have hr1 : 0 < firstNeighborRadius lam Z i := hlam.trans_le (lam_le_firstNeighborRadius lam Z i)
  have hr12 := firstNeighborRadius_le_secondNeighborRadius hN lam Z i
  have hr2 : 0 < secondNeighborRadius hN lam Z i := hr1.trans_le hr12
  have hq0 : 0 ≤ (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 := sq_nonneg _
  have hq1 : (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 ≤ 1 := by
    have : firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i ≤ 1 :=
      (div_le_one hr2).2 hr12
    exact pow_le_one₀ (div_nonneg hr1.le hr2.le) this
  set q := (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 with hq
  have hG := smearedKernel_add_log_firstNeighborRadius_ge hCg hlam Z i
  set g := smearedKernel lam (Z i - Z (nearestNeighbor Z i)) with hg
  have hCq : C₀ * q ≤ C₀ := mul_le_of_le_one_right hC₀.le hq1
  have hκ := le_abs_self kappa
  have hCg' := le_abs_self Cg
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hCg0 := abs_nonneg Cg
  have hκ0 := abs_nonneg (kappa)
  by_cases hcyc : nearestNeighbor Z (nearestNeighbor Z i) = i
  · -- the vertex `i` is on a 2-cycle
    have hτ : firstNeighborRadius lam Z i ≤
        min (secondNeighborRadius hN lam Z i) (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) :=
      firstNeighborRadius_le_min_secondNeighborRadius hN lam Z hcyc
    have hτpos : 0 < min (secondNeighborRadius hN lam Z i)
        (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) := hr1.trans_le hτ
    have hlogτ := Real.log_le_log hr1 hτ
    rw [logKernel_ofReal hτpos]
    simp only [hcyc, ne_eq, not_true_eq_false, ite_true, ite_false, sub_zero]
    have hii : charge i * charge i = 1 := by
      rcases charge_eq_one_or_neg_one i with h | h <;> simp [h]
    by_cases hs : charge i * charge (nearestNeighbor Z i) = 1
    · -- same-sign 2-cycle
      have hD : charge i * (charge i + charge (nearestNeighbor Z i)) = 2 := by
        rw [mul_add, hii, hs]
        norm_num
      have hnd : ¬ IsIsolatedDipole Z i := fun h => by
        have := ((isIsolatedDipole_iff Z i).1 h).2
        rw [hs] at this
        norm_num at this
      rw [hs, hD]
      have hB : ¬ (IsIsolatedDipole Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))) := fun h => hnd h.1
      rw [ite_eq_right hB]
      by_cases hE : IsIsolatedPair Z i ∧ IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
          IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))
      · rw [ite_eq_left ⟨hE.1, hnd, hE.2.1, hE.2.2⟩, ite_eq_left hE, Real.log_div hτpos.ne' hr1.ne']
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
        have h3 : C₀ / 2 * q ≤ C' * q :=
          mul_le_mul_of_nonneg_right (by linarith) hq0
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
    rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right hE, ite_eq_right hcyc, ite_eq_left hcyc, logKernel_ofReal hr2]
    have hlog2 := Real.log_le_log hr1 hr12
    linarith

/-! ### The comparison -/

open scoped Classical in
/-- **From Proposition 2.2 to Corollary 2.3** (source l. 466--489). For every constant `C₀` of
the right-hand side of Proposition 2.2 there is a constant `C'` such that the right-hand side of
Corollary 2.3 with constant `C'` is at most the right-hand side of Proposition 2.2 with constant
`C₀`, for every generic configuration. Both sides are written out as in the frozen statements
`proposition_2_2` and `corollary_2_3`. -/
theorem mino_rhs_ge_coromino_rhs :
    ∀ C₀ : ℝ, 0 < C₀ → ∃ C' : ℝ, 0 < C' ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam →
      ∀ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) → IsGeneric Z →
        (-(1 / 2) * ∑ i, smearedKernel lam (Z i - Z (nearestNeighbor Z i))
          + ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedPair Z i ∧ ¬ IsIsolatedDipole Z i ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
              (Real.log (min (secondNeighborRadius hN lam Z i)
                  (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) / firstNeighborRadius lam Z i)
                - C')
          - C' * ∑ i ∈ Finset.univ.filter (fun i => IsIsolatedDipole Z i ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z i) ∧
                IsIsolatedPair Z (secondNearestNeighbor hN Z (nearestNeighbor Z i))),
              (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2
          - C' * ((N : ℝ) - numComponents Z))
        ≤ (1 / 2) * (∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) = i,
            (charge i * charge (nearestNeighbor Z i) * smearedKernel lam (Z i - Z (nearestNeighbor Z i))
              - charge i * (charge i + charge (nearestNeighbor Z i)) *
                  (logKernel ((min (secondNeighborRadius hN lam Z i)
                    (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) : ℝ) : ℂ) + kappa)
              - C₀ * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2)
          - ∑ i ∈ Finset.univ.filter fun i => nearestNeighbor Z (nearestNeighbor Z i) ≠ i,
              (logKernel (secondNeighborRadius hN lam Z i) + kappa)) := by
  intro C₀ hC₀
  obtain ⟨Cg, hCg⟩ := exists_smearedKernel_ge
  set c : ℝ := |Cg| + Real.log 4 + |kappa| + C₀ / 2 with hc
  have hc0 : 0 < c := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    positivity
  refine ⟨151 * c, by positivity, ?_⟩
  intro N hN lam hlam Z _ hZ
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N ⊕ Fin N)))
    (fun i _ => termwise_le hN hC₀ hCg hc.ge (by linarith : c ≤ 151 * c) hlam Z i)
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
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hE] at hsum
  simp only [Finset.sum_filter]
  have h1 := mul_le_mul_of_nonneg_left hcardR hc0.le
  have h2 := mul_nonneg hc0.le hNK
  linarith

end TwoComponentCoulomb

end
