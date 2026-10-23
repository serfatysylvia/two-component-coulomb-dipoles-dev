/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.NearestNeighbor.General
public import TwoComponentCoulomb.UpperBound.PairAssignedEnergy
public import TwoComponentCoulomb.UpperBound.IsolatedRadial
public import TwoComponentCoulomb.UpperBound.IsolatedReduction
public import TwoComponentCoulomb.UpperBound.IsolatedIntegration
public import TwoComponentCoulomb.UpperBound.IsolatedOptimization
public import TwoComponentCoulomb.UpperBound.IsolatedSubcritical
public import TwoComponentCoulomb.UpperBound.IsolatedCrude
public import TwoComponentCoulomb.UpperBound.AuxNearestNeighbor
public import TwoComponentCoulomb.UpperBound.AuxTwoSpecies
import TwoComponentCoulomb.Integrals.Radial

/-!
# Proposition 3.8: quadratic error terms for isolated `2`-cycles

Source `source/dipole-formation.tex`, Proposition 3.8 (`prop:isolated`, l. 1171–1199) and its proof
(l. 1202–1333): the bounds (eq:n neutral), (eq:n neutral conv) and (eq:crude).

## The objects

A graph `γ ∈ G_{p,p₀}` of `p` `2`-cycles on a finite index set `ι` with `|ι| = 2p` is a
fixed-point-free involution `f : ι → ι`. The pairs are split into `p₀` neutral pairs and
`q = p - p₀` same-sign pairs; `S` is the `f`-invariant set of the `2q` vertices of the same-sign
pairs. As the source notes, the proof uses only the *assigned* pair terms, not the
charges, so `S` is arbitrary . The integral `I(γ)` of
the source (l. 1173–1175) is
`∫_{Λ^ι ∩ {nnMap key z = f}} exp (-β E(z)) dz`, with
`E = pairAssignedEnergy h3 key λ C S` (`F^nn_λ - C ∑_{i ∉ S} (r̃₁/r̃₂)² + ∑_{i ∈ S} (log (r̃₂(z_i) ∧
r̃₂(z_{φ₁(i)}))/r̃₁(z_i)) - C)`) and `Λ = box N`. The function `f(p₀)` of the source (l. 1177–1178)
is `p log p - p₀ log p₀ - q log q + C₀ q + max_γ log I(γ)`; a bound
`max_γ log I(γ) + (entropy) ≤ X` is stated, for every `γ`, as
`e^{entropy} · I(γ) ≤ e^X` (ruling R10). We take `0 log 0 = 0` (Mathlib's `Real.log 0 = 0`).

The indicator terms and the error rate are written as `if`-chains on `β`:
`(2 - β) log λ 1_{β>2} + log |log λ| 1_{β=2}` and
`ℓ^{-1} 1_{β=2} + λ^{β-2} 1_{2<β<4} + λ²ℓ² 1_{β=4} + λ²ℓ 1_{β>4}` (`ℓ = |log λ|`).

## Main results

* `TwoComponentCoulomb.isolated_n_neutral_conv`: **(eq:n neutral conv)**, with `c_β = 1`.
* `TwoComponentCoulomb.isolated_n_neutral`: **(eq:n neutral)**.
* `TwoComponentCoulomb.isolated_crude`: **(eq:crude)**. The source states it for `p < N/2`; the
  proof holds for every `2 ≤ p ≤ N`, and the statement is given in that generality.

The constants `C_β, c_β` are quantified before `ι, γ, N, p, p₀, λ` and depend only on `β`, `C`,
`C₀` ( ruling R11).

## Proof structure

Steps 3--4 of the proof (source l. 1269–1330) are proved once, for the integral over the
representatives on the right side of `(pred3)` with an arbitrary constant `C' > 0`. They are also
used by Step 4 of Proposition 3.9 (`UpperAssembly.exists_anchor_conv`, `exists_anchor_crude`) and
by the tilted blocks of Theorem 2 (`Fluctuations/TiltedIsolated.lean`).

Source: `source/dipole-formation.tex`, l. 1291–1332. The subcritical regimes remain
separate through optimization. The `β > 2` crude bound integrates constant factors,
while the critical extension retains its logarithmic and packing estimates.

* `IsolatedAssembly.refIntegral_le`: Steps 3--4 for the representatives relabelled by `Fin p`, the
  same-sign ones forming `T ⊆ Fin p`, for every `β ≥ 2`. The four ranges of `β` are
  `refIntegral_le_of_eq_two`, `refIntegral_le_of_two_lt_of_lt_four`, `refIntegral_le_of_eq_four`
  and `refIntegral_le_of_four_lt` (source l. 1291–1314, 1319–1330), with the quadratic gain
  `-p (q/p)²` included.
* `IsolatedAssembly.refSetIntegral_conv`, `IsolatedAssembly.refSetIntegral_crude`:
  (eq:n neutral conv) and (eq:crude) for the integral over a set `R` of representatives.
* The three main results: `(pred3)` (`lintegral_isolatedCell_le_gpRefSet`) followed by these.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

universe u

namespace TwoComponentCoulomb

namespace IsolatedAssembly

open AuxIntegration IsolatedIntegration IsolatedOptimization

/-! ### Algebraic helpers -/

theorem exp_add_log (A : ℝ) {m : ℝ} (hm : 0 < m) : Real.exp (A + Real.log m) = Real.exp A * m := by
  rw [Real.exp_add, Real.exp_log hm]

theorem exp_two_mul_add_log (A : ℝ) {m : ℝ} (hm : 0 < m) :
    Real.exp (2 * (A + Real.log m)) = Real.exp (2 * A) * m ^ 2 := by
  rw [mul_add, Real.exp_add, show (2 : ℝ) * Real.log m = Real.log (m ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

/-- `log (𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2})) = (2 - β) log λ 1_{β>2} + log ℓ 1_{β=2} + log 𝒵_β`. -/
theorem log_mul_isolatedScale {β : ℝ} (hβ : 2 ≤ β) {lam : ℝ} (hlam : 0 < lam)
    (hl1 : lam ≤ Real.exp (-1)) :
    Real.log (dipoleConstant β hβ * isolatedScale β hβ lam) =
      (if 2 < β then (2 - β) * Real.log lam else 0)
        + (if β = 2 then Real.log |Real.log lam| else 0) + Real.log (dipoleConstant β hβ) := by
  rw [Real.log_mul (dipoleConstant_pos β hβ).ne' (isolatedScale_pos hβ hlam hl1).ne']
  unfold isolatedScale
  rcases hβ.eq_or_lt with h | h
  · subst h
    simp only [lt_irrefl, ite_false, ite_true, zero_add]
    ring
  · simp only [h, h.ne', ite_true, ite_false, Real.log_rpow hlam]
    ring

/-- `e^E · (Z^p · (N^p · K^p e^x)) = e^{E + p log Z + p log N + p log K + x}`. -/
theorem ofReal_exp_mul_pow_eq {E Z K x : ℝ} {N : ℕ} (hZ : 0 < Z) (hK : 0 < K) (hN : (0 : ℝ) < N)
    (p : ℕ) :
    ENNReal.ofReal (Real.exp E) * (ENNReal.ofReal Z ^ p * ((N : ℝ≥0∞) ^ p *
        ENNReal.ofReal (K ^ p * Real.exp x))) =
      ENNReal.ofReal (Real.exp (E + p * Real.log Z + p * Real.log N + p * Real.log K + x)) := by
  rw [show (N : ℝ≥0∞) ^ p = ENNReal.ofReal ((N : ℝ) ^ p) by
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast],
    ← ENNReal.ofReal_pow hZ.le, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_nat_mul,
    Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hZ, Real.exp_log hN, Real.exp_log hK]
  ring

/-- `λ^{2 - 2b} (λ^b)² = λ²` and `λ^{2-b} λ^b = λ²`. -/
theorem rpow_two_sub_mul_sq {lam : ℝ} (hlam : 0 < lam) (b : ℝ) :
    lam ^ (2 - 2 * b) * (lam ^ b) ^ 2 = lam ^ 2 := by
  rw [← Real.rpow_natCast (lam ^ b), ← Real.rpow_mul hlam.le, ← Real.rpow_add hlam,
    show (2 - 2 * b + b * ((2 : ℕ) : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

theorem rpow_two_sub_mul {lam : ℝ} (hlam : 0 < lam) (b : ℝ) :
    lam ^ (2 - b) * lam ^ b = lam ^ 2 := by
  rw [← Real.rpow_add hlam]
  norm_num

/-- The error rate `r(λ)` of (eq:n neutral conv) is nonnegative for `λ ≥ 0`. -/
theorem rate_nonneg (β : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
      else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|) := by
  split_ifs
  · positivity
  · exact Real.rpow_nonneg hlam _
  · positivity
  · positivity

/-- The factor of `(pred3)` with `ENNReal.ofReal` taken inside the case split. -/
theorem ofReal_ite_le (P : Prop) [Decidable P] (x y : ℝ) :
    ENNReal.ofReal (if P then x else 1 + y) ≤
      if P then ENNReal.ofReal x else 1 + ENNReal.ofReal y := by
  split_ifs
  · exact le_rfl
  · exact ENNReal.ofReal_add_le.trans_eq (by rw [ENNReal.ofReal_one])

/-- The entropy of the two pair types is at most `p log 2`, as in the current
manuscript, line 1375. The formula includes empty types with `0 log 0 = 0`. -/
theorem entropy_le_log_two {p p₀ q : ℕ} (hpq : p₀ + q = p) (hp : 0 < p) :
    p * Real.log p - p₀ * Real.log p₀ - q * Real.log q ≤ p * Real.log 2 := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have h := mul_log_add_le (Nat.cast_nonneg p₀) (Nat.cast_nonneg q)
  have hpq' : (p₀ : ℝ) + q = p := by exact_mod_cast hpq
  rw [hpq', Real.log_div hP.ne' (by norm_num)] at h
  linarith

/-! ### Steps 3--4 for the representatives, in the four ranges of `β` -/

/-- **Steps 3--4 for `β = 2`** : Proposition 3.6 with
`β = 0`, `δ' = 1` on the `k + q` selected representatives, and the optimization gives the error
`K ℓ^{-1}`, with the quadratic gain `-p (q/p)²`. (Internal.) -/
theorem refIntegral_le_of_eq_two {β : ℝ} (hβ : 2 ≤ β) (h2 : β = 2) {C' : ℝ} (hC' : 0 < C')
    (C₀ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N p p₀ q : ℕ) [Nontrivial (Fin p)] (T : Finset (Fin p)), 2 ≤ p →
      p ≤ N → (N : ℝ) ≤ 2 * p → p₀ + q = p → T.card = q →
      ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
            + C₀ * q)) *
          (ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^ p *
            ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∏ i, (if i ∈ T then
              ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam z i))
              else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam z i)))) ≤
        ENNReal.ofReal (Real.exp (p * Real.log N
          + p * Real.log (dipoleConstant β hβ * isolatedScale β hβ lam)
          - p * ((q : ℝ) / p) ^ 2 + K * p * |Real.log lam|⁻¹ + Real.log (N + 1))) := by
  obtain ⟨C₆, -, hB6⟩ := lintegral_auxk_finset_abs
  refine ⟨Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆)) * C' ^ 2
    + Real.exp (2 + Real.log 2 + |C₀| + C₆) * C', by positivity, ?_⟩
  intro N p p₀ q _ T hp2 hpN hN hpq hT lam hlam hl1
  have hp : 0 < p := by omega
  have hℓ := one_le_abs_log hlam hl1
  have hm : 0 < C' / |Real.log lam| := div_pos hC' (by linarith)
  have hZ : 0 < dipoleConstant β hβ * isolatedScale β hβ lam :=
    mul_pos (dipoleConstant_pos β hβ) (isolatedScale_pos hβ hlam hl1)
  have hTc : Tᶜ.card = p₀ := by rw [Finset.card_compl, Fintype.card_fin, hT]; omega
  have hW := lintegral_prod_ite_le N lam T
    (a := fun ρ => ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ))
    (b := fun ρ => ENNReal.ofReal (C' * isolatedTail β hβ lam ρ))
    (measurable_sourceWeight 0 0 1 lam) (measurable_sourceWeight 0 0 1 lam)
    (fun ρ _ => ofReal_isolatedPhi_le_of_eq_two hβ h2 hC'.le ρ)
    (fun ρ _ => ofReal_isolatedTail_le_of_eq_two hβ h2 hC'.le ρ)
    (fun k => ENNReal.ofReal (Real.exp (p * Real.log N + C₆ * ((k + q : ℕ) : ℝ)
      + ((k + q : ℕ) : ℝ) / 2 * (fun _ : ℕ => (0 : ℝ)) (k + q))))
    (fun A hA => by
      have hAT : Disjoint A T :=
        Finset.disjoint_left.2 fun x hxA hxT => Finset.mem_compl.1 (hA hxA) hxT
      simp_rw [← Finset.prod_union hAT]
      refine (hB6 N p (A.card + q) (A ∪ T) (by rw [Finset.card_union_of_disjoint hAT, hT])
        hpN hN lam hlam hl1).trans (le_of_eq ?_)
      simp)
  rw [hTc, hT] at hW
  have hfin := ofReal_exp_mul_le_single hpq hp hpN C₀ C₆ hZ hm one_pos one_pos (fun _ => 0)
    (fun k _ => Real.log_nonneg (le_max_of_le_right (by norm_num))) hW
  refine hfin.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  rw [exp_two_mul_add_log _ hm, exp_add_log _ hm]
  have hinv0 : 0 ≤ |Real.log lam|⁻¹ := by positivity
  have hinv : |Real.log lam|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hℓ
  have hsq : (C' / |Real.log lam|) ^ 2 ≤ C' ^ 2 * |Real.log lam|⁻¹ := by
    rw [div_pow, div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hinv0 hinv two_ne_zero) (sq_nonneg C')
  have hrate : 1 * (Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆)) * (C' / |Real.log lam|) ^ 2)
      + 1 * (Real.exp (2 + Real.log 2 + |C₀| + C₆) * (C' / |Real.log lam|)) ≤
      (Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆)) * C' ^ 2
        + Real.exp (2 + Real.log 2 + |C₀| + C₆) * C') * |Real.log lam|⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_left hsq (Real.exp_pos (2 * (2 + Real.log 2 + |C₀| + C₆))).le
    have e : Real.exp (2 + Real.log 2 + |C₀| + C₆) * (C' / |Real.log lam|) =
        Real.exp (2 + Real.log 2 + |C₀| + C₆) * C' * |Real.log lam|⁻¹ := by
      rw [div_eq_mul_inv]; ring
    linarith
  gcongr _ + ?_ + _
  exact (mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg p)).trans_eq (by ring)

/-- **Steps 3--4 for `2 < β < 4`** (source l. 1269–1300, 1320–1324, 1329–1330):
Proposition 3.6 with parameter `2b`, `b = β - 2`, on the `k + q` selected representatives, and
the optimization gives the error `K λ^{β-2}` (in the three regimes `b < 1`, `b = 1`, `b > 1`).
(Internal.) -/
theorem refIntegral_le_of_two_lt_of_lt_four {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) (h4 : β < 4)
    {C' : ℝ} (hC' : 0 < C') (C₀ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N p p₀ q : ℕ) [Nontrivial (Fin p)] (T : Finset (Fin p)), 2 ≤ p →
      p ≤ N → (N : ℝ) ≤ 2 * p → p₀ + q = p → T.card = q →
      ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
            + C₀ * q)) *
          (ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^ p *
            ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∏ i, (if i ∈ T then
              ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam z i))
              else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam z i)))) ≤
        ENNReal.ofReal (Real.exp (p * Real.log N
          + p * Real.log (dipoleConstant β hβ * isolatedScale β hβ lam)
          - p * ((q : ℝ) / p) ^ 2 + K * p * lam ^ (β - 2) + Real.log (N + 1))) := by
  have hb : (0 : ℝ) ≤ 2 * (β - 2) := by linarith
  obtain ⟨C₆, -, hB6⟩ := lintegral_auxk_finset_le (2 * (β - 2)) hb 0 0 (Or.inl rfl) (Or.inl rfl)
  refine ⟨Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆)) * C' ^ 2
    + Real.exp (2 + Real.log 2 + |C₀| + C₆) * C', by positivity, ?_⟩
  intro N p p₀ q _ T hp2 hpN hN hpq hT lam hlam hl1
  have hp : 0 < p := by omega
  have ht : 0 < lam ^ (β - 2) := Real.rpow_pos_of_pos hlam _
  have hm : 0 < C' * lam ^ (β - 2) := by positivity
  have hZ : 0 < dipoleConstant β hβ * isolatedScale β hβ lam :=
    mul_pos (dipoleConstant_pos β hβ) (isolatedScale_pos hβ hlam hl1)
  have hTc : Tᶜ.card = p₀ := by rw [Finset.card_compl, Fintype.card_fin, hT]; omega
  have hW := lintegral_prod_ite_le N lam T
    (a := fun ρ => ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ))
    (b := fun ρ => ENNReal.ofReal (C' * isolatedTail β hβ lam ρ))
    (measurable_sourceWeight (2 * (β - 2)) 0 0 lam)
    (measurable_sourceWeight (2 * (β - 2)) 0 0 lam)
    (fun ρ hρ => ofReal_isolatedPhi_le_of_two_lt_of_lt_four hβ h2 h4 hlam hC'.le hρ)
    (fun ρ hρ => ofReal_isolatedTail_le_of_two_lt hβ h2 hlam hC'.le hρ)
    (fun k => ENNReal.ofReal (Real.exp (p * Real.log N + C₆ * ((k + q : ℕ) : ℝ)
      + ((k + q : ℕ) : ℝ) / 2 * (fun M => gammaBeta (2 * (β - 2)) hb 0 lam M N) (k + q))))
    (fun A hA => by
      have hAT : Disjoint A T :=
        Finset.disjoint_left.2 fun x hxA hxT => Finset.mem_compl.1 (hA hxA) hxT
      simp_rw [← Finset.prod_union hAT]
      exact hB6 N p (A.card + q) (A ∪ T) (by rw [Finset.card_union_of_disjoint hAT, hT])
        hpN hN lam hlam hl1)
  rw [hTc, hT] at hW
  by_cases h3 : β < 3
  · have hzero : ∀ M, gammaBeta (2 * (β - 2)) hb 0 lam M N = 0 :=
      fun _ => gammaBeta_of_lt_two (by linarith) _ _
    simp only [hzero, mul_zero, add_zero] at hW
    have hfin := IsolatedSubcritical.ofReal_exp_mul_le hpq hp hpN C₀ C₆ hZ hm hW
    refine hfin.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    rw [exp_add_log _ hm]
    have hrate : Real.exp (2 + Real.log 2 + |C₀| + C₆) * (C' * lam ^ (β - 2)) ≤
        (Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆)) * C' ^ 2 +
          Real.exp (2 + Real.log 2 + |C₀| + C₆) * C') * lam ^ (β - 2) := by
      nlinarith [mul_nonneg
        (by positivity : 0 ≤ Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆)) * C' ^ 2) ht.le]
    gcongr _ + ?_ + _
    exact (mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg p)).trans_eq (by ring)
  have hfin := ofReal_exp_mul_le_single hpq hp hpN C₀ C₆ hZ hm
    (subcriticalCycleScale_pos β hlam hl1) one_pos
    (fun M => gammaBeta (2 * (β - 2)) hb 0 lam M N)
    (fun k _ => gammaBeta_le_of_lt_four h4 hb hlam hp hpN) hW
  refine hfin.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  rw [exp_two_mul_add_log _ hm, exp_add_log _ hm]
  have hbranch := subcriticalCycleScale_mul_sq_le h2 h4 hlam hl1
  have hrate : subcriticalCycleScale β lam *
      (Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆)) * (C' * lam ^ (β - 2)) ^ 2)
      + 1 * (Real.exp (2 + Real.log 2 + |C₀| + C₆) * (C' * lam ^ (β - 2))) ≤
      (Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆)) * C' ^ 2
        + Real.exp (2 + Real.log 2 + |C₀| + C₆) * C') * lam ^ (β - 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hbranch
      (by positivity : 0 ≤ Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆)) * C' ^ 2)]
  gcongr _ + ?_ + _
  exact (mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg p)).trans_eq (by ring)

/-- **Steps 3--4 for `β = 4`** (source l. 1301–1306, 1325–1326, 1329–1330): the same-sign
factors are enlarged by `1 + log (ρ_j/λ) ≥ 1`, Proposition 3.6 with parameter `4`, `δ = 1`, on the
`k + q` selected representatives, and the optimization gives the error `K λ² ℓ²`. (Internal.) -/
theorem refIntegral_le_of_eq_four {β : ℝ} (hβ : 2 ≤ β) (h4 : β = 4) {C' : ℝ} (hC' : 0 < C')
    (C₀ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N p p₀ q : ℕ) [Nontrivial (Fin p)] (T : Finset (Fin p)), 2 ≤ p →
      p ≤ N → (N : ℝ) ≤ 2 * p → p₀ + q = p → T.card = q →
      ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
            + C₀ * q)) *
          (ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^ p *
            ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∏ i, (if i ∈ T then
              ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam z i))
              else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam z i)))) ≤
        ENNReal.ofReal (Real.exp (p * Real.log N
          + p * Real.log (dipoleConstant β hβ * isolatedScale β hβ lam)
          - p * ((q : ℝ) / p) ^ 2 + K * p * (lam ^ 2 * |Real.log lam| ^ 2)
          + Real.log (N + 1))) := by
  obtain ⟨C₆, -, hB6⟩ := lintegral_auxk_finset_le 4 (by norm_num) 1 0 (Or.inr ⟨rfl, rfl⟩)
    (Or.inl rfl)
  refine ⟨Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆)) * C' ^ 2
    + Real.exp (2 + Real.log 2 + |C₀| + C₆) * C', by positivity, ?_⟩
  intro N p p₀ q _ T hp2 hpN hN hpq hT lam hlam hl1
  have hp : 0 < p := by omega
  have hℓ := one_le_abs_log hlam hl1
  have hm : 0 < C' * lam ^ 2 := by positivity
  have hZ : 0 < dipoleConstant β hβ * isolatedScale β hβ lam :=
    mul_pos (dipoleConstant_pos β hβ) (isolatedScale_pos hβ hlam hl1)
  have hTc : Tᶜ.card = p₀ := by rw [Finset.card_compl, Fintype.card_fin, hT]; omega
  have hW := lintegral_prod_ite_le N lam T
    (a := fun ρ => ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ))
    (b := fun ρ => ENNReal.ofReal (C' * isolatedTail β hβ lam ρ))
    (measurable_sourceWeight 4 1 0 lam) (measurable_sourceWeight 4 1 0 lam)
    (fun ρ hρ => ofReal_isolatedPhi_le_of_eq_four hβ h4 hlam hC'.le hρ)
    (fun ρ hρ => ofReal_isolatedTail_le_of_eq_four hβ h4 hlam hC'.le hρ)
    (fun k => ENNReal.ofReal (Real.exp (p * Real.log N + C₆ * ((k + q : ℕ) : ℝ)
      + ((k + q : ℕ) : ℝ) / 2 * (fun M => gammaBeta 4 (by norm_num) 1 lam M N) (k + q))))
    (fun A hA => by
      have hAT : Disjoint A T :=
        Finset.disjoint_left.2 fun x hxA hxT => Finset.mem_compl.1 (hA hxA) hxT
      simp_rw [← Finset.prod_union hAT]
      exact hB6 N p (A.card + q) (A ∪ T) (by rw [Finset.card_union_of_disjoint hAT, hT])
        hpN hN lam hlam hl1)
  rw [hTc, hT] at hW
  have hfin := ofReal_exp_mul_le_single hpq hp hpN C₀ C₆ hZ hm
    (by positivity : (0 : ℝ) < (lam ^ 2)⁻¹) (by positivity : (0 : ℝ) < |Real.log lam| ^ 2)
    (fun M => gammaBeta 4 (by norm_num) 1 lam M N)
    (fun k _ => gammaBeta_four_le _ hlam hl1 hp hpN) hW
  refine hfin.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  rw [exp_two_mul_add_log _ hm, exp_add_log _ hm]
  set E₂ := Real.exp (2 * (2 + Real.log 2 + |C₀| + C₆)) with hE₂
  set E₁ := Real.exp (2 + Real.log 2 + |C₀| + C₆) with hE₁
  have hE₂0 : 0 < E₂ := Real.exp_pos _
  have hl2 : 1 ≤ |Real.log lam| ^ 2 := one_le_pow₀ hℓ
  have hrate : (lam ^ 2)⁻¹ * (E₂ * (C' * lam ^ 2) ^ 2) + |Real.log lam| ^ 2 * (E₁ * (C' * lam ^ 2))
      ≤ (E₂ * C' ^ 2 + E₁ * C') * (lam ^ 2 * |Real.log lam| ^ 2) := by
    have e : (lam ^ 2)⁻¹ * (E₂ * (C' * lam ^ 2) ^ 2) = E₂ * C' ^ 2 * lam ^ 2 := by
      field_simp
    rw [e]
    have : E₂ * C' ^ 2 * lam ^ 2 ≤ E₂ * C' ^ 2 * lam ^ 2 * |Real.log lam| ^ 2 :=
      le_mul_of_one_le_right (by positivity) hl2
    linarith only [this]
  gcongr _ + ?_ + _
  exact (mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg p)).trans_eq (by ring)

/-- **Steps 3--4 for `β > 4`** (source l. 1307–1314, 1327, 1329–1330): Proposition 3.7 with the
`k` selected neutral factors (parameter `4`, `δ = 0`) and the `q` same-sign factors (parameter
`2b`, `b = β - 2`), and the optimization gives the error `K λ² ℓ` (`K λ²` from the `x₀` terms and
`K λ² ℓ` from the `x₁` terms). (Internal.) -/
theorem refIntegral_le_of_four_lt {β : ℝ} (hβ : 2 ≤ β) (h4 : 4 < β) {C' : ℝ} (hC' : 0 < C')
    (C₀ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N p p₀ q : ℕ) [Nontrivial (Fin p)] (T : Finset (Fin p)), 2 ≤ p →
      p ≤ N → (N : ℝ) ≤ 2 * p → p₀ + q = p → T.card = q →
      ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
            + C₀ * q)) *
          (ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^ p *
            ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∏ i, (if i ∈ T then
              ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam z i))
              else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam z i)))) ≤
        ENNReal.ofReal (Real.exp (p * Real.log N
          + p * Real.log (dipoleConstant β hβ * isolatedScale β hβ lam)
          - p * ((q : ℝ) / p) ^ 2 + K * p * (lam ^ 2 * |Real.log lam|)
          + Real.log (N + 1))) := by
  have hb' : 4 < 2 * (β - 2) := by linarith
  have hb : (0 : ℝ) ≤ 2 * (β - 2) := by linarith
  obtain ⟨C₇, -, hB7⟩ := lintegral_twoSpecies_finset_le (2 * (β - 2)) hb'
  refine ⟨2 * Real.exp (2 * (2 + |C₀| + C₇)) * C' ^ 2 + 2 * Real.exp (2 + |C₀| + C₇) * C',
    by positivity, ?_⟩
  intro N p p₀ q _ T hp2 hpN hN hpq hT lam hlam hl1
  have hp : 0 < p := by omega
  have hℓ := one_le_abs_log hlam hl1
  have hm₁ : 0 < C' * lam ^ 2 := by positivity
  have hm₂ : 0 < C' * lam ^ (β - 2) := mul_pos hC' (Real.rpow_pos_of_pos hlam _)
  have hZ : 0 < dipoleConstant β hβ * isolatedScale β hβ lam :=
    mul_pos (dipoleConstant_pos β hβ) (isolatedScale_pos hβ hlam hl1)
  have hTc : Tᶜ.card = p₀ := by rw [Finset.card_compl, Fintype.card_fin, hT]; omega
  have hW := lintegral_prod_ite_le N lam T
    (a := fun ρ => ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ))
    (b := fun ρ => ENNReal.ofReal (C' * isolatedTail β hβ lam ρ))
    (measurable_sourceWeight 4 0 0 lam) (measurable_sourceWeight (2 * (β - 2)) 0 0 lam)
    (fun ρ hρ => ofReal_isolatedPhi_le_of_four_lt hβ h4 hlam hC'.le hρ)
    (fun ρ hρ => ofReal_isolatedTail_le_of_two_lt hβ (by linarith) hlam hC'.le hρ)
    (fun k => ENNReal.ofReal (Real.exp (p * Real.log N + C₇ * ((k : ℝ) + q)
      + k / 2 * (fun k : ℕ => gammaBeta 4 (by norm_num) 0 lam k N) k
      + q / 2 * gammaBeta (2 * (β - 2)) hb 0 lam q N)))
    (fun A hA => by
      have hAT : Disjoint A T :=
        Finset.disjoint_left.2 fun x hxA hxT => Finset.mem_compl.1 (hA hxA) hxT
      exact hB7 0 (Or.inl rfl) N p A.card q A T hAT rfl hT hpN hN lam hlam hl1)
  rw [hTc, hT] at hW
  have hfin := ofReal_exp_mul_le_two hpq hp hpN C₀ C₇ hZ hm₁ hm₂
    (by positivity : (0 : ℝ) < (lam ^ 2)⁻¹) (by linarith : (0 : ℝ) < |Real.log lam|)
    (Real.rpow_pos_of_pos hlam (2 - 2 * (β - 2))) (Real.rpow_pos_of_pos hlam (4 - β))
    (fun k : ℕ => gammaBeta 4 (by norm_num) 0 lam k N) (gammaBeta (2 * (β - 2)) hb 0 lam q N)
    (fun k _ => gammaBeta_four_zero_le _ hlam hl1 hp hpN)
    (gammaBeta_four_lt_le h4 hb hlam hp hpN) hW
  refine hfin.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  rw [exp_two_mul_add_log _ hm₁, exp_add_log _ hm₁, exp_two_mul_add_log _ hm₂,
    exp_add_log _ hm₂]
  set E₂ := Real.exp (2 * (2 + |C₀| + C₇)) with hE₂
  set E₁ := Real.exp (2 + |C₀| + C₇) with hE₁
  have hE₂0 : 0 < E₂ := Real.exp_pos _
  have hE₁0 : 0 < E₁ := Real.exp_pos _
  have e1 : (lam ^ 2)⁻¹ * (E₂ * (C' * lam ^ 2) ^ 2) = E₂ * C' ^ 2 * lam ^ 2 := by
    field_simp
  have e2 : lam ^ (2 - 2 * (β - 2)) * (E₂ * (C' * lam ^ (β - 2)) ^ 2) = E₂ * C' ^ 2 * lam ^ 2 := by
    rw [mul_pow, ← rpow_two_sub_mul_sq hlam (β - 2)]
    ring
  have e3 : lam ^ (4 - β) * (E₁ * (C' * lam ^ (β - 2))) = E₁ * C' * lam ^ 2 := by
    rw [show (4 : ℝ) - β = 2 - (β - 2) by ring, ← rpow_two_sub_mul hlam (β - 2)]
    ring
  have hrate : (lam ^ 2)⁻¹ * (E₂ * (C' * lam ^ 2) ^ 2) + |Real.log lam| * (E₁ * (C' * lam ^ 2))
      + (lam ^ (2 - 2 * (β - 2)) * (E₂ * (C' * lam ^ (β - 2)) ^ 2)
        + lam ^ (4 - β) * (E₁ * (C' * lam ^ (β - 2)))) ≤
      (2 * E₂ * C' ^ 2 + 2 * E₁ * C') * (lam ^ 2 * |Real.log lam|) := by
    rw [e1, e2, e3]
    have h1 : E₂ * C' ^ 2 * lam ^ 2 ≤ E₂ * C' ^ 2 * lam ^ 2 * |Real.log lam| :=
      le_mul_of_one_le_right (by positivity) hℓ
    have h2 : E₁ * C' * lam ^ 2 ≤ E₁ * C' * lam ^ 2 * |Real.log lam| :=
      le_mul_of_one_le_right (by positivity) hℓ
    linarith only [h1, h2]
  gcongr _ + ?_ + _
  exact (mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg p)).trans_eq (by ring)

/-- **Steps 3--4 of Proposition 3.8 for the representatives** (source l. 1269–1330): for `β ≥ 2`,
`C' > 0` and `C₀ ∈ ℝ` there is `K > 0` (depending only on `β`, `C'`, `C₀`) such that for
`2 ≤ p ≤ N ≤ 2p`, `p = p₀ + q`, `T ⊆ Fin p` with `|T| = q` and `0 < λ ≤ e^{-1}`,
`e^{p log p - p₀ log p₀ - q log q + C₀ q} (𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}))^p
  ∫_{Λ^p} ∏_{i ∈ T} C' τ_β(ρ_i) ∏_{i ∉ T} (1 + C' φ_β(ρ_i))
  ≤ exp (p log N + p log (𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2})) - p (q/p)² + K p r(λ) + log (N + 1))`,
with the error rate `r(λ)` of (eq:n neutral conv). This is the single proof of Steps 3--4; the
integral over the representatives of `(pred3)` is relabelled to this form by
`IsolatedIntegration.exists_relabel_ref`. (Internal.) -/
theorem refIntegral_le {β : ℝ} (hβ : 2 ≤ β) {C' : ℝ} (hC' : 0 < C') (C₀ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N p p₀ q : ℕ) [Nontrivial (Fin p)] (T : Finset (Fin p)), 2 ≤ p →
      p ≤ N → (N : ℝ) ≤ 2 * p → p₀ + q = p → T.card = q →
      ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
            + C₀ * q)) *
          (ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^ p *
            ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∏ i, (if i ∈ T then
              ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam z i))
              else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam z i)))) ≤
        ENNReal.ofReal (Real.exp (p * Real.log N
          + p * Real.log (dipoleConstant β hβ * isolatedScale β hβ lam)
          - p * ((q : ℝ) / p) ^ 2
          + K * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
              else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|)
          + Real.log (N + 1))) := by
  rcases hβ.eq_or_lt with h2 | h2
  · obtain ⟨K, hK, h⟩ := refIntegral_le_of_eq_two hβ h2.symm hC' C₀
    refine ⟨K, hK, fun N p p₀ q _ T hp2 hpN hN hpq hT lam hlam hl1 => ?_⟩
    rw [ite_eq_left h2.symm]
    exact h N p p₀ q T hp2 hpN hN hpq hT lam hlam hl1
  rcases lt_trichotomy β 4 with h4 | h4 | h4
  · obtain ⟨K, hK, h⟩ := refIntegral_le_of_two_lt_of_lt_four hβ h2 h4 hC' C₀
    refine ⟨K, hK, fun N p p₀ q _ T hp2 hpN hN hpq hT lam hlam hl1 => ?_⟩
    rw [ite_eq_right h2.ne', ite_eq_left h4]
    exact h N p p₀ q T hp2 hpN hN hpq hT lam hlam hl1
  · obtain ⟨K, hK, h⟩ := refIntegral_le_of_eq_four hβ h4 hC' C₀
    refine ⟨K, hK, fun N p p₀ q _ T hp2 hpN hN hpq hT lam hlam hl1 => ?_⟩
    rw [ite_eq_right h2.ne', ite_eq_right h4.not_lt, ite_eq_left h4]
    exact h N p p₀ q T hp2 hpN hN hpq hT lam hlam hl1
  · obtain ⟨K, hK, h⟩ := refIntegral_le_of_four_lt hβ h4 hC' C₀
    refine ⟨K, hK, fun N p p₀ q _ T hp2 hpN hN hpq hT lam hlam hl1 => ?_⟩
    rw [ite_eq_right h2.ne', ite_eq_right (not_lt.2 h4.le), ite_eq_right h4.ne']
    exact h N p p₀ q T hp2 hpN hN hpq hT lam hlam hl1

/-! ### (eq:n neutral conv) and (eq:crude) for a set of representatives -/

open scoped Classical in
/-- **(eq:n neutral conv) for the integral over the representatives** (source l. 1188–1189, 1269–1330): for `β ≥ 2`, `C' > 0` and `C₀` there are `C_β, c_β > 0` such that for every set `R` of
representatives (`|R| = p`, `2 ≤ p ≤ N ≤ 2p`) of a fixed-point-free involution `f`, every
`f`-invariant `S` with `|S| = 2(p - p₀)` and `0 < λ ≤ e⁻¹`,
`e^{entropy} (𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}))^p W
  ≤ exp (p (log N + (2-β) log λ 1_{β>2} + log ℓ 1_{β=2} + log 𝒵_β) - c_β p ((p-p₀)/p)²
    + C_β p r(λ) + C_β log (N + 1))`,
where `W` is the integral over the representatives of the right side of `(pred3)` with the constant
`C'`. Steps 3--4 (`refIntegral_le`) after relabelling, with `C_β = max K 1`, `c_β = 1`. -/
theorem refSetIntegral_conv {β : ℝ} (hβ : 2 ≤ β) {C' : ℝ} (hC' : 0 < C') (C₀ : ℝ) :
    ∃ Cβ cβ : ℝ, 0 < Cβ ∧ 0 < cβ ∧ ∀ (ι : Type u) [Fintype ι] (f : ι → ι) (R : Set ι)
      [DecidablePred (· ∈ R)] [Nontrivial {i // i ∈ R}], (∀ i, f (f i) = i) →
      (∀ i, i ∈ R ↔ f i ∉ R) → ∀ (S : Finset ι), (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N p p₀ : ℕ),
      Fintype.card {i // i ∈ R} = p → 2 ≤ p → p ≤ N → (N : ℝ) ≤ 2 * p → p₀ ≤ p →
      S.card = 2 * (p - p₀) → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
            - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀))) *
          (ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^ p *
            ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
              ∏ j : {i // i ∈ R}, ENNReal.ofReal (if (j : ι) ∈ S then
                C' * isolatedTail β hβ lam (nnRadius lam w j)
                else 1 + C' * isolatedPhi β hβ lam (nnRadius lam w j))) ≤
        ENNReal.ofReal (Real.exp (p * (Real.log N
                + (if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0)
                + Real.log (dipoleConstant β hβ))
              - cβ * p * (((p : ℝ) - p₀) / p) ^ 2
              + Cβ * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
                  else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|)
              + Cβ * Real.log (N + 1))) := by
  obtain ⟨K, hK, hJ⟩ := refIntegral_le hβ hC' C₀
  refine ⟨max K 1, 1, lt_max_of_lt_right one_pos, one_pos, ?_⟩
  intro ι _ f R _ _ hf2 hRf S hS N p p₀ hR hp2 hpN hN hp₀ hSq lam hlam hl1
  have : Nontrivial (Fin p) := Fin.nontrivial_iff_two_le.2 hp2
  obtain ⟨T, hT, hrel⟩ := exists_relabel_ref hf2 hRf hS hR hSq N lam
  have h := hJ N p p₀ (p - p₀) T hp2 hpN hN (by omega) hT lam hlam hl1
  rw [← hrel (fun ρ => ENNReal.ofReal (C' * isolatedTail β hβ lam ρ))
    (fun ρ => 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ)), Nat.cast_sub hp₀] at h
  refine (mul_le_mul_right (mul_le_mul_right (lintegral_mono fun w =>
    Finset.prod_le_prod fun j _ => ofReal_ite_le _ _ _) _) _).trans
    (h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)))
  rw [log_mul_isolatedScale hβ hlam hl1]
  have hr0 := rate_nonneg β hlam.le
  set r := (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
    else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|) with hr
  have hP : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hlogN : 0 ≤ Real.log (N + 1) := Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have h1 : K * p * r ≤ max K 1 * p * r :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hP) hr0
  have h2 : Real.log (N + 1) ≤ max K 1 * Real.log (N + 1) :=
    le_mul_of_one_le_left hlogN (le_max_right _ _)
  have e : (p : ℝ) * (Real.log N + (if 2 < β then (2 - β) * Real.log lam else 0)
      + (if β = 2 then Real.log |Real.log lam| else 0) + Real.log (dipoleConstant β hβ)) =
      p * Real.log N + p * ((if 2 < β then (2 - β) * Real.log lam else 0)
        + (if β = 2 then Real.log |Real.log lam| else 0) + Real.log (dipoleConstant β hβ)) := by
    ring
  rw [e]
  linarith

open scoped Classical in
/-- **(eq:crude) for the integral over the representatives** :
for `β ≥ 2`, `C' > 0` and `C₀` there is `C_β > 0` such that for every set `R` of `p ≤ N`
representatives, every `S` and `0 < λ ≤ e⁻¹`,
`e^{entropy} (𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}))^p W
  ≤ exp (p (log N + (2-β) log λ 1_{β>2} + log ℓ 1_{β=2}) + C_β N)`,
`W` the integral over the representatives of the right side of `(pred3)` with the constant `C'`
(`IsolatedCrude.lintegral_ref_le_crude` and the crude entropy bound). -/
theorem refSetIntegral_crude {β : ℝ} (hβ : 2 ≤ β) {C' : ℝ} (hC' : 0 < C') (C₀ : ℝ) :
    ∃ Cβ : ℝ, 0 < Cβ ∧ ∀ (ι : Type u) [Fintype ι] (R : Set ι) [DecidablePred (· ∈ R)]
      [Nontrivial {i // i ∈ R}] (S : Finset ι) (N p p₀ : ℕ),
      Fintype.card {i // i ∈ R} = p → p ≤ N → p₀ ≤ p → ∀ lam : ℝ, 0 < lam →
      lam ≤ Real.exp (-1) →
        ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
            - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀))) *
          (ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^ p *
            ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
              ∏ j : {i // i ∈ R}, ENNReal.ofReal (if (j : ι) ∈ S then
                C' * isolatedTail β hβ lam (nnRadius lam w j)
                else 1 + C' * isolatedPhi β hβ lam (nnRadius lam w j))) ≤
        ENNReal.ofReal (Real.exp (p * (Real.log N
                + (if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0))
              + Cβ * N)) := by
  set K : ℝ := 1 + 2 * C' with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; linarith
  refine ⟨1 + |C₀| + |Real.log (dipoleConstant β hβ)| + Real.log K + 2, by
    have := Real.log_nonneg hK
    positivity, ?_⟩
  intro ι _ R _ _ S N p p₀ hR hpN hp₀ lam hlam hl1
  have hp2 : 2 ≤ p := by
    rw [← hR]
    exact Fintype.one_lt_card_iff_nontrivial.2 inferInstance
  have hW : (∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
      ∏ j : {i // i ∈ R}, ENNReal.ofReal (if (j : ι) ∈ S then
        C' * isolatedTail β hβ lam (nnRadius lam w j)
        else 1 + C' * isolatedPhi β hβ lam (nnRadius lam w j))) ≤
      (N : ℝ≥0∞) ^ Fintype.card {i // i ∈ R} *
        ENNReal.ofReal (K ^ Fintype.card {i // i ∈ R} * Real.exp (2 * N)) := by
    rcases hβ.eq_or_lt with h2 | h2
    · exact IsolatedCrude.lintegral_ref_le_crude (κ := {i // i ∈ R}) (N := N)
        (by rw [hR]; exact hpN) hlam hl1 hC'.le
        (fun j ρ => if (j : ι) ∈ S then C' * isolatedTail β hβ lam ρ
          else 1 + C' * isolatedPhi β hβ lam ρ)
        (fun j ρ hρ => IsolatedCrude.factor_le hβ hlam hl1 hC'.le hρ _)
    · -- Source, line 1332: bound each factor by `1 + C'` and integrate the box.
      refine (IsolatedCrude.lintegral_ref_le_of_two_lt N hβ h2 hlam hl1 hC'.le
        {j : {i // i ∈ R} | (j : ι) ∈ S}).trans ?_
      gcongr
      calc (1 + C') ^ Fintype.card {i // i ∈ R}
          ≤ K ^ Fintype.card {i // i ∈ R} := by gcongr; dsimp [K]; linarith
        _ ≤ K ^ Fintype.card {i // i ∈ R} * Real.exp (2 * N) :=
          le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
  rw [hR] at hW
  have hp : 0 < p := by omega
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have hPN : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hN0 : (0 : ℝ) < N := hP.trans_le hPN
  have hZ : 0 < dipoleConstant β hβ * isolatedScale β hβ lam :=
    mul_pos (dipoleConstant_pos β hβ) (isolatedScale_pos hβ hlam hl1)
  have hent₀ := entropy_le_log_two (p := p) (p₀ := p₀) (q := p - p₀) (by omega) hp
  rw [Nat.cast_sub hp₀] at hent₀
  have hent : p * Real.log p - p₀ * Real.log p₀
      - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀) ≤
      (1 + |C₀|) * p := by
    have hq : 0 ≤ (p : ℝ) - p₀ := sub_nonneg.2 (by exact_mod_cast hp₀)
    have hqp : (p : ℝ) - p₀ ≤ p := sub_le_self _ (Nat.cast_nonneg _)
    have hlog : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [mul_le_mul_of_nonneg_left hlog hP.le,
      mul_le_mul_of_nonneg_right (le_abs_self C₀) hq,
      mul_le_mul_of_nonneg_left hqp (abs_nonneg C₀)]
  refine (mul_le_mul_right (mul_le_mul_right hW _) _).trans ?_
  rw [ofReal_exp_mul_pow_eq hZ (by linarith : (0 : ℝ) < K) hN0]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  rw [log_mul_isolatedScale hβ hlam hl1]
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK
  have h1 : (p : ℝ) * Real.log (dipoleConstant β hβ) ≤
      N * |Real.log (dipoleConstant β hβ)| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hP.le).trans
      (mul_le_mul_of_nonneg_right hPN (abs_nonneg _))
  have h2 : (p : ℝ) * Real.log K ≤ N * Real.log K := mul_le_mul_of_nonneg_right hPN hlK
  have h3 : (1 + |C₀|) * (p : ℝ) ≤ (1 + |C₀|) * N :=
    mul_le_mul_of_nonneg_left hPN (by positivity)
  have e : (p : ℝ) * ((if 2 < β then (2 - β) * Real.log lam else 0)
      + (if β = 2 then Real.log |Real.log lam| else 0) + Real.log (dipoleConstant β hβ)) =
      p * (if 2 < β then (2 - β) * Real.log lam else 0)
        + p * (if β = 2 then Real.log |Real.log lam| else 0)
        + p * Real.log (dipoleConstant β hβ) := by ring
  have e2 : (p : ℝ) * (Real.log N + (if 2 < β then (2 - β) * Real.log lam else 0)
      + (if β = 2 then Real.log |Real.log lam| else 0)) =
      p * Real.log N + p * (if 2 < β then (2 - β) * Real.log lam else 0)
        + p * (if β = 2 then Real.log |Real.log lam| else 0) := by ring
  rw [e, e2]
  linarith

end IsolatedAssembly

open IsolatedAssembly

/-! ### Proposition 3.8 -/

/-- **Proposition 3.8, (eq:n neutral conv)** (`prop:isolated`, source l. 1188–1189). For
`β ≥ 2`, `C ≥ 0` and `C₀ ∈ ℝ` there are `C_β, c_β > 0` (depending only on `β`, `C`, `C₀`) such that
for every finite index type `ι` with `|ι| = 2p`, tie-break key, graph `γ ∈ G_p` (a
fixed-point-free involution `f`) with assigned set `S` (`f`-invariant, `|S| = 2(p - p₀)`), every
`2 ≤ p ≤ N` with `p ≥ N/2`, `p₀ ≤ p` and `0 < λ ≤ e^{-1}`:
`f(p₀) - p (log N + (2-β) log λ 1_{β>2} + log |log λ| 1_{β=2} + log 𝒵_β)
  ≤ -c_β p ((p - p₀)/p)² + C_β p (|log λ|^{-1} 1_{β=2} + λ^{β-2} 1_{2<β<4} + λ²|log λ|² 1_{β=4}
    + λ²|log λ| 1_{β>4}) + C_β log (N + 1)`,
stated for each `γ`, `S` as `e^{entropy} I(γ, S) ≤ e^{…}` (ruling R10). -/
theorem isolated_n_neutral_conv {β : ℝ} (hβ : 2 ≤ β) {C : ℝ} (hC : 0 ≤ C) (C₀ : ℝ) :
    ∃ Cβ cβ : ℝ, 0 < Cβ ∧ 0 < cβ ∧
      ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (f : ι → ι),
        (∀ i, f (f i) = i) → (∀ i, f i ≠ i) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
        (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N p p₀ : ℕ), Fintype.card ι = 2 * p → 2 ≤ p → p ≤ N →
        (N : ℝ) ≤ 2 * p → p₀ ≤ p → S.card = 2 * (p - p₀) →
        ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
          ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
              - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀))) *
            ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
              ENNReal.ofReal (Real.exp (-(β * pairAssignedEnergy h3 key lam C S z))) ≤
          ENNReal.ofReal (Real.exp (p * (Real.log N
                + (if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0)
                + Real.log (dipoleConstant β hβ))
              - cβ * p * (((p : ℝ) - p₀) / p) ^ 2
              + Cβ * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
                  else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|)
              + Cβ * Real.log (N + 1))) := by
  classical
  obtain ⟨C', hC', hpred⟩ := lintegral_isolatedCell_le_gpRefSet.{u} hβ hC
  obtain ⟨Cβ, cβ, hCβ, hcβ, h⟩ := refSetIntegral_conv.{u} hβ hC' C₀
  refine ⟨Cβ, cβ, hCβ, hcβ, fun ι _ _ key f hf2 hf0 h3 S hS N p p₀ hcard hp2 hpN hN hp₀ hSq lam
    hlam hl1 => ?_⟩
  have hRf := gpRefSet_mem_iff (key := key) hf2 hf0
  have hR : Fintype.card {i // i ∈ gpRefSet key f} = p := by
    have := IsolatedReduction.two_mul_card_ref hf2 hRf
    omega
  have : Nontrivial {i // i ∈ gpRefSet key f} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hI := hpred ι key f hf2 hf0 h3 S hS N lam hlam hl1
  rw [hR] at hI
  exact (mul_le_mul_right hI _).trans
    (h ι f (gpRefSet key f) hf2 hRf S hS N p p₀ hR hp2 hpN hN hp₀ hSq lam hlam hl1)

/-- **Proposition 3.8, (eq:n neutral)** (`prop:isolated`, source l. 1183–1185). For `β ≥ 2`,
`C ≥ 0` and `C₀ ∈ ℝ` there is `C_β > 0` (depending only on `β`, `C`, `C₀`) such that for every
finite index type `ι` with `|ι| = 2p`, tie-break key, graph `γ ∈ G_p` (a fixed-point-free
involution `f`) with assigned set `S` (`f`-invariant, `|S| = 2(p - p₀)`), every `2 ≤ p ≤ N` with
`p ≥ N/2`, `p₀ ≤ p` and `0 < λ ≤ e^{-1}`:
`f(p₀) ≤ p (log N + (2-β) log λ 1_{β>2} + log |log λ| 1_{β=2} + log 𝒵_β
    + C_β (|log λ|^{-1} 1_{β=2} + λ^{β-2} 1_{2<β<4} + λ²|log λ|² 1_{β=4} + λ²|log λ| 1_{β>4}))
    + C_β log (N + 1)`,
stated for each `γ`, `S` as `e^{entropy} I(γ, S) ≤ e^{…}` (ruling R10); the maximum over `p₀`,
`γ`, `S` of the source is the conjunction over all `p₀`, `γ`, `S`. -/
theorem isolated_n_neutral {β : ℝ} (hβ : 2 ≤ β) {C : ℝ} (hC : 0 ≤ C) (C₀ : ℝ) :
    ∃ Cβ : ℝ, 0 < Cβ ∧
      ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (f : ι → ι),
        (∀ i, f (f i) = i) → (∀ i, f i ≠ i) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
        (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N p p₀ : ℕ), Fintype.card ι = 2 * p → 2 ≤ p → p ≤ N →
        (N : ℝ) ≤ 2 * p → p₀ ≤ p → S.card = 2 * (p - p₀) →
        ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
          ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
              - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀))) *
            ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
              ENNReal.ofReal (Real.exp (-(β * pairAssignedEnergy h3 key lam C S z))) ≤
          ENNReal.ofReal (Real.exp (p * (Real.log N
                + (if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0)
                + Real.log (dipoleConstant β hβ)
                + Cβ * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
                  else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|))
              + Cβ * Real.log (N + 1))) := by
  obtain ⟨Cβ, cβ, hCβ, hcβ, h⟩ := isolated_n_neutral_conv.{u} hβ hC C₀
  refine ⟨Cβ, hCβ, fun ι _ _ key f hf2 hf0 h3 S hS N p p₀ hcard hp2 hpN hN hp₀ hSq lam hlam
    hl1 => (h ι key f hf2 hf0 h3 S hS N p p₀ hcard hp2 hpN hN hp₀ hSq lam hlam hl1).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))⟩
  have hq : 0 ≤ cβ * p * (((p : ℝ) - p₀) / p) ^ 2 := by positivity
  linarith

/-- **Proposition 3.8, (eq:crude)** (`prop:isolated`, source l. 1193–1197, proof ).
For `β ≥ 2`, `C ≥ 0` and `C₀ ∈ ℝ` there is `C_β > 0` (depending only on `β`, `C`, `C₀`) such that
for every finite index type `ι` with `|ι| = 2p`, tie-break key, graph `γ ∈ G_p` (a
fixed-point-free involution `f`), every `f`-invariant set `S` of vertices, every `2 ≤ p ≤ N`,
`p₀ ≤ p` and `0 < λ ≤ e^{-1}`:
`f(p₀) ≤ p (log N + (2-β) log λ 1_{β>2} + log |log λ| 1_{β=2}) + C_β N`,
stated for each `γ`, `S` as `e^{entropy} I(γ, S) ≤ e^{…}` (ruling R10). The source states this for
`p < N/2` (and `|I_S| = 2(p - p₀)`); neither restriction is used by the proof. -/
theorem isolated_crude {β : ℝ} (hβ : 2 ≤ β) {C : ℝ} (hC : 0 ≤ C) (C₀ : ℝ) :
    ∃ Cβ : ℝ, 0 < Cβ ∧
      ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (f : ι → ι),
        (∀ i, f (f i) = i) → (∀ i, f i ≠ i) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
        (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N p p₀ : ℕ), Fintype.card ι = 2 * p → 2 ≤ p → p ≤ N →
        p₀ ≤ p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
          ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
              - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀))) *
            ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
              ENNReal.ofReal (Real.exp (-(β * pairAssignedEnergy h3 key lam C S z))) ≤
          ENNReal.ofReal (Real.exp (p * (Real.log N
                + (if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0))
              + Cβ * N)) := by
  classical
  obtain ⟨C', hC', hpred⟩ := lintegral_isolatedCell_le_gpRefSet.{u} hβ hC
  obtain ⟨Cβ, hCβ, h⟩ := refSetIntegral_crude.{u} hβ hC' C₀
  refine ⟨Cβ, hCβ, fun ι _ _ key f hf2 hf0 h3 S hS N p p₀ hcard hp2 hpN hp₀ lam hlam hl1 => ?_⟩
  have hRf := gpRefSet_mem_iff (key := key) hf2 hf0
  have hR : Fintype.card {i // i ∈ gpRefSet key f} = p := by
    have := IsolatedReduction.two_mul_card_ref hf2 hRf
    omega
  have : Nontrivial {i // i ∈ gpRefSet key f} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hI := hpred ι key f hf2 hf0 h3 S hS N lam hlam hl1
  rw [hR] at hI
  exact (mul_le_mul_right hI _).trans (h ι (gpRefSet key f) S N p p₀ hR hpN hp₀ lam hlam hl1)

end TwoComponentCoulomb

end
