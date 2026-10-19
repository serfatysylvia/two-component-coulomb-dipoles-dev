/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.Basic
public import TwoComponentCoulomb.Integrals.LogFacts

/-!
# Proposition 3.7, Step 3: the real-variable optimization

Source: proof of Proposition 3.7 (`prop:auxk`), l. 1119--1140 (Step 3,
"optimization"), together with the definition (def:gbetak, l. 1020--1028) of the entropy-correction
exponent `γ_{β,k}`. Nothing in this file refers to the geometry of the nearest-neighbour graph:
it is pure real analysis, consumed by `AuxNearestNeighbor.lean`.

## The scales

Step 2 bounds a `2`-cycle displacement integral by `C · A` and any other displacement integral by
`C · B`, where (with `ℓ = |log λ|`)

* `A = cycleScale β λ` is `1` for `β < 2`, `ℓ` for `β = 2` and `λ^{2-β}` for `β > 2`;
* `B = treeScale β δ λ` is `1` for `β < 4`, `ℓ^{1+δ}` for `β = 4` and `λ^{2-β/2}` for `β > 4`.

## Main definitions and results

* `TwoComponentCoulomb.psiBeta`: the function `ψ_β` of source l. 1108--1117.
* `TwoComponentCoulomb.gammaBeta`: `γ_{β,k}` of source l. 1020--1028.
* `TwoComponentCoulomb.psiBeta_eq`: `ψ_β(x) = x log A + (1 - 2x) log B`.
* `TwoComponentCoulomb.gammaBeta_eq`: `γ_{β,k} = log (max (A k / N) (B ^ 2))`.
* `TwoComponentCoulomb.affine_maximization`: for `0 ≤ x ≤ 1/2`,
  `x log (k/N) + ψ_β(x) ≤ γ_{β,k} / 2`, with equality at `x = 0` or `x = 1/2`
  (source l. 1135--1139: "The function being maximized is affine").
* `TwoComponentCoulomb.count_mul_pow_le`: the entropy combination of the graph count with the
  integral bound (source l. 1122--1133): for `2 k₀ + k₁ ≤ k ≤ p ≤ N`,
  `(2^k k^k p^{k₁} / (k₀! k₁!)) N^{p - k + k₀} ≤ (2 e²)^k N^p (k/N)^{k₀}`.
* `TwoComponentCoulomb.affine_max`, `TwoComponentCoulomb.affine_max_log`: the endpoint
  maximization of `x ↦ x u + (1 - 2x) v` on `[0, 1/2]`, for general scales `A, B > 0`.
* `TwoComponentCoulomb.pow_mul_pow_le_exp`: the multiplicative form of the same maximization,
  `X^{k₀} b^{k - 2 k₀} ≤ exp ((k/2) log m)`; it is the form used in the assembly.
* `TwoComponentCoulomb.sum_le_exp`: the summation over `(k₀, k₁)` (source l. 1134): the sum of
  the per-cell bounds is at most `exp (p log N + C k + (k/2) log (max (A k / N) (B ^ 2)))`.

`psiBeta` and `gammaBeta` take the hypothesis `0 ≤ β` as an (unused) argument, so that they are
defined exactly on the carrier of the source (`β ≥ 0`, ruling R6).
-/

@[expose] public section

open scoped Nat
open Finset

namespace TwoComponentCoulomb

/-! ### Entropy combination (source l. 1122--1133) -/

/-- **Count against the volume factor** (source l. 1122--1133, the first inequality of the
displayed chain, written multiplicatively): for `2 k₀ + k₁ ≤ k ≤ p ≤ N`,
`(2^k k^k p^{k₁} / (k₀! k₁!)) N^{p - k + k₀} ≤ (2 e²)^k N^p (k/N)^{k₀}`.
We use `x^n / n! ≤ eˣ` for `k^{k₀} / k₀!` and `k^{k₁} / k₁!`, `p ≤ N`, and
`(k/N)^{k - k₀ - k₁} ≤ (k/N)^{k₀}` (which uses `2 k₀ + k₁ ≤ k` and `k ≤ N`). -/
theorem count_mul_pow_le {k₀ k₁ k p N : ℕ} (h : 2 * k₀ + k₁ ≤ k) (hkp : k ≤ p) (hpN : p ≤ N)
    (hk : 1 ≤ k) :
    2 ^ k * (k : ℝ) ^ k * (p : ℝ) ^ k₁ / ((k₀ ! : ℝ) * (k₁ ! : ℝ)) * (N : ℝ) ^ (p - k + k₀) ≤
      (2 * Real.exp 2) ^ k * (N : ℝ) ^ p * ((k : ℝ) / N) ^ k₀ := by
  obtain ⟨t, ht⟩ : ∃ t, k = 2 * k₀ + k₁ + t := ⟨k - (2 * k₀ + k₁), by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, p = k + q := ⟨p - k, by omega⟩
  have hK0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hKN : (k : ℝ) ≤ N := by exact_mod_cast hkp.trans hpN
  have hN0 : (0 : ℝ) < N := hK0.trans_le hKN
  have hpN' : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hf0 : (0 : ℝ) < (k₀ ! : ℝ) := by exact_mod_cast Nat.factorial_pos k₀
  have hf1 : (0 : ℝ) < (k₁ ! : ℝ) := by exact_mod_cast Nat.factorial_pos k₁
  have hA := Real.pow_div_factorial_le_exp (k : ℝ) hK0.le k₀
  have hB := Real.pow_div_factorial_le_exp (k : ℝ) hK0.le k₁
  have hpk : (p : ℝ) ^ k₁ ≤ (N : ℝ) ^ k₁ := pow_le_pow_left₀ hp0 hpN' k₁
  have hKt : (k : ℝ) ^ t ≤ (N : ℝ) ^ t := pow_le_pow_left₀ hK0.le hKN t
  have hexp : (Real.exp 2) ^ k = Real.exp k * Real.exp k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; exact congrArg Real.exp (by ring)
  have hkexp : (k : ℝ) ^ k = (k : ℝ) ^ k₀ * (k : ℝ) ^ k₁ * (k : ℝ) ^ (k₀ + t) := by
    rw [← pow_add, ← pow_add]; exact congrArg (fun e => (k : ℝ) ^ e) (by omega)
  have hNexp : (N : ℝ) ^ p = (N : ℝ) ^ (q + k₀ + k₁ + t) * (N : ℝ) ^ k₀ := by
    rw [← pow_add]; exact congrArg (fun e => (N : ℝ) ^ e) (by omega)
  have hsub : p - k + k₀ = q + k₀ := by omega
  have hNK : (N : ℝ) ^ k₀ * ((k : ℝ) / N) ^ k₀ = (k : ℝ) ^ k₀ := by
    rw [← mul_pow, mul_div_cancel₀ _ hN0.ne']
  have hLHS : 2 ^ k * (k : ℝ) ^ k * (p : ℝ) ^ k₁ / ((k₀ ! : ℝ) * (k₁ ! : ℝ)) *
      (N : ℝ) ^ (p - k + k₀) = 2 ^ k * ((k : ℝ) ^ k₀ / (k₀ ! : ℝ)) * ((k : ℝ) ^ k₁ / (k₁ ! : ℝ)) *
        ((k : ℝ) ^ (k₀ + t) * (p : ℝ) ^ k₁ * (N : ℝ) ^ (q + k₀)) := by
    rw [hsub]
    conv_lhs => rw [hkexp]
    ring
  rw [hLHS, mul_pow, hexp]
  have hmid : (k : ℝ) ^ (k₀ + t) * (N : ℝ) ^ k₁ * (N : ℝ) ^ (q + k₀) ≤
      (N : ℝ) ^ (q + k₀ + k₁ + t) * (k : ℝ) ^ k₀ := by
    calc (k : ℝ) ^ (k₀ + t) * (N : ℝ) ^ k₁ * (N : ℝ) ^ (q + k₀)
        = (k : ℝ) ^ k₀ * (k : ℝ) ^ t * (N : ℝ) ^ (q + k₀ + k₁) := by
          rw [pow_add, pow_add (N : ℝ) (q + k₀) k₁]; ring
      _ ≤ (k : ℝ) ^ k₀ * (N : ℝ) ^ t * (N : ℝ) ^ (q + k₀ + k₁) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKt (by positivity))
            (by positivity)
      _ = (N : ℝ) ^ (q + k₀ + k₁ + t) * (k : ℝ) ^ k₀ := by
          rw [pow_add (N : ℝ) (q + k₀ + k₁) t]; ring
  have hE0 : 0 ≤ 2 ^ k * Real.exp k * Real.exp k := by positivity
  have hE0' : 0 ≤ 2 ^ k * Real.exp k := by positivity
  calc 2 ^ k * ((k : ℝ) ^ k₀ / (k₀ ! : ℝ)) * ((k : ℝ) ^ k₁ / (k₁ ! : ℝ)) *
        ((k : ℝ) ^ (k₀ + t) * (p : ℝ) ^ k₁ * (N : ℝ) ^ (q + k₀))
      ≤ 2 ^ k * Real.exp k * Real.exp k *
        ((k : ℝ) ^ (k₀ + t) * (N : ℝ) ^ k₁ * (N : ℝ) ^ (q + k₀)) :=
      mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity)) hB (by positivity) hE0')
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpk (by positivity))
          (by positivity)) (by positivity) hE0
    _ ≤ 2 ^ k * Real.exp k * Real.exp k *
        ((N : ℝ) ^ (q + k₀ + k₁ + t) * (k : ℝ) ^ k₀) := mul_le_mul_of_nonneg_left hmid hE0
    _ = 2 ^ k * (Real.exp k * Real.exp k) * (N : ℝ) ^ p * ((k : ℝ) / N) ^ k₀ := by
        rw [hNexp, ← hNK]; ring

/-! ### The scales and the functions `ψ_β`, `γ_{β,k}` -/

/-- The size of the integral of a `2`-cycle displacement (source l. 1097--1118), as a function of
`β` and `λ`: `1` for `β < 2`, `ℓ = |log λ|` for `β = 2` and `λ^{2-β}` for `β > 2`. -/
noncomputable def cycleScale (β lam : ℝ) : ℝ :=
  if β < 2 then 1 else if β = 2 then |Real.log lam| else lam ^ (2 - β)

/-- The size of the integral of a non-cycle displacement (source l. 1097--1118): `1` for `β < 4`,
`ℓ^{1+δ}` for `β = 4` and `λ^{2-β/2}` for `β > 4`. -/
noncomputable def treeScale (β : ℝ) (δ : ℕ) (lam : ℝ) : ℝ :=
  if β < 4 then 1 else if β = 4 then |Real.log lam| ^ (1 + δ) else lam ^ (2 - β / 2)

/-- The function `ψ_β` of source l. 1108--1117 (`ℓ = |log λ|`), for `β ≥ 0`. -/
noncomputable def psiBeta (β : ℝ) (_hβ : 0 ≤ β) (δ : ℕ) (lam x : ℝ) : ℝ :=
  if β < 2 then 0
  else if β = 2 then x * Real.log |Real.log lam|
  else if β < 4 then (2 - β) * x * Real.log lam
  else if β = 4 then
    -2 * x * Real.log lam + (1 + (δ : ℝ)) * (1 - 2 * x) * Real.log |Real.log lam|
  else (2 - β) * x * Real.log lam + (2 - β / 2) * (1 - 2 * x) * Real.log lam

/-- The entropy-correction exponent `γ_{β,k}` of source l. 1020--1028 (def:gbetak), for `β ≥ 0`.
The case `β = 0`, `δ' = 1` and the case `β ∈ (0, 2)` of the source both give `0`. -/
noncomputable def gammaBeta (β : ℝ) (_hβ : 0 ≤ β) (δ : ℕ) (lam : ℝ) (k N : ℕ) : ℝ :=
  if β < 2 then 0
  else if β = 2 then Real.log (max (|Real.log lam| * k / N) 1)
  else if β < 4 then Real.log (max (lam ^ (2 - β) * k / N) 1)
  else if β = 4 then
    Real.log (max ((lam ^ 2)⁻¹ * k / N) (|Real.log lam| ^ (2 * (1 + δ))))
  else Real.log (max (lam ^ (2 - β) * k / N) (lam ^ (4 - β)))

section Scales

/-! #### Equation lemmas for the case splits -/

section Cases

variable {β : ℝ} {δ : ℕ} {lam : ℝ}

theorem cycleScale_of_lt_two (h : β < 2) : cycleScale β lam = 1 := by simp [cycleScale, h]

theorem cycleScale_two : cycleScale 2 lam = |Real.log lam| := by simp [cycleScale]

theorem cycleScale_of_two_lt (h : 2 < β) : cycleScale β lam = lam ^ (2 - β) := by
  simp [cycleScale, not_lt.2 h.le, h.ne']

theorem treeScale_of_lt_four (h : β < 4) : treeScale β δ lam = 1 := by simp [treeScale, h]

theorem treeScale_four : treeScale 4 δ lam = |Real.log lam| ^ (1 + δ) := by simp [treeScale]

theorem treeScale_of_four_lt (h : 4 < β) : treeScale β δ lam = lam ^ (2 - β / 2) := by
  simp [treeScale, not_lt.2 h.le, h.ne']

variable {hβ : 0 ≤ β}

theorem psiBeta_of_lt_two (h : β < 2) (x : ℝ) : psiBeta β hβ δ lam x = 0 := by
  simp [psiBeta, h]

theorem psiBeta_two (h : 0 ≤ (2 : ℝ)) (x : ℝ) :
    psiBeta 2 h δ lam x = x * Real.log |Real.log lam| := by simp [psiBeta]

theorem psiBeta_of_two_lt_of_lt_four (h2 : 2 < β) (h4 : β < 4) (x : ℝ) :
    psiBeta β hβ δ lam x = (2 - β) * x * Real.log lam := by
  simp [psiBeta, not_lt.2 h2.le, h2.ne', h4]

theorem psiBeta_four (h : 0 ≤ (4 : ℝ)) (x : ℝ) :
    psiBeta 4 h δ lam x =
      -2 * x * Real.log lam + (1 + (δ : ℝ)) * (1 - 2 * x) * Real.log |Real.log lam| := by
  simp [psiBeta]
  norm_num

theorem psiBeta_of_four_lt (h4 : 4 < β) (x : ℝ) :
    psiBeta β hβ δ lam x =
      (2 - β) * x * Real.log lam + (2 - β / 2) * (1 - 2 * x) * Real.log lam := by
  simp [psiBeta, not_lt.2 (h4.le.trans' (by norm_num : (2 : ℝ) ≤ 4)), h4.ne',
    (by linarith : ¬ β < 4), (by linarith : ¬ β = 2)]

theorem gammaBeta_of_lt_two (h : β < 2) (k N : ℕ) : gammaBeta β hβ δ lam k N = 0 := by
  simp [gammaBeta, h]

theorem gammaBeta_two (h : 0 ≤ (2 : ℝ)) (k N : ℕ) :
    gammaBeta 2 h δ lam k N = Real.log (max (|Real.log lam| * k / N) 1) := by
  simp [gammaBeta]

theorem gammaBeta_of_two_lt_of_lt_four (h2 : 2 < β) (h4 : β < 4) (k N : ℕ) :
    gammaBeta β hβ δ lam k N = Real.log (max (lam ^ (2 - β) * k / N) 1) := by
  simp [gammaBeta, not_lt.2 h2.le, h2.ne', h4]

theorem gammaBeta_four (h : 0 ≤ (4 : ℝ)) (k N : ℕ) :
    gammaBeta 4 h δ lam k N =
      Real.log (max ((lam ^ 2)⁻¹ * k / N) (|Real.log lam| ^ (2 * (1 + δ)))) := by
  simp [gammaBeta]
  norm_num

theorem gammaBeta_of_four_lt (h4 : 4 < β) (k N : ℕ) :
    gammaBeta β hβ δ lam k N =
      Real.log (max (lam ^ (2 - β) * k / N) (lam ^ (4 - β))) := by
  simp [gammaBeta, not_lt.2 (h4.le.trans' (by norm_num : (2 : ℝ) ≤ 4)), h4.ne',
    (by linarith : ¬ β < 4), (by linarith : ¬ β = 2)]

end Cases


variable {lam : ℝ}

theorem cycleScale_pos (β : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ Real.exp (-1)) :
    0 < cycleScale β lam := by
  have := one_le_abs_log hlam hlam1
  unfold cycleScale
  split_ifs
  · exact one_pos
  · linarith
  · exact Real.rpow_pos_of_pos hlam _

theorem treeScale_pos (β : ℝ) (δ : ℕ) (hlam : 0 < lam) (hlam1 : lam ≤ Real.exp (-1)) :
    0 < treeScale β δ lam := by
  have := one_le_abs_log hlam hlam1
  unfold treeScale
  split_ifs
  · exact one_pos
  · positivity
  · exact Real.rpow_pos_of_pos hlam _

theorem log_max_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (max a b) = max (Real.log a) (Real.log b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Real.log_le_log ha h)]
  · rw [max_eq_left h, max_eq_left (Real.log_le_log hb h)]

variable {lam : ℝ}

/-- The source's `ψ_β` is `x log A + (1 - 2x) log B` for the scales `A`, `B` of Step 2. -/
theorem psiBeta_eq (β : ℝ) (hβ : 0 ≤ β) (δ : ℕ) (hlam : 0 < lam) (x : ℝ) :
    psiBeta β hβ δ lam x =
      x * Real.log (cycleScale β lam) + (1 - 2 * x) * Real.log (treeScale β δ lam) := by
  rcases lt_or_ge β 2 with h2 | h2
  · rw [psiBeta_of_lt_two h2, cycleScale_of_lt_two h2, treeScale_of_lt_four (by linarith)]
    simp
  rcases eq_or_lt_of_le h2 with h2 | h2
  · subst h2
    rw [psiBeta_two, cycleScale_two, treeScale_of_lt_four (by norm_num)]
    simp
  rcases lt_or_ge β 4 with h4 | h4
  · rw [psiBeta_of_two_lt_of_lt_four h2 h4, cycleScale_of_two_lt h2, treeScale_of_lt_four h4,
      Real.log_rpow hlam]
    simp
    ring
  rcases eq_or_lt_of_le h4 with h4 | h4
  · subst h4
    rw [psiBeta_four, cycleScale_of_two_lt (by norm_num), treeScale_four, Real.log_rpow hlam,
      Real.log_pow]
    push_cast
    ring
  · rw [psiBeta_of_four_lt h4, cycleScale_of_two_lt (by linarith), treeScale_of_four_lt h4,
      Real.log_rpow hlam, Real.log_rpow hlam]
    ring

/-- The source's `γ_{β,k}` is `log (max (A k / N) (B²))` for the scales `A`, `B` of Step 2. -/
theorem gammaBeta_eq (β : ℝ) (hβ : 0 ≤ β) (δ : ℕ) (hlam : 0 < lam) {k N : ℕ} (hkN : k ≤ N) :
    gammaBeta β hβ δ lam k N =
      Real.log (max (cycleScale β lam * k / N) (treeScale β δ lam ^ 2)) := by
  have hkN' : (k : ℝ) / N ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hkN) (Nat.cast_nonneg N)
  rcases lt_or_ge β 2 with h2 | h2
  · rw [gammaBeta_of_lt_two h2, cycleScale_of_lt_two h2, treeScale_of_lt_four (by linarith),
      one_mul, one_pow, max_eq_right hkN', Real.log_one]
  rcases eq_or_lt_of_le h2 with h2 | h2
  · subst h2
    rw [gammaBeta_two, cycleScale_two, treeScale_of_lt_four (by norm_num), one_pow]
  rcases lt_or_ge β 4 with h4 | h4
  · rw [gammaBeta_of_two_lt_of_lt_four h2 h4, cycleScale_of_two_lt h2, treeScale_of_lt_four h4,
      one_pow]
  rcases eq_or_lt_of_le h4 with h4 | h4
  · subst h4
    rw [gammaBeta_four, cycleScale_of_two_lt (by norm_num), treeScale_four]
    have e1 : lam ^ ((2 : ℝ) - 4) = (lam ^ 2)⁻¹ := by
      rw [show (2 : ℝ) - 4 = -(2 : ℕ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_natCast]
    rw [e1, ← pow_mul, mul_comm (1 + δ) 2]
  · have e2 : (lam ^ (2 - β / 2)) ^ 2 = lam ^ (4 - β) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
      congr 1
      push_cast
      ring
    rw [gammaBeta_of_four_lt h4, cycleScale_of_two_lt (by linarith), treeScale_of_four_lt h4, e2]

/-! #### Maximization of the affine function (source l. 1135--1139) -/

/-- An affine function `x ↦ x u + (1 - 2x) v` on `[0, 1/2]` is at most `max u (2 v) / 2`, and
this maximum is attained at one of the two endpoints (`x = 0`: value `v`; `x = 1/2`: value `u/2`). -/
theorem affine_max (u v : ℝ) :
    (∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), x * u + (1 - 2 * x) * v ≤ max u (2 * v) / 2) ∧
      (0 * u + (1 - 2 * 0) * v = max u (2 * v) / 2 ∨
        1 / 2 * u + (1 - 2 * (1 / 2)) * v = max u (2 * v) / 2) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨hx0, hx1⟩ := hx
    have h1 : u ≤ max u (2 * v) := le_max_left _ _
    have h2 : 2 * v ≤ max u (2 * v) := le_max_right _ _
    linarith only [mul_le_mul_of_nonneg_left h1 hx0,
      mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - 2 * x by linarith only [hx1])]
  · rcases le_total u (2 * v) with h | h
    · left
      rw [max_eq_right h]
      ring
    · right
      rw [max_eq_left h]
      ring

/-- **Affine maximization for general scales**: for `A, B > 0` and `1 ≤ k ≤ N`,
`x log (k/N) + (x log A + (1 - 2x) log B) ≤ log (max (A k / N) (B²)) / 2` on `[0, 1/2]`, with
equality at `x = 0` or `x = 1/2`. -/
theorem affine_max_log {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {k N : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    (∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), x * Real.log ((k : ℝ) / N) +
        (x * Real.log A + (1 - 2 * x) * Real.log B) ≤
        Real.log (max (A * k / N) (B ^ 2)) / 2) ∧
      (0 * Real.log ((k : ℝ) / N) + (0 * Real.log A + (1 - 2 * 0) * Real.log B) =
          Real.log (max (A * k / N) (B ^ 2)) / 2 ∨
        1 / 2 * Real.log ((k : ℝ) / N) + (1 / 2 * Real.log A + (1 - 2 * (1 / 2)) * Real.log B) =
          Real.log (max (A * k / N) (B ^ 2)) / 2) := by
  have hK0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hKN : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hN0 : (0 : ℝ) < N := hK0.trans_le hKN
  have hu : Real.log (A * k / N) = Real.log A + Real.log ((k : ℝ) / N) := by
    rw [mul_div_assoc, Real.log_mul hA.ne' (by positivity)]
  have hv : Real.log (B ^ 2) = 2 * Real.log B := by
    rw [Real.log_pow]; norm_num
  have hm : Real.log (max (A * k / N) (B ^ 2)) =
      max (Real.log A + Real.log ((k : ℝ) / N)) (2 * Real.log B) := by
    rw [log_max_eq (by positivity) (by positivity), hu, hv]
  obtain ⟨h1, h2⟩ := affine_max (Real.log A + Real.log ((k : ℝ) / N)) (Real.log B)
  rw [hm]
  refine ⟨fun x hx => ?_, ?_⟩
  · linarith only [h1 x hx]
  · rcases h2 with h | h
    · left; linear_combination h
    · right; linear_combination h

/-- **Proposition 3.7, Step 3: affine maximization** (source l. 1135--1139), in the source's
notation. For `0 ≤ β`, `0 < λ ≤ e⁻¹` and integers `1 ≤ k ≤ N`, the function
`x ↦ x log (k/N) + ψ_β(x)` is at most `γ_{β,k} / 2` on `[0, 1/2]`, and the value `γ_{β,k} / 2`
is attained at one of the endpoints `x = 0`, `x = 1/2`. -/
theorem affine_maximization (β : ℝ) (hβ : 0 ≤ β) (δ : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ Real.exp (-1)) {k N : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    (∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
        x * Real.log ((k : ℝ) / N) + psiBeta β hβ δ lam x ≤ gammaBeta β hβ δ lam k N / 2) ∧
      (0 * Real.log ((k : ℝ) / N) + psiBeta β hβ δ lam 0 = gammaBeta β hβ δ lam k N / 2 ∨
        1 / 2 * Real.log ((k : ℝ) / N) + psiBeta β hβ δ lam (1 / 2) =
          gammaBeta β hβ δ lam k N / 2) := by
  have hA := cycleScale_pos β hlam hlam1
  have hB := treeScale_pos β δ hlam hlam1
  obtain ⟨h1, h2⟩ := affine_max_log hA hB hk hkN
  simp only [psiBeta_eq β hβ δ hlam, gammaBeta_eq β hβ δ hlam hkN]
  exact ⟨h1, h2⟩

end Scales

/-! ### Summation over the graph types (source l. 1134--1140) -/

/-- **Maximization of the affine function, in multiplicative form** (source l. 1134--1139): if
`X, b > 0` and `X, b² ≤ m`, then for `1 ≤ k` and `2 k₀ ≤ k` we have
`X^{k₀} b^{k - 2 k₀} ≤ m^{k/2} = exp ((k/2) log m)`. Indeed, with `x = k₀/k ∈ [0, 1/2]` the logarithm
of the left side is `k (x log X + (1 - 2x) log b) ≤ k max (log X) (2 log b) / 2` (`affine_max`). -/
theorem pow_mul_pow_le_exp {X b m : ℝ} (hX : 0 < X) (hb : 0 < b) (hXm : X ≤ m) (hbm : b ^ 2 ≤ m)
    {k k₀ : ℕ} (hk : 1 ≤ k) (h : 2 * k₀ ≤ k) :
    X ^ k₀ * b ^ (k - 2 * k₀) ≤ Real.exp ((k : ℝ) / 2 * Real.log m) := by
  have hK0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : Real.log X ≤ Real.log m := Real.log_le_log hX hXm
  have h2 : 2 * Real.log b ≤ Real.log m := by
    have := Real.log_le_log (pow_pos hb 2) hbm
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hkk : ((k - 2 * k₀ : ℕ) : ℝ) = (k : ℝ) - 2 * k₀ := by
    rw [Nat.cast_sub h]; push_cast; ring
  have h2' : 2 * (k₀ : ℝ) ≤ k := by exact_mod_cast h
  have hx0 : 0 ≤ (k₀ : ℝ) / k := by positivity
  have hx1 : (k₀ : ℝ) / k ≤ 1 / 2 := by
    rw [div_le_iff₀ hK0]; linarith
  have hmax := (affine_max (Real.log X) (Real.log b)).1 ((k₀ : ℝ) / k) ⟨hx0, hx1⟩
  have hmax' : max (Real.log X) (2 * Real.log b) ≤ Real.log m := max_le h1 h2
  have hlog : (k₀ : ℝ) * Real.log X + ((k : ℝ) - 2 * k₀) * Real.log b =
      k * ((k₀ : ℝ) / k * Real.log X + (1 - 2 * ((k₀ : ℝ) / k)) * Real.log b) := by
    field_simp
  have hX' : X ^ k₀ = Real.exp (k₀ * Real.log X) := by
    rw [Real.exp_nat_mul, Real.exp_log hX]
  have hb' : b ^ (k - 2 * k₀) = Real.exp (((k : ℝ) - 2 * k₀) * Real.log b) := by
    rw [← hkk, Real.exp_nat_mul, Real.exp_log hb]
  rw [hX', hb', ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [hlog]
  calc (k : ℝ) * ((k₀ : ℝ) / k * Real.log X + (1 - 2 * ((k₀ : ℝ) / k)) * Real.log b)
      ≤ k * (Real.log m / 2) :=
        mul_le_mul_of_nonneg_left
          (hmax.trans (div_le_div_of_nonneg_right hmax' (by norm_num : (0 : ℝ) ≤ 2))) hK0.le
    _ = (k : ℝ) / 2 * Real.log m := by ring

/-- **Summation over `(k₀, k₁)` and assembly of Step 3** (source l. 1126--1140). Let `d k₀ k₁`
bound the number of graphs in `D(k₀, k₁)`: `d k₀ k₁ · k₀! k₁! ≤ 2^k k^k p^{k₁}` whenever
`2 k₀ + k₁ ≤ k`, and `d k₀ k₁ = 0` when `2 k₀ + k₁ > k`. If the integral over one graph of type
`(k₀, k₁)` is bounded by `e^{2k} N^{p - k + k₀} (C_a A)^{k₀} (C_b B)^{k - 2 k₀}` (Step 2 with the
cycle scale `A` and the non-cycle scale `B`), then, for `1 ≤ k ≤ p ≤ N`, the sum over
`k₀, k₁ ≤ k` is at most `exp (p log N + C k + (k/2) log (max (A k / N) (B²)))` with
`C = 4 + log 8 + (log C_m)/2` for any `C_m ≥ max (C_a, C_b²)`. The factor
`(k+1)² ≤ 4^k` is the cost `2 log (k+1) ≤ C k` of the source. -/
theorem sum_le_exp {k p N : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p) (hpN : p ≤ N)
    {A B Ca Cb Cm : ℝ} (hA : 0 < A) (hB : 0 < B) (hCa : 0 < Ca) (hCb : 0 < Cb)
    (hCaCm : Ca ≤ Cm) (hCbCm : Cb ^ 2 ≤ Cm)
    (d : ℕ → ℕ → ℝ)
    (hd : ∀ k₀ k₁, 2 * k₀ + k₁ ≤ k →
      d k₀ k₁ * ((k₀ ! : ℝ) * (k₁ ! : ℝ)) ≤ 2 ^ k * (k : ℝ) ^ k * (p : ℝ) ^ k₁)
    (hdz : ∀ k₀ k₁, k < 2 * k₀ + k₁ → d k₀ k₁ = 0) :
    ∑ k₀ ∈ range (k + 1), ∑ k₁ ∈ range (k + 1), d k₀ k₁ *
        (Real.exp 2 ^ k * (N : ℝ) ^ (p - k + k₀) * ((Ca * A) ^ k₀ * (Cb * B) ^ (k - 2 * k₀))) ≤
      Real.exp (p * Real.log N + (4 + Real.log 8 + Real.log Cm / 2) * k +
        k / 2 * Real.log (max (A * k / N) (B ^ 2))) := by
  have hK0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hKN : (k : ℝ) ≤ N := by exact_mod_cast hkp.trans hpN
  have hN0 : (0 : ℝ) < N := hK0.trans_le hKN
  have hCm : 0 < Cm := hCa.trans_le hCaCm
  set mx := max (A * k / N) (B ^ 2) with hmx
  have hmx0 : 0 < mx := lt_max_of_lt_right (pow_pos hB 2)
  set m := Cm * mx with hm
  have hm0 : 0 < m := mul_pos hCm hmx0
  have hterm : ∀ k₀ ∈ range (k + 1), ∀ k₁ ∈ range (k + 1), d k₀ k₁ *
      (Real.exp 2 ^ k * (N : ℝ) ^ (p - k + k₀) * ((Ca * A) ^ k₀ * (Cb * B) ^ (k - 2 * k₀))) ≤
      Real.exp ((Real.log 2 + 4) * k + p * Real.log N + k / 2 * Real.log m) := by
    intro k₀ _ k₁ _
    by_cases hlt : k < 2 * k₀ + k₁
    · rw [hdz _ _ hlt, zero_mul]; positivity
    · replace hlt := not_lt.1 hlt
      have hdle : d k₀ k₁ ≤ 2 ^ k * (k : ℝ) ^ k * (p : ℝ) ^ k₁ / ((k₀ ! : ℝ) * (k₁ ! : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]; exact hd _ _ hlt
      have hc := count_mul_pow_le hlt hkp hpN hk
      have h1 : d k₀ k₁ * (N : ℝ) ^ (p - k + k₀) ≤
          (2 * Real.exp 2) ^ k * (N : ℝ) ^ p * ((k : ℝ) / N) ^ k₀ :=
        (mul_le_mul_of_nonneg_right hdle (by positivity)).trans hc
      have h2 : 2 * k₀ ≤ k := by omega
      have hX : 0 < (k : ℝ) / N * (Ca * A) := by positivity
      have hb : 0 < Cb * B := by positivity
      have hXm : (k : ℝ) / N * (Ca * A) ≤ m := by
        calc (k : ℝ) / N * (Ca * A) = Ca * (A * k / N) := by ring
          _ ≤ Cm * mx := by
            have : A * k / N ≤ mx := le_max_left _ _
            have h0 : 0 ≤ A * k / N := by positivity
            exact mul_le_mul hCaCm this h0 hCm.le
      have hbm : (Cb * B) ^ 2 ≤ m := by
        calc (Cb * B) ^ 2 = Cb ^ 2 * B ^ 2 := by ring
          _ ≤ Cm * mx := by
            have : B ^ 2 ≤ mx := le_max_right _ _
            exact mul_le_mul hCbCm this (by positivity) hCm.le
      have hcore := pow_mul_pow_le_exp hX hb hXm hbm hk h2
      have hE : 0 ≤ Real.exp 2 ^ k * ((Ca * A) ^ k₀ * (Cb * B) ^ (k - 2 * k₀)) := by positivity
      calc d k₀ k₁ * (Real.exp 2 ^ k * (N : ℝ) ^ (p - k + k₀) *
            ((Ca * A) ^ k₀ * (Cb * B) ^ (k - 2 * k₀)))
          = (d k₀ k₁ * (N : ℝ) ^ (p - k + k₀)) *
            (Real.exp 2 ^ k * ((Ca * A) ^ k₀ * (Cb * B) ^ (k - 2 * k₀))) := by ring
        _ ≤ ((2 * Real.exp 2) ^ k * (N : ℝ) ^ p * ((k : ℝ) / N) ^ k₀) *
            (Real.exp 2 ^ k * ((Ca * A) ^ k₀ * (Cb * B) ^ (k - 2 * k₀))) :=
            mul_le_mul_of_nonneg_right h1 hE
        _ = (2 * Real.exp 4) ^ k * (N : ℝ) ^ p *
            (((k : ℝ) / N * (Ca * A)) ^ k₀ * (Cb * B) ^ (k - 2 * k₀)) := by
            have : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
            rw [this, mul_pow, mul_pow, mul_pow, mul_pow]
            ring
        _ ≤ (2 * Real.exp 4) ^ k * (N : ℝ) ^ p * Real.exp ((k : ℝ) / 2 * Real.log m) :=
            mul_le_mul_of_nonneg_left hcore (by positivity)
        _ = Real.exp ((Real.log 2 + 4) * k + p * Real.log N + k / 2 * Real.log m) := by
            have e1 : (2 * Real.exp 4) ^ k = Real.exp ((Real.log 2 + 4) * k) := by
              rw [mul_comm (Real.log 2 + 4), Real.exp_nat_mul, Real.exp_add, Real.exp_log two_pos]
            have e2 : (N : ℝ) ^ p = Real.exp (p * Real.log N) := by
              rw [Real.exp_nat_mul, Real.exp_log hN0]
            rw [e1, e2, ← Real.exp_add, ← Real.exp_add]
  have hcount : ((k : ℝ) + 1) * ((k : ℝ) + 1) ≤ 4 ^ k := by
    have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    have h2 : ((k : ℝ) + 1) ≤ 2 ^ k := by exact_mod_cast h1
    calc ((k : ℝ) + 1) * ((k : ℝ) + 1) ≤ 2 ^ k * 2 ^ k :=
          mul_le_mul h2 h2 (by positivity) (by positivity)
      _ = 4 ^ k := by rw [← mul_pow]; norm_num
  have hfin : (4 : ℝ) ^ k * Real.exp ((Real.log 2 + 4) * k + p * Real.log N + k / 2 * Real.log m) =
      Real.exp (p * Real.log N + (4 + Real.log 8 + Real.log Cm / 2) * k +
        k / 2 * Real.log mx) := by
    have e4 : (4 : ℝ) ^ k = Real.exp (Real.log 4 * k) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have e8 : Real.log 8 = Real.log 2 + Real.log 4 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have elm : Real.log m = Real.log Cm + Real.log mx := Real.log_mul hCm.ne' hmx0.ne'
    rw [e4, ← Real.exp_add, elm, e8]
    congr 1
    ring
  calc ∑ k₀ ∈ range (k + 1), ∑ k₁ ∈ range (k + 1), d k₀ k₁ *
        (Real.exp 2 ^ k * (N : ℝ) ^ (p - k + k₀) * ((Ca * A) ^ k₀ * (Cb * B) ^ (k - 2 * k₀)))
      ≤ ∑ k₀ ∈ range (k + 1), ∑ k₁ ∈ range (k + 1),
        Real.exp ((Real.log 2 + 4) * k + p * Real.log N + k / 2 * Real.log m) :=
        sum_le_sum fun k₀ h0 => sum_le_sum fun k₁ h1 => hterm k₀ h0 k₁ h1
    _ = ((k : ℝ) + 1) * ((k : ℝ) + 1) *
        Real.exp ((Real.log 2 + 4) * k + p * Real.log N + k / 2 * Real.log m) := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 4 ^ k * Real.exp ((Real.log 2 + 4) * k + p * Real.log N + k / 2 * Real.log m) :=
        mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = _ := hfin

end TwoComponentCoulomb

end
