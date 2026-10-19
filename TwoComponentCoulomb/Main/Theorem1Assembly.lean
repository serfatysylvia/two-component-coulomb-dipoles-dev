/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.Energy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TwoComponentCoulomb.Frozen.M0
public import TwoComponentCoulomb.Frozen.ErrorRate
public import TwoComponentCoulomb.Frozen.GibbsMeasure
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.Frozen.PartitionFunction
public import TwoComponentCoulomb.Frozen.ReducedEnergy
public import TwoComponentCoulomb.Frozen.ReducedPartitionFunction
public import TwoComponentCoulomb.Frozen.SmearedKernel
import TwoComponentCoulomb.Frozen.Proposition41
import TwoComponentCoulomb.Gibbs.Basic
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Main.ErrorRateBounds
import TwoComponentCoulomb.Main.Theorem1AssemblyBounds
import TwoComponentCoulomb.NearestNeighbor.Isolated

/-!
# Theorem 1 from Lemma 3.6 and Propositions 3.10 and 4.1

Source: proof of Theorem 1 (l. 1904--1959); the statement is l. 235--274. The proof of the
theorem consists of two ingredients:

* the upper bounds, Lemma 3.6 (`lemma:part nn`, l. 922--946) and Proposition 3.10
  (`prop:upper bound`, l. 1423--1455), and
* the lower bound of Proposition 4.1 (`prop:lower bound`, l. 1745--1759), which is sealed
  (`TwoComponentCoulomb.proposition_4_1`).

The assembly is proved once, for a general error rate `ω : ℝ → ℝ` and a general error term
`E λ R` of the `β = 2` long-dipole bound (`theorem_1_of_gates_rate`). Its hypotheses on `ω` and
`E` are the elementary comparisons that the source proof uses: `0 ≤ ω`, the error rates of
Proposition 4.1 and of Lemma 3.6 are at most `ω` (l. 1905--1911, 1937), and `0 ≤ E`; its other
hypotheses are the statement of Lemma 3.6 and the statement of Proposition 3.10 with the rate `ω`
and the error `E` (without the bound `λ₀ ≤ e⁻²`, and with a separate threshold for the `β = 2`
bound). Its conclusion is the statement of Theorem 1 with the rate `ω` and the error `E`. The
instance used for Theorem 1 is

* `theorem_1_of_gates` (`ω = errorRate`, `E = log (1/R) / |log λ|`): the hypotheses are
  `Lemma36Statement` (the type of the sealed `lemma_3_6`) and `Proposition310Statement` (the type
  of the frozen `proposition_3_10`), and the conclusion is `Theorem1Statement` (the type of
  the frozen `theorem_1`), all three copied verbatim from the frozen files. This module imports
  neither `Frozen/Proposition310.lean` nor `Frozen/Theorem1.lean` (the provider of `theorem_1`
  imports this module). The provider `Main/Theorem1.lean` applies `theorem_1_of_gates` to the
  anchors `lemma_3_6` and `proposition_3_10` and states the frozen type of `theorem_1`, so the
  elaborator checks that the copies agree with the frozen types.

Both `theorem_1_of_gates_rate` and `theorem_1_of_gates` are *conditional helpers*: they are not
frozen statements and never stand in for one; the provider of `theorem_1` applies
`theorem_1_of_gates` to the anchors of Lemma 3.6 and Proposition 3.10.

The assembly follows the source proof:

* `0 < Z < ∞` and (eq:devlogz): the upper bound of Proposition 3.10 and the lower bound of
  Proposition 4.1, with the error comparisons of `Main/ErrorRateBounds.lean` and the elementary
  bounds of `Main/Theorem1AssemblyBounds.lean`;
* (eq:momexp): `𝔼[e^{β(F - F̃)}] = 𝒦 / Z` (`lintegral_gibbsMeasure_exp_energy_sub_reducedEnergy`),
  Lemma 3.6 for `𝒦` and the lower bound for `Z`;
* (eq:b1): the Boltzmann integral over `{#dipoles = p₀}` (Proposition 3.10) divided by the lower
  bound for `Z`;
* (eq:b2) for `β > 2` (l. 1949--1958): the same for `{D_R ≥ p₀'}`, with the tail
  `μ_β([R/λ, ∞)) = 2π (λ/R)^{β-2} / (𝒵_β (β - 2))` computed by
  `integral_Ici_exp_smearedKernel_one`, and the threshold chosen so that the hypothesis of
  Proposition 3.10 holds and `log (x₀/α_μ) ≥ ½ log (x₀/α)` (`tail_threshold`), where
  `α = (λ/R)^{β-2}` and `α_μ = μ_β([R/λ, ∞))`; the errors of both bounds are `O(N ω)`;
* (eq:critical lengths) for `β = 2`: Markov's inequality using `N - |I^dip|/2 ≥ 0`
  (`isolatedDipoles_card_le`), the last clause of Proposition 3.10, and the lower bound.

Main declarations: `Lemma36Statement`, `Proposition310Statement`, `Theorem1Statement`,
`theorem_1_of_gates_rate`, `theorem_1_of_gates`.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace TwoComponentCoulomb

/-! ### Passing between `[0, ∞]`-valued bounds and real logarithms -/

private theorem ofReal_exp_eq_of_eq {a b : ℝ} (h : a = b) :
    ENNReal.ofReal (Real.exp a) = ENNReal.ofReal (Real.exp b) := by
  rw [h]

/-- `ofReal (e^{M - A}) ≤ Z ≤ ofReal (e^{M + B})` gives `0 < Z < ∞` and
`|log Z - M| ≤ A + B`. -/
private theorem zBounds {Z : ℝ≥0∞} {M A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hl : ENNReal.ofReal (Real.exp (M - A)) ≤ Z) (hu : Z ≤ ENNReal.ofReal (Real.exp (M + B))) :
    0 < Z ∧ Z < ∞ ∧ |Real.log Z.toReal - M| ≤ A + B := by
  have hpos : 0 < Z := lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos _)) hl
  have hfin : Z < ∞ := lt_of_le_of_lt hu ENNReal.ofReal_lt_top
  refine ⟨hpos, hfin, ?_⟩
  have h1 : Real.exp (M - A) ≤ Z.toReal := (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 hl
  have h2 : Z.toReal ≤ Real.exp (M + B) := ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hu
  have h3 : 0 < Z.toReal := lt_of_lt_of_le (Real.exp_pos _) h1
  have h4 : M - A ≤ Real.log Z.toReal := (Real.le_log_iff_exp_le h3).2 h1
  have h5 : Real.log Z.toReal ≤ M + B := (Real.log_le_iff_le_exp h3).2 h2
  rw [abs_le]
  constructor <;> linarith

/-- `0 < K < ∞` and `|log K - M| ≤ B` give `K ≤ ofReal (e^{M + B})`. -/
private theorem le_ofReal_exp_of_abs_log_sub_le {K : ℝ≥0∞} {M B : ℝ} (h0 : 0 < K) (h1 : K < ∞)
    (h : |Real.log K.toReal - M| ≤ B) : K ≤ ENNReal.ofReal (Real.exp (M + B)) := by
  have hpos : 0 < K.toReal := ENNReal.toReal_pos h0.ne' h1.ne
  have h2 : Real.log K.toReal ≤ M + B := by linarith [(abs_le.1 h).2]
  have h3 : K.toReal ≤ Real.exp (M + B) := (Real.log_le_iff_le_exp hpos).1 h2
  calc K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal h1.ne).symm
    _ ≤ ENNReal.ofReal (Real.exp (M + B)) := ENNReal.ofReal_le_ofReal h3

/-- A quotient of `[0, ∞]`-valued bounds: `Z ≥ e^{M - A}` and `I ≤ e^E` give
`I / Z ≤ e^Y` as soon as `E + A - M ≤ Y`. -/
private theorem inv_mul_le_ofReal_exp {Z I : ℝ≥0∞} {M A E Y : ℝ}
    (hZ : ENNReal.ofReal (Real.exp (M - A)) ≤ Z) (hI : I ≤ ENNReal.ofReal (Real.exp E))
    (hY : E + A - M ≤ Y) : Z⁻¹ * I ≤ ENNReal.ofReal (Real.exp Y) := by
  calc Z⁻¹ * I ≤ (ENNReal.ofReal (Real.exp (M - A)))⁻¹ * ENNReal.ofReal (Real.exp E) :=
        mul_le_mul' (ENNReal.inv_le_inv.2 hZ) hI
    _ = ENNReal.ofReal (Real.exp (E - (M - A))) := by
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity),
          ← Real.exp_neg, ← Real.exp_add]
        congr 2
        ring
    _ ≤ ENNReal.ofReal (Real.exp Y) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))

/-! ### The lower bound for `Z` in the form of Theorem 1 -/

/-- The case split of Proposition 4.1 versus the one of Theorem 1. -/
private theorem ite_main (β : ℝ) (hβ : 2 ≤ β) (x y : ℝ) :
    (if β = 2 then x else y) = (if 2 < β then y else 0) + (if β = 2 then x else 0) := by
  by_cases h : β = 2
  · have h' : ¬ 2 < β := by rw [h]; exact lt_irrefl _
    simp [h]
  · have h' : 2 < β := lt_of_le_of_ne hβ (Ne.symm h)
    simp [h, h']

/-- Proposition 4.1, with its error term replaced by a rate `ω` that dominates it on
`0 < λ < e⁻¹` (source l. 1905--1911). -/
private theorem exists_partitionFunction_ge_rate (β : ℝ) (hβ : 2 ≤ β) (ω : ℝ → ℝ)
    (hlower : ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) →
      (if β = 2 then |Real.log lam| ^ (-(1 / 5 : ℝ))
        else if β < 4 then lam ^ (β - 2)
        else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
        else lam ^ 2 * |Real.log lam|) ≤ ω lam) :
    ∃ lam₄ C₄ : ℝ, 0 < lam₄ ∧ 0 < C₄ ∧ ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₄ →
      lam < Real.exp (-1) →
      ENNReal.ofReal (Real.exp (2 * (N : ℝ) * Real.log N
          + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
            + (if β = 2 then Real.log |Real.log lam| else 0)
            + (Real.log (dipoleConstant β hβ) - 1))
          - C₄ * N * ω lam)) ≤ partitionFunction N β lam := by
  obtain ⟨lam₄, C₄, h0, hC, h⟩ := proposition_4_1 β hβ
  refine ⟨lam₄, C₄, h0, hC, fun N hN lam hlam hlam4 hle => ?_⟩
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) (h N hN lam hlam hlam4)
  rw [ite_main β hβ (Real.log |Real.log lam|) ((2 - β) * Real.log lam)]
  have hrate := hlower lam hlam hle
  have hmul := mul_le_mul_of_nonneg_left hrate (mul_nonneg hC.le (Nat.cast_nonneg (α := ℝ) N))
  linarith

/-! ### Events and the Gibbs measure -/

/-- The mass of an event is at most the Boltzmann integral over a larger set, divided by `Z`. -/
private theorem gibbsMeasure_le_inv_mul {N : ℕ} {β lam : ℝ} {s t : Set (Fin N ⊕ Fin N → ℂ)}
    (hst : s ⊆ t) :
    gibbsMeasure N β lam s ≤ (partitionFunction N β lam)⁻¹ *
      ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ t,
        ENNReal.ofReal (Real.exp (-β * energy lam Z)) := by
  rw [gibbsMeasure_apply']
  exact mul_le_mul' le_rfl (lintegral_mono_set (Set.inter_subset_inter_right _ hst))

/-- Markov's inequality for the number of long isolated dipoles at `β = 2` (source l. 1958):
on `{D_R = p}` one has `N - |I^dip|/2 + D_R ≥ p`, because there are at most `N` isolated
dipoles. -/
private theorem gibbsMeasure_long_le {N : ℕ} {β lam R : ℝ} (hb : β = 2) (p : ℕ) :
    gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p} ≤
      (partitionFunction N β lam)⁻¹ * (ENNReal.ofReal (Real.exp (-(p : ℝ))) *
        ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
          ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
            + (longIsolatedDipoles Z R).card))) := by
  subst hb
  rw [gibbsMeasure_apply']
  refine mul_le_mul' le_rfl ?_
  have hmeas : MeasurableSet {Z : Fin N ⊕ Fin N → ℂ | (longIsolatedDipoles Z R).card = p} :=
    measurable_card_longIsolatedDipoles R (measurableSet_singleton p)
  calc ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
          {Z | (longIsolatedDipoles Z R).card = p}, ENNReal.ofReal (Real.exp (-2 * energy lam Z))
      ≤ ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
          {Z | (longIsolatedDipoles Z R).card = p}, ENNReal.ofReal (Real.exp (-(p : ℝ))) *
          ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
            + (longIsolatedDipoles Z R).card)) := by
        refine setLIntegral_mono' ((measurableSet_pi_box N).inter hmeas) fun Z hZ => ?_
        have hcard : (longIsolatedDipoles Z R).card = p := hZ.2
        have hle : ((isolatedDipoles Z).card : ℝ) ≤ N := by exact_mod_cast isolatedDipoles_card_le Z
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        rw [hcard]
        linarith
    _ ≤ ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N, ENNReal.ofReal (Real.exp (-(p : ℝ))) *
          ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
            + (longIsolatedDipoles Z R).card)) :=
        lintegral_mono_set Set.inter_subset_left
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ### The tail of `μ_β` and the threshold of (eq:b2) -/

/-- `μ_β`-tail: for `β > 2` and `R ≥ 2λ`,
`∫_{R/λ}^∞ e^{β g₁(r)} r dr = (λ/R)^{β-2} / (β - 2)` (source l. 1440, 1949--1953). -/
private theorem integral_tail_eq {β lam R : ℝ} (hβ : 2 < β) (hlam : 0 < lam) (hR : 2 * lam ≤ R) :
    ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r =
      (lam / R) ^ (β - 2) / (β - 2) := by
  have hs : 2 ≤ R / lam := by rw [le_div_iff₀ hlam]; linarith
  have hR0 : 0 < R := by linarith
  rw [integral_Ici_exp_smearedKernel_one hβ hs]
  congr 1
  rw [show (2 - β) = -(β - 2) by ring, Real.rpow_neg (by positivity),
    ← Real.inv_rpow (by positivity), inv_div]

/-- Choice of the threshold constant of (eq:b2) (source l. 1954--1957): if
`x ≥ max (C κ) (max κ² 2) α`, then `x > 0`, the hypothesis `C κ α ≤ x` of Proposition 3.10
holds, and `log (x / (κ α)) ≥ ½ log (x / α)`, so that the main term with `α_μ = κ α` is
dominated by the one with `α`. -/
private theorem tail_threshold {κ α x C c N : ℝ} (hκ : 0 < κ) (hα : 0 < α)
    (hc : 0 < c) (hN : 0 ≤ N) (hx : max (C * κ) (max (κ ^ 2) 2) * α ≤ x) :
    0 < x ∧ C * (κ * α) ≤ x ∧
      -c * N * x * Real.log (x / (κ * α)) ≤ -(c / 2) * N * x * Real.log (x / α) := by
  have h1 : C * κ ≤ max (C * κ) (max (κ ^ 2) 2) := le_max_left _ _
  have h2 : κ ^ 2 ≤ max (C * κ) (max (κ ^ 2) 2) := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : 2 ≤ max (C * κ) (max (κ ^ 2) 2) := (le_max_right _ _).trans (le_max_right _ _)
  have hx0 : 0 < x := lt_of_lt_of_le (mul_pos (by linarith) hα) hx
  refine ⟨hx0, ?_, ?_⟩
  · calc C * (κ * α) = (C * κ) * α := by ring
      _ ≤ max (C * κ) (max (κ ^ 2) 2) * α := mul_le_mul_of_nonneg_right h1 hα.le
      _ ≤ x := hx
  · have hu : max (C * κ) (max (κ ^ 2) 2) ≤ x / α := (le_div_iff₀ hα).2 hx
    have hu2 : κ ^ 2 ≤ x / α := h2.trans hu
    have hu1 : 1 ≤ x / α := by linarith
    have hL : 0 ≤ Real.log (x / α) := Real.log_nonneg hu1
    have hlogκ : 2 * Real.log κ ≤ Real.log (x / α) := by
      have h : Real.log (κ ^ 2) = 2 * Real.log κ := by
        rw [Real.log_pow]
        norm_num
      rw [← h]
      exact Real.log_le_log (by positivity) hu2
    have hdiv : Real.log (x / (κ * α)) = Real.log (x / α) - Real.log κ := by
      have h : x / (κ * α) = (x / α) / κ := by field_simp
      rw [h, Real.log_div (by positivity) hκ.ne']
    have hD : Real.log (x / α) / 2 ≤ Real.log (x / (κ * α)) := by
      rw [hdiv]
      linarith
    linarith only [mul_nonneg (mul_nonneg (mul_nonneg hc.le hN) hx0.le) (sub_nonneg.2 hD)]

/-- A threshold that exists under a hypothesis `p` can be chosen before deciding `p`. -/
private theorem exists_pos_and_imp {p : Prop} {Q : ℝ → ℝ → Prop}
    (h : p → ∃ C lam₁ : ℝ, 0 < C ∧ 0 < lam₁ ∧ Q C lam₁) :
    ∃ lam₁ : ℝ, 0 < lam₁ ∧ (p → ∃ C : ℝ, 0 < C ∧ Q C lam₁) := by
  by_cases hp : p
  · obtain ⟨C, lam₁, hC, hlam₁, hQ⟩ := h hp
    exact ⟨lam₁, hlam₁, fun _ => ⟨C, hC, hQ⟩⟩
  · exact ⟨1, one_pos, fun h => absurd h hp⟩

/-! ### The statements of Lemma 3.6, Proposition 3.10 and Theorem 1 -/

/-- The statement of Lemma 3.6 (`lemma:part nn`, source l. 922--946): the type of the sealed
anchor `TwoComponentCoulomb.lemma_3_6 β hβ`, copied verbatim from `Frozen/Lemma36.lean`. -/
def Lemma36Statement (β : ℝ) (hβ : 2 ≤ β) : Prop :=
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        0 < reducedPartitionFunction N β lam ∧ reducedPartitionFunction N β lam < ∞ ∧
        |Real.log (reducedPartitionFunction N β lam).toReal
            - (2 * N * Real.log N
              + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0)
                + (Real.log (dipoleConstant β hβ) - 1)))|
          ≤ C * (N * (if β = 2 then |Real.log lam| ^ (-(1 / 2 : ℝ)) else lam ^ min ((β - 2) / 2) 1)
            + Real.log (N + 1))

/-- The statement of Proposition 3.10 (`prop:upper bound`, source l. 1423--1455): the type of
the frozen anchor `TwoComponentCoulomb.proposition_3_10 β hβ`, copied verbatim from
`Frozen/Proposition310.lean`. -/
def Proposition310Statement (β : ℝ) (hβ : 2 ≤ β) : Prop :=
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ Real.exp (-2) ∧
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          partitionFunction N β lam
              ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                  + (if β = 2 then Real.log |Real.log lam| else 0)
                  + Real.log (dipoleConstant β hβ) - 1 + C * errorRate β hβ lam)
                + C * Real.log (N + 1))) ∧
          ∀ p₀ : ℕ, p₀ ≤ N →
            ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
                {Z | (isolatedDipoles Z).card = p₀},
                ENNReal.ofReal (Real.exp (-β * energy lam Z))
              ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                  + (if β = 2 then Real.log |Real.log lam| else 0))
                + N * (Real.log (dipoleConstant β hβ) - 1)
                - c * N * (((p₀ : ℝ) - N) / N) ^ 2
                + C * N * errorRate β hβ lam + C * Real.log (N + 1)))) ∧
      (2 < β → ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, 1 ≤ p₀' → p₀' ≤ N →
          C₁ * (2 * Real.pi / dipoleConstant β hβ *
              ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r) ≤ (p₀' : ℝ) / N →
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
              {Z | p₀' ≤ (longIsolatedDipoles Z R).card},
              ENNReal.ofReal (Real.exp (-β * energy lam Z))
            ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ) - 1)
                - c * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) /
                    (2 * Real.pi / dipoleConstant β hβ *
                      ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r))
                + C₂ * N * errorRate β hβ lam + C₂ * Real.log (N + 1)))) ∧
      (β = 2 → ∃ C : ℝ, 0 < C ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 →
          ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
              ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
                + (longIsolatedDipoles Z R).card))
            ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * (Real.log (2 * Real.pi * |Real.log lam|) - 1)
                + C * N * (errorRate β hβ lam + Real.log (1 / R) / |Real.log lam|)
                + C * Real.log (N + 1))))

/-- The statement of Theorem 1 (`theorem:th1`, source l. 235--274): the type of the frozen
anchor `TwoComponentCoulomb.theorem_1 β hβ`, copied verbatim from `Frozen/Theorem1.lean`. -/
def Theorem1Statement (β : ℝ) (hβ : 2 ≤ β) : Prop :=
    ∃ lamβ : ℝ, 0 < lamβ ∧ lamβ < Real.exp (-1) ∧
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
          0 < partitionFunction N β lam ∧ partitionFunction N β lam < ∞ ∧
          |Real.log (partitionFunction N β lam).toReal
              - (2 * N * Real.log N
                + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                  + (if β = 2 then Real.log |Real.log lam| else 0)
                  + (Real.log (dipoleConstant β hβ) - 1)))|
            ≤ C * (N * errorRate β hβ lam + Real.log (N + 1)) ∧
          ∫⁻ Z, ENNReal.ofReal (Real.exp (β * (energy lam Z - reducedEnergy lam Z)))
              ∂gibbsMeasure N β lam
            ≤ ENNReal.ofReal (Real.exp (C * N * errorRate β hβ lam + C * Real.log (N + 1))) ∧
          ∀ p₀ : ℕ, p₀ ≤ N →
            gibbsMeasure N β lam {Z | (isolatedDipoles Z).card = p₀}
              ≤ ENNReal.ofReal (Real.exp (-c * N * (1 - (p₀ : ℝ) / N) ^ 2
                + C * N * errorRate β hβ lam + C * Real.log (N + 1)))) ∧
      (2 < β → ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, p₀' ≤ N →
          C₁ * (lam / R) ^ (β - 2) ≤ (p₀' : ℝ) / N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (Real.exp
                (-c * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) / (lam / R) ^ (β - 2))
                  + C₂ * N * errorRate β hβ lam + C₂ * Real.log (N + 1)))) ∧
      (β = 2 → ∃ C : ℝ, 0 < C ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
        ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 → ∀ p₀' : ℕ, p₀' ≤ N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (((N : ℝ) + 1) ^ C * Real.exp (-(p₀' : ℝ) + C * N *
                (errorRate β hβ lam + Real.log (1 / R) / |Real.log lam|))))

/-! ### Theorem 1 for a general rate -/

/-- **Theorem 1 from Lemma 3.6 and Propositions 3.10 and 4.1, for a general error rate**
(source l. 1904--1959). Conditional helper. The rate `ω` and the error term `E λ R` of the `β = 2`
long-dipole bound are arbitrary functions with the comparisons used by the source proof, on
`0 < λ < e⁻¹`: `0 ≤ ω`, the error rates of Proposition 4.1 and of Lemma 3.6 are at most `ω`, and
`0 ≤ E λ R` for `2λ ≤ R ≤ 1`. The hypothesis `h36` is the statement of Lemma 3.6 and `h310` is the
statement of the frozen `proposition_3_10` with `errorRate β hβ` replaced by `ω` and the `β = 2`
error `log (1/R) / |log λ|` replaced by `E`, without the bound `λ₀ ≤ e⁻²` and with a separate
threshold for the `β = 2` bound. The conclusion is the statement of the frozen `theorem_1` with
`errorRate β hβ` replaced by `ω` and the `β = 2` error `log (1/R) / |log λ|` replaced by `E`. The
lower bound for the partition function comes from the sealed `proposition_4_1`. -/
theorem theorem_1_of_gates_rate (β : ℝ) (hβ : 2 ≤ β) (ω : ℝ → ℝ) (E : ℝ → ℝ → ℝ)
    (hω : ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) → 0 ≤ ω lam)
    (hlower : ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) →
      (if β = 2 then |Real.log lam| ^ (-(1 / 5 : ℝ))
        else if β < 4 then lam ^ (β - 2)
        else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
        else lam ^ 2 * |Real.log lam|) ≤ ω lam)
    (hreduced : ∀ lam : ℝ, 0 < lam → lam < Real.exp (-1) →
      (if β = 2 then |Real.log lam| ^ (-(1 / 2 : ℝ)) else lam ^ min ((β - 2) / 2) 1) ≤ ω lam)
    (hE : ∀ lam R : ℝ, 0 < lam → lam < Real.exp (-1) → 2 * lam ≤ R → R ≤ 1 → 0 ≤ E lam R)
    (h36 : Lemma36Statement β hβ)
    (h310 :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          partitionFunction N β lam
              ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                  + (if β = 2 then Real.log |Real.log lam| else 0)
                  + Real.log (dipoleConstant β hβ) - 1 + C * ω lam)
                + C * Real.log (N + 1))) ∧
          ∀ p₀ : ℕ, p₀ ≤ N →
            ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
                {Z | (isolatedDipoles Z).card = p₀},
                ENNReal.ofReal (Real.exp (-β * energy lam Z))
              ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                  + (if β = 2 then Real.log |Real.log lam| else 0))
                + N * (Real.log (dipoleConstant β hβ) - 1)
                - c * N * (((p₀ : ℝ) - N) / N) ^ 2
                + C * N * ω lam + C * Real.log (N + 1)))) ∧
      (2 < β → ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, 1 ≤ p₀' → p₀' ≤ N →
          C₁ * (2 * Real.pi / dipoleConstant β hβ *
              ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r) ≤ (p₀' : ℝ) / N →
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
              {Z | p₀' ≤ (longIsolatedDipoles Z R).card},
              ENNReal.ofReal (Real.exp (-β * energy lam Z))
            ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ) - 1)
                - c * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) /
                    (2 * Real.pi / dipoleConstant β hβ *
                      ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r))
                + C₂ * N * ω lam + C₂ * Real.log (N + 1)))) ∧
      (β = 2 → ∃ C lam₁ : ℝ, 0 < C ∧ 0 < lam₁ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₁ →
        ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 →
          ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
              ENNReal.ofReal (Real.exp (-2 * energy lam Z + N - (isolatedDipoles Z).card
                + (longIsolatedDipoles Z R).card))
            ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * (Real.log (2 * Real.pi * |Real.log lam|) - 1)
                + C * N * (ω lam + E lam R)
                + C * Real.log (N + 1))))
    ) :
    ∃ lamβ : ℝ, 0 < lamβ ∧ lamβ < Real.exp (-1) ∧
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
          0 < partitionFunction N β lam ∧ partitionFunction N β lam < ∞ ∧
          |Real.log (partitionFunction N β lam).toReal
              - (2 * N * Real.log N
                + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
                  + (if β = 2 then Real.log |Real.log lam| else 0)
                  + (Real.log (dipoleConstant β hβ) - 1)))|
            ≤ C * (N * ω lam + Real.log (N + 1)) ∧
          ∫⁻ Z, ENNReal.ofReal (Real.exp (β * (energy lam Z - reducedEnergy lam Z)))
              ∂gibbsMeasure N β lam
            ≤ ENNReal.ofReal (Real.exp (C * N * ω lam + C * Real.log (N + 1))) ∧
          ∀ p₀ : ℕ, p₀ ≤ N →
            gibbsMeasure N β lam {Z | (isolatedDipoles Z).card = p₀}
              ≤ ENNReal.ofReal (Real.exp (-c * N * (1 - (p₀ : ℝ) / N) ^ 2
                + C * N * ω lam + C * Real.log (N + 1)))) ∧
      (2 < β → ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, p₀' ≤ N →
          C₁ * (lam / R) ^ (β - 2) ≤ (p₀' : ℝ) / N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (Real.exp
                (-c * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) / (lam / R) ^ (β - 2))
                  + C₂ * N * ω lam + C₂ * Real.log (N + 1)))) ∧
      (β = 2 → ∃ C : ℝ, 0 < C ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lamβ →
        ∀ R : ℝ, 2 * lam ≤ R → R ≤ 1 → ∀ p₀' : ℕ, p₀' ≤ N →
          gibbsMeasure N β lam {Z | (longIsolatedDipoles Z R).card = p₀'}
            ≤ ENNReal.ofReal (((N : ℝ) + 1) ^ C * Real.exp (-(p₀' : ℝ) + C * N *
                (ω lam + E lam R)))) := by
  obtain ⟨lam₅, C₅, hlam₅, hC₅, h5⟩ := h36
  obtain ⟨lam₃, hlam₃, ⟨C₃, c₃, hC₃, hc₃, h3a⟩, h3b, h3c⟩ := h310
  obtain ⟨lam₆, hlam₆, h6⟩ := exists_pos_and_imp h3c
  obtain ⟨lam₄, C₄, hlam₄, hC₄, h4⟩ := exists_partitionFunction_ge_rate β hβ ω hlower
  have key : ∀ lam : ℝ, lam < min (min lam₃ lam₄) (min lam₅ (min lam₆ (Real.exp (-1) / 2))) →
      lam < lam₃ ∧ lam < lam₄ ∧ lam < lam₅ ∧ lam < lam₆ ∧ lam < Real.exp (-1) := by
    intro lam h
    simp only [lt_min_iff] at h
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2.1, by linarith [h.2.2.2, Real.exp_pos (-1)]⟩
  refine ⟨min (min lam₃ lam₄) (min lam₅ (min lam₆ (Real.exp (-1) / 2))), ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (lt_min hlam₃ hlam₄) (lt_min hlam₅ (lt_min hlam₆ (by positivity)))
  · exact lt_of_le_of_lt
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
      (by linarith [Real.exp_pos (-1)])
  · -- items (devlogz), (momexp) and (b1)
    refine ⟨C₃ + C₄ + C₅, c₃, by positivity, hc₃, ?_⟩
    intro N hN lam hlam hlamβ
    obtain ⟨hl3, hl4, hl5, -, hle⟩ := key lam hlamβ
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlogN : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hω0 : 0 ≤ ω lam := hω lam hlam hle
    have hNω : 0 ≤ (N : ℝ) * ω lam := mul_nonneg hN0.le hω0
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * (N : ℝ) * Real.log N
        + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
          + (if β = 2 then Real.log |Real.log lam| else 0)
          + (Real.log (dipoleConstant β hβ) - 1)) := ⟨_, rfl⟩
    have hZl := h4 N hN lam hlam hl4 hle
    rw [← hM] at hZl
    obtain ⟨h3a1, h3a2⟩ := h3a N hN lam hlam hl3
    have hZu : partitionFunction N β lam ≤ ENNReal.ofReal (Real.exp (M +
        (C₃ * N * ω lam + C₃ * Real.log ((N : ℝ) + 1)))) :=
      h3a1.trans_eq (ofReal_exp_eq_of_eq (by rw [hM]; ring))
    obtain ⟨hZpos, hZfin, hZabs⟩ := zBounds (by positivity) (by positivity) hZl hZu
    refine ⟨hZpos, hZfin, ?_, ?_, ?_⟩
    · rw [← hM]
      refine hZabs.trans ?_
      linarith [mul_nonneg hC₅.le hNω, mul_nonneg hC₅.le hlogN, mul_nonneg hC₄.le hlogN]
    · rw [lintegral_gibbsMeasure_exp_energy_sub_reducedEnergy]
      obtain ⟨hK0, hK1, hK⟩ := h5 N hN lam hlam hl5
      rw [← hM] at hK
      have hω' := hreduced lam hlam hle
      have hI := le_ofReal_exp_of_abs_log_sub_le hK0 hK1 hK
      have hmul := mul_le_mul_of_nonneg_left hω' (mul_nonneg hC₅.le hN0.le)
      refine inv_mul_le_ofReal_exp hZl hI ?_
      linarith [mul_nonneg hC₃.le hNω, mul_nonneg hC₃.le hlogN, mul_nonneg hC₄.le hlogN]
    · intro p₀ hp
      have hsq : (((p₀ : ℝ) - N) / N) ^ 2 = (1 - (p₀ : ℝ) / N) ^ 2 := by
        field_simp
        ring
      refine (gibbsMeasure_le_inv_mul (β := β) (lam := lam)
        (subset_refl {Z : Fin N ⊕ Fin N → ℂ | (isolatedDipoles Z).card = p₀})).trans ?_
      have hI := h3a2 p₀ hp
      rw [hsq] at hI
      refine inv_mul_le_ofReal_exp hZl hI ?_
      linarith [mul_nonneg hC₅.le hNω, mul_nonneg hC₅.le hlogN, mul_nonneg hC₄.le hlogN]
  · -- (b2), `β > 2`: the errors of the long-dipole bound and of the lower bound are `O(N ω)`
    intro hβ2
    obtain ⟨cb, Cb₁, Cb₂, hcb, hCb₁, hCb₂, hb⟩ := h3b hβ2
    have hZ0 := dipoleConstant_pos β hβ
    have hβm : 0 < β - 2 := by linarith
    obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 2 * Real.pi / (dipoleConstant β hβ * (β - 2)) := ⟨_, rfl⟩
    have hκ : 0 < κ := by rw [hκdef]; positivity
    refine ⟨cb / 2, max (Cb₁ * κ) (max (κ ^ 2) 2), Cb₂ + C₄, by positivity, by positivity,
      by positivity, ?_⟩
    intro N hN lam hlam hlamβ R hR p₀' hp hthr
    obtain ⟨hl3, hl4, -, -, hle⟩ := key lam hlamβ
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hR0 : 0 < R := by linarith
    have hα : 0 < (lam / R) ^ (β - 2) := by positivity
    have hlogN : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hD : 2 * Real.pi / dipoleConstant β hβ *
        ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r =
          κ * (lam / R) ^ (β - 2) := by
      rw [integral_tail_eq hβ2 hlam hR, hκdef]
      field_simp
    obtain ⟨hx0, hhyp, hlog⟩ := tail_threshold (c := cb) hκ hα hcb hN0.le hthr
    have hp1 : 1 ≤ p₀' := by
      rcases Nat.eq_zero_or_pos p₀' with h | h
      · rw [h] at hx0
        simp at hx0
      · exact h
    have hI := hb N hN lam hlam hl3 R hR p₀' hp1 hp (by rw [hD]; exact hhyp)
    rw [hD] at hI
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * (N : ℝ) * Real.log N
        + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
          + (if β = 2 then Real.log |Real.log lam| else 0)
          + (Real.log (dipoleConstant β hβ) - 1)) := ⟨_, rfl⟩
    have hZl := h4 N hN lam hlam hl4 hle
    rw [← hM] at hZl
    have hT : (if 2 < β then (2 - β) * Real.log lam else 0)
        + (if β = 2 then Real.log |Real.log lam| else 0) = (2 - β) * Real.log lam := by
      simp [hβ2, hβ2.ne']
    rw [hT] at hM
    have hP := gibbsMeasure_le_inv_mul (β := β) (lam := lam)
      (s := {Z : Fin N ⊕ Fin N → ℂ | (longIsolatedDipoles Z R).card = p₀'})
      (t := {Z | p₀' ≤ (longIsolatedDipoles Z R).card}) fun Z hZ => hZ.ge
    refine hP.trans (inv_mul_le_ofReal_exp hZl hI ?_)
    linarith [mul_nonneg hC₄.le hlogN]
  · -- (critical lengths), `β = 2`
    intro hb
    obtain ⟨C₆, hC₆, h6'⟩ := h6 hb
    refine ⟨C₆ + C₄, by positivity, ?_⟩
    intro N hN lam hlam hlamβ R hR hR1 p₀' hp
    obtain ⟨-, hl4, -, hl6, hle⟩ := key lam hlamβ
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlogN : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hℓ := one_lt_abs_log hlam hle
    have ht : 0 ≤ E lam R := hE lam R hlam hle hR hR1
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * (N : ℝ) * Real.log N
        + N * ((if 2 < β then (2 - β) * Real.log lam else 0)
          + (if β = 2 then Real.log |Real.log lam| else 0)
          + (Real.log (dipoleConstant β hβ) - 1)) := ⟨_, rfl⟩
    have hZl := h4 N hN lam hlam hl4 hle
    rw [← hM] at hZl
    have hT : (if 2 < β then (2 - β) * Real.log lam else 0)
        + (if β = 2 then Real.log |Real.log lam| else 0) = Real.log |Real.log lam| := by
      simp [hb]
    have hL : Real.log (dipoleConstant β hβ) = Real.log (2 * Real.pi) := by
      unfold dipoleConstant
      rw [ite_eq_left hb]
    rw [hT, hL] at hM
    have hlog2 : Real.log (2 * Real.pi * |Real.log lam|) =
        Real.log (2 * Real.pi) + Real.log |Real.log lam| :=
      Real.log_mul (by positivity) (by positivity)
    have hJ := h6' N hN lam hlam hl6 R hR hR1
    rw [hlog2] at hJ
    have hI := mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp (-(p₀' : ℝ))))) hJ
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add] at hI
    refine (gibbsMeasure_long_le hb p₀').trans
      ((inv_mul_le_ofReal_exp hZl hI (Y := Real.log ((N : ℝ) + 1) * (C₆ + C₄)
        + (-(p₀' : ℝ) + (C₆ + C₄) * N * (ω lam + E lam R))) ?_).trans
        (ENNReal.ofReal_le_ofReal ?_))
    · linarith [mul_nonneg hC₄.le hlogN, mul_nonneg (mul_nonneg hC₄.le hN0.le) ht]
    · rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]

/-! ### Theorem 1 from the frozen statements -/

/-- **Theorem 1 from the statements of Lemma 3.6 and Proposition 3.10** (source l. 1904--1959).
Conditional helper: the hypotheses are `Lemma36Statement β hβ`, the type of the sealed anchor
`lemma_3_6 β hβ`, and `Proposition310Statement β hβ`, the type of the frozen anchor
`proposition_3_10 β hβ`; the conclusion `Theorem1Statement β hβ` is the type of the frozen anchor
`theorem_1 β hβ`. It is `theorem_1_of_gates_rate` for `ω = errorRate β hβ` and
`E = log (1/R) / |log λ|`. -/
theorem theorem_1_of_gates (β : ℝ) (hβ : 2 ≤ β) (h36 : Lemma36Statement β hβ)
    (h310 : Proposition310Statement β hβ) : Theorem1Statement β hβ := by
  obtain ⟨lam₀, hlam₀, -, hA, hB, hC⟩ := h310
  exact theorem_1_of_gates_rate β hβ (errorRate β hβ)
    (fun lam R => Real.log (1 / R) / |Real.log lam|)
    (fun _ h0 h1 => (errorRate_pos β hβ h0 h1).le)
    (fun _ h0 h1 => lowerRate_le_errorRate β hβ h0 h1)
    (fun _ h0 h1 => reducedRate_le_errorRate β hβ h0 h1)
    (fun _ R _ _ hR hR1 => div_nonneg
      (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)) (abs_nonneg _))
    h36 ⟨lam₀, hlam₀, hA, hB, fun hb => (hC hb).imp fun _ hC' => ⟨lam₀, hC'.1, hlam₀, hC'.2⟩⟩

end TwoComponentCoulomb

end
