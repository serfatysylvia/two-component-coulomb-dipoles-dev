/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.IsolatedReduction
import TwoComponentCoulomb.Gibbs.Basic
import TwoComponentCoulomb.Gibbs.Measurability
import TwoComponentCoulomb.Integrals.LogFacts
import TwoComponentCoulomb.Integrals.Radial

/-!
# Theorem 2, Steps 3--4: the tilted isolated-pair block energies and their pair reduction

Source: proof of Theorem 2 (`prop:linear`), Step 3 (l. 1969–1998) and
Step 4 (l. 2007–2043), for `β > 2`. Both steps repeat Steps 2--3 of the proof of Proposition 3.9
on a marked nearest-neighbour graph: the configuration is split into the block `I = I^pair` of the
isolated `2`-cycles and its complement (gred3), and the block `I` is integrated as in the proof of
Proposition 3.8, with modified pair factors. This file defines the tilted block integrands and
carries out Steps 1--2 of the proof of Proposition 3.8 for them (the pointwise bound by a product
of pair weights, and the reduction to an integral over one representative of each pair).

As in `UpperBound/Isolated.lean`, the block is a finite index type `ι` (the vertices of `I`), the
graph of the cell is a fixed-point-free involution `f : ι → ι`, and `S` is the `f`-invariant set of
vertices of the pairs assigned the logarithmic term (the `q = p - p₀` marked same-sign pairs; the
source's `I'`). All radii are computed within the block (`nnRadius`, `nnRadius2`).

## The block energies

* **Step 3** (`A₁`, l. 1969–1978). `A₁ - F_λ` cancels `F_λ` (`linearA1`), and
  `e^{β A₁ - β F_λ} = e^{-β G_α}` with
  `G_α = -½ ∑_i g_λ(z_i - z_{φ₁ i}) + ∑_{i ∈ I'} (log (α_i / r̃₁(z_i)) - C)`,
  `α_i = (τ_i ∧ γ) ∨ r̃₁(z_i)`, `τ_i = r̃₂(z_i) ∧ r̃₂(z_{φ₁ i})` (`alphaRadius`). On a marked cell,
  `G_α = G⁽¹⁾_γ(z_I) + F⁽²⁾(z_{Iᶜ})` exactly, where `G⁽¹⁾_γ = alphaBlockEnergy` is
  `F^nn + ∑_{i ∈ S} (log (α^I_i / r̃₁(z_i)) - C)` and `α^I_i = alphaPairRadius` is `α_i` with `r̃₂`
  computed within `I`: for `i ∈ I'` both `φ₂(i)` and `φ₂(φ₁ i)` lie in `I^pair`, so `r̃₂` within `I`
  equals `r̃₂` (source l. 1450: at marked vertices the second neighbour also lies in `I`), and
  `r̃₁` is the same within `I` for every `i ∈ I^pair`.
* **Step 4** (`A₃`, l. 2011–2027). On a marked cell
  `A₃ ≤ ∑_{i ∈ I} ((r̃₁(z_i)/γ)² ∧ 1)` (distances within `I`), and the block integrand is
  `exp (t ∑_{i ∈ I} ((r̃₁(z_i)/γ)² ∧ 1) - β F⁽¹⁾)`, with `F⁽¹⁾ = pairAssignedEnergy`.

## Main results

* `alphaPairRadius`, `alphaBlockEnergy`: `α^I_i` and `G⁽¹⁾_γ`.
* `TiltedReduction.ofReal_exp_neg_mul_alphaBlockEnergy_le`: Step 1 for `G⁽¹⁾_γ`; the same-sign
  pair factor is `C₂ e^{β g_λ(u)} (a/((ρ ∧ γ) ∨ a))^{2β}` (`alphaPairWeight`), from
  `α ≥ ((ρ ∧ γ) ∨ a)/3` (`ρ ≤ 3 r̃₂`, the comparison of pair radii in Step 1).
* `TiltedReduction.ofReal_exp_tilt_sub_le`: Step 1 for the `A₃`-tilted integrand; the tilt of the
  pair `j` is `exp (2t ((a_j/γ)² ∧ 1))`.
* `lintegral_alphaBlockCell_le`: (pred3) for `G⁽¹⁾_γ`, with the same-sign factor
  `C' ((λ/ρ)^{β-2} + (λ/γ)^{β-2})` (`lintegral_sameSignPair_cutoff_le`, source l. 1970–1978).
* `lintegral_tiltedCell_le`: (pred3) for the `A₃`-tilted integrand: every pair factor gains at most
  `1 + C_t φ_β(γ)` (`lintegral_neutralTilt_le` after `e^{c s} ≤ 1 + (e^c - 1) s` on `[0, 1]`, source
  l. 2021–2027), and the same-sign tilt `e^{2t}` is absorbed into the constant `C'`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

universe u

namespace TwoComponentCoulomb

/-! ### Definitions -/

section Definitions

variable {ι : Type*} [Fintype ι] [Nontrivial ι]

/-- The radius `α^I_i = ((r̃₂(z_i) ∧ r̃₂(z_{φ₁ i})) ∧ γ) ∨ r̃₁(z_i)` of the isolated-pair block,
with the radii computed within the block (source the definition of αᵢ in Step 2, l. 1882–1883, restricted to
`I` as in l. 1450–1454 and l. 1970). On a twice-isolated pair of a configuration it is the radius
`α_i` of Theorem 2, Step 2 (`alphaRadius`). -/
noncomputable def alphaPairRadius (h3 : 3 ≤ Fintype.card ι) (key : ι ↪ ℕ) (lam γ : ℝ)
    (z : ι → ℂ) (i : ι) : ℝ :=
  max (min (min (nnRadius2 h3 key lam z i) (nnRadius2 h3 key lam z (nnMap key z i))) γ)
    (nnRadius lam z i)

/-- The `A₁`-block energy
`G⁽¹⁾_γ(z) = -½ ∑_i g_λ(z_i - z_{φ₁ i}) + ∑_{i ∈ S} (log (α^I_i / r̃₁(z_i)) - C)` of
Theorem 2, Step 3 (source l. 1969–1978: the energy `G` of (eq:alt) with `α_i` in place of
`r̃₂(z_i) ∧ r̃₂(z_{φ₁ i})`, restricted to the isolated-pair block as in the definition of F⁽¹⁾, l. 1453–1459).
`S` is the set of vertices of the marked same-sign pairs. -/
noncomputable def alphaBlockEnergy (h3 : 3 ≤ Fintype.card ι) (key : ι ↪ ℕ) (lam γ C : ℝ)
    (S : Finset ι) (z : ι → ℂ) : ℝ :=
  nnEnergy key lam z
    + ∑ i ∈ S, (Real.log (alphaPairRadius h3 key lam γ z i / nnRadius lam z i) - C)

variable (h3 : 3 ≤ Fintype.card ι) (key : ι ↪ ℕ)

/-- `r̃₁(z_i) ≤ α^I_i`. -/
theorem nnRadius_le_alphaPairRadius (lam γ : ℝ) (z : ι → ℂ) (i : ι) :
    nnRadius lam z i ≤ alphaPairRadius h3 key lam γ z i :=
  le_max_right _ _

/-- The logarithmic terms of `G⁽¹⁾_γ` are nonnegative up to `C`:
`G⁽¹⁾_γ ≥ F^nn - C |S|` (used in the crude bound). -/
theorem nnEnergy_sub_le_alphaBlockEnergy {lam : ℝ} (hlam : 0 < lam) (γ C : ℝ) (S : Finset ι)
    (z : ι → ℂ) :
    nnEnergy key lam z - C * S.card ≤ alphaBlockEnergy h3 key lam γ C S z := by
  unfold alphaBlockEnergy
  have h : ∀ i ∈ S, -C ≤ Real.log (alphaPairRadius h3 key lam γ z i / nnRadius lam z i) - C := by
    intro i _
    have h0 : 0 < nnRadius lam z i := hlam.trans_le (le_nnRadius lam z i)
    have h1 : 1 ≤ alphaPairRadius h3 key lam γ z i / nnRadius lam z i :=
      (one_le_div h0).2 (nnRadius_le_alphaPairRadius h3 key lam γ z i)
    linarith [Real.log_nonneg h1]
  have := Finset.sum_le_sum h
  rw [Finset.sum_const, nsmul_eq_mul] at this
  linarith

end Definitions

namespace TiltedReduction

open IsolatedReduction

/-! ### Step 1 for `G⁽¹⁾_γ`: the pointwise bound -/

section AlphaStepOne

variable {ι : Type*} [Fintype ι] [Nontrivial ι] {key : ι ↪ ℕ} {f : ι → ι} {z : ι → ℂ}
  {R : Set ι} [DecidablePred (· ∈ R)]

/-- **The cut-off logarithmic term** (source l. 1970–1978, as in l. 1217–1220): on the cell
`{nnMap key z = f}`, for both endpoints `i` of the pair `j`,
`-(log (α^I_i / r̃₁(z_i)) - C) ≤ log (3 a_j / ((ρ_j ∧ γ) ∨ a_j)) + C`, since `r̃₁(z_i) = a_j` and
`α^I_i ≥ ((ρ_j ∧ γ) ∨ a_j)/3` (from `ρ_j ≤ 3 r̃₂` at both endpoints). -/
theorem neg_alphaLogTerm_le (hz : nnMap key z = f) (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) [Nontrivial {i // i ∈ R}] (h3 : 3 ≤ Fintype.card ι)
    {lam : ℝ} (hlam : 0 < lam) (γ C : ℝ) (j : {i // i ∈ R}) {i : ι} (hi : i = j ∨ i = f j) :
    -(Real.log (alphaPairRadius h3 key lam γ z i / nnRadius lam z i) - C) ≤
      Real.log (3 * (displacementScale lam (z (f j) - z j) /
        max (min (nnRadius lam (fun l : {i // i ∈ R} => z l) j) γ)
          (displacementScale lam (z (f j) - z j)))) + C := by
  set a := displacementScale lam (z (f j) - z j) with ha
  set ρ := nnRadius lam (fun l : {i // i ∈ R} => z l) j with hρ
  have ha0 : 0 < a := displacementScale_pos hlam _
  have hfi : f i = j ∨ f i = f j := by
    rcases hi with hi | hi
    · exact Or.inr (by rw [hi])
    · exact Or.inl (by rw [hi, hf2])
  have h1 : ρ / 3 ≤ nnRadius2 h3 key lam z i := by
    have := nnRadius_ref_le_three_mul_nnRadius2 lam hz hf2 hRf h3 hlam.le j hi
    linarith
  have h2 : ρ / 3 ≤ nnRadius2 h3 key lam z (nnMap key z i) := by
    rw [hz]
    have := nnRadius_ref_le_three_mul_nnRadius2 lam hz hf2 hRf h3 hlam.le j hfi
    linarith
  have hr1 : nnRadius lam z i = a := nnRadius_eq_displacementScale lam hz hf2 hi
  set m := max (min ρ γ) a with hm
  have hm0 : 0 < m := lt_of_lt_of_le ha0 (le_max_right _ _)
  have hα : m / 3 ≤ alphaPairRadius h3 key lam γ z i := by
    unfold alphaPairRadius
    rw [hr1]
    rcases le_total (min ρ γ) a with h | h
    · rw [hm, max_eq_right h]
      exact le_trans (by linarith) (le_max_right _ _)
    · rw [hm, max_eq_left h]
      refine le_trans ?_ (le_max_left _ _)
      have hmin0 : 0 < min ρ γ := lt_of_lt_of_le ha0 h
      have hρ1 := min_le_left ρ γ
      have hγ1 := min_le_right ρ γ
      refine le_min (le_min ?_ ?_) ?_ <;> linarith
  have hαpos : 0 < alphaPairRadius h3 key lam γ z i := lt_of_lt_of_le (by positivity) hα
  have hlog : -Real.log (alphaPairRadius h3 key lam γ z i / nnRadius lam z i) ≤
      Real.log (3 * (a / m)) := by
    rw [hr1, ← Real.log_inv, inv_div]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ hαpos]
    have h3' : 3 * (a / m) * (m / 3) ≤ 3 * (a / m) * alphaPairRadius h3 key lam γ z i :=
      mul_le_mul_of_nonneg_left hα (by positivity)
    have e : 3 * (a / m) * (m / 3) = a := by field_simp
    linarith
  linarith

open scoped Classical in
/-- **Step 1, pointwise energy bound for `G⁽¹⁾_γ`**: on the cell `{nnMap key z = f}`, for an
`f`-invariant `S` and `β ≥ 0`,
`-β G⁽¹⁾_γ(z) ≤ ∑_{j ∈ R} (β g_λ(u_j) + c_j)`, where `c_j = 2βC + 2β log (3 a_j/((ρ_j ∧ γ) ∨ a_j))`
if `j ∈ S` and `c_j = 0` otherwise. -/
theorem neg_mul_alphaBlockEnergy_le (hz : nnMap key z = f) (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) [Nontrivial {i // i ∈ R}] (h3 : 3 ≤ Fintype.card ι)
    {S : Finset ι} (hS : ∀ i, f i ∈ S ↔ i ∈ S) {β C lam : ℝ} (hβ : 0 ≤ β) (hlam : 0 < lam)
    (γ : ℝ) :
    -(β * alphaBlockEnergy h3 key lam γ C S z) ≤
      ∑ j : {i // i ∈ R}, (β * smearedKernel lam (z (f j) - z j) +
        if (j : ι) ∈ S then
          2 * β * C + 2 * β * Real.log (3 * (displacementScale lam (z (f j) - z j) /
            max (min (nnRadius lam (fun l : {i // i ∈ R} => z l) j) γ)
              (displacementScale lam (z (f j) - z j))))
        else 0) := by
  classical
  set E : ι → ℝ := fun i => if i ∈ S then
    Real.log (alphaPairRadius h3 key lam γ z i / nnRadius lam z i) - C else 0 with hE
  have hG : alphaBlockEnergy h3 key lam γ C S z = nnEnergy key lam z + ∑ i, E i := by
    unfold alphaBlockEnergy
    simp only [hE]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hpair : ∀ j : {i // i ∈ R}, -β * (E j + E (f j)) ≤
      if (j : ι) ∈ S then
        2 * β * C + 2 * β * Real.log (3 * (displacementScale lam (z (f j) - z j) /
          max (min (nnRadius lam (fun l : {i // i ∈ R} => z l) j) γ)
            (displacementScale lam (z (f j) - z j))))
      else 0 := by
    intro j
    by_cases hj : (j : ι) ∈ S
    · have hfj : f j ∈ S := (hS j).2 hj
      have h1 := neg_alphaLogTerm_le hz hf2 hRf h3 hlam γ C j (Or.inl rfl)
      have h2 := neg_alphaLogTerm_le hz hf2 hRf h3 hlam γ C j (Or.inr rfl)
      have h1' := mul_le_mul_of_nonneg_left h1 hβ
      have h2' := mul_le_mul_of_nonneg_left h2 hβ
      simp only [hE, hj, hfj, ↓reduceIte]
      linarith
    · have hfj : f j ∉ S := fun h => hj ((hS j).1 h)
      simp only [hE, hj, hfj, ↓reduceIte]
      simp
  have hsum : -(β * alphaBlockEnergy h3 key lam γ C S z) =
      ∑ j : {i // i ∈ R}, (β * smearedKernel lam (z (f j) - z j) + -β * (E j + E (f j))) := by
    rw [hG, nnEnergy_eq_neg_sum hz hf2 hRf, sum_eq_sum_ref hf2 hRf E]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hsum]
  exact Finset.sum_le_sum fun j _ => by linarith [hpair j]

open scoped Classical in
/-- The pair weight of `G⁽¹⁾_γ` as a function of the displacement `u` and the radius `ρ = ρ_j`:
for `j ∈ S`, `C₂ e^{β g_λ(u)} (a(u)/((ρ ∧ γ) ∨ a(u)))^{2β}` with `C₂ = e^{2βC} 3^{2β}`; otherwise
`e^{β g_λ(u)}`. -/
noncomputable def alphaPairWeight (β C lam γ : ℝ) (S : Finset ι) (j : ι) (u : ℂ) (ρ : ℝ) :
    ℝ≥0∞ :=
  if j ∈ S then
    ENNReal.ofReal (Real.exp (2 * β * C) * 3 ^ (2 * β)) *
      ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
        (displacementScale lam u / max (min ρ γ) (displacementScale lam u)) ^ (2 * β))
  else ENNReal.ofReal (Real.exp (β * smearedKernel lam u))

/-- The exponential of the per-pair bound of `neg_mul_alphaBlockEnergy_le`. -/
theorem ofReal_exp_alpha_pair_eq {β C g s : ℝ} (hs : 0 < s) (P : Prop) [Decidable P] :
    ENNReal.ofReal (Real.exp (β * g +
        if P then 2 * β * C + 2 * β * Real.log (3 * s) else 0)) =
      if P then ENNReal.ofReal (Real.exp (2 * β * C) * 3 ^ (2 * β)) *
          ENNReal.ofReal (Real.exp (β * g) * s ^ (2 * β))
        else ENNReal.ofReal (Real.exp (β * g)) := by
  split_ifs
  · have h1 : Real.exp (2 * β * Real.log (3 * s)) = 3 ^ (2 * β) * s ^ (2 * β) := by
      rw [mul_comm, ← Real.rpow_def_of_pos (by positivity), Real.mul_rpow (by norm_num) hs.le]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.exp_add, Real.exp_add, h1]
    ring
  · rw [add_zero]

/-- **Step 1, the integrand bound for `G⁽¹⁾_γ`**: on the cell `{nnMap key z = f}`,
`exp(-β G⁽¹⁾_γ(z)) ≤ ∏_{j ∈ R} W_j(u_j, ρ_j)` with the pair weights `alphaPairWeight`. -/
theorem ofReal_exp_neg_mul_alphaBlockEnergy_le (hz : nnMap key z = f)
    (hf2 : ∀ i, f (f i) = i) (hRf : ∀ i, i ∈ R ↔ f i ∉ R) [Nontrivial {i // i ∈ R}]
    (h3 : 3 ≤ Fintype.card ι) {S : Finset ι} (hS : ∀ i, f i ∈ S ↔ i ∈ S) {β C lam : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) (γ : ℝ) :
    ENNReal.ofReal (Real.exp (-(β * alphaBlockEnergy h3 key lam γ C S z))) ≤
      ∏ j : {i // i ∈ R}, alphaPairWeight β C lam γ S j (z (f j) - z j)
        (nnRadius lam (fun l : {i // i ∈ R} => z l) j) := by
  refine (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
    (neg_mul_alphaBlockEnergy_le hz hf2 hRf h3 hS hβ hlam γ))).trans ?_
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le]
  refine Finset.prod_le_prod fun j _ => le_of_eq ?_
  have hs : 0 < displacementScale lam (z (f j) - z j) /
      max (min (nnRadius lam (fun l : {i // i ∈ R} => z l) j) γ)
        (displacementScale lam (z (f j) - z j)) :=
    div_pos (displacementScale_pos hlam _)
      (lt_of_lt_of_le (displacementScale_pos hlam _) (le_max_right _ _))
  rw [ofReal_exp_alpha_pair_eq hs]
  rfl

end AlphaStepOne

/-! ### Step 1 for the `A₃`-tilted integrand -/

section TiltStepOne

variable {ι : Type*} [Fintype ι] [Nontrivial ι] {key : ι ↪ ℕ} {f : ι → ι} {z : ι → ℂ}
  {R : Set ι} [DecidablePred (· ∈ R)]

/-- On the cell `{nnMap key z = f}`, both endpoints of the pair `j` have `r̃₁ = a_j`, so
`∑_i ((r̃₁(z_i)/γ)² ∧ 1) = ∑_{j ∈ R} 2 ((a_j/γ)² ∧ 1)`. -/
theorem sum_min_sq_eq (hz : nnMap key z = f) (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) (lam γ : ℝ) :
    ∑ i, min ((nnRadius lam z i / γ) ^ 2) 1 =
      ∑ j : {i // i ∈ R}, 2 * min ((displacementScale lam (z (f j) - z j) / γ) ^ 2) 1 := by
  rw [sum_eq_sum_ref hf2 hRf]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nnRadius_eq_displacementScale lam hz hf2 (Or.inl rfl),
    nnRadius_eq_displacementScale lam hz hf2 (Or.inr rfl)]
  ring

/-- **Step 1, the integrand bound for the `A₃`-tilted block** (source l. 2011–2027): on the cell
`{nnMap key z = f}`,
`exp (t ∑_i ((r̃₁(z_i)/γ)² ∧ 1) - β F⁽¹⁾(z)) ≤ ∏_{j ∈ R} W_j(u_j, ρ_j) e^{2t ((a_j/γ)² ∧ 1)}`,
with the pair weights `pairWeight` of Proposition 3.8. -/
theorem ofReal_exp_tilt_sub_le (hz : nnMap key z = f) (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) [Nontrivial {i // i ∈ R}] (h3 : 3 ≤ Fintype.card ι)
    {S : Finset ι} (hS : ∀ i, f i ∈ S ↔ i ∈ S) {β C lam : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hlam : 0 < lam) (γ t : ℝ) :
    ENNReal.ofReal (Real.exp (t * ∑ i, min ((nnRadius lam z i / γ) ^ 2) 1
        - β * pairAssignedEnergy h3 key lam C S z)) ≤
      ∏ j : {i // i ∈ R}, (pairWeight β C lam S j (z (f j) - z j)
          (nnRadius lam (fun l : {i // i ∈ R} => z l) j) *
        ENNReal.ofReal (Real.exp (2 * t *
          min ((displacementScale lam (z (f j) - z j) / γ) ^ 2) 1))) := by
  rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm,
    Finset.prod_mul_distrib]
  refine mul_le_mul' (ofReal_exp_neg_mul_pairAssignedEnergy_le hz hf2 hRf h3 hS hβ hC hlam)
    (le_of_eq ?_)
  rw [sum_min_sq_eq hz hf2 hRf, Finset.mul_sum, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring_nf

end TiltStepOne

end TiltedReduction

/-! ### Step 2: the reduction to an integral over the representatives -/

section Pred3

open IsolatedReduction TiltedReduction

/-- The cell `Λ^ι ∩ {nnMap key z = f}` is measurable. -/
theorem TiltedReduction.measurableSet_pairCell {ι : Type*} [Fintype ι] [Nontrivial ι]
    (key : ι ↪ ℕ) (f : ι → ι) (N : ℕ) :
    MeasurableSet ((Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f}) := by
  have : {z : ι → ℂ | nnMap key z = f} = ⋂ i, {z | nnMap key z i = f i} := by
    ext z; simp [funext_iff]
  rw [this]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_box N).inter
    (MeasurableSet.iInter fun i => measurableSet_nnMap_eq key i (f i))

open scoped Classical in
/-- **`(pred3)` for `G⁽¹⁾_γ`** (Theorem 2, Step 3, source l. 1970–1978 with Steps 1--2 of the proof
of Proposition 3.8). For `β > 2` and `C ∈ ℝ` there is `C' > 0`, depending only on `β` and `C`,
such that for every block `ι` with graph `f` (a fixed-point-free involution), set of
representatives `R`, `f`-invariant same-sign set `S`, `N`, `0 < λ ≤ e^{-1}` and `γ ≥ λ`,
`∫_{Λ^ι ∩ {nnMap key z = f}} e^{-β G⁽¹⁾_γ(z)} dz ≤ (𝒵_β λ^{2-β})^p ∫_{Λ^R} ∏_{j ∈ R ∖ S}
  (1 + C' φ_β(ρ_j)) ∏_{j ∈ R ∩ S} C' ((λ/ρ_j)^{β-2} + (λ/γ)^{β-2}) dW`.
The same-sign factor is `lintegral_sameSignPair_cutoff_le`; the neutral factor is `align1`. -/
theorem lintegral_alphaBlockCell_le {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) (C : ℝ) :
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
  obtain ⟨Cc, hCc0, hCc⟩ := lintegral_sameSignPair_cutoff_le h2
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

open scoped Classical in
/-- **`(pred3)` for the `A₃`-tilted block** (Theorem 2, Step 4, source l. 2011–2036 with Steps 1--2
of the proof of Proposition 3.8). For `β > 2`, `C ≥ 0` and `t ≥ 0` there are `C' > 0` and
`C_t ≥ 0`, depending only on `β`, `C`, `t`, such that for every block `ι` with graph `f`, set of
representatives `R`, `f`-invariant same-sign set `S`, `N`, `0 < λ ≤ e^{-1}` and `γ ≥ λ`,
`∫_{Λ^ι ∩ {nnMap key z = f}} exp (t ∑_i ((r̃₁(z_i)/γ)² ∧ 1) - β F⁽¹⁾(z)) dz
  ≤ (𝒵_β λ^{2-β} (1 + C_t φ_β(γ)))^p ∫_{Λ^R} ∏_{j ∈ R ∖ S} (1 + C' φ_β(ρ_j))
    ∏_{j ∈ R ∩ S} C' (λ/ρ_j)^{β-2} dW`,
with `F⁽¹⁾ = pairAssignedEnergy`. For an auxiliary neutral pair the tilt costs
`∫ e^{β g_λ} ((a/γ)² ∧ 1) ≤ C 𝒵_β λ^{2-β} φ_β(γ)` (`lintegral_neutralTilt_le`); for a same-sign
pair the tilt is at most `e^{2t}`, absorbed into `C'` (the source absorbs it into `C₀`, l. 2036). -/
theorem lintegral_tiltedCell_le {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) {C : ℝ} (hC : 0 ≤ C) {t : ℝ}
    (ht : 0 ≤ t) :
    ∃ C' Ct : ℝ, 0 < C' ∧ 0 ≤ Ct ∧ ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ)
      (f : ι → ι) (R : Set ι) [DecidablePred (· ∈ R)] [Nontrivial {i // i ∈ R}],
      (∀ i, f (f i) = i) → (∀ i, i ∈ R ↔ f i ∉ R) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
      (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N : ℕ) (lam γ : ℝ), 0 < lam → lam ≤ Real.exp (-1) → lam ≤ γ →
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
            ENNReal.ofReal (Real.exp (t * ∑ i, min ((nnRadius lam z i / γ) ^ 2) 1
              - β * pairAssignedEnergy h3 key lam C S z)) ≤
          ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam *
              (1 + Ct * isolatedPhi β hβ lam γ)) ^ Fintype.card {i // i ∈ R} *
            ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
              ∏ j : {i // i ∈ R}, (if (j : ι) ∈ S then
                ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam w j))
                else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam w j))) := by
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨Cn, hCn0, hCn⟩ := lintegral_neutralPair_le hβ (C := 18 * β * C) (by positivity)
  obtain ⟨Cs, hCs0, hCs⟩ := lintegral_sameSignPair_le_normalized hβ
  obtain ⟨CT, hCT0, hCT⟩ := lintegral_neutralTilt_le h2
  set C₂ : ℝ := Real.exp (2 * β * C) * 3 ^ (2 * β) with hC₂def
  have hC₂ : 0 ≤ C₂ := by positivity
  have het : 1 ≤ Real.exp (2 * t) := Real.one_le_exp (by positivity)
  set Ct : ℝ := (Real.exp (2 * t) - 1) * Real.exp (18 * β * C) * CT with hCtdef
  have hCt : 0 ≤ Ct := mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) hCT0.le
  set C' : ℝ := max Cn (Real.exp (2 * t) * C₂ * Cs) with hC'def
  refine ⟨C', Ct, lt_max_of_lt_left hCn0, hCt, ?_⟩
  intro ι _ _ key f R _ _ hf2 hRf h3 S hS N lam γ hlam hl1 hγ
  have hZ := dipoleConstant_pos β hβ
  have hscale := isolatedScale_pos hβ hlam hl1
  have hγ0 : 0 < γ := hlam.trans_le hγ
  have hφγ := isolatedPhi_nonneg hβ hlam hγ
  -- Step 1: the integrand bound
  refine (setLIntegral_mono' (measurableSet_pairCell key f N) fun z hz =>
    ofReal_exp_tilt_sub_le hz.2 hf2 hRf h3 hS hβ0 hC hlam γ t).trans ?_
  -- Step 2: displacement reduction
  have hg : Measurable (smearedKernel lam) := measurable_smearedKernel lam
  have hd : Measurable (displacementScale lam) := (continuous_displacementScale lam).measurable
  have e1 : Measurable fun p : ℂ × ℝ => Real.exp (β * smearedKernel lam p.1) :=
    Real.measurable_exp.comp ((hg.comp measurable_fst).const_mul β)
  have e2 : Measurable fun p : ℂ × ℝ => displacementScale lam p.1 / p.2 :=
    (hd.comp measurable_fst).div measurable_snd
  have e3 : Measurable fun p : ℂ × ℝ => ENNReal.ofReal (Real.exp (2 * t *
      min ((displacementScale lam p.1 / γ) ^ 2) 1)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((((hd.comp measurable_fst).div_const γ).pow_const 2).min measurable_const |>.const_mul _))
  have hΦ : ∀ j : {i // i ∈ R}, Measurable fun p : ℂ × ℝ =>
      pairWeight β C lam S j p.1 p.2 * ENNReal.ofReal (Real.exp (2 * t *
        min ((displacementScale lam p.1 / γ) ^ 2) 1)) := by
    intro j
    refine Measurable.mul ?_ e3
    by_cases hj : (j : ι) ∈ S
    · simp only [pairWeight, hj, ↓reduceIte]
      exact (ENNReal.measurable_ofReal.comp (e1.mul (e2.pow_const (2 * β)))).const_mul _
    · simp only [pairWeight, hj, ↓reduceIte]
      exact ENNReal.measurable_ofReal.comp
        (e1.mul (Real.measurable_exp.comp ((e2.pow_const 2).const_mul _)))
  refine (lintegral_cell_le_lintegral_ref key hf2 hRf lam
    (fun j u ρ => pairWeight β C lam S j u ρ * ENNReal.ofReal (Real.exp (2 * t *
      min ((displacementScale lam u / γ) ^ 2) 1))) hΦ).trans ?_
  -- Step 3: the radial integrals
  set Zt : ℝ := dipoleConstant β hβ * isolatedScale β hβ lam * (1 + Ct * isolatedPhi β hβ lam γ)
    with hZtdef
  have hinner : ∀ (w : {i // i ∈ R} → ℂ) (j : {i // i ∈ R}),
      ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j),
          pairWeight β C lam S j u (nnRadius lam w j) * ENNReal.ofReal (Real.exp (2 * t *
            min ((displacementScale lam u / γ) ^ 2) 1)) ≤
        ENNReal.ofReal Zt *
          (if (j : ι) ∈ S then ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam w j))
            else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam w j))) := by
    intro w j
    set ρ := nnRadius lam w j with hρdef
    have hρ : lam ≤ ρ := le_nnRadius lam w j
    have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
    have hφρ := isolatedPhi_nonneg hβ hlam hρ
    by_cases hj : (j : ι) ∈ S
    · simp only [pairWeight, hj, ↓reduceIte]
      have htail := isolatedTail_nonneg hβ hlam hρ0
      -- the tilt is at most `e^{2t}`
      have hpt : ∀ u : ℂ, ENNReal.ofReal C₂ * ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
            (displacementScale lam u / ρ) ^ (2 * β)) *
          ENNReal.ofReal (Real.exp (2 * t * min ((displacementScale lam u / γ) ^ 2) 1)) ≤
          ENNReal.ofReal (C₂ * Real.exp (2 * t)) *
            ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
              (displacementScale lam u / ρ) ^ (2 * β)) := by
        intro u
        rw [ENNReal.ofReal_mul hC₂, mul_right_comm]
        refine mul_le_mul_left
          (mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) _) _
        have := min_le_right ((displacementScale lam u / γ) ^ 2) 1
        have h2t : (0 : ℝ) ≤ 2 * t := by linarith only [ht]
        linarith only [mul_le_mul_of_nonneg_left this h2t]
      calc ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal C₂ *
            ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
              (displacementScale lam u / ρ) ^ (2 * β)) *
            ENNReal.ofReal (Real.exp (2 * t * min ((displacementScale lam u / γ) ^ 2) 1))
          ≤ ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal (C₂ * Real.exp (2 * t)) *
              ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
                (displacementScale lam u / ρ) ^ (2 * β)) := lintegral_mono hpt
        _ = ENNReal.ofReal (C₂ * Real.exp (2 * t)) *
              ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ),
                ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
                  (displacementScale lam u / ρ) ^ (2 * β)) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (C₂ * Real.exp (2 * t)) * ENNReal.ofReal (Cs * dipoleConstant β hβ *
              isolatedScale β hβ lam * isolatedTail β hβ lam ρ) := by
            gcongr
            exact hCs lam ρ hlam hl1 hρ
        _ ≤ _ := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hle : Real.exp (2 * t) * C₂ * Cs ≤ C' := le_max_right _ _
            have hq : 0 ≤ dipoleConstant β hβ * isolatedScale β hβ lam *
                isolatedTail β hβ lam ρ := by positivity
            have h1 : 1 ≤ 1 + Ct * isolatedPhi β hβ lam γ := by
              have := mul_nonneg hCt hφγ
              linarith
            calc C₂ * Real.exp (2 * t) * (Cs * dipoleConstant β hβ * isolatedScale β hβ lam *
                  isolatedTail β hβ lam ρ)
                = (Real.exp (2 * t) * C₂ * Cs) * (dipoleConstant β hβ * isolatedScale β hβ lam *
                    isolatedTail β hβ lam ρ) := by ring
              _ ≤ C' * (dipoleConstant β hβ * isolatedScale β hβ lam *
                    isolatedTail β hβ lam ρ) := mul_le_mul_of_nonneg_right hle hq
              _ ≤ (1 + Ct * isolatedPhi β hβ lam γ) * (C' * (dipoleConstant β hβ *
                    isolatedScale β hβ lam * isolatedTail β hβ lam ρ)) :=
                  le_mul_of_one_le_left (by positivity) h1
              _ = _ := by rw [hZtdef]; ring
    · simp only [pairWeight, hj, ↓reduceIte]
      -- `e^{2ts} ≤ 1 + (e^{2t} - 1) s` and `e^{18βC (a/ρ)²} ≤ e^{18βC}` on the disc
      set A : ℂ → ℝ := fun u => Real.exp (β * smearedKernel lam u) *
        Real.exp (18 * β * C * (displacementScale lam u / ρ) ^ 2) with hAdef
      set B : ℂ → ℝ := fun u => Real.exp (β * smearedKernel lam u) *
        min ((displacementScale lam u / γ) ^ 2) 1 with hBdef
      have hpt : ∀ u ∈ Metric.closedBall (0 : ℂ) (4 * ρ),
          ENNReal.ofReal (A u) *
            ENNReal.ofReal (Real.exp (2 * t * min ((displacementScale lam u / γ) ^ 2) 1)) ≤
          ENNReal.ofReal (A u) +
            ENNReal.ofReal ((Real.exp (2 * t) - 1) * Real.exp (18 * β * C)) *
              ENNReal.ofReal (B u) := by
        intro u hu
        have hu' : ‖u‖ ≤ 4 * ρ := by simpa using hu
        have ha1 : displacementScale lam u / ρ ≤ 1 :=
          (div_le_one hρ0).2 (displacementScale_le_of_norm_le hρ hu')
        have ha0 : 0 ≤ displacementScale lam u / ρ :=
          div_nonneg (displacementScale_pos hlam u).le hρ0.le
        have hs0 : 0 ≤ min ((displacementScale lam u / γ) ^ 2) 1 :=
          le_min (sq_nonneg _) zero_le_one
        have hs1 : min ((displacementScale lam u / γ) ^ 2) 1 ≤ 1 := min_le_right _ _
        have hexp := exp_mul_le_one_add (c := 2 * t) hs0 hs1
        have hE : Real.exp (18 * β * C * (displacementScale lam u / ρ) ^ 2) ≤
            Real.exp (18 * β * C) := by
          refine Real.exp_le_exp.2 ?_
          have : (displacementScale lam u / ρ) ^ 2 ≤ 1 := pow_le_one₀ ha0 ha1
          have h18 : 0 ≤ 18 * β * C := by positivity
          exact mul_le_of_le_one_right h18 this
        have hA0 : 0 ≤ A u := by positivity
        have hB0 : 0 ≤ B u := by positivity
        have hg0 := Real.exp_pos (β * smearedKernel lam u)
        have hc0' : 0 ≤ (Real.exp (2 * t) - 1) * Real.exp (18 * β * C) :=
          mul_nonneg (by linarith) (Real.exp_pos _).le
        rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul hc0',
          ← ENNReal.ofReal_add hA0 (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hc : 0 ≤ (Real.exp (2 * t) - 1) * min ((displacementScale lam u / γ) ^ 2) 1 :=
          mul_nonneg (by linarith) hs0
        calc A u * Real.exp (2 * t * min ((displacementScale lam u / γ) ^ 2) 1)
            ≤ A u * (1 + (Real.exp (2 * t) - 1) * min ((displacementScale lam u / γ) ^ 2) 1) :=
              mul_le_mul_of_nonneg_left hexp hA0
          _ = A u + (Real.exp (2 * t) - 1) * min ((displacementScale lam u / γ) ^ 2) 1 *
                (Real.exp (β * smearedKernel lam u) *
                  Real.exp (18 * β * C * (displacementScale lam u / ρ) ^ 2)) := by
              rw [hAdef]; ring
          _ ≤ A u + (Real.exp (2 * t) - 1) * min ((displacementScale lam u / γ) ^ 2) 1 *
                (Real.exp (β * smearedKernel lam u) * Real.exp (18 * β * C)) := by
              gcongr
          _ = _ := by rw [hBdef]; ring
      have hAm : Measurable fun u => ENNReal.ofReal (A u) :=
        ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp (hg.const_mul β)).mul
          (Real.measurable_exp.comp (((hd.div_const ρ).pow_const 2).const_mul _)))
      have hball := hCn lam ρ hlam hl1 hρ
      calc ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal (A u) *
            ENNReal.ofReal (Real.exp (2 * t * min ((displacementScale lam u / γ) ^ 2) 1))
          ≤ ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), (ENNReal.ofReal (A u) +
              ENNReal.ofReal ((Real.exp (2 * t) - 1) * Real.exp (18 * β * C)) *
                ENNReal.ofReal (B u)) :=
            setLIntegral_mono' Metric.isClosed_closedBall.measurableSet hpt
        _ = (∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal (A u)) +
              ENNReal.ofReal ((Real.exp (2 * t) - 1) * Real.exp (18 * β * C)) *
                ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), ENNReal.ofReal (B u) := by
            rw [lintegral_add_left hAm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam *
              (1 + Cn * isolatedPhi β hβ lam ρ)) +
            ENNReal.ofReal ((Real.exp (2 * t) - 1) * Real.exp (18 * β * C)) *
              ENNReal.ofReal (CT * dipoleConstant β hβ * isolatedScale β hβ lam *
                isolatedPhi β hβ lam γ) := by
            exact add_le_add hball (mul_le_mul_right
              ((setLIntegral_le_lintegral _ _).trans (hCT lam γ hlam hl1 hγ)) _)
        _ ≤ _ := by
            have hZs : 0 < dipoleConstant β hβ * isolatedScale β hβ lam := mul_pos hZ hscale
            have hc0 : 0 ≤ (Real.exp (2 * t) - 1) * Real.exp (18 * β * C) :=
              mul_nonneg (by linarith) (Real.exp_pos _).le
            have hC'0 : 0 < C' := lt_max_of_lt_left hCn0
            have hT0 : 0 ≤ CT * dipoleConstant β hβ * isolatedScale β hβ lam *
                isolatedPhi β hβ lam γ := by
              have := mul_nonneg hCT0.le hZs.le
              rw [mul_assoc CT] at *
              exact mul_nonneg this hφγ
            have hn0 : 0 ≤ dipoleConstant β hβ * isolatedScale β hβ lam *
                (1 + Cn * isolatedPhi β hβ lam ρ) :=
              mul_nonneg hZs.le (by have := mul_nonneg hCn0.le hφρ; linarith)
            have hZt0 : 0 ≤ Zt := by
              rw [hZtdef]
              exact mul_nonneg hZs.le (by have := mul_nonneg hCt hφγ; linarith)
            rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add hn0 (mul_nonneg hc0 hT0),
              ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (mul_nonneg hC'0.le hφρ),
              ← ENNReal.ofReal_mul hZt0]
            refine ENNReal.ofReal_le_ofReal ?_
            have hCnC' : Cn ≤ C' := le_max_left _ _
            have hq : 0 ≤ dipoleConstant β hβ * isolatedScale β hβ lam := hZs.le
            have hφ1 : Cn * isolatedPhi β hβ lam ρ ≤ C' * isolatedPhi β hβ lam ρ :=
              mul_le_mul_of_nonneg_right hCnC' hφρ
            have hprod : 0 ≤ Ct * isolatedPhi β hβ lam γ * (C' * isolatedPhi β hβ lam ρ) :=
              mul_nonneg (mul_nonneg hCt hφγ) (mul_nonneg hC'0.le hφρ)
            have e : (Real.exp (2 * t) - 1) * Real.exp (18 * β * C) *
                (CT * dipoleConstant β hβ * isolatedScale β hβ lam * isolatedPhi β hβ lam γ) =
                dipoleConstant β hβ * isolatedScale β hβ lam * (Ct * isolatedPhi β hβ lam γ) := by
              rw [hCtdef]; ring
            rw [e, hZtdef]
            have key : 1 + Cn * isolatedPhi β hβ lam ρ + Ct * isolatedPhi β hβ lam γ ≤
                (1 + Ct * isolatedPhi β hβ lam γ) * (1 + C' * isolatedPhi β hβ lam ρ) := by
              linarith only [hφ1, hprod]
            calc dipoleConstant β hβ * isolatedScale β hβ lam *
                  (1 + Cn * isolatedPhi β hβ lam ρ) +
                  dipoleConstant β hβ * isolatedScale β hβ lam * (Ct * isolatedPhi β hβ lam γ)
                = dipoleConstant β hβ * isolatedScale β hβ lam *
                    (1 + Cn * isolatedPhi β hβ lam ρ + Ct * isolatedPhi β hβ lam γ) := by ring
              _ ≤ dipoleConstant β hβ * isolatedScale β hβ lam *
                    ((1 + Ct * isolatedPhi β hβ lam γ) * (1 + C' * isolatedPhi β hβ lam ρ)) :=
                  mul_le_mul_of_nonneg_left key hq
              _ = _ := by ring
  calc ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
        ∏ j : {i // i ∈ R}, ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j),
          pairWeight β C lam S j u (nnRadius lam w j) * ENNReal.ofReal (Real.exp (2 * t *
            min ((displacementScale lam u / γ) ^ 2) 1))
      ≤ ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
          ∏ j : {i // i ∈ R}, (ENNReal.ofReal Zt *
            (if (j : ι) ∈ S then ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam w j))
              else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam w j)))) :=
        lintegral_mono fun w => Finset.prod_le_prod fun j _ => hinner w j
    _ = _ := by
        simp_rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
        exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

end Pred3

end TwoComponentCoulomb

end
