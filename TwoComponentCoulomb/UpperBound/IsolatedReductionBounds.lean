/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.NearestNeighbor.SecondRadius
public import TwoComponentCoulomb.UpperBound.IsolatedRadial
public import TwoComponentCoulomb.UpperBound.PairAssignedEnergy
import TwoComponentCoulomb.Potential.PairIntegral

/-!
# Proposition 3.9, Step 1: comparison of the radii and the pointwise integrand bound

Source: proof of Proposition 3.9 (`prop:isolated`), Step 1, l. 1263--1277.
Fix a finite index type `ι`, a fixed-point-free involution `f : ι → ι` (the nearest-neighbour graph
`γ` of the cell, all of whose components are `2`-cycles) and a set `R ⊆ ι` of *representatives*,
containing exactly one endpoint of each `2`-cycle (`i ∈ R ↔ f i ∉ R`; for the Gunson--Panta
reference set `gpRefSet key f` see `TwoComponentCoulomb.gpRefSet_mem_iff`).

For a configuration `z : ι → ℂ` in the cell `{nnMap key z = f}` and a representative `j ∈ R`, put
* `u_j = z (f j) - z j`, the displacement of the pair;
* `a_j = (|u_j| / 4) ∨ λ` (`displacementScale lam u_j`);
* `ρ_j = nnRadius lam (z|_R) j`, `¼ min_{l ∈ R, l ≠ j} |z_j - z_l| ∨ λ`, the first-neighbour radius
  of the representative `z_j` among the representatives.

## Main results

* `TwoComponentCoulomb.IsolatedReduction.nnRadius_eq_displacementScale`: `r̃₁(z_i) = a_j` for both
  endpoints `i` of the pair `j`.
* `TwoComponentCoulomb.IsolatedReduction.displacementScale_le_nnRadius_ref`: `a_j ≤ ρ_j`
  (and hence `|u_j| ≤ 4ρ_j`, `norm_le_four_mul_nnRadius_ref`).
* `TwoComponentCoulomb.IsolatedReduction.nnRadius_ref_le_three_mul_nnRadius2`:
  `ρ_j ≤ 3 r̃₂(z_i)` for both endpoints `i` (source l. 1266--1270).
* `TwoComponentCoulomb.IsolatedReduction.nnRadius_div_nnRadius2_le`:
  `r̃₁(z_i)/r̃₂(z_i) ≤ 3 a_j/ρ_j` (`mainclaimr1r2`, l. 1270--1272).
* `TwoComponentCoulomb.IsolatedReduction.neg_mul_pairAssignedEnergy_le`: the pointwise bound
  on the pair-assigned energy (l. 1272--1276): `-β E ≤ ∑_{j ∈ R} (β g_λ(u_j) + …)`.
* `TwoComponentCoulomb.IsolatedReduction.pairWeight`,
  `TwoComponentCoulomb.IsolatedReduction.ofReal_exp_neg_mul_pairAssignedEnergy_le`: the integrand
  bound `e^{-β E} ≤ ∏_{j ∈ R} W_j(u_j, ρ_j)` with the pair weights
  `W_j = C₂ e^{β g_λ(u)} (a(u)/ρ)^{2β}` (`j ∈ S`) and
  `W_j = e^{β g_λ(u)} e^{18 β C (a(u)/ρ)²}` (`j ∉ S`), `C₂ = e^{2βC} 3^{2β}`.
* `TwoComponentCoulomb.IsolatedReduction.sum_eq_sum_ref`,
  `TwoComponentCoulomb.IsolatedReduction.nnEnergy_eq_neg_sum`: sums over the vertices organised by
  pairs, and `F^nn = -∑_{j ∈ R} g_λ(u_j)`.
-/

@[expose] public section

namespace TwoComponentCoulomb

namespace IsolatedReduction

open Finset

/-! ### Elementary bounds for `nnRadius` -/

section NnRadius

variable {κ : Type*} [Fintype κ] [Nontrivial κ]

/-- If every other point is at distance at least `4 t` from `z j`, then `t ∨ λ ≤ r̃₁(z_j)`. -/
theorem le_nnRadius_of_forall (lam : ℝ) (z : κ → ℂ) (j : κ) {t : ℝ}
    (h : ∀ l, l ≠ j → 4 * t ≤ ‖z j - z l‖) : max t lam ≤ nnRadius lam z j := by
  classical
  unfold nnRadius
  refine max_le_max ?_ le_rfl
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
  refine Finset.le_inf' _ _ fun l hl => ?_
  have := h l (Finset.mem_erase.1 hl).1
  linarith

end NnRadius

/-! ### The representative of the pair containing a vertex -/

section RefPoint

variable {ι : Type*} (f : ι → ι) (R : Set ι) [DecidablePred (· ∈ R)]

/-- The representative in `R` of the pair `{k, f k}` containing `k`. -/
def refPt (k : ι) : ι := if k ∈ R then k else f k

variable {f R}

theorem refPt_mem (hRf : ∀ i, i ∈ R ↔ f i ∉ R) (k : ι) : refPt f R k ∈ R := by
  unfold refPt
  split_ifs with h
  · exact h
  · by_contra h'
    exact h ((hRf k).2 h')

theorem eq_or_eq_of_refPt_eq (hf2 : ∀ i, f (f i) = i) {k j : ι} (h : refPt f R k = j) :
    k = j ∨ k = f j := by
  unfold refPt at h
  split_ifs at h with hk
  · exact Or.inl h
  · exact Or.inr (by rw [← h, hf2])

end RefPoint

/-! ### Geometry of a cell whose nearest-neighbour graph is an involution -/

section Geometry

variable {ι : Type*} [Fintype ι] [Nontrivial ι] {key : ι ↪ ℕ} {f : ι → ι} {z : ι → ℂ}
  {R : Set ι} [DecidablePred (· ∈ R)]

theorem norm_sub_f_le (hz : nnMap key z = f) {i k : ι} (hk : k ≠ i) :
    ‖z i - z (f i)‖ ≤ ‖z i - z k‖ := by
  rw [← hz]
  exact norm_sub_nnMap_le key z hk

theorem norm_sub_refPt_le (hz : nnMap key z = f) {i k : ι} (hik : i ≠ k) :
    ‖z k - z (refPt f R k)‖ ≤ ‖z k - z i‖ := by
  unfold refPt
  split_ifs
  · simp
  · exact norm_sub_f_le hz hik

/-- The representative of the pair containing `k` is within `3 |z_i - z_k|` of the representative
`z_j` of the pair of `i`, for `k` outside the pair of `i` (source l. 1267--1269: the distance
from `v` to `w_l` and from `z` to `w_j` are at most `|z - v|`). -/
theorem norm_sub_refPt_le_three (hz : nnMap key z = f) (hf2 : ∀ i, f (f i) = i) {j i k : ι}
    (hi : i = j ∨ i = f j) (hki : k ≠ i) :
    ‖z j - z (refPt f R k)‖ ≤ 3 * ‖z i - z k‖ := by
  have h1 : ‖z j - z i‖ ≤ ‖z i - z (f i)‖ := by
    rcases hi with rfl | rfl
    · simp
    · rw [hf2 j, norm_sub_rev]
  have h2 : ‖z i - z (f i)‖ ≤ ‖z i - z k‖ := norm_sub_f_le hz hki
  have h3 : ‖z k - z (refPt f R k)‖ ≤ ‖z i - z k‖ := by
    rw [norm_sub_rev (z i)]
    exact norm_sub_refPt_le hz hki.symm
  calc ‖z j - z (refPt f R k)‖ ≤ ‖z j - z k‖ + ‖z k - z (refPt f R k)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (‖z j - z i‖ + ‖z i - z k‖) + ‖z k - z (refPt f R k)‖ := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 3 * ‖z i - z k‖ := by linarith

omit [Fintype ι] [Nontrivial ι] in
theorem refPt_ne (hf2 : ∀ i, f (f i) = i) {j i k : ι} (hi : i = j ∨ i = f j) (hki : k ≠ i)
    (hkf : k ≠ f i) : refPt f R k ≠ j := by
  intro h
  rcases eq_or_eq_of_refPt_eq hf2 h with hk | hk
  · rcases hi with hi | hi
    · exact hki (hk.trans hi.symm)
    · exact hkf (by rw [hi, hf2]; exact hk)
  · rcases hi with hi | hi
    · exact hkf (by rw [hi]; exact hk)
    · exact hki (hk.trans hi.symm)

variable (lam : ℝ)

/-- `r̃₁(z_i) = a_j` for both endpoints `i` of the pair `{j, f j}` (source l. 1269). -/
theorem nnRadius_eq_displacementScale (hz : nnMap key z = f) (hf2 : ∀ i, f (f i) = i) {j i : ι}
    (hi : i = j ∨ i = f j) : nnRadius lam z i = displacementScale lam (z (f j) - z j) := by
  rw [nnRadius_eq key lam z i, hz]
  unfold displacementScale
  rcases hi with rfl | rfl
  · rw [norm_sub_rev]
  · rw [hf2]

/-- `a_j ≤ ρ_j` (source l. 1268). -/
theorem displacementScale_le_nnRadius_ref (hz : nnMap key z = f) [Nontrivial {i // i ∈ R}]
    (j : {i // i ∈ R}) :
    displacementScale lam (z (f j) - z j) ≤ nnRadius lam (fun l : {i // i ∈ R} => z l) j := by
  refine le_nnRadius_of_forall lam (fun l : {i // i ∈ R} => z l) j
    (t := ‖z (f j) - z j‖ / 4) fun l hl => ?_
  have hl' : (l : ι) ≠ j := fun h => hl (Subtype.ext h)
  have := norm_sub_f_le hz hl'
  rw [norm_sub_rev (z (f j))]
  linarith

/-- `|u_j| ≤ 4 ρ_j` (source l. 1268). -/
theorem norm_le_four_mul_nnRadius_ref (hz : nnMap key z = f) [Nontrivial {i // i ∈ R}]
    (j : {i // i ∈ R}) :
    ‖z (f j) - z j‖ ≤ 4 * nnRadius lam (fun l : {i // i ∈ R} => z l) j := by
  have h1 := displacementScale_le_nnRadius_ref lam hz j
  have h2 : ‖z (f j) - z j‖ / 4 ≤ displacementScale lam (z (f j) - z j) := le_max_left _ _
  linarith

/-- `ρ_j ≤ 3 r̃₂(z_i)` for both endpoints `i` of the pair `j` (source l. 1266--1270). -/
theorem nnRadius_ref_le_three_mul_nnRadius2 (hz : nnMap key z = f) (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) [Nontrivial {i // i ∈ R}] (h3 : 3 ≤ Fintype.card ι)
    (hlam : 0 ≤ lam) (j : {i // i ∈ R}) {i : ι} (hi : i = j ∨ i = f j) :
    nnRadius lam (fun l : {i // i ∈ R} => z l) j ≤ 3 * nnRadius2 h3 key lam z i := by
  set key' : {i // i ∈ R} ↪ ℕ := (Function.Embedding.subtype (· ∈ R)).trans key with hkey'
  set w : {i // i ∈ R} → ℂ := fun l => z l with hw
  set m₀ : ℝ := ‖w j - w (nnMap key' w j)‖ with hm₀
  have h1 : max (m₀ / 12) lam ≤ nnRadius2 h3 key lam z i := by
    refine le_nnRadius2_of_forall h3 key lam z i (ρ := m₀ / 12) fun k hki hkf => ?_
    rw [hz] at hkf
    have hne : (⟨refPt f R k, refPt_mem hRf k⟩ : {i // i ∈ R}) ≠ j := fun h =>
      refPt_ne hf2 hi hki hkf (congrArg Subtype.val h)
    have h : m₀ ≤ ‖z j - z (refPt f R k)‖ := norm_sub_nnMap_le key' w hne
    have h' := norm_sub_refPt_le_three (R := R) hz hf2 hi hki
    linarith
  rw [nnRadius_eq key' lam w j]
  refine max_le ?_ ?_
  · have := le_max_left (m₀ / 12) lam
    linarith
  · have := le_max_right (m₀ / 12) lam
    linarith

/-- **`mainclaimr1r2`** (source l. 1270--1272): `r̃₁(z_i)/r̃₂(z_i) ≤ 3 a_j/ρ_j` for both endpoints
`i` of the pair `j`. -/
theorem nnRadius_div_nnRadius2_le (hz : nnMap key z = f) (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) [Nontrivial {i // i ∈ R}] (h3 : 3 ≤ Fintype.card ι)
    (hlam : 0 < lam) (j : {i // i ∈ R}) {i : ι} (hi : i = j ∨ i = f j) :
    nnRadius lam z i / nnRadius2 h3 key lam z i ≤
      3 * (displacementScale lam (z (f j) - z j) /
        nnRadius lam (fun l : {i // i ∈ R} => z l) j) := by
  rw [nnRadius_eq_displacementScale lam hz hf2 hi]
  have hρ := nnRadius_ref_le_three_mul_nnRadius2 lam hz hf2 hRf h3 hlam.le j hi
  have hρ0 : 0 < nnRadius lam (fun l : {i // i ∈ R} => z l) j :=
    lt_of_lt_of_le hlam (le_nnRadius _ _ _)
  have ha0 := displacementScale_pos hlam (z (f j) - z j)
  rw [mul_div_assoc', div_le_div_iff₀ (lt_of_lt_of_le hlam (le_nnRadius2 h3 key lam z i)) hρ0]
  nlinarith

/-- The logarithmic pair term (source l. 1273--1276): for both endpoints `i` of the pair `j`,
`-(log((r̃₂(z_i) ∧ r̃₂(z_{φ₁ i}))/r̃₁(z_i)) - C) ≤ log(3 a_j/ρ_j) + C`. -/
theorem neg_logTerm_le (hz : nnMap key z = f) (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) [Nontrivial {i // i ∈ R}] (h3 : 3 ≤ Fintype.card ι)
    (hlam : 0 < lam) (C : ℝ) (j : {i // i ∈ R}) {i : ι} (hi : i = j ∨ i = f j) :
    -(Real.log (min (nnRadius2 h3 key lam z i) (nnRadius2 h3 key lam z (nnMap key z i)) /
        nnRadius lam z i) - C) ≤
      Real.log (3 * (displacementScale lam (z (f j) - z j) /
        nnRadius lam (fun l : {i // i ∈ R} => z l) j)) + C := by
  set a := displacementScale lam (z (f j) - z j) with ha
  set ρ := nnRadius lam (fun l : {i // i ∈ R} => z l) j with hρ
  have ha0 : 0 < a := displacementScale_pos hlam _
  have hρ0 : 0 < ρ := lt_of_lt_of_le hlam (le_nnRadius _ _ _)
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
  have hinv : (3 * (a / ρ))⁻¹ = (ρ / 3) / a := by
    field_simp
  have hlog : -Real.log (3 * (a / ρ)) ≤
      Real.log (min (nnRadius2 h3 key lam z i) (nnRadius2 h3 key lam z (nnMap key z i)) /
        nnRadius lam z i) := by
    rw [← Real.log_inv, hinv, hr1]
    refine Real.log_le_log (by positivity) ?_
    exact div_le_div_of_nonneg_right (le_min h1 h2) ha0.le
  linarith

end Geometry

/-! ### Sums over the vertices, organised by pairs -/

section Sums

variable {ι : Type*} [Fintype ι] {f : ι → ι} {R : Set ι} [DecidablePred (· ∈ R)]

/-- The bijection `j ↦ f j` between the representatives and the other endpoints. -/
def refEquiv (hf2 : ∀ i, f (f i) = i) (hRf : ∀ i, i ∈ R ↔ f i ∉ R) :
    {i // i ∈ R} ≃ {i // i ∉ R} where
  toFun j := ⟨f j, (hRf j).1 j.2⟩
  invFun i := ⟨f i, not_not.1 (mt (hRf i).2 i.2)⟩
  left_inv j := Subtype.ext (hf2 j)
  right_inv i := Subtype.ext (hf2 i)

/-- A sum over all vertices is the sum over the representatives `j` of the contributions of the two
endpoints `j` and `f j` of the pair. -/
theorem sum_eq_sum_ref (hf2 : ∀ i, f (f i) = i) (hRf : ∀ i, i ∈ R ↔ f i ∉ R) (H : ι → ℝ) :
    ∑ i, H i = ∑ j : {i // i ∈ R}, (H j + H (f j)) := by
  rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ R) H, Finset.sum_add_distrib]
  congr 1
  exact (Fintype.sum_equiv (refEquiv hf2 hRf) (fun j : {i // i ∈ R} => H (f j))
    (fun i : {i // i ∉ R} => H i) fun j => rfl).symm

/-- The nearest-neighbour energy of a cell with graph `f` is `-∑_{j ∈ R} g_λ(u_j)` (each pair is
counted twice in `F^nn`, source l. 827, 1274; `g_λ` is even). -/
theorem nnEnergy_eq_neg_sum {key : ι ↪ ℕ} [Nontrivial ι] {z : ι → ℂ} (hz : nnMap key z = f)
    (hf2 : ∀ i, f (f i) = i) (hRf : ∀ i, i ∈ R ↔ f i ∉ R) (lam : ℝ) :
    nnEnergy key lam z = -∑ j : {i // i ∈ R}, smearedKernel lam (z (f j) - z j) := by
  unfold nnEnergy
  simp only [hz]
  rw [sum_eq_sum_ref hf2 hRf (fun i => smearedKernel lam (z i - z (f i)))]
  simp only [hf2]
  have : ∀ j : {i // i ∈ R}, smearedKernel lam (z j - z (f j)) + smearedKernel lam (z (f j) - z j)
      = 2 * smearedKernel lam (z (f j) - z j) := fun j => by
    rw [← smearedKernel_neg lam (z j - z (f j)), neg_sub]
    ring
  simp only [this, ← Finset.mul_sum]
  ring

end Sums

/-! ### The pointwise bound on the pair-assigned energy -/

section Energy

variable {ι : Type*} [Fintype ι] [Nontrivial ι] {key : ι ↪ ℕ} {f : ι → ι} {z : ι → ℂ}
  {R : Set ι} [DecidablePred (· ∈ R)]

open scoped Classical in
/-- **Step 1, pointwise energy bound** (source l. 1272--1276): on the cell `{nnMap key z = f}`,
for an `f`-invariant set `S` of assigned pairs, `β ≥ 0` and `C ≥ 0`,
`-β E(z) ≤ ∑_{j ∈ R} (β g_λ(u_j) + c_j)` where `c_j = 2βC + 2β log(3 a_j/ρ_j)` if the pair `j` is
assigned the logarithmic term (`j ∈ S`) and `c_j = 18 β C (a_j/ρ_j)²` otherwise. -/
theorem neg_mul_pairAssignedEnergy_le (hz : nnMap key z = f) (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) [Nontrivial {i // i ∈ R}] (h3 : 3 ≤ Fintype.card ι)
    {S : Finset ι} (hS : ∀ i, f i ∈ S ↔ i ∈ S) {β C lam : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hlam : 0 < lam) :
    -(β * pairAssignedEnergy h3 key lam C S z) ≤
      ∑ j : {i // i ∈ R}, (β * smearedKernel lam (z (f j) - z j) +
        if (j : ι) ∈ S then
          2 * β * C + 2 * β * Real.log (3 * (displacementScale lam (z (f j) - z j) /
            nnRadius lam (fun l : {i // i ∈ R} => z l) j))
        else 18 * β * C * (displacementScale lam (z (f j) - z j) /
            nnRadius lam (fun l : {i // i ∈ R} => z l) j) ^ 2) := by
  classical
  set E : ι → ℝ := fun i => if i ∈ S then
    Real.log (min (nnRadius2 h3 key lam z i) (nnRadius2 h3 key lam z (nnMap key z i)) /
      nnRadius lam z i) - C else 0 with hE
  set Q : ι → ℝ := fun i => if i ∈ S then 0 else
    (nnRadius lam z i / nnRadius2 h3 key lam z i) ^ 2 with hQ
  have hpae : pairAssignedEnergy h3 key lam C S z =
      nnEnergy key lam z + ∑ i, E i - C * ∑ i, Q i := by
    unfold pairAssignedEnergy
    have h1 : ∑ i, E i = ∑ i ∈ S, (Real.log (min (nnRadius2 h3 key lam z i)
        (nnRadius2 h3 key lam z (nnMap key z i)) / nnRadius lam z i) - C) := by
      simp only [hE]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have h2 : ∑ i, Q i = ∑ i ∈ Sᶜ, (nnRadius lam z i / nnRadius2 h3 key lam z i) ^ 2 := by
      have : ∀ i, Q i = if i ∈ Sᶜ then (nnRadius lam z i / nnRadius2 h3 key lam z i) ^ 2
          else 0 := fun i => by
        simp only [hQ, Finset.mem_compl]
        split_ifs <;> rfl
      simp only [this]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [h1, h2]
  have hpair : ∀ j : {i // i ∈ R}, -β * (E j + E (f j)) + β * C * (Q j + Q (f j)) ≤
      if (j : ι) ∈ S then
        2 * β * C + 2 * β * Real.log (3 * (displacementScale lam (z (f j) - z j) /
          nnRadius lam (fun l : {i // i ∈ R} => z l) j))
      else 18 * β * C * (displacementScale lam (z (f j) - z j) /
          nnRadius lam (fun l : {i // i ∈ R} => z l) j) ^ 2 := by
    intro j
    by_cases hj : (j : ι) ∈ S
    · have hfj : f j ∈ S := (hS j).2 hj
      have h1 := neg_logTerm_le lam hz hf2 hRf h3 hlam C j (Or.inl rfl)
      have h2 := neg_logTerm_le lam hz hf2 hRf h3 hlam C j (Or.inr rfl)
      have h1' := mul_le_mul_of_nonneg_left h1 hβ
      have h2' := mul_le_mul_of_nonneg_left h2 hβ
      simp only [hE, hQ, hj, hfj, ↓reduceIte]
      linarith
    · have hfj : f j ∉ S := fun h => hj ((hS j).1 h)
      have h1 := nnRadius_div_nnRadius2_le lam hz hf2 hRf h3 hlam j (Or.inl rfl)
      have h2 := nnRadius_div_nnRadius2_le lam hz hf2 hRf h3 hlam j (Or.inr rfl)
      have hρ0 : 0 < nnRadius lam (fun l : {i // i ∈ R} => z l) j :=
        lt_of_lt_of_le hlam (le_nnRadius _ _ _)
      have ha0 := displacementScale_pos hlam (z (f j) - z j)
      have hx1 : 0 ≤ nnRadius lam z j / nnRadius2 h3 key lam z j :=
        div_nonneg (lt_of_lt_of_le hlam (le_nnRadius _ _ _)).le
          (lt_of_lt_of_le hlam (le_nnRadius2 h3 key lam z j)).le
      have hx2 : 0 ≤ nnRadius lam z (f j) / nnRadius2 h3 key lam z (f j) :=
        div_nonneg (lt_of_lt_of_le hlam (le_nnRadius _ _ _)).le
          (lt_of_lt_of_le hlam (le_nnRadius2 h3 key lam z (f j))).le
      have h1' := pow_le_pow_left₀ hx1 h1 2
      have h2' := pow_le_pow_left₀ hx2 h2 2
      have hβC : 0 ≤ β * C := mul_nonneg hβ hC
      simp only [hE, hQ, hj, hfj, ↓reduceIte]
      have := mul_le_mul_of_nonneg_left (add_le_add h1' h2') hβC
      nlinarith
  have hsum : -(β * pairAssignedEnergy h3 key lam C S z) =
      ∑ j : {i // i ∈ R}, (β * smearedKernel lam (z (f j) - z j) +
        (-β * (E j + E (f j)) + β * C * (Q j + Q (f j)))) := by
    rw [hpae, nnEnergy_eq_neg_sum hz hf2 hRf, sum_eq_sum_ref hf2 hRf E,
      sum_eq_sum_ref hf2 hRf Q]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hsum]
  refine Finset.sum_le_sum fun j _ => ?_
  have := hpair j
  linarith

end Energy

/-! ### The pair weights and the integrand bound -/

section Weights

open scoped ENNReal

variable {ι : Type*}

open scoped Classical in
/-- The weight of the pair `j` as a function of its displacement `u` and the radius `ρ = ρ_j`
(source l. 1273--1276): for a pair assigned the logarithmic term (`j ∈ S`),
`C₂ e^{β g_λ(u)} (a(u)/ρ)^{2β}` with `C₂ = e^{2βC} 3^{2β}`; for the other pairs,
`e^{β g_λ(u)} e^{18 β C (a(u)/ρ)²}` (the neutral pair factor). -/
noncomputable def pairWeight (β C lam : ℝ) (S : Finset ι) (j : ι) (u : ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  if j ∈ S then
    ENNReal.ofReal (Real.exp (2 * β * C) * 3 ^ (2 * β)) *
      ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
        (displacementScale lam u / ρ) ^ (2 * β))
  else
    ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
      Real.exp (18 * β * C * (displacementScale lam u / ρ) ^ 2))

/-- The exponential of the per-pair bound of `neg_mul_pairAssignedEnergy_le`. -/
theorem ofReal_exp_pair_le {β C g s : ℝ} (hs : 0 < s) (S : Prop) [Decidable S] :
    ENNReal.ofReal (Real.exp (β * g +
        if S then 2 * β * C + 2 * β * Real.log (3 * s) else 18 * β * C * s ^ 2)) =
      if S then ENNReal.ofReal (Real.exp (2 * β * C) * 3 ^ (2 * β)) *
          ENNReal.ofReal (Real.exp (β * g) * s ^ (2 * β))
        else ENNReal.ofReal (Real.exp (β * g) * Real.exp (18 * β * C * s ^ 2)) := by
  split_ifs
  · have h1 : Real.exp (2 * β * Real.log (3 * s)) = 3 ^ (2 * β) * s ^ (2 * β) := by
      rw [mul_comm, ← Real.rpow_def_of_pos (by positivity), Real.mul_rpow (by norm_num) hs.le]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.exp_add, Real.exp_add, h1]
    ring
  · rw [Real.exp_add]

end Weights

/-! ### The integrand bound -/

section Integrand

open scoped ENNReal

variable {ι : Type*} [Fintype ι] [Nontrivial ι] {key : ι ↪ ℕ} {f : ι → ι} {z : ι → ℂ}
  {R : Set ι} [DecidablePred (· ∈ R)]

/-- **Step 1, the integrand bound** (source l. 1272--1276): on the cell `{nnMap key z = f}`, for an
`f`-invariant set `S` of pairs assigned the logarithmic term, `β ≥ 0` and `C ≥ 0`,
`exp(-β E(z)) ≤ ∏_{j ∈ R} W_j(u_j, ρ_j)` with the pair weights `pairWeight`: the neutral pair
factor is at most `e^{β g_λ(u_j)} e^{18 β C (a_j/ρ_j)²}` and the same-sign pair factor at most
`C₂ e^{β g_λ(u_j)} (a_j/ρ_j)^{2β}`, `C₂ = e^{2βC} 3^{2β}`. -/
theorem ofReal_exp_neg_mul_pairAssignedEnergy_le (hz : nnMap key z = f)
    (hf2 : ∀ i, f (f i) = i) (hRf : ∀ i, i ∈ R ↔ f i ∉ R) [Nontrivial {i // i ∈ R}]
    (h3 : 3 ≤ Fintype.card ι) {S : Finset ι} (hS : ∀ i, f i ∈ S ↔ i ∈ S) {β C lam : ℝ}
    (hβ : 0 ≤ β) (hC : 0 ≤ C) (hlam : 0 < lam) :
    ENNReal.ofReal (Real.exp (-(β * pairAssignedEnergy h3 key lam C S z))) ≤
      ∏ j : {i // i ∈ R}, pairWeight β C lam S j (z (f j) - z j)
        (nnRadius lam (fun l : {i // i ∈ R} => z l) j) := by
  refine (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
    (neg_mul_pairAssignedEnergy_le hz hf2 hRf h3 hS hβ hC hlam))).trans ?_
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le]
  refine Finset.prod_le_prod fun j _ => le_of_eq ?_
  have hs : 0 < displacementScale lam (z (f j) - z j) /
      nnRadius lam (fun l : {i // i ∈ R} => z l) j :=
    div_pos (displacementScale_pos hlam _) (lt_of_lt_of_le hlam (le_nnRadius _ _ _))
  rw [ofReal_exp_pair_le hs]
  rfl

end Integrand


end IsolatedReduction

end TwoComponentCoulomb

end
