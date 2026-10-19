/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.FirstNeighborRadius
public import TwoComponentCoulomb.Frozen.LogKernel
public import TwoComponentCoulomb.Frozen.NearestNeighbor
public import TwoComponentCoulomb.Frozen.SecondNeighborRadius
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.NearestNeighbor.Basic
public import TwoComponentCoulomb.NearestNeighbor.Second
public import TwoComponentCoulomb.Potential.Electric

/-!
# The enlarged radii `τ` of Proposition 2.2 and the interacting pairs

This file collects the combinatorial and metric part of the proof of Proposition 2.2
(`prop:mino2`, source l. 512–593, ball-growth method). Write `φ = nearestNeighbor Z`,
`r₁ = firstNeighborRadius λ Z`, `r₂ = secondNeighborRadius hN λ Z`.

* `tau` : the enlarged radii (source (deftau), l. 513–517): `τᵢ = min (r₂ i) (r₂ (φ i))` when
  `φ (φ i) = i` and `τᵢ = r₂ i` otherwise.
* `lam_le_tau`, `tau_le_secondNeighborRadius`, `tau_eq_of_twoCycle` : `λ ≤ τᵢ ≤ r₂ i` and
  `τ_{φ i} = τᵢ` on a 2-cycle.
* radius calculus : `secondNeighborRadius_le`, `exists_secondNeighborRadius_eq` (the basic
  identities `firstNeighborRadius_eq`, `firstNeighborRadius_le_secondNeighborRadius` come from
  `TwoComponentCoulomb.NearestNeighbor.Second`).
* `isTwoCycle_of_overlap` : (source l. 537–545, (disz)) if `i ≠ j`, the enlarged discs overlap
  and `max (τᵢ, τⱼ) > λ`, then `i` and `j` are the two vertices of a 2-cycle.
* `bracket_eq_zero_of_tau_le` : the pair bracket vanishes when `τᵢ = τⱼ = λ`.
* `abs_secondNeighborRadius_sub_le` : (rrj) on a 2-cycle `|r₂ i - r₂ (φ i)| ≤ ¼ |zᵢ - z_{φ i}|`.
* `sq_norm_div_tau_le` : the displacement ratio (source l. 563–574):
  on a 2-cycle `|z_{φ i} - zᵢ|² / τᵢ² ≤ 64 (r₁ i / r₂ i)²`.
-/

@[expose] public section

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### Calculus of the radii `r₁` and `r₂` -/

section Radii

/-- `|zᵢ - z_{φ i}| ≤ 4 r₁(zᵢ)`. -/
theorem norm_sub_nearestNeighbor_le_four_mul (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : ‖Z i - Z (nearestNeighbor Z i)‖ ≤ 4 * firstNeighborRadius lam Z i := by
  rw [firstNeighborRadius_eq]
  have := le_max_left (‖Z i - Z (nearestNeighbor Z i)‖ / 4) lam
  linarith

/-- Any competitor `k ∉ {i, φ i}` bounds the second-neighbour radius:
`r₂(zᵢ) ≤ (¼ |zᵢ - z_k|) ∨ λ`. -/
theorem secondNeighborRadius_le (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    {i k : Fin N ⊕ Fin N} (hki : k ≠ i) (hkφ : k ≠ nearestNeighbor Z i) :
    secondNeighborRadius hN lam Z i ≤ max (‖Z i - Z k‖ / 4) lam := by
  unfold secondNeighborRadius
  refine max_le_max (div_le_div_of_nonneg_right (Finset.inf'_le _ ?_) (by norm_num)) le_rfl
  exact Finset.mem_erase.2 ⟨hkφ, Finset.mem_erase.2 ⟨hki, Finset.mem_univ _⟩⟩

/-- The competitor in `r₂` is attained: `r₂(zᵢ) = (¼ |zᵢ - z_k|) ∨ λ` for some `k ∉ {i, φ i}`. -/
theorem exists_secondNeighborRadius_eq (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) :
    ∃ k, k ≠ i ∧ k ≠ nearestNeighbor Z i ∧
      secondNeighborRadius hN lam Z i = max (‖Z i - Z k‖ / 4) lam := by
  unfold secondNeighborRadius
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ.erase i).erase
    (nearestNeighbor Z i)) (by
      have hcard : 0 < ((Finset.univ.erase i).erase (nearestNeighbor Z i)).card := by
        have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.erase i)
          (a := nearestNeighbor Z i)
        have h2 := Finset.pred_card_le_card_erase
          (s := (Finset.univ : Finset (Fin N ⊕ Fin N))) (a := i)
        simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at h2
        omega
      exact Finset.card_pos.1 hcard) (fun j => ‖Z i - Z j‖)
  obtain ⟨hkφ, hk'⟩ := Finset.mem_erase.1 hk
  exact ⟨k, (Finset.mem_erase.1 hk').1, hkφ, by rw [hkeq]⟩

/-- If `λ < r₂(zᵢ)` then every `k ∉ {i, φ i}` is at distance at least `4 r₂(zᵢ)` from `zᵢ`. -/
theorem four_mul_secondNeighborRadius_le (hN : 2 ≤ N) {lam : ℝ} (Z : Fin N ⊕ Fin N → ℂ)
    {i k : Fin N ⊕ Fin N} (hlt : lam < secondNeighborRadius hN lam Z i) (hki : k ≠ i)
    (hkφ : k ≠ nearestNeighbor Z i) : 4 * secondNeighborRadius hN lam Z i ≤ ‖Z i - Z k‖ := by
  have h := secondNeighborRadius_le hN lam Z hki hkφ
  rcases le_max_iff.1 h with h | h
  · linarith
  · exact absurd hlt (not_lt.2 h)

/-- (ppj) For mutual nearest neighbours `i`, `j`: `r₂(z_j) ≤ ¼ |zᵢ - z_j| + r₂(zᵢ)`. -/
theorem secondNeighborRadius_le_add (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    {i j : Fin N ⊕ Fin N} (hij : nearestNeighbor Z i = j) (hji : nearestNeighbor Z j = i) :
    secondNeighborRadius hN lam Z j ≤ ‖Z i - Z j‖ / 4 + secondNeighborRadius hN lam Z i := by
  obtain ⟨k, hki, hkφ, hk⟩ := exists_secondNeighborRadius_eq hN lam Z i
  have hkj : k ≠ j := hij ▸ hkφ
  have h := secondNeighborRadius_le hN lam Z (i := j) hkj (hji ▸ hki)
  have htri : ‖Z j - Z k‖ ≤ ‖Z i - Z j‖ + ‖Z i - Z k‖ := by
    calc ‖Z j - Z k‖ = ‖(Z i - Z k) - (Z i - Z j)‖ := by congr 1; ring
      _ ≤ ‖Z i - Z k‖ + ‖Z i - Z j‖ := norm_sub_le _ _
      _ = ‖Z i - Z j‖ + ‖Z i - Z k‖ := add_comm _ _
  refine h.trans ?_
  rw [hk]
  have h1 : ‖Z j - Z k‖ / 4 ≤ ‖Z i - Z j‖ / 4 + ‖Z i - Z k‖ / 4 := by linarith
  have h2 := le_max_left (‖Z i - Z k‖ / 4) lam
  have h3 := le_max_right (‖Z i - Z k‖ / 4) lam
  have h4 : 0 ≤ ‖Z i - Z j‖ / 4 := by positivity
  exact max_le (by linarith) (by linarith)

end Radii

/-! ### The enlarged radii -/

section Tau

/-- The enlarged radii `τᵢ` of the ball-growth proof of Proposition 2.2 (source (deftau),
l. 513–517): `τᵢ = min (r₂ i, r₂ (φ i))` if `i` lies on a 2-cycle of the nearest-neighbour
graph (`φ (φ i) = i`), and `τᵢ = r₂ i` otherwise. -/
noncomputable def tau (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) : ℝ :=
  if nearestNeighbor Z (nearestNeighbor Z i) = i then
    min (secondNeighborRadius hN lam Z i) (secondNeighborRadius hN lam Z (nearestNeighbor Z i))
  else secondNeighborRadius hN lam Z i

theorem tau_of_twoCycle (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) {i : Fin N ⊕ Fin N}
    (hi : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    tau hN lam Z i =
      min (secondNeighborRadius hN lam Z i) (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) := by
  simp [tau, hi]

theorem tau_of_not_twoCycle (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    {i : Fin N ⊕ Fin N} (hi : nearestNeighbor Z (nearestNeighbor Z i) ≠ i) :
    tau hN lam Z i = secondNeighborRadius hN lam Z i := by
  simp [tau, hi]

/-- `λ ≤ τᵢ` (source l. 530, "by definition and (nn3)"). -/
theorem lam_le_tau (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    lam ≤ tau hN lam Z i := by
  unfold tau
  split_ifs
  · exact le_min (lam_le_secondNeighborRadius hN lam Z i)
      (lam_le_secondNeighborRadius hN lam Z _)
  · exact lam_le_secondNeighborRadius hN lam Z i

theorem tau_pos (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : 0 < tau hN lam Z i :=
  hlam.trans_le (lam_le_tau hN lam Z i)

/-- `τᵢ ≤ r₂(zᵢ)`. -/
theorem tau_le_secondNeighborRadius (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) : tau hN lam Z i ≤ secondNeighborRadius hN lam Z i := by
  unfold tau
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- On a 2-cycle `{i, φ i}`: `τ_{φ i} = τᵢ`. -/
theorem tau_eq_of_twoCycle (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) {i : Fin N ⊕ Fin N}
    (hi : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    tau hN lam Z (nearestNeighbor Z i) = tau hN lam Z i := by
  have hj : nearestNeighbor Z (nearestNeighbor Z (nearestNeighbor Z i)) = nearestNeighbor Z i := by
    rw [hi]
  rw [tau_of_twoCycle hN lam Z hj, tau_of_twoCycle hN lam Z hi, hi, min_comm]

end Tau

/-! ### Classification of the interacting pairs (source l. 537–545) -/

section Classification

/-- One-sided version of the classification: `r₂(z_j) ≤ r₂(zᵢ)`, `λ < r₂(zᵢ)` and
`|zᵢ - z_j| < r₂(zᵢ) + r₂(z_j)` force `i`, `j` to be mutual nearest neighbours. -/
theorem mutual_of_lt_secondNeighborRadius_aux (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (Z : Fin N ⊕ Fin N → ℂ) {i j : Fin N ⊕ Fin N} (hij : i ≠ j)
    (hle : secondNeighborRadius hN lam Z j ≤ secondNeighborRadius hN lam Z i)
    (hlt : lam < secondNeighborRadius hN lam Z i)
    (hd : ‖Z i - Z j‖ < secondNeighborRadius hN lam Z i + secondNeighborRadius hN lam Z j) :
    nearestNeighbor Z i = j ∧ nearestNeighbor Z j = i := by
  have hr0 : 0 < secondNeighborRadius hN lam Z i := hlam.trans hlt
  have h1 : nearestNeighbor Z i = j := by
    by_contra hne
    have := four_mul_secondNeighborRadius_le hN Z hlt (k := j) hij.symm (Ne.symm hne)
    linarith
  refine ⟨h1, ?_⟩
  by_contra hne
  have hkj : nearestNeighbor Z j ≠ j := nearestNeighbor_ne Z j
  have hjk : ‖Z j - Z (nearestNeighbor Z j)‖ ≤ ‖Z j - Z i‖ := norm_sub_nearestNeighbor_le Z hij
  rw [norm_sub_rev (Z j) (Z i)] at hjk
  -- the competitor `φ j` bounds `r₂ i` by `d / 2`
  have hA := secondNeighborRadius_le hN lam Z (i := i) (k := nearestNeighbor Z j) hne
    (h1 ▸ hkj)
  have htri : ‖Z i - Z (nearestNeighbor Z j)‖ ≤ 2 * ‖Z i - Z j‖ := by
    calc ‖Z i - Z (nearestNeighbor Z j)‖
        = ‖(Z i - Z j) + (Z j - Z (nearestNeighbor Z j))‖ := by congr 1; ring
      _ ≤ ‖Z i - Z j‖ + ‖Z j - Z (nearestNeighbor Z j)‖ := norm_add_le _ _
      _ ≤ 2 * ‖Z i - Z j‖ := by linarith
  have hA' : secondNeighborRadius hN lam Z i ≤ ‖Z i - Z j‖ / 2 := by
    rcases le_max_iff.1 hA with h | h
    · linarith
    · exact absurd hlt (not_lt.2 h)
  -- `i` is a competitor for `r₂ j`, giving `r₂ j ≤ (d / 4) ∨ λ`
  have hB := secondNeighborRadius_le hN lam Z (i := j) (k := i) hij (Ne.symm hne)
  rw [norm_sub_rev (Z j) (Z i)] at hB
  have hB' : secondNeighborRadius hN lam Z j ≤ ‖Z i - Z j‖ / 2 := by
    rcases le_max_iff.1 hB with h | h
    · have := norm_nonneg (Z i - Z j)
      linarith
    · linarith
  linarith

/-- If `r₂` is large enough for one of two distinct points to see the other
(`|zᵢ - z_j| < r₂ i + r₂ j`, and `max (r₂ i, r₂ j) > λ`), then `i` and `j` are mutual nearest
neighbours. -/
theorem mutual_of_lt_secondNeighborRadius (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (Z : Fin N ⊕ Fin N → ℂ) {i j : Fin N ⊕ Fin N} (hij : i ≠ j)
    (hlt : lam < secondNeighborRadius hN lam Z i ∨ lam < secondNeighborRadius hN lam Z j)
    (hd : ‖Z i - Z j‖ < secondNeighborRadius hN lam Z i + secondNeighborRadius hN lam Z j) :
    nearestNeighbor Z i = j ∧ nearestNeighbor Z j = i := by
  rcases le_total (secondNeighborRadius hN lam Z j) (secondNeighborRadius hN lam Z i) with h | h
  · exact mutual_of_lt_secondNeighborRadius_aux hN hlam Z hij h
      (hlt.elim id fun h' => h'.trans_le h) hd
  · obtain ⟨h1, h2⟩ := mutual_of_lt_secondNeighborRadius_aux hN hlam Z hij.symm h
      (hlt.elim (fun h' => h'.trans_le h) id) (by rwa [norm_sub_rev, add_comm])
    exact ⟨h2, h1⟩

/-- **Classification of the interacting pairs** (source l. 537–545, (disz)): if `i ≠ j`, the
enlarged discs `B(zᵢ, τᵢ)` and `B(z_j, τ_j)` overlap, and `max (τᵢ, τ_j) > λ`, then `{i, j}`
is a 2-cycle of the nearest-neighbour graph. -/
theorem isTwoCycle_of_overlap (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (Z : Fin N ⊕ Fin N → ℂ) {i j : Fin N ⊕ Fin N} (hij : i ≠ j)
    (hd : ‖Z i - Z j‖ < tau hN lam Z i + tau hN lam Z j)
    (hτ : lam < tau hN lam Z i ∨ lam < tau hN lam Z j) :
    nearestNeighbor Z i = j ∧ nearestNeighbor Z j = i := by
  refine mutual_of_lt_secondNeighborRadius hN hlam Z hij
    (hτ.imp (fun h => h.trans_le (tau_le_secondNeighborRadius hN lam Z i))
      (fun h => h.trans_le (tau_le_secondNeighborRadius hN lam Z j))) ?_
  exact hd.trans_le (add_le_add (tau_le_secondNeighborRadius hN lam Z i)
    (tau_le_secondNeighborRadius hN lam Z j))

/-- If `τᵢ = τ_j = λ`, the bracket `g_λ(z_j - zᵢ) - P(zᵢ, τᵢ; z_j, τ_j)` of the pair `(i, j)`
vanishes. -/
theorem bracket_eq_zero_of_tau_le (hN : 2 ≤ N) {lam : ℝ} (Z : Fin N ⊕ Fin N → ℂ)
    {i j : Fin N ⊕ Fin N} (hi : tau hN lam Z i ≤ lam) (hj : tau hN lam Z j ≤ lam) :
    smearedKernel lam (Z j - Z i) -
      pairInteraction (Z i) (Z j) (tau hN lam Z i) (tau hN lam Z j) = 0 := by
  have hi' : tau hN lam Z i = lam := le_antisymm hi (lam_le_tau hN lam Z i)
  have hj' : tau hN lam Z j = lam := le_antisymm hj (lam_le_tau hN lam Z j)
  rw [hi', hj', pairInteraction_eq_smearedKernel, sub_self]

end Classification

/-! ### The displacement ratio (source l. 559–574) -/

section Displacement

/-- (rrj) For mutual nearest neighbours, `|r₂(zᵢ) - r₂(z_j)| ≤ ¼ |zᵢ - z_j|`. -/
theorem abs_secondNeighborRadius_sub_le (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    {i j : Fin N ⊕ Fin N} (hij : nearestNeighbor Z i = j) (hji : nearestNeighbor Z j = i) :
    |secondNeighborRadius hN lam Z i - secondNeighborRadius hN lam Z j| ≤ ‖Z i - Z j‖ / 4 := by
  have h1 := secondNeighborRadius_le_add hN lam Z hij hji
  have h2 := secondNeighborRadius_le_add hN lam Z hji hij
  rw [norm_sub_rev] at h2
  rw [abs_le]
  constructor <;> linarith

/-- **The displacement ratio**, for mutual nearest neighbours `i`, `j` (source l. 563–574):
`|z_j - zᵢ|² / τᵢ² ≤ 64 (r₁(zᵢ) / r₂(zᵢ))²`. -/
theorem sq_norm_div_tau_le_of_mutual (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (Z : Fin N ⊕ Fin N → ℂ) {i j : Fin N ⊕ Fin N} (hij : nearestNeighbor Z i = j)
    (hji : nearestNeighbor Z j = i) :
    ‖Z j - Z i‖ ^ 2 / tau hN lam Z i ^ 2 ≤
      64 * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 := by
  have hi : nearestNeighbor Z (nearestNeighbor Z i) = i := by rw [hij, hji]
  have hτ : tau hN lam Z i = min (secondNeighborRadius hN lam Z i)
      (secondNeighborRadius hN lam Z j) := by
    rw [tau_of_twoCycle hN lam Z hi, hij]
  have hτpos := tau_pos hN hlam Z i
  have hρ4 : ‖Z j - Z i‖ ≤ 4 * firstNeighborRadius lam Z i := by
    have := norm_sub_nearestNeighbor_le_four_mul lam Z i
    rwa [hij, norm_sub_rev] at this
  have hρR := firstNeighborRadius_le_secondNeighborRadius hN lam Z i
  have hρ' : ‖Z j - Z i‖ ≤ 4 * secondNeighborRadius hN lam Z j := by
    have h1 := norm_sub_nearestNeighbor_le_four_mul lam Z j
    have h2 := firstNeighborRadius_le_secondNeighborRadius hN lam Z j
    rw [hji] at h1
    linarith
  have hrr := abs_secondNeighborRadius_sub_le hN lam Z hij hji
  rw [norm_sub_rev] at hrr
  have hRpos : 0 < secondNeighborRadius hN lam Z i :=
    hlam.trans_le (lam_le_secondNeighborRadius hN lam Z i)
  have hd0 := norm_nonneg (Z j - Z i)
  rw [hτ] at hτpos ⊢
  generalize ‖Z j - Z i‖ = d at *
  generalize firstNeighborRadius lam Z i = ρ at *
  generalize secondNeighborRadius hN lam Z i = R at *
  generalize secondNeighborRadius hN lam Z j = R' at *
  have hmain : d * R ≤ 8 * ρ * min R R' := by
    rcases le_or_gt ρ (R / 2) with h | h
    · -- `τ ≥ R - ρ ≥ R / 2`
      have h1 : R / 2 ≤ min R R' := by
        refine le_min (by linarith) ?_
        have := (abs_le.1 hrr).2
        linarith
      nlinarith
    · -- `τ ≥ d / 4`
      have h1 : d / 4 ≤ min R R' := le_min (by linarith) (by linarith)
      nlinarith
  have hfrac : d / min R R' ≤ 8 * (ρ / R) := by
    rw [div_le_iff₀ hτpos]
    have : 8 * (ρ / R) * min R R' = 8 * ρ * min R R' / R := by ring
    rw [this, le_div_iff₀ hRpos]
    linarith
  calc d ^ 2 / min R R' ^ 2 = (d / min R R') ^ 2 := by rw [div_pow]
    _ ≤ (8 * (ρ / R)) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg hd0 hτpos.le) hfrac 2
    _ = 64 * (ρ / R) ^ 2 := by ring

/-- The displacement ratio at a vertex `i` of a 2-cycle (`φ (φ i) = i`). -/
theorem sq_norm_div_tau_le (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (Z : Fin N ⊕ Fin N → ℂ)
    {i : Fin N ⊕ Fin N} (hi : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    ‖Z (nearestNeighbor Z i) - Z i‖ ^ 2 / tau hN lam Z i ^ 2 ≤
      64 * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 :=
  sq_norm_div_tau_le_of_mutual hN hlam Z rfl hi

end Displacement

end TwoComponentCoulomb

end
