/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.Frozen.Energy
public import TwoComponentCoulomb.Frozen.IsGeneric
public import TwoComponentCoulomb.Frozen.IsIsolatedDipole
public import TwoComponentCoulomb.Frozen.IsIsolatedPair
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.Frozen.SecondNeighborRadius
public import TwoComponentCoulomb.NearestNeighbor.General
public import TwoComponentCoulomb.NearestNeighbor.Radius
public import TwoComponentCoulomb.UpperBound.IsolatedRadial
import TwoComponentCoulomb.Frozen.Proposition22
import TwoComponentCoulomb.NearestNeighbor.Isolated
import TwoComponentCoulomb.NearestNeighbor.Second
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# The energy lower bound of the critical case `β = 2` (Proposition 3.10, eq. (eq:critical upper))

Source: l. 1595–1610 (proof of Proposition 3.10, `β = 2`).

Fix a nearest-neighbour map `f` (a self-map of `Fin N ⊕ Fin N`). Its *isolated pairs* are the
2-cycles `{i, f i}` into which no other vertex points (`TwoComponentCoulomb.IsIsoPairOf`; for
`f = φ₁(Z)` this is the frozen `IsIsolatedPair`). In each isolated pair the source retains one
endpoint `w_j` and writes the other as `w_j + u_j`; here the non-retained endpoints form the set
`S = TwoComponentCoulomb.isoSecondVerts f` (the endpoint with the larger index), and the retained
points are all the others. The radius of the pair `s ∈ S` is
`ρ_s = (¼ dist (w, other retained points)) ∨ λ` with `w = z_{f s}`, the first-neighbour radius of
`w` inside the retained configuration (`TwoComponentCoulomb.isoRadius`).

## Main results

* `TwoComponentCoulomb.sum_isoPairVerts`: a sum over the isolated-pair vertices is the sum over
  `s ∈ S` of the two endpoint terms.
* `TwoComponentCoulomb.norm_sub_le_four_mul_isoRadius`,
  `TwoComponentCoulomb.isoRadius_le_two_mul_secondNeighborRadius`,
  `TwoComponentCoulomb.isoRadius_le_three_mul_secondNeighborRadius` (source l. 1595–1597):
  `|u_j| ≤ 4ρ_j` and `ρ_j ≤ 3 r₂(z)` for either endpoint `z` of the pair (in fact `ρ_j ≤ 2 r₂`
  at the retained endpoint).
* `TwoComponentCoulomb.exists_neg_two_mul_energy_le` (source l. 1605–1610): from
  Proposition 2.2, for generic configurations in `Λ`,
  `-2 F_λ + N - |I^dip|/2 + D_R ≤ ∑_{i ∉ I^pair} (g_λ(z_i - z_{φ₁ i}) + c₁) + ∑_{s ∈ S} E_s`,
  where `E_s = 2 g_λ(u_s) + c₂ (a_s/ρ_s)² + 1_{|u_s| > R}` for a neutral pair and
  `E_s = 2 log (|u_s| ∨ λ) - 4 log ρ_s + c₃` for a same-sign pair. This is the source's
  `F_λ ≥ F^nn_λ - C ∑_{neutral}(a_j/ρ_j)² + 2 ∑_{same-sign} log (ρ_j/a_j) - C (q + d)`, with the
  exponent `N - |I^dip|/2 + D_R` distributed over the vertices and `e^{2 g_λ(u)} (a/ρ)⁴` replaced
  by the larger `C (|u| ∨ λ)² / ρ⁴` (`e^{-2 g_λ(u)} ≤ C (|u| ∨ λ)²`).
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

variable {N : ℕ}

/-! ### Isolated 2-cycles of a self-map -/

/-- `{i, f i}` is a 2-cycle of the self-map `f` into which no other vertex points: an isolated pair
of the graph of `f` (for `f = φ₁(Z)` this is `IsIsolatedPair Z i`, ruling R5). -/
def IsIsoPairOf (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (i : Fin N ⊕ Fin N) : Prop :=
  f (f i) = i ∧ ∀ k, (f k = i ∨ f k = f i) → k = i ∨ k = f i

variable {f : Fin N ⊕ Fin N → Fin N ⊕ Fin N}

theorem IsIsoPairOf.apply {i : Fin N ⊕ Fin N} (h : IsIsoPairOf f i) : IsIsoPairOf f (f i) := by
  obtain ⟨h2, hk⟩ := h
  refine ⟨by rw [h2], fun k hk' => ?_⟩
  rw [h2] at hk'
  rcases hk (k := k) hk'.symm with h | h
  · exact Or.inr (by rw [h2]; exact h)
  · exact Or.inl h

variable (f) in
open scoped Classical in
/-- The vertices `I^pair` of the isolated pairs of `f`. -/
noncomputable def isoPairVerts : Finset (Fin N ⊕ Fin N) :=
  univ.filter (IsIsoPairOf f)

variable (f) in
open scoped Classical in
/-- The non-retained endpoints of the isolated pairs: the endpoint `s` of the larger index in the
source numbering (so that the retained endpoint is `f s`). -/
noncomputable def isoSecondVerts : Finset (Fin N ⊕ Fin N) :=
  univ.filter fun s => IsIsoPairOf f s ∧ sumKey N (f s) < sumKey N s

theorem mem_isoPairVerts {i : Fin N ⊕ Fin N} : i ∈ isoPairVerts f ↔ IsIsoPairOf f i := by
  simp [isoPairVerts]

theorem mem_isoSecondVerts {s : Fin N ⊕ Fin N} :
    s ∈ isoSecondVerts f ↔ IsIsoPairOf f s ∧ sumKey N (f s) < sumKey N s := by
  simp [isoSecondVerts]

theorem isoSecondVerts_subset : isoSecondVerts f ⊆ isoPairVerts f := fun _ hs =>
  mem_isoPairVerts.2 (mem_isoSecondVerts.1 hs).1

/-- The retained endpoint `f s` of a pair is not a non-retained endpoint. -/
theorem apply_notMem_isoSecondVerts {s : Fin N ⊕ Fin N} (hs : s ∈ isoSecondVerts f) :
    f s ∉ isoSecondVerts f := by
  intro h
  obtain ⟨⟨h2, -⟩, hlt⟩ := mem_isoSecondVerts.1 hs
  obtain ⟨-, hlt'⟩ := mem_isoSecondVerts.1 h
  rw [h2] at hlt'
  exact lt_asymm hlt hlt'

theorem apply_mem_isoPairVerts {i : Fin N ⊕ Fin N} (hi : i ∈ isoPairVerts f) :
    f i ∈ isoPairVerts f :=
  mem_isoPairVerts.2 (mem_isoPairVerts.1 hi).apply

/-- `f` maps the vertices outside `I^pair` to vertices outside `I^pair`. -/
theorem apply_notMem_isoPairVerts (hf0 : ∀ i, f i ≠ i) {i : Fin N ⊕ Fin N}
    (hi : i ∉ isoPairVerts f) : f i ∉ isoPairVerts f := by
  intro h
  have h' := mem_isoPairVerts.1 h
  rcases h'.2 i (Or.inl rfl) with h1 | h1
  · exact hf0 i h1.symm
  · apply hi
    have := h'.apply
    rw [← h1] at this
    exact mem_isoPairVerts.2 this

theorem mem_isoSecondVerts_or (hf0 : ∀ i, f i ≠ i) {i : Fin N ⊕ Fin N}
    (hi : i ∈ isoPairVerts f) : i ∈ isoSecondVerts f ∨ f i ∈ isoSecondVerts f := by
  have h := mem_isoPairVerts.1 hi
  rcases lt_or_gt_of_ne (fun h' => hf0 i ((sumKey N).injective h')) with hlt | hlt
  · exact Or.inl (mem_isoSecondVerts.2 ⟨h, hlt⟩)
  · refine Or.inr (mem_isoSecondVerts.2 ⟨h.apply, ?_⟩)
    rw [h.1]
    exact hlt

theorem injOn_isoSecondVerts : Set.InjOn f (isoSecondVerts f) := by
  intro s hs s' hs' h
  have h1 := (mem_isoSecondVerts.1 hs).1.1
  have h2 := (mem_isoSecondVerts.1 hs').1.1
  rw [← h1, ← h2, h]

theorem disjoint_isoSecondVerts_image :
    Disjoint (isoSecondVerts f) ((isoSecondVerts f).image f) := by
  refine Finset.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx'
  exact apply_notMem_isoSecondVerts hs hx

/-- `I^pair = S ⊔ f(S)`. -/
theorem isoPairVerts_eq_union (hf0 : ∀ i, f i ≠ i) :
    isoPairVerts f = isoSecondVerts f ∪ (isoSecondVerts f).image f := by
  ext i
  rw [Finset.mem_union, Finset.mem_image]
  constructor
  · intro hi
    rcases mem_isoSecondVerts_or hf0 hi with h | h
    · exact Or.inl h
    · exact Or.inr ⟨f i, h, (mem_isoPairVerts.1 hi).1⟩
  · rintro (h | ⟨s, hs, rfl⟩)
    · exact isoSecondVerts_subset h
    · exact apply_mem_isoPairVerts (isoSecondVerts_subset hs)

/-- A sum over the isolated-pair vertices is the sum over the non-retained endpoints `s` of the
two endpoint terms. -/
theorem sum_isoPairVerts (hf0 : ∀ i, f i ≠ i) (w : Fin N ⊕ Fin N → ℝ) :
    ∑ i ∈ isoPairVerts f, w i = ∑ s ∈ isoSecondVerts f, (w s + w (f s)) := by
  rw [isoPairVerts_eq_union hf0, Finset.sum_union disjoint_isoSecondVerts_image,
    Finset.sum_image injOn_isoSecondVerts, Finset.sum_add_distrib]

theorem card_isoPairVerts (hf0 : ∀ i, f i ≠ i) :
    (isoPairVerts f).card = 2 * (isoSecondVerts f).card := by
  rw [isoPairVerts_eq_union hf0, Finset.card_union_of_disjoint disjoint_isoSecondVerts_image,
    Finset.card_image_of_injOn injOn_isoSecondVerts]
  ring

/-- There are at most `N` non-retained endpoints. -/
theorem card_isoSecondVerts_le : (isoSecondVerts f).card ≤ N := by
  have h1 := Finset.card_union_of_disjoint (disjoint_isoSecondVerts_image (f := f))
  rw [Finset.card_image_of_injOn injOn_isoSecondVerts] at h1
  have h2 := Finset.card_le_univ (isoSecondVerts f ∪ (isoSecondVerts f).image f)
  have h3 : Fintype.card (Fin N ⊕ Fin N) = 2 * N := by simp [two_mul]
  omega

variable (f) in
/-- For `N ≥ 2` there are at least two retained points. -/
theorem nontrivial_isoRetained (hN : 2 ≤ N) : Nontrivial {i // i ∉ isoSecondVerts f} := by
  rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_subtype_compl, Fintype.card_coe]
  have h1 := card_isoSecondVerts_le (f := f)
  have h3 : Fintype.card (Fin N ⊕ Fin N) = 2 * N := by simp [two_mul]
  omega

/-- The retained endpoint `f s` of the pair of a non-retained endpoint `s`. -/
def isoPartner (s : {s // s ∈ isoSecondVerts f}) : {i // i ∉ isoSecondVerts f} :=
  ⟨f s, apply_notMem_isoSecondVerts s.2⟩

@[simp] theorem isoPartner_coe (s : {s // s ∈ isoSecondVerts f}) : (isoPartner s : _) = f s :=
  rfl

/-! ### The radius of a pair -/

variable (f) in
/-- The radius `ρ` of a retained point `r` (source l. 1595): the first-neighbour radius
`(¼ min_{k retained, k ≠ r} |y_r - y_k|) ∨ λ` of `r` inside the retained configuration `y`. -/
noncomputable def isoRadius (hN : 2 ≤ N) (lam : ℝ) (y : {i // i ∉ isoSecondVerts f} → ℂ)
    (r : {i // i ∉ isoSecondVerts f}) : ℝ :=
  haveI := nontrivial_isoRetained f hN
  nnRadius lam y r

theorem lam_le_isoRadius (hN : 2 ≤ N) (lam : ℝ) (y : {i // i ∉ isoSecondVerts f} → ℂ)
    (r : {i // i ∉ isoSecondVerts f}) : lam ≤ isoRadius f hN lam y r := by
  have := nontrivial_isoRetained f hN
  exact le_nnRadius lam y r

theorem measurable_isoRadius (hN : 2 ≤ N) (lam : ℝ) (r : {i // i ∉ isoSecondVerts f}) :
    Measurable fun y : {i // i ∉ isoSecondVerts f} → ℂ => isoRadius f hN lam y r := by
  have := nontrivial_isoRetained f hN
  exact measurable_nnRadius lam r

/-- The radius is `max (D/4) λ` with `D` the minimal distance to the other retained points. -/
theorem isoRadius_spec (hN : 2 ≤ N) (lam : ℝ) (y : {i // i ∉ isoSecondVerts f} → ℂ)
    (r : {i // i ∉ isoSecondVerts f}) :
    ∃ D : ℝ, isoRadius f hN lam y r = max (D / 4) lam ∧
      (∀ k, k ≠ r → D ≤ ‖y r - y k‖) ∧ ∀ t : ℝ, (∀ k, k ≠ r → t ≤ ‖y r - y k‖) → t ≤ D := by
  have := nontrivial_isoRetained f hN
  unfold isoRadius nnRadius
  refine ⟨_, rfl, fun k hk => Finset.inf'_le _ ?_, fun t ht => Finset.le_inf' _ _ fun k hk => ?_⟩
  · convert Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩
  · refine ht k ?_
    have hk' : k ∈ Finset.univ.erase r := by convert hk
    exact (Finset.mem_erase.1 hk').1

/-- `r₂(z_i) ≥ (t/4) ∨ λ` as soon as `t ≤ |z_i - z_j|` for all `j ∉ {i, φ₁ i}`. -/
theorem le_secondNeighborRadius_of (hN : 2 ≤ N) (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) {t : ℝ}
    (h : ∀ j, j ≠ i → j ≠ nearestNeighbor Z i → t ≤ ‖Z i - Z j‖) :
    max (t / 4) lam ≤ secondNeighborRadius hN lam Z i := by
  rw [secondNeighborRadius_eq]
  have := h _ (secondNearestNeighbor_ne_self hN Z i)
    (secondNearestNeighbor_ne_nearestNeighbor hN Z i)
  exact max_le_max (by linarith) le_rfl

section Radii

variable {Z : Fin N ⊕ Fin N → ℂ} (hf : nearestNeighbor Z = f)
include hf

theorem nearestNeighbor_apply_of_mem {s : Fin N ⊕ Fin N} (hs : s ∈ isoSecondVerts f) :
    nearestNeighbor Z (f s) = s := by
  rw [hf]
  exact (mem_isoSecondVerts.1 hs).1.1

/-- **`|u_j| ≤ 4ρ_j`** . -/
theorem norm_sub_le_four_mul_isoRadius (hN : 2 ≤ N) (lam : ℝ) (s : {s // s ∈ isoSecondVerts f}) :
    ‖Z s - Z (f s)‖ ≤ 4 * isoRadius f hN lam (fun k => Z k) (isoPartner s) := by
  obtain ⟨D, hρ, -, hD⟩ := isoRadius_spec hN lam (fun k => Z k) (isoPartner s)
  have hu : ‖Z s - Z (f s)‖ ≤ D := by
    refine hD _ fun k hk => ?_
    have hk' : (k : Fin N ⊕ Fin N) ≠ f s := fun h => hk (Subtype.ext h)
    have := norm_sub_nearestNeighbor_le Z hk'
    rw [nearestNeighbor_apply_of_mem hf s.2] at this
    rw [norm_sub_rev]
    exact this
  rw [hρ]
  have := le_max_left (D / 4) lam
  linarith

/-- **`ρ_j ≤ 2 r₂(w_j)`** at the retained endpoint `w_j = z_{f s}` (source l. 1597). -/
theorem isoRadius_le_two_mul_secondNeighborRadius (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (s : {s // s ∈ isoSecondVerts f}) :
    isoRadius f hN lam (fun k => Z k) (isoPartner s) ≤
      2 * secondNeighborRadius hN lam Z (f s) := by
  obtain ⟨D, hρ, hDle, hD⟩ := isoRadius_spec hN lam (fun k => Z k) (isoPartner s)
  have hD0 : 0 ≤ D := hD 0 fun _ _ => norm_nonneg _
  have hs := s.2
  have key : ∀ j, j ≠ f s → j ≠ nearestNeighbor Z (f s) → D / 2 ≤ ‖Z (f s) - Z j‖ := by
    intro j hj1 hj2
    rw [nearestNeighbor_apply_of_mem hf hs] at hj2
    by_cases hjS : j ∈ isoSecondVerts f
    · have hfj : f j ≠ f s := fun h => hj2 (injOn_isoSecondVerts hjS hs h)
      have h1 := hDle ⟨f j, apply_notMem_isoSecondVerts hjS⟩
        (fun h => hfj (congrArg Subtype.val h))
      simp only [isoPartner_coe] at h1
      have hjfs : f s ≠ j := fun h => apply_notMem_isoSecondVerts hs (h ▸ hjS)
      have h2 := norm_sub_nearestNeighbor_le Z hjfs
      rw [hf] at h2
      have h3 := norm_sub_le_norm_sub_add_norm_sub (Z (f s)) (Z j) (Z (f j))
      rw [norm_sub_rev (Z j) (Z (f s))] at h2
      linarith
    · have h1 := hDle ⟨j, hjS⟩ (fun h => hj1 (congrArg Subtype.val h))
      simp only [isoPartner_coe] at h1
      linarith
  have h := le_secondNeighborRadius_of hN lam Z (f s) key
  rw [hρ]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h (by norm_num))
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  exact max_le_max (by linarith) (by linarith)

/-- **`ρ_j ≤ 3 r₂(w_j + u_j)`** at the non-retained endpoint `s` (source l. 1597). -/
theorem isoRadius_le_three_mul_secondNeighborRadius (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (s : {s // s ∈ isoSecondVerts f}) :
    isoRadius f hN lam (fun k => Z k) (isoPartner s) ≤
      3 * secondNeighborRadius hN lam Z s := by
  obtain ⟨D, hρ, hDle, hD⟩ := isoRadius_spec hN lam (fun k => Z k) (isoPartner s)
  have hD0 : 0 ≤ D := hD 0 fun _ _ => norm_nonneg _
  have hs := s.2
  have hφs : nearestNeighbor Z s = f s := by rw [hf]
  have key : ∀ j, j ≠ (s : Fin N ⊕ Fin N) → j ≠ nearestNeighbor Z s →
      D / 3 ≤ ‖Z s - Z j‖ := by
    intro j hj1 hj2
    rw [hφs] at hj2
    -- `|z_s - z_{f s}| ≤ |z_s - z_j|`
    have hA := norm_sub_nearestNeighbor_le Z hj1
    rw [hφs] at hA
    by_cases hjS : j ∈ isoSecondVerts f
    · have hfj : f j ≠ f s := fun h => hj1 (injOn_isoSecondVerts hjS hs h)
      have h1 := hDle ⟨f j, apply_notMem_isoSecondVerts hjS⟩
        (fun h => hfj (congrArg Subtype.val h))
      simp only [isoPartner_coe] at h1
      have hsj : (s : Fin N ⊕ Fin N) ≠ j := fun h => hj1 h.symm
      have h2 := norm_sub_nearestNeighbor_le Z hsj
      rw [hf] at h2
      have h3 := norm_sub_le_norm_sub_add_norm_sub (Z (f s)) (Z s) (Z (f j))
      have h4 := norm_sub_le_norm_sub_add_norm_sub (Z s) (Z j) (Z (f j))
      rw [norm_sub_rev (Z (f s)) (Z s)] at h3
      rw [norm_sub_rev (Z j) (Z s)] at h2
      linarith
    · have h1 := hDle ⟨j, hjS⟩ (fun h => hj2 (congrArg Subtype.val h))
      simp only [isoPartner_coe] at h1
      have h3 := norm_sub_le_norm_sub_add_norm_sub (Z (f s)) (Z s) (Z j)
      rw [norm_sub_rev (Z (f s)) (Z s)] at h3
      linarith
  have h := le_secondNeighborRadius_of hN lam Z s key
  rw [hρ]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h (by norm_num))
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3)]
  exact max_le_max (by linarith) (by linarith)

end Radii

/-! ### The exponent of an isolated pair -/

/-- The exponent `E_s` of the isolated pair of the non-retained endpoint `s` (source
l. 1606–1610): with `u = z_s - z_{f s}` and `ρ = ρ_s`, `2 g_λ(u) + c₂ (a(u)/ρ)² + 1_{|u| > R}`
for a neutral pair and `2 log (|u| ∨ λ) - 4 log ρ + c₃` for a same-sign pair. -/
noncomputable def critPairExponent (hN : 2 ≤ N) (lam R c₂ c₃ : ℝ) (Z : Fin N ⊕ Fin N → ℂ)
    (s : {s // s ∈ isoSecondVerts f}) : ℝ :=
  if charge (s : Fin N ⊕ Fin N) * charge (f s) = -1 then
    2 * smearedKernel lam (Z s - Z (f s)) +
      c₂ * (displacementScale lam (Z s - Z (f s)) /
        isoRadius f hN lam (fun k => Z k) (isoPartner s)) ^ 2 +
      (if R < ‖Z s - Z (f s)‖ then 1 else 0)
  else
    2 * Real.log (max ‖Z s - Z (f s)‖ lam) -
      4 * Real.log (isoRadius f hN lam (fun k => Z k) (isoPartner s)) + c₃

/-! ### The energy bound -/

section Energy

/-- The tree term: `g(r₂) + κ ≤ g_λ(z_i - z_{φ₁ i}) + C`. -/
theorem tree_term_le (hN : 2 ≤ N) {Cg : ℝ}
    (hCg : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, -Real.log (max ‖z‖ lam) - Cg ≤ smearedKernel lam z)
    {lam : ℝ} (hlam : 0 < lam) (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    logKernel ((secondNeighborRadius hN lam Z i : ℝ) : ℂ) + kappa ≤
      smearedKernel lam (Z i - Z (nearestNeighbor Z i)) + (|Cg| + Real.log 4 + |kappa|) := by
  have hr1 : 0 < firstNeighborRadius lam Z i := hlam.trans_le (lam_le_firstNeighborRadius lam Z i)
  have hr12 := firstNeighborRadius_le_secondNeighborRadius hN lam Z i
  rw [logKernel_ofReal (hr1.trans_le hr12)]
  have := Real.log_le_log hr1 hr12
  have := smearedKernel_add_log_firstNeighborRadius_ge hCg hlam Z i
  have := le_abs_self Cg
  have := le_abs_self kappa
  linarith

/-- The cycle term of a vertex on a 2-cycle (not necessarily isolated):
`-[d d' g_λ - d (d + d') (g(r₂ ∧ r₂') + κ) - C (r₁/r₂)²] ≤ g_λ + C'`. -/
theorem cycle_term_le (hN : 2 ≤ N) {Cg C : ℝ}
    (hCg : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, -Real.log (max ‖z‖ lam) - Cg ≤ smearedKernel lam z)
    (hC : 0 ≤ C) {lam : ℝ} (hlam : 0 < lam) (Z : Fin N ⊕ Fin N → ℂ) {i : Fin N ⊕ Fin N}
    (hcyc : nearestNeighbor Z (nearestNeighbor Z i) = i) :
    -(charge i * charge (nearestNeighbor Z i) * smearedKernel lam (Z i - Z (nearestNeighbor Z i))
        - charge i * (charge i + charge (nearestNeighbor Z i)) *
            (logKernel ((min (secondNeighborRadius hN lam Z i)
              (secondNeighborRadius hN lam Z (nearestNeighbor Z i)) : ℝ) : ℂ) + kappa)
        - C * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2) ≤
      smearedKernel lam (Z i - Z (nearestNeighbor Z i)) +
        (2 * |Cg| + 2 * Real.log 4 + 2 * |kappa| + C) := by
  have hr1 : 0 < firstNeighborRadius lam Z i := hlam.trans_le (lam_le_firstNeighborRadius lam Z i)
  have hr12 := firstNeighborRadius_le_secondNeighborRadius hN lam Z i
  have hr2 : 0 < secondNeighborRadius hN lam Z i := hr1.trans_le hr12
  have hq1 : (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 ≤ 1 :=
    pow_le_one₀ (div_nonneg hr1.le hr2.le) ((div_le_one hr2).2 hr12)
  have hCq : C * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 ≤ C :=
    mul_le_of_le_one_right hC hq1
  have hτ := firstNeighborRadius_le_min_secondNeighborRadius hN lam Z hcyc
  have hτpos := hr1.trans_le hτ
  rw [logKernel_ofReal hτpos]
  have hlogτ := Real.log_le_log hr1 hτ
  have hG := smearedKernel_add_log_firstNeighborRadius_ge hCg hlam Z i
  have hCg1 := le_abs_self Cg
  have hκ1 := le_abs_self kappa
  have hCg0 := abs_nonneg Cg
  have hκ0 := abs_nonneg kappa
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  generalize (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 = q at hCq ⊢
  rcases charge_eq_one_or_neg_one i with h | h <;>
    rcases charge_eq_one_or_neg_one (nearestNeighbor Z i) with h' | h' <;>
    · rw [h, h']
      linarith only [hCq, hG, hlogτ, hCg1, hκ1, hCg0, hκ0, hl4]

/-- `(a/r₂)² ≤ k² (a/ρ)²` when `ρ ≤ k r₂`. -/
theorem sq_div_le_of_le_mul {a ρ r k : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) (hr : 0 < r)
    (h : ρ ≤ k * r) : (a / r) ^ 2 ≤ k ^ 2 * (a / ρ) ^ 2 := by
  have h1 : a / r ≤ k * (a / ρ) := by
    rw [div_le_iff₀ hr]
    calc a = (a / ρ) * ρ := by field_simp
      _ ≤ (a / ρ) * (k * r) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = k * (a / ρ) * r := by ring
  calc (a / r) ^ 2 ≤ (k * (a / ρ)) ^ 2 := pow_le_pow_left₀ (div_nonneg ha hr.le) h1 2
    _ = k ^ 2 * (a / ρ) ^ 2 := by ring

/-- The two cycle terms of an isolated neutral pair:
`-T_s - T_{f s} ≤ 2 g_λ(u_s) + 13 C (a/ρ)²` (source l. 1606). -/
theorem neutral_pair_term_le (hN : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C) {lam : ℝ} (hlam : 0 < lam)
    (Z : Fin N ⊕ Fin N → ℂ) (s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)})
    (hn : charge (s : Fin N ⊕ Fin N) * charge (nearestNeighbor Z s) = -1) :
    -(charge (s : Fin N ⊕ Fin N) * charge (nearestNeighbor Z s) *
          smearedKernel lam (Z s - Z (nearestNeighbor Z s))
        - charge (s : Fin N ⊕ Fin N) * (charge (s : Fin N ⊕ Fin N) + charge (nearestNeighbor Z s)) *
            (logKernel ((min (secondNeighborRadius hN lam Z s)
              (secondNeighborRadius hN lam Z (nearestNeighbor Z s)) : ℝ) : ℂ) + kappa)
        - C * (firstNeighborRadius lam Z s / secondNeighborRadius hN lam Z s) ^ 2)
      - (charge (nearestNeighbor Z s) * charge (nearestNeighbor Z (nearestNeighbor Z s)) *
          smearedKernel lam (Z (nearestNeighbor Z s) - Z (nearestNeighbor Z (nearestNeighbor Z s)))
        - charge (nearestNeighbor Z s) *
            (charge (nearestNeighbor Z s) + charge (nearestNeighbor Z (nearestNeighbor Z s))) *
            (logKernel ((min (secondNeighborRadius hN lam Z (nearestNeighbor Z s))
              (secondNeighborRadius hN lam Z (nearestNeighbor Z (nearestNeighbor Z s))) : ℝ) : ℂ)
              + kappa)
        - C * (firstNeighborRadius lam Z (nearestNeighbor Z s) /
            secondNeighborRadius hN lam Z (nearestNeighbor Z s)) ^ 2) ≤
      2 * smearedKernel lam (Z s - Z (nearestNeighbor Z s)) +
        13 * C * (displacementScale lam (Z s - Z (nearestNeighbor Z s)) /
          isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s)) ^ 2 := by
  have hs := s.2
  have h2 : nearestNeighbor Z (nearestNeighbor Z s) = s := (mem_isoSecondVerts.1 hs).1.1
  rw [h2]
  set ρ := isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s) with hρdef
  have hρ0 : 0 < ρ := hlam.trans_le (lam_le_isoRadius hN lam _ _)
  have hρs := isoRadius_le_three_mul_secondNeighborRadius rfl hN hlam s
  have hρr := isoRadius_le_two_mul_secondNeighborRadius rfl hN hlam s
  rw [← hρdef] at hρs hρr
  set a := displacementScale lam (Z s - Z (nearestNeighbor Z s)) with ha
  have ha0 : 0 ≤ a := (displacementScale_pos hlam _).le
  have hr1s : firstNeighborRadius lam Z s = a := by
    rw [firstNeighborRadius_eq, ha, displacementScale]
  have hr1r : firstNeighborRadius lam Z (nearestNeighbor Z s) = a := by
    rw [firstNeighborRadius_eq, h2, ha, displacementScale, norm_sub_rev]
  have hgr : smearedKernel lam (Z (nearestNeighbor Z s) - Z s) =
      smearedKernel lam (Z s - Z (nearestNeighbor Z s)) := by
    rw [← neg_sub, smearedKernel_neg]
  have hr2s : 0 < secondNeighborRadius hN lam Z s :=
    hlam.trans_le (lam_le_secondNeighborRadius hN lam Z s)
  have hr2r : 0 < secondNeighborRadius hN lam Z (nearestNeighbor Z s) :=
    hlam.trans_le (lam_le_secondNeighborRadius hN lam Z (nearestNeighbor Z s))
  have hqs := sq_div_le_of_le_mul ha0 hρ0 hr2s hρs
  have hqr := sq_div_le_of_le_mul ha0 hρ0 hr2r hρr
  rw [hr1s] at *
  rw [hr1r, hgr]
  have hsum : charge (s : Fin N ⊕ Fin N) + charge (nearestNeighbor Z s) = 0 := by
    rcases charge_eq_one_or_neg_one (s : Fin N ⊕ Fin N) with h | h <;>
      rcases charge_eq_one_or_neg_one (nearestNeighbor Z s) with h' | h' <;>
      (rw [h, h'] at hn ⊢; first | (norm_num at hn; done) | norm_num)
  have hn' : charge (nearestNeighbor Z s) * charge (s : Fin N ⊕ Fin N) = -1 := by
    rw [mul_comm]; exact hn
  have hsum' : charge (nearestNeighbor Z s) + charge (s : Fin N ⊕ Fin N) = 0 := by
    rw [add_comm]; exact hsum
  rw [hn, hn', hsum, hsum', mul_zero, mul_zero, zero_mul, zero_mul]
  have e1 : C * (a / secondNeighborRadius hN lam Z s) ^ 2 ≤ C * (3 ^ 2 * (a / ρ) ^ 2) :=
    mul_le_mul_of_nonneg_left hqs hC
  have e2 : C * (a / secondNeighborRadius hN lam Z (nearestNeighbor Z s)) ^ 2 ≤
      C * (2 ^ 2 * (a / ρ) ^ 2) :=
    mul_le_mul_of_nonneg_left hqr hC
  generalize (a / secondNeighborRadius hN lam Z s) ^ 2 = q1 at e1 ⊢
  generalize (a / secondNeighborRadius hN lam Z (nearestNeighbor Z s)) ^ 2 = q2 at e2 ⊢
  generalize (a / ρ) ^ 2 = w at e1 e2 ⊢
  linarith only [e1, e2]

/-- The two cycle terms of an isolated same-sign pair:
`-T_s - T_{f s} ≤ 2 log (|u_s| ∨ λ) - 4 log ρ + C'` (source l. 1606, with
`-g_λ(u) ≤ log (|u| ∨ λ) + C` and `r₂ ≥ ρ/3` at both endpoints). -/
theorem sameSign_pair_term_le (hN : 2 ≤ N) {Cg C : ℝ}
    (hCg : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, -Real.log (max ‖z‖ lam) - Cg ≤ smearedKernel lam z)
    (hC : 0 ≤ C) {lam : ℝ} (hlam : 0 < lam)
    (Z : Fin N ⊕ Fin N → ℂ) (s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)})
    (hn : ¬ charge (s : Fin N ⊕ Fin N) * charge (nearestNeighbor Z s) = -1) :
    -(charge (s : Fin N ⊕ Fin N) * charge (nearestNeighbor Z s) *
          smearedKernel lam (Z s - Z (nearestNeighbor Z s))
        - charge (s : Fin N ⊕ Fin N) * (charge (s : Fin N ⊕ Fin N) + charge (nearestNeighbor Z s)) *
            (logKernel ((min (secondNeighborRadius hN lam Z s)
              (secondNeighborRadius hN lam Z (nearestNeighbor Z s)) : ℝ) : ℂ) + kappa)
        - C * (firstNeighborRadius lam Z s / secondNeighborRadius hN lam Z s) ^ 2)
      - (charge (nearestNeighbor Z s) * charge (nearestNeighbor Z (nearestNeighbor Z s)) *
          smearedKernel lam (Z (nearestNeighbor Z s) - Z (nearestNeighbor Z (nearestNeighbor Z s)))
        - charge (nearestNeighbor Z s) *
            (charge (nearestNeighbor Z s) + charge (nearestNeighbor Z (nearestNeighbor Z s))) *
            (logKernel ((min (secondNeighborRadius hN lam Z (nearestNeighbor Z s))
              (secondNeighborRadius hN lam Z (nearestNeighbor Z (nearestNeighbor Z s))) : ℝ) : ℂ)
              + kappa)
        - C * (firstNeighborRadius lam Z (nearestNeighbor Z s) /
            secondNeighborRadius hN lam Z (nearestNeighbor Z s)) ^ 2) ≤
      2 * Real.log (max ‖Z s - Z (nearestNeighbor Z s)‖ lam) -
        4 * Real.log (isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s)) +
        (2 * |Cg| + 4 * Real.log 3 + 4 * |kappa| + 2 * C) := by
  have hs := s.2
  have h2 : nearestNeighbor Z (nearestNeighbor Z s) = s := (mem_isoSecondVerts.1 hs).1.1
  rw [h2]
  set ρ := isoRadius (nearestNeighbor Z) hN lam (fun k => Z k) (isoPartner s) with hρdef
  have hρ0 : 0 < ρ := hlam.trans_le (lam_le_isoRadius hN lam _ _)
  have hρs := isoRadius_le_three_mul_secondNeighborRadius rfl hN hlam s
  have hρr := isoRadius_le_two_mul_secondNeighborRadius rfl hN hlam s
  rw [← hρdef] at hρs hρr
  have hr2s : 0 < secondNeighborRadius hN lam Z s :=
    hlam.trans_le (lam_le_secondNeighborRadius hN lam Z s)
  have hr2r : 0 < secondNeighborRadius hN lam Z (nearestNeighbor Z s) :=
    hlam.trans_le (lam_le_secondNeighborRadius hN lam Z (nearestNeighbor Z s))
  -- the minima are at least `ρ/3`
  have hτ : ρ / 3 ≤
      min (secondNeighborRadius hN lam Z s) (secondNeighborRadius hN lam Z (nearestNeighbor Z s)) :=
    le_min (by linarith) (by linarith)
  have hτ' : ρ / 3 ≤
      min (secondNeighborRadius hN lam Z (nearestNeighbor Z s)) (secondNeighborRadius hN lam Z s) :=
    le_min (by linarith) (by linarith)
  have hτpos : 0 < min (secondNeighborRadius hN lam Z s)
      (secondNeighborRadius hN lam Z (nearestNeighbor Z s)) :=
    lt_min hr2s hr2r
  have hτpos' : 0 < min (secondNeighborRadius hN lam Z (nearestNeighbor Z s))
      (secondNeighborRadius hN lam Z s) :=
    lt_min hr2r hr2s
  rw [logKernel_ofReal hτpos, logKernel_ofReal hτpos']
  have hl1 := Real.log_le_log (by positivity) hτ
  have hl2 := Real.log_le_log (by positivity) hτ'
  rw [Real.log_div hρ0.ne' (by norm_num)] at hl1 hl2
  -- the quotients `(r₁/r₂)²` are at most `1`
  have hq : ∀ i, C * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 ≤ C := by
    intro i
    have hr1 : 0 < firstNeighborRadius lam Z i := hlam.trans_le (lam_le_firstNeighborRadius lam Z i)
    have hr12 := firstNeighborRadius_le_secondNeighborRadius hN lam Z i
    exact mul_le_of_le_one_right hC
      (pow_le_one₀ (div_nonneg hr1.le (hr1.trans_le hr12).le)
        ((div_le_one (hr1.trans_le hr12)).2 hr12))
  have hqs := hq s
  have hqr := hq (nearestNeighbor Z s)
  -- `-g_λ(u) ≤ log (|u| ∨ λ) + C_g`
  have hgs := hCg lam hlam (Z s - Z (nearestNeighbor Z s))
  have hgr := hCg lam hlam (Z (nearestNeighbor Z s) - Z s)
  rw [norm_sub_rev (Z (nearestNeighbor Z s)) (Z s)] at hgr
  have hss : charge (s : Fin N ⊕ Fin N) * charge (nearestNeighbor Z s) = 1 := by
    rcases charge_eq_one_or_neg_one (s : Fin N ⊕ Fin N) with h | h <;>
      rcases charge_eq_one_or_neg_one (nearestNeighbor Z s) with h' | h' <;>
      (rw [h, h'] at hn ⊢; first | (norm_num at hn; done) | norm_num)
  have hss' : charge (nearestNeighbor Z s) * charge (s : Fin N ⊕ Fin N) = 1 := by
    rw [mul_comm]; exact hss
  have hD : charge (s : Fin N ⊕ Fin N) *
      (charge (s : Fin N ⊕ Fin N) + charge (nearestNeighbor Z s)) = 2 := by
    rw [mul_add, charge_mul_self, hss]; norm_num
  have hD' : charge (nearestNeighbor Z s) *
      (charge (nearestNeighbor Z s) + charge (s : Fin N ⊕ Fin N)) = 2 := by
    rw [mul_add, charge_mul_self, hss']; norm_num
  rw [hss, hss', hD, hD']
  have := le_abs_self Cg
  have := le_abs_self kappa
  linarith

theorem card_filter_isIsolatedDipole_long (Z : Fin N ⊕ Fin N → ℂ) (R : ℝ)
    [DecidablePred fun i => IsIsolatedDipole Z i ∧ R < ‖Z i - Z (nearestNeighbor Z i)‖] :
    (univ.filter fun i => IsIsolatedDipole Z i ∧ R < ‖Z i - Z (nearestNeighbor Z i)‖).card =
      2 * (longIsolatedDipoles Z R).card := by
  classical
  unfold longIsolatedDipoles
  convert card_filter_eq_two_mul_card_image_pair Z
    (fun i => IsIsolatedDipole Z i ∧ R < ‖Z i - Z (nearestNeighbor Z i)‖)
    (fun i hi => ⟨hi.1.1, isIsolatedDipole_nearestNeighbor hi.1, by
      rw [hi.1.1, norm_sub_rev]; exact hi.2⟩)

/-- **The energy lower bound of the critical case** (source l. 1605–1610, from
Proposition 2.2). There are constants `c₁, c₂ ≥ 0` and `c₃` such that for `N ≥ 2`, `λ > 0`,
`R ∈ ℝ` and every generic configuration `Z` in `Λ`, with `f = φ₁(Z)`,
`-2 F_λ(Z) + N - |I^dip|/2 + D_R ≤ ∑_{i ∉ I^pair} (g_λ(z_i - z_{f i}) + c₁) + ∑_{s ∈ S} E_s`,
where `E_s` is `TwoComponentCoulomb.critPairExponent` (with constants `c₂`, `c₃`). -/
theorem exists_neg_two_mul_energy_le :
    ∃ c₁ c₂ c₃ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → ∀ R : ℝ,
      ∀ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) → IsGeneric Z →
        -2 * energy lam Z + N - (isolatedDipoles Z).card + (longIsolatedDipoles Z R).card ≤
          ∑ i ∈ (isoPairVerts (nearestNeighbor Z))ᶜ,
              (smearedKernel lam (Z i - Z (nearestNeighbor Z i)) + c₁) +
            ∑ s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)},
              critPairExponent hN lam R c₂ c₃ Z s := by
  obtain ⟨C, hC, h22⟩ := proposition_2_2
  obtain ⟨Cg, hCg⟩ := exists_smearedKernel_ge
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨2 * |Cg| + 2 * Real.log 4 + 2 * |kappa| + C + 1 / 2, 13 * C,
    2 * |Cg| + 4 * Real.log 3 + 4 * |kappa| + 2 * C + 1, by positivity, by positivity,
    fun N hN lam hlam R Z hbox hgen => ?_⟩
  classical
  have hA := h22 N hN lam hlam Z hbox hgen
  simp only [ne_eq] at hA
  set f := nearestNeighbor Z with hf
  have hf0 : ∀ i, f i ≠ i := nearestNeighbor_ne Z
  -- the per-vertex terms of Proposition 2.2
  set T : Fin N ⊕ Fin N → ℝ := fun i =>
    charge i * charge (f i) * smearedKernel lam (Z i - Z (f i))
      - charge i * (charge i + charge (f i)) *
          (logKernel ((min (secondNeighborRadius hN lam Z i)
            (secondNeighborRadius hN lam Z (f i)) : ℝ) : ℂ) + kappa)
      - C * (firstNeighborRadius lam Z i / secondNeighborRadius hN lam Z i) ^ 2 with hT
  set L : Fin N ⊕ Fin N → ℝ := fun i =>
    logKernel ((secondNeighborRadius hN lam Z i : ℝ) : ℂ) + kappa with hL
  set W : Fin N ⊕ Fin N → ℝ := fun i => if f (f i) = i then -T i else L i with hW
  set V : Fin N ⊕ Fin N → ℝ := fun i => W i + 1 / 2 - (if IsIsolatedDipole Z i then 1 / 2 else 0)
    + (if IsIsolatedDipole Z i ∧ R < ‖Z i - Z (f i)‖ then 1 / 2 else 0) with hV
  -- Step 1: Proposition 2.2
  have hstep1 : -2 * energy lam Z ≤ ∑ i, W i := by
    have e : ∑ i, W i = -∑ i ∈ univ.filter (fun i => f (f i) = i), T i +
        ∑ i ∈ univ.filter (fun i => ¬ f (f i) = i), L i := by
      rw [hW, Finset.sum_ite, Finset.sum_neg_distrib]
    rw [e]
    linarith only [hA]
  -- Step 2: the exponent `N - |I^dip|/2 + D_R` distributed over the vertices
  have hstep2 : ∑ i, V i = ∑ i, W i + N - (isolatedDipoles Z).card +
      (longIsolatedDipoles Z R).card := by
    have h1 : ∑ _i : Fin N ⊕ Fin N, (1 / 2 : ℝ) = N := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    have h2 : ∑ i, (if IsIsolatedDipole Z i then (1 / 2 : ℝ) else 0) =
        (isolatedDipoles Z).card := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
        card_filter_isIsolatedDipole Z]
      push_cast
      ring
    have h3 : ∑ i, (if IsIsolatedDipole Z i ∧ R < ‖Z i - Z (f i)‖ then (1 / 2 : ℝ) else 0) =
        (longIsolatedDipoles Z R).card := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
        card_filter_isIsolatedDipole_long Z R]
      push_cast
      ring
    rw [hV]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3]
  -- Step 3: the vertices outside `I^pair`
  have hstep3 : ∀ i ∈ (isoPairVerts f)ᶜ, V i ≤
      smearedKernel lam (Z i - Z (f i)) +
        (2 * |Cg| + 2 * Real.log 4 + 2 * |kappa| + C + 1 / 2) := by
    intro i hi
    have hiP : ¬ IsIsoPairOf f i := fun h => (Finset.mem_compl.1 hi) (mem_isoPairVerts.2 h)
    have hnd : ¬ IsIsolatedDipole Z i := fun h => hiP h.isIsolatedPair
    have hW' : W i ≤ smearedKernel lam (Z i - Z (f i)) +
        (2 * |Cg| + 2 * Real.log 4 + 2 * |kappa| + C) := by
      rw [hW]
      dsimp only
      by_cases hcyc : f (f i) = i
      · rw [ite_eq_left hcyc]
        exact cycle_term_le hN hCg hC.le hlam Z hcyc
      · rw [ite_eq_right hcyc]
        have htree := tree_term_le hN hCg hlam Z i
        rw [hL]
        dsimp only
        linarith only [htree, abs_nonneg Cg, abs_nonneg kappa, hl4, hC]
    rw [hV]
    dsimp only
    rw [ite_eq_right hnd, ite_eq_right (fun h => hnd h.1)]
    linarith only [hW']
  -- Step 4: the isolated pairs
  have hstep4 : ∀ s : {s // s ∈ isoSecondVerts f}, V s + V (f s) ≤
      critPairExponent hN lam R (13 * C)
        (2 * |Cg| + 4 * Real.log 3 + 4 * |kappa| + 2 * C + 1) Z s := by
    intro s
    have hs := s.2
    have hsP : IsIsolatedPair Z s := (mem_isoSecondVerts.1 hs).1
    have h2 : f (f s) = s := hsP.1
    have hrP : IsIsolatedPair Z (f s) := isIsolatedPair_nearestNeighbor hsP
    have hWs : W s = -T s := by rw [hW]; dsimp only; rw [ite_eq_left h2]
    have hWr : W (f s) = -T (f s) := by
      rw [hW]; dsimp only; rw [ite_eq_left (by rw [h2])]
    have hlr : ‖Z (f s) - Z (f (f s))‖ = ‖Z s - Z (f s)‖ := by rw [h2, norm_sub_rev]
    unfold critPairExponent
    by_cases hn : charge (s : Fin N ⊕ Fin N) * charge (f s) = -1
    · rw [ite_eq_left hn]
      have hds : IsIsolatedDipole Z s := (isIsolatedDipole_iff Z s).2 ⟨hsP, hn⟩
      have hdr : IsIsolatedDipole Z (f s) := isIsolatedDipole_nearestNeighbor hds
      have hpair := neutral_pair_term_le hN hC.le hlam Z s hn
      have e : V s + V (f s) = (-T s) + (-T (f s)) +
          (if R < ‖Z s - Z (f s)‖ then 1 else 0) := by
        rw [hV]
        dsimp only
        rw [hWs, hWr, ite_eq_left hds, ite_eq_left hdr]
        by_cases hR : R < ‖Z s - Z (f s)‖
        · rw [ite_eq_left ⟨hds, hR⟩, ite_eq_left ⟨hdr, hlr ▸ hR⟩, ite_eq_left hR]
          ring
        · rw [ite_eq_right (fun h => hR h.2), ite_eq_right (fun h => hR (hlr ▸ h.2)),
            ite_eq_right hR]
          ring
      rw [e]
      exact add_le_add (by rw [← sub_eq_add_neg]; exact hpair) le_rfl
    · rw [ite_eq_right hn]
      have hds : ¬ IsIsolatedDipole Z s := fun h => hn ((isIsolatedDipole_iff Z s).1 h).2
      have hdr : ¬ IsIsolatedDipole Z (f s) := fun h => by
        have := isIsolatedDipole_nearestNeighbor h
        rw [← hf, h2] at this
        exact hds this
      have hpair := sameSign_pair_term_le hN hCg hC.le hlam Z s hn
      have e : V s + V (f s) = (-T s) + (-T (f s)) + 1 := by
        rw [hV]
        dsimp only
        rw [hWs, hWr, ite_eq_right hds, ite_eq_right hdr, ite_eq_right (fun h => hds h.1),
          ite_eq_right (fun h => hdr h.1)]
        ring
      rw [e]
      refine (add_le_add ((sub_eq_add_neg _ _).symm.le.trans hpair) (le_refl (1 : ℝ))).trans_eq ?_
      ring
  -- assembly
  have hsplit : ∑ i, V i = ∑ i ∈ (isoPairVerts f)ᶜ, V i +
      ∑ s : {s // s ∈ isoSecondVerts f}, (V s + V (f s)) := by
    rw [← Finset.sum_compl_add_sum (isoPairVerts f), sum_isoPairVerts hf0,
      Finset.sum_coe_sort (isoSecondVerts f) (fun s => V s + V (f s))]
  have hle1 := Finset.sum_le_sum hstep3
  have hle2 := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hstep4 s)
  linarith only [hstep1, hstep2, hsplit, hle1, hle2]

end Energy

end TwoComponentCoulomb

end
