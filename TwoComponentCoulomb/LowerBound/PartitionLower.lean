/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.PhaseSpace.Placement

/-!
# The radius `ϱ(x_i)` and the discs of the lower bound

Source: Proposition 4.1, Step 1 (l. 1671–1684) and the case
`β = 2` (l. 1730–1736). The proof of Proposition 4.1 follows the source (ruling R22); this module
holds the geometry of the configurations used there.

Positive charges are restricted to the set `placementSet N N a b` of configurations in the inner
square `Λ_a = [a, √N - a]²` at mutual distance at least `b` (the source's `H` for `a = 4λ`,
`b = 8λ`). About each `x_i` the source uses the disc `B(x_i, ϱ(x_i))`; these discs are disjoint,
lie in `Λ`, and carry the Neumann problems of Step 1.

* `lowerRadius` : the radius `ϱ(x_i) = min {½ min_{j ≠ i} |x_j - x_i|, dist(x_i, ∂Λ), 1}` of
  l. 1680–1682. We write the distance to the boundary as the distance to the complement of `Λ`,
  which is the quantity that is convenient to bound below (`le_infDist_compl_box`: a point of the
  inner square `Λ_a` has distance at least `a` from `Λᶜ`, and a disc of smaller radius about it
  lies in `Λ`). For `x_i ∈ Λ` this is the source's `dist(x_i, ∂Λ)`: `infDist_frontier_box_eq`
  proves `dist(x_i, ∂Λ) = dist(x_i, Λᶜ)` (a segment from `x_i` to a point of `Λᶜ` meets `∂Λ`,
  and `∂Λ ⊆ closure Λᶜ`), and `lowerRadius_eq_min_frontier` restates `lowerRadius` with the
  frontier.
* `measurable_lowerRadius`, `four_mul_le_lowerRadius`, `closedBall_lowerRadius_div_two_subset_box`,
  `lowerRadius_add_lowerRadius_le` : measurability, `ϱ(x_i) ≥ 4λ` on `H`, the discs
  `B̄(x_i, ϱ(x_i)/2)` lie in `Λ`, and the discs `B(x_i, ϱ(x_i))` are disjoint (l. 1683).
* `closedBall_subset_box_of_mem_placementSet` : discs about the points of `placementSet N n a b`
  of radius at most `a` lie in `Λ` (used for `β = 2`, l. 1730–1733).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### Discs around the points of the inner square -/

/-- A closed disc of radius `r ≤ a` about a point of the inner square `Λ_a` lies in `Λ`. -/
theorem closedBall_subset_box_of_mem_innerSquare {a r : ℝ} {z : ℂ}
    (hz : z ∈ Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a)))
    (hr : r ≤ a) : Metric.closedBall z r ⊆ box N := by
  intro w hw
  have hd : ‖w - z‖ ≤ a := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    linarith
  have hre : |w.re - z.re| ≤ a :=
    le_trans (by simpa using Complex.abs_re_le_norm (w - z)) hd
  have him : |w.im - z.im| ≤ a :=
    le_trans (by simpa using Complex.abs_im_le_norm (w - z)) hd
  rw [Complex.mem_reProdIm] at hz
  rw [abs_le] at hre him
  rw [box, Complex.mem_reProdIm]
  exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
    ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩

/-- The closed discs of radius `r ≤ a` about the points of a configuration in
`H(N, n, a, b)` lie in the box `Λ`. -/
theorem closedBall_subset_box_of_mem_placementSet {n : ℕ} {a b r : ℝ} {X : Fin n → ℂ}
    (hX : X ∈ placementSet N n a b) (hr : r ≤ a) (i : Fin n) :
    Metric.closedBall (X i) r ⊆ box N :=
  closedBall_subset_box_of_mem_innerSquare (hX.1 i) hr

/-- A point of the inner square `Λ_a` has distance at least `a` from the complement of `Λ`. -/
theorem le_infDist_compl_box {a : ℝ} {z : ℂ}
    (hz : z ∈ Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a))) :
    a ≤ Metric.infDist z (box N)ᶜ := by
  have hne : (box N)ᶜ.Nonempty := by
    refine ⟨-1, fun h => ?_⟩
    rw [box, Complex.mem_reProdIm] at h
    have := h.1.1
    simp at this
    linarith
  rw [Metric.le_infDist hne]
  intro w hw
  by_contra hlt
  push Not at hlt
  refine hw (closedBall_subset_box_of_mem_innerSquare hz le_rfl ?_)
  rw [Metric.mem_closedBall, dist_comm]
  exact hlt.le

/-! ### Distance to the boundary -/

/-- A segment from a point of `s` to a point outside `s` meets the frontier of `s`. -/
theorem exists_mem_segment_frontier {s : Set ℂ} {x z : ℂ} (hx : x ∈ s) (hz : z ∉ s) :
    ∃ w ∈ segment ℝ x z, w ∈ frontier s := by
  by_contra hcon
  push Not at hcon
  have hxi : x ∈ interior s := by
    by_contra h
    exact hcon x (left_mem_segment ℝ x z) ⟨subset_closure hx, h⟩
  have hzc : z ∈ (closure s)ᶜ := by
    intro h
    exact hcon z (right_mem_segment ℝ x z) ⟨h, fun hi => hz (interior_subset hi)⟩
  have hsub : segment ℝ x z ⊆ interior s ∪ (closure s)ᶜ := by
    intro w hw
    by_cases hws : w ∈ interior s
    · exact Or.inl hws
    · exact Or.inr fun hc => hcon w hw ⟨hc, hws⟩
  obtain ⟨w, -, hw1, hw2⟩ := (convex_segment x z).isPreconnected (interior s) (closure s)ᶜ
    isOpen_interior isClosed_closure.isOpen_compl hsub ⟨x, left_mem_segment ℝ x z, hxi⟩
    ⟨z, right_mem_segment ℝ x z, hzc⟩
  exact hw2 (subset_closure (interior_subset hw1))

/-- For `x ∈ s`, the distance to the frontier of `s` equals the distance to the complement of
`s`. -/
theorem infDist_frontier_eq_infDist_compl {s : Set ℂ} {x : ℂ} (hx : x ∈ s) (hs : sᶜ.Nonempty) :
    Metric.infDist x (frontier s) = Metric.infDist x sᶜ := by
  have key : ∀ z ∈ sᶜ, ∃ w ∈ frontier s, dist x w ≤ dist x z := by
    intro z hz
    obtain ⟨w, hw1, hw2⟩ := exists_mem_segment_frontier hx hz
    refine ⟨w, hw2, ?_⟩
    have := segment_subset_closedBall_left x z hw1
    rw [Metric.mem_closedBall, dist_comm] at this
    exact this
  obtain ⟨z0, hz0⟩ := id hs
  obtain ⟨w0, hw0, -⟩ := key z0 hz0
  have hfne : (frontier s).Nonempty := ⟨w0, hw0⟩
  apply le_antisymm
  · rw [Metric.le_infDist hs]
    intro z hz
    obtain ⟨w, hw, hwz⟩ := key z hz
    exact (Metric.infDist_le_dist_of_mem hw).trans hwz
  · rw [Metric.le_infDist hfne]
    intro w hw
    have hw' : w ∈ closure sᶜ := by
      rw [frontier_eq_closure_inter_closure] at hw
      exact hw.2
    rw [← Metric.infDist_closure]
    exact Metric.infDist_le_dist_of_mem hw'

/-- For `x ∈ Λ`, `dist(x, ∂Λ) = dist(x, Λᶜ)`: the radius `ϱ(x_i)` of `lowerRadius` is the
source's `min {½ min_{j ≠ i} |x_j - x_i|, dist(x_i, ∂Λ), 1}`. -/
theorem infDist_frontier_box_eq {x : ℂ} (hx : x ∈ box N) :
    Metric.infDist x (frontier (box N)) = Metric.infDist x (box N)ᶜ := by
  refine infDist_frontier_eq_infDist_compl hx ⟨-1, fun h => ?_⟩
  rw [box, Complex.mem_reProdIm] at h
  have := h.1.1
  simp at this
  linarith

/-! ### The radius `ϱ(x_i)` -/

theorem univ_erase_nonempty (hN : 2 ≤ N) (i : Fin N) : (Finset.univ.erase i).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- The radius `ϱ(x_i) = min {½ min_{j ≠ i} |x_j - x_i|, dist(x_i, ∂Λ), 1}` of l. 1680–1682,
with the distance to the boundary of `Λ` written as the distance to the complement of `Λ` (see the
module docstring). -/
noncomputable def lowerRadius (hN : 2 ≤ N) (X : Fin N → ℂ) (i : Fin N) : ℝ :=
  min (min ((1 / 2) * (Finset.univ.erase i).inf' (univ_erase_nonempty hN i)
    fun j => ‖X j - X i‖) (Metric.infDist (X i) (box N)ᶜ)) 1

/-- For `x_i ∈ Λ`, `lowerRadius` is exactly the source's
`min {½ min_{j ≠ i} |x_j - x_i|, dist(x_i, ∂Λ), 1}`, with the distance to the frontier. -/
theorem lowerRadius_eq_min_frontier (hN : 2 ≤ N) (X : Fin N → ℂ) {i : Fin N} (hx : X i ∈ box N) :
    lowerRadius hN X i =
      min (min ((1 / 2) * (Finset.univ.erase i).inf' (univ_erase_nonempty hN i)
        fun j => ‖X j - X i‖) (Metric.infDist (X i) (frontier (box N)))) 1 := by
  unfold lowerRadius
  rw [infDist_frontier_box_eq hx]

theorem le_lowerRadius_iff (hN : 2 ≤ N) (X : Fin N → ℂ) (i : Fin N) {r : ℝ} :
    r ≤ lowerRadius hN X i ↔ (∀ j, j ≠ i → 2 * r ≤ ‖X j - X i‖) ∧
      r ≤ Metric.infDist (X i) (box N)ᶜ ∧ r ≤ 1 := by
  have h1 : r ≤ (1 / 2) * (Finset.univ.erase i).inf' (univ_erase_nonempty hN i)
      (fun j => ‖X j - X i‖) ↔ ∀ j, j ≠ i → 2 * r ≤ ‖X j - X i‖ := by
    have h2 : r ≤ (1 / 2) * (Finset.univ.erase i).inf' (univ_erase_nonempty hN i)
        (fun j => ‖X j - X i‖) ↔ 2 * r ≤ (Finset.univ.erase i).inf' (univ_erase_nonempty hN i)
        (fun j => ‖X j - X i‖) := by
      constructor <;> intro h <;> linarith
    rw [h2, Finset.le_inf'_iff]
    simp
  unfold lowerRadius
  rw [le_min_iff, le_min_iff, h1, and_assoc]

theorem lowerRadius_le_infDist (hN : 2 ≤ N) (X : Fin N → ℂ) (i : Fin N) :
    lowerRadius hN X i ≤ Metric.infDist (X i) (box N)ᶜ :=
  ((le_lowerRadius_iff hN X i).1 le_rfl).2.1

theorem two_mul_lowerRadius_le (hN : 2 ≤ N) (X : Fin N → ℂ) {i j : Fin N} (hji : j ≠ i) :
    2 * lowerRadius hN X i ≤ ‖X j - X i‖ :=
  ((le_lowerRadius_iff hN X i).1 le_rfl).1 j hji

/-- `ϱ(x_i)` depends continuously on `X`. -/
theorem continuous_lowerRadius (hN : 2 ≤ N) (i : Fin N) :
    Continuous fun X : Fin N → ℂ => lowerRadius hN X i := by
  unfold lowerRadius
  have h1 : Continuous fun X : Fin N → ℂ =>
      (Finset.univ.erase i).inf' (univ_erase_nonempty hN i) fun j => ‖X j - X i‖ :=
    Continuous.finset_inf'_apply _ fun j _ => by fun_prop
  have h2 : Continuous fun X : Fin N → ℂ => Metric.infDist (X i) (box N)ᶜ :=
    (Metric.continuous_infDist_pt _).comp (continuous_apply i)
  exact ((continuous_const.mul h1).min h2).min continuous_const

theorem measurable_lowerRadius (hN : 2 ≤ N) (i : Fin N) :
    Measurable fun X : Fin N → ℂ => lowerRadius hN X i :=
  (continuous_lowerRadius hN i).measurable

/-- For `X ∈ H(N, N, 4λ, 8λ)` and `4λ ≤ 1` the radii satisfy `ϱ(x_i) ≥ 4λ` (source l. 1683). -/
theorem four_mul_le_lowerRadius (hN : 2 ≤ N) {lam : ℝ} (h4 : 4 * lam ≤ 1) {X : Fin N → ℂ}
    (hX : X ∈ placementSet N N (4 * lam) (8 * lam)) (i : Fin N) :
    4 * lam ≤ lowerRadius hN X i := by
  rw [le_lowerRadius_iff]
  refine ⟨fun j hji => ?_, le_infDist_compl_box (hX.1 i), h4⟩
  have := hX.2 j i hji
  linarith

/-- The closed discs `B̄(x_i, ϱ(x_i) / 2)` lie in `Λ` (source l. 1683). -/
theorem closedBall_lowerRadius_div_two_subset_box (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (h4 : 4 * lam ≤ 1) {X : Fin N → ℂ} (hX : X ∈ placementSet N N (4 * lam) (8 * lam))
    (i : Fin N) : Metric.closedBall (X i) (lowerRadius hN X i / 2) ⊆ box N := by
  have hpos := four_mul_le_lowerRadius hN h4 hX i
  have hlt : lowerRadius hN X i / 2 < Metric.infDist (X i) (box N)ᶜ := by
    linarith [lowerRadius_le_infDist hN X i]
  have hd := Metric.disjoint_closedBall_of_lt_infDist hlt
  intro z hz
  by_contra hzb
  exact Set.disjoint_left.1 hd hz hzb

/-- The discs `B(x_i, ϱ(x_i))` are disjoint: `ϱ(x_i) + ϱ(x_j) ≤ |x_i - x_j|` for `i ≠ j`
(source l. 1683). -/
theorem lowerRadius_add_lowerRadius_le (hN : 2 ≤ N) (X : Fin N → ℂ) {i j : Fin N} (hij : i ≠ j) :
    lowerRadius hN X i + lowerRadius hN X j ≤ ‖X i - X j‖ := by
  have h1 := two_mul_lowerRadius_le hN X (i := j) (j := i) hij
  have h2 := two_mul_lowerRadius_le hN X (i := i) (j := j) hij.symm
  have h4 : ‖X j - X i‖ = ‖X i - X j‖ := norm_sub_rev _ _
  linarith

end TwoComponentCoulomb

end
