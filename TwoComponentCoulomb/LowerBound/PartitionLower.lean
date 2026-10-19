/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.LowerBound.LabelSum
public import TwoComponentCoulomb.PhaseSpace.Placement

/-!
# Lower bounds for the partition function from separated configurations

Source: Proposition 4.1, Step 1 (l. 1763--1775), the case
`β = 2` (l. 1820--1827) and Step 2, eq. (minz3) (l. 1837--1843), by the route of ruling R12a.

Positive charges are restricted to the set `placementSet N N a b` of configurations in the inner
square `Λ_a = [a, √N - a]²` at mutual distance at least `b`, and the negative charge `y_i` is
restricted to a disc (or annulus) around `x_i`; the dipole Jensen bound and the sum over the
assignments of negative labels (`partitionFunction_ge_label_sum`) then bound the partition
function from below by one-dipole integrals.

* `lowerRadius` : the radius `r(x_i) = min {½ min_{j ≠ i} |x_j - x_i|, dist(x_i, ∂Λ), 1}` of
  l. 1770--1772. We write the distance to the boundary as the distance to the complement of `Λ`,
  which is the quantity that is convenient to bound below (`le_infDist_compl_box`: a point of the
  inner square `Λ_a` has distance at least `a` from `Λᶜ`, and a disc of smaller radius about it
  lies in `Λ`). For `x_i ∈ Λ` this is the source's `dist(x_i, ∂Λ)`: `infDist_frontier_box_eq`
  proves `dist(x_i, ∂Λ) = dist(x_i, Λᶜ)` (a segment from `x_i` to a point of `Λᶜ` meets `∂Λ`,
  and `∂Λ ⊆ closure Λᶜ`), and `lowerRadius_eq_min_frontier` restates `lowerRadius` with the
  frontier.
* `measurable_lowerRadius`, `four_mul_le_lowerRadius`, `closedBall_lowerRadius_div_two_subset_box`,
  `lowerRadius_sep` : measurability, `r(x_i) ≥ 4λ`, and the discs `B̄(x_i, r(x_i)/2)` lie in `Λ`
  and are `2λ`-separated.
* `partitionFunction_ge_lowerRadius` : (minz3) with the dipole bound of R12a.
* `partitionFunction_ge_placement_annulus`, `partitionFunction_two_ge_placement` : the lower bound
  of l. 1820--1827 for `β = 2`.
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

/-- For `x ∈ Λ`, `dist(x, ∂Λ) = dist(x, Λᶜ)`: the radius `r(x_i)` of `lowerRadius` is the
source's `min {½ min_{j ≠ i} |x_j - x_i|, dist(x_i, ∂Λ), 1}`. -/
theorem infDist_frontier_box_eq {x : ℂ} (hx : x ∈ box N) :
    Metric.infDist x (frontier (box N)) = Metric.infDist x (box N)ᶜ := by
  refine infDist_frontier_eq_infDist_compl hx ⟨-1, fun h => ?_⟩
  rw [box, Complex.mem_reProdIm] at h
  have := h.1.1
  simp at this
  linarith

/-! ### The radius `r(x_i)` -/

theorem univ_erase_nonempty (hN : 2 ≤ N) (i : Fin N) : (Finset.univ.erase i).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- The radius `r(x_i) = min {½ min_{j ≠ i} |x_j - x_i|, dist(x_i, ∂Λ), 1}` of l. 1770--1772,
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

/-- `r(x_i)` depends continuously on `X`. -/
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

/-- For `X ∈ H(N, N, 4λ, 8λ)` and `4λ ≤ 1` the radii satisfy `r(x_i) ≥ 4λ` (source l. 1772). -/
theorem four_mul_le_lowerRadius (hN : 2 ≤ N) {lam : ℝ} (h4 : 4 * lam ≤ 1) {X : Fin N → ℂ}
    (hX : X ∈ placementSet N N (4 * lam) (8 * lam)) (i : Fin N) :
    4 * lam ≤ lowerRadius hN X i := by
  rw [le_lowerRadius_iff]
  refine ⟨fun j hji => ?_, le_infDist_compl_box (hX.1 i), h4⟩
  have := hX.2 j i hji
  linarith

/-- The closed discs `B̄(x_i, r(x_i) / 2)` lie in `Λ` (source l. 1772). -/
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

/-- The discs `B̄(x_i, r(x_i) / 2)` are `2λ`-separated:
`r(x_i) / 2 + r(x_j) / 2 + 2λ ≤ |x_i - x_j|` for `i ≠ j` (source l. 1772). -/
theorem lowerRadius_sep (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    {X : Fin N → ℂ} (hX : X ∈ placementSet N N (4 * lam) (8 * lam)) {i j : Fin N} (hij : i ≠ j) :
    lowerRadius hN X i / 2 + lowerRadius hN X j / 2 + 2 * lam ≤ ‖X i - X j‖ := by
  have h1 := two_mul_lowerRadius_le hN X (i := j) (j := i) hij
  have h2 := two_mul_lowerRadius_le hN X (i := i) (j := j) hij.symm
  have h3 := hX.2 i j hij
  have h4 : ‖X j - X i‖ = ‖X i - X j‖ := norm_sub_rev _ _
  linarith

/-! ### The instances of `partitionFunction_ge_label_sum` -/

/-- The closed ball about `0` as a closed annulus with inner radius `0`. -/
theorem setOf_zero_le_norm_le (b : ℝ) :
    {u : ℂ | 0 ≤ ‖u‖ ∧ ‖u‖ ≤ b} = Metric.closedBall (0 : ℂ) b := by
  ext u
  simp [norm_nonneg]

/-- **The lower bound (minz3) with the dipole Jensen bound** (source l. 1763--1775, 1837--1843;
ruling R12a, no correction term). For `4λ ≤ 1`, restricting the positive charges to
`H = H(N, N, 4λ, 8λ)` and each negative charge `y_i` to the disc `B̄(x_i, r(x_i) / 2)`,
`Z ≥ N! ∫_H ∏_i ∫_{B̄(0, r(x_i)/2)} e^{β g_λ(u)} du dX`. -/
theorem partitionFunction_ge_lowerRadius (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (β : ℝ)
    (h4 : 4 * lam ≤ 1) :
    ENNReal.ofReal (N.factorial : ℝ) *
        ∫⁻ X in placementSet N N (4 * lam) (8 * lam), ∏ i, ENNReal.ofReal
          (∫ u in Metric.closedBall (0 : ℂ) (lowerRadius hN X i / 2),
            Real.exp (β * smearedKernel lam u)) ≤
      partitionFunction N β lam := by
  have h := partitionFunction_ge_label_sum hlam β (measurableSet_placementSet N N (4 * lam)
    (8 * lam)) (a := fun _ _ => 0) (b := fun X i => lowerRadius hN X i / 2)
    (fun _ => measurable_const) (fun i => (measurable_lowerRadius hN i).div_const 2)
    (fun X hX i => ⟨le_rfl, by linarith [four_mul_le_lowerRadius hN h4 hX i]⟩)
    (fun X hX i => closedBall_lowerRadius_div_two_subset_box hN hlam h4 hX i)
    (fun X hX i j hij => lowerRadius_sep hN hlam hX hij)
  simpa only [setOf_zero_le_norm_le] using h

/-- **The lower bound of source l. 1820--1827** (the case `β = 2`, but valid for every `β`):
restricting the positive charges to `H(N, N, t, 4t)` and each displacement to
`2λ ≤ |x_i - y_i| ≤ t²`, with `0 < t ≤ 1` and `2λ ≤ t²`,
`Z ≥ N! · vol H(N, N, t, 4t) · (∫_{2λ ≤ |u| ≤ t²} e^{β g_λ(u)} du)^N`. -/
theorem partitionFunction_ge_placement_annulus {lam t : ℝ} (hlam : 0 < lam) (β : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hlt : 2 * lam ≤ t ^ 2) :
    ENNReal.ofReal (N.factorial : ℝ) * volume (placementSet N N t (4 * t)) *
        (ENNReal.ofReal (∫ u in {u : ℂ | 2 * lam ≤ ‖u‖ ∧ ‖u‖ ≤ t ^ 2},
          Real.exp (β * smearedKernel lam u))) ^ N ≤
      partitionFunction N β lam := by
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have h := partitionFunction_ge_label_sum hlam β (measurableSet_placementSet N N t (4 * t))
    (a := fun _ _ => 2 * lam) (b := fun _ _ => t ^ 2) (fun _ => measurable_const)
    (fun _ => measurable_const) (fun X hX i => ⟨by linarith, hlt⟩)
    (fun X hX i => closedBall_subset_box_of_mem_placementSet hX ht2 i)
    (fun X hX i j hij => by
      have := hX.2 i j hij
      nlinarith)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, setLIntegral_const] at h
  calc ENNReal.ofReal (N.factorial : ℝ) * volume (placementSet N N t (4 * t)) *
        (ENNReal.ofReal (∫ u in {u : ℂ | 2 * lam ≤ ‖u‖ ∧ ‖u‖ ≤ t ^ 2},
          Real.exp (β * smearedKernel lam u))) ^ N
      = ENNReal.ofReal (N.factorial : ℝ) *
        ((ENNReal.ofReal (∫ u in {u : ℂ | 2 * lam ≤ ‖u‖ ∧ ‖u‖ ≤ t ^ 2},
          Real.exp (β * smearedKernel lam u))) ^ N * volume (placementSet N N t (4 * t))) := by
        ring
    _ ≤ partitionFunction N β lam := h

/-- **The lower bound of source l. 1820--1827 for `β = 2`.** -/
theorem partitionFunction_two_ge_placement {lam t : ℝ} (hlam : 0 < lam)
    (ht : 0 < t) (ht1 : t ≤ 1) (hlt : 2 * lam ≤ t ^ 2) :
    ENNReal.ofReal (N.factorial : ℝ) * volume (placementSet N N t (4 * t)) *
        (ENNReal.ofReal (∫ u in {u : ℂ | 2 * lam ≤ ‖u‖ ∧ ‖u‖ ≤ t ^ 2},
          Real.exp (2 * smearedKernel lam u))) ^ N ≤
      partitionFunction N 2 lam :=
  partitionFunction_ge_placement_annulus hlam 2 ht ht1 hlt

end TwoComponentCoulomb

end
