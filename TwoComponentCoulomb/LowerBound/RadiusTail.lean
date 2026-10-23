/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import TwoComponentCoulomb.LowerBound.PartitionLower
import Mathlib.Analysis.Complex.ExponentialBounds
import TwoComponentCoulomb.Gibbs.Basic

/-!
# The radius `ϱ(x_i)` on the placement set: its tail, and the quantities `ε_λ`, `η_λ`

Source: Proposition 4.1, Step 3 (l. 1775–1786). The proof of
Proposition 4.1 follows the source (ruling R22); this module proves the tail bound of Step 3,
which `LowerBound/PhiExpectation.lean` integrates against the profile `φ_β`.

Let `H = H(N, N, 4λ, 8λ)` (`placementSet N N (4 * lam) (8 * lam)`) and let `ℚ` be the normalised
Lebesgue measure on `H`. Isolating the coordinate `x_i` (Fubini along `Fin.insertNth`), the
admissible positions of `x_i` given the other points form a set of area at least `N / 2`, while
the event `ϱ(x_i) ≤ s` forces `x_i` into the union of the discs `B̄(x_j, 2s)`, `j ≠ i`, and the
boundary strip of width `s`, of area at most `(N - 1) π (2s)² + 4 s √N`.

* `lowerRadius_nonneg`, `exists_close_of_lowerRadius_lt` : `ϱ(x_i) < σ ≤ 1` forces a close
  neighbour or a close boundary.
* `insertNth_mem_placementSet_iff`, `volume_eq_lintegral_insertNth` : Fubini along a coordinate.
* `volume_bad_section_le`, `subset_bad_section` : the bad set of a section.
* `volume_inter_closeSet_le`, `radius_tail_le` : `vol (H ∩ {ϱ(x_i) ≤ s}) ≤
  (32π s² + 16 s / √N) vol H` (source l. 1775–1778, `ℚ(ϱ(x_1) ≤ r) ≤ C (r² + r / √N)`).
* `placement_area_condition` : the area condition of (eq:volume-lower) for `a = 4λ`, `b = 8λ`.
* `lowerEps`, `lowerEta` : the quantities `ε_λ`, `η_λ` of l. 1780–1786 (for `β > 2`), with
  `λ² ≤ ε_λ` and `λ ≤ η_λ` for `64 λ ≤ 1` (`sq_le_lowerEps`, `le_lowerEta`; l. 1793).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### The radius -/

theorem lowerRadius_nonneg (hN : 2 ≤ N) (X : Fin N → ℂ) (i : Fin N) :
    0 ≤ lowerRadius hN X i := by
  rw [le_lowerRadius_iff]
  exact ⟨fun j _ => by simp, Metric.infDist_nonneg, zero_le_one⟩

/-- If `ϱ(x_i) < σ ≤ 1`, then either some other point is at distance less than `2σ` from `x_i`
or `x_i` is at distance less than `σ` from the complement of the box. -/
theorem exists_close_of_lowerRadius_lt (hN : 2 ≤ N) (X : Fin N → ℂ) (i : Fin N) {σ : ℝ}
    (hσ : σ ≤ 1) (h : lowerRadius hN X i < σ) :
    (∃ j, j ≠ i ∧ ‖X j - X i‖ < 2 * σ) ∨ Metric.infDist (X i) (box N)ᶜ < σ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact absurd ((le_lowerRadius_iff hN X i).2 ⟨h1, h2, hσ⟩) (not_le.2 h)

theorem insertNth_mem_placementSet_iff {N n : ℕ} {a b : ℝ} (i : Fin (n + 1)) (z : ℂ)
    (Y : Fin n → ℂ) :
    (Fin.insertNth i z Y : Fin (n + 1) → ℂ) ∈ placementSet N (n + 1) a b ↔
      z ∈ Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a)) ∧
        (∀ k, b ≤ ‖z - Y k‖) ∧ Y ∈ placementSet N n a b := by
  simp only [placementSet, Set.mem_ofPred_eq]
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  simp only [Fin.forall_iff_succAbove i, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    ne_eq, not_true_eq_false, false_implies, true_and, (Fin.succAbove_ne i _).symm,
    (Fin.succAbove_ne i _), not_false_eq_true, Fin.succAbove_right_inj]
  constructor
  · rintro ⟨⟨hz, hY⟩, hC, hD⟩
    exact ⟨hz, fun k => hC k trivial, hY, fun i j hij => (hD i).2 j hij⟩
  · rintro ⟨hz, hC, hY, hD⟩
    refine ⟨⟨hz, hY⟩, fun k _ => hC k, fun k => ⟨fun _ => ?_, fun j hij => hD k j hij⟩⟩
    rw [← norm_neg, neg_sub]
    exact hC k

/-- Fubini along the `i`-th coordinate: the volume of a measurable set of configurations is the
integral over the other coordinates of the area of the section. -/
theorem volume_eq_lintegral_insertNth {n : ℕ} (i : Fin (n + 1)) {T : Set (Fin (n + 1) → ℂ)}
    (hT : MeasurableSet T) :
    volume T = ∫⁻ Y : Fin n → ℂ, volume {z : ℂ | (Fin.insertNth i z Y : Fin (n + 1) → ℂ) ∈ T} := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) i with he
  have hmp : MeasurePreserving e volume (volume : Measure (ℂ × (Fin n → ℂ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) i
  set S : Set (ℂ × (Fin n → ℂ)) := e.symm ⁻¹' T with hS
  have hSm : MeasurableSet S := e.symm.measurable hT
  have hpre : T = e ⁻¹' S := by
    ext X
    simp [hS]
  conv_lhs => rw [hpre]
  rw [hmp.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_apply_symm hSm]
  exact lintegral_congr fun Y => rfl

/-- A point of the inner square `Λ_a` (`a ≥ 0`) at distance at most `s` from the complement of the
box lies in one of the four boundary strips of width `s`. -/
theorem mem_strips_of_infDist_le {N : ℕ} {a s : ℝ} (ha : 0 ≤ a) {z : ℂ}
    (hz : z ∈ Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a)))
    (h : Metric.infDist z (box N)ᶜ ≤ s) :
    z ∈ Complex.reProdIm (Set.Icc 0 s) (Set.Icc 0 (Real.sqrt N)) ∪
        Complex.reProdIm (Set.Icc (Real.sqrt N - s) (Real.sqrt N)) (Set.Icc 0 (Real.sqrt N)) ∪
        Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc 0 s) ∪
        Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc (Real.sqrt N - s) (Real.sqrt N)) := by
  by_contra hnot
  simp only [Set.mem_union, Complex.mem_reProdIm, Set.mem_Icc, not_or, not_and] at hnot
  rw [Complex.mem_reProdIm] at hz
  obtain ⟨⟨hz1, hz2⟩, hz3, hz4⟩ := hz
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hnot
  have hre0 : 0 ≤ z.re := by linarith
  have him0 : 0 ≤ z.im := by linarith
  have hre1 : z.re ≤ Real.sqrt N := by linarith
  have him1 : z.im ≤ Real.sqrt N := by linarith
  have e1 : s < z.re := by
    by_contra hc
    exact h1 ⟨hre0, not_lt.1 hc⟩ him0 (by linarith)
  have e2 : z.re < Real.sqrt N - s := by
    by_contra hc
    exact h2 ⟨not_lt.1 hc, hre1⟩ him0 (by linarith)
  have e3 : s < z.im := by
    by_contra hc
    exact h3 ⟨hre0, hre1⟩ him0 (not_lt.1 hc)
  have e4 : z.im < Real.sqrt N - s := by
    by_contra hc
    exact h4 ⟨hre0, hre1⟩ (not_lt.1 hc) him1
  set a' : ℝ := min (min z.re (Real.sqrt N - z.re)) (min z.im (Real.sqrt N - z.im)) with ha'
  have ha's : s < a' := by
    rw [ha', lt_min_iff, lt_min_iff, lt_min_iff]
    refine ⟨⟨e1, by linarith⟩, e3, by linarith⟩
  have hza : z ∈ Complex.reProdIm (Set.Icc a' (Real.sqrt N - a'))
      (Set.Icc a' (Real.sqrt N - a')) := by
    rw [Complex.mem_reProdIm]
    have m1 : a' ≤ z.re := (min_le_left _ _).trans (min_le_left _ _)
    have m2 : a' ≤ Real.sqrt N - z.re := (min_le_left _ _).trans (min_le_right _ _)
    have m3 : a' ≤ z.im := (min_le_right _ _).trans (min_le_left _ _)
    have m4 : a' ≤ Real.sqrt N - z.im := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨⟨m1, by linarith⟩, m3, by linarith⟩
  have := le_infDist_compl_box (N := N) hza
  linarith


/-- The union of `n` closed discs of radius `b ≥ 0` has area at most `nπb²`. -/
theorem volume_closedBall_union_le {n : ℕ} {b : ℝ} (hb : 0 ≤ b) (Y : Fin n → ℂ) :
    volume (⋃ i, Metric.closedBall (Y i) b) ≤ ENNReal.ofReal (n * Real.pi * b ^ 2) := by
  refine (measure_iUnion_fintype_le _ _).trans ?_
  simp only [Complex.volume_closedBall, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow hb]
  have hpi : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi :=
    (ENNReal.ofReal_eq_coe_nnreal Real.pi_pos.le).symm
  rw [hpi]
  exact le_of_eq (by ring)

/-- The four boundary strips of width `s` of the box have total area at most `4 s √N`. -/
theorem volume_strips_le {N : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    volume (Complex.reProdIm (Set.Icc 0 s) (Set.Icc 0 (Real.sqrt N)) ∪
        Complex.reProdIm (Set.Icc (Real.sqrt N - s) (Real.sqrt N)) (Set.Icc 0 (Real.sqrt N)) ∪
        Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc 0 s) ∪
        Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc (Real.sqrt N - s) (Real.sqrt N))) ≤
      ENNReal.ofReal (4 * s * Real.sqrt N) := by
  have hN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have h1 : volume (Complex.reProdIm (Set.Icc 0 s) (Set.Icc 0 (Real.sqrt N))) =
      ENNReal.ofReal (s * Real.sqrt N) := by
    rw [volume_reProdIm_Icc_Icc, ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    ring
  have h2 : volume (Complex.reProdIm (Set.Icc (Real.sqrt N - s) (Real.sqrt N))
      (Set.Icc 0 (Real.sqrt N))) = ENNReal.ofReal (s * Real.sqrt N) := by
    rw [volume_reProdIm_Icc_Icc, ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    ring
  have h3 : volume (Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc 0 s)) =
      ENNReal.ofReal (s * Real.sqrt N) := by
    rw [volume_reProdIm_Icc_Icc, ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    ring
  have h4 : volume (Complex.reProdIm (Set.Icc 0 (Real.sqrt N))
      (Set.Icc (Real.sqrt N - s) (Real.sqrt N))) = ENNReal.ofReal (s * Real.sqrt N) := by
    rw [volume_reProdIm_Icc_Icc, ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    ring
  set R1 := Complex.reProdIm (Set.Icc 0 s) (Set.Icc 0 (Real.sqrt N))
  set R2 := Complex.reProdIm (Set.Icc (Real.sqrt N - s) (Real.sqrt N)) (Set.Icc 0 (Real.sqrt N))
  set R3 := Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc 0 s)
  set R4 := Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc (Real.sqrt N - s) (Real.sqrt N))
  calc volume (R1 ∪ R2 ∪ R3 ∪ R4) ≤ volume (R1 ∪ R2 ∪ R3) + volume R4 := measure_union_le _ _
    _ ≤ (volume (R1 ∪ R2) + volume R3) + volume R4 :=
        add_le_add_left (measure_union_le _ _) _
    _ ≤ ((volume R1 + volume R2) + volume R3) + volume R4 :=
        add_le_add_left (add_le_add_left (measure_union_le _ _) _) _
    _ = ENNReal.ofReal (s * Real.sqrt N) + ENNReal.ofReal (s * Real.sqrt N) +
        ENNReal.ofReal (s * Real.sqrt N) + ENNReal.ofReal (s * Real.sqrt N) := by
      rw [h1, h2, h3, h4]
    _ = ENNReal.ofReal (4 * s * Real.sqrt N) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring


/-- The bad part of a section: the positions `z` of the `i`-th point in `Λ_a` at distance at most
`2s` from another point or at distance at most `s` from the complement of the box have area at
most `n π (2s)² + 4 s √N`. -/
theorem volume_bad_section_le {N n : ℕ} {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (Y : Fin n → ℂ) :
    volume {z : ℂ | z ∈ Complex.reProdIm (Set.Icc a (Real.sqrt N - a))
        (Set.Icc a (Real.sqrt N - a)) ∧
      ((∃ k, ‖Y k - z‖ ≤ 2 * s) ∨ Metric.infDist z (box N)ᶜ ≤ s)} ≤
      ENNReal.ofReal (4 * Real.pi * n * s ^ 2 + 4 * s * Real.sqrt N) := by
  have hsub : {z : ℂ | z ∈ Complex.reProdIm (Set.Icc a (Real.sqrt N - a))
        (Set.Icc a (Real.sqrt N - a)) ∧
      ((∃ k, ‖Y k - z‖ ≤ 2 * s) ∨ Metric.infDist z (box N)ᶜ ≤ s)} ⊆
      (⋃ k, Metric.closedBall (Y k) (2 * s)) ∪
        (Complex.reProdIm (Set.Icc 0 s) (Set.Icc 0 (Real.sqrt N)) ∪
        Complex.reProdIm (Set.Icc (Real.sqrt N - s) (Real.sqrt N)) (Set.Icc 0 (Real.sqrt N)) ∪
        Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc 0 s) ∪
        Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc (Real.sqrt N - s) (Real.sqrt N))) := by
    rintro z ⟨hz, hk | hd⟩
    · obtain ⟨k, hk⟩ := hk
      left
      exact Set.mem_iUnion.2 ⟨k, by rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]; exact hk⟩
    · right
      exact mem_strips_of_infDist_le ha hz hd
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine le_trans (add_le_add (volume_closedBall_union_le (by positivity : 0 ≤ 2 * s) Y)
    (volume_strips_le hs)) ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-- The event that the point `x_i` is within `2σ` of another point of the configuration, or within
`σ` of the complement of the box (so that `ϱ(x_i) < σ` forces it, see
`exists_close_of_lowerRadius_lt`). -/
def closeSet (N : ℕ) (σ : ℝ) (i : Fin N) : Set (Fin N → ℂ) :=
  {X | (∃ j, j ≠ i ∧ ‖X j - X i‖ ≤ 2 * σ) ∨ Metric.infDist (X i) (box N)ᶜ ≤ σ}

theorem measurableSet_closeSet (N : ℕ) (σ : ℝ) (i : Fin N) : MeasurableSet (closeSet N σ i) := by
  have h1 : MeasurableSet {X : Fin N → ℂ | ∃ j, j ≠ i ∧ ‖X j - X i‖ ≤ 2 * σ} := by
    simp_rw [Set.ofPred_exists, Set.ofPred_and]
    refine MeasurableSet.iUnion fun j => (MeasurableSet.const _).inter ?_
    exact measurableSet_le (by fun_prop) measurable_const
  have h2 : MeasurableSet {X : Fin N → ℂ | Metric.infDist (X i) (box N)ᶜ ≤ σ} :=
    measurableSet_le ((Metric.continuous_infDist_pt _).comp (continuous_apply i)).measurable
      measurable_const
  exact h1.union h2

/-- The section of the close-neighbour event: if all points but `x_i` are fixed, the positions `z`
of `x_i` in the event `closeSet` form a subset of the bad set of `volume_bad_section_le`. -/
theorem subset_bad_section {n : ℕ} {σ : ℝ} (i : Fin (n + 1)) (z : ℂ) (Y : Fin n → ℂ)
    (h : (Fin.insertNth i z Y : Fin (n + 1) → ℂ) ∈ closeSet (n + 1) σ i) :
    (∃ k, ‖Y k - z‖ ≤ 2 * σ) ∨ Metric.infDist z (box (n + 1))ᶜ ≤ σ := by
  rcases h with ⟨j, hj, hjn⟩ | h
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    left
    exact ⟨k, by simpa [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same] using hjn⟩
  · right
    simpa [Fin.insertNth_apply_same] using h

/-- Numerics of the section estimate: the room `(√M - 2a)² - nπb²` is at least `M / 2`. -/
theorem room_ge_half {M n a b r : ℝ} (hn : n ≤ M) (hr : r * r = M)
    (hab : 4 * a * r + M * Real.pi * b ^ 2 ≤ M / 2) :
    M / 2 ≤ (r - 2 * a) ^ 2 - n * Real.pi * b ^ 2 := by
  have h1 : n * Real.pi * b ^ 2 ≤ M * Real.pi * b ^ 2 := by gcongr
  linarith only [h1, hr, hab, sq_nonneg a]

/-- Numerics of the section estimate: the bad area is at most `c · M / 2`. -/
theorem bad_le_mul_half {M n s r : ℝ} (hn : n ≤ M) (hr0 : 0 < r) (hr : r * r = M) :
    4 * Real.pi * n * s ^ 2 + 4 * s * r ≤ (8 * Real.pi * s ^ 2 + 8 * s / r) * (M / 2) := by
  have h1 : 4 * Real.pi * n * s ^ 2 ≤ 4 * Real.pi * M * s ^ 2 := by gcongr
  have h2 : 8 * s / r * (M / 2) = 4 * s * r := by
    rw [← hr]
    field_simp
    ring
  linarith only [h1, h2]

/-- **The close-neighbour event, in volume** (source l. 1775–1778, Step 3): if the placement area
condition `4a√N + Nπb² ≤ N/2` holds then for `n + 1 = N`,
`vol (H ∩ {x_i within 2σ of another point or σ of ∂Λ}) ≤ (8π σ² + 8 σ / √N) vol H`.
The union bound over the other `n` particles and the boundary strip. -/
theorem volume_inter_closeSet_le {n : ℕ} {a b σ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 4 * a * Real.sqrt ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) * Real.pi * b ^ 2 ≤
      ((n + 1 : ℕ) : ℝ) / 2)
    (hσ : 0 ≤ σ) (i : Fin (n + 1)) :
    volume (placementSet (n + 1) (n + 1) a b ∩ closeSet (n + 1) σ i) ≤
      ENNReal.ofReal (8 * Real.pi * σ ^ 2 + 8 * σ / Real.sqrt ((n + 1 : ℕ) : ℝ)) *
        volume (placementSet (n + 1) (n + 1) a b) := by
  have hM2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hMn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hsq : Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) :=
    Real.mul_self_sqrt (by linarith)
  have hsqpos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hHm : MeasurableSet (placementSet (n + 1) (n + 1) a b) :=
    measurableSet_placementSet _ _ _ _
  have h2a : 2 * a ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    by_contra hcon
    push Not at hcon
    linarith only [mul_pos (sub_pos.2 hcon) hsqpos,
      mul_nonneg (mul_nonneg (by linarith : 0 ≤ ((n + 1 : ℕ) : ℝ)) Real.pi_pos.le) (sq_nonneg b),
      hab, hsq, hM2]
  rw [volume_eq_lintegral_insertNth i (hHm.inter (measurableSet_closeSet _ _ _)),
    volume_eq_lintegral_insertNth i hHm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun Y => ?_
  by_cases hY : Y ∈ placementSet (n + 1) n a b
  · have hsec : {z : ℂ | (Fin.insertNth i z Y : Fin (n + 1) → ℂ) ∈
          placementSet (n + 1) (n + 1) a b} =
        {z : ℂ | z ∈ Complex.reProdIm (Set.Icc a (Real.sqrt ((n + 1 : ℕ) : ℝ) - a))
            (Set.Icc a (Real.sqrt ((n + 1 : ℕ) : ℝ) - a)) ∧ ∀ k, b ≤ ‖z - Y k‖} := by
      ext z
      simp only [Set.mem_ofPred_eq, insertNth_mem_placementSet_iff, hY, and_true]
    rw [hsec]
    have hbad := volume_bad_section_le (N := n + 1) (n := n) (a := a) (s := σ) ha hσ Y
    have hsub : {z : ℂ | (Fin.insertNth i z Y : Fin (n + 1) → ℂ) ∈
          placementSet (n + 1) (n + 1) a b ∩ closeSet (n + 1) σ i} ⊆
        {z : ℂ | z ∈ Complex.reProdIm (Set.Icc a (Real.sqrt ((n + 1 : ℕ) : ℝ) - a))
            (Set.Icc a (Real.sqrt ((n + 1 : ℕ) : ℝ) - a)) ∧
          ((∃ k, ‖Y k - z‖ ≤ 2 * σ) ∨ Metric.infDist z (box (n + 1))ᶜ ≤ σ)} := by
      intro z hz
      obtain ⟨hzH, hzE⟩ := hz
      exact ⟨((insertNth_mem_placementSet_iff i z Y).1 hzH).1, subset_bad_section i z Y hzE⟩
    have hsec_ge := volume_section_ge (N := n + 1) (n := n) (a := a) (b := b) hb h2a Y
    have hroom := room_ge_half (n := (n : ℝ)) hMn hsq hab
    have hbl := bad_le_mul_half (s := σ) hMn hsqpos hsq
    calc _ ≤ _ := measure_mono hsub
      _ ≤ _ := hbad
      _ ≤ ENNReal.ofReal (8 * Real.pi * σ ^ 2 + 8 * σ / Real.sqrt ((n + 1 : ℕ) : ℝ)) *
          ENNReal.ofReal (((n + 1 : ℕ) : ℝ) / 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hbl
      _ ≤ _ := mul_le_mul_right ((ENNReal.ofReal_le_ofReal hroom).trans hsec_ge) _
  · have hempty : {z : ℂ | (Fin.insertNth i z Y : Fin (n + 1) → ℂ) ∈
          placementSet (n + 1) (n + 1) a b ∩ closeSet (n + 1) σ i} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro h
      exact absurd ((insertNth_mem_placementSet_iff i z Y).1 h).2.2 hY
    rw [hempty]
    simp

/-- `H(N, n, a, b)` has finite volume (it lies in a compact set). -/
theorem volume_placementSet_lt_top (N n : ℕ) (a b : ℝ) : volume (placementSet N n a b) < ∞ := by
  have hK : IsCompact (Complex.reProdIm (Set.Icc a (Real.sqrt N - a))
      (Set.Icc a (Real.sqrt N - a))) := isCompact_Icc.reProdIm isCompact_Icc
  refine lt_of_le_of_lt (measure_mono ?_) (isCompact_univ_pi fun _ : Fin n => hK).measure_lt_top
  intro X hX
  exact fun i _ => hX.1 i

/-- The placement area condition `4a√N + Nπb² ≤ N/2` for `a = 4λ`, `b = 8λ`, `64 λ ≤ 1`. -/
theorem placement_area_condition {N : ℕ} (hN : 1 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (h64 : 64 * lam ≤ 1) :
    4 * (4 * lam) * Real.sqrt N + N * Real.pi * (8 * lam) ^ 2 ≤ N / 2 := by
  have hM : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsq : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    rw [Real.sqrt_le_left (by linarith)]
    have := mul_le_mul_of_nonneg_left hM (by linarith : (0 : ℝ) ≤ N)
    linarith only [this]
  have hsq0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hl : lam ≤ 1 / 64 := by linarith
  have hpi := Real.pi_le_four
  have h1 : 4 * (4 * lam) * Real.sqrt (N : ℝ) ≤ (N : ℝ) / 4 := by
    have := mul_le_mul_of_nonneg_right hl hsq0
    linarith only [this, hsq]
  have h2 : (N : ℝ) * Real.pi * (8 * lam) ^ 2 ≤ (N : ℝ) / 4 := by
    have : Real.pi * (8 * lam) ^ 2 ≤ 1 / 4 := by
      have e1 := mul_le_mul_of_nonneg_right hpi (sq_nonneg lam)
      have e2 := pow_le_pow_left₀ hlam.le hl 2
      linarith only [e1, e2]
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ N)
    linarith only [this]
  linarith

/-- **The tail of the radius** (source l. 1775–1778, Step 3: `ℚ(ϱ(x_1) ≤ r) ≤ C (r² + r/√N)`):
for `64 λ ≤ 1`, `H = H(N, N, 4λ, 8λ)` and every `s > 0`,
`vol (H ∩ {ϱ(x_i) ≤ s}) ≤ (32π s² + 16 s / √N) vol H`. -/
theorem radius_tail_le (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam) (h64 : 64 * lam ≤ 1) {s : ℝ}
    (hs : 0 < s) (i : Fin N) :
    volume (placementSet N N (4 * lam) (8 * lam) ∩ {X | lowerRadius hN X i ≤ s}) ≤
      ENNReal.ofReal (32 * Real.pi * s ^ 2 + 16 * s / Real.sqrt N) *
        volume (placementSet N N (4 * lam) (8 * lam)) := by
  by_cases hs1 : 1 < 2 * s
  · have hc : 1 ≤ 32 * Real.pi * s ^ 2 + 16 * s / Real.sqrt N := by
      have h8 : 0 ≤ 16 * s / Real.sqrt N := by positivity
      have e1 := mul_le_mul_of_nonneg_right Real.two_le_pi (sq_nonneg s)
      have e2 : (1 / 2 : ℝ) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
      linarith only [e1, e2, h8]
    refine (measure_mono Set.inter_subset_left).trans ?_
    refine le_mul_of_one_le_left zero_le ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hc
  push Not at hs1
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hmain := volume_inter_closeSet_le (n := n) (a := 4 * lam) (b := 8 * lam) (σ := 2 * s)
    (by positivity) (by positivity) (placement_area_condition (by omega) hlam h64) (by positivity) i
  refine le_trans (measure_mono ?_) (hmain.trans (le_of_eq ?_))
  · intro X hX
    refine ⟨hX.1, ?_⟩
    have h := exists_close_of_lowerRadius_lt hN X i hs1 (lt_of_le_of_lt hX.2 (by linarith))
    rcases h with ⟨j, hj, hjn⟩ | h
    · exact Or.inl ⟨j, hj, by linarith⟩
    · exact Or.inr h.le
  · congr 2
    ring

/-! ### The quantities `ε_λ` and `η_λ` -/

/-- The quantity `ε_λ` (source l. 1780–1786) for `β > 2`. -/
@[expose] noncomputable def lowerEps (β : ℝ) (_hβ : 2 < β) (lam : ℝ) : ℝ :=
  if β < 4 then lam ^ (β - 2)
  else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
  else lam ^ 2 * |Real.log lam|

/-- The quantity `η_λ` (source l. 1780–1786) for `β > 2`. -/
@[expose] noncomputable def lowerEta (β : ℝ) (_hβ : 2 < β) (lam : ℝ) : ℝ :=
  if β < 3 then lam ^ (β - 2)
  else if β = 3 then lam * |Real.log lam|
  else lam

theorem one_le_abs_log_of_sixtyFour_mul_le {lam : ℝ} (hlam : 0 < lam) (h : 64 * lam ≤ 1) : 1 ≤ |Real.log lam| := by
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h1 : lam ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    have : 0 < Real.exp 1 := Real.exp_pos 1
    rw [le_inv_comm₀ hlam this]
    have h64 : (64 : ℝ) ≤ lam⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hlam]
      norm_num
      linarith
    linarith
  have h2 : Real.log lam ≤ -1 := (Real.log_le_iff_le_exp hlam).2 h1
  rw [abs_of_neg (by linarith)]
  linarith

theorem log_inv_four_mul_le {lam : ℝ} (hlam : 0 < lam) (h : 64 * lam ≤ 1) :
    Real.log (4 * lam)⁻¹ ≤ |Real.log lam| := by
  rw [Real.log_inv, Real.log_mul (by norm_num) hlam.ne']
  have : Real.log lam ≤ 0 := Real.log_nonpos hlam.le (by linarith)
  rw [abs_of_nonpos this]
  have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

theorem lowerEps_nonneg {β : ℝ} (hβ : 2 < β) {lam : ℝ} (hlam : 0 < lam) :
    0 ≤ lowerEps β hβ lam := by
  unfold lowerEps
  split_ifs <;> positivity

theorem lowerEta_nonneg {β : ℝ} (hβ : 2 < β) {lam : ℝ} (hlam : 0 < lam) :
    0 ≤ lowerEta β hβ lam := by
  unfold lowerEta
  split_ifs <;> positivity

theorem le_lowerEta {β : ℝ} (hβ : 2 < β) {lam : ℝ} (hlam : 0 < lam) (h64 : 64 * lam ≤ 1) :
    lam ≤ lowerEta β hβ lam := by
  have hl1 : lam ≤ 1 := by linarith
  unfold lowerEta
  split_ifs with h3 h3e
  · have := Real.rpow_le_rpow_of_exponent_ge hlam hl1 (show β - 2 ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  · have := one_le_abs_log_of_sixtyFour_mul_le hlam h64
    exact le_mul_of_one_le_right hlam.le this
  · exact le_rfl

theorem sq_le_lowerEps {β : ℝ} (hβ : 2 < β) {lam : ℝ} (hlam : 0 < lam) (h64 : 64 * lam ≤ 1) :
    lam ^ 2 ≤ lowerEps β hβ lam := by
  have hl1 : lam ≤ 1 := by linarith
  have hl := one_le_abs_log_of_sixtyFour_mul_le hlam h64
  unfold lowerEps
  split_ifs with h4 h4e
  · have := Real.rpow_le_rpow_of_exponent_ge hlam hl1 (show β - 2 ≤ 2 by linarith)
    rwa [Real.rpow_two] at this
  · have h2 : 1 ≤ |Real.log lam| ^ 2 := one_le_pow₀ hl
    calc lam ^ 2 = lam ^ 2 * 1 := by ring
      _ ≤ lam ^ 2 * |Real.log lam| ^ 2 := by gcongr
  · calc lam ^ 2 = lam ^ 2 * 1 := by ring
      _ ≤ lam ^ 2 * |Real.log lam| := by gcongr

end TwoComponentCoulomb

end
