/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.PhaseSpace.Packing

/-!
# Successive placement: volume of separated configurations

Source: l. 1763--1772 and 1848--1853 (Proposition 4.1: placing the
points one at a time leaves area at least `N - C√Nλ - CNλ² ≥ N/2` at each step), l. 1820--1824
(the case `β = 2`) and l. 970--973, 982--985 (Lemma 3.6, lower bounds: placing the positive
particles one at a time gives volume at least `N^N e^{-C(Nt² + √N t)}`).

Let `Λ = [0, √N]²` be the box (`box N`) and `Λ_a = [a, √N - a]²` the inner square. The set
`H(N, n, a, b)` (`placementSet N n a b`) consists of the `n`-tuples of points of `Λ_a` at mutual
distance at least `b`. Placing the points one at a time (Fubini over the first coordinate), the
new point avoids the `n` previous discs of radius `b` inside `Λ_a`, so that
`vol H(n + 1) ≥ vol H(n) · ((√N - 2a)² - nπb²)`.

* `placementSet` : the set `H(N, n, a, b)`; `measurableSet_placementSet` : it is measurable.
* `volume_placementSet_succ_ge` : the successive-placement step (needs `2a ≤ √N`, otherwise
  `Λ_a` is empty).
* `prod_le_volume_placementSet` : `vol H(N, n, a, b) ≥ ∏_{k<n} ((√N - 2a)² - kπb²)`.
* `volume_placementSet_ge` : if `4a√N + Nπb² ≤ N/2` then
  `vol H(N, N, a, b) ≥ N^N exp(-8a√N - πNb²)`.
* `placementSet_subset_box` : the points of `H` lie in `Λ`.
-/

@[expose] public section

open MeasureTheory

namespace TwoComponentCoulomb

/-- The set `H(N, n, a, b)` of `n`-tuples of points of the inner square
`Λ_a = [a, √N - a]²` at mutual distance at least `b`. -/
def placementSet (N n : ℕ) (a b : ℝ) : Set (Fin n → ℂ) :=
  {X | (∀ i, X i ∈ Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a))) ∧
    ∀ i j, i ≠ j → b ≤ ‖X i - X j‖}

/-- The set `H(N, n, a, b)` is measurable. -/
theorem measurableSet_placementSet (N n : ℕ) (a b : ℝ) :
    MeasurableSet (placementSet N n a b) := by
  have hΛ : MeasurableSet
      (Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a))) :=
    (isClosed_Icc.reProdIm isClosed_Icc).measurableSet
  have h1 : MeasurableSet {X : Fin n → ℂ | ∀ i, X i ∈
      Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a))} := by
    simp_rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurable_pi_apply i hΛ
  have h2 : MeasurableSet {X : Fin n → ℂ | ∀ i j, i ≠ j → b ≤ ‖X i - X j‖} := by
    simp_rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le measurable_const (by fun_prop)
  exact h1.inter h2

/-- Prepending a point `z` to `Y` gives an element of `H(N, n + 1, a, b)` iff `z ∈ Λ_a`, `z` is at
distance at least `b` from every point of `Y`, and `Y ∈ H(N, n, a, b)`. -/
theorem cons_mem_placementSet_succ_iff {N n : ℕ} {a b : ℝ} (z : ℂ) (Y : Fin n → ℂ) :
    (Fin.cons z Y : Fin (n + 1) → ℂ) ∈ placementSet N (n + 1) a b ↔
      z ∈ Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a)) ∧
        (∀ i, b ≤ ‖z - Y i‖) ∧ Y ∈ placementSet N n a b := by
  simp only [placementSet, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro ⟨⟨h0, hY⟩, ⟨_, hz⟩, hrest⟩
    exact ⟨h0, fun i => hz i (Fin.succ_ne_zero i).symm, hY,
      fun i j hij => (hrest i).2 j (fun h => hij (Fin.succ_injective _ h))⟩
  · rintro ⟨h0, hz, hY, hsep⟩
    refine ⟨⟨h0, hY⟩, ⟨fun h => absurd rfl h, fun i _ => hz i⟩, fun i => ⟨fun _ => ?_, ?_⟩⟩
    · rw [← norm_neg, neg_sub]
      exact hz i
    · exact fun j hij => hsep i j fun h => hij (by rw [h])

/-- The area of the inner square `Λ_a`. -/
theorem volume_innerSquare {N : ℕ} {a : ℝ} (h2a : 2 * a ≤ Real.sqrt N) :
    volume (Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a))) =
      ENNReal.ofReal ((Real.sqrt N - 2 * a) ^ 2) := by
  rw [volume_reProdIm_Icc, ← ENNReal.ofReal_pow (by linarith)]
  congr 1
  ring

/-- The union of `n` discs of radius `b ≥ 0` has area at most `nπb²`. -/
theorem volume_ball_union_le {n : ℕ} {b : ℝ} (hb : 0 ≤ b) (Y : Fin n → ℂ) :
    volume (⋃ i, Metric.ball (Y i) b) ≤ ENNReal.ofReal (n * Real.pi * b ^ 2) := by
  refine (measure_iUnion_fintype_le _ _).trans ?_
  simp only [Complex.volume_ball, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow hb]
  have hpi : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi :=
    (ENNReal.ofReal_eq_coe_nnreal Real.pi_pos.le).symm
  rw [hpi]
  exact le_of_eq (by ring)

/-- The `k`-th point has room: the part of `Λ_a` at distance at least `b` from `n` given points
has area at least `(√N - 2a)² - nπb²`. -/
theorem volume_section_ge {N n : ℕ} {a b : ℝ} (hb : 0 ≤ b) (h2a : 2 * a ≤ Real.sqrt N)
    (Y : Fin n → ℂ) :
    ENNReal.ofReal ((Real.sqrt N - 2 * a) ^ 2 - n * Real.pi * b ^ 2) ≤
      volume {z : ℂ | z ∈
        Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a)) ∧
          ∀ i, b ≤ ‖z - Y i‖} := by
  have hset : {z : ℂ | z ∈
        Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a)) ∧
          ∀ i, b ≤ ‖z - Y i‖} =
      (Complex.reProdIm (Set.Icc a (Real.sqrt N - a)) (Set.Icc a (Real.sqrt N - a)) \
        (⋃ i, Metric.ball (Y i) b)) := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  rw [hset]
  refine le_trans ?_ le_measure_sdiff
  rw [volume_innerSquare h2a]
  have hn : 0 ≤ (n : ℝ) * Real.pi * b ^ 2 := by positivity
  rw [ENNReal.ofReal_sub _ hn]
  exact tsub_le_tsub_left (volume_ball_union_le hb Y) _

/-- **Successive placement**: adding one more point to a separated configuration of `n` points
leaves room of area at least `(√N - 2a)² - nπb²` (source l. 1763--1772). -/
theorem volume_placementSet_succ_ge {N n : ℕ} {a b : ℝ} (hab : 0 ≤ a ∧ 0 ≤ b)
    (h2a : 2 * a ≤ Real.sqrt N) :
    volume (placementSet N (n + 1) a b) ≥
      volume (placementSet N n a b) *
        ENNReal.ofReal ((Real.sqrt N - 2 * a) ^ 2 - n * Real.pi * b ^ 2) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0 with he
  have hmp : MeasurePreserving e volume (volume : Measure (ℂ × (Fin n → ℂ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
  set S : Set (ℂ × (Fin n → ℂ)) := e.symm ⁻¹' placementSet N (n + 1) a b with hS
  have hSm : MeasurableSet S := e.symm.measurable (measurableSet_placementSet N (n + 1) a b)
  have hpre : placementSet N (n + 1) a b = e ⁻¹' S := by
    ext X
    simp [hS]
  have hsymm : ∀ (z : ℂ) (Y : Fin n → ℂ), e.symm (z, Y) = Fin.cons z Y := by
    intro z Y
    rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
    exact Fin.insertNth_zero' z Y
  rw [hpre, hmp.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_apply_symm hSm]
  rw [mul_comm, ← lintegral_indicator_const (measurableSet_placementSet N n a b)]
  refine lintegral_mono fun Y => ?_
  by_cases hY : Y ∈ placementSet N n a b
  · rw [Set.indicator_of_mem hY]
    refine le_trans (volume_section_ge hab.2 h2a Y) (measure_mono ?_)
    intro z hz
    have h := (cons_mem_placementSet_succ_iff (N := N) (a := a) (b := b) z Y).2
      ⟨hz.1, hz.2, hY⟩
    show e.symm (z, Y) ∈ placementSet N (n + 1) a b
    rw [hsymm]
    exact h
  · rw [Set.indicator_of_notMem hY]
    exact zero_le

/-- `H(N, 0, a, b)` is the whole (one-point) space `Fin 0 → ℂ`. -/
theorem placementSet_zero (N : ℕ) (a b : ℝ) : placementSet N 0 a b = Set.univ := by
  ext X
  simp [placementSet]

/-- The space `Fin 0 → ℂ` has volume `1`. -/
theorem volume_placementSet_zero (N : ℕ) (a b : ℝ) : volume (placementSet N 0 a b) = 1 := by
  rw [placementSet_zero, volume_pi, Measure.pi_univ]
  simp

/-- **Volume of separated configurations, product form** (source l. 1763--1772, 1848--1853):
`vol H(N, n, a, b) ≥ ∏_{k<n} ((√N - 2a)² - kπb²)`. -/
theorem prod_le_volume_placementSet {N : ℕ} {a b : ℝ} (hab : 0 ≤ a ∧ 0 ≤ b)
    (h2a : 2 * a ≤ Real.sqrt N) (n : ℕ) :
    ∏ k ∈ Finset.range n,
        ENNReal.ofReal ((Real.sqrt N - 2 * a) ^ 2 - k * Real.pi * b ^ 2) ≤
      volume (placementSet N n a b) := by
  induction n with
  | zero => simp [volume_placementSet_zero]
  | succ n ih =>
    rw [Finset.prod_range_succ]
    exact le_trans (mul_le_mul_left ih _) (volume_placementSet_succ_ge hab h2a)

/-- The elementary inequality `1 - x ≥ e^{-2x}` for `0 ≤ x ≤ 1/2`. -/
theorem exp_neg_two_mul_le_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have h2 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h3 : (1 + x) ^ 2 ≤ Real.exp (2 * x) := by
    rw [two_mul, Real.exp_add, sq]
    exact mul_self_le_mul_self (by linarith) h2
  have h4 : Real.exp (-(2 * x)) * (1 + x) ^ 2 ≤ 1 := by
    calc Real.exp (-(2 * x)) * (1 + x) ^ 2 ≤ Real.exp (-(2 * x)) * Real.exp (2 * x) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  have h5 : 1 ≤ (1 - x) * (1 + x) ^ 2 := by
    have hx2 : x * x ≤ x * (1 / 2) := mul_le_mul_of_nonneg_left h1 h0
    have : 0 ≤ x * (1 - x - x ^ 2) := mul_nonneg h0 (by linarith only [hx2, h1])
    linarith only [this]
  exact le_of_mul_le_mul_right (h4.trans h5) (by positivity)

/-- **Volume of separated configurations** (source l. 1848--1853, 1820--1824, 970--973, 982--985):
if `4a√N + Nπb² ≤ N/2` then `vol H(N, N, a, b) ≥ N^N exp(-8a√N - πNb²)`. -/
theorem volume_placementSet_ge {N : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : 4 * a * Real.sqrt N + N * Real.pi * b ^ 2 ≤ N / 2) :
    ENNReal.ofReal ((N : ℝ) ^ N * Real.exp (-8 * a * Real.sqrt N - Real.pi * N * b ^ 2)) ≤
      volume (placementSet N N a b) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [volume_placementSet_zero]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  have hsqsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr.le
  have hpi : 0 ≤ (N : ℝ) * Real.pi * b ^ 2 := by positivity
  have h4a : 4 * a * Real.sqrt N ≤ N / 2 := by linarith only [h, hpi]
  have h2a : 2 * a ≤ Real.sqrt N := by
    by_contra hcon
    push Not at hcon
    have hprod := mul_pos (sub_pos.2 hcon) hsq
    linarith only [hprod, hsqsq, h4a, hNr]
  -- the exponent of the `k`-th factor
  set x : ℕ → ℝ := fun k => (4 * a * Real.sqrt N + k * Real.pi * b ^ 2) / N with hx
  have hx0 : ∀ k, 0 ≤ x k := fun k => by positivity
  have hx1 : ∀ k ∈ Finset.range N, x k ≤ 1 / 2 := by
    intro k hk
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.1 hk).le
    rw [hx]
    simp only
    rw [div_le_iff₀ hNr]
    have : (k : ℝ) * Real.pi * b ^ 2 ≤ N * Real.pi * b ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkN Real.pi_pos.le) (sq_nonneg b)
    linarith only [h, this]
  have hfac : ∀ k ∈ Finset.range N,
      (N : ℝ) * Real.exp (-(2 * x k)) ≤ (Real.sqrt N - 2 * a) ^ 2 - k * Real.pi * b ^ 2 := by
    intro k hk
    have h1 := exp_neg_two_mul_le_one_sub (hx0 k) (hx1 k hk)
    have h2 : (N : ℝ) * Real.exp (-(2 * x k)) ≤ N * (1 - x k) := by gcongr
    have h3 : (N : ℝ) * (1 - x k) = N - 4 * a * Real.sqrt N - k * Real.pi * b ^ 2 := by
      rw [hx]
      simp only
      field_simp
      ring
    have h4 : (Real.sqrt N - 2 * a) ^ 2 = N - 4 * a * Real.sqrt N + 4 * a ^ 2 := by
      linear_combination hsqsq
    linarith only [h2, h3, h4, sq_nonneg a]
  have hsum : ∑ k ∈ Finset.range N, 2 * x k ≤ 8 * a * Real.sqrt N + Real.pi * N * b ^ 2 := by
    have hs : (∑ i ∈ Finset.range N, (i : ℝ)) * 2 = N * (N - 1) := by
      have h' : ((∑ i ∈ Finset.range N, i) * 2 : ℕ) = N * (N - 1) :=
        Finset.sum_range_id_mul_two N
      have h'' := congrArg (Nat.cast : ℕ → ℝ) h'
      push_cast [Nat.cast_sub hN] at h''
      linarith only [h'']
    have : ∑ k ∈ Finset.range N, 2 * x k =
        8 * a * Real.sqrt N + Real.pi * b ^ 2 * (N - 1) := by
      rw [← Finset.mul_sum, hx]
      simp only
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        ← Finset.sum_mul, ← Finset.sum_mul, nsmul_eq_mul]
      field_simp
      linear_combination (Real.pi * b ^ 2) * hs
    rw [this]
    have hpb : 0 ≤ Real.pi * b ^ 2 := mul_nonneg Real.pi_pos.le (sq_nonneg b)
    linarith only [hpb]
  have hnn : ∀ k ∈ Finset.range N, 0 ≤ (Real.sqrt N - 2 * a) ^ 2 - k * Real.pi * b ^ 2 :=
    fun k hk => le_trans (by positivity) (hfac k hk)
  refine le_trans ?_ (prod_le_volume_placementSet ⟨ha, hb⟩ h2a N)
  rw [← ENNReal.ofReal_prod_of_nonneg hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (N : ℝ) ^ N * Real.exp (-8 * a * Real.sqrt N - Real.pi * N * b ^ 2)
      ≤ (N : ℝ) ^ N * Real.exp (-∑ k ∈ Finset.range N, 2 * x k) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith only [hsum]))
          (by positivity)
    _ = ∏ k ∈ Finset.range N, ((N : ℝ) * Real.exp (-(2 * x k))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Real.exp_sum,
          Finset.sum_neg_distrib]
    _ ≤ ∏ k ∈ Finset.range N, ((Real.sqrt N - 2 * a) ^ 2 - k * Real.pi * b ^ 2) :=
        Finset.prod_le_prod₀ (fun k _ => by positivity) fun k hk => hfac k hk

/-! ### Geometry of the placement set -/

/-- The points of a configuration in `H(N, n, a, b)` lie in the box `Λ` (for `a ≥ 0`). -/
theorem placementSet_subset_box {N n : ℕ} {a b : ℝ} (ha : 0 ≤ a) :
    ∀ X ∈ placementSet N n a b, ∀ i, X i ∈ box N := by
  rintro X ⟨hX, -⟩ i
  have h := hX i
  rw [Complex.mem_reProdIm] at h
  rw [box, Complex.mem_reProdIm]
  exact ⟨⟨by linarith [h.1.1, ha], by linarith [h.1.2, ha]⟩,
    ⟨by linarith [h.2.1, ha], by linarith [h.2.2, ha]⟩⟩

end TwoComponentCoulomb

end
