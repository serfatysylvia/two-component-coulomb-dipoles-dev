/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.NearestNeighbor
public import TwoComponentCoulomb.NearestNeighbor.Basic

/-!
# Packing bound for nearest-neighbour distances

Elementary packing estimate behind the bound `∑_cycles |u_j|² ≤ C N` of the source
(l. 799 "disjoint balls … area", l. 845 "`s = 36N/π`", ).

If points `z_i` of the box `Λ = [0, √N]²` carry radii `ρ_i ≤ √(2N)` (the diameter of `Λ`) with
`ρ_i ≤ |z_i - z_j|` for all `j ≠ i`, then the open discs `B(z_i, ρ_i / 2)` are pairwise disjoint
and contained in the square `[-√N, 2√N]²` of area `9N`, so `∑ π ρ_i² / 4 ≤ 9N`.

* `norm_sub_le_of_mem_box` : the diameter of `Λ` is at most `√(2N)`.
* `sum_sq_le_of_separated_finset` : the packing bound for a finite subfamily `S` of indices.
* `sum_sq_le_of_separated` : the packing bound for a whole finite family.
* `sum_sq_norm_sub_nearestNeighbor_le` : `∑_i |z_i - z_{φ₁(i)}|² ≤ 36 N / π` for every
  configuration in the box.
-/

public section

open MeasureTheory

namespace TwoComponentCoulomb

/-- The diameter of the box `Λ = [0, √N]²` is at most `√(2N)` (source l. 799). -/
theorem norm_sub_le_of_mem_box {N : ℕ} {z w : ℂ} (hz : z ∈ box N) (hw : w ∈ box N) :
    ‖z - w‖ ≤ Real.sqrt (2 * N) := by
  rw [box, Complex.mem_reProdIm] at hz hw
  have hN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have h1 : |z.re - w.re| ≤ Real.sqrt N := by
    rw [abs_le]; constructor <;> linarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2]
  have h2 : |z.im - w.im| ≤ Real.sqrt N := by
    rw [abs_le]; constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
  have h3 : (z.re - w.re) ^ 2 ≤ N := by
    calc (z.re - w.re) ^ 2 = |z.re - w.re| ^ 2 := (sq_abs _).symm
      _ ≤ Real.sqrt N ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have h4 : (z.im - w.im) ^ 2 ≤ N := by
    calc (z.im - w.im) ^ 2 = |z.im - w.im| ^ 2 := (sq_abs _).symm
      _ ≤ Real.sqrt N ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = N := Real.sq_sqrt (Nat.cast_nonneg N)
  rw [Complex.norm_def, Complex.normSq_apply]
  refine Real.sqrt_le_sqrt ?_
  simp only [Complex.sub_re, Complex.sub_im]
  nlinarith

/-- The area of the square `[a, b]²` in `ℂ`. -/
theorem volume_reProdIm_Icc (a b : ℝ) :
    volume (Complex.reProdIm (Set.Icc a b) (Set.Icc a b)) = ENNReal.ofReal (b - a) ^ 2 := by
  have h : Complex.reProdIm (Set.Icc a b) (Set.Icc a b) =
      Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc a b) := by
    ext z
    simp only [Complex.mem_reProdIm, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
      Set.mem_prod]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, sq]

/-- **Packing bound** (source l. 799, 845): points `z_i` of the box carrying radii
`ρ_i ∈ [0, √(2N)]` with `ρ_i ≤ |z_i - z_j|` for all `i ≠ j` in a finite set `S` of indices
satisfy `∑_{i ∈ S} ρ_i² ≤ 36 N / π`. Only the indices of `S` are constrained. -/
theorem sum_sq_le_of_separated_finset {ι : Type*} {N : ℕ} (S : Finset ι) (z : ι → ℂ)
    (ρ : ι → ℝ) (hz : ∀ i ∈ S, z i ∈ box N) (hρ0 : ∀ i ∈ S, 0 ≤ ρ i)
    (hρd : ∀ i ∈ S, ρ i ≤ Real.sqrt (2 * N))
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ρ i ≤ ‖z i - z j‖) :
    ∑ i ∈ S, ρ i ^ 2 ≤ 36 * N / Real.pi := by
  classical
  have hN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hd : Real.sqrt (2 * N) ≤ 2 * Real.sqrt N := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)]
  set B : ι → Set ℂ := fun i => Metric.ball (z i) (ρ i / 2) with hB
  have hdisj : (S : Set ι).PairwiseDisjoint B := by
    intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_left]
    intro w hwi hwj
    have h1 := hsep i hi j hj hij
    have h2 := hsep j hj i hi hij.symm
    rw [hB, Metric.mem_ball, dist_eq_norm] at hwi hwj
    have h3 : ‖z i - z j‖ ≤ ‖w - z j‖ + ‖w - z i‖ :=
      calc ‖z i - z j‖ = ‖(w - z j) - (w - z i)‖ := by congr 1; ring
        _ ≤ ‖w - z j‖ + ‖w - z i‖ := norm_sub_le _ _
    have h4 : ‖z j - z i‖ = ‖z i - z j‖ := norm_sub_rev _ _
    linarith
  have hsub : (⋃ i ∈ S, B i) ⊆
      Complex.reProdIm (Set.Icc (-Real.sqrt N) (2 * Real.sqrt N))
        (Set.Icc (-Real.sqrt N) (2 * Real.sqrt N)) := by
    intro w hw
    simp only [Set.mem_iUnion] at hw
    obtain ⟨i, hi, hw⟩ := hw
    have hzi := hz i hi
    rw [box, Complex.mem_reProdIm] at hzi
    rw [hB, Metric.mem_ball, dist_eq_norm] at hw
    have hρi : ρ i / 2 ≤ Real.sqrt N := by linarith [hρd i hi]
    have hre : |(w - z i).re| ≤ ‖w - z i‖ := Complex.abs_re_le_norm _
    have him : |(w - z i).im| ≤ ‖w - z i‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_re, abs_le] at hre
    rw [Complex.sub_im, abs_le] at him
    rw [Complex.mem_reProdIm]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hzi.1.1, hzi.1.2, hzi.2.1, hzi.2.2]
  have hvol : volume (⋃ i ∈ S, B i) = ∑ i ∈ S, volume (B i) :=
    measure_biUnion_finset hdisj fun i _ => Metric.isOpen_ball.measurableSet
  have hle : volume (⋃ i ∈ S, B i) ≤ ENNReal.ofReal (9 * N) := by
    refine (measure_mono hsub).trans ?_
    rw [volume_reProdIm_Icc, ← ENNReal.ofReal_pow (by linarith)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have : (2 * Real.sqrt N - -Real.sqrt N) ^ 2 = 9 * Real.sqrt N ^ 2 := by ring
    rw [this, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hterm : ∀ i ∈ S, volume (B i) = ENNReal.ofReal (ρ i ^ 2 / 4 * Real.pi) := by
    intro i hi
    have h0 := hρ0 i hi
    rw [hB, Complex.volume_ball, ← ENNReal.ofReal_pow (by linarith),
      ← NNReal.coe_real_pi, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hvol, Finset.sum_congr rfl hterm,
    ← ENNReal.ofReal_sum_of_nonneg (fun i hi => by have := hρ0 i hi; positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  rw [le_div_iff₀ Real.pi_pos]
  have : ∑ i ∈ S, ρ i ^ 2 / 4 * Real.pi = (∑ i ∈ S, ρ i ^ 2) * Real.pi / 4 := by
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- **Packing bound** (source l. 799, 845): points `z_i` of the box carrying radii
`ρ_i ∈ [0, √(2N)]` with `ρ_i ≤ |z_i - z_j|` for all `i ≠ j` satisfy `∑ ρ_i² ≤ 36 N / π`. -/
theorem sum_sq_le_of_separated {ι : Type*} [Fintype ι] {N : ℕ} (z : ι → ℂ) (ρ : ι → ℝ)
    (hz : ∀ i, z i ∈ box N) (hρ0 : ∀ i, 0 ≤ ρ i) (hρd : ∀ i, ρ i ≤ Real.sqrt (2 * N))
    (hsep : ∀ i j, i ≠ j → ρ i ≤ ‖z i - z j‖) :
    ∑ i, ρ i ^ 2 ≤ 36 * N / Real.pi :=
  sum_sq_le_of_separated_finset Finset.univ z ρ (fun i _ => hz i) (fun i _ => hρ0 i)
    (fun i _ => hρd i) fun i _ j _ hij => hsep i j hij

/-- For every configuration of `2N` points in the box `Λ`, the squared nearest-neighbour
distances sum to at most `36 N / π` . No genericity is needed:
coinciding points have distance `0`. -/
theorem sum_sq_norm_sub_nearestNeighbor_le {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ)
    (hZ : ∀ i, Z i ∈ box N) :
    ∑ i, ‖Z i - Z (nearestNeighbor Z i)‖ ^ 2 ≤ 36 * N / Real.pi :=
  sum_sq_le_of_separated Z (fun i => ‖Z i - Z (nearestNeighbor Z i)‖) hZ (fun _ => norm_nonneg _)
    (fun i => norm_sub_le_of_mem_box (hZ i) (hZ _))
    fun _ _ hij => norm_sub_nearestNeighbor_le Z hij.symm

end TwoComponentCoulomb

end
