/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Gibbs.Basic
public import TwoComponentCoulomb.LowerBound.PolarPi

/-!
# Volume and radial estimates for Proposition 3.7, Step 2

Source: proof of Proposition 3.7 (`prop:auxk`), l. 1087--1118. This file
collects the elementary real-analysis inputs of Step 2 (integration over one restricted graph,
`AuxIntegration.lean`).

## Volume available to the trivial vertices (l. 1087--1093)

Once the coordinates of the nontrivial components are fixed, every remaining vertex `z_t` avoids
the balls `B(z_i, 4 r(z_i))`, `i < k`, where `r(z_i) = |z_i - z_{φ(i)}| / 4`; the balls
`B(z_i, 2 r(z_i))` are pairwise disjoint and each meets the box `Λ = [0, √N]²` in a set of area at
least `r(z_i)²`. Hence the volume available to one trivial vertex is at most `N - ∑ r(z_i)²` and the
`n` trivial vertices contribute at most `(N - ∑ r(z_i)²)ⁿ ≤ e^{2k} Nⁿ e^{-∑ r(z_i)² / 4}` (when
`n ≥ p - 2k`, `N ≤ 2p`). We write `d_i = 4 r(z_i)` for the radius of the forbidden balls.

* `AuxIntegration.ofReal_sq_div_four_le_volume_box_inter_ball`: a ball of radius `ρ ≤ √N`
  centred in `Λ` meets `Λ` in area at least `ρ² / 4`.
* `AuxIntegration.volume_box_diff_iUnion_ball_le`: for centres `c_i ∈ Λ` and radii `d_i`
  with `d_i ≤ |c_i - c_j|` (`i ≠ j`), `∑ d_i² / 16 ≤ N` and
  `|Λ \ ⋃ B(c_i, d_i)| ≤ N - ∑ d_i² / 16`.
* `AuxIntegration.sub_pow_le_exp_mul`: the numerical estimate behind the case split
  `k ≤ p / 4` versus `k > p / 4` of the source.
* `AuxIntegration.volume_pi_diff_iUnion_ball_le`: the corresponding bound for the product
  set of `n` trivial vertices.

## The displacement integrals (l. 1095--1118)

After the Gunson--Panta change of variables each selected displacement `u` is integrated over `ℂ`
against the Gaussian factor `e^{-c|u|²}` left by the trivial vertices, with `c = 1/64`
(`AuxIntegration.auxC`), and a radial weight `w` evaluated at `r̃₁ = |u|/4 ∨ λ`. A `2`-cycle
contributes `w²` (`AuxIntegration.cycleIntegral`) and any other displacement `w`
(`AuxIntegration.noncycleIntegral`). For the weights of the source,
`w(r) = r^{-β/2} (1 + log (r/λ))^δ (1 + |log r|)^{δ'}` (`AuxIntegration.sourceWeight`), the
integrals are estimated by polar coordinates (the split at `λ` and `1` of the source l. 1097--1103):
with `ℓ = |log λ|` and `C` depending on `β` (and `δ`) only,

* `AuxIntegration.cycleIntegral_sourceWeight_le_of_lt_two`, `…_le_two`,
  `…_le_of_two_lt`: `≤ C` for `β < 2`; `≤ C ℓ` for `β = 2`; `≤ C λ^{2-β}` for `β > 2` (any `δ`,
  in particular `β = 4`, `δ = 1`: `C λ^{-2}`);
* `AuxIntegration.noncycleIntegral_sourceWeight_le_of_lt_four`, `…_le_four`,
  `…_le_of_four_lt`: `≤ C` for `β < 4`; `≤ C ℓ^{1+δ}` for `β = 4`; `≤ C λ^{2-β/2}` for `β > 4`;
* `AuxIntegration.cycleIntegral_sourceWeight_abs_le`,
  `AuxIntegration.noncycleIntegral_sourceWeight_abs_le`: the absolute logarithm at `β = 0`,
  `δ' = 1` is integrable uniformly in `λ`.

They rest on three estimates for `gaussRadial c α m λ = ∫_ℂ max(|u|/4, λ)^{-α}
(1 + log (max(|u|/4, λ)/λ))^m e^{-c|u|²}`: `gaussRadial_le_of_lt_two` (`α < 2`, `m = 0`),
`gaussRadial_le_of_eq_two` (`α = 2`, bound `ℓ^{m+1}`) and `gaussRadial_le_of_two_lt` (`α > 2`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

namespace AuxIntegration

/-! ### Areas -/

/-- An interval of length `t ≤ s / 2` inside `[0, s]`, all of whose points are within `t` of a
given point `x ∈ [0, s]`. -/
theorem exists_Icc_subset_near {s t x : ℝ} (hx : x ∈ Set.Icc 0 s) (ht : 0 ≤ t) (hts : t ≤ s / 2) :
    ∃ a : ℝ, Set.Icc a (a + t) ⊆ Set.Icc 0 s ∧ ∀ y ∈ Set.Icc a (a + t), |y - x| ≤ t := by
  by_cases h : x ≤ s / 2
  · refine ⟨x, fun y hy => ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩, fun y hy => ?_⟩
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  · push Not at h
    refine ⟨x - t, fun y hy => ⟨by linarith [hy.1], by linarith [hx.2, hy.2]⟩, fun y hy => ?_⟩
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]

/-- A ball of radius `ρ ≤ √N` centred at a point of the box `Λ = [0, √N]²` meets `Λ` in a set of
area at least `ρ² / 4` (it contains a square of side `ρ / 2` lying in `Λ`; source l. 1087,
"a quarter of a disc"). -/
theorem ofReal_sq_div_four_le_volume_box_inter_ball {N : ℕ} {x : ℂ} (hx : x ∈ box N) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρN : ρ ≤ Real.sqrt N) :
    ENNReal.ofReal (ρ ^ 2 / 4) ≤ volume (box N ∩ Metric.ball x ρ) := by
  rcases hρ0.eq_or_lt with rfl | hρ
  · simp
  have hx' := hx
  rw [box, Complex.mem_reProdIm] at hx'
  obtain ⟨a, ha, ha'⟩ := exists_Icc_subset_near hx'.1 (t := ρ / 2) (by positivity) (by linarith)
  obtain ⟨b, hb, hb'⟩ := exists_Icc_subset_near hx'.2 (t := ρ / 2) (by positivity) (by linarith)
  have hsub : Complex.reProdIm (Set.Icc a (a + ρ / 2)) (Set.Icc b (b + ρ / 2)) ⊆
      box N ∩ Metric.ball x ρ := by
    intro y hy
    rw [Complex.mem_reProdIm] at hy
    refine ⟨?_, ?_⟩
    · rw [box, Complex.mem_reProdIm]
      exact ⟨ha hy.1, hb hy.2⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 := ha' _ hy.1
      have h2 := hb' _ hy.2
      have h1' : (y.re - x.re) ^ 2 ≤ (ρ / 2) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h2' : (y.im - x.im) ^ 2 ≤ (ρ / 2) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      have h3 : ‖y - x‖ ^ 2 < ρ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im]
        nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hρ.le h3
  refine le_trans (le_of_eq ?_) (measure_mono hsub)
  rw [volume_reProdIm_Icc_Icc, ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

/-- **Available volume** (source l. 1087--1091): if the balls `B(c_i, d_i)` have centres in the box
and `d_i ≤ |c_i - c_j|` for `i ≠ j`, then the balls `B(c_i, d_i / 2)` are pairwise disjoint, so
`∑ d_i² / 16 ≤ N` and the box minus the union of the balls `B(c_i, d_i)` has area at most
`N - ∑ d_i² / 16`. -/
theorem volume_box_diff_iUnion_ball_le {I : Type*} [Fintype I] {N : ℕ} (c : I → ℂ) (d : I → ℝ)
    (hc : ∀ i, c i ∈ box N) (hd0 : ∀ i, 0 ≤ d i) (hdN : ∀ i, d i ≤ 2 * Real.sqrt N)
    (hsep : ∀ i j, i ≠ j → d i ≤ ‖c i - c j‖) :
    ∑ i, d i ^ 2 / 16 ≤ (N : ℝ) ∧
      volume (box N \ ⋃ i, Metric.ball (c i) (d i)) ≤
        ENNReal.ofReal ((N : ℝ) - ∑ i, d i ^ 2 / 16) := by
  set S : I → Set ℂ := fun i => box N ∩ Metric.ball (c i) (d i / 2) with hS
  have hSmeas : ∀ i, MeasurableSet (S i) := fun i =>
    (measurableSet_box N).inter Metric.isOpen_ball.measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro w ⟨-, hwi⟩ ⟨-, hwj⟩
    rw [Metric.mem_ball, dist_eq_norm] at hwi hwj
    have h1 := hsep i j hij
    have h2 := hsep j i hij.symm
    have h3 : ‖c i - c j‖ ≤ ‖w - c i‖ + ‖w - c j‖ :=
      calc ‖c i - c j‖ = ‖(w - c j) - (w - c i)‖ := by congr 1; ring
        _ ≤ ‖w - c j‖ + ‖w - c i‖ := norm_sub_le _ _
        _ = ‖w - c i‖ + ‖w - c j‖ := add_comm _ _
    have h4 : ‖c j - c i‖ = ‖c i - c j‖ := norm_sub_rev _ _
    linarith
  have hvol : volume (⋃ i, S i) = ∑ i, volume (S i) := by
    rw [measure_iUnion hdisj hSmeas, tsum_fintype]
  have hterm : ∀ i, ENNReal.ofReal (d i ^ 2 / 16) ≤ volume (S i) := by
    intro i
    have := ofReal_sq_div_four_le_volume_box_inter_ball (hc i) (ρ := d i / 2) (by
      have := hd0 i; positivity) (by linarith [hdN i])
    refine le_trans (le_of_eq ?_) this
    congr 1
    ring
  have hsum : ENNReal.ofReal (∑ i, d i ^ 2 / 16) ≤ volume (⋃ i, S i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := hd0 i; positivity), hvol]
    exact Finset.sum_le_sum fun i _ => hterm i
  have hσ0 : 0 ≤ ∑ i, d i ^ 2 / 16 :=
    Finset.sum_nonneg fun i _ => by have := hd0 i; positivity
  have hU : MeasurableSet (⋃ i, Metric.ball (c i) (d i)) :=
    MeasurableSet.iUnion fun i => Metric.isOpen_ball.measurableSet
  have hsub : (⋃ i, S i) ⊆ box N ∩ ⋃ i, Metric.ball (c i) (d i) := by
    intro w hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hw
    refine ⟨hi.1, Set.mem_iUnion.2 ⟨i, Metric.ball_subset_ball (by linarith [hd0 i]) hi.2⟩⟩
  have hle : ENNReal.ofReal (∑ i, d i ^ 2 / 16) ≤ volume (box N ∩ ⋃ i, Metric.ball (c i) (d i)) :=
    hsum.trans (measure_mono hsub)
  have hdiff := measure_sdiff_add_inter (box N) hU (μ := volume)
  rw [volume_box] at hdiff
  have hσN : ENNReal.ofReal (∑ i, d i ^ 2 / 16) ≤ N := by
    rw [← hdiff]
    exact hle.trans le_add_self
  refine ⟨?_, ?_⟩
  · rw [← ENNReal.ofReal_natCast] at hσN
    exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg N)).1 hσN
  · have h1 : volume (box N \ ⋃ i, Metric.ball (c i) (d i)) +
        ENNReal.ofReal (∑ i, d i ^ 2 / 16) ≤ N := by
      rw [← hdiff]
      exact add_le_add le_rfl hle
    have h2 := ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top h1
    refine h2.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_sub _ hσ0]

/-! ### The numerical estimate -/

/-- `(N - σ)ⁿ ≤ Nⁿ e^{-nσ/N}` for `σ ≤ N`, `N > 0`. -/
theorem sub_pow_le_pow_mul_exp (n : ℕ) {N σ : ℝ} (hN : 0 < N) (hσN : σ ≤ N) :
    (N - σ) ^ n ≤ N ^ n * Real.exp (-(n * σ / N)) := by
  have h1 : 0 ≤ 1 - σ / N := by
    rw [sub_nonneg, div_le_one hN]; exact hσN
  have h2 : 1 - σ / N ≤ Real.exp (-(σ / N)) := by
    have := Real.add_one_le_exp (-(σ / N))
    linarith
  have h3 : (1 - σ / N) ^ n ≤ Real.exp (-(n * σ / N)) := by
    calc (1 - σ / N) ^ n ≤ Real.exp (-(σ / N)) ^ n := pow_le_pow_left₀ h1 h2 n
      _ = Real.exp (-(n * σ / N)) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
  calc (N - σ) ^ n = N ^ n * (1 - σ / N) ^ n := by
        rw [← mul_pow]; congr 1; field_simp
    _ ≤ N ^ n * Real.exp (-(n * σ / N)) := by gcongr

/-- The case split of source l. 1089--1093: if `n ≥ p - 2k` trivial vertices remain, `N ≤ 2p`,
`k ≤ p` and `0 ≤ σ ≤ N`, then `(N - σ)ⁿ ≤ e^{2k} Nⁿ e^{-σ/4}`. For `4k ≤ p` this follows from
`n ≥ N/4`; for `4k > p` the Gaussian factor is inserted at the cost `e^{σ/4} ≤ e^{N/4} ≤ e^{2k}`. -/
theorem sub_pow_le_exp_mul {p k n N : ℕ} (hn : p ≤ n + 2 * k) (hN : (N : ℝ) ≤ 2 * p)
    (hN0 : 0 < N) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσN : σ ≤ N) :
    ((N : ℝ) - σ) ^ n ≤ Real.exp (2 * k) * (N : ℝ) ^ n * Real.exp (-(σ / 4)) := by
  have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
  have h1 := sub_pow_le_pow_mul_exp n hN0' hσN
  have hpos : 0 < (N : ℝ) ^ n := by positivity
  have hn' : (p : ℝ) ≤ n + 2 * k := by exact_mod_cast hn
  rcases le_or_gt (4 * k) p with hkp | hkp
  · have hkp' : (4 * k : ℝ) ≤ p := by exact_mod_cast hkp
    have h4 : (N : ℝ) ≤ 4 * n := by linarith
    have h5 : σ / 4 ≤ n * σ / N := by
      rw [le_div_iff₀ hN0']
      nlinarith
    have h6 : Real.exp (-(n * σ / N)) ≤ Real.exp (-(σ / 4)) := Real.exp_le_exp.2 (by linarith)
    have h7 : 1 ≤ Real.exp (2 * k) := Real.one_le_exp (by positivity)
    calc ((N : ℝ) - σ) ^ n ≤ (N : ℝ) ^ n * Real.exp (-(n * σ / N)) := h1
      _ ≤ (N : ℝ) ^ n * Real.exp (-(σ / 4)) := by gcongr
      _ = 1 * (N : ℝ) ^ n * Real.exp (-(σ / 4)) := by ring
      _ ≤ Real.exp (2 * k) * (N : ℝ) ^ n * Real.exp (-(σ / 4)) := by gcongr
  · have hkp' : (p : ℝ) < 4 * k := by exact_mod_cast hkp
    have h6 : Real.exp (-(n * σ / N)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ n * σ / N := by positivity
      linarith
    have h7 : 1 ≤ Real.exp (2 * k) * Real.exp (-(σ / 4)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ((N : ℝ) - σ) ^ n ≤ (N : ℝ) ^ n * Real.exp (-(n * σ / N)) := h1
      _ ≤ (N : ℝ) ^ n * 1 := by gcongr
      _ ≤ (N : ℝ) ^ n * (Real.exp (2 * k) * Real.exp (-(σ / 4))) := by gcongr
      _ = Real.exp (2 * k) * (N : ℝ) ^ n * Real.exp (-(σ / 4)) := by ring

/-! ### The product set of the trivial vertices -/

/-- **Volume of the trivial-vertex section** (source l. 1087--1093): the product over `n` trivial
vertices of `Λ \ ⋃ B(c_i, d_i)` has volume at most `e^{2k} Nⁿ e^{-σ/4}` with
`σ = ∑ d_i² / 16`, whenever `n ≥ p - 2k` and `N ≤ 2p`. -/
theorem volume_pi_diff_iUnion_ball_le {I T : Type*} [Fintype I] [Fintype T] {p k N : ℕ}
    (hn : p ≤ Fintype.card T + 2 * k) (hN : (N : ℝ) ≤ 2 * p) (hN0 : 0 < N) (c : I → ℂ) (d : I → ℝ) (hc : ∀ i, c i ∈ box N) (hd0 : ∀ i, 0 ≤ d i)
    (hdN : ∀ i, d i ≤ 2 * Real.sqrt N) (hsep : ∀ i j, i ≠ j → d i ≤ ‖c i - c j‖) :
    volume (Set.univ.pi fun _ : T => box N \ ⋃ i, Metric.ball (c i) (d i)) ≤
      ENNReal.ofReal (Real.exp (2 * k)) * (N : ℝ≥0∞) ^ Fintype.card T *
        ENNReal.ofReal (Real.exp (-((∑ i, d i ^ 2 / 16) / 4))) := by
  obtain ⟨hσN, hvol⟩ := volume_box_diff_iUnion_ball_le c d hc hd0 hdN hsep
  have hσ0 : 0 ≤ ∑ i, d i ^ 2 / 16 :=
    Finset.sum_nonneg fun i _ => by have := hd0 i; positivity
  rw [volume_pi_pi, Finset.prod_const, Finset.card_univ]
  refine (pow_le_pow_left' hvol _).trans ?_
  rw [← ENNReal.ofReal_pow (by linarith)]
  have := sub_pow_le_exp_mul (p := p) (k := k) (n := Fintype.card T) hn hN hN0 hσ0 hσN
  refine (ENNReal.ofReal_le_ofReal this).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (Nat.cast_nonneg N), ENNReal.ofReal_natCast]

/-! ### The weights of the displacements -/

/-- The Gaussian constant `c = 1/64`: the volume bound of the trivial vertices contributes
`exp(-∑_{i<k} r(z_i)²/4)` with `r(z_i) = |z_i - z_{g i}|/4`, i.e. `exp(-∑ |z_i - z_{g i}|²/64)`. -/
noncomputable def auxC : ℝ := 1 / 64

theorem auxC_pos : 0 < auxC := by norm_num [auxC]

/-- The weight of one displacement `s = |z_i - z_{g i}|`: `w(r(z_i) ∨ λ) e^{-c s²}` with
`r(z_i) = s/4`. -/
noncomputable def dispWeight (lam : ℝ) (w : ℝ → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  w (max (s / 4) lam) * ENNReal.ofReal (Real.exp (-(auxC * s ^ 2)))

theorem measurable_dispWeight (lam : ℝ) {w : ℝ → ℝ≥0∞} (hw : Measurable w) :
    Measurable (dispWeight lam w) := by
  unfold dispWeight
  refine Measurable.mul (hw.comp ?_) ?_
  · exact (measurable_id.div_const _).max measurable_const
  · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_id.pow_const 2).const_mul auxC).neg)

/-- The integral of one non-cycle displacement against the Gaussian weight. -/
noncomputable def noncycleIntegral (lam : ℝ) (w : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ u : ℂ, w (max (‖u‖ / 4) lam) * ENNReal.ofReal (Real.exp (-(auxC * ‖u‖ ^ 2)))

/-- The integral of one cycle displacement (weight squared) against the Gaussian weight. -/
noncomputable def cycleIntegral (lam : ℝ) (w : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ u : ℂ, w (max (‖u‖ / 4) lam) ^ 2 * ENNReal.ofReal (Real.exp (-(auxC * ‖u‖ ^ 2)))

theorem lintegral_dispWeight_norm (lam : ℝ) (w : ℝ → ℝ≥0∞) :
    ∫⁻ u : ℂ, dispWeight lam w ‖u‖ = noncycleIntegral lam w := rfl

theorem lintegral_dispWeight_norm_pow_two_le (lam : ℝ) (w : ℝ → ℝ≥0∞) :
    ∫⁻ u : ℂ, dispWeight lam w ‖u‖ ^ 2 ≤ cycleIntegral lam w := by
  refine lintegral_mono fun u => ?_
  unfold dispWeight
  rw [mul_pow, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  refine mul_le_mul_right ?_ _
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := auxC_pos
  push_cast
  nlinarith [sq_nonneg ‖u‖]

theorem lintegral_Ioi_ofReal_rpow {p a : ℝ} (hp : p < -1) (ha : 0 < a) :
    ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ p) = ENNReal.ofReal (a ^ (p + 1) / (-(p + 1))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hp ha)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      Real.rpow_nonneg (ha.trans ht).le _), integral_Ioi_rpow_of_lt hp ha]
  congr 1
  have : p + 1 ≠ 0 := by linarith
  field_simp

theorem lintegral_complex_norm_le (F : ℝ → ℝ≥0∞) (hF : Measurable F) {a : ℝ} (ha : 0 < a)
    (K : ℝ≥0∞) (hK : ∀ ρ, ρ ≤ a → F ρ ≤ K) :
    ∫⁻ u : ℂ, F ‖u‖ ≤ K * ENNReal.ofReal (Real.pi * a ^ 2) +
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioi a, ENNReal.ofReal t * F t := by
  have hs : MeasurableSet (Metric.closedBall (0 : ℂ) a) := Metric.isClosed_closedBall.measurableSet
  rw [← lintegral_add_compl _ hs]
  refine add_le_add ?_ ?_
  · calc ∫⁻ u in Metric.closedBall (0 : ℂ) a, F ‖u‖
        ≤ ∫⁻ u in Metric.closedBall (0 : ℂ) a, K := by
          refine setLIntegral_mono measurable_const fun u hu => hK _ ?_
          simpa using hu
      _ = K * ENNReal.ofReal (Real.pi * a ^ 2) := by
          rw [setLIntegral_const, Complex.volume_closedBall,
            ENNReal.ofReal_mul Real.pi_pos.le, ← ENNReal.ofReal_pow ha.le, ← NNReal.coe_real_pi,
            ENNReal.ofReal_coe_nnreal, mul_comm (ENNReal.ofReal (a ^ 2))]
  · have hc : (Metric.closedBall (0 : ℂ) a)ᶜ = {u : ℂ | ‖u‖ ∈ Ioi a} := by
      ext u
      simp [not_le]
    rw [hc, lintegral_radial_set (Ioi a) measurableSet_Ioi F hF]
    have h1 : ∀ t : ℝ, ENNReal.ofReal t * ((Ioi a).indicator F t * ENNReal.ofReal (2 * Real.pi)) =
        ENNReal.ofReal (2 * Real.pi) * (Ioi a).indicator (fun t => ENNReal.ofReal t * F t) t := by
      intro t
      by_cases ht : t ∈ Ioi a
      · rw [indicator_of_mem ht, indicator_of_mem ht]; ring
      · rw [indicator_of_notMem ht, indicator_of_notMem ht]; simp
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.2 (Ioi_subset_Ioi ha.le)]

/-! ### The radial integrand -/

/-- The radial integrand `max (ρ/4, λ)^{-α} (1 + log (max (ρ/4, λ)/λ))^m e^{-cρ²}`. -/
noncomputable def radialG (c α : ℝ) (m : ℕ) (lam ρ : ℝ) : ℝ :=
  max (ρ / 4) lam ^ (-α) * (1 + Real.log (max (ρ / 4) lam / lam)) ^ m * Real.exp (-(c * ρ ^ 2))

theorem measurable_radialG (c α : ℝ) (m : ℕ) (lam : ℝ) : Measurable (radialG c α m lam) := by
  unfold radialG
  fun_prop

theorem radialG_nonneg {c : ℝ} (α : ℝ) (m : ℕ) {lam : ℝ} (hlam : 0 < lam) (ρ : ℝ) :
    0 ≤ radialG c α m lam ρ := by
  unfold radialG
  have h1 : 1 ≤ max (ρ / 4) lam / lam := by
    rw [le_div_iff₀ hlam, one_mul]; exact le_max_right _ _
  have h2 : 0 ≤ 1 + Real.log (max (ρ / 4) lam / lam) := by
    have := Real.log_nonneg h1; linarith
  have h3 : 0 < max (ρ / 4) lam := lt_max_of_lt_right hlam
  positivity

theorem radialG_of_le {c : ℝ} (hc : 0 ≤ c) (α : ℝ) (m : ℕ) {lam : ℝ} (hlam : 0 < lam) {ρ : ℝ}
    (hρ : ρ ≤ 4 * lam) : radialG c α m lam ρ ≤ lam ^ (-α) := by
  unfold radialG
  rw [max_eq_right (by linarith), div_self hlam.ne', Real.log_one, add_zero, one_pow, mul_one]
  calc lam ^ (-α) * Real.exp (-(c * ρ ^ 2)) ≤ lam ^ (-α) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hlam.le _)
        rw [Real.exp_le_one_iff]
        have : 0 ≤ c * ρ ^ 2 := by positivity
        linarith
    _ = lam ^ (-α) := mul_one _

theorem radialG_of_gt (c α : ℝ) (m : ℕ) {lam : ℝ} {ρ : ℝ} (hρ : 4 * lam < ρ) :
    radialG c α m lam ρ =
      (ρ / 4) ^ (-α) * (1 + Real.log (ρ / (4 * lam))) ^ m * Real.exp (-(c * ρ ^ 2)) := by
  unfold radialG
  rw [max_eq_left (by linarith)]
  congr 4
  field_simp

/-- The Gaussian radial integral. -/
noncomputable def gaussRadial (c α : ℝ) (m : ℕ) (lam : ℝ) : ℝ≥0∞ :=
  ∫⁻ u : ℂ, ENNReal.ofReal (radialG c α m lam ‖u‖)

theorem gaussRadial_le {c : ℝ} (hc : 0 ≤ c) (α : ℝ) (m : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    gaussRadial c α m lam ≤ ENNReal.ofReal (lam ^ (-α)) * ENNReal.ofReal (Real.pi * (4 * lam) ^ 2) +
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ t in Ioi (4 * lam), ENNReal.ofReal t * ENNReal.ofReal (radialG c α m lam t) := by
  unfold gaussRadial
  exact lintegral_complex_norm_le (fun ρ => ENNReal.ofReal (radialG c α m lam ρ))
    (ENNReal.measurable_ofReal.comp (measurable_radialG c α m lam)) (by positivity) _
    fun ρ hρ => ENNReal.ofReal_le_ofReal (radialG_of_le hc α m hlam hρ)

/-! ### Power-function algebra -/

theorem mul_div_four_rpow_neg {t : ℝ} (ht : 0 < t) (α : ℝ) :
    t * (t / 4) ^ (-α) = 4 ^ α * t ^ (1 - α) := by
  rw [Real.div_rpow ht.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
    show 1 - α = 1 + -α by ring, Real.rpow_add ht, Real.rpow_one, div_inv_eq_mul]
  ring

/-! ### The case `α < 2` -/

theorem gaussRadial_le_of_lt_two {c : ℝ} (hc : 0 < c) {α : ℝ} (hα : α < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 → gaussRadial c α 0 lam ≤ ENNReal.ofReal C := by
  set M : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (1 - α) * Real.exp (-(c * t ^ 2)) with hM
  have hint : IntegrableOn (fun t : ℝ => t ^ (1 - α) * Real.exp (-(c * t ^ 2))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq hc (s := 1 - α) (by linarith)
    simpa only [neg_mul] using this
  have hM0 : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  refine ⟨16 * Real.pi + 2 * Real.pi * (4 ^ α * M), by positivity, fun lam hlam hlam1 => ?_⟩
  refine (gaussRadial_le hc.le α 0 hlam).trans ?_
  -- the first term
  have h1 : ENNReal.ofReal (lam ^ (-α)) * ENNReal.ofReal (Real.pi * (4 * lam) ^ 2) ≤
      ENNReal.ofReal (16 * Real.pi) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : lam ^ (-α) * (Real.pi * (4 * lam) ^ 2) = 16 * Real.pi * lam ^ (2 - α) := by
      rw [show 2 - α = 2 + -α by ring, Real.rpow_add hlam, Real.rpow_two]; ring
    rw [this]
    have h2 : lam ^ (2 - α) ≤ 1 := Real.rpow_le_one hlam.le hlam1 (by linarith)
    nlinarith [Real.pi_pos]
  -- the second term
  have h2 : ∫⁻ t in Ioi (4 * lam), ENNReal.ofReal t * ENNReal.ofReal (radialG c α 0 lam t) ≤
      ENNReal.ofReal (4 ^ α * M) := by
    have h3 : ∫⁻ t in Ioi (4 * lam), ENNReal.ofReal t * ENNReal.ofReal (radialG c α 0 lam t) =
        ∫⁻ t in Ioi (4 * lam), ENNReal.ofReal (4 ^ α * (t ^ (1 - α) * Real.exp (-(c * t ^ 2)))) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht' : 4 * lam < t := ht
      have htpos : 0 < t := by linarith
      rw [radialG_of_gt c α 0 ht', ← ENNReal.ofReal_mul htpos.le, pow_zero, mul_one,
        ← mul_assoc, mul_div_four_rpow_neg htpos, mul_assoc]
    rw [h3]
    refine (lintegral_mono_set (Ioi_subset_Ioi (by linarith) : Ioi (4 * lam) ⊆ Ioi 0)).trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        have : 0 < t := ht
        positivity), integral_const_mul]
  calc _ ≤ ENNReal.ofReal (16 * Real.pi) + ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (4 ^ α * M) :=
        add_le_add h1 (mul_le_mul_right h2 _)
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]

/-! ### Logarithmic factors -/

/-- A logarithmic power is dominated by a power: for `x ≥ 1`, `γ > 0`,
`(1 + log x)^m ≤ m! e^γ γ^{-m} x^γ`. -/
theorem one_add_log_pow_le {x γ : ℝ} (hx : 1 ≤ x) (hγ : 0 < γ) (m : ℕ) :
    (1 + Real.log x) ^ m ≤ (m.factorial * Real.exp γ / γ ^ m) * x ^ γ := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have h := Real.pow_div_factorial_le_exp (x := γ * (1 + Real.log x)) (by positivity) m
  have hexp : Real.exp (γ * (1 + Real.log x)) = Real.exp γ * x ^ γ := by
    rw [mul_add, mul_one, Real.exp_add, Real.rpow_def_of_pos hx0, mul_comm γ]
  rw [hexp, div_le_iff₀ (by positivity), mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [h]

/-! ### The case `α > 2` -/

theorem gaussRadial_le_of_two_lt {c : ℝ} (hc : 0 ≤ c) {α : ℝ} (hα : 2 < α) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      gaussRadial c α m lam ≤ ENNReal.ofReal (C * lam ^ (2 - α)) := by
  set γ : ℝ := (α - 2) / 2 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  set K : ℝ := m.factorial * Real.exp γ / γ ^ m with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨16 * Real.pi + 2 * Real.pi * (16 * K / γ), by positivity, fun lam hlam hlam1 => ?_⟩
  refine (gaussRadial_le hc α m hlam).trans ?_
  have h1 : ENNReal.ofReal (lam ^ (-α)) * ENNReal.ofReal (Real.pi * (4 * lam) ^ 2) =
      ENNReal.ofReal (16 * Real.pi * lam ^ (2 - α)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _)]
    congr 1
    rw [show 2 - α = 2 + -α by ring, Real.rpow_add hlam, Real.rpow_two]; ring
  -- the second term
  set p : ℝ := 1 - α + γ with hp
  have hp1 : p < -1 := by rw [hp, hγ]; linarith
  set D : ℝ := 4 ^ α * K * (4 * lam) ^ (-γ) with hD
  have h2 : ∫⁻ t in Ioi (4 * lam), ENNReal.ofReal t * ENNReal.ofReal (radialG c α m lam t) ≤
      ENNReal.ofReal D * ∫⁻ t in Ioi (4 * lam), ENNReal.ofReal (t ^ p) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    have ht' : 4 * lam < t := ht
    have htpos : 0 < t := by linarith
    rw [radialG_of_gt c α m ht', ← ENNReal.ofReal_mul htpos.le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx : 1 ≤ t / (4 * lam) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hlogpow := one_add_log_pow_le hx hγ0 m
    have hexp : Real.exp (-(c * t ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ c * t ^ 2 := by positivity
      linarith
    have hpos1 : 0 ≤ (t / 4) ^ (-α) := Real.rpow_nonneg (by positivity) _
    calc t * ((t / 4) ^ (-α) * (1 + Real.log (t / (4 * lam))) ^ m * Real.exp (-(c * t ^ 2)))
        ≤ t * ((t / 4) ^ (-α) * (K * (t / (4 * lam)) ^ γ) * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ htpos.le
          refine mul_le_mul (mul_le_mul_of_nonneg_left hlogpow hpos1) hexp (Real.exp_pos _).le
            (by positivity)
      _ = D * t ^ p := by
          have e1 : t * (t / 4) ^ (-α) = 4 ^ α * t ^ (1 - α) := mul_div_four_rpow_neg htpos α
          have e2 : (t / (4 * lam)) ^ γ = t ^ γ * (4 * lam) ^ (-γ) := by
            rw [Real.div_rpow htpos.le (by positivity), Real.rpow_neg (by positivity),
              div_eq_mul_inv]
          have e3 : t ^ (1 - α) * t ^ γ = t ^ p := by rw [hp, ← Real.rpow_add htpos]
          calc t * ((t / 4) ^ (-α) * (K * (t / (4 * lam)) ^ γ) * 1)
              = (t * (t / 4) ^ (-α)) * K * (t / (4 * lam)) ^ γ := by ring
            _ = 4 ^ α * t ^ (1 - α) * K * (t ^ γ * (4 * lam) ^ (-γ)) := by rw [e1, e2]
            _ = D * t ^ p := by rw [hD, ← e3]; ring
  rw [lintegral_Ioi_ofReal_rpow hp1 (by positivity)] at h2
  have hD2 : D * (4 * lam) ^ (p + 1) = 16 * K * lam ^ (2 - α) := by
    have e1 : (4 * lam) ^ (-γ) * (4 * lam) ^ (p + 1) = (4 * lam) ^ (2 - α) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      rw [hp]; ring
    have e2 : (4 * lam) ^ (2 - α) = 4 ^ (2 - α) * lam ^ (2 - α) := Real.mul_rpow (by norm_num) hlam.le
    have e3 : (4 : ℝ) ^ α * 4 ^ (2 - α) = 16 := by
      rw [← Real.rpow_add (by norm_num)]
      norm_num
    calc D * (4 * lam) ^ (p + 1) = 4 ^ α * K * ((4 * lam) ^ (-γ) * (4 * lam) ^ (p + 1)) := by
          rw [hD]; ring
      _ = 16 * K * lam ^ (2 - α) := by rw [e1, e2, ← e3]; ring
  have hneg : -(p + 1) = γ := by rw [hp, hγ]; ring
  rw [← ENNReal.ofReal_mul (by positivity)] at h2
  have h3 : D * ((4 * lam) ^ (p + 1) / (-(p + 1))) = 16 * K / γ * lam ^ (2 - α) := by
    rw [hneg, ← mul_div_assoc, hD2]; ring
  rw [h3] at h2
  calc _ ≤ ENNReal.ofReal (16 * Real.pi * lam ^ (2 - α)) +
        ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (16 * K / γ * lam ^ (2 - α)) := by
        rw [← h1]
        exact add_le_add le_rfl (mul_le_mul_right h2 _)
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

/-! ### The case `α = 2` -/

theorem lintegral_Ioc_inv_le {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioc a 1, ENNReal.ofReal t⁻¹ ≤ ENNReal.ofReal (-Real.log a) := by
  rcases le_or_gt a 1 with h | h
  · have hint : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc a 1) := by
      refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
      exact (continuousOn_inv₀.mono (fun t ht => (ha.trans_le ht.1).ne')).integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => inv_nonneg.2 (ha.trans ht.1).le),
      ← intervalIntegral.integral_of_le h, integral_inv_of_pos ha one_pos, one_div,
      Real.log_inv]
  · rw [Ioc_eq_empty (not_lt.2 h.le)]
    simp

theorem integrableOn_one_add_pow_mul_exp {c : ℝ} (hc : 0 < c) (m : ℕ) :
    IntegrableOn (fun t : ℝ => (1 + t) ^ m * Real.exp (-(c * t ^ 2))) (Ioi 0) := by
  have h : ∀ k ∈ Finset.range (m + 1), IntegrableOn (fun t : ℝ =>
      ((m.choose k : ℝ) * (t ^ k * Real.exp (-(c * t ^ 2))))) (Ioi 0) := by
    intro k _
    have := integrableOn_rpow_mul_exp_neg_mul_sq hc (s := (k : ℝ)) (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith)
    simp only [Real.rpow_natCast, neg_mul] at this
    exact this.const_mul _
  have hsum : IntegrableOn (fun t : ℝ => ∑ k ∈ Finset.range (m + 1),
      ((m.choose k : ℝ) * (t ^ k * Real.exp (-(c * t ^ 2))))) (Ioi 0) :=
    integrable_finsetSum _ h
  refine hsum.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only
  rw [add_comm 1 t, add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp
  ring

theorem gaussRadial_le_of_eq_two {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      gaussRadial c 2 m lam ≤ ENNReal.ofReal (C * (-Real.log lam) ^ (m + 1)) := by
  set M : ℝ := ∫ t in Ioi (0 : ℝ), (1 + t) ^ m * Real.exp (-(c * t ^ 2)) with hM
  have hint := integrableOn_one_add_pow_mul_exp hc m
  have hM0 : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (pow_nonneg (by have : 0 < t := ht; linarith) _) (Real.exp_pos _).le
  refine ⟨16 * Real.pi + 32 * Real.pi * 2 ^ m * (1 + M), by positivity, fun lam hlam hlam1 => ?_⟩
  set ℓ : ℝ := -Real.log lam with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    have := Real.log_le_log hlam hlam1
    rw [Real.log_exp] at this
    linarith
  refine (gaussRadial_le hc.le 2 m hlam).trans ?_
  -- the first term
  have h1 : ENNReal.ofReal (lam ^ (-(2 : ℝ))) * ENNReal.ofReal (Real.pi * (4 * lam) ^ 2) =
      ENNReal.ofReal (16 * Real.pi) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _)]
    congr 1
    rw [Real.rpow_neg hlam.le, Real.rpow_two]
    field_simp
    norm_num
  -- the second term
  set a : ℝ := 4 * lam with ha
  have ha0 : 0 < a := by positivity
  have hloga : -Real.log a ≤ ℓ := by
    rw [ha, Real.log_mul (by norm_num) hlam.ne', hℓ]
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal
    (16 * (t⁻¹ * ((1 + Real.log (t / a)) ^ m * Real.exp (-(c * t ^ 2))))) with hg
  have hpt : ∀ t ∈ Ioi a, ENNReal.ofReal t * ENNReal.ofReal (radialG c 2 m lam t) = g t := by
    intro t ht
    have ht' : a < t := ht
    have htpos : 0 < t := by linarith
    rw [radialG_of_gt c 2 m ht', ← ENNReal.ofReal_mul htpos.le]
    congr 1
    have h4 : t * (t / 4) ^ (-(2 : ℝ)) = 16 * t⁻¹ := by
      rw [mul_div_four_rpow_neg htpos 2, show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one,
        show (4 : ℝ) ^ (2 : ℝ) = 16 by norm_num [Real.rpow_two]]
    calc t * ((t / 4) ^ (-(2 : ℝ)) * (1 + Real.log (t / (4 * lam))) ^ m * Real.exp (-(c * t ^ 2)))
        = (t * (t / 4) ^ (-(2 : ℝ))) * ((1 + Real.log (t / a)) ^ m * Real.exp (-(c * t ^ 2))) := by
          rw [ha]; ring
      _ = _ := by rw [h4]; ring
  have hsub : Ioi a ⊆ Ioc a 1 ∪ Ioi (max a 1) := by
    intro t ht
    rcases le_or_gt t 1 with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr (max_lt ht h)
  have hexp : ∀ t : ℝ, Real.exp (-(c * t ^ 2)) ≤ 1 := by
    intro t
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c * t ^ 2 := by positivity
    linarith
  have hA : ∫⁻ t in Ioc a 1, g t ≤ ENNReal.ofReal (16 * (1 + ℓ) ^ m) * ENNReal.ofReal ℓ := by
    calc ∫⁻ t in Ioc a 1, g t
        ≤ ∫⁻ t in Ioc a 1, ENNReal.ofReal (16 * (1 + ℓ) ^ m) * ENNReal.ofReal t⁻¹ := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have htpos : 0 < t := ha0.trans ht.1
          have hlog0 : 0 ≤ Real.log (t / a) :=
            Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith [ht.1])
          have hlogle : Real.log (t / a) ≤ ℓ := by
            rw [Real.log_div htpos.ne' ha0.ne']
            have : Real.log t ≤ 0 := Real.log_nonpos htpos.le ht.2
            linarith
          have hpow : (1 + Real.log (t / a)) ^ m ≤ (1 + ℓ) ^ m :=
            pow_le_pow_left₀ (by linarith) (by linarith) m
          calc 16 * (t⁻¹ * ((1 + Real.log (t / a)) ^ m * Real.exp (-(c * t ^ 2))))
              ≤ 16 * (t⁻¹ * ((1 + ℓ) ^ m * 1)) := by
                gcongr
                exact hexp t
            _ = 16 * (1 + ℓ) ^ m * t⁻¹ := by ring
      _ = ENNReal.ofReal (16 * (1 + ℓ) ^ m) * ∫⁻ t in Ioc a 1, ENNReal.ofReal t⁻¹ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (16 * (1 + ℓ) ^ m) * ENNReal.ofReal ℓ :=
          mul_le_mul_right ((lintegral_Ioc_inv_le ha0).trans (ENNReal.ofReal_le_ofReal hloga)) _
  have hB : ∫⁻ t in Ioi (max a 1), g t ≤ ENNReal.ofReal (16 * (1 + ℓ) ^ m * M) := by
    calc ∫⁻ t in Ioi (max a 1), g t
        ≤ ∫⁻ t in Ioi (max a 1), ENNReal.ofReal (16 * (1 + ℓ) ^ m *
            ((1 + t) ^ m * Real.exp (-(c * t ^ 2)))) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have ht' : max a 1 < t := ht
          have hta : a < t := lt_of_le_of_lt (le_max_left _ _) ht'
          have ht1 : 1 < t := lt_of_le_of_lt (le_max_right _ _) ht'
          have htpos : 0 < t := by linarith
          have hlog0 : 0 ≤ Real.log (t / a) :=
            Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
          have hlogle : Real.log (t / a) ≤ t + ℓ := by
            rw [Real.log_div htpos.ne' ha0.ne']
            have : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
            linarith
          have hpow : (1 + Real.log (t / a)) ^ m ≤ (1 + ℓ) ^ m * (1 + t) ^ m := by
            rw [← mul_pow]
            refine pow_le_pow_left₀ (by linarith) ?_ m
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ) htpos.le]
          have htinv : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1.le
          calc 16 * (t⁻¹ * ((1 + Real.log (t / a)) ^ m * Real.exp (-(c * t ^ 2))))
              ≤ 16 * (1 * ((1 + ℓ) ^ m * (1 + t) ^ m * Real.exp (-(c * t ^ 2)))) := by
                gcongr
            _ = 16 * (1 + ℓ) ^ m * ((1 + t) ^ m * Real.exp (-(c * t ^ 2))) := by ring
      _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (16 * (1 + ℓ) ^ m *
            ((1 + t) ^ m * Real.exp (-(c * t ^ 2)))) :=
          lintegral_mono_set (Ioi_subset_Ioi (by positivity : (0 : ℝ) ≤ max a 1))
      _ = ENNReal.ofReal (16 * (1 + ℓ) ^ m * M) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
            (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
              have : 0 < t := ht
              positivity), integral_const_mul]
  have h2 : ∫⁻ t in Ioi a, ENNReal.ofReal t * ENNReal.ofReal (radialG c 2 m lam t) ≤
      ENNReal.ofReal (16 * (1 + ℓ) ^ m * ℓ) + ENNReal.ofReal (16 * (1 + ℓ) ^ m * M) := by
    calc _ = ∫⁻ t in Ioi a, g t := setLIntegral_congr_fun measurableSet_Ioi hpt
      _ ≤ ∫⁻ t in Ioc a 1 ∪ Ioi (max a 1), g t := lintegral_mono_set hsub
      _ ≤ (∫⁻ t in Ioc a 1, g t) + ∫⁻ t in Ioi (max a 1), g t :=
          lintegral_union_le g (Ioc a 1) (Ioi (max a 1))
      _ ≤ ENNReal.ofReal (16 * (1 + ℓ) ^ m * ℓ) + ENNReal.ofReal (16 * (1 + ℓ) ^ m * M) := by
          refine add_le_add ?_ hB
          rw [ENNReal.ofReal_mul (by positivity)]
          exact hA
  rw [h1]
  calc _ ≤ ENNReal.ofReal (16 * Real.pi) + ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (16 * (1 + ℓ) ^ m * ℓ) + ENNReal.ofReal (16 * (1 + ℓ) ^ m * M)) :=
        add_le_add le_rfl (mul_le_mul_right h2 _)
    _ = ENNReal.ofReal (16 * Real.pi + 2 * Real.pi * (16 * (1 + ℓ) ^ m * ℓ + 16 * (1 + ℓ) ^ m * M)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : (1 + ℓ) ^ m ≤ 2 ^ m * ℓ ^ m := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by linarith) (by linarith) m
        have e2 : ℓ + M ≤ ℓ * (1 + M) := by nlinarith
        have e3 : 1 ≤ ℓ ^ (m + 1) := one_le_pow₀ hℓ1
        have e4 : 0 ≤ (1 + ℓ) ^ m := by positivity
        have e5 : 16 * (1 + ℓ) ^ m * ℓ + 16 * (1 + ℓ) ^ m * M = 16 * (1 + ℓ) ^ m * (ℓ + M) := by
          ring
        have e6 : (1 + ℓ) ^ m * (ℓ + M) ≤ 2 ^ m * (1 + M) * ℓ ^ (m + 1) := by
          calc (1 + ℓ) ^ m * (ℓ + M) ≤ (2 ^ m * ℓ ^ m) * (ℓ * (1 + M)) :=
                mul_le_mul e1 e2 (by positivity) (by positivity)
            _ = 2 ^ m * (1 + M) * ℓ ^ (m + 1) := by ring
        rw [e5]
        have hpi := Real.pi_pos
        nlinarith [mul_le_mul_of_nonneg_left e6 (by positivity : (0 : ℝ) ≤ 32 * Real.pi),
          mul_le_mul_of_nonneg_left e3 (by positivity : (0 : ℝ) ≤ 16 * Real.pi)]

/-! ### The absolute logarithm (case `β = 0`, `δ' = 1`) -/

theorem one_add_abs_log_pow_le (q : ℕ) {r : ℝ} (hr : 0 < r) :
    (1 + |Real.log r|) ^ q ≤
      (q.factorial * Real.exp (1 / 2) / (1 / 2) ^ q) * (r ^ (-(1 / 2 : ℝ)) + r ^ (1 / 2 : ℝ)) := by
  have hK : 0 ≤ (q.factorial * Real.exp (1 / 2) / (1 / 2 : ℝ) ^ q) := by positivity
  have h1 : 0 ≤ r ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hr.le _
  have h2 : 0 ≤ r ^ (1 / 2 : ℝ) := Real.rpow_nonneg hr.le _
  rcases le_or_gt r 1 with h | h
  · have hlog : |Real.log r| = Real.log r⁻¹ := by
      rw [Real.log_inv, abs_of_nonpos (Real.log_nonpos hr.le h)]
    rw [hlog]
    have := one_add_log_pow_le (x := r⁻¹) (one_le_inv₀ hr |>.2 h) (by norm_num : (0 : ℝ) < 1 / 2) q
    rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le] at this
    refine this.trans ?_
    nlinarith [mul_nonneg hK h2]
  · have hlog : |Real.log r| = Real.log r := abs_of_nonneg (Real.log_nonneg h.le)
    rw [hlog]
    have := one_add_log_pow_le (x := r) h.le (by norm_num : (0 : ℝ) < 1 / 2) q
    refine this.trans ?_
    nlinarith [mul_nonneg hK h1]

/-- The Gaussian radial integral with the weight `(1 + |log r|)^q`. -/
noncomputable def gaussRadialAbs (c : ℝ) (q : ℕ) (lam : ℝ) : ℝ≥0∞ :=
  ∫⁻ u : ℂ, ENNReal.ofReal ((1 + |Real.log (max (‖u‖ / 4) lam)|) ^ q * Real.exp (-(c * ‖u‖ ^ 2)))

theorem gaussRadialAbs_le {c : ℝ} (hc : 0 < c) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 → gaussRadialAbs c q lam ≤ ENNReal.ofReal C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := gaussRadial_le_of_lt_two hc (α := 1 / 2) (by norm_num)
  obtain ⟨C₂, hC₂0, hC₂⟩ := gaussRadial_le_of_lt_two hc (α := -(1 / 2)) (by norm_num)
  set K : ℝ := q.factorial * Real.exp (1 / 2) / (1 / 2) ^ q with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * (C₁ + C₂), by positivity, fun lam hlam hlam1 => ?_⟩
  have hbound : ∀ u : ℂ, ENNReal.ofReal ((1 + |Real.log (max (‖u‖ / 4) lam)|) ^ q *
        Real.exp (-(c * ‖u‖ ^ 2))) ≤
      ENNReal.ofReal K * (ENNReal.ofReal (radialG c (1 / 2) 0 lam ‖u‖) +
        ENNReal.ofReal (radialG c (-(1 / 2)) 0 lam ‖u‖)) := by
    intro u
    have hr : 0 < max (‖u‖ / 4) lam := lt_max_of_lt_right hlam
    have h := one_add_abs_log_pow_le q hr
    rw [← ENNReal.ofReal_add (radialG_nonneg _ _ hlam _) (radialG_nonneg _ _ hlam _),
      ← ENNReal.ofReal_mul hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp := (Real.exp_pos (-(c * ‖u‖ ^ 2))).le
    unfold radialG
    simp only [pow_zero, mul_one, neg_neg]
    calc (1 + |Real.log (max (‖u‖ / 4) lam)|) ^ q * Real.exp (-(c * ‖u‖ ^ 2))
        ≤ (K * (max (‖u‖ / 4) lam ^ (-(1 / 2 : ℝ)) + max (‖u‖ / 4) lam ^ (1 / 2 : ℝ))) *
            Real.exp (-(c * ‖u‖ ^ 2)) := mul_le_mul_of_nonneg_right h hexp
      _ = _ := by ring
  unfold gaussRadialAbs
  calc _ ≤ ∫⁻ u : ℂ, ENNReal.ofReal K * (ENNReal.ofReal (radialG c (1 / 2) 0 lam ‖u‖) +
        ENNReal.ofReal (radialG c (-(1 / 2)) 0 lam ‖u‖)) := lintegral_mono hbound
    _ = ENNReal.ofReal K * (gaussRadial c (1 / 2) 0 lam + gaussRadial c (-(1 / 2)) 0 lam) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left]
        · rfl
        · exact ENNReal.measurable_ofReal.comp ((measurable_radialG c (1 / 2) 0 lam).comp measurable_norm)
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal C₁ + ENNReal.ofReal C₂) :=
        mul_le_mul_right (add_le_add (hC₁ lam hlam hlam1) (hC₂ lam hlam hlam1)) _
    _ = ENNReal.ofReal (K * (C₁ + C₂)) := by
        rw [← ENNReal.ofReal_add hC₁0 hC₂0, ← ENNReal.ofReal_mul hK0]

/-! ### The weights of the source -/

/-- The radial weight of the source (Proposition 3.7, l. 1008--1031) evaluated at the
first-neighbour radius: `w(r) = r^{-β/2} (1 + log (r/λ))^δ (1 + |log r|)^{δ'}`. -/
noncomputable def sourceWeight (β : ℝ) (δ δ' : ℕ) (lam r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (r ^ (-(β / 2)) * (1 + Real.log (r / lam)) ^ δ * (1 + |Real.log r|) ^ δ')

theorem measurable_sourceWeight (β : ℝ) (δ δ' : ℕ) (lam : ℝ) :
    Measurable (sourceWeight β δ δ' lam) := by
  unfold sourceWeight
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

theorem log_div_nonneg_of_le {lam r : ℝ} (hlam : 0 < lam) (hr : lam ≤ r) :
    0 ≤ 1 + Real.log (r / lam) := by
  have h1 : 1 ≤ r / lam := by rw [le_div_iff₀ hlam, one_mul]; exact hr
  have := Real.log_nonneg h1
  linarith

theorem noncycleIntegral_sourceWeight_zero {lam : ℝ} (hlam : 0 < lam) (β : ℝ) (δ : ℕ) :
    noncycleIntegral lam (sourceWeight β δ 0 lam) = gaussRadial auxC (β / 2) δ lam := by
  unfold noncycleIntegral gaussRadial
  refine lintegral_congr fun u => ?_
  have hr : 0 < max (‖u‖ / 4) lam := lt_max_of_lt_right hlam
  have hL := log_div_nonneg_of_le hlam (le_max_right (‖u‖ / 4) lam)
  unfold sourceWeight radialG
  rw [← ENNReal.ofReal_mul (by positivity)]
  simp only [pow_zero, mul_one]

theorem cycleIntegral_sourceWeight_zero {lam : ℝ} (hlam : 0 < lam) (β : ℝ) (δ : ℕ) :
    cycleIntegral lam (sourceWeight β δ 0 lam) = gaussRadial auxC β (2 * δ) lam := by
  unfold cycleIntegral gaussRadial
  refine lintegral_congr fun u => ?_
  have hr : 0 < max (‖u‖ / 4) lam := lt_max_of_lt_right hlam
  have hL := log_div_nonneg_of_le hlam (le_max_right (‖u‖ / 4) lam)
  unfold sourceWeight radialG
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [pow_zero, mul_one]
  rw [mul_pow, ← Real.rpow_mul_natCast hr.le, ← pow_mul, mul_comm δ 2]
  congr 3
  ring

theorem noncycleIntegral_sourceWeight_abs {lam : ℝ} (hlam : 0 < lam) :
    noncycleIntegral lam (sourceWeight 0 0 1 lam) = gaussRadialAbs auxC 1 lam := by
  unfold noncycleIntegral gaussRadialAbs
  refine lintegral_congr fun u => ?_
  have hr : 0 < max (‖u‖ / 4) lam := lt_max_of_lt_right hlam
  unfold sourceWeight
  rw [← ENNReal.ofReal_mul (by positivity)]
  simp

theorem cycleIntegral_sourceWeight_abs {lam : ℝ} (hlam : 0 < lam) :
    cycleIntegral lam (sourceWeight 0 0 1 lam) = gaussRadialAbs auxC 2 lam := by
  unfold cycleIntegral gaussRadialAbs
  refine lintegral_congr fun u => ?_
  have hr : 0 < max (‖u‖ / 4) lam := lt_max_of_lt_right hlam
  unfold sourceWeight
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  simp

/-! ### The radial integrals for the source weights -/

/-- **Cycle displacement, `β < 2`** (source l. 1097--1117): `∫ w² e^{-c|u|²} ≤ C`, uniformly in
`0 < λ ≤ 1`. -/
theorem cycleIntegral_sourceWeight_le_of_lt_two {β : ℝ} (hβ : β < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      cycleIntegral lam (sourceWeight β 0 0 lam) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC0, hC⟩ := gaussRadial_le_of_lt_two auxC_pos (α := β) hβ
  refine ⟨C, hC0, fun lam hlam hlam1 => ?_⟩
  rw [cycleIntegral_sourceWeight_zero hlam]
  simpa using hC lam hlam hlam1

/-- **Cycle displacement, `β = 2`**: `∫ w² e^{-c|u|²} ≤ C |log λ|` for `0 < λ ≤ e^{-1}`. -/
theorem cycleIntegral_sourceWeight_le_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      cycleIntegral lam (sourceWeight 2 0 0 lam) ≤ ENNReal.ofReal (C * |Real.log lam|) := by
  obtain ⟨C, hC0, hC⟩ := gaussRadial_le_of_eq_two auxC_pos 0
  refine ⟨C, hC0, fun lam hlam hlam1 => ?_⟩
  rw [cycleIntegral_sourceWeight_zero hlam]
  have hlog : Real.log lam ≤ 0 := Real.log_nonpos hlam.le (hlam1.trans (Real.exp_le_one_iff.2 (by norm_num)))
  have := hC lam hlam hlam1
  simpa [abs_of_nonpos hlog] using this

/-- **Cycle displacement, `β > 2`** (any `δ`, in particular `β = 4`, `δ = 1`):
`∫ w² e^{-c|u|²} ≤ C λ^{2-β}` for `0 < λ ≤ 1`. -/
theorem cycleIntegral_sourceWeight_le_of_two_lt {β : ℝ} (hβ : 2 < β) (δ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      cycleIntegral lam (sourceWeight β δ 0 lam) ≤ ENNReal.ofReal (C * lam ^ (2 - β)) := by
  obtain ⟨C, hC0, hC⟩ := gaussRadial_le_of_two_lt auxC_pos.le hβ (2 * δ)
  refine ⟨C, hC0, fun lam hlam hlam1 => ?_⟩
  rw [cycleIntegral_sourceWeight_zero hlam]
  exact hC lam hlam hlam1

/-- **Cycle displacement, `β = 0`, `δ' = 1`**: the absolute logarithms are integrable uniformly in
`λ`. -/
theorem cycleIntegral_sourceWeight_abs_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      cycleIntegral lam (sourceWeight 0 0 1 lam) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC0, hC⟩ := gaussRadialAbs_le auxC_pos 2
  refine ⟨C, hC0, fun lam hlam hlam1 => ?_⟩
  rw [cycleIntegral_sourceWeight_abs hlam]
  exact hC lam hlam hlam1

/-- **Non-cycle displacement, `β < 4`**: `∫ w e^{-c|u|²} ≤ C`, uniformly in `0 < λ ≤ 1`. -/
theorem noncycleIntegral_sourceWeight_le_of_lt_four {β : ℝ} (hβ : β < 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      noncycleIntegral lam (sourceWeight β 0 0 lam) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC0, hC⟩ := gaussRadial_le_of_lt_two auxC_pos (α := β / 2) (by linarith)
  refine ⟨C, hC0, fun lam hlam hlam1 => ?_⟩
  rw [noncycleIntegral_sourceWeight_zero hlam]
  simpa using hC lam hlam hlam1

/-- **Non-cycle displacement, `β = 4`, `δ ∈ {0, 1}`**: `∫ w e^{-c|u|²} ≤ C |log λ|^{1+δ}` for
`0 < λ ≤ e^{-1}`. -/
theorem noncycleIntegral_sourceWeight_le_four (δ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      noncycleIntegral lam (sourceWeight 4 δ 0 lam) ≤
        ENNReal.ofReal (C * |Real.log lam| ^ (δ + 1)) := by
  obtain ⟨C, hC0, hC⟩ := gaussRadial_le_of_eq_two auxC_pos δ
  refine ⟨C, hC0, fun lam hlam hlam1 => ?_⟩
  rw [noncycleIntegral_sourceWeight_zero hlam, show (4 : ℝ) / 2 = 2 by norm_num]
  have hlog : Real.log lam ≤ 0 := Real.log_nonpos hlam.le (hlam1.trans (Real.exp_le_one_iff.2 (by norm_num)))
  have := hC lam hlam hlam1
  simpa [abs_of_nonpos hlog] using this

/-- **Non-cycle displacement, `β > 4`** (any `δ`): `∫ w e^{-c|u|²} ≤ C λ^{2-β/2}` for
`0 < λ ≤ 1`. -/
theorem noncycleIntegral_sourceWeight_le_of_four_lt {β : ℝ} (hβ : 4 < β) (δ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      noncycleIntegral lam (sourceWeight β δ 0 lam) ≤ ENNReal.ofReal (C * lam ^ (2 - β / 2)) := by
  obtain ⟨C, hC0, hC⟩ := gaussRadial_le_of_two_lt auxC_pos.le (α := β / 2) (by linarith) δ
  refine ⟨C, hC0, fun lam hlam hlam1 => ?_⟩
  rw [noncycleIntegral_sourceWeight_zero hlam]
  exact hC lam hlam hlam1

/-- **Non-cycle displacement, `β = 0`, `δ' = 1`.** -/
theorem noncycleIntegral_sourceWeight_abs_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      noncycleIntegral lam (sourceWeight 0 0 1 lam) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC0, hC⟩ := gaussRadialAbs_le auxC_pos 1
  refine ⟨C, hC0, fun lam hlam hlam1 => ?_⟩
  rw [noncycleIntegral_sourceWeight_abs hlam]
  exact hC lam hlam hlam1

end AuxIntegration

end TwoComponentCoulomb

end
