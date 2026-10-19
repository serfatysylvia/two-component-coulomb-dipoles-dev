/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Algebra.Order.Floor.Semiring
public import TwoComponentCoulomb.NearestNeighbor.Basic

/-!
# Cone bounds (Remark 2.1)

Source l. 388--397: dividing the plane around a point `O` into six half-open cones of angle
`π/3`, if `A, B` lie in one cone and `|OA| ≤ |OB|` then `|AB| < |OB|`. Consequently `O` is the
nearest neighbour of at most six points, and the number of points `j ≠ O` having at most one
point strictly closer than `O` is at most twelve (the points having `O` as second nearest
neighbour are among them).

All statements involving configurations assume that the points of the configuration are distinct
(`Function.Injective Z`); the cone lemmas themselves are pure plane geometry.

* `norm_sub_lt_of_mul_conj_re`: law of cosines form of the cone estimate.
* `exists_sector`: six half-open sectors of angle `π/3`.
* `card_filter_nearestNeighbor_eq_le_six`: the nearest-neighbour in-degree is at most six.
* `card_filter_card_filter_lt_le_one_le_twelve`: the second-neighbour form of the bound.
-/

public section

namespace TwoComponentCoulomb

open Finset

/-- Law of cosines form of the cone estimate: if the angle between `a - o` and `b - o` is less
than `π/3` (that is, `cos (angle) > 1/2`) and `|a - o| ≤ |b - o|`, then `|a - b| < |b - o|`. -/
theorem norm_sub_lt_of_mul_conj_re {o a b : ℂ} (hle : ‖a - o‖ ≤ ‖b - o‖)
    (hcos : ‖a - o‖ * ‖b - o‖ < 2 * ((a - o) * (starRingEnd ℂ) (b - o)).re) :
    ‖a - b‖ < ‖b - o‖ := by
  have hab : a - b = (a - o) - (b - o) := by ring
  rw [hab]
  generalize a - o = v at *
  generalize b - o = w at *
  have hsq : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 - 2 * (v * (starRingEnd ℂ) w).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hv := norm_nonneg v
  have hw := norm_nonneg w
  have hvw : ‖v‖ ^ 2 ≤ ‖v‖ * ‖w‖ := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hw (by nlinarith)

/-- The index (in `{1, …, 6}`) of the half-open sector `(-π + (k-1) π/3, -π + k π/3]` containing
the argument of `v`. -/
private noncomputable def sectorIdx (v : ℂ) : ℕ :=
  ⌈3 * (Complex.arg v + Real.pi) / Real.pi⌉₊

private theorem one_le_sectorIdx (v : ℂ) : 1 ≤ sectorIdx v := by
  have hπ := Real.pi_pos
  have := Complex.neg_pi_lt_arg v
  exact Nat.ceil_pos.2 (div_pos (by linarith) hπ)

private theorem sectorIdx_le_six (v : ℂ) : sectorIdx v ≤ 6 := by
  have hπ := Real.pi_pos
  have := Complex.arg_le_pi v
  refine Nat.ceil_le.2 ?_
  rw [div_le_iff₀ hπ]
  push_cast
  nlinarith

private theorem abs_arg_sub_arg_lt {v w : ℂ} (h : sectorIdx v = sectorIdx w) :
    |Complex.arg v - Complex.arg w| < Real.pi / 3 := by
  have hπ := Real.pi_pos
  have hv := Complex.neg_pi_lt_arg v
  have hw := Complex.neg_pi_lt_arg w
  have hv0 : 0 ≤ 3 * (Complex.arg v + Real.pi) / Real.pi := div_nonneg (by linarith) hπ.le
  have hw0 : 0 ≤ 3 * (Complex.arg w + Real.pi) / Real.pi := div_nonneg (by linarith) hπ.le
  have h1 := Nat.le_ceil (3 * (Complex.arg v + Real.pi) / Real.pi)
  have h2 := Nat.le_ceil (3 * (Complex.arg w + Real.pi) / Real.pi)
  have h3 := Nat.ceil_lt_add_one hv0
  have h4 := Nat.ceil_lt_add_one hw0
  have e : ((⌈3 * (Complex.arg v + Real.pi) / Real.pi⌉₊ : ℕ) : ℝ) =
      ((⌈3 * (Complex.arg w + Real.pi) / Real.pi⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [e] at h1 h3
  rw [abs_lt]
  have h1' : 3 * (Complex.arg v + Real.pi) / Real.pi - 3 * (Complex.arg w + Real.pi) / Real.pi <
      1 := by linarith
  have h2' : 3 * (Complex.arg w + Real.pi) / Real.pi - 3 * (Complex.arg v + Real.pi) / Real.pi <
      1 := by linarith
  have e1 : 3 * (Complex.arg v + Real.pi) / Real.pi - 3 * (Complex.arg w + Real.pi) / Real.pi =
      3 * (Complex.arg v - Complex.arg w) / Real.pi := by
    field_simp
    ring
  have e2 : 3 * (Complex.arg w + Real.pi) / Real.pi - 3 * (Complex.arg v + Real.pi) / Real.pi =
      3 * (Complex.arg w - Complex.arg v) / Real.pi := by
    field_simp
    ring
  rw [e1, div_lt_one hπ] at h1'
  rw [e2, div_lt_one hπ] at h2'
  constructor <;> linarith

/-- Six half-open sectors of angle `π/3` around the origin: two nonzero vectors in the same sector
make an angle less than `π/3`, i.e. have `cos (angle) > 1/2`. -/
theorem exists_sector : ∃ s : ℂ → Fin 6, ∀ v w : ℂ, v ≠ 0 → w ≠ 0 → s v = s w →
    ‖v‖ * ‖w‖ < 2 * (v * (starRingEnd ℂ) w).re := by
  refine ⟨fun v => ⟨sectorIdx v - 1, by have := sectorIdx_le_six v; omega⟩, ?_⟩
  intro v w hv hw hs
  have hs' : sectorIdx v = sectorIdx w := by
    have h1 := one_le_sectorIdx v
    have h2 := one_le_sectorIdx w
    have := congrArg Fin.val hs
    simp only at this
    omega
  have habs := abs_arg_sub_arg_lt hs'
  have hcos : 1 / 2 < Real.cos (Complex.arg v - Complex.arg w) := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) habs
  have hre : (v * (starRingEnd ℂ) w).re =
      ‖v‖ * ‖w‖ * Real.cos (Complex.arg v - Complex.arg w) := by
    rw [Real.cos_sub]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    rw [← Complex.norm_mul_cos_arg v, ← Complex.norm_mul_cos_arg w,
      ← Complex.norm_mul_sin_arg v, ← Complex.norm_mul_sin_arg w]
    ring
  rw [hre]
  have hvw : 0 < ‖v‖ * ‖w‖ := mul_pos (norm_pos_iff.2 hv) (norm_pos_iff.2 hw)
  nlinarith

variable {N : ℕ}

/-- Core counting bound: if every `j ∈ T` is different from `o` and has at most `c` indices
`k ∉ {j, o}` with `z_k` strictly closer to `z_j` than `z_o`, then `T` has at most `6 (c + 1)`
elements (points of `Z` distinct). In each of the six sectors around `z_o`, the point of `T`
farthest from `z_o` has all the other `T`-points of that sector strictly closer than `z_o`. -/
theorem card_le_six_mul_of_card_filter_lt_le {Z : Fin N ⊕ Fin N → ℂ} (hZ : Function.Injective Z)
    (o : Fin N ⊕ Fin N) (c : ℕ) (T : Finset (Fin N ⊕ Fin N))
    (hT : ∀ j ∈ T, j ≠ o ∧
      (univ.filter fun k => k ≠ j ∧ k ≠ o ∧ ‖Z j - Z k‖ < ‖Z j - Z o‖).card ≤ c) :
    T.card ≤ 6 * (c + 1) := by
  obtain ⟨s, hs⟩ := exists_sector
  have hfib : ∀ b ∈ T.image (fun j => s (Z j - Z o)),
      (T.filter fun j => s (Z j - Z o) = b).card ≤ c + 1 := by
    intro b _
    set F := T.filter fun j => s (Z j - Z o) = b with hF
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · simp [hFe]
    obtain ⟨m, hmF, hmmax⟩ := F.exists_max_image (fun j => ‖Z j - Z o‖) hFne
    have hsub : F.erase m ⊆
        univ.filter fun k => k ≠ m ∧ k ≠ o ∧ ‖Z m - Z k‖ < ‖Z m - Z o‖ := by
      intro j hj
      obtain ⟨hjm, hjF⟩ := mem_erase.1 hj
      have hjT := (mem_filter.1 hjF).1
      have hmT := (mem_filter.1 hmF).1
      have hsj : s (Z j - Z o) = s (Z m - Z o) :=
        (mem_filter.1 hjF).2.trans (mem_filter.1 hmF).2.symm
      have hjo : Z j - Z o ≠ 0 := sub_ne_zero.2 (hZ.ne (hT j hjT).1)
      have hmo : Z m - Z o ≠ 0 := sub_ne_zero.2 (hZ.ne (hT m hmT).1)
      have hlt := norm_sub_lt_of_mul_conj_re (o := Z o) (a := Z j) (b := Z m)
        (hmmax j hjF) (hs _ _ hjo hmo hsj)
      rw [norm_sub_rev] at hlt
      simpa [mem_filter, hjm, (hT j hjT).1] using hlt
    have h1 := card_le_card hsub
    have h2 := (hT m (mem_filter.1 hmF).1).2
    have h3 := card_erase_add_one hmF
    omega
  have h1 := Finset.card_le_mul_card_image (f := fun j => s (Z j - Z o)) T (c + 1) hfib
  have h2 : (T.image fun j => s (Z j - Z o)).card ≤ 6 :=
    (card_le_univ _).trans (by simp)
  calc T.card ≤ (c + 1) * (T.image fun j => s (Z j - Z o)).card := h1
    _ ≤ (c + 1) * 6 := Nat.mul_le_mul_left _ h2
    _ = 6 * (c + 1) := by ring

/-- Remark 2.1, first bound: a point is the nearest neighbour of at most six points. -/
theorem card_filter_nearestNeighbor_eq_le_six {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : Function.Injective Z) (o : Fin N ⊕ Fin N) :
    (univ.filter fun j => nearestNeighbor Z j = o).card ≤ 6 := by
  have h := card_le_six_mul_of_card_filter_lt_le hZ o 0
    (univ.filter fun j => nearestNeighbor Z j = o) ?_
  · simpa using h
  intro j hj
  have hφ : nearestNeighbor Z j = o := (mem_filter.1 hj).2
  refine ⟨fun hjo => nearestNeighbor_ne Z j (hφ.trans hjo.symm), ?_⟩
  refine (card_eq_zero.2 (filter_eq_empty_iff.2 fun k _ hk => ?_)).le
  have := norm_sub_nearestNeighbor_le Z hk.1
  rw [hφ] at this
  exact absurd hk.2.2 (not_lt.2 this)

/-- Remark 2.1, second bound (stated without the second nearest neighbour map): at most twelve
indices `j ≠ o` have at most one index `k ∉ {j, o}` with `z_k` strictly closer to `z_j` than
`z_o`. In particular `o` is the second nearest neighbour of at most twelve points. -/
theorem card_filter_card_filter_lt_le_one_le_twelve {Z : Fin N ⊕ Fin N → ℂ}
    (hZ : Function.Injective Z) (o : Fin N ⊕ Fin N) :
    (univ.filter fun j => j ≠ o ∧
      (univ.filter fun k => k ≠ j ∧ k ≠ o ∧ ‖Z j - Z k‖ < ‖Z j - Z o‖).card ≤ 1).card ≤ 12 :=
  card_le_six_mul_of_card_filter_lt_le hZ o 1 _ fun _ hj => (mem_filter.1 hj).2

end TwoComponentCoulomb

end
