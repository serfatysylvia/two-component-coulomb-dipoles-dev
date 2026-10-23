/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TwoComponentCoulomb.Integrals.PiProduct
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Gaussian decoupling of a packing constraint

Source `source/dipole-formation.tex`, Lemma `lem:gaussian decoupling`.
The pointwise exponential bound is integrated against an arbitrary family of measurable
nonnegative planar weights. Fubini then separates the Gaussian factors.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-- The indicator of the packing constraint is bounded by its exponential Markov weight. -/
theorem indicator_packing_le_gaussian {ι : Type*} [Fintype ι] {a s : ℝ} (ha : 0 ≤ a)
    (u : ι → ℂ) :
    (if ∑ j, ‖u j‖ ^ 2 ≤ s then (1 : ℝ) else 0) ≤
      Real.exp (a * (s - ∑ j, ‖u j‖ ^ 2)) := by
  split_ifs with hu
  · exact Real.one_le_exp (mul_nonneg ha (sub_nonneg.2 hu))
  · exact (Real.exp_pos _).le

/-- Gaussian decoupling for arbitrary, possibly different measurable nonnegative weights
on the plane, including the empty family. -/
theorem lintegral_gaussian_decoupling {ι : Type*} [Fintype ι] {a s : ℝ} (ha : 0 ≤ a)
    (w : ι → ℂ → ℝ) (hw : ∀ j, Measurable (w j)) (hw0 : ∀ j u, 0 ≤ w j u) :
    ∫⁻ u : ι → ℂ in {u | ∑ j, ‖u j‖ ^ 2 ≤ s}, ENNReal.ofReal (∏ j, w j (u j)) ≤
      ENNReal.ofReal (Real.exp (a * s)) *
        ∏ j, ∫⁻ u : ℂ, ENNReal.ofReal (w j u * Real.exp (-a * ‖u‖ ^ 2)) := by
  classical
  have hset : MeasurableSet {u : ι → ℂ | ∑ j, ‖u j‖ ^ 2 ≤ s} := by
    exact measurableSet_le (by fun_prop) measurable_const
  rw [← lintegral_indicator hset]
  calc
    _ ≤ ∫⁻ u : ι → ℂ, ENNReal.ofReal (Real.exp (a * s)) *
        ∏ j, ENNReal.ofReal (w j (u j) * Real.exp (-a * ‖u j‖ ^ 2)) := by
      apply lintegral_mono
      intro u
      dsimp only
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => mul_nonneg (hw0 j _) (Real.exp_pos _).le),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      by_cases hu : ∑ j, ‖u j‖ ^ 2 ≤ s
      · rw [Set.indicator_of_mem (show u ∈ {u : ι → ℂ | ∑ j, ‖u j‖ ^ 2 ≤ s} from hu)]
        apply ENNReal.ofReal_le_ofReal
        have hprod : Real.exp (a * s) * ∏ j, (w j (u j) * Real.exp (-a * ‖u j‖ ^ 2)) =
            (∏ j, w j (u j)) * Real.exp (a * (s - ∑ j, ‖u j‖ ^ 2)) := by
          rw [Finset.prod_mul_distrib, ← Real.exp_sum, mul_left_comm, ← Real.exp_add,
            ← Finset.mul_sum]
          congr 2
          ring
        rw [hprod]
        have h := indicator_packing_le_gaussian ha u (s := s)
        rw [ite_eq_left hu] at h
        exact le_mul_of_one_le_right (Finset.prod_nonneg fun j _ => hw0 j _) h
      · rw [Set.indicator_of_notMem (show u ∉ {u : ι → ℂ | ∑ j, ‖u j‖ ^ 2 ≤ s} from hu)]
        exact zero_le
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact lintegral_fintype_pi_prod volume
        (fun j u => ENNReal.ofReal (w j u * Real.exp (-a * ‖u‖ ^ 2)))
        (fun j => by fun_prop)

end TwoComponentCoulomb

end
