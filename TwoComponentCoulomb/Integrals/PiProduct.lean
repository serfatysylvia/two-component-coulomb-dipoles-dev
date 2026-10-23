/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Integrals of products of one-variable functions over a product measure

Fubini's theorem in `[0, ∞]` for a product of functions of one coordinate each, with respect to
the product `Measure.pi fun _ => μ` of copies of one `σ`-finite measure `μ`.

* `TwoComponentCoulomb.lintegral_fin_pi_prod` : the integral over `Fin n → E` of `∏ᵢ fᵢ(xᵢ)`
  is `∏ᵢ ∫ fᵢ`.
* `TwoComponentCoulomb.lintegral_fintype_pi_prod` : the same over `ι → E` for a finite type `ι`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-- Fubini for a product of one-variable functions over `Fin n → E`, in `[0, ∞]`. -/
theorem lintegral_fin_pi_prod {n : ℕ} {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ x, f i x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero]
    simp only [Equiv.coe_fn_mk, Fin.cons_succ, cast_eq, Fin.cons_zero]
    have hg : Measurable fun y : Fin n → E => ∏ x, f x.succ (y x) :=
      Finset.measurable_prod _ fun x _ => (hf x.succ).comp (measurable_pi_apply x)
    rw [lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable,
      ih (fun i => f i.succ) (fun i => hf i.succ)]

/-- **Fubini for a product of functions of one coordinate each**, in `[0, ∞]`: the integral over
`ι → E` of `∏ᵢ fᵢ(xᵢ)` is `∏ᵢ ∫ fᵢ`. -/
theorem lintegral_fintype_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (f : ι → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ x, f i x ∂μ := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft (fun _ : ι => μ) e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_pi_prod μ (fun i => f (e i)) fun i => hf (e i)

end TwoComponentCoulomb

end
