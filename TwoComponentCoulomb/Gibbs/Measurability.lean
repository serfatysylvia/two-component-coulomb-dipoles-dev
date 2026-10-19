/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import TwoComponentCoulomb.Frozen.ReducedEnergy
public import TwoComponentCoulomb.NearestNeighbor.Basic
public import TwoComponentCoulomb.Potential.PairIntegral

/-!
# Measurability of the energies

Measurability of the Hamiltonians appearing in the Gibbs measure `gibbsMeasure` (source l. 172--177) as functions on the configuration space
`Fin N ⊕ Fin N → ℂ`.

* `measurable_logKernel` : `g = -log |·|` is measurable.
* `smearedKernel_eq_integral_sub` : `g_λ(z) = ∬ g(x - y - z) dδ₀^{(λ)}(x) dδ₀^{(λ)}(y)`
  (translation of the second disc to the origin).
* `measurable_smearedKernel` : `g_λ` is measurable. This is the measurability of a parametric
  Bochner integral of a jointly measurable function; no continuity or integrability of
  `g_λ` is used.
* `measurable_energy` : `F_λ` (source eq. (eq:F3), l. 155--158) is measurable.
* `measurable_reducedEnergy` : `F̃_λ` (source l. 255--257) is measurable.
-/

public section

open MeasureTheory

namespace TwoComponentCoulomb

/-! ### The kernel `g_λ` -/

/-- The logarithmic kernel `g = -log |·|` is measurable. -/
theorem measurable_logKernel : Measurable logKernel := by
  unfold logKernel
  exact (Real.measurable_log.comp continuous_norm.measurable).neg

/-- Translating the second disc to the origin: `g_λ(z)` is the integral of `g(x - y - z)` against
`δ₀^{(λ)} ⊗ δ₀^{(λ)}`. -/
theorem smearedKernel_eq_integral_sub (lam : ℝ) (z : ℂ) :
    smearedKernel lam z =
      ∫ p : ℂ × ℂ, logKernel (p.1 - p.2 - z) ∂(smearedCharge 0 lam).prod (smearedCharge 0 lam) := by
  have h1 : smearedCharge z lam = (smearedCharge 0 lam).map (· + z) := by
    rw [map_add_right_smearedCharge, zero_add]
  have h2 : (smearedCharge 0 lam).prod (smearedCharge z lam) =
      ((smearedCharge 0 lam).map id).prod ((smearedCharge 0 lam).map (· + z)) := by
    rw [Measure.map_id, ← h1]
  unfold smearedKernel
  rw [h2, Measure.map_prod_map _ _ measurable_id (measurable_add_const z),
    (MeasurableEmbedding.id.prodMap (measurableEmbedding_addRight z)).integral_map]
  simp only [Prod.map_fst, Prod.map_snd, id, sub_add_eq_sub_sub]

/-- `g_λ` is measurable, for every `λ`. -/
theorem measurable_smearedKernel (lam : ℝ) : Measurable (smearedKernel lam) := by
  have h : smearedKernel lam = fun z => ∫ p : ℂ × ℂ,
      logKernel (p.1 - p.2 - z) ∂(smearedCharge 0 lam).prod (smearedCharge 0 lam) :=
    funext (smearedKernel_eq_integral_sub lam)
  rw [h]
  have hm : Measurable fun q : ℂ × (ℂ × ℂ) => logKernel (q.2.1 - q.2.2 - q.1) :=
    measurable_logKernel.comp (by fun_prop)
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

/-! ### The energies `F_λ` and `F̃_λ` -/

/-- `F_λ` (source eq. (eq:F3)) is measurable on the configuration space. -/
theorem measurable_energy {N : ℕ} (lam : ℝ) : Measurable (energy (N := N) lam) := by
  have hk := measurable_smearedKernel lam
  have h : energy (N := N) lam = fun Z => (1 / 2) * ∑ a, ∑ b, charge a * charge b *
      smearedKernel lam (Z b - Z a) - N * (logKernel lam + kappa) :=
    funext (energy_eq_sum_smearedKernel lam)
  rw [h]
  fun_prop

/-- The index type `Fin N ⊕ Fin N` has measurable singletons. -/
local instance measurableSingletonClass_sum_fin (N : ℕ) :
    MeasurableSingletonClass (Fin N ⊕ Fin N) :=
  ⟨fun x => by rcases x with a | a <;> simp [measurableSet_sum_iff]⟩

open scoped Classical in
/-- `F̃_λ` (source l. 255--257) is measurable on the configuration space. The summand depends on
`Z` through `Z ↦ φ₁ Z`, which is measurable with values in the finite set of self-maps of the index
set, and through the measurable map `g_λ ∘ (Z i - Z (φ₁ i))` on each of its fibres. -/
theorem measurable_reducedEnergy {N : ℕ} (lam : ℝ) :
    Measurable (reducedEnergy (N := N) lam) := by
  have hk := measurable_smearedKernel lam
  unfold reducedEnergy
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  let G : (Fin N ⊕ Fin N → ℂ) × (Fin N ⊕ Fin N → Fin N ⊕ Fin N) → ℝ := fun p =>
    if p.2 (p.2 i) = i ∧ charge i * charge (p.2 i) = -1 then
      smearedKernel lam (p.1 i - p.1 (p.2 i)) else 0
  have hG : Measurable G := by
    refine measurable_from_prod_countable_left fun f => ?_
    by_cases h : f (f i) = i ∧ charge i * charge (f i) = -1
    · simp only [G, h, and_self, ite_true]
      exact hk.comp (by fun_prop)
    · simp only [G, h, ite_false]
      exact measurable_const
  exact hG.comp (measurable_id.prodMk measurable_nearestNeighbor)

end TwoComponentCoulomb

end
