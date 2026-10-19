/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Charge
public import TwoComponentCoulomb.Frozen.Energy
public import TwoComponentCoulomb.Frozen.Kappa
public import TwoComponentCoulomb.Frozen.LogKernel
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.Potential.SmearedCharge

/-!
# The pair integral of two uniform disc measures

Identities for the double integrals `∬ f(x - y) dδ_z^{(a)}(x) dδ_w^{(b)}(y)` occurring in the
definitions of `smearedKernel` (source eq. (eq:defgeta), l. 162–163), `kappa` and `energy`
(eq. (eq:F3), l. 155–158).

* `integral_prod_smearedCharge_sub` : translation invariance of the pair integral.
* `integral_logKernel_prod_smearedCharge` : the pair integral of `logKernel` is
  `smearedKernel lam (w - z)`.
* `energy_eq_sum_smearedKernel` : `energy lam Z` as a sum of values of `smearedKernel`.
* `smearedKernel_neg`, `smearedKernel_eq_of_norm_eq`, `smearedKernel_eq_norm` : `g_λ` is even and
  radial.
* `charge_inl`, `charge_inr`, `charge_mul_self`, `charge_eq_one_or_neg_one` : the sign function
  `charge`.

No integrability of `logKernel` is needed: every identity is a change of variables for Bochner
integrals along measurable embeddings or the swap of the factors of a product measure.
-/

public section

open MeasureTheory

namespace TwoComponentCoulomb

/-! ### The sign function -/

section Charge

@[simp]
theorem charge_inl {N : ℕ} (i : Fin N) : charge (Sum.inl i) = 1 := rfl

@[simp]
theorem charge_inr {N : ℕ} (i : Fin N) : charge (Sum.inr i) = -1 := rfl

@[simp]
theorem charge_mul_self {N : ℕ} (a : Fin N ⊕ Fin N) : charge a * charge a = 1 := by
  rcases a with i | i <;> simp

theorem charge_eq_one_or_neg_one {N : ℕ} (a : Fin N ⊕ Fin N) : charge a = 1 ∨ charge a = -1 := by
  rcases a with a | a
  · exact Or.inl (charge_inl a)
  · exact Or.inr (charge_inr a)

end Charge

/-! ### Elementary facts on `logKernel` -/

@[simp]
theorem logKernel_neg (x : ℂ) : logKernel (-x) = logKernel x := by
  simp [logKernel]

theorem logKernel_mul_sub_mul_of_norm_eq_one (x y : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    logKernel (u * x - u * y) = logKernel (x - y) := by
  simp [logKernel, ← mul_sub, hu]

/-! ### Change of variables for product measures -/

/-- Change of variables on a product of two pushforwards by the same measurable embedding. -/
theorem integral_prod_map_embedding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → ℂ} (hf : MeasurableEmbedding f) (μ ν : Measure ℂ) [SFinite μ] [SFinite ν]
    (g : ℂ × ℂ → E) :
    ∫ p, g p ∂(μ.map f).prod (ν.map f) = ∫ p, g (f p.1, f p.2) ∂μ.prod ν := by
  rw [Measure.map_prod_map μ ν hf.measurable hf.measurable]
  exact (hf.prodMap hf).integral_map g

/-- Translation invariance of the pair integral of a function of the difference. -/
theorem integral_prod_smearedCharge_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (z w : ℂ) (a b : ℝ) :
    ∫ p : ℂ × ℂ, f (p.1 - p.2) ∂(smearedCharge z a).prod (smearedCharge w b) =
      ∫ p : ℂ × ℂ, f (p.1 - p.2) ∂(smearedCharge 0 a).prod (smearedCharge (w - z) b) := by
  have h1 : smearedCharge z a = (smearedCharge 0 a).map (· + z) := by
    rw [map_add_right_smearedCharge, zero_add]
  have h2 : smearedCharge w b = (smearedCharge (w - z) b).map (· + z) := by
    rw [map_add_right_smearedCharge, sub_add_cancel]
  rw [h1, h2, integral_prod_map_embedding (measurableEmbedding_addRight z)]
  simp

/-- The pair integral of `logKernel` against two discs of radius `lam` is `smearedKernel`
evaluated at the difference of the centres. -/
theorem integral_logKernel_prod_smearedCharge (z w : ℂ) (lam : ℝ) :
    ∫ p : ℂ × ℂ, logKernel (p.1 - p.2) ∂(smearedCharge z lam).prod (smearedCharge w lam) =
      smearedKernel lam (w - z) :=
  integral_prod_smearedCharge_sub logKernel z w lam lam

/-- `F_λ` as a sum of values of `g_λ` at differences of the charge positions. -/
theorem energy_eq_sum_smearedKernel {N : ℕ} (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) :
    energy lam Z = (1 / 2) * ∑ a, ∑ b, charge a * charge b * smearedKernel lam (Z b - Z a) -
      N * (logKernel lam + kappa) := by
  unfold energy
  simp_rw [integral_logKernel_prod_smearedCharge]

/-! ### Symmetries of the pair integral and of `smearedKernel` -/

/-- Swapping the two discs in the pair integral of an even function of the difference. -/
theorem integral_prod_smearedCharge_sub_comm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (hf : ∀ x, f (-x) = f x) (z w : ℂ) (a b : ℝ) :
    ∫ p : ℂ × ℂ, f (p.1 - p.2) ∂(smearedCharge z a).prod (smearedCharge w b) =
      ∫ p : ℂ × ℂ, f (p.1 - p.2) ∂(smearedCharge w b).prod (smearedCharge z a) := by
  rw [← integral_prod_swap (fun p : ℂ × ℂ => f (p.1 - p.2))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← hf, neg_sub]

/-- `g_λ` is even. -/
theorem smearedKernel_neg (lam : ℝ) (z : ℂ) : smearedKernel lam (-z) = smearedKernel lam z := by
  have h := integral_logKernel_prod_smearedCharge (-z) 0 lam
  rw [zero_sub, neg_neg] at h
  rw [← h]
  exact integral_prod_smearedCharge_sub_comm logKernel logKernel_neg 0 (-z) lam lam

/-- `g_λ` is radial: it only depends on `‖z‖`. -/
theorem smearedKernel_eq_of_norm_eq (lam : ℝ) {z w : ℂ} (h : ‖z‖ = ‖w‖) :
    smearedKernel lam z = smearedKernel lam w := by
  by_cases hz : z = 0
  · subst hz
    have hw : w = 0 := norm_eq_zero.1 (by simpa using h.symm)
    rw [hw]
  · have hu : ‖w / z‖ = 1 := by
      rw [norm_div, ← h, div_self (norm_ne_zero_iff.2 hz)]
    have hu0 : w / z ≠ 0 := by
      intro h0
      rw [h0] at hu
      simp at hu
    have huz : w / z * z = w := div_mul_cancel₀ w hz
    have e : (smearedCharge 0 lam).prod (smearedCharge w lam) =
        ((smearedCharge 0 lam).map (fun x => w / z * x)).prod
          ((smearedCharge z lam).map (fun x => w / z * x)) := by
      rw [map_mul_smearedCharge_of_norm_eq_one _ _ hu, map_mul_smearedCharge_of_norm_eq_one _ _ hu,
        mul_zero, huz]
    unfold smearedKernel
    rw [e, integral_prod_map_embedding (measurableEmbedding_mulLeft₀ hu0)]
    simp only [logKernel_mul_sub_mul_of_norm_eq_one _ _ hu]

/-- `g_λ z = g_λ ‖z‖`. -/
theorem smearedKernel_eq_norm (lam : ℝ) (z : ℂ) :
    smearedKernel lam z = smearedKernel lam (‖z‖ : ℂ) :=
  smearedKernel_eq_of_norm_eq lam (by simp)

end TwoComponentCoulomb

end
