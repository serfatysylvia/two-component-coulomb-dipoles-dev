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
public import TwoComponentCoulomb.Potential.Electric
import TwoComponentCoulomb.Potential.DiscField
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.ElectricEnergy
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# The ball-growth inequality for disc charges of general radii

For centres `zᵢ`, radii `αᵢ > 0` and real charges `dᵢ` write
`P(z, a; w, b) = pairInteraction z w a b = ∬ g(x - y) dδ_z^{(a)}(x) dδ_w^{(b)}(y)` and
`E(α) = Σᵢⱼ dᵢ dⱼ P(zᵢ, αᵢ; zⱼ, αⱼ)`. The key input is the positivity `E(α) ≥ 0` of the energy of
a neutral configuration of discs (`sum_pairInteraction_nonneg`, Lemma 2.4). Since
`F_λ(Z) = ½ E(λ) - N (g(λ) + κ)` (eq. (eq:F3), l. 155–158), the inequality `E(α) ≥ 0` gives the
ball-growth bound of Proposition 2.2 (source l. 512–544, (peq)):
`F_λ(Z) ≥ ½ (E(λ) - E(α)) - N (g(λ) + κ)`, in which the discs of radius `λ ≤ αᵢ` are replaced
by grown discs, and by Newton's theorem most terms cancel.

* `pairInteraction_eq_logKernel_of_add_le` : Newton's theorem for two discs of radii `a` and `b`
  whose closures are disjoint (`a + b ≤ |z - w|`): `P(z, a; w, b) = g(z - w)`.
* `pairInteraction_self`, `pairInteraction_eq_scaling` : `P(z, a; z, a) = g(a) + κ` and
  `P(z, a; w, a) = g(a) + g₁((w - z) / a)`.
* `energy_eq_half_sum_pairInteraction` : `F_λ = ½ Σ_{ab} d_a d_b P(z_a, λ; z_b, λ) - N (g(λ) + κ)`.
* `energy_ge_ballGrowth` : the ball-growth inequality for arbitrary radii `αᵢ ≥ λ`.
* `energy_ge_ballGrowth_overlap` : the reduced form of the inequality, in which only the
  ordered pairs `(i, j)`, `i ≠ j`, whose grown discs overlap (`|zᵢ - zⱼ| < αᵢ + αⱼ`) contribute:
  `F_λ(Z) ≥ -½ Σᵢ (g(αᵢ) + κ) + ½ Σ_{(i,j)} dᵢ dⱼ [g_λ(zⱼ - zᵢ) - P(zᵢ, αᵢ; zⱼ, αⱼ)]`.
-/

@[expose] public section

open MeasureTheory

namespace TwoComponentCoulomb

/-! ### The pair interaction of two discs -/

section PairInteraction

/-- **Newton's theorem for two discs of different radii**: if the closed discs `B̄(z, a)` and
`B̄(w, b)` have disjoint interiors (`a + b ≤ |z - w|`), then
`∬ g(x - y) dδ_z^{(a)}(x) dδ_w^{(b)}(y) = g(z - w)`. -/
theorem pairInteraction_eq_logKernel_of_add_le {z w : ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a + b ≤ ‖z - w‖) : pairInteraction z w a b = logKernel (z - w) := by
  rw [pairInteraction_eq_integral_discPotential z w hb]
  have h1 : ∀ᵐ x ∂smearedCharge z a, discPotential b (x - w) = logKernel (w - x) := by
    filter_upwards [ae_mem_ball_smearedCharge z a] with x hx
    have hx' : ‖x - z‖ < a := by simpa [dist_eq_norm] using hx
    have hxw : b ≤ ‖x - w‖ := by
      have h2 := norm_sub_le_norm_sub_add_norm_sub z x w
      rw [norm_sub_rev z x] at h2
      linarith
    rw [← integral_logKernel_sub_smearedCharge_eq_discPotential hb x w,
      integral_logKernel_sub_smearedCharge_of_le x w hb hxw, ← neg_sub x w, logKernel_neg]
  rw [integral_congr_ae h1, integral_logKernel_sub_smearedCharge_of_le w z ha
    (by rw [norm_sub_rev]; linarith), ← neg_sub z w, logKernel_neg]

/-- The self-interaction of a disc of radius `a > 0` is `g(a) + κ`. -/
theorem pairInteraction_self (z : ℂ) {a : ℝ} (ha : 0 < a) :
    pairInteraction z z a a = logKernel (a : ℂ) + kappa := by
  rw [pairInteraction_eq_smearedKernel, sub_self, smearedKernel_zero ha]

/-- **Scaling** of the interaction of two discs of the same radius `a > 0`:
`P(z, a; w, a) = g(a) + g₁((w - z) / a)`. -/
theorem pairInteraction_eq_scaling (z w : ℂ) {a : ℝ} (ha : 0 < a) :
    pairInteraction z w a a = logKernel (a : ℂ) + smearedKernel 1 ((w - z) / a) := by
  rw [pairInteraction_eq_smearedKernel, smearedKernel_eq_logKernel_add ha]

end PairInteraction

/-! ### The energy as a sum of pair interactions -/

section BallGrowth

/-- `F_λ` as a bilinear form in the pair interactions of discs of radius `λ`
(source eq. (eq:F3), l. 155–158). -/
theorem energy_eq_half_sum_pairInteraction {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ) {lam : ℝ} :
    energy lam Z = (1 / 2) * ∑ i, ∑ j, charge i * charge j * pairInteraction (Z i) (Z j) lam lam -
      N * (logKernel (lam : ℂ) + kappa) := by
  rfl

/-- **The ball-growth inequality for disc charges of general radii** (source l. 512–544, (peq)):
for radii `αᵢ ≥ λ`,
`F_λ(Z) ≥ ½ Σᵢⱼ dᵢ dⱼ [P(zᵢ, λ; zⱼ, λ) - P(zᵢ, αᵢ; zⱼ, αⱼ)] - N (g(λ) + κ)`.
It follows from the positivity of the pair energy `Σᵢⱼ dᵢ dⱼ P(zᵢ, αᵢ; zⱼ, αⱼ)` of the neutral
configuration of grown discs (Lemma 2.4). -/
theorem energy_ge_ballGrowth {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ) {lam : ℝ} (hlam : 0 < lam)
    (α : Fin N ⊕ Fin N → ℝ) (hα : ∀ i, lam ≤ α i) :
    energy lam Z ≥ (1 / 2) * ∑ i, ∑ j, charge i * charge j *
        (pairInteraction (Z i) (Z j) lam lam - pairInteraction (Z i) (Z j) (α i) (α j)) -
      N * (logKernel (lam : ℂ) + kappa) := by
  have hpos : ∀ i, 0 < α i := fun i => hlam.trans_le (hα i)
  have h0 := sum_pairInteraction_nonneg (d := charge) (z := Z) hpos (sum_charge_eq_zero N)
  rw [energy_eq_half_sum_pairInteraction Z]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  linarith

/-- A double sum over `ι × ι` whose off-diagonal terms vanish outside a relation `P` splits into
the diagonal and the sum over the ordered pairs `i ≠ j` with `P i j`. -/
theorem sum_sum_eq_sum_diag_add_sum_filter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ι → ℝ) (P : ι → ι → Prop) [∀ i j, Decidable (P i j)]
    (h : ∀ i j, i ≠ j → ¬P i j → D i j = 0) :
    ∑ i, ∑ j, D i j =
      ∑ i, D i i + ∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.1 ≠ p.2 ∧ P p.1 p.2), D p.1 p.2 := by
  have hpt : ∀ p : ι × ι, D p.1 p.2 =
      (if p.1 = p.2 then D p.1 p.1 else 0) + (if p.1 ≠ p.2 ∧ P p.1 p.2 then D p.1 p.2 else 0) := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · subst hij
      simp
    · by_cases hP : P i j
      · simp [hij, hP]
      · simp [hij, hP, h i j hij hP]
  have h1 : ∑ i, ∑ j, D i j = ∑ p : ι × ι, D p.1 p.2 := (Fintype.sum_prod_type' (f := D)).symm
  have h2 : ∑ p : ι × ι, (if p.1 = p.2 then D p.1 p.1 else 0) = ∑ i, D i i := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [h1, Finset.sum_congr rfl fun p _ => hpt p, Finset.sum_add_distrib, h2, Finset.sum_filter]

/-- **The reduced ball-growth inequality** (source l. 512–544, (peq)): for radii `αᵢ ≥ λ`, with
`S` the set of ordered pairs `i ≠ j` whose grown discs overlap (`|zᵢ - zⱼ| < αᵢ + αⱼ`),
`F_λ(Z) ≥ -½ Σᵢ (g(αᵢ) + κ) + ½ Σ_{(i,j) ∈ S} dᵢ dⱼ [g_λ(zⱼ - zᵢ) - P(zᵢ, αᵢ; zⱼ, αⱼ)]`.
The diagonal terms contribute `g(λ) - g(αᵢ)`, and the pairs of disjoint grown discs cancel by
Newton's theorem (`pairInteraction_eq_logKernel_of_add_le`). -/
theorem energy_ge_ballGrowth_overlap {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ) {lam : ℝ} (hlam : 0 < lam)
    (α : Fin N ⊕ Fin N → ℝ) (hα : ∀ i, lam ≤ α i) :
    energy lam Z ≥ -(1 / 2) * ∑ i, (logKernel (α i : ℂ) + kappa) +
      (1 / 2) * ∑ p ∈ Finset.univ.filter (fun p : (Fin N ⊕ Fin N) × (Fin N ⊕ Fin N) =>
          p.1 ≠ p.2 ∧ ‖Z p.1 - Z p.2‖ < α p.1 + α p.2),
        charge p.1 * charge p.2 *
          (smearedKernel lam (Z p.2 - Z p.1) -
            pairInteraction (Z p.1) (Z p.2) (α p.1) (α p.2)) := by
  have hpos : ∀ i, 0 < α i := fun i => hlam.trans_le (hα i)
  refine le_of_eq_of_le ?_ (energy_ge_ballGrowth Z hlam α hα)
  rw [sum_sum_eq_sum_diag_add_sum_filter _ (fun i j => ‖Z i - Z j‖ < α i + α j)]
  · have hdiag : ∀ i, charge i * charge i *
        (pairInteraction (Z i) (Z i) lam lam - pairInteraction (Z i) (Z i) (α i) (α i)) =
        logKernel (lam : ℂ) - logKernel (α i : ℂ) := fun i => by
      rw [charge_mul_self, pairInteraction_self _ hlam, pairInteraction_self _ (hpos i)]
      ring
    have hcard : (Finset.univ : Finset (Fin N ⊕ Fin N)).card = 2 * N := by
      simp [two_mul]
    have hS : ∀ p ∈ Finset.univ.filter (fun p : (Fin N ⊕ Fin N) × (Fin N ⊕ Fin N) =>
          p.1 ≠ p.2 ∧ ‖Z p.1 - Z p.2‖ < α p.1 + α p.2),
        charge p.1 * charge p.2 *
          (pairInteraction (Z p.1) (Z p.2) lam lam - pairInteraction (Z p.1) (Z p.2) (α p.1) (α p.2))
        = charge p.1 * charge p.2 *
          (smearedKernel lam (Z p.2 - Z p.1) -
            pairInteraction (Z p.1) (Z p.2) (α p.1) (α p.2)) := fun p _ => by
      rw [pairInteraction_eq_smearedKernel]
    have e1 : ∑ i, charge i * charge i *
        (pairInteraction (Z i) (Z i) lam lam - pairInteraction (Z i) (Z i) (α i) (α i)) =
        ∑ i, (logKernel (lam : ℂ) - logKernel (α i : ℂ)) := Finset.sum_congr rfl fun i _ => hdiag i
    rw [e1, Finset.sum_congr rfl hS, Finset.sum_sub_distrib,
      Finset.sum_const, hcard, Finset.sum_add_distrib, Finset.sum_const, hcard]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  · intro i j _ hP
    rw [not_lt] at hP
    have h1 : lam + lam ≤ ‖Z i - Z j‖ := by linarith [hα i, hα j]
    rw [pairInteraction_eq_logKernel_of_add_le hlam hlam h1,
      pairInteraction_eq_logKernel_of_add_le (hpos i) (hpos j) hP, sub_self, mul_zero]

end BallGrowth

end TwoComponentCoulomb

end
