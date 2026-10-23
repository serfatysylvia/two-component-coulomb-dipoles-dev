/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.ReducedPartitionFunction
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import TwoComponentCoulomb.Gibbs.Basic
import TwoComponentCoulomb.Integrals.GaussianMass
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.NearestNeighbor.Basic
import TwoComponentCoulomb.PhaseSpace.Packing
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.UpperBound.MatchingSum

/-!
# The matching upper bound for the reduced partition function (Lemma 3.5, upper half)

Source `source/dipole-formation.tex`, l. 898–908, 933–935. For `Z = (X, Y)` (positive charges
`inl`, negative charges `inr`) with nearest-neighbour map `φ = nearestNeighbor Z`, the *neutral
2-cycles* are the pairs `(a, b)` with `φ (inl a) = inr b` and `φ (inr b) = inl a`; they form a
partial matching between positive and negative indices. The reduced energy only sees them, and
counts each twice with weight `1/2`, so that
`exp (-β F̃_λ (Z)) = ∏_{(a, b) neutral 2-cycle} exp (β g_λ (x_a - y_b))`.

If the weight is dominated by `K₀ ∏_{(a, b)} G (x_a - y_b)` then the integrand is at most `K₀`
times the sum over *all* partial matchings `M` of `∏_{(a, b) ∈ M} G (x_a - y_b)`. Integrating over
`Λ^{2N}`, a matching of size `p` contributes at most `N ^ (2 N - p) (∫ G) ^ p`
(`lintegral_prod_matching_le`), and there are exactly `C(N, p) · N! / (N - p)!` of them
(`card_matchings_filter_card_eq`). The sum is then bounded by `sum_matchings_le`.

* `neutralPairs`, `IsMatching`, `isMatching_neutralPairs` : the neutral 2-cycles as a partial
  matching.
* `exp_neg_reducedEnergy_eq_prod` : the product formula for the reduced Boltzmann weight (and its
  `Sum.elim X Y` form).
* `sum_sq_neutralPairs_le` : the packing bound `∑_{pairs} |u|² ≤ 18 N / π` .
* `lintegral_prod_matching_le` : the integral of a matching product.
* `reducedPartitionFunction_le_sum_matchings` : the reduction of `𝒦_{N, β}^λ` to the matching sum.
* `reducedPartitionFunction_le_of_gt_two` (`β > 2`) and `reducedPartitionFunction_two_le`
  (`β = 2`, Gaussian factor of parameter `ℓ`): the final bounds
  `𝒦 ≤ N! N^N A^N e^{2 N / √A}` (times `e^{18 N / (π ℓ)}` when `β = 2`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Nat

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### The neutral 2-cycles -/

/-- The neutral 2-cycles of `φ₁ = nearestNeighbor Z`, as pairs `(a, b)` of a positive index `a` and
a negative index `b` that are mutual nearest neighbours: `φ₁ (inl a) = inr b` and
`φ₁ (inr b) = inl a`. -/
noncomputable def neutralPairs (Z : Fin N ⊕ Fin N → ℂ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p => nearestNeighbor Z (Sum.inl p.1) = Sum.inr p.2 ∧
    nearestNeighbor Z (Sum.inr p.2) = Sum.inl p.1

theorem mem_neutralPairs {Z : Fin N ⊕ Fin N → ℂ} {p : Fin N × Fin N} :
    p ∈ neutralPairs Z ↔
      nearestNeighbor Z (Sum.inl p.1) = Sum.inr p.2 ∧
        nearestNeighbor Z (Sum.inr p.2) = Sum.inl p.1 := by
  simp [neutralPairs]

/-- A finite set of pairs `(a, b)` (positive index `a`, negative index `b`) is a *partial matching*
if no positive and no negative index occurs twice. -/
def IsMatching (M : Finset (Fin N × Fin N)) : Prop :=
  Set.InjOn Prod.fst (M : Set (Fin N × Fin N)) ∧ Set.InjOn Prod.snd (M : Set (Fin N × Fin N))

/-- The neutral 2-cycles form a partial matching between positive and negative indices. -/
theorem isMatching_neutralPairs (Z : Fin N ⊕ Fin N → ℂ) : IsMatching (neutralPairs Z) := by
  constructor
  · intro p hp q hq h
    have hp' := mem_neutralPairs.1 hp
    have hq' := mem_neutralPairs.1 hq
    have h2 : p.2 = q.2 := by
      have := hp'.1.symm.trans (h ▸ hq'.1)
      exact Sum.inr_injective this
    exact Prod.ext h h2
  · intro p hp q hq h
    have hp' := mem_neutralPairs.1 hp
    have hq' := mem_neutralPairs.1 hq
    have h1 : p.1 = q.1 := by
      have := hp'.2.symm.trans (h ▸ hq'.2)
      exact Sum.inl_injective this
    exact Prod.ext h1 h

theorem card_le_of_isMatching {M : Finset (Fin N × Fin N)} (hM : IsMatching M) : M.card ≤ N := by
  calc M.card = (M.image Prod.snd).card := (Finset.card_image_of_injOn hM.2).symm
    _ ≤ Finset.univ.card := Finset.card_le_univ _
    _ = N := by simp

open scoped Classical in
/-- The (finite) set of all partial matchings between positive and negative indices. -/
noncomputable def matchings (N : ℕ) : Finset (Finset (Fin N × Fin N)) :=
  Finset.univ.filter IsMatching

theorem mem_matchings {M : Finset (Fin N × Fin N)} : M ∈ matchings N ↔ IsMatching M := by
  classical
  simp [matchings]

/-! ### The reduced energy in terms of the neutral 2-cycles -/

open scoped Classical in
theorem sum_cycle_inl (Z : Fin N ⊕ Fin N → ℂ) (h : ℂ → ℝ) :
    (∑ a : Fin N, if nearestNeighbor Z (nearestNeighbor Z (Sum.inl a)) = Sum.inl a ∧
        charge (Sum.inl a) * charge (nearestNeighbor Z (Sum.inl a)) = -1 then
      h (Z (Sum.inl a) - Z (nearestNeighbor Z (Sum.inl a))) else 0) =
    ∑ p ∈ neutralPairs Z, h (Z (Sum.inl p.1) - Z (Sum.inr p.2)) := by
  rw [neutralPairs, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases hφ : nearestNeighbor Z (Sum.inl a) with a' | b'
  · norm_num [hφ, charge_inl]
  · simp only [hφ, charge_inl, charge_inr, Sum.inr.injEq, ite_and, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    norm_num

open scoped Classical in
theorem sum_cycle_inr (Z : Fin N ⊕ Fin N → ℂ) (h : ℂ → ℝ) (heven : ∀ x, h (-x) = h x) :
    (∑ b : Fin N, if nearestNeighbor Z (nearestNeighbor Z (Sum.inr b)) = Sum.inr b ∧
        charge (Sum.inr b) * charge (nearestNeighbor Z (Sum.inr b)) = -1 then
      h (Z (Sum.inr b) - Z (nearestNeighbor Z (Sum.inr b))) else 0) =
    ∑ p ∈ neutralPairs Z, h (Z (Sum.inl p.1) - Z (Sum.inr p.2)) := by
  rw [neutralPairs, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases hφ : nearestNeighbor Z (Sum.inr b) with a' | b'
  · rw [Finset.sum_eq_single a']
    · by_cases h1 : nearestNeighbor Z (Sum.inl a') = Sum.inr b
      · simp only [hφ, h1, charge_inl, charge_inr, and_self, mul_one, ite_true]
        rw [← heven, neg_sub]
      · simp [hφ, h1]
    · intro a _ ha
      simp [hφ, Ne.symm ha]
    · simp
  · norm_num [hφ, charge_inr]

open scoped Classical in
/-- Key counting identity (source l. 247–249): the sum, over the points `i` that lie on a neutral
2-cycle, of `h (Z i - Z (φ₁ i))` for an even `h` counts every neutral 2-cycle twice. -/
theorem sum_cycle_eq_two_mul (Z : Fin N ⊕ Fin N → ℂ) (h : ℂ → ℝ) (heven : ∀ x, h (-x) = h x) :
    (∑ i, if nearestNeighbor Z (nearestNeighbor Z i) = i ∧
        charge i * charge (nearestNeighbor Z i) = -1 then
      h (Z i - Z (nearestNeighbor Z i)) else 0) =
    2 * ∑ p ∈ neutralPairs Z, h (Z (Sum.inl p.1) - Z (Sum.inr p.2)) := by
  rw [Fintype.sum_sum_type, sum_cycle_inl, sum_cycle_inr Z h heven]
  ring

/-- `F̃_λ (Z) = - ∑_{(a, b) neutral 2-cycle} g_λ (z_a - z_b)`. -/
theorem reducedEnergy_eq_neg_sum (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) :
    reducedEnergy lam Z =
      -∑ p ∈ neutralPairs Z, smearedKernel lam (Z (Sum.inl p.1) - Z (Sum.inr p.2)) := by
  unfold reducedEnergy
  rw [sum_cycle_eq_two_mul Z (smearedKernel lam) (smearedKernel_neg lam)]
  ring

/-- **Source l. 898–901.** For `Z = Sum.elim X Y` (positive charges `X`, negative charges `Y`),
`exp (-β F̃_λ (Z)) = ∏_{(a, b) neutral 2-cycle} exp (β g_λ (x_a - y_b))`. -/
theorem exp_neg_reducedEnergy_eq_prod (β lam : ℝ) (X Y : Fin N → ℂ) :
    Real.exp (-β * reducedEnergy lam (Sum.elim X Y)) =
      ∏ p ∈ neutralPairs (Sum.elim X Y), Real.exp (β * smearedKernel lam (X p.1 - Y p.2)) := by
  rw [reducedEnergy_eq_neg_sum, ← Real.exp_sum]
  simp only [Sum.elim_inl, Sum.elim_inr]
  congr 1
  rw [← Finset.mul_sum, neg_mul_neg]

/-- The reduced Boltzmann weight is the product over the neutral 2-cycles of `exp (β g_λ)`
(source l. 873, 900). -/
theorem exp_neg_reducedEnergy_eq_prod_inl_inr (β lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) :
    Real.exp (-β * reducedEnergy lam Z) =
      ∏ p ∈ neutralPairs Z,
        Real.exp (β * smearedKernel lam (Z (Sum.inl p.1) - Z (Sum.inr p.2))) := by
  have hZ : Sum.elim (fun a => Z (Sum.inl a)) (fun b => Z (Sum.inr b)) = Z := by
    funext i
    cases i <;> rfl
  have h := exp_neg_reducedEnergy_eq_prod β lam
    (fun a => Z (Sum.inl a)) (fun b => Z (Sum.inr b))
  rwa [hZ] at h

/-- The packing bound for the neutral 2-cycles : `∑ |x_a - y_b|² ≤ 18 N / π`. -/
theorem sum_sq_neutralPairs_le (Z : Fin N ⊕ Fin N → ℂ) (hZ : ∀ i, Z i ∈ box N) :
    ∑ p ∈ neutralPairs Z, ‖Z (Sum.inl p.1) - Z (Sum.inr p.2)‖ ^ 2 ≤ 18 * N / Real.pi := by
  have h := sum_cycle_eq_two_mul Z (fun x => ‖x‖ ^ 2) (fun x => by simp)
  have h2 := sum_sq_norm_sub_nearestNeighbor_le Z hZ
  have h3 : (∑ i, if nearestNeighbor Z (nearestNeighbor Z i) = i ∧
        charge i * charge (nearestNeighbor Z i) = -1 then
      ‖Z i - Z (nearestNeighbor Z i)‖ ^ 2 else 0) ≤
      ∑ i, ‖Z i - Z (nearestNeighbor Z i)‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => by
      split_ifs
      · exact le_rfl
      · positivity
  have : 36 * (N : ℝ) / Real.pi = 2 * (18 * N / Real.pi) := by ring
  linarith

/-! ### Product integrals over `Λ^N` -/

/-- The product formula for the lintegral of a product of one-variable functions with respect to
a finite product measure on `Fin n → E` (Fubini). -/
theorem lintegral_fin_nat_prod_eq_prod {E : Type*} [MeasurableSpace E] {n : ℕ}
    {μ : Fin n → Measure E} [∀ i, SigmaFinite (μ i)]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc _ = ∫⁻ x : E × (Fin n → E), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← ih (μ := fun i => μ i.succ) (fun i => f i.succ) (fun i => hf _)]
          have h0 : AEMeasurable (f 0) (μ 0) := (hf 0).aemeasurable
          have h1 : AEMeasurable (fun y : Fin n → E => ∏ i : Fin n, f (Fin.succ i) (y i))
              (Measure.pi fun i : Fin n => μ i.succ) :=
            (Finset.measurable_prod _
              fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
          exact lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun i : Fin n => μ i.succ)
            (f := f 0) (g := fun y : Fin n → E => ∏ i : Fin n, f (Fin.succ i) (y i)) h0 h1
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/-- The Lebesgue measure restricted to the box `Λ = [0, √N]²`. -/
noncomputable abbrev boxMeasure (N : ℕ) : Measure ℂ := volume.restrict (box N)

/-- Splitting the integral over `Λ^{2N}` into positive and negative charges (Fubini). -/
theorem lintegral_pi_box_sum (f : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N, f Z =
      ∫⁻ X, ∫⁻ Y, f (Sum.elim X Y) ∂(Measure.pi fun _ : Fin N => boxMeasure N)
        ∂(Measure.pi fun _ : Fin N => boxMeasure N) := by
  have h1 : (volume : Measure (Fin N ⊕ Fin N → ℂ)).restrict (Set.univ.pi fun _ => box N) =
      Measure.pi fun _ : Fin N ⊕ Fin N => boxMeasure N := by
    rw [volume_pi]
    exact Measure.restrict_pi_pi (fun _ => (volume : Measure ℂ)) (fun _ => box N)
  rw [h1]
  have h2 := (measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : Fin N ⊕ Fin N => ℂ) (fun _ => boxMeasure N))
  rw [← h2.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  rw [lintegral_prod]
  · rfl
  · exact (hf.comp (MeasurableEquiv.measurable _)).aemeasurable

theorem prod_ite_mem_image {M : Finset (Fin N × Fin N)} (hM : IsMatching M) {m n : ℝ≥0∞} :
    ∏ b : Fin N, (if b ∈ M.image Prod.snd then m else n) = m ^ M.card * n ^ (N - M.card) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  · rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_image_of_injOn hM.2]
  · rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
      Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_image_of_injOn hM.2]
    simp

/-- The integral over the negative charges `Y ∈ Λ^N` of a matching product, for fixed positive
charges `X = c`: each matched negative charge contributes at most `∫ G`, each unmatched one `N`. -/
theorem lintegral_boxMeasure_matching_y {M : Finset (Fin N × Fin N)} (hM : IsMatching M)
    {G : ℂ → ℝ≥0∞} (hG : Measurable G) (c : Fin N → ℂ) :
    ∫⁻ Y, ∏ p ∈ M, G (c p.1 - Y p.2) ∂(Measure.pi fun _ : Fin N => boxMeasure N) ≤
      (N : ℝ≥0∞) ^ (N - M.card) * (∫⁻ u, G u) ^ M.card := by
  set m := ∫⁻ u, G u with hm
  let f : Fin N → ℂ → ℝ≥0∞ := fun b w => ∏ p ∈ M.filter (fun p => p.2 = b), G (c p.1 - w)
  have hf : ∀ b, Measurable (f b) := fun b =>
    Finset.measurable_prod _ fun _ _ => hG.comp (measurable_const.sub measurable_id)
  have h1 : ∀ Y : Fin N → ℂ, ∏ p ∈ M, G (c p.1 - Y p.2) = ∏ b, f b (Y b) := by
    intro Y
    rw [← Finset.prod_fiberwise_of_maps_to (s := M) (t := Finset.univ) (g := Prod.snd)
      (fun p _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun b _ => Finset.prod_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.1 hp).2]
  simp_rw [h1]
  rw [lintegral_fin_nat_prod_eq_prod f hf]
  calc ∏ b, ∫⁻ w, f b w ∂(boxMeasure N)
      ≤ ∏ b : Fin N, (if b ∈ M.image Prod.snd then m else (N : ℝ≥0∞)) := by
        refine Finset.prod_le_prod fun b _ => ?_
        by_cases hb : b ∈ M.image Prod.snd
        · simp only [hb, ite_true]
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
          have hfib : M.filter (fun q => q.2 = p.2) = {p} := by
            ext q
            simp only [Finset.mem_filter, Finset.mem_singleton]
            refine ⟨fun ⟨hq, h⟩ => hM.2 hq hp h, ?_⟩
            rintro rfl
            exact ⟨hp, rfl⟩
          have : ∀ w, f p.2 w = G (c p.1 - w) := fun w => by
            simp only [f, hfib, Finset.prod_singleton]
          simp_rw [this]
          calc ∫⁻ w, G (c p.1 - w) ∂(boxMeasure N) ≤ ∫⁻ w, G (c p.1 - w) :=
                lintegral_mono' Measure.restrict_le_self le_rfl
            _ = m := lintegral_sub_left_eq_self G (c p.1)
        · simp only [hb, ite_false]
          have hfib : ∀ q, ¬ (q ∈ M ∧ q.2 = b) := fun q ⟨hq, h⟩ =>
            hb (Finset.mem_image.2 ⟨q, hq, h⟩)
          have : ∀ w, f b w = 1 := fun w => by
            simp only [f]
            rw [Finset.filter_false_of_mem (fun q hq h => hfib q ⟨hq, h⟩), Finset.prod_empty]
          simp_rw [this]
          rw [lintegral_one, Measure.restrict_apply_univ, volume_box]
    _ = _ := by
        rw [prod_ite_mem_image hM, mul_comm]

theorem measurable_prod_matching (M : Finset (Fin N × Fin N)) {G : ℂ → ℝ≥0∞}
    (hG : Measurable G) :
    Measurable fun Z : Fin N ⊕ Fin N → ℂ => ∏ p ∈ M, G (Z (Sum.inl p.1) - Z (Sum.inr p.2)) :=
  Finset.measurable_prod _ fun _ _ =>
    hG.comp ((measurable_pi_apply _).sub (measurable_pi_apply _))

/-- **Integral of a matching product** : for a partial matching `M` of size `p`,
`∫_{Λ^{2N}} ∏_{(a, b) ∈ M} G (x_a - y_b) ≤ N ^ (2 N - p) (∫ G) ^ p`. Each matched pair contributes
`∫_Λ ∫_Λ G (x - y) dy dx ≤ N ∫ G` and each unmatched point contributes `N`. -/
theorem lintegral_prod_matching_le {M : Finset (Fin N × Fin N)} (hM : IsMatching M)
    {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ Z in Set.univ.pi fun _ : Fin N ⊕ Fin N => box N,
        ∏ p ∈ M, G (Z (Sum.inl p.1) - Z (Sum.inr p.2)) ≤
      (N : ℝ≥0∞) ^ (2 * N - M.card) * (∫⁻ u, G u) ^ M.card := by
  rw [lintegral_pi_box_sum _ (measurable_prod_matching M hG)]
  simp only [Sum.elim_inl, Sum.elim_inr]
  calc ∫⁻ X, ∫⁻ Y, ∏ p ∈ M, G (X p.1 - Y p.2) ∂(Measure.pi fun _ : Fin N => boxMeasure N)
        ∂(Measure.pi fun _ : Fin N => boxMeasure N)
      ≤ ∫⁻ _X, (N : ℝ≥0∞) ^ (N - M.card) * (∫⁻ u, G u) ^ M.card
          ∂(Measure.pi fun _ : Fin N => boxMeasure N) :=
        lintegral_mono fun X => lintegral_boxMeasure_matching_y hM hG X
    _ = (N : ℝ≥0∞) ^ (2 * N - M.card) * (∫⁻ u, G u) ^ M.card := by
        rw [lintegral_const, Measure.pi_univ]
        simp only [Measure.restrict_apply_univ, volume_box, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        have hp := card_le_of_isMatching hM
        have : 2 * N - M.card = (N - M.card) + N := by omega
        rw [this, pow_add]
        ring

/-! ### Counting the partial matchings -/

/-- There are exactly `C(N, p) · N! / (N - p)!` partial matchings of size `p` :
choose the `p` positive indices, then an injective assignment of negative partners. -/
theorem card_matchings_filter_card_eq (N p : ℕ) :
    (((matchings N).filter fun M => M.card = p).card) = N.choose p * N.descFactorial p := by
  classical
  let ι := Σ S : Finset.powersetCard p (Finset.univ : Finset (Fin N)),
    ((S : Finset (Fin N)) ↪ Fin N)
  let Φ : ι → Finset (Fin N × Fin N) := fun s =>
    (Finset.univ : Finset (s.1 : Finset (Fin N))).image fun a => (a.1, s.2 a)
  have hsub : (matchings N).filter (fun M => M.card = p) ⊆ (Finset.univ : Finset ι).image Φ := by
    intro M hM
    rw [Finset.mem_filter, mem_matchings] at hM
    obtain ⟨⟨hfst, hsnd⟩, hcard⟩ := hM
    have hS : M.image Prod.fst ∈ Finset.powersetCard p (Finset.univ : Finset (Fin N)) := by
      rw [Finset.mem_powersetCard, Finset.card_image_of_injOn hfst]
      exact ⟨Finset.subset_univ _, hcard⟩
    have h : ∀ a : (M.image Prod.fst), ∃ b, (a.1, b) ∈ M := fun a => by
      obtain ⟨q, hq, hqa⟩ := Finset.mem_image.1 a.2
      exact ⟨q.2, by rw [← hqa]; exact hq⟩
    choose f hf using h
    let e : (M.image Prod.fst) ↪ Fin N :=
      ⟨f, fun a a' haa' => by
        have := hsnd (hf a) (hf a') haa'
        exact Subtype.ext (congrArg Prod.fst this)⟩
    refine Finset.mem_image.2 ⟨⟨⟨M.image Prod.fst, hS⟩, e⟩, Finset.mem_univ _, ?_⟩
    ext ⟨a, b⟩
    simp only [Φ, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨x, rfl, rfl⟩
      exact hf x
    · intro hab
      refine ⟨⟨a, Finset.mem_image.2 ⟨(a, b), hab, rfl⟩⟩, rfl, ?_⟩
      have := hfst (hf ⟨a, Finset.mem_image.2 ⟨(a, b), hab, rfl⟩⟩) hab rfl
      exact congrArg Prod.snd this
  have hfst : ∀ s : ι, (Φ s).image Prod.fst = s.1.val := by
    intro s
    ext a
    simp only [Φ, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, ⟨x, rfl⟩, rfl⟩
      exact x.2
    · intro ha
      exact ⟨(a, s.2 ⟨a, ha⟩), ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨S, e⟩ ⟨T, f⟩ heq
    have hST : S = T := Subtype.ext
      ((hfst ⟨S, e⟩).symm.trans ((congrArg (Finset.image Prod.fst) heq).trans (hfst ⟨T, f⟩)))
    subst T
    congr 1
    apply Function.Embedding.ext
    intro a
    have hmem : (a.1, e a) ∈ Φ ⟨S, e⟩ :=
      Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩
    rw [heq] at hmem
    obtain ⟨b, _, hb⟩ := Finset.mem_image.1 hmem
    have hba : b = a := Subtype.ext (congrArg Prod.fst hb)
    subst b
    exact (congrArg Prod.snd hb).symm
  have hrev : (Finset.univ : Finset ι).image Φ ⊆
      (matchings N).filter (fun M => M.card = p) := by
    intro M hM
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hM
    rw [Finset.mem_filter, mem_matchings]
    constructor
    · constructor
      · intro q hq r hr hqr
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hq
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hr
        have hab : a = b := Subtype.ext hqr
        rw [hab]
      · intro q hq r hr hqr
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hq
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hr
        have hab := s.2.injective hqr
        rw [hab]
    · rw [Finset.card_image_of_injective _ (fun a b h => Subtype.ext (congrArg Prod.fst h)),
        Finset.card_univ, Fintype.card_coe]
      exact (Finset.mem_powersetCard.1 s.1.2).2
  calc _ = ((Finset.univ : Finset ι).image Φ).card := congrArg Finset.card (Finset.Subset.antisymm hsub hrev)
    _ = (Finset.univ : Finset ι).card := Finset.card_image_of_injective _ hinj
    _ = N.choose p * N.descFactorial p := by
        rw [Finset.card_univ, Fintype.card_sigma]
        have hS : ∀ S : Finset.powersetCard p (Finset.univ : Finset (Fin N)),
            Fintype.card ((S : Finset (Fin N)) ↪ Fin N) = N.descFactorial p := fun S => by
          rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe,
            (Finset.mem_powersetCard.1 S.2).2]
        simp only [hS, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          Finset.card_powersetCard, Fintype.card_fin, smul_eq_mul]

/-- The matching count in the upper-bound form used by the integral estimates. -/
theorem card_matchings_filter_card_le (N p : ℕ) :
    (((matchings N).filter fun M => M.card = p).card) ≤ N.choose p * N.descFactorial p :=
  (card_matchings_filter_card_eq N p).le

/-- The manuscript's exact count `binom(N,p)^2 p!` of partial matchings. -/
theorem card_matchings_filter_card_eq_choose (N p : ℕ) :
    (((matchings N).filter fun M => M.card = p).card) = (N.choose p) ^ 2 * p.factorial := by
  rw [card_matchings_filter_card_eq, Nat.descFactorial_eq_factorial_mul_choose]
  ring

/-- `C(N, p) · N! / (N - p)! = (N !)² / (p ! ((N - p) !)²)` . -/
theorem choose_mul_descFactorial_eq {N p : ℕ} (hp : p ≤ N) :
    ((N.choose p * N.descFactorial p : ℕ) : ℝ) = (N ! : ℝ) ^ 2 / (p ! * ((N - p) ! : ℝ) ^ 2) := by
  have h1 : (N.choose p * p ! * (N - p)! : ℕ) = N ! := Nat.choose_mul_factorial_mul_factorial hp
  have h2 : ((N - p)! * N.descFactorial p : ℕ) = N ! := Nat.factorial_mul_descFactorial hp
  have hp0 : (0 : ℝ) < p ! := by exact_mod_cast Nat.factorial_pos p
  have hq0 : (0 : ℝ) < (N - p)! := by exact_mod_cast Nat.factorial_pos _
  have e1 : (N ! : ℝ) = N.choose p * p ! * (N - p)! := by exact_mod_cast h1.symm
  have e2 : (N ! : ℝ) = (N - p)! * N.descFactorial p := by exact_mod_cast h2.symm
  rw [eq_div_iff (by positivity)]
  push_cast
  calc (N.choose p : ℝ) * N.descFactorial p * (p ! * ((N - p)! : ℝ) ^ 2)
      = (N.choose p * p ! * (N - p)!) * ((N - p)! * N.descFactorial p) := by ring
    _ = (N ! : ℝ) ^ 2 := by rw [← e1, ← e2]; ring

/-! ### Reduction of the partition function to the matching sum -/

/-- **Source l. 900–909 (reduction).** If the reduced Boltzmann weight is dominated, on `Λ^{2N}`,
by `K₀ ∏_{(a, b) neutral 2-cycle} G (z_a - z_b)` for a measurable weight `G`, then
`𝒦_{N, β}^λ ≤ K₀ ∑_{p ≤ N} C(N, p) (N!/(N - p)!) N^(2 N - p) (∫ G)^p`. -/
theorem reducedPartitionFunction_le_sum_matchings {β lam : ℝ} {G : ℂ → ℝ≥0∞}
    (hG : Measurable G) {K₀ : ℝ≥0∞}
    (h : ∀ Z ∈ Set.univ.pi (fun _ : Fin N ⊕ Fin N => box N),
      ENNReal.ofReal (Real.exp (-β * reducedEnergy lam Z)) ≤
        K₀ * ∏ p ∈ neutralPairs Z, G (Z (Sum.inl p.1) - Z (Sum.inr p.2))) :
    reducedPartitionFunction N β lam ≤
      K₀ * ∑ p ∈ Finset.range (N + 1),
        ((N.choose p * N.descFactorial p : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞) ^ (2 * N - p) *
          (∫⁻ u, G u) ^ p := by
  unfold reducedPartitionFunction
  have hdom : ∀ Z ∈ Set.univ.pi (fun _ : Fin N ⊕ Fin N => box N),
      ENNReal.ofReal (Real.exp (-β * reducedEnergy lam Z)) ≤
        K₀ * ∑ M ∈ matchings N, ∏ p ∈ M, G (Z (Sum.inl p.1) - Z (Sum.inr p.2)) := by
    intro Z hZ
    have hle : ∏ p ∈ neutralPairs Z, G (Z (Sum.inl p.1) - Z (Sum.inr p.2)) ≤
        ∑ M ∈ matchings N, ∏ p ∈ M, G (Z (Sum.inl p.1) - Z (Sum.inr p.2)) :=
      Finset.single_le_sum
        (f := fun M : Finset (Fin N × Fin N) => ∏ p ∈ M, G (Z (Sum.inl p.1) - Z (Sum.inr p.2)))
        (fun _ _ => zero_le) (mem_matchings.2 (isMatching_neutralPairs Z))
    exact (h Z hZ).trans (mul_le_mul_right hle K₀)
  calc ∫⁻ Z in Set.univ.pi (fun _ : Fin N ⊕ Fin N => box N),
        ENNReal.ofReal (Real.exp (-β * reducedEnergy lam Z))
      ≤ ∫⁻ Z in Set.univ.pi (fun _ : Fin N ⊕ Fin N => box N),
          K₀ * ∑ M ∈ matchings N, ∏ p ∈ M, G (Z (Sum.inl p.1) - Z (Sum.inr p.2)) :=
        setLIntegral_mono' (measurableSet_pi_box N) hdom
    _ = K₀ * ∑ M ∈ matchings N, ∫⁻ Z in Set.univ.pi (fun _ : Fin N ⊕ Fin N => box N),
          ∏ p ∈ M, G (Z (Sum.inl p.1) - Z (Sum.inr p.2)) := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun M _ => measurable_prod_matching M hG),
          lintegral_finsetSum _ fun M _ => measurable_prod_matching M hG]
    _ ≤ K₀ * ∑ M ∈ matchings N, (N : ℝ≥0∞) ^ (2 * N - M.card) * (∫⁻ u, G u) ^ M.card :=
        mul_le_mul_right (Finset.sum_le_sum fun M hM =>
          lintegral_prod_matching_le (mem_matchings.1 hM) hG) _
    _ = K₀ * ∑ p ∈ Finset.range (N + 1), ∑ M ∈ (matchings N).filter (fun M => M.card = p),
          (N : ℝ≥0∞) ^ (2 * N - M.card) * (∫⁻ u, G u) ^ M.card := by
        rw [Finset.sum_fiberwise_of_maps_to (s := matchings N) (t := Finset.range (N + 1))
          (g := Finset.card) (fun M hM => Finset.mem_range.2 (Nat.lt_succ_of_le
            (card_le_of_isMatching (mem_matchings.1 hM))))]
    _ ≤ _ := by
        refine mul_le_mul_right (Finset.sum_le_sum fun p _ => ?_) _
        have : ∑ M ∈ (matchings N).filter (fun M => M.card = p),
            (N : ℝ≥0∞) ^ (2 * N - M.card) * (∫⁻ u, G u) ^ M.card =
            (((matchings N).filter (fun M => M.card = p)).card : ℝ≥0∞) *
              ((N : ℝ≥0∞) ^ (2 * N - p) * (∫⁻ u, G u) ^ p) := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          refine Finset.sum_congr rfl fun M hM => ?_
          rw [(Finset.mem_filter.1 hM).2]
        rw [this, ← mul_assoc]
        gcongr
        exact_mod_cast card_matchings_filter_card_le N p

/-! ### The real-valued bound -/

/-- The matching sum in `[0, ∞]`, for a weight of mass `A`, is the `ofReal` of the real sum of
`sum_matchings_le`. -/
theorem sum_coeff_eq_ofReal (N : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∑ p ∈ Finset.range (N + 1),
        ((N.choose p * N.descFactorial p : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞) ^ (2 * N - p) *
          ENNReal.ofReal A ^ p =
      ENNReal.ofReal (∑ p ∈ Finset.range (N + 1),
        ((N ! : ℝ) ^ 2 / (p ! * ((N - p) ! : ℝ) ^ 2)) * (N : ℝ) ^ (2 * N - p) * A ^ p) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpN : p ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
  rw [← choose_mul_descFactorial_eq hpN, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hA, ENNReal.ofReal_pow (Nat.cast_nonneg N),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

/-- **Source l. 907–917.** If the reduced Boltzmann weight is dominated on `Λ^{2N}` by
`K ∏_{neutral 2-cycles} G (z_a - z_b)` with `∫ G = A > 0` finite, then
`𝒦_{N, β}^λ ≤ K · N! N^N A^N e^{2 N / √A}`. -/
theorem reducedPartitionFunction_le_ofReal {β lam : ℝ} {G : ℂ → ℝ≥0∞} (hG : Measurable G)
    {K A : ℝ} (hK : 0 ≤ K) (hA : 0 < A) (hGA : ∫⁻ u, G u = ENNReal.ofReal A)
    (h : ∀ Z ∈ Set.univ.pi (fun _ : Fin N ⊕ Fin N => box N),
      ENNReal.ofReal (Real.exp (-β * reducedEnergy lam Z)) ≤
        ENNReal.ofReal K * ∏ p ∈ neutralPairs Z, G (Z (Sum.inl p.1) - Z (Sum.inr p.2))) :
    reducedPartitionFunction N β lam ≤
      ENNReal.ofReal (K * (N ! * (N : ℝ) ^ N * A ^ N * Real.exp (2 * N / Real.sqrt A))) := by
  refine (reducedPartitionFunction_le_sum_matchings hG h).trans ?_
  rw [hGA, sum_coeff_eq_ofReal N hA.le, ← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (sum_matchings_le N hA) hK)

/-- **Lemma 3.5, upper bound for `β > 2`** (source l. 926–931):
`𝒦_{N, β}^λ ≤ N! N^N A^N e^{2 N / √A}` with `A = 𝒵_β λ^{2 - β} = ∫ e^{β g_λ}`. -/
theorem reducedPartitionFunction_le_of_gt_two {β lam : ℝ} (hβ : 2 < β) (hlam : 0 < lam) :
    reducedPartitionFunction N β lam ≤
      ENNReal.ofReal (N ! * (N : ℝ) ^ N * (dipoleConstant β hβ.le * lam ^ (2 - β)) ^ N *
        Real.exp (2 * N / Real.sqrt (dipoleConstant β hβ.le * lam ^ (2 - β)))) := by
  have hA : 0 < dipoleConstant β hβ.le * lam ^ (2 - β) :=
    mul_pos (dipoleConstant_pos β hβ.le) (Real.rpow_pos_of_pos hlam _)
  have hmeas : Measurable fun u : ℂ => ENNReal.ofReal (Real.exp (β * smearedKernel lam u)) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_smearedKernel lam).const_mul β))
  have hint : ∫⁻ u, ENNReal.ofReal (Real.exp (β * smearedKernel lam u)) =
      ENNReal.ofReal (dipoleConstant β hβ.le * lam ^ (2 - β)) := by
    rw [← integral_exp_smearedKernel hβ hlam, ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_smearedKernel hβ hlam) (Filter.Eventually.of_forall fun u =>
        (Real.exp_pos _).le)]
  have := reducedPartitionFunction_le_ofReal (N := N) (β := β) (lam := lam) hmeas
    (K := 1) zero_le_one hA hint (fun Z _ => by
      rw [ENNReal.ofReal_one, one_mul, exp_neg_reducedEnergy_eq_prod_inl_inr,
        ENNReal.ofReal_prod_of_nonneg fun p _ => (Real.exp_pos _).le])
  simpa only [one_mul] using this

/-- For `ℓ > 0` and `2λ ≤ √ℓ`, the Gaussian mass integrand `e^{2 g_λ(u) - |u|²/ℓ}` is integrable
and its integral is positive. -/
theorem integrable_gaussianMass_of_le_sqrt {lam ℓ : ℝ} (hlam : 0 < lam) (hℓ : 0 < ℓ)
    (h2 : 2 * lam ≤ Real.sqrt ℓ) :
    Integrable (fun u : ℂ => Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ)) := by
  have hf : (fun u : ℂ => Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ)) =
      fun u : ℂ => gaussianProfile lam ℓ ‖u‖ := funext (gaussianProfile_eq_comp_norm lam ℓ)
  rw [hf]
  exact (integrable_comp_norm_complex_iff _).2 (integrableOn_mul_gaussianProfile hlam hℓ h2)

theorem integral_gaussianMass_pos {lam ℓ : ℝ} (hlam : 0 < lam) (hℓ : 0 < ℓ)
    (h2 : 2 * lam ≤ Real.sqrt ℓ) :
    0 < ∫ u : ℂ, Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ) := by
  rw [integral_pos_iff_support_of_nonneg (fun u => (Real.exp_pos _).le)
    (integrable_gaussianMass_of_le_sqrt hlam hℓ h2)]
  have : Function.support (fun u : ℂ => Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ)) =
      Set.univ := by
    ext u
    simp [Function.mem_support]
  rw [this]
  simp

/-- **Source (Gaussian insertion).** For `Z ∈ Λ^{2N}` and `ℓ > 0`, the packing bound
gives `exp (-2 F̃_λ (Z)) ≤ e^{18 N / (π ℓ)} ∏_{neutral 2-cycles} exp (2 g_λ (u) - |u|² / ℓ)`. -/
theorem ofReal_exp_neg_two_mul_reducedEnergy_le {lam ℓ : ℝ} (hℓ : 0 < ℓ)
    (Z : Fin N ⊕ Fin N → ℂ) (hZ : ∀ i, Z i ∈ box N) :
    ENNReal.ofReal (Real.exp (-2 * reducedEnergy lam Z)) ≤
      ENNReal.ofReal (Real.exp (18 * N / (Real.pi * ℓ))) *
        ∏ p ∈ neutralPairs Z, ENNReal.ofReal
          (Real.exp (2 * smearedKernel lam (Z (Sum.inl p.1) - Z (Sum.inr p.2)) -
            ‖Z (Sum.inl p.1) - Z (Sum.inr p.2)‖ ^ 2 / ℓ)) := by
  have hsq := sum_sq_neutralPairs_le Z hZ
  rw [exp_neg_reducedEnergy_eq_prod_inl_inr,
    ← ENNReal.ofReal_prod_of_nonneg fun p _ => (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hdiv : ∑ p ∈ neutralPairs Z, ‖Z (Sum.inl p.1) - Z (Sum.inr p.2)‖ ^ 2 / ℓ ≤
      18 * N / (Real.pi * ℓ) := by
    rw [← Finset.sum_div, show 18 * (N : ℝ) / (Real.pi * ℓ) = 18 * N / Real.pi / ℓ by
      rw [div_div]]
    exact div_le_div_of_nonneg_right hsq hℓ.le
  rw [Finset.sum_sub_distrib]
  linarith

/-- **Lemma 3.5, upper bound for `β = 2`** (source l. 899–917): for `ℓ > 0` with `2 λ ≤ √ℓ`,
`𝒦_{N, 2}^λ ≤ e^{18 N / (π ℓ)} N! N^N B^N e^{2 N / √B}`, where
`B = ∫ e^{2 g_λ(u) - |u|²/ℓ} du` is the Gaussian mass (`J_λ(1/ℓ)` of the source). -/
theorem reducedPartitionFunction_two_le {lam ℓ : ℝ} (hlam : 0 < lam) (hℓ : 0 < ℓ)
    (h2 : 2 * lam ≤ Real.sqrt ℓ) :
    reducedPartitionFunction N 2 lam ≤
      ENNReal.ofReal (Real.exp (18 * N / (Real.pi * ℓ)) *
        (N ! * (N : ℝ) ^ N *
          (∫ u : ℂ, Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ)) ^ N *
          Real.exp (2 * N /
            Real.sqrt (∫ u : ℂ, Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ))))) := by
  have hB := integral_gaussianMass_pos hlam hℓ h2
  have hmeas : Measurable fun u : ℂ =>
      ENNReal.ofReal (Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_smearedKernel lam).const_mul 2).sub
        ((continuous_norm.measurable.pow_const 2).div_const ℓ)))
  have hint : ∫⁻ u, ENNReal.ofReal (Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ)) =
      ENNReal.ofReal (∫ u : ℂ, Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / ℓ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_gaussianMass_of_le_sqrt hlam hℓ h2)
      (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)]
  exact reducedPartitionFunction_le_ofReal (N := N) (β := 2) (lam := lam) hmeas
    (Real.exp_pos _).le hB hint fun Z hZ =>
      ofReal_exp_neg_two_mul_reducedEnergy_le hℓ Z (Set.mem_univ_pi.1 hZ)

/-- **Lemma 3.5, upper bound for `β = 2`, with the source's choice `ℓ = |log λ|`**
(source l. 899–917), for `0 < λ ≤ e⁻¹`. -/
theorem reducedPartitionFunction_two_le_abs_log {lam : ℝ} (hlam : 0 < lam)
    (hle : lam ≤ Real.exp (-1)) :
    reducedPartitionFunction N 2 lam ≤
      ENNReal.ofReal (Real.exp (18 * N / (Real.pi * |Real.log lam|)) *
        (N ! * (N : ℝ) ^ N *
          (∫ u : ℂ, Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|)) ^ N *
          Real.exp (2 * N / Real.sqrt
            (∫ u : ℂ, Real.exp (2 * smearedKernel lam u - ‖u‖ ^ 2 / |Real.log lam|))))) := by
  obtain ⟨h1, h2⟩ := two_mul_le_sqrt_neg_log hlam hle
  have hab : |Real.log lam| = -Real.log lam := abs_of_neg (by linarith)
  exact reducedPartitionFunction_two_le hlam (by rw [hab]; linarith) (by rw [hab]; exact h2)

end TwoComponentCoulomb

end
