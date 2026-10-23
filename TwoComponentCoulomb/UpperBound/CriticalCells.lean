/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.NumComponents
public import TwoComponentCoulomb.NearestNeighbor.TwiceIsolated
public import TwoComponentCoulomb.PhaseSpace.GunsonPanta
public import TwoComponentCoulomb.UpperBound.CriticalEnergy
import TwoComponentCoulomb.Gibbs.Generic
import TwoComponentCoulomb.NearestNeighbor.Isolated
import TwoComponentCoulomb.PhaseSpace.Packing
public import TwoComponentCoulomb.UpperBound.CriticalMass
import TwoComponentCoulomb.UpperBound.CriticalGaussian
import TwoComponentCoulomb.UpperBound.ReducedMatching

/-!
# The cell integral of the critical case `β = 2` (Proposition 3.10, eq. (eq:critical upper))

Source `source/dipole-formation.tex`, l. 1605–1620 (proof of Proposition 3.10, `β = 2`), also used for
the electric moment of Theorem 2 at `β = 2` (l. 1910–1912).

Fix a nearest-neighbour graph `f` with `K` components, `m` isolated pairs and `p₀` isolated
neutral pairs. On the cell `{φ₁ = f}` the source integrates the displacement `u_j` of each
isolated pair first, conditional on the retained coordinates (one endpoint `w_j` of each isolated
pair and all vertices of the other components); the pair radius `ρ_j` depends only on the
retained coordinates and confines `u_j` to the disc `|u_j| ≤ 4ρ_j`. Then the retained endpoints
`w_j` contribute `N` each and the other components are integrated in Gunson--Panta variables.

This only uses a pointwise bound of the integrand by a product of pair weights, so it is stated
here for a general integrand. The instances are the Gibbs integrand of (eq:critical upper)
(`UpperBound/CriticalUpper.lean`) and the electric moment of (eq:critical electric)
(`Fluctuations/CriticalElectric.lean`).

## Main results

* `TwoComponentCoulomb.lintegral_pi_complex_prod_eq_prod`: Fubini for a product of one-variable
  functions over `σ → ℂ`, `σ` a finite type.
* `TwoComponentCoulomb.lintegral_pair_prod_le` ( "conditional on the retained
  coordinates"): integrating the displacements of the pairs, each pair contributes at most the
  supremum over `ρ` of its radial integral.
* `TwoComponentCoulomb.lintegral_prod_indicator_box_mul`: the retained endpoints `w_j ∈ Λ`
  contribute `N` each.
* `TwoComponentCoulomb.card_filter_eq_two_mul_card_filter_lt`: a set of 2-cycle vertices closed
  under the map has twice as many elements as it has 2-cycles.
* `TwoComponentCoulomb.IsoNon`, `TwoComponentCoulomb.nnMap_isoNon`,
  `TwoComponentCoulomb.two_mul_card_gpRefSet_isoNonMap`: the sub-configuration of the components
  that are not isolated pairs, whose nearest-neighbour map is the restriction of `f` and which has
  `K - m` 2-cycles.
* `TwoComponentCoulomb.lintegral_cell_le_of_pointwise` (source l. 1618–1620): integrating the pair
  displacements conditional on the retained coordinates, and then the retained endpoints.
* `TwoComponentCoulomb.ofReal_exp_le_cell_of_exponent` (source l. 1605–1610): from an exponent
  bound `Φ ≤ ∑_{i ∉ I^pair} (g_λ + c₁) + ∑_s P_s` and pair weights dominating `e^{P_s - |u_s|²/ℓ}`,
  the integrand on the cell is at most
  `e^{c₁ |(I^pair)^c| + 36N/(πℓ)} e^{∑_{i ∉ I^pair} g_λ(z_i - z_{f i})} ∏_s W_s(u_s, ρ_s)` (the
  Gaussian factor is inserted by the packing bound).
* `TwoComponentCoulomb.exists_commonCutoffFactor`: the common Gaussian cutoff in the
  nonisolated components gives `N^h J_λ(1/ℓ)^h exp(d log(N/d) + Cd + 36N/(πℓ))`.
* `TwoComponentCoulomb.criticalCellExponent`,
  `TwoComponentCoulomb.exists_lintegral_cell_le_criticalCellExponent`: the full cell
  estimate with pair masses `Mₙ`, `Mₛ` and the same cycle mass `J_λ(1/ℓ)`.

The isolated and nonisolated Gaussian insertions are made in their respective
integrals. Their two packing costs sum to `72N/(πℓ)`, an explicit choice of the
paper's `CN/ℓ`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### Fubini over finite products -/

/-- **Fubini** for a product of one-variable functions over `σ → ℂ`, `σ` a finite type. -/
theorem lintegral_pi_complex_prod_eq_prod {σ : Type*} [Fintype σ] (φ : σ → ℂ → ℝ≥0∞)
    (hφ : ∀ s, Measurable (φ s)) :
    ∫⁻ x : σ → ℂ, ∏ s, φ s (x s) = ∏ s, ∫⁻ u, φ s u := by
  let e := (Fintype.equivFin σ).symm
  rw [← (volume_measurePreserving_piCongrLeft (fun _ : σ => ℂ) e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (μ := fun _ => volume) (fun i => φ (e i))
    (fun i => hφ (e i))

/-- **Integration of the pair displacements** . Let `σ` index the pairs and `α`
the retained points, `π s` the retained endpoint of the pair `s` and `ρ s y` its radius, a
function of the retained configuration `y`. If, uniformly in `y`, the radial weight `Φ s` of the
pair `s` has integral at most `M s` in the displacement, then integrating the non-retained
endpoints gives the factor `∏ M s`. -/
theorem lintegral_pair_prod_le {σ α : Type*} [Fintype σ] [Fintype α] (π : σ → α)
    (F : (α → ℂ) → ℝ≥0∞) (hF : Measurable F)
    (Φ : σ → ℂ × ℝ → ℝ≥0∞) (hΦ : ∀ s, Measurable (Φ s))
    (ρ : σ → (α → ℂ) → ℝ) (hρ : ∀ s, Measurable (ρ s))
    (M : σ → ℝ≥0∞) (hM : ∀ s y, ∫⁻ u, Φ s (u, ρ s y) ≤ M s) :
    ∫⁻ x : (σ → ℂ) × (α → ℂ), F x.2 * ∏ s, Φ s (x.1 s - x.2 (π s), ρ s x.2) ≤
      (∏ s, M s) * ∫⁻ y, F y := by
  have hm : Measurable fun x : (σ → ℂ) × (α → ℂ) =>
      F x.2 * ∏ s, Φ s (x.1 s - x.2 (π s), ρ s x.2) := by
    refine (hF.comp measurable_snd).mul (Finset.measurable_prod _ fun s _ => ?_)
    refine (hΦ s).comp (Measurable.prodMk ?_ ((hρ s).comp measurable_snd))
    exact ((measurable_pi_apply s).comp measurable_fst).sub
      ((measurable_pi_apply (π s)).comp measurable_snd)
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ hm.aemeasurable]
  calc ∫⁻ y : α → ℂ, ∫⁻ x : σ → ℂ, F y * ∏ s, Φ s (x s - y (π s), ρ s y)
      = ∫⁻ y : α → ℂ, F y * ∏ s, ∫⁻ u, Φ s (u - y (π s), ρ s y) := by
        refine lintegral_congr fun y => ?_
        have hmeas : Measurable fun x : σ → ℂ => ∏ s, Φ s (x s - y (π s), ρ s y) :=
          Finset.measurable_prod _ fun s _ =>
            (hΦ s).comp (Measurable.prodMk ((measurable_pi_apply s).sub_const _) measurable_const)
        rw [lintegral_const_mul _ hmeas]
        congr 1
        exact lintegral_pi_complex_prod_eq_prod (fun s u => Φ s (u - y (π s), ρ s y))
          (fun s => (hΦ s).comp (Measurable.prodMk (measurable_id.sub_const _) measurable_const))
    _ ≤ ∫⁻ y, F y * ∏ s, M s := by
        refine lintegral_mono fun y => ?_
        gcongr with s
        rw [lintegral_sub_right_eq_self (fun u => Φ s (u, ρ s y)) (y (π s))]
        exact hM s y
    _ = (∏ s, M s) * ∫⁻ y, F y := by
        rw [lintegral_mul_const _ hF, mul_comm]

/-- **The retained endpoints** ( "Their reference points and the `m` retained
endpoints contribute `N^K`"): for a predicate `p` on a finite type `α`, the coordinates `y_j ∈ Λ`
(`p j`) integrate to `N` each. -/
theorem lintegral_prod_indicator_box_mul {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (N : ℕ) (H : ({j // ¬ p j} → ℂ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ y : α → ℂ, (∏ j : {j // p j}, (box N).indicator 1 (y j)) * H (fun j => y j) =
      (N : ℝ≥0∞) ^ Fintype.card {j // p j} * ∫⁻ w, H w := by
  have hmp := volume_preserving_piEquivPiSubtypeProd (fun _ : α => ℂ) p
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : α => ℂ) p with he
  have h := hmp.lintegral_comp_emb e.measurableEmbedding
    (fun x => (∏ j : {j // p j}, (box N).indicator 1 (x.1 j)) * H x.2)
  refine h.trans ?_
  have hind : ∀ j : {j // p j}, Measurable fun u : ℂ => (box N).indicator (1 : ℂ → ℝ≥0∞) u :=
    fun _ => measurable_one.indicator (measurableSet_box N)
  rw [Measure.volume_eq_prod, lintegral_prod_mul (μ := volume) (ν := volume)
    (f := fun x : {j // p j} → ℂ => ∏ j, (box N).indicator 1 (x j)) (g := H)
    (Finset.measurable_prod _ fun j _ => (hind j).comp (measurable_pi_apply j)).aemeasurable
    hH.aemeasurable, lintegral_pi_complex_prod_eq_prod (fun j u => (box N).indicator 1 u) hind]
  congr 1
  rw [Finset.prod_congr rfl fun j _ => lintegral_indicator_one (measurableSet_box N),
    volume_box, Finset.prod_const, Finset.card_univ]

/-! ### Counting 2-cycles -/

/-- A set of 2-cycle vertices closed under `g` has twice as many elements as it has 2-cycles
(each 2-cycle is counted at its endpoint with the smaller key). -/
theorem card_filter_eq_two_mul_card_filter_lt {α : Type*} [Fintype α] (key : α ↪ ℕ) (g : α → α)
    (hg0 : ∀ i, g i ≠ i) (Q : α → Prop) [DecidablePred Q]
    (hQ : ∀ i, Q i → g (g i) = i ∧ Q (g i)) :
    (univ.filter Q).card = 2 * (univ.filter fun i => Q i ∧ key i < key (g i)).card := by
  classical
  set A := univ.filter fun i => Q i ∧ key i < key (g i) with hA
  have hinj : Set.InjOn g A := by
    intro a ha b hb hab
    rw [← (hQ a (Finset.mem_filter.1 ha).2.1).1, ← (hQ b (Finset.mem_filter.1 hb).2.1).1, hab]
  have hdisj : Disjoint A (A.image g) := by
    refine Finset.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx'
    have h1 := (Finset.mem_filter.1 ha).2
    have h2 := (Finset.mem_filter.1 hx).2
    rw [(hQ a h1.1).1] at h2
    exact lt_asymm h1.2 h2.2
  have hunion : univ.filter Q = A ∪ A.image g := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image,
      hA]
    constructor
    · intro hi
      rcases lt_or_gt_of_ne (fun h => hg0 i (key.injective h).symm) with h | h
      · exact Or.inl ⟨hi, h⟩
      · refine Or.inr ⟨g i, ⟨(hQ i hi).2, ?_⟩, (hQ i hi).1⟩
        rw [(hQ i hi).1]
        exact h
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact h.1
      · exact (hQ a ha.1).2
  rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]
  ring

/-- The orientation-reversed form of `card_filter_eq_two_mul_card_filter_lt`: each 2-cycle is
counted at its endpoint with the larger key. -/
theorem card_filter_eq_two_mul_card_filter_gt {α : Type*} [Fintype α] (key : α ↪ ℕ) (g : α → α)
    (hg0 : ∀ i, g i ≠ i) (Q : α → Prop) [DecidablePred Q]
    (hQ : ∀ i, Q i → g (g i) = i ∧ Q (g i)) :
    (univ.filter Q).card = 2 * (univ.filter fun i => Q i ∧ key (g i) < key i).card := by
  classical
  have h := card_filter_eq_two_mul_card_filter_lt key g hg0 Q hQ
  have hsplit := Finset.card_filter_add_card_filter_not (s := univ.filter Q)
    (fun i => key i < key (g i))
  have e : (univ.filter Q).filter (fun i => ¬ key i < key (g i)) =
      univ.filter fun i => Q i ∧ key (g i) < key i := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun i _ => and_congr_right fun _ => ?_
    exact ⟨fun h' => lt_of_le_of_ne (not_lt.1 h') fun e => hg0 i (key.injective e),
      fun h' => not_lt.2 h'.le⟩
  rw [Finset.filter_filter, e] at hsplit
  omega

/-! ### The sub-configuration of the non-isolated components -/

section NonIso

variable {N : ℕ} (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N)

/-- The retained points: all vertices except the non-retained endpoints of the isolated pairs. -/
abbrev IsoRet : Type := {i // i ∉ isoSecondVerts f}

/-- The retained endpoints of the isolated pairs. -/
abbrev IsoRetPair : Type := {j : IsoRet f // (j : Fin N ⊕ Fin N) ∈ isoPairVerts f}

/-- The vertices of the components that are not isolated pairs. -/
abbrev IsoNon : Type := {j : IsoRet f // (j : Fin N ⊕ Fin N) ∉ isoPairVerts f}

/-- The inclusion of the non-isolated vertices. -/
def isoNonEmb : IsoNon f ↪ Fin N ⊕ Fin N :=
  (Function.Embedding.subtype _).trans (Function.Embedding.subtype _)

@[simp] theorem isoNonEmb_apply (j : IsoNon f) : isoNonEmb f j = ((j : IsoRet f) : Fin N ⊕ Fin N) :=
  rfl

/-- The restriction of `f` to the non-isolated vertices. -/
def isoNonMap (hf0 : ∀ i, f i ≠ i) (j : IsoNon f) : IsoNon f :=
  ⟨⟨f (isoNonEmb f j), fun h => apply_notMem_isoPairVerts hf0 j.2 (isoSecondVerts_subset h)⟩,
    apply_notMem_isoPairVerts hf0 j.2⟩

@[simp] theorem isoNonEmb_isoNonMap (hf0 : ∀ i, f i ≠ i) (j : IsoNon f) :
    isoNonEmb f (isoNonMap f hf0 j) = f (isoNonEmb f j) :=
  rfl

/-- The non-isolated vertices are the vertices outside `I^pair`. -/
def isoNonEquiv : IsoNon f ≃ {i // i ∉ isoPairVerts f} :=
  Equiv.subtypeSubtypeEquivSubtype (p := fun i => i ∉ isoSecondVerts f)
    (q := fun i => i ∉ isoPairVerts f) fun h h' => h (isoSecondVerts_subset h')

theorem card_isoNon : Fintype.card (IsoNon f) = 2 * N - (isoPairVerts f).card := by
  rw [Fintype.card_congr (isoNonEquiv f), Fintype.card_subtype_compl, Fintype.card_coe]
  simp [two_mul]

/-- The retained endpoints of the isolated pairs are `I^pair ∖ S`. -/
theorem card_isoRetPair :
    Fintype.card (IsoRetPair f) = (isoPairVerts f).card - (isoSecondVerts f).card := by
  rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _), Fintype.card_subtype]
  have : (univ.filter fun i => i ∉ isoSecondVerts f ∧ i ∈ isoPairVerts f) =
      isoPairVerts f \ isoSecondVerts f := by
    ext i
    simp [and_comm]
  rw [this, Finset.card_sdiff_of_subset isoSecondVerts_subset]

/-- Sums over the vertices outside `I^pair` as sums over the non-isolated vertices. -/
theorem sum_compl_isoPairVerts (w : Fin N ⊕ Fin N → ℝ) :
    ∑ i ∈ (isoPairVerts f)ᶜ, w i = ∑ j : IsoNon f, w (isoNonEmb f j) := by
  rw [Finset.sum_subtype (isoPairVerts f)ᶜ (p := fun i => i ∉ isoPairVerts f) (by simp)]
  exact (Fintype.sum_equiv (isoNonEquiv f) (fun j => w (isoNonEmb f j)) (fun i => w i)
    fun _ => rfl).symm

/-- The 2-cycle vertices of the non-isolated sub-configuration. -/
theorem card_filter_isoNonMap_two_cycle (hf0 : ∀ i, f i ≠ i) :
    (univ.filter fun j : IsoNon f => isoNonMap f hf0 (isoNonMap f hf0 j) = j).card =
      (univ.filter fun i : Fin N ⊕ Fin N => f (f i) = i).card - (isoPairVerts f).card := by
  classical
  have e : {j : IsoNon f // isoNonMap f hf0 (isoNonMap f hf0 j) = j} ≃
      {i : Fin N ⊕ Fin N // i ∉ isoPairVerts f ∧ f (f i) = i} :=
    { toFun := fun j => ⟨isoNonEmb f j.1, j.1.2, congrArg (fun x => isoNonEmb f x) j.2⟩
      invFun := fun i => ⟨⟨⟨i.1, fun h => i.2.1 (isoSecondVerts_subset h)⟩, i.2.1⟩,
        Subtype.ext (Subtype.ext i.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_subtype]
  have hsub : isoPairVerts f ⊆ univ.filter fun i : Fin N ⊕ Fin N => f (f i) = i := fun i hi =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_isoPairVerts.1 hi).1⟩
  rw [← Finset.card_sdiff_of_subset hsub]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  tauto

/-- The tie-break key of the non-isolated sub-configuration. -/
def isoNonKey : IsoNon f ↪ ℕ := (isoNonEmb f).trans (sumKey N)

/-- The number of 2-cycles of the non-isolated sub-configuration. -/
theorem two_mul_card_gpRefSet_isoNonMap (hf0 : ∀ i, f i ≠ i) :
    2 * Fintype.card {j // j ∈ gpRefSet (isoNonKey f) (isoNonMap f hf0)} =
      (univ.filter fun i : Fin N ⊕ Fin N => f (f i) = i).card - (isoPairVerts f).card := by
  classical
  rw [← card_filter_isoNonMap_two_cycle f hf0, card_filter_eq_two_mul_card_filter_lt
    (isoNonKey f) (isoNonMap f hf0) (fun j h => hf0 _ (congrArg (fun x => isoNonEmb f x) h))
    (fun j => isoNonMap f hf0 (isoNonMap f hf0 j) = j) (fun j hj => ⟨hj, by rw [hj]⟩),
    Fintype.card_subtype]
  congr 2
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

/-- **Restriction of the nearest-neighbour map** (source l. 1450, used at ): on the cell
`φ₁ = f`, the nearest-neighbour map of the non-isolated sub-configuration is the restriction of
`f`. -/
theorem nnMap_isoNon (hN : 2 ≤ N) (hf0 : ∀ i, f i ≠ i) [Nontrivial (IsoNon f)]
    {Z : Fin N ⊕ Fin N → ℂ} (hf : nearestNeighbor Z = f) :
    nnMap (isoNonKey f) (fun j => Z (isoNonEmb f j)) = isoNonMap f hf0 := by
  have : NeZero N := ⟨by omega⟩
  funext k
  have hrange : nnMap (sumKey N) Z (isoNonEmb f k) ∈ Set.range (isoNonEmb f) := by
    rw [← nearestNeighbor_eq_nnMap, hf]
    exact ⟨isoNonMap f hf0 k, rfl⟩
  have h := nnMap_restrict (sumKey N) Z (isoNonEmb f) k hrange
  apply (isoNonEmb f).injective
  rw [isoNonEmb_isoNonMap]
  calc isoNonEmb f (nnMap (isoNonKey f) (fun j => Z (isoNonEmb f j)) k)
      = nnMap (sumKey N) Z (isoNonEmb f k) := h
    _ = nearestNeighbor Z (isoNonEmb f k) := (nearestNeighbor_eq_nnMap Z _).symm
    _ = f (isoNonEmb f k) := by rw [hf]

end NonIso

/-! ### The cell integral for a general integrand -/

section Cell

variable {N : ℕ}

/-- The cell `Λ^{2N} ∩ {φ₁ = f}` is measurable. -/
theorem measurableSet_cell (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) :
    MeasurableSet ((Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f}) := by
  refine (measurableSet_pi_box N).inter ?_
  have : {Z : Fin N ⊕ Fin N → ℂ | nearestNeighbor Z = f} =
      ⋂ i, {Z | nearestNeighbor Z i = f i} := by
    ext Z
    simp [funext_iff]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_nearestNeighbor_eq i (f i)

/-- **The cell integral, given a pointwise bound by pair weights** (source l. 1622–1639). If at
the generic configurations of the cell `Λ^{2N} ∩ {φ₁ = f}` the integrand `Φ` is at most
`c · H(z_{non-isolated}) ∏_s W_s(u_s, ρ_s)`, and every pair weight has integral at most `M_s` in the
displacement (uniformly in `ρ ≥ λ`), then integrating the pair displacements conditional on the
retained coordinates and then the retained endpoints of the pairs (`N` each) gives
`c ∏_s M_s · N^{m} ∫ H`. -/
theorem lintegral_cell_le_of_pointwise (hN : 2 ≤ N) (lam : ℝ)
    (Φ : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N)
    (W : {s // s ∈ isoSecondVerts f} → ℂ × ℝ → ℝ≥0∞) (hW : ∀ s, Measurable (W s))
    (M : {s // s ∈ isoSecondVerts f} → ℝ≥0∞) (hM : ∀ s ρ, lam ≤ ρ → ∫⁻ u, W s (u, ρ) ≤ M s)
    (H : (IsoNon f → ℂ) → ℝ≥0∞) (hH : Measurable H)
    (hpt : ∀ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) → IsGeneric Z → nearestNeighbor Z = f →
      Φ Z ≤ c * (H (fun j => Z (isoNonEmb f j)) *
        ∏ s, W s (Z s - Z (f s), isoRadius f hN lam (fun k => Z k) (isoPartner s)))) :
    ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f}, Φ Z ≤
      c * ((∏ s, M s) * ((N : ℝ≥0∞) ^ Fintype.card (IsoRetPair f) * ∫⁻ w, H w)) := by
  have hA := measurableSet_cell (N := N) f
  set A := (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f} with hAdef
  set ρ : {s // s ∈ isoSecondVerts f} → (IsoRet f → ℂ) → ℝ :=
    fun s y => isoRadius f hN lam y (isoPartner s) with hρ
  set F : (IsoRet f → ℂ) → ℝ≥0∞ :=
    fun y => (∏ j : IsoRetPair f, (box N).indicator 1 (y j)) * H (fun j => y j) with hF
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N ⊕ Fin N => ℂ)
    (fun i => i ∈ isoSecondVerts f) with he
  set Ψ : ({i // i ∈ isoSecondVerts f} → ℂ) × (IsoRet f → ℂ) → ℝ≥0∞ :=
    fun x => F x.2 * ∏ s, W s (x.1 s - x.2 (isoPartner s), ρ s x.2) with hΨ
  have hFm : Measurable F := by
    refine Measurable.mul (Finset.measurable_prod _ fun j _ =>
      (measurable_one.indicator (measurableSet_box N)).comp (measurable_pi_apply _)) ?_
    exact hH.comp (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  have hρm : ∀ s, Measurable (ρ s) := fun s => measurable_isoRadius hN lam (isoPartner s)
  have hMb : ∀ s y, ∫⁻ u, W s (u, ρ s y) ≤ M s := fun s y =>
    hM s _ (lam_le_isoRadius hN lam _ _)
  have hpt' : ∀ Z ∈ A, IsGeneric Z → Φ Z ≤ c * Ψ (e Z) := by
    intro Z hZ hgen
    have hbox : ∀ i, Z i ∈ box N := fun i => hZ.1 i (Set.mem_univ i)
    refine (hpt Z hbox hgen hZ.2).trans ?_
    gcongr
    have hind : (∏ j : IsoRetPair f, (box N).indicator (1 : ℂ → ℝ≥0∞) (Z j)) = 1 := by
      refine Finset.prod_eq_one fun j _ => ?_
      rw [Set.indicator_of_mem (hbox _)]
      rfl
    show _ ≤ F (fun k => Z k) * _
    rw [hF]
    dsimp only
    rw [hind, one_mul]
    exact le_rfl
  calc ∫⁻ Z in A, Φ Z
      ≤ ∫⁻ Z in A, c * Ψ (e Z) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hA, ae_restrict_isGeneric A] with Z hZ hgen
        exact hpt' Z hZ hgen
    _ ≤ ∫⁻ Z, c * Ψ (e Z) := setLIntegral_le_lintegral _ _
    _ = c * ∫⁻ x, Ψ x := by
        rw [lintegral_const_mul' _ _ hc]
        congr 1
        convert (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N ⊕ Fin N => ℂ)
          (fun i => i ∈ isoSecondVerts f)).lintegral_comp_emb e.measurableEmbedding Ψ
    _ ≤ c * ((∏ s, M s) * ∫⁻ y, F y) := by
        gcongr
        exact lintegral_pair_prod_le (fun s => isoPartner s) F hFm W hW ρ hρm M hMb
    _ = _ := by
        rw [lintegral_prod_indicator_box_mul (α := IsoRet f)
          (fun j => (j : Fin N ⊕ Fin N) ∈ isoPairVerts f) N H hH]

/-! ### The pointwise bound on a cell from an exponent bound -/

/-- `e^{2 log m - 4 log ρ + c} = e^c m² / ρ⁴` (the weight of a same-sign pair). -/
theorem exp_two_mul_log_sub_four_mul_log {m ρ c : ℝ} (hm : 0 < m) (hρ : 0 < ρ) :
    Real.exp (2 * Real.log m - 4 * Real.log ρ + c) = Real.exp c * m ^ 2 / ρ ^ 4 := by
  have e2 : Real.exp (2 * Real.log m) = m ^ 2 := by
    rw [show (2 : ℝ) * Real.log m = ((2 : ℕ) : ℝ) * Real.log m by norm_num, ← Real.log_pow,
      Real.exp_log (by positivity)]
  have e4 : Real.exp (4 * Real.log ρ) = ρ ^ 4 := by
    rw [show (4 : ℝ) * Real.log ρ = ((4 : ℕ) : ℝ) * Real.log ρ by norm_num, ← Real.log_pow,
      Real.exp_log (by positivity)]
  rw [Real.exp_add, Real.exp_sub, e2, e4]
  ring

/-- **The pointwise bound on a cell** (source l. 1605–1622): for `Z` in `Λ` with `φ₁(Z) = f`, if
`Φ ≤ ∑_{i ∉ I^pair} (g_λ(z_i - z_{f i}) + c₁) + ∑_s P_s` and the pair weights dominate
`e^{P_s - |u_s|²/ℓ}`, then `e^Φ` is at most
`e^{c₁ |(I^pair)ᶜ| + 36N/(πℓ)} e^{∑_{i ∉ I^pair} g_λ(z_i - z_{f i})} ∏_s W_s(u_s, ρ_s)`. The Gaussian
factor `e^{-|u_s|²/ℓ}` is inserted by the packing bound `∑_s |u_s|² ≤ 36N/π` . -/
theorem ofReal_exp_le_cell_of_exponent (hN : 2 ≤ N) {lam : ℝ} (hlam : 0 < lam)
    (hle : lam ≤ Real.exp (-1)) {c₁ Φ : ℝ} (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N)
    {Z : Fin N ⊕ Fin N → ℂ} (hbox : ∀ i, Z i ∈ box N) (hf : nearestNeighbor Z = f)
    (P : {s // s ∈ isoSecondVerts f} → ℝ) (W : {s // s ∈ isoSecondVerts f} → ℂ × ℝ → ℝ≥0∞)
    (hE : Φ ≤ ∑ i ∈ (isoPairVerts f)ᶜ, (smearedKernel lam (Z i - Z (f i)) + c₁) + ∑ s, P s)
    (hW : ∀ s, ENNReal.ofReal (Real.exp (P s - ‖Z s - Z (f s)‖ ^ 2 / |Real.log lam|)) ≤
      W s (Z s - Z (f s), isoRadius f hN lam (fun k => Z k) (isoPartner s))) :
    ENNReal.ofReal (Real.exp Φ) ≤
      ENNReal.ofReal (Real.exp (c₁ * (isoPairVerts f)ᶜ.card +
          36 * N / (Real.pi * |Real.log lam|))) *
        (ENNReal.ofReal (Real.exp (∑ i ∈ (isoPairVerts f)ᶜ, smearedKernel lam (Z i - Z (f i)))) *
          ∏ s, W s (Z s - Z (f s), isoRadius f hN lam (fun k => Z k) (isoPartner s))) := by
  subst hf
  have h1 : Real.log lam ≤ -1 := by
    have := Real.log_le_log hlam hle
    rwa [Real.log_exp] at this
  have hℓ : 0 < |Real.log lam| := by rw [abs_of_neg (by linarith)]; linarith
  set ℓ := |Real.log lam| with hℓdef
  have hpack : ∑ s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)},
      ‖Z s - Z (nearestNeighbor Z s)‖ ^ 2 ≤ 36 * N / Real.pi := by
    rw [Finset.sum_coe_sort (isoSecondVerts (nearestNeighbor Z))
      (fun s => ‖Z s - Z (nearestNeighbor Z s)‖ ^ 2)]
    exact (Finset.sum_le_univ_sum_of_nonneg fun i => sq_nonneg _).trans
      (sum_sq_norm_sub_nearestNeighbor_le Z hbox)
  set E : {s // s ∈ isoSecondVerts (nearestNeighbor Z)} → ℝ := fun s =>
    P s - ‖Z s - Z (nearestNeighbor Z s)‖ ^ 2 / ℓ with hEdef
  have hkey : Φ ≤ (c₁ * (isoPairVerts (nearestNeighbor Z))ᶜ.card + 36 * N / (Real.pi * ℓ)) +
      (∑ i ∈ (isoPairVerts (nearestNeighbor Z))ᶜ,
          smearedKernel lam (Z i - Z (nearestNeighbor Z i)) + ∑ s, E s) := by
    have e1 : ∑ i ∈ (isoPairVerts (nearestNeighbor Z))ᶜ,
        (smearedKernel lam (Z i - Z (nearestNeighbor Z i)) + c₁) =
        ∑ i ∈ (isoPairVerts (nearestNeighbor Z))ᶜ,
            smearedKernel lam (Z i - Z (nearestNeighbor Z i)) +
          c₁ * (isoPairVerts (nearestNeighbor Z))ᶜ.card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have e2 : ∑ s, P s = ∑ s, E s +
        (∑ s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)},
          ‖Z s - Z (nearestNeighbor Z s)‖ ^ 2) / ℓ := by
      rw [hEdef, Finset.sum_sub_distrib, Finset.sum_div]
      ring
    have e3 : (∑ s : {s // s ∈ isoSecondVerts (nearestNeighbor Z)},
        ‖Z s - Z (nearestNeighbor Z s)‖ ^ 2) / ℓ ≤ 36 * N / (Real.pi * ℓ) := by
      have e : 36 * (N : ℝ) / (Real.pi * ℓ) = 36 * N / Real.pi / ℓ := by rw [div_div]
      rw [e]
      exact div_le_div_of_nonneg_right hpack hℓ.le
    linarith
  calc ENNReal.ofReal (Real.exp Φ)
      ≤ ENNReal.ofReal (Real.exp ((c₁ * (isoPairVerts (nearestNeighbor Z))ᶜ.card +
          36 * N / (Real.pi * ℓ)) + (∑ i ∈ (isoPairVerts (nearestNeighbor Z))ᶜ,
            smearedKernel lam (Z i - Z (nearestNeighbor Z i)) + ∑ s, E s))) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hkey)
    _ = ENNReal.ofReal (Real.exp (c₁ * (isoPairVerts (nearestNeighbor Z))ᶜ.card +
          36 * N / (Real.pi * ℓ))) *
        (ENNReal.ofReal (Real.exp (∑ i ∈ (isoPairVerts (nearestNeighbor Z))ᶜ,
            smearedKernel lam (Z i - Z (nearestNeighbor Z i)))) *
          ∏ s, ENNReal.ofReal (Real.exp (E s))) := by
        rw [← ENNReal.ofReal_prod_of_nonneg fun s _ => (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
        gcongr with s
        exact hW s

/-! ### Counting the isolated pairs of a graph -/

theorem isoPairVerts_nearestNeighbor_eq (Z₀ : Fin N ⊕ Fin N → ℂ) :
    isoPairVerts (nearestNeighbor Z₀) = isolatedPairSet Z₀ := by
  ext i
  rw [mem_isoPairVerts, mem_isolatedPairSet]
  rfl

/-- `|I^pair| = 2m`. -/
theorem card_isoPairVerts_nearestNeighbor (Z₀ : Fin N ⊕ Fin N → ℂ) :
    (isoPairVerts (nearestNeighbor Z₀)).card = 2 * numIsolatedPairs Z₀ := by
  rw [isoPairVerts_nearestNeighbor_eq]
  exact card_isolatedPairSet

/-- `|S| = m`: one non-retained endpoint per isolated pair. -/
theorem card_isoSecondVerts_nearestNeighbor (Z₀ : Fin N ⊕ Fin N → ℂ) :
    (isoSecondVerts (nearestNeighbor Z₀)).card = numIsolatedPairs Z₀ := by
  have h1 := card_isoPairVerts (nearestNeighbor_ne Z₀)
  have h2 := card_isoPairVerts_nearestNeighbor Z₀
  omega

/-- The number of neutral pairs among the isolated pairs is the number `p₀` of isolated dipoles. -/
theorem card_filter_neutral_isoSecondVerts (Z₀ : Fin N ⊕ Fin N → ℂ) :
    ((isoSecondVerts (nearestNeighbor Z₀)).filter
      fun s => charge s * charge (nearestNeighbor Z₀ s) = -1).card = (isolatedDipoles Z₀).card := by
  classical
  set f := nearestNeighbor Z₀ with hf
  have hf0 : ∀ i, f i ≠ i := nearestNeighbor_ne Z₀
  have h1 := card_filter_isIsolatedDipole Z₀
  have h2 := card_filter_eq_two_mul_card_filter_gt (sumKey N) f hf0 (IsIsolatedDipole Z₀)
    (fun i hi => ⟨hi.1, isIsolatedDipole_nearestNeighbor hi⟩)
  have h3 : (univ.filter fun i => IsIsolatedDipole Z₀ i ∧ sumKey N (f i) < sumKey N i) =
      (isoSecondVerts f).filter fun s => charge s * charge (f s) = -1 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_isoSecondVerts,
      isIsolatedDipole_iff]
    rw [← hf]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
  rw [h3] at h2
  omega

theorem ofReal_pow_eq_ofReal_exp {x : ℝ} (hx : 0 < x) (k : ℕ) :
    ENNReal.ofReal x ^ k = ENNReal.ofReal (Real.exp (k * Real.log x)) := by
  rw [← ENNReal.ofReal_pow hx.le, ← Real.log_pow, Real.exp_log (pow_pos hx k)]


/-! ### The common cutoff on the nonisolated components -/

/-- **The nonisolated components in (eq:critical-fixed-graph)**. Each of the
`K-m` cycles contributes `J_λ(1/ℓ)`. The `2(N-K)` tree variables keep the
packing constraint and contribute the Dirichlet factor, including `N = K`. -/
theorem exists_commonCutoffFactor :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-2) →
      ∀ (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (Z₀ : Fin N ⊕ Fin N → ℂ), nearestNeighbor Z₀ = f →
        ∃ H : (IsoNon f → ℂ) → ℝ≥0∞, Measurable H ∧
          (∀ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) → nearestNeighbor Z = f →
            ENNReal.ofReal (Real.exp (∑ i ∈ (isoPairVerts f)ᶜ, smearedKernel lam (Z i - Z (f i)))) ≤
              H (fun j => Z (isoNonEmb f j))) ∧
          ∫⁻ w, H w ≤ ENNReal.ofReal (Real.exp
            (((numComponents Z₀ : ℝ) - numIsolatedPairs Z₀) * Real.log N +
              ((numComponents Z₀ : ℝ) - numIsolatedPairs Z₀) * Real.log (criticalCycleMass lam) +
              ((N : ℝ) - numComponents Z₀) * Real.log (N / ((N : ℝ) - numComponents Z₀)) +
              CJ * ((N : ℝ) - numComponents Z₀) +
              36 * N / (Real.pi * |Real.log lam|))) := by
  obtain ⟨CJ₀, hJ⟩ := exists_lintegral_cell_common_cutoff_le
  refine ⟨max CJ₀ 0, le_max_right _ _, ?_⟩
  intro N hN lam hlam hlam2 f Z₀ hf₀
  subst hf₀
  set f := nearestNeighbor Z₀ with hf
  have hf0 : ∀ i, f i ≠ i := nearestNeighbor_ne Z₀
  set ℓ := |Real.log lam| with hℓdef
  have hlog : Real.log lam ≤ -2 := by
    have := Real.log_le_log hlam hlam2
    rwa [Real.log_exp] at this
  have hℓ2 : 2 ≤ ℓ := by rw [hℓdef, abs_of_neg (by linarith)]; linarith
  set K := numComponents Z₀ with hK
  set m := numIsolatedPairs Z₀ with hm
  have hP : (isoPairVerts f).card = 2 * m := card_isoPairVerts_nearestNeighbor Z₀
  have hmK : m ≤ K := numIsolatedPairs_le_numComponents Z₀
  have hKN : K ≤ N := numComponents_le Z₀
  have hPc : (isoPairVerts f)ᶜ.card = 2 * N - 2 * m := by
    rw [Finset.card_compl, hP]
    simp [two_mul]
  by_cases hmN : m = N
  · -- all components are isolated pairs
    have hKm : K = m := le_antisymm (hmN ▸ hKN) hmK
    have hcard : Fintype.card (IsoNon f) = 0 := by rw [card_isoNon, hP]; omega
    have hempty : IsEmpty (IsoNon f) := Fintype.card_eq_zero_iff.1 hcard
    refine ⟨fun _ => 1, measurable_const, fun Z _ _ => ?_, ?_⟩
    · have : (isoPairVerts f)ᶜ = ∅ := by
        rw [← Finset.card_eq_zero, hPc, hmN]; simp
      rw [this, Finset.sum_empty, Real.exp_zero, ENNReal.ofReal_one]
    · rw [lintegral_const, one_mul, volume_pi, Measure.pi_univ, Finset.univ_eq_empty,
        Finset.prod_empty]
      rw [hKm, hmN, sub_self]
      simp only [zero_mul, mul_zero, zero_add]
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      refine Real.one_le_exp ?_
      positivity
  · -- Insert the common Gaussian and keep the tree packing constraint.
    have hmN' : m < N := lt_of_le_of_ne (le_trans hmK hKN) hmN
    have hcard : Fintype.card (IsoNon f) = 2 * (N - m) := by rw [card_isoNon, hP]; omega
    have hnt : Nontrivial (IsoNon f) := by
      rw [← Fintype.one_lt_card_iff_nontrivial, hcard]; omega
    set K' := Fintype.card {j // j ∈ gpRefSet (isoNonKey f) (isoNonMap f hf0)} with hK'
    have hK'eq : 2 * K' = 2 * K - 2 * m := by
      rw [hK', two_mul_card_gpRefSet_isoNonMap f hf0, hP]
      congr 1
      rw [← card_cycleVerts_eq_two_mul_numComponents Z₀]
      rfl
    have hK'R : (K' : ℝ) = K - m := by
      have : K' = K - m := by omega
      rw [this, Nat.cast_sub hmK]
    set C' := Set.univ.pi (fun _ : IsoNon f => box N) ∩
      {w | nnMap (isoNonKey f) w = isoNonMap f hf0} with hC'
    have hC'm : MeasurableSet C' := by
      refine (MeasurableSet.univ_pi fun _ => measurableSet_box N).inter ?_
      have : {w : IsoNon f → ℂ | nnMap (isoNonKey f) w = isoNonMap f hf0} =
          ⋂ j, {w | nnMap (isoNonKey f) w j = isoNonMap f hf0 j} := by
        ext w; simp [funext_iff]
      rw [this]
      exact MeasurableSet.iInter fun j => measurableSet_nnMap_eq _ j _
    set H : (IsoNon f → ℂ) → ℝ≥0∞ := C'.indicator fun w => ENNReal.ofReal (Real.exp
      ((2 / 2) * ∑ j, smearedKernel lam (w j - w (isoNonMap f hf0 j)))) with hH
    refine ⟨H, ?_, fun Z hZ hZf => ?_, ?_⟩
    · refine Measurable.indicator ?_ hC'm
      have := measurable_smearedKernel lam
      refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _))
      exact this.comp ((measurable_pi_apply j).sub (measurable_pi_apply _))
    · have hmem : (fun j => Z (isoNonEmb f j)) ∈ C' :=
        ⟨fun j _ => hZ _, nnMap_isoNon f hN hf0 hZf⟩
      rw [hH, Set.indicator_of_mem hmem]
      refine le_of_eq (congrArg ENNReal.ofReal (congrArg Real.exp ?_))
      rw [sum_compl_isoPairVerts f]
      norm_num
      rfl
    · have hK'p : K' ≤ N - m := by omega
      have hreal : ∃ w : IsoNon f → ℂ, nnMap (isoNonKey f) w = isoNonMap f hf0 :=
        ⟨fun j => Z₀ (isoNonEmb f j), nnMap_isoNon f hN hf0 rfl⟩
      have hJ' := hJ (isoNonKey f) N (N - m) K' (isoNonMap f hf0) (by omega)
        hK'p hcard hreal rfl lam ℓ hlam (by linarith)
      have hint : ∫⁻ w, H w = ∫⁻ w in C', ENNReal.ofReal (Real.exp
          (∑ j, smearedKernel lam (w j - w (isoNonMap f hf0 j)))) := by
        rw [hH, lintegral_indicator hC'm]
        norm_num
      rw [hint]
      refine hJ'.trans ?_
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      rw [← ofReal_criticalCycleMass hlam (hlam2.trans (Real.exp_le_exp.2 (by norm_num))),
        ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_pow hNpos.le,
        ← ENNReal.ofReal_pow (criticalCycleMass_pos hlam
          (hlam2.trans (Real.exp_le_exp.2 (by norm_num)))).le]
      have hnp : (N : ℝ) ^ K' = Real.exp (K' * Real.log N) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos hNpos _)]
      have hjp : criticalCycleMass lam ^ K' = Real.exp (K' * Real.log (criticalCycleMass lam)) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos (criticalCycleMass_pos hlam
          (hlam2.trans (Real.exp_le_exp.2 (by norm_num)))) _)]
      rw [hnp, hjp, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      rw [hK'R, Nat.cast_sub (by omega : K' ≤ N - m), Nat.cast_sub hmN'.le, hK'R]
      have hNK : 0 ≤ (N : ℝ) - K := by
        have : (K : ℝ) ≤ N := by exact_mod_cast hKN
        linarith only [this]
      have h1 := mul_le_mul_of_nonneg_right (le_max_left CJ₀ 0) hNK
      rw [show (N : ℝ) - m - (K - m) = N - K by ring]
      dsimp [ℓ]
      linarith only [h1]

/-! ### The cell bound in exponential form -/

/-- The logarithm of the bound on the cell of a graph with `K` components, `m` isolated pairs and
`p₀` isolated neutral pairs, for neutral and same-sign pair masses `Mₙ` and `Mₛ` (source
l. 1618–1620): the packing cost `72N/(πℓ)` and the cost `c₁ (2N - 2m)` of the non-isolated
vertices, the `p₀` neutral pairs, the `m - p₀` same-sign pairs, the `m` retained endpoints, and the
non-isolated components (`K - m` cycles and `2(N - K)` tree vertices). -/
noncomputable def criticalCellExponent (c₁ CJ lam Mn Ms : ℝ) (N K m p₀ : ℕ) : ℝ :=
  c₁ * (2 * (N : ℝ) - 2 * m) + 36 * N / (Real.pi * |Real.log lam|) +
    p₀ * Real.log Mn + ((m : ℝ) - p₀) * Real.log Ms + m * Real.log N +
    (((K : ℝ) - m) * Real.log N +
      ((K : ℝ) - m) * Real.log (criticalCycleMass lam) + ((N : ℝ) - K) * Real.log (N / ((N : ℝ) - K)) +
      CJ * ((N : ℝ) - K) + 36 * N / (Real.pi * |Real.log lam|))


/-- **The cell bound for a general integrand** (source l. 1618–1620). There is a constant `C_J`
such that for `N ≥ 2`, `0 < λ ≤ e⁻²` and every nearest-neighbour graph `f = φ₁(Z₀)`: if at the
generic configurations of the cell `Λ^{2N} ∩ {φ₁ = f}` the integrand `Φ` is at most
`e^{c₁ |(I^pair)ᶜ| + 36N/(πℓ)} e^{∑_{i ∉ I^pair} g_λ(z_i - z_{f i})} ∏_s W_s(u_s, ρ_s)`, where every
neutral (resp. same-sign) pair weight has integral at most `Mₙ` (resp. `Mₛ`) in the displacement,
uniformly in `ρ ≥ λ`, then the cell integral of `Φ` is at most `exp (criticalCellExponent …)`. -/
theorem exists_lintegral_cell_le_criticalCellExponent :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ (N : ℕ) (hN : 2 ≤ N) (lam : ℝ), 0 < lam → lam ≤ Real.exp (-2) →
      ∀ (c₁ Mn Ms : ℝ), 0 < Mn → 0 < Ms →
      ∀ (f : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (Z₀ : Fin N ⊕ Fin N → ℂ), nearestNeighbor Z₀ = f →
      ∀ (Φ : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) (W : {s // s ∈ isoSecondVerts f} → ℂ × ℝ → ℝ≥0∞),
        (∀ s, Measurable (W s)) →
        (∀ s ρ, lam ≤ ρ → ∫⁻ u, W s (u, ρ) ≤
          if charge (s : Fin N ⊕ Fin N) * charge (f s) = -1 then ENNReal.ofReal Mn
          else ENNReal.ofReal Ms) →
        (∀ Z : Fin N ⊕ Fin N → ℂ, (∀ i, Z i ∈ box N) → IsGeneric Z → nearestNeighbor Z = f →
          Φ Z ≤ ENNReal.ofReal (Real.exp (c₁ * (isoPairVerts f)ᶜ.card +
              36 * N / (Real.pi * |Real.log lam|))) *
            (ENNReal.ofReal (Real.exp (∑ i ∈ (isoPairVerts f)ᶜ, smearedKernel lam (Z i - Z (f i)))) *
              ∏ s, W s (Z s - Z (f s), isoRadius f hN lam (fun k => Z k) (isoPartner s)))) →
        ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩ {Z | nearestNeighbor Z = f}, Φ Z ≤
          ENNReal.ofReal (Real.exp (criticalCellExponent c₁ CJ lam Mn Ms N (numComponents Z₀)
            (numIsolatedPairs Z₀) (isolatedDipoles Z₀).card)) := by
  obtain ⟨CJ, hCJ, hJ⟩ := exists_commonCutoffFactor
  refine ⟨CJ, hCJ, ?_⟩
  intro N hN lam hlam hlam2 c₁ Mn Ms hMn0 hMs0 f Z₀ hf₀ Φ W hWm hWM hpt
  obtain ⟨H, hHm, hHpt, hHJ⟩ := hJ N hN lam hlam hlam2 f Z₀ hf₀
  set ℓ := |Real.log lam| with hℓdef
  set K := numComponents Z₀ with hK
  set m := numIsolatedPairs Z₀ with hm
  set p₀ := (isolatedDipoles Z₀).card with hp₀
  have hP : (isoPairVerts f).card = 2 * m := by
    rw [← hf₀]; exact card_isoPairVerts_nearestNeighbor Z₀
  have hS : (isoSecondVerts f).card = m := by
    rw [← hf₀]; exact card_isoSecondVerts_nearestNeighbor Z₀
  have hRP : Fintype.card (IsoRetPair f) = m := by rw [card_isoRetPair, hP, hS]; omega
  have hmK : m ≤ K := numIsolatedPairs_le_numComponents Z₀
  have hKN : K ≤ N := numComponents_le Z₀
  have hPc : (isoPairVerts f)ᶜ.card = 2 * N - 2 * m := by
    rw [Finset.card_compl, hP]
    simp [two_mul]
  have hneu : ((isoSecondVerts f).filter fun s => charge s * charge (f s) = -1).card = p₀ := by
    rw [← hf₀]; exact card_filter_neutral_isoSecondVerts Z₀
  have hprod : (∏ s : {s // s ∈ isoSecondVerts f},
      (if charge (s : Fin N ⊕ Fin N) * charge (f s) = -1 then ENNReal.ofReal Mn
        else ENNReal.ofReal Ms)) =
      ENNReal.ofReal Mn ^ p₀ * ENNReal.ofReal Ms ^ (m - p₀) := by
    rw [Finset.prod_coe_sort (isoSecondVerts f)
      (fun s => if charge s * charge (f s) = -1 then ENNReal.ofReal Mn else ENNReal.ofReal Ms),
      Finset.prod_ite, Finset.prod_const, Finset.prod_const, hneu]
    have := Finset.card_filter_add_card_filter_not (s := isoSecondVerts f)
      (fun s => charge s * charge (f s) = -1)
    rw [hneu, hS] at this
    congr 2
    omega
  have haux := lintegral_cell_le_of_pointwise hN lam Φ ENNReal.ofReal_ne_top f W hWm
    (fun s => if charge (s : Fin N ⊕ Fin N) * charge (f s) = -1 then ENNReal.ofReal Mn
      else ENNReal.ofReal Ms) hWM H hHm
    (fun Z hZ hgen hZf => (hpt Z hZ hgen hZf).trans (by gcongr; exact hHpt Z hZ hZf))
  rw [hprod, hRP, hPc] at haux
  refine haux.trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNm : ((N : ℝ≥0∞)) ^ m = ENNReal.ofReal (Real.exp (m * Real.log N)) := by
    rw [← ofReal_pow_eq_ofReal_exp hNpos, ENNReal.ofReal_natCast]
  rw [ofReal_pow_eq_ofReal_exp hMn0, ofReal_pow_eq_ofReal_exp hMs0, hNm]
  calc ENNReal.ofReal (Real.exp (c₁ * ((2 * N - 2 * m : ℕ) : ℝ) + 36 * N / (Real.pi * ℓ))) *
        (ENNReal.ofReal (Real.exp (p₀ * Real.log Mn)) *
          ENNReal.ofReal (Real.exp (((m - p₀ : ℕ) : ℝ) * Real.log Ms)) *
          (ENNReal.ofReal (Real.exp (m * Real.log N)) * ∫⁻ w, H w))
      ≤ ENNReal.ofReal (Real.exp (c₁ * ((2 * N - 2 * m : ℕ) : ℝ) + 36 * N / (Real.pi * ℓ))) *
        (ENNReal.ofReal (Real.exp (p₀ * Real.log Mn)) *
          ENNReal.ofReal (Real.exp (((m - p₀ : ℕ) : ℝ) * Real.log Ms)) *
          (ENNReal.ofReal (Real.exp (m * Real.log N)) * ENNReal.ofReal (Real.exp
            (((K : ℝ) - m) * Real.log N +
              ((K : ℝ) - m) * Real.log (criticalCycleMass lam) +
              ((N : ℝ) - K) * Real.log (N / ((N : ℝ) - K)) +
              CJ * ((N : ℝ) - K) + 36 * N / (Real.pi * ℓ))))) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 2
        have hp₀m : p₀ ≤ m := by
          have := Finset.card_filter_le (isoSecondVerts f)
            (fun s => charge s * charge (f s) = -1)
          rw [hneu, hS] at this
          exact this
        rw [criticalCellExponent, Nat.cast_sub hp₀m, Nat.cast_sub (by omega : 2 * m ≤ 2 * N)]
        push_cast
        ring

end Cell

end TwoComponentCoulomb

end
