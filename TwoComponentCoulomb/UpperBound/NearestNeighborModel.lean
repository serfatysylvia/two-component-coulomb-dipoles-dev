/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.NearestNeighbor.General
public import TwoComponentCoulomb.NearestNeighbor.GeneralStructure
public import TwoComponentCoulomb.PhaseSpace.CellIntegral
public import TwoComponentCoulomb.PhaseSpace.GunsonPanta
import TwoComponentCoulomb.Gibbs.Basic
import TwoComponentCoulomb.Gibbs.Measurability
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Potential.PairIntegral

/-!
# The nearest-neighbour model: reduction to the cycle and tree integrals (Lemma 3.4, Steps 1--2)

Source: l. 781–807 (Lemma 3.4, Steps 1 and 2). Let `ι` be a finite index
type with a tie-break key `key : ι ↪ ℕ`, and `f : ι → ι` the nearest-neighbour map of some
configuration. The cell `Λ^ι ∩ {nnMap key z = f}` is integrated against
`exp (-β F^nn_λ (z)) = exp ((β/2) ∑_i g_λ (z_i - z_{φ(i)}))`.

In the Gunson--Panta variables `u = GP z` (`TwoComponentCoulomb.gpMap`) with the reference set
`R = gpRefSet key f` (one vertex m′ₖ of each 2-cycle) one has
* `z_i - z_{f i} = u_i` for `i ∉ R`, and
* `z_i - z_{f i} = -u_{f i}` for `i ∈ R`, where `f i = m_k ∉ R` is the other vertex of the 2-cycle,
so that, `g_λ` being even, the displacement `u_{m_k}` of each 2-cycle appears twice (weight
`exp (β g_λ (u_{m_k}))`, the source's eq. (eq:red neutral)) and every other non-reference vertex
once (weight `exp ((β/2) g_λ (u_i))`).

## Main results

* `TwoComponentCoulomb.card_cycIdx`, `TwoComponentCoulomb.card_treeIdx`: the `K` cycle vertices
  `m_k` and the `|ι| - 2K` tree vertices among the non-reference vertices.
* `TwoComponentCoulomb.two_mul_card_gpRefSet_nnMap_le`, `TwoComponentCoulomb.one_le_card_gpRefSet_nnMap`
  and `TwoComponentCoulomb.card_gpRefSet_nnMap_eq_card_components`: `1 ≤ K`, `2K ≤ |ι|`, and `K` is
  the number of connected components of the nearest-neighbour graph.
* `TwoComponentCoulomb.sum_smearedKernel_gp_symm`: the exponent bookkeeping of (eq:red neutral).
* `TwoComponentCoulomb.lintegral_ball_prod_equiv`, `TwoComponentCoulomb.lintegral_ball_mul_le`:
  relabelling of the coordinates of a ball integral, and the separation of two groups of
  coordinates (the inclusion `B ⊆ B₁ × B₂` of (eq:cutt)).
* `TwoComponentCoulomb.lintegral_cell_le_cycle_mul_tree`: source (eq:red neutral) and (eq:cutt),
  `J(f) ≤ N^K · (∫_{B₁} ∏ e^{β g_λ(u_k)}) · (∫_{B₂} ∏ e^{(β/2) g_λ(u_i)})`, with
  `B₁ = {U ∈ ℂ^K | |U|² ≤ 36N/π}` and `B₂ = {U ∈ ℂ^{2p-2K} | |U|² ≤ 36N/π}`.
* `TwoComponentCoulomb.lintegral_ball_prod_exp_le`: source the planar pair-mass identity and the planar pair-mass identity,
  `∫_{|U|² ≤ s} ∏_{i ≤ m} e^{γ g_λ(u_i)} ≤ (𝒵_γ λ^{2-γ})^m` for `γ > 2`.

The index type `ι` is arbitrary (finite, with a tie-break key), so that the lemma applies to the
complement `I^c` of a marked set of points (source l. 1474–1481); `N` (the area of `Λ`) and the
number `2p` of points are independent.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### The reference set of a self-map without fixed points -/

section RefSet

variable {ι : Type*} {key : ι ↪ ℕ} {f : ι → ι}

/-- The partner `f i` of a reference vertex `i` is not a reference vertex. -/
theorem apply_notMem_gpRefSet (hf0 : ∀ i, f i ≠ i) {i : ι} (hi : i ∈ gpRefSet key f) :
    f i ∉ gpRefSet key f :=
  (gpRefSet_mem_iff_not_mem hi.1 (hf0 i)).1 hi

/-- A non-reference vertex on a 2-cycle has its partner in the reference set. -/
theorem apply_mem_gpRefSet_of_notMem (hf0 : ∀ i, f i ≠ i) {j : ι} (hj : j ∉ gpRefSet key f)
    (h2 : f (f j) = j) : f j ∈ gpRefSet key f := by
  by_contra h
  exact hj ((gpRefSet_mem_iff_not_mem h2 (hf0 j)).2 h)

end RefSet

/-! ### Cycle vertices and tree vertices -/

section CycleTree

open scoped Classical

variable {ι : Type*} [Fintype ι] (key : ι ↪ ℕ) (f : ι → ι)

/-- The non-reference vertices (the indices of the Gunson--Panta displacements `u_i`, `i ∉ R`). -/
abbrev NonRef : Type _ := {i : ι // i ∉ gpRefSet key f}

/-- The *cycle vertices*: non-reference vertices lying on a 2-cycle (the vertices `m_k` of the
source, l. 645–660). -/
abbrev CycIdx : Type _ := {j : NonRef key f // f (f j) = j}

/-- The *tree vertices*: non-reference vertices not lying on a 2-cycle. -/
abbrev TreeIdx : Type _ := {j : NonRef key f // ¬ f (f j) = j}

variable {key f}

/-- The map `i ↦ f i` is a bijection from the reference vertices onto the cycle vertices. -/
def refEquivCyc (hf0 : ∀ i, f i ≠ i) : {i // i ∈ gpRefSet key f} ≃ CycIdx key f where
  toFun i := ⟨⟨f i.1, apply_notMem_gpRefSet hf0 i.2⟩, by
    show f (f (f i.1)) = f i.1
    rw [i.2.1]⟩
  invFun j := ⟨f j.1.1, apply_mem_gpRefSet_of_notMem hf0 j.1.2 j.2⟩
  left_inv i := Subtype.ext i.2.1
  right_inv j := Subtype.ext (Subtype.ext j.2)

/-- There are as many cycle vertices as reference vertices (`K` of them). -/
theorem card_cycIdx (hf0 : ∀ i, f i ≠ i) :
    Fintype.card (CycIdx key f) = Fintype.card {i // i ∈ gpRefSet key f} :=
  (Fintype.card_congr (refEquivCyc hf0)).symm

/-- The number of non-reference vertices is `|ι| - K`. -/
theorem card_nonRef : Fintype.card (NonRef key f) =
    Fintype.card ι - Fintype.card {i // i ∈ gpRefSet key f} :=
  Fintype.card_subtype_compl _

/-- `2K ≤ |ι|`: the reference vertices and their partners are disjoint. -/
theorem two_mul_card_gpRefSet_le (hf0 : ∀ i, f i ≠ i) :
    2 * Fintype.card {i // i ∈ gpRefSet key f} ≤ Fintype.card ι := by
  have h1 : Fintype.card (CycIdx key f) ≤ Fintype.card (NonRef key f) :=
    Fintype.card_subtype_le _
  rw [card_cycIdx hf0, card_nonRef] at h1
  have h2 := Fintype.card_subtype_le (fun i => i ∈ gpRefSet key f)
  omega

/-- There are `|ι| - 2K` tree vertices. -/
theorem card_treeIdx (hf0 : ∀ i, f i ≠ i) :
    Fintype.card (TreeIdx key f) = Fintype.card ι - 2 * Fintype.card {i // i ∈ gpRefSet key f} := by
  have h1 : Fintype.card (TreeIdx key f) =
      Fintype.card (NonRef key f) - Fintype.card (CycIdx key f) :=
    Fintype.card_subtype_compl (fun j : NonRef key f => f (f j) = j)
  have h2 := two_mul_card_gpRefSet_le (key := key) hf0
  rw [card_cycIdx hf0, card_nonRef] at h1
  omega

/-! ### The energy in Gunson--Panta variables -/

section Energy

variable (lam : ℝ) (hR : ∀ i, ∃ n, f^[n] i ∈ gpRefSet key f) (u : ι → ℂ)

/-- On a non-reference vertex, the nearest-neighbour displacement is the Gunson--Panta coordinate
`u_i` (source l. 785–787). -/
theorem gp_symm_sub_of_notMem {i : ι} (hi : i ∉ gpRefSet key f) :
    (gpLinearEquiv f (gpRefSet key f) hR).symm u i -
        (gpLinearEquiv f (gpRefSet key f) hR).symm u (f i) = u i := by
  rw [gpLinearEquiv_symm_apply_of_not_mem hR u hi]
  ring

/-- On a reference vertex `i`, the displacement `z_i - z_{f i}` is `-u_{f i}`, where `f i = m_k` is
the other vertex of the 2-cycle. -/
theorem gp_symm_sub_of_mem (hf0 : ∀ i, f i ≠ i) {i : ι} (hi : i ∈ gpRefSet key f) :
    (gpLinearEquiv f (gpRefSet key f) hR).symm u i -
        (gpLinearEquiv f (gpRefSet key f) hR).symm u (f i) = -u (f i) := by
  have h1 := gpLinearEquiv_symm_apply_of_not_mem hR u (apply_notMem_gpRefSet hf0 hi)
  rw [hi.1] at h1
  rw [h1]
  ring

/-- **Exponent bookkeeping** (source l. 789, "the interaction `g_λ(u_{m_k})` is counted
twice"): in Gunson--Panta variables, `∑_i g_λ(z_i - z_{f i})` is twice the sum over the cycle
vertices plus the sum over the tree vertices of `g_λ(u_j)`. -/
theorem sum_smearedKernel_gp_symm (hf0 : ∀ i, f i ≠ i) :
    ∑ i, smearedKernel lam ((gpLinearEquiv f (gpRefSet key f) hR).symm u i -
        (gpLinearEquiv f (gpRefSet key f) hR).symm u (f i)) =
      2 * ∑ j : CycIdx key f, smearedKernel lam (u j.1.1) +
        ∑ j : TreeIdx key f, smearedKernel lam (u j.1.1) := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ gpRefSet key f)]
  have hR' : ∑ i : {i // i ∈ gpRefSet key f}, smearedKernel lam
      ((gpLinearEquiv f (gpRefSet key f) hR).symm u i -
        (gpLinearEquiv f (gpRefSet key f) hR).symm u (f i)) =
      ∑ j : CycIdx key f, smearedKernel lam (u j.1.1) := by
    rw [← Fintype.sum_equiv (refEquivCyc hf0) _ (fun j => smearedKernel lam (u j.1.1))
      (fun i => rfl)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gp_symm_sub_of_mem hR u hf0 i.2, smearedKernel_neg]
    rfl
  have hN : ∑ i : {i // i ∉ gpRefSet key f}, smearedKernel lam
      ((gpLinearEquiv f (gpRefSet key f) hR).symm u i -
        (gpLinearEquiv f (gpRefSet key f) hR).symm u (f i)) =
      ∑ j : CycIdx key f, smearedKernel lam (u j.1.1) +
        ∑ j : TreeIdx key f, smearedKernel lam (u j.1.1) := by
    rw [Fintype.sum_subtype_add_sum_subtype (fun j : NonRef key f => f (f j) = j)
      (fun j => smearedKernel lam (u j.1))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gp_symm_sub_of_notMem hR u i.2]
  rw [hR', hN]
  ring

end Energy

/-! ### Integrals over balls of `κ → ℂ` -/

section Ball

/-- Relabelling the coordinates: the ball integral of a product of one-variable functions depends
only on the cardinality of the index type. -/
theorem lintegral_ball_prod_equiv {κ κ' : Type*} [Fintype κ] [Fintype κ'] (e : κ ≃ κ') (s : ℝ)
    (G : ℂ → ℝ≥0∞) :
    ∫⁻ v in {v : κ → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s}, ∏ i, G (v i) =
      ∫⁻ w in {w : κ' → ℂ | ∑ j, ‖w j‖ ^ 2 ≤ s}, ∏ j, G (w j) := by
  set E := MeasurableEquiv.piCongrLeft (fun _ : κ => ℂ) e.symm with hE
  have hEapp : ∀ (w : κ' → ℂ) (i : κ), E w i = w (e i) := fun w i => by
    rw [hE, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp
  have hmp : MeasurePreserving E volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : κ => ℂ) e.symm
  have hpre : E ⁻¹' {v : κ → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s} = {w : κ' → ℂ | ∑ j, ‖w j‖ ^ 2 ≤ s} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hEapp]
    rw [Equiv.sum_comp e fun j => ‖w j‖ ^ 2]
  have h := hmp.setLIntegral_comp_preimage_emb E.measurableEmbedding
    (fun v : κ → ℂ => ∏ i, G (v i)) {v : κ → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s}
  rw [hpre] at h
  rw [← h]
  refine lintegral_congr fun w => ?_
  simp only [hEapp]
  exact Equiv.prod_comp e fun j => G (w j)

/-- **Separation of the cycle and tree variables** (source l. 802–807, "Splitting the
variables", the inclusion `B ⊆ B₁ × B₂`): the integral over the ball `∑ |v_i|² ≤ s` of a product
`H₁(v|_P) H₂(v|_{¬P})` is at most the product of the integrals over the two balls. -/
theorem lintegral_ball_mul_le {κ : Type*} [Fintype κ] (P : κ → Prop) [DecidablePred P] (s : ℝ)
    (H₁ : ({j // P j} → ℂ) → ℝ≥0∞) (H₂ : ({j // ¬ P j} → ℂ) → ℝ≥0∞) (h₁ : Measurable H₁)
    (h₂ : Measurable H₂) :
    ∫⁻ v in {v : κ → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s},
        H₁ (fun i : {j // P j} => v i) * H₂ (fun i : {j // ¬ P j} => v i) ≤
      (∫⁻ w in {w : {j // P j} → ℂ | ∑ i, ‖w i‖ ^ 2 ≤ s}, H₁ w) *
        ∫⁻ w in {w : {j // ¬ P j} → ℂ | ∑ i, ‖w i‖ ^ 2 ≤ s}, H₂ w := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : κ => ℂ) P with he
  have hmp := volume_preserving_piEquivPiSubtypeProd (fun _ : κ => ℂ) P
  set S₁ : Set ({j // P j} → ℂ) := {w | ∑ i, ‖w i‖ ^ 2 ≤ s} with hS₁
  set S₂ : Set ({j // ¬ P j} → ℂ) := {w | ∑ i, ‖w i‖ ^ 2 ≤ s} with hS₂
  have hsub : {v : κ → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s} ⊆ e ⁻¹' (S₁ ×ˢ S₂) := by
    intro v hv
    have hsum := Fintype.sum_subtype_add_sum_subtype P fun i => ‖v i‖ ^ 2
    have h1 : 0 ≤ ∑ i : {j // P j}, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    have h2 : 0 ≤ ∑ i : {j // ¬ P j}, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    refine ⟨?_, ?_⟩
    · show ∑ i : {j // P j}, ‖v i‖ ^ 2 ≤ s
      have : ∑ i, ‖v i‖ ^ 2 ≤ s := hv
      linarith
    · show ∑ i : {j // ¬ P j}, ‖v i‖ ^ 2 ≤ s
      have : ∑ i, ‖v i‖ ^ 2 ≤ s := hv
      linarith
  refine (lintegral_mono_set hsub).trans (le_of_eq ?_)
  have h := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun y : ({j // P j} → ℂ) × ({j // ¬ P j} → ℂ) => H₁ y.1 * H₂ y.2) (S₁ ×ˢ S₂)
  refine h.trans ?_
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact lintegral_prod_mul h₁.aemeasurable h₂.aemeasurable

end Ball

/-! ### The reduction -/

section Reduction

open scoped Classical

/-- **Lemma 3.4, Steps 1--2** (source (eq:red neutral) and (eq:cutt), l. 785–807). Let `f` be the
nearest-neighbour map of some configuration of `|ι| = 2p` points, with `K` 2-cycles
(`K = |gpRefSet key f|`; this is the number of connected components of the graph). The integral
`J(f)` of `exp (-β F^nn_λ) = exp ((β/2) ∑_i g_λ(z_i - z_{φ(i)}))` over the cell
`Λ^ι ∩ {nnMap key z = f}` is at most
`N^K · (∫_{B₁} ∏_k e^{β g_λ(u_k)} du) · (∫_{B₂} ∏_i e^{(β/2) g_λ(u_i)} du)`
where `B₁ ⊆ ℂ^K` and `B₂ ⊆ ℂ^{2p-2K}` are the balls `|U|² ≤ 36N/π` (source the cycle-variable ball, the tree-variable ball). -/
theorem lintegral_cell_le_cycle_mul_tree [Nontrivial ι] {N p K : ℕ}
    (hcard : Fintype.card ι = 2 * p) (key : ι ↪ ℕ) {f : ι → ι}
    (hf : ∃ z₀ : ι → ℂ, nnMap key z₀ = f) (hK : Fintype.card {i // i ∈ gpRefSet key f} = K)
    (β lam : ℝ) :
    ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
        ENNReal.ofReal (Real.exp ((β / 2) * ∑ i, smearedKernel lam (z i - z (nnMap key z i)))) ≤
      (N : ℝ≥0∞) ^ K *
        ((∫⁻ v in {v : Fin K → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ 36 * N / Real.pi},
            ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel lam (v i)))) *
          ∫⁻ v in {v : Fin (2 * p - 2 * K) → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ 36 * N / Real.pi},
            ∏ i, ENNReal.ofReal (Real.exp ((β / 2) * smearedKernel lam (v i)))) := by
  obtain ⟨z₀, rfl⟩ := hf
  set f := nnMap key z₀ with hfdef
  have hf0 : ∀ i, f i ≠ i := nnMap_ne key z₀
  have hR : ∀ i, ∃ n, f^[n] i ∈ gpRefSet key f := exists_iterate_nnMap_mem_gpRefSet key z₀
  have hg : Measurable (smearedKernel lam) := measurable_smearedKernel lam
  have hcell : MeasurableSet {z : ι → ℂ | nnMap key z = f} := by
    have : {z : ι → ℂ | nnMap key z = f} = ⋂ i, {z | nnMap key z i = f i} := by
      ext z; simp [funext_iff]
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_nnMap_eq key i (f i)
  have hcell' : MeasurableSet ((Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f}) :=
    (MeasurableSet.univ_pi fun _ => measurableSet_box N).inter hcell
  -- the weights
  set G₁ : ℂ → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (β * smearedKernel lam v)) with hG₁
  set G₂ : ℂ → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp ((β / 2) * smearedKernel lam v))
    with hG₂
  have hG₁m : Measurable G₁ := by rw [hG₁]; fun_prop
  have hG₂m : Measurable G₂ := by rw [hG₂]; fun_prop
  set H₁ : (CycIdx key f → ℂ) → ℝ≥0∞ := fun w => ∏ j, G₁ (w j) with hH₁
  set H₂ : (TreeIdx key f → ℂ) → ℝ≥0∞ := fun w => ∏ j, G₂ (w j) with hH₂
  have hH₁m : Measurable H₁ :=
    Finset.measurable_prod _ fun j _ => hG₁m.comp (measurable_pi_apply j)
  have hH₂m : Measurable H₂ :=
    Finset.measurable_prod _ fun j _ => hG₂m.comp (measurable_pi_apply j)
  set H : (NonRef key f → ℂ) → ℝ≥0∞ := fun v =>
    H₁ (fun i : CycIdx key f => v i) * H₂ (fun i : TreeIdx key f => v i) with hH
  have hHm : Measurable H := by
    refine Measurable.mul (hH₁m.comp ?_) (hH₂m.comp ?_) <;>
      exact measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hFH : ∀ u : ι → ℂ,
      ENNReal.ofReal (Real.exp ((β / 2) * ∑ i, smearedKernel lam
        ((gpLinearEquiv f (gpRefSet key f) hR).symm u i -
          (gpLinearEquiv f (gpRefSet key f) hR).symm u (f i)))) =
        H (fun i : NonRef key f => u i) := by
    intro u
    rw [sum_smearedKernel_gp_symm lam hR u hf0]
    have h1 : (β / 2) * (2 * ∑ j : CycIdx key f, smearedKernel lam (u j.1.1) +
        ∑ j : TreeIdx key f, smearedKernel lam (u j.1.1)) =
        ∑ j : CycIdx key f, β * smearedKernel lam (u j.1.1) +
          ∑ j : TreeIdx key f, (β / 2) * smearedKernel lam (u j.1.1) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [h1, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, Real.exp_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le),
      ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
  have hmain := lintegral_cell_le_comp (N := N) key (gpRefSet key f) hR
    (fun z => ENNReal.ofReal (Real.exp ((β / 2) * ∑ i, smearedKernel lam (z i - z (f i)))))
    H hHm hFH
  -- compare the integrands on the cell
  have hcongr : ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
        ENNReal.ofReal (Real.exp ((β / 2) * ∑ i, smearedKernel lam (z i - z (nnMap key z i)))) =
      ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
        ENNReal.ofReal (Real.exp ((β / 2) * ∑ i, smearedKernel lam (z i - z (f i)))) := by
    refine setLIntegral_congr_fun hcell' fun z hz => ?_
    have : nnMap key z = f := hz.2
    simp only [this]
  rw [hcongr]
  refine hmain.trans ?_
  rw [hK]
  gcongr
  refine (lintegral_ball_mul_le (fun j : NonRef key f => f (f j) = j) _ H₁ H₂ hH₁m hH₂m).trans ?_
  have eC : CycIdx key f ≃ Fin K := Fintype.equivFinOfCardEq ((card_cycIdx hf0).trans hK)
  have eT : TreeIdx key f ≃ Fin (2 * p - 2 * K) := Fintype.equivFinOfCardEq (by
    rw [card_treeIdx hf0, hK, hcard])
  refine le_of_eq ?_
  congr 1
  · exact lintegral_ball_prod_equiv eC _ G₁
  · exact lintegral_ball_prod_equiv eT _ G₂

end Reduction

/-! ### Counts for a nonempty cell -/

section Counts

variable [Nontrivial ι] (key : ι ↪ ℕ) (z₀ : ι → ℂ)

/-- A nearest-neighbour map has at least one 2-cycle: `1 ≤ K`. -/
theorem one_le_card_gpRefSet_nnMap :
    1 ≤ Fintype.card {i // i ∈ gpRefSet key (nnMap key z₀)} := by
  obtain ⟨i₀⟩ : Nonempty ι := inferInstance
  obtain ⟨n, hn⟩ := exists_iterate_nnMap_mem_gpRefSet key z₀ i₀
  exact Fintype.card_pos_iff.2 ⟨⟨_, hn⟩⟩

/-- The reference vertices and their partners are disjoint: `2K ≤ |ι|`. -/
theorem two_mul_card_gpRefSet_nnMap_le :
    2 * Fintype.card {i // i ∈ gpRefSet key (nnMap key z₀)} ≤ Fintype.card ι :=
  two_mul_card_gpRefSet_le (nnMap_ne key z₀)

/-- **`K` is the number of connected components** (source l. 781–785): the reference set of the
nearest-neighbour map `nnMap key z₀` contains one vertex of each 2-cycle, so its cardinality is the
number of connected components of the nearest-neighbour graph. -/
theorem card_gpRefSet_nnMap_eq_card_components :
    Fintype.card {i // i ∈ gpRefSet key (nnMap key z₀)} =
      Nat.card (nnGraph key z₀).ConnectedComponent := by
  classical
  set f := nnMap key z₀ with hfdef
  have hf0 : ∀ i, f i ≠ i := nnMap_ne key z₀
  set Rf : Finset ι := Finset.univ.filter (· ∈ gpRefSet key f) with hRf
  have hRfcard : Rf.card = Fintype.card {i // i ∈ gpRefSet key f} := by
    rw [hRf, Fintype.card_subtype]
  have hinj : Set.InjOn f (Rf : Set ι) := by
    intro a ha b hb hab
    have ha' : a ∈ gpRefSet key f := by simpa [hRf] using ha
    have hb' : b ∈ gpRefSet key f := by simpa [hRf] using hb
    rw [← ha'.1, ← hb'.1]
    exact congrArg f hab
  have hdisj : Disjoint Rf (Rf.image f) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hi'
    have hr' : r ∈ gpRefSet key f := by simpa [hRf] using hr
    exact apply_notMem_gpRefSet hf0 hr' (by simpa [hRf] using hi)
  have hcyc : nnCycleVerts key z₀ = Rf ∪ Rf.image f := by
    ext i
    rw [mem_nnCycleVerts, Finset.mem_union, Finset.mem_image]
    constructor
    · intro h
      by_cases hi : i ∈ gpRefSet key f
      · exact Or.inl (by simpa [hRf] using hi)
      · refine Or.inr ⟨f i, ?_, h⟩
        simpa [hRf] using apply_mem_gpRefSet_of_notMem hf0 hi h
    · rintro (h | ⟨r, hr, rfl⟩)
      · exact (by simpa [hRf] using h : i ∈ gpRefSet key f).1
      · have hr' : r ∈ gpRefSet key f := by simpa [hRf] using hr
        show f (f (f r)) = f r
        rw [hr'.1]
  have h2 := card_nnCycleVerts_eq_two_mul_card_components key z₀
  rw [hcyc, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj] at h2
  omega

end Counts

/-! ### The cycle integral for an integrable weight -/

section FullSpace

/-- **Source the planar pair-mass identity and the planar pair-mass identity** (l. 819–825), for any number `m` of variables and any
radius: for `γ > 2`, removing the restriction to the ball,
`∫_{|U|² ≤ s} ∏_{i ≤ m} e^{γ g_λ(u_i)} du ≤ (𝒵_γ λ^{2-γ})^m`. -/
theorem lintegral_ball_prod_exp_le {γ : ℝ} (hγ : 2 < γ) {lam : ℝ} (hlam : 0 < lam) (m : ℕ)
    (s : ℝ) :
    ∫⁻ v in {v : Fin m → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s},
        ∏ i, ENNReal.ofReal (Real.exp (γ * smearedKernel lam (v i))) ≤
      ENNReal.ofReal ((dipoleConstant γ hγ.le * lam ^ (2 - γ)) ^ m) := by
  have hint := integrable_exp_smearedKernel (β := γ) hγ hlam
  calc ∫⁻ v in {v : Fin m → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s},
        ∏ i, ENNReal.ofReal (Real.exp (γ * smearedKernel lam (v i)))
      ≤ ∫⁻ v : Fin m → ℂ, ∏ i, ENNReal.ofReal (Real.exp (γ * smearedKernel lam (v i))) :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ v : Fin m → ℂ, ENNReal.ofReal (∏ i, Real.exp (γ * smearedKernel lam (v i))) := by
        refine lintegral_congr fun v => ?_
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
    _ = ENNReal.ofReal (∫ v : Fin m → ℂ, ∏ i, Real.exp (γ * smearedKernel lam (v i))) := by
        refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
        · exact Integrable.fintype_prod (f := fun _ : Fin m => fun u : ℂ =>
            Real.exp (γ * smearedKernel lam u)) (μ := fun _ => volume) fun _ => hint
        · exact Filter.Eventually.of_forall fun v =>
            Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
    _ = ENNReal.ofReal ((dipoleConstant γ hγ.le * lam ^ (2 - γ)) ^ m) := by
        rw [integral_fintype_prod_volume_eq_pow (fun u : ℂ => Real.exp (γ * smearedKernel lam u)),
          integral_exp_smearedKernel hγ hlam]
        simp

end FullSpace




end CycleTree

end TwoComponentCoulomb

end
