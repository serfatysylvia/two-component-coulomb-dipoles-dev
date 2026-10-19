/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.NearestNeighbor.General
public import TwoComponentCoulomb.PhaseSpace.GunsonPanta
public import TwoComponentCoulomb.UpperBound.IsolatedRadial
public import TwoComponentCoulomb.UpperBound.IsolatedReductionBounds
public import TwoComponentCoulomb.UpperBound.PairAssignedEnergy
import TwoComponentCoulomb.Gibbs.Basic
import TwoComponentCoulomb.Gibbs.Measurability
import TwoComponentCoulomb.Integrals.PiProduct
import TwoComponentCoulomb.Integrals.Radial

/-!
# Proposition 3.9, Steps 1--2: reduction to an integral over the pair representatives

Source: proof of Proposition 3.9 (`prop:isolated`), l. 1257--1333, up to
(pred3). Fix a finite index type `ι`, a tie-break key `key`, a fixed-point-free involution
`f : ι → ι` (the nearest-neighbour graph `γ` of the cell, all of whose components are `2`-cycles)
and a set `R ⊆ ι` of representatives, with exactly one endpoint of each `2`-cycle
(`i ∈ R ↔ f i ∉ R`). The integral `I(γ)` of Proposition 3.9 is
`∫_{Λ^ι ∩ {nnMap key z = f}} exp(-β E(z)) dz` with `E = pairAssignedEnergy h3 key lam C S`, where
`S` is the `f`-invariant set of vertices of the pairs assigned the logarithmic (same-sign) term.

## Main results

* `TwoComponentCoulomb.IsolatedReduction.pairCoords`,
  `TwoComponentCoulomb.IsolatedReduction.measurePreserving_pairCoords`: the change of variables
  `z ↦ (w, u)`, `w_j = z_j`, `u_j = z_{f j} - z_j` (`j ∈ R`), is a measure-preserving measurable
  embedding of `ι → ℂ` into `(R → ℂ) × (R → ℂ)` (it is the Gunson--Panta map of
  `PhaseSpace/GunsonPanta.lean` with the reference set `R`, followed by a relabelling; source
  l. 1273: the change of variables has Jacobian `1`).
* `TwoComponentCoulomb.IsolatedReduction.lintegral_cell_le_lintegral_ref`: the displacement
  reduction. For measurable pair weights `Φ_j(u, ρ)`,
  `∫_{Λ^ι ∩ cell} ∏_j Φ_j(u_j(z), ρ_j(z)) dz ≤ ∫_{Λ^R} ∏_j ∫_{|u| ≤ 4 ρ_j(w)} Φ_j(u, ρ_j(w)) du dw`
  (Fubini with the displacement domain enlarged to `|u_j| ≤ 4ρ_j`, source l. 1268, 1277).
* `TwoComponentCoulomb.lintegral_isolatedCell_le`: **`(pred3)`** (source l. 1322--1333).
  For `β ≥ 2` and `C ≥ 0` there is `C' > 0` (depending only on `β` and `C`) such that, for
  `0 < λ ≤ e^{-1}`, the cell integral is at most
  `(𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}))^p ∫_{Λ^R} ∏_{j ∈ R ∖ S} (1 + C' φ_β(ρ_j))
    ∏_{j ∈ R ∩ S} C' (ℓ^{-1} 1_{β=2} + (λ/ρ_j)^{β-2} 1_{β>2}) dW`.
* `TwoComponentCoulomb.lintegral_isolatedCell_le_gpRefSet`: the same with the Gunson--Panta
  reference set `gpRefSet key f` as the set of representatives.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe u

namespace TwoComponentCoulomb

namespace IsolatedReduction

/-! ### The change of variables `z ↦ (w, u)` -/

section ChangeOfVariables

variable {ι : Type*} [Fintype ι] {f : ι → ι} {R : Set ι} [DecidablePred (· ∈ R)]

omit [Fintype ι] in
/-- Every `f`-orbit reaches the set of representatives. -/
theorem exists_iterate_mem_ref (hRf : ∀ i, i ∈ R ↔ f i ∉ R) (i : ι) : ∃ n, f^[n] i ∈ R := by
  by_cases h : i ∈ R
  · exact ⟨0, h⟩
  · exact ⟨1, not_not.1 (mt (hRf i).2 h)⟩

variable (f R) in
/-- The pair coordinates `(w, u)` of a configuration: the representatives `w_j = z_j` and the
displacements `u_j = z_{f j} - z_j`, `j ∈ R` (source l. 1258, 1263). -/
def pairCoords (z : ι → ℂ) : ({i // i ∈ R} → ℂ) × ({i // i ∈ R} → ℂ) :=
  (fun j => z j, fun j => z (f j) - z j)

/-- The pair coordinates as a measurable equivalence: the Gunson--Panta map with reference set
`R`, the splitting of `ι` into `R` and its complement, and the relabelling of the complement by
`j ↦ f j`. -/
noncomputable def pairCoordsEquiv (hf2 : ∀ i, f (f i) = i) (hRf : ∀ i, i ∈ R ↔ f i ∉ R) :
    (ι → ℂ) ≃ᵐ ({i // i ∈ R} → ℂ) × ({i // i ∈ R} → ℂ) :=
  (gpLinearEquiv f R (exists_iterate_mem_ref hRf)).toContinuousLinearEquiv.toHomeomorph
    |>.toMeasurableEquiv.trans
    ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (· ∈ R)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.piCongrLeft (fun _ : {i // i ∈ R} => ℂ) (refEquiv hf2 hRf).symm)))

theorem pairCoordsEquiv_apply (hf2 : ∀ i, f (f i) = i) (hRf : ∀ i, i ∈ R ↔ f i ∉ R)
    (z : ι → ℂ) : pairCoordsEquiv hf2 hRf z = pairCoords f R z := by
  have h1 : ∀ j : {i // i ∈ R}, gpLinearEquiv f R (exists_iterate_mem_ref hRf) z j = z j :=
    fun j => by rw [gpLinearEquiv_apply, gpMap_apply_of_mem _ j.2]
  have h2 : ∀ j : {i // i ∈ R},
      gpLinearEquiv f R (exists_iterate_mem_ref hRf) z (f j) = z (f j) - z j := fun j => by
    rw [gpLinearEquiv_apply, gpMap_apply_of_not_mem _ ((hRf j).1 j.2), hf2]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · exact h1 j
  · show (MeasurableEquiv.piCongrLeft (fun _ : {i // i ∈ R} => ℂ) (refEquiv hf2 hRf).symm
      (fun i : {i // i ∉ R} => gpLinearEquiv f R (exists_iterate_mem_ref hRf) z i)) j = _
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp only [Equiv.symm_symm, eq_rec_constant]
    exact h2 j

theorem measurePreserving_pairCoordsEquiv (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) :
    MeasurePreserving (pairCoordsEquiv hf2 hRf) volume volume := by
  have h1 : MeasurePreserving (gpLinearEquiv f R (exists_iterate_mem_ref hRf)
      ).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv volume volume :=
    measurePreserving_gpLinearEquiv (exists_iterate_mem_ref hRf)
  have h2 := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (· ∈ R)
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ({i // i ∈ R} → ℂ))
        (MeasurableEquiv.piCongrLeft (fun _ : {i // i ∈ R} => ℂ) (refEquiv hf2 hRf).symm))
      volume volume :=
    (MeasurePreserving.id volume).prod
      (volume_measurePreserving_piCongrLeft (fun _ : {i // i ∈ R} => ℂ) (refEquiv hf2 hRf).symm)
  exact h3.comp (h2.comp h1)

/-- **Change of variables with Jacobian `1`** (source l. 1273): `z ↦ (w, u)` is a measurable
embedding. -/
theorem measurableEmbedding_pairCoords (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) : MeasurableEmbedding (pairCoords f R) := by
  have : pairCoords f R = pairCoordsEquiv hf2 hRf :=
    funext fun z => (pairCoordsEquiv_apply hf2 hRf z).symm
  rw [this]
  exact (pairCoordsEquiv hf2 hRf).measurableEmbedding

/-- **Change of variables with Jacobian `1`** (source l. 1273, "The change of variables
`Z_{2p} ↦ (U_p, W_p)` has Jacobian `1`"): `z ↦ (w, u)` preserves Lebesgue measure. -/
theorem measurePreserving_pairCoords (hf2 : ∀ i, f (f i) = i) (hRf : ∀ i, i ∈ R ↔ f i ∉ R) :
    MeasurePreserving (pairCoords f R) volume volume := by
  have : pairCoords f R = pairCoordsEquiv hf2 hRf :=
    funext fun z => (pairCoordsEquiv_apply hf2 hRf z).symm
  rw [this]
  exact measurePreserving_pairCoordsEquiv hf2 hRf

/-- The involution `f` pairs the representatives with the other vertices, so `|ι| = 2 |R|`. -/
theorem two_mul_card_ref (hf2 : ∀ i, f (f i) = i) (hRf : ∀ i, i ∈ R ↔ f i ∉ R) :
    2 * Fintype.card {i // i ∈ R} = Fintype.card ι := by
  have h1 := Fintype.card_congr (refEquiv hf2 hRf)
  have h2 := Fintype.card_subtype_compl (fun i => i ∈ R)
  have h3 := Fintype.card_subtype_le (fun i => i ∈ R)
  omega

end ChangeOfVariables

/-! ### Integrating the displacements -/

section Fubini

/-- Integral of a product of one-variable functions over a polydisc-like product set. -/
theorem lintegral_pi_set_prod {κ : Type*} [Fintype κ] (s : κ → Set ℂ)
    (hs : ∀ j, MeasurableSet (s j)) (φ : κ → ℂ → ℝ≥0∞) (hφ : ∀ j, Measurable (φ j)) :
    ∫⁻ u in Set.univ.pi s, ∏ j, φ j (u j) = ∏ j, ∫⁻ u in s j, φ j u := by
  have hmeas : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hH : ∀ u : κ → ℂ, (Set.univ.pi s).indicator (fun u => ∏ j, φ j (u j)) u =
      ∏ j, (s j).indicator (φ j) (u j) := by
    intro u
    by_cases hu : u ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hu]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Set.indicator_of_mem (hu j (Set.mem_univ j))]
    · rw [Set.indicator_of_notMem hu]
      rw [Set.mem_univ_pi, not_forall] at hu
      obtain ⟨j, hj⟩ := hu
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)).symm
  rw [← lintegral_indicator hmeas]
  simp_rw [hH]
  have := lintegral_fintype_pi_prod (volume : Measure ℂ)
    (fun j => (s j).indicator (φ j)) (fun j => (hφ j).indicator (hs j))
  rw [volume_pi, this]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [lintegral_indicator (hs j)]

variable {κ : Type*} [Fintype κ] [Nontrivial κ]

/-- Fubini on `(κ → ℂ) × (κ → ℂ)` for the set of pairs `(w, u)` with `w ∈ P` and `u` in the
polydisc `|u_j| ≤ 4 ρ_j(w)` (source l. 1258, 1277). -/
theorem lintegral_polydisc_set (lam : ℝ) (P : Set (κ → ℂ)) (hP : MeasurableSet P)
    (G : (κ → ℂ) × (κ → ℂ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x in {x : (κ → ℂ) × (κ → ℂ) | x.1 ∈ P ∧ ∀ j, ‖x.2 j‖ ≤ 4 * nnRadius lam x.1 j}, G x =
      ∫⁻ w in P, ∫⁻ u in Set.univ.pi (fun j => Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j)),
        G (w, u) := by
  set A : Set ((κ → ℂ) × (κ → ℂ)) :=
    {x | x.1 ∈ P ∧ ∀ j, ‖x.2 j‖ ≤ 4 * nnRadius lam x.1 j} with hA
  have hA2 : MeasurableSet {x : (κ → ℂ) × (κ → ℂ) | ∀ j, ‖x.2 j‖ ≤ 4 * nnRadius lam x.1 j} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le
      (by fun_prop) (((measurable_nnRadius lam j).comp measurable_fst).const_mul 4)
  have hAm : MeasurableSet A := (measurable_fst hP).inter hA2
  have hsec : ∀ w : κ → ℂ, MeasurableSet
      (Set.univ.pi (fun j => Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j))) :=
    fun w => MeasurableSet.univ_pi fun j => Metric.isClosed_closedBall.measurableSet
  rw [← lintegral_indicator hAm, Measure.volume_eq_prod,
    lintegral_prod _ (hG.indicator hAm).aemeasurable, ← lintegral_indicator hP]
  refine lintegral_congr fun w => ?_
  by_cases hw : w ∈ P
  · rw [Set.indicator_of_mem hw, ← lintegral_indicator (hsec w)]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ Set.univ.pi (fun j => Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j))
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem]
      exact ⟨hw, fun j => by simpa using hu j (Set.mem_univ j)⟩
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem]
      rintro ⟨-, h⟩
      exact hu fun j _ => by simpa using h j
  · rw [Set.indicator_of_notMem hw]
    have : ∀ u : κ → ℂ, A.indicator G (w, u) = 0 := fun u =>
      Set.indicator_of_notMem (fun h => hw h.1) _
    simp [this]

end Fubini

/-! ### The displacement reduction -/

section Displacement

variable {ι : Type*} [Fintype ι] [Nontrivial ι] {f : ι → ι} {R : Set ι} [DecidablePred (· ∈ R)]

/-- **Displacement reduction** (source l. 1258, 1271--1277, 1280): integrate first over the pair
displacements and then over one representative of each pair. For measurable pair weights
`Φ_j(u, ρ) ≥ 0` the integral over the cell `Λ^ι ∩ {nnMap key z = f}` of
`∏_{j ∈ R} Φ_j(u_j(z), ρ_j(z))` is at most
`∫_{Λ^R} ∏_{j ∈ R} ∫_{|u| ≤ 4 ρ_j(w)} Φ_j(u, ρ_j(w)) du dw`, where `u_j = z_{f j} - z_j` and
`ρ_j = nnRadius λ (z|_R) j` is the first-neighbour radius of the representative `z_j` among the
representatives. The displacement domain is enlarged to `|u_j| ≤ 4 ρ_j` (which holds on the
cell, `norm_le_four_mul_nnRadius_ref`), and `z ↦ (w, u)` has Jacobian `1`
(`measurePreserving_pairCoords`). -/
theorem lintegral_cell_le_lintegral_ref {N : ℕ} (key : ι ↪ ℕ) (hf2 : ∀ i, f (f i) = i)
    (hRf : ∀ i, i ∈ R ↔ f i ∉ R) [Nontrivial {i // i ∈ R}] (lam : ℝ)
    (Φ : {i // i ∈ R} → ℂ → ℝ → ℝ≥0∞) (hΦ : ∀ j, Measurable fun p : ℂ × ℝ => Φ j p.1 p.2) :
    ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
        ∏ j : {i // i ∈ R}, Φ j (z (f j) - z j) (nnRadius lam (fun l : {i // i ∈ R} => z l) j) ≤
      ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
        ∏ j : {i // i ∈ R}, ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j),
          Φ j u (nnRadius lam w j) := by
  set P : Set ({i // i ∈ R} → ℂ) := Set.univ.pi fun _ => box N with hPdef
  set G : ({i // i ∈ R} → ℂ) × ({i // i ∈ R} → ℂ) → ℝ≥0∞ :=
    fun x => ∏ j, Φ j (x.2 j) (nnRadius lam x.1 j) with hGdef
  have hG : Measurable G := by
    refine Finset.measurable_prod _ fun j _ => ?_
    have h1 : Measurable fun x : ({i // i ∈ R} → ℂ) × ({i // i ∈ R} → ℂ) => x.2 j :=
      (measurable_pi_apply j).comp measurable_snd
    have h2 : Measurable fun x : ({i // i ∈ R} → ℂ) × ({i // i ∈ R} → ℂ) =>
        nnRadius lam x.1 j := (measurable_nnRadius lam j).comp measurable_fst
    exact (hΦ j).comp (h1.prodMk h2)
  have hP : MeasurableSet P := MeasurableSet.univ_pi fun _ => measurableSet_box N
  set A : Set (({i // i ∈ R} → ℂ) × ({i // i ∈ R} → ℂ)) :=
    {x | x.1 ∈ P ∧ ∀ j, ‖x.2 j‖ ≤ 4 * nnRadius lam x.1 j} with hAdef
  have hsub : (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f} ⊆
      pairCoords f R ⁻¹' A := by
    rintro z ⟨hz1, hz2⟩
    exact ⟨fun j _ => hz1 j (Set.mem_univ _), fun j => norm_le_four_mul_nnRadius_ref lam hz2 j⟩
  calc ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
        ∏ j : {i // i ∈ R}, Φ j (z (f j) - z j) (nnRadius lam (fun l : {i // i ∈ R} => z l) j)
      ≤ ∫⁻ z in pairCoords f R ⁻¹' A, G (pairCoords f R z) := lintegral_mono_set hsub
    _ = ∫⁻ x in A, G x :=
        (measurePreserving_pairCoords hf2 hRf).setLIntegral_comp_preimage_emb
          (measurableEmbedding_pairCoords hf2 hRf) G A
    _ = ∫⁻ w in P, ∫⁻ u in Set.univ.pi
          (fun j => Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j)), G (w, u) :=
        lintegral_polydisc_set lam P hP G hG
    _ = _ := by
        refine lintegral_congr fun w => ?_
        exact lintegral_pi_set_prod (fun j => Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j))
          (fun j => Metric.isClosed_closedBall.measurableSet)
          (fun j u => Φ j u (nnRadius lam w j))
          (fun j => (hΦ j).comp (measurable_id.prodMk measurable_const))

end Displacement

end IsolatedReduction

/-! ### `(pred3)`: the bound by an integral over the representatives -/

section Pred3

open IsolatedReduction

open scoped Classical in
/-- **`(pred3)`** (source `pred3`, l. 1322--1333, with the integrand of Proposition 3.9): for
`β ≥ 2` and `C ≥ 0` there is a constant `C' > 0`, depending only on `β` and `C`, such that for every
finite index type `ι`, tie-break key, fixed-point-free involution `f` (the nearest-neighbour graph
of the cell, all components being `2`-cycles) with set of representatives `R`
(`i ∈ R ↔ f i ∉ R`), every `f`-invariant set `S` of pairs assigned the logarithmic term, every
`N` and every `0 < λ ≤ e^{-1}`,
`I(γ) = ∫_{Λ^ι ∩ {nnMap key z = f}} exp(-β E(z)) dz`, with `E = pairAssignedEnergy h3 key lam C S`,
is at most
`(𝒵_β (λ^{2-β} 1_{β>2} + ℓ 1_{β=2}))^p ∫_{Λ^R} ∏_{j ∈ R ∖ S} (1 + C' φ_β(ρ_j))
  ∏_{j ∈ R ∩ S} C' (ℓ^{-1} 1_{β=2} + (λ/ρ_j)^{β-2} 1_{β>2}) dW`,
where `p = |R|` and `ρ_j = nnRadius λ w j` is the first-neighbour radius of the representative
`w_j` among the representatives (`isolatedPhi` is `φ_β`, `isolatedTail` the same-sign factor).
As in the source, only the assigned pair terms enter, not the charges (`S` is an arbitrary set of
`2`-cycles, l. 1225, 1322). -/
theorem lintegral_isolatedCell_le {β : ℝ} (hβ : 2 ≤ β) {C : ℝ} (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (f : ι → ι)
      (R : Set ι) [DecidablePred (· ∈ R)] [Nontrivial {i // i ∈ R}],
      (∀ i, f (f i) = i) → (∀ i, i ∈ R ↔ f i ∉ R) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
      (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N : ℕ) (lam : ℝ), 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
            ENNReal.ofReal (Real.exp (-(β * pairAssignedEnergy h3 key lam C S z))) ≤
          ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^
              Fintype.card {i // i ∈ R} *
            ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
              ∏ j : {i // i ∈ R}, ENNReal.ofReal (if (j : ι) ∈ S then
                C' * isolatedTail β hβ lam (nnRadius lam w j)
                else 1 + C' * isolatedPhi β hβ lam (nnRadius lam w j)) := by
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨Cn, hCn0, hCn⟩ := lintegral_neutralPair_le hβ (C := 18 * β * C) (by positivity)
  obtain ⟨Cs, hCs0, hCs⟩ := lintegral_sameSignPair_le_normalized hβ
  have hC₂ : 0 ≤ Real.exp (2 * β * C) * (3 : ℝ) ^ (2 * β) := by positivity
  refine ⟨max Cn (Real.exp (2 * β * C) * 3 ^ (2 * β) * Cs), lt_max_of_lt_left hCn0, ?_⟩
  intro ι _ _ key f R _ _ hf2 hRf h3 S hS N lam hlam hl1
  have hZ := dipoleConstant_pos β hβ
  have hscale := isolatedScale_pos hβ hlam hl1
  -- Step 1: the integrand bound
  have hcell : MeasurableSet {z : ι → ℂ | nnMap key z = f} := by
    have : {z : ι → ℂ | nnMap key z = f} = ⋂ i, {z | nnMap key z i = f i} := by
      ext z; simp [funext_iff]
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_nnMap_eq key i (f i)
  have hcell' : MeasurableSet ((Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f}) :=
    (MeasurableSet.univ_pi fun _ => measurableSet_box N).inter hcell
  refine (setLIntegral_mono' hcell' fun z hz =>
    ofReal_exp_neg_mul_pairAssignedEnergy_le hz.2 hf2 hRf h3 hS hβ0 hC hlam).trans ?_
  -- Step 2: displacement reduction
  have hg : Measurable (smearedKernel lam) := measurable_smearedKernel lam
  have hd : Measurable (displacementScale lam) := (continuous_displacementScale lam).measurable
  have e1 : Measurable fun p : ℂ × ℝ => Real.exp (β * smearedKernel lam p.1) :=
    Real.measurable_exp.comp ((hg.comp measurable_fst).const_mul β)
  have e2 : Measurable fun p : ℂ × ℝ => displacementScale lam p.1 / p.2 :=
    (hd.comp measurable_fst).div measurable_snd
  have hΦ : ∀ j : {i // i ∈ R}, Measurable fun p : ℂ × ℝ => pairWeight β C lam S j p.1 p.2 := by
    intro j
    by_cases hj : (j : ι) ∈ S
    · simp only [pairWeight, hj, ↓reduceIte]
      exact (ENNReal.measurable_ofReal.comp (e1.mul (e2.pow_const (2 * β)))).const_mul _
    · simp only [pairWeight, hj, ↓reduceIte]
      exact ENNReal.measurable_ofReal.comp
        (e1.mul (Real.measurable_exp.comp ((e2.pow_const 2).const_mul _)))
  refine (lintegral_cell_le_lintegral_ref key hf2 hRf lam
    (fun j u ρ => pairWeight β C lam S j u ρ) hΦ).trans ?_
  -- Step 3: the radial integrals
  have hinner : ∀ (w : {i // i ∈ R} → ℂ) (j : {i // i ∈ R}),
      ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j),
          pairWeight β C lam S j u (nnRadius lam w j) ≤
        ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) *
          ENNReal.ofReal (if (j : ι) ∈ S then
            max Cn (Real.exp (2 * β * C) * 3 ^ (2 * β) * Cs) *
              isolatedTail β hβ lam (nnRadius lam w j)
            else 1 + max Cn (Real.exp (2 * β * C) * 3 ^ (2 * β) * Cs) *
              isolatedPhi β hβ lam (nnRadius lam w j)) := by
    intro w j
    have hρ : lam ≤ nnRadius lam w j := le_nnRadius lam w j
    have hρ0 : 0 < nnRadius lam w j := lt_of_lt_of_le hlam hρ
    by_cases hj : (j : ι) ∈ S
    · simp only [pairWeight, hj, ↓reduceIte]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have h1 := hCs lam (nnRadius lam w j) hlam hl1 hρ
      have ht := isolatedTail_nonneg hβ hlam hρ0
      calc ENNReal.ofReal (Real.exp (2 * β * C) * 3 ^ (2 * β)) * ∫⁻ u in Metric.closedBall (0 : ℂ)
              (4 * nnRadius lam w j), ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
                (displacementScale lam u / nnRadius lam w j) ^ (2 * β))
          ≤ ENNReal.ofReal (Real.exp (2 * β * C) * 3 ^ (2 * β)) * ENNReal.ofReal (Cs *
              dipoleConstant β hβ * isolatedScale β hβ lam *
                isolatedTail β hβ lam (nnRadius lam w j)) := by gcongr
        _ = ENNReal.ofReal (Real.exp (2 * β * C) * 3 ^ (2 * β) * (Cs *
              dipoleConstant β hβ * isolatedScale β hβ lam *
                isolatedTail β hβ lam (nnRadius lam w j))) := (ENNReal.ofReal_mul hC₂).symm
        _ ≤ _ := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hq : 0 ≤ dipoleConstant β hβ * isolatedScale β hβ lam *
                isolatedTail β hβ lam (nnRadius lam w j) := by positivity
            nlinarith [le_max_right Cn (Real.exp (2 * β * C) * 3 ^ (2 * β) * Cs)]
    · simp only [pairWeight, hj, ↓reduceIte]
      have h1 := hCn lam (nnRadius lam w j) hlam hl1 hρ
      have hφ := isolatedPhi_nonneg hβ hlam hρ
      calc _ ≤ ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam *
              (1 + Cn * isolatedPhi β hβ lam (nnRadius lam w j))) := h1
        _ ≤ _ := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have : Cn ≤ max Cn (Real.exp (2 * β * C) * 3 ^ (2 * β) * Cs) := le_max_left _ _
            have hq : 0 ≤ dipoleConstant β hβ * isolatedScale β hβ lam := by positivity
            gcongr
  calc ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
        ∏ j : {i // i ∈ R}, ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j),
          pairWeight β C lam S j u (nnRadius lam w j)
      ≤ ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
          ∏ j : {i // i ∈ R}, (ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) *
            ENNReal.ofReal (if (j : ι) ∈ S then
              max Cn (Real.exp (2 * β * C) * 3 ^ (2 * β) * Cs) *
                isolatedTail β hβ lam (nnRadius lam w j)
              else 1 + max Cn (Real.exp (2 * β * C) * 3 ^ (2 * β) * Cs) *
                isolatedPhi β hβ lam (nnRadius lam w j))) :=
        lintegral_mono fun w => Finset.prod_le_prod fun j _ => hinner w j
    _ = _ := by
        simp_rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
        exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- The reference set `gpRefSet key f` contains exactly one endpoint of each `2`-cycle of a
fixed-point-free involution `f`. -/
theorem gpRefSet_mem_iff {ι : Type*} {key : ι ↪ ℕ} {f : ι → ι} (hf2 : ∀ i, f (f i) = i)
    (hf0 : ∀ i, f i ≠ i) (i : ι) : i ∈ gpRefSet key f ↔ f i ∉ gpRefSet key f :=
  gpRefSet_mem_iff_not_mem (hf2 i) (hf0 i)

open scoped Classical in
/-- **`(pred3)`** with the Gunson--Panta reference set `gpRefSet key f` (the smaller-key endpoint of
each pair) as the set of representatives; see `lintegral_isolatedCell_le`. -/
theorem lintegral_isolatedCell_le_gpRefSet {β : ℝ} (hβ : 2 ≤ β) {C : ℝ} (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (f : ι → ι)
      [Nontrivial {i // i ∈ gpRefSet key f}],
      (∀ i, f (f i) = i) → (∀ i, f i ≠ i) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
      (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N : ℕ) (lam : ℝ), 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
            ENNReal.ofReal (Real.exp (-(β * pairAssignedEnergy h3 key lam C S z))) ≤
          ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^
              Fintype.card {i // i ∈ gpRefSet key f} *
            ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ gpRefSet key f} => box N,
              ∏ j : {i // i ∈ gpRefSet key f}, ENNReal.ofReal (if (j : ι) ∈ S then
                C' * isolatedTail β hβ lam (nnRadius lam w j)
                else 1 + C' * isolatedPhi β hβ lam (nnRadius lam w j)) := by
  obtain ⟨C', hC', h⟩ := lintegral_isolatedCell_le hβ hC
  exact ⟨C', hC', fun ι _ _ key f _ hf2 hf0 h3 S hS N lam hlam hl1 =>
    h ι key f (gpRefSet key f) hf2 (gpRefSet_mem_iff hf2 hf0) h3 S hS N lam hlam hl1⟩

end Pred3

end TwoComponentCoulomb

end
