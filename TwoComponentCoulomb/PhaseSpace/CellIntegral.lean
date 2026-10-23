/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Gibbs.Basic
public import TwoComponentCoulomb.NearestNeighbor.General
public import TwoComponentCoulomb.PhaseSpace.GunsonPanta
public import TwoComponentCoulomb.PhaseSpace.Packing

/-!
# Integrals over a nearest-neighbour cell in Gunson--Panta variables

Source l. 781–820 (Lemma 3.4, Steps 1 and 2). Fix a finite index type `ι`, a tie-break key
`key`, a self-map `f` (the nearest-neighbour map of the cell) and a set `R` of reference
vertices such that every `f`-orbit reaches `R`. The cell is
`Λ^ι ∩ {z | nnMap key z = f}` (`Λ = box N`).

On the cell the Gunson--Panta map `GP` (`TwoComponentCoulomb.gpLinearEquiv`) takes values in the
set `B` of the source (l. 795–798): `u_r ∈ Λ` for `r ∈ R` and `∑_{i ∉ R} |u_i|² ≤ 36 N / π`
(packing, l. 799). Since `GP` has determinant `1`, the integral of any `F ≥ 0` over the cell is
at most the integral of `F ∘ GP⁻¹` over `B` (`lintegral_cell_le`). Integrating out the reference
coordinates (each gives the area `N` of `Λ`) reduces the integral to the ball integral of the
non-reference coordinates, to which the polar reduction of `PhaseSpace/RadialSimplex.lean` applies.

## Main results

* `TwoComponentCoulomb.gpMap_mem_of_mem_cell`: the image of the cell lies in `B`.
* `TwoComponentCoulomb.lintegral_cell_le`: `∫⁻_{cell} F ≤ ∫⁻_B F ∘ GP⁻¹`.
* `TwoComponentCoulomb.lintegral_gpBall_comp`: the reference coordinates integrate to `N^|R|`.
* `TwoComponentCoulomb.lintegral_cell_le_prod`: the bound by `N^|R|` times the ball integral
  when `F ∘ GP⁻¹` is a product of functions of the non-reference coordinates.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

variable {ι : Type*} [Fintype ι]

/-! ### The image of a cell -/

/-- On the cell `Λ^ι ∩ {nnMap key z = f}` the Gunson--Panta map takes values in the set `B` of the
source (l. 795–799): reference coordinates stay in `Λ` and the non-reference coordinates
satisfy `∑_{i ∉ R} |u_i|² ≤ 36 N / π` by the packing bound. -/
theorem gpMap_mem_of_mem_cell [Nontrivial ι] {N : ℕ} (key : ι ↪ ℕ) {f : ι → ι} (R : Set ι)
    [DecidablePred (· ∈ R)] {z : ι → ℂ} (hz : z ∈ Set.univ.pi fun _ : ι => box N)
    (hf : nnMap key z = f) :
    (∀ r ∈ R, gpMap f R z r ∈ box N) ∧
      ∑ i ∈ Finset.univ.filter (· ∉ R), ‖gpMap f R z i‖ ^ 2 ≤ 36 * N / Real.pi := by
  have hz' : ∀ i, z i ∈ box N := fun i => hz i (Set.mem_univ i)
  refine ⟨fun r hr => by rw [gpMap_apply_of_mem z hr]; exact hz' r, ?_⟩
  have hpack := sum_sq_le_of_separated z (fun i => ‖z i - z (nnMap key z i)‖) hz'
    (fun _ => norm_nonneg _) (fun i => norm_sub_le_of_mem_box (hz' i) (hz' _))
    fun i j hij => norm_sub_nnMap_le key z hij.symm
  refine le_trans ?_ hpack
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => by positivity))
  rw [gpMap_apply_of_not_mem z (Finset.mem_filter.1 hi).2, hf]

/-! ### Transfer to Gunson--Panta variables -/

/-- **Lemma 3.4, Steps 1--2** (source l. 785–799): for every nonnegative function `F`, the
integral of `F` over the nearest-neighbour cell `Λ^ι ∩ {nnMap key z = f}` is at most the integral
of `F ∘ GP⁻¹` over the set `B` (reference coordinates in `Λ`, non-reference coordinates in the ball
`∑ |u_i|² ≤ 36 N / π`). No Jacobian factor appears since `GP` has determinant `1`. -/
theorem lintegral_cell_le [Nontrivial ι] {N : ℕ} (key : ι ↪ ℕ) {f : ι → ι} (R : Set ι)
    [DecidablePred (· ∈ R)] (hR : ∀ i, ∃ n, f^[n] i ∈ R) (F : (ι → ℂ) → ℝ≥0∞) :
    ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f}, F z ≤
      ∫⁻ u in {u : ι → ℂ | (∀ r ∈ R, u r ∈ box N) ∧
          ∑ i ∈ Finset.univ.filter (· ∉ R), ‖u i‖ ^ 2 ≤ 36 * N / Real.pi},
        F ((gpLinearEquiv f R hR).symm u) := by
  set B : Set (ι → ℂ) := {u : ι → ℂ | (∀ r ∈ R, u r ∈ box N) ∧
      ∑ i ∈ Finset.univ.filter (· ∉ R), ‖u i‖ ^ 2 ≤ 36 * N / Real.pi} with hB
  have hsub : ((Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f}) ⊆
      gpLinearEquiv f R hR ⁻¹' B :=
    fun z hz => gpMap_mem_of_mem_cell key R hz.1 hz.2
  refine (lintegral_mono_set hsub).trans (le_of_eq ?_)
  have h := (measurePreserving_gpLinearEquiv hR).setLIntegral_comp_preimage_emb
    (measurableEmbedding_gpLinearEquiv hR) (fun u => F ((gpLinearEquiv f R hR).symm u)) B
  simpa only [LinearEquiv.symm_apply_apply] using h

/-! ### Integrating out the reference coordinates -/

/-- **Reference coordinates** (source l. 802, "integrating a reference point in each connected
component in the box `Λ` of volume `N`"): for an integrand depending only on the non-reference
coordinates, the integral over `B = {u_r ∈ Λ (r ∈ R), ∑_{i ∉ R} |u_i|² ≤ s}` is `N^|R|` times the
integral over the ball `{v : {i // i ∉ R} → ℂ | ∑ |v_i|² ≤ s}`. -/
theorem lintegral_gpBall_comp (N : ℕ) (R : Set ι) [DecidablePred (· ∈ R)] (s : ℝ)
    (H : ({i // i ∉ R} → ℂ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ u in {u : ι → ℂ | (∀ r ∈ R, u r ∈ box N) ∧
        ∑ i ∈ Finset.univ.filter (· ∉ R), ‖u i‖ ^ 2 ≤ s}, H (fun i : {i // i ∉ R} => u i) =
      (N : ℝ≥0∞) ^ Fintype.card {i // i ∈ R} *
        ∫⁻ v in {v : {i // i ∉ R} → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s}, H v := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (· ∈ R) with he
  have hmp := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (· ∈ R)
  set Pset : Set ({i // i ∈ R} → ℂ) := Set.univ.pi fun _ => box N with hPset
  set S : Set ({i // i ∉ R} → ℂ) := {v | ∑ i, ‖v i‖ ^ 2 ≤ s} with hS
  have hpre : {u : ι → ℂ | (∀ r ∈ R, u r ∈ box N) ∧
      ∑ i ∈ Finset.univ.filter (· ∉ R), ‖u i‖ ^ 2 ≤ s} = e ⁻¹' (Pset ×ˢ S) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, hPset, hS, Set.mem_univ_pi]
    refine and_congr ?_ ?_
    · exact ⟨fun h r => h r r.2, fun h r hr => h ⟨r, hr⟩⟩
    · rw [Finset.sum_subtype (Finset.univ.filter (· ∉ R)) (p := (· ∉ R)) (by simp)]
      rfl
  rw [hpre]
  have h := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding (fun x => H x.2)
    (Pset ×ˢ S)
  refine h.trans ?_
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod (fun x => H x.2) (hH.comp measurable_snd).aemeasurable]
  dsimp only
  rw [lintegral_const, Measure.restrict_apply_univ, hPset, volume_pi_pi]
  simp only [volume_box, Finset.prod_const, Finset.card_univ]
  exact mul_comm _ _

/-! ### Cell integrals of functions of the non-reference coordinates -/

/-- **Lemma 3.4, Steps 1--2** (source l. 785–807): if `F ∘ GP⁻¹` depends only on the
non-reference coordinates `(u_i)_{i ∉ R}` through a measurable `H`, then the cell integral of `F`
is at most `N^|R|` times the integral of `H` over the ball `∑ |v_i|² ≤ 36 N / π`. -/
theorem lintegral_cell_le_comp [Nontrivial ι] {N : ℕ} (key : ι ↪ ℕ) {f : ι → ι} (R : Set ι)
    [DecidablePred (· ∈ R)] (hR : ∀ i, ∃ n, f^[n] i ∈ R) (F : (ι → ℂ) → ℝ≥0∞)
    (H : ({i // i ∉ R} → ℂ) → ℝ≥0∞) (hH : Measurable H)
    (hFH : ∀ u, F ((gpLinearEquiv f R hR).symm u) = H (fun i : {i // i ∉ R} => u i)) :
    ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f}, F z ≤
      (N : ℝ≥0∞) ^ Fintype.card {i // i ∈ R} *
        ∫⁻ v in {v : {i // i ∉ R} → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ 36 * N / Real.pi}, H v := by
  refine (lintegral_cell_le key R hR F).trans (le_of_eq ?_)
  simp only [hFH]
  exact lintegral_gpBall_comp N R _ H hH

/-- **Lemma 3.4, Step 2** (source l. 802–807, product form): if
`F (GP⁻¹ u) = ∏_{i ∉ R} G_i(u_i)` with measurable `G_i ≥ 0`, then the cell integral of `F` is at
most `N^|R|` times the integral of `∏_{i ∉ R} G_i(v_i)` over the ball `∑ |v_i|² ≤ 36 N / π`. -/
theorem lintegral_cell_le_prod [Nontrivial ι] {N : ℕ} (key : ι ↪ ℕ) {f : ι → ι} (R : Set ι)
    [DecidablePred (· ∈ R)] (hR : ∀ i, ∃ n, f^[n] i ∈ R) (F : (ι → ℂ) → ℝ≥0∞)
    (G : {i // i ∉ R} → ℂ → ℝ≥0∞) (hG : ∀ i, Measurable (G i))
    (hFG : ∀ u, F ((gpLinearEquiv f R hR).symm u) = ∏ i : {i // i ∉ R}, G i (u i)) :
    ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f}, F z ≤
      (N : ℝ≥0∞) ^ Fintype.card {i // i ∈ R} *
        ∫⁻ v in {v : {i // i ∉ R} → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ 36 * N / Real.pi},
          ∏ i : {i // i ∉ R}, G i (v i) :=
  lintegral_cell_le_comp key R hR F (fun v => ∏ i : {i // i ∉ R}, G i (v i))
    (Finset.measurable_prod _ fun i _ => (hG i).comp (measurable_pi_apply i)) hFG

end TwoComponentCoulomb

end
