/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Gibbs.Basic
public import TwoComponentCoulomb.NearestNeighbor.Radius
public import TwoComponentCoulomb.PhaseSpace.GunsonPanta
public import TwoComponentCoulomb.PhaseSpace.Packing
public import TwoComponentCoulomb.UpperBound.AuxIntegrationVolume
public import TwoComponentCoulomb.UpperBound.RestrictedGraph
import TwoComponentCoulomb.Integrals.PiProduct

/-!
# Proposition 3.6, Step 2: integration over one restricted graph

Source: proof of Proposition 3.6 (`prop:auxk`), l. 1035–1062 (Step 2,
"integration"), in the weighted generality of ruling R12c: the factors
`r̃₁^{-β/2} (1 + log (r̃₁/λ))^δ (1 + |log r̃₁|)^{δ'}` of the source are replaced by a measurable
radial weight `w` evaluated at the first-neighbour radius `r̃₁(z_i) = r(z_i) ∨ λ`
(`TwoComponentCoulomb.nnRadius`).

Fix `p` points `z₁, …, z_p` in the box `Λ`, the selected vertices `i < k` and a restricted graph
`g ∈ D(k₀, k₁)` (`TwoComponentCoulomb.restrictedGraphs`). On the cell `Λ^p ∩ {γ'_p = g}` we have
`r̃₁(z_i) = max (|z_i - z_{g i}| / 4, λ)` for `i < k`, which depends only on the coordinates of
the `m = k + k₁` vertices of the nontrivial components. The proof follows the source:

* *Trivial vertices* (l. 1035–1041, `UpperBound/AuxIntegrationVolume.lean`). Fubini over the `p - m` other
  vertices: each avoids the balls `B(z_i, |z_i - z_{g i}|)`, whose halves are disjoint and meet `Λ`
  in area `≥ |z_i - z_{g i}|²/16`, so the available volume is at most `N - ∑ r(z_i)²`; with
  `p - m ≥ p - 2k` and `N ≤ 2p` this contributes at most `e^{2k} N^{p-m} e^{-∑ r(z_i)²/4}`
  (`AuxIntegration.volume_section_le`, `AuxIntegration.lintegral_cell_le_fubini`).
* *Gunson--Panta variables* (l. 1043). On the nontrivial vertices `NtV g` the map
  `v ↦ g v` (`stepNt`) and the reference set `R` (`refSet`: the roots and the first vertex of each
  `2`-cycle of `g`) satisfy that every orbit reaches `R`
  (`AuxIntegration.exists_iterate_stepNt_mem_refSet`), so the Gunson--Panta map is measure
  preserving. The reference coordinates are integrated over `Λ` (`N^{k₀+k₁}`) and the
  `k - k₀` displacement coordinates over `ℂ`; a `2`-cycle has a single displacement on which both
  endpoints depend (`AuxIntegration.norm_sub_symm_eq`, `AuxIntegration.sigma`), which gives
  the weight `w²` there (`AuxIntegration.setLIntegral_disp_le`).

## Main results

* `TwoComponentCoulomb.AuxIntegration.lintegral_cellSet_le`: the bound with the explicit
  constants `C = e²`, `c = 1/64`.
* `TwoComponentCoulomb.lintegral_restrictedNnMap_eq_le`: the same, stated with existentially
  quantified absolute constants `C, c > 0`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

namespace AuxIntegration

/-! ### Integrals over a reference box in Gunson--Panta variables -/

section GunsonPanta

variable {κ : Type*} [Fintype κ] (f : κ → κ) (R : Set κ) [DecidablePred (· ∈ R)]

/-- **Reference coordinates** (source l. 1043: "We integrate the reference points in `Λ` and
extend each integral over a variable `u_j` to `ℝ²`"): if
`Ψ (GP⁻¹ u) = ∏_{v ∉ R} G_v (u_v)`, then the integral of `Ψ` over the set where all reference
coordinates lie in `Λ` is `N^{|R|} ∏_{v ∉ R} ∫ G_v`. -/
theorem setLIntegral_ref_eq (hR : ∀ v, ∃ n, f^[n] v ∈ R) (N : ℕ) (Ψ : (κ → ℂ) → ℝ≥0∞)
    (G : κ → ℂ → ℝ≥0∞) (hG : ∀ v, Measurable (G v))
    (hΨ : ∀ u : κ → ℂ, Ψ ((gpLinearEquiv f R hR).symm u) =
      ∏ v ∈ Finset.univ.filter (· ∉ R), G v (u v)) :
    ∫⁻ x in {x : κ → ℂ | ∀ r ∈ R, x r ∈ box N}, Ψ x =
      (N : ℝ≥0∞) ^ (Finset.univ.filter (· ∈ R)).card *
        ∏ v ∈ Finset.univ.filter (· ∉ R), ∫⁻ s, G v s := by
  set S : Set (κ → ℂ) := {u : κ → ℂ | ∀ r ∈ R, u r ∈ box N} with hS
  have hpre : (gpLinearEquiv f R hR) ⁻¹' S = S := by
    ext x
    simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq, gpLinearEquiv_apply]
    refine forall₂_congr fun r hr => ?_
    rw [gpMap_apply_of_mem x hr]
  rw [← hpre]
  have h := (measurePreserving_gpLinearEquiv hR).setLIntegral_comp_preimage_emb
    (measurableEmbedding_gpLinearEquiv hR) (fun u => Ψ ((gpLinearEquiv f R hR).symm u)) S
  simp only [LinearEquiv.symm_apply_apply] at h
  rw [h]
  -- the integrand is a product of one-variable functions
  set H : κ → ℂ → ℝ≥0∞ := fun v s => if v ∈ R then (box N).indicator (fun _ => 1) s else G v s
    with hH
  have hHm : ∀ v, Measurable (H v) := by
    intro v
    by_cases hv : v ∈ R
    · simp only [hH, hv, ite_true]
      exact measurable_const.indicator (measurableSet_box N)
    · simp only [hH, hv, ite_false]
      exact hG v
  have hSmeas : MeasurableSet S := by
    have : S = ⋂ r ∈ {r | r ∈ R}, (fun u : κ → ℂ => u r) ⁻¹' (box N) := by
      ext u; simp [hS]
    rw [this]
    exact MeasurableSet.biInter (Set.toFinite _).countable fun r _ =>
      (measurableSet_box N).preimage (measurable_pi_apply r)
  have hind : ∀ u : κ → ℂ, S.indicator (fun u => Ψ ((gpLinearEquiv f R hR).symm u)) u =
      ∏ v, H v (u v) := by
    intro u
    rw [Finset.prod_ite]
    by_cases hu : u ∈ S
    · have h1 : ∏ x ∈ Finset.univ.filter (· ∈ R), (box N).indicator (fun _ => (1 : ℝ≥0∞)) (u x) =
          1 := by
        refine Finset.prod_eq_one fun r hr => ?_
        have hrR : r ∈ R := (Finset.mem_filter.1 hr).2
        rw [Set.indicator_of_mem (hu r hrR)]
      rw [Set.indicator_of_mem hu, hΨ, h1, one_mul]
    · rw [Set.indicator_of_notMem hu]
      simp only [hS, Set.mem_ofPred_eq, not_forall] at hu
      obtain ⟨r, hrR, hr⟩ := hu
      rw [Finset.prod_eq_zero (i := r) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hrR⟩)
        (Set.indicator_of_notMem hr _), zero_mul]
  rw [← lintegral_indicator hSmeas]
  simp_rw [hind]
  have := lintegral_fintype_pi_prod volume H hHm
  rw [show (volume : Measure (κ → ℂ)) = Measure.pi fun _ => volume from rfl, this,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ R)]
  congr 1
  · rw [Finset.prod_congr rfl (g := fun _ => (N : ℝ≥0∞))]
    · simp
    · intro v hv
      have hvR : v ∈ R := (Finset.mem_filter.1 hv).2
      simp only [hH, hvR, ite_true]
      rw [lintegral_indicator_const (measurableSet_box N), volume_box, one_mul]
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hvR : v ∉ R := (Finset.mem_filter.1 hv).2
    simp only [hH, hvR, ite_false]

end GunsonPanta

/-! ### The nontrivial components of a restricted graph -/

section Setup

open scoped Classical

variable {p k : ℕ} (hk : k ≤ p) (g : Fin k → Fin p)

/-- A vertex of a nontrivial component of the restricted graph of `g` (source l. 1030: there are
`m = k + k₁` vertices "in its nontrivial connected components"): a selected vertex `v < k`, or a
root, i.e. a vertex which is the target of a selected vertex. -/
def IsNtVertex (v : Fin p) : Prop := (v : ℕ) < k ∨ ∃ i, g i = v

/-- The type of the vertices of the nontrivial components of the restricted graph of `g`. -/
abbrev NtV : Type := {v : Fin p // IsNtVertex g v}

/-- The map `v ↦ g v` on selected vertices and the identity elsewhere: the restricted graph of
`g` as a self-map of `Fin p`. -/
def stepV (v : Fin p) : Fin p := if h : (v : ℕ) < k then g ⟨v, h⟩ else v

theorem stepV_castLE (i : Fin k) : stepV g (Fin.castLE hk i) = g i := by
  simp [stepV]

theorem isNtVertex_stepV {v : Fin p} (hv : IsNtVertex g v) : IsNtVertex g (stepV g v) := by
  by_cases h : (v : ℕ) < k
  · exact Or.inr ⟨⟨v, h⟩, by simp [stepV, h]⟩
  · simpa [stepV, h] using hv

/-- The restricted graph as a self-map of its nontrivial vertices. -/
def stepNt (v : NtV g) : NtV g := ⟨stepV g v.1, isNtVertex_stepV g v.2⟩

/-- The selected vertex `i < k` as a vertex of a nontrivial component. -/
def selV (i : Fin k) : NtV g := ⟨Fin.castLE hk i, Or.inl i.2⟩

/-- The target `g i` of the selected vertex `i` as a vertex of a nontrivial component. -/
def tgtV (i : Fin k) : NtV g := ⟨g i, Or.inr ⟨i, rfl⟩⟩

theorem stepNt_selV (i : Fin k) : stepNt g (selV hk g i) = tgtV g i :=
  Subtype.ext (stepV_castLE hk g i)

theorem selV_injective : Function.Injective (selV hk g) := fun _ _ h =>
  Fin.castLE_injective hk (congrArg Subtype.val h)

theorem exists_selV_of_lt (v : NtV g) (h : (v.1 : ℕ) < k) : ∃ i, selV hk g i = v :=
  ⟨⟨v.1, h⟩, Subtype.ext (Fin.ext rfl)⟩

include hk in
theorem card_ntV_le : Fintype.card (NtV g) ≤ 2 * k := by
  have hsub : (Finset.univ.filter (IsNtVertex g)) ⊆
      (Finset.univ : Finset (Fin k)).image (Fin.castLE hk) ∪
        (Finset.univ : Finset (Fin k)).image g := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rcases hv.2 with h | ⟨i, hi⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨⟨v, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)
  rw [Fintype.card_subtype]
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := Fin.castLE hk)
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := g)
  simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
  omega

theorem card_ntV_le_p : Fintype.card (NtV g) ≤ p := by
  simpa using Fintype.card_subtype_le (IsNtVertex g)

/-- The *reference set* of the Gunson--Panta change of variables on the nontrivial components
(source l. 645–662, 1043): the roots (vertices `≥ k`) and the first vertex of each `2`-cycle
inside the selected set (the source retains the larger-indexed vertex; either choice gives a
triangular map with determinant `1`). -/
def refSet : Set (NtV g) :=
  {v | k ≤ (v.1 : ℕ) ∨ ∃ e ∈ twoCyclesIn g, v.1 = Fin.castLE hk e.1}

theorem selV_mem_refSet_iff (i : Fin k) :
    selV hk g i ∈ refSet hk g ↔ ∃ e ∈ twoCyclesIn g, e.1 = i := by
  simp only [refSet, selV, Set.mem_ofPred_eq]
  constructor
  · rintro (h | ⟨e, he, h⟩)
    · exact absurd i.2 (not_lt.2 (by simpa using h))
    · exact ⟨e, he, (Fin.castLE_injective hk h).symm⟩
  · rintro ⟨e, he, rfl⟩
    exact Or.inr ⟨e, he, rfl⟩

theorem mem_refSet_of_le {v : NtV g} (h : k ≤ (v.1 : ℕ)) : v ∈ refSet hk g := Or.inl h

theorem lt_of_notMem_refSet {v : NtV g} (h : v ∉ refSet hk g) : (v.1 : ℕ) < k :=
  not_le.1 fun h' => h (Or.inl h')

/-! #### Orbits reach the reference set -/

theorem val_iterate_stepNt (v : NtV g) (n : ℕ) :
    (((stepNt g)^[n] v : NtV g) : Fin p) = (stepV g)^[n] v.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact congrArg (stepV g) ih

theorem exists_iterate_stepV_of_reflTransGen {a b : Fin p}
    (h : Relation.ReflTransGen (restrictedEdge g) a b) : ∃ n, (stepV g)^[n] a = b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨hlt, rfl⟩ := hbc
    exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]; simp [stepV, hlt]⟩

include hk in
/-- **Every orbit reaches the reference set** (source l. 990–993, 1043): in an admissible
restricted graph, every forward path ends at a root or at a `2`-cycle inside the selected set,
which contains exactly one reference vertex. -/
theorem exists_iterate_stepNt_mem_refSet (hg : IsAdmissibleRestriction g) (v : NtV g) :
    ∃ n, (stepNt g)^[n] v ∈ refSet hk g := by
  obtain ⟨w, hw, hw'⟩ := exists_reach_root_or_twoCycle hg v.1
  obtain ⟨n, hn⟩ := exists_iterate_stepV_of_reflTransGen g hw
  have hval := val_iterate_stepNt g v n
  rw [hn] at hval
  rcases hw' with hwk | ⟨x, hwx, hxw⟩
  · exact ⟨n, mem_refSet_of_le hk g (by rw [hval]; exact hwk)⟩
  · obtain ⟨hwlt, hgw⟩ := hwx
    obtain ⟨hxlt, hgx⟩ := hxw
    set a : Fin k := ⟨w, hwlt⟩ with ha
    set b : Fin k := ⟨x, hxlt⟩ with hb
    have hga : (g a : ℕ) = x := by rw [ha, hgw]
    have hgb : (g b : ℕ) = w := by rw [hb, hgx]
    have hne : a ≠ b := by
      intro h
      have := hg.1 a
      rw [hga, h] at this
      exact this rfl
    rcases lt_or_gt_of_ne hne with hab | hab
    · refine ⟨n, Or.inr ⟨(a, b), mem_twoCyclesIn.2 ⟨hab, hga, hgb⟩, ?_⟩⟩
      show _ = Fin.castLE hk a
      rw [hval]
      exact Fin.ext rfl
    · refine ⟨n + 1, Or.inr ⟨(b, a), mem_twoCyclesIn.2 ⟨hab, hgb, hga⟩, ?_⟩⟩
      rw [Function.iterate_succ_apply']
      show stepV g ((stepNt g)^[n] v).1 = Fin.castLE hk b
      rw [hval]
      have hwa : w = Fin.castLE hk a := Fin.ext rfl
      rw [hwa, stepV_castLE hk g a, hgw]
      exact Fin.ext rfl

/-! #### Counting the non-reference vertices -/

include hk in
theorem card_notMem_refSet :
    (Finset.univ.filter (· ∉ refSet hk g)).card = k - (twoCyclesIn g).card := by
  have h1 : (Finset.univ.filter (· ∉ refSet hk g)) =
      (Finset.univ.filter fun i : Fin k => selV hk g i ∉ refSet hk g).image (selV hk g) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hv
      obtain ⟨i, hi⟩ := exists_selV_of_lt hk g v (lt_of_notMem_refSet hk g hv)
      exact ⟨i, hi ▸ hv, hi⟩
    · rintro ⟨i, hi, rfl⟩
      exact hi
  have h2 : (Finset.univ.filter fun i : Fin k => selV hk g i ∈ refSet hk g) =
      (twoCyclesIn g).image Prod.fst := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      selV_mem_refSet_iff]
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (fun i : Fin k => selV hk g i ∈ refSet hk g)
  rw [h2, Finset.card_image_of_injOn fst_injOn_twoCyclesIn, Finset.card_univ,
    Fintype.card_fin] at h3
  rw [h1, Finset.card_image_of_injective _ (selV_injective hk g)]
  omega

/-! #### The displacement attached to a selected vertex -/

/-- The vertex of `κ ∖ R` whose Gunson--Panta coordinate is the displacement `z_i - z_{g i}` of the
selected vertex `i` (up to sign): `i` itself if `i` is not a reference vertex, and its partner
`g i` in the `2`-cycle otherwise (source l. 1043: for a `2`-cycle both endpoints have the same
displacement). -/
noncomputable def sigma (i : Fin k) : NtV g :=
  if selV hk g i ∈ refSet hk g then tgtV g i else selV hk g i

/-- For a first vertex `i` of a `2`-cycle `(i, j)`, the target `g i` is the second vertex `j`. -/
theorem tgtV_eq_selV_of_mem_twoCyclesIn {e : Fin k × Fin k} (he : e ∈ twoCyclesIn g) :
    tgtV g e.1 = selV hk g e.2 :=
  Subtype.ext (Fin.ext (mem_twoCyclesIn.1 he).2.1)

theorem stepNt_selV_of_mem_twoCyclesIn {e : Fin k × Fin k} (he : e ∈ twoCyclesIn g) :
    stepNt g (selV hk g e.2) = selV hk g e.1 :=
  Subtype.ext (by
    rw [stepNt, selV]
    simp only
    rw [stepV_castLE hk g]
    exact Fin.ext (mem_twoCyclesIn.1 he).2.2)

theorem selV_snd_notMem_refSet {e : Fin k × Fin k} (he : e ∈ twoCyclesIn g) :
    selV hk g e.2 ∉ refSet hk g := by
  intro h
  obtain ⟨e', he', h'⟩ := (selV_mem_refSet_iff hk g _).1 h
  exact fst_ne_snd_of_mem_twoCyclesIn he' he h'

include hk in
theorem sigma_notMem_refSet (i : Fin k) : sigma hk g i ∉ refSet hk g := by
  unfold sigma
  by_cases h : selV hk g i ∈ refSet hk g
  · rw [ite_eq_left h]
    obtain ⟨e, he, rfl⟩ := (selV_mem_refSet_iff hk g i).1 h
    rw [tgtV_eq_selV_of_mem_twoCyclesIn hk g he]
    exact selV_snd_notMem_refSet hk g he
  · rw [ite_eq_right h]
    exact h

include hk in
theorem one_le_card_fiber {v : NtV g} (hv : v ∉ refSet hk g) :
    1 ≤ (Finset.univ.filter fun i : Fin k => sigma hk g i = v).card := by
  obtain ⟨i, rfl⟩ := exists_selV_of_lt hk g v (lt_of_notMem_refSet hk g hv)
  refine Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
  simp [sigma, hv]

include hk in
theorem card_fiber_le_two (v : NtV g) :
    (Finset.univ.filter fun i : Fin k => sigma hk g i = v).card ≤ 2 := by
  set Fa : Finset (Fin k) := Finset.univ.filter fun i => selV hk g i ∉ refSet hk g ∧ selV hk g i = v
    with hFa
  set Fb : Finset (Fin k) := Finset.univ.filter fun i => selV hk g i ∈ refSet hk g ∧ tgtV g i = v
    with hFb
  have hsub : (Finset.univ.filter fun i : Fin k => sigma hk g i = v) ⊆ Fa ∪ Fb := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_union, hFa, hFb, Finset.mem_filter, Finset.mem_filter]
    by_cases h : selV hk g i ∈ refSet hk g
    · right
      refine ⟨Finset.mem_univ _, h, ?_⟩
      simpa [sigma, h] using hi.2
    · left
      refine ⟨Finset.mem_univ _, h, ?_⟩
      simpa [sigma, h] using hi.2
  have hFa1 : Fa.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    rw [hFa, Finset.mem_filter] at hi hj
    exact selV_injective hk g (hi.2.2.trans hj.2.2.symm)
  have hFb1 : Fb.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    rw [hFb, Finset.mem_filter] at hi hj
    obtain ⟨e, he, rfl⟩ := (selV_mem_refSet_iff hk g i).1 hi.2.1
    obtain ⟨e', he', rfl⟩ := (selV_mem_refSet_iff hk g j).1 hj.2.1
    have h1 := tgtV_eq_selV_of_mem_twoCyclesIn hk g he
    have h2 := tgtV_eq_selV_of_mem_twoCyclesIn hk g he'
    have h3 : selV hk g e.2 = selV hk g e'.2 := by rw [← h1, ← h2, hi.2.2, hj.2.2]
    have h4 := selV_injective hk g h3
    have := snd_injOn_twoCyclesIn (g := g) (Finset.mem_coe.2 he) (Finset.mem_coe.2 he') h4
    rw [this]
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

include hk in
theorem card_fiber_eq_zero {v : NtV g} (hv : v ∈ refSet hk g) :
    (Finset.univ.filter fun i : Fin k => sigma hk g i = v).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ h
  exact sigma_notMem_refSet hk g i (h ▸ hv)

theorem sum_card_fiber :
    ∑ v : NtV g, (Finset.univ.filter fun i : Fin k => sigma hk g i = v).card = k := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin k)))
    (t := (Finset.univ : Finset (NtV g))) (f := sigma hk g) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

/-! #### Displacements in Gunson--Panta coordinates -/

section Displacement

variable (hg : IsAdmissibleRestriction g)

include hk hg in
/-- **Displacements** (source l. 1043): in the Gunson--Panta coordinates `u = GP z` on the
nontrivial components, the displacement `z_i - z_{g i}` of the selected vertex `i` has the same norm
as the coordinate `u_{σ i}` of `σ i ∉ R`. For a `2`-cycle both endpoints have the same
displacement. -/
theorem norm_sub_symm_eq (u : NtV g → ℂ) (i : Fin k) :
    ‖(gpLinearEquiv (stepNt g) (refSet hk g) (exists_iterate_stepNt_mem_refSet hk g hg)).symm u
        (selV hk g i) -
      (gpLinearEquiv (stepNt g) (refSet hk g) (exists_iterate_stepNt_mem_refSet hk g hg)).symm u
        (tgtV g i)‖ = ‖u (sigma hk g i)‖ := by
  set hR := exists_iterate_stepNt_mem_refSet hk g hg with hhR
  set x := (gpLinearEquiv (stepNt g) (refSet hk g) hR).symm u with hx
  by_cases h : selV hk g i ∈ refSet hk g
  · obtain ⟨e, he, rfl⟩ := (selV_mem_refSet_iff hk g i).1 h
    have ht := tgtV_eq_selV_of_mem_twoCyclesIn hk g he
    have hnot := selV_snd_notMem_refSet hk g he
    have hxt := gpLinearEquiv_symm_apply_of_not_mem hR u hnot
    rw [stepNt_selV_of_mem_twoCyclesIn hk g he] at hxt
    rw [ht, hx]
    have hs : sigma hk g e.1 = selV hk g e.2 := by
      rw [sigma, ite_eq_left h, ht]
    rw [hs, hxt, ← hx]
    rw [show x (selV hk g e.1) - (u (selV hk g e.2) + x (selV hk g e.1)) = -u (selV hk g e.2) by
      ring, norm_neg]
  · have hxs := gpLinearEquiv_symm_apply_of_not_mem hR u h
    rw [stepNt_selV] at hxs
    rw [sigma, ite_eq_right h, hx, hxs]
    rw [add_sub_cancel_right]

end Displacement

/-! #### Integration in Gunson--Panta coordinates -/

section Integration

variable (hg : IsAdmissibleRestriction g)

include hk hg in
/-- **Source l. 1043–1050, the displacement integrals.** After the Gunson--Panta change of
variables on the nontrivial components, the reference points (`|R| = k₀ + k₁` of them) integrate to
`N^{|R|}`, and the `k - k₀` displacement coordinates give `k₀` cycle integrals and `k - 2 k₀`
non-cycle integrals. -/
theorem setLIntegral_disp_le (N : ℕ) (lam : ℝ) {w : ℝ → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ x in {x : NtV g → ℂ | ∀ r ∈ refSet hk g, x r ∈ box N},
        ∏ i : Fin k, dispWeight lam w ‖x (selV hk g i) - x (tgtV g i)‖ ≤
      (N : ℝ≥0∞) ^ (Finset.univ.filter (· ∈ refSet hk g)).card *
        (cycleIntegral lam w ^ (twoCyclesIn g).card *
          noncycleIntegral lam w ^ (k - 2 * (twoCyclesIn g).card)) := by
  set hR := exists_iterate_stepNt_mem_refSet hk g hg with hhR
  set m : NtV g → ℕ := fun v => (Finset.univ.filter fun i : Fin k => sigma hk g i = v).card
    with hm
  set T : Finset (NtV g) := Finset.univ.filter (· ∉ refSet hk g) with hT
  have hΨ : ∀ u : NtV g → ℂ,
      ∏ i : Fin k, dispWeight lam w ‖(gpLinearEquiv (stepNt g) (refSet hk g) hR).symm u
          (selV hk g i) - (gpLinearEquiv (stepNt g) (refSet hk g) hR).symm u (tgtV g i)‖ =
        ∏ v ∈ T, (fun (v : NtV g) (s : ℂ) => dispWeight lam w ‖s‖ ^ m v) v (u v) := by
    intro u
    simp_rw [norm_sub_symm_eq hk g hg u]
    rw [← Finset.prod_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin k))) (t := T)
      (g := sigma hk g) (fun i _ => by
        rw [hT, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, sigma_notMem_refSet hk g i⟩)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => dispWeight lam w ‖u v‖)
      (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.prod_const]
  rw [setLIntegral_ref_eq (stepNt g) (refSet hk g) hR N _
    (fun (v : NtV g) (s : ℂ) => dispWeight lam w ‖s‖ ^ m v)
    (fun v => ((measurable_dispWeight lam hw).comp measurable_norm).pow_const _) hΨ]
  refine mul_le_mul_right ?_ _
  -- the product of the displacement integrals
  have hJ : ∀ v ∈ T, ∫⁻ s : ℂ, dispWeight lam w ‖s‖ ^ m v ≤
      if m v = 2 then cycleIntegral lam w else noncycleIntegral lam w := by
    intro v hv
    have hv' : v ∉ refSet hk g := (Finset.mem_filter.1 hv).2
    have h1 : 1 ≤ m v := one_le_card_fiber hk g hv'
    have h2 : m v ≤ 2 := card_fiber_le_two hk g v
    by_cases h : m v = 2
    · rw [ite_eq_left h, h]
      exact lintegral_dispWeight_norm_pow_two_le lam w
    · rw [ite_eq_right h]
      have : m v = 1 := by omega
      rw [this]
      simp only [pow_one]
      exact (lintegral_dispWeight_norm lam w).le
  refine (Finset.prod_le_prod hJ).trans (le_of_eq ?_)
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  -- counting the cycle and non-cycle displacements
  have hk0 := two_mul_card_twoCyclesIn_add_card_rootsOf_le g
  have hTcard : T.card = k - (twoCyclesIn g).card := card_notMem_refSet hk g
  have hsum : ∑ v ∈ T, m v = k := by
    have := sum_card_fiber hk g
    rw [hT, Finset.sum_filter_of_ne]
    · exact this
    · intro v _ hv
      by_contra hvR
      exact hv (card_fiber_eq_zero hk g hvR)
  have hsum2 : ∑ v ∈ T, m v = T.card + (T.filter fun v => m v = 2).card := by
    calc ∑ v ∈ T, m v = ∑ v ∈ T, (1 + if m v = 2 then 1 else 0) := by
          refine Finset.sum_congr rfl fun v hv => ?_
          have hv' : v ∉ refSet hk g := (Finset.mem_filter.1 hv).2
          have h1 : 1 ≤ m v := one_le_card_fiber hk g hv'
          have h2 : m v ≤ 2 := card_fiber_le_two hk g v
          by_cases h : m v = 2
          · rw [ite_eq_left h]; omega
          · rw [ite_eq_right h]; omega
      _ = T.card + (T.filter fun v => m v = 2).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_filter]
  have hn2 : (T.filter fun v => m v = 2).card = (twoCyclesIn g).card := by omega
  have hn1 : (T.filter fun v => ¬ m v = 2).card = k - 2 * (twoCyclesIn g).card := by
    have := Finset.card_filter_add_card_filter_not (s := T) (fun v => m v = 2)
    omega
  rw [hn2, hn1]

end Integration

/-! #### Fubini over the trivial vertices -/

section Fubini

/-- The coordinates of a configuration on the nontrivial components. -/
def restrictNt (z : Fin p → ℂ) : NtV g → ℂ := fun v => z v.1

/-- The decomposition of a configuration into the coordinates of the nontrivial components and of
the trivial vertices. -/
noncomputable def splitNt : (Fin p → ℂ) ≃ᵐ (NtV g → ℂ) × ({v : Fin p // ¬IsNtVertex g v} → ℂ) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin p => ℂ) (IsNtVertex g)

/-- The displacement `|z_i - z_{g i}|` of a selected vertex, as a function of the coordinates of the
nontrivial components. -/
noncomputable def dispNt (x : NtV g → ℂ) (i : Fin k) : ℝ := ‖x (selV hk g i) - x (tgtV g i)‖

/-- **Fubini over the trivial vertices** (source l. 1035: "We first integrate the `p - m`
vertices in trivial components"): the integral over a set `cell` of a function of the nontrivial
coordinates is at most the integral over the nontrivial coordinates of that function times the
volume of the section of `cell` by the trivial coordinates. -/
theorem lintegral_cell_le_fubini (cell : Set (Fin p → ℂ)) (hcell : MeasurableSet cell)
    (Φ : (NtV g → ℂ) → ℝ≥0∞) (F : (Fin p → ℂ) → ℝ≥0∞)
    (hF : ∀ z ∈ cell, F z = Φ (restrictNt g z)) :
    ∫⁻ z in cell, F z ≤
      ∫⁻ x, Φ x * volume {y : {v : Fin p // ¬IsNtVertex g v} → ℂ | (x, y) ∈ splitNt g '' cell} := by
  have hmp : MeasurePreserving (splitNt g) volume volume :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : Fin p => ℂ) (IsNtVertex g)
  have hE : MeasurableSet (splitNt g '' cell) :=
    (splitNt g).measurableEmbedding.measurableSet_image.2 hcell
  calc ∫⁻ z in cell, F z = ∫⁻ z in cell, (fun q => Φ q.1) (splitNt g z) :=
        setLIntegral_congr_fun hcell fun z hz => hF z hz
    _ = ∫⁻ q in splitNt g '' cell, Φ q.1 :=
        hmp.setLIntegral_comp_emb (splitNt g).measurableEmbedding (fun q => Φ q.1) cell
    _ = ∫⁻ q, (splitNt g '' cell).indicator (fun q => Φ q.1) q := (lintegral_indicator hE _).symm
    _ ≤ ∫⁻ x, ∫⁻ y, (splitNt g '' cell).indicator (fun q => Φ q.1) (x, y) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_le _
    _ ≤ _ := by
        refine lintegral_mono fun x => ?_
        have : ∀ y : {v : Fin p // ¬IsNtVertex g v} → ℂ,
            (splitNt g '' cell).indicator (fun q => Φ q.1) (x, y) =
              {y | (x, y) ∈ splitNt g '' cell}.indicator (fun _ => Φ x) y := by
          intro y
          by_cases hy : (x, y) ∈ splitNt g '' cell
          · have hy' : y ∈ {y | (x, y) ∈ splitNt g '' cell} := hy
            rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy']
          · have hy' : y ∉ {y | (x, y) ∈ splitNt g '' cell} := hy
            rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy']
        simp_rw [this]
        exact lintegral_indicator_const_le _ _

variable [Nontrivial (Fin p)] (key : Fin p ↪ ℕ)

/-- The cell `{γ'_p = g} ∩ Λ^p` of source l. 1030–1034. -/
def cellSet (N : ℕ) : Set (Fin p → ℂ) :=
  (Set.univ.pi fun _ : Fin p => box N) ∩ {z | restrictedNnMap hk key z = g}

theorem measurableSet_cellSet (N : ℕ) : MeasurableSet (cellSet hk g key N) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_box N).inter
    (measurableSet_restrictedNnMap_eq hk key g)

theorem norm_sub_le_of_mem_cellSet {N : ℕ} {z : Fin p → ℂ} (hz : z ∈ cellSet hk g key N)
    (i : Fin k) {j : Fin p} (hj : j ≠ Fin.castLE hk i) :
    ‖z (Fin.castLE hk i) - z (g i)‖ ≤ ‖z (Fin.castLE hk i) - z j‖ := by
  have h : nnMap key z (Fin.castLE hk i) = g i := congrFun hz.2 i
  rw [← h]
  exact norm_sub_nnMap_le key z hj

theorem mem_box_of_mem_cellSet {N : ℕ} {z : Fin p → ℂ} (hz : z ∈ cellSet hk g key N) (i : Fin p) :
    z i ∈ box N :=
  hz.1 i (Set.mem_univ i)

/-- **The volume available to the trivial vertices** (source l. 1035–1041). For fixed coordinates
`x` of the nontrivial components, the section of the cell by the trivial coordinates has volume at
most `e^{2k} N^{p - m} exp(-(∑_{i<k} |z_i - z_{g i}|²/16)/4)`, `m = |κ|`, and is empty unless all
the coordinates `x` lie in `Λ`. -/
theorem volume_section_le {N : ℕ} (hN0 : 0 < N) (hN : (N : ℝ) ≤ 2 * p) (x : NtV g → ℂ) :
    volume {y : {v : Fin p // ¬IsNtVertex g v} → ℂ | (x, y) ∈ splitNt g '' cellSet hk g key N} ≤
      {x : NtV g → ℂ | ∀ v, x v ∈ box N}.indicator (fun x =>
        ENNReal.ofReal (Real.exp (2 * k)) *
          (N : ℝ≥0∞) ^ Fintype.card {v : Fin p // ¬IsNtVertex g v} *
          ENNReal.ofReal (Real.exp (-((∑ i, dispNt hk g x i ^ 2 / 16) / 4)))) x := by
  by_cases hne : ∃ y, (x, y) ∈ splitNt g '' cellSet hk g key N
  swap
  · have : {y : {v : Fin p // ¬IsNtVertex g v} → ℂ | (x, y) ∈ splitNt g '' cellSet hk g key N} =
        ∅ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hy => hne ⟨y, hy⟩
    rw [this, measure_empty]
    exact zero_le
  obtain ⟨y₀, z₀, hz₀, hez⟩ := hne
  have hx : restrictNt g z₀ = x := congrArg Prod.fst hez
  have hxbox : x ∈ {x : NtV g → ℂ | ∀ v, x v ∈ box N} := by
    intro v
    rw [← hx]
    exact mem_box_of_mem_cellSet hk g key hz₀ _
  rw [Set.indicator_of_mem hxbox]
  have hsub : {y : {v : Fin p // ¬IsNtVertex g v} → ℂ |
        (x, y) ∈ splitNt g '' cellSet hk g key N} ⊆
      Set.univ.pi fun _ : {v : Fin p // ¬IsNtVertex g v} =>
        box N \ ⋃ i : Fin k, Metric.ball (x (selV hk g i)) (dispNt hk g x i) := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hxz : restrictNt g z = x := congrArg Prod.fst hzy
    have hyz : (fun v : {v : Fin p // ¬IsNtVertex g v} => z v.1) = y := congrArg Prod.snd hzy
    intro t _
    refine ⟨?_, ?_⟩
    · rw [← hyz]
      exact mem_box_of_mem_cellSet hk g key hz _
    · intro hmem
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem
      rw [Metric.mem_ball, dist_eq_norm, ← hyz] at hi
      have hne : t.1 ≠ Fin.castLE hk i := fun h => t.2 (h ▸ Or.inl i.2)
      have h1 := norm_sub_le_of_mem_cellSet hk g key hz i hne
      have h2 : dispNt hk g x i = ‖z (Fin.castLE hk i) - z (g i)‖ := by
        rw [← hxz]; rfl
      have h3 : x (selV hk g i) = z (Fin.castLE hk i) := by rw [← hxz]; rfl
      rw [h3, h2] at hi
      rw [norm_sub_rev] at hi
      simp only at hi
      linarith
  refine (measure_mono hsub).trans ?_
  have hn : p ≤ Fintype.card {v : Fin p // ¬IsNtVertex g v} + 2 * k := by
    rw [Fintype.card_subtype_compl]
    have h1 : Fintype.card {x // IsNtVertex g x} ≤ 2 * k := card_ntV_le hk g
    have h2 : Fintype.card {x // IsNtVertex g x} ≤ p := card_ntV_le_p g
    simp only [Fintype.card_fin]
    omega
  refine volume_pi_diff_iUnion_ball_le (p := p) (k := k) hn hN hN0 (fun i => x (selV hk g i))
    (dispNt hk g x) (fun i => hxbox _) (fun i => norm_nonneg _) ?_ ?_
  · intro i
    have hz1 := mem_box_of_mem_cellSet hk g key hz₀ (Fin.castLE hk i)
    have hz2 := mem_box_of_mem_cellSet hk g key hz₀ (g i)
    have h := norm_sub_le_of_mem_box hz1 hz2
    have h2 : Real.sqrt (2 * N) ≤ 2 * Real.sqrt N := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)]
    rw [← hx]
    exact h.trans h2
  · intro i j hij
    have hne : Fin.castLE hk j ≠ Fin.castLE hk i := fun h => hij (Fin.castLE_injective hk h).symm
    have := norm_sub_le_of_mem_cellSet hk g key hz₀ i hne
    rw [← hx]
    exact this

theorem prod_ofReal_exp_neg_auxC_mul (t : Fin k → ℝ) :
    ∏ i, ENNReal.ofReal (Real.exp (-(auxC * t i ^ 2))) =
      ENNReal.ofReal (Real.exp (-((∑ i, t i ^ 2 / 16) / 4))) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [Finset.sum_neg_distrib, Finset.sum_div, neg_inj]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [auxC]
  ring

/-- **Source l. 1035–1062, Step 2 for one restricted graph, with explicit constants.** For
`g ∈ D(k₀, k₁)` the integral over the cell `{γ'_p = g} ∩ Λ^p` of `∏_{i<k} w(r̃₁(z_i))` is at most
`e^{2k} N^{p - k + k₀} I₂^{k₀} I₁^{k - 2k₀}`, where `I₂` (resp. `I₁`) is the Gaussian integral of
`w(|u|/4 ∨ λ)²` (resp. `w(|u|/4 ∨ λ)`) against `e^{-|u|²/64}` over `ℂ`. -/
theorem lintegral_cellSet_le {N k₀ k₁ : ℕ} (hN : (N : ℝ) ≤ 2 * p) (lam : ℝ) {w : ℝ → ℝ≥0∞}
    (hw : Measurable w) (hg : g ∈ restrictedGraphs p k k₀ k₁) :
    ∫⁻ z in cellSet hk g key N, ∏ i : Fin k, w (nnRadius lam z (Fin.castLE hk i)) ≤
      ENNReal.ofReal (Real.exp 2) ^ k * (N : ℝ≥0∞) ^ (p - k + k₀) *
        (cycleIntegral lam w ^ k₀ * noncycleIntegral lam w ^ (k - 2 * k₀)) := by
  obtain ⟨hadm, h0, h1⟩ := mem_restrictedGraphs.1 hg
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · -- the box is a null set
    have hnull : volume (cellSet hk g key 0) = 0 := by
      refine measure_mono_null (Set.inter_subset_left) ?_
      rw [volume_pi_pi]
      exact Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary (Fin p))) (by
        simp [volume_box])
    rw [setLIntegral_measure_zero _ _ hnull]
    exact zero_le
  set T := {v : Fin p // ¬IsNtVertex g v} with hT
  set Φ : (NtV g → ℂ) → ℝ≥0∞ := fun x => ∏ i : Fin k, w (max (dispNt hk g x i / 4) lam) with hΦ
  have hF : ∀ z ∈ cellSet hk g key N,
      ∏ i : Fin k, w (nnRadius lam z (Fin.castLE hk i)) = Φ (restrictNt g z) := by
    intro z hz
    refine Finset.prod_congr rfl fun i _ => ?_
    have h : nnMap key z (Fin.castLE hk i) = g i := congrFun hz.2 i
    rw [nnRadius_eq key lam z (Fin.castLE hk i), h]
    rfl
  set c₀ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * k)) * (N : ℝ≥0∞) ^ Fintype.card T with hc₀
  have hc₀top : c₀ ≠ ∞ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  have hid : ∀ x : NtV g → ℂ, Φ x * (c₀ * ENNReal.ofReal (Real.exp
      (-((∑ i, dispNt hk g x i ^ 2 / 16) / 4)))) =
        c₀ * ∏ i : Fin k, dispWeight lam w (dispNt hk g x i) := by
    intro x
    simp only [dispWeight]
    rw [Finset.prod_mul_distrib, prod_ofReal_exp_neg_auxC_mul (fun i => dispNt hk g x i)]
    ring
  calc ∫⁻ z in cellSet hk g key N, ∏ i : Fin k, w (nnRadius lam z (Fin.castLE hk i))
      ≤ ∫⁻ x, Φ x * volume {y : T → ℂ | (x, y) ∈ splitNt g '' cellSet hk g key N} :=
        lintegral_cell_le_fubini g _ (measurableSet_cellSet hk g key N) Φ _ hF
    _ ≤ ∫⁻ x, {x : NtV g → ℂ | ∀ v, x v ∈ box N}.indicator (fun x =>
          c₀ * ∏ i : Fin k, dispWeight lam w (dispNt hk g x i)) x := by
        refine lintegral_mono fun x => ?_
        have hv := volume_section_le hk g key hN0 hN x
        by_cases hx : x ∈ {x : NtV g → ℂ | ∀ v, x v ∈ box N}
        · rw [Set.indicator_of_mem hx] at hv ⊢
          calc Φ x * _ ≤ Φ x * (c₀ * ENNReal.ofReal (Real.exp
                (-((∑ i, dispNt hk g x i ^ 2 / 16) / 4)))) := by
                exact mul_le_mul_right hv _
            _ = _ := hid x
        · rw [Set.indicator_of_notMem hx] at hv ⊢
          rw [le_zero_iff.1 hv, mul_zero]
    _ ≤ ∫⁻ x in {x : NtV g → ℂ | ∀ v, x v ∈ box N}, c₀ * ∏ i : Fin k,
          dispWeight lam w (dispNt hk g x i) := lintegral_indicator_le _ _
    _ ≤ ∫⁻ x in {x : NtV g → ℂ | ∀ r ∈ refSet hk g, x r ∈ box N}, c₀ * ∏ i : Fin k,
          dispWeight lam w (dispNt hk g x i) :=
        lintegral_mono_set fun x hx r _ => hx r
    _ = c₀ * ∫⁻ x in {x : NtV g → ℂ | ∀ r ∈ refSet hk g, x r ∈ box N}, ∏ i : Fin k,
          dispWeight lam w (dispNt hk g x i) := lintegral_const_mul' _ _ hc₀top
    _ ≤ c₀ * ((N : ℝ≥0∞) ^ (Finset.univ.filter (· ∈ refSet hk g)).card *
          (cycleIntegral lam w ^ (twoCyclesIn g).card *
            noncycleIntegral lam w ^ (k - 2 * (twoCyclesIn g).card))) :=
        mul_le_mul_right (setLIntegral_disp_le hk g hadm N lam hw) _
    _ = _ := by
        have hexp : ENNReal.ofReal (Real.exp (2 * k)) = ENNReal.ofReal (Real.exp 2) ^ k := by
          rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
          congr 2
          ring
        have hcard := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (NtV g))) (fun v => v ∈ refSet hk g)
        rw [Finset.card_univ] at hcard
        have hnot := card_notMem_refSet hk g
        have hTcard : Fintype.card T = p - Fintype.card {x // IsNtVertex g x} := by
          change Fintype.card {v : Fin p // ¬IsNtVertex g v} = _
          rw [Fintype.card_subtype_compl, Fintype.card_fin]
        have h2 : Fintype.card {x // IsNtVertex g x} ≤ p := card_ntV_le_p g
        have h3 := two_mul_card_twoCyclesIn_add_card_rootsOf_le g
        have hexpN : Fintype.card T + (Finset.univ.filter (· ∈ refSet hk g)).card =
            p - k + (twoCyclesIn g).card := by
          have h4 : Fintype.card {x // IsNtVertex g x} = Fintype.card (NtV g) := rfl
          omega
        rw [h0] at hexpN ⊢
        rw [hc₀, hexp, show ∀ a b c d : ℝ≥0∞, a * b * (c * d) = a * (b * c) * d from
          fun a b c d => by ring, ← pow_add, hexpN]

end Fubini

end Setup

end AuxIntegration

/-! ### The integral over one restricted graph -/

/-- **Proposition 3.6, Step 2 (integration over one restricted graph; source l. 1035–1062), in
weighted generality (ruling R12c).** There are absolute constants `C, c > 0` such that for every
`p ≥ 2`, `k ≤ p`, `N ≤ 2p`, every tie-break key, every measurable radial weight `w` (evaluated at
the first-neighbour radius `r̃₁ = r ∨ λ`) and every restricted graph `g ∈ D(k₀, k₁)`,
the integral over the cell `Λ^p ∩ {γ'_p = g}` of `∏_{i<k} w(r̃₁(z_i))` is at most
`C^k N^{p - k + k₀} I₂^{k₀} I₁^{k - 2 k₀}`, where
`I₂ = ∫_ℂ w(|u|/4 ∨ λ)² e^{-c|u|²} du` (a `2`-cycle displacement: both endpoints have radius
`|u|/4`) and `I₁ = ∫_ℂ w(|u|/4 ∨ λ) e^{-c|u|²} du` (any other displacement).

No positivity of `λ` and no regularity of `w` beyond measurability are needed. In the
application of the source, `w(r) = r^{-β/2} (1 + log (r/λ))^δ (1 + |log r|)^{δ'}`. -/
theorem lintegral_restrictedNnMap_eq_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (p k N k₀ k₁ : ℕ) [Nontrivial (Fin p)] (hk : k ≤ p) (_ : (N : ℝ) ≤ 2 * p)
        (key : Fin p ↪ ℕ) (lam : ℝ) (w : ℝ → ℝ≥0∞) (_ : Measurable w) (g : Fin k → Fin p)
        (_ : g ∈ restrictedGraphs p k k₀ k₁),
        ∫⁻ z in (Set.univ.pi fun _ : Fin p => box N) ∩ {z | restrictedNnMap hk key z = g},
            ∏ i : Fin k, w (nnRadius lam z (Fin.castLE hk i)) ≤
          ENNReal.ofReal C ^ k * (N : ℝ≥0∞) ^ (p - k + k₀) *
            ((∫⁻ u : ℂ, w (max (‖u‖ / 4) lam) ^ 2 *
                ENNReal.ofReal (Real.exp (-(c * ‖u‖ ^ 2)))) ^ k₀ *
              (∫⁻ u : ℂ, w (max (‖u‖ / 4) lam) *
                ENNReal.ofReal (Real.exp (-(c * ‖u‖ ^ 2)))) ^ (k - 2 * k₀)) :=
  ⟨Real.exp 2, AuxIntegration.auxC, Real.exp_pos 2, AuxIntegration.auxC_pos,
    fun _ _ _ _ _ _ hk hN key lam _ hw g hg =>
    AuxIntegration.lintegral_cellSet_le hk g key hN lam hw hg⟩

end TwoComponentCoulomb

end
