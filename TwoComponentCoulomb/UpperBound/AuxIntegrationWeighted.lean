/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.AuxIntegration

/-!
# Proposition 3.7, Step 2: integration over one restricted graph with one weight per vertex

Source: proof of Proposition 3.7 (`prop:two species`), l. 1122–1135
("We repeat the Gaussian integration from Step 2 of Proposition 3.6, with `t` marked vertices").

In Proposition 3.6 (`UpperBound/AuxIntegration.lean`) all selected vertices carry the same radial weight `w`.
Here the selected vertex `i < k` carries its own measurable weight `W i`, evaluated at the
first-neighbour radius `r̃₁(z_i) = r(z_i) ∨ λ` (`TwoComponentCoulomb.nnRadius`). For a restricted
graph `g ∈ D(k₀, k₁)` the integral over the cell `Λ^p ∩ {γ'_p = g}` of `∏_{i<k} W i (r̃₁(z_i))`
is bounded by `e^{2k} N^{p-k+k₀}` times

* for every `2`-cycle `(i, j)` of `g` inside the selected set, the Gaussian integral
  `pairIntegral λ (W i) (W j) = ∫_ℂ W i (a(u)) W j (a(u)) e^{-c|u|²} du`, `a(u) = |u|/4 ∨ λ`
  (both endpoints of a `2`-cycle have the radius `|u|/4` of the single displacement `u`);
* for every other selected vertex `i`, the Gaussian integral
  `noncycleIntegral λ (W i) = ∫_ℂ W i (a(u)) e^{-c|u|²} du`.

The proof is the proof of `AuxIntegration.lintegral_cellSet_le` with the product over the selected
vertices grouped according to the fibres of the displacement map `σ`: a fibre is either a single
non-cycle vertex or the two vertices of a `2`-cycle.

## Main results

* `TwoComponentCoulomb.AuxIntegration.pairIntegral`: the Gaussian integral of the product of two
  weights; `pairIntegral_self` (it is `cycleIntegral` for equal weights) and `pairIntegral_comm`.
* `TwoComponentCoulomb.AuxIntegration.setLIntegral_disp_le_weighted`: the displacement integrals in
  Gunson--Panta coordinates.
* `TwoComponentCoulomb.AuxIntegration.lintegral_cellSet_le_weighted`: the bound for one cell, with
  the explicit constants `C = e²`, `c = 1/64`.
* `TwoComponentCoulomb.lintegral_restrictedNnMap_eq_le_weighted`: the same, stated with
  existentially quantified absolute constants.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

namespace AuxIntegration

/-! ### The integral of a product of two weights -/

/-- The Gaussian integral of the product of two displacement weights `w, w'` at the common radius
`a(u) = |u|/4 ∨ λ` of a `2`-cycle (source l. 1122, "a mixed cycle"). -/
noncomputable def pairIntegral (lam : ℝ) (w w' : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ u : ℂ, w (max (‖u‖ / 4) lam) * w' (max (‖u‖ / 4) lam) *
    ENNReal.ofReal (Real.exp (-(auxC * ‖u‖ ^ 2)))

/-- For equal weights the pair integral is the cycle integral. -/
theorem pairIntegral_self (lam : ℝ) (w : ℝ → ℝ≥0∞) : pairIntegral lam w w = cycleIntegral lam w := by
  unfold pairIntegral cycleIntegral
  simp only [sq]

theorem pairIntegral_comm (lam : ℝ) (w w' : ℝ → ℝ≥0∞) :
    pairIntegral lam w w' = pairIntegral lam w' w := by
  unfold pairIntegral
  refine lintegral_congr fun u => ?_
  rw [mul_comm (w _)]

/-- The product of the displacement weights of the two endpoints of a `2`-cycle is bounded by the
pair integral. -/
theorem lintegral_dispWeight_mul_le (lam : ℝ) (w w' : ℝ → ℝ≥0∞) :
    ∫⁻ u : ℂ, dispWeight lam w ‖u‖ * dispWeight lam w' ‖u‖ ≤ pairIntegral lam w w' := by
  refine lintegral_mono fun u => ?_
  unfold dispWeight
  have h : ENNReal.ofReal (Real.exp (-(auxC * ‖u‖ ^ 2))) *
      ENNReal.ofReal (Real.exp (-(auxC * ‖u‖ ^ 2))) ≤
        ENNReal.ofReal (Real.exp (-(auxC * ‖u‖ ^ 2))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := auxC_pos
    nlinarith [sq_nonneg ‖u‖]
  calc _ = (w (max (‖u‖ / 4) lam) * w' (max (‖u‖ / 4) lam)) *
        (ENNReal.ofReal (Real.exp (-(auxC * ‖u‖ ^ 2))) *
          ENNReal.ofReal (Real.exp (-(auxC * ‖u‖ ^ 2)))) := by ring
    _ ≤ _ := mul_le_mul_right h _

/-! ### The fibres of the displacement map -/

section Fibres

open scoped Classical

variable {p k : ℕ} (hk : k ≤ p) (g : Fin k → Fin p)

/-- A non-cycle selected vertex `i` is the only selected vertex whose displacement coordinate is
`selV i`. -/
theorem sigma_eq_selV_iff_of_notMem_restrictedCycleVerts {i : Fin k} (hi : i ∉ restrictedCycleVerts g) (j : Fin k) :
    sigma hk g j = selV hk g i ↔ j = i := by
  unfold sigma
  by_cases h : selV hk g j ∈ refSet hk g
  · rw [ite_eq_left h]
    obtain ⟨e, he, rfl⟩ := (selV_mem_refSet_iff hk g j).1 h
    rw [tgtV_eq_selV_of_mem_twoCyclesIn hk g he]
    constructor
    · intro h2
      exact absurd (mem_restrictedCycleVerts.2 ⟨e, he, Or.inr (selV_injective hk g h2)⟩) hi
    · intro h2
      exact absurd (mem_restrictedCycleVerts.2 ⟨e, he, Or.inl h2⟩) hi
  · rw [ite_eq_right h]
    exact ⟨fun h2 => selV_injective hk g h2, fun h2 => by rw [h2]⟩

/-- The two vertices of a `2`-cycle `(e₁, e₂)` are exactly the selected vertices whose displacement
coordinate is `selV e₂`. -/
theorem sigma_eq_selV_snd_iff {e : Fin k × Fin k} (he : e ∈ twoCyclesIn g) (j : Fin k) :
    sigma hk g j = selV hk g e.2 ↔ j = e.1 ∨ j = e.2 := by
  unfold sigma
  by_cases h : selV hk g j ∈ refSet hk g
  · rw [ite_eq_left h]
    obtain ⟨e', he', rfl⟩ := (selV_mem_refSet_iff hk g j).1 h
    rw [tgtV_eq_selV_of_mem_twoCyclesIn hk g he']
    constructor
    · intro h2
      have h3 := snd_injOn_twoCyclesIn (g := g) (Finset.mem_coe.2 he') (Finset.mem_coe.2 he)
        (selV_injective hk g h2)
      left
      rw [h3]
    · rintro (h2 | h2)
      · have := fst_injOn_twoCyclesIn (g := g) (Finset.mem_coe.2 he') (Finset.mem_coe.2 he) h2
        rw [this]
      · exact absurd h2 (fst_ne_snd_of_mem_twoCyclesIn he' he)
  · rw [ite_eq_right h]
    constructor
    · intro h2
      right
      exact selV_injective hk g h2
    · rintro (h2 | h2)
      · exact absurd ((selV_mem_refSet_iff hk g j).2 ⟨e, he, h2.symm⟩) h
      · rw [h2]

theorem filter_sigma_eq_of_notMem_restrictedCycleVerts {i : Fin k} (hi : i ∉ restrictedCycleVerts g) :
    (Finset.univ.filter fun j : Fin k => sigma hk g j = selV hk g i) = {i} := by
  ext j
  simp [sigma_eq_selV_iff_of_notMem_restrictedCycleVerts hk g hi]

theorem filter_sigma_eq_of_mem_twoCyclesIn {e : Fin k × Fin k} (he : e ∈ twoCyclesIn g) :
    (Finset.univ.filter fun j : Fin k => sigma hk g j = selV hk g e.2) = {e.1, e.2} := by
  ext j
  simp [sigma_eq_selV_snd_iff hk g he]

/-- The displacement coordinates not in the reference set are indexed by the second vertices of the
`2`-cycles and by the non-cycle selected vertices. -/
theorem notMem_refSet_selV_iff (i : Fin k) :
    selV hk g i ∉ refSet hk g ↔
      i ∈ (twoCyclesIn g).image Prod.snd ∪ (restrictedCycleVerts g)ᶜ := by
  rw [selV_mem_refSet_iff hk g i]
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_compl, mem_restrictedCycleVerts]
  constructor
  · intro h
    by_cases h2 : ∃ e ∈ twoCyclesIn g, e.2 = i
    · obtain ⟨e, he, he2⟩ := h2
      exact Or.inl ⟨e, he, he2⟩
    · right
      rintro ⟨e, he, h3 | h3⟩
      · exact h ⟨e, he, h3⟩
      · exact h2 ⟨e, he, h3⟩
  · rintro (⟨e, he, he2⟩ | h) ⟨e', he', he1⟩
    · exact fst_ne_snd_of_mem_twoCyclesIn he' he (he1.trans he2.symm)
    · exact h ⟨e', he', Or.inl he1⟩

theorem disjoint_image_snd_compl_restrictedCycleVerts :
    Disjoint ((twoCyclesIn g).image Prod.snd) (restrictedCycleVerts g)ᶜ := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [Finset.mem_compl] at hi'
  exact hi' (mem_restrictedCycleVerts.2 (by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hi
    exact ⟨e, he, Or.inr rfl⟩))

end Fibres

/-! ### Integration in Gunson--Panta coordinates -/

section Integration

open scoped Classical

variable {p k : ℕ} (hk : k ≤ p) (g : Fin k → Fin p) (hg : IsAdmissibleRestriction g)

include hk hg in
/-- **Source l. 1122–1135, the displacement integrals with one weight per vertex.** After the
Gunson--Panta change of variables on the nontrivial components, the reference points integrate to
`N^{|R|}`; every `2`-cycle `(i, j)` gives the pair integral of `W i` and `W j`, and every other
selected vertex `i` gives the integral of `W i`. -/
theorem setLIntegral_disp_le_weighted (N : ℕ) (lam : ℝ) {W : Fin k → ℝ → ℝ≥0∞}
    (hW : ∀ i, Measurable (W i)) :
    ∫⁻ x in {x : NtV g → ℂ | ∀ r ∈ refSet hk g, x r ∈ box N},
        ∏ i : Fin k, dispWeight lam (W i) ‖x (selV hk g i) - x (tgtV g i)‖ ≤
      (N : ℝ≥0∞) ^ (Finset.univ.filter (· ∈ refSet hk g)).card *
        ((∏ e ∈ twoCyclesIn g, pairIntegral lam (W e.1) (W e.2)) *
          ∏ i ∈ (restrictedCycleVerts g)ᶜ, noncycleIntegral lam (W i)) := by
  set hR := exists_iterate_stepNt_mem_refSet hk g hg with hhR
  set T : Finset (NtV g) := Finset.univ.filter (· ∉ refSet hk g) with hT
  set G : NtV g → ℂ → ℝ≥0∞ := fun v s =>
    ∏ i ∈ Finset.univ.filter (fun i : Fin k => sigma hk g i = v), dispWeight lam (W i) ‖s‖
    with hG
  have hGm : ∀ v, Measurable (G v) := fun v =>
    Finset.measurable_prod _ fun i _ => (measurable_dispWeight lam (hW i)).comp measurable_norm
  have hΨ : ∀ u : NtV g → ℂ,
      ∏ i : Fin k, dispWeight lam (W i) ‖(gpLinearEquiv (stepNt g) (refSet hk g) hR).symm u
          (selV hk g i) - (gpLinearEquiv (stepNt g) (refSet hk g) hR).symm u (tgtV g i)‖ =
        ∏ v ∈ T, G v (u v) := by
    intro u
    simp_rw [norm_sub_symm_eq hk g hg u]
    rw [← Finset.prod_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin k))) (t := T)
      (g := sigma hk g) (fun i _ => by
        rw [hT, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, sigma_notMem_refSet hk g i⟩)]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  rw [setLIntegral_ref_eq (stepNt g) (refSet hk g) hR N _ G hGm hΨ]
  refine mul_le_mul_right ?_ _
  -- reindex the displacement coordinates by the selected vertices
  set U : Finset (Fin k) := Finset.univ.filter fun i => selV hk g i ∉ refSet hk g with hU
  have hTU : T = U.image (selV hk g) := by
    ext v
    simp only [hT, hU, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hv
      obtain ⟨i, hi⟩ := exists_selV_of_lt hk g v (lt_of_notMem_refSet hk g hv)
      exact ⟨i, hi ▸ hv, hi⟩
    · rintro ⟨i, hi, rfl⟩
      exact hi
  have hUsplit : U = (twoCyclesIn g).image Prod.snd ∪ (restrictedCycleVerts g)ᶜ := by
    ext i
    simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and]
    exact notMem_refSet_selV_iff hk g i
  show ∏ v ∈ T, ∫⁻ s, G v s ≤ _
  rw [hTU, Finset.prod_image (fun a _ b _ h => selV_injective hk g h), hUsplit,
    Finset.prod_union (disjoint_image_snd_compl_restrictedCycleVerts g),
    Finset.prod_image (fun a ha b hb h => snd_injOn_twoCyclesIn ha hb h)]
  refine mul_le_mul' (Finset.prod_le_prod fun e he => ?_) (le_of_eq (Finset.prod_congr rfl
    fun i hi => ?_))
  · -- a `2`-cycle
    have hf := filter_sigma_eq_of_mem_twoCyclesIn hk g he
    have hne : e.1 ≠ e.2 := (mem_twoCyclesIn.1 he).1.ne
    simp only [hG, hf, Finset.prod_pair hne]
    exact lintegral_dispWeight_mul_le lam (W e.1) (W e.2)
  · -- a non-cycle selected vertex
    have hi' : i ∉ restrictedCycleVerts g := Finset.mem_compl.1 hi
    simp only [hG, filter_sigma_eq_of_notMem_restrictedCycleVerts hk g hi', Finset.prod_singleton]
    rfl

end Integration

/-! ### The weighted bound for one cell -/

section Cell

open scoped Classical

variable {p k : ℕ} (hk : k ≤ p) (g : Fin k → Fin p) [Nontrivial (Fin p)] (key : Fin p ↪ ℕ)

/-- **Source l. 1035–1062, 1122–1135, Step 2 for one restricted graph with one weight per
selected vertex.** For `g ∈ D(k₀, k₁)` the integral over the cell `{γ'_p = g} ∩ Λ^p` of
`∏_{i<k} W i (r̃₁(z_i))` is at most `e^{2k} N^{p-k+k₀}` times the product of the pair integrals of
the weights of the `2`-cycles of `g` and of the integrals of the weights of the other selected
vertices. -/
theorem lintegral_cellSet_le_weighted {N k₀ k₁ : ℕ} (hN : (N : ℝ) ≤ 2 * p) (lam : ℝ)
    {W : Fin k → ℝ → ℝ≥0∞} (hW : ∀ i, Measurable (W i)) (hg : g ∈ restrictedGraphs p k k₀ k₁) :
    ∫⁻ z in cellSet hk g key N, ∏ i : Fin k, W i (nnRadius lam z (Fin.castLE hk i)) ≤
      ENNReal.ofReal (Real.exp 2) ^ k * (N : ℝ≥0∞) ^ (p - k + k₀) *
        ((∏ e ∈ twoCyclesIn g, pairIntegral lam (W e.1) (W e.2)) *
          ∏ i ∈ (restrictedCycleVerts g)ᶜ, noncycleIntegral lam (W i)) := by
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
  set Φ : (NtV g → ℂ) → ℝ≥0∞ := fun x =>
    ∏ i : Fin k, W i (max (dispNt hk g x i / 4) lam) with hΦ
  have hF : ∀ z ∈ cellSet hk g key N,
      ∏ i : Fin k, W i (nnRadius lam z (Fin.castLE hk i)) = Φ (restrictNt g z) := by
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
        c₀ * ∏ i : Fin k, dispWeight lam (W i) (dispNt hk g x i) := by
    intro x
    simp only [dispWeight]
    rw [Finset.prod_mul_distrib, prod_ofReal_exp_neg_auxC_mul (fun i => dispNt hk g x i)]
    ring
  calc ∫⁻ z in cellSet hk g key N, ∏ i : Fin k, W i (nnRadius lam z (Fin.castLE hk i))
      ≤ ∫⁻ x, Φ x * volume {y : T → ℂ | (x, y) ∈ splitNt g '' cellSet hk g key N} :=
        lintegral_cell_le_fubini g _ (measurableSet_cellSet hk g key N) Φ _ hF
    _ ≤ ∫⁻ x, {x : NtV g → ℂ | ∀ v, x v ∈ box N}.indicator (fun x =>
          c₀ * ∏ i : Fin k, dispWeight lam (W i) (dispNt hk g x i)) x := by
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
          dispWeight lam (W i) (dispNt hk g x i) := lintegral_indicator_le _ _
    _ ≤ ∫⁻ x in {x : NtV g → ℂ | ∀ r ∈ refSet hk g, x r ∈ box N}, c₀ * ∏ i : Fin k,
          dispWeight lam (W i) (dispNt hk g x i) :=
        lintegral_mono_set fun x hx r _ => hx r
    _ = c₀ * ∫⁻ x in {x : NtV g → ℂ | ∀ r ∈ refSet hk g, x r ∈ box N}, ∏ i : Fin k,
          dispWeight lam (W i) (dispNt hk g x i) := lintegral_const_mul' _ _ hc₀top
    _ ≤ c₀ * ((N : ℝ≥0∞) ^ (Finset.univ.filter (· ∈ refSet hk g)).card *
          ((∏ e ∈ twoCyclesIn g, pairIntegral lam (W e.1) (W e.2)) *
            ∏ i ∈ (restrictedCycleVerts g)ᶜ, noncycleIntegral lam (W i))) :=
        mul_le_mul_right (setLIntegral_disp_le_weighted hk g hadm N lam hW) _
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
        rw [h0] at hexpN
        rw [hc₀, hexp, show ∀ a b c d : ℝ≥0∞, a * b * (c * d) = a * (b * c) * d from
          fun a b c d => by ring, ← pow_add, hexpN]

end Cell

end AuxIntegration

/-! ### The integral over one restricted graph -/

/-- **Proposition 3.7, Step 2 (integration over one restricted graph, one weight per vertex;
source l. 1122–1135).** There are absolute constants `C, c > 0` such that for every `p ≥ 2`,
`k ≤ p`, `N ≤ 2p`, every tie-break key, every family of measurable radial weights `W i` and every
restricted graph `g ∈ D(k₀, k₁)`, the integral over the cell `Λ^p ∩ {γ'_p = g}` of
`∏_{i<k} W i (r̃₁(z_i))` is at most `C^k N^{p-k+k₀}` times the product over the `2`-cycles `(i, j)`
of `g` of `∫_ℂ W i (a(u)) W j (a(u)) e^{-c|u|²} du` and over the other selected vertices `i` of
`∫_ℂ W i (a(u)) e^{-c|u|²} du`, with `a(u) = |u|/4 ∨ λ`. -/
theorem lintegral_restrictedNnMap_eq_le_weighted :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (p k N k₀ k₁ : ℕ) [Nontrivial (Fin p)] (hk : k ≤ p) (_ : (N : ℝ) ≤ 2 * p)
        (key : Fin p ↪ ℕ) (lam : ℝ) (W : Fin k → ℝ → ℝ≥0∞) (_ : ∀ i, Measurable (W i))
        (g : Fin k → Fin p) (_ : g ∈ restrictedGraphs p k k₀ k₁),
        ∫⁻ z in (Set.univ.pi fun _ : Fin p => box N) ∩ {z | restrictedNnMap hk key z = g},
            ∏ i : Fin k, W i (nnRadius lam z (Fin.castLE hk i)) ≤
          ENNReal.ofReal C ^ k * (N : ℝ≥0∞) ^ (p - k + k₀) *
            ((∏ e ∈ twoCyclesIn g, ∫⁻ u : ℂ, W e.1 (max (‖u‖ / 4) lam) *
                W e.2 (max (‖u‖ / 4) lam) * ENNReal.ofReal (Real.exp (-(c * ‖u‖ ^ 2)))) *
              ∏ i ∈ (restrictedCycleVerts g)ᶜ, ∫⁻ u : ℂ, W i (max (‖u‖ / 4) lam) *
                ENNReal.ofReal (Real.exp (-(c * ‖u‖ ^ 2)))) :=
  ⟨Real.exp 2, AuxIntegration.auxC, Real.exp_pos 2, AuxIntegration.auxC_pos,
    fun _ _ _ _ _ _ hk hN key lam _ hW g hg =>
    AuxIntegration.lintegral_cellSet_le_weighted hk g key hN lam hW hg⟩

end TwoComponentCoulomb

end
