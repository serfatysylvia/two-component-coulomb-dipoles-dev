/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.AuxIntegrationWeighted
public import TwoComponentCoulomb.UpperBound.AuxNearestNeighbor

/-!
# Proposition 3.8: two marked species with distinct exponents

Source: Proposition 3.8 (`prop:two species`, l. 1141--1153, eq.
(eq:two species)) and its proof (l. 1155--1217), in the weighted generality of ruling R12c.

For `β > 4`, `δ ∈ {0, 1}`, `0 < λ ≤ e⁻¹`, integers `k + k' ≤ p ≤ N ≤ 2 p` (`p ≥ 2` is the instance
`Nontrivial (Fin p)`), the integrand of the proposition,
`exp (-4 F_k - β F_{k,k'}) ∏_{i ≤ k} (1 + log (r̃₁(z_i)/λ))^δ`, is the product of the radial weights
`∏_{i<k} sourceWeight 4 δ 0 λ (r̃₁(z_i)) · ∏_{k ≤ i < k+k'} sourceWeight β 0 0 λ (r̃₁(z_i))`
(`prod_twoSpecies_eq`), and the integral over `Λ^p` is at most
`exp (p log N + C_β (k + k') + (k/2) γ_{4,k} + (k'/2) γ_{β,k'})` (`lintegral_twoSpecies_le`).
The first block `{i < k}` of the marked vertices is `Fin.castAdd k'` and the second block
`{k ≤ i < k + k'}` is `Fin.natAdd k`, as embeddings of `Fin k` and `Fin k'` into `Fin (k + k')`.

## The proof

Let `t = k + k'`. The proof of the source reruns Steps 1--3 of Proposition 3.7 with the `t` marked
vertices of the restricted graph `γ'_p` (`RestrictedGraph.lean`) and one radial weight per vertex.

* *Step 1, counting* (l. 1160--1170). The number of graphs of type `(k₀, k₁)` is bounded by
  `2^t t^t p^{k₁}/(k₀! k₁!)` irrespective of the species (`card_restrictedGraphs_le`). The refined
  cycle counts `(k₀,₁, k₀,₂, k₀,₃)` of the source are not introduced: the three inequalities of
  l. 1162--1164 only serve to bound the exponent of the maximum of l. 1191--1205, and this bound is
  obtained vertex by vertex below (the cycles are indexed by pairs of vertices, so the refined
  counts are the numbers of cycles of each type `(i, j)`).
* *Step 2, integration* (l. 1174--1187). `AuxIntegrationWeighted.lean`
  (`lintegral_cellSet_le_weighted`) bounds the integral over the cell of a graph `g` by
  `e^{2t} N^{p-t+k₀}` times the product, over the `2`-cycles `(i, j)` of `g`, of the Gaussian
  integral of `W i · W j` and, over the other vertices `i`, of the Gaussian integral of `W i`.
  The radial integrals are bounded in `exists_twoSpecies_radial_bounds`; the one of a mixed cycle,
  with the weight `r̃₁^{-2-β/2} (1 + log (r̃₁/λ))^δ`, is `pairIntegral_sourceWeight_four_le`
  (`C λ^{-β/2}`, since `2 + β/2 > 2`).
* *Step 3, optimization* (l. 1191--1216). With `x = t/N`, the scales `θ₁² = C_m max (A₁ x, B₁²)`,
  `θ₂² = C_m max (A₂ x, B₂²)` satisfy `x · (cost of a pair) ≤ θ_i θ_j` for every pair of vertices
  (the mixed cycle cost `C A₁₂` has `A₁₂² = A₁ A₂`) and `cost of a vertex ≤ θ_i`. Since the vertices
  of the `2`-cycles are the disjoint union of their first and second vertices, this gives
  `x^{k₀} ∏_{cycles} ∏_{other vertices} ≤ ∏_i θ_i = θ₁^k θ₂^{k'}` (`pow_mul_prod_cycles_le`),
  which is the content of the maximization over the counts of the source (the bound
  `(k/2)(A ∨ 0) + (k'/2)(B ∨ 0)` of l. 1202--1205). Together with the count
  `|D| N^{p-t+k₀} ≤ (2e²)^t N^p (t/N)^{k₀}` (`count_mul_pow_le`) and the cost `(t+1)² ≤ 4^t` of the
  sum over `(k₀, k₁)`, this is `lintegral_twoSpecies_le_of_scales`. Finally `t` is replaced by `k`
  and `k'` in the logarithms at the cost `(t/2) log 2` (`log_regroup`, l. 1212--1216).

When one of the groups is empty the same argument applies verbatim (an empty block contributes the
factor `θ^0 = 1`); this includes the reduction to Proposition 3.7 of l. 1156. The case `k = k' = 0`
is the volume `N^p`.

## Main results

* `TwoComponentCoulomb.lintegral_twoSpecies_le`: **Proposition 3.8**, with the constant `C_β`
  quantified before `δ, N, p, k, k', λ` (ruling R11).
* `TwoComponentCoulomb.lintegral_twoSpecies_finset_le`: the same bound for two disjoint selected
  subsets `S₁, S₂ ⊆ Fin p` of cardinalities `k, k'` (used by Proposition 3.9).
* `TwoComponentCoulomb.prop_twoSpecies`: Proposition 3.8 in the source's own form, with
  `exp (-4 F_k - β F_{k,k'})` (`TwoComponentCoulomb.auxEnergy`, `auxEnergySecond`).
* `TwoComponentCoulomb.lintegral_twoSpecies_le_of_scales`: Steps 1--3 for abstract measurable
  weights with given scales.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace TwoComponentCoulomb

open AuxIntegration

/-! ### Step 2: the radial integral of a mixed cycle (source l. 1174) -/

/-- For the weights `r̃₁^{-2} (1 + log (r̃₁/λ))^δ` (first group) and `r̃₁^{-β/2}` (second group), the
integral of a mixed `2`-cycle is the radial Gaussian integral with the exponent `2 + β/2`. -/
theorem pairIntegral_sourceWeight_four {lam : ℝ} (hlam : 0 < lam) (β : ℝ) (δ : ℕ) :
    pairIntegral lam (sourceWeight 4 δ 0 lam) (sourceWeight β 0 0 lam) =
      gaussRadial auxC (2 + β / 2) δ lam := by
  unfold pairIntegral gaussRadial
  refine lintegral_congr fun u => ?_
  have hr : 0 < max (‖u‖ / 4) lam := lt_max_of_lt_right hlam
  have hL := log_div_nonneg_of_le hlam (le_max_right (‖u‖ / 4) lam)
  unfold sourceWeight radialG
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e1 : max (‖u‖ / 4) lam ^ (-(2 + β / 2)) =
      max (‖u‖ / 4) lam ^ (-(4 / 2 : ℝ)) * max (‖u‖ / 4) lam ^ (-(β / 2)) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  simp only [pow_zero, mul_one]
  rw [e1]
  ring

/-- **A mixed cycle** (source l. 1174): for `β > 0`, `∫ w₁ w₂ e^{-c|u|²} ≤ C λ^{-β/2}` uniformly
in `0 < λ ≤ 1`, where `w₁ = sourceWeight 4 δ 0 λ` and `w₂ = sourceWeight β 0 0 λ`. -/
theorem pairIntegral_sourceWeight_four_le {β : ℝ} (hβ : 0 < β) (δ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      pairIntegral lam (sourceWeight 4 δ 0 lam) (sourceWeight β 0 0 lam) ≤
        ENNReal.ofReal (C * lam ^ (-(β / 2))) := by
  obtain ⟨C, hC0, hC⟩ := gaussRadial_le_of_two_lt auxC_pos.le (α := 2 + β / 2) (by linarith) δ
  refine ⟨C, hC0, fun lam hlam hlam1 => ?_⟩
  rw [pairIntegral_sourceWeight_four hlam]
  have := hC lam hlam hlam1
  rwa [show (2 : ℝ) - (2 + β / 2) = -(β / 2) by ring] at this

namespace TwoSpecies

/-! ### Steps 1 and 2: the product over the cycles and the non-cycle vertices -/

theorem disjoint_image_fst_snd {p t : ℕ} (g : Fin t → Fin p) :
    Disjoint ((twoCyclesIn g).image Prod.fst) ((twoCyclesIn g).image Prod.snd) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hi
  obtain ⟨e', he', h⟩ := Finset.mem_image.1 hi'
  exact fst_ne_snd_of_mem_twoCyclesIn he he' h.symm

/-- **The scales of the cycles and of the other vertices** (source l. 1183--1187, 1197--1205).
Let `θ i ≥ 0` be a scale for every selected vertex. If every pair `(i, j)` satisfies
`x · a i j ≤ θ i θ j` and every vertex satisfies `b i ≤ θ i`, then
`x^{k₀} ∏_{cycles} a ∏_{other vertices} b ≤ ∏_i θ i`, where `k₀` is the number of cycles. The
point is that the vertices of the cycles are the disjoint union of the first and second vertices of
the cycles. -/
theorem pow_mul_prod_cycles_le {p t : ℕ} (g : Fin t → Fin p) {x : ℝ} (hx : 0 ≤ x)
    {a : Fin t → Fin t → ℝ} {b θ : Fin t → ℝ} (ha : ∀ i j, 0 ≤ a i j) (hb : ∀ i, 0 ≤ b i)
    (hθ : ∀ i, 0 ≤ θ i) (hθa : ∀ i j, x * a i j ≤ θ i * θ j) (hθb : ∀ i, b i ≤ θ i) :
    x ^ (twoCyclesIn g).card * ((∏ e ∈ twoCyclesIn g, a e.1 e.2) * ∏ i ∈ (restrictedCycleVerts g)ᶜ, b i) ≤
      ∏ i, θ i := by
  classical
  have h1 : x ^ (twoCyclesIn g).card * ∏ e ∈ twoCyclesIn g, a e.1 e.2 =
      ∏ e ∈ twoCyclesIn g, (x * a e.1 e.2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have h2 : ∏ e ∈ twoCyclesIn g, (x * a e.1 e.2) ≤ ∏ i ∈ restrictedCycleVerts g, θ i := by
    calc ∏ e ∈ twoCyclesIn g, (x * a e.1 e.2) ≤ ∏ e ∈ twoCyclesIn g, (θ e.1 * θ e.2) :=
          Finset.prod_le_prod₀ (fun e _ => mul_nonneg hx (ha _ _)) (fun e _ => hθa _ _)
      _ = ∏ i ∈ restrictedCycleVerts g, θ i := by
        rw [restrictedCycleVerts, Finset.prod_union (disjoint_image_fst_snd g),
          Finset.prod_image (fun a ha b hb h => fst_injOn_twoCyclesIn ha hb h),
          Finset.prod_image (fun a ha b hb h => snd_injOn_twoCyclesIn ha hb h),
          Finset.prod_mul_distrib]
  have h3 : ∏ i ∈ (restrictedCycleVerts g)ᶜ, b i ≤ ∏ i ∈ (restrictedCycleVerts g)ᶜ, θ i :=
    Finset.prod_le_prod₀ (fun i _ => hb i) (fun i _ => hθb i)
  calc x ^ (twoCyclesIn g).card * ((∏ e ∈ twoCyclesIn g, a e.1 e.2) * ∏ i ∈ (restrictedCycleVerts g)ᶜ, b i)
      = (x ^ (twoCyclesIn g).card * ∏ e ∈ twoCyclesIn g, a e.1 e.2) *
          ∏ i ∈ (restrictedCycleVerts g)ᶜ, b i := by ring
    _ ≤ (∏ i ∈ restrictedCycleVerts g, θ i) * ∏ i ∈ (restrictedCycleVerts g)ᶜ, θ i := by
        rw [h1]
        exact mul_le_mul h2 h3 (Finset.prod_nonneg fun i _ => hb i)
          (Finset.prod_nonneg fun i _ => hθ i)
    _ = ∏ i, θ i := Finset.prod_mul_prod_compl _ _

/-- The weight of the selected vertex `i` of the two-species model: `w₁` in the first group
`{i < k}` and `w₂` in the second group. -/
def twoWeight (k : ℕ) (w₁ w₂ : ℝ → ℝ≥0∞) {t : ℕ} (i : Fin t) : ℝ → ℝ≥0∞ :=
  if (i : ℕ) < k then w₁ else w₂

theorem measurable_twoWeight (k : ℕ) {w₁ w₂ : ℝ → ℝ≥0∞} (hw₁ : Measurable w₁)
    (hw₂ : Measurable w₂) {t : ℕ} (i : Fin t) : Measurable (twoWeight k w₁ w₂ i) := by
  unfold twoWeight
  split_ifs
  exacts [hw₁, hw₂]

section Cell

variable {p k k' : ℕ} [Nontrivial (Fin p)]

open scoped Classical in
/-- **Source l. 1174--1187, the integral over one restricted graph for two species.** Let
`a₁₁, a₂₂, a₁₂` bound the pair integrals of the `2`-cycles inside the first group, inside the second
group and between the groups, `b₁, b₂` the integrals of the other vertices of the two groups, and
let `θ₁, θ₂` be scales with `x a₁₁ ≤ θ₁²`, `x a₂₂ ≤ θ₂²`, `x a₁₂ ≤ θ₁ θ₂`, `b₁ ≤ θ₁`, `b₂ ≤ θ₂`,
where `x = t/N`, `t = k + k'`. Then the integral over the cell of a restricted graph with `k₀`
cycles is at most `e^{2t} N^{p-t+k₀} (N/t)^{k₀} θ₁^k θ₂^{k'}`. -/
theorem lintegral_cell_le_twoSpecies {N k₀ k₁ : ℕ} (hkk : k + k' ≤ p) (key : Fin p ↪ ℕ)
    (hN : (N : ℝ) ≤ 2 * p) (hN0 : 0 < N) (ht : 0 < k + k') (lam : ℝ)
    {w₁ w₂ : ℝ → ℝ≥0∞} (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    {g : Fin (k + k') → Fin p} (hg : g ∈ restrictedGraphs p (k + k') k₀ k₁)
    {a₁₁ a₂₂ a₁₂ b₁ b₂ θ₁ θ₂ : ℝ} (ha₁₁ : 0 ≤ a₁₁) (ha₂₂ : 0 ≤ a₂₂) (ha₁₂ : 0 ≤ a₁₂)
    (hb₁0 : 0 ≤ b₁) (hb₂0 : 0 ≤ b₂) (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂)
    (hcyc₁ : cycleIntegral lam w₁ ≤ ENNReal.ofReal a₁₁)
    (hcyc₂ : cycleIntegral lam w₂ ≤ ENNReal.ofReal a₂₂)
    (hmix : pairIntegral lam w₁ w₂ ≤ ENNReal.ofReal a₁₂)
    (hnon₁ : noncycleIntegral lam w₁ ≤ ENNReal.ofReal b₁)
    (hnon₂ : noncycleIntegral lam w₂ ≤ ENNReal.ofReal b₂)
    (h11 : ((k + k' : ℕ) : ℝ) / N * a₁₁ ≤ θ₁ * θ₁) (h22 : ((k + k' : ℕ) : ℝ) / N * a₂₂ ≤ θ₂ * θ₂)
    (h12 : ((k + k' : ℕ) : ℝ) / N * a₁₂ ≤ θ₁ * θ₂) (hb₁ : b₁ ≤ θ₁) (hb₂ : b₂ ≤ θ₂) :
    ∫⁻ z in AuxIntegration.cellSet hkk g key N,
        ∏ i : Fin (k + k'), twoWeight k w₁ w₂ i (nnRadius lam z (Fin.castLE hkk i)) ≤
      ENNReal.ofReal (Real.exp 2 ^ (k + k') * (N : ℝ) ^ (p - (k + k') + k₀) *
        (((N : ℝ) / ((k + k' : ℕ) : ℝ)) ^ k₀ * (θ₁ ^ k * θ₂ ^ k'))) := by
  obtain ⟨-, h0, -⟩ := mem_restrictedGraphs.1 hg
  set x : ℝ := ((k + k' : ℕ) : ℝ) / N with hx
  have hx0 : 0 < x := by
    have : (0 : ℝ) < ((k + k' : ℕ) : ℝ) := by exact_mod_cast ht
    have : (0 : ℝ) < N := by exact_mod_cast hN0
    positivity
  -- the scales of the vertices
  set a : Fin (k + k') → Fin (k + k') → ℝ := fun i j =>
    if (i : ℕ) < k then (if (j : ℕ) < k then a₁₁ else a₁₂) else (if (j : ℕ) < k then a₁₂ else a₂₂)
    with ha
  set b : Fin (k + k') → ℝ := fun i => if (i : ℕ) < k then b₁ else b₂ with hb
  set θ : Fin (k + k') → ℝ := fun i => if (i : ℕ) < k then θ₁ else θ₂ with hθ
  have ha0 : ∀ i j, 0 ≤ a i j := by
    intro i j; simp only [ha]; split_ifs <;> assumption
  have hb0 : ∀ i, 0 ≤ b i := by
    intro i; simp only [hb]; split_ifs <;> assumption
  have hθ0 : ∀ i, 0 ≤ θ i := by
    intro i; simp only [hθ]; split_ifs <;> assumption
  have hθa : ∀ i j, x * a i j ≤ θ i * θ j := by
    intro i j
    simp only [ha, hθ]
    split_ifs
    · exact h11
    · exact h12
    · rw [mul_comm θ₂]; exact h12
    · exact h22
  have hθb : ∀ i, b i ≤ θ i := by
    intro i; simp only [hb, hθ]; split_ifs
    exacts [hb₁, hb₂]
  have hpair : ∀ i j : Fin (k + k'), pairIntegral lam (twoWeight k w₁ w₂ i) (twoWeight k w₁ w₂ j) ≤
      ENNReal.ofReal (a i j) := by
    intro i j
    simp only [ha, twoWeight]
    split_ifs
    · rw [pairIntegral_self]; exact hcyc₁
    · exact hmix
    · rw [pairIntegral_comm]; exact hmix
    · rw [pairIntegral_self]; exact hcyc₂
  have hnon : ∀ i : Fin (k + k'), noncycleIntegral lam (twoWeight k w₁ w₂ i) ≤
      ENNReal.ofReal (b i) := by
    intro i
    simp only [hb, twoWeight]
    split_ifs
    exacts [hnon₁, hnon₂]
  have hcell := lintegral_cellSet_le_weighted hkk g key hN lam
    (W := twoWeight k w₁ w₂) (measurable_twoWeight k hw₁ hw₂) hg
  refine hcell.trans ?_
  have hprod : (∏ e ∈ twoCyclesIn g, pairIntegral lam (twoWeight k w₁ w₂ e.1)
        (twoWeight k w₁ w₂ e.2)) *
      ∏ i ∈ (restrictedCycleVerts g)ᶜ, noncycleIntegral lam (twoWeight k w₁ w₂ i) ≤
      ENNReal.ofReal ((∏ e ∈ twoCyclesIn g, a e.1 e.2) * ∏ i ∈ (restrictedCycleVerts g)ᶜ, b i) := by
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun e _ => ha0 _ _),
      ENNReal.ofReal_prod_of_nonneg (fun e _ => ha0 _ _),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => hb0 i)]
    exact mul_le_mul' (Finset.prod_le_prod fun e _ => hpair _ _)
      (Finset.prod_le_prod fun i _ => hnon i)
  have hreal : (∏ e ∈ twoCyclesIn g, a e.1 e.2) * ∏ i ∈ (restrictedCycleVerts g)ᶜ, b i ≤
      ((N : ℝ) / ((k + k' : ℕ) : ℝ)) ^ k₀ * (θ₁ ^ k * θ₂ ^ k') := by
    have hP := pow_mul_prod_cycles_le g hx0.le ha0 hb0 hθ0 hθa hθb
    rw [h0] at hP
    have hΘ : ∏ i, θ i = θ₁ ^ k * θ₂ ^ k' := by
      simp [hθ, Fin.prod_univ_add]
    rw [hΘ] at hP
    have hxinv : ((N : ℝ) / ((k + k' : ℕ) : ℝ)) = x⁻¹ := by rw [hx, inv_div]
    rw [hxinv, inv_pow]
    have hxk : 0 < x ^ k₀ := pow_pos hx0 _
    rw [← div_eq_inv_mul, le_div_iff₀ hxk, mul_comm]
    exact hP
  calc _ ≤ ENNReal.ofReal (Real.exp 2) ^ (k + k') * (N : ℝ≥0∞) ^ (p - (k + k') + k₀) *
        ENNReal.ofReal ((∏ e ∈ twoCyclesIn g, a e.1 e.2) * ∏ i ∈ (restrictedCycleVerts g)ᶜ, b i) :=
        mul_le_mul_right hprod _
    _ ≤ ENNReal.ofReal (Real.exp 2) ^ (k + k') * (N : ℝ≥0∞) ^ (p - (k + k') + k₀) *
        ENNReal.ofReal (((N : ℝ) / ((k + k' : ℕ) : ℝ)) ^ k₀ * (θ₁ ^ k * θ₂ ^ k')) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hreal) _
    _ = _ := by
        have hexp : (0 : ℝ) ≤ Real.exp 2 := (Real.exp_pos 2).le
        have hNk : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        rw [ENNReal.ofReal_mul (show 0 ≤ Real.exp 2 ^ (k + k') * (N : ℝ) ^ (p - (k + k') + k₀) by
            positivity), ENNReal.ofReal_mul (show 0 ≤ Real.exp 2 ^ (k + k') by positivity),
          ENNReal.ofReal_pow hexp, ENNReal.ofReal_pow hNk, ENNReal.ofReal_natCast]

end Cell

/-! ### Step 3: summation over the graph types -/

section Assembly

variable {p t : ℕ} [Nontrivial (Fin p)]

/-- **Summation over the graph types** (source l. 1191--1196 with the count of l. 1167--1170). If
the integral of `F` over the cell of every restricted graph with `k₀` two-cycles is at most
`c^t N^{p-t+k₀} (N/t)^{k₀} Θ`, then the integral over `Λ^p` is at most
`4^t (2 e²)^t c^t N^p Θ`: the number of graphs of type `(k₀, k₁)` times
`N^{p-t+k₀} (t/N)^{k₀}` is at most `(2 e²)^t N^p`, and there are `(t+1)² ≤ 4^t` types. -/
theorem lintegral_pi_box_le_of_cell_bound {N : ℕ} (ht : 1 ≤ t) (htp : t ≤ p) (hpN : p ≤ N)
    (F : (Fin p → ℂ) → ℝ≥0∞) {c Θ : ℝ} (hc : 0 ≤ c) (hΘ : 0 ≤ Θ)
    (hcell : ∀ k₀ k₁ : ℕ, ∀ g ∈ restrictedGraphs p t k₀ k₁,
      ∫⁻ z in (Set.univ.pi fun _ : Fin p => box N) ∩ {z | restrictedNnMap htp Fin.valEmbedding z = g},
          F z ≤
        ENNReal.ofReal (c ^ t * (N : ℝ) ^ (p - t + k₀) * (((N : ℝ) / t) ^ k₀ * Θ))) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), F z ≤
      ENNReal.ofReal (4 ^ t * (2 * Real.exp 2) ^ t * c ^ t * (N : ℝ) ^ p * Θ) := by
  classical
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le ht0 (by exact_mod_cast htp.trans hpN)
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (2 * Real.exp 2) ^ t * c ^ t * (N : ℝ) ^ p * Θ := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hterm : ∀ k₀ ∈ range (t + 1), ∀ k₁ ∈ range (t + 1),
      (restrictedGraphs p t k₀ k₁).card •
        ENNReal.ofReal (c ^ t * (N : ℝ) ^ (p - t + k₀) * (((N : ℝ) / t) ^ k₀ * Θ)) ≤
      ENNReal.ofReal X := by
    intro k₀ _ k₁ _
    rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hle : 2 * k₀ + k₁ ≤ t
    · have hd := card_restrictedGraphs_le p t k₀ k₁
      have hcnt := count_mul_pow_le hle htp hpN ht
      have hone : ((t : ℝ) / N) ^ k₀ * ((N : ℝ) / t) ^ k₀ = 1 := by
        rw [← mul_pow, show (t : ℝ) / N * (N / t) = 1 by field_simp, one_pow]
      calc ((restrictedGraphs p t k₀ k₁).card : ℝ) *
            (c ^ t * (N : ℝ) ^ (p - t + k₀) * (((N : ℝ) / t) ^ k₀ * Θ))
          = (((restrictedGraphs p t k₀ k₁).card : ℝ) * (N : ℝ) ^ (p - t + k₀)) *
            (c ^ t * (((N : ℝ) / t) ^ k₀ * Θ)) := by ring
        _ ≤ ((2 * Real.exp 2) ^ t * (N : ℝ) ^ p * ((t : ℝ) / N) ^ k₀) *
            (c ^ t * (((N : ℝ) / t) ^ k₀ * Θ)) := by
            refine mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hd (by positivity)).trans
              hcnt) (by positivity)
        _ = X * (((t : ℝ) / N) ^ k₀ * ((N : ℝ) / t) ^ k₀) := by rw [hX]; ring
        _ = X := by rw [hone, mul_one]
    · have h0 : (restrictedGraphs p t k₀ k₁).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro g hg
        exact hle (two_mul_add_le_of_mem_restrictedGraphs hg)
      rw [h0, Nat.cast_zero, zero_mul]
      exact hX0
  calc _ ≤ ∑ k₀ ∈ range (t + 1), ∑ k₁ ∈ range (t + 1), (restrictedGraphs p t k₀ k₁).card •
        ENNReal.ofReal (c ^ t * (N : ℝ) ^ (p - t + k₀) * (((N : ℝ) / t) ^ k₀ * Θ)) :=
        lintegral_pi_box_le_sum_types_of_le htp Fin.valEmbedding N F _ hcell
    _ ≤ ∑ k₀ ∈ range (t + 1), ∑ k₁ ∈ range (t + 1), ENNReal.ofReal X :=
        sum_le_sum fun k₀ h0 => sum_le_sum fun k₁ h1 => hterm k₀ h0 k₁ h1
    _ = ENNReal.ofReal (((t : ℝ) + 1) * ((t : ℝ) + 1) * X) := by
        have e : ((t : ℝ) + 1) = ((t + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hcount : ((t : ℝ) + 1) * ((t : ℝ) + 1) ≤ 4 ^ t := by
          have h1 : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
          have h2 : ((t : ℝ) + 1) ≤ 2 ^ t := by exact_mod_cast h1
          calc ((t : ℝ) + 1) * ((t : ℝ) + 1) ≤ 2 ^ t * 2 ^ t := by gcongr
            _ = 4 ^ t := by rw [← mul_pow]; norm_num
        calc ((t : ℝ) + 1) * ((t : ℝ) + 1) * X ≤ 4 ^ t * X := by gcongr
          _ = _ := by rw [hX]; ring

end Assembly

theorem le_of_sq_le_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  (le_abs_self a).trans (abs_le_of_sq_le_sq h hb)

theorem pow_eq_exp_nat_mul_log {y : ℝ} (hy : 0 < y) (n : ℕ) : y ^ n = Real.exp (n * Real.log y) := by
  rw [Real.exp_nat_mul, Real.exp_log hy]

end TwoSpecies

open TwoSpecies

/-! ### Steps 1--3 for abstract weights with given scales -/

section Scales

variable {p k k' : ℕ} [Nontrivial (Fin p)]

/-- **Proposition 3.8 for abstract radial weights** (source l. 1160--1205). Let `w₁, w₂` be measurable
radial weights and `A₁, A₂, A₁₂, B₁, B₂, C > 0` with `A₁₂² = A₁ A₂` such that the cycle integrals of
`w₁` and `w₂`, the mixed cycle integral, and the non-cycle integrals of `w₁` and `w₂` are at most
`C A₁`, `C A₂`, `C A₁₂`, `C B₁`, `C B₂`. Then, for `1 ≤ t = k + k' ≤ p ≤ N ≤ 2p`,
`∫_{Λ^p} ∏_{i<k} w₁(r̃₁(z_i)) ∏_{k ≤ i < t} w₂(r̃₁(z_i)) dz` is at most
`exp (p log N + C' t + (k/2) log max (A₁ t/N, B₁²) + (k'/2) log max (A₂ t/N, B₂²))`
with `C' = 4 + log 8 + (log max (C, C²))/2`. -/
theorem lintegral_twoSpecies_le_of_scales {N : ℕ} (hkk : k + k' ≤ p) (hpN : p ≤ N)
    (hN : (N : ℝ) ≤ 2 * p) (ht : 1 ≤ k + k') (lam : ℝ) {w₁ w₂ : ℝ → ℝ≥0∞}
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) {A₁ A₂ A₁₂ B₁ B₂ C : ℝ} (hA₁ : 0 < A₁)
    (hA₂ : 0 < A₂) (hA₁₂ : 0 < A₁₂) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hC : 0 < C)
    (hA : A₁₂ ^ 2 = A₁ * A₂)
    (hcyc₁ : cycleIntegral lam w₁ ≤ ENNReal.ofReal (C * A₁))
    (hcyc₂ : cycleIntegral lam w₂ ≤ ENNReal.ofReal (C * A₂))
    (hmix : pairIntegral lam w₁ w₂ ≤ ENNReal.ofReal (C * A₁₂))
    (hnon₁ : noncycleIntegral lam w₁ ≤ ENNReal.ofReal (C * B₁))
    (hnon₂ : noncycleIntegral lam w₂ ≤ ENNReal.ofReal (C * B₂)) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
        ∏ i : Fin (k + k'), twoWeight k w₁ w₂ i (nnRadius lam z (Fin.castLE hkk i)) ≤
      ENNReal.ofReal (Real.exp (p * Real.log N +
        (4 + Real.log 8 + Real.log (max C (C ^ 2)) / 2) * ((k + k' : ℕ) : ℝ) +
        k / 2 * Real.log (max (A₁ * ((k + k' : ℕ) : ℝ) / N) (B₁ ^ 2)) +
        k' / 2 * Real.log (max (A₂ * ((k + k' : ℕ) : ℝ) / N) (B₂ ^ 2)))) := by
  have ht0 : (0 : ℝ) < ((k + k' : ℕ) : ℝ) := by exact_mod_cast ht
  have hN0' : 0 < N := lt_of_lt_of_le (by omega) (hkk.trans hpN)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN0'
  set t : ℝ := ((k + k' : ℕ) : ℝ) with htdef
  set m₁ : ℝ := max (A₁ * t / N) (B₁ ^ 2) with hm₁
  set m₂ : ℝ := max (A₂ * t / N) (B₂ ^ 2) with hm₂
  have hm₁0 : 0 < m₁ := lt_max_of_lt_right (pow_pos hB₁ 2)
  have hm₂0 : 0 < m₂ := lt_max_of_lt_right (pow_pos hB₂ 2)
  set Cm : ℝ := max C (C ^ 2) with hCm
  have hCm0 : 0 < Cm := lt_max_of_lt_left hC
  have hCCm : C ≤ Cm := le_max_left _ _
  have hC2Cm : C ^ 2 ≤ Cm := le_max_right _ _
  set θ₁ : ℝ := Real.exp ((Real.log Cm + Real.log m₁) / 2) with hθ₁
  set θ₂ : ℝ := Real.exp ((Real.log Cm + Real.log m₂) / 2) with hθ₂
  have hθ₁sq : θ₁ * θ₁ = Cm * m₁ := by
    rw [hθ₁, ← Real.exp_add, show (Real.log Cm + Real.log m₁) / 2 + (Real.log Cm + Real.log m₁) / 2 =
      Real.log Cm + Real.log m₁ by ring, Real.exp_add, Real.exp_log hCm0, Real.exp_log hm₁0]
  have hθ₂sq : θ₂ * θ₂ = Cm * m₂ := by
    rw [hθ₂, ← Real.exp_add, show (Real.log Cm + Real.log m₂) / 2 + (Real.log Cm + Real.log m₂) / 2 =
      Real.log Cm + Real.log m₂ by ring, Real.exp_add, Real.exp_log hCm0, Real.exp_log hm₂0]
  have hθ₁0 : 0 < θ₁ := Real.exp_pos _
  have hθ₂0 : 0 < θ₂ := Real.exp_pos _
  have hxA₁ : t / N * (C * A₁) ≤ θ₁ * θ₁ := by
    rw [hθ₁sq]
    calc t / N * (C * A₁) = C * (A₁ * t / N) := by ring
      _ ≤ C * m₁ := mul_le_mul_of_nonneg_left (le_max_left _ _) hC.le
      _ ≤ Cm * m₁ := mul_le_mul_of_nonneg_right hCCm hm₁0.le
  have hxA₂ : t / N * (C * A₂) ≤ θ₂ * θ₂ := by
    rw [hθ₂sq]
    calc t / N * (C * A₂) = C * (A₂ * t / N) := by ring
      _ ≤ C * m₂ := mul_le_mul_of_nonneg_left (le_max_left _ _) hC.le
      _ ≤ Cm * m₂ := mul_le_mul_of_nonneg_right hCCm hm₂0.le
  have hxA₁₂ : t / N * (C * A₁₂) ≤ θ₁ * θ₂ := by
    refine le_of_sq_le_sq' (mul_nonneg hθ₁0.le hθ₂0.le) ?_
    calc (t / N * (C * A₁₂)) ^ 2 = (t / N) ^ 2 * C ^ 2 * A₁₂ ^ 2 := by ring
      _ = (t / N * (C * A₁)) * (t / N * (C * A₂)) := by rw [hA]; ring
      _ ≤ (θ₁ * θ₁) * (θ₂ * θ₂) := mul_le_mul hxA₁ hxA₂ (by positivity) (by positivity)
      _ = (θ₁ * θ₂) ^ 2 := by ring
  have hbB₁ : C * B₁ ≤ θ₁ := by
    refine le_of_sq_le_sq' hθ₁0.le ?_
    calc (C * B₁) ^ 2 = C ^ 2 * B₁ ^ 2 := by ring
      _ ≤ Cm * m₁ := mul_le_mul hC2Cm (le_max_right _ _) (by positivity) hCm0.le
      _ = θ₁ ^ 2 := by rw [← hθ₁sq]; ring
  have hbB₂ : C * B₂ ≤ θ₂ := by
    refine le_of_sq_le_sq' hθ₂0.le ?_
    calc (C * B₂) ^ 2 = C ^ 2 * B₂ ^ 2 := by ring
      _ ≤ Cm * m₂ := mul_le_mul hC2Cm (le_max_right _ _) (by positivity) hCm0.le
      _ = θ₂ ^ 2 := by rw [← hθ₂sq]; ring
  have hmain := lintegral_pi_box_le_of_cell_bound (p := p) (t := k + k') (N := N) ht
    (hkk) hpN (fun z => ∏ i : Fin (k + k'),
      twoWeight k w₁ w₂ i (nnRadius lam z (Fin.castLE hkk i)))
    (c := Real.exp 2) (Θ := θ₁ ^ k * θ₂ ^ k') (Real.exp_pos 2).le (by positivity)
    (fun k₀ k₁ g hg => lintegral_cell_le_twoSpecies hkk Fin.valEmbedding hN hN0' (by omega) lam
      hw₁ hw₂ hg (mul_pos hC hA₁).le (mul_pos hC hA₂).le (mul_pos hC hA₁₂).le
      (mul_pos hC hB₁).le (mul_pos hC hB₂).le hθ₁0.le hθ₂0.le hcyc₁ hcyc₂ hmix hnon₁ hnon₂
      hxA₁ hxA₂ hxA₁₂ hbB₁ hbB₂)
  refine hmain.trans (le_of_eq ?_)
  congr 1
  have e8 : Real.log 8 = Real.log 2 + Real.log 4 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have e22 : Real.log (2 * Real.exp 2) = Real.log 2 + 2 := by
    rw [Real.log_mul (by norm_num) (Real.exp_pos 2).ne', Real.log_exp]
  rw [pow_eq_exp_nat_mul_log (by norm_num : (0 : ℝ) < 4),
    pow_eq_exp_nat_mul_log (by positivity : (0 : ℝ) < 2 * Real.exp 2),
    pow_eq_exp_nat_mul_log (Real.exp_pos 2), pow_eq_exp_nat_mul_log hN0, hθ₁, hθ₂,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add, e22, Real.log_exp]
  congr 1
  rw [e8, htdef]
  push_cast
  ring

end Scales

namespace TwoSpecies

/-! ### Step 3: replacing `t` by `k` and `k'` in the logarithms -/

section Entropy

theorem log_div_mul_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    a * Real.log (t / a) ≤ a * Real.log 2 + t / 2 - a := by
  have h1 : Real.log (t / a) = Real.log 2 + Real.log (t / (2 * a)) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  have h2 : Real.log (t / (2 * a)) ≤ t / (2 * a) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h3 : a * (t / (2 * a) - 1) = t / 2 - a := by field_simp
  rw [h1]
  calc a * (Real.log 2 + Real.log (t / (2 * a))) = a * Real.log 2 + a * Real.log (t / (2 * a)) := by
        ring
    _ ≤ a * Real.log 2 + a * (t / (2 * a) - 1) := by gcongr
    _ = a * Real.log 2 + t / 2 - a := by rw [h3]; ring

/-- The entropy of a two-point distribution is at most `log 2`
(source l. 1212--1216: `(k/2) log (t/k) + (k'/2) log (t/k') ≤ (t/2) log 2`). -/
theorem mul_log_div_add_le {k k' : ℕ} (hk : 1 ≤ k) (hk' : 1 ≤ k') :
    (k : ℝ) * Real.log (((k + k' : ℕ) : ℝ) / k) + k' * Real.log (((k + k' : ℕ) : ℝ) / k') ≤
      ((k + k' : ℕ) : ℝ) * Real.log 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk0' : (0 : ℝ) < k' := by exact_mod_cast hk'
  have ht : (0 : ℝ) < ((k + k' : ℕ) : ℝ) := by positivity
  have h1 := log_div_mul_le hk0 ht
  have h2 := log_div_mul_le hk0' ht
  push_cast at h1 h2 ⊢
  linarith

/-- Replacing `t` by `k` and `k'` inside the logarithms (source l. 1212--1216). -/
theorem log_regroup {k k' N : ℕ} {A₁ A₂ B₁ B₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hB₁ : 0 < B₁)
    (hB₂ : 0 < B₂) (hN : 0 < N) :
    (k : ℝ) / 2 * Real.log (max (A₁ * ((k + k' : ℕ) : ℝ) / N) (B₁ ^ 2)) +
        k' / 2 * Real.log (max (A₂ * ((k + k' : ℕ) : ℝ) / N) (B₂ ^ 2)) ≤
      k / 2 * Real.log (max (A₁ * k / N) (B₁ ^ 2)) + k' / 2 * Real.log (max (A₂ * k' / N) (B₂ ^ 2)) +
        ((k + k' : ℕ) : ℝ) / 2 * Real.log 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- one group: for `1 ≤ k`, `log max (A t/N, B²) ≤ log max (A k/N, B²) + log (t/k)`
  have one : ∀ {A B : ℝ} {k k' : ℕ}, 0 < A → 0 < B → 1 ≤ k →
      Real.log (max (A * ((k + k' : ℕ) : ℝ) / N) (B ^ 2)) ≤
        Real.log (max (A * k / N) (B ^ 2)) + Real.log (((k + k' : ℕ) : ℝ) / k) := by
    intro A B k k' hA hB hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hr : 1 ≤ ((k + k' : ℕ) : ℝ) / k := by
      rw [le_div_iff₀ hk0, one_mul]; exact_mod_cast Nat.le_add_right k k'
    have hm0 : 0 < max (A * k / N) (B ^ 2) := lt_max_of_lt_right (pow_pos hB 2)
    rw [← Real.log_mul hm0.ne' (by positivity)]
    refine Real.log_le_log (lt_max_of_lt_right (pow_pos hB 2)) ?_
    refine max_le ?_ ?_
    · calc A * ((k + k' : ℕ) : ℝ) / N = (((k + k' : ℕ) : ℝ) / k) * (A * k / N) := by
            field_simp
        _ ≤ (((k + k' : ℕ) : ℝ) / k) * max (A * k / N) (B ^ 2) :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
        _ = max (A * k / N) (B ^ 2) * (((k + k' : ℕ) : ℝ) / k) := mul_comm _ _
    · calc B ^ 2 = 1 * B ^ 2 := (one_mul _).symm
        _ ≤ (((k + k' : ℕ) : ℝ) / k) * B ^ 2 := mul_le_mul_of_nonneg_right hr (by positivity)
        _ ≤ (((k + k' : ℕ) : ℝ) / k) * max (A * k / N) (B ^ 2) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
        _ = max (A * k / N) (B ^ 2) * (((k + k' : ℕ) : ℝ) / k) := mul_comm _ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_div, zero_mul, zero_add]
    have : 0 ≤ (k' : ℝ) / 2 * Real.log 2 := by positivity
    linarith
  rcases Nat.eq_zero_or_pos k' with rfl | hk'
  · simp only [Nat.cast_zero, zero_div, zero_mul, add_zero]
    have : 0 ≤ (k : ℝ) / 2 * Real.log 2 := by positivity
    linarith
  have h1 := one (k' := k') hA₁ hB₁ hk
  have h2 := one (A := A₂) (B := B₂) (k := k') (k' := k) hA₂ hB₂ hk'
  rw [Nat.add_comm k' k] at h2
  have he := mul_log_div_add_le hk hk'
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk0' : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
  have hm1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ k / 2)
  have hm2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ k' / 2)
  linarith only [hm1, hm2, he]

end Entropy

/-! ### Two selected subsets -/

section Subsets

/-- Any injective map `φ : Fin t → Fin p` is the restriction to the first `t` points of a
permutation of `Fin p`. -/
theorem exists_perm_castLE_eq {p t : ℕ} (ht : t ≤ p) (φ : Fin t → Fin p) (hφ : Function.Injective φ) :
    ∃ σ : Equiv.Perm (Fin p), ∀ i : Fin t, σ (Fin.castLE ht i) = φ i := by
  classical
  set f : Fin p → Fin p := fun j => if h : (j : ℕ) < t then φ ⟨j, h⟩ else j with hf
  have hfc : ∀ i : Fin t, f (Fin.castLE ht i) = φ i := by
    intro i
    have hi : ((Fin.castLE ht i : Fin p) : ℕ) < t := i.2
    simp only [hf, hi, dite_true]
    rfl
  have hcard : Fintype.card (Fin p) = (Finset.univ : Finset (Fin p)).card := by simp
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hcard (s := prefixSet ht) (f := f)
    (by intro x _; exact Finset.mem_univ _)
    (by
      intro a ha b hb hab
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 ha)
      obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hb)
      have h1 : f (Fin.castLE ht i) = f (Fin.castLE ht j) := hab
      rw [hfc, hfc] at h1
      rw [hφ h1])
  refine ⟨g.trans (Equiv.subtypeUnivEquiv fun x => Finset.mem_univ x), fun i => ?_⟩
  have hmem : Fin.castLE ht i ∈ prefixSet ht := Finset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩
  have := hg _ hmem
  simp only [Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply]
  rw [this, hfc]


/-- Two disjoint finite sets of cardinalities `k` and `k'` in `Fin p` are the images of the
consecutive blocks `{i < k}` and `{k ≤ i < k + k'}` under one permutation of `Fin p`. -/
theorem exists_perm_two_finset {p k k' : ℕ} (hkk : k + k' ≤ p) {S₁ S₂ : Finset (Fin p)}
    (hd : Disjoint S₁ S₂) (h₁ : S₁.card = k) (h₂ : S₂.card = k') :
    ∃ σ : Equiv.Perm (Fin p),
      S₁ = Finset.univ.image (fun i : Fin k => σ (Fin.castLE hkk (Fin.castAdd k' i))) ∧
      S₂ = Finset.univ.image (fun j : Fin k' => σ (Fin.castLE hkk (Fin.natAdd k j))) := by
  classical
  set e₁ : S₁ ≃ Fin k := Finset.equivFinOfCardEq h₁ with he₁
  set e₂ : S₂ ≃ Fin k' := Finset.equivFinOfCardEq h₂ with he₂
  set φ : Fin (k + k') → Fin p := Fin.addCases (fun i => (e₁.symm i : Fin p))
    (fun j => (e₂.symm j : Fin p)) with hφ
  have hφl : ∀ i : Fin k, φ (Fin.castAdd k' i) = (e₁.symm i : Fin p) := fun i => by
    simp [hφ]
  have hφr : ∀ j : Fin k', φ (Fin.natAdd k j) = (e₂.symm j : Fin p) := fun j => by
    simp [hφ]
  have hinj : Function.Injective φ := by
    intro a b hab
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j =>
        rw [hφl, hφl] at hab
        rw [e₁.symm.injective (Subtype.val_injective hab)]
      | right j =>
        rw [hφl, hφr] at hab
        exact absurd (hab ▸ (e₁.symm i).2) (Finset.disjoint_right.1 hd (e₂.symm j).2)
    | right i =>
      induction b using Fin.addCases with
      | left j =>
        rw [hφr, hφl] at hab
        exact absurd (hab ▸ (e₂.symm i).2) (Finset.disjoint_right.1 hd.symm (e₁.symm j).2)
      | right j =>
        rw [hφr, hφr] at hab
        rw [e₂.symm.injective (Subtype.val_injective hab)]
  obtain ⟨σ, hσ⟩ := exists_perm_castLE_eq hkk φ hinj
  refine ⟨σ, ?_, ?_⟩
  · ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hσ, hφl]
    constructor
    · intro hx
      exact ⟨e₁ ⟨x, hx⟩, by simp⟩
    · rintro ⟨i, rfl⟩
      exact (e₁.symm i).2
  · ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hσ, hφr]
    constructor
    · intro hx
      exact ⟨e₂ ⟨x, hx⟩, by simp⟩
    · rintro ⟨i, rfl⟩
      exact (e₂.symm i).2


end Subsets

end TwoSpecies

section Subsets

open scoped Classical in
/-- **Two selected subsets = two consecutive blocks** (needed for Proposition 3.9). The integral over
`Λ^p` of `∏_{i ∈ S₁} w₁(r̃₁(z_i)) ∏_{i ∈ S₂} w₂(r̃₁(z_i))` for disjoint `S₁, S₂` of cardinalities
`k, k'` is the integral of the same product over the blocks `{i < k}` and `{k ≤ i < k + k'}`, by the
invariance of `Λ^p` and of Lebesgue measure under permutations of the points and the
equivariance of `r̃₁`. -/
theorem lintegral_prod_two_finset_eq {p k k' : ℕ} [Nontrivial (Fin p)] (hkk : k + k' ≤ p)
    {S₁ S₂ : Finset (Fin p)} (hd : Disjoint S₁ S₂) (h₁ : S₁.card = k) (h₂ : S₂.card = k')
    (lam : ℝ) (N : ℕ) (w₁ w₂ : ℝ → ℝ≥0∞) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
        (∏ i ∈ S₁, w₁ (nnRadius lam z i)) * ∏ i ∈ S₂, w₂ (nnRadius lam z i) =
      ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
        (∏ i : Fin k, w₁ (nnRadius lam z (Fin.castLE hkk (Fin.castAdd k' i)))) *
          ∏ j : Fin k', w₂ (nnRadius lam z (Fin.castLE hkk (Fin.natAdd k j))) := by
  obtain ⟨σ, hS₁, hS₂⟩ := exists_perm_two_finset hkk hd h₁ h₂
  rw [← lintegral_comp_perm σ N (fun z => (∏ i : Fin k, w₁ (nnRadius lam z
    (Fin.castLE hkk (Fin.castAdd k' i)))) * ∏ j : Fin k', w₂ (nnRadius lam z
      (Fin.castLE hkk (Fin.natAdd k j))))]
  refine lintegral_congr fun z => ?_
  have hi₁ : Function.Injective fun i : Fin k => σ (Fin.castLE hkk (Fin.castAdd k' i)) :=
    fun a b h => Fin.castAdd_injective k k' (Fin.castLE_injective hkk (σ.injective h))
  have hi₂ : Function.Injective fun j : Fin k' => σ (Fin.castLE hkk (Fin.natAdd k j)) :=
    fun a b h => Fin.natAdd_injective k' k (Fin.castLE_injective hkk (σ.injective h))
  rw [hS₁, hS₂, Finset.prod_image (fun a _ b _ h => hi₁ h),
    Finset.prod_image (fun a _ b _ h => hi₂ h)]
  simp only [nnRadius_comp_equiv]

end Subsets

/-! ### Proposition 3.8 for the weights of the source -/

section Main

namespace TwoSpecies

/-- The product over the two blocks of the selected vertices. -/
theorem prod_twoWeight_eq {p k k' : ℕ} [Nontrivial (Fin p)] (hkk : k + k' ≤ p) (lam : ℝ)
    (w₁ w₂ : ℝ → ℝ≥0∞) (z : Fin p → ℂ) :
    ∏ i : Fin (k + k'), twoWeight k w₁ w₂ i (nnRadius lam z (Fin.castLE hkk i)) =
      (∏ i : Fin k, w₁ (nnRadius lam z (Fin.castLE hkk (Fin.castAdd k' i)))) *
        ∏ j : Fin k', w₂ (nnRadius lam z (Fin.castLE hkk (Fin.natAdd k j))) := by
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [twoWeight]
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp [twoWeight]

end TwoSpecies

/-- **Step 2, radial integrals** (source l. 1174--1179): for `β > 4`, `δ ∈ {0, 1}` there is `C > 0`,
depending on `β` only, such that for `0 < λ ≤ e⁻¹` a cycle within the first group costs
`C λ^{-2}`, a cycle within the second `C λ^{2-β}`, a mixed cycle `C λ^{-β/2}`, any other
displacement of the first group `C ℓ^{1+δ}` and of the second `C λ^{2-β/2}`. -/
theorem exists_twoSpecies_radial_bounds (β : ℝ) (hβ : 4 < β) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      cycleIntegral lam (sourceWeight 4 δ 0 lam) ≤ ENNReal.ofReal (C * cycleScale 4 lam) ∧
      cycleIntegral lam (sourceWeight β 0 0 lam) ≤ ENNReal.ofReal (C * cycleScale β lam) ∧
      pairIntegral lam (sourceWeight 4 δ 0 lam) (sourceWeight β 0 0 lam) ≤
        ENNReal.ofReal (C * lam ^ (-(β / 2))) ∧
      noncycleIntegral lam (sourceWeight 4 δ 0 lam) ≤ ENNReal.ofReal (C * treeScale 4 δ lam) ∧
      noncycleIntegral lam (sourceWeight β 0 0 lam) ≤ ENNReal.ofReal (C * treeScale β 0 lam) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_radial_bounds 4 (by norm_num) δ 0
    (hδ.imp id fun h => ⟨rfl, h⟩) (Or.inl rfl)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_radial_bounds β (by linarith) 0 0 (Or.inl rfl) (Or.inl rfl)
  obtain ⟨C₃, hC₃, h₃⟩ := pairIntegral_sourceWeight_four_le (by linarith : 0 < β) δ
  have hC₁C : C₁ ≤ max C₁ (max C₂ C₃) := le_max_left _ _
  have hC₂C : C₂ ≤ max C₁ (max C₂ C₃) := (le_max_left _ _).trans (le_max_right _ _)
  have hC₃C : C₃ ≤ max C₁ (max C₂ C₃) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max C₁ (max C₂ C₃), lt_max_of_lt_left hC₁, fun lam hlam hlam1 => ?_⟩
  obtain ⟨a₁, a₂⟩ := h₁ lam hlam hlam1
  obtain ⟨b₁, b₂⟩ := h₂ lam hlam hlam1
  exact ⟨a₁.trans (ofReal_mul_le_ofReal_mul hC₁C (cycleScale_pos 4 hlam hlam1).le),
    b₁.trans (ofReal_mul_le_ofReal_mul hC₂C (cycleScale_pos β hlam hlam1).le),
    (h₃ lam hlam (le_one_of_le_exp_neg_one hlam1)).trans
      (ofReal_mul_le_ofReal_mul hC₃C (Real.rpow_nonneg hlam.le _)),
    a₂.trans (ofReal_mul_le_ofReal_mul hC₁C (treeScale_pos 4 δ hlam hlam1).le),
    b₂.trans (ofReal_mul_le_ofReal_mul hC₂C (treeScale_pos β 0 hlam hlam1).le)⟩

/-- **Proposition 3.8 for a fixed `δ`** (source l. 1141--1217; `prop:two species`). -/
theorem lintegral_twoSpecies_le_of_delta (β : ℝ) (hβ : 4 < β) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k k' : ℕ) [Nontrivial (Fin p)] (hkk : k + k' ≤ p), p ≤ N →
      (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            (∏ i : Fin k, sourceWeight 4 δ 0 lam
                (nnRadius lam z (Fin.castLE hkk (Fin.castAdd k' i)))) *
              ∏ j : Fin k', sourceWeight β 0 0 lam
                (nnRadius lam z (Fin.castLE hkk (Fin.natAdd k j))) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * ((k : ℝ) + k') +
            k / 2 * gammaBeta 4 (by norm_num) δ lam k N +
            k' / 2 * gammaBeta β (by linarith) 0 lam k' N)) := by
  obtain ⟨Cr, hCr, hrad⟩ := exists_twoSpecies_radial_bounds β hβ δ hδ
  set C' : ℝ := 4 + Real.log 8 + Real.log (max Cr (Cr ^ 2)) / 2 with hC'
  refine ⟨max (C' + Real.log 2 / 2) 1, lt_max_of_lt_right one_pos,
    fun N p k k' _ hkk hpN hN lam hlam hlam1 => ?_⟩
  have hp2 : 2 ≤ p := Fin.nontrivial_iff_two_le.1 inferInstance
  have hN0 : 0 < N := by omega
  have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
  rcases Nat.eq_zero_or_pos (k + k') with ht | ht
  · -- both groups are empty
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ k' = 0 := by omega
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, setLIntegral_const, one_mul]
    rw [volume_pi_box_fin N]
    simp only [Nat.cast_zero, mul_zero, zero_div, zero_mul, add_zero]
    rw [Real.exp_nat_mul, Real.exp_log hN0', ENNReal.ofReal_pow hN0'.le, ENNReal.ofReal_natCast]
  · have hkN : k ≤ N := (Nat.le_add_right k k').trans (hkk.trans hpN)
    have hk'N : k' ≤ N := (Nat.le_add_left k' k).trans (hkk.trans hpN)
    obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := hrad lam hlam hlam1
    have hA₁ := cycleScale_pos 4 hlam hlam1
    have hA₂ := cycleScale_pos β hlam hlam1
    have hB₁ := treeScale_pos 4 δ hlam hlam1
    have hB₂ := treeScale_pos β 0 hlam hlam1
    have hA : (lam ^ (-(β / 2))) ^ 2 = cycleScale 4 lam * cycleScale β lam := by
      rw [cycleScale_of_two_lt (by norm_num), cycleScale_of_two_lt (by linarith),
        ← Real.rpow_natCast, ← Real.rpow_mul hlam.le, ← Real.rpow_add hlam]
      congr 1
      push_cast
      ring
    have hS := lintegral_twoSpecies_le_of_scales hkk hpN hN ht lam
      (measurable_sourceWeight 4 δ 0 lam) (measurable_sourceWeight β 0 0 lam) hA₁ hA₂
      (Real.rpow_pos_of_pos hlam _) hB₁ hB₂ hCr hA hc1 hc2 hc3 hc4 hc5
    simp_rw [prod_twoWeight_eq hkk] at hS
    refine hS.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have hreg := log_regroup (k := k) (k' := k') hA₁ hA₂ hB₁ hB₂ hN0
    rw [gammaBeta_eq 4 (by norm_num) δ hlam hkN, gammaBeta_eq β (by linarith) 0 hlam hk'N]
    have hCt : (C' + Real.log 2 / 2) * ((k : ℝ) + k') ≤ max (C' + Real.log 2 / 2) 1 * ((k : ℝ) + k') :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    push_cast at hreg ⊢
    rw [← hC']
    linarith only [hreg, hCt]

/-- **Proposition 3.8** (`prop:two species`, source l. 1141--1217, eq. (eq:two species)), in the
weighted form `∏_{i<k} sourceWeight 4 δ 0 λ (r̃₁(z_i)) ∏_{k ≤ i < k + k'} sourceWeight β 0 0 λ (r̃₁(z_i))`.
For `β > 4` there is `C_β > 0`, depending on `β` only, such that for `δ ∈ {0, 1}`, all integers
`k + k' ≤ p ≤ N` with `N ≤ 2p` and `p ≥ 2` (encoded by `Nontrivial (Fin p)`), and `0 < λ ≤ e⁻¹`,
`∫_{Λ^p} ∏_{i<k} w₁(r̃₁(z_i)) ∏_{k ≤ i < k + k'} w₂(r̃₁(z_i)) dz ≤
  exp (p log N + C_β (k + k') + (k/2) γ_{4,k} + (k'/2) γ_{β,k'})`
with `γ_{β,k} = gammaBeta β _ δ λ k N` (the statement `log ∫ ≤ X` being written as `∫ ≤ exp X`,
ruling R10). The first block `{i < k}` is `Fin.castAdd k'` and the second `{k ≤ i < k + k'}` is
`Fin.natAdd k`. -/
theorem lintegral_twoSpecies_le (β : ℝ) (hβ : 4 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℕ, (δ = 0 ∨ δ = 1) →
      ∀ (N p k k' : ℕ) [Nontrivial (Fin p)] (hkk : k + k' ≤ p), p ≤ N →
        (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
          ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
              (∏ i : Fin k, sourceWeight 4 δ 0 lam
                  (nnRadius lam z (Fin.castLE hkk (Fin.castAdd k' i)))) *
                ∏ j : Fin k', sourceWeight β 0 0 lam
                  (nnRadius lam z (Fin.castLE hkk (Fin.natAdd k j))) ≤
            ENNReal.ofReal (Real.exp (p * Real.log N + C * ((k : ℝ) + k') +
              k / 2 * gammaBeta 4 (by norm_num) δ lam k N +
              k' / 2 * gammaBeta β (by linarith) 0 lam k' N)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := lintegral_twoSpecies_le_of_delta β hβ 0 (Or.inl rfl)
  obtain ⟨C₁, hC₁, h₁⟩ := lintegral_twoSpecies_le_of_delta β hβ 1 (Or.inr rfl)
  refine ⟨max C₀ C₁, lt_max_of_lt_left hC₀, fun δ hδ N p k k' _ hkk hpN hN lam hlam hlam1 => ?_⟩
  have key : ∀ {C : ℝ}, C ≤ max C₀ C₁ → ∀ γ₁ γ₂ : ℝ,
      p * Real.log N + C * ((k : ℝ) + k') + k / 2 * γ₁ + k' / 2 * γ₂ ≤
        p * Real.log N + max C₀ C₁ * ((k : ℝ) + k') + k / 2 * γ₁ + k' / 2 * γ₂ := by
    intro C hC γ₁ γ₂
    have : C * ((k : ℝ) + k') ≤ max C₀ C₁ * ((k : ℝ) + k') :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    linarith
  rcases hδ with rfl | rfl
  · exact (h₀ N p k k' hkk hpN hN lam hlam hlam1).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (key (le_max_left _ _) _ _)))
  · exact (h₁ N p k k' hkk hpN hN lam hlam hlam1).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (key (le_max_right _ _) _ _)))

/-! #### Two selected subsets -/

/-- **Proposition 3.8 for two selected subsets** (needed by Proposition 3.9): the bound of
`lintegral_twoSpecies_le` holds for `∏_{i ∈ S₁} w₁(r̃₁(z_i)) ∏_{i ∈ S₂} w₂(r̃₁(z_i))` for all
disjoint `S₁, S₂ ⊆ Fin p` with `|S₁| = k`, `|S₂| = k'` (via `lintegral_prod_two_finset_eq`). -/
theorem lintegral_twoSpecies_finset_le (β : ℝ) (hβ : 4 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℕ, (δ = 0 ∨ δ = 1) →
      ∀ (N p k k' : ℕ) [Nontrivial (Fin p)] (S₁ S₂ : Finset (Fin p)), Disjoint S₁ S₂ →
        S₁.card = k → S₂.card = k' → p ≤ N → (N : ℝ) ≤ 2 * p →
          ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
            ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
                (∏ i ∈ S₁, sourceWeight 4 δ 0 lam (nnRadius lam z i)) *
                  ∏ i ∈ S₂, sourceWeight β 0 0 lam (nnRadius lam z i) ≤
              ENNReal.ofReal (Real.exp (p * Real.log N + C * ((k : ℝ) + k') +
                k / 2 * gammaBeta 4 (by norm_num) δ lam k N +
                k' / 2 * gammaBeta β (by linarith) 0 lam k' N)) := by
  obtain ⟨C, hC, h⟩ := lintegral_twoSpecies_le β hβ
  refine ⟨C, hC, fun δ hδ N p k k' _ S₁ S₂ hd h₁ h₂ hpN hN lam hlam hlam1 => ?_⟩
  have hkk : k + k' ≤ p := by
    rw [← h₁, ← h₂, ← Finset.card_union_of_disjoint hd]
    simpa using Finset.card_le_univ (S₁ ∪ S₂)
  rw [lintegral_prod_two_finset_eq hkk hd h₁ h₂ lam N]
  exact h δ hδ N p k k' hkk hpN hN lam hlam hlam1

/-! #### The source form -/

variable {p k k' : ℕ} [Nontrivial (Fin p)]

/-- The energy `F_{k,k'}(z_1, …, z_p) = ½ ∑_{i=k+1}^{k+k'} log r̃₁(z_i)` of the second marked group
(source l. 1145--1147). -/
noncomputable def auxEnergySecond (hkk : k + k' ≤ p) (lam : ℝ) (z : Fin p → ℂ) : ℝ :=
  (1 / 2) * ∑ j : Fin k', Real.log (nnRadius lam z (Fin.castLE hkk (Fin.natAdd k j)))

/-- The product of the source weights over the two blocks is the integrand of Proposition 3.8:
`exp (-4 F_k - β F_{k,k'}) ∏_{i ≤ k} (1 + log (r̃₁(z_i)/λ))^δ`. -/
theorem prod_twoSpecies_eq (hkk : k + k' ≤ p) (β : ℝ) (δ : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (z : Fin p → ℂ) :
    (∏ i : Fin k, sourceWeight 4 δ 0 lam (nnRadius lam z (Fin.castLE hkk (Fin.castAdd k' i)))) *
        ∏ j : Fin k', sourceWeight β 0 0 lam (nnRadius lam z (Fin.castLE hkk (Fin.natAdd k j))) =
      ENNReal.ofReal (Real.exp (-4 * auxEnergy ((Nat.le_add_right k k').trans hkk) lam z -
          β * auxEnergySecond hkk lam z) *
        ∏ i : Fin k, (1 + Real.log (nnRadius lam z
          (Fin.castLE ((Nat.le_add_right k k').trans hkk) i) / lam)) ^ δ) := by
  have hc : ∀ i : Fin k, Fin.castLE ((Nat.le_add_right k k').trans hkk) i =
      Fin.castLE hkk (Fin.castAdd k' i) := fun i => Fin.ext rfl
  have h1 := prod_sourceWeight_eq 4 δ 0 hlam Finset.univ
    (fun i : Fin k => nnRadius lam z (Fin.castLE hkk (Fin.castAdd k' i)))
    (fun _ _ => le_nnRadius lam z _)
  have h2 := prod_sourceWeight_eq β 0 0 hlam Finset.univ
    (fun j : Fin k' => nnRadius lam z (Fin.castLE hkk (Fin.natAdd k j)))
    (fun _ _ => le_nnRadius lam z _)
  have hnn : 0 ≤ (Real.exp (-4 * (1 / 2 * ∑ i : Fin k, Real.log (nnRadius lam z
        (Fin.castLE hkk (Fin.castAdd k' i))))) *
        ∏ i : Fin k, (1 + Real.log (nnRadius lam z (Fin.castLE hkk (Fin.castAdd k' i)) / lam)) ^ δ) *
      ∏ i : Fin k, (1 + |Real.log (nnRadius lam z (Fin.castLE hkk (Fin.castAdd k' i)))|) ^ 0 := by
    refine mul_nonneg (mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun i _ => ?_))
      (Finset.prod_nonneg fun i _ => by positivity)
    exact pow_nonneg (log_div_nonneg_of_le hlam (le_nnRadius lam z _)) _
  rw [h1, h2, ← ENNReal.ofReal_mul hnn]
  congr 1
  have e : -4 * auxEnergy ((Nat.le_add_right k k').trans hkk) lam z -
        β * auxEnergySecond hkk lam z =
      -4 * (1 / 2 * ∑ i : Fin k, Real.log (nnRadius lam z (Fin.castLE hkk (Fin.castAdd k' i)))) +
        -β * (1 / 2 * ∑ j : Fin k', Real.log (nnRadius lam z (Fin.castLE hkk (Fin.natAdd k j)))) := by
    simp only [auxEnergy, auxEnergySecond, hc]
    ring
  simp only [hc]
  rw [e, Real.exp_add]
  simp only [pow_zero, Finset.prod_const_one, mul_one]
  exact mul_right_comm _ _ _

/-- **Proposition 3.8 in the form of the source** (`prop:two species`, l. 1141--1153, eq.
(eq:two species)): for `β > 4`, `δ ∈ {0, 1}`, integers `k + k' ≤ p ≤ N` with `p ≥ max (2, N/2)` and
`0 < λ ≤ e⁻¹`,
`∫_{Λ^p} exp (-4 F_k(Z_p) - β F_{k,k'}(Z_p)) ∏_{i ≤ k} (1 + log (r̃₁(z_i)/λ))^δ dZ_p
  ≤ exp (p log N + C_β (k + k') + (k/2) γ_{4,k} + (k'/2) γ_{β,k'})`
(the statement `log ∫ ≤ X` being written as `∫ ≤ exp X`, ruling R10). -/
theorem prop_twoSpecies (β : ℝ) (hβ : 4 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℕ, (δ = 0 ∨ δ = 1) →
      ∀ (N p k k' : ℕ) [Nontrivial (Fin p)] (hkk : k + k' ≤ p), p ≤ N →
        (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
          ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
              ENNReal.ofReal (Real.exp (-4 * auxEnergy ((Nat.le_add_right k k').trans hkk) lam z -
                  β * auxEnergySecond hkk lam z) *
                ∏ i : Fin k, (1 + Real.log (nnRadius lam z
                  (Fin.castLE ((Nat.le_add_right k k').trans hkk) i) / lam)) ^ δ) ≤
            ENNReal.ofReal (Real.exp (p * Real.log N + C * ((k : ℝ) + k') +
              k / 2 * gammaBeta 4 (by norm_num) δ lam k N +
              k' / 2 * gammaBeta β (by linarith) 0 lam k' N)) := by
  obtain ⟨C, hC, h⟩ := lintegral_twoSpecies_le β hβ
  refine ⟨C, hC, fun δ hδ N p k k' _ hkk hpN hN lam hlam hlam1 => ?_⟩
  simp_rw [← prod_twoSpecies_eq hkk β δ hlam]
  exact h δ hδ N p k k' hkk hpN hN lam hlam hlam1

end Main

end TwoComponentCoulomb

end
