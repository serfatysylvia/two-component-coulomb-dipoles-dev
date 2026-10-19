/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import TwoComponentCoulomb.UpperBound.AuxIntegration
public import TwoComponentCoulomb.UpperBound.AuxOptimization

/-!
# Proposition 3.7: the nearest-neighbour model on a subset of `k` points

Source: Proposition 3.7 (`prop:auxk`, l. 1008--1031) and its proof
(l. 1035--1140), in the weighted generality of ruling R12c: the integrand of the source,
`exp (-β F_k) ∏_{i ≤ k} (1 + log (r̃₁/λ))^δ ∏_{i ≤ k} (1 + |log r̃₁|)^{δ'}`, is
`∏_{i<k} sourceWeight β δ δ' λ (r̃₁(z_i))` (the bridge `prod_sourceWeight_eq`).

The proof assembles the three steps of the source:

* *Step 1* (`RestrictedGraph.lean`; here the partition of `Λ^p`, l. 1054, 1081--1086): the cells
  `Λ^p ∩ {γ'_p = g}` form a finite measurable partition, and the integral is the sum over the
  types `(k₀, k₁)` and the graphs `g ∈ D(k₀, k₁)` of the cell integrals.
* *Step 2* (`AuxIntegration*.lean`): each cell integral is at most
  `C^k N^{p-k+k₀} I_cyc^{k₀} I_non^{k-2k₀}`; the radial integrals of the source weights are
  bounded by `C · cycleScale β λ` and `C · treeScale β δ λ` (`exists_radial_bounds`).
* *Step 3* (`AuxOptimization.lean`): the entropy combination of the graph count with the cell
  bounds, the cost `(k+1)² ≤ 4^k` of the sum over `(k₀, k₁)`, and the maximization of the affine
  function `x log (k/N) + ψ_β(x)` on `[0, 1/2]`, whose maximum is `γ_{β,k}/2`.

## Main results

* `TwoComponentCoulomb.lintegral_pi_box_eq_sum_cell`, `…_eq_sum_types`: the partition of `Λ^p`
  (l. 1054).
* `TwoComponentCoulomb.lintegral_pi_box_prod_fin_zero`: the case `k = 0` (`N^p`, l. 1036).
* `TwoComponentCoulomb.lintegral_prod_le_of_scales`: Steps 2--3 for an abstract radial weight with
  cycle and non-cycle displacement integrals of sizes `C_a A` and `C_b B`.
* `TwoComponentCoulomb.lintegral_auxk_le`: **Proposition 3.7** for `sourceWeight β δ δ' λ`, in the
  unified form with `γ_{β,k} = gammaBeta β δ λ k N`; `TwoComponentCoulomb.lintegral_auxk_abs`,
  `…_lt_two`, `…_two`, `…_two_lt_four`, `…_four`, `…_four_lt`: one theorem for each case of the
  source (`β = 0` with `δ' = 1`; `0 ≤ β < 2`; `β = 2`; `2 < β < 4`; `β = 4` with `δ ∈ {0, 1}`;
  `β > 4`) with the explicit `γ_{β,k}`.
* `TwoComponentCoulomb.prop_auxk`: Proposition 3.7 in the source's own form, with
  `exp (-β F_k)` (`TwoComponentCoulomb.auxEnergy`) and the factors
  `(1 + log (r̃₁/λ))^δ (1 + |log r̃₁|)^{δ'}`.
* `TwoComponentCoulomb.lintegral_auxk_finset_le`, `…_finset_abs`, …: the same bounds for
  `∏_{i ∈ S}` with `S ⊆ Fin p`, `|S| = k` (via `lintegral_prod_finset_eq`: permutation invariance of
  `Λ^p` and of Lebesgue measure, and equivariance of `nnRadius`); used by Propositions 3.8, 3.9.

The constants `C` are quantified before `N, p, k, λ` (ruling R11): they depend on `β` (and `δ`)
only. The hypothesis `p ≥ 2` is the instance `Nontrivial (Fin p)`, and `p ≥ N/2` is `N ≤ 2p`;
`0 ≤ k ≤ p ≤ N`. A bound `log ∫ ≤ X` is stated as `∫ ≤ ofReal (exp X)` (ruling R10).
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### Step 1: the partition of `Λ^p` by the restricted graph (source l. 1054, 1081--1086) -/

section Partition

variable {p k : ℕ} [Nontrivial (Fin p)] (hk : k ≤ p) (key : Fin p ↪ ℕ)

/-- The cells `Λ^p ∩ {γ'_p = g}` cover `Λ^p`. -/
theorem pi_box_eq_biUnion_cell (N : ℕ) :
    (Set.univ.pi fun _ : Fin p => box N) =
      ⋃ g ∈ (Finset.univ : Finset (Fin k → Fin p)),
        (Set.univ.pi fun _ : Fin p => box N) ∩ {z | restrictedNnMap hk key z = g} := by
  ext z
  simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · intro hz
    exact ⟨restrictedNnMap hk key z, hz, rfl⟩
  · rintro ⟨g, hz, -⟩
    exact hz

/-- **Step 1, graph partition** (source l. 1054, 1081--1086): for any
function `f` the integral over `Λ^p` is the sum over the restricted graphs `g : Fin k → Fin p` of
the integrals over the cells `Λ^p ∩ {γ'_p = g}`, which form a finite measurable partition. -/
theorem lintegral_pi_box_eq_sum_cell (N : ℕ) (f : (Fin p → ℂ) → ℝ≥0∞) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), f z =
      ∑ g : Fin k → Fin p,
        ∫⁻ z in (Set.univ.pi fun _ : Fin p => box N) ∩ {z | restrictedNnMap hk key z = g}, f z := by
  conv_lhs => rw [pi_box_eq_biUnion_cell hk key N]
  refine lintegral_biUnion_finset ?_ (fun g _ => ?_) f
  · intro g _ g' _ hgg'
    refine Set.disjoint_left.2 fun z hz hz' => hgg' ?_
    rw [← hz.2, ← hz'.2]
  · exact (MeasurableSet.univ_pi fun _ => measurableSet_box N).inter
      (measurableSet_restrictedNnMap_eq hk key g)

/-- The cell of a non-admissible graph is empty. -/
theorem cell_eq_empty_of_not_admissible (N : ℕ) {g : Fin k → Fin p}
    (hg : ¬IsAdmissibleRestriction g) :
    (Set.univ.pi fun _ : Fin p => box N) ∩ {z | restrictedNnMap hk key z = g} = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun z hz => hg ?_
  rw [← hz.2]
  exact isAdmissibleRestriction_restrictedNnMap hk key z

open scoped Classical in
/-- **Step 1, sum over the graph types** (source l. 1054, 1081--1086, 1134): the integral over `Λ^p`
is the sum over `k₀, k₁ ≤ k` and the graphs `g ∈ D(k₀, k₁)` of the integrals over the cells
`{γ'_p = g}`. -/
theorem lintegral_pi_box_eq_sum_types (N : ℕ) (f : (Fin p → ℂ) → ℝ≥0∞) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), f z =
      ∑ k₀ ∈ range (k + 1), ∑ k₁ ∈ range (k + 1), ∑ g ∈ restrictedGraphs p k k₀ k₁,
        ∫⁻ z in (Set.univ.pi fun _ : Fin p => box N) ∩ {z | restrictedNnMap hk key z = g}, f z := by
  rw [lintegral_pi_box_eq_sum_cell hk key N f]
  set G : (Fin k → Fin p) → ℝ≥0∞ := fun g =>
    ∫⁻ z in (Set.univ.pi fun _ : Fin p => box N) ∩ {z | restrictedNnMap hk key z = g}, f z
    with hG
  have hG0 : ∀ g, ¬IsAdmissibleRestriction g → G g = 0 := by
    intro g hg
    simp only [hG]
    rw [cell_eq_empty_of_not_admissible hk key N hg]
    simp
  have h1 : ∑ g : Fin k → Fin p, G g =
      ∑ g ∈ (Finset.univ : Finset (Fin k → Fin p)).filter IsAdmissibleRestriction, G g := by
    refine (Finset.sum_filter_of_ne fun g _ hne => ?_).symm
    by_contra hg
    exact hne (hG0 g hg)
  have hmaps : ∀ g ∈ (Finset.univ : Finset (Fin k → Fin p)).filter IsAdmissibleRestriction,
      ((twoCyclesIn g).card, (rootsOf g).card) ∈ range (k + 1) ×ˢ range (k + 1) := by
    intro g _
    have := two_mul_card_twoCyclesIn_add_card_rootsOf_le g
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps G, Finset.sum_product]
  refine Finset.sum_congr rfl fun k₀ _ => Finset.sum_congr rfl fun k₁ _ => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext g
  simp [restrictedGraphs, and_comm]


/-- **Step 1 and Step 3, summation over the graph types** (source l. 1134): if the integral over
every cell `{γ'_p = g}` with `g ∈ D(k₀, k₁)` is at most `B k₀ k₁`, then the integral over `Λ^p` is at
most `∑_{k₀, k₁ ≤ k} |D(k₀, k₁)| · B k₀ k₁`. -/
theorem lintegral_pi_box_le_sum_types_of_le (N : ℕ) (f : (Fin p → ℂ) → ℝ≥0∞)
    (B : ℕ → ℕ → ℝ≥0∞)
    (hB : ∀ k₀ k₁, ∀ g ∈ restrictedGraphs p k k₀ k₁,
      ∫⁻ z in (Set.univ.pi fun _ : Fin p => box N) ∩ {z | restrictedNnMap hk key z = g}, f z ≤
        B k₀ k₁) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), f z ≤
      ∑ k₀ ∈ range (k + 1), ∑ k₁ ∈ range (k + 1), (restrictedGraphs p k k₀ k₁).card • B k₀ k₁ := by
  rw [lintegral_pi_box_eq_sum_types hk key N f]
  refine sum_le_sum fun k₀ _ => sum_le_sum fun k₁ _ => ?_
  calc _ ≤ ∑ _g ∈ restrictedGraphs p k k₀ k₁, B k₀ k₁ := sum_le_sum fun g hg => hB k₀ k₁ g hg
    _ = _ := by rw [sum_const]

end Partition


/-! ### Steps 2 and 3: the bound for abstract radial weights -/

section Assembly

open AuxIntegration

variable {p k : ℕ} [Nontrivial (Fin p)] (hk : k ≤ p)

/-- **Step 2 for one cell, in real form** (source l. 1087--1107): if the cycle and non-cycle
displacement integrals of the weight `w` are at most `a` and `b`, the integral over the cell of
`g ∈ D(k₀, k₁)` is at most `e^{2k} N^{p - k + k₀} a^{k₀} b^{k - 2 k₀}`. -/
theorem lintegral_cell_le_ofReal (key : Fin p ↪ ℕ) {N k₀ k₁ : ℕ} (hN : (N : ℝ) ≤ 2 * p) (lam : ℝ)
    {w : ℝ → ℝ≥0∞} (hw : Measurable w) {g : Fin k → Fin p} (hg : g ∈ restrictedGraphs p k k₀ k₁)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hcyc : cycleIntegral lam w ≤ ENNReal.ofReal a)
    (hnon : noncycleIntegral lam w ≤ ENNReal.ofReal b) :
    ∫⁻ z in (Set.univ.pi fun _ : Fin p => box N) ∩ {z | restrictedNnMap hk key z = g},
        ∏ i : Fin k, w (nnRadius lam z (Fin.castLE hk i)) ≤
      ENNReal.ofReal (Real.exp 2 ^ k * (N : ℝ) ^ (p - k + k₀) * (a ^ k₀ * b ^ (k - 2 * k₀))) := by
  refine (lintegral_cellSet_le hk g key hN lam hw hg).trans ?_
  have hexp : (0 : ℝ) ≤ Real.exp 2 := (Real.exp_pos 2).le
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hexp, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow ha, ENNReal.ofReal_pow hb, ENNReal.ofReal_natCast]
  gcongr

/-- **Proposition 3.7 for an abstract radial weight** (source l. 1126--1140). Let `w` be a
measurable radial weight whose `2`-cycle displacement integral is at most `C_a A` and whose
non-cycle displacement integral is at most `C_b B`. Then for `1 ≤ k ≤ p ≤ N ≤ 2p`
`∫_{Λ^p} ∏_{i<k} w(r̃₁(z_i)) dz ≤ exp (p log N + C k + (k/2) log (max (A k / N) (B²)))`,
with `C = 4 + log 8 + (log C_m)/2` for any `C_m ≥ max (C_a, C_b²)`. -/
theorem lintegral_prod_le_of_scales {N : ℕ} (hpN : p ≤ N) (hN : (N : ℝ) ≤ 2 * p) (hk1 : 1 ≤ k)
    (lam : ℝ) {w : ℝ → ℝ≥0∞} (hw : Measurable w) {A B Ca Cb Cm : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hCa : 0 < Ca) (hCb : 0 < Cb) (hCaCm : Ca ≤ Cm) (hCbCm : Cb ^ 2 ≤ Cm)
    (hcyc : cycleIntegral lam w ≤ ENNReal.ofReal (Ca * A))
    (hnon : noncycleIntegral lam w ≤ ENNReal.ofReal (Cb * B)) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
        ∏ i : Fin k, w (nnRadius lam z (Fin.castLE hk i)) ≤
      ENNReal.ofReal (Real.exp (p * Real.log N + (4 + Real.log 8 + Real.log Cm / 2) * k +
        k / 2 * Real.log (max (A * k / N) (B ^ 2)))) := by
  classical
  have ha : 0 ≤ Ca * A := (mul_pos hCa hA).le
  have hb : 0 ≤ Cb * B := (mul_pos hCb hB).le
  have hT : ∀ k₀ : ℕ, 0 ≤ Real.exp 2 ^ k * (N : ℝ) ^ (p - k + k₀) *
      ((Ca * A) ^ k₀ * (Cb * B) ^ (k - 2 * k₀)) := fun k₀ => by positivity
  calc _ ≤ ∑ k₀ ∈ range (k + 1), ∑ k₁ ∈ range (k + 1), (restrictedGraphs p k k₀ k₁).card •
        ENNReal.ofReal (Real.exp 2 ^ k * (N : ℝ) ^ (p - k + k₀) *
          ((Ca * A) ^ k₀ * (Cb * B) ^ (k - 2 * k₀))) :=
        lintegral_pi_box_le_sum_types_of_le hk Fin.valEmbedding N _ _ fun k₀ k₁ g hg =>
          lintegral_cell_le_ofReal hk Fin.valEmbedding hN lam hw hg ha hb hcyc hnon
    _ = ∑ k₀ ∈ range (k + 1), ∑ k₁ ∈ range (k + 1),
        ENNReal.ofReal ((restrictedGraphs p k k₀ k₁).card *
          (Real.exp 2 ^ k * (N : ℝ) ^ (p - k + k₀) * ((Ca * A) ^ k₀ * (Cb * B) ^ (k - 2 * k₀)))) := by
        refine sum_congr rfl fun k₀ _ => sum_congr rfl fun k₁ _ => ?_
        rw [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (∑ k₀ ∈ range (k + 1), ∑ k₁ ∈ range (k + 1),
        ((restrictedGraphs p k k₀ k₁).card : ℝ) *
          (Real.exp 2 ^ k * (N : ℝ) ^ (p - k + k₀) * ((Ca * A) ^ k₀ * (Cb * B) ^ (k - 2 * k₀)))) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun k₀ _ => sum_nonneg fun k₁ _ =>
          mul_nonneg (Nat.cast_nonneg _) (hT k₀)]
        refine sum_congr rfl fun k₀ _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun k₁ _ => mul_nonneg (Nat.cast_nonneg _) (hT k₀)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hmain := sum_le_exp (N := N) (p := p) (k := k) hk1 hk hpN hA hB hCa hCb hCaCm hCbCm
          (fun k₀ k₁ => ((restrictedGraphs p k k₀ k₁).card : ℝ))
          (fun k₀ k₁ h => by exact_mod_cast card_restrictedGraphs_mul_le p k k₀ k₁)
          (fun k₀ k₁ h => by
            rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro g hg
            have := two_mul_add_le_of_mem_restrictedGraphs hg
            omega)
        exact hmain

end Assembly


/-! ### The radial integrals for the weights of the source -/

section Radial

open AuxIntegration

theorem ofReal_mul_le_ofReal_mul {C C' A : ℝ} (h : C ≤ C') (hA : 0 ≤ A) :
    ENNReal.ofReal (C * A) ≤ ENNReal.ofReal (C' * A) :=
  ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h hA)

theorem le_one_of_le_exp_neg_one {lam : ℝ} (h : lam ≤ Real.exp (-1)) : lam ≤ 1 :=
  h.trans (Real.exp_le_one_iff.2 (by norm_num))

/-- **Step 2, radial integrals in all cases of the proposition** (source l. 1108--1118). For
`β ≥ 0`, with `δ = 0` unless `β = 4` (where `δ ≤ 1`) and `δ' = 0` unless `β = 0` (where `δ' = 1`),
there is `C > 0` depending on `β` and `δ` only such that, for `0 < λ ≤ e⁻¹`, the cycle displacement
integral of `sourceWeight β δ δ' λ` is at most `C · cycleScale β λ` and its non-cycle displacement
integral is at most `C · treeScale β δ λ`. -/
theorem exists_radial_bounds (β : ℝ) (hβ : 0 ≤ β) (δ δ' : ℕ) (hδ : δ = 0 ∨ (β = 4 ∧ δ = 1))
    (hδ' : δ' = 0 ∨ (β = 0 ∧ δ' = 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
      cycleIntegral lam (sourceWeight β δ δ' lam) ≤ ENNReal.ofReal (C * cycleScale β lam) ∧
      noncycleIntegral lam (sourceWeight β δ δ' lam) ≤ ENNReal.ofReal (C * treeScale β δ lam) := by
  -- the common constant
  have key : ∀ {Ca Cb : ℝ}, 0 ≤ Ca → 0 ≤ Cb → ∃ C : ℝ, 0 < C ∧ Ca ≤ C ∧ Cb ≤ C :=
    fun {Ca Cb} h1 h2 =>
      ⟨max Ca Cb + 1, by positivity, by linarith [le_max_left Ca Cb],
        by linarith [le_max_right Ca Cb]⟩
  rcases hδ' with rfl | ⟨rfl, rfl⟩
  · -- `δ' = 0`
    rcases lt_or_ge β 2 with h2 | h2
    · have hδ0 : δ = 0 := by
        rcases hδ with h | ⟨h4, -⟩
        · exact h
        · exfalso; linarith
      subst hδ0
      obtain ⟨Ca, hCa0, hCa⟩ := cycleIntegral_sourceWeight_le_of_lt_two h2
      obtain ⟨Cb, hCb0, hCb⟩ := noncycleIntegral_sourceWeight_le_of_lt_four (by linarith : β < 4)
      obtain ⟨C, hC, hCaC, hCbC⟩ := key hCa0 hCb0
      refine ⟨C, hC, fun lam hlam hlam1 => ⟨?_, ?_⟩⟩
      · rw [cycleScale_of_lt_two h2]
        refine (hCa lam hlam (le_one_of_le_exp_neg_one hlam1)).trans ?_
        simpa using ofReal_mul_le_ofReal_mul hCaC zero_le_one
      · rw [treeScale_of_lt_four (by linarith)]
        refine (hCb lam hlam (le_one_of_le_exp_neg_one hlam1)).trans ?_
        simpa using ofReal_mul_le_ofReal_mul hCbC zero_le_one
    rcases eq_or_lt_of_le h2 with h2 | h2
    · subst h2
      have hδ0 : δ = 0 := by
        rcases hδ with h | ⟨h4, -⟩
        · exact h
        · exfalso; norm_num at h4
      subst hδ0
      obtain ⟨Ca, hCa0, hCa⟩ := cycleIntegral_sourceWeight_le_two
      obtain ⟨Cb, hCb0, hCb⟩ := noncycleIntegral_sourceWeight_le_of_lt_four (by norm_num : (2 : ℝ) < 4)
      obtain ⟨C, hC, hCaC, hCbC⟩ := key hCa0 hCb0
      refine ⟨C, hC, fun lam hlam hlam1 => ⟨?_, ?_⟩⟩
      · rw [cycleScale_two]
        exact (hCa lam hlam hlam1).trans
          (ofReal_mul_le_ofReal_mul hCaC (abs_nonneg _))
      · rw [treeScale_of_lt_four (by norm_num)]
        refine (hCb lam hlam (le_one_of_le_exp_neg_one hlam1)).trans ?_
        simpa using ofReal_mul_le_ofReal_mul hCbC zero_le_one
    rcases lt_or_ge β 4 with h4 | h4
    · have hδ0 : δ = 0 := by
        rcases hδ with h | ⟨h4', -⟩
        · exact h
        · exfalso; linarith
      subst hδ0
      obtain ⟨Ca, hCa0, hCa⟩ := cycleIntegral_sourceWeight_le_of_two_lt h2 0
      obtain ⟨Cb, hCb0, hCb⟩ := noncycleIntegral_sourceWeight_le_of_lt_four h4
      obtain ⟨C, hC, hCaC, hCbC⟩ := key hCa0 hCb0
      refine ⟨C, hC, fun lam hlam hlam1 => ⟨?_, ?_⟩⟩
      · rw [cycleScale_of_two_lt h2]
        exact (hCa lam hlam (le_one_of_le_exp_neg_one hlam1)).trans
          (ofReal_mul_le_ofReal_mul hCaC (Real.rpow_nonneg hlam.le _))
      · rw [treeScale_of_lt_four h4]
        refine (hCb lam hlam (le_one_of_le_exp_neg_one hlam1)).trans ?_
        simpa using ofReal_mul_le_ofReal_mul hCbC zero_le_one
    rcases eq_or_lt_of_le h4 with h4 | h4
    · subst h4
      obtain ⟨Ca, hCa0, hCa⟩ := cycleIntegral_sourceWeight_le_of_two_lt (by norm_num : (2 : ℝ) < 4) δ
      obtain ⟨Cb, hCb0, hCb⟩ := noncycleIntegral_sourceWeight_le_four δ
      obtain ⟨C, hC, hCaC, hCbC⟩ := key hCa0 hCb0
      refine ⟨C, hC, fun lam hlam hlam1 => ⟨?_, ?_⟩⟩
      · rw [cycleScale_of_two_lt (by norm_num)]
        exact (hCa lam hlam (le_one_of_le_exp_neg_one hlam1)).trans
          (ofReal_mul_le_ofReal_mul hCaC (Real.rpow_nonneg hlam.le _))
      · rw [treeScale_four, add_comm 1 δ]
        exact (hCb lam hlam hlam1).trans
          (ofReal_mul_le_ofReal_mul hCbC (pow_nonneg (abs_nonneg _) _))
    · have hδ0 : δ = 0 := by
        rcases hδ with h | ⟨h4', -⟩
        · exact h
        · exfalso; linarith
      subst hδ0
      obtain ⟨Ca, hCa0, hCa⟩ := cycleIntegral_sourceWeight_le_of_two_lt (by linarith : (2 : ℝ) < β) 0
      obtain ⟨Cb, hCb0, hCb⟩ := noncycleIntegral_sourceWeight_le_of_four_lt h4 0
      obtain ⟨C, hC, hCaC, hCbC⟩ := key hCa0 hCb0
      refine ⟨C, hC, fun lam hlam hlam1 => ⟨?_, ?_⟩⟩
      · rw [cycleScale_of_two_lt (by linarith)]
        exact (hCa lam hlam (le_one_of_le_exp_neg_one hlam1)).trans
          (ofReal_mul_le_ofReal_mul hCaC (Real.rpow_nonneg hlam.le _))
      · rw [treeScale_of_four_lt h4]
        exact (hCb lam hlam (le_one_of_le_exp_neg_one hlam1)).trans
          (ofReal_mul_le_ofReal_mul hCbC (Real.rpow_nonneg hlam.le _))
  · -- `β = 0`, `δ = 0`, `δ' = 1`
    rcases hδ with rfl | ⟨h4, -⟩
    · obtain ⟨Ca, hCa0, hCa⟩ := cycleIntegral_sourceWeight_abs_le
      obtain ⟨Cb, hCb0, hCb⟩ := noncycleIntegral_sourceWeight_abs_le
      obtain ⟨C, hC, hCaC, hCbC⟩ := key hCa0 hCb0
      refine ⟨C, hC, fun lam hlam hlam1 => ⟨?_, ?_⟩⟩
      · rw [cycleScale_of_lt_two (by norm_num)]
        refine (hCa lam hlam (le_one_of_le_exp_neg_one hlam1)).trans ?_
        simpa using ofReal_mul_le_ofReal_mul hCaC zero_le_one
      · rw [treeScale_of_lt_four (by norm_num)]
        refine (hCb lam hlam (le_one_of_le_exp_neg_one hlam1)).trans ?_
        simpa using ofReal_mul_le_ofReal_mul hCbC zero_le_one
    · norm_num at h4

end Radial


/-! ### The case `k = 0` (source l. 1036) -/

section KZero

variable {p : ℕ}

/-- The volume of `Λ^p` is `N^p`. -/
theorem volume_pi_box_fin (N : ℕ) :
    volume (Set.univ.pi fun _ : Fin p => box N) = (N : ℝ≥0∞) ^ p := by
  rw [volume_pi_pi]
  simp [volume_box, Finset.prod_const]

/-- **Case `k = 0` of Proposition 3.7** (source l. 1036): with no marked
point the integrand is `1` (`F_0 = 0`, empty products) and the integral equals `N^p`. -/
theorem lintegral_pi_box_prod_fin_zero (N : ℕ) (f : (Fin p → ℂ) → Fin 0 → ℝ≥0∞) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∏ i : Fin 0, f z i = (N : ℝ≥0∞) ^ p := by
  simp only [Finset.univ_eq_empty, Finset.prod_empty, setLIntegral_const, one_mul]
  exact volume_pi_box_fin N

end KZero


/-! ### Selected subsets: relabelling to the first `k` points -/

section Subset

open AuxIntegration

/-- The first-neighbour radius is equivariant under relabelling. -/
theorem nnRadius_comp_equiv {ι : Type*} [Fintype ι] [Nontrivial ι] (lam : ℝ) (z : ι → ℂ)
    (e : ι ≃ ι) (j : ι) : nnRadius lam (z ∘ e) j = nnRadius lam z (e j) := by
  classical
  unfold nnRadius
  congr 2
  apply le_antisymm
  · refine Finset.le_inf' _ _ fun i hi => ?_
    have hne := (Finset.mem_erase.1 hi).1
    have hi' : e.symm i ∈ Finset.univ.erase j :=
      Finset.mem_erase.2 ⟨fun h => hne (by rw [← h]; simp), Finset.mem_univ _⟩
    exact (Finset.inf'_le _ hi').trans (le_of_eq (by simp))
  · refine Finset.le_inf' _ _ fun j' hj' => ?_
    have hne := (Finset.mem_erase.1 hj').1
    have hj'' : e j' ∈ Finset.univ.erase (e j) :=
      Finset.mem_erase.2 ⟨fun h => hne (e.injective h), Finset.mem_univ _⟩
    exact Finset.inf'_le (fun i => ‖z (e j) - z i‖) hj''

variable {p : ℕ}

/-- The Lebesgue measure on `ℂ^p` and the box `Λ^p` are invariant under permutations of the
coordinates. -/
theorem lintegral_comp_perm (σ : Equiv.Perm (Fin p)) (N : ℕ) (F : (Fin p → ℂ) → ℝ≥0∞) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), F (z ∘ σ) =
      ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), F z := by
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin p => ℂ) σ.symm with hE
  have hEapp : ∀ (w : Fin p → ℂ) (i : Fin p), E w i = w (σ i) := fun w i => by
    rw [hE, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp
  have hmp : MeasurePreserving E volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin p => ℂ) σ.symm
  have hpre : E ⁻¹' (Set.univ.pi fun _ : Fin p => box N) = Set.univ.pi fun _ : Fin p => box N := by
    ext w
    simp only [Set.mem_preimage, Set.mem_univ_pi, hEapp]
    exact (Equiv.forall_congr_left σ.symm (p := fun i => w i ∈ box N)).symm
  have h := hmp.setLIntegral_comp_preimage_emb E.measurableEmbedding F
    (Set.univ.pi fun _ : Fin p => box N)
  rw [hpre] at h
  rw [← h]
  refine lintegral_congr fun w => ?_
  congr 1
  ext i
  exact (hEapp w i).symm

end Subset

section Subset2

variable {p k : ℕ}

/-- The first `k` indices `{i : i < k}` of `Fin p`, as a finset. -/
def prefixSet (hk : k ≤ p) : Finset (Fin p) :=
  (Finset.univ : Finset (Fin k)).map ⟨Fin.castLE hk, Fin.castLE_injective hk⟩

theorem card_prefixSet (hk : k ≤ p) : (prefixSet hk).card = k := by
  simp [prefixSet]

theorem prod_prefixSet {M : Type*} [CommMonoid M] (hk : k ≤ p) (f : Fin p → M) :
    ∏ i ∈ prefixSet hk, f i = ∏ i : Fin k, f (Fin.castLE hk i) := by
  simp [prefixSet]

/-- **Relabelling a selected subset to the first `k` indices.** Any `S ⊆ Fin p` with `|S| = k` is
the image of `{i : i < k}` under a permutation of `Fin p`. -/
theorem exists_perm_image_prefixSet (hk : k ≤ p) (S : Finset (Fin p)) (hS : S.card = k) :
    ∃ σ : Equiv.Perm (Fin p), S = (prefixSet hk).image σ := by
  classical
  have hcard : (prefixSet hk).card = S.card := by rw [card_prefixSet, hS]
  let e : ↥(prefixSet hk) ≃ ↥S := Finset.equivOfCardEq hcard
  refine ⟨e.extendSubtype, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact Equiv.extendSubtype_mem e y hy
  · rw [Finset.card_image_of_injective _ e.extendSubtype.injective, hcard]

end Subset2

section Subset3

variable {p k : ℕ} [Nontrivial (Fin p)]

/-- **Selected subset = first `k` points** (needed for Propositions 3.8 and 3.9): the integral over
`Λ^p` of `∏_{i ∈ S} w(r̃₁(z_i))` depends only on the cardinality `|S| = k` of the selected set, by
the invariance of `Λ^p` and of Lebesgue measure under permutations of the points and the
equivariance of `r̃₁`. -/
theorem lintegral_prod_finset_eq (hk : k ≤ p) (S : Finset (Fin p)) (hS : S.card = k) (lam : ℝ)
    (N : ℕ) (w : ℝ → ℝ≥0∞) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∏ i ∈ S, w (nnRadius lam z i) =
      ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
        ∏ i : Fin k, w (nnRadius lam z (Fin.castLE hk i)) := by
  obtain ⟨σ, hσ⟩ := exists_perm_image_prefixSet hk S hS
  rw [← lintegral_comp_perm σ.symm N (fun z => ∏ i ∈ S, w (nnRadius lam z i))]
  refine lintegral_congr fun z => ?_
  rw [hσ, Finset.prod_image (fun a _ b _ h => σ.injective h), prod_prefixSet hk]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [nnRadius_comp_equiv lam z σ.symm (σ _)]
  simp

end Subset3


/-! ### The source's form of the integrand -/

section Bridge

open AuxIntegration

variable {α : Type*}

/-- **Bridge to the source's form** (eq. (defFaux), l. 1011--1017): for radii `ρ i ≥ λ`,
`∏_{i ∈ s} ρ_i^{-β/2} (1 + log (ρ_i/λ))^δ (1 + |log ρ_i|)^{δ'}` is
`exp (-β · ½ ∑_{i ∈ s} log ρ_i) · ∏ (1 + log (ρ_i/λ))^δ · ∏ (1 + |log ρ_i|)^{δ'}`, i.e.
`exp (-β F) ∏ (1 + log (r̃₁/λ))^δ ∏ (1 + |log r̃₁|)^{δ'}` for `ρ_i = r̃₁(z_i)`. -/
theorem prod_sourceWeight_eq (β : ℝ) (δ δ' : ℕ) {lam : ℝ} (hlam : 0 < lam) (s : Finset α)
    (ρ : α → ℝ) (hρ : ∀ i ∈ s, lam ≤ ρ i) :
    ∏ i ∈ s, sourceWeight β δ δ' lam (ρ i) =
      ENNReal.ofReal (Real.exp (-β * ((1 / 2) * ∑ i ∈ s, Real.log (ρ i))) *
        (∏ i ∈ s, (1 + Real.log (ρ i / lam)) ^ δ) * ∏ i ∈ s, (1 + |Real.log (ρ i)|) ^ δ') := by
  have hpos : ∀ i ∈ s, 0 < ρ i := fun i hi => hlam.trans_le (hρ i hi)
  have hlog : ∀ i ∈ s, 0 ≤ 1 + Real.log (ρ i / lam) :=
    fun i hi => log_div_nonneg_of_le hlam (hρ i hi)
  unfold sourceWeight
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i hi => by
    have := hpos i hi
    have := hlog i hi
    positivity)]
  have h1 : ∏ i ∈ s, ρ i ^ (-(β / 2)) =
      Real.exp (-β * ((1 / 2) * ∑ i ∈ s, Real.log (ρ i))) := by
    rw [Finset.prod_congr rfl fun i hi => Real.rpow_def_of_pos (hpos i hi) _, ← Real.exp_sum,
      ← Finset.sum_mul]
    congr 1
    ring
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, h1]


variable {p k : ℕ} [Nontrivial (Fin p)]

/-- The energy `F_k(z_1, …, z_p) = ½ ∑_{i=1}^k log r̃₁(z_i)` of source eq. (defFaux), l. 1011--1014:
the nearest-neighbour energy counted only for the first `k` of the `p` points. -/
noncomputable def auxEnergy (hk : k ≤ p) (lam : ℝ) (z : Fin p → ℂ) : ℝ :=
  (1 / 2) * ∑ i : Fin k, Real.log (nnRadius lam z (Fin.castLE hk i))

/-- The product of the source weights over the first `k` points is the integrand of
Proposition 3.7: `exp (-β F_k) ∏ (1 + log (r̃₁/λ))^δ ∏ (1 + |log r̃₁|)^{δ'}`. -/
theorem prod_sourceWeight_auxEnergy (β : ℝ) (δ δ' : ℕ) {lam : ℝ} (hlam : 0 < lam) (hk : k ≤ p)
    (z : Fin p → ℂ) :
    ∏ i : Fin k, sourceWeight β δ δ' lam (nnRadius lam z (Fin.castLE hk i)) =
      ENNReal.ofReal (Real.exp (-β * auxEnergy hk lam z) *
        (∏ i : Fin k, (1 + Real.log (nnRadius lam z (Fin.castLE hk i) / lam)) ^ δ) *
          ∏ i : Fin k, (1 + |Real.log (nnRadius lam z (Fin.castLE hk i))|) ^ δ') :=
  prod_sourceWeight_eq β δ δ' hlam Finset.univ (fun i => nnRadius lam z (Fin.castLE hk i))
    fun _ _ => le_nnRadius lam z _

end Bridge


/-! ### Proposition 3.7 for the weights of the source -/

section Main

open AuxIntegration

/-- **Proposition 3.7** (`prop:auxk`, source l. 1008--1031), in the weighted form
`∏_{i<k} sourceWeight β δ δ' λ (r̃₁(z_i))` (see `prod_sourceWeight_eq` for the identification with
`exp (-β F_k) ∏ (1 + log (r̃₁/λ))^δ ∏ (1 + |log r̃₁|)^{δ'}`). For `β ≥ 0`, `δ = 0` unless `β = 4`
(where `δ = 1` is allowed) and `δ' = 0` unless `β = 0` (where `δ' = 1` is allowed) there is
`C_β > 0`, depending on `β` and `δ` only, such that for all integers `0 ≤ k ≤ p ≤ N` with
`N ≤ 2 p` and `p ≥ 2` (encoded by `Nontrivial (Fin p)`), and `0 < λ ≤ e⁻¹`:
`∫_{Λ^p} ∏_{i<k} w(r̃₁(z_i)) dz ≤ exp (p log N + C_β k + (k/2) γ_{β,k})`. -/
theorem lintegral_auxk_le (β : ℝ) (hβ : 0 ≤ β) (δ δ' : ℕ) (hδ : δ = 0 ∨ (β = 4 ∧ δ = 1))
    (hδ' : δ' = 0 ∨ (β = 0 ∧ δ' = 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (hk : k ≤ p), p ≤ N →
      (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i : Fin k, sourceWeight β δ δ' lam (nnRadius lam z (Fin.castLE hk i)) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k +
            k / 2 * gammaBeta β hβ δ lam k N)) := by
  obtain ⟨C₀, hC₀, hrad⟩ := exists_radial_bounds β hβ δ δ' hδ hδ'
  set Cm : ℝ := max C₀ (C₀ ^ 2) with hCm
  set c : ℝ := 4 + Real.log 8 + Real.log Cm / 2 with hc
  refine ⟨max c 1, lt_max_of_lt_right one_pos, fun N p k _ hk hpN hN lam hlam hlam1 => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [lintegral_pi_box_prod_fin_zero N]
    have hp2 : 2 ≤ p := Fin.nontrivial_iff_two_le.1 inferInstance
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    simp only [Nat.cast_zero, mul_zero, zero_div, zero_mul, add_zero]
    rw [Real.exp_nat_mul, Real.exp_log hN0, ENNReal.ofReal_pow hN0.le, ENNReal.ofReal_natCast]
  · obtain ⟨hcyc, hnon⟩ := hrad lam hlam hlam1
    have hkN : k ≤ N := hk.trans hpN
    refine (lintegral_prod_le_of_scales hk hpN hN hk1 lam (measurable_sourceWeight β δ δ' lam)
      (cycleScale_pos β hlam hlam1) (treeScale_pos β δ hlam hlam1) hC₀ hC₀ (le_max_left _ _)
      (le_max_right _ _) hcyc hnon).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    rw [gammaBeta_eq β hβ δ hlam hkN]
    have : c * k ≤ max c 1 * k := mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
    simp only [hc, hCm] at this
    linarith

end Main



section Cases

open AuxIntegration

/-- **Proposition 3.7 for a selected subset** (needed by Propositions 3.8 and 3.9): the bound of
`lintegral_auxk_le` holds for `∏_{i ∈ S}` for every `S ⊆ Fin p` with `|S| = k`. -/
theorem lintegral_auxk_finset_le (β : ℝ) (hβ : 0 ≤ β) (δ δ' : ℕ)
    (hδ : δ = 0 ∨ (β = 4 ∧ δ = 1)) (hδ' : δ' = 0 ∨ (β = 0 ∧ δ' = 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (S : Finset (Fin p)), S.card = k →
      p ≤ N → (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i ∈ S, sourceWeight β δ δ' lam (nnRadius lam z i) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k +
            k / 2 * gammaBeta β hβ δ lam k N)) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_le β hβ δ δ' hδ hδ'
  refine ⟨C, hC, fun N p k _ S hS hpN hN lam hlam hlam1 => ?_⟩
  have hk : k ≤ p := by
    rw [← hS]
    simpa using Finset.card_le_univ S
  rw [lintegral_prod_finset_eq hk S hS lam N]
  exact h N p k hk hpN hN lam hlam hlam1

/-- **Proposition 3.7**, the case `β = 0`, `δ = 0`, `δ' = 1` (weight `1 + |log r̃₁|`), where `γ_{0,k} = 0`.
There is `C > 0`, depending only on the parameters displayed, such that for integers
`k ≤ p ≤ N ≤ 2 p` (`p ≥ 2`) and `0 < λ ≤ e⁻¹`,
`∫_{Λ^p} ∏_{i<k} w(r̃₁(z_i)) dz ≤ exp (p log N + C k + (k/2) γ_{β,k})`, where
`w = sourceWeight 0 0 1 λ`. -/
theorem lintegral_auxk_abs :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (hk : k ≤ p), p ≤ N →
      (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i : Fin k, sourceWeight 0 0 1 lam
              (nnRadius lam z (Fin.castLE hk i)) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k)) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_le 0 le_rfl 0 1 (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩)
  refine ⟨C, hC, fun N p k _ hk hpN hN lam hlam hlam1 => ?_⟩
  have := h N p k hk hpN hN lam hlam hlam1
  rwa [gammaBeta_of_lt_two (by norm_num), mul_zero, add_zero] at this

/-- Subset version of `lintegral_auxk_abs`: the same bound for `∏_{i ∈ S}`, `S ⊆ Fin p`,
`|S| = k`. -/
theorem lintegral_auxk_finset_abs :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (S : Finset (Fin p)), S.card = k →
      p ≤ N → (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i ∈ S, sourceWeight 0 0 1 lam (nnRadius lam z i) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k)) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_abs 
  refine ⟨C, hC, fun N p k _ S hS hpN hN lam hlam hlam1 => ?_⟩
  have hk : k ≤ p := by
    rw [← hS]
    simpa using Finset.card_le_univ S
  rw [lintegral_prod_finset_eq hk S hS lam N]
  exact h N p k hk hpN hN lam hlam hlam1

/-- **Proposition 3.7**, the case `0 ≤ β < 2`, `δ = δ' = 0`, where `γ_{β,k} = 0`.
There is `C > 0`, depending only on the parameters displayed, such that for integers
`k ≤ p ≤ N ≤ 2 p` (`p ≥ 2`) and `0 < λ ≤ e⁻¹`,
`∫_{Λ^p} ∏_{i<k} w(r̃₁(z_i)) dz ≤ exp (p log N + C k + (k/2) γ_{β,k})`, where
`w = sourceWeight β 0 0 λ`. -/
theorem lintegral_auxk_lt_two (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (hk : k ≤ p), p ≤ N →
      (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i : Fin k, sourceWeight β 0 0 lam
              (nnRadius lam z (Fin.castLE hk i)) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k)) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_le β hβ0 0 0 (Or.inl rfl) (Or.inl rfl)
  refine ⟨C, hC, fun N p k _ hk hpN hN lam hlam hlam1 => ?_⟩
  have := h N p k hk hpN hN lam hlam hlam1
  rwa [gammaBeta_of_lt_two hβ, mul_zero, add_zero] at this

/-- Subset version of `lintegral_auxk_lt_two`: the same bound for `∏_{i ∈ S}`, `S ⊆ Fin p`,
`|S| = k`. -/
theorem lintegral_auxk_finset_lt_two (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (S : Finset (Fin p)), S.card = k →
      p ≤ N → (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i ∈ S, sourceWeight β 0 0 lam (nnRadius lam z i) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k)) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_lt_two β hβ0 hβ
  refine ⟨C, hC, fun N p k _ S hS hpN hN lam hlam hlam1 => ?_⟩
  have hk : k ≤ p := by
    rw [← hS]
    simpa using Finset.card_le_univ S
  rw [lintegral_prod_finset_eq hk S hS lam N]
  exact h N p k hk hpN hN lam hlam hlam1

/-- **Proposition 3.7**, the critical case `β = 2`, `δ = δ' = 0`, where `γ_{2,k} = log (|log λ| k/N ∨ 1)`.
There is `C > 0`, depending only on the parameters displayed, such that for integers
`k ≤ p ≤ N ≤ 2 p` (`p ≥ 2`) and `0 < λ ≤ e⁻¹`,
`∫_{Λ^p} ∏_{i<k} w(r̃₁(z_i)) dz ≤ exp (p log N + C k + (k/2) γ_{β,k})`, where
`w = sourceWeight 2 0 0 λ`. -/
theorem lintegral_auxk_two :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (hk : k ≤ p), p ≤ N →
      (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i : Fin k, sourceWeight 2 0 0 lam
              (nnRadius lam z (Fin.castLE hk i)) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k +
            k / 2 * Real.log (max (|Real.log lam| * k / N) 1))) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_le 2 (by norm_num) 0 0 (Or.inl rfl) (Or.inl rfl)
  refine ⟨C, hC, fun N p k _ hk hpN hN lam hlam hlam1 => ?_⟩
  have := h N p k hk hpN hN lam hlam hlam1
  rwa [gammaBeta_two] at this

/-- Subset version of `lintegral_auxk_two`: the same bound for `∏_{i ∈ S}`, `S ⊆ Fin p`,
`|S| = k`. -/
theorem lintegral_auxk_finset_two :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (S : Finset (Fin p)), S.card = k →
      p ≤ N → (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i ∈ S, sourceWeight 2 0 0 lam (nnRadius lam z i) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k +
            k / 2 * Real.log (max (|Real.log lam| * k / N) 1))) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_two 
  refine ⟨C, hC, fun N p k _ S hS hpN hN lam hlam hlam1 => ?_⟩
  have hk : k ≤ p := by
    rw [← hS]
    simpa using Finset.card_le_univ S
  rw [lintegral_prod_finset_eq hk S hS lam N]
  exact h N p k hk hpN hN lam hlam hlam1

/-- **Proposition 3.7**, the case `2 < β < 4`, `δ = δ' = 0`, where `γ_{β,k} = log (λ^{2-β} k/N ∨ 1)`.
There is `C > 0`, depending only on the parameters displayed, such that for integers
`k ≤ p ≤ N ≤ 2 p` (`p ≥ 2`) and `0 < λ ≤ e⁻¹`,
`∫_{Λ^p} ∏_{i<k} w(r̃₁(z_i)) dz ≤ exp (p log N + C k + (k/2) γ_{β,k})`, where
`w = sourceWeight β 0 0 λ`. -/
theorem lintegral_auxk_two_lt_four (β : ℝ) (hβ2 : 2 < β) (hβ4 : β < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (hk : k ≤ p), p ≤ N →
      (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i : Fin k, sourceWeight β 0 0 lam
              (nnRadius lam z (Fin.castLE hk i)) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k +
            k / 2 * Real.log (max (lam ^ (2 - β) * k / N) 1))) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_le β (by linarith) 0 0 (Or.inl rfl) (Or.inl rfl)
  refine ⟨C, hC, fun N p k _ hk hpN hN lam hlam hlam1 => ?_⟩
  have := h N p k hk hpN hN lam hlam hlam1
  rwa [gammaBeta_of_two_lt_of_lt_four hβ2 hβ4] at this

/-- Subset version of `lintegral_auxk_two_lt_four`: the same bound for `∏_{i ∈ S}`, `S ⊆ Fin p`,
`|S| = k`. -/
theorem lintegral_auxk_finset_two_lt_four (β : ℝ) (hβ2 : 2 < β) (hβ4 : β < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (S : Finset (Fin p)), S.card = k →
      p ≤ N → (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i ∈ S, sourceWeight β 0 0 lam (nnRadius lam z i) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k +
            k / 2 * Real.log (max (lam ^ (2 - β) * k / N) 1))) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_two_lt_four β hβ2 hβ4
  refine ⟨C, hC, fun N p k _ S hS hpN hN lam hlam hlam1 => ?_⟩
  have hk : k ≤ p := by
    rw [← hS]
    simpa using Finset.card_le_univ S
  rw [lintegral_prod_finset_eq hk S hS lam N]
  exact h N p k hk hpN hN lam hlam hlam1

/-- **Proposition 3.7**, the case `β = 4`, `δ ∈ {0, 1}`, `δ' = 0`, where `γ_{4,k} = log (λ^{-2} k/N ∨ |log λ|^{2(1+δ)})`.
There is `C > 0`, depending only on the parameters displayed, such that for integers
`k ≤ p ≤ N ≤ 2 p` (`p ≥ 2`) and `0 < λ ≤ e⁻¹`,
`∫_{Λ^p} ∏_{i<k} w(r̃₁(z_i)) dz ≤ exp (p log N + C k + (k/2) γ_{β,k})`, where
`w = sourceWeight 4 δ 0 λ`. -/
theorem lintegral_auxk_four (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (hk : k ≤ p), p ≤ N →
      (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i : Fin k, sourceWeight 4 δ 0 lam
              (nnRadius lam z (Fin.castLE hk i)) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k +
            k / 2 * Real.log (max ((lam ^ 2)⁻¹ * k / N) (|Real.log lam| ^ (2 * (1 + δ)))))) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_le 4 (by norm_num) δ 0 (hδ.imp id fun h => ⟨rfl, h⟩) (Or.inl rfl)
  refine ⟨C, hC, fun N p k _ hk hpN hN lam hlam hlam1 => ?_⟩
  have := h N p k hk hpN hN lam hlam hlam1
  rwa [gammaBeta_four] at this

/-- Subset version of `lintegral_auxk_four`: the same bound for `∏_{i ∈ S}`, `S ⊆ Fin p`,
`|S| = k`. -/
theorem lintegral_auxk_finset_four (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (S : Finset (Fin p)), S.card = k →
      p ≤ N → (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i ∈ S, sourceWeight 4 δ 0 lam (nnRadius lam z i) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k +
            k / 2 * Real.log (max ((lam ^ 2)⁻¹ * k / N) (|Real.log lam| ^ (2 * (1 + δ)))))) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_four δ hδ
  refine ⟨C, hC, fun N p k _ S hS hpN hN lam hlam hlam1 => ?_⟩
  have hk : k ≤ p := by
    rw [← hS]
    simpa using Finset.card_le_univ S
  rw [lintegral_prod_finset_eq hk S hS lam N]
  exact h N p k hk hpN hN lam hlam hlam1

/-- **Proposition 3.7**, the case `β > 4`, `δ = δ' = 0`, where `γ_{β,k} = log (λ^{2-β} k/N ∨ λ^{4-β})`.
There is `C > 0`, depending only on the parameters displayed, such that for integers
`k ≤ p ≤ N ≤ 2 p` (`p ≥ 2`) and `0 < λ ≤ e⁻¹`,
`∫_{Λ^p} ∏_{i<k} w(r̃₁(z_i)) dz ≤ exp (p log N + C k + (k/2) γ_{β,k})`, where
`w = sourceWeight β 0 0 λ`. -/
theorem lintegral_auxk_four_lt (β : ℝ) (hβ : 4 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (hk : k ≤ p), p ≤ N →
      (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i : Fin k, sourceWeight β 0 0 lam
              (nnRadius lam z (Fin.castLE hk i)) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k +
            k / 2 * Real.log (max (lam ^ (2 - β) * k / N) (lam ^ (4 - β))))) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_le β (by linarith) 0 0 (Or.inl rfl) (Or.inl rfl)
  refine ⟨C, hC, fun N p k _ hk hpN hN lam hlam hlam1 => ?_⟩
  have := h N p k hk hpN hN lam hlam hlam1
  rwa [gammaBeta_of_four_lt hβ] at this

/-- Subset version of `lintegral_auxk_four_lt`: the same bound for `∏_{i ∈ S}`, `S ⊆ Fin p`,
`|S| = k`. -/
theorem lintegral_auxk_finset_four_lt (β : ℝ) (hβ : 4 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (S : Finset (Fin p)), S.card = k →
      p ≤ N → (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ∏ i ∈ S, sourceWeight β 0 0 lam (nnRadius lam z i) ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k +
            k / 2 * Real.log (max (lam ^ (2 - β) * k / N) (lam ^ (4 - β))))) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_four_lt β hβ
  refine ⟨C, hC, fun N p k _ S hS hpN hN lam hlam hlam1 => ?_⟩
  have hk : k ≤ p := by
    rw [← hS]
    simpa using Finset.card_le_univ S
  rw [lintegral_prod_finset_eq hk S hS lam N]
  exact h N p k hk hpN hN lam hlam hlam1

end Cases

/-- **Proposition 3.7 in the form of the source** (`prop:auxk`, l. 1008--1031; eq. (defZaux)): for
`β ≥ 0`, `δ = 0` unless `β = 4` (where `δ ∈ {0, 1}`), `δ' = 0` unless `β = 0` (where `δ' = 1`),
there is `C_β > 0` such that for all integers `0 ≤ k ≤ p ≤ N` with `p ≥ max (2, N/2)` and
`0 < λ ≤ e⁻¹`,
`∫_{Λ^p} exp (-β F_k(Z_p)) ∏_{i ≤ k} (1 + log (r̃₁(z_i)/λ))^δ ∏_{i ≤ k} (1 + |log r̃₁(z_i)|)^{δ'} dZ_p
  ≤ exp (p log N + C_β k + (k/2) γ_{β,k})`
(the statement `log ∫ ≤ X` being written as `∫ ≤ exp X`, ruling R10). -/
theorem prop_auxk (β : ℝ) (hβ : 0 ≤ β) (δ δ' : ℕ) (hδ : δ = 0 ∨ (β = 4 ∧ δ = 1))
    (hδ' : δ' = 0 ∨ (β = 0 ∧ δ' = 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N p k : ℕ) [Nontrivial (Fin p)] (hk : k ≤ p), p ≤ N →
      (N : ℝ) ≤ 2 * p → ∀ lam : ℝ, 0 < lam → lam ≤ Real.exp (-1) →
        ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
            ENNReal.ofReal (Real.exp (-β * auxEnergy hk lam z) *
              (∏ i : Fin k, (1 + Real.log (nnRadius lam z (Fin.castLE hk i) / lam)) ^ δ) *
                ∏ i : Fin k, (1 + |Real.log (nnRadius lam z (Fin.castLE hk i))|) ^ δ') ≤
          ENNReal.ofReal (Real.exp (p * Real.log N + C * k +
            k / 2 * gammaBeta β hβ δ lam k N)) := by
  obtain ⟨C, hC, h⟩ := lintegral_auxk_le β hβ δ δ' hδ hδ'
  refine ⟨C, hC, fun N p k _ hk hpN hN lam hlam hlam1 => ?_⟩
  have := h N p k hk hpN hN lam hlam hlam1
  simpa only [prod_sourceWeight_auxEnergy β δ δ' hlam hk] using this




end TwoComponentCoulomb

end
