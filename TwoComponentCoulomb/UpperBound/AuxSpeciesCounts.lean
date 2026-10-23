/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.UpperBound.RestrictedGraph
public import TwoComponentCoulomb.UpperBound.AuxOptimization
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Three cycle counts for the two-species estimate

The paper, `prop:two species`, lines 1108–1152, separates cycles within
each marked group from mixed cycles. We count their endpoints and prove the linear
maximization under the two vertex budgets.
-/

@[expose] public section

open Finset

namespace TwoComponentCoulomb.TwoSpecies

open scoped Classical in
/-- Cycles contained in the first group. The endpoints are listed in increasing order. -/
noncomputable def cyclesFirst {p t : ℕ} (k : ℕ) (g : Fin t → Fin p) :=
  (twoCyclesIn g).filter fun e => (e.2 : ℕ) < k

open scoped Classical in
/-- Cycles contained in the second group. -/
noncomputable def cyclesSecond {p t : ℕ} (k : ℕ) (g : Fin t → Fin p) :=
  (twoCyclesIn g).filter fun e => ¬ (e.1 : ℕ) < k

open scoped Classical in
/-- Cycles with one endpoint in each group. -/
noncomputable def cyclesMixed {p t : ℕ} (k : ℕ) (g : Fin t → Fin p) :=
  (twoCyclesIn g).filter fun e => (e.1 : ℕ) < k ∧ ¬ (e.2 : ℕ) < k

/-- Sum a cost over the three cycle types. -/
theorem sum_cycle_types {p t : ℕ} (k : ℕ) (g : Fin t → Fin p) (a b c : ℝ) :
    (∑ e ∈ twoCyclesIn g, if (e.1 : ℕ) < k then
      (if (e.2 : ℕ) < k then a else c) else b) =
      (cyclesFirst k g).card * a + (cyclesSecond k g).card * b +
        (cyclesMixed k g).card * c := by
  classical
  have hsum (s : Finset (Fin t × Fin t)) (x : ℝ) :
      (s.card : ℝ) * x = ∑ _e ∈ s, x := by simp
  simp only [cyclesFirst, cyclesSecond, cyclesMixed, hsum, sum_filter]
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun e he => ?_
  have hlt := (mem_twoCyclesIn.1 he).1
  by_cases hi : (e.1 : ℕ) < k <;> by_cases hj : (e.2 : ℕ) < k
  · simp [hi, hj]
  · simp [hi, hj]
  · exact False.elim (by omega)
  · simp [hi, hj]

/-- Every cycle belongs to exactly one of the three types. -/
theorem cycle_counts_sum {p t : ℕ} (k : ℕ) (g : Fin t → Fin p) :
    (cyclesFirst k g).card + (cyclesSecond k g).card + (cyclesMixed k g).card =
      (twoCyclesIn g).card := by
  have h := sum_cycle_types k g 1 1 1
  simp only [ite_self, sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h.symm

/-- Cycle endpoints are disjoint, so their weighted sum equals the sum over cycle vertices. -/
theorem sum_cycle_endpoints {p t : ℕ} (g : Fin t → Fin p) (w : Fin t → ℝ) :
    (∑ e ∈ twoCyclesIn g, (w e.1 + w e.2)) = ∑ i ∈ restrictedCycleVerts g, w i := by
  classical
  have hd : Disjoint ((twoCyclesIn g).image Prod.fst) ((twoCyclesIn g).image Prod.snd) := by
    rw [disjoint_left]
    rintro i hi hj
    obtain ⟨e, he, rfl⟩ := mem_image.1 hi
    obtain ⟨e', he', h⟩ := mem_image.1 hj
    exact fst_ne_snd_of_mem_twoCyclesIn he he' h.symm
  rw [restrictedCycleVerts, sum_union hd,
    sum_image (fun a ha b hb h => fst_injOn_twoCyclesIn ha hb h),
    sum_image (fun a ha b hb h => snd_injOn_twoCyclesIn ha hb h), sum_add_distrib]

/-- The two vertex budgets of the manuscript: `2 k₀,₁ + k₀,₃ ≤ k` and
`2 k₀,₂ + k₀,₃ ≤ k'`. -/
theorem cycle_vertex_budgets {p k k' : ℕ} (g : Fin (k + k') → Fin p) :
    2 * (cyclesFirst k g).card + (cyclesMixed k g).card ≤ k ∧
      2 * (cyclesSecond k g).card + (cyclesMixed k g).card ≤ k' := by
  classical
  have one (v₁ v₂ : ℝ) :
      2 * (cyclesFirst k g).card * v₁ + 2 * (cyclesSecond k g).card * v₂ +
        (cyclesMixed k g).card * (v₁ + v₂) =
      ∑ i ∈ restrictedCycleVerts g, (if (i : ℕ) < k then v₁ else v₂) := by
    rw [← sum_cycle_endpoints]
    have h := sum_cycle_types k g (2 * v₁) (2 * v₂) (v₁ + v₂)
    calc _ = ∑ e ∈ twoCyclesIn g, if (e.1 : ℕ) < k then
          (if (e.2 : ℕ) < k then 2 * v₁ else v₁ + v₂) else 2 * v₂ := by
            rw [h]; ring
      _ = _ := by
        refine sum_congr rfl fun e he => ?_
        have hlt := (mem_twoCyclesIn.1 he).1
        by_cases hi : (e.1 : ℕ) < k <;> by_cases hj : (e.2 : ℕ) < k
        · simp [hi, hj]; ring
        · simp [hi, hj]
        · exact False.elim (by omega)
        · simp [hi, hj]; ring
  have h₁ := one 1 0
  have h₂ := one 0 1
  have hle (v₁ v₂ : ℝ) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) :
      (∑ i ∈ restrictedCycleVerts g, if (i : ℕ) < k then v₁ else v₂) ≤
        (k : ℝ) * v₁ + k' * v₂ := by
    calc _ ≤ ∑ i : Fin (k + k'), if (i : ℕ) < k then v₁ else v₂ :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => by split_ifs <;> assumption)
      _ = _ := by simp [Fin.sum_univ_add]
  have h₃ := hle 1 0 zero_le_one le_rfl
  have h₄ := hle 0 1 le_rfl zero_le_one
  simp only [mul_one, mul_zero, add_zero, zero_add] at h₁ h₂ h₃ h₄
  constructor
  · exact_mod_cast (h₁.trans_le h₃)
  · exact_mod_cast (h₂.trans_le h₄)

/-- The explicit linear maximization in the manuscript, lines 1139–1152. -/
theorem three_count_max {a b c k k' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h₁ : 2 * a + c ≤ k) (h₂ : 2 * b + c ≤ k') (A B : ℝ) :
    a * A + b * B + c / 2 * (A + B) ≤ k / 2 * max A 0 + k' / 2 * max B 0 := by
  have hA := le_max_left A 0
  have hB := le_max_left B 0
  have hA0 := le_max_right A 0
  have hB0 := le_max_right B 0
  nlinarith [mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ a + c / 2),
    mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ b + c / 2),
    mul_le_mul_of_nonneg_right h₁ hA0, mul_le_mul_of_nonneg_right h₂ hB0]

/-- The fixed-graph product, with all three cycle types retained, is bounded by
optimizing their linear contribution under the two vertex budgets. This is the
multiplicative form of manuscript lines 1128–1158. -/
theorem cycle_product_le {p k k' : ℕ} (g : Fin (k + k') → Fin p)
    {x a₁ a₂ a₁₂ b₁ b₂ : ℝ} (hx : 0 < x) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (ha₁₂ : 0 < a₁₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hmix : a₁₂ ^ 2 = a₁ * a₂) :
    x ^ (twoCyclesIn g).card *
      ((∏ e ∈ twoCyclesIn g, if (e.1 : ℕ) < k then
        (if (e.2 : ℕ) < k then a₁ else a₁₂) else a₂) *
        ∏ i ∈ (restrictedCycleVerts g)ᶜ, if (i : ℕ) < k then b₁ else b₂) ≤
      Real.exp (k / 2 * Real.log (max (a₁ * x) (b₁ ^ 2)) +
        k' / 2 * Real.log (max (a₂ * x) (b₂ ^ 2))) := by
  classical
  let a : Fin (k + k') × Fin (k + k') → ℝ := fun e =>
    if (e.1 : ℕ) < k then (if (e.2 : ℕ) < k then a₁ else a₁₂) else a₂
  let b : Fin (k + k') → ℝ := fun i => if (i : ℕ) < k then b₁ else b₂
  have ha : ∀ e, 0 < a e := by intro e; dsimp [a]; split_ifs <;> assumption
  have hb : ∀ i, 0 < b i := by intro i; dsimp [b]; split_ifs <;> assumption
  have hmixlog : 2 * Real.log a₁₂ = Real.log a₁ + Real.log a₂ := by
    have h := congrArg Real.log hmix
    rw [Real.log_pow, Real.log_mul ha₁.ne' ha₂.ne'] at h
    norm_num at h
    exact h
  have htree := sum_add_sum_compl (restrictedCycleVerts g) (fun i => Real.log (b i))
  have hend := sum_cycle_endpoints g (fun i => Real.log (b i))
  have hends : (∑ e ∈ twoCyclesIn g, (Real.log (b e.1) + Real.log (b e.2))) =
      (cyclesFirst k g).card * (2 * Real.log b₁) +
        (cyclesSecond k g).card * (2 * Real.log b₂) +
        (cyclesMixed k g).card * (Real.log b₁ + Real.log b₂) := by
    rw [← sum_cycle_types]
    refine sum_congr rfl fun e he => ?_
    have hlt := (mem_twoCyclesIn.1 he).1
    dsimp [b]
    by_cases hi : (e.1 : ℕ) < k <;> by_cases hj : (e.2 : ℕ) < k
    · simp [hi, hj]; ring
    · simp [hi, hj]
    · exact False.elim (by omega)
    · simp [hi, hj]; ring
  have hall : (∑ i, Real.log (b i)) = k * Real.log b₁ + k' * Real.log b₂ := by
    simp [b, Fin.sum_univ_add]
  have hcycles : (∑ e ∈ twoCyclesIn g, Real.log (a e)) =
      (cyclesFirst k g).card * Real.log a₁ + (cyclesSecond k g).card * Real.log a₂ +
        (cyclesMixed k g).card * Real.log a₁₂ := by
    simpa only [a, apply_ite Real.log] using sum_cycle_types k g
      (Real.log a₁) (Real.log a₂) (Real.log a₁₂)
  have hcounts : ((twoCyclesIn g).card : ℝ) =
      (cyclesFirst k g).card + (cyclesSecond k g).card + (cyclesMixed k g).card := by
    exact_mod_cast (cycle_counts_sum k g).symm
  obtain ⟨h₁, h₂⟩ := cycle_vertex_budgets g
  have h₁' : 2 * ((cyclesFirst k g).card : ℝ) + (cyclesMixed k g).card ≤ k := by exact_mod_cast h₁
  have h₂' : 2 * ((cyclesSecond k g).card : ℝ) + (cyclesMixed k g).card ≤ k' := by exact_mod_cast h₂
  let A := Real.log (a₁ * x) - 2 * Real.log b₁
  let B := Real.log (a₂ * x) - 2 * Real.log b₂
  have hmax := three_count_max (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    h₁' h₂' A B
  have hlogmax (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      Real.log (max (a * x) (b ^ 2)) =
        2 * Real.log b + max (Real.log (a * x) - 2 * Real.log b) 0 := by
    rw [log_max_eq (mul_pos ha hx) (pow_pos hb 2), Real.log_pow]
    norm_num
    rcases le_total (Real.log (a * x)) (2 * Real.log b) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  apply (Real.log_le_iff_le_exp (by positivity)).1
  change Real.log (x ^ _ * ((∏ e ∈ twoCyclesIn g, a e) * ∏ i ∈ (restrictedCycleVerts g)ᶜ, b i)) ≤ _
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_prod (fun e _ => (ha e).ne'),
    Real.log_prod (fun i _ => (hb i).ne'), hcycles, hcounts,
    hlogmax a₁ b₁ ha₁ hb₁, hlogmax a₂ b₂ ha₂ hb₂]
  dsimp [A, B] at hmax
  rw [Real.log_mul ha₁.ne' hx.ne', Real.log_mul ha₂.ne' hx.ne'] at hmax ⊢
  rw [← hend, hends, hall] at htree
  nlinarith only [htree, hmax, hmixlog]

end TwoComponentCoulomb.TwoSpecies

end
