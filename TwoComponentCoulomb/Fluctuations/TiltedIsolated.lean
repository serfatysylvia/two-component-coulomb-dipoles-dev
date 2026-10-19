/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Fluctuations.TiltedEnergy
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.UpperBound.Isolated

/-!
# Theorem 2, Steps 3--4: the tilted Proposition 3.9 bounds for the isolated-pair block

Source: proof of Theorem 2 (`prop:linear`), Step 3 (l. 2091--2112) and
Step 4 (l. 2143--2166), for `β > 2`. The isolated-pair block `I` of a marked cell is integrated
as in the proof of Proposition 3.9, with the modified pair factors of `TiltedEnergy.lean`. The
results are stated in exactly the shape of `isolated_n_neutral_conv` (eq:n neutral conv) and
`isolated_n_neutral` (eq:n neutral), with the additional error `C N φ_β(γ)`, so that they enter
the graph sum of Proposition 3.10 (Steps 2--3, (eq:F(1)) and (eq:2cases p)) in place of
Proposition 3.9.

## Main results

* `alphaBlock_n_neutral_conv`: **Step 3** (l. 2092--2112), the analogue of (eq:n neutral conv) for
  `∫_{cell} e^{-β G⁽¹⁾_γ}` (`alphaBlockEnergy`), with the extra error `C_β N φ_β(γ)`.
* `tiltedBlock_n_neutral_conv`: **Step 4** (l. 2143--2166), the analogue for
  `∫_{cell} exp (t ∑_i ((r̃₁(z_i)/γ)² ∧ 1) - β F⁽¹⁾)`, with the extra error `C_{β,t} N φ_β(γ)`.

## The expansion of the added constant (Step 3, l. 2102--2111)

The same-sign factor of `G⁽¹⁾_γ` is `C' ((λ/ρ)^{β-2} + x)`, `x = (λ/γ)^{β-2}`. The product over
the `q` same-sign representatives is expanded over the set `B` of the `s` pairs assigned the added
constant `C' x`; these pairs are then given the neutral factor `1 + C' φ_β(ρ) ≥ 1`, and the
remaining integral is the one of Proposition 3.9 with `(p₀ + s, q - s)` neutral and same-sign pairs
(Steps 3--4 of Proposition 3.9 for the representatives relabelled by `Fin p`,
`IsolatedAssembly.refIntegral_le` in `UpperBound/Isolated.lean`; the relabelling is
`IsolatedIntegration.exists_relabel_ref`). The source compares entropies through
`C(m, q) C(q, s) = C(m, q - s) C(m - q + s, s) ≤ C(m, q - s) C(m, s)`. We use the equivalent exact
identity for the entropy `H(a, b) = (a + b) log (a + b) - a log a - b log b`,
`H(p₀, q) + H(s, q - s) = H(p₀ + s, q - s) + H(p₀, s)`, in the form
`log C(q, s) + H(p₀, q) - H(p₀ + s, q - s) ≤ 2s + s log p - s log s` (`exponent_expand_le`); the
quadratic gain is kept with `c_β = 1/2` (`(q/p)² ≤ 2((q - s)/p)² + 2 (s/p)²`), and the sum over
`s` is bounded by the supremum inequality `s (A - log s) ≤ e^{A - 1}`, which gives
`C' e^{2 + |C₀|} p x ≤ C_β N φ_β(γ)`. This is the source's bound
`(1 + C_β e^{C₀} (λ/γ)^{β-2})^m ≤ exp (C_β N φ_β(γ))`.

## The tilt (Step 4, l. 2143--2158)

By `lintegral_tiltedCell_le`, each pair factor of `(pred3)` gains at most `1 + C_t φ_β(γ)`, and
the same-sign tilt `e^{2t}` is absorbed into the constant `C'` of the same-sign factor (the source
absorbs it into `C₀`; the two are equivalent since the entropy and `C'^q` enter the same way).
Hence the extra factor `(1 + C_t φ_β(γ))^p ≤ exp (C_t N φ_β(γ))`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

universe u

namespace TwoComponentCoulomb

namespace TiltedAssembly

open AuxIntegration IsolatedIntegration IsolatedOptimization IsolatedAssembly

/-! ### Measurability of the profiles -/

theorem measurable_isolatedPhi {β : ℝ} (hβ : 2 ≤ β) (lam : ℝ) :
    Measurable (isolatedPhi β hβ lam) := by
  unfold isolatedPhi
  split_ifs <;> fun_prop

theorem measurable_isolatedTail {β : ℝ} (hβ : 2 ≤ β) (lam : ℝ) :
    Measurable (isolatedTail β hβ lam) := by
  unfold isolatedTail
  split_ifs <;> fun_prop

/-! ### The expansion of the added constant (Step 3, l. 2102--2108) -/

/-- Splitting a product over `Fin p` according to a set `U`. -/
theorem prod_ite_eq {p : ℕ} (U : Finset (Fin p)) (F G : Fin p → ℝ≥0∞) :
    ∏ i, (if i ∈ U then F i else G i) = (∏ i ∈ U, F i) * ∏ i ∈ Uᶜ, G i := by
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext i; simp
  · congr 1; ext i; simp

/-- **The expansion over the same-sign pairs** (source l. 2102--2108): expanding the product of
the same-sign factors `b_i + c` over the set `B ⊆ T` of the pairs assigned the added constant `c`,
and giving these pairs the neutral factor `1 + a_i ≥ 1`,
`∏_{i ∈ T} (b_i + c) ∏_{i ∉ T} (1 + a_i)
  ≤ ∑_{B ⊆ T} c^{|B|} ∏_{i ∈ T ∖ B} b_i ∏_{i ∉ T ∖ B} (1 + a_i)`. -/
theorem prod_ite_add_le {p : ℕ} (T : Finset (Fin p)) (a b : Fin p → ℝ≥0∞) (c : ℝ≥0∞) :
    ∏ i, (if i ∈ T then b i + c else 1 + a i) ≤
      ∑ B ∈ T.powerset, c ^ B.card * ∏ i, (if i ∈ T \ B then b i else 1 + a i) := by
  rw [prod_ite_eq T (fun i => b i + c) (fun i => 1 + a i)]
  have hT : ∏ i ∈ T, (b i + c) = ∑ B ∈ T.powerset, c ^ B.card * ∏ i ∈ T \ B, b i := by
    rw [Finset.prod_congr rfl fun i _ => add_comm (b i) c, Finset.prod_add (fun _ => c) b T]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [Finset.prod_const]
  rw [hT, Finset.sum_mul]
  refine Finset.sum_le_sum fun B _ => ?_
  rw [prod_ite_eq (T \ B) b (fun i => 1 + a i), mul_assoc (c ^ B.card)]
  refine mul_le_mul_right (mul_le_mul_right ?_ _) _
  exact Finset.prod_le_prod_of_subset_of_one_le
    (Finset.compl_subset_compl.2 Finset.sdiff_subset) fun i _ _ => le_self_add

/-- **The expansion, integrated over the representatives** (source l. 2102--2108). -/
theorem lintegral_prod_ite_add_le {p : ℕ} [Nontrivial (Fin p)] (N : ℕ) (lam : ℝ)
    (T : Finset (Fin p)) {a b : ℝ → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) (c : ℝ≥0∞) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
        ∏ i, (if i ∈ T then b (nnRadius lam z i) + c else 1 + a (nnRadius lam z i)) ≤
      ∑ B ∈ T.powerset, c ^ B.card * ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
        ∏ i, (if i ∈ T \ B then b (nnRadius lam z i) else 1 + a (nnRadius lam z i)) := by
  have hm : ∀ U : Finset (Fin p), Measurable fun z : Fin p → ℂ =>
      ∏ i, (if i ∈ U then b (nnRadius lam z i) else 1 + a (nnRadius lam z i)) := by
    intro U
    refine Finset.measurable_prod _ fun i _ => ?_
    by_cases h : i ∈ U
    · simp only [h, ↓reduceIte]
      exact hb.comp (measurable_nnRadius lam i)
    · simp only [h, ↓reduceIte]
      exact measurable_const.add (ha.comp (measurable_nnRadius lam i))
  calc _ ≤ ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∑ B ∈ T.powerset, c ^ B.card *
          ∏ i, (if i ∈ T \ B then b (nnRadius lam z i) else 1 + a (nnRadius lam z i)) :=
        lintegral_mono fun z => prod_ite_add_le T (fun i => a (nnRadius lam z i))
          (fun i => b (nnRadius lam z i)) c
    _ = _ := by
        rw [lintegral_finsetSum _ fun B _ => (hm (T \ B)).const_mul _]
        exact Finset.sum_congr rfl fun B _ => lintegral_const_mul _ (hm (T \ B))

/-! ### The entropy comparison of the expansion (Step 3, l. 2102--2111) -/

/-- **The entropy comparison of the expansion** (source l. 2102--2111, in entropy form): for
`p = p₀ + q > 0`, `s ≤ q` and `y > 0`,
`log C(q, s) + [p log p - p₀ log p₀ - q log q + C₀ q + s log y]
  - [p log p - (p₀ + s) log (p₀ + s) - (q - s) log (q - s) + C₀ (q - s)] - p ((q - s)/p)²
  ≤ -½ p (q/p)² + p y e^{2 + |C₀|}`.
This is the source's `C(m, q) C(q, s) = C(m, q - s) C(m - q + s, s) ≤ C(m, q - s) C(m, s)`
followed by `∑_s C(m, s) (C e^{C₀} x)^s = (1 + C e^{C₀} x)^m`, through the entropy identity
`H(p₀, q) + H(s, q - s) = H(p₀ + s, q - s) + H(p₀, s)` and the supremum inequality
`s (A - log s) ≤ e^{A - 1}`; the quadratic gain uses `(q/p)² ≤ 2 ((q - s)/p)² + 2 (s/p)²`. -/
theorem exponent_expand_le {p p₀ q s : ℕ} (hpq : p₀ + q = p) (hp : 0 < p) (hs : s ≤ q)
    (C₀ : ℝ) {y : ℝ} (hy : 0 < y) :
    Real.log (q.choose s)
      + (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q + C₀ * q + s * Real.log y
        - (p * Real.log p - ((p₀ + s : ℕ) : ℝ) * Real.log ((p₀ + s : ℕ) : ℝ)
          - ((q - s : ℕ) : ℝ) * Real.log ((q - s : ℕ) : ℝ) + C₀ * ((q - s : ℕ) : ℝ)))
      - p * (((q - s : ℕ) : ℝ) / p) ^ 2 ≤
    -(1 / 2) * (p * ((q : ℝ) / p) ^ 2) + p * y * Real.exp (2 + |C₀|) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have hey : 0 ≤ p * y * Real.exp (2 + |C₀|) := by positivity
  have hq2 : 0 ≤ (p : ℝ) * ((q : ℝ) / p) ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos s with rfl | hspos
  · simp only [Nat.choose_zero_right, Nat.cast_one, Real.log_one, Nat.cast_zero, add_zero,
      Nat.sub_zero, zero_mul]
    linarith
  have hqs : ((q - s : ℕ) : ℝ) = q - s := Nat.cast_sub hs
  have hps : ((p₀ + s : ℕ) : ℝ) = p₀ + s := by push_cast; ring
  rw [hqs, hps]
  have hpq' : (p : ℝ) = p₀ + q := by exact_mod_cast hpq.symm
  have hsq : (s : ℝ) ≤ q := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hspos
  have hp00 : (0 : ℝ) ≤ p₀ := Nat.cast_nonneg p₀
  have hsp : (s : ℝ) ≤ p := by linarith
  -- the quadratic term
  have hquad : -(p * (((q : ℝ) - s) / p) ^ 2) ≤ -(1 / 2) * (p * ((q : ℝ) / p) ^ 2) + s := by
    have e1 : (p : ℝ) * (((q : ℝ) - s) / p) ^ 2 = ((q : ℝ) - s) ^ 2 * (p : ℝ)⁻¹ := by
      field_simp
    have e2 : (p : ℝ) * ((q : ℝ) / p) ^ 2 = (q : ℝ) ^ 2 * (p : ℝ)⁻¹ := by field_simp
    rw [e1, e2]
    have key : (q : ℝ) ^ 2 ≤ 2 * ((q : ℝ) - s) ^ 2 + 2 * p * s := by
      linarith only [sq_nonneg ((q : ℝ) - 2 * s), mul_nonneg hs0.le (sub_nonneg.2 hsp)]
    have hinv : 0 < (p : ℝ)⁻¹ := inv_pos.2 hP
    have h1 := mul_le_mul_of_nonneg_right key hinv.le
    have e3 : (2 * ((q : ℝ) - s) ^ 2 + 2 * p * s) * (p : ℝ)⁻¹ =
        2 * (((q : ℝ) - s) ^ 2 * (p : ℝ)⁻¹) + 2 * s := by
      field_simp
    linarith
  -- the binomial coefficient and the entropy `H(p₀, s)`
  have hchoose := log_choose_le hs
  have hent := entropy_le (p := p₀ + s) (p₀ := p₀) (q := s) rfl (by omega) (Nat.zero_le p₀)
    (k := 0)
  simp only [Nat.choose_zero_right, Nat.cast_one, Real.log_one, add_zero, Nat.cast_zero,
    zero_mul, sub_zero] at hent
  push_cast at hent
  have hlog1 : Real.log ((p₀ : ℝ) + s) ≤ Real.log p :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog1' := mul_le_mul_of_nonneg_left hlog1 hs0.le
  have hcq : ((q : ℝ) - s) * Real.log ((q : ℝ) - s) ≤ ((q : ℝ) - s) * Real.log q := by
    rcases (sub_nonneg.2 hsq).eq_or_lt with h | h
    · rw [← h]
      simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log h (by linarith)) h.le
  -- the supremum inequality
  have hopt := mul_sub_log_le_exp (3 + |C₀| + Real.log p + Real.log y) hs0.le
  have hexp : Real.exp (3 + |C₀| + Real.log p + Real.log y - 1) =
      p * y * Real.exp (2 + |C₀|) := by
    rw [show 3 + |C₀| + Real.log p + Real.log y - 1 = (2 + |C₀|) + Real.log p + Real.log y by
      ring, Real.exp_add, Real.exp_add, Real.exp_log hP, Real.exp_log hy]
    ring
  rw [hexp] at hopt
  have hC₀ : C₀ * s ≤ |C₀| * s := mul_le_mul_of_nonneg_right (le_abs_self C₀) hs0.le
  linarith

/-- **The sum over `0 ≤ s ≤ n` costs at most `log (N + 1)`**: if every term is at most `e^Y`, the
sum is at most `e^{Y + log (N + 1)}` for `n ≤ N`. -/
theorem sum_range_le_ofReal_exp {n N : ℕ} (hn : n ≤ N) (Y : ℝ) (F : ℕ → ℝ≥0∞)
    (hF : ∀ k ∈ range (n + 1), F k ≤ ENNReal.ofReal (Real.exp Y)) :
    ∑ k ∈ range (n + 1), F k ≤ ENNReal.ofReal (Real.exp (Y + Real.log (N + 1))) := by
  refine (sum_le_card_nsmul _ _ _ hF).trans ?_
  rw [card_range, nsmul_eq_mul, Real.exp_add, Real.exp_log (by positivity),
    ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm (ENNReal.ofReal (Real.exp Y))]
  refine mul_le_mul_left ?_ _
  rw [show ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n + 1 : ℕ) : ℝ) from
    (ENNReal.ofReal_natCast _).symm]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  exact_mod_cast Nat.add_le_add_right hn 1

/-- One term of the expansion: if `e^{H_s} W ≤ e^M`, then `e^{E} y^s W ≤ e^{E + s log y - H_s + M}`
for `y > 0`. -/
theorem ofReal_exp_mul_pow_mul_le {E Hs M y : ℝ} (s : ℕ) (hy : 0 < y) {W : ℝ≥0∞}
    (hW : ENNReal.ofReal (Real.exp Hs) * W ≤ ENNReal.ofReal (Real.exp M)) :
    ENNReal.ofReal (Real.exp E) * (ENNReal.ofReal y ^ s * W) ≤
      ENNReal.ofReal (Real.exp (E + s * Real.log y - Hs + M)) := by
  have e : ENNReal.ofReal (Real.exp E) * ENNReal.ofReal y ^ s =
      ENNReal.ofReal (Real.exp (E + s * Real.log y - Hs)) * ENNReal.ofReal (Real.exp Hs) := by
    rw [← ENNReal.ofReal_pow hy.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    rw [show E + s * Real.log y - Hs + Hs = E + s * Real.log y by ring, Real.exp_add,
      Real.exp_nat_mul, Real.exp_log hy]
  calc ENNReal.ofReal (Real.exp E) * (ENNReal.ofReal y ^ s * W)
      = ENNReal.ofReal (Real.exp (E + s * Real.log y - Hs)) *
          (ENNReal.ofReal (Real.exp Hs) * W) := by
        rw [← mul_assoc, e, mul_assoc]
    _ ≤ ENNReal.ofReal (Real.exp (E + s * Real.log y - Hs)) * ENNReal.ofReal (Real.exp M) :=
        mul_le_mul_right hW _
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]

/-! ### Step 3: the `A₁`-block (internal form) -/

open scoped Classical in
/-- **Theorem 2, Step 3, the isolated-pair block** (source l. 2092--2112), internal form with
explicit constants: for `β > 2`, `C, C₀ ∈ ℝ` there are `K, C₁ > 0` such that for every block with
`p = p₀ + q` pairs (`2 ≤ p ≤ N ≤ 2p`), `|S| = 2q`, `0 < λ ≤ e^{-1}` and `γ ≥ λ`,
`e^{p log p - p₀ log p₀ - q log q + C₀ q} ∫_{cell} e^{-β G⁽¹⁾_γ}
  ≤ exp (p log N + p log (𝒵_β λ^{2-β}) - ½ p (q/p)² + K p r(λ) + C₁ p (λ/γ)^{β-2}
    + 2 log (N + 1))`. (Internal.) -/
theorem alphaBlock_le {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) (C C₀ : ℝ) :
    ∃ K C₁ : ℝ, 0 < K ∧ 0 < C₁ ∧ ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ)
      (f : ι → ι), (∀ i, f (f i) = i) → (∀ i, f i ≠ i) → ∀ (h3 : 3 ≤ Fintype.card ι)
      (S : Finset ι), (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N p p₀ q : ℕ), Fintype.card ι = 2 * p →
      2 ≤ p → p ≤ N → (N : ℝ) ≤ 2 * p → p₀ + q = p → S.card = 2 * q →
      ∀ lam γ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → lam ≤ γ →
        ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
            + C₀ * q)) *
          ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
            ENNReal.ofReal (Real.exp (-(β * alphaBlockEnergy h3 key lam γ C S z))) ≤
        ENNReal.ofReal (Real.exp (p * Real.log N
          + p * Real.log (dipoleConstant β hβ * isolatedScale β hβ lam)
          - (1 / 2) * (p * ((q : ℝ) / p) ^ 2)
          + K * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
              else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|)
          + C₁ * p * (lam / γ) ^ (β - 2) + 2 * Real.log (N + 1))) := by
  obtain ⟨C', hC', hpred⟩ := lintegral_alphaBlockCell_le.{u} hβ h2 C
  obtain ⟨K, hK, hJ⟩ := refIntegral_le hβ hC' C₀
  refine ⟨K, C' * Real.exp (2 + |C₀|), hK, by positivity, ?_⟩
  intro ι _ _ key f hf2 hf0 h3 S hS N p p₀ q hcard hp2 hpN hN hpq hSq lam γ hlam hl1 hγ
  have hRf := gpRefSet_mem_iff (key := key) hf2 hf0
  have hR : Fintype.card {i // i ∈ gpRefSet key f} = p := by
    have := IsolatedReduction.two_mul_card_ref hf2 hRf
    omega
  have : Nontrivial {i // i ∈ gpRefSet key f} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have : Nontrivial (Fin p) := Fin.nontrivial_iff_two_le.2 hp2
  have hp : 0 < p := by omega
  have hγ0 : 0 < γ := hlam.trans_le hγ
  have hx : 0 < (lam / γ) ^ (β - 2) := Real.rpow_pos_of_pos (div_pos hlam hγ0) _
  have hy : 0 < C' * (lam / γ) ^ (β - 2) := mul_pos hC' hx
  have hI := hpred ι key f (gpRefSet key f) hf2 hRf h3 S hS N lam γ hlam hl1 hγ
  rw [hR] at hI
  obtain ⟨T, hT, hrel⟩ := exists_relabel_ref hf2 hRf hS hR hSq N lam
  have hqN : q ≤ N := by omega
  -- Step 2 (pred3), relabelled, and the expansion over the same-sign pairs
  have hexp : ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
        ENNReal.ofReal (Real.exp (-(β * alphaBlockEnergy h3 key lam γ C S z))) ≤
      ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^ p *
        ∑ B ∈ T.powerset, ENNReal.ofReal (C' * (lam / γ) ^ (β - 2)) ^ B.card *
          ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∏ i, (if i ∈ T \ B then
            ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam z i))
            else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam z i))) := by
    refine hI.trans (mul_le_mul_right ?_ _)
    refine (le_of_eq (hrel (fun ρ => ENNReal.ofReal (C' * isolatedTail β hβ lam ρ
      + C' * (lam / γ) ^ (β - 2))) (fun ρ => 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ)))
      ).trans ?_
    refine (lintegral_mono fun z => le_of_eq (Finset.prod_congr rfl fun i _ => ?_)).trans
      (lintegral_prod_ite_add_le N lam T
        (a := fun ρ => ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ))
        (b := fun ρ => ENNReal.ofReal (C' * isolatedTail β hβ lam ρ))
        (ENNReal.measurable_ofReal.comp ((measurable_isolatedPhi hβ lam).const_mul C'))
        (ENNReal.measurable_ofReal.comp ((measurable_isolatedTail hβ lam).const_mul C'))
        (ENNReal.ofReal (C' * (lam / γ) ^ (β - 2))))
    split_ifs
    · exact ENNReal.ofReal_add (mul_nonneg hC'.le (isolatedTail_nonneg hβ hlam
        (hlam.trans_le (le_nnRadius lam z i)))) hy.le
    · rfl
  -- the terms of the expansion
  set Zs : ℝ := dipoleConstant β hβ * isolatedScale β hβ lam with hZsdef
  set H0 : ℝ := p * Real.log p - p₀ * Real.log p₀ - q * Real.log q + C₀ * q with hH0
  set r : ℝ := if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
    else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam| with hr
  set F : ℕ → ℝ := fun s => H0 + s * Real.log (C' * (lam / γ) ^ (β - 2))
    - (p * Real.log p - ((p₀ + s : ℕ) : ℝ) * Real.log ((p₀ + s : ℕ) : ℝ)
      - ((q - s : ℕ) : ℝ) * Real.log ((q - s : ℕ) : ℝ) + C₀ * ((q - s : ℕ) : ℝ))
    + (p * Real.log N + p * Real.log Zs - p * (((q - s : ℕ) : ℝ) / p) ^ 2 + K * p * r
      + Real.log (N + 1)) with hFdef
  have hterm : ∀ B ∈ T.powerset,
      ENNReal.ofReal (Real.exp H0) * (ENNReal.ofReal (C' * (lam / γ) ^ (β - 2)) ^ B.card *
        (ENNReal.ofReal Zs ^ p * ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
          ∏ i, (if i ∈ T \ B then
            ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam z i))
            else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam z i))))) ≤
        ENNReal.ofReal (Real.exp (F B.card)) := by
    intro B hB
    have hBT : B ⊆ T := Finset.mem_powerset.1 hB
    have hBq : B.card ≤ q := hT ▸ Finset.card_le_card hBT
    have hcard' : (T \ B).card = q - B.card := by
      rw [Finset.card_sdiff_of_subset hBT, hT]
    have h := hJ N p (p₀ + B.card) (q - B.card) (T \ B) hp2 hpN hN (by omega) hcard' lam hlam hl1
    exact ofReal_exp_mul_pow_mul_le B.card hy h
  have hF : ∀ s ∈ range (q + 1), q.choose s • ENNReal.ofReal (Real.exp (F s)) ≤
      ENNReal.ofReal (Real.exp (p * Real.log N + p * Real.log Zs
        - (1 / 2) * (p * ((q : ℝ) / p) ^ 2) + K * p * r
        + C' * Real.exp (2 + |C₀|) * p * (lam / γ) ^ (β - 2) + Real.log (N + 1))) := by
    intro s hs
    have hsq : s ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    have hc : (0 : ℝ) < q.choose s := by exact_mod_cast Nat.choose_pos hsq
    rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hc.le,
      ← Real.exp_log hc, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have key := exponent_expand_le hpq hp hsq C₀ hy
    simp only [hFdef, hH0]
    have e : (p : ℝ) * (C' * (lam / γ) ^ (β - 2)) * Real.exp (2 + |C₀|) =
        C' * Real.exp (2 + |C₀|) * p * (lam / γ) ^ (β - 2) := by ring
    linarith
  calc ENNReal.ofReal (Real.exp H0) *
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
          ENNReal.ofReal (Real.exp (-(β * alphaBlockEnergy h3 key lam γ C S z)))
      ≤ ENNReal.ofReal (Real.exp H0) * (ENNReal.ofReal Zs ^ p *
          ∑ B ∈ T.powerset, ENNReal.ofReal (C' * (lam / γ) ^ (β - 2)) ^ B.card *
            ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∏ i, (if i ∈ T \ B then
              ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam z i))
              else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam z i)))) :=
        mul_le_mul_right hexp _
    _ = ∑ B ∈ T.powerset, ENNReal.ofReal (Real.exp H0) *
          (ENNReal.ofReal (C' * (lam / γ) ^ (β - 2)) ^ B.card *
            (ENNReal.ofReal Zs ^ p * ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N),
              ∏ i, (if i ∈ T \ B then
                ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam z i))
                else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam z i))))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [mul_left_comm (ENNReal.ofReal Zs ^ p)]
    _ ≤ ∑ B ∈ T.powerset, ENNReal.ofReal (Real.exp (F B.card)) := Finset.sum_le_sum hterm
    _ = ∑ s ∈ range (q + 1), q.choose s • ENNReal.ofReal (Real.exp (F s)) := by
        rw [Finset.sum_powerset_apply_card (fun s => ENNReal.ofReal (Real.exp (F s))), hT]
    _ ≤ _ := by
        refine (sum_range_le_ofReal_exp hqN _ _ hF).trans (le_of_eq ?_)
        congr 2
        ring

/-! ### Step 4: the `A₃`-tilted block (internal form) -/

open scoped Classical in
/-- **Theorem 2, Step 4, the isolated-pair block** (source l. 2143--2166), internal form with
explicit constants: for `β > 2`, `C ≥ 0`, `C₀ ∈ ℝ` and `t ≥ 0` there are `K > 0`, `C_t ≥ 0` such
that for every block with `p = p₀ + q` pairs (`2 ≤ p ≤ N ≤ 2p`), `|S| = 2q`, `0 < λ ≤ e^{-1}` and
`γ ≥ λ`,
`e^{p log p - p₀ log p₀ - q log q + C₀ q} ∫_{cell} exp (t ∑_i ((r̃₁(z_i)/γ)² ∧ 1) - β F⁽¹⁾)
  ≤ exp (p log N + p log (𝒵_β λ^{2-β}) - p (q/p)² + K p r(λ) + C_t p φ_β(γ) + log (N + 1))`.
(Internal.) -/
theorem tiltedBlock_le {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) {C : ℝ} (hC : 0 ≤ C) (C₀ : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ K Ct : ℝ, 0 < K ∧ 0 ≤ Ct ∧ ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ)
      (f : ι → ι), (∀ i, f (f i) = i) → (∀ i, f i ≠ i) → ∀ (h3 : 3 ≤ Fintype.card ι)
      (S : Finset ι), (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N p p₀ q : ℕ), Fintype.card ι = 2 * p →
      2 ≤ p → p ≤ N → (N : ℝ) ≤ 2 * p → p₀ + q = p → S.card = 2 * q →
      ∀ lam γ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → lam ≤ γ →
        ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
            + C₀ * q)) *
          ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
            ENNReal.ofReal (Real.exp (t * ∑ i, min ((nnRadius lam z i / γ) ^ 2) 1
              - β * pairAssignedEnergy h3 key lam C S z)) ≤
        ENNReal.ofReal (Real.exp (p * Real.log N
          + p * Real.log (dipoleConstant β hβ * isolatedScale β hβ lam)
          - p * ((q : ℝ) / p) ^ 2
          + K * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
              else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|)
          + Ct * p * isolatedPhi β hβ lam γ + Real.log (N + 1))) := by
  obtain ⟨C', Ct, hC', hCt, hpred⟩ := lintegral_tiltedCell_le.{u} hβ h2 hC ht
  obtain ⟨K, hK, hJ⟩ := refIntegral_le hβ hC' C₀
  refine ⟨K, Ct, hK, hCt, ?_⟩
  intro ι _ _ key f hf2 hf0 h3 S hS N p p₀ q hcard hp2 hpN hN hpq hSq lam γ hlam hl1 hγ
  have hRf := gpRefSet_mem_iff (key := key) hf2 hf0
  have hR : Fintype.card {i // i ∈ gpRefSet key f} = p := by
    have := IsolatedReduction.two_mul_card_ref hf2 hRf
    omega
  have : Nontrivial {i // i ∈ gpRefSet key f} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have : Nontrivial (Fin p) := Fin.nontrivial_iff_two_le.2 hp2
  have hZs : 0 < dipoleConstant β hβ * isolatedScale β hβ lam :=
    mul_pos (dipoleConstant_pos β hβ) (isolatedScale_pos hβ hlam hl1)
  have hφγ := isolatedPhi_nonneg hβ hlam hγ
  have hu : 0 ≤ 1 + Ct * isolatedPhi β hβ lam γ := by
    have := mul_nonneg hCt hφγ
    linarith
  have hI := hpred ι key f (gpRefSet key f) hf2 hRf h3 S hS N lam γ hlam hl1 hγ
  rw [hR] at hI
  obtain ⟨T, hT, hrel⟩ := exists_relabel_ref hf2 hRf hS hR hSq N lam
  rw [hrel (fun ρ => ENNReal.ofReal (C' * isolatedTail β hβ lam ρ))
    (fun ρ => 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam ρ)),
    ENNReal.ofReal_mul hZs.le, mul_pow] at hI
  have hJ' := hJ N p p₀ q T hp2 hpN hN hpq hT lam hlam hl1
  calc ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
          + C₀ * q)) *
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
          ENNReal.ofReal (Real.exp (t * ∑ i, min ((nnRadius lam z i / γ) ^ 2) 1
            - β * pairAssignedEnergy h3 key lam C S z))
      ≤ ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
          + C₀ * q)) *
        (ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^ p *
          ENNReal.ofReal (1 + Ct * isolatedPhi β hβ lam γ) ^ p *
          ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∏ i, (if i ∈ T then
            ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam z i))
            else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam z i)))) :=
        mul_le_mul_right hI _
    _ = ENNReal.ofReal (1 + Ct * isolatedPhi β hβ lam γ) ^ p *
        (ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀ - q * Real.log q
          + C₀ * q)) *
        (ENNReal.ofReal (dipoleConstant β hβ * isolatedScale β hβ lam) ^ p *
          ∫⁻ z in Set.univ.pi (fun _ : Fin p => box N), ∏ i, (if i ∈ T then
            ENNReal.ofReal (C' * isolatedTail β hβ lam (nnRadius lam z i))
            else 1 + ENNReal.ofReal (C' * isolatedPhi β hβ lam (nnRadius lam z i))))) := by
        ring
    _ ≤ ENNReal.ofReal (Real.exp (Ct * isolatedPhi β hβ lam γ)) ^ p *
        ENNReal.ofReal (Real.exp (p * Real.log N
          + p * Real.log (dipoleConstant β hβ * isolatedScale β hβ lam)
          - p * ((q : ℝ) / p) ^ 2
          + K * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
              else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|)
          + Real.log (N + 1))) := by
        gcongr
        rw [add_comm]
        exact Real.add_one_le_exp _
    _ = _ := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring

end TiltedAssembly

open TiltedAssembly IsolatedAssembly

/-! ### Step 3: the analogues of (eq:n neutral conv) and (eq:n neutral) for `G⁽¹⁾_γ` -/

/-- **Theorem 2, Step 3: the tilted (eq:n neutral conv) for the `A₁`-block** (source
l. 2092--2112). For `β > 2` and `C, C₀ ∈ ℝ` there are `C_β, c_β > 0` (depending only on `β`, `C`,
`C₀`) such that for every finite index type `ι` with `|ι| = 2p`, tie-break key, graph
`γ ∈ G_{p,p₀}` (a fixed-point-free involution `f`) with same-sign set `S` (`f`-invariant,
`|S| = 2(p - p₀)`), every `2 ≤ p ≤ N` with `p ≥ N/2`, `p₀ ≤ p`, `0 < λ ≤ e^{-1}` and `γ ≥ λ`:
`p log p - p₀ log p₀ - (p-p₀) log (p-p₀) + C₀ (p-p₀) + log ∫_{cell} e^{-β G⁽¹⁾_γ}
  - p (log N + (2-β) log λ + log 𝒵_β)
  ≤ -c_β p ((p - p₀)/p)² + C_β p r(λ) + C_β N φ_β(γ) + C_β log (N + 1)`,
where `G⁽¹⁾_γ = alphaBlockEnergy` and `r(λ)` is the error rate of (eq:n neutral conv); stated
for each graph as `e^{entropy} I(γ) ≤ e^{…}` (ruling R10). The source assumes `2λ ≤ γ ≤ 1`; only
`λ ≤ γ` is used. -/
theorem alphaBlock_n_neutral_conv {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) (C C₀ : ℝ) :
    ∃ Cβ cβ : ℝ, 0 < Cβ ∧ 0 < cβ ∧
      ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (f : ι → ι),
        (∀ i, f (f i) = i) → (∀ i, f i ≠ i) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
        (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N p p₀ : ℕ), Fintype.card ι = 2 * p → 2 ≤ p → p ≤ N →
        (N : ℝ) ≤ 2 * p → p₀ ≤ p → S.card = 2 * (p - p₀) →
        ∀ lam γ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → lam ≤ γ →
          ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
              - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀))) *
            ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
              ENNReal.ofReal (Real.exp (-(β * alphaBlockEnergy h3 key lam γ C S z))) ≤
          ENNReal.ofReal (Real.exp (p * (Real.log N
                + (if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0)
                + Real.log (dipoleConstant β hβ))
              - cβ * p * (((p : ℝ) - p₀) / p) ^ 2
              + Cβ * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
                  else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|)
              + Cβ * N * isolatedPhi β hβ lam γ
              + Cβ * Real.log (N + 1))) := by
  obtain ⟨K, C₁, hK, hC₁, h⟩ := alphaBlock_le.{u} hβ h2 C C₀
  refine ⟨max (max K C₁) 2, 1 / 2, by positivity, by norm_num, ?_⟩
  intro ι _ _ key f hf2 hf0 h3 S hS N p p₀ hcard hp2 hpN hN hp₀ hSq lam γ hlam hl1 hγ
  have hmain := h ι key f hf2 hf0 h3 S hS N p p₀ (p - p₀) hcard hp2 hpN hN (by omega) hSq lam γ
    hlam hl1 hγ
  have hcast : ((p - p₀ : ℕ) : ℝ) = (p : ℝ) - p₀ := Nat.cast_sub hp₀
  rw [hcast] at hmain
  refine hmain.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  rw [log_mul_isolatedScale hβ hlam hl1]
  have hr0 := rate_nonneg β hlam.le
  have hγ0 : 0 < γ := hlam.trans_le hγ
  have hx0 : 0 ≤ (lam / γ) ^ (β - 2) := Real.rpow_nonneg (div_pos hlam hγ0).le _
  have hφ := rpow_div_le_isolatedPhi hβ h2 hlam hγ
  have hP : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hPN : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hlogN : 0 ≤ Real.log (N + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  have hKm : K ≤ max (max K C₁) 2 := (le_max_left _ _).trans (le_max_left _ _)
  have hC₁m : C₁ ≤ max (max K C₁) 2 := (le_max_right _ _).trans (le_max_left _ _)
  have h2m : (2 : ℝ) ≤ max (max K C₁) 2 := le_max_right _ _
  have e1 : K * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
        else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|) ≤
      max (max K C₁) 2 * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
        else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKm hP) hr0
  have e2 : C₁ * p * (lam / γ) ^ (β - 2) ≤ max (max K C₁) 2 * N * isolatedPhi β hβ lam γ := by
    calc C₁ * p * (lam / γ) ^ (β - 2) ≤ max (max K C₁) 2 * N * (lam / γ) ^ (β - 2) := by
          gcongr
      _ ≤ max (max K C₁) 2 * N * isolatedPhi β hβ lam γ := by
          gcongr
  have e3 : 2 * Real.log (N + 1) ≤ max (max K C₁) 2 * Real.log (N + 1) :=
    mul_le_mul_of_nonneg_right h2m hlogN
  have e : (p : ℝ) * (Real.log N + (if 2 < β then (2 - β) * Real.log lam else 0)
      + (if β = 2 then Real.log |Real.log lam| else 0) + Real.log (dipoleConstant β hβ)) =
      p * Real.log N + p * ((if 2 < β then (2 - β) * Real.log lam else 0)
        + (if β = 2 then Real.log |Real.log lam| else 0) + Real.log (dipoleConstant β hβ)) := by
    ring
  rw [e]
  linarith

/-! ### Step 4: the analogues of (eq:n neutral conv) and (eq:n neutral) with the `A₃` tilt -/

/-- **Theorem 2, Step 4: the tilted (eq:n neutral conv) with the `A₃` tilt** (source
l. 2143--2166). For `β > 2`, `C ≥ 0`, `C₀ ∈ ℝ` and `t ≥ 0` there are `C_{β,t}, c_{β,t} > 0`
(depending only on `β`, `C`, `C₀`, `t`) such that for every finite index type `ι` with `|ι| = 2p`,
tie-break key, graph `γ ∈ G_{p,p₀}` (a fixed-point-free involution `f`) with same-sign set `S`
(`f`-invariant, `|S| = 2(p - p₀)`), every `2 ≤ p ≤ N` with `p ≥ N/2`, `p₀ ≤ p`, `0 < λ ≤ e^{-1}` and
`γ ≥ λ`:
`p log p - p₀ log p₀ - (p-p₀) log (p-p₀) + C₀ (p-p₀)
  + log ∫_{cell} exp (t ∑_i ((r̃₁(z_i)/γ)² ∧ 1) - β F⁽¹⁾) - p (log N + (2-β) log λ + log 𝒵_β)
  ≤ -c p ((p - p₀)/p)² + C p r(λ) + C N φ_β(γ) + C log (N + 1)`,
with `F⁽¹⁾ = pairAssignedEnergy` (the energy of Proposition 3.9 and (def:F(1))) and the radii
computed within the block; stated for each graph as `e^{entropy} I(γ) ≤ e^{…}` (ruling R10). -/
theorem tiltedBlock_n_neutral_conv {β : ℝ} (hβ : 2 ≤ β) (h2 : 2 < β) {C : ℝ} (hC : 0 ≤ C)
    (C₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ Cβ cβ : ℝ, 0 < Cβ ∧ 0 < cβ ∧
      ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (f : ι → ι),
        (∀ i, f (f i) = i) → (∀ i, f i ≠ i) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
        (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (N p p₀ : ℕ), Fintype.card ι = 2 * p → 2 ≤ p → p ≤ N →
        (N : ℝ) ≤ 2 * p → p₀ ≤ p → S.card = 2 * (p - p₀) →
        ∀ lam γ : ℝ, 0 < lam → lam ≤ Real.exp (-1) → lam ≤ γ →
          ENNReal.ofReal (Real.exp (p * Real.log p - p₀ * Real.log p₀
              - ((p : ℝ) - p₀) * Real.log ((p : ℝ) - p₀) + C₀ * ((p : ℝ) - p₀))) *
            ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
              ENNReal.ofReal (Real.exp (t * ∑ i, min ((nnRadius lam z i / γ) ^ 2) 1
                - β * pairAssignedEnergy h3 key lam C S z)) ≤
          ENNReal.ofReal (Real.exp (p * (Real.log N
                + (if 2 < β then (2 - β) * Real.log lam else 0)
                + (if β = 2 then Real.log |Real.log lam| else 0)
                + Real.log (dipoleConstant β hβ))
              - cβ * p * (((p : ℝ) - p₀) / p) ^ 2
              + Cβ * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
                  else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|)
              + Cβ * N * isolatedPhi β hβ lam γ
              + Cβ * Real.log (N + 1))) := by
  obtain ⟨K, Ct, hK, hCt, h⟩ := tiltedBlock_le.{u} hβ h2 hC C₀ ht
  refine ⟨max (max K Ct) 1, 1, by positivity, one_pos, ?_⟩
  intro ι _ _ key f hf2 hf0 h3 S hS N p p₀ hcard hp2 hpN hN hp₀ hSq lam γ hlam hl1 hγ
  have hmain := h ι key f hf2 hf0 h3 S hS N p p₀ (p - p₀) hcard hp2 hpN hN (by omega) hSq lam γ
    hlam hl1 hγ
  have hcast : ((p - p₀ : ℕ) : ℝ) = (p : ℝ) - p₀ := Nat.cast_sub hp₀
  rw [hcast] at hmain
  refine hmain.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  rw [log_mul_isolatedScale hβ hlam hl1]
  have hr0 := rate_nonneg β hlam.le
  have hφ := isolatedPhi_nonneg hβ hlam hγ
  have hP : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hPN : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hlogN : 0 ≤ Real.log (N + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  have hKm : K ≤ max (max K Ct) 1 := (le_max_left _ _).trans (le_max_left _ _)
  have hCtm : Ct ≤ max (max K Ct) 1 := (le_max_right _ _).trans (le_max_left _ _)
  have h1m : (1 : ℝ) ≤ max (max K Ct) 1 := le_max_right _ _
  have e1 : K * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
        else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|) ≤
      max (max K Ct) 1 * p * (if β = 2 then |Real.log lam|⁻¹ else if β < 4 then lam ^ (β - 2)
        else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2 else lam ^ 2 * |Real.log lam|) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKm hP) hr0
  have e2 : Ct * p * isolatedPhi β hβ lam γ ≤ max (max K Ct) 1 * N * isolatedPhi β hβ lam γ := by
    gcongr
  have e3 : Real.log (N + 1) ≤ max (max K Ct) 1 * Real.log (N + 1) :=
    le_mul_of_one_le_left hlogN h1m
  have e : (p : ℝ) * (Real.log N + (if 2 < β then (2 - β) * Real.log lam else 0)
      + (if β = 2 then Real.log |Real.log lam| else 0) + Real.log (dipoleConstant β hβ)) =
      p * Real.log N + p * ((if 2 < β then (2 - β) * Real.log lam else 0)
        + (if β = 2 then Real.log |Real.log lam| else 0) + Real.log (dipoleConstant β hβ)) := by
    ring
  rw [e]
  linarith

end TwoComponentCoulomb

end
