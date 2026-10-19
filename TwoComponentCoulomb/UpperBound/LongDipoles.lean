/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.UpperBound.UpperAssembly
import TwoComponentCoulomb.Integrals.Radial

/-!
# Proposition 3.10, Step 4: control on the size of dipoles (`β > 2`)

Source: proof of Proposition 3.10, Step 4, l. 1643--1664, and the statement (eq:u bound),
l. 1440--1445.

For `R ≥ 2λ` let `α = μ_β([R/λ, ∞)) = (2π/𝒵_β) ∫_{R/λ}^∞ e^{β g_1(r)} r dr`. On the event
`{D_R ≥ p₀'}` at least `p₀'` isolated neutral pairs are longer than `R`; each such pair receives
the quadratic correction in `F⁽¹⁾`, and requiring it to be long bounds its radial factor by
`C_β ∫_{|u| ≥ R} e^{β g_λ} = C_β 𝒵_β λ^{2-β} α`, with the same remaining integral over the
representatives (l. 1644--1649). Summing over the choices of the long pairs costs `C(N, p₀')`
(l. 1651), which gives (eq:A'), and (eq:claim F(1)) gives (eq:u bound).

## Main results

* `TwoComponentCoulomb.LongDipoles.lintegral_closedBall_long_le`: the radial factor of a long
  neutral pair (l. 1644--1647); `tail_eq_mul_alpha`: `2π R^{2-β}/(β-2) = 𝒵_β λ^{2-β} α`.
* `TwoComponentCoulomb.LongDipoles.exists_lintegral_isolatedCell_long_le`: `(pred3)` with a set `L`
  of prescribed long neutral pairs: the factor `(e^{18βC} α)^{|L|}` in front of the same integral
  over the representatives (l. 1649).
* `TwoComponentCoulomb.LongDipoles.neutralReps`, `subset_iUnion_long`: the choice of the long
  pairs (l. 1651), at most `C(N, p₀')` choices (`card_neutralReps_le`).
* `TwoComponentCoulomb.LongDipoles.exists_cellBound_long_rate`: the per-cell bound `CellBoundRate`
  with the extra exponent `p₀' log (e^{C_m} α)` (l. 1644--1652), in the cases `m = 1`, `m = N` and
  `2 ≤ m < N`.
* `TwoComponentCoulomb.LongDipoles.log_choose_add_le`: (eq:claim F(1)) (l. 1658--1663).
* `TwoComponentCoulomb.LongDipoles.proposition_3_10_long_of_two_lt_rate`: **(eq:A') and
  (eq:u bound)**, the long-dipole clause of the frozen statement of Proposition 3.10.

The per-cell bound and (eq:u bound) are stated for a rate function `ω` satisfying
`TwoComponentCoulomb.UpperRateHyp` in place of `ω_λ`; they are instantiated at `errorRate` in
`UpperBound/UpperRate.lean` (`TwoComponentCoulomb.LongDipoles.proposition_3_10_long_of_two_lt`).
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace TwoComponentCoulomb

namespace LongDipoles

/-! ### The radial factor of a long pair (source l. 1644--1649) -/

section Radial

/-- `2π R^{2-β}/(β-2) = 𝒵_β λ^{2-β} α` with `α = (2π/𝒵_β) ∫_{R/λ}^∞ e^{β g_1(r)} r dr`, for
`R ≥ 2λ` (source l. 1645--1647). -/
theorem tail_eq_mul_alpha {β : ℝ} (hβ : 2 < β) {lam Rl : ℝ} (hlam : 0 < lam)
    (hRl : 2 * lam ≤ Rl) :
    2 * Real.pi * (Rl ^ (2 - β) / (β - 2)) =
      dipoleConstant β hβ.le * lam ^ (2 - β) * (2 * Real.pi / dipoleConstant β hβ.le *
        ∫ r in Set.Ici (Rl / lam), Real.exp (β * smearedKernel 1 r) * r) := by
  have hs : 2 ≤ Rl / lam := by rw [le_div_iff₀ hlam]; linarith
  have hRl0 : 0 < Rl := by linarith
  rw [integral_Ici_exp_smearedKernel_one hβ hs, Real.div_rpow hRl0.le hlam.le]
  have hZ := dipoleConstant_pos β hβ.le
  have h1 : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have h2 : β - 2 ≠ 0 := by linarith
  field_simp

/-- `α > 0` for `R ≥ 2λ`. -/
theorem alpha_pos {β : ℝ} (hβ : 2 < β) {lam Rl : ℝ} (hlam : 0 < lam) (hRl : 2 * lam ≤ Rl) :
    0 < 2 * Real.pi / dipoleConstant β hβ.le *
      ∫ r in Set.Ici (Rl / lam), Real.exp (β * smearedKernel 1 r) * r := by
  have hs : 2 ≤ Rl / lam := by rw [le_div_iff₀ hlam]; linarith
  rw [integral_Ici_exp_smearedKernel_one hβ hs]
  have hZ := dipoleConstant_pos β hβ.le
  have : 0 < (Rl / lam) ^ (2 - β) := Real.rpow_pos_of_pos (by linarith) _
  have : 0 < β - 2 := by linarith
  positivity

/-- **The radial factor of a long neutral pair** (source l. 1644--1647): for `ρ ≥ λ` and
`R ≥ 2λ`, the integral over `|u| ≤ 4ρ`, `|u| > R` of the neutral pair weight
`e^{β g_λ(u)} e^{C (a(u)/ρ)²}` is at most `e^{C} · 2π R^{2-β}/(β - 2)`, since `a(u) ≤ ρ` there. -/
theorem lintegral_closedBall_long_le {β : ℝ} (hβ : 2 < β) {C lam ρ Rl : ℝ} (hC : 0 ≤ C)
    (hlam : 0 < lam) (hρ : lam ≤ ρ) (hRl : 2 * lam ≤ Rl) :
    ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ),
        ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
          Real.exp (C * (displacementScale lam u / ρ) ^ 2)) *
          ({v : ℂ | Rl < ‖v‖}.indicator (fun _ => (1 : ℝ≥0∞)) u) ≤
      ENNReal.ofReal (Real.exp C * (2 * Real.pi * (Rl ^ (2 - β) / (β - 2)))) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hlam hρ
  set G : ℂ → ℝ≥0∞ := (Metric.ball (0 : ℂ) Rl)ᶜ.indicator
    (fun u => ENNReal.ofReal (Real.exp C * Real.exp (β * smearedKernel lam u))) with hG
  have hpt : ∀ u ∈ Metric.closedBall (0 : ℂ) (4 * ρ),
      ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
          Real.exp (C * (displacementScale lam u / ρ) ^ 2)) *
          ({v : ℂ | Rl < ‖v‖}.indicator (fun _ => (1 : ℝ≥0∞)) u) ≤ G u := by
    intro u hu
    by_cases hlong : Rl < ‖u‖
    · have hmem : u ∈ (Metric.ball (0 : ℂ) Rl)ᶜ := by
        simp only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt]
        exact hlong.le
      rw [Set.indicator_of_mem (show u ∈ {v : ℂ | Rl < ‖v‖} from hlong), mul_one, hG,
        Set.indicator_of_mem hmem]
      refine ENNReal.ofReal_le_ofReal ?_
      have ha := displacementScale_le_of_norm_le hρ (mem_closedBall_zero_iff.1 hu)
      have ha0 := (displacementScale_pos hlam u).le
      have hs : (displacementScale lam u / ρ) ^ 2 ≤ 1 := by
        rw [div_pow, div_le_one (by positivity)]
        exact pow_le_pow_left₀ ha0 ha 2
      have : Real.exp (C * (displacementScale lam u / ρ) ^ 2) ≤ Real.exp C :=
        Real.exp_le_exp.2 (mul_le_of_le_one_right hC hs)
      rw [mul_comm (Real.exp C)]
      exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem (show u ∉ {v : ℂ | Rl < ‖v‖} from hlong), mul_zero]
      exact zero_le
  have hint : Integrable (fun u : ℂ => Real.exp C * Real.exp (β * smearedKernel lam u))
      (volume.restrict (Metric.ball (0 : ℂ) Rl)ᶜ) :=
    ((integrable_exp_smearedKernel hβ hlam).const_mul _).integrableOn
  calc _ ≤ ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * ρ), G u :=
        setLIntegral_mono' Metric.isClosed_closedBall.measurableSet hpt
    _ ≤ ∫⁻ u, G u := setLIntegral_le_lintegral _ _
    _ = ∫⁻ u in (Metric.ball (0 : ℂ) Rl)ᶜ,
          ENNReal.ofReal (Real.exp C * Real.exp (β * smearedKernel lam u)) :=
        lintegral_indicator Metric.isOpen_ball.measurableSet.compl _
    _ = ENNReal.ofReal (∫ u in (Metric.ball (0 : ℂ) Rl)ᶜ,
          Real.exp C * Real.exp (β * smearedKernel lam u)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun u => by positivity)).symm
    _ = _ := by
        rw [integral_const_mul, integral_compl_ball_exp_smearedKernel hβ hlam hRl]

end Radial

/-! ### `(pred3)` with prescribed long pairs (source l. 1644--1651) -/

section Pred3

open IsolatedReduction

open scoped Classical in
/-- **`(pred3)` with prescribed long neutral pairs** (source l. 1644--1651): for `β > 2` and
`C ≥ 0` there is `C' > 0` (depending only on `β` and `C`) such that for every finite index type,
fixed-point-free involution `f` with set of representatives `R`, `f`-invariant `S`, every set `L`
of representatives of pairs not in `S` (the pairs `j ∉ S` of l. 1644), `R_l ≥ 2λ` and
`0 < λ ≤ e⁻¹`, the integral of `exp(-β E)`, `E = pairAssignedEnergy h3 key λ C S`, over the cell
intersected with `{|z_{f j} - z_j| > R_l, j ∈ L}` is at most
`(e^{18βC} α)^{|L|} (𝒵_β λ^{2-β})^{|R|} ∫_{Λ^R} ∏_{j ∈ R ∖ S} (1 + C' φ_β(ρ_j))
  ∏_{j ∈ R ∩ S} C' τ_β(ρ_j) dW`
for any `α` with `2π R_l^{2-β}/(β-2) ≤ 𝒵_β λ^{2-β} α`: each long pair's radial factor is
replaced by `e^{18βC} 𝒵_β λ^{2-β} α ≤ e^{18βC} α · 𝒵_β λ^{2-β} (1 + C' φ_β)`. -/
theorem exists_lintegral_isolatedCell_long_le {β : ℝ} (hβ : 2 < β) {C : ℝ} (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (ι : Type) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (f : ι → ι)
      (R : Set ι) [DecidablePred (· ∈ R)] [Nontrivial {i // i ∈ R}],
      (∀ i, f (f i) = i) → (∀ i, i ∈ R ↔ f i ∉ R) → ∀ (h3 : 3 ≤ Fintype.card ι) (S : Finset ι),
      (∀ i, f i ∈ S ↔ i ∈ S) → ∀ (L : Finset {i // i ∈ R}), (∀ j ∈ L, (j : ι) ∉ S) →
      ∀ (N : ℕ) (lam Rl α : ℝ), 0 < lam → lam ≤ Real.exp (-1) → 2 * lam ≤ Rl →
      2 * Real.pi * (Rl ^ (2 - β) / (β - 2)) ≤ dipoleConstant β hβ.le * lam ^ (2 - β) * α →
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f} ∩
            {z | ∀ j ∈ L, Rl < ‖z (f j) - z j‖},
            ENNReal.ofReal (Real.exp (-(β * pairAssignedEnergy h3 key lam C S z))) ≤
          ENNReal.ofReal (Real.exp (18 * β * C) * α) ^ L.card *
            (ENNReal.ofReal (dipoleConstant β hβ.le * isolatedScale β hβ.le lam) ^
                Fintype.card {i // i ∈ R} *
              ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
                ∏ j : {i // i ∈ R}, ENNReal.ofReal (if (j : ι) ∈ S then
                  C' * isolatedTail β hβ.le lam (nnRadius lam w j)
                  else 1 + C' * isolatedPhi β hβ.le lam (nnRadius lam w j))) := by
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨Cn, hCn0, hCn⟩ := lintegral_neutralPair_le hβ.le (C := 18 * β * C) (by positivity)
  obtain ⟨Cs, hCs0, hCs⟩ := lintegral_sameSignPair_le_normalized hβ.le
  have hC₂ : 0 ≤ Real.exp (2 * β * C) * (3 : ℝ) ^ (2 * β) := by positivity
  set C' := max Cn (Real.exp (2 * β * C) * 3 ^ (2 * β) * Cs) with hC'def
  refine ⟨C', lt_max_of_lt_left hCn0, ?_⟩
  intro ι _ _ key f R _ _ hf2 hRf h3 S hS L hLS N lam Rl α hlam hl1 hRl hα
  have hZ := dipoleConstant_pos β hβ.le
  have hscale := isolatedScale_pos hβ.le hlam hl1
  have hscale' : isolatedScale β hβ.le lam = lam ^ (2 - β) := by
    simp [isolatedScale, hβ.ne']
  have hC'0 : 0 < C' := lt_max_of_lt_left hCn0
  -- the long sets
  set Long : Set (ι → ℂ) := {z | ∀ j ∈ L, Rl < ‖z (f j) - z j‖} with hLong
  have hcell : MeasurableSet {z : ι → ℂ | nnMap key z = f} := by
    have : {z : ι → ℂ | nnMap key z = f} = ⋂ i, {z | nnMap key z i = f i} := by
      ext z; simp [funext_iff]
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_nnMap_eq key i (f i)
  have hcell' : MeasurableSet ((Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f}) :=
    (MeasurableSet.univ_pi fun _ => measurableSet_box N).inter hcell
  have hLongm : MeasurableSet Long := by
    have : Long = ⋂ j ∈ L, {z : ι → ℂ | Rl < ‖z (f j) - z j‖} := by
      ext z; simp [hLong]
    rw [this]
    refine Finset.measurableSet_biInter _ fun j _ => measurableSet_lt measurable_const ?_
    fun_prop
  -- the modified pair weights
  set ind : ℂ → ℝ≥0∞ := {v : ℂ | Rl < ‖v‖}.indicator (fun _ => (1 : ℝ≥0∞)) with hind
  have hindm : Measurable ind :=
    measurable_const.indicator (measurableSet_lt measurable_const measurable_norm)
  set Φ : {i // i ∈ R} → ℂ → ℝ → ℝ≥0∞ := fun j u ρ =>
    pairWeight β C lam S j u ρ * (if j ∈ L then ind u else 1) with hΦdef
  -- Step 1: the integrand bound on the cell and the long set
  have hpt : ∀ z ∈ (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f} ∩ Long,
      ENNReal.ofReal (Real.exp (-(β * pairAssignedEnergy h3 key lam C S z))) ≤
        ∏ j : {i // i ∈ R}, Φ j (z (f j) - z j) (nnRadius lam (fun l : {i // i ∈ R} => z l) j) := by
    rintro z ⟨⟨_, hz⟩, hzL⟩
    refine (ofReal_exp_neg_mul_pairAssignedEnergy_le hz hf2 hRf h3 hS hβ0 hC hlam).trans
      (le_of_eq ?_)
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hΦdef]
    by_cases hj : j ∈ L
    · rw [ite_eq_left hj, hind, Set.indicator_of_mem (show z (f j) - z j ∈ {v : ℂ | Rl < ‖v‖} from
        hzL j hj), mul_one]
    · rw [ite_eq_right hj, mul_one]
  have hstep1 : ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f} ∩ Long,
      ENNReal.ofReal (Real.exp (-(β * pairAssignedEnergy h3 key lam C S z))) ≤
      ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
        ∏ j : {i // i ∈ R}, Φ j (z (f j) - z j) (nnRadius lam (fun l : {i // i ∈ R} => z l) j) :=
    (setLIntegral_mono' (hcell'.inter hLongm) hpt).trans
      (lintegral_mono_set Set.inter_subset_left)
  -- Step 2: displacement reduction
  have hg : Measurable (smearedKernel lam) := measurable_smearedKernel lam
  have hd : Measurable (displacementScale lam) := (continuous_displacementScale lam).measurable
  have e1 : Measurable fun p : ℂ × ℝ => Real.exp (β * smearedKernel lam p.1) :=
    Real.measurable_exp.comp ((hg.comp measurable_fst).const_mul β)
  have e2 : Measurable fun p : ℂ × ℝ => displacementScale lam p.1 / p.2 :=
    (hd.comp measurable_fst).div measurable_snd
  have hΦ : ∀ j : {i // i ∈ R}, Measurable fun p : ℂ × ℝ => Φ j p.1 p.2 := by
    intro j
    have hw : Measurable fun p : ℂ × ℝ => pairWeight β C lam S j p.1 p.2 := by
      by_cases hj : (j : ι) ∈ S
      · simp only [pairWeight, hj, ↓reduceIte]
        exact (ENNReal.measurable_ofReal.comp (e1.mul (e2.pow_const (2 * β)))).const_mul _
      · simp only [pairWeight, hj, ↓reduceIte]
        exact ENNReal.measurable_ofReal.comp
          (e1.mul (Real.measurable_exp.comp ((e2.pow_const 2).const_mul _)))
    by_cases hj : j ∈ L
    · simp only [hΦdef, hj, ↓reduceIte]
      exact hw.mul (hindm.comp measurable_fst)
    · simp only [hΦdef, hj, ↓reduceIte, mul_one]
      exact hw
  refine hstep1.trans ((lintegral_cell_le_lintegral_ref key hf2 hRf lam Φ hΦ).trans ?_)
  -- Step 3: the radial integrals
  have hα0 : 0 ≤ α := by
    have h1 : 0 < 2 * Real.pi * (Rl ^ (2 - β) / (β - 2)) := by
      have : 0 < β - 2 := by linarith
      have : 0 < Rl ^ (2 - β) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    have h2 : 0 < dipoleConstant β hβ.le * lam ^ (2 - β) :=
      mul_pos hZ (Real.rpow_pos_of_pos hlam _)
    by_contra h
    push Not at h
    have : dipoleConstant β hβ.le * lam ^ (2 - β) * α < 0 := mul_neg_of_pos_of_neg h2 h
    linarith
  set Mα : ℝ := Real.exp (18 * β * C) * α with hMα
  have hMα0 : 0 ≤ Mα := mul_nonneg (Real.exp_pos _).le hα0
  have hinner : ∀ (w : {i // i ∈ R} → ℂ) (j : {i // i ∈ R}),
      ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j), Φ j u (nnRadius lam w j) ≤
        (if j ∈ L then ENNReal.ofReal Mα else 1) *
          (ENNReal.ofReal (dipoleConstant β hβ.le * isolatedScale β hβ.le lam) *
            ENNReal.ofReal (if (j : ι) ∈ S then C' * isolatedTail β hβ.le lam (nnRadius lam w j)
              else 1 + C' * isolatedPhi β hβ.le lam (nnRadius lam w j))) := by
    intro w j
    have hρ : lam ≤ nnRadius lam w j := le_nnRadius lam w j
    have hρ0 : 0 < nnRadius lam w j := lt_of_lt_of_le hlam hρ
    by_cases hjL : j ∈ L
    · have hjS := hLS j hjL
      simp only [hΦdef, pairWeight, hjS, hjL, ↓reduceIte]
      have h1 := lintegral_closedBall_long_le hβ (C := 18 * β * C) (by positivity) hlam hρ hRl
      refine h1.trans ?_
      have hφ := isolatedPhi_nonneg hβ.le hlam hρ
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hMα0]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hscale']
      have h2 : Real.exp (18 * β * C) * (2 * Real.pi * (Rl ^ (2 - β) / (β - 2))) ≤
          Real.exp (18 * β * C) * (dipoleConstant β hβ.le * lam ^ (2 - β) * α) :=
        mul_le_mul_of_nonneg_left hα (Real.exp_pos _).le
      have h3' : 0 ≤ dipoleConstant β hβ.le * lam ^ (2 - β) * α := by
        have : 0 ≤ 2 * Real.pi * (Rl ^ (2 - β) / (β - 2)) := by
          have : 0 < β - 2 := by linarith
          have : 0 ≤ Rl ^ (2 - β) := Real.rpow_nonneg (by linarith) _
          positivity
        linarith
      have h4 : 1 ≤ 1 + C' * isolatedPhi β hβ.le lam (nnRadius lam w j) := by
        have := mul_nonneg hC'0.le hφ
        linarith
      have h5 : 0 ≤ Real.exp (18 * β * C) * (dipoleConstant β hβ.le * lam ^ (2 - β) * α) :=
        mul_nonneg (Real.exp_pos _).le h3'
      calc Real.exp (18 * β * C) * (2 * Real.pi * (Rl ^ (2 - β) / (β - 2)))
          ≤ Real.exp (18 * β * C) * (dipoleConstant β hβ.le * lam ^ (2 - β) * α) := h2
        _ ≤ Real.exp (18 * β * C) * (dipoleConstant β hβ.le * lam ^ (2 - β) * α) *
              (1 + C' * isolatedPhi β hβ.le lam (nnRadius lam w j)) :=
            le_mul_of_one_le_right h5 h4
        _ = _ := by rw [hMα]; ring
    · simp only [hΦdef, hjL, ↓reduceIte, mul_one, one_mul]
      by_cases hj : (j : ι) ∈ S
      · simp only [pairWeight, hj, ↓reduceIte]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have h1 := hCs lam (nnRadius lam w j) hlam hl1 hρ
        have ht := isolatedTail_nonneg hβ.le hlam hρ0
        calc ENNReal.ofReal (Real.exp (2 * β * C) * 3 ^ (2 * β)) * ∫⁻ u in Metric.closedBall
                (0 : ℂ) (4 * nnRadius lam w j), ENNReal.ofReal (Real.exp (β * smearedKernel lam u) *
                  (displacementScale lam u / nnRadius lam w j) ^ (2 * β))
            ≤ ENNReal.ofReal (Real.exp (2 * β * C) * 3 ^ (2 * β)) * ENNReal.ofReal (Cs *
                dipoleConstant β hβ.le * isolatedScale β hβ.le lam *
                  isolatedTail β hβ.le lam (nnRadius lam w j)) := by gcongr
          _ = ENNReal.ofReal (Real.exp (2 * β * C) * 3 ^ (2 * β) * (Cs *
                dipoleConstant β hβ.le * isolatedScale β hβ.le lam *
                  isolatedTail β hβ.le lam (nnRadius lam w j))) := (ENNReal.ofReal_mul hC₂).symm
          _ ≤ _ := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              refine ENNReal.ofReal_le_ofReal ?_
              have hq : 0 ≤ dipoleConstant β hβ.le * isolatedScale β hβ.le lam *
                  isolatedTail β hβ.le lam (nnRadius lam w j) := by positivity
              have hE : Real.exp (2 * β * C) * 3 ^ (2 * β) * Cs ≤ C' := le_max_right _ _
              have := mul_le_mul_of_nonneg_right hE hq
              linarith only [this]
      · simp only [pairWeight, hj, ↓reduceIte]
        have h1 := hCn lam (nnRadius lam w j) hlam hl1 hρ
        have hφ := isolatedPhi_nonneg hβ.le hlam hρ
        calc _ ≤ ENNReal.ofReal (dipoleConstant β hβ.le * isolatedScale β hβ.le lam *
                (1 + Cn * isolatedPhi β hβ.le lam (nnRadius lam w j))) := h1
          _ ≤ _ := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              refine ENNReal.ofReal_le_ofReal ?_
              have : Cn ≤ C' := le_max_left _ _
              have hq : 0 ≤ dipoleConstant β hβ.le * isolatedScale β hβ.le lam := by positivity
              gcongr
  calc ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
        ∏ j : {i // i ∈ R}, ∫⁻ u in Metric.closedBall (0 : ℂ) (4 * nnRadius lam w j),
          Φ j u (nnRadius lam w j)
      ≤ ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
          ∏ j : {i // i ∈ R}, ((if j ∈ L then ENNReal.ofReal Mα else 1) *
            (ENNReal.ofReal (dipoleConstant β hβ.le * isolatedScale β hβ.le lam) *
            ENNReal.ofReal (if (j : ι) ∈ S then C' * isolatedTail β hβ.le lam (nnRadius lam w j)
              else 1 + C' * isolatedPhi β hβ.le lam (nnRadius lam w j)))) :=
        lintegral_mono fun w => Finset.prod_le_prod fun j _ => hinner w j
    _ = ∫⁻ w in Set.univ.pi fun _ : {i // i ∈ R} => box N,
          ENNReal.ofReal Mα ^ L.card *
            (ENNReal.ofReal (dipoleConstant β hβ.le * isolatedScale β hβ.le lam) ^
                Fintype.card {i // i ∈ R} *
              ∏ j : {i // i ∈ R}, ENNReal.ofReal (if (j : ι) ∈ S then
                C' * isolatedTail β hβ.le lam (nnRadius lam w j)
                else 1 + C' * isolatedPhi β hβ.le lam (nnRadius lam w j))) := by
        refine lintegral_congr fun w => ?_
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_mem,
          Finset.univ_inter, Finset.prod_const, Finset.prod_const, Finset.card_univ]
    _ = _ := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]

end Pred3

/-! ### Long dipoles and prescribed long pairs (source l. 1651) -/

section Events

variable {N : ℕ}

open scoped Classical in
/-- The representatives of the isolated neutral pairs of `φ`: the vertex `i` of the isolated pair
`{i, φ i}` with opposite charges having the smaller key (one vertex per pair). -/
noncomputable def neutralReps (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) : Finset (Fin N ⊕ Fin N) :=
  Finset.univ.filter fun i =>
    i ∈ pairVerts φ ∧ charge i * charge (φ i) = -1 ∧ sumKey N i < sumKey N (φ i)

theorem mem_neutralReps {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} {i : Fin N ⊕ Fin N} :
    i ∈ neutralReps φ ↔
      i ∈ pairVerts φ ∧ charge i * charge (φ i) = -1 ∧ sumKey N i < sumKey N (φ i) := by
  classical
  unfold neutralReps
  rw [mem_filter]
  exact and_iff_right (mem_univ i)

/-- The representatives of the isolated neutral pairs and their partners are disjoint subsets of
`I^pair`: `2 |reps| ≤ |I^pair|`. -/
theorem two_mul_card_neutralReps_le (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) :
    2 * (neutralReps φ).card ≤ (pairVerts φ).card := by
  classical
  have hinj : Set.InjOn φ (neutralReps φ : Set (Fin N ⊕ Fin N)) := by
    intro a ha b hb hab
    have ha' := (mem_pairVerts.1 (mem_neutralReps.1 ha).1).1
    have hb' := (mem_pairVerts.1 (mem_neutralReps.1 hb).1).1
    rw [← ha', ← hb', hab]
  have hdisj : Disjoint (neutralReps φ) ((neutralReps φ).image φ) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi'
    have h1 := (mem_neutralReps.1 hj).2.2
    have h2 := (mem_neutralReps.1 hi).2.2
    rw [(mem_pairVerts.1 (mem_neutralReps.1 hj).1).1] at h2
    omega
  have hsub : (neutralReps φ) ∪ (neutralReps φ).image φ ⊆ pairVerts φ := by
    intro i hi
    rcases Finset.mem_union.1 hi with h | h
    · exact (mem_neutralReps.1 h).1
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
      exact apply_mem_pairVerts (mem_neutralReps.1 hj).1
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj] at h
  omega

/-- At most `N` isolated neutral pairs. -/
theorem card_neutralReps_le (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) : (neutralReps φ).card ≤ N := by
  have h1 := two_mul_card_neutralReps_le φ
  have h2 := Finset.card_le_univ (pairVerts φ)
  simp only [Fintype.card_sum, Fintype.card_fin] at h2
  omega

/-- The representatives in `L ⊆ reps` correspond to the representatives of the reference set
`gpRefSet key f` of a block `ι` embedded by `e` (with `key = sumKey ∘ e` and `e ∘ f = φ ∘ e`). -/
theorem card_filter_gpRefSet_eq {ι : Type} [Fintype ι] (e : ι → Fin N ⊕ Fin N)
    (he : Function.Injective e) {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N} (f : ι → ι)
    (hf : ∀ j, e (f j) = φ (e j)) (key : ι ↪ ℕ) (hkey : ∀ j, key j = sumKey N (e j))
    {L : Finset (Fin N ⊕ Fin N)} (hL : L ⊆ neutralReps φ) (hLr : ∀ i ∈ L, ∃ j, e j = i) :
    (Finset.univ.filter fun j : {j // j ∈ gpRefSet key f} => e j ∈ L).card = L.card := by
  classical
  refine Finset.card_bij (fun j _ => e j) (fun j hj => (mem_filter.1 hj).2)
    (fun j₁ _ j₂ _ h => Subtype.ext (he h)) ?_
  intro i hi
  obtain ⟨j, rfl⟩ := hLr i hi
  obtain ⟨hpv, -, hk⟩ := mem_neutralReps.1 (hL hi)
  have h2 : f (f j) = j := he (by rw [hf, hf]; exact (mem_pairVerts.1 hpv).1)
  have hR : j ∈ gpRefSet key f := ⟨h2, by rw [hkey, hkey, hf]; exact hk⟩
  exact ⟨⟨j, hR⟩, mem_filter.2 ⟨mem_univ _, hi⟩, rfl⟩

/-- On the cell of `φ`, the long isolated dipoles are at most the long isolated neutral pairs
counted by their representatives. -/
theorem card_longIsolatedDipoles_le {Z : Fin N ⊕ Fin N → ℂ} (Rl : ℝ) :
    (longIsolatedDipoles Z Rl).card ≤
      ((neutralReps (nearestNeighbor Z)).filter
        fun i => Rl < ‖Z (nearestNeighbor Z i) - Z i‖).card := by
  classical
  set φ := nearestNeighbor Z with hφ
  set D := Finset.univ.filter fun i => IsIsolatedDipole Z i ∧ Rl < ‖Z i - Z (φ i)‖ with hD
  have hrep : ∀ i ∈ D, ∃ j ∈ D.filter (fun j => sumKey N j < sumKey N (φ j)),
      ({j, φ j} : Finset (Fin N ⊕ Fin N)) = {i, φ i} := by
    intro i hi
    obtain ⟨hdip, hlong⟩ := (mem_filter.1 hi).2
    have hpair := ((isIsolatedDipole_iff Z i).1 hdip).1
    have h2 : φ (φ i) = i := hpair.1
    have hne : sumKey N i ≠ sumKey N (φ i) := fun h =>
      nearestNeighbor_ne Z i ((sumKey N).injective h).symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨i, mem_filter.2 ⟨hi, hlt⟩, rfl⟩
    · refine ⟨φ i, mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, by rw [h2]; exact hgt⟩, ?_⟩
      · rw [isIsolatedDipole_iff]
        refine ⟨isIsolatedPair_nearestNeighbor hpair, ?_⟩
        rw [← hφ, h2, mul_comm]
        exact ((isIsolatedDipole_iff Z i).1 hdip).2
      · rw [h2, norm_sub_rev]
        exact hlong
      · rw [h2, Finset.pair_comm]
  have hsub : D.image (fun i => ({i, φ i} : Finset (Fin N ⊕ Fin N))) ⊆
      (D.filter fun j => sumKey N j < sumKey N (φ j)).image fun i => {i, φ i} := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, hj, hji⟩ := hrep i hi
    exact Finset.mem_image.2 ⟨j, hj, hji⟩
  have hsub2 : D.filter (fun j => sumKey N j < sumKey N (φ j)) ⊆
      (neutralReps φ).filter fun i => Rl < ‖Z (φ i) - Z i‖ := by
    intro i hi
    obtain ⟨hiD, hkey⟩ := mem_filter.1 hi
    obtain ⟨hdip, hlong⟩ := (mem_filter.1 hiD).2
    obtain ⟨hpair, hch⟩ := (isIsolatedDipole_iff Z i).1 hdip
    refine mem_filter.2 ⟨mem_neutralReps.2 ⟨mem_pairVerts_nearestNeighbor.2 hpair, hch, hkey⟩, ?_⟩
    rw [norm_sub_rev]
    exact hlong
  have heq : longIsolatedDipoles Z Rl = D.image fun i => ({i, φ i} : Finset (Fin N ⊕ Fin N)) := by
    unfold longIsolatedDipoles
    rfl
  rw [heq]
  exact (card_le_card hsub).trans (card_image_le.trans (card_le_card hsub2))

/-- **The choice of the long pairs** (source l. 1651): on the cell of `φ`, the event
`{D_R ≥ p₀'}` is contained in the union, over the sets `L` of `p₀'` representatives of isolated
neutral pairs, of the events that all pairs of `L` are longer than `R`. -/
theorem subset_iUnion_long (hN : 2 ≤ N) {φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N}
    {T : Finset (Fin N ⊕ Fin N)} (Rl : ℝ) (p₀' : ℕ) :
    {Z | p₀' ≤ (longIsolatedDipoles Z Rl).card} ∩ markedCell hN φ T ⊆
      ⋃ L ∈ (neutralReps φ).powersetCard p₀', {Z | ∀ i ∈ L, Rl < ‖Z (φ i) - Z i‖} := by
  classical
  rintro Z ⟨hZ, hZc⟩
  have hφ : nearestNeighbor Z = φ := hZc.2.1
  have h := (show p₀' ≤ _ from hZ).trans (card_longIsolatedDipoles_le (Z := Z) Rl)
  rw [hφ] at h
  obtain ⟨L, hL, hLc⟩ := Finset.exists_subset_card_eq h
  refine Set.mem_iUnion₂.2 ⟨L, Finset.mem_powersetCard.2 ⟨hL.trans (filter_subset _ _), hLc⟩, ?_⟩
  intro i hi
  exact (mem_filter.1 (hL hi)).2

/-- The set integral over `A ∩ E ∩ C` with `E` contained in a finite union is at most the sum of
the set integrals over the pieces. -/
theorem setLIntegral_le_sum_of_subset {α κ : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset κ) (B : κ → Set α) (A E C : Set α) (hE : E ∩ C ⊆ ⋃ L ∈ s, B L)
    (F : α → ℝ≥0∞) :
    ∫⁻ x in A ∩ E ∩ C, F x ∂μ ≤ ∑ L ∈ s, ∫⁻ x in A ∩ B L ∩ C, F x ∂μ := by
  classical
  have h1 : A ∩ E ∩ C ⊆ ⋃ L ∈ s, A ∩ B L ∩ C := by
    rintro x ⟨⟨hA, hE'⟩, hC⟩
    obtain ⟨L, hL, hx⟩ := Set.mem_iUnion₂.1 (hE ⟨hE', hC⟩)
    exact Set.mem_iUnion₂.2 ⟨L, hL, ⟨hA, hx⟩, hC⟩
  refine (lintegral_mono_set h1).trans ?_
  clear h1 hE
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

end Events

/-! ### The per-cell bound with prescribed long pairs (source l. 1644--1652) -/

section Cell

open UpperCellBound UpperAssembly

/-- A bound with prescribed long pairs (`I ≤ (Mα)^k Q`) and a bound on `e^H Q` combine into
`e^H I ≤ exp (B + k log (Mα))`. -/
theorem ofReal_exp_mul_le_of_long {I Q : ℝ≥0∞} {Mα H B : ℝ} {k : ℕ} (hMα : 0 < Mα)
    (hI : I ≤ ENNReal.ofReal Mα ^ k * Q)
    (hQ : ENNReal.ofReal (Real.exp H) * Q ≤ ENNReal.ofReal (Real.exp B)) :
    ENNReal.ofReal (Real.exp H) * I ≤ ENNReal.ofReal (Real.exp (B + k * Real.log Mα)) := by
  have hpow : ENNReal.ofReal Mα ^ k = ENNReal.ofReal (Real.exp (k * Real.log Mα)) := by
    rw [← ENNReal.ofReal_pow hMα.le, Real.exp_nat_mul, Real.exp_log hMα]
  calc ENNReal.ofReal (Real.exp H) * I
      ≤ ENNReal.ofReal (Real.exp H) * (ENNReal.ofReal Mα ^ k * Q) := mul_le_mul_right hI _
    _ = ENNReal.ofReal Mα ^ k * (ENNReal.ofReal (Real.exp H) * Q) := by ring
    _ ≤ ENNReal.ofReal Mα ^ k * ENNReal.ofReal (Real.exp B) := mul_le_mul_right hQ _
    _ = _ := by rw [hpow, ofReal_exp_mul_ofReal_exp, add_comm]

variable {N : ℕ}

/-- **The per-cell bound with prescribed long pairs, generic rate** (source l. 1644--1652): the
per-cell bound `CellBoundRate`, with the extra exponent `p₀' log (e^{C_m} α)`, for a rate `ω`
satisfying `UpperRateHyp` in place of `ω_λ`. -/
theorem exists_cellBound_long_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ)
    (hω : UpperRateHyp β hβ ω) :
    ∃ A c Cb Cm : ℝ, 0 < c ∧ 0 ≤ Cb ∧ 0 ≤ Cm ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (lam Rl α : ℝ), 0 < lam → lam ≤ Real.exp (-1) → 2 * lam ≤ Rl →
      2 * Real.pi * (Rl ^ (2 - β) / (β - 2)) = dipoleConstant β hβ.le * lam ^ (2 - β) * α →
      ∀ (K p p₀ : ℕ) (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (T : Finset (Fin N ⊕ Fin N)),
        (φ, T) ∈ markedGraphs hN K p p₀ → ∀ (p₀' : ℕ), 1 ≤ p₀' →
        ∀ L ∈ (neutralReps φ).powersetCard p₀',
        CellBoundRate β hβ ω A c Cb N K p p₀ lam (p₀' * Real.log (Real.exp Cm * α))
          (∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
              {Z | ∀ i ∈ L, Rl < ‖Z (φ i) - Z i‖} ∩ markedCell hN φ T,
            ENNReal.ofReal (Real.exp (-β * energy lam Z))) := by
  classical
  obtain ⟨Cc, hCc0, hCc⟩ := exists_corollary23Holds
  obtain ⟨C', hC', hpred⟩ := exists_lintegral_isolatedCell_long_le hβ hCc0.le
  obtain ⟨C₁, c₁, hC₁, hc₁, hconvA⟩ := exists_anchor_conv hβ hC' 60
  obtain ⟨C₂, hC₂, hcrudeA⟩ := exists_anchor_crude hβ hC' 60
  obtain ⟨C₄, hF2⟩ := exists_lintegral_nnEnergy_le hβ
  set Lz := Real.log (dipoleConstant β hβ.le) with hLz
  refine ⟨β * Cc + C₄, c₁, C₁ + C₂ + |Lz|, 18 * β * Cc, hc₁, by positivity,
    by have : 0 ≤ β := by linarith
       positivity, ?_⟩
  intro N hN lam Rl α hlam hlam1 hRl hα K p p₀ φ T hγ p₀' hp₀' L hL
  obtain ⟨hLsub, hLc⟩ := Finset.mem_powersetCard.1 hL
  obtain ⟨Z₀, -, hgen, hφ, hT, hK, hp, hp₀⟩ := mem_markedGraphs.1 hγ
  subst hφ hT hK
  set m := numIsolatedPairs Z₀ with hm
  have hmK : m ≤ numComponents Z₀ := numIsolatedPairs_le_numComponents Z₀
  have hKN : numComponents Z₀ ≤ N := numComponents_le Z₀
  have hpm : p ≤ m := hp ▸ numTwiceIsolated_le_numIsolatedPairs
  have hp₀p : p₀ ≤ p := hp ▸ hp₀ ▸ numNeutralTwiceIsolated_le_numTwiceIsolated
  have hNpos : 0 < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨hr0, hr⟩ := isolatedRate_le_rate hβ ω hω hlam hlam1
  have hω0 : 0 ≤ ω lam := hr0.trans hr
  have hlogN : 0 ≤ Real.log (N + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  have hNω : 0 ≤ (N : ℝ) * ω lam := mul_nonneg hN0.le hω0
  have hCb : 0 ≤ C₁ + C₂ + |Lz| := by positivity
  have hZ := dipoleConstant_pos β hβ.le
  have hα0 : 0 < α := by
    have h1 : 0 < 2 * Real.pi * (Rl ^ (2 - β) / (β - 2)) := by
      have : 0 < β - 2 := by linarith
      have : 0 < Rl ^ (2 - β) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    have h2 : 0 < dipoleConstant β hβ.le * lam ^ (2 - β) := mul_pos hZ (Real.rpow_pos_of_pos hlam _)
    rw [hα] at h1
    exact pos_of_mul_pos_right h1 h2.le
  have hMα : 0 < Real.exp (18 * β * Cc) * α := mul_pos (Real.exp_pos _) hα0
  have hlogMα : Real.log (Real.exp (18 * β * Cc) * α) = 18 * β * Cc + Real.log α := by
    rw [Real.log_mul (Real.exp_pos _).ne' hα0.ne', Real.log_exp]
  obtain ⟨hF2c, hF2f⟩ := hF2 N Z₀ (nearestNeighbor Z₀) hNpos rfl lam hlam hlam1
  have hcardPV : (pairVerts (nearestNeighbor Z₀)).card = 2 * m := by
    rw [← isolatedPairSet_eq_pairVerts, card_isolatedPairSet]
  have hreps := two_mul_card_neutralReps_le (nearestNeighbor Z₀)
  have hLle : p₀' ≤ m := by
    have := Finset.card_le_card hLsub
    omega
  set E : Set (Fin N ⊕ Fin N → ℂ) :=
    {Z | ∀ i ∈ L, Rl < ‖Z (nearestNeighbor Z₀ i) - Z i‖} with hEdef
  have hT2 : ∀ Z ∈ markedCell hN (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀),
      twiceIsolatedSet hN Z = twiceIsolatedSet hN Z₀ := fun Z hZ => hZ.2.2
  have hK2 : ∀ Z ∈ markedCell hN (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀),
      numComponents Z = numComponents Z₀ := fun Z hZ =>
    numComponents_eq_of_mem_markedCell hγ hZ
  have hcardI : Fintype.card {i // i ∈ pairVerts (nearestNeighbor Z₀)} = 2 * m :=
    card_pairVerts_subtype rfl
  have hf2 := pairRestrict_pairRestrict (nearestNeighbor Z₀)
  have hf0 := pairRestrict_ne_of_nearestNeighbor (Z := Z₀) rfl
  have hnt : Nontrivial (Fin N ⊕ Fin N) :=
    ⟨⟨Sum.inl ⟨0, hNpos⟩, Sum.inr ⟨0, hNpos⟩, Sum.inl_ne_inr⟩⟩
  -- `m = 1`: one isolated pair, which is the long one
  by_cases hm1 : m = 1
  · have hT0 : twiceIsolatedSet hN Z₀ = ∅ :=
      twiceIsolatedSet_eq_empty_of_numIsolatedPairs_le_one hN (by omega)
    have hp0 : p = 0 := by
      have h := card_twiceIsolatedSet (hN := hN) (Z := Z₀)
      rw [hT0, hp] at h
      simp at h
      omega
    have hp₀0 : p₀ = 0 := by omega
    have hL1 : p₀' = 1 := by omega
    obtain ⟨i₀, hi₀⟩ : L.Nonempty := Finset.card_pos.1 (by omega)
    have hi₀pv : i₀ ∈ pairVerts (nearestNeighbor Z₀) := (mem_neutralReps.1 (hLsub hi₀)).1
    have : Nontrivial {i // i ∈ pairVerts (nearestNeighbor Z₀)} :=
      Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    have : Nontrivial {i // i ∉ pairVerts (nearestNeighbor Z₀)} :=
      Fintype.one_lt_card_iff_nontrivial.1 (by
        rw [card_compl_pairVerts_subtype rfl]; omega)
    set j₀ : {i // i ∈ pairVerts (nearestNeighbor Z₀)} := ⟨i₀, hi₀pv⟩ with hj₀
    set E₁ : Set ({i // i ∈ pairVerts (nearestNeighbor Z₀)} → ℂ) :=
      {x | Rl < ‖x (pairRestrict (nearestNeighbor Z₀) j₀) - x j₀‖} with hE₁
    have hE₁m : MeasurableSet E₁ := measurableSet_lt measurable_const (by fun_prop)
    have hE : ∀ Z ∈ E, (fun j : {i // i ∈ pairVerts (nearestNeighbor Z₀)} => Z j) ∈ E₁ :=
      fun Z hZ => hZ i₀ hi₀
    have hcell := lintegral_markedCell_le_mul_event hN hβ0 (T := twiceIsolatedSet hN Z₀)
      (c := Cc * ((N : ℝ) - numComponents Z₀))
      (nnEnergy (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) lam)
      (measurable_nnEnergy _ lam)
      (fun Z hZc hZΛ => by
        have h := le_energy_split_of_empty hCc hN hlam hZΛ hZc.1 hZc.2.1
          ((hT2 Z hZc).trans hT0)
        rwa [hK2 Z hZc] at h)
      E E₁ hE₁m hE
    have hI₁ := lintegral_pair_long_le hβ (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀))
      (sumKey N)) (by rw [hcardI, hm1]) hf0 hf2 j₀ N hlam hRl
    have hY₂ := @hF2c inferInstance
    set c₁' : ℝ := Real.log N + Real.log (dipoleConstant β hβ.le) + (2 - β) * Real.log lam +
      Real.log α with hc₁'
    have hI₁' : ENNReal.ofReal (Real.exp 0) *
        ∫⁻ x in (Set.univ.pi fun _ : {i // i ∈ pairVerts (nearestNeighbor Z₀)} => box N) ∩
            ({x | nnMap (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) x =
              pairRestrict (nearestNeighbor Z₀)} ∩ E₁),
            ENNReal.ofReal (Real.exp (-β *
              nnEnergy (subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N)) lam x)) ≤
        ENNReal.ofReal (Real.exp c₁') := by
      rw [Real.exp_zero, ENNReal.ofReal_one, one_mul]
      refine hI₁.trans (le_of_eq ?_)
      congr 1
      rw [hα, hc₁', Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hN0,
        Real.exp_log hZ, Real.exp_log hα0, mul_comm (2 - β), ← Real.rpow_def_of_pos hlam]
      ring
    refine Or.inl (le_ofReal_exp_of_le_mul hcell hI₁' hY₂ ?_)
    have e1 : (p : ℝ) = 0 := by exact_mod_cast hp0
    have e2 : (p₀ : ℝ) = 0 := by exact_mod_cast hp₀0
    have e3 : (p₀' : ℝ) = 1 := by exact_mod_cast hL1
    have e4 : ((numIsolatedPairs Z₀ : ℕ) : ℝ) = 1 := by exact_mod_cast hm1
    rw [e1, e2, e3, e4, hlogMα]
    have h3 : c₁ * (0 : ℝ) ^ 2 / N = 0 := by simp
    have h1 : 0 ≤ (C₁ + C₂ + |Lz|) * N * ω lam := by
      rw [mul_assoc]; exact mul_nonneg hCb hNω
    have h2 : 0 ≤ (C₁ + C₂ + |Lz|) * Real.log (N + 1) := mul_nonneg hCb hlogN
    have h4 : 0 ≤ 18 * β * Cc := by positivity
    simp only [mul_zero, Real.log_zero, sub_self]
    rw [← hLz]
    linarith
  have hm2 : 2 ≤ m := by
    have : 1 ≤ m := by omega
    omega
  have hmN : m ≤ N := hmK.trans hKN
  have h3 : 3 ≤ Fintype.card {i // i ∈ pairVerts (nearestNeighbor Z₀)} := by omega
  have : Nontrivial {i // i ∈ pairVerts (nearestNeighbor Z₀)} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hScard : (markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)).card =
      2 * (m - (p₀ + m - p)) := by
    rw [card_markedSameSignIn (hN := hN) rfl rfl, hp, hp₀]
    congr 1
    omega
  have hSinv : ∀ i, pairRestrict (nearestNeighbor Z₀) i ∈
      markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) ↔
        i ∈ markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) := by
    intro i
    refine ⟨fun h => ?_, fun h => pairRestrict_mem_markedSameSignIn rfl rfl h⟩
    have := pairRestrict_mem_markedSameSignIn (hN := hN) rfl rfl h
    rwa [pairRestrict_pairRestrict] at this
  have hp₀' : p₀ + m - p + p = p₀ + m := by omega
  have hLneg : ∀ i ∈ L, charge i * charge (nearestNeighbor Z₀ i) = -1 := fun i hi =>
    (mem_neutralReps.1 (hLsub hi)).2.1
  -- the error rate of Proposition 3.9 (`exists_anchor_conv`)
  have hr' := hω.isolated_le lam hlam hlam1
  have hr0' : 0 ≤ (if β < 4 then lam ^ (β - 2) else if β = 4 then lam ^ 2 * |Real.log lam| ^ 2
      else lam ^ 2 * |Real.log lam|) := by
    split_ifs
    · exact (Real.rpow_pos_of_pos hlam _).le
    · positivity
    · positivity
  by_cases hmN' : m = N
  · -- `Iᶜ = ∅`: all points are in isolated pairs
    have hKeq : numComponents Z₀ = N := by omega
    have h3' : 3 ≤ Fintype.card (Fin N ⊕ Fin N) := by simp; omega
    have huniv : pairVerts (nearestNeighbor Z₀) = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      rw [hcardPV]
      simp
      omega
    have hφ2 : ∀ i, nearestNeighbor Z₀ (nearestNeighbor Z₀ i) = i := fun i =>
      (mem_pairVerts.1 (huniv ▸ Finset.mem_univ i)).1
    have hφ0 : ∀ i, nearestNeighbor Z₀ i ≠ i := nearestNeighbor_ne Z₀
    have hSinv' : ∀ i, nearestNeighbor Z₀ i ∈
        markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) ↔
          i ∈ markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) := by
      intro i
      simp only [mem_markedSameSign]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' := nearestNeighbor_mem_twiceIsolatedSet h1
        rw [hφ2] at h1' h2
        exact ⟨h1', by rwa [mul_comm] at h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨nearestNeighbor_mem_twiceIsolatedSet h1, ?_⟩
        rwa [hφ2, mul_comm]
    have hScard' : (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)).card =
        2 * (N - (p₀ + N - p)) := by
      rw [card_markedSameSign hN Z₀, hp, hp₀]
      congr 1
      omega
    set R : Set (Fin N ⊕ Fin N) := gpRefSet (sumKey N) (nearestNeighbor Z₀) with hRdef
    have hRf : ∀ i, i ∈ R ↔ nearestNeighbor Z₀ i ∉ R := gpRefSet_mem_iff hφ2 hφ0
    have hcardR : Fintype.card {i // i ∈ R} = N := by
      have := IsolatedReduction.two_mul_card_ref hφ2 hRf
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      omega
    have : Nontrivial {i // i ∈ R} := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    set Ls : Finset {i // i ∈ R} := Finset.univ.filter fun j => (j : Fin N ⊕ Fin N) ∈ L
      with hLs
    have hLsc : Ls.card = p₀' := by
      rw [← hLc]
      exact card_filter_gpRefSet_eq (fun x => x) (fun _ _ h => h) (nearestNeighbor Z₀)
        (fun _ => rfl) (sumKey N) (fun _ => rfl) hLsub (fun i _ => ⟨i, rfl⟩)
    have hLS : ∀ j ∈ Ls, (j : Fin N ⊕ Fin N) ∉
        markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) := by
      intro j hj h
      exact (mem_markedSameSign.1 h).2 (hLneg _ (mem_filter.1 hj).2)
    set E' : Set (Fin N ⊕ Fin N → ℂ) :=
      {z | ∀ j ∈ Ls, Rl < ‖z (nearestNeighbor Z₀ j) - z j‖} with hE'
    have hE'm : MeasurableSet E' := by
      have : E' = ⋂ j ∈ Ls, {z : Fin N ⊕ Fin N → ℂ | Rl < ‖z (nearestNeighbor Z₀ j) - z j‖} := by
        ext z; simp [hE']
      rw [this]
      exact Finset.measurableSet_biInter _ fun j _ =>
        measurableSet_lt measurable_const (by fun_prop)
    have hEE' : E ⊆ E' := fun Z hZ j hj => hZ _ (mem_filter.1 hj).2
    have hcell := lintegral_markedCell_le_event hN hβ0 (T := twiceIsolatedSet hN Z₀)
      (c := Cc * ((N : ℝ) - numComponents Z₀))
      (pairAssignedEnergy h3' (sumKey N) lam Cc
        (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)))
      (fun Z hZc hZΛ => by
        have h := le_energy_full hCc0.le hCc hN h3' hlam hZΛ hZc.1 hZc.2.1 hZc.2.2
        rwa [hK2 Z hZc] at h)
      E E' hE'm hEE'
    rw [lintegral_ofReal_exp_neg_mul volume _ β (pairAssignedEnergy h3' (sumKey N) lam Cc
      (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)))] at hcell
    have hP := hpred (Fin N ⊕ Fin N) (sumKey N) (nearestNeighbor Z₀) R hφ2 hRf h3'
      (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) hSinv' Ls hLS N lam Rl α
      hlam hlam1 hRl (le_of_eq hα)
    rw [hcardR, hLsc] at hP
    have hA := hconvA (Fin N ⊕ Fin N) (nearestNeighbor Z₀) R hφ2 hRf
      (markedSameSign (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀)) hSinv' N N (p₀ + N - p)
      hcardR (by omega) le_rfl (by linarith) (by omega) hScard' lam hlam hlam1
    have hY := ofReal_exp_mul_le_of_long hMα hP hA
    have hF1 := entropy_mul_le_main_rate hβ ω (X := p₀' * Real.log (Real.exp (18 * β * Cc) * α))
      hc₁.le hC₁.le
      (N := N) (m := N) (p := p) (p₀ := p₀) (p₀' := p₀ + N - p) hNpos le_rfl hp₀p
      (hmN' ▸ hpm) (by omega) hr0' hr' hY
    refine Or.inl (le_ofReal_exp_of_le_mul_one hcell hF1 ?_)
    rw [hKeq]
    have h1 : C₁ * N * ω lam ≤
        (C₁ + C₂ + |Lz|) * N * ω lam := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Lz]) hNω
    have h2 : C₁ * Real.log (N + 1) ≤ (C₁ + C₂ + |Lz|) * Real.log (N + 1) :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Lz]) hlogN
    rw [← hLz]
    linarith
  -- `m < N`: the separation (gred3) with the event on `I`
  have : Nontrivial {i // i ∉ pairVerts (nearestNeighbor Z₀)} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by
      rw [card_compl_pairVerts_subtype rfl]; omega)
  set f := pairRestrict (nearestNeighbor Z₀) with hfdef
  set keyI := subtypeKey (· ∈ pairVerts (nearestNeighbor Z₀)) (sumKey N) with hkeyI
  set S := markedSameSignIn (nearestNeighbor Z₀) (twiceIsolatedSet hN Z₀) with hSdef
  set R : Set {i // i ∈ pairVerts (nearestNeighbor Z₀)} := gpRefSet keyI f with hRdef
  have hRf : ∀ i, i ∈ R ↔ f i ∉ R := gpRefSet_mem_iff hf2 hf0
  have hcardR : Fintype.card {i // i ∈ R} = m := by
    have := IsolatedReduction.two_mul_card_ref hf2 hRf
    omega
  have : Nontrivial {i // i ∈ R} := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  set Ls : Finset {i // i ∈ R} :=
    Finset.univ.filter fun j => ((j : {i // i ∈ pairVerts (nearestNeighbor Z₀)}) :
      Fin N ⊕ Fin N) ∈ L with hLs
  have hLsc : Ls.card = p₀' := by
    rw [← hLc]
    exact card_filter_gpRefSet_eq
      (fun x : {i // i ∈ pairVerts (nearestNeighbor Z₀)} => (x : Fin N ⊕ Fin N))
      Subtype.val_injective f
      (fun _ => rfl) keyI (fun _ => rfl) hLsub
      (fun i hi => ⟨⟨i, (mem_neutralReps.1 (hLsub hi)).1⟩, rfl⟩)
  have hLS : ∀ j ∈ Ls, ((j : {i // i ∈ pairVerts (nearestNeighbor Z₀)})) ∉ S := by
    intro j hj h
    exact (mem_markedSameSignIn.1 h).2 (hLneg _ (mem_filter.1 hj).2)
  set E₁ : Set ({i // i ∈ pairVerts (nearestNeighbor Z₀)} → ℂ) :=
    {x | ∀ j ∈ Ls, Rl < ‖x (f j) - x j‖} with hE₁
  have hE₁m : MeasurableSet E₁ := by
    have : E₁ = ⋂ j ∈ Ls,
        {x : {i // i ∈ pairVerts (nearestNeighbor Z₀)} → ℂ | Rl < ‖x (f j) - x j‖} := by
      ext x; simp [hE₁]
    rw [this]
    exact Finset.measurableSet_biInter _ fun j _ =>
      measurableSet_lt measurable_const (by fun_prop)
  have hE : ∀ Z ∈ E, (fun j : {i // i ∈ pairVerts (nearestNeighbor Z₀)} => Z j) ∈ E₁ :=
    fun Z hZ j hj => hZ _ (mem_filter.1 hj).2
  have hcell := lintegral_markedCell_le_mul_event hN hβ0 (T := twiceIsolatedSet hN Z₀)
    (c := Cc * ((N : ℝ) - numComponents Z₀))
    (pairAssignedEnergy h3 keyI lam Cc S) (measurable_pairAssignedEnergy _ h3 lam Cc S)
    (fun Z hZc hZΛ => by
      have h := le_energy_split hCc0.le hCc hN hlam hZΛ hZc.1 hZc.2.1 hZc.2.2 h3
      rwa [hK2 Z hZc] at h)
    E E₁ hE₁m hE
  rw [← Set.inter_assoc, lintegral_ofReal_exp_neg_mul volume _ β
    (pairAssignedEnergy h3 keyI lam Cc S)] at hcell
  have hP := hpred {i // i ∈ pairVerts (nearestNeighbor Z₀)} keyI f R hf2 hRf h3 S hSinv Ls hLS
    N lam Rl α hlam hlam1 hRl (le_of_eq hα)
  rw [hcardR, hLsc] at hP
  have hY₂ := @hF2c inferInstance
  by_cases hNm : (N : ℝ) ≤ 2 * m
  · have hA := hconvA {i // i ∈ pairVerts (nearestNeighbor Z₀)} f R hf2 hRf S hSinv N m
      (p₀ + m - p) hcardR hm2 hmN hNm (by omega) hScard lam hlam hlam1
    have hY := ofReal_exp_mul_le_of_long hMα hP hA
    have hF1 := entropy_mul_le_main_rate hβ ω (X := p₀' * Real.log (Real.exp (18 * β * Cc) * α))
      hc₁.le hC₁.le
      (N := N) (m := m) (p := p) (p₀ := p₀) (p₀' := p₀ + m - p) (by omega) hmN hp₀p hpm hp₀'
      hr0' hr' hY
    refine Or.inl (le_ofReal_exp_of_le_mul hcell hF1 hY₂ ?_)
    have h1 : C₁ * N * ω lam ≤
        (C₁ + C₂ + |Lz|) * N * ω lam := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Lz]) hNω
    have h2 : C₁ * Real.log (N + 1) ≤ (C₁ + C₂ + |Lz|) * Real.log (N + 1) :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Lz]) hlogN
    have hmr : (m : ℝ) = numIsolatedPairs Z₀ := rfl
    rw [← hLz, ← hmr]
    linarith
  · replace hNm := not_le.1 hNm
    have hA := hcrudeA {i // i ∈ pairVerts (nearestNeighbor Z₀)} R S N m (p₀ + m - p) hcardR
      hmN (by omega) lam hlam hlam1
    have hY := ofReal_exp_mul_le_of_long hMα hP hA
    have hF1 := entropy_mul_le_crude (m := m) (p := p) (p₀ := p₀) (p₀' := p₀ + m - p) hp₀p hpm hp₀' hY
    have hpN : (p : ℝ) < N / 2 := by
      have : (p : ℝ) ≤ m := by exact_mod_cast hpm
      linarith
    refine Or.inr ⟨hpN, le_ofReal_exp_of_le_mul hcell hF1 hY₂ ?_⟩
    have hmN'' : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have h1 : -((m : ℝ) * Lz) ≤ |Lz| * N := by
      have := neg_abs_le Lz
      have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have e1 := mul_le_mul_of_nonneg_left (neg_le_abs Lz) h0
      have e2 := mul_le_mul_of_nonneg_left hmN'' (abs_nonneg Lz)
      linarith only [e1, e2]
    have hmr : (m : ℝ) = numIsolatedPairs Z₀ := rfl
    rw [← hLz, ← hmr]
    have h2 := mul_pos hC₁ hN0
    linarith

end Cell

/-! ### (eq:claim F(1)) and (eq:u bound) (source l. 1652--1663) -/

section Main

open UpperCellBound UpperAssembly

/-- **(eq:claim F(1))** (source l. 1658--1663): for `1 ≤ k ≤ N`, `M ≥ 1`, `α > 0` and
`x₀ = k/N ≥ (e M)² α`, `log C(N, k) + k log (M α) ≤ -½ N x₀ log (x₀/α)`. -/
theorem log_choose_add_le {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) {M α : ℝ} (hM : 1 ≤ M)
    (hα : 0 < α) (hx : (Real.exp 1 * M) ^ 2 * α ≤ (k : ℝ) / N) :
    Real.log (N.choose k) + k * Real.log (M * α) ≤
      -(1 / 2) * N * ((k : ℝ) / N) * Real.log (((k : ℝ) / N) / α) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM0 : 0 < M := by linarith
  have hx0 : 0 < (k : ℝ) / N := div_pos hk0 hN0
  -- `log C(N, k) ≤ k log N - k log k + k`
  have hC0 : (0 : ℝ) < N.choose k := by exact_mod_cast Nat.choose_pos hkN
  have hch : ((N.choose k : ℕ) : ℝ) ≤ (N : ℝ) ^ k / (k.factorial : ℝ) := Nat.choose_le_pow_div k N
  have hf0 : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hlogC : Real.log (N.choose k) ≤ k * Real.log N - (k * Real.log k - k) := by
    have h1 : Real.log (N.choose k) ≤ Real.log ((N : ℝ) ^ k / (k.factorial : ℝ)) :=
      Real.log_le_log hC0 hch
    rw [Real.log_div (by positivity) hf0.ne', Real.log_pow] at h1
    have h2 := mul_log_sub_le_log_factorial k
    linarith
  -- `x₀/α ≥ (e M)²`
  have hlx : 2 * (1 + Real.log M) ≤ Real.log (((k : ℝ) / N) / α) := by
    have h1 : (Real.exp 1 * M) ^ 2 ≤ ((k : ℝ) / N) / α := by rw [le_div_iff₀ hα]; exact hx
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_mul (Real.exp_pos 1).ne' hM0.ne', Real.log_exp] at h2
    push_cast at h2
    linarith
  have e1 : Real.log (((k : ℝ) / N) / α) = Real.log k - Real.log N - Real.log α := by
    rw [Real.log_div hx0.ne' hα.ne', Real.log_div hk0.ne' hN0.ne']
  have e2 : Real.log (M * α) = Real.log M + Real.log α := Real.log_mul hM0.ne' hα.ne'
  have e3 : -(1 / 2) * (N : ℝ) * ((k : ℝ) / N) * Real.log (((k : ℝ) / N) / α) =
      -(1 / 2) * k * Real.log (((k : ℝ) / N) / α) := by
    field_simp
  rw [e3, e2]
  rw [e1] at hlx ⊢
  have hp := mul_le_mul_of_nonneg_left hlx hk0.le
  linarith only [hlogC, hp]

/-- **(eq:A') and (eq:u bound) for `β > 2`, generic rate** (`prop:upper bound`, eq:u bound,
source l. 1440--1445, proof l. 1643--1664), for a rate `ω` satisfying `UpperRateHyp` in place of
`ω_λ`; the constants and the threshold depend only on `β` and `ω`. Instantiated at `errorRate` in
`proposition_3_10_long_of_two_lt` (`UpperBound/UpperRate.lean`). -/
theorem proposition_3_10_long_of_two_lt_rate {β : ℝ} (hβ : 2 < β) (ω : ℝ → ℝ)
    (hω : UpperRateHyp β hβ ω) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
        ∀ N : ℕ, 2 ≤ N → ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∀ R : ℝ, 2 * lam ≤ R → ∀ p₀' : ℕ, 1 ≤ p₀' → p₀' ≤ N →
          C₁ * (2 * Real.pi / dipoleConstant β hβ.le *
              ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r) ≤ (p₀' : ℝ) / N →
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
              {Z | p₀' ≤ (longIsolatedDipoles Z R).card},
              ENNReal.ofReal (Real.exp (-β * energy lam Z))
            ≤ ENNReal.ofReal (Real.exp (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1)
                - c * N * ((p₀' : ℝ) / N) * Real.log (((p₀' : ℝ) / N) /
                    (2 * Real.pi / dipoleConstant β hβ.le *
                      ∫ r in Set.Ici (R / lam), Real.exp (β * smearedKernel 1 r) * r))
                + C₂ * N * ω lam + C₂ * Real.log (N + 1))) := by
  classical
  obtain ⟨A, c, Cb, Cm, hc, hCb, hCm, hcellL⟩ := exists_cellBound_long_rate hβ ω hω
  obtain ⟨c', C', lam₀, hc', hC', hlam₀, hlam₀1, hgraph⟩ :=
    exists_card_mul_le_of_cellBound_rate hβ ω hω A c Cb hc hCb
  refine ⟨lam₀, hlam₀, 1 / 2, (Real.exp 1 * Real.exp Cm) ^ 2, C' + 3, by norm_num,
    by positivity, by linarith, ?_⟩
  intro N hN lam hlam hlamlt Rl hRl p₀' hp1 hpN hx
  have hlam1 : lam ≤ Real.exp (-1) := hlamlt.le.trans hlam₀1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set α : ℝ := 2 * Real.pi / dipoleConstant β hβ.le *
    ∫ r in Set.Ici (Rl / lam), Real.exp (β * smearedKernel 1 r) * r with hαdef
  have hα := tail_eq_mul_alpha hβ hlam hRl
  rw [← hαdef] at hα
  have hα0 : 0 < α := alpha_pos hβ hlam hRl
  set X : ℝ := p₀' * Real.log (Real.exp Cm * α) with hX
  set Y : ℝ := 2 * N * Real.log N
    + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant β hβ.le) - 1)
    + C' * N * ω lam + C' * Real.log (N + 1) with hY
  have hω0 : 0 ≤ ω lam := hω.nonneg lam hlam
  have hchoose : (1 : ℝ) ≤ N.choose p₀' := by exact_mod_cast Nat.choose_pos hpN
  -- one marked graph: the sum over the choices of the long pairs (l. 1651)
  have hcell : ∀ (K p p₀ : ℕ) (φ : Fin N ⊕ Fin N → Fin N ⊕ Fin N) (T : Finset (Fin N ⊕ Fin N)),
      (φ, T) ∈ markedGraphs hN K p p₀ →
        ((markedGraphs hN K p p₀).card : ℝ≥0∞) *
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
              {Z | p₀' ≤ (longIsolatedDipoles Z Rl).card} ∩ markedCell hN φ T,
            ENNReal.ofReal (Real.exp (-β * energy lam Z)) ≤
          ENNReal.ofReal (Real.exp (Y + X + Real.log (N.choose p₀'))) := by
    intro K p p₀ φ T hγ
    have hsub : {Z | p₀' ≤ (longIsolatedDipoles Z Rl).card} ∩ markedCell hN φ T ⊆
        ⋃ L ∈ (neutralReps φ).powersetCard p₀', {Z | ∀ i ∈ L, Rl < ‖Z (φ i) - Z i‖} :=
      subset_iUnion_long hN Rl p₀'
    have hsum : ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
          {Z | p₀' ≤ (longIsolatedDipoles Z Rl).card} ∩ markedCell hN φ T,
          ENNReal.ofReal (Real.exp (-β * energy lam Z)) ≤
        ∑ L ∈ (neutralReps φ).powersetCard p₀',
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
              {Z | ∀ i ∈ L, Rl < ‖Z (φ i) - Z i‖} ∩ markedCell hN φ T,
            ENNReal.ofReal (Real.exp (-β * energy lam Z)) :=
      setLIntegral_le_sum_of_subset (α := Fin N ⊕ Fin N → ℂ) (κ := Finset (Fin N ⊕ Fin N))
        (μ := volume) ((neutralReps φ).powersetCard p₀')
        (fun L => {Z | ∀ i ∈ L, Rl < ‖Z (φ i) - Z i‖}) (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N)
        {Z | p₀' ≤ (longIsolatedDipoles Z Rl).card} (markedCell hN φ T) hsub
        (fun Z => ENNReal.ofReal (Real.exp (-β * energy lam Z)))
    have hterm : ∀ L ∈ (neutralReps φ).powersetCard p₀',
        ((markedGraphs hN K p p₀).card : ℝ≥0∞) *
          ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
              {Z | ∀ i ∈ L, Rl < ‖Z (φ i) - Z i‖} ∩ markedCell hN φ T,
            ENNReal.ofReal (Real.exp (-β * energy lam Z)) ≤
          ENNReal.ofReal (Real.exp (Y + X)) := by
      intro L hL
      refine (hgraph N hN K p p₀ lam hlam hlamlt ⟨_, hγ⟩ X _
        (hcellL N hN lam Rl α hlam hlam1 hRl hα K p p₀ φ T hγ p₀' hp1 L hL)).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
      have : 0 ≤ c' * ((N : ℝ) - p₀) ^ 2 / N := by positivity
      rw [hY]
      linarith
    have hcard : (((neutralReps φ).powersetCard p₀').card : ℝ≥0∞) ≤ (N.choose p₀' : ℝ≥0∞) := by
      rw [Finset.card_powersetCard]
      exact_mod_cast Nat.choose_le_choose p₀' (card_neutralReps_le φ)
    calc _ ≤ ((markedGraphs hN K p p₀).card : ℝ≥0∞) *
          ∑ L ∈ (neutralReps φ).powersetCard p₀',
            ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
                {Z | ∀ i ∈ L, Rl < ‖Z (φ i) - Z i‖} ∩ markedCell hN φ T,
              ENNReal.ofReal (Real.exp (-β * energy lam Z)) := mul_le_mul_right hsum _
      _ = ∑ L ∈ (neutralReps φ).powersetCard p₀', ((markedGraphs hN K p p₀).card : ℝ≥0∞) *
            ∫⁻ Z in (Set.univ.pi fun _ : Fin N ⊕ Fin N => box N) ∩
                {Z | ∀ i ∈ L, Rl < ‖Z (φ i) - Z i‖} ∩ markedCell hN φ T,
              ENNReal.ofReal (Real.exp (-β * energy lam Z)) := Finset.mul_sum _ _ _
      _ ≤ ((neutralReps φ).powersetCard p₀').card • ENNReal.ofReal (Real.exp (Y + X)) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ (N.choose p₀' : ℝ≥0∞) * ENNReal.ofReal (Real.exp (Y + X)) := by
          rw [nsmul_eq_mul]
          exact mul_le_mul_left hcard _
      _ = _ := by
          rw [Real.exp_add (Y + X) (Real.log (N.choose p₀' : ℝ)), Real.exp_log (by linarith),
            ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm, ENNReal.ofReal_natCast]
  -- the sum over the graphs (l. 1622, 1652--1657: (eq:A'))
  have hA' := UpperAssembly.lintegral_le_of_card_mul_le hN
    {Z | p₀' ≤ (longIsolatedDipoles Z Rl).card}
    (fun Z => ENNReal.ofReal (Real.exp (-β * energy lam Z))) _ hcell
  rw [natCast_add_one_pow_mul_ofReal_exp] at hA'
  refine hA'.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  -- (eq:claim F(1))
  have hclaim := log_choose_add_le hp1 hpN (M := Real.exp Cm) (Real.one_le_exp hCm) hα0
    (by rw [mul_pow, mul_assoc]; exact (le_of_eq (by ring)).trans hx)
  have hlogN : 0 ≤ Real.log (N + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  have h1 : C' * N * ω lam ≤ (C' + 3) * N * ω lam := by
    have := mul_nonneg hN0.le hω0
    linarith only [this]
  rw [hY, hX]
  linarith

end Main

end LongDipoles

end TwoComponentCoulomb

end
