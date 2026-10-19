/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.Integrals.Dirichlet
public import TwoComponentCoulomb.PhaseSpace.RadialSimplex
public import TwoComponentCoulomb.UpperBound.NearestNeighborModel
import TwoComponentCoulomb.Integrals.Radial
import TwoComponentCoulomb.Potential.DiscPotentialMeasure
import TwoComponentCoulomb.Potential.PairIntegral
import TwoComponentCoulomb.Potential.SmearedKernel

/-!
# The nearest-neighbour model: the tree integrals and the cases `β ∈ (2,4)` and `β > 4`

Source: l. 884--914 (Lemma 3.5, Step 4) and l. 858--865 (Step 3, `β > 2`).
The reduction of `NearestNeighborModel.lean` leaves the integrals, over the balls
`|U|² ≤ 36N/π` of `ℂ^K` and `ℂ^{2p-2K}`, of the weights `exp (β g_λ (u_k))` (cycles) and
`exp ((β/2) g_λ (u_i))` (tree vertices).

* `exists_smearedKernel_le_neg_log`: `g_λ(z) ≤ g(z) + C` for `z ≠ 0` (eq. (approxgeta)).
* `exists_lintegral_ball_tree_le`: for `β ∈ [2,4)`, the tree integral is at most
  `exp ((1 - β/4) (2q) log (N/q) + C q)`, `q = p - K` (source (eq:reD) and (eq:bound dir)); the
  proof removes the cutoff, goes to polar coordinates and uses the Dirichlet estimate of Lemma 3.1.
* `exists_lintegral_ball_tree_le_of_four_lt`: for `β > 4`, the tree integral is at most
  `exp ((2q)(2 - β/2) log λ + C q)` (source l. 911--914, "Arguing as in (3.20b)").
* `natCast_pow_mul_le`, `lintegral_cell_eq_zero_of_not_exists`, `dipoleConstant_mul_rpow_pow`:
  the arithmetic of the final assembly and the empty cell.
* `lintegral_cell_le_of_two_lt_of_lt_four`, `lintegral_cell_le_of_four_lt`: the cases `β ∈ (2,4)`
  and `β > 4` of Lemma 3.5, in the form `J(f) ≤ exp (RHS)` with `RHS` as in the source (l. 793--797,
  805--809); the constant depends only on `β`, and the bounds hold for every `λ > 0`.

The cases `β = 2` and `β = 4` (the critical weight `exp (2 g_λ)`) and the combined statement for
`β > 2` are in `NearestNeighborModelCritical.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TwoComponentCoulomb

/-! ### Comparison of `g_λ` with the logarithm -/

/-- Source eq. (approxgeta): `g_λ(z) ≤ g(z) + C` for `z ≠ 0`, uniformly in `λ > 0`. -/
theorem exists_smearedKernel_le_neg_log :
    ∃ C : ℝ, ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, z ≠ 0 → smearedKernel lam z ≤ -Real.log ‖z‖ + C := by
  obtain ⟨C, hC⟩ := exists_abs_smearedKernel_sub_logKernel_le
  refine ⟨C, fun lam hlam z hz => ?_⟩
  have h1 := (abs_le.1 (hC lam hlam z)).2
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [logKernel_ofReal (lt_of_lt_of_le hz0 (le_max_left _ _))] at h1
  have h2 : Real.log ‖z‖ ≤ Real.log (max ‖z‖ lam) := Real.log_le_log hz0 (le_max_left _ _)
  linarith

/-- The pointwise bound of the tree weight (source l. 884--887): for `t > 0`,
`exp (γ g_λ(√t)) ≤ exp (γ C) t^{-γ/2}`. -/
theorem exp_mul_smearedKernel_sqrt_le {C : ℝ}
    (hC : ∀ lam : ℝ, 0 < lam → ∀ z : ℂ, z ≠ 0 → smearedKernel lam z ≤ -Real.log ‖z‖ + C)
    {γ lam t : ℝ} (hγ : 0 ≤ γ) (hlam : 0 < lam) (ht : 0 < t) :
    Real.exp (γ * smearedKernel lam ((Real.sqrt t : ℝ) : ℂ)) ≤
      Real.exp (γ * C) * t ^ (-(γ / 2)) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hne : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have h1 := hC lam hlam _ hne
  rw [Complex.norm_real, Real.norm_of_nonneg hs.le, Real.log_sqrt ht.le] at h1
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left h1 hγ
  linarith only [this]

/-! ### The tree integral for `β ∈ [2, 4)` -/

/-- A ball integral over an empty family of variables is at most `1`. -/
theorem lintegral_ball_prod_le_one_of_eq_zero {m : ℕ} (hm : m = 0) (s : ℝ) (G : ℂ → ℝ≥0∞) :
    ∫⁻ v in {v : Fin m → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s}, ∏ i, G (v i) ≤ 1 := by
  subst hm
  calc ∫⁻ v in {v : Fin 0 → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s}, ∏ i, G (v i)
      ≤ ∫⁻ v : Fin 0 → ℂ, ∏ i, G (v i) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ v : Fin 0 → ℂ, 1 := by simp
    _ = 1 := by
      rw [lintegral_const, one_mul, volume_pi, Measure.pi_univ]
      simp

/-- **Source (eq:reD) and (eq:bound dir)** (l. 884--903): for `β ∈ [2,4)` the integral of the
tree weights over the ball `|U|² ≤ 36N/π` of `ℂ^{2q}` is at most
`exp ((1 - β/4)(2q) log (N/q) + C q)` (here `q = p - K`; the weight is first compared with
`|u|^{-β/2}`, then polar coordinates and the Dirichlet estimate of Lemma 3.1 are used). -/
theorem exists_lintegral_ball_tree_le {β : ℝ} (hβ2 : 2 ≤ β) (hβ4 : β < 4) :
    ∃ C : ℝ, ∀ (N q m : ℕ), 0 < N → m = 2 * q → ∀ lam : ℝ, 0 < lam →
      ∫⁻ v in {v : Fin m → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ 36 * N / Real.pi},
          ∏ i, ENNReal.ofReal (Real.exp ((β / 2) * smearedKernel lam (v i))) ≤
        ENNReal.ofReal (Real.exp ((1 - β / 4) * (2 * q) * Real.log (N / q) + C * q)) := by
  obtain ⟨c, hc⟩ := exists_smearedKernel_le_neg_log
  have hα : 0 < 1 - β / 4 := by linarith
  obtain ⟨Cα, hCα⟩ := dirichletTwoLevel_log_estimate hα
  set α : ℝ := 1 - β / 4 with hαdef
  refine ⟨2 * |Real.log Real.pi| + |β * c| +
    2 * |α * (Real.log 36 - Real.log Real.pi - Real.log α - Real.log 2)| + 2 + 4 * |Cα|,
    fun N q m hN hmq' lam hlam => ?_⟩
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine (lintegral_ball_prod_le_one_of_eq_zero (m := m) (by omega) _
      (fun v => ENNReal.ofReal (Real.exp ((β / 2) * smearedKernel lam v)))).trans ?_
    simp
  have hx : (0 : ℝ) < q := by exact_mod_cast hq
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm1 : 1 ≤ m := by omega
  have hmq : (m : ℝ) = 2 * q := by rw [hmq']; push_cast; ring
  set s : ℝ := 36 * N / Real.pi with hsdef
  have hs : 0 < s := by positivity
  set gr : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp ((β / 2) * smearedKernel lam (r : ℂ)))
    with hgr
  have hgrm : Measurable gr := by
    have : Measurable fun r : ℝ => smearedKernel lam (r : ℂ) :=
      (measurable_smearedKernel lam).comp Complex.measurable_ofReal
    rw [hgr]
    fun_prop
  -- polar coordinates
  have hpolar : ∫⁻ v in {v : Fin m → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s},
      ∏ i, ENNReal.ofReal (Real.exp ((β / 2) * smearedKernel lam (v i))) =
        ENNReal.ofReal Real.pi ^ m * ∫⁻ t in posSimplex m s, ∏ i, gr (Real.sqrt (t i)) := by
    rw [← lintegral_ball_prod_radial_eq_posSimplex hs (fun _ : Fin m => gr) (fun _ => hgrm)]
    refine lintegral_congr fun v => ?_
    simp only [hgr, ← smearedKernel_eq_norm]
  -- comparison with the unregularised weight
  have hpt : ∀ t ∈ posSimplex m s, ∏ i, gr (Real.sqrt (t i)) ≤
      ENNReal.ofReal (Real.exp (m * ((β / 2) * c))) *
        ENNReal.ofReal (∏ i, t i ^ (α - 1)) := by
    intro t ht
    have h1 : ∀ i, gr (Real.sqrt (t i)) ≤
        ENNReal.ofReal (Real.exp ((β / 2) * c) * t i ^ (α - 1)) := by
      intro i
      refine ENNReal.ofReal_le_ofReal ?_
      have := exp_mul_smearedKernel_sqrt_le hc (γ := β / 2) (by linarith) hlam (ht.1 i)
      have e : -(β / 2 / 2) = α - 1 := by rw [hαdef]; ring
      rw [e] at this
      exact this
    calc ∏ i, gr (Real.sqrt (t i))
        ≤ ∏ i, ENNReal.ofReal (Real.exp ((β / 2) * c) * t i ^ (α - 1)) :=
          Finset.prod_le_prod fun i _ => h1 i
      _ = ENNReal.ofReal (∏ i, (Real.exp ((β / 2) * c) * t i ^ (α - 1))) :=
          (ENNReal.ofReal_prod_of_nonneg fun i _ =>
            mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (ht.1 i).le _)).symm
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ENNReal.ofReal_mul (pow_nonneg (Real.exp_pos _).le _), ← Real.exp_nat_mul]
  -- the Dirichlet integral
  have hI : ∫⁻ t in posSimplex m s, ENNReal.ofReal (∏ i, t i ^ (α - 1)) =
      dirichletTwoLevel α m m s := by
    unfold dirichletTwoLevel
    refine lintegral_congr fun t => ?_
    rw [Finset.prod_congr rfl fun i _ => (by simp [i.2] :
      t i ^ (α - 1) = t i ^ ((if (i : ℕ) < m then α else 1) - 1))]
  have hIbound : dirichletTwoLevel α m m s ≤ ENNReal.ofReal (Real.exp
      ((α * m) * (Real.log s - Real.log (α * m)) + m + |Cα| * (m + Real.log (m + 1)))) := by
    have hpos := dirichletTwoLevel_pos hα hm1 le_rfl hs
    have hlt := dirichletTwoLevel_lt_top hα (le_refl m) hs
    have hlog := hCα m m hm1 le_rfl s hs
    simp only [sub_self, add_zero] at hlog
    rw [← ENNReal.ofReal_toReal hlt.ne]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_log (ENNReal.toReal_pos hpos.ne' hlt.ne)]
    refine Real.exp_le_exp.2 ?_
    have h2 := (abs_le.1 hlog).2
    have h3 : Cα * (m + Real.log (m + 1)) ≤ |Cα| * (m + Real.log (m + 1)) := by
      refine mul_le_mul_of_nonneg_right (le_abs_self _) ?_
      have : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by simp)
      positivity
    linarith
  -- assembling
  have hfin : (m : ℝ) * Real.log Real.pi + m * ((β / 2) * c) +
      ((α * m) * (Real.log s - Real.log (α * m)) + m + |Cα| * (m + Real.log (m + 1))) ≤
      (1 - β / 4) * (2 * q) * Real.log (N / q) +
        (2 * |Real.log Real.pi| + |β * c| +
          2 * |α * (Real.log 36 - Real.log Real.pi - Real.log α - Real.log 2)| + 2 + 4 * |Cα|) *
          q := by
    have e1 : Real.log s = Real.log 36 + Real.log N - Real.log Real.pi := by
      rw [hsdef, Real.log_div (by positivity) Real.pi_pos.ne',
        Real.log_mul (by norm_num) hN'.ne']
    have e2 : Real.log (α * m) = Real.log α + Real.log 2 + Real.log q := by
      rw [hmq, Real.log_mul hα.ne' (by positivity), Real.log_mul (by norm_num) hx.ne']
      ring
    have e3 : Real.log ((N : ℝ) / q) = Real.log N - Real.log q := Real.log_div hN'.ne' hx.ne'
    have hlogm : Real.log ((m : ℝ) + 1) ≤ m := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m + 1 by positivity)
      linarith
    have f1 : (q : ℝ) * Real.log Real.pi ≤ q * |Real.log Real.pi| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hx.le
    have f2 : (q : ℝ) * (β * c) ≤ q * |β * c| := mul_le_mul_of_nonneg_left (le_abs_self _) hx.le
    have f3 : (q : ℝ) * (α * (Real.log 36 - Real.log Real.pi - Real.log α - Real.log 2)) ≤
        q * |α * (Real.log 36 - Real.log Real.pi - Real.log α - Real.log 2)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hx.le
    have f4 : |Cα| * (m + Real.log ((m : ℝ) + 1)) ≤ |Cα| * (4 * q) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [hmq] at hlogm ⊢
      linarith
    have hexp : (m : ℝ) * Real.log Real.pi + m * ((β / 2) * c) +
        ((α * m) * (Real.log s - Real.log (α * m)) + m + |Cα| * (m + Real.log (m + 1))) =
        (1 - β / 4) * (2 * q) * Real.log (N / q) +
          ((q : ℝ) * (2 * Real.log Real.pi + β * c +
            2 * (α * (Real.log 36 - Real.log Real.pi - Real.log α - Real.log 2)) + 2) +
            |Cα| * (m + Real.log (m + 1))) := by
      rw [e1, e2, e3, hmq]
      ring
    rw [hexp]
    linarith only [f1, f2, f3, f4]
  calc ∫⁻ v in {v : Fin m → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s},
        ∏ i, ENNReal.ofReal (Real.exp ((β / 2) * smearedKernel lam (v i)))
      = ENNReal.ofReal Real.pi ^ m * ∫⁻ t in posSimplex m s, ∏ i, gr (Real.sqrt (t i)) := hpolar
    _ ≤ ENNReal.ofReal Real.pi ^ m * ∫⁻ t in posSimplex m s,
          ENNReal.ofReal (Real.exp (m * ((β / 2) * c))) * ENNReal.ofReal (∏ i, t i ^ (α - 1)) := by
        exact mul_le_mul_right (setLIntegral_mono' (measurableSet_posSimplex m s) hpt) _
    _ = ENNReal.ofReal Real.pi ^ m *
          (ENNReal.ofReal (Real.exp (m * ((β / 2) * c))) * dirichletTwoLevel α m m s) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hI]
    _ ≤ ENNReal.ofReal Real.pi ^ m * (ENNReal.ofReal (Real.exp (m * ((β / 2) * c))) *
          ENNReal.ofReal (Real.exp
            ((α * m) * (Real.log s - Real.log (α * m)) + m + |Cα| * (m + Real.log (m + 1))))) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp ((m : ℝ) * Real.log Real.pi + m * ((β / 2) * c) +
          ((α * m) * (Real.log s - Real.log (α * m)) + m +
            |Cα| * (m + Real.log (m + 1))))) := by
        have hπ : Real.pi ^ m = Real.exp (m * Real.log Real.pi) := by
          rw [Real.exp_nat_mul, Real.exp_log Real.pi_pos]
        rw [← ENNReal.ofReal_pow Real.pi_pos.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hπ, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hfin)

/-! ### The tree integral for `β > 4` -/

/-- **Source l. 911--914** (`β > 4`, "Arguing as in (3.20b)"): the tree integral over the ball of
`ℂ^{2q}` is at most `exp ((2q)(2 - β/2) log λ + C q)`. -/
theorem exists_lintegral_ball_tree_le_of_four_lt {β : ℝ} (hβ : 4 < β) :
    ∃ C : ℝ, ∀ (q m : ℕ), m = 2 * q → ∀ lam : ℝ, 0 < lam → ∀ s : ℝ,
      ∫⁻ v in {v : Fin m → ℂ | ∑ i, ‖v i‖ ^ 2 ≤ s},
          ∏ i, ENNReal.ofReal (Real.exp ((β / 2) * smearedKernel lam (v i))) ≤
        ENNReal.ofReal (Real.exp ((2 * q) * ((2 - β / 2) * Real.log lam) + C * q)) := by
  have hγ : 2 < β / 2 := by linarith
  have hZ := dipoleConstant_pos (β / 2) hγ.le
  refine ⟨2 * |Real.log (dipoleConstant (β / 2) hγ.le)|, fun q m hm lam hlam s => ?_⟩
  refine (lintegral_ball_prod_exp_le hγ hlam m s).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : dipoleConstant (β / 2) hγ.le * lam ^ (2 - β / 2) =
      Real.exp (Real.log (dipoleConstant (β / 2) hγ.le) + (2 - β / 2) * Real.log lam) := by
    rw [Real.exp_add, Real.exp_log hZ, Real.rpow_def_of_pos hlam, mul_comm (Real.log lam)]
  rw [h1, ← Real.exp_nat_mul]
  refine Real.exp_le_exp.2 ?_
  have h2 := le_abs_self (Real.log (dipoleConstant (β / 2) hγ.le))
  have hq : (m : ℝ) = 2 * q := by rw [hm]; push_cast; ring
  rw [hq]
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h3 := mul_le_mul_of_nonneg_left h2 hq0
  linarith only [h3]

/-! ### Combining the cycle and tree factors -/

/-- Arithmetic of the final assembly: if the cycle and tree integrals are at most `e^a` and `e^b`,
then `N^K` times their product is at most `e^{K log N + a + b}`. -/
theorem natCast_pow_mul_le {N K : ℕ} (hN : 0 < N) {A B : ℝ≥0∞} {a b : ℝ}
    (hA : A ≤ ENNReal.ofReal (Real.exp a)) (hB : B ≤ ENNReal.ofReal (Real.exp b)) :
    (N : ℝ≥0∞) ^ K * (A * B) ≤ ENNReal.ofReal (Real.exp (K * Real.log N + (a + b))) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  calc (N : ℝ≥0∞) ^ K * (A * B)
      ≤ ENNReal.ofReal N ^ K * (ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b)) := by
        rw [ENNReal.ofReal_natCast]
        exact mul_le_mul' le_rfl (mul_le_mul' hA hB)
    _ = ENNReal.ofReal (Real.exp (K * Real.log N + (a + b))) := by
        rw [← ENNReal.ofReal_pow hN'.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (by positivity), Real.exp_add, Real.exp_add, Real.exp_nat_mul,
          Real.exp_log hN']

/-! ### Lemma 3.5 for `β ∈ (2, 4)` and `β > 4` -/

section Cases

universe u

/-- The cell integral is zero when no configuration has nearest-neighbour map `f`. -/
theorem lintegral_cell_eq_zero_of_not_exists {ι : Type u} [Fintype ι] [Nontrivial ι]
    (key : ι ↪ ℕ) (N : ℕ) (f : ι → ι) (hf : ¬ ∃ z₀ : ι → ℂ, nnMap key z₀ = f)
    (F : (ι → ℂ) → ℝ≥0∞) :
    ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f}, F z = 0 := by
  have : (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun z hz => hf ⟨z, hz.2⟩
  rw [this]
  simp

/-- The cycle factor for `β > 2` in exponential form: `(𝒵_γ λ^{2-γ})^K = exp (K (log 𝒵_γ + (2-γ) log λ))`. -/
theorem dipoleConstant_mul_rpow_pow {γ : ℝ} (hγ : 2 < γ) {lam : ℝ} (hlam : 0 < lam) (K : ℕ) :
    (dipoleConstant γ hγ.le * lam ^ (2 - γ)) ^ K =
      Real.exp (K * (Real.log (dipoleConstant γ hγ.le) + (2 - γ) * Real.log lam)) := by
  have hZ := dipoleConstant_pos γ hγ.le
  have hpos : 0 < dipoleConstant γ hγ.le * lam ^ (2 - γ) :=
    mul_pos hZ (Real.rpow_pos_of_pos hlam _)
  have hlog : Real.log (dipoleConstant γ hγ.le * lam ^ (2 - γ)) =
      Real.log (dipoleConstant γ hγ.le) + (2 - γ) * Real.log lam := by
    rw [Real.log_mul hZ.ne' (Real.rpow_pos_of_pos hlam _).ne', Real.log_rpow hlam]
  rw [← hlog, Real.exp_nat_mul, Real.exp_log hpos]

/-- **Lemma 3.5, case `β ∈ (2, 4)`** (source l. 793--797). For `f` the nearest-neighbour map of a
configuration of `2p` points in `Λ = [0, √N]²`, with `K` 2-cycles,
`log J(f) ≤ K log N + (2-β) K log λ + K log 𝒵_β + (1 - β/4)(2p-2K) log (N/(p-K)) + C_β (p-K)`. The
constant `C` depends only on `β`; the bound holds for every `λ > 0` and every `0 < N`. -/
theorem lintegral_cell_le_of_two_lt_of_lt_four {β : ℝ} (hβ2 : 2 < β) (hβ4 : β < 4) :
    ∃ C : ℝ, ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (N p K : ℕ) (f : ι → ι),
      0 < N → Fintype.card ι = 2 * p → Fintype.card {i // i ∈ gpRefSet key f} = K →
      ∀ lam : ℝ, 0 < lam →
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
            ENNReal.ofReal (Real.exp ((β / 2) *
              ∑ i, smearedKernel lam (z i - z (nnMap key z i)))) ≤
          ENNReal.ofReal (Real.exp (K * Real.log N + (2 - β) * K * Real.log lam +
            K * Real.log (dipoleConstant β hβ2.le) +
            (1 - β / 4) * (2 * p - 2 * K) * Real.log (N / (p - K)) + C * (p - K))) := by
  obtain ⟨Ct, hCt⟩ := exists_lintegral_ball_tree_le hβ2.le hβ4
  refine ⟨Ct, fun ι _ _ key N p K f hN hcard hK lam hlam => ?_⟩
  by_cases hf : ∃ z₀ : ι → ℂ, nnMap key z₀ = f
  swap
  · rw [lintegral_cell_eq_zero_of_not_exists key N f hf]
    exact zero_le
  obtain ⟨z₀, rfl⟩ := hf
  have hK2 : 2 * K ≤ 2 * p := by
    have := two_mul_card_gpRefSet_nnMap_le key z₀
    omega
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (show K ≤ p by omega)
  refine (lintegral_cell_le_cycle_mul_tree hcard key ⟨z₀, rfl⟩ hK β lam).trans ?_
  have hA := (lintegral_ball_prod_exp_le hβ2 hlam K (36 * N / Real.pi)).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq (dipoleConstant_mul_rpow_pow hβ2 hlam K)))
  have hB := hCt N q (2 * (K + q) - 2 * K) hN (by omega) lam hlam
  refine (natCast_pow_mul_le hN hA hB).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  push_cast
  rw [add_sub_cancel_left, show 2 * ((K : ℝ) + q) - 2 * K = 2 * q by ring]
  refine le_of_eq ?_
  ring

/-- **Lemma 3.5, case `β > 4`** (source l. 805--809). For `f` the nearest-neighbour map of a
configuration of `2p` points in `Λ`, with `K` 2-cycles,
`log J(f) ≤ K log N + (2-β) K log λ + K log 𝒵_β + (2p-2K)(2 - β/2) log λ + C_β (p-K)`,
for every `λ > 0` and `0 < N`. -/
theorem lintegral_cell_le_of_four_lt {β : ℝ} (hβ : 4 < β) :
    ∃ C : ℝ, ∀ (ι : Type u) [Fintype ι] [Nontrivial ι] (key : ι ↪ ℕ) (N p K : ℕ) (f : ι → ι),
      0 < N → Fintype.card ι = 2 * p → Fintype.card {i // i ∈ gpRefSet key f} = K →
      ∀ lam : ℝ, 0 < lam →
        ∫⁻ z in (Set.univ.pi fun _ : ι => box N) ∩ {z | nnMap key z = f},
            ENNReal.ofReal (Real.exp ((β / 2) *
              ∑ i, smearedKernel lam (z i - z (nnMap key z i)))) ≤
          ENNReal.ofReal (Real.exp (K * Real.log N + (2 - β) * K * Real.log lam +
            K * Real.log (dipoleConstant β (by linarith)) +
            (2 * p - 2 * K) * (2 - β / 2) * Real.log lam + C * (p - K))) := by
  have hβ2 : 2 < β := by linarith
  obtain ⟨Ct, hCt⟩ := exists_lintegral_ball_tree_le_of_four_lt hβ
  refine ⟨Ct, fun ι _ _ key N p K f hN hcard hK lam hlam => ?_⟩
  by_cases hf : ∃ z₀ : ι → ℂ, nnMap key z₀ = f
  swap
  · rw [lintegral_cell_eq_zero_of_not_exists key N f hf]
    exact zero_le
  obtain ⟨z₀, rfl⟩ := hf
  have hK2 : 2 * K ≤ 2 * p := by
    have := two_mul_card_gpRefSet_nnMap_le key z₀
    omega
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (show K ≤ p by omega)
  refine (lintegral_cell_le_cycle_mul_tree hcard key ⟨z₀, rfl⟩ hK β lam).trans ?_
  have hA := (lintegral_ball_prod_exp_le hβ2 hlam K (36 * N / Real.pi)).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq (dipoleConstant_mul_rpow_pow hβ2 hlam K)))
  have hB := hCt q (2 * (K + q) - 2 * K) (by omega) lam hlam (36 * N / Real.pi)
  refine (natCast_pow_mul_le hN hA hB).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  push_cast
  rw [add_sub_cancel_left, show 2 * ((K : ℝ) + q) - 2 * K = 2 * q by ring]
  refine le_of_eq ?_
  ring

end Cases

end TwoComponentCoulomb

end
