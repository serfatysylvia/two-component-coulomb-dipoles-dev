/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Gibbs.Basic
public import TwoComponentCoulomb.LowerBound.DipoleJensen
public import TwoComponentCoulomb.Potential.PairIntegral

/-!
# The sum over the assignments of negative labels

Source: Proposition 4.1, Step 1 (l. 1763--1775), the case `β = 2`
(l. 1820--1827) and Step 2, eq. (minz3) (l. 1837--1843): "the `N!` assignments of negative labels
are disjoint". Combined with the dipole Jensen bound `prod_annulus_le_lintegral_exp_energy`
(ruling R12a), this gives a lower bound on the partition function in terms of one-dipole integrals.

* `energy_comp_equiv`, `energy_sum_elim_comp_perm` : the energy is invariant under relabelling
  the negative charges.
* `lintegral_sumPi_eq_prod` : the measure-preserving identification of
  `Fin N ⊕ Fin N → ℂ` with `(Fin N → ℂ) × (Fin N → ℂ)`, `Z ↦ (Z ∘ inl, Z ∘ inr)`.
* `partitionFunction_eq_lintegral_prod` : the partition function as an integral over
  `(X, Y) ∈ Λ^N × Λ^N`.
* `labelSet` : the set `A_σ` where the `i`-th positive charge is paired with the `σ i`-th negative
  charge, which lies in the annulus `a ≤ |y_{σ i} - x_i| ≤ b` around `x_i`.
* `partitionFunction_ge_label_sum` : `Z ≥ N! ∫_{H'} ∏_i ∫_{a ≤ |u| ≤ b} e^{β g_λ(u)} du dX`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TwoComponentCoulomb

variable {N : ℕ}

/-! ### Invariance of the energy under relabelling -/

/-- The energy is invariant under any relabelling of the charges that preserves the signs. -/
theorem energy_comp_equiv (lam : ℝ) (Z : Fin N ⊕ Fin N → ℂ) (e : Fin N ⊕ Fin N ≃ Fin N ⊕ Fin N)
    (he : ∀ a, charge (e a) = charge a) : energy lam (Z ∘ e) = energy lam Z := by
  rw [energy_eq_sum_smearedKernel, energy_eq_sum_smearedKernel]
  congr 2
  refine Fintype.sum_equiv e _ _ fun a => ?_
  refine Fintype.sum_equiv e _ _ fun b => ?_
  simp [he]

/-- A permutation of the positive and a permutation of the negative labels preserve the sign. -/
theorem charge_sumCongr (σ τ : Equiv.Perm (Fin N)) (a : Fin N ⊕ Fin N) :
    charge (Equiv.sumCongr σ τ a) = charge a := by
  cases a <;> rfl

/-- **The energy is invariant under relabelling the negative charges**:
`F_λ(x, y ∘ σ) = F_λ(x, y)`. -/
theorem energy_sum_elim_comp_perm (lam : ℝ) (X Y : Fin N → ℂ) (σ : Equiv.Perm (Fin N)) :
    energy lam (Sum.elim X (Y ∘ σ)) = energy lam (Sum.elim X Y) := by
  have h : (Sum.elim X (Y ∘ σ) : Fin N ⊕ Fin N → ℂ) =
      (Sum.elim X Y) ∘ (Equiv.sumCongr (Equiv.refl _) σ) := by
    funext a
    cases a <;> rfl
  rw [h]
  exact energy_comp_equiv lam _ _ (charge_sumCongr (Equiv.refl _) σ)

/-! ### Positive and negative charges as a product -/

/-- The identification `Z ↦ (Z ∘ inl, Z ∘ inr)` of `ℂ^{N ⊕ N}` with `ℂ^N × ℂ^N` preserves the
Lebesgue measure: integrals over configurations of `2N` charges are iterated integrals over the
positions `X` of the positive and `Y` of the negative charges. -/
theorem lintegral_sumPi_eq_prod (f : (Fin N ⊕ Fin N → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ Z, f Z = ∫⁻ p : (Fin N → ℂ) × (Fin N → ℂ), f (Sum.elim p.1 p.2) := by
  have h := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ Fin N => ℂ))
  rw [← h.lintegral_comp hf]
  congr 1

/-- The map `(X, Y) ↦ Sum.elim X Y` is measurable. -/
theorem measurable_sumElim_prod :
    Measurable fun p : (Fin N → ℂ) × (Fin N → ℂ) => (Sum.elim p.1 p.2 : Fin N ⊕ Fin N → ℂ) := by
  refine measurable_pi_iff.2 fun a => ?_
  rcases a with i | i
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply i).comp measurable_snd

/-- The Boltzmann weight `e^{-β F_λ(X, Y)}` as a function on `ℂ^N × ℂ^N`. -/
theorem measurable_weight_prod (β lam : ℝ) :
    Measurable fun p : (Fin N → ℂ) × (Fin N → ℂ) =>
      ENNReal.ofReal (Real.exp (-β * energy lam (Sum.elim p.1 p.2))) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
    ((measurable_energy lam).comp measurable_sumElim_prod)))

/-- **The partition function as an integral over the positive and negative charges**:
`Z = ∫_{Λ^N × Λ^N} e^{-β F_λ(X, Y)} d(X, Y)`. -/
theorem partitionFunction_eq_lintegral_prod (β lam : ℝ) :
    partitionFunction N β lam =
      ∫⁻ p in (Set.univ.pi fun _ : Fin N => box N) ×ˢ (Set.univ.pi fun _ : Fin N => box N),
        ENNReal.ofReal (Real.exp (-β * energy lam (Sum.elim p.1 p.2))) := by
  unfold partitionFunction
  rw [← lintegral_indicator (measurableSet_pi_box N),
    lintegral_sumPi_eq_prod _ ((measurable_ofReal_exp_neg_mul_energy β lam).indicator
      (measurableSet_pi_box N)),
    ← lintegral_indicator ((MeasurableSet.univ_pi fun _ => measurableSet_box N).prod
      (MeasurableSet.univ_pi fun _ => measurableSet_box N))]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ (Set.univ.pi fun _ : Fin N => box N) ×ˢ (Set.univ.pi fun _ : Fin N => box N)
  · have hp' : (Sum.elim p.1 p.2 : Fin N ⊕ Fin N → ℂ) ∈ Set.univ.pi fun _ : Fin N ⊕ Fin N =>
        box N := by
      rintro (i | i) -
      · exact hp.1 i (Set.mem_univ i)
      · exact hp.2 i (Set.mem_univ i)
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp']
  · have hp' : (Sum.elim p.1 p.2 : Fin N ⊕ Fin N → ℂ) ∉ Set.univ.pi fun _ : Fin N ⊕ Fin N =>
        box N := by
      intro h
      refine hp ⟨fun i _ => ?_, fun i _ => ?_⟩
      · exact h (Sum.inl i) (Set.mem_univ _)
      · exact h (Sum.inr i) (Set.mem_univ _)
    rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']

/-! ### The sets `A_σ` -/

/-- The set `A_σ` of pairs `(X, Y)` of positive and negative charges such that `X ∈ H` and the
`i`-th positive charge is paired with the `σ i`-th negative charge, which lies in the closed
annulus `a(X)_i ≤ |y_{σ i} - x_i| ≤ b(X)_i` (source l. 1820--1827: "the `N!` assignments of
negative labels"). -/
def labelSet (H : Set (Fin N → ℂ)) (a b : (Fin N → ℂ) → Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    Set ((Fin N → ℂ) × (Fin N → ℂ)) :=
  {p | p.1 ∈ H ∧ ∀ i, a p.1 i ≤ ‖p.2 (σ i) - p.1 i‖ ∧ ‖p.2 (σ i) - p.1 i‖ ≤ b p.1 i}

/-- The closed annuli `a(X)_i ≤ |Y_i - X_i| ≤ b(X)_i` (the fibre of `labelSet` for `σ = 1`). -/
def annulusSet (a b : (Fin N → ℂ) → Fin N → ℝ) (X : Fin N → ℂ) : Set (Fin N → ℂ) :=
  {Y | ∀ i, a X i ≤ ‖Y i - X i‖ ∧ ‖Y i - X i‖ ≤ b X i}

theorem measurableSet_annulusSet {a b : (Fin N → ℂ) → Fin N → ℝ} (X : Fin N → ℂ) :
    MeasurableSet (annulusSet a b X) := by
  have : annulusSet a b X = ⋂ i, ({Y : Fin N → ℂ | a X i ≤ ‖Y i - X i‖} ∩
      {Y : Fin N → ℂ | ‖Y i - X i‖ ≤ b X i}) := by
    ext Y
    simp [annulusSet]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.inter ?_ ?_
  · exact measurableSet_le measurable_const (by fun_prop)
  · exact measurableSet_le (by fun_prop) measurable_const

theorem measurableSet_labelSet {H : Set (Fin N → ℂ)} {a b : (Fin N → ℂ) → Fin N → ℝ}
    (hH : MeasurableSet H) (ha : ∀ i, Measurable fun X => a X i)
    (hb : ∀ i, Measurable fun X => b X i) (σ : Equiv.Perm (Fin N)) :
    MeasurableSet (labelSet H a b σ) := by
  have : labelSet H a b σ = (Prod.fst ⁻¹' H) ∩
      ⋂ i, ({p : (Fin N → ℂ) × (Fin N → ℂ) | a p.1 i ≤ ‖p.2 (σ i) - p.1 i‖} ∩
        {p : (Fin N → ℂ) × (Fin N → ℂ) | ‖p.2 (σ i) - p.1 i‖ ≤ b p.1 i}) := by
    ext p
    simp [labelSet]
  rw [this]
  refine (measurable_fst hH).inter (MeasurableSet.iInter fun i => MeasurableSet.inter ?_ ?_)
  · exact measurableSet_le ((ha i).comp measurable_fst) (by fun_prop)
  · exact measurableSet_le (by fun_prop) ((hb i).comp measurable_fst)

/-- **The `N!` assignments of negative labels are disjoint** (source l. 1820, 1839): if the
annuli around the points of `X ∈ H` are `2λ`-separated, then a negative charge lies in at most one
of them. -/
theorem pairwise_disjoint_labelSet {lam : ℝ} (hlam : 0 < lam) {H : Set (Fin N → ℂ)}
    {a b : (Fin N → ℂ) → Fin N → ℝ}
    (hsep : ∀ X ∈ H, ∀ i j, i ≠ j → b X i + b X j + 2 * lam ≤ ‖X i - X j‖) :
    Pairwise (Function.onFun Disjoint (labelSet H a b)) := by
  intro σ τ hστ
  rw [Function.onFun, Set.disjoint_left]
  rintro p ⟨hpH, hσ⟩ ⟨-, hτ⟩
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
    by_contra hcon
    push Not at hcon
    exact hστ (Equiv.ext hcon)
  set k : Fin N := σ i with hk
  set j : Fin N := τ.symm k with hj
  have hji : j ≠ i := by
    intro h
    apply hi
    have h' : τ j = τ i := by rw [h]
    rwa [hj, Equiv.apply_symm_apply] at h'
  have h1 : ‖p.2 k - p.1 i‖ ≤ b p.1 i := (hσ i).2
  have h2 : ‖p.2 k - p.1 j‖ ≤ b p.1 j := by
    have := (hτ j).2
    rwa [hj, Equiv.apply_symm_apply] at this
  have h3 := hsep p.1 hpH i j hji.symm
  have h4 : ‖p.1 i - p.1 j‖ ≤ ‖p.2 k - p.1 i‖ + ‖p.2 k - p.1 j‖ := by
    calc ‖p.1 i - p.1 j‖ = ‖(p.2 k - p.1 j) - (p.2 k - p.1 i)‖ := by congr 1; ring
      _ ≤ ‖p.2 k - p.1 j‖ + ‖p.2 k - p.1 i‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  linarith

/-- The map `Y ↦ Y ∘ σ` on `ℂ^N` preserves the Lebesgue measure. -/
theorem measurePreserving_comp_perm (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (fun Y : Fin N → ℂ => Y ∘ σ) volume volume := by
  have h := volume_preserving_arrowCongr' σ.symm (MeasurableEquiv.refl ℂ)
    (MeasurePreserving.id volume)
  convert h using 1
  funext Y j
  simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr']

/-- The fibre of `labelSet` over `X ∈ H` is the preimage of the annuli under `Y ↦ Y ∘ σ`. -/
theorem labelSet_section {H : Set (Fin N → ℂ)} {a b : (Fin N → ℂ) → Fin N → ℝ}
    {X : Fin N → ℂ} (hX : X ∈ H) (σ : Equiv.Perm (Fin N)) :
    {Y | (X, Y) ∈ labelSet H a b σ} = (fun Y : Fin N → ℂ => Y ∘ σ) ⁻¹' annulusSet a b X := by
  ext Y
  simp [labelSet, annulusSet, hX]

/-- **The integral over `A_σ` reduces to the integral over the annuli** (change of variables
`Y ↦ Y ∘ σ`, using that the energy is invariant under relabelling the negative charges). -/
theorem lintegral_labelSet {H : Set (Fin N → ℂ)} {a b : (Fin N → ℂ) → Fin N → ℝ}
    (hH : MeasurableSet H) (ha : ∀ i, Measurable fun X => a X i)
    (hb : ∀ i, Measurable fun X => b X i) (β lam : ℝ) (σ : Equiv.Perm (Fin N)) :
    ∫⁻ p in labelSet H a b σ,
        ENNReal.ofReal (Real.exp (-β * energy lam (Sum.elim p.1 p.2))) =
      ∫⁻ X in H, ∫⁻ Y in annulusSet a b X,
        ENNReal.ofReal (Real.exp (-β * energy lam (Sum.elim X Y))) := by
  set W : (Fin N → ℂ) × (Fin N → ℂ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-β * energy lam (Sum.elim p.1 p.2))) with hW
  have hWm : Measurable W := measurable_weight_prod β lam
  have hAm := measurableSet_labelSet hH ha hb σ
  rw [← lintegral_indicator hAm, Measure.volume_eq_prod,
    lintegral_prod _ ((hWm.indicator hAm).aemeasurable), ← lintegral_indicator hH]
  refine lintegral_congr fun X => ?_
  by_cases hX : X ∈ H
  · rw [Set.indicator_of_mem hX]
    have hS : MeasurableSet {Y | (X, Y) ∈ labelSet H a b σ} := hAm.preimage measurable_prodMk_left
    have h1 : ∀ Y, (labelSet H a b σ).indicator W (X, Y) =
        {Y | (X, Y) ∈ labelSet H a b σ}.indicator (fun Y => W (X, Y)) Y := by
      intro Y
      by_cases hY : (X, Y) ∈ labelSet H a b σ
      · rw [Set.indicator_of_mem hY,
          Set.indicator_of_mem (show Y ∈ {Y | (X, Y) ∈ labelSet H a b σ} from hY)]
      · rw [Set.indicator_of_notMem hY,
          Set.indicator_of_notMem (show Y ∉ {Y | (X, Y) ∈ labelSet H a b σ} from hY)]
    simp_rw [h1]
    rw [lintegral_indicator hS, labelSet_section hX σ]
    have hfm : Measurable fun Y : Fin N → ℂ => W (X, Y) := hWm.comp measurable_prodMk_left
    have hinv : ∀ Y : Fin N → ℂ, W (X, Y ∘ σ) = W (X, Y) := fun Y => by
      simp only [hW]
      rw [energy_sum_elim_comp_perm]
    have := (measurePreserving_comp_perm σ).setLIntegral_comp_preimage
      (measurableSet_annulusSet (a := a) (b := b) X) hfm
    simpa only [hinv] using this
  · rw [Set.indicator_of_notMem hX]
    have : ∀ Y, (labelSet H a b σ).indicator W (X, Y) = 0 := fun Y =>
      Set.indicator_of_notMem (fun h => hX h.1) _
    simp [this]

/-- The sets `A_σ` lie in `Λ^N × Λ^N` when the discs `B̄(x_i, b_i)` lie in `Λ`. -/
theorem labelSet_subset {H : Set (Fin N → ℂ)} {a b : (Fin N → ℂ) → Fin N → ℝ}
    (hab : ∀ X ∈ H, ∀ i, 0 ≤ a X i ∧ a X i ≤ b X i)
    (hbox : ∀ X ∈ H, ∀ i, Metric.closedBall (X i) (b X i) ⊆ box N) (σ : Equiv.Perm (Fin N)) :
    labelSet H a b σ ⊆ (Set.univ.pi fun _ : Fin N => box N) ×ˢ
      (Set.univ.pi fun _ : Fin N => box N) := by
  rintro p ⟨hpH, hp⟩
  refine ⟨fun i _ => hbox p.1 hpH i ?_, fun j _ => ?_⟩
  · exact Metric.mem_closedBall_self (le_trans (hab p.1 hpH i).1 (hab p.1 hpH i).2)
  · apply hbox p.1 hpH (σ.symm j)
    have := (hp (σ.symm j)).2
    rw [Equiv.apply_symm_apply] at this
    rwa [Metric.mem_closedBall, dist_eq_norm]

/-- **The partition function dominates the sum over the assignments of negative labels**
(source l. 1820--1827 and eq. (minz3), l. 1837--1843; Prop. 4.1, Steps 1--2, by the route of
ruling R12a). Let `H` be a measurable set of positions of the positive charges and `a ≤ b` radius
functions such that, for `X ∈ H`, the closed discs `B̄(x_i, b_i)` lie in `Λ` and
`b_i + b_j + 2λ ≤ |x_i - x_j|` for `i ≠ j`. Then
`Z ≥ N! ∫_H ∏_i ∫_{a_i ≤ |u| ≤ b_i} e^{β g_λ(u)} du dX`. -/
theorem partitionFunction_ge_label_sum {lam : ℝ} (hlam : 0 < lam) (β : ℝ)
    {H : Set (Fin N → ℂ)} (hH : MeasurableSet H) {a b : (Fin N → ℂ) → Fin N → ℝ}
    (ha : ∀ i, Measurable fun X => a X i) (hb : ∀ i, Measurable fun X => b X i)
    (hab : ∀ X ∈ H, ∀ i, 0 ≤ a X i ∧ a X i ≤ b X i)
    (hbox : ∀ X ∈ H, ∀ i, Metric.closedBall (X i) (b X i) ⊆ box N)
    (hsep : ∀ X ∈ H, ∀ i j, i ≠ j → b X i + b X j + 2 * lam ≤ ‖X i - X j‖) :
    ENNReal.ofReal (N.factorial : ℝ) *
        ∫⁻ X in H, ∏ i, ENNReal.ofReal (∫ u in {u : ℂ | a X i ≤ ‖u‖ ∧ ‖u‖ ≤ b X i},
          Real.exp (β * smearedKernel lam u)) ≤
      partitionFunction N β lam := by
  classical
  set W : (Fin N → ℂ) × (Fin N → ℂ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-β * energy lam (Sum.elim p.1 p.2))) with hW
  calc ENNReal.ofReal (N.factorial : ℝ) * ∫⁻ X in H, ∏ i, ENNReal.ofReal
          (∫ u in {u : ℂ | a X i ≤ ‖u‖ ∧ ‖u‖ ≤ b X i}, Real.exp (β * smearedKernel lam u))
      ≤ ENNReal.ofReal (N.factorial : ℝ) * ∫⁻ X in H, ∫⁻ Y in annulusSet a b X,
          ENNReal.ofReal (Real.exp (-β * energy lam (Sum.elim X Y))) := by
        refine mul_le_mul_right (setLIntegral_mono' hH fun X hX => ?_) _
        exact prod_annulus_le_lintegral_exp_energy hlam β X (a X) (b X) (hab X hX) (hsep X hX)
    _ = ∑ σ : Equiv.Perm (Fin N), ∫⁻ p in labelSet H a b σ, W p := by
        simp_rw [hW, lintegral_labelSet hH ha hb β lam]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_natCast]
    _ = ∫⁻ p in ⋃ σ : Equiv.Perm (Fin N), labelSet H a b σ, W p := by
        rw [lintegral_iUnion (fun σ => measurableSet_labelSet hH ha hb σ)
          (pairwise_disjoint_labelSet hlam fun X hX => hsep X hX), tsum_fintype]
    _ ≤ ∫⁻ p in (Set.univ.pi fun _ : Fin N => box N) ×ˢ (Set.univ.pi fun _ : Fin N => box N),
          W p :=
        lintegral_mono_set (Set.iUnion_subset fun σ => labelSet_subset hab hbox σ)
    _ = partitionFunction N β lam := (partitionFunction_eq_lintegral_prod β lam).symm

end TwoComponentCoulomb

end
