/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.NearestNeighbor.SecondRadius

/-!
# The pair-assigned energy of Propositions 3.9 and 3.10

Source: Proposition 3.9 (`prop:isolated`, l. 1223–1237) and the
definition (def:F(1)) in the proof of Proposition 3.10 (l. 1532–1538). Both integrate, over a
configuration whose nearest-neighbour graph consists of 2-cycles, the energy

`F^nn(Z) − C ∑_{i ∉ S} (r̃₁(z_i)/r̃₂(z_i))² + ∑_{i ∈ S} (log((r̃₂(z_i) ∧ r̃₂(z_{φ₁(i)}))/r̃₁(z_i)) − C)`,

where `F^nn = −½ ∑_i g_λ(z_i − z_{φ₁(i)})` and `S` is the set of vertices of the pairs that are
*assigned* the logarithmic (same-sign) term. In Proposition 3.9, `S` is the vertex set `I_S` of
an arbitrary set of 2-cycles (l. 1225); in (def:F(1)), `S = I'` is the set of vertices of the
marked same-sign pairs and the distances are computed within `I`. Only the assigned pair terms
enter, not the charges (Proposition 3.9 is applied with `S` the marked pairs, l. 1553), so the
energy is defined for an arbitrary `S`.

## Main definitions

* `TwoComponentCoulomb.nnEnergy key lam z`: `F^nn(z) = −½ ∑_i g_λ(z_i − z_{φ₁(i)})`.
* `TwoComponentCoulomb.pairAssignedEnergy h3 key lam C S z`: the energy above.
-/

@[expose] public section

namespace TwoComponentCoulomb

open Finset

variable {ι : Type*} [Fintype ι] [Nontrivial ι]

/-- The nearest-neighbour energy `F^nn(z) = −½ ∑_i g_λ(z_i − z_{φ₁(i)})` (eq:defdipoleen,
source l. 778–780), on a general finite index set. -/
noncomputable def nnEnergy (key : ι ↪ ℕ) (lam : ℝ) (z : ι → ℂ) : ℝ :=
  -(1 / 2) * ∑ i, smearedKernel lam (z i - z (nnMap key z i))

open scoped Classical in
/-- The pair-assigned energy of Proposition 3.9 and of (def:F(1)) (source l. 1228–1230,
l. 1533–1537): the nearest-neighbour energy, plus `log((r̃₂(z_i) ∧ r̃₂(z_{φ₁(i)}))/r̃₁(z_i)) − C`
for each vertex `i ∈ S`, minus `C (r̃₁(z_i)/r̃₂(z_i))²` for each vertex `i ∉ S`. -/
noncomputable def pairAssignedEnergy (h3 : 3 ≤ Fintype.card ι) (key : ι ↪ ℕ) (lam C : ℝ)
    (S : Finset ι) (z : ι → ℂ) : ℝ :=
  nnEnergy key lam z
    + ∑ i ∈ S, (Real.log (min (nnRadius2 h3 key lam z i) (nnRadius2 h3 key lam z (nnMap key z i))
        / nnRadius lam z i) - C)
    - C * ∑ i ∈ Sᶜ, (nnRadius lam z i / nnRadius2 h3 key lam z i) ^ 2

end TwoComponentCoulomb

end
