/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TwoComponentCoulomb.Frozen.DipoleConstant
public import TwoComponentCoulomb.Frozen.Energy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TwoComponentCoulomb.Frozen.M0
public import TwoComponentCoulomb.Frozen.GibbsMeasure
public import TwoComponentCoulomb.Frozen.IsolatedDipoles
public import TwoComponentCoulomb.Frozen.LongIsolatedDipoles
public import TwoComponentCoulomb.Frozen.PartitionFunction
public import TwoComponentCoulomb.Frozen.ReducedEnergy
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TwoComponentCoulomb.Frozen.Fluct
public import TwoComponentCoulomb.Frozen.Proposition22
public import TwoComponentCoulomb.Frozen.Corollary23
public import TwoComponentCoulomb.Frozen.Lemma36
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Frozen.SmearedKernel
public import TwoComponentCoulomb.Frozen.Proposition41
public import TwoComponentCoulomb.Frozen.Proposition310
public import TwoComponentCoulomb.Frozen.Theorem1
public import TwoComponentCoulomb.Frozen.Theorem2

/-!
# Two-component Coulomb gas

Lean formalization of Boursier–Serfaty, *Dipole Formation in the Two-component Plasma*
(arXiv:2410.01025; the version formalized here is in `source/`).

This root module exports the seven frozen theorems, together with the frozen
definitions their statements use:

* `TwoComponentCoulomb.theorem_1` (Theorem 1)
* `TwoComponentCoulomb.theorem_2` (Theorem 2)
* `TwoComponentCoulomb.proposition_2_2` (Proposition 2.2)
* `TwoComponentCoulomb.corollary_2_3` (Corollary 2.3)
* `TwoComponentCoulomb.lemma_3_6` (Lemma 3.6)
* `TwoComponentCoulomb.proposition_3_10` (Proposition 3.10)
* `TwoComponentCoulomb.proposition_4_1` (Proposition 4.1)
-/

public section
