/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
Frozen declaration (see manifest/frozen_anchors.json). Never edit this file.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TwoComponentCoulomb.Frozen.NearestNeighbor

/-!
# Frozen: `TwoComponentCoulomb.numComponents`

Frozen definition, approved by the authors in this exact form (RULINGS.md R18, R19).
Source: l. 375.
-/

@[expose] public section

namespace TwoComponentCoulomb

/-- `K`: the number of connected components of the nearest-neighbour graph `γ_{2N}(Z_{2N})`,
the graph on `{1, …, 2N}` with an edge from `i` to `φ₁(i)` (source l. 375). -/
noncomputable def numComponents {N : ℕ} (Z : Fin N ⊕ Fin N → ℂ) : ℕ :=
  Nat.card (SimpleGraph.fromRel fun i j => nearestNeighbor Z i = j).ConnectedComponent

end TwoComponentCoulomb

end
