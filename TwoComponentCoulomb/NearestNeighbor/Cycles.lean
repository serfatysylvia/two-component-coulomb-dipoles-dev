/-
Copyright (c) 2026 Sylvia Serfaty.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import TwoComponentCoulomb.NearestNeighbor.Basic

/-!
# Cycles of the nearest-neighbour map

The directed nearest-neighbour graph `i ↦ φ₁ i` of a configuration has only 2-cycles (source
l. 202–207: its components are 2-cycles with trees attached). Thanks to the index tie-break of
the frozen definition (ruling R4) this holds for *every* configuration, not just almost surely.

* `norm_sub_nearestNeighbor_nearestNeighbor_le`: edge lengths do not increase along an orbit.
* `nearestNeighbor_nearestNeighbor_of_iterate_eq_self`: every periodic point lies in a 2-cycle.
* `exists_iterate_nearestNeighbor_two_cycle`: every orbit reaches a 2-cycle within `2N` steps.
-/

public section

namespace TwoComponentCoulomb

variable {N : ℕ}

/-- The edge lengths of the nearest-neighbour graph do not increase along an orbit. -/
theorem norm_sub_nearestNeighbor_nearestNeighbor_le (Z : Fin N ⊕ Fin N → ℂ)
    (i : Fin N ⊕ Fin N) :
    ‖Z (nearestNeighbor Z i) - Z (nearestNeighbor Z (nearestNeighbor Z i))‖ ≤
      ‖Z i - Z (nearestNeighbor Z i)‖ := by
  rw [norm_sub_rev (Z i)]
  exact norm_sub_nearestNeighbor_le Z (nearestNeighbor_ne Z i).symm

/-- Tie-break step: if two consecutive edges have equal length and the orbit does not return
after two steps, the index strictly drops two steps later. -/
theorem finSumFinEquiv_nearestNeighbor_nearestNeighbor_lt (Z : Fin N ⊕ Fin N → ℂ)
    {a : Fin N ⊕ Fin N}
    (hd : ‖Z (nearestNeighbor Z a) - Z (nearestNeighbor Z (nearestNeighbor Z a))‖ =
      ‖Z a - Z (nearestNeighbor Z a)‖)
    (hne : nearestNeighbor Z (nearestNeighbor Z a) ≠ a) :
    finSumFinEquiv (nearestNeighbor Z (nearestNeighbor Z a)) < finSumFinEquiv a := by
  refine lt_of_le_of_ne (finSumFinEquiv_nearestNeighbor_le Z (nearestNeighbor_ne Z a).symm ?_)
    (fun h => hne (finSumFinEquiv.injective h))
  rw [norm_sub_rev, hd]

/-- Lexicographic key (edge length, index) of a vertex of the nearest-neighbour graph. -/
private noncomputable def lexKey (Z : Fin N ⊕ Fin N → ℂ) (a : Fin N ⊕ Fin N) : ℝ ×ₗ ℕ :=
  toLex (‖Z a - Z (nearestNeighbor Z a)‖, (finSumFinEquiv a : ℕ))

/-- Either `a` is in a 2-cycle, or two steps of the map strictly decrease the key. -/
private theorem nearestNeighbor_nearestNeighbor_eq_or_key_lt (Z : Fin N ⊕ Fin N → ℂ)
    (a : Fin N ⊕ Fin N) :
    nearestNeighbor Z (nearestNeighbor Z a) = a ∨
      lexKey Z (nearestNeighbor Z (nearestNeighbor Z a)) < lexKey Z a := by
  by_cases hc : nearestNeighbor Z (nearestNeighbor Z a) = a
  · exact Or.inl hc
  right
  have h1 := norm_sub_nearestNeighbor_nearestNeighbor_le Z a
  have h2 := norm_sub_nearestNeighbor_nearestNeighbor_le Z (nearestNeighbor Z a)
  unfold lexKey
  rw [Prod.Lex.toLex_lt_toLex]
  by_cases hlt : ‖Z (nearestNeighbor Z (nearestNeighbor Z a)) -
      Z (nearestNeighbor Z (nearestNeighbor Z (nearestNeighbor Z a)))‖ <
        ‖Z a - Z (nearestNeighbor Z a)‖
  · exact Or.inl hlt
  right
  have hd1 : ‖Z (nearestNeighbor Z (nearestNeighbor Z a)) -
      Z (nearestNeighbor Z (nearestNeighbor Z (nearestNeighbor Z a)))‖ =
        ‖Z a - Z (nearestNeighbor Z a)‖ := by
    refine le_antisymm ?_ (not_lt.1 hlt)
    exact h2.trans h1
  have hd2 : ‖Z (nearestNeighbor Z a) - Z (nearestNeighbor Z (nearestNeighbor Z a))‖ =
      ‖Z a - Z (nearestNeighbor Z a)‖ := by
    refine le_antisymm h1 ?_
    rw [← hd1]
    exact h2
  refine ⟨hd1, ?_⟩
  exact_mod_cast finSumFinEquiv_nearestNeighbor_nearestNeighbor_lt Z hd2 hc

/-- All cycles of the nearest-neighbour map are 2-cycles: a periodic point `i` of `φ₁` satisfies
`φ₁ (φ₁ i) = i`. This holds for every configuration, thanks to the index tie-break (source
l. 202–207, ruling R4). -/
theorem nearestNeighbor_nearestNeighbor_of_iterate_eq_self (Z : Fin N ⊕ Fin N → ℂ)
    {i : Fin N ⊕ Fin N} {n : ℕ} (hn : 0 < n) (h : (nearestNeighbor Z)^[n] i = i) :
    nearestNeighbor Z (nearestNeighbor Z i) = i := by
  have hper : Function.IsPeriodicPt (nearestNeighbor Z) n i := h
  -- the key attains its minimum on the cycle at some `φ^[k] i`
  obtain ⟨k, hk, hmin⟩ := (Finset.range n).exists_min_image
    (fun k => lexKey Z ((nearestNeighbor Z)^[k] i)) ⟨0, Finset.mem_range.2 hn⟩
  set a := (nearestNeighbor Z)^[k] i with ha
  -- the minimizer lies in a 2-cycle
  have ha2 : nearestNeighbor Z (nearestNeighbor Z a) = a := by
    refine (nearestNeighbor_nearestNeighbor_eq_or_key_lt Z a).resolve_right (not_lt.2 ?_)
    have hmem : (k + 2) % n ∈ Finset.range n := Finset.mem_range.2 (Nat.mod_lt _ hn)
    have := hmin _ hmem
    rw [hper.iterate_mod_apply] at this
    have e : (nearestNeighbor Z)^[k + 2] i = nearestNeighbor Z (nearestNeighbor Z a) := by
      rw [add_comm, Function.iterate_add_apply]
      rfl
    rwa [e] at this
  -- `i` is in the forward orbit of `a`, hence also lies in this 2-cycle
  have hper2 : Function.IsPeriodicPt (nearestNeighbor Z) 2 a := ha2
  have hi : (nearestNeighbor Z)^[(n - 1) * k] a = i := by
    rw [ha, ← Function.iterate_add_apply]
    have : (n - 1) * k + k = n * k := by
      cases n with
      | zero => omega
      | succ m => simp [Nat.succ_mul]
    rw [this]
    exact (hper.mul_const k).eq
  rw [← hper2.iterate_mod_apply] at hi
  rw [← hi]
  have e : nearestNeighbor Z (nearestNeighbor Z ((nearestNeighbor Z)^[(n - 1) * k % 2] a)) =
      (nearestNeighbor Z)^[(n - 1) * k % 2] (nearestNeighbor Z (nearestNeighbor Z a)) := by
    have comm : ∀ (x : Fin N ⊕ Fin N) (r : ℕ), (nearestNeighbor Z)^[2] ((nearestNeighbor Z)^[r] x) =
        (nearestNeighbor Z)^[r] ((nearestNeighbor Z)^[2] x) := fun x r => by
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, add_comm]
    exact comm a _
  rw [e, ha2]

/-- Every orbit of the nearest-neighbour map reaches a 2-cycle after at most `2N` steps. -/
theorem exists_iterate_nearestNeighbor_two_cycle (Z : Fin N ⊕ Fin N → ℂ) (i : Fin N ⊕ Fin N) :
    ∃ m ≤ 2 * N, nearestNeighbor Z (nearestNeighbor Z ((nearestNeighbor Z)^[m] i)) =
      (nearestNeighbor Z)^[m] i := by
  have hcard : Fintype.card (Fin N ⊕ Fin N) < Fintype.card (Fin (2 * N + 1)) := by
    simp [two_mul]
  obtain ⟨p, q, hpq, hfpq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (2 * N + 1) => (nearestNeighbor Z)^[(k : ℕ)] i) hcard
  -- WLOG `p < q`
  have aux : ∀ p q : Fin (2 * N + 1), (p : ℕ) < q →
      (nearestNeighbor Z)^[(p : ℕ)] i = (nearestNeighbor Z)^[(q : ℕ)] i →
        ∃ m ≤ 2 * N, nearestNeighbor Z (nearestNeighbor Z ((nearestNeighbor Z)^[m] i)) =
          (nearestNeighbor Z)^[m] i := by
    intro p q hlt heq
    refine ⟨p, Nat.lt_succ_iff.1 p.2, ?_⟩
    refine nearestNeighbor_nearestNeighbor_of_iterate_eq_self Z (n := (q : ℕ) - p)
      (Nat.sub_pos_of_lt hlt) ?_
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact heq.symm
  rcases lt_trichotomy (p : ℕ) q with hlt | heq | hgt
  · exact aux p q hlt hfpq
  · exact absurd (Fin.ext heq) hpq
  · exact aux q p hgt hfpq.symm

end TwoComponentCoulomb

end
