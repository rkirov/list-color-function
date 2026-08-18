/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
/-
The case-split assembly for `cycle_gm_bound_even` (UM-104).
-/
import Cacti.EvenBase

namespace ListColoring

open Finset SimpleGraph

section Split

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The `C₆` branch** (`m_lean = 5`, note `m = 3`, UM-096) as a hypothesis. -/
abbrev EvenCycleBranchSix (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (ix : Fin (5 + 1) ≃ V),
    (∀ i j : Fin (5 + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1)) →
    ∀ (L : ListAssignment V), IsNListAssignment L 3 → ∀ (w : V → ℕ → ℕ) (W : V → ℕ),
    (∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) →
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3 ≤
      ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c

/-- **The general branch** (`m_lean ≥ 7`, note `m ≥ 4`, handoff §5.3–§5.6) as a hypothesis. -/
abbrev EvenCycleBranchLarge (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ {m : ℕ}, 7 ≤ m → ∀ (ix : Fin (m + 1) ≃ V),
    (∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1)) →
    Even (m + 1) →
    ∀ (L : ListAssignment V), IsNListAssignment L 3 → ∀ (w : V → ℕ → ℕ) (W : V → ℕ),
    (∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) →
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3 ≤
      ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c

/-- Under `Even (m + 1)` and `2 ≤ m`, the only lengths are `m = 3`, `m = 5` and `m ≥ 7`. -/
theorem even_cycle_index_trichotomy {m : ℕ} (hm : 2 ≤ m) (hpar : Even (m + 1)) :
    m = 3 ∨ m = 5 ∨ 7 ≤ m := by
  rw [Nat.even_iff] at hpar
  omega

/-- **UM-104 from its two branches.** With the `C₄` case already proved
(`cycle_gm_bound_even_at_three`), the `C₆` base case and the general `m ≥ 7` argument close
`cycle_gm_bound_even` exactly as stated in `Cacti/Three.lean`. -/
theorem cycle_gm_bound_even_of_branches
    (h5 : EvenCycleBranchSix V G) (h7 : EvenCycleBranchLarge V G)
    {m : ℕ} (hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (hpar : Even (m + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) :
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3 ≤
      ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c := by
  rcases even_cycle_index_trichotomy hm hpar with rfl | rfl | hlarge
  · exact cycle_gm_bound_even_at_three hm ix hadj hpar L hL w W hdom
  · exact h5 ix hadj L hL w W hdom
  · exact h7 hlarge ix hadj hpar L hL w W hdom

/-- The same assembly, with the branches presented in the *literal* shape of the repo statement
(the mirror of `cycle_gm_bound_even_at_three`: every hypothesis of `cycle_gm_bound_even`
specialized at `m = 5`, resp. carried along at `7 ≤ m`).  A branch lemma proved in that shape
applies here with no massaging at all. -/
theorem cycle_gm_bound_even_of_branches'
    (h5 : ∀ (_hm : 2 ≤ 5) (ix : Fin (5 + 1) ≃ V),
      (∀ i j : Fin (5 + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1)) →
      Even (5 + 1) → ∀ (L : ListAssignment V), IsNListAssignment L 3 →
      ∀ (w : V → ℕ → ℕ) (W : V → ℕ), (∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) →
      (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3 ≤
        ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c)
    (h7 : ∀ {m : ℕ}, 7 ≤ m → ∀ (_hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V),
      (∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1)) →
      Even (m + 1) → ∀ (L : ListAssignment V), IsNListAssignment L 3 →
      ∀ (w : V → ℕ → ℕ) (W : V → ℕ), (∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) →
      (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3 ≤
        ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c)
    {m : ℕ} (hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (hpar : Even (m + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) :
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3 ≤
      ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c := by
  refine cycle_gm_bound_even_of_branches ?_ ?_ hm ix hadj hpar L hL w W hdom
  · intro ix hadj L hL w W hdom
    exact h5 (by omega) ix hadj (by decide) L hL w W hdom
  · intro m hlarge ix hadj hpar L hL w W hdom
    exact h7 hlarge (by omega) ix hadj hpar L hL w W hdom

#print axioms cycle_gm_bound_even_of_branches
#print axioms cycle_gm_bound_even_of_branches'

end Split

end ListColoring
