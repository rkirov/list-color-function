/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Induction

/-!
# The weighted cycle pair theorem (interface)

The single remaining input to the pair-invariant induction (`cactus_pair_bound`): on a cycle
with pair-dominant weights at every non-root vertex, the weighted rooted profile is
pair-bounded by the uniform normalizer times the weight normalizers.

This is UM-106 (the bare pair bound, by the corrected inverse-orientation transfer expansion,
handoff §6.2–6.3) combined with UM-107's peeling (two-valued weights, extension-count slack
`k - 3 ≥ 1`). The statement is pinned here as the interface; the transfer-matrix development
proceeds beneath it.
-/

namespace ListColoring

open SimpleGraph Finset

/-- **The weighted cycle pair theorem** (UM-106 + UM-107, `k ≥ 4`): stated for any graph
isomorphic to `closePath m`, `m ≥ 2`, since that is how cycles arise inside the induction. -/
theorem cycle_pair_bound {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {m : ℕ} (hm : 2 ≤ m) (e : G ≃g closePath m)
    {k : ℕ} (hk : 4 ≤ k) (L : ListAssignment V) (hL : IsNListAssignment L k)
    (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, ∀ c ∈ L v, ∀ d ∈ L v, c ≠ d → (W v) ^ 2 ≤ w v c * w v d)
    (r : V) : ∀ c ∈ L r, ∀ d ∈ L r, c ≠ d →
      (rootedCol G (constList V k) r 0 * ∏ v, W v) ^ 2 ≤
        (rootedWcol G L w r c) * (rootedWcol G L w r d) := by
  sorry

end ListColoring
