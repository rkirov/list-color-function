/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.CycleRotate
import ListColoring.Iso
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Theorem 1 on Mathlib's cycle graph

`SimpleGraph.ecc_cycleGraph_of_three_le` restates Kirov–Naimi's Theorem 1
(`ListColoring.ecc_closePath_of_two_le`) on Mathlib's `SimpleGraph.cycleGraph`, so that the
statement depends on no graph construction of this development.  The bridge is
`ListColoring.cycleGraphIsoClosePath`: Mathlib's cycle graph on `k + 1` vertices is `closePath k`,
via the vertex numbering `pathVtxEquiv`.
-/

namespace ListColoring

open SimpleGraph

/-- Mathlib's cycle graph on `k + 1` vertices, `k ≥ 1`, is `closePath k`: the vertex numbered `i`
is `pathVtx k i`, and both adjacencies are cyclic successorship. -/
def cycleGraphIsoClosePath (k : ℕ) (hk : 1 ≤ k) : cycleGraph (k + 1) ≃g closePath k where
  toEquiv := pathVtxEquiv k
  map_rel_iff' := by
    intro a b
    have h1 : (1 : Fin (k + 1)).val = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    show (closePath k).Adj (pathVtx k a.val) (pathVtx k b.val) ↔ _
    rw [closePath_adj_pathVtx_fin hk a b, cycleGraph_adj']
    constructor
    · rintro (h | h)
      · exact Or.inr (by rw [← h, add_sub_cancel_left]; exact h1)
      · exact Or.inl (by rw [← h, add_sub_cancel_left]; exact h1)
    · rintro (h | h)
      · exact Or.inr (sub_eq_iff_eq_add'.mp (Fin.val_injective (h.trans h1.symm))).symm
      · exact Or.inl (sub_eq_iff_eq_add'.mp (Fin.val_injective (h.trans h1.symm))).symm

end ListColoring

namespace SimpleGraph

open ListColoring

/-- **Theorem 1 of Kirov–Naimi: every cycle is enumeratively chromatic-choosable at `n`, for every
`n ≥ 2`.**  `cycleGraph n` is Mathlib's cycle graph on `n` vertices. -/
theorem ecc_cycleGraph_of_three_le {n m : ℕ} (hn : 3 ≤ n) :
    (cycleGraph n).ECCAt (m + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (ecc_iso (cycleGraphIsoClosePath k (by omega)) (m + 2)).mpr
    (ecc_closePath_of_two_le (by omega))

end SimpleGraph

#print axioms SimpleGraph.ecc_cycleGraph_of_three_le
