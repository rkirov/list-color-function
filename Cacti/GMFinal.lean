/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.LargeBranch

/-!
# The `k = 3` block induction, completed

`cycle_gm_bound_even` (UM-104) is proved here from its three cases — `C₄`
(`cycle_gm_bound_even_at_three`), `C₆` (`branch_six`, UM-096) and `m ≥ 7` (`branch_large`) —
through the trichotomy assembly `cycle_gm_bound_even_of_branches`. The GM induction and the
cycle block that consume it follow, so no step of the `k = 3` route is left unproved.
-/

namespace ListColoring

open SimpleGraph Finset

section Final

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **UM-104**: the full tensor capacity of an even cycle, from its three cases. -/
theorem cycle_gm_bound_even {m : ℕ} (hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (hpar : Even (m + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) :
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3 ≤
      ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c :=
  cycle_gm_bound_even_of_branches branch_six branch_large hm ix hadj hpar L hL w W hdom

/-- **The cycle block at `k = 3`** (UM-104 for even cycles, UM-025 for odd): on a cycle with
GM-dominant weights the rooted profile clears the cube of the uniform normalizer. This is the
full tensor capacity of a cycle — handoff §5.2–§5.6 — and the one mathematical input of the
`k = 3` classification that the `k ≥ 4` route does not already supply. -/
theorem cycle_gm_bound {m : ℕ} (hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) :
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3 ≤
      ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c := by
  rcases Nat.even_or_odd (m + 1) with hpar | hpar
  · exact cycle_gm_bound_even hm ix hadj hpar L hL w W hdom
  · -- odd cycles: the balanced core, through `gm_bound_of_balanced`
    obtain ⟨S, hS, hbal⟩ := exists_balanced_core_odd hm ix hadj hpar L hL
    have hApos : 0 < rootedCol G (constList V 3) (ix 0) 0 := by
      rw [rootedCol_constList_cycle (by omega) ix hadj, uniformA]
      have hb := one_le_beta (by omega : 3 ≤ 3) m (by omega)
      have : (0:ℕ) < 3 - 1 := by omega
      exact Nat.mul_pos this hb
    exact gm_bound_of_balanced hApos L hL w W hdom S hS hbal (ix 0)

end Final

/-- **The GM-invariant induction at `k = 3`** (UM-105, handoff §5.6): on a cactus with
GM-dominant weights, the weighted rooted profile has product at least the cube of the uniform
normalizer times the weight normalizers.

The case split is `exists_cut_split_or_cyclic_index_of_three_le`: the one-vertex base, the
single-edge base (`gm_edge_base`), the cut-vertex step (`gm_bound_of_cut`, with two uses of the
induction hypothesis), and the cycle blocks (`cycle_gm_bound`). -/
theorem cactus_gm_bound :
    ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → IsCactus G →
      ∀ (L : ListAssignment V), IsNListAssignment L 3 →
      ∀ (w : V → ℕ → ℕ) (W : V → ℕ),
        (∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) →
      ∀ r : V,
        (rootedCol G (constList V 3) r 0 * ∏ v, W v) ^ 3 ≤
          ∏ c ∈ L r, rootedWcol G L w r c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V _ _ G _ hcard hG L hL w W hdom r
    rcases Nat.lt_or_ge n 2 with hn | hn
    · -- one vertex: the invariant is the weight dominance at the root
      have h1 : Fintype.card V = 1 := by
        have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
        omega
      have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h1)
      have hprodV : (∏ v, W v) = W r := by
        rw [show (Finset.univ : Finset V) = {r} from by
          ext v; simp [Subsingleton.elim v r]]
        rw [Finset.prod_singleton]
      have hA : rootedCol G (constList V 3) r 0 = 1 := by
        have h0 : (0 : ℕ) ∈ constList V 3 r := by
          simp [constList_apply, Finset.mem_range]
        have h2 := rootedWcol_of_card_eq_one (G := G) h1 (constList V 3) (fun _ _ => 1) r h0
        rw [rootedWcol_one] at h2
        exact h2
      rw [hA, hprodV, one_mul,
        Finset.prod_congr rfl (fun c hc => rootedWcol_of_card_eq_one h1 L w r hc)]
      exact hdom r
    · rcases Nat.lt_or_ge n 3 with hn2 | hn3
      · -- two vertices: a single edge
        exact gm_edge_base (by omega) hG L hL w W hdom r
      · rcases exists_cut_split_or_cyclic_index_of_three_le hG (by omega) r with
          ⟨u, A, B, dA, dB, hrA, huA, huB, hcover, hmeet, hedge, ⟨a, haA, hau⟩,
            ⟨b, hbB, hbu⟩, hcA, hcB⟩ | ⟨m, ix, hm, hix0, hadj⟩
        · -- a cut vertex: absorb the `B` side and recurse on both
          have hbA : b ∉ A := fun h => hbu (hmeet b h hbB)
          have haB : a ∉ B := fun h => hau (hmeet a haA h)
          refine gm_bound_of_cut huA huB hcover hmeet hedge hrA (by omega) L w W hdom ?_ ?_
          · intro wB WB hdomB
            exact IH _ (by rw [← hcard]; exact Fintype.card_subtype_lt (x := a) haB) _
              (G.induce B) rfl hcB _ (fun x => hL x.val) wB WB hdomB ⟨u, huB⟩
          · intro wA WA hdomA
            exact IH _ (by rw [← hcard]; exact Fintype.card_subtype_lt (x := b) hbA) _
              (G.induce A) rfl hcA _ (fun v => hL v.val) wA WA hdomA ⟨r, hrA⟩
        · -- a single cycle
          rw [← hix0]
          exact cycle_gm_bound hm ix hadj L hL w W hdom






end ListColoring
