/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Basic

/-!
# Deleting a vertex and the induced list assignment

Kirov–Naimi (p. 4) introduce, for a list assignment `L` on `G`, vertices `v₁, …, v_k` and colors
`cᵢ ∈ L(vᵢ)`, the list assignment **induced** by `L, c₁, …, c_k` on `H = G − {v₁,…,v_k}`, given by
deleting `cᵢ` from the list of every neighbor of `vᵢ`. The point of the construction is the identity

  `col(G, L, v₁, c₁, …, v_k, c_k) = col(H, L_{c₁,…,c_k})`,

which is the engine of every counting argument in the paper.

We formalize the one-vertex case, which is what the arguments iterate. The vertex being deleted is
`none : Option V`, so that the graph after deletion is `H.comap some`, a graph on `V` itself — no
subtypes and no transport of `Fintype` instances.

## Main results

* `SimpleGraph.colFix_none_eq_col_delNone` : `col(G, M, none, c) = col(G − none, M_c)`
* `SimpleGraph.col_eq_sum_delNone` : `col(G, M) = ∑ c ∈ M none, col(G − none, M_c)`
-/

open Finset

-- Several helper lemmas below do not use the ambient `Fintype`/`DecidableEq` instances.
set_option linter.unusedSectionVars false

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph (Option V)) [DecidableRel H.Adj]

/-- The graph obtained from `H` by deleting the vertex `none`. -/
abbrev delNone : SimpleGraph V := H.comap some

instance : DecidableRel (H.delNone).Adj :=
  fun a b => inferInstanceAs (Decidable (H.Adj (some a) (some b)))

@[simp] lemma delNone_adj {a b : V} : (H.delNone).Adj a b ↔ H.Adj (some a) (some b) := Iff.rfl

/-- The list assignment induced on `H − none` by assigning the color `c` to `none`: the color `c`
becomes unavailable at every neighbor of `none`. -/
def inducedList (M : ListAssignment (Option V)) (c : ℕ) : ListAssignment V :=
  fun v => if H.Adj none (some v) then (M (some v)).erase c else M (some v)

lemma inducedList_subset (M : ListAssignment (Option V)) (c : ℕ) (v : V) :
    H.inducedList M c v ⊆ M (some v) := by
  unfold inducedList
  split
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

lemma mem_inducedList_iff {M : ListAssignment (Option V)} {c : ℕ} {v : V} {x : ℕ} :
    x ∈ H.inducedList M c v ↔ x ∈ M (some v) ∧ (H.Adj none (some v) → x ≠ c) := by
  unfold inducedList
  split <;> simp_all [Finset.mem_erase, and_comm]

/-- The list induced at a neighbor of the deleted vertex has one fewer color, provided the deleted
color was there to begin with. -/
lemma card_inducedList_of_adj {M : ListAssignment (Option V)} {c : ℕ} {v : V}
    (hadj : H.Adj none (some v)) (hc : c ∈ M (some v)) :
    (H.inducedList M c v).card = (M (some v)).card - 1 := by
  rw [inducedList, if_pos hadj, Finset.card_erase_of_mem hc]

lemma card_inducedList_of_not_adj {M : ListAssignment (Option V)} {c : ℕ} {v : V}
    (hadj : ¬ H.Adj none (some v)) :
    (H.inducedList M c v).card = (M (some v)).card := by
  rw [inducedList, if_neg hadj]

/-- **The deletion identity.** Colorings of `H` from `M` that give the color `c` to `none`
correspond exactly to colorings of `H − none` from the induced list assignment. -/
theorem colFix_none_eq_col_delNone (M : ListAssignment (Option V)) {c : ℕ} (hc : c ∈ M none) :
    H.colFix M none c = (H.delNone).col (H.inducedList M c) := by
  rw [colFix, col]
  refine Finset.card_bij'
    (fun f _ v => f (some v))
    (fun g _ o => Option.elim o c g)
    ?_ ?_ ?_ ?_
  · -- restriction of a coloring is a coloring from the induced lists
    intro f hf
    rw [Finset.mem_filter, mem_colorings] at hf
    obtain ⟨⟨hmem, hprop⟩, hnone⟩ := hf
    rw [mem_colorings]
    refine ⟨fun v => (mem_inducedList_iff H).mpr ⟨hmem (some v), fun hadj => ?_⟩, ?_⟩
    · exact hnone ▸ (hprop hadj).symm
    · intro a b hab
      exact hprop hab
  · -- extending by `c` at `none` gives a coloring of `H`
    intro g hg
    rw [mem_colorings] at hg
    obtain ⟨hmem, hprop⟩ := hg
    rw [Finset.mem_filter, mem_colorings]
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · rintro (_ | v)
      · exact hc
      · exact inducedList_subset H M c v (hmem v)
    · rintro (_ | a) (_ | b) hab
      · exact absurd hab H.irrefl
      · exact fun hcon => ((mem_inducedList_iff H).mp (hmem b)).2 hab hcon.symm
      · exact fun hcon => ((mem_inducedList_iff H).mp (hmem a)).2 hab.symm hcon
      · exact hprop hab
  · -- round trip on colorings of `H`
    intro f hf
    rw [Finset.mem_filter] at hf
    funext o
    cases o with
    | none => exact hf.2.symm
    | some v => rfl
  · intro g _; rfl

/-- Splitting the colorings of `H` according to the color assigned to the deleted vertex. This is
the recursion used throughout Kirov–Naimi §3. -/
theorem col_eq_sum_delNone (M : ListAssignment (Option V)) :
    H.col M = ∑ c ∈ M none, (H.delNone).col (H.inducedList M c) := by
  rw [sum_colFix M none]
  exact Finset.sum_congr rfl fun c hc => colFix_none_eq_col_delNone H M hc

end SimpleGraph
