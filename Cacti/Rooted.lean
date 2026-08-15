/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Defs

/-!
# Rooted coloring counts

The cactus induction (handoff §4) passes **rooted profiles** up a decomposition: for a rooted
graph, the vector of counts of proper `L`-colorings taking each colour at the root. This file
defines rooted counts and proves the two facts every layer consumes:

* `col_eq_sum_rootedCol` — the total count is the sum of the rooted counts over the root's list;
* rooted counts multiply across unions glued at the root (the cut-vertex product), in the
  concrete `Finset`-bijection form the block induction uses.
-/

namespace ListColoring

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **rooted count**: proper `L`-colorings of `G` giving colour `c` to the root `r`. -/
def rootedCol (L : ListAssignment V) (r : V) (c : ℕ) : ℕ :=
  ((G.colorings L).filter (fun f => f r = c)).card

/-- The total count partitions over the root's list. -/
theorem col_eq_sum_rootedCol (L : ListAssignment V) (r : V) :
    G.col L = ∑ c ∈ L r, rootedCol G L r c :=
  Finset.card_eq_sum_card_fiberwise fun f hf => G.mem_list_of_mem_colorings hf r


section CutVertex

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The cut-vertex product**: when `V` is covered by `A` and `B` meeting exactly at the root
`r`, with every edge inside `A` or inside `B`, rooted counts multiply. -/
theorem rootedCol_mul_of_cut {A B : Set V} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {r : V} (hrA : r ∈ A) (hrB : r ∈ B) (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hmeet : ∀ v, v ∈ A → v ∈ B → v = r)
    (hedge : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (L : ListAssignment V) (c : ℕ) :
    rootedCol G L r c =
      rootedCol (G.induce A) (fun v => L v) ⟨r, hrA⟩ c *
        rootedCol (G.induce B) (fun v => L v) ⟨r, hrB⟩ c := by
  rw [rootedCol, rootedCol, rootedCol, ← Finset.card_product]
  refine Finset.card_bij' (fun f _ => (fun v => f v.val, fun v => f v.val))
    (fun p _ => fun v => if hv : v ∈ A then p.1 ⟨v, hv⟩ else p.2 ⟨v, (hcover v).resolve_left hv⟩)
    ?_ ?_ ?_ ?_
  · -- forward membership
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hfc, hfr⟩ := hf
    rw [SimpleGraph.mem_colorings_iff] at hfc
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
      SimpleGraph.mem_colorings_iff, SimpleGraph.mem_colorings_iff]
    exact ⟨⟨⟨fun v => hfc.1 v.val, fun v w hadj => hfc.2 v.val w.val hadj⟩, hfr⟩,
      ⟨⟨fun v => hfc.1 v.val, fun v w hadj => hfc.2 v.val w.val hadj⟩, hfr⟩⟩
  · -- backward membership
    intro p hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
      SimpleGraph.mem_colorings_iff, SimpleGraph.mem_colorings_iff] at hp
    obtain ⟨⟨⟨h1mem, h1prop⟩, h1r⟩, ⟨⟨h2mem, h2prop⟩, h2r⟩⟩ := hp
    -- coherence: on `B` the glued function is the second component
    have hglueB : ∀ (v : V) (hv : v ∈ B),
        (if hv' : v ∈ A then p.1 ⟨v, hv'⟩ else p.2 ⟨v, (hcover v).resolve_left hv'⟩)
          = p.2 ⟨v, hv⟩ := by
      intro v hv
      by_cases hv' : v ∈ A
      · rw [dif_pos hv']
        have hveq : v = r := hmeet v hv' hv
        subst hveq
        rw [h1r, ← h2r]
      · rw [dif_neg hv']
    rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v
      by_cases hv : v ∈ A
      · rw [dif_pos hv]; exact h1mem ⟨v, hv⟩
      · rw [dif_neg hv]; exact h2mem _
    · intro v w hadj
      rcases hedge v w hadj with ⟨hvA, hwA⟩ | ⟨hvB, hwB⟩
      · rw [dif_pos hvA, dif_pos hwA]
        exact h1prop ⟨v, hvA⟩ ⟨w, hwA⟩ hadj
      · rw [hglueB v hvB, hglueB w hwB]
        exact h2prop ⟨v, hvB⟩ ⟨w, hwB⟩ hadj
    · show (if hv : r ∈ A then p.1 ⟨r, hv⟩ else p.2 ⟨r, (hcover r).resolve_left hv⟩) = c
      rw [dif_pos hrA]; exact h1r
  · -- left inverse
    intro f hf
    funext v
    by_cases hv : v ∈ A
    · rw [dif_pos hv]
    · rw [dif_neg hv]
  · -- right inverse
    intro p hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨_, h1r⟩, ⟨_, h2r⟩⟩ := hp
    have hglueB : ∀ (v : V) (hvA : v ∈ A) (hv : v ∈ B), p.1 ⟨v, hvA⟩ = p.2 ⟨v, hv⟩ := by
      intro v hvA hv
      have hveq : v = r := hmeet v hvA hv
      subst hveq
      rw [h1r, ← h2r]
    refine Prod.ext ?_ ?_
    · funext v
      show (if hv : v.val ∈ A then _ else _) = p.1 v
      rw [dif_pos v.property]
    · funext v
      show (if hv : v.val ∈ A then _ else _) = p.2 v
      by_cases hv : v.val ∈ A
      · rw [dif_pos hv]
        exact hglueB v.val hv v.property
      · rw [dif_neg hv]

end CutVertex

end ListColoring
