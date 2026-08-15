/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Weighted

/-!
# The absorption lemma

The single decomposition step of the block induction: when a piece `B` of the graph hangs off
the rest `A` at a cut vertex `u`, and the root lies in `A`, the whole piece is **absorbed**
into the weight at `u` — the new weight of colour `d` at `u` is the old one times the
`B`-side rooted weighted count at colour `d` (with `u`'s own weight charged to the `A` side).

Pendant vertices, bridges, and leaf cycles are all instances.
-/

namespace ListColoring

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Absorption**: with `V` covered by `A ∪ B` meeting exactly at `u`, all edges inside a
side, and the root `r` in `A`, the rooted weighted count of `G` is that of `G.induce A` with
the weight at `u` multiplied by the `B`-side profile. -/
theorem rootedWcol_absorb {A B : Set V} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {u : V} (huA : u ∈ A) (huB : u ∈ B) (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hmeet : ∀ v, v ∈ A → v ∈ B → v = u)
    (hedge : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    {r : V} (hrA : r ∈ A)
    (L : ListAssignment V) (w : V → ℕ → ℕ) (c : ℕ) :
    letI : DecidableRel (G.induce A).Adj := fun a b => inferInstanceAs (Decidable (G.Adj a b))
    letI : DecidableRel (G.induce B).Adj := fun a b => inferInstanceAs (Decidable (G.Adj a b))
    rootedWcol G L w r c =
      rootedWcol (G.induce A) (fun v => L v)
        (fun v d => if v.val = u then
            w u d * rootedWcol (G.induce B) (fun x => L x)
              (fun x e => if x.val = u then 1 else w x.val e) ⟨u, huB⟩ d
          else w v.val d) ⟨r, hrA⟩ c := by
  letI : DecidableRel (G.induce A).Adj := fun a b => inferInstanceAs (Decidable (G.Adj a b))
  letI : DecidableRel (G.induce B).Adj := fun a b => inferInstanceAs (Decidable (G.Adj a b))
  set wB : B → ℕ → ℕ := fun x e => if x.val = u then 1 else w x.val e with hwB
  set msg : ℕ → ℕ := fun d =>
    rootedWcol (G.induce B) (fun x => L x) wB ⟨u, huB⟩ d with hmsg
  -- Step 1: the global sum equals the sum over matched pairs.
  have step1 : rootedWcol G L w r c =
      ∑ g ∈ ((G.induce A).colorings (fun v => L v)).filter (fun g => g ⟨r, hrA⟩ = c),
        (∏ v, w v.val (g v)) * msg (g ⟨u, huA⟩) := by
    rw [rootedWcol]
    -- expand msg as an inner filtered sum and turn the double sum into a sum over pairs
    simp only [hmsg, rootedWcol, Finset.mul_sum]
    rw [Finset.sum_sigma']
    -- bijection between colorings of `G` fixing `r ↦ c` and matched pairs
    refine Finset.sum_nbij' (fun f => ⟨fun v => f v.val, fun v => f v.val⟩)
      (fun p => fun v => if hv : v ∈ A then p.1 ⟨v, hv⟩ else p.2 ⟨v, (hcover v).resolve_left hv⟩)
      ?_ ?_ ?_ ?_ ?_
    · -- forward membership
      intro f hf
      rw [Finset.mem_filter] at hf
      obtain ⟨hfc, hfr⟩ := hf
      rw [SimpleGraph.mem_colorings_iff] at hfc
      rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter,
        SimpleGraph.mem_colorings_iff, SimpleGraph.mem_colorings_iff]
      exact ⟨⟨⟨fun v => hfc.1 v.val, fun v x hadj => hfc.2 v.val x.val hadj⟩, hfr⟩,
        ⟨⟨fun v => hfc.1 v.val, fun v x hadj => hfc.2 v.val x.val hadj⟩, rfl⟩⟩
    · -- backward membership
      intro p hp
      rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter,
        SimpleGraph.mem_colorings_iff, SimpleGraph.mem_colorings_iff] at hp
      obtain ⟨⟨⟨h1mem, h1prop⟩, h1r⟩, ⟨⟨h2mem, h2prop⟩, h2u⟩⟩ := hp
      have hglueB : ∀ (v : V) (hv : v ∈ B),
          (if hv' : v ∈ A then p.1 ⟨v, hv'⟩ else p.2 ⟨v, (hcover v).resolve_left hv'⟩)
            = p.2 ⟨v, hv⟩ := by
        intro v hv
        by_cases hv' : v ∈ A
        · rw [dif_pos hv']
          have hveq : v = u := hmeet v hv' hv
          subst hveq
          rw [h2u]
        · rw [dif_neg hv']
      rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro v
        by_cases hv : v ∈ A
        · rw [dif_pos hv]; exact h1mem ⟨v, hv⟩
        · rw [dif_neg hv]; exact h2mem _
      · intro v x hadj
        rcases hedge v x hadj with ⟨hvA, hxA⟩ | ⟨hvB, hxB⟩
        · rw [dif_pos hvA, dif_pos hxA]
          exact h1prop ⟨v, hvA⟩ ⟨x, hxA⟩ hadj
        · rw [hglueB v hvB, hglueB x hxB]
          exact h2prop ⟨v, hvB⟩ ⟨x, hxB⟩ hadj
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
      rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter] at hp
      obtain ⟨⟨_, h1r⟩, ⟨_, h2u⟩⟩ := hp
      have hcoh : ∀ (v : V) (hvA : v ∈ A) (hv : v ∈ B), p.1 ⟨v, hvA⟩ = p.2 ⟨v, hv⟩ := by
        intro v hvA hv
        have hveq : v = u := hmeet v hvA hv
        subst hveq
        rw [h2u]
      have h1 : (fun (v : A) => (if hv : (v : V) ∈ A then p.1 ⟨v, hv⟩
          else p.2 ⟨v, (hcover v).resolve_left hv⟩)) = p.1 := by
        funext v
        show (if hv : v.val ∈ A then _ else _) = p.1 v
        rw [dif_pos v.property]
      have h2 : (fun (v : B) => (if hv : (v : V) ∈ A then p.1 ⟨v, hv⟩
          else p.2 ⟨v, (hcover v).resolve_left hv⟩)) = p.2 := by
        funext v
        show (if hv : v.val ∈ A then _ else _) = p.2 v
        by_cases hv : v.val ∈ A
        · rw [dif_pos hv]
          exact hcoh v.val hv v.property
        · rw [dif_neg hv]
      exact Sigma.ext h1 (heq_of_eq h2)
    · -- the summand matches
      intro f hf
      have hsplit := prod_split_of_cut huA huB hcover hmeet (fun v => w v (f v))
      rw [hsplit]
  -- Step 2: fold the message into the `A`-side weight.
  rw [step1, rootedWcol]
  refine Finset.sum_congr rfl fun g hg => ?_
  show (∏ v, w v.val (g v)) * msg (g ⟨u, huA⟩)
      = ∏ v : A, (if v.val = u then w u (g v) * msg (g v) else w v.val (g v))
  have hu' : (⟨u, huA⟩ : A) ∈ (Finset.univ : Finset A) := Finset.mem_univ _
  have herase : (∏ x ∈ Finset.univ.erase (⟨u, huA⟩ : A),
        (if x.val = u then w u (g x) * msg (g x) else w x.val (g x)))
      = ∏ x ∈ Finset.univ.erase (⟨u, huA⟩ : A), w x.val (g x) :=
    Finset.prod_congr rfl fun v hv =>
      if_neg (fun h => Finset.ne_of_mem_erase hv (Subtype.ext h))
  rw [← Finset.mul_prod_erase Finset.univ
    (fun v => if v.val = u then w u (g v) * msg (g v) else w v.val (g v)) hu',
    ← Finset.mul_prod_erase Finset.univ (fun v => w v.val (g v)) hu', herase, if_pos rfl]
  ring

end ListColoring
