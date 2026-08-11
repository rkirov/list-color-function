/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.PathCount

/-!
# Paths are greedily colorable, and Lemma 4 of Kirov–Naimi

Kirov–Naimi, *List coloring and `n`-monophilic graphs* (arXiv:1004.5183), use throughout §3 the
fact that a path is *degenerate*: colors can be chosen greedily from one end to the other, so a
path can be colored from any list assignment giving two colors to every vertex — even after
prescribing the color of one vertex.

This file proves that in the shape needed later, and deduces the paper's Lemma 4:

> Let `L` and `L'` be distinct list assignments for a path `P` such that `L(v) ⊆ L'(v)` for every
> vertex and `|L'(v)| ≥ 2` for every `v`. Then `col(P, L) < col(P, L')`.

The easy half, `col(P, L) ≤ col(P, L')`, is `SimpleGraph.col_le_col_of_subset` and holds for every
graph. Strictness is what needs the path structure: one must exhibit an `L'`-coloring that is not
an `L`-coloring, i.e. one realizing a color of `L'(w) \ L(w)` at a vertex `w` where the two
assignments differ, and that is exactly `ListColoring.colFix_pos_of_two_le_card`.

Both colorability statements are proved by induction on the length of the path, peeling off the
pendant endpoint. The inductive steps are isolated as statements about `G.addPendant v₀` for an
arbitrary graph `G` (`SimpleGraph.col_addPendant_pos`, `SimpleGraph.colFix_none_addPendant_pos`,
`SimpleGraph.colFix_some_addPendant_pos`), which is both cleaner and what keeps the two
descriptions `PathV (k+1)` and `Option (PathV k)` of the vertex type from getting in the way.

## Main results

* `ListColoring.col_pos_of_one_le_card_pathEnd` : a path can be colored from any list assignment
  with at least one color at `pathEnd` and at least two colors everywhere else
* `ListColoring.colFix_pos_of_two_le_card` : with at least two colors at every vertex, a path can be
  colored with any prescribed color at any prescribed vertex
* `ListColoring.col_lt_col_of_ssubset` : **Lemma 4** of Kirov–Naimi
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Greedily colouring across a pendant vertex

The three lemmas of this section are the inductive step of the two colorability results below,
stated for an arbitrary graph with a pendant vertex attached. -/

/-- Prescribing a color can only cut down the colorings. -/
lemma colFix_le_col (L : ListAssignment V) (v : V) (c : ℕ) : G.colFix L v c ≤ G.col L :=
  card_le_card (Finset.filter_subset _ _)

omit [Fintype V] in
/-- The list assignment induced on `G` by giving the color `c` to the pendant vertex of
`G.addPendant v₀`: only the attachment point `v₀` loses the color `c`. -/
lemma inducedList_addPendant (v₀ : V) (L : ListAssignment (Option V)) (c : ℕ) (w : V) :
    (G.addPendant v₀).inducedList L c w =
      if w = v₀ then (L (some w)).erase c else L (some w) := rfl

/-- **Greedy extension.** A coloring `g` of `G` from the restricted lists `L ∘ some`, together with
a color `d ∈ L none` different from the color of the attachment point `v₀`, is a coloring of
`G.addPendant v₀` from `L`. -/
lemma mem_colorings_addPendant {v₀ : V} {L : ListAssignment (Option V)} {g : V → ℕ}
    (hg : g ∈ G.colorings (fun v => L (some v))) {d : ℕ} (hd : d ∈ L none) (hne : d ≠ g v₀) :
    (fun o => Option.elim o d g) ∈ (G.addPendant v₀).colorings L := by
  rw [mem_colorings] at hg ⊢
  refine ⟨?_, ?_⟩
  · rintro (_ | v)
    · exact hd
    · exact hg.1 v
  · rintro (_ | a) (_ | b) hab
    · exact absurd hab (G.addPendant v₀).irrefl
    · have hb : b = v₀ := (G.addPendant_adj_none_some).mp hab
      subst hb
      exact hne
    · have ha : a = v₀ := (G.addPendant_adj_none_some).mp hab.symm
      subst ha
      exact hne.symm
    · exact hg.2 ((G.addPendant_adj_some_some).mp hab)

/-- Colorings of `G.addPendant v₀` giving the color `c` to the pendant vertex are colorings of `G`
from the induced lists; in particular there is one as soon as the induced lists have one. -/
theorem colFix_none_addPendant_pos (v₀ : V) (L : ListAssignment (Option V)) {c : ℕ}
    (hc : c ∈ L none) (h : 0 < G.col ((G.addPendant v₀).inducedList L c)) :
    0 < (G.addPendant v₀).colFix L none c := by
  rw [colFix_none_eq_col_delNone _ L hc]
  exact h

/-- If the lists induced by some color of the pendant vertex allow a coloring of `G`, then
`G.addPendant v₀` is colorable. -/
theorem col_addPendant_pos (v₀ : V) (L : ListAssignment (Option V)) {c : ℕ}
    (hc : c ∈ L none) (h : 0 < G.col ((G.addPendant v₀).inducedList L c)) :
    0 < (G.addPendant v₀).col L :=
  lt_of_lt_of_le (colFix_none_addPendant_pos G v₀ L hc h) (colFix_le_col _ _ _ _)

/-- Prescribing a color at an *old* vertex: color `G` first, then give the pendant vertex one of
its at least two colors avoiding the color of the attachment point. -/
theorem colFix_some_addPendant_pos (v₀ : V) (L : ListAssignment (Option V)) {w : V} {c : ℕ}
    (hL : 2 ≤ (L none).card) (h : 0 < G.colFix (fun v => L (some v)) w c) :
    0 < (G.addPendant v₀).colFix L (some w) c := by
  rw [colFix, Finset.card_pos] at h ⊢
  obtain ⟨g, hgmem⟩ := h
  rw [Finset.mem_filter] at hgmem
  obtain ⟨d, hd, hdne⟩ := Finset.exists_mem_ne hL (g v₀)
  exact ⟨fun o => Option.elim o d g,
    Finset.mem_filter.mpr ⟨mem_colorings_addPendant G hgmem.1 hd hdne, hgmem.2⟩⟩

end SimpleGraph

namespace ListColoring

open SimpleGraph

/-- No vertex of `pathG (k+1)` inherited from `pathG k` is its endpoint. -/
lemma some_ne_pathEnd_succ {k : ℕ} (v : PathV k) : (some v : PathV (k + 1)) ≠ pathEnd (k + 1) := by
  show (some v : Option (PathV k)) ≠ none
  exact Option.some_ne_none v

/-! ### Greedy colorability, with one weak end -/

/-- **A path is greedily colorable.** If the endpoint `pathEnd k` has at least one available color
and every other vertex has at least two, then the path of length `k` has a coloring: color the far
end first and work towards `pathEnd k`, at each step at most one color being blocked by the
already-colored neighbor. -/
theorem col_pos_of_one_le_card_pathEnd :
    ∀ (k : ℕ) (L : ListAssignment (PathV k)), 1 ≤ (L (pathEnd k)).card →
      (∀ v, v ≠ pathEnd k → 2 ≤ (L v).card) → 0 < (pathG k).col L := by
  intro k
  induction k with
  | zero =>
    intro L hend _
    rw [col_pathG_zero, Subsingleton.elim (default : PathV 0) (pathEnd 0)]
    exact hend
  | succ k ih =>
    intro L hend hrest
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hend
    refine col_addPendant_pos (pathG k) (pathEnd k) L hc (ih _ ?_ ?_)
    · -- the new endpoint lost at most one color from a list of size at least two
      -- `rw [inducedList_addPendant]` no longer matches: the goal carries a different (though
      -- defeq) `DecidableRel` instance than the lemma's, and `rw` matches syntactically. Naming
      -- the equation instead works, because `inducedList_addPendant` is definitional and the
      -- ascription is checked at default transparency.
      have e : ((pathG k).addPendant (pathEnd k)).inducedList L c (pathEnd k)
          = (L (some (pathEnd k))).erase c := if_pos rfl
      rw [e]
      have h2 : 2 ≤ (L (some (pathEnd k))).card := hrest _ (some_ne_pathEnd_succ _)
      have h1 := Finset.pred_card_le_card_erase (s := L (some (pathEnd k))) (a := c)
      omega
    · -- every other vertex keeps its whole list
      intro v hv
      have e : ((pathG k).addPendant (pathEnd k)).inducedList L c v = L (some v) := if_neg hv
      rw [e]
      exact hrest _ (some_ne_pathEnd_succ v)

/-! ### Greedy colorability, with a prescribed color -/

/-- **A path is colorable with a prescribed color.** If every vertex of a path has at least two
available colors, then for every vertex `w` and every color `c ∈ L w` there is a coloring of the
path from `L` giving the color `c` to `w`. -/
theorem colFix_pos_of_two_le_card :
    ∀ (k : ℕ) (L : ListAssignment (PathV k)), (∀ v, 2 ≤ (L v).card) →
      ∀ (w : PathV k) (c : ℕ), c ∈ L w → 0 < (pathG k).colFix L w c := by
  intro k
  induction k with
  | zero =>
    intro L _ w c hc
    rw [colFix, Finset.card_pos]
    refine ⟨fun _ => c, ?_⟩
    rw [Finset.mem_filter, mem_colorings]
    refine ⟨⟨fun v => ?_, ?_⟩, rfl⟩
    · show c ∈ L v
      rw [Subsingleton.elim v w]
      exact hc
    · intro a b hab
      exact absurd hab (by simp [pathG])
  | succ k ih =>
    intro L hcard w c hc
    match w with
    | none =>
      -- prescribing a color at the endpoint is deletion; then color greedily
      refine colFix_none_addPendant_pos (pathG k) (pathEnd k) L hc
        (col_pos_of_one_le_card_pathEnd k _ ?_ ?_)
      · have e : ((pathG k).addPendant (pathEnd k)).inducedList L c (pathEnd k)
            = (L (some (pathEnd k))).erase c := if_pos rfl
        rw [e]
        have h2 := hcard (some (pathEnd k))
        have h1 := Finset.pred_card_le_card_erase (s := L (some (pathEnd k))) (a := c)
        omega
      · intro v hv
        have e : ((pathG k).addPendant (pathEnd k)).inducedList L c v = L (some v) := if_neg hv
        rw [e]
        exact hcard (some v)
    | some w' =>
      -- color the shorter path first, then extend over the endpoint
      exact colFix_some_addPendant_pos (pathG k) (pathEnd k) L (hcard none)
        (ih (fun v => L (some v)) (fun v => hcard (some v)) w' c hc)

/-! ### Lemma 4 -/

/-- **Lemma 4 of Kirov–Naimi.** For a path, enlarging the lists *strictly* increases the number of
colorings, provided the larger assignment gives at least two colors to every vertex.

The inclusion `colorings L ⊆ colorings L'` is `SimpleGraph.colorings_subset_colorings`; strictness
comes from `colFix_pos_of_two_le_card`, which produces an `L'`-coloring realizing a color of
`L' w \ L w`. -/
theorem col_lt_col_of_ssubset (k : ℕ) {L L' : ListAssignment (PathV k)}
    (hsub : ∀ v, L v ⊆ L' v) (hne : L ≠ L') (hcard : ∀ v, 2 ≤ (L' v).card) :
    (pathG k).col L < (pathG k).col L' := by
  -- a vertex where the assignments differ, and a color witnessing the difference
  obtain ⟨w, hw⟩ : ∃ w, L w ≠ L' w := by
    by_contra hcon
    push Not at hcon
    exact hne (funext hcon)
  obtain ⟨c, hcL', hcL⟩ : ∃ c ∈ L' w, c ∉ L w := by
    by_contra hcon
    push Not at hcon
    exact hw (Finset.Subset.antisymm (hsub w) hcon)
  -- an `L'`-coloring giving `c` to `w`; it is not an `L`-coloring
  have hpos := colFix_pos_of_two_le_card k L' hcard w c hcL'
  rw [colFix, Finset.card_pos] at hpos
  obtain ⟨f, hf⟩ := hpos
  rw [Finset.mem_filter] at hf
  refine Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset (colorings_subset_colorings hsub)).mpr ⟨f, hf.1, ?_⟩)
  intro hmem
  have := mem_list_of_mem_colorings hmem w
  rw [hf.2] at this
  exact hcL this

end ListColoring
