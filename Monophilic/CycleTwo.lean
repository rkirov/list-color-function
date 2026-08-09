/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.CycleMonophilic

/-!
# Towards the case `n = 2` of Theorem 1 of Kirov–Naimi

`Monophilic.CycleMonophilic` proves Theorem 1 for every `n ≥ 3`, and for `n = 2` on cycles with an
**odd** number of vertices (`Monophilic.monophilic_closePath_of_odd`, where the count `col(C, 2)`
is `0` and the statement is vacuous). This file develops the machinery for the remaining case,
`n = 2` on cycles with an **even** number of vertices.

## Indexing and parity

`closePath k` is `pathG k` together with the single edge joining `pathStart k` to `pathEnd k`, and
has `k + 1` vertices. So an **even** number of vertices means `Odd k`, and the smallest genuine
instance is `closePath 3 = C₄`. Indeed `col(C₄, 2) = 2` while `col(C₃, 2) = 0`; see the `#guard`s
below.

## The structure of the argument (Kirov–Naimi, p. 5–6)

Because `closePath k` and `pathG k` live on the *same* vertex type, the paper's path `Q` — the cycle
with one edge, but not its vertices, removed — is literally `pathG k`, with `v = pathEnd k` and
`w = pathStart k`; no rotation isomorphism is needed. A coloring of the cycle is exactly a coloring
of the path whose two terminal vertices get different colors
(`Monophilic.colorings_closePath_eq_filter`).

For a `2`-list assignment `L` it therefore suffices to show `2 ≤ col(closePath k, L)`, since
`col(closePath k, 2) = 2` for odd `k` (`Monophilic.colConst_closePath_two_of_odd`).

* If `L` is **constant** this is an equality, by renaming invariance
  (`Monophilic.col_closePath_const`).
* If `L` is **not** constant, the paper's *forcing* argument applies. Write
  `reach k L c` for the set of colors that `pathStart k` can receive in a coloring of the path
  giving the color `c` to `pathEnd k`. Each such set is nonempty, and `c` *forces* a color exactly
  when `reach k L c` is a singleton. Propagating along the path
  (`Monophilic.const_of_forall_reach_card_one`) shows that if **every** color of `L (pathEnd k)`
  forces, then `L` is constant. So some `α` has `reach k L α = L (pathStart k)`, of size two, and
  two distinct colorings of the *cycle* can be extracted from that.

## Main results

* `Monophilic.colConst_closePath_two_of_odd` : `col(C, 2) = 2` for a cycle on an even number of
  vertices
* `Monophilic.colorings_closePath_eq_filter` : cycle colorings are the path colorings with distinct
  colors at the two ends
* `Monophilic.const_of_forall_reach_card_one` : **the propagation lemma** — if every color of
  `L (pathEnd k)` forces a color of `L (pathStart k)`, then `L` is constant
* `Monophilic.exists_reach_eq_pathStart` : consequently some color of `L (pathEnd k)` forces nothing
* `Monophilic.two_le_col_closePath_of_ends_ne` : **`2 ≤ col(C, L)`** whenever the two ends of the
  removed edge carry different lists
* `Monophilic.col_closePath_const` : the constant case

## What is missing

The one configuration not covered here is a non-constant `L` with
`L (pathEnd k) = L (pathStart k)`. See the note before
`Monophilic.two_le_col_closePath_of_ends_ne` for exactly where the paper's argument uses
`L(v) ≠ L(w)` and why that hypothesis is not for free in this presentation.
-/

open Finset

namespace Monophilic

open SimpleGraph

/-! ### Numerical sanity checks

`closePath k` has `k + 1` vertices, so an even number of vertices means `Odd k`. -/

#guard Fintype.card (PathV 3) = 4
#guard (closePath 3).colConst 2 = 2      -- `C₄`, four vertices
#guard (closePath 5).colConst 2 = 2      -- `C₆`, six vertices
#guard (closePath 2).colConst 2 = 0      -- `C₃`: not `2`-colorable
#guard (closePath 4).colConst 2 = 0      -- `C₅`: not `2`-colorable

/-- The paper's tight example: on an even cycle, giving `{1,2}` to two *adjacent* vertices and
`{2,3}` to all the others is a non-constant `2`-list assignment realizing the minimum `2`. -/
private def testTight (k : ℕ) : ListAssignment (PathV k) := fun v =>
  if v = pathVtx k 0 ∨ v = pathVtx k 1 then ({1, 2} : Finset ℕ) else ({2, 3} : Finset ℕ)

#guard (closePath 3).col (testTight 3) = 2
#guard (closePath 5).col (testTight 5) = 2
#guard (closePath 3).colConst 2 ≤ (closePath 3).col (testTight 3)
#guard (closePath 5).colConst 2 ≤ (closePath 5).col (testTight 5)

/-! ### `col(C, 2)` for a cycle on an even number of vertices -/

/-- At `n = 2` the two recurrences of Lemma 3 just alternate: `A_k = 1` and `B_k = 0` for even `k`,
`A_k = 0` and `B_k = 1` for odd `k`. -/
lemma pathA_pathB_zero_parity : ∀ k : ℕ,
    pathA 0 k = (if Even k then 1 else 0) ∧ pathB 0 k = (if Even k then 0 else 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [pathA_succ, pathB_succ, h1, h2]
    by_cases he : Even k
    · simp [he, Nat.even_add_one]
    · simp [he, Nat.even_add_one]

/-- **`col(C, 2) = 2` for a cycle on an even number of vertices.** `closePath k` has `k + 1`
vertices, so `Odd k` says that number is even. -/
theorem colConst_closePath_two_of_odd {k : ℕ} (hk : Odd k) : (closePath k).colConst 2 = 2 := by
  have hk1 : 1 ≤ k := hk.pos
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : Even j := by
    rcases Nat.even_or_odd j with h | h
    · exact h
    · exact absurd hk (by simpa [Nat.even_add_one] using h)
  have h := colConst_closePath_succ 0 j
  rw [(pathA_pathB_zero_parity j).1, if_pos hj] at h
  simpa only [zero_add, mul_one] using h

/-! ### Colorings of the cycle are colorings of the path with distinct ends -/

/-- The closing edge of `closePath k`, for `k ≥ 1`. -/
lemma adj_pathEnd_pathStart {k : ℕ} (hk : 1 ≤ k) :
    (closePath k).Adj (pathEnd k) (pathStart k) :=
  (closePath_adj k _ _).mpr (Or.inr ⟨pathEnd_ne_pathStart hk, Or.inr ⟨rfl, rfl⟩⟩)

/-- **A coloring of the cycle is a coloring of the path whose two ends differ.** -/
theorem mem_colorings_closePath_iff {k : ℕ} (hk : 1 ≤ k) {L : ListAssignment (PathV k)}
    {f : PathV k → ℕ} :
    f ∈ (closePath k).colorings L ↔
      f ∈ (pathG k).colorings L ∧ f (pathEnd k) ≠ f (pathStart k) := by
  constructor
  · intro hf
    rw [mem_colorings] at hf
    refine ⟨mem_colorings.mpr ⟨hf.1, ?_⟩, hf.2 (adj_pathEnd_pathStart hk)⟩
    intro a b hab
    exact hf.2 (pathG_le_closePath k hab)
  · rintro ⟨hf, hne⟩
    rw [mem_colorings] at hf ⊢
    refine ⟨hf.1, ?_⟩
    intro a b hab
    rcases (closePath_adj k a b).mp hab with h | ⟨-, h | h⟩
    · exact hf.2 h
    · obtain ⟨rfl, rfl⟩ := h
      exact Ne.symm hne
    · obtain ⟨rfl, rfl⟩ := h
      exact hne

/-- The colorings of the cycle, as a subset of the colorings of the path. -/
theorem colorings_closePath_eq_filter {k : ℕ} (hk : 1 ≤ k) (L : ListAssignment (PathV k)) :
    (closePath k).colorings L
      = ((pathG k).colorings L).filter (fun f => f (pathEnd k) ≠ f (pathStart k)) := by
  ext f
  rw [Finset.mem_filter]
  exact mem_colorings_closePath_iff hk

/-- Two distinct colorings of the path with distinct ends give `2 ≤ col(C, L)`. -/
theorem two_le_col_closePath {k : ℕ} (hk : 1 ≤ k) {L : ListAssignment (PathV k)}
    {f g : PathV k → ℕ} (hf : f ∈ (pathG k).colorings L) (hg : g ∈ (pathG k).colorings L)
    (hfe : f (pathEnd k) ≠ f (pathStart k)) (hge : g (pathEnd k) ≠ g (pathStart k))
    (hfg : f ≠ g) : 2 ≤ (closePath k).col L := by
  have hf' : f ∈ (closePath k).colorings L := (mem_colorings_closePath_iff hk).mpr ⟨hf, hfe⟩
  have hg' : g ∈ (closePath k).colorings L := (mem_colorings_closePath_iff hk).mpr ⟨hg, hge⟩
  have hsub : ({f, g} : Finset (PathV k → ℕ)) ⊆ (closePath k).colorings L := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hf'
    · rw [Finset.mem_singleton] at hx; exact hx ▸ hg'
  have hcard : ({f, g} : Finset (PathV k → ℕ)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hfg), Finset.card_singleton]
  exact hcard ▸ Finset.card_le_card hsub

/-! ### The constant case -/

/-- On a cycle with an even number of vertices, a constant `2`-list assignment realizes the
minimum: it has exactly `col(C, 2) = 2` colorings, by renaming invariance. -/
theorem col_closePath_const {k : ℕ} (hk : Odd k) {s : Finset ℕ} (hs : s.card = 2) :
    (closePath k).col (fun _ => s) = 2 := by
  rw [col_const_eq_colConst hs]
  exact colConst_closePath_two_of_odd hk

/-! ### Reachability along the path

`reach k L c` is the set of colors that the far end `pathStart k` of the path can receive in a
coloring from `L` giving the color `c` to `pathEnd k`. In the language of Kirov–Naimi, `c` *forces*
the color `d` exactly when `reach k L c = {d}`. -/

/-- The colors available at `pathStart k` to a coloring of `pathG k` from `L` that gives the color
`c` to `pathEnd k`. -/
def reach (k : ℕ) (L : ListAssignment (PathV k)) (c : ℕ) : Finset ℕ :=
  (((pathG k).colorings L).filter (fun f => f (pathEnd k) = c)).image (fun f => f (pathStart k))

lemma mem_reach {k : ℕ} {L : ListAssignment (PathV k)} {c d : ℕ} :
    d ∈ reach k L c ↔
      ∃ f ∈ (pathG k).colorings L, f (pathEnd k) = c ∧ f (pathStart k) = d := by
  constructor
  · intro h
    obtain ⟨f, hf, hd⟩ := Finset.mem_image.mp h
    obtain ⟨hf1, hf2⟩ := Finset.mem_filter.mp hf
    exact ⟨f, hf1, hf2, hd⟩
  · rintro ⟨f, hf, h1, h2⟩
    exact Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, h1⟩, h2⟩

lemma reach_subset {k : ℕ} {L : ListAssignment (PathV k)} (c : ℕ) :
    reach k L c ⊆ L (pathStart k) := by
  intro d hd
  obtain ⟨f, hf, -, rfl⟩ := mem_reach.mp hd
  exact mem_list_of_mem_colorings hf _

/-- Every color of `L (pathEnd k)` reaches at least one color at the far end: a path is colorable
with a prescribed color at a prescribed vertex. -/
lemma reach_nonempty {k : ℕ} {L : ListAssignment (PathV k)} (hcard : ∀ v, 2 ≤ (L v).card)
    {c : ℕ} (hc : c ∈ L (pathEnd k)) : (reach k L c).Nonempty := by
  have h := colFix_pos_of_two_le_card k L hcard (pathEnd k) c hc
  rw [colFix, Finset.card_pos] at h
  obtain ⟨f, hf⟩ := h
  rw [Finset.mem_filter] at hf
  exact ⟨f (pathStart k), mem_reach.mpr ⟨f, hf.1, hf.2, rfl⟩⟩

lemma one_le_card_reach {k : ℕ} {L : ListAssignment (PathV k)} (hcard : ∀ v, 2 ≤ (L v).card)
    {c : ℕ} (hc : c ∈ L (pathEnd k)) : 1 ≤ (reach k L c).card :=
  Finset.card_pos.mpr (reach_nonempty hcard hc)

/-! ### The recursion for `reach`

Peeling the pendant endpoint off `pathG (k+1)` expresses `reach (k+1) L c` as the union of the
`reach k (L ∘ some) c'` over the colors `c' ≠ c` available at the old endpoint. -/

/-- One direction of the recursion: extend a coloring of the shorter path over the new endpoint. -/
theorem mem_reach_succ {k : ℕ} {L : ListAssignment (PathV (k + 1))} {c c' d : ℕ}
    (hc : c ∈ L (pathEnd (k + 1))) (hne : c' ≠ c)
    (h : d ∈ reach k (fun v => L (some v)) c') : d ∈ reach (k + 1) L c := by
  obtain ⟨g, hg, hg1, hg2⟩ := mem_reach.mp h
  refine mem_reach.mpr ⟨fun o => Option.elim o c g, ?_, rfl, hg2⟩
  refine mem_colorings_addPendant (pathG k) hg hc ?_
  rw [hg1]
  exact Ne.symm hne

/-- The other direction: restrict a coloring of the longer path. -/
theorem exists_of_mem_reach_succ {k : ℕ} {L : ListAssignment (PathV (k + 1))} {c d : ℕ}
    (h : d ∈ reach (k + 1) L c) :
    ∃ c' ∈ L (some (pathEnd k)), c' ≠ c ∧ d ∈ reach k (fun v => L (some v)) c' := by
  obtain ⟨f, hf, h1, h2⟩ := mem_reach.mp h
  rw [mem_colorings] at hf
  have hadj : (pathG (k + 1)).Adj (some (pathEnd k)) (pathEnd (k + 1)) := rfl
  refine ⟨f (some (pathEnd k)), hf.1 _, ?_, ?_⟩
  · rw [← h1]
    exact hf.2 hadj
  · refine mem_reach.mpr ⟨fun v => f (some v), mem_colorings.mpr ⟨fun v => hf.1 (some v), ?_⟩,
      rfl, h2⟩
    intro a b hab
    exact hf.2 (show (pathG (k + 1)).Adj (some a) (some b) from hab)

/-! ### Colorings from a constant assignment alternate

A path colored from a constant `2`-list assignment is determined by the color of either end: the
colors alternate. The consequence used below is that two such colorings differing at `pathEnd`
differ at `pathStart` too, so distinct colors at `pathEnd` have *disjoint* reachable sets. -/

/-- In a two-element set, everything other than a given element is the same. -/
private lemma eq_of_card_two {s : Finset ℕ} (hs : s.card = 2) {x y z : ℕ}
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hyx : y ≠ x) (hzx : z ≠ x) : y = z := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> simp_all

/-- **Colors alternate.** Two colorings of a path from the same constant `2`-list assignment that
differ at `pathEnd` also differ at `pathStart`. -/
theorem ne_pathStart_of_ne_pathEnd : ∀ (k : ℕ) (s : Finset ℕ), s.card = 2 →
    ∀ f ∈ (pathG k).colorings (fun _ => s), ∀ g ∈ (pathG k).colorings (fun _ => s),
      f (pathEnd k) ≠ g (pathEnd k) → f (pathStart k) ≠ g (pathStart k) := by
  intro k
  induction k with
  | zero =>
    intro s _ f _ g _ hne
    rw [Subsingleton.elim (pathStart 0) (pathEnd 0)]
    exact hne
  | succ k ih =>
    intro s hs f hf g hg hne
    rw [mem_colorings] at hf hg
    have hadj : (pathG (k + 1)).Adj (some (pathEnd k)) (pathEnd (k + 1)) := rfl
    -- the vertex next to the endpoint takes the *other* color, so the two colorings swap there
    have hf' : f (some (pathEnd k)) ≠ f (pathEnd (k + 1)) := hf.2 hadj
    have hg' : g (some (pathEnd k)) ≠ g (pathEnd (k + 1)) := hg.2 hadj
    have key : f (some (pathEnd k)) = g (pathEnd (k + 1)) := by
      refine eq_of_card_two hs (hf.1 (pathEnd (k + 1))) (hf.1 (some (pathEnd k)))
        (hg.1 (pathEnd (k + 1))) hf' ?_
      exact fun hcon => hne hcon.symm
    have key' : g (some (pathEnd k)) = f (pathEnd (k + 1)) := by
      refine eq_of_card_two hs (hg.1 (pathEnd (k + 1))) (hg.1 (some (pathEnd k)))
        (hf.1 (pathEnd (k + 1))) hg' hne
    have hstep : f (some (pathEnd k)) ≠ g (some (pathEnd k)) := by
      rw [key, key']
      exact Ne.symm hne
    exact ih s hs (fun v => f (some v))
      (mem_colorings.mpr ⟨fun v => hf.1 (some v),
        fun a b hab => hf.2 (show (pathG (k + 1)).Adj (some a) (some b) from hab)⟩)
      (fun v => g (some v))
      (mem_colorings.mpr ⟨fun v => hg.1 (some v),
        fun a b hab => hg.2 (show (pathG (k + 1)).Adj (some a) (some b) from hab)⟩)
      hstep

/-- Consequently distinct colors at `pathEnd` reach disjoint sets, for a constant assignment. -/
theorem reach_disjoint_of_const {k : ℕ} {s : Finset ℕ} (hs : s.card = 2) {a b : ℕ} (hab : a ≠ b) :
    ∀ d, d ∈ reach k (fun _ => s) a → d ∉ reach k (fun _ => s) b := by
  intro d hda hdb
  obtain ⟨f, hf, hf1, hf2⟩ := mem_reach.mp hda
  obtain ⟨g, hg, hg1, hg2⟩ := mem_reach.mp hdb
  exact ne_pathStart_of_ne_pathEnd k s hs f hf g hg (by rw [hf1, hg1]; exact hab)
    (by rw [hf2, hg2])

/-! ### The propagation lemma

If every color of `L (pathEnd k)` forces a color of `L (pathStart k)` — that is, has a singleton
reachable set — then `L` is constant. This is the first step of the paper's argument on p. 5. -/

/-- **Propagation.** If every color available at `pathEnd k` forces a color at `pathStart k`, then
all the lists of `L` are equal. -/
theorem const_of_forall_reach_card_one : ∀ (k : ℕ) (L : ListAssignment (PathV k)),
    (∀ v, (L v).card = 2) → (∀ c ∈ L (pathEnd k), (reach k L c).card = 1) →
      ∀ v, L v = L (pathEnd k) := by
  intro k
  induction k with
  | zero => intro L _ _ v; rw [Subsingleton.elim v (pathEnd 0)]
  | succ k ih =>
    intro L hcard hforce
    set L' : ListAssignment (PathV k) := fun v => L (some v) with hL'
    have hcard' : ∀ v, (L' v).card = 2 := fun v => hcard (some v)
    have hcard2 : ∀ v, 2 ≤ (L' v).card := fun v => (hcard' v).ge
    -- the reachable set of a color available at the old endpoint sits inside that of any
    -- different color available at the new endpoint
    have hsub : ∀ c ∈ L (pathEnd (k + 1)), ∀ c' ∈ L' (pathEnd k), c' ≠ c →
        reach k L' c' ⊆ reach (k + 1) L c := by
      intro c hc c' _ hne d hd
      exact mem_reach_succ hc hne hd
    -- each such reachable set is therefore a singleton too
    have hone : ∀ c ∈ L (pathEnd (k + 1)), ∀ c' ∈ L' (pathEnd k), c' ≠ c →
        (reach k L' c').card = 1 := by
      intro c hc c' hc' hne
      have h1 := one_le_card_reach hcard2 hc'
      have h2 := Finset.card_le_card (hsub c hc c' hc' hne)
      rw [hforce c hc] at h2
      omega
    -- the two lists at the two ends of the first edge agree
    have hTE : L (pathEnd (k + 1)) = L' (pathEnd k) := by
      by_contra hTE
      -- otherwise some color `α` of the new endpoint is unavailable at the old one, and *both*
      -- colors there have singleton reachable sets, forcing `L'` to be constant …
      obtain ⟨α, hα, hαE⟩ : ∃ α ∈ L (pathEnd (k + 1)), α ∉ L' (pathEnd k) := by
        by_contra hcon
        push Not at hcon
        exact hTE (Finset.eq_of_subset_of_card_le hcon (by rw [hcard' _, hcard _]))
      have hforce' : ∀ c' ∈ L' (pathEnd k), (reach k L' c').card = 1 :=
        fun c' hc' => hone α hα c' hc' (fun hcon => hαE (hcon ▸ hc'))
      have hconst := ih L' hcard' hforce'
      -- … and then the two colors at the old endpoint have disjoint reachable sets, while both
      -- are contained in the single reachable set of `α`
      obtain ⟨p, q, hpq, hEpq⟩ := Finset.card_eq_two.mp (hcard' (pathEnd k))
      have hp : p ∈ L' (pathEnd k) := by rw [hEpq]; exact Finset.mem_insert_self _ _
      have hq : q ∈ L' (pathEnd k) := by
        rw [hEpq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      obtain ⟨d, hd⟩ := reach_nonempty hcard2 hp
      have hdq : d ∈ reach k L' q := by
        have h1 : d ∈ reach (k + 1) L α := hsub α hα p hp (fun hcon => hαE (hcon ▸ hp)) hd
        have h2 : reach k L' q ⊆ reach (k + 1) L α :=
          hsub α hα q hq (fun hcon => hαE (hcon ▸ hq))
        obtain ⟨e, he⟩ := reach_nonempty hcard2 hq
        have hcardα := hforce α hα
        have : reach k L' q = reach (k + 1) L α := by
          refine Finset.eq_of_subset_of_card_le h2 ?_
          rw [hcardα, hforce' q hq]
        rw [this]
        exact h1
      have hLfun : L' = fun _ => L' (pathEnd k) := funext hconst
      rw [hLfun] at hd hdq
      exact reach_disjoint_of_const (hcard' (pathEnd k)) hpq d hd hdq
    -- with the two lists equal, every color of the old endpoint is ≠ some color of the new one
    have hforce' : ∀ c' ∈ L' (pathEnd k), (reach k L' c').card = 1 := by
      intro c' hc'
      obtain ⟨c, hc, hne⟩ := Finset.exists_mem_ne (s := L (pathEnd (k + 1)))
        (by rw [hcard (pathEnd (k + 1))]; omega) c'
      exact hone c hc c' hc' (Ne.symm hne)
    have hconst := ih L' hcard' hforce'
    intro v
    match v with
    | none => rfl
    | some w => rw [show L (some w) = L' w from rfl, hconst w, hTE]

/-- **Some color forces nothing.** For a non-constant `2`-list assignment on a path, some color of
`L (pathEnd k)` reaches *both* colors of `L (pathStart k)`. -/
theorem exists_reach_eq_pathStart {k : ℕ} {L : ListAssignment (PathV k)}
    (hcard : ∀ v, (L v).card = 2) (hne : ∃ v, L v ≠ L (pathEnd k)) :
    ∃ α ∈ L (pathEnd k), reach k L α = L (pathStart k) := by
  have hcard2 : ∀ v, 2 ≤ (L v).card := fun v => (hcard v).ge
  obtain ⟨α, hα, hα1⟩ : ∃ α ∈ L (pathEnd k), (reach k L α).card ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v, hv⟩ := hne
    exact hv (const_of_forall_reach_card_one k L hcard hcon v)
  refine ⟨α, hα, ?_⟩
  have h1 := one_le_card_reach hcard2 hα
  have h2 := Finset.card_le_card (reach_subset (L := L) α)
  have h3 : (L (pathStart k)).card = 2 := hcard _
  rw [h3] at h2
  exact Finset.eq_of_subset_of_card_le (reach_subset α) (by omega)

/-! ### The paper's Case 2, when the two ends of the removed edge differ

With `α ∈ L(pathEnd k)` reaching *both* colors of `L(pathStart k)`, two distinct colorings of the
cycle are produced as follows. If `α ∉ L(pathStart k)`, the two colorings realizing the two colors
of `L(pathStart k)` both already avoid `α` at `pathStart k`, so both close up. Otherwise
`L(pathStart k) = {α, δ}`: the coloring realizing `δ` closes up, and so does *any* coloring giving
the other color `β` of `L(pathEnd k)` to `pathEnd k` — for that we need `β ∉ L(pathStart k)`, which
is where the hypothesis `L (pathEnd k) ≠ L (pathStart k)` enters. -/

/-- A two-element finset is the pair of any two of its distinct elements. -/
private lemma eq_pair_of_card_two {s : Finset ℕ} (hs : s.card = 2) {x y : ℕ}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s = {x, y} := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · rw [Finset.mem_singleton] at hz
      exact hz ▸ hy
  · rw [hs, Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]

/-- **`2 ≤ col(C, L)` for a `2`-list assignment whose two lists at the ends of the removed edge
differ.** This is Case 2 of Kirov–Naimi p. 5–6, in the only form in which their choice of edge is
available here. Note that no parity hypothesis is needed. -/
theorem two_le_col_closePath_of_ends_ne {k : ℕ} (hk : 1 ≤ k) {L : ListAssignment (PathV k)}
    (hcard : ∀ v, (L v).card = 2) (hends : L (pathEnd k) ≠ L (pathStart k)) :
    2 ≤ (closePath k).col L := by
  have hcard2 : ∀ v, 2 ≤ (L v).card := fun v => (hcard v).ge
  obtain ⟨α, hα, hreach⟩ :=
    exists_reach_eq_pathStart hcard ⟨pathStart k, fun h => hends h.symm⟩
  by_cases hαS : α ∈ L (pathStart k)
  · -- `L (pathStart k) = {α, δ}`; the other color `β` of `L (pathEnd k)` is not available there
    obtain ⟨δ, hδ, hδα⟩ := Finset.exists_mem_ne (s := L (pathStart k))
      (by rw [hcard (pathStart k)]; omega) α
    obtain ⟨β, hβ, hβα⟩ := Finset.exists_mem_ne (s := L (pathEnd k))
      (by rw [hcard (pathEnd k)]; omega) α
    have hSpair : L (pathStart k) = {α, δ} :=
      eq_pair_of_card_two (hcard _) hαS hδ (Ne.symm hδα)
    have hEpair : L (pathEnd k) = {α, β} :=
      eq_pair_of_card_two (hcard _) hα hβ (Ne.symm hβα)
    have hβδ : β ≠ δ := by
      intro h
      exact hends (hEpair.trans (by rw [h, ← hSpair]))
    -- the coloring `pathEnd ↦ α`, `pathStart ↦ δ`
    obtain ⟨f, hf, hf1, hf2⟩ := mem_reach.mp (hreach ▸ hδ)
    -- any coloring with `pathEnd ↦ β`
    obtain ⟨d, hd⟩ := reach_nonempty hcard2 hβ
    obtain ⟨g, hg, hg1, hg2⟩ := mem_reach.mp hd
    have hdβ : d ≠ β := by
      intro h
      have hdS : d ∈ L (pathStart k) := reach_subset β hd
      rw [hSpair, h] at hdS
      rcases Finset.mem_insert.mp hdS with h' | h'
      · exact hβα h'
      · exact hβδ (Finset.mem_singleton.mp h')
    refine two_le_col_closePath hk hf hg ?_ ?_ ?_
    · rw [hf1, hf2]
      exact Ne.symm hδα
    · rw [hg1, hg2]
      exact Ne.symm hdβ
    · intro h
      exact hβα (by rw [← hg1, ← h, hf1])
  · -- `α` is unavailable at the far end, so *both* colorings from `α` close up
    obtain ⟨p, q, hpq, hPQ⟩ := Finset.card_eq_two.mp (hcard (pathStart k))
    have hpS : p ∈ L (pathStart k) := by rw [hPQ]; exact Finset.mem_insert_self _ _
    have hqS : q ∈ L (pathStart k) := by
      rw [hPQ]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨f, hf, hf1, hf2⟩ := mem_reach.mp (hreach ▸ hpS)
    obtain ⟨g, hg, hg1, hg2⟩ := mem_reach.mp (hreach ▸ hqS)
    refine two_le_col_closePath hk hf hg ?_ ?_ ?_
    · rw [hf1, hf2]
      exact fun h => hαS (by rw [h]; exact hpS)
    · rw [hg1, hg2]
      exact fun h => hαS (by rw [h]; exact hqS)
    · intro h
      exact hpq (by rw [← hf2, h, hg2])

/-! ### Where the case `n = 2` stands

Everything except one configuration is now in place. The assembly below reduces the case `n = 2`
of Theorem 1, for a cycle on an even number of vertices, to the single remaining statement `H`:

> a **non-constant** `2`-list assignment whose two lists at `pathEnd k` and `pathStart k` are
> **equal** admits at least two colorings of the cycle.

That configuration genuinely occurs — for instance on `C₄` with the lists `{0,1}`, `{1,2}`,
`{0,2}`, `{0,1}` read around the cycle from `pathEnd 3` — and there the forcing argument stalls:
the only achievable pair of colors at the two ends with distinct entries is a single pair, so the
two required colorings must both come from *that one pair*, which is a counting statement rather
than an existence statement. (The example does have three colorings.) Kirov–Naimi avoid the
configuration by choosing an edge `vw` with `L(v) ≠ L(w)`, which in this presentation of the cycle
would require rotating the cycle by a graph isomorphism. -/

/-- The lists of the stalling example, for the record: a non-constant `2`-assignment on `C₄` whose
two lists at `pathEnd 3` and `pathStart 3` agree. It has three colorings, but only one achievable
pair of distinct colors at the two ends of the path. -/
private def testEqualEnds : ListAssignment (PathV 3) := fun v =>
  if v = pathVtx 3 0 then ({0, 1} : Finset ℕ)
  else if v = pathVtx 3 1 then ({1, 2} : Finset ℕ)
  else if v = pathVtx 3 2 then ({0, 2} : Finset ℕ)
  else ({0, 1} : Finset ℕ)

#guard testEqualEnds (pathEnd 3) = testEqualEnds (pathStart 3)
#guard (closePath 3).col testEqualEnds = 3
#guard (closePath 3).colConst 2 ≤ (closePath 3).col testEqualEnds
#guard reach 3 testEqualEnds 0 = {0, 1}    -- the color `0` forces nothing …
#guard reach 3 testEqualEnds 1 = {1}       -- … but the color `1` forces `1`

/-- **The case `n = 2` of Theorem 1 for a cycle on an even number of vertices, conditionally on the
one remaining configuration.** `closePath k` has `k + 1` vertices, so `Odd k` says that number is
even. The hypothesis `H` is exactly the configuration described above; everything else — the
constant case and the case of distinct lists at the two ends — is proved. -/
theorem monophilic_closePath_two_of_odd {k : ℕ} (hk : Odd k)
    (H : ∀ L : ListAssignment (PathV k), (∀ v, (L v).card = 2) →
      L (pathEnd k) = L (pathStart k) → (∃ v, L v ≠ L (pathEnd k)) →
      2 ≤ (closePath k).col L) :
    (closePath k).Monophilic 2 := by
  intro L hL
  have hcard : ∀ v, (L v).card = 2 := hL
  rw [colConst_closePath_two_of_odd hk]
  by_cases hnc : ∃ v, L v ≠ L (pathEnd k)
  · by_cases hends : L (pathEnd k) = L (pathStart k)
    · exact H L hcard hends hnc
    · exact two_le_col_closePath_of_ends_ne hk.pos hcard hends
  · push Not at hnc
    have hLc : L = fun _ => L (pathEnd k) := funext hnc
    rw [hLc, col_closePath_const hk (hcard (pathEnd k))]

end Monophilic

#print axioms Monophilic.colConst_closePath_two_of_odd
#print axioms Monophilic.mem_colorings_closePath_iff
#print axioms Monophilic.colorings_closePath_eq_filter
#print axioms Monophilic.col_closePath_const
#print axioms Monophilic.ne_pathStart_of_ne_pathEnd
#print axioms Monophilic.const_of_forall_reach_card_one
#print axioms Monophilic.exists_reach_eq_pathStart
#print axioms Monophilic.two_le_col_closePath_of_ends_ne
#print axioms Monophilic.monophilic_closePath_two_of_odd
