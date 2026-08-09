/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.PathCount

/-!
# Cycles, and the number of their colorings

Kirov–Naimi, *List coloring and `n`-monophilic graphs* (arXiv:1004.5183), compute in §3 the number
of colorings of a cycle from the constant list assignment by deleting one vertex: fixing a color
`c` at a vertex `v` of a cycle `C` and removing `v` leaves a path whose two terminal vertices (the
former neighbors of `v`) have both lost the *same* color `c`, i.e. a **type A** `(n, n-1)`-list
assignment. Since `pathA m k` counts the colorings of such a path (`Monophilic.col_pathAssign`),
summing over the `n` choices of `c` gives the paper's `col(C, n) = n · A_{k-2}` for a cycle on `k`
vertices.

Following `Monophilic.Path`, a cycle is built as the path of length `k` (so `k + 1` vertices) with
one extra edge joining its two terminal vertices `pathStart k` and `pathEnd k`. Concretely,
`closePath (k + 1)` attaches a single new vertex `none` to *both* ends of `pathG k`, which is what
`SimpleGraph.addPendantPair` does; deleting `none` therefore returns `pathG k` definitionally and
`Monophilic.Delete` applies with no transport. For `k ≥ 2` this really is the cycle on `k + 1`
vertices — see the `#guard`s against the chromatic polynomial `(n-1)^{k+1} + (-1)^{k+1} (n-1)`.
The degenerate values are `closePath 0 = ⊥` (one vertex) and `closePath 1 = pathG 1` (one edge),
since a simple graph cannot record the doubled edge.

## Main definitions

* `SimpleGraph.addPendantPair G u v` : `G` with a new vertex `none` joined to both `u` and `v`
* `Monophilic.closePath k` : `pathG k` together with the edge `pathStart k — pathEnd k`

## Main results

* `Monophilic.closePath_adj` : `closePath k` is `pathG k` plus that one edge and nothing else
* `Monophilic.delNone_closePath_succ` : deleting `pathEnd` from `closePath (k+1)` leaves `pathG k`
* `Monophilic.inducedList_closePath_constList` : the list assignment induced on that path by giving
  the color `c` to the deleted vertex is the type A assignment `pathAssign k n c c`
* `Monophilic.colFix_closePath_succ` : consequently
  `col(C, n, pathEnd, c) = col(P_k, pathAssign k n c c)`
* `Monophilic.colConst_closePath` : `col(C, n) = n · A_{k-1}` for the cycle `closePath k`
-/

open Finset

-- Several lemmas below do not use all of the ambient instances.
set_option linter.unusedSectionVars false

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ### Attaching a new vertex to two old ones -/

/-- Adjacency for `G` with a new vertex `none` joined to both `u` and `v` (and to nothing else). -/
def addPendantPairAdj (u v : V) : Option V → Option V → Prop
  | none, none => False
  | none, some b => b = u ∨ b = v
  | some a, none => a = u ∨ a = v
  | some a, some b => G.Adj a b

/-- `G` with one new vertex `none`, joined to both `u` and `v`.

For `u ≠ v` this adds a vertex of degree two; taking `G` to be a path and `u`, `v` its two ends
closes the path into a cycle. -/
def addPendantPair (u v : V) : SimpleGraph (Option V) where
  Adj := G.addPendantPairAdj u v
  symm := ⟨by rintro (_ | a) (_ | b) h <;> simp_all [addPendantPairAdj, G.adj_comm]⟩
  loopless := ⟨by rintro (_ | a) h <;> simp_all [addPendantPairAdj]⟩

instance instDecidableRelAddPendantPair [DecidableEq V] [DecidableRel G.Adj] (u v : V) :
    DecidableRel (G.addPendantPair u v).Adj := fun a b =>
  match a, b with
  | none, none => inferInstanceAs (Decidable False)
  | none, some b => inferInstanceAs (Decidable (b = u ∨ b = v))
  | some a, none => inferInstanceAs (Decidable (a = u ∨ a = v))
  | some a, some b => inferInstanceAs (Decidable (G.Adj a b))

@[simp] lemma addPendantPair_adj_some_some {u v a b : V} :
    (G.addPendantPair u v).Adj (some a) (some b) ↔ G.Adj a b := Iff.rfl

@[simp] lemma addPendantPair_adj_none_some {u v b : V} :
    (G.addPendantPair u v).Adj none (some b) ↔ b = u ∨ b = v := Iff.rfl

@[simp] lemma addPendantPair_adj_some_none {u v a : V} :
    (G.addPendantPair u v).Adj (some a) none ↔ a = u ∨ a = v := Iff.rfl

@[simp] lemma addPendantPair_adj_none_none {u v : V} :
    ¬ (G.addPendantPair u v).Adj none none := id

/-- Attaching a new vertex to `u` and `v` adds exactly one edge to `G.addPendant u`, namely the
edge joining the new vertex to `v`. -/
theorem addPendantPair_adj_iff (u v : V) (a b : Option V) :
    (G.addPendantPair u v).Adj a b ↔
      (G.addPendant u).Adj a b ∨
        (a ≠ b ∧ ((a = some v ∧ b = none) ∨ (a = none ∧ b = some v))) := by
  match a, b with
  | none, none => simp [addPendant]
  | none, some b => simp [addPendant, addPendantAdj]
  | some a, none => simp [addPendant, addPendantAdj]
  | some a, some b => simp [addPendant, addPendantAdj]

/-- Deleting the new vertex recovers the original graph. -/
@[simp] lemma delNone_addPendantPair [Fintype V] [DecidableEq V] (u v : V) :
    (G.addPendantPair u v).delNone = G := rfl

/-- The list assignment induced on `G` by giving the color `c` to the new vertex of
`G.addPendantPair u v`: exactly the two attachment points `u` and `v` lose the color `c`. -/
lemma inducedList_addPendantPair [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (u v : V)
    (M : ListAssignment (Option V)) (c : ℕ) (w : V) :
    (G.addPendantPair u v).inducedList M c w =
      if w = u ∨ w = v then (M (some w)).erase c else M (some w) := rfl

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-! ### The cycle -/

/-- The path of length `k` closed up: `pathG k` together with one extra edge joining its two
terminal vertices `pathStart k` and `pathEnd k`.

For `k ≥ 2` this is the cycle on `k + 1` vertices. The two degenerate values are
`closePath 0 = ⊥`, a single vertex, and `closePath 1 = pathG 1`, a single edge. -/
def closePath : (k : ℕ) → SimpleGraph (PathV k)
  | 0 => ⊥
  | k + 1 => (pathG k).addPendantPair (pathEnd k) (pathStart k)

instance instDecidableRelClosePath : (k : ℕ) → DecidableRel (closePath k).Adj
  | 0 => fun _ _ => inferInstanceAs (Decidable False)
  | k + 1 =>
      letI := instDecidableEqPathV k
      letI := instDecidableRelPathG k
      inferInstanceAs
        (DecidableRel ((pathG k).addPendantPair (pathEnd k) (pathStart k)).Adj)

@[simp] lemma closePath_zero : closePath 0 = ⊥ := rfl

@[simp] lemma closePath_succ (k : ℕ) :
    closePath (k + 1) = (pathG k).addPendantPair (pathEnd k) (pathStart k) := rfl

/-! `closePath k` is the cycle on `k + 1` vertices for `k ≥ 2`: the chromatic polynomial of a cycle
on `N` vertices is `(n-1)^N + (-1)^N (n-1)`. -/

#guard (closePath 2).colConst 3 = 6      -- `C₃`, `n = 3`: `2^3 - 2`
#guard (closePath 3).colConst 3 = 18     -- `C₄`, `n = 3`: `2^4 + 2`
#guard (closePath 4).colConst 3 = 30     -- `C₅`, `n = 3`: `2^5 - 2`
#guard (closePath 2).colConst 4 = 24     -- `C₃`, `n = 4`: `3^3 - 3`
#guard (closePath 3).colConst 4 = 84     -- `C₄`, `n = 4`: `3^4 + 3`
#guard (closePath 4).colConst 4 = 240    -- `C₅`, `n = 4`: `3^5 - 3`
#guard (closePath 5).colConst 3 = 66     -- `C₆`, `n = 3`: `2^6 + 2`
#guard (closePath 1).colConst 4 = 12     -- degenerate: a single edge

/-! The count of `colConst_closePath`, checked numerically. -/

#guard (closePath 1).colConst 4 = 4 * pathA 2 0
#guard (closePath 2).colConst 3 = 3 * pathA 1 1
#guard (closePath 3).colConst 3 = 3 * pathA 1 2
#guard (closePath 4).colConst 3 = 3 * pathA 1 3
#guard (closePath 5).colConst 3 = 3 * pathA 1 4
#guard (closePath 2).colConst 5 = 5 * pathA 3 1
#guard (closePath 3).colConst 5 = 5 * pathA 3 2
#guard (closePath 4).colConst 5 = 5 * pathA 3 3

/-- The closing edge really is there. -/
theorem closePath_adj_pathStart_pathEnd (k : ℕ) :
    (closePath (k + 1)).Adj (pathStart (k + 1)) (pathEnd (k + 1)) := Or.inr rfl

/-- **`closePath k` is `pathG k` plus one edge.** Its edges are those of the path together with the
single edge joining `pathStart k` to `pathEnd k` (which for `k = 0` would be a loop, and so is not
present). -/
theorem closePath_adj : ∀ (k : ℕ) (a b : PathV k),
    (closePath k).Adj a b ↔
      (pathG k).Adj a b ∨
        (a ≠ b ∧ ((a = pathStart k ∧ b = pathEnd k) ∨ (a = pathEnd k ∧ b = pathStart k)))
  | 0, a, b => by
      have hab : a = b := Subsingleton.elim a b
      simp [closePath_zero, pathG_zero, hab]
  | k + 1, a, b => addPendantPair_adj_iff (pathG k) (pathEnd k) (pathStart k) a b

/-- The path is a subgraph of the cycle. -/
theorem pathG_le_closePath (k : ℕ) : pathG k ≤ closePath k := by
  intro a b h
  exact (closePath_adj k a b).mpr (Or.inl h)

/-! ### Deleting a vertex of the cycle -/

/-- **Deleting one vertex of a cycle leaves a path.** Removing the terminal vertex `pathEnd`
of `closePath (k + 1)` returns exactly `pathG k`: the extra edge was incident to the deleted
vertex. -/
@[simp] theorem delNone_closePath_succ (k : ℕ) : (closePath (k + 1)).delNone = pathG k := rfl

/-- **Peeling a vertex off the cycle.** -/
theorem col_closePath_succ (k : ℕ) (M : ListAssignment (PathV (k + 1))) :
    (closePath (k + 1)).col M
      = ∑ c ∈ M (pathEnd (k + 1)), (pathG k).col ((closePath (k + 1)).inducedList M c) :=
  col_eq_sum_delNone _ M

/-- The list assignment induced on `pathG k` by giving the color `c` to the deleted vertex: both
terminal vertices `pathEnd k` and `pathStart k` lose `c`, everyone else keeps their list. -/
theorem inducedList_closePath_succ (k : ℕ) (M : ListAssignment (PathV (k + 1))) (c : ℕ)
    (w : PathV k) :
    (closePath (k + 1)).inducedList M c w =
      if w = pathEnd k ∨ w = pathStart k then (M (some w)).erase c else M (some w) :=
  inducedList_addPendantPair (pathG k) (pathEnd k) (pathStart k) M c w

/-! ### The induced assignment is of type A -/

/-- `pathInterior k n y` gives every vertex the full palette except `pathStart k`, which is missing
the color `y`. -/
theorem pathInterior_eq_ite_pathStart :
    ∀ (k n y : ℕ) (w : PathV k),
      pathInterior k n y w = if w = pathStart k then (range n).erase y else range n := by
  intro k
  induction k with
  | zero =>
    intro n y w
    have h : w = pathStart 0 := Subsingleton.elim w (pathStart 0)
    show (range n).erase y = if w = pathStart 0 then (range n).erase y else range n
    rw [if_pos h]
  | succ k ih =>
    intro n y w
    match w with
    | none =>
      have h : ¬ ((none : PathV (k + 1)) = pathStart (k + 1)) :=
        fun hc => absurd hc.symm (Option.some_ne_none (pathStart k))
      show range n
          = if (none : PathV (k + 1)) = pathStart (k + 1) then (range n).erase y else range n
      rw [if_neg h]
    | some w' =>
      have key : ((some w' : PathV (k + 1)) = pathStart (k + 1)) ↔ w' = pathStart k :=
        ⟨fun h => Option.some_inj.mp h, fun h => congrArg some h⟩
      show pathInterior k n y w'
          = if (some w' : PathV (k + 1)) = pathStart (k + 1) then (range n).erase y else range n
      rw [ih n y w']
      by_cases h : w' = pathStart k
      · rw [if_pos h, if_pos (key.mpr h)]
      · rw [if_neg h, if_neg (fun hc => h (key.mp hc))]

/-- **The type A assignment, pointwise.** `pathAssign k n c c` — the `(n, n-1)`-assignment missing
the *same* color `c` at both ends of the path — is exactly "the full palette, minus `c` at the two
terminal vertices". -/
theorem pathAssign_self_apply :
    ∀ (k n c : ℕ) (w : PathV k),
      pathAssign k n c c w
        = if w = pathEnd k ∨ w = pathStart k then (range n).erase c else range n := by
  intro k
  induction k with
  | zero =>
    intro n c w
    have h : w = pathEnd 0 ∨ w = pathStart 0 := Or.inl (Subsingleton.elim w (pathEnd 0))
    show ((range n).erase c).erase c
        = if w = pathEnd 0 ∨ w = pathStart 0 then (range n).erase c else range n
    rw [if_pos h, Finset.erase_idem]
  | succ k _ =>
    intro n c w
    match w with
    | none =>
      have h : (none : PathV (k + 1)) = pathEnd (k + 1) ∨
          (none : PathV (k + 1)) = pathStart (k + 1) := Or.inl rfl
      show (range n).erase c
          = if (none : PathV (k + 1)) = pathEnd (k + 1) ∨
              (none : PathV (k + 1)) = pathStart (k + 1) then (range n).erase c else range n
      rw [if_pos h]
    | some w' =>
      have key : ((some w' : PathV (k + 1)) = pathEnd (k + 1) ∨
          (some w' : PathV (k + 1)) = pathStart (k + 1)) ↔ w' = pathStart k := by
        constructor
        · rintro (h | h)
          · exact absurd h (Option.some_ne_none w')
          · exact Option.some_inj.mp h
        · exact fun h => Or.inr (congrArg some h)
      show pathInterior k n c w'
          = if (some w' : PathV (k + 1)) = pathEnd (k + 1) ∨
              (some w' : PathV (k + 1)) = pathStart (k + 1) then (range n).erase c else range n
      rw [pathInterior_eq_ite_pathStart]
      by_cases h : w' = pathStart k
      · rw [if_pos h, if_pos (key.mpr h)]
      · rw [if_neg h, if_neg (fun hc => h (key.mp hc))]

/-- **Deliverable: deleting a vertex of the cycle gives a type A assignment.** Giving the color `c`
to the deleted vertex `pathEnd (k+1)` of `closePath (k+1)` induces on the remaining path `pathG k`
precisely the canonical type A `(n, n-1)`-list assignment `pathAssign k n c c`: both surviving
terminal vertices are missing the single color `c`, and the interior keeps the full palette. -/
theorem inducedList_closePath_constList (k n c : ℕ) :
    (closePath (k + 1)).inducedList (constList (PathV (k + 1)) n) c = pathAssign k n c c := by
  funext w
  rw [inducedList_closePath_succ]
  simp only [constList_apply]
  rw [pathAssign_self_apply]

/-- The colorings of the cycle giving the color `c` to `pathEnd` are the colorings of the path
`pathG k` from the type A assignment `pathAssign k n c c`. -/
theorem colFix_closePath_succ (k n c : ℕ) (hc : c ∈ range n) :
    (closePath (k + 1)).colFix (constList (PathV (k + 1)) n) (pathEnd (k + 1)) c
      = (pathG k).col (pathAssign k n c c) := by
  rw [← inducedList_closePath_constList k n c]
  exact colFix_none_eq_col_delNone _ _ hc

/-! ### The count -/

/-- **`col(C, n) = n · A_{k-1}`**, in the form `col(closePath (k+1), n) = n · A_k`. -/
theorem colConst_closePath_succ (m k : ℕ) :
    (closePath (k + 1)).colConst (m + 2) = (m + 2) * pathA m k := by
  have hterm : ∀ c ∈ range (m + 2),
      (pathG k).col ((closePath (k + 1)).inducedList (constList (PathV (k + 1)) (m + 2)) c)
        = pathA m k := by
    intro c hc
    rw [inducedList_closePath_constList,
      col_pathAssign m k c c (mem_range.mp hc) (mem_range.mp hc), if_pos rfl]
  rw [colConst, col_closePath_succ]
  simp only [constList_apply]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Kirov–Naimi's `col(C, n) = n · A_{k-2}`** for a cycle `C` on `k` vertices. Here the cycle
`closePath k` has `k + 1` vertices, so the index is `k - 1`.

The hypothesis `1 ≤ k` is needed: `closePath 0` is a single vertex, with `col = n`, whereas
`n · A_{-1}` would be read as `n · A_0 = n(n-1)`. It is *not* necessary to assume `2 ≤ k`: the
degenerate `closePath 1` is a single edge, with `col = n(n-1) = n · A_0`. -/
theorem colConst_closePath (m k : ℕ) (hk : 1 ≤ k) :
    (closePath k).colConst (m + 2) = (m + 2) * pathA m (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simpa using colConst_closePath_succ m j

end Monophilic
