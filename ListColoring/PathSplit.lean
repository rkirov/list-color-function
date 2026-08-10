/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Bridge
import ListColoring.Iso
import ListColoring.Path

/-!
# Cutting a path at an edge

Removing one edge from a path of length `a + b + 1` leaves two paths, of lengths `a` and `b`.
Reinstating that edge presents the long path as a `SimpleGraph.bridge` of the two short ones, which
is exactly the shape required by Lemma 2 of Kirov–Naimi (`SimpleGraph.exists_nested_of_bridge`).
Lemma 3(c) applies Lemma 2 to the two sides of an edge of a path, and this file is what lets it.

## Orientation

Number the vertices of `pathG k` by `0, …, k`, with `pathEnd k` the vertex `0` (the one attached
last, always `none`) and `pathStart k` the vertex `k`. Cutting `pathG (a + b + 1)` between vertices
`a` and `a + 1` leaves `{0, …, a} ≅ pathG a` and `{a+1, …, a+b+1} ≅ pathG b`, matched so that

* vertex `a` of the long path becomes `pathStart a`, and
* vertex `a + 1` of the long path becomes `pathEnd b`.

So the bridged union to use is `bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)`: the *left*
summand carries the piece containing `pathEnd (a + b + 1)`, and the bridge joins the `pathStart` end
of `pathG a` to the `pathEnd` end of `pathG b`. Any other pairing of the terminal vertices attaches
a piece by the wrong end, and is not an isomorphism as soon as that piece is long enough for its two
ends to differ.

The recursion is on `a`: attaching a pendant vertex to `pathG (b + a + 1)` lengthens the left-hand
piece by one, `pathEnd` and all. Because `Nat.add` recurses on its second argument this is
definitionally smooth only when the total length is written `b + a + 1`, so `pathSplitIsoAux` uses
that form and `pathSplitIso` transports it along `a + b + 1 = b + a + 1` with `pathGCongr`.

## Main results

* `ListColoring.pathGCongr` : paths of equal length are isomorphic (transport along `m = n`)
* `ListColoring.pathSplitIso` :
  `pathG (a + b + 1) ≃g bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)`
* `ListColoring.pathSplitIso_pathEnd`, `ListColoring.pathSplitIso_pathStart` : where the two
  terminal vertices of the long path go
* `ListColoring.adj_pathSplitIso_symm` : the bridging edge is an edge of the path
* `ListColoring.col_pathG_split` : the induced identity of list-coloring counts,
  `col(P_{a+b+1}, M) = col(bridge, M ∘ (pathSplitIso a b).symm)`
* `ListColoring.col_bridge_pathSplit` : its converse, transporting a list assignment of the bridged
  union back to the path
-/

open Finset

namespace ListColoring

open SimpleGraph

/-! ### Two bijections of vertex types

Everything up to `ListColoring.pathGCongr` is stated for arbitrary graphs. The point of that is that
`ListColoring.PathV` — whose `Option` structure is visible only at default transparency, `PathV`
being defined by recursion on the length — never has to be unfolded by `simp` or `rw`. -/

/-- `Option W ≃ Unit ⊕ W`: the extra point becomes the single vertex of the left summand. -/
def optionUnitSumEquiv (W : Type*) : Option W ≃ Unit ⊕ W where
  toFun x := x.elim (.inl ()) (.inr ·)
  invFun := Sum.elim (fun _ => none) some
  left_inv := by rintro (_ | y) <;> rfl
  right_inv := by rintro (u | y) <;> rfl

/-- `Option (V ⊕ W) ≃ Option V ⊕ W`: the extra point joins the left summand. -/
def optionSumEquiv (V W : Type*) : Option (V ⊕ W) ≃ Option V ⊕ W where
  toFun x := x.elim (.inl none) (Sum.map some id)
  invFun := Sum.elim (Option.map Sum.inl) fun y => some (.inr y)
  left_inv := by rintro (_ | (x | y)) <;> rfl
  right_inv := by rintro ((_ | x) | y) <;> rfl

/-! ### The two steps of the recursion, for arbitrary graphs -/

/-- Embedding both sides of a bridged union into the bridged union with a pendant vertex added on
the left does not change any adjacency. -/
lemma bridge_addPendant_map_some_adj {V W : Type*} [DecidableEq V] (G : SimpleGraph V)
    (H : SimpleGraph W) (p v₀ : V) (w₀ : W) (u u' : V ⊕ W) :
    (bridge (G.addPendant p) H (some v₀) w₀).Adj (Sum.map some id u) (Sum.map some id u')
      ↔ (bridge G H v₀ w₀).Adj u u' := by
  cases u <;> cases u' <;> simp
  -- the surviving goal is `(G.addPendant p).Adj (some _) (some _) ↔ G.Adj _ _`, true by definition
  exact Iff.rfl

/-- **Base step.** A graph `H` with a pendant vertex attached at `w₀` is the bridged union of a
single vertex and `H`, bridged at `w₀`. -/
theorem bridge_bot_adj {W : Type*} [DecidableEq W] (H : SimpleGraph W) (w₀ : W) (x y : Option W) :
    (bridge (⊥ : SimpleGraph Unit) H () w₀).Adj (optionUnitSumEquiv W x) (optionUnitSumEquiv W y)
      ↔ (H.addPendant w₀).Adj x y := by
  rcases x with _ | x <;> rcases y with _ | y <;>
    simp [optionUnitSumEquiv, SimpleGraph.addPendant, SimpleGraph.addPendantAdj]

/-- **Recursive step.** If `e` presents `K` as the bridged union `bridge G H v₀ w₀`, and `q` is the
vertex of `K` sitting over `p` on the left-hand side, then attaching a pendant vertex to `K` at `q`
presents it as the bridged union with a pendant vertex attached to `G` at `p`.

Note that the new left-hand endpoint of the bridge is `some v₀`: the bridging edge is unchanged. -/
theorem bridge_addPendant_adj {U V W : Type*} [DecidableEq V] {K : SimpleGraph U}
    {G : SimpleGraph V} {H : SimpleGraph W} {v₀ : V} {w₀ : W} (e : U ≃ V ⊕ W)
    (he : ∀ x y : U, (bridge G H v₀ w₀).Adj (e x) (e y) ↔ K.Adj x y)
    {q : U} {p : V} (hq : e q = Sum.inl p) (x y : Option U) :
    (bridge (G.addPendant p) H (some v₀) w₀).Adj
        (((Equiv.optionCongr e).trans (optionSumEquiv V W)) x)
        (((Equiv.optionCongr e).trans (optionSumEquiv V W)) y)
      ↔ (K.addPendant q).Adj x y := by
  -- the pendant vertex of the bridged union sees exactly the vertex sitting over `p`
  have key : ∀ z : U, (bridge (G.addPendant p) H (some v₀) w₀).Adj
      (Sum.inl none) (Sum.map some id (e z)) ↔ z = q := by
    intro z
    have hz : (e z = Sum.inl p) ↔ z = q := by rw [← hq]; exact e.apply_eq_iff_eq
    rcases hez : e z with c | d <;> rw [hez] at hz
    · simp only [Sum.map_inl, bridge_adj_inl_inl]
      -- `(G.addPendant p).Adj none (some c)` is `c = p` by definition
      show c = p ↔ z = q
      simpa using hz
    · simp only [Sum.map_inr, bridge_adj_inl_inr, reduceCtorEq, false_and, false_iff]
      intro h
      exact absurd (hz.mpr h) (by simp)
  rcases x with _ | x <;> rcases y with _ | y
  · -- the pendant vertex is not adjacent to itself
    show (bridge (G.addPendant p) H (some v₀) w₀).Adj (Sum.inl none) (Sum.inl none) ↔ _
    simp
  · show (bridge (G.addPendant p) H (some v₀) w₀).Adj (Sum.inl none) (Sum.map some id (e y)) ↔ _
    exact key y
  · show (bridge (G.addPendant p) H (some v₀) w₀).Adj (Sum.map some id (e x)) (Sum.inl none) ↔ _
    exact (SimpleGraph.adj_comm _ _ _).trans
      ((key x).trans (SimpleGraph.adj_comm (K.addPendant q) none (some x)))
  · show (bridge (G.addPendant p) H (some v₀) w₀).Adj
      (Sum.map some id (e x)) (Sum.map some id (e y)) ↔ _
    exact (bridge_addPendant_map_some_adj G H p v₀ w₀ (e x) (e y)).trans (he x y)

/-! ### Transport along an equality of lengths -/

/-- Paths of the same length are the same graph; this is the transport, the identity on vertices
once the two lengths are identified. -/
def pathGCongr {m n : ℕ} (h : m = n) : pathG m ≃g pathG n where
  toEquiv := Equiv.cast (congrArg PathV h)
  map_rel_iff' := by subst h; exact Iff.rfl

@[simp] lemma pathGCongr_pathEnd {m n : ℕ} (h : m = n) :
    pathGCongr h (pathEnd m) = pathEnd n := by subst h; rfl

@[simp] lemma pathGCongr_pathStart {m n : ℕ} (h : m = n) :
    pathGCongr h (pathStart m) = pathStart n := by subst h; rfl

/-! ### The splitting bijection -/

/-- The bijection underlying `ListColoring.pathSplitIso`: it cuts the `b + a + 2` vertices of a path
of length `b + a + 1` into the first `a + 1` and the last `b + 1`, keeping their order.

The recursion is on `a`; the pendant vertex `pathEnd` of the long path becomes the pendant vertex
`pathEnd` of the left-hand piece. -/
def pathSplitEquiv : (a b : ℕ) → PathV (b + a + 1) ≃ PathV a ⊕ PathV b
  | 0, b => optionUnitSumEquiv (PathV b)
  | a + 1, b => (Equiv.optionCongr (pathSplitEquiv a b)).trans (optionSumEquiv _ _)

@[simp] lemma pathSplitEquiv_succ_some (a b : ℕ) (x : PathV (b + a + 1)) :
    pathSplitEquiv (a + 1) b (some x) = Sum.map some id (pathSplitEquiv a b x) := rfl

/-- The pendant end of the long path is the pendant end of the left-hand piece. -/
@[simp] lemma pathSplitEquiv_pathEnd (a b : ℕ) :
    pathSplitEquiv a b (pathEnd (b + a + 1)) = .inl (pathEnd a) := by
  cases a <;> rfl

/-- The far end of the long path is the far end of the right-hand piece. -/
@[simp] lemma pathSplitEquiv_pathStart : ∀ (a b : ℕ),
    pathSplitEquiv a b (pathStart (b + a + 1)) = .inr (pathStart b) := by
  intro a
  induction a with
  | zero => intro b; rfl
  | succ a ih =>
      intro b
      show Sum.map some id (pathSplitEquiv a b (pathStart (b + a + 1))) = _
      rw [ih b]
      rfl

/-- `pathSplitEquiv` matches the adjacencies of the path with those of the bridged union. -/
theorem pathSplitEquiv_adj : ∀ (a b : ℕ) (x y : PathV (b + a + 1)),
    (bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)).Adj
        (pathSplitEquiv a b x) (pathSplitEquiv a b y)
      ↔ (pathG (b + a + 1)).Adj x y := by
  intro a
  induction a with
  | zero => exact fun b => bridge_bot_adj (pathG b) (pathEnd b)
  | succ a ih =>
      exact fun b => bridge_addPendant_adj (pathSplitEquiv a b) (ih b)
        (pathSplitEquiv_pathEnd a b)

/-! ### The isomorphism -/

/-- The two ways of writing the length of the long path. -/
private lemma splitLen (a b : ℕ) : a + b + 1 = b + a + 1 := by omega

/-- **Cutting a path at an edge**, in the form produced by the recursion. -/
def pathSplitIsoAux (a b : ℕ) :
    pathG (b + a + 1) ≃g bridge (pathG a) (pathG b) (pathStart a) (pathEnd b) :=
  ⟨pathSplitEquiv a b, pathSplitEquiv_adj a b _ _⟩

/-- **Cutting a path at an edge.** Deleting the edge between the vertices numbered `a` and `a + 1`
of the path of length `a + b + 1` leaves a path of length `a` and a path of length `b`; putting the
edge back exhibits the long path as `bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)`.

The vertex `pathEnd (a + b + 1)` goes to `Sum.inl (pathEnd a)` and the vertex
`pathStart (a + b + 1)` goes to `Sum.inr (pathStart b)`, so the two ends of the bridging edge,
`Sum.inl (pathStart a)` and `Sum.inr (pathEnd b)`, are the vertices numbered `a` and `a + 1` of the
long path. -/
def pathSplitIso (a b : ℕ) :
    pathG (a + b + 1) ≃g bridge (pathG a) (pathG b) (pathStart a) (pathEnd b) :=
  RelIso.trans (pathGCongr (splitLen a b)) (pathSplitIsoAux a b)

/-- `pathSplitIso` is the recursively defined bijection, read through the identification
`a + b + 1 = b + a + 1`. Not a `simp` lemma: it exposes the construction. -/
lemma pathSplitIso_apply (a b : ℕ) (x : PathV (a + b + 1)) :
    pathSplitIso a b x = pathSplitEquiv a b (pathGCongr (splitLen a b) x) := rfl

/-- The pendant end of the path lands on the pendant end of the left-hand piece. -/
@[simp] lemma pathSplitIso_pathEnd (a b : ℕ) :
    pathSplitIso a b (pathEnd (a + b + 1)) = .inl (pathEnd a) := by
  rw [pathSplitIso_apply, pathGCongr_pathEnd, pathSplitEquiv_pathEnd]

/-- The far end of the path lands on the far end of the right-hand piece. -/
@[simp] lemma pathSplitIso_pathStart (a b : ℕ) :
    pathSplitIso a b (pathStart (a + b + 1)) = .inr (pathStart b) := by
  rw [pathSplitIso_apply, pathGCongr_pathStart, pathSplitEquiv_pathStart]

/-- The bridging edge really is an edge of the path: its two ends are adjacent vertices of
`pathG (a + b + 1)`. -/
theorem adj_pathSplitIso_symm (a b : ℕ) :
    (pathG (a + b + 1)).Adj ((pathSplitIso a b).symm (.inl (pathStart a)))
      ((pathSplitIso a b).symm (.inr (pathEnd b))) :=
  (pathSplitIso a b).symm.map_rel_iff.mpr bridge_adj_bridge

/-! ### The counting corollary -/

/-- **The number of list colorings of a path, cut at an edge.** For every list assignment `M` of the
path of length `a + b + 1`, the count is the count of the bridged union of the two pieces along the
transported list assignment `M ∘ (pathSplitIso a b).symm`.

This is the form consumed by Lemma 3(c): rewrite `col(P, M)` as a count on a bridge, apply Lemma 2
(`SimpleGraph.exists_nested_of_bridge`, `SimpleGraph.col_swapRight_lt`), then come back along
`col_bridge_pathSplit`. -/
theorem col_pathG_split (a b : ℕ) (M : ListAssignment (PathV (a + b + 1))) :
    (pathG (a + b + 1)).col M
      = (bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)).col
          (M ∘ (pathSplitIso a b).symm) :=
  (col_comp_iso (pathSplitIso a b).symm M).symm

/-- The converse transport: a list assignment `N` of the bridged union is counted by the path along
`N ∘ pathSplitIso a b`. -/
theorem col_bridge_pathSplit (a b : ℕ) (N : ListAssignment (PathV a ⊕ PathV b)) :
    (pathG (a + b + 1)).col (N ∘ pathSplitIso a b)
      = (bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)).col N :=
  col_comp_iso (pathSplitIso a b) N

/-- Transporting an `n`-list assignment across the cut preserves all the list sizes. -/
theorem isNListAssignment_comp_pathSplitIso (a b : ℕ)
    {N : ListAssignment (PathV a ⊕ PathV b)} {n : ℕ} (hN : IsNListAssignment N n) :
    IsNListAssignment (N ∘ pathSplitIso a b) n :=
  isNListAssignment_comp_iso (pathSplitIso a b) hN

end ListColoring
