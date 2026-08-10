import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "The Swapping Lemma" =>

%%%
tag := "swapping"
%%%

Source:
[Bridge.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Bridge.lean),
[PathColorable.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/PathColorable.lean).

Lemma 2 is the technical heart of the paper. It says that if a graph splits into two pieces joined
by a single edge, then the lists at the two ends of that edge can be made *nested* — one contained
in the other — without ever increasing the number of colorings. It is what lets later arguments
assume that a count-minimizing assignment has a very rigid shape.

# Bridges

The setting is a graph that falls into two pieces joined by a single edge:

```diagram (cssWidth := "72%")
open Illuminate Diagram in
let v (x y : Float) : Diagram _ := translate x y (circle 8)
let e (x1 y1 x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
-- left piece G, with its distinguished vertex v₀ on the right
let g := [v (-230) 60, v (-230) (-60), v (-150) 0, v (-70) 0]
let gEdges := [e (-230) 60 (-150) 0, e (-230) (-60) (-150) 0, e (-150) 0 (-70) 0,
               e (-230) 60 (-230) (-60)]
-- right piece H, with its distinguished vertex w₀ on the left
let h := [v 70 0, v 150 0, v 230 60, v 230 (-60)]
let hEdges := [e 70 0 150 0, e 150 0 230 60, e 150 0 230 (-60), e 230 60 230 (-60)]
let bridge := [line ⟨-70, 0⟩ ⟨70, 0⟩]
let labels := [translate (-70) 26 (text "v0"), translate 70 26 (text "w0"),
               translate 0 (-30) (text "the bridge"),
               translate (-160) (-96) (text "G"), translate 160 (-96) (text "H")]
(gEdges ++ hEdges ++ bridge ++ g ++ h ++ labels).foldl atop emptyDiagram
```

Cutting that edge disconnects the graph, and the counting factors accordingly.

```lean
open SimpleGraph ListColoring in
example {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (v₀ : V) (w₀ : W) :
    (bridge G H v₀ w₀).Adj (Sum.inl v₀) (Sum.inr w₀) :=
  bridge_adj_bridge

```

Counting across a bridge factors. Fix the color at `v₀`; the two sides are then independent except
that `w₀` must avoid that color. Writing `colAvoid` for the number of colorings giving a specified
vertex anything *other* than a given color:

```lean
open SimpleGraph ListColoring in
example {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]
    {v₀ : V} {w₀ : W} (M : ListAssignment (V ⊕ W)) (c : ℕ) :
    (bridge G H v₀ w₀).colFix M (Sum.inl v₀) c
      = G.colFix (M ∘ Sum.inl) v₀ c * H.colAvoid (M ∘ Sum.inr) w₀ c :=
  colFix_bridge M c
```

Summing over the color at `v₀` gives the decomposition that everything else is computed from.
Throughout, `colAvoid` and `colFix` are related additively rather than by subtraction, which keeps
the whole development inside `ℕ`:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : ListAssignment V) (v : V) (c : ℕ) :
    G.colAvoid L v c + G.colFix L v c = G.col L :=
  colAvoid_add_colFix L v c
```

# The swap

Suppose the two lists at the bridge are not nested: there is a color `c₁` available at `v₀` but not
at `w₀`, and a color `c₂` available at `w₀` but not at `v₀`. Swap `c₁` and `c₂` throughout the lists
on the `w₀` side only. Transpositions are injective, so no list changes size:

```lean
open SimpleGraph ListColoring in
example {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (M : ListAssignment (V ⊕ W)) (c₁ c₂ : ℕ) (x : V ⊕ W) :
    (swapRight M c₁ c₂ x).card = (M x).card :=
  card_swapRight M c₁ c₂ x
```

and the count strictly drops by a computable amount — the paper's equation (1), here in additive
form:

```lean
open SimpleGraph ListColoring in
example {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]
    {v₀ : V} {w₀ : W} (M : ListAssignment (V ⊕ W)) {c₁ c₂ : ℕ}
    (h₁ : c₁ ∈ M (Sum.inl v₀)) (h₁' : c₁ ∉ M (Sum.inr w₀)) (h₂' : c₂ ∉ M (Sum.inl v₀)) :
    (bridge G H v₀ w₀).col (swapRight M c₁ c₂)
        + G.colFix (M ∘ Sum.inl) v₀ c₁ * H.colFix (M ∘ Sum.inr) w₀ c₂
      = (bridge G H v₀ w₀).col M :=
  col_swapRight_add M h₁ h₁' h₂'
```

Read that as: the swapped count, plus the number of colorings that used `c₁` at `v₀` and `c₂` at
`w₀`, equals the original count. Those are exactly the colorings the swap destroys.

Mechanizing this turned up something about the hypotheses. The identity does **not** need
`c₂ ∈ M(w₀)`. Only three facts are used: `c₁` is available at `v₀`, `c₁` is not available at `w₀`,
and `c₂` is not available at `v₀`. If `c₂` happens to be absent from `w₀`'s list too, the correction
term is zero and the identity degenerates into the true but empty statement that the swap changed
nothing. The hypothesis `c₂ ∈ M(w₀)` is not redundant in the lemma as a whole — it is what makes the
swap actually decrease the nesting defect — but it plays no part in the counting identity.

# Iterating to nestedness

Each swap moves `c₁` into `w₀`'s list, so it strictly decreases the number of colors available at
`v₀` but not at `w₀`. Iterating terminates, and Lemma 2 is the result:

```lean
open SimpleGraph ListColoring in
example {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]
    {v₀ : V} {w₀ : W} (M : ListAssignment (V ⊕ W)) :
    ∃ M', (∀ x, (M' x).card = (M x).card) ∧
      (M' (Sum.inl v₀) ⊆ M' (Sum.inr w₀) ∨ M' (Sum.inr w₀) ⊆ M' (Sum.inl v₀)) ∧
      (bridge G H v₀ w₀).col M' ≤ (bridge G H v₀ w₀).col M :=
  exists_nested_of_bridge M
```

The termination argument has a wrinkle that the informal phrasing hides, and it is instructive. The
obvious measure is the number of colors at `v₀` not available at `w₀`. When it reaches zero, the
first list is contained in the second and we are done. But the process can also halt with the
measure still positive — when the *second* list is contained in the first and there is simply no
`c₂` to swap. The paper's own phrasing anticipates this: it says to repeat "as long as
`L(v₁) ⊄ L(v₂)` and `L(v₂) ⊄ L(v₁)`", which is exactly the right loop condition. A naive induction
on the measure is what goes wrong, and the second disjunct has to be produced directly.

# Strict monotonicity on paths

One more tool is needed later. If one assignment is contained in another pointwise, every coloring
of the first is a coloring of the second, so the count cannot decrease. On a path, if the
containment is anywhere strict and all lists have at least two colors, the count *strictly*
increases:

```lean
open SimpleGraph ListColoring in
example (k : ℕ) {L L' : ListAssignment (PathV k)}
    (hsub : ∀ v, L v ⊆ L' v) (hne : L ≠ L') (hcard : ∀ v, 2 ≤ (L' v).card) :
    (pathG k).col L < (pathG k).col L' :=
  col_lt_col_of_ssubset k hsub hne hcard
```

That is Lemma 4. The proof needs a witness: a coloring from the bigger assignment that uses the
extra color. It exists because a path with lists of size at least two is colorable even with one
vertex's color prescribed in advance — a greedy argument, and one of the few places in this
development where an honest graph-theoretic induction is unavoidable rather than a consequence of
the counting identities.
