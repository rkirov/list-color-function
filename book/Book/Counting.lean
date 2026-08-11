import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Counting List Colorings" =>

%%%
tag := "counting"
%%%

Source: [Defs.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Defs.lean),
[Rename.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Rename.lean),
[Basic.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Basic.lean),
[Delete.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Delete.lean),
[Sum.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Sum.lean).

The whole subject rests on one number. Given a graph `G` and, for each vertex, a finite list of
permitted colors, how many proper colorings draw each vertex's color from its own list? Everything
else — enumerative chromatic-choosability, the recurrences, the theorems — is a statement about how
that number moves as the lists move.

So the first decision is how to make that number a Lean object, and it is worth dwelling on,
because the obvious choice is the wrong one.

# Why not `SimpleGraph.Coloring`

Mathlib already has proper colorings. `SimpleGraph.Coloring G α` is defined as a graph homomorphism
`G →g completeGraph α` — a bundled structure. It is a good definition for reasoning about
*existence* of colorings, which is what `Colorable` and `chromaticNumber` need.

It is a bad definition for *counting* them. Counting requires a `Fintype` instance, and at the
Mathlib revision this development is built against there is none for the bundled hom type. There is
also a second, subtler problem: our lists vary from vertex to vertex, and `Coloring G α` has a
single color type `α` for the whole graph. The list constraint would have to be bolted on afterwards
as a predicate, which puts it exactly where it is least convenient.

We count functions instead. A coloring is a plain `V → ℕ`, and the colorings drawn from a list
assignment `L` are cut out of the finite set of all list-respecting functions by properness:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : ListAssignment V) :
    G.colorings L = (Fintype.piFinset L).filter G.IsProperColoring :=
  rfl
```

`Fintype.piFinset L` is the finite set of dependent functions choosing one element from each `L v`,
so the list constraint is definitional rather than an extra hypothesis. The count is then just a
cardinality, and `col` and its uniform special case `colConst` fall out:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    G.colConst n = G.col (constList V n) :=
  rfl
```

The bundled `Coloring` type does not disappear — it reappears in exactly one place, as the bridge
that connects this counting world back to Mathlib's existence world:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    0 < G.colConst n ↔ G.Colorable n :=
  colConst_pos_iff_colorable
```

# Enumerative chromatic-choosability

A graph is enumeratively chromatic-choosable at `n` when giving every vertex the *same* list of `n`
colors minimizes the count, over all ways of handing out lists of size `n`. The name is the paper's:
the graph "loves sameness".

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    G.ECCAt n ↔ ∀ L : ListAssignment V, IsNListAssignment L n → G.colConst n ≤ G.col L :=
  Iff.rfl
```

Kostochka and Sidorenko {citep kostochkaSidorenko}[] asked which graphs have this property, and
observed that chordal graphs do. Donner {citep donner}[] showed every graph is enumeratively
chromatic-choosable at `n` once `n` is large enough. The paper this book accompanies
{citep kirovNaimi}[] settles cycles for all `n`, characterizes the graphs that are enumeratively
chromatic-choosable at `2`, and shows that `n`-choosability does not imply enumerative
chromatic-choosability at `n`.

Before any of that, three easy observations locate the interesting range. If `n` is below the
chromatic number there are no colorings from the uniform list at all, so the inequality holds
vacuously:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ} (h : ¬ G.Colorable n) :
    G.ECCAt n :=
  ecc_of_not_colorable h
```

If `n` is at least the chromatic number but below the *list* chromatic number, there is some
`n`-assignment with no colorings at all, while the uniform list has some — so enumerative
chromatic-choosability fails:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}
    (hcol : G.Colorable n) (hch : ¬ G.Choosable n) :
    ¬ G.ECCAt n :=
  not_ecc_of_colorable_of_not_choosable hcol hch
```

Everything interesting therefore happens at or above the list chromatic number.

# Renaming colors

The paper is full of sentences like "without loss of generality `L(x) = {1,2}`". Each one is an
appeal to the fact that the count depends on the lists only up to renaming the colors. Mechanized,
this cannot be waved through; it has to be a lemma, and it is used constantly enough to be worth
proving in the sharpest available form.

The sharp form does not ask for a bijection of `ℕ`. It asks only for a function injective on the
colors that actually occur somewhere in the lists:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : ListAssignment V} {e : ℕ → ℕ}
    (he : Set.InjOn e (⋃ v, (L v : Set ℕ))) :
    G.col (fun v => (L v).image e) = G.col L :=
  col_image_of_injOn he
```

That generality matters. Later, the swap step of Lemma 2 renames colors on only one side of a
bridge, and the transposition it uses is injective everywhere, but the *statement* that gets applied
is about the lists on that side only.

The consequence that licenses the paper's "WLOG" is that any `n`-element palette computes the same
number as the standard one:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset ℕ} {n : ℕ} (hs : s.card = n) :
    G.col (fun _ => s) = G.colConst n :=
  col_const_eq_colConst hs
```

# The deletion identity

One identity does most of the work in the paper's third section. Fix a vertex and a color for it;
the colorings that make that choice are exactly the colorings of the graph with that vertex deleted,
from the lists that have lost the chosen color at each neighbor. The paper calls the shrunken
assignment the *induced* one.

```diagram (cssWidth := "88%")
open Illuminate Diagram in
let v (x y : Float) : Diagram SVG := translate x y (circle 8)
let e (x1 y1 x2 y2 : Float) : Diagram SVG := line ⟨x1, y1⟩ ⟨x2, y2⟩
-- left: the whole graph, with the chosen vertex on the left and its three neighbours
let left :=
  [e 0 0 90 70, e 0 0 90 0, e 0 0 90 (-70), e 90 70 170 0, e 90 (-70) 170 0, e 90 0 170 0,
   v 0 0, v 90 70, v 90 0, v 90 (-70), v 170 0,
   translate 0 (-28) (text "v, coloured c"),
   translate 130 100 (text "neighbours of v")]
-- right: the same graph with v deleted; its neighbours have lost the colour c
let right :=
  [e 90 70 170 0, e 90 (-70) 170 0, e 90 0 170 0,
   v 90 70, v 90 0, v 90 (-70), v 170 0,
   translate 130 100 (text "each list has lost c")]
   |>.map (translate 330 0)
let arrow := [line ⟨210, 0⟩ ⟨390, 0⟩, translate 300 22 (text "delete v")]
(left ++ right ++ arrow).foldl atop emptyDiagram
```

Formalizing it requires deciding what "delete a vertex" means, and here there is a choice that pays
off repeatedly. Deleting a vertex from a graph on `V` naturally lands on a subtype, which drags
`Fintype` and `DecidableEq` instances along with it and makes every subsequent rewrite awkward.
Instead we arrange for the deleted vertex to be `none : Option V`, so that the graph after deletion
lives on `V` itself:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph (Option V)) [DecidableRel H.Adj]
    (M : ListAssignment (Option V)) {c : ℕ} (hc : c ∈ M none) :
    H.colFix M none c = (H.delNone).col (H.inducedList M c) :=
  colFix_none_eq_col_delNone H M hc
```

Summing over the color given to the deleted vertex turns this into a recursion, and that recursion
is the engine of everything that follows:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph (Option V)) [DecidableRel H.Adj] (M : ListAssignment (Option V)) :
    H.col M = ∑ c ∈ M none, (H.delNone).col (H.inducedList M c) :=
  col_eq_sum_delNone H M
```

Read from left to right this is a case split on one vertex's color. Read from right to left it is
the statement that a graph's count is determined by the counts of a smaller graph. Every count in
this development is ultimately computed by iterating it.

# Multiplicativity

The last piece of general theory: counts multiply over disjoint unions.

```lean
open SimpleGraph in
example {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (M : ListAssignment (V ⊕ W)) :
    (G ⊕g H).col M = G.col (M ∘ Sum.inl) * H.col (M ∘ Sum.inr) :=
  col_sum G H M
```

This is what stands behind the paper's remark that a graph is enumeratively chromatic-choosable at
`n` exactly when each of its connected components is, and it is what makes the bridge decomposition
of the next chapter possible.
