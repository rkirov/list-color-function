import VersoManual
import Book.Papers
import Monophilic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true

#doc (Manual) "Map of the Formalization" =>

%%%
tag := "map"
%%%

This chapter is for orientation: what is where, what depends on what, and how to get from a
statement in the paper to the Lean proof of it.

# How to read this

The chapters are ordered by dependency, not by the paper's section order. In particular
{ref "counting"}[Counting List Colorings] comes first because every later chapter needs its
definitions, and the material on cores and $`K_{2,3}` is deferred until after Theorem 1 even though
the paper introduces it earlier.

Every displayed Lean block is an `example` whose proof is the corresponding theorem in the
development. That means two things for you as a reader. First, the statements you see are the
statements that were actually proved — not paraphrases. Second, if a theorem is ever renamed or its
hypotheses change, this book stops building, so the prose cannot silently drift out of date.

You do not need to read Lean to follow the mathematics. Each displayed statement is explained in
the surrounding text, and the Lean is there so you can check that the explanation is honest.

# The shape of the development

Everything rests on one number: for a graph $`G` and a list assignment $`L`, the count
$`\mathrm{col}(G, L)` of proper colorings drawing each vertex's color from its own list. Two pieces
of infrastructure do most of the work, and almost every later result is one of them applied in a
particular shape.

```diagram (cssWidth := "88%")
open Illuminate Diagram in
let box (x y : Float) (s : String) : Diagram _ :=
  atop (translate x y (rect 150 34)) (translate x y (text s))
let arrow (x1 y1 x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
let boxes := [
  box 0 0 "col G L",
  box (-190) (-70) "deletion identity",
  box 190 (-70) "cone over a set",
  box (-190) (-150) "paths, A_k B_k",
  box 190 (-150) "Lemma 1, chordal",
  box (-190) (-230) "Lemma 2, swap",
  box (-190) (-310) "Theorem 1",
  box 190 (-310) "Theorem 2"]
let arrows := [
  arrow 0 (-17) (-190) (-53), arrow 0 (-17) 190 (-53),
  arrow (-190) (-87) (-190) (-133), arrow 190 (-87) 190 (-133),
  arrow (-190) (-167) (-190) (-213),
  arrow (-190) (-247) (-190) (-293),
  arrow (-115) (-310) 115 (-310)]
(arrows ++ boxes).foldl atop emptyDiagram
```

The **deletion identity** says that the colorings giving a fixed color to a fixed vertex are exactly
the colorings of the graph with that vertex removed, from the lists that have lost that color at
each neighbour. Summing over the color turns it into a recursion, and every count in the development
is ultimately computed by iterating it.

The **cone construction** attaches a new vertex to a chosen set of existing ones. Used with a clique
it gives Lemma 1 and the chordal corollary; used with a singleton it gives pendant vertices and
hence cores; used twice on a path it gives the theta graphs of Theorem 2.

# From the paper to the code

Each Lean name below is the exact statement proved; each file link goes to the source.

:::table +header (align := left)
*
  * Paper
  * Lean
  * File
*
  * Lemma 1
  * `SimpleGraph.Monophilic.coneOn`
  * [Cone.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Cone.lean)
*
  * Kostochka–Sidorenko
  * `SimpleGraph.monophilic_cliqueTower_of_isEmpty`
  * [Chordal.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Chordal.lean)
*
  * Lemma 2
  * `SimpleGraph.exists_nested_of_bridge`
  * [Bridge.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Bridge.lean)
*
  * Lemma 3(a)
  * `Monophilic.col_pathAssign`, `Monophilic.pathA_closed_form`
  * [PathCount.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/PathCount.lean), [Recurrence.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Recurrence.lean)
*
  * Lemma 3(b)
  * `Monophilic.min_pathA_pathB_le_col`
  * [PathMinimizing.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/PathMinimizing.lean)
*
  * Lemma 3(c)
  * `Monophilic.isPathShape_parity_of_minimizing`
  * [PathMinimizing.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/PathMinimizing.lean)
*
  * Lemma 4
  * `Monophilic.col_lt_col_of_ssubset`
  * [PathColorable.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/PathColorable.lean)
*
  * **Theorem 1**
  * `Monophilic.monophilic_closePath_of_two_le`
  * [CycleRotate.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/CycleRotate.lean)
*
  * Lemma 5
  * `SimpleGraph.monophilic_pendantTower_iff`
  * [Core.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Core.lean)
*
  * Lemma 6
  * `SimpleGraph.monophilic_K23`
  * [K23.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/K23.lean)
*
  * **Theorem 2**
  * `SimpleGraph.monophilic_two_iff_of_rubin`
  * [Theta.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Theta.lean)
*
  * §5 building block
  * `SimpleGraph.ERT.not_choosable`
  * [NotChoosable.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/NotChoosable.lean)
:::

# The core vocabulary

Four definitions carry the whole development. They live in
[Defs.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Defs.lean).

:::table +header (align := left)
*
  * Name
  * Meaning
*
  * `ListAssignment V`
  * `V → Finset ℕ` — a finite list of permitted colors at each vertex
*
  * `G.colorings L`
  * the `Finset` of proper colorings drawing each vertex's color from its own list
*
  * `G.col L`
  * $`\mathrm{col}(G,L)`, the size of that finset
*
  * `G.colConst n`
  * $`\mathrm{col}(G,n)` — the same count when every list is $`\{0,\dots,n-1\}`
*
  * `G.Monophilic n`
  * $`\mathrm{col}(G,n) \le \mathrm{col}(G,L)` for every $`n`-list assignment $`L`
:::

Two more appear constantly. `G.colFix L v c` counts the colorings sending a chosen vertex `v` to a
chosen color `c` — the paper's $`\mathrm{col}(G,L,v,c)`. And `IsNListAssignment L n` says every list
has exactly $`n` colors.

# Verifying it yourself

```
git clone https://github.com/rkirov/list-color-function
cd list-color-function
lake exe cache get && lake build
lake env lean scripts/AxiomAudit.lean
```

The last line prints the axiom dependencies of every headline result. All of them should read
`[propext, Classical.choice, Quot.sound]` — Lean's three standard axioms and nothing else. In
particular `sorryAx` never appears, which is what rules out an incomplete proof. Continuous
integration runs exactly this check and fails the build if it does not hold.
