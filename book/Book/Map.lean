import VersoManual
import Book.Papers
import ListColoring

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

The book is in two parts. *Part I* tells the story, from the definition of a proper colouring to a
guide to `comparator/Challenge.lean`; it states results and explains them, and proves nothing. It
begins at {ref "colouring"}[Colouring a Graph] and ends at
{ref "readingchallenge"}[Reading `Challenge.lean`]. *Part II* is the proofs, and its chapters are
ordered by dependency rather than by the paper's section order: {ref "counting"}[Counting List
Colorings] comes first because every later chapter needs its definitions, and the material on cores
and $`K_{2,3}` is deferred until after Theorem 1 even though the paper introduces it earlier.

This chapter is orientation for Part II. If you are reading for the mathematics rather than for the
formalization, skip it and start at {ref "colouring"}[Colouring a Graph].

Every displayed Lean block is an `example` whose proof is the corresponding theorem in the
development. That means two things for you as a reader. First, the statements you see are the
statements that were actually proved — not paraphrases. Second, if a theorem is ever renamed or its
hypotheses change, this book stops building, so the prose cannot silently drift out of date.

There is a second check, aimed at a different failure. An `example` keeps a displayed *statement*
honest, but a sentence that merely names a declaration is only text, and it would survive that
declaration being deleted. So the names in the table below, and the load-bearing names elsewhere in
the prose, are written as resolved references: each is elaborated when the book is built, and a name
that no longer exists is a build error rather than a piece of stale typography.
{ref "reference"}[The last chapter] does the same job in bulk, by rendering the declarations
themselves.

You do not need to read Lean to follow the mathematics. Each displayed statement is explained in
the surrounding text, and the Lean is there so you can check that the explanation is honest.

# The shape of the development

Everything rests on one number: for a graph $`G` and a list assignment $`L`, the count
$`\mathrm{col}(G, L)` of proper colorings drawing each vertex's color from its own list. Two pieces
of infrastructure do most of the work, and almost every later result is one of them applied in a
particular shape.

```diagram (cssWidth := "88%")
open Illuminate Diagram in
let box (x y : Float) (s : String) : Diagram SVG :=
  atop (translate x y (rect 150 34)) (translate x y (text s))
let arrow (x1 y1 x2 y2 : Float) : Diagram SVG := line ⟨x1, y1⟩ ⟨x2, y2⟩
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

The *deletion identity* says that the colorings giving a fixed color to a fixed vertex are exactly
the colorings of the graph with that vertex removed, from the lists that have lost that color at
each neighbour. Summing over the color turns it into a recursion, and every count in the development
is ultimately computed by iterating it.

The *cone construction* attaches a new vertex to a chosen set of existing ones. Used with a clique
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
  * {name}`SimpleGraph.ECCAt.coneOn`
  * [Cone.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Cone.lean)
*
  * Kostochka–Sidorenko
  * {name}`SimpleGraph.ecc_cliqueTower_of_isEmpty`
  * [Chordal.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Chordal.lean)
*
  * Lemma 2
  * {name}`SimpleGraph.exists_nested_of_bridge`
  * [Bridge.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Bridge.lean)
*
  * Lemma 3(a)
  * {name}`ListColoring.col_pathAssign`, {name}`ListColoring.pathA_closed_form`
  * [PathCount.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/PathCount.lean), [Recurrence.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Recurrence.lean)
*
  * Lemma 3(b)
  * {name}`ListColoring.min_pathA_pathB_le_col`
  * [PathMinimizing.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/PathMinimizing.lean)
*
  * Lemma 3(c)
  * {name}`ListColoring.isPathShape_parity_of_minimizing`
  * [PathMinimizing.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/PathMinimizing.lean)
*
  * Lemma 4
  * {name}`ListColoring.col_lt_col_of_ssubset`
  * [PathColorable.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/PathColorable.lean)
*
  * *Theorem 1*
  * {name}`ListColoring.ecc_closePath_of_two_le`
  * [CycleRotate.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/CycleRotate.lean)
*
  * Lemma 5
  * {name}`SimpleGraph.ecc_pendantTower_iff`
  * [Core.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Core.lean)
*
  * Lemma 6
  * {name}`SimpleGraph.ecc_K23`
  * [K23.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/K23.lean)
*
  * *Theorem 2*
  * {name}`ListColoring.ecc_two_iff`
  * [RubinProof.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/RubinProof.lean)
*
  * *Rubin's theorem*
  * {name}`ListColoring.rubinTheorem`
  * [RubinProof.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/RubinProof.lean)
*
  * Rubin, steps 1–6
  * {name}`ListColoring.rubin_structure`
  * [RubinCases.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/RubinCases.lean)
*
  * the core exists
  * {name}`ListColoring.hasCore`
  * [CoreExtract.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/CoreExtract.lean)
*
  * §5 building block
  * {name}`SimpleGraph.ERT.not_choosable`
  * [NotChoosable.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/NotChoosable.lean)
*
  * *§5: `n`-choosable, not enumeratively chromatic-choosable at `n`*
  * {name}`SimpleGraph.KN5.exists_choosable_not_ecc_of_two_le`
  * [Section5.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Section5.lean)
*
  * §5 Lemmas 7 and 10, for the paper's $`H_{n+1}`
  * {name}`SimpleGraph.KN5.exists_choosable_not_ecc`
  * [Section5.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Section5.lean)
:::

# The core vocabulary

Four definitions carry the whole development. They live in
[Defs.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Defs.lean).

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
  * `G.ECCAt n`
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
```

That elaborates every proof and, because each file ends with a block of `#print axioms` lines for
the results it establishes, prints their axiom dependencies as it goes. All of them should read
`[propext, Classical.choice, Quot.sound]` — Lean's three standard axioms and nothing else. In
particular `sorryAx` never appears, which is what rules out an incomplete proof.

The authoritative check is stronger than an axiom audit and is a separate script:

```
./verify.sh
```

This runs `leanprover/comparator` against the `comparator/` workspace: it checks that the
statements in `comparator/Challenge.lean` really are the ones the library proves, that the
permitted axioms are exactly the three above, and it replays the proofs through two independent
kernels — `lean4export` in a sandbox, and the `nanoda` kernel. Continuous integration runs it on
every push, alongside a grep that fails if `sorry`, `admit` or `native_decide` ever appears in the
library sources. {ref "readingchallenge"}[Reading `Challenge.lean`] is a guide to the eleven
statements that check covers.
