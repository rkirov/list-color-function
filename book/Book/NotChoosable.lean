import VersoManual
import Book.Papers
import Monophilic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Colorable but Not Choosable" =>

%%%
tag := "notchoosable"
%%%

Source: [NotChoosable.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/NotChoosable.lean).

Section 5 of the paper constructs, for each `n`, a graph that is `n`-choosable but *not*
`n`-monophilic — showing that the two notions, which the characterization of `2`-monophilic graphs
makes look almost identical, genuinely come apart. The construction is assembled from many copies of
one building block: a complete bipartite graph that is `n`-colorable but not `n`-choosable. This
chapter formalizes that block.

# The separating assignment

Take the complete bipartite graph with `n` vertices on one side and `nⁿ` on the other. The trick is
to index the large side by *functions* `Fin n → Fin n`, so that "there are `nⁿ` of them" is a fact
about the type rather than an arithmetic side condition:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) : Fintype.card (Fin n → Fin n) = n ^ n :=
  card_right n
```

Now assign lists as follows. The `i`-th vertex on the small side gets the `i`-th block of `n`
consecutive colours, so the small side's lists are pairwise disjoint. The vertex indexed by `φ` on
the large side gets one colour from each block, namely the one `φ` selects. Every list has exactly
`n` colours:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) : IsNListAssignment (L₀ n) n :=
  isNListAssignment_L₀ n
```

And there are no colorings at all:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) : (K n).col (L₀ n) = 0 :=
  col_L₀_eq_zero n
```

The argument is short and does not need induction. A proper coloring must choose, at each small-side
vertex `i`, some colour from the `i`-th block — that is, it determines a function `φ`. Now look at
the *single* large-side vertex indexed by that very `φ`. Its list is exactly the set of colours the
coloring has just used on the small side, and it is adjacent to all of them. So it has nothing left,
and no such coloring exists. The large side is precisely large enough to enumerate every possible
choice and block each one.

# The separation

Consequently the graph is not `n`-choosable:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) : ¬ (K n).Choosable n :=
  not_choosable n
```

but it is `n`-colorable, being bipartite:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) (hn : 2 ≤ n) : (K n).Colorable n :=
  colorable n hn
```

So it sits squarely in the regime identified in the first chapter — colorable but not choosable —
and is therefore not monophilic:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) (hn : 2 ≤ n) : ¬ (K n).Monophilic n :=
  not_monophilic n hn
```

This last line is a one-liner from the three-regime observation, but it is worth pausing on: it is a
complete, if easy, instance of the paper's theme. What Section 5 goes on to do is much harder —
build a graph that *is* `n`-choosable and still fails to be `n`-monophilic, so that the failure
cannot be explained away by non-choosability. That construction, which stacks `n²` copies of this
block underneath a complete bipartite graph, is not yet formalized.

# A note on the arithmetic

One small thing worth recording, because it is a recurring trap. The proof needs that
`a * n + c = b * n + d` with `c, d < n` forces `a = b` and `c = d`. This is exactly the uniqueness of
division with remainder, and it is *not* something `omega` can do: `a * n` is nonlinear, with both
factors variable, and `omega` handles only linear integer arithmetic. The fix is to go through
`Nat.div` and `Nat.mod` explicitly rather than to look for a stronger tactic.
