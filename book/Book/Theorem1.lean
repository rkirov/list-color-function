import VersoManual
import Book.Papers
import Monophilic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Theorem 1: Cycles" =>

%%%
tag := "theorem1"
%%%

Source: [Cycle.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Cycle.lean), [Recurrence.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Recurrence.lean), [CycleMonophilic.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/CycleMonophilic.lean), [CycleRotate.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/CycleRotate.lean), [ListColorFunction.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/ListColorFunction.lean).

This chapter states the first main theorem of Kirov and Naimi {citep kirovNaimi}[] and explains what
makes it hard. The proof is in Part II; nothing here is proved, only said precisely.

# The statement

*Every cycle is `n`-monophilic, for every `n`.*

In this development a cycle is a path with its two ends joined, and `closePath k` has `k + 1`
vertices, so `2 ≤ k` says the cycle is a genuine one — at least a triangle.

```lean
open Monophilic in
example {k m : ℕ} (hk : 2 ≤ k) : (closePath k).Monophilic (m + 2) :=
  monophilic_closePath_of_two_le hk
```

The `m + 2` is how `n ≥ 2` is written without a side condition. The cases `n = 0` and `n = 1` are
true for a different and duller reason — with at most one colour available and at least one edge
present there are no colourings at all — so the theorem also holds with no hypothesis on `n`
whatever:

```lean
open Monophilic in
example (k n : ℕ) (hk : 2 ≤ k) : (closePath k).Monophilic n :=
  monophilic_closePath_all k n hk
```

In the language of the literature, the list colour function of a cycle equals its chromatic
polynomial, everywhere:

```lean
open Monophilic in
example (k n : ℕ) (hk : 2 ≤ k) :
    (closePath k).listColorFunction n = (closePath k).colConst n :=
  listColorFunction_closePath k n hk
```

# Why it is not obvious

Three reasons, each worth understanding before reading any proof.

*Cycles have no simplicial vertex.* Every vertex of a cycle of length four or more has two
neighbours which are not adjacent to each other. So the argument of
{ref "chordal"}[the previous chapter] never starts. There is no vertex whose removal is a cone over
a clique, and the count does not factor.

*Monophilicity is not inherited.* It is not a monotone property: a subgraph of a monophilic graph
need not be monophilic, and neither need a supergraph. So the fact that a cycle is a path plus one
edge, and that paths are trees and hence monophilic, gives exactly nothing.

*The result is tight, in a way that rules out soft arguments.* Attach one more path of length two
between two vertices of a `4`-cycle and you get $`\theta_{2,2,4}`, which is *not* `2`-monophilic —
as {ref "lists"}[the previous chapter] showed with an explicit assignment. So no argument that
proves Theorem 1 can be robust under adding an edge or a path, and any proof must use the cycle
structure closely.

There is a fourth reason, and it is the one that shapes the whole proof. Delete a vertex from a
cycle and fix its colour. What remains is a *path*, but the list assignment on that path is no
longer uniform: the two vertices adjacent to the deleted one have each lost one colour. So the very
first step of any recursion leaves the class of uniform assignments and lands in the class of
assignments where two distinguished vertices have `n - 1` colours and everything else has `n`.

Controlling *those* is the content of the proof, and it needs two numbers.

# The two shapes, and the numbers $`A_k` and $`B_k`

Call a list assignment on a path an `(n, n-1)`-*assignment* when the two end vertices get `n - 1`
colours and every interior vertex gets `n`.

```lean
open SimpleGraph Monophilic in
example {k m : ℕ} {L : ListAssignment (PathV k)} (hL : IsNNAssign k m L) :
    (L (pathEnd k)).card = m + 1 :=
  hL.card_pathEnd
```

Among these there is a special family: all the interior lists equal to one common palette `S` of
size `n`, and the two end lists equal to `S` minus one colour each. If the two missing colours are
the *same* the assignment has *type A*; if they are different, *type B*.

```diagram (cssWidth := "94%")
open Illuminate Diagram in
let v (x y : Float) : Diagram _ := translate x y (circle 9)
let e (x1 y1 x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
let edges :=
  [e (-240) 70 (-120) 70, e (-120) 70 0 70, e 0 70 120 70, e 120 70 240 70,
   e (-240) (-70) (-120) (-70), e (-120) (-70) 0 (-70), e 0 (-70) 120 (-70),
   e 120 (-70) 240 (-70)]
let verts :=
  [v (-240) 70, v (-120) 70, v 0 70, v 120 70, v 240 70,
   v (-240) (-70), v (-120) (-70), v 0 (-70), v 120 (-70), v 240 (-70)]
let labelsA :=
  [translate (-240) 102 (text "S-{1}"), translate (-120) 102 (text "S"),
   translate 0 102 (text "S"), translate 120 102 (text "S"),
   translate 240 102 (text "S-{1}"), translate (-350) 70 (text "type A")]
let labelsB :=
  [translate (-240) (-38) (text "S-{1}"), translate (-120) (-38) (text "S"),
   translate 0 (-38) (text "S"), translate 120 (-38) (text "S"),
   translate 240 (-38) (text "S-{2}"), translate (-350) (-70) (text "type B")]
(edges ++ verts ++ labelsA ++ labelsB).foldl atop emptyDiagram
```

Write $`A_k` for the number of colourings of a type A assignment on the path with `k` edges, and
$`B_k` for a type B one. Neither depends on which colours were removed — only on whether they agree
— which is already a small theorem, and it is what makes the two numbers well defined:

```lean
open Monophilic in
example (m : ℕ) : ∀ (k x y : ℕ), x < m + 2 → y < m + 2 →
    (pathG k).col (pathAssign k (m + 2) x y)
      = if x = y then pathA m k else pathB m k :=
  col_pathAssign m
```

They satisfy a coupled recursion, obtained by deleting the end vertex and splitting on its colour.
With `n = m + 2`:

```lean
open Monophilic in
example (m : ℕ) : pathA m 0 = m + 1 := rfl
```

```lean
open Monophilic in
example (m k : ℕ) : pathA m (k + 1) = (m + 1) * pathB m k := rfl
```

```lean
open Monophilic in
example (m : ℕ) : pathB m 0 = m := rfl
```

```lean
open Monophilic in
example (m k : ℕ) : pathB m (k + 1) = pathA m k + m * pathB m k := rfl
```

For `n = 3` the first few values are:

:::table +header (align := left)
*
  * `k`
  * `0`
  * `1`
  * `2`
  * `3`
  * `4`
*
  * $`A_k`
  * `2`
  * `2`
  * `6`
  * `10`
  * `22`
*
  * $`B_k`
  * `1`
  * `3`
  * `5`
  * `11`
  * `21`
:::

```lean
open Monophilic in
example : pathA 1 2 = 6 := by decide
```

```lean
open Monophilic in
example : pathB 1 2 = 5 := by decide
```

The pattern in the table is the key identity of the whole argument: the two numbers differ by
exactly one, and *which is larger alternates with the parity of `k`*.

```lean
open Monophilic in
example (m k : ℕ) : ((pathA m k : ℤ) - (pathB m k : ℤ)) = (-1) ^ k :=
  pathA_sub_pathB m k
```

So the minimum of the two is $`A_k` for odd `k` and $`B_k` for even `k`:

```lean
open Monophilic in
example (m k : ℕ) :
    min (pathA m k) (pathB m k) = if Even k then pathB m k else pathA m k :=
  min_pathA_pathB_eq m k
```

A closed form follows by solving the recursion. It is stated with the division cleared, so that it
is an identity in $`\mathbb{Z}` rather than a statement about rounding:

```lean
open Monophilic in
example (m k : ℕ) :
    ((m + 2) * pathA m k : ℤ) = (m + 1) * ((m + 1) ^ (k + 1) + (-1) ^ k) :=
  pathA_closed_form m k
```

That is $`A_k = \frac{(n-1)\bigl((n-1)^{k+1} + (-1)^k\bigr)}{n}` in the paper's notation.

# The cycle count

Now close the path up. Delete one vertex of the cycle and fix its colour: the two neighbours each
lose that colour, everything else keeps the full palette, and that is a type A assignment on the
path that remains. There are `n` choices of colour for the deleted vertex, so:

```lean
open Monophilic in
example (m k : ℕ) (hk : 1 ≤ k) :
    (closePath k).colConst (m + 2) = (m + 2) * pathA m (k - 1) :=
  colConst_closePath m k hk
```

which is the paper's $`\mathrm{col}(C, n) = n \cdot A_{k-2}` with the indices shifted to this
development's convention. Combined with the closed form for $`A_k`, this is the familiar chromatic
polynomial of a cycle:

```lean
open Monophilic in
example (m k : ℕ) :
    (((closePath (k + 1)).colConst (m + 2) : ℤ))
      = ((m + 1) : ℤ) ^ (k + 2) + (-1) ^ (k + 2) * ((m + 1) : ℤ) :=
  colConst_closePath_chromatic m k
```

A check, at `n = 3` on the four-cycle: $`2^4 + 2 = 18`, and also $`3 \cdot A_2 = 3 \cdot 6 = 18`.

```lean
open Monophilic in
example : (closePath 3).colConst 3 = 18 := by decide
```

# Theorem 1, in the notation of the literature

Putting the theorem and the closed form together gives the sharpest statement of what has been
proved: for the cycle on `v` vertices and `n` colours, *no* `n`-list assignment admits fewer than
$`(n-1)^v + (-1)^v (n-1)` colourings, and the uniform one achieves that bound.

```lean
open Monophilic in
example (m k : ℕ) (hk : 1 ≤ k) :
    (((closePath (k + 1)).listColorFunction (m + 2) : ℤ))
      = ((m + 1) : ℤ) ^ (k + 2) + (-1) ^ (k + 2) * ((m + 1) : ℤ) :=
  listColorFunction_closePath_chromatic m k hk
```

# What the proof requires

For orientation, since the chapters of Part II are organized around these pieces rather than around
the statement.

*A lower bound for all `(n, n-1)`-assignments, not just the two special shapes.* This is Lemma 3(b):
every `(n,n-1)`-assignment on a path admits at least $`\min(A_k, B_k)` colourings. It is proved by
showing that a *minimizing* assignment must have the special shape, which needs two further tools:
that minimizers exist at all, and a swapping argument showing that if two adjacent lists are not
nested then some other assignment does strictly better ({ref "swapping"}[the swapping chapter]).

*The parity refinement.* Lemma 3(c) says a minimizing assignment is type A for odd `k` and type B
for even `k` — which, given $`A_k - B_k = (-1)^k`, is exactly the statement that the minimizer
realizes the smaller of the two. This is where the hypothesis "path of length at least one" becomes
load-bearing, as the {ref "cycles"}[cycles chapter] records.

*The even case is tight.* When the cycle has an even number of vertices the obvious bound — one
fibre contributes at least $`A+1`, the rest at least `B` — gives $`nA - n + 2`, which is *less* than
the required $`nA`. The argument that works is stronger and has no slack in it at all.

*The case `n = 2` is separate.* It touches none of the $`A_k`/$`B_k` machinery, running instead on
a forcing relation along the path, and it is the one place where the freedom to choose *which* edge
to delete is genuinely needed — supplied by a rotation automorphism of the cycle.
