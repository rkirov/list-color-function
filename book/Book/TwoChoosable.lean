import VersoManual
import Book.Papers
import Monophilic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Which Graphs Are 2-Choosable?" =>

%%%
tag := "twochoosable"
%%%

Source: [Choosable.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Choosable.lean), [ThetaChoosable.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/ThetaChoosable.lean), [Rubin.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Rubin.lean), [RubinHard.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/RubinHard.lean), [ThetaClass.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/ThetaClass.lean).

The classification of the `2`-monophilic graphs, which is the second main theorem of the paper,
rests on an older classification: which graphs are `2`-choosable? That question was answered by
Erdős, Rubin and Taylor {citep erdosRubinTaylor}[] in 1980, and the answer is usually credited to
Rubin. This chapter states it, says which parts of it are proved in this development, and is candid
about which part is not.

# Pendant vertices do not matter

Start with the reduction that makes a classification possible at all. A vertex of degree one can
always be coloured last: whatever colour its single neighbour took, its own list of two colours
still contains something else. So attaching a pendant vertex changes nothing about `2`-choosability
— nor about `n`-choosability for any `n ≥ 2`:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ} (hn : 2 ≤ n)
    (k : ℕ) (d : TowerData V k) :
    (pendantTower G k d).Choosable n ↔ G.Choosable n :=
  choosable_pendantTower_iff hn k d
```

Repeatedly deleting vertices of degree one until none is left produces the *core* of the graph. The
statement above is that reduction run backwards, which is the form a formalization can use directly:
rather than define a fixpoint of a deletion operation, present the graph as its core with a tower of
pendant attachments on top.

So the classification only has to describe the possible cores, and those have minimum degree at
least two.

# Rubin's list

*A connected graph is `2`-choosable if and only if its core is a single vertex, an even cycle, or
$`\theta_{2,2,2m}` for some $`m \ge 1`.*

```diagram (cssWidth := "96%")
open Illuminate Diagram in
let v (x y : Float) : Diagram _ := translate x y (circle 8)
let e (x1 y1 x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
-- a single vertex
let one := [v (-400) 0, translate (-400) (-46) (text "a single vertex")]
-- an even cycle, drawn as a hexagon
let hex :=
  [e (-80) 0 (-115) 61, e (-115) 61 (-185) 61, e (-185) 61 (-220) 0,
   e (-220) 0 (-185) (-61), e (-185) (-61) (-115) (-61), e (-115) (-61) (-80) 0,
   v (-80) 0, v (-115) 61, v (-185) 61, v (-220) 0, v (-185) (-61), v (-115) (-61),
   translate (-150) (-100) (text "an even cycle")]
-- the theta graph
let th :=
  [e 140 0 205 0, e 205 0 270 0, e 270 0 335 0, e 335 0 400 0,
   e 140 0 270 70, e 270 70 400 0, e 140 0 270 (-70), e 270 (-70) 400 0,
   v 140 0, v 205 0, v 270 0, v 335 0, v 400 0, v 270 70, v 270 (-70),
   translate 270 22 (text "length 2m"),
   translate 270 (-100) (text "theta(2,2,2m)")]
(one ++ hex ++ th).foldl atop emptyDiagram
```

In the development the three families are collected into one predicate, stated up to isomorphism
because each family is built on its own vertex type. Recall that `closePath k` has `k + 1` vertices,
so `Odd k` picks out the cycles on an *even* number of vertices:

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    RubinFamily G ↔ (Subsingleton V ∨
      (∃ k, Odd k ∧ 2 ≤ k ∧ Nonempty (G ≃g closePath k)) ∨
      (∃ m, 1 ≤ m ∧ Nonempty (G ≃g theta m))) :=
  Iff.rfl
```

The smallest theta on the list, $`\theta_{2,2,2}`, is $`K_{2,3}` — two branch vertices joined by
three paths of length two is exactly two vertices each joined to the same three others.

# The easy direction, proved

Everything on Rubin's list really is `2`-choosable:

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : RubinFamily G) :
    G.Choosable 2 :=
  choosable_two_of_rubinFamily G h
```

Its three cases are of quite different weights.

*A single vertex* is `n`-choosable for any `n ≥ 1`, there being no edge to violate.

*An even cycle* is a corollary of Theorem 1 rather than a separate argument, and this is the
pleasing part. `2`-monophilicity says the uniform assignment minimizes the count; for an even cycle
that minimum is $`\mathrm{col}(C, 2) = 2`; so *every* `2`-list assignment on an even cycle admits at
least two colourings, in particular at least one.

```lean
open Monophilic in
example {k : ℕ} (hk : Odd k) (hk2 : 2 ≤ k) : (closePath k).Choosable 2 :=
  choosable_two_closePath_of_odd hk hk2
```

The odd cycles are excluded for the bluntest possible reason — they are not even `2`-colourable:

```lean
open Monophilic in
example {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) : ¬ (closePath k).Choosable 2 :=
  not_choosable_two_closePath_of_even hk hk2
```

*The theta graphs* need a genuine argument. Colour the two branch vertices first; a pair of colours
for them either agrees or differs, and one checks that each arm can be completed in at least one of
the cases. The two length-two arms handle the pairs the long arm cannot.

```lean
open Monophilic in
example (m : ℕ) (hm : 1 ≤ m) : (theta m).Choosable 2 :=
  choosable_theta m hm
```

# The hard direction

The other half — that a `2`-choosable graph's core *must* be on the list — splits into two
independent statements, and it is worth separating them because their status here differs.

*The classification of theta graphs.* A general theta graph $`\theta_{a,b,c}` is two branch vertices
joined by three internally disjoint paths of lengths `a`, `b`, `c`. Rubin's list contains only the
shape $`(2, 2, \text{even})`; every other valid shape must be shown non-`2`-choosable. That is
proved here, in full generality, with an explicit `2`-list assignment admitting no colouring:

```lean
open Monophilic in
example {a b c : ℕ} (hv : ValidShape a b c) (hbad : ¬ GoodShape a b c) :
    ¬ (thetaGen a b c).Choosable 2 :=
  not_choosable_two_thetaGen hv hbad
```

```lean
open Monophilic in
example : ThetaClassification := thetaClassification
```

The witness gives both branch vertices the list `{1, 2}`, so a colouring is a pair of branch colours
plus a completion along each arm; an arm *blocks* a pair when no completion exists. An arm whose
interior lists are all `{1,2}` forces the two ends to alternate, so it blocks two pairs according to
its parity; an arm carrying a suitably staggered pattern of lists propagates a forced chain and
blocks a single pair. Either $`b = 2` — and then the shape contains an odd cycle and the uniform
lists already fail — or $`3 \le b \le c` and the three arms between them block all four pairs. Small
shapes are also checked outright:

```lean
open Monophilic in
example : ¬ (thetaGen 3 3 3).Choosable 2 := not_choosable_two_thetaGen_333
```

```lean
open Monophilic in
example : ¬ (thetaGen 2 4 4).Choosable 2 := not_choosable_two_thetaGen_244
```

*The structural statement.* What remains is not about colouring at all. It is the claim that a graph
of the kind under consideration falls into one of four structural cases: it is a cycle, or it is
$`\theta_{2,2,2m}`, or it contains an odd cycle, or it contains a theta of some shape other than
Rubin's.

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    ThetaAlternative H ↔
      ((∃ k, 2 ≤ k ∧ Nonempty (H ≃g closePath k)) ∨
       (∃ m, 1 ≤ m ∧ Nonempty (H ≃g theta m)) ∨
       (∃ k, Even k ∧ 2 ≤ k ∧ Contains H (closePath k)) ∨
       (∃ a b c, ValidShape a b c ∧ ¬ GoodShape a b c ∧
          Contains H (thetaGen a b c))) :=
  Iff.rfl
```

Granted that for a particular graph, Rubin's theorem follows outright — the theta classification is
no longer a hypothesis:

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (halt : ThetaAlternative H) :
    H.Choosable 2 ↔ RubinFamily H :=
  choosable_two_iff_rubinFamily' H halt
```

and over a core:

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (halt : ThetaAlternative H)
    (k : ℕ) (d : TowerData V k) :
    (pendantTower H k d).Choosable 2 ↔ RubinFamily H :=
  choosable_two_pendantTower_iff' H halt k d
```

The hypothesis holds, provably, for the two families it is applied to:

```lean
open Monophilic in
example {k : ℕ} (hk : 2 ≤ k) : ThetaAlternative (closePath k) :=
  thetaAlternative_closePath hk
```

```lean
open Monophilic in
example {m : ℕ} (hm : 1 ≤ m) : ThetaAlternative (theta m) :=
  thetaAlternative_theta hm
```

What is missing is the general establishment of `ThetaAlternative` — the "follow a path until it
returns to the cycle" argument, which in the literature is a block or ear decomposition. Mathlib has
neither, and building one is a substantial piece of graph theory unrelated to colouring. So that,
and only that, is the loan.

# Why the obvious reduction fails: $`K_{2,4}`

It is worth seeing why `ThetaAlternative` is stated for *a particular graph* rather than proved once
and for all. The tempting universal statement is:

> a connected graph of minimum degree at least two is a cycle, or $`\theta_{2,2,2m}`, or it
> contains an odd cycle, or it contains a theta of some other shape.

That statement is *false*, and the counterexample is a graph this book has already met:
$`K_{2,4}`, the Erdős–Rubin–Taylor example of {ref "lists"}[the lists chapter], which lives here as
`ERT.K 2`.

Check it against the four alternatives. It is connected. It is bipartite, so it contains no odd
cycle. Its two left vertices have degree four and its four right vertices degree two, so it is not a
cycle; and it is not any $`\theta_{2,2,2m}`, which has exactly two vertices of degree three. And
every theta subgraph of it is a $`\theta_{2,2,2}`: three internally disjoint paths between two of
its vertices can only be three of the four length-two paths joining the two degree-four vertices. So
all four alternatives fail.

Yet $`K_{2,4}` is not `2`-choosable:

```lean
open SimpleGraph in
example : ¬ (SimpleGraph.ERT.K 2).Choosable 2 :=
  SimpleGraph.ERT.not_choosable 2
```

The moral is that a universal structural dichotomy strong enough to finish Rubin's theorem must
offer strictly more configurations than "odd cycle or bad theta": at least *generalized* thetas —
two vertices joined by four or more internally disjoint paths — and pairs of cycles meeting in at
most one vertex, each of which then needs its own non-choosability witness. The single-graph
hypothesis `ThetaAlternative` is exactly the fragment of that dichotomy that the rest of the
argument consumes, which is why it is the thing left open rather than something larger.

# What this buys

With Rubin's theorem in hand, and no more of it borrowed than the structural statement above,
{ref "twomonophilic"}[the next chapter] can ask which of the `2`-choosable graphs are actually
`2`-monophilic. There are not many candidates left: a single vertex, the even cycles, and the theta
graphs. Two of those three families are settled by theorems already proved.
