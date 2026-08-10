import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

#doc (Manual) "Which Graphs Are 2-Choosable?" =>

%%%
tag := "twochoosable"
%%%

Source:
[Choosable.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Choosable.lean),
[ThetaChoosable.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/ThetaChoosable.lean),
[Rubin.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Rubin.lean),
[RubinHard.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/RubinHard.lean),
[ThetaClass.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/ThetaClass.lean),
[Theorem2.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Theorem2.lean).

The classification of the graphs that are enumeratively chromatic-choosable at `2`, which is the
second main theorem of the paper, rests on an older classification: which graphs are `2`-choosable?
That question was answered by A. L. Rubin, in the paper of Erdős, Rubin and Taylor
{citep erdosRubinTaylor}[] where list colouring is introduced, and the result is universally
credited to Rubin. Kirov and Naimi cite it; this development is *proving* it. This chapter states
it, and says exactly how much of it is proved and what is outstanding.

The short version: the ⟸ direction is proved, the theta graphs are classified in full, and what
remains is one purely structural statement about subgraphs, with no colouring in it.

# Pendant vertices do not matter

Start with the reduction that makes a classification possible at all. A vertex of degree one can
always be coloured last: whatever colour its single neighbour took, its own list of two colours
still contains something else. So attaching a pendant vertex changes nothing about `2`-choosability
— nor about `n`-choosability for any `n ≥ 2`:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}
    (hn : 2 ≤ n) (k : ℕ) (d : TowerData V k) :
    (pendantTower G k d).Choosable n ↔ G.Choosable n :=
  choosable_pendantTower_iff hn k d
```

Repeatedly deleting vertices of degree one until none is left produces the *core* of the graph. The
statement above is that reduction run backwards, which is the form a formalization can use directly:
rather than define a fixpoint of a deletion operation, present the graph as its core with a tower of
pendant attachments on top. That reading is what {name ListColoring.CoreIs}`CoreIs` says, and it is
spelled out exactly so:

```lean
open SimpleGraph ListColoring in
example {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    CoreIs G H ↔
      ∃ (k : ℕ) (d : TowerData W k),
        Nonempty (G ≃g pendantTower H k d) :=
  Iff.rfl
```

This is mechanization and not mathematics — the papers simply say "core" — and the two readings are
interchangeable because of the display above it. Choosability transports along it:

```lean
open SimpleGraph ListColoring in
example {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (h : CoreIs G H) : G.Choosable 2 ↔ H.Choosable 2 :=
  choosable_iff_of_coreIs h le_rfl
```

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

That sentence is a named proposition in the development, so that statements which consume it can be
written against it before it is available. Unfolded, it reads:

```lean
open SimpleGraph ListColoring in
example : RubinTheorem =
    ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → (G.Choosable 2 ↔
        CoreIsVertex G ∨ CoreIsEvenCycle G ∨
          CoreIsTheta G) :=
  rfl
```

The three alternatives are the three families, each said of the *core* by way of the definition
above. Recall that `closePath k` has `k + 1` vertices, so `Odd k` picks out the cycles on an *even*
number of vertices:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    CoreIsEvenCycle G ↔
      ∃ k, Odd k ∧ 2 ≤ k ∧ CoreIs G (closePath k) := Iff.rfl
```

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    CoreIsTheta G ↔ ∃ m, 1 ≤ m ∧ CoreIs G (theta m) :=
  Iff.rfl
```

The same three families collected up to isomorphism, without the core, are
{name ListColoring.RubinFamily}`RubinFamily`:

```lean
open SimpleGraph ListColoring in
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
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : RubinFamily G) : G.Choosable 2 :=
  choosable_two_of_rubinFamily G h
```

and therefore, transported along the core, in the form in which Rubin's theorem states it:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : CoreIsVertex G ∨ CoreIsEvenCycle G ∨
      CoreIsTheta G) : G.Choosable 2 :=
  choosable_two_of_rubinAlternatives h
```

That display is worth pausing on: it is one half of {name ListColoring.RubinTheorem}`RubinTheorem`,
discharged. What is missing from the named proposition is only its *forward* implication.

The three cases are of quite different weights.

*A single vertex* is `n`-choosable for any `n ≥ 1`, there being no edge to violate.

*An even cycle* is a corollary of Theorem 1 rather than a separate argument, and this is the
pleasing part. Enumerative chromatic-choosability at `2` says the uniform assignment minimizes the
count; for an even cycle that minimum is $`\mathrm{col}(C, 2) = 2`; so *every* `2`-list assignment
on an even cycle admits at least two colourings, in particular at least one.

```lean
open ListColoring in
example {k : ℕ} (hk : Odd k) (hk2 : 2 ≤ k) :
    (closePath k).Choosable 2 :=
  choosable_two_closePath_of_odd hk hk2
```

The odd cycles are excluded for the bluntest possible reason — they are not even `2`-colourable:

```lean
open ListColoring in
example {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    ¬ (closePath k).Choosable 2 :=
  not_choosable_two_closePath_of_even hk hk2
```

*The theta graphs* need a genuine argument. Colour the two branch vertices first; a pair of colours
for them either agrees or differs, and one checks that each arm can be completed in at least one of
the cases. The two length-two arms handle the pairs the long arm cannot.

```lean
open ListColoring in
example (m : ℕ) (hm : 1 ≤ m) : (theta m).Choosable 2 :=
  choosable_theta m hm
```

# The forward direction

The other half — that a `2`-choosable graph's core *must* be on the list — splits into a colouring
part and a structural part. The colouring part is done.

## The theta graphs are classified

A general theta graph $`\theta_{a,b,c}` is two branch vertices joined by three internally disjoint
paths of lengths `a`, `b`, `c`. Normalize the shape so that $`1 \le a \le b \le c` with $`b \ge 2` —
sorting costs nothing, and $`b \ge 2` says at most one arm is a bare edge, since two would collapse:

```lean
open ListColoring in
example {a b c : ℕ} :
    ValidShape a b c ↔
      1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ 2 ≤ b := Iff.rfl
```

```lean
open ListColoring in
example {a b c : ℕ} :
    GoodShape a b c ↔ a = 2 ∧ b = 2 ∧ Even c := Iff.rfl
```

Rubin's list contains exactly the good shapes, and for theta graphs that is now a theorem in both
directions:

```lean
open ListColoring in
example {a b c : ℕ} (hv : ValidShape a b c) :
    (thetaGen a b c).Choosable 2 ↔ GoodShape a b c :=
  choosable_two_thetaGen_iff hv
```

The ⟸ half of that is Rubin's family again, on the general model:

```lean
open ListColoring in
example (m : ℕ) (hm : 1 ≤ m) :
    (thetaGen 2 2 (2 * m)).Choosable 2 :=
  choosable_two_thetaGen_two_two m hm
```

The ⟹ half is an explicit `2`-list assignment admitting no colouring, uniform in the shape:

```lean
open ListColoring in
example {a b c : ℕ} (hv : ValidShape a b c)
    (hbad : ¬ GoodShape a b c) :
    ¬ (thetaGen a b c).Choosable 2 :=
  not_choosable_two_thetaGen hv hbad
```

```lean
open ListColoring in
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
open ListColoring in
example : ¬ (thetaGen 3 3 3).Choosable 2 :=
  not_choosable_two_thetaGen_333
```

```lean
open ListColoring in
example : ¬ (thetaGen 2 4 4).Choosable 2 :=
  not_choosable_two_thetaGen_244
```

## What is outstanding

What remains is not about colouring at all. It is the structural step: a connected graph of minimum
degree at least two which is not a cycle and not a $`\theta_{2,2,2m}` must contain one of the
configurations already known not to be `2`-choosable. In the literature that step is a block or ear
decomposition. Mathlib has neither, and building one is a substantial piece of graph theory
unrelated to colouring.

The next section is about what the list of configurations has to contain, because getting that wrong
is easy and this development got it wrong once.

# The smallest counterexample: $`K_{2,4}`

An earlier version of this development carried an auxiliary hypothesis, invented here and not found
in any paper, meant to be the structural half of the argument. Applied to a graph `H`, it offered
four alternatives:

> `H` is a cycle, or a $`\theta_{2,2,2m}`, or it contains an odd cycle, or it contains a theta
> $`\theta_{a,b,c}` of some shape other than $`(2,2,\text{even})`.

Every disjunct is a configuration whose colouring behaviour is settled above, so the hypothesis
looked like exactly the right currency. *It is false*, and it has been deleted along with
everything that took it as a hypothesis. The counterexample is a graph this book has already met:
$`K_{2,4}`, the Erdős–Rubin–Taylor example of {ref "lists"}[the lists chapter], which lives here as
`ERT.K 2` — the complete bipartite graph whose right side is indexed by the four functions
$`\mathbf{2} \to \mathbf{2}`.

```lean
open SimpleGraph in
example : ERT.K 2 =
    completeBipartiteGraph (Fin 2) (Fin 2 → Fin 2) := rfl
```

```lean
open SimpleGraph in
example : Fintype.card (Fin 2 → Fin 2) = 2 ^ 2 :=
  ERT.card_right 2
```

```diagram (cssWidth := "80%")
open Illuminate Diagram in
let v (x y : Float) : Diagram _ := translate x y (circle 8)
let e (x1 y1 x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
let left := [v (-160) 0, v 160 0]
let mid := [v 0 120, v 0 40, v 0 (-40), v 0 (-120)]
let edges :=
  [e (-160) 0 0 120, e (-160) 0 0 40, e (-160) 0 0 (-40), e (-160) 0 0 (-120),
   e 160 0 0 120, e 160 0 0 40, e 160 0 0 (-40), e 160 0 0 (-120)]
let labels :=
  [translate (-160) (-30) (text "degree 4"), translate 160 (-30) (text "degree 4"),
   translate 0 (-166) (text "K(2,4): four arms of length two")]
(edges ++ left ++ mid ++ labels).foldl atop emptyDiagram
```

Check $`K_{2,4}` against the four alternatives. It is connected, and its minimum degree is two.

*Not a cycle, and not any* $`\theta_{2,2,2m}`. Its degree sequence is `4, 4, 2, 2, 2, 2`, whereas a
cycle is `2`-regular and a $`\theta_{2,2,2m}` has maximum degree three.

```lean
open SimpleGraph in
example : (ERT.K 2).degree (Sum.inl 0) = 4 := by decide
```

```lean
open SimpleGraph in
example : ∀ φ : Fin 2 → Fin 2,
    (ERT.K 2).degree (Sum.inr φ) = 2 := by decide
```

*No odd cycle.* It is bipartite, hence `2`-colourable, and a graph with an odd cycle is not:

```lean
open SimpleGraph ListColoring in
example : ¬ HasOddCycle (ERT.K 2) := fun h =>
  not_colorable_two_of_hasOddCycle h
    (ERT.colorable 2 le_rfl)
```

*No bad theta.* A theta subgraph has two branch vertices of degree at least three *in the subgraph*,
so of degree at least three in $`K_{2,4}` — which leaves only the two vertices of degree four. Those
two are not adjacent, and the only paths between them that are internally disjoint are the four
length-two paths through the right-hand vertices. So every theta subgraph of $`K_{2,4}` consists of
three of those four paths: it is a $`\theta_{2,2,2}`, and that is the *good* shape.

```lean
open SimpleGraph ListColoring in
example : Contains (ERT.K 2) (thetaGen 2 2 2) :=
  ⟨![Sum.inr ![0, 0], Sum.inr ![0, 1], Sum.inr ![1, 1],
     Sum.inl 0, Sum.inl 1], by decide, by decide⟩
```

```lean
open ListColoring in
example : (thetaGen 2 2 2).Choosable 2 :=
  choosable_two_thetaGen_two_two 1 le_rfl
```

So all four alternatives fail. And yet:

```lean
open SimpleGraph in
example : ¬ (ERT.K 2).Choosable 2 := ERT.not_choosable 2
```

```lean
open SimpleGraph in
example : (ERT.K 2).Colorable 2 := ERT.colorable 2 le_rfl
```

Six vertices and eight edges is enough to refute the hypothesis outright.

## What the counterexample teaches

Look at the picture again. $`K_{2,4}` *is* a theta graph — it is two vertices joined by internally
disjoint paths, all of length two. What it is not is a theta graph with *three* arms. The discarded
hypothesis offered only three-arm thetas, and that is precisely where it was too weak.

The right structural object is the *generalized theta*: two vertices joined by arbitrarily many
internally disjoint paths. $`K_{2,4}` is the one with four arms of length two, and it is the
smallest graph that a three-arm dichotomy cannot see. A universal structural statement strong enough
to finish Rubin's argument must therefore offer generalized thetas of every arity — each with its
own non-choosability witness — together with pairs of cycles meeting in at most one vertex. Work
generalizing the theta classification above from three arms to arbitrary arity is what $`K_{2,4}`
demands, and it is in progress.

Two things about this episode should be stated plainly, because they are easy to garble.

First, *this was a defect in this repository's scaffolding, not an error in Kirov–Naimi*. The
hypothesis was invented here, as a way of splitting Rubin's theorem into a structural half and a
colouring half so that the halves could be worked on separately. Kirov and Naimi *cite* Rubin's
theorem rather than proving it, and so never assert anything of the kind. No error has been found in
their paper — zero, across the whole formalization.

Second, the episode is an argument for the discipline this book runs on rather than against it. The
hypothesis was plausible, it was consistent with every example anyone had checked by hand, and it
was refuted by brute force on a six-vertex graph the development already owned. That is the ordinary
working of mechanization: a statement that cannot be discharged is a statement worth attacking with
a search.

# What this buys

With Rubin's theorem stated as a named proposition, its ⟸ direction proved and its theta content
proved, {ref "twoecc"}[the next chapter] can ask which of the `2`-choosable graphs are actually
enumeratively chromatic-choosable at `2` — and can state Theorem 2 in a form that becomes
unconditional the moment the forward implication lands. There are not many candidates to sort
through: a single vertex, the even cycles, and the theta graphs. Two of those three families are
settled by theorems already proved.
