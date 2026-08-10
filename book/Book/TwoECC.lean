import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Which Graphs Are Enumeratively Chromatic-Choosable at 2?" =>

%%%
tag := "twoecc"
%%%

Source: [Core.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Core.lean),
[K23.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/K23.lean),
[Theta.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Theta.lean),
[Rubin.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Rubin.lean),
[Theorem2.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Theorem2.lean).

This chapter states the second main theorem of Kirov and Naimi {citep kirovNaimi}[]: a complete
description of the graphs that are enumeratively chromatic-choosable at `2`. It also says exactly
what the description still rests on, because the answer is *almost* unconditional and the remaining
gap is worth being precise about.

# Narrowing the field

Recall the three regimes of {ref "lists"}[the lists chapter], specialized to `n = 2`.

If `G` is not `2`-colourable — equivalently, if it has an odd cycle — then it is enumeratively
chromatic-choosable at `2` vacuously, since there are no colourings from the uniform palette to
compare against. That is a large and uninteresting class, and it has to appear in the answer.

If `G` is `2`-colourable but not `2`-choosable, enumerative chromatic-choosability fails.

So the only graphs that can be enumeratively chromatic-choosable at `2` *for a reason* are the
`2`-choosable ones, and {ref "twochoosable"}[the previous chapter] listed those: a graph is
`2`-choosable exactly when its core is a single vertex, an even cycle, or $`\theta_{2,2,2m}`.

The classification is therefore a matter of going through that short list.

# Cores again

Just as pendant vertices are invisible to choosability, they are invisible to enumerative
chromatic-choosability — this is Lemma 5 of the paper, and unlike its choosability counterpart it
needs no hypothesis on `n` at all:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n k : ℕ)
    (d : TowerData V k) :
    (pendantTower G k d).ECCAt n ↔ G.ECCAt n :=
  ecc_pendantTower_iff n k d
```

One direction is free: attaching a pendant vertex is coning over a singleton, and a singleton is a
clique, so it is the Lemma 1 of {ref "chordal"}[the chordal chapter]. The other direction needs a
matching identity for arbitrary lists, obtained by giving the new vertex *the same list as its
neighbour* — then exactly one of its colours is always blocked, and the count is multiplied by
`n - 1` exactly rather than merely bounded.

Read backwards, the same statement transports enumerative chromatic-choosability between a graph and
its core:

```lean
open SimpleGraph ListColoring in
example {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (h : CoreIs G H) (n : ℕ) :
    G.ECCAt n ↔ H.ECCAt n :=
  ecc_iff_of_coreIs h n
```

So it is enough to classify the possible cores.

# Going down the list

*A single vertex.* Enumeratively chromatic-choosable, for every `n`: with one vertex and no edges
every list of size `n` gives `n` colourings.

```lean
open SimpleGraph in
example (n : ℕ) : (⊤ : SimpleGraph (Fin 1)).ECCAt n :=
  ecc_top (Fin 1) n
```

*An even cycle.* Enumeratively chromatic-choosable, by Theorem 1.

```lean
open ListColoring in
example {k : ℕ} (hk : Odd k) : (closePath k).ECCAt 2 :=
  ecc_closePath_two hk
```

*The theta graphs.* Here the list splits, and this is the whole content of Theorem 2. The smallest
theta, $`\theta_{2,2,2}`, *is* $`K_{2,3}` — two branch vertices joined by three paths of length two
is two vertices each joined to the same three others — and it is enumeratively chromatic-choosable
at `2`. Every larger one is not.

```diagram (cssWidth := "94%")
open Illuminate Diagram in
let v (x y : Float) : Diagram _ := translate x y (circle 8)
let e (x1 y1 x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
let small :=
  [e (-360) 0 (-260) 80, e (-260) 80 (-160) 0, e (-360) 0 (-260) 0, e (-260) 0 (-160) 0,
   e (-360) 0 (-260) (-80), e (-260) (-80) (-160) 0,
   v (-360) 0, v (-160) 0, v (-260) 80, v (-260) 0, v (-260) (-80),
   translate (-260) (-124) (text "theta(2,2,2) = K(2,3)"),
   translate (-260) (-152) (text "ECC at 2")]
let big :=
  [e 20 0 100 0, e 100 0 180 0, e 180 0 260 0, e 260 0 340 0,
   e 20 0 180 90, e 180 90 340 0, e 20 0 180 (-90), e 180 (-90) 340 0,
   v 20 0, v 100 0, v 180 0, v 260 0, v 340 0, v 180 90, v 180 (-90),
   translate 180 (-124) (text "theta(2,2,4)"),
   translate 180 (-152) (text "not ECC at 2")]
(small ++ big).foldl atop emptyDiagram
```

The positive case is a finite but genuinely fiddly computation, carried out in full:

```lean
open SimpleGraph in
example :
    (completeBipartiteGraph (Fin 2) (Fin 3)).ECCAt 2 :=
  ecc_K23
```

The identification of $`K_{2,3}` with the smallest theta is an explicit bijection, checked by
`decide`, and it is what lets the same fact be quoted on either model:

```lean
open SimpleGraph ListColoring in
example :
    completeBipartiteGraph (Fin 2) (Fin 3) ≃g theta 1 :=
  k23IsoThetaOne
```

The negative case is a family of explicit witnesses. For every `m ≥ 1` the uniform count is `2`,

```lean
open ListColoring in
example (m : ℕ) (hm : 1 ≤ m) : (theta m).colConst 2 = 2 :=
  colConst_theta m hm
```

and for `m ≥ 2` there is a `2`-list assignment achieving `1`:

```lean
open ListColoring in
example (m : ℕ) (hm : 2 ≤ m) :
    (theta m).col (thetaWitness m) = 1 :=
  col_theta_witness m hm
```

```lean
open ListColoring in
example (m : ℕ) (hm : 2 ≤ m) : ¬ (theta m).ECCAt 2 :=
  not_ecc_theta m hm
```

The hypothesis `m ≥ 2` is exactly right rather than an artefact of the proof, and the boundary is a
good consistency check on the whole chain: at `m = 1` the same witness gives `col = 2`, equal to the
uniform count — as it must, since $`\theta_{2,2,2}` is $`K_{2,3}`, which the previous display shows
is enumeratively chromatic-choosable at `2`.

Along the way this settles the question that motivated the notion. Enumerative
chromatic-choosability is *strictly* stronger than choosability:

```lean
open ListColoring in
example (m : ℕ) (hm : 2 ≤ m) :
    (theta m).Choosable 2 ∧ ¬ (theta m).ECCAt 2 :=
  choosable_and_not_ecc_theta m hm
```

# Theorem 2

*A connected graph is enumeratively chromatic-choosable at `2` if and only if its core is a single
vertex, is a cycle, is $`K_{2,3}`, or it contains an odd cycle.*

The Lean statement takes Rubin's theorem as its first explicit argument, and the way it does so is
the point of this section:

```lean
open SimpleGraph ListColoring in
example (rubin : RubinTheorem) {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    G.ECCAt 2 ↔
      CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨
        HasOddCycle G :=
  ecc_two_iff_of_rubin rubin G hconn
```

Three things are worth reading off that signature.

*The four alternatives are real definitions, not abstract propositions.* Each spells out on top of
the {name ListColoring.CoreIs}`CoreIs` predicate of {ref "twochoosable"}[the previous chapter] a
phrase the paper states in words, so there is nothing to take on trust about what "core" means here:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    CoreIsCycle G ↔
      ∃ k, 2 ≤ k ∧ CoreIs G (closePath k) := Iff.rfl
```

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    CoreIsK23 G ↔ CoreIs G (theta 1) := Iff.rfl
```

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasOddCycle G ↔
      ∃ k, Even k ∧ 2 ≤ k ∧ Contains G (closePath k) :=
  Iff.rfl
```

Note that Theorem 2 asks for less than Rubin's theorem does: "is a cycle", with no parity
restriction, where Rubin's list says "is an even cycle". That is because *every* cycle is
enumeratively chromatic-choosable at `2`, by Theorem 1, whereas only the even ones are
`2`-choosable.

*The hypothesis is a single named proposition.* {name ListColoring.RubinTheorem}`RubinTheorem` is
Rubin's theorem, stated in the development and being proved there; it is not an axiom and it is not
a re-statement tailored to what Theorem 2 happens to need.

*It is the first explicit argument.* The day a term `rubinTheorem : RubinTheorem` exists,
`ecc_two_iff_of_rubin rubinTheorem` is the unconditional theorem, with no other edit
anywhere in the development and no change to this chapter beyond deleting the hypothesis.

# How much of this is unconditional?

More than the shape of the statement suggests, and the difference matters.

*The entire ⟸ direction*, with no hypothesis at all — not Rubin's theorem, and not even
connectivity:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨
      HasOddCycle G) :
    G.ECCAt 2 :=
  ecc_two_of_alternatives h
```

*The ⟹ direction for a graph that is not `2`-colourable*, which is the case the paper disposes of
in its opening sentence: such a graph contains an odd cycle. This is the classical characterization
of bipartite graphs, and it is the one ingredient of the paper's proof that had to be built from
scratch, because Mathlib records it as an open `TODO` in its `Bipartite.lean`:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : ¬ G.Colorable 2) : HasOddCycle G :=
  hasOddCycle_of_not_colorable_two h
```

Its substance is the middle step, folklore rather than anybody's theorem: an odd closed *walk*
contains an odd *cycle*. Rotate the walk to a repeated vertex and cut it there; the two shorter
closed walks have lengths summing to the original, so exactly one of them is odd, and the induction
is on length.

```lean
open SimpleGraph ListColoring in
example {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {x : V} (w : G.Walk x x) (hodd : Odd w.length) :
    ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ Odd c.length :=
  exists_odd_isCycle_of_odd_closed_walk w.length w rfl hodd
```

That is a by-product rather than a contribution: a piece of textbook graph theory that Mathlib had
flagged as missing and that this development needed anyway.

*The ⟹ direction for a `2`-colourable graph, granted Rubin's conclusion.* Rubin's theorem is not
assumed here; its three-way conclusion is taken as a hypothesis and converted into the four-way one:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmono : G.ECCAt 2)
    (h : CoreIsVertex G ∨ CoreIsEvenCycle G ∨
      CoreIsTheta G) :
    CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨
      HasOddCycle G :=
  alternatives_of_rubinAlternatives hmono h
```

The two moving parts there are the collapse of "even cycle" into "cycle", and the elimination of
$`\theta_{2,2,2m}` for `m ≥ 2` — which is the witness family displayed above — leaving `m = 1`,
which is $`K_{2,3}`.

*The ⟸ direction of Rubin's theorem itself*, so that what is missing from `RubinTheorem` is only
its forward implication:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : CoreIsVertex G ∨ CoreIsEvenCycle G ∨
      CoreIsTheta G) : G.Choosable 2 :=
  choosable_two_of_rubinAlternatives h
```

So the honest summary is: *every colouring-theoretic ingredient of Theorem 2 is proved outright, and
what remains is the forward implication of Rubin's theorem, which reduces to a structural statement
about subgraphs with no colouring in it.* Connectivity is load-bearing in exactly one place — it is
the hypothesis of Rubin's theorem — and is used nowhere else.

The graphs that the missing structural step would have to exclude are, individually, excluded
already:

```lean
open ListColoring in
example : ¬ (thetaGen 3 3 3).ECCAt 2 :=
  not_ecc_two_thetaGen_333
```

```lean
open ListColoring in
example : ¬ (thetaGen 1 3 3).ECCAt 2 :=
  not_ecc_two_thetaGen_133
```

What that step must *not* be is the subject of the $`K_{2,4}` section of
{ref "twochoosable"}[the previous chapter]: a three-arm dichotomy is provably too weak, and the
generalized theta of arbitrary arity is the right object.

# What is left

The classification at `n = 2` is essentially complete; cycles are settled for every `n`; chordal
graphs are settled for every `n`. What is not settled is anything like a classification for `n ≥ 3`,
and it is not known what one would look like. What *is* known, and is the subject of
{ref "threshold"}[the last chapter], is that the question always has a positive answer eventually:
every graph is enumeratively chromatic-choosable at `n` once `n` is large enough.
