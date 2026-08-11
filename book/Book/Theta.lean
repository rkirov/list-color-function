import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Theta Graphs and Theorem 2" =>

%%%
tag := "theta"
%%%

Source:
[Theta.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Theta.lean).

Theorem 2 characterizes the graphs that are enumeratively chromatic-choosable at `2`. Its easy
direction assembles results already in hand — trees, cycles, `K₂,₃`, and the observation that a
graph with an odd cycle is not `2`-colorable and so is enumeratively chromatic-choosable at `2`
vacuously. Its converse runs through Rubin's theorem, which is proved in this development
({ref "twochoosable"}[the `2`-choosability chapter] tells that story). This chapter is about the
theta graphs themselves — the one family on Rubin's list that is *not* enumeratively
chromatic-choosable — and about how the dependency on Rubin was arranged so that the two halves
could be worked on independently before it landed.

# Where Rubin's theorem enters

Rubin's theorem {citep erdosRubinTaylor}[] says a connected graph is `2`-choosable exactly when its
core is a single vertex, an even cycle, or `θ_{2,2,2m}` — two vertices joined by three internally
disjoint paths of lengths `2`, `2`, and `2m`. A graph that is enumeratively chromatic-choosable
at `2` and `2`-colorable is
`2`-choosable, so Rubin's list is the list of candidates, and the only work left is to rule out the
theta graphs beyond the smallest. (The smallest, `θ_{2,2,2}`, *is* `K₂,₃`, which the previous
chapter showed is enumeratively chromatic-choosable at `2` — so it stays on the list.)

The graph $`\theta_{2,2,2m}` is two branch vertices joined by three internally disjoint paths, of
lengths $`2`, $`2` and $`2m`:

```diagram (cssWidth := "80%")
open Illuminate Diagram in
let v (x y : Float) : Diagram SVG := translate x y (circle 8)
let e (x1 y1 x2 y2 : Float) : Diagram SVG := line ⟨x1, y1⟩ ⟨x2, y2⟩
-- branch vertices, and the long path between them along the middle
let branch := [v 0 0, v 300 0]
let longPath := [v 75 0, v 150 0, v 225 0]
let longEdges := [e 0 0 75 0, e 75 0 150 0, e 150 0 225 0, e 225 0 300 0]
-- the two length-2 paths, above and below
let shortVerts := [v 150 80, v 150 (-80)]
let shortEdges := [e 0 0 150 80, e 150 80 300 0, e 0 0 150 (-80), e 150 (-80) 300 0]
let labels := [translate 0 (-26) (text "u"), translate 300 (-26) (text "w"),
               translate 150 104 (text "a"), translate 150 (-104) (text "b"),
               translate 150 22 (text "length 2m")]
(longEdges ++ shortEdges ++ branch ++ longPath ++ shortVerts ++ labels).foldl atop emptyDiagram
```

There is a pleasant economy in the construction. Attaching a new vertex adjacent to *both* branch
vertices — the vertices `a` and `b` above — is precisely a path of length 2 between them, which is
to say a cone over a two-element set. So a theta graph is the long path with two cones stacked on
it, and no new graph construction is needed at all:

```lean
open SimpleGraph ListColoring in
example (m : ℕ) : theta m = thetaOf (2 * m) := rfl
```

Note the two branch vertices are *not* adjacent, so `{pathStart, pathEnd}` is not a clique and the
clique-based identity from the Lemma 1 chapter does not apply. But the extension count it was
derived from carries no clique hypothesis, and that is what gets used — one more instance of the
pattern that the general lemma is the useful one.

# The witness

```lean
open SimpleGraph ListColoring in
example (m : ℕ) (hm : 1 ≤ m) : (theta m).colConst 2 = 2 :=
  colConst_theta m hm
```

```lean
open SimpleGraph ListColoring in
example (m : ℕ) (hm : 2 ≤ m) : (theta m).col (thetaWitness m) = 1 :=
  col_theta_witness m hm
```

and therefore

```lean
open SimpleGraph ListColoring in
example (m : ℕ) (hm : 2 ≤ m) : ¬ (theta m).ECCAt 2 :=
  not_ecc_theta m hm
```

The hypothesis `m ≥ 2` is essential rather than an artifact, and the boundary is a good consistency
check on the whole chain: `θ_{2,2,2}` *is* `K₂,₃`, and there the same witness gives `col = 2`, equal
to `colConst` — exactly as it must, since the previous chapter proved `K₂,₃` is enumeratively
chromatic-choosable at `2`.

The paper gives a figure for `m = 2`. A figure cannot be formalized: what is needed is a family
uniform in `m`. Searching for one found 48 assignments achieving `col = 1` at `m = 2`, and from them
a family that works for every `m` — the branch vertices get `{1,2}` and `{1,3}`, the two short
interior vertices `{1,2}` and `{2,3}`, and the long path's interior gets `{1,2}` repeated, ending
`{2,3}, {1,3}`. Along the long path the `{1,2}` lists force an alternating colouring, so the colour
arriving at the far end is determined, and the last two lists then pin the branch vertex — which is
what collapses the count to one.

# Isolating Rubin's theorem

Theorem 2 is then stated so that Rubin's theorem is a hypothesis and nothing else is, and the way
it is stated matters more than the fact that it is:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {CoreIsVertex CoreIsEvenCycle : Prop} {CoreIsTheta : ℕ → Prop}
    (rubin : G.Choosable 2 ↔
      CoreIsVertex ∨ CoreIsEvenCycle ∨ ∃ m, 1 ≤ m ∧ CoreIsTheta m)
    (hvertex : CoreIsVertex → G.ECCAt 2)
    (hcycle : CoreIsEvenCycle → G.ECCAt 2)
    (hK23 : CoreIsTheta 1 → G.ECCAt 2)
    (htheta : ∀ m, 2 ≤ m → CoreIsTheta m → ¬ G.ECCAt 2) :
    G.ECCAt 2 ↔ ¬ G.Colorable 2 ∨ CoreIsVertex ∨ CoreIsEvenCycle ∨ CoreIsTheta 1 :=
  ecc_two_iff_of_rubin rubin hvertex hcycle hK23 htheta
```

Since only the forward implication is ever used, the hypothesis is a one-way implication rather
than an equivalence — and the backward half is no longer assumed at all, because it is proved:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : RubinFamily G) : G.Choosable 2 :=
  choosable_two_of_rubinFamily G h
```

That is Rubin's easy direction: every graph on his list — a single vertex, an even cycle, or
$`\theta_{2,2,2m}` — really is `2`-choosable. The even-cycle case is a corollary of Theorem 1 rather
than a separate argument: enumerative chromatic-choosability at `2` says the constant assignment
minimizes, and for an even cycle that minimum is `col(C,2) = 2 > 0`.

The other direction — that a `2`-choosable graph *must* have one of those cores — is the long one,
and it is proved. Its colouring content is that a theta graph is `2`-choosable exactly when its
shape is $`(2,2,\text{even})`, at every arity; its structural content is Rubin's own case analysis
on a shortest cycle and two shortest connecting paths. No block or ear decomposition is needed
anywhere, which is what makes the whole thing formalizable against a Mathlib that has neither.
{ref "twochoosable"}[The `2`-choosability chapter] tells it in full, together with the two
six-vertex counterexamples, $`K_{2,4}` and $`K_{3,3}-e`, that killed the structural detour this
development first tried.

The three alternatives above are *abstract propositions*, not definitions. That was deliberate, and
it is the most conservative form the statement can take: if `CoreIsEvenCycle` were defined here, the
theorem would quietly depend on whatever that definition happened to say about cores, and a reader
could not tell by inspection how much had been assumed. Left abstract, the theorem says exactly what
it should: *given* Rubin's classification, and *given* the four enumerative chromatic-choosability
facts about the classes it names — each of which is proved in this development — the Kirov–Naimi
characterization follows.

The version in `ListColoring.Theorem2`, displayed in {ref "twoecc"}[the enumerative
chromatic-choosability at `2` chapter], goes the other way and pays off the definitions: there the
four alternatives are spelled out on a concrete notion of core, and the hypothesis is a single named
proposition {name ListColoring.RubinTheorem}`RubinTheorem` taken as the first explicit argument.
Both forms are proved, and the term {name ListColoring.rubinTheorem}`rubinTheorem` now discharges
the hypothesis of the second — which is what makes
{name ListColoring.ecc_two_iff}`ecc_two_iff` unconditional. The abstract form is kept because it is
the only place a reader can see, from a signature alone, that nothing beyond Rubin's statement was
ever used.

What was assumed is legible in the signature. Nothing else was.
