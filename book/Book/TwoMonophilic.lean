import VersoManual
import Book.Papers
import Monophilic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Which Graphs Are 2-Monophilic?" =>

%%%
tag := "twomonophilic"
%%%

Source: [Core.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Core.lean), [K23.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/K23.lean), [Theta.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Theta.lean), [Rubin.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Rubin.lean).

This chapter states the second main theorem of Kirov and Naimi {citep kirovNaimi}[]: a complete
description of the `2`-monophilic graphs. It also says exactly what the description is conditional
on, because the answer is *almost* unconditional and the remaining gap is worth being precise about.

# Narrowing the field

Recall the three regimes of {ref "lists"}[the lists chapter], specialized to `n = 2`.

If `G` is not `2`-colourable — equivalently, if it has an odd cycle — then it is `2`-monophilic
vacuously, since there are no colourings from the uniform palette to compare against. That is a
large and uninteresting class, and it has to appear in the answer.

If `G` is `2`-colourable but not `2`-choosable, monophilicity fails.

So the only graphs that can be `2`-monophilic *for a reason* are the `2`-choosable ones, and
{ref "twochoosable"}[the previous chapter] listed those: a graph is `2`-choosable exactly when its
core is a single vertex, an even cycle, or $`\theta_{2,2,2m}`.

The classification is therefore a matter of going through that short list.

# Cores again

Just as pendant vertices are invisible to choosability, they are invisible to monophilicity — this
is Lemma 5 of the paper, and unlike its choosability counterpart it needs no hypothesis on `n` at
all:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n k : ℕ) (d : TowerData V k) :
    (pendantTower G k d).Monophilic n ↔ G.Monophilic n :=
  monophilic_pendantTower_iff n k d
```

One direction is free: attaching a pendant vertex is coning over a singleton, and a singleton is a
clique, so it is the Lemma 1 of {ref "chordal"}[the chordal chapter]. The other direction needs a
matching identity for arbitrary lists, obtained by giving the new vertex *the same list as its
neighbour* — then exactly one of its colours is always blocked, and the count is multiplied by
`n - 1` exactly rather than merely bounded.

So it is enough to classify the possible cores.

# Going down the list

*A single vertex.* Monophilic, for every `n`: with one vertex and no edges every list of size `n`
gives `n` colourings.

```lean
open SimpleGraph in
example (n : ℕ) : (⊤ : SimpleGraph (Fin 1)).Monophilic n :=
  monophilic_top (Fin 1) n
```

*An even cycle.* Monophilic, by Theorem 1.

```lean
open Monophilic in
example {k : ℕ} (hk : Odd k) : (closePath k).Monophilic 2 :=
  monophilic_closePath_two hk
```

*The theta graphs.* Here the list splits, and this is the whole content of Theorem 2. The smallest
theta, $`\theta_{2,2,2}`, *is* $`K_{2,3}` — two branch vertices joined by three paths of length two
is two vertices each joined to the same three others — and it is `2`-monophilic. Every larger one is
not.

```diagram (cssWidth := "94%")
open Illuminate Diagram in
let v (x y : Float) : Diagram _ := translate x y (circle 8)
let e (x1 y1 x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
let small :=
  [e (-360) 0 (-260) 80, e (-260) 80 (-160) 0, e (-360) 0 (-260) 0, e (-260) 0 (-160) 0,
   e (-360) 0 (-260) (-80), e (-260) (-80) (-160) 0,
   v (-360) 0, v (-160) 0, v (-260) 80, v (-260) 0, v (-260) (-80),
   translate (-260) (-124) (text "theta(2,2,2) = K(2,3)"),
   translate (-260) (-152) (text "2-monophilic")]
let big :=
  [e 20 0 100 0, e 100 0 180 0, e 180 0 260 0, e 260 0 340 0,
   e 20 0 180 90, e 180 90 340 0, e 20 0 180 (-90), e 180 (-90) 340 0,
   v 20 0, v 100 0, v 180 0, v 260 0, v 340 0, v 180 90, v 180 (-90),
   translate 180 (-124) (text "theta(2,2,4)"),
   translate 180 (-152) (text "not 2-monophilic")]
(small ++ big).foldl atop emptyDiagram
```

The positive case is a finite but genuinely fiddly computation, carried out in full:

```lean
open SimpleGraph in
example : (completeBipartiteGraph (Fin 2) (Fin 3)).Monophilic 2 :=
  monophilic_K23
```

The negative case is a family of explicit witnesses. For every `m ≥ 1` the uniform count is `2`,

```lean
open Monophilic in
example (m : ℕ) (hm : 1 ≤ m) : (theta m).colConst 2 = 2 :=
  colConst_theta m hm
```

and for `m ≥ 2` there is a `2`-list assignment achieving `1`:

```lean
open Monophilic in
example (m : ℕ) (hm : 2 ≤ m) : (theta m).col (thetaWitness m) = 1 :=
  col_theta_witness m hm
```

```lean
open Monophilic in
example (m : ℕ) (hm : 2 ≤ m) : ¬ (theta m).Monophilic 2 :=
  not_monophilic_theta m hm
```

The hypothesis `m ≥ 2` is exactly right rather than an artefact of the proof, and the boundary is a
good consistency check on the whole chain: at `m = 1` the same witness gives `col = 2`, equal to the
uniform count — as it must, since $`\theta_{2,2,2}` is $`K_{2,3}`, which the previous display shows
is `2`-monophilic.

Along the way this settles the question that motivated the notion. Monophilicity is *strictly*
stronger than choosability:

```lean
open Monophilic in
example (m : ℕ) (hm : 2 ≤ m) :
    (theta m).Choosable 2 ∧ ¬ (theta m).Monophilic 2 :=
  choosable_and_not_monophilic_theta m hm
```

# Theorem 2

*A graph is `2`-monophilic if and only if it is not `2`-colourable, or its core is a single vertex,
an even cycle, or $`K_{2,3}`.*

The Lean statement carries the borrowed half of Rubin's theorem as an explicit hypothesis, and the
way it does so is the point of this section:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {CoreIsVertex CoreIsEvenCycle : Prop} {CoreIsTheta : ℕ → Prop}
    (rubin : G.Choosable 2 →
      CoreIsVertex ∨ CoreIsEvenCycle ∨ ∃ m, 1 ≤ m ∧ CoreIsTheta m)
    (hvertex : CoreIsVertex → G.Monophilic 2)
    (hcycle : CoreIsEvenCycle → G.Monophilic 2)
    (hK23 : CoreIsTheta 1 → G.Monophilic 2)
    (htheta : ∀ m, 2 ≤ m → CoreIsTheta m → ¬ G.Monophilic 2) :
    G.Monophilic 2 ↔
      ¬ G.Colorable 2 ∨ CoreIsVertex ∨ CoreIsEvenCycle ∨ CoreIsTheta 1 :=
  monophilic_two_iff_of_rubin_hard rubin hvertex hcycle hK23 htheta
```

Read it as follows. The three propositions `CoreIsVertex`, `CoreIsEvenCycle` and `CoreIsTheta m` are
*abstract* — they are quantified variables, with no definition attached. The hypothesis `rubin` says
that whenever `G` is `2`-choosable, one of them holds. The four remaining hypotheses say what
monophilicity does on each: the first three families are `2`-monophilic, and the theta graphs beyond
the smallest are not.

Every one of those four hypotheses is a theorem of this development, displayed above. The `rubin`
hypothesis is the only thing borrowed, and it is:

* a one-way implication, not an equivalence, because only that direction is used — the converse is
  proved, in {ref "twochoosable"}[the previous chapter];
* stated in terms of abstract propositions, so that nothing about what "core" means can be smuggled
  in through a definition.

That second point is a deliberate design decision and it is worth defending. If `CoreIsEvenCycle`
were *defined* here, the theorem would quietly depend on whatever that definition said, and a reader
could no longer tell by inspecting the statement how much had been assumed. Left abstract, the
theorem says precisely what it should: given Rubin's classification, and given the four
monophilicity facts about the families it names, the Kirov–Naimi characterization follows.

# How conditional is this, really?

Less than the shape of the statement suggests, and the difference matters.

What is *not* borrowed: that a single vertex, an even cycle and $`K_{2,3}` are `2`-monophilic; that
$`\theta_{2,2,2m}` is not, for `m ≥ 2`; that every graph on Rubin's list is `2`-choosable; and that
every theta graph of a shape other than $`(2,2,\text{even})` fails to be `2`-choosable — the last of
these being the classification `Monophilic.thetaClassification`, proved in full.

What *is* borrowed reduces, after the previous chapter, to a single purely structural claim with no
colouring in it: that the graph in question is a cycle, or $`\theta_{2,2,2m}`, or contains an odd
cycle, or contains a theta of another shape. Establishing that in general is a block or ear
decomposition argument, which Mathlib does not have.

So the honest summary is: *Theorem 2 is proved modulo one structural graph-theoretic lemma about
subgraph containment, and every colouring-theoretic ingredient is proved outright.* Two further
data points suggest the borrowed lemma is not hiding anything: it is *provable* for the two families
the theorem actually applies it to,

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

and the graphs it would have to exclude are individually excluded already, on their own vertex
models:

```lean
open Monophilic in
example : ¬ (thetaGen 3 3 3).Monophilic 2 :=
  not_monophilic_two_thetaGen_333
```

```lean
open Monophilic in
example : ¬ (thetaGen 1 3 3).Monophilic 2 :=
  not_monophilic_two_thetaGen_133
```

# What is left

The classification at `n = 2` is essentially complete; cycles are settled for every `n`; chordal
graphs are settled for every `n`. What is not settled is anything like a classification for `n ≥ 3`,
and it is not known what one would look like. What *is* known, and is the subject of
{ref "threshold"}[the last chapter], is that the question always has a positive answer eventually:
every graph is `n`-monophilic once `n` is large enough.
