import VersoManual
import Book.Papers
import Monophilic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Cores" =>

%%%
tag := "cores"
%%%

Source: [Core.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Core.lean), [K23.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/K23.lean).

Theorem 2 of the paper characterizes the `2`-monophilic graphs, and it does so in terms of a graph's
**core** — what is left after repeatedly deleting vertices of degree 1 until every remaining vertex
has degree at least 2. Lemma 5 is what makes that reduction legitimate: a connected graph is
`n`-monophilic exactly when its core is.

# A pendant vertex is a cone over a singleton

The whole of Lemma 5 is one step, repeated. Attaching a vertex of degree 1 is a special case of the
construction already used for Lemma 1 — coning over a clique — because a one-element set is
trivially a clique:

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.addPendant v = coneOn G {v} :=
  addPendant_eq_coneOn v
```

So one direction of Lemma 5 is free: it is Lemma 1 specialized to a singleton.

# The exact pendant counts

Specializing the cone's extension count to `K = {v}` gives an identity with no error term, because
a coloring uses exactly one color at `v`:

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (v : V) (n : ℕ) :
    (coneOn G {v}).colConst n = (n - 1) * G.colConst n :=
  colConst_coneOn_singleton v n
```

The converse needs a matching identity for *arbitrary* lists, and here there is a choice to make.
Given a list assignment `L` on `G`, we must extend it to the new vertex. Give the new vertex **the
same list as its neighbor**. Then every coloring already uses one of those colors at `v`, so exactly
`n - 1` remain — the count is again exact rather than merely bounded:

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : ListAssignment V} {n : ℕ}
    (hL : IsNListAssignment L n) (v : V) :
    (coneOn G {v}).col (extendList L v) = (n - 1) * G.col L :=
  col_coneOn_singleton_extend hL v
```

Monophilicity of the cone now reads `(n-1) · colConst G n ≤ (n-1) · col G L`, and cancelling `n-1`
gives monophilicity of `G`. Both directions together:

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (n : ℕ) :
    (G.addPendant v).Monophilic n ↔ G.Monophilic n :=
  monophilic_addPendant_iff v n
```

# A hypothesis that turned out to be an artifact

The cancellation above needs `n - 1 ≠ 0`, so the natural statement carries `2 ≤ n`. And the
hypothesis really is needed *for that argument*: at `n ≤ 1` the cone identity degenerates to
`0 ≤ 0` and says nothing at all, since a pendant vertex has no color available once its neighbor is
colored.

But the conclusion survives anyway, for a reason that has nothing to do with the argument: at
`n ≤ 1` every graph is `n`-monophilic outright.

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (hn : n ≤ 1) :
    G.Monophilic n :=
  monophilic_of_le_one hn
```

So the equivalence is stated with no hypothesis on `n`. This is a small thing, but it is the kind of
small thing mechanization is good at: the `2 ≤ n` looks essential right up until you ask what
happens without it, and then the degenerate case turns out to be trivially true rather than false.

# Iterating: the tower form

Lemma 5 as printed speaks of "the core", defined by repeated deletion. Formalizing a fixpoint of
degree-1 deletion over an arbitrary vertex type is awkward and, it turns out, unnecessary: what the
paper's arguments actually use is the reverse direction — that building a graph up from its core by
repeatedly attaching pendant vertices preserves monophilicity in both directions. That is directly
expressible, and it allows a new pendant to attach to a previously added one, which is the general
case:

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n k : ℕ) (d : TowerData V k) :
    (pendantTower G k d).Monophilic n ↔ G.Monophilic n :=
  monophilic_pendantTower_iff n k d
```

A pleasant check on the definition: a path is nothing but a tower of pendant attachments, and the
two constructions — built independently, in different files, for different purposes — turn out to be
*definitionally* the same graph:

```lean
open SimpleGraph Monophilic in
example : pendantTower (pathG 0) 2 ((PUnit.unit, pathEnd 0), pathEnd 1) = pathG 2 :=
  rfl
```

# The other ingredient: K₂,₃

Theorem 2's list of possible cores contains one graph that is neither a vertex nor a cycle, and it
has to be handled by hand:

```diagram (cssWidth := "56%")
open Illuminate Diagram in
let v (x y : Float) : Diagram _ := translate x y (circle 8)
let e (x1 y1 x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
let small := [v 0 70, v 0 (-70)]
let large := [v 170 90, v 170 0, v 170 (-90)]
let edges := [e 0 70 170 90, e 0 70 170 0, e 0 70 170 (-90),
              e 0 (-70) 170 90, e 0 (-70) 170 0, e 0 (-70) 170 (-90)]
let labels := [translate (-24) 70 (text "x"), translate (-24) (-70) (text "y"),
               translate 196 90 (text "u"), translate 196 0 (text "v"),
               translate 196 (-90) (text "w")]
(edges ++ small ++ large ++ labels).foldl atop emptyDiagram
```

Everything follows from a decomposition of the count. The two vertices on
the small side are non-adjacent to each other, the three on the large side are pairwise
non-adjacent, and every small-side vertex is adjacent to every large-side one. So a colouring is:
choose colours `a` and `b` on the small side freely, then choose independently for each large-side
vertex any colour of its list other than `a` and `b`.

```lean
open Finset SimpleGraph in
example (L : ListAssignment (Fin 2 ⊕ Fin 3)) :
    (completeBipartiteGraph (Fin 2) (Fin 3)).col L
      = ∑ a ∈ L (Sum.inl 0), ∑ b ∈ L (Sum.inl 1),
          ∏ j : Fin 3, (L (Sum.inr j) \ {a, b}).card :=
  col_completeBipartite_two_three L
```

After that the lemma is finite combinatorics about five two-element sets, and the count from the
uniform list is `2`:

```lean
open SimpleGraph in
example : (completeBipartiteGraph (Fin 2) (Fin 3)).colConst 2 = 2 :=
  colConst_completeBipartite_two_three_two
```

```lean
open SimpleGraph in
example : (completeBipartiteGraph (Fin 2) (Fin 3)).Monophilic 2 :=
  monophilic_K23
```

The paper splits the argument by `|L(x) ∩ L(y)|` into three cases. Mechanizing it showed that the
first two collapse into one. If the two small-side lists share a colour `p`, there are two
possibilities: some large-side list omits `p`, in which case the single term `(p,p)` already
contributes `2`; or every large-side list contains `p`, in which case pick *any* `u ∈ L(x)` and
`v ∈ L(y)` other than `p`, and both `(p,p)` and `(u,v)` contribute — because `p` survives in every
large-side list, `p` being different from `u` and `v`. That covers `L(x) = L(y)` and
`|L(x) ∩ L(y)| = 1` uniformly. Only the disjoint case needs a separate argument, and there the
counting is genuinely tight: with `L(x)={0,1}`, `L(y)={2,3}` and large-side lists
`{0,2}, {0,3}, {1,2}`, three of the four possible pairs are killed and the total is exactly `2`.
