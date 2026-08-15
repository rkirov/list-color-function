import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Lists Instead of a Palette" =>

%%%
tag := "lists"
%%%

Source: [Defs.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Defs.lean),
[Basic.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Basic.lean),
[NotChoosable.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/NotChoosable.lean),
[ListColorFunction.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/ListColorFunction.lean).

So far every vertex drew its colour from the same palette $`\{0, \dots, n-1\}`. Now give each vertex
its own private list of permitted colours, all lists of the same size `n`, and ask the same two
questions: is there a proper colouring, and how many are there?

This is not a perverse generalization. It is what you get whenever the constraint is local: a
timetable in which each course may only use the rooms it fits in, a frequency assignment in which
each transmitter has its own licensed band. The uniform palette is the special case where every
vertex happens to have the same options.

# List assignments

A list assignment gives each vertex a finite set of naturals. An `n`-list assignment gives each
vertex exactly `n` of them.

```lean
open SimpleGraph in
example {V : Type} (L : ListAssignment V) (n : ℕ) :
    IsNListAssignment L n ↔ ∀ v, (L v).card = n :=
  Iff.rfl
```

`G.col L` counts the proper colourings that respect `L`, and the uniform count of the previous two
chapters is the special case where every list is $`\{0, \dots, n-1\}`:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    G.colConst n = G.col (constList V n) :=
  rfl
```

Two remarks before anything else.

First, lists of *different* sizes are allowed by the definition of `col`, and the development uses
that freedom constantly — the deletion identity produces shorter lists at the neighbours of a
deleted vertex. But the statements we care about always compare assignments of one fixed common
size, because comparing counts across different list sizes is not meaningful.

Second, only the sizes and the *pattern of overlaps* matter, never the names of the colours.
Renaming the colours by any injection changes nothing, and that is proved once so that the paper's
innumerable "without loss of generality" steps have something to appeal to.

# Choosability

`G` is `n`-*choosable* when *every* `n`-list assignment admits at least one proper colouring.

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    G.Choosable n ↔ ∀ L : ListAssignment V, IsNListAssignment L n → 0 < G.col L :=
  Iff.rfl
```

The least `n` for which `G` is `n`-choosable is the *list chromatic number* $`\chi_\ell(G)`, also
called the choice number. Taking every list to be $`\{0,\dots,n-1\}` shows immediately that
`n`-choosable implies `n`-colourable, so

$$`\chi(G) \le \chi_\ell(G).`

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ} (h : G.Choosable n) :
    G.Colorable n :=
  colorable_of_choosable h
```

The natural guess is that this is an equality — that if `n` colours suffice when they are shared,
`n` colours suffice when they are private. The guess is wrong, and the smallest counterexample is
small enough to check by hand.

# Where they differ: $`K_{2,4}`

Take the complete bipartite graph with two vertices on the left and four on the right, every left
vertex joined to every right vertex. It is bipartite, so $`\chi = 2`. Now assign lists:

```diagram (cssWidth := "72%")
open Illuminate Diagram in
let v (x y : Float) : Diagram SVG := translate x y (circle 9)
let e (x1 y1 x2 y2 : Float) : Diagram SVG := line ⟨x1, y1⟩ ⟨x2, y2⟩
let left := [v (-150) 70, v (-150) (-70)]
let right := [v 150 165, v 150 55, v 150 (-55), v 150 (-165)]
let edges :=
  [e (-150) 70 150 165, e (-150) 70 150 55, e (-150) 70 150 (-55), e (-150) 70 150 (-165),
   e (-150) (-70) 150 165, e (-150) (-70) 150 55, e (-150) (-70) 150 (-55),
   e (-150) (-70) 150 (-165)]
let labels :=
  [translate (-215) 70 (text "{0,1}"), translate (-215) (-70) (text "{2,3}"),
   translate 215 165 (text "{0,2}"), translate 215 55 (text "{0,3}"),
   translate 215 (-55) (text "{1,2}"), translate 215 (-165) (text "{1,3}")]
(edges ++ left ++ right ++ labels).foldl atop emptyDiagram
```

Every list has two colours. The left vertices must take one colour each — say `a` from `{0,1}` and
`b` from `{2,3}` — and there are four possible pairs `(a,b)`. But the four right-hand lists are
exactly the four possible pairs. Whichever pair the left side chooses, the right vertex carrying
that very pair is adjacent to both and has nothing left. So there is no proper colouring at all:
$`K_{2,4}` is `2`-colourable but not `2`-choosable, and $`\chi_\ell = 3 > 2 = \chi`.

This graph is `ERT.K 2` in the development — the Erdős–Rubin–Taylor example
{citep erdosRubinTaylor}[] — and the lists above are `ERT.L₀ 2`:

```lean
open SimpleGraph SimpleGraph.ERT in
example : (L₀ 2 (Sum.inl 0), L₀ 2 (Sum.inl 1))
    = (({0, 1} : Finset ℕ), ({2, 3} : Finset ℕ)) := by decide
```

```lean
open SimpleGraph SimpleGraph.ERT in
example : L₀ 2 (Sum.inr ![0, 1]) = ({0, 3} : Finset ℕ) := by decide
```

The right side is indexed by the *functions* `Fin 2 → Fin 2` — one right vertex per possible choice
by the left side — and that indexing is what generalizes. For any `n`, put `n` vertices on the left
and $`n^n` on the right, give the `i`-th left vertex the `i`-th block of `n` consecutive colours,
and give the right vertex indexed by `φ` the list picking colour `φ(i)` out of block `i`. Any
colouring of the left side determines one such `φ`, and the right vertex indexed by that `φ` is
blocked. So:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) : ¬ (K n).Choosable n :=
  not_choosable n
```

while, being bipartite, it is `n`-colourable for every `n ≥ 2`:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) (hn : 2 ≤ n) : (K n).Colorable n :=
  colorable n hn
```

The gap between $`\chi` and $`\chi_\ell` can therefore be arbitrarily large, on bipartite graphs at
that.

# The list colour function

Now count rather than merely ask for existence. Fix `n`, and let `L` range over all `n`-list
assignments. The set of counts obtained is a nonempty set of naturals, so it has a least element,
and that least element is the *list colour function*:

$$`P_\ell(G, n) = \min_L \mathrm{col}(G, L).`

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    G.listColorFunction n = sInf (G.colCounts n) :=
  rfl
```

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} {L : ListAssignment V} (hL : IsNListAssignment L n) :
    G.listColorFunction n ≤ G.col L :=
  listColorFunction_le_col hL
```

The uniform assignment is one of the competitors, so

$$`P_\ell(G, n) \le P(G, n)`

always:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    G.listColorFunction n ≤ G.colConst n :=
  listColorFunction_le_colConst n
```

Everything in this book is about when that inequality is an equality.

# Enumerative chromatic-choosability

Kostochka and Sidorenko {citep kostochkaSidorenko}[] asked the question in the following form. Give
every vertex the same list. Intuitively that should be the *worst* case for the count: identical
lists at adjacent vertices create the maximum number of conflicts, and any deviation should free up
colourings. Is the uniform assignment always a minimizer?

Kirov and Naimi {citep kirovNaimi}[] call a graph for which the answer is yes `n`-*monophilic* —
it loves sameness. That is the historical name. The one the literature settled on is
*enumeratively chromatic-choosable at `n`*, because `P_ℓ` is the enumerative analogue of the
chromatic polynomial and so agreement of the two lifts Ohba's *chromatic-choosable*,
$`\chi(G) = \chi_\ell(G)`, from a number to a counting function. The development uses the modern
name: `SimpleGraph.ECCAt` for the property at a single `n`, and `SimpleGraph.ECC` for all `n` at
once. The Lean definition is the inequality, unadorned:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    G.ECCAt n ↔
      ∀ L : ListAssignment V, IsNListAssignment L n → G.colConst n ≤ G.col L :=
  Iff.rfl
```

and it is exactly the statement that the two functions of the previous section agree:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (n : ℕ) :
    G.ECCAt n ↔ G.listColorFunction n = G.colConst n :=
  ecc_iff_listColorFunction_eq n
```

or, in the notation the literature uses, that $`P_\ell(G, n) = P(G, n)` with a genuine polynomial on
the right:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (n : ℕ) :
    G.ECCAt n ↔
      (G.listColorFunction n : ℤ) = (G.chromaticPolynomial).eval (n : ℤ) :=
  ecc_iff_listColorFunction_eq_eval n
```

The two phrasings are interchangeable and both appear below; "enumeratively chromatic-choosable" is
shorter, and $`P_\ell = P` is what you will find in the literature.

# Three regimes

Whether a graph is enumeratively chromatic-choosable at `n` is only interesting for some `n`, and
the boundaries are the two chromatic numbers. Fix `G` and vary `n`.

*Below $`\chi(G)`.* There are no colourings from the uniform palette at all, so the inequality
$`\mathrm{col}(G,n) \le \mathrm{col}(G,L)` reads `0 ≤ ...` and holds for nothing better than
vacuous reasons.

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ} (h : ¬ G.Colorable n) :
    G.ECCAt n :=
  ecc_of_not_colorable h
```

The five-cycle is enumeratively chromatic-choosable at `2` for this reason and no other:

```lean
open SimpleGraph ListColoring in
example : (closePath 4).ECCAt 2 :=
  ecc_of_not_colorable
    (not_colorable_two_closePath_of_even (by decide) (by norm_num))
```

*Between $`\chi(G)` and $`\chi_\ell(G)`.* Here the uniform assignment has colourings but some other
`n`-assignment has none, so the minimum is `0` and the uniform count is not. Enumerative
chromatic-choosability fails, always.

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}
    (hcol : G.Colorable n) (hch : ¬ G.Choosable n) :
    ¬ G.ECCAt n :=
  not_ecc_of_colorable_of_not_choosable hcol hch
```

$`K_{2,4}` is the example: `2`-colourable, not `2`-choosable, hence not enumeratively
chromatic-choosable at `2`. Its uniform count is `2` — one colour on each side, two ways round — and
the assignment drawn above achieves `0`.

```lean
open SimpleGraph SimpleGraph.ERT in
example : (K 2).colConst 2 = 2 := by decide
```

```lean
open SimpleGraph SimpleGraph.ERT in
example : ¬ (K 2).ECCAt 2 :=
  not_ecc 2 (by norm_num)
```

*At or above $`\chi_\ell(G)`.* This is the only regime with content, and the reason is worth stating
as its own implication: an enumeratively chromatic-choosable graph that is colourable is
automatically choosable, because the minimum count is then positive.

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}
    (hmono : G.ECCAt n) (hcol : G.Colorable n) :
    G.Choosable n :=
  choosable_of_ecc_of_colorable hmono hcol
```

:::table +header (align := left)
*
  * range of `n`
  * $`P(G,n)`
  * $`P_\ell(G,n)`
  * enumeratively chromatic-choosable?
*
  * $`n < \chi(G)`
  * `0`
  * `0`
  * yes, vacuously
*
  * $`\chi(G) \le n < \chi_\ell(G)`
  * positive
  * `0`
  * no, always
*
  * $`\chi_\ell(G) \le n`
  * positive
  * positive
  * the real question
:::

So enumerative chromatic-choosability is a strengthening of choosability, and the interesting
content of the notion is what happens *after* choosability has been achieved.

# It really can fail

The remaining question is whether the third regime ever produces a failure — whether a graph can be
`n`-choosable and still prefer some non-uniform assignment. It can. The smallest example in this
book is the theta graph $`\theta_{2,2,4}`: two vertices joined by three internally disjoint paths of
lengths `2`, `2` and `4`. It is `2`-choosable, its uniform count at `n = 2` is `2`,

```lean
open ListColoring in
example (m : ℕ) (hm : 1 ≤ m) : (theta m).colConst 2 = 2 :=
  colConst_theta m hm
```

and there is an explicit `2`-list assignment achieving `1`:

```lean
open ListColoring in
example (m : ℕ) (hm : 2 ≤ m) : (theta m).col (thetaWitness m) = 1 :=
  col_theta_witness m hm
```

One is less than two, so $`\theta_{2,2,4}` is not enumeratively chromatic-choosable at `2`.

Section 5 of the paper turns the example into a theorem at every list size: for each `k ≥ 2` there
is a graph that is `k`-choosable and still not enumeratively chromatic-choosable at `k`. The
construction is {ref "notchoosable"}[a Part II chapter]; the statement needs nothing but the two
definitions above.

```lean
open SimpleGraph in
example {k : ℕ} (hk : 2 ≤ k) :
    ∃ (V : Type) (iF : Fintype V) (iD : DecidableEq V) (G : SimpleGraph V)
      (iA : DecidableRel G.Adj), @Choosable V iF iD G iA k ∧ ¬ @ECCAt V iF iD G iA k :=
  KN5.exists_choosable_not_ecc_of_two_le hk
```

The intuition that sameness is worst is simply false in general, and the rest of this book is about
the graphs for which it is nevertheless true.
