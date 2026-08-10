import VersoManual
import Book.Papers
import Monophilic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Reading `Challenge.lean`" =>

%%%
tag := "readingchallenge"
%%%

Source: [comparator/Challenge.lean](https://github.com/rkirov/list-color-function/blob/main/comparator/Challenge.lean), [comparator/config.json](https://github.com/rkirov/list-color-function/blob/main/comparator/config.json), [comparator/Submission.lean](https://github.com/rkirov/list-color-function/blob/main/comparator/Submission.lean).

Everything up to here has been exposition. This chapter is a guide to a single file, and the file is
the point: `comparator/Challenge.lean` is the *statement surface* of the development — what is
claimed, stated exactly as the library states it, with the proofs removed.

If you have read Part I, you can now read that file top to bottom. Its nine sections are the eight
chapters you have just read, in the same order.

# What the file is for

The comparator is a checking harness. It takes two Lean modules — a *challenge* file containing
statements and a *submission* file containing proofs — and verifies that the submission proves
declarations with the same names and the same types, using only permitted axioms. `Challenge.lean`
is the first of those; the second is `Submission.lean`, which contains no mathematics at all:

> The comparator matches the placeholder statements of `Challenge.lean` against declarations of the
> same fully-qualified names in this module's environment. Every one of them is proved in the
> `Monophilic` library of this repository, under exactly those names, so importing the library is
> the whole submission — no re-export shim is needed, and none is wanted: a shim would put a second
> declaration between the comparator and the thing that was actually proved.

So `Challenge.lean` is a specification and `Submission.lean` is one line. What sits between them is
the library, and this book.

Compiling `Challenge.lean` on its own is *expected* to report "declaration uses `sorry`". That is
not a defect; the file exists to state, not to prove.

# The ten claims

`config.json` lists what is claimed under the key `theorem_names`, and it is a short list. Each of
the ten is displayed below with the library theorem that discharges it, in the file's own order.

*One: the chromatic polynomial evaluates to the colouring count* —
{ref "polynomial"}[the chromatic polynomial chapter].

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    (G.chromaticPolynomial).eval (n : ℤ) = (G.colConst n : ℤ) :=
  eval_chromaticPolynomial G n
```

*Two: $`P_\ell(G,n) = P(G,n)` is `n`-monophilicity* — {ref "lists"}[the lists chapter].

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (n : ℕ) :
    G.Monophilic n ↔
      (G.listColorFunction n : ℤ) = (G.chromaticPolynomial).eval (n : ℤ) :=
  monophilic_iff_listColorFunction_eq_eval n
```

*Three and four: $`K_{n,n^n}` is `n`-colourable but not `n`-choosable* — the Erdős–Rubin–Taylor
separation {citep erdosRubinTaylor}[], again {ref "lists"}[the lists chapter]. The two are claimed
together because either alone would miss the point, which is the gap between them.

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) : ¬ (K n).Choosable n := not_choosable n
```

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) (hn : 2 ≤ n) : (K n).Colorable n := colorable n hn
```

*Five: Kostochka–Sidorenko* — {ref "chordal"}[the chordal chapter].

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsChordal) (n : ℕ) :
    G.Monophilic n :=
  monophilic_of_isChordal G hG n
```

*Six: Dirac's theorem* {citep dirac}[] — same chapter, and the reason the fifth can be stated in its
own terms.

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsChordal ↔ ∃ (k : ℕ) (d : CliqueTowerData (Fin 0) k),
      CliqueTowerData.IsSimplicial (⊥ : SimpleGraph (Fin 0)) k d ∧
        Nonempty (G ≃g cliqueTower (⊥ : SimpleGraph (Fin 0)) k d) :=
  isChordal_iff_exists_cliqueTower G
```

*Seven: Theorem 1 of Kirov–Naimi* {citep kirovNaimi}[] — {ref "theorem1"}[the cycles chapter].

```lean
open Monophilic in
example {k m : ℕ} (hk : 2 ≤ k) : (closePath k).Monophilic (m + 2) :=
  monophilic_closePath_of_two_le hk
```

*Eight: Rubin's theorem, the direction that is proved* —
{ref "twochoosable"}[the `2`-choosability chapter].

```lean
open SimpleGraph Monophilic in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : RubinFamily G) :
    G.Choosable 2 :=
  choosable_two_of_rubinFamily G h
```

*Nine: Theorem 2 of Kirov–Naimi* — {ref "twomonophilic"}[the `2`-monophilicity chapter]. The one
statement in the list that carries a hypothesis: Rubin's theorem, which this development is in the
course of proving. The hypothesis is visible in the signature, and it is stated in the most
conservative form available — the three classes it names are quantified variables with no definition
attached, so nothing about what "core" means can be smuggled in through one.

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

*Ten: Donner's theorem* {citep donner}[] — {ref "threshold"}[the threshold chapter].

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ N, ∀ k, N ≤ k → G.Monophilic k :=
  exists_monophilic_forall_ge G
```

# The nine sections

```
### 1. Colouring a graph
### 2. The chromatic polynomial
### 3. Lists instead of a palette
### 4. Chordal graphs and Kostochka–Sidorenko
### 5. Theorem 1: every cycle is n-monophilic
### 6. The machinery behind Theorem 1
### 7. 2-choosability: Rubin's list
### 8. 2-monophilicity: Theorem 2
### 9. Every graph, eventually
```

:::table +header (align := left)
*
  * Section of `Challenge.lean`
  * Chapter
  * Claims
*
  * §1 Colouring a graph
  * {ref "colouring"}[Colouring a Graph]
  * none — vocabulary only
*
  * §2 The chromatic polynomial
  * {ref "polynomial"}[The Chromatic Polynomial]
  * 1
*
  * §3 Lists instead of a palette
  * {ref "lists"}[Lists Instead of a Palette]
  * 2, 3, 4
*
  * §4 Chordal graphs
  * {ref "chordal"}[First Answers: Chordal Graphs]
  * 5, 6
*
  * §5 Theorem 1
  * {ref "theorem1"}[Theorem 1: Cycles]
  * 7
*
  * §6 The machinery behind Theorem 1
  * {ref "paths"}[Paths], {ref "swapping"}[Swapping], {ref "cycles"}[Cycles]
  * none — prose only
*
  * §7 Rubin's list
  * {ref "twochoosable"}[Which Graphs Are 2-Choosable?]
  * 8
*
  * §8 Theorem 2
  * {ref "twomonophilic"}[Which Graphs Are 2-Monophilic?]
  * 9
*
  * §9 Every graph, eventually
  * {ref "threshold"}[Every Graph, Eventually]
  * 10
:::

Two sections carry no claim and are there for continuity. §1 defines the vocabulary every later
statement is written in — `col`, `colConst`, `IsProperColoring` — and claims nothing about it. §6 is
prose only: it names the three technical steps behind Theorem 1 (the nesting lemma for a bridge, the
strict monotonicity of the count on a path, and the two parts of Lemma 3), points at the library
names, and defines nothing. Part II of this book is where those live.

# Conventions

*Placeholders where a body is not a statement.* Every theorem has `sorry` for a proof — that is what
makes it a challenge file rather than a library. Most *definitions*, by contrast, carry their real
bodies, so that the file reads as a specification: the comparator never inspects the body of a
listed definition, so nothing is given away. Placeholders remain only where a body is not a
statement at all — the graph constructions built as `SimpleGraph` structure instances with
tactic-proved `symm` and `loopless` fields (`coneOn`, `addPendant`, `addPendantPair`), and the
decidability instances.

*`config.json` names what is claimed.* Two lists. `theorem_names` is the ten above. `definition_names`
is not a curated aesthetic choice but a computed one: exactly the definitions reachable from the
types of those ten statements, together with the notions those are in turn written in terms of, so
that the file can be read without the library open beside it.

*Instances are in the list because they are in the types.* `(closePath k).Monophilic (m + 2)` does
not typecheck without a `DecidableRel` for the adjacency of `closePath k`, a `Fintype` and a
`DecidableEq` for `PathV k`. Those instances therefore occur in the *type* of a listed theorem, and
the comparator's traversal demands that every constant reachable from a listed type be either a
listed definition or bit-identical between challenge and submission — which a placeholder body is
not. So they are listed, and they are the only instances that are.

*Two declarations appear without being listed*, because a *body* rather than a statement needs them:
the decidability of `IsProperColoring`, so that `colorings` can be written as a `Finset.filter`, and
the decidability of adjacency in `fromEdgeSet`, so that `compCount` can count components.

*Permitted axioms.* `config.json` also fixes `permitted_axioms` to Lean's three standard ones —
`propext`, `Quot.sound` and `Classical.choice`. In particular `sorryAx` is not among them, which is
what rules out an incomplete proof on the submission side.

# Where Lean fought the teaching order

Two places, both worth noticing because they are the only ones.

`ListAssignment` and `constList` are declared in §1, although conceptually they belong to §3. The
reason is that `col` is defined on a list assignment and the palette count `colConst` is its special
case — so the general notion has to exist before the special one can be named, even though the book
introduces them the other way round.

The chromatic polynomial sits at §2, before lists are introduced, which pulls `compCount` and the
`fromEdgeSet` decidability instance forward with it. That is the order the definitions force: §3's
reformulation of monophilicity as $`P_\ell = P` mentions the polynomial.

Neither is a distortion of the story. But they are a reminder that a Lean file is a dependency order
first and a narrative second, and that the two coincide less often than one would like.

# What is in the library and not in the file

A great deal. The file claims ten theorems; the library proves several hundred. Everything discussed
in this book that is not one of the ten — Kirov and Naimi's Lemmas 1 through 6, the three regimes,
the explicit threshold $`n > 2^{|E|}`, the counts $`A_k` and $`B_k` and their closed forms, Dirac's
lemma, Rubin's easy direction family by family, the classification of `2`-choosable theta graphs, the
witness assignments for the theta graphs — is in the library, under the names given in the section
headers of `Challenge.lean`.

The ten were chosen as the load-bearing ones: the results a reader would quote. Reading the file is
reading those ten and the vocabulary they need. Reading this book is everything else.
