import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Reading `Challenge.lean`" =>

%%%
tag := "readingchallenge"
%%%

Source:
[comparator/Challenge.lean](https://github.com/rkirov/list-color-function/blob/main/comparator/Challenge.lean),
[comparator/config.json](https://github.com/rkirov/list-color-function/blob/main/comparator/config.json),
[comparator/Submission.lean](https://github.com/rkirov/list-color-function/blob/main/comparator/Submission.lean).

Everything up to here has been exposition. This chapter is a guide to a single file, and the file is
the point: `comparator/Challenge.lean` is the *statement surface* of the development — what is
claimed, stated exactly as the library states it, with the proofs removed.

If you have read Part I, you can now read that file top to bottom. Its eight sections are the
eight chapters you have just read, in the same order.

# What the file is for

The comparator is a checking harness. It takes two Lean modules — a *challenge* file containing
statements and a *submission* file containing proofs — and verifies that the submission proves
declarations with the same names and the same types, using only permitted axioms. `Challenge.lean`
is the first of those; the second is `Submission.lean`, which contains no mathematics at all:

> The comparator matches the placeholder statements of `Challenge.lean` against declarations of the
> same fully-qualified names in this module's environment. Every one of them is proved in the
> `ListColoring` library of this repository, under exactly those names, so importing the library is
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

*Two: $`P_\ell(G,n) = P(G,n)` is enumerative chromatic-choosability at `n`* — {ref "lists"}[the
lists chapter].

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (n : ℕ) :
    G.ECCAt n ↔
      (G.listColorFunction n : ℤ) = (G.chromaticPolynomial).eval (n : ℤ) :=
  ecc_iff_listColorFunction_eq_eval n
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

*Five: the paper's §5 separation* — for every `k ≥ 2`, a graph that is `k`-choosable but not
enumeratively chromatic-choosable at `k`. The smallest instance is in {ref "lists"}[the lists
chapter]; the construction is {ref "notchoosable"}[a Part II chapter].

```lean
open SimpleGraph in
example {k : ℕ} (hk : 2 ≤ k) :
    ∃ (V : Type) (iF : Fintype V) (iD : DecidableEq V) (G : SimpleGraph V)
      (iA : DecidableRel G.Adj), @Choosable V iF iD G iA k ∧ ¬ @ECCAt V iF iD G iA k :=
  KN5.exists_choosable_not_ecc_of_two_le hk
```

*Six: Kostochka–Sidorenko* — {ref "chordal"}[the chordal chapter]. Dirac's theorem {citep dirac}[]
— chordal ⟺ a simplicial elimination ordering, the reason this claim can say "chordal" — is
proved in the library and displayed in that chapter, but it is scaffolding for a statement rather
than a list-colouring result, so it is not claimed.

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsChordal) (n : ℕ) :
    G.ECCAt n :=
  ecc_of_isChordal G hG n
```

*Seven: Theorem 1 of Kirov–Naimi* {citep kirovNaimi}[] — {ref "theorem1"}[the cycles chapter].
Stated on Mathlib's `SimpleGraph.cycleGraph`, so the claim involves no graph construction of this
development; the form on the development's own `closePath`, which the proof machinery runs on, is
{name ListColoring.ecc_closePath_of_two_le}`ecc_closePath_of_two_le`.

```lean
open SimpleGraph in
example {n m : ℕ} (hn : 3 ≤ n) : (cycleGraph n).ECCAt (m + 2) :=
  ecc_cycleGraph_of_three_le hn
```

*Eight: Rubin's theorem* {citep erdosRubinTaylor}[] —
{ref "twochoosable"}[the `2`-choosability chapter]. Like Theorem 1, it is claimed on Mathlib's
graphs: a single vertex is `⊥` on `Fin 1`, a cycle is `cycleGraph n`, and $`\theta_{2,2,2m}` is
`thetaGraph m`, the cycle $`C_{2m+2}` with one extra vertex joined to `0` and `2`. The forms on
the development's own path-built models are {name ListColoring.rubinTheorem}`rubinTheorem` and
{name ListColoring.ecc_two_iff}`ecc_two_iff` in the library, and the claimed statements are proved
from them by transporting `CoreIs` along the isomorphisms of the cores.

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    G.Choosable 2 ↔
      CoreIsVertex G ∨ CoreIsEvenCycle G ∨ CoreIsTheta G :=
  rubinTheorem G hconn
```

*Nine: Theorem 2 of Kirov–Naimi* — {ref "twoecc"}[the enumerative chromatic-choosability at `2`
chapter]. It carries no hypothesis beyond connectivity.

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    G.ECCAt 2 ↔
      CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨
        HasOddCycle G :=
  ecc_two_iff G hconn
```

*Ten: Donner's theorem* {citep donner}[] — {ref "threshold"}[the threshold chapter].

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ N, ∀ k, N ≤ k → G.ECCAt k :=
  exists_ecc_forall_ge G
```

# The eight sections

```
### 1. Colouring a graph
### 2. The chromatic polynomial
### 3. Lists instead of a palette
### 4. Chordal graphs and Kostochka–Sidorenko
### 5. Theorem 1: every cycle is enumeratively chromatic-choosable at `n`
### 6. 2-choosability: Rubin's theorem
### 7. Enumerative chromatic-choosability at `2`: Theorem 2
### 8. Every graph, eventually
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
  * {ref "lists"}[Lists Instead of a Palette], {ref "notchoosable"}[Colorable but Not Choosable]
  * 2, 3, 4, 5
*
  * §4 Chordal graphs
  * {ref "chordal"}[First Answers: Chordal Graphs]
  * 6
*
  * §5 Theorem 1
  * {ref "theorem1"}[Theorem 1: Cycles]
  * 7
*
  * §6 Rubin's theorem
  * {ref "twochoosable"}[Which Graphs Are 2-Choosable?]
  * 8
*
  * §7 Theorem 2
  * {ref "twoecc"}[Which Graphs Are Enumeratively Chromatic-Choosable at 2?]
  * 9
*
  * §8 Every graph, eventually
  * {ref "threshold"}[Every Graph, Eventually]
  * 10
:::

One section carries no claim: §1 defines the vocabulary every later statement is written in —
`col`, `colConst`, `IsProperColoring` — and claims nothing about it. The machinery behind
Theorem 1 — the nesting lemma for a bridge, the strict monotonicity of the count on a path, the
two parts of Lemma 3 — has no section at all; {ref "paths"}[Paths], {ref "swapping"}[Swapping]
and {ref "cycles"}[Cycles] in Part II are where it lives.

# Conventions

*Every definition carries its real body.* Every theorem has `sorry` for a proof — that is what
makes it a challenge file rather than a library. Definitions, by contrast, are given in full, down
to the tactic-proved `symm` and `loopless` fields of the two pendant attachments and the adjacency
matches (`addPendantAdj`, `addPendantPairAdj`) they are built on, so the file reads as a complete
specification; the comparator never inspects the body of a listed definition, so nothing is given
away. Only two decidability instances are `sorry`, and a `Decidable` instance is a subsingleton:
which one is used cannot change any count.

*`config.json` names what is claimed.* Two lists. `theorem_names` is the ten above.
`definition_names` is not a curated aesthetic choice but a computed one: exactly the definitions
reachable from the types of those ten statements, together with the notions those are in turn
written in terms of, so that the file can be read without the library open beside it.

*Instances are in the list because the surface needs them.* The Erdős–Rubin–Taylor claims' types
need decidable adjacency for `K n`, and the core alternatives name `⊥ : SimpleGraph (Fin 1)`,
`cycleGraph n` and `thetaGraph m` through `CoreIs`, which asks for decidable adjacency and finite,
decidable vertex types. Mathlib's own instances serve everything except `thetaGraph`, which
carries its two (`instDecidableRelAddPendantPair`, `instDecidableRelThetaGraph`). The comparator's
traversal demands that every constant reachable from the listed statements be either a listed
definition or bit-identical between challenge and submission, so those three instances are listed,
and they are the only instances that are.

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
reformulation of enumerative chromatic-choosability as $`P_\ell = P` mentions the polynomial.

Neither is a distortion of the story. But they are a reminder that a Lean file is a dependency order
first and a narrative second, and that the two coincide less often than one would like.

# What is in the library and not in the file

A great deal. The file claims ten theorems; the library proves several hundred. Everything
discussed in this book that is not one of the ten — Kirov and Naimi's Lemmas 1 through 6, the
three regimes,
the explicit threshold $`n > 2^{|E|}`, the counts $`A_k` and $`B_k` and their closed forms,
Dirac's theorem and Dirac's lemma, Theorem 1 on the development's own `closePath`, Rubin's easy
direction family by family, the classification of `2`-choosable generalized theta graphs at every
arity, the dumbbell, the six cases of Rubin's steps 5 and 6, the witness assignments for the theta
graphs — is in the library.

The count is derived, not chosen: one claim per named list-colouring result. Two claims pin down
what the subject is, five statements are the four named theorems of the literature the development
stands on — the Erdős–Rubin–Taylor separation being one result in two statements — and three are
the results the paper's abstract advertises. Reading the file is reading those ten and the
vocabulary they need. Reading this book is everything else.
