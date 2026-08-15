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

If you have read Part I, you can now read that file top to bottom. Its nine sections are the eight
chapters you have just read, in the same order.

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

# The eleven claims

`config.json` lists what is claimed under the key `theorem_names`, and it is a short list. Each of
the eleven is displayed below with the library theorem that discharges it, in the file's own order.

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

*Six: Kostochka–Sidorenko* — {ref "chordal"}[the chordal chapter].

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsChordal) (n : ℕ) :
    G.ECCAt n :=
  ecc_of_isChordal G hG n
```

*Seven: Dirac's theorem* {citep dirac}[] — same chapter, and the reason the sixth can be stated in
its own terms.

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsChordal ↔ ∃ (k : ℕ) (d : CliqueTowerData (Fin 0) k),
      CliqueTowerData.IsSimplicial (⊥ : SimpleGraph (Fin 0)) k d ∧
        Nonempty (G ≃g cliqueTower (⊥ : SimpleGraph (Fin 0)) k d) :=
  isChordal_iff_exists_cliqueTower G
```

*Eight: Theorem 1 of Kirov–Naimi* {citep kirovNaimi}[] — {ref "theorem1"}[the cycles chapter].

```lean
open ListColoring in
example {k m : ℕ} (hk : 2 ≤ k) : (closePath k).ECCAt (m + 2) :=
  ecc_closePath_of_two_le hk
```

*Nine: Rubin's theorem* {citep erdosRubinTaylor}[] —
{ref "twochoosable"}[the `2`-choosability chapter].

```lean
open ListColoring in
example : RubinTheorem := rubinTheorem
```

That display is unusual, and deliberately so. The claimed theorem's type is the bare constant
{name ListColoring.RubinTheorem}`RubinTheorem`, so *the statement of Rubin's theorem is the body of
that definition* — unfolding it is the only way to see what claim nine says:

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

`Challenge.lean` therefore reproduces that body verbatim rather than leaving it a placeholder; the
comparator matches `RubinTheorem` by its type, which is only `Prop`, so the library is where the
statement is really checked.

*Ten: Theorem 2 of Kirov–Naimi* — {ref "twoecc"}[the enumerative chromatic-choosability at `2`
chapter]. It carries no hypothesis beyond connectivity.

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    G.ECCAt 2 ↔
      CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨
        HasOddCycle G :=
  ecc_two_iff G hconn
```

*Eleven: Donner's theorem* {citep donner}[] — {ref "threshold"}[the threshold chapter].

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ N, ∀ k, N ≤ k → G.ECCAt k :=
  exists_ecc_forall_ge G
```

# The nine sections

```
### 1. Colouring a graph
### 2. The chromatic polynomial
### 3. Lists instead of a palette
### 4. Chordal graphs and Kostochka–Sidorenko
### 5. Theorem 1: every cycle is enumeratively chromatic-choosable at `n`
### 6. The machinery behind Theorem 1
### 7. 2-choosability: Rubin's theorem
### 8. Enumerative chromatic-choosability at `2`: Theorem 2
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
  * {ref "lists"}[Lists Instead of a Palette], {ref "notchoosable"}[Colorable but Not Choosable]
  * 2, 3, 4, 5
*
  * §4 Chordal graphs
  * {ref "chordal"}[First Answers: Chordal Graphs]
  * 6, 7
*
  * §5 Theorem 1
  * {ref "theorem1"}[Theorem 1: Cycles]
  * 8
*
  * §6 The machinery behind Theorem 1
  * {ref "paths"}[Paths], {ref "swapping"}[Swapping], {ref "cycles"}[Cycles]
  * none — prose only
*
  * §7 Rubin's theorem
  * {ref "twochoosable"}[Which Graphs Are 2-Choosable?]
  * 9
*
  * §8 Theorem 2
  * {ref "twoecc"}[Which Graphs Are Enumeratively Chromatic-Choosable at 2?]
  * 10
*
  * §9 Every graph, eventually
  * {ref "threshold"}[Every Graph, Eventually]
  * 11
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

*`config.json` names what is claimed.* Two lists. `theorem_names` is the eleven above.
`definition_names` is not a curated aesthetic choice but a computed one: exactly the definitions
reachable from the types of those eleven statements, together with the notions those are in turn
written in terms of, so that the file can be read without the library open beside it.

*Instances are in the list because they are in the types.* `(closePath k).ECCAt (m + 2)` does
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
reformulation of enumerative chromatic-choosability as $`P_\ell = P` mentions the polynomial.

Neither is a distortion of the story. But they are a reminder that a Lean file is a dependency order
first and a narrative second, and that the two coincide less often than one would like.

# What is in the library and not in the file

A great deal. The file claims eleven theorems; the library proves several hundred. Everything
discussed in this book that is not one of the eleven — Kirov and Naimi's Lemmas 1 through 6, the
three regimes,
the explicit threshold $`n > 2^{|E|}`, the counts $`A_k` and $`B_k` and their closed forms, Dirac's
lemma, Rubin's easy direction family by family, the classification of `2`-choosable generalized
theta graphs at every arity, the dumbbell, the six cases of Rubin's steps 5 and 6, the witness
assignments for the theta graphs — is in the library, under the names given in the section headers
of `Challenge.lean`.

The count is derived, not chosen: one claim per named result. Two claims pin down what the subject
is, six statements are the five named theorems of the literature the development stands on — the
Erdős–Rubin–Taylor separation being one result in two statements — and three are the results the
paper's abstract advertises. Reading the file is reading those eleven and the vocabulary they need.
Reading this book is everything else.
