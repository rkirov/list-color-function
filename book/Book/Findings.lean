import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true

#doc (Manual) "What Mechanization Found" =>

%%%
tag := "findings"
%%%

It is worth separating out what formalizing this paper actually taught us, as distinct from what it
merely confirmed. Nothing below is an error in the paper. The interesting findings are of three
kinds: hypotheses that turned out to be load-bearing in a specific and identifiable way, hypotheses
that turned out to be unnecessary, and pieces of received wisdom about the surrounding literature
that did not survive checking.

# Hypotheses that are exactly load-bearing

**"A path of length at least one."** The paper's definition of an `(n,n-1)`-list assignment carries
this restriction, and it is easy to read past. Part (c) of Lemma 3 is precisely the claim that needs
it. At length zero the two terminal vertices coincide, every `(n,n-1)`-assignment is therefore
minimizing, and every such assignment is type A — while zero is even, so (c) would demand type B.
The development contains a machine-checked witness. What mechanization contributes here is not a
correction but a sharpening: it identifies the unique claim that fails and produces the
counterexample.

**`n ≥ 3` in part (c), but not in part (b).** Part (b) holds with no hypothesis on `n` at all: at
`n = 2` the bound `min(A_k, B_k) ≤ col` is true because the minimum is zero. The `n ≥ 3` in the
lemma statement is needed only by (c), where it is what guarantees that both sides of a cut path
have all lists of size at least two, so that the strictness in the swap lemma is available.

**The tightness of Case 2 of Theorem 1.** The even-cycle case admits an obvious-looking argument —
one fibre contributes `A + 1`, the rest contribute `B` — which yields `nA - n + 2` and therefore
fails for every `n ≥ 3`. The paper's argument is genuinely stronger and has no slack: `B + (A+1) +
(n-2)A = nA` on the nose. This is the kind of thing a careful reader can miss, because the printed
proof does not advertise that the weaker bookkeeping is insufficient.

# Hypotheses that are not needed

**Equation (1) of Lemma 2 does not need `c₂ ∈ L(v₂)`.** The counting identity uses only that `c₁` is
available at `v₁`, unavailable at `v₂`, and that `c₂` is unavailable at `v₁`. The hypothesis
`c₂ ∈ L(v₂)` is what makes the swap decrease the nesting defect, and so is needed for termination —
but it plays no role in the identity itself.

**The extension count for cones needs no clique hypothesis.** In Lemma 1 the identity
`col(coneOn G K, M) = ∑ |M(none) \ f(K)|` and the resulting inequality are true for an arbitrary
vertex set `K`. The clique hypothesis is needed only to collapse the sum to an exact product in the
uniform case.

**No rotation automorphism is needed for Theorem 1.** The paper deletes an edge chosen so that its
endpoints have different lists, which appears to require moving that edge into a canonical position.
It does not: in the deficient case the shape of the assignment already forces the two neighbors of
the distinguished vertex to carry different lists.

**Minimizers exist without a finite-palette argument.** Colors range over `ℕ`, so the space of
assignments is infinite; the natural move is to relabel into a finite palette and minimize there.
Unnecessary — the set of achievable counts is a nonempty set of naturals and has a least element.

# The termination of Lemma 2

One place where the informal phrasing is right and the obvious formalization is wrong. Iterating the
swap decreases the number of colors available at `v₁` but not at `v₂`. When that measure reaches
zero the lists are nested and we are done — but the process can also halt with the measure still
positive, when the *other* containment holds and no swap is available. The paper's loop condition
("as long as `L(v₁) ⊄ L(v₂)` and `L(v₂) ⊄ L(v₁)`") is exactly correct; it is an induction on the
measure alone that fails to cover the second exit.

# Checking statements before proving them

A habit worth naming, because it paid for itself repeatedly. Before any Lean effort went into a
statement, the statement was checked by brute-force evaluation on small cases. Three examples from
this development:

* The `A_k` / `B_k` recurrences and the path graph were written independently and then checked
  against each other: at `n = 3` a path of length one carries `2` type A and `3` type B colorings,
  a path of length two carries `6` and `5`. Those pin down the `k = 0` convention — the one place
  where the two types have *different* list sizes — before it could cost anything inside an
  induction.
* The isomorphism exhibiting a path as a bridge of two shorter paths has four plausible
  orientations. The wrong pairing gives `29` where the truth is `32` at lengths `(2,2)`. Checking
  first turned a potentially long debugging session into a one-line decision.
* For the theta graphs of Theorem 2, the paper's figure gives a witness for `m = 2`. A search found
  `48` such witnesses, and from them a *uniform* family that works for every `m` — which is what a
  formalization needs and what a figure cannot supply.

None of these errors would have appeared as type errors. All of them would have appeared as a proof
that would not close, at the bottom of an induction, with no indication of which end was wrong.

# A scaffolding hypothesis of our own that was false

The one genuinely negative finding, and it is about this repository rather than about any paper.

To split Rubin's theorem into a structural half and a colouring half — so that the two could be
worked on independently — an auxiliary hypothesis was invented here. Applied to a graph `H`, it
offered four alternatives: `H` is a cycle, or it is $`\theta_{2,2,2m}`, or it contains an odd cycle,
or it contains a theta $`\theta_{a,b,c}` of some shape other than $`(2,2,\text{even})`. Each
disjunct names a configuration whose colouring behaviour is settled, so it looked like exactly the
right currency to buy the hard direction with.

It is false. The counterexample is $`K_{2,4}`, a graph the development already owned as the
Erdős–Rubin–Taylor block of {ref "notchoosable"}[the separation chapter]: six vertices, eight edges,
connected, minimum degree two, bipartite so no odd cycle, degree sequence `4,4,2,2,2,2` so neither a
cycle nor any $`\theta_{2,2,2m}` — and its only theta subgraph is the *good* $`\theta_{2,2,2}`,
because a theta needs two branch vertices of degree at least three and $`K_{2,4}` has only two such
vertices, joined by exactly four internally disjoint paths of length two. Yet $`K_{2,4}` is not
`2`-choosable. Every disjunct fails at once. The refutation is by brute force, and the hypothesis
has been deleted along with everything that took it.

Two things follow, and they are worth keeping apart.

*What went wrong is a three-arm restriction.* $`K_{2,4}` **is** a theta graph — two vertices joined
by internally disjoint paths — just not one with three arms. The right structural object is the
generalized theta of arbitrary arity, and $`K_{2,4}` is the four-arm one. A dichotomy strong enough
to finish Rubin's argument has to offer those, plus pairs of cycles meeting in at most one vertex.
{ref "twochoosable"}[The `2`-choosability chapter] tells the story in full, with the checks.

*This is a defect in our scaffolding and not an error in Kirov–Naimi.* Their proof of Theorem 2
cites Rubin's theorem rather than proving it, and therefore never asserts anything of the kind. The
distinction is not a courtesy: no claim is being made here about the correctness of the paper, in
which no error has been found.

# The surrounding literature

Two claims that are widely repeated did not survive checking.

**Counting list colorings does not require the chromatic polynomial.** The natural reading of the
literature suggests a dependency chain running through deletion–contraction, edge contraction, and
Whitney's broken-cycle theorem. Kirov–Naimi needs none of it. It needs the *number* of colorings,
never the polynomial in which that number is a coefficient or a value. Removing that layer removes
edge contraction — which Mathlib does not have — from the critical path entirely.

**Kostochka–Sidorenko does not require Dirac's theorem.** Lemma 1 plus induction along a simplicial
elimination ordering gives the chordal result directly. Dirac's theorem {citep dirac}[] is what
connects "has a simplicial elimination ordering" to "every long cycle has a chord"; it is a
convenience for recognizing chordal graphs, not a step in the argument.

# The state of the ground

At the Mathlib revision this development targets, there is no chromatic polynomial, no list coloring
or choosability, no DP-coloring, no chordality or perfect elimination orderings, and no Brooks or
Vizing. There is also, contrary to a claim we started from, no `Fintype` instance for the bundled
coloring type — which is what forced the design decision in the first chapter.

One gap turned into a small by-product. "A graph that is not `2`-colourable contains an odd cycle" —
the classical characterization of bipartite graphs — is an open `TODO` in Mathlib's
`Bipartite.lean`. Kirov and Naimi's proof of Theorem 2 opens with exactly that sentence, so it had
to be built here, and it is: the middle step, that an odd closed *walk* contains an odd *cycle*, is
proved by rotating the walk to a repeated vertex and cutting it there. It is textbook material and
no kind of contribution, but it is a piece of the standard library that this project happens to have
supplied.

More broadly, list coloring and choosability appear not to have been formalized in any major proof
assistant. The adjacent mechanized results are Gonthier's Four Color Theorem in Coq
{citep gonthier4ct}[], Bauer and Nipkow's Five Colour Theorem in Isabelle {citep bauerNipkow}[], and
a standalone Lean proof of Vizing's theorem {citep bhojaVizing}[] which is not part of Mathlib. So
the list color function has, as far as we can determine, not been formalized anywhere before.

# What is done, and what is not

Proved here: Lemmas 1 through 6; Kostochka–Sidorenko in its simplicial-elimination-ordering form;
Theorem 1 for every `n ≥ 3`; Theorem 2 given Rubin's theorem; and the building block of Section 5.

Theorem 1 is complete: **every cycle, every `n ≥ 2`**. Two things remain, of quite different kinds.

Before them, one observation about the `n = 2` case that is worth recording because it justifies the
paper's route. One might hope non-constant assignments simply give more colourings, so that the
constant case would settle everything and the forcing argument could be skipped. That is false:
exhaustively, 72 non-constant assignments on the 4-cycle and 720 on the 6-cycle achieve exactly the
same minimum of `2`. The paper itself notes as much — every even cycle has a minimizing 2-list
assignment that is not constant. The forcing argument is necessary, not merely the route the authors
happened to take.

That case also turned out to be the *only* point in Section 3 where the paper's freedom to choose
which edge to delete is load-bearing rather than a convenience. Everywhere else the fixed edge
sufficed; there, a rotation automorphism of the cycle had to be built to supply the same freedom.

**Rubin's theorem, and therefore the converse half of Theorem 2 unconditionally.** Rubin's
characterization of `2`-choosable graphs {citep erdosRubinTaylor}[] is a 1979 result that appears
not to have been machine-checked before. It is not treated as an external dependency here: it is a
named proposition {name ListColoring.RubinTheorem}`RubinTheorem` in the development, it is being
proved, and Theorem 2 takes it as its first explicit argument so that supplying a term makes Theorem
2 unconditional with no other edit anywhere.

How far that has got: the ⟸ direction is proved. So is the whole colouring content of the forward
direction — a theta graph is `2`-choosable exactly when its shape is $`(2,2,\text{even})`. What
remains is a structural statement about which subgraphs a connected graph of minimum degree at least
two must contain, which in the literature is a block or ear decomposition and which Mathlib does not
have. Every colouring-theoretic ingredient of Theorem 2 is proved outright, and so is its entire ⟸
direction, with no hypothesis and not even connectivity.

**Section 5's full construction** — `n²` copies of `K_{n,nⁿ}` beneath a complete bipartite graph,
with the second parameter chosen by a counting argument — is a substantial project of its own and
has not been attempted. What is formalized is its building block, which already exhibits the
colourable-but-not-choosable separation.
