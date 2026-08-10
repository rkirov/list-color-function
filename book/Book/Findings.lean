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
merely confirmed. *Nothing below is an error in Kirov and Naimi's paper*: none was found, across the
whole formalization. The findings are of five kinds: hypotheses of theirs that turned out to be
load-bearing in a specific and identifiable way, hypotheses that turned out to be unnecessary,
hypotheses of *ours* that turned out to be false, three points in Rubin's forty-year-old exposition
that do not survive as printed, and pieces of received wisdom about the surrounding literature that
did not survive checking.

# Hypotheses that are exactly load-bearing

*"A path of length at least one."* The paper's definition of an `(n,n-1)`-list assignment carries
this restriction, and it is easy to read past. Part (c) of Lemma 3 is precisely the claim that needs
it. At length zero the two terminal vertices coincide, every `(n,n-1)`-assignment is therefore
minimizing, and every such assignment is type A — while zero is even, so (c) would demand type B.
The development contains a machine-checked witness. What mechanization contributes here is not a
correction but a sharpening: it identifies the unique claim that fails and produces the
counterexample.

*`n ≥ 3` in part (c), but not in part (b).* Part (b) holds with no hypothesis on `n` at all: at
`n = 2` the bound `min(A_k, B_k) ≤ col` is true because the minimum is zero. The `n ≥ 3` in the
lemma statement is needed only by (c), where it is what guarantees that both sides of a cut path
have all lists of size at least two, so that the strictness in the swap lemma is available.

*The tightness of Case 2 of Theorem 1.* The even-cycle case admits an obvious-looking argument —
one fibre contributes `A + 1`, the rest contribute `B` — which yields `nA - n + 2` and therefore
fails for every `n ≥ 3`. The paper's argument is genuinely stronger and has no slack: `B + (A+1) +
(n-2)A = nA` on the nose. This is the kind of thing a careful reader can miss, because the printed
proof does not advertise that the weaker bookkeeping is insufficient.

# Hypotheses that are not needed

*Equation (1) of Lemma 2 does not need `c₂ ∈ L(v₂)`.* The counting identity uses only that `c₁` is
available at `v₁`, unavailable at `v₂`, and that `c₂` is unavailable at `v₁`. The hypothesis
`c₂ ∈ L(v₂)` is what makes the swap decrease the nesting defect, and so is needed for termination —
but it plays no role in the identity itself.

*The extension count for cones needs no clique hypothesis.* In Lemma 1 the identity
`col(coneOn G K, M) = ∑ |M(none) \ f(K)|` and the resulting inequality are true for an arbitrary
vertex set `K`. The clique hypothesis is needed only to collapse the sum to an exact product in the
uniform case.

*No rotation automorphism is needed for Theorem 1.* The paper deletes an edge chosen so that its
endpoints have different lists, which appears to require moving that edge into a canonical position.
It does not: in the deficient case the shape of the assignment already forces the two neighbors of
the distinguished vertex to carry different lists.

*Minimizers exist without a finite-palette argument.* Colors range over `ℕ`, so the space of
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

# Scaffolding hypotheses of our own that were false

The genuinely negative findings, and they are about this repository rather than about any paper.

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

*The repair was false too.* Replacing three-arm thetas by generalized ones of arbitrary arity, and
adding "contains two cycles meeting in at most one vertex", gives a statement that $`K_{3,3}` minus
an edge refutes on six vertices: four of its vertices have degree at least three, whereas a
generalized theta has exactly two, and its girth is four, so two cycles meeting in at most one
vertex would need seven. An exhaustive sweep of the `129,073` bipartite `2`-connected non-cycle
graphs on at most nine vertices finds `4,162` satisfying neither branch. A third version, adding a
dumbbell branch, closes all `129,073` — but only empirically; it was never proved, and it turned out
not to be needed.

Two smaller claims of ours went the same way, and are recorded because the shape of the error is the
same each time. *A connected graph of minimum degree at least two that is not a cycle contains a
theta subgraph* — false: the *bowtie*, two triangles sharing a vertex, contains no theta at all. And
*two cycles meeting in at most one vertex are not `2`-choosable* — false as stated, because two
*disjoint* even cycles are `2`-choosable, colourings of a disjoint union being independent. The
connecting path is not a formalization artefact; it is what connectivity actually supplies, and it
is a hypothesis of the theorem that ended up being proved.

Four things follow, and they are worth keeping apart.

*What went wrong the first time is a three-arm restriction.* $`K_{2,4}` *is* a theta graph — two
vertices joined by internally disjoint paths — just not one with three arms. The right object is the
generalized theta of arbitrary arity, and $`K_{2,4}` is the four-arm one.

*What went wrong the second time is `contains` versus `is`.* Under a *contains* reading
$`K_{3,3}-e` refutes nothing, since it contains both $`\theta_{1,3,3}` and $`\theta_{2,2,2}` — which
is exactly why containment is the wrong predicate. A *good* theta is `2`-choosable, so exhibiting a
theta subgraph implies nothing at all; what matters is containing a *bad* one. Neither "contains"
and "is", nor "a theta" and "a bad theta", are interchangeable here, and both substitutions were
made.

*These are defects in our scaffolding and not errors in Kirov–Naimi.* Their proof of Theorem 2
cites Rubin's theorem rather than proving it, and therefore never asserts anything of the kind. The
distinction is not a courtesy: no claim is being made here about the correctness of the paper, in
which no error has been found — zero, across the whole formalization. Every refuted claim in this
project has been one of ours.

*And in the end no such statement was used.* Rubin's own argument — a shortest cycle, two shortest
connecting paths, and a case analysis — needs no structural dichotomy, no ear decomposition, no
Menger and no `2`-connectivity. The detour left two lemmas behind that the real proof does use: the
classification of generalized thetas at arbitrary arity, forced by $`K_{2,4}`, and the dumbbell,
forced by $`K_{3,3}-e`. {ref "twochoosable"}[The `2`-choosability chapter] tells the whole story,
with the checks.

# Three corrections to Rubin's published argument

A separate finding, and the only one in this book about someone else's writing. Rubin's proof
{citep erdosRubinTaylor}[] is three pages long and dates from 1979. Running his procedure
exhaustively over all `316,460` connected bipartite non-cycle graphs of minimum degree at least two
on at most eight vertices — every shortest cycle, every shortest admissible connecting path — turned
up three points that do not survive as printed:

* cases (i) and (ii) of his six cannot occur at all, being already excluded by his own step 3;
* case (v) is correct only because the first connecting path is *shortest*, a fact the argument uses
  without saying so — with a non-minimal path the claim is false, and arms `2, 2, 4, 2` are the
  counterexample;
* step 5's "the shortest cycle is a four-cycle" needs the minimality of that cycle, in a sub-case
  where the printed argument does not invoke it.

Each is a gap in the exposition rather than in the result: the theorem is true, and is now checked.
These are *not* findings about Kirov and Naimi, who cite Rubin's theorem rather than proving it.
{ref "twochoosable"}[The `2`-choosability chapter] states all three precisely.

# The surrounding literature

Two claims that are widely repeated did not survive checking.

*Counting list colorings does not require the chromatic polynomial.* The natural reading of the
literature suggests a dependency chain running through deletion–contraction, edge contraction, and
Whitney's broken-cycle theorem. Kirov–Naimi needs none of it. It needs the *number* of colorings,
never the polynomial in which that number is a coefficient or a value. Removing that layer removes
edge contraction — which Mathlib does not have — from the critical path entirely.

*Kostochka–Sidorenko does not require Dirac's theorem.* Lemma 1 plus induction along a simplicial
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
Theorem 1 for every cycle and every `n ≥ 2`; Theorem 2 with no hypothesis but connectivity; Rubin's
theorem; and the building block of Section 5.

One observation about Theorem 1's `n = 2` case is worth recording, because it justifies the paper's
route. One might hope non-constant assignments simply give more colourings, so that the constant
case would settle everything and the forcing argument could be skipped. That is false:
exhaustively, 72 non-constant assignments on the 4-cycle and 720 on the 6-cycle achieve exactly the
same minimum of `2`. The paper itself notes as much — every even cycle has a minimizing 2-list
assignment that is not constant. The forcing argument is necessary, not merely the route the authors
happened to take.

That case also turned out to be the *only* point in Section 3 where the paper's freedom to choose
which edge to delete is load-bearing rather than a convenience. Everywhere else the fixed edge
sufficed; there, a rotation automorphism of the cycle had to be built to supply the same freedom.

*Rubin's theorem, and therefore Theorem 2 unconditionally.* Rubin's characterization of
`2`-choosable graphs {citep erdosRubinTaylor}[] is a 1979 result that appears not to have been
machine-checked before. It was not treated as an external dependency: it was a named proposition
{name ListColoring.RubinTheorem}`RubinTheorem` in the development, taken as the first explicit
argument of Theorem 2, so that supplying a term would make Theorem 2 unconditional with no other
edit anywhere. That term now exists — {name ListColoring.rubinTheorem}`rubinTheorem` — and
{name ListColoring.ecc_two_iff}`ecc_two_iff` is Kirov and Naimi's Theorem 2 with no hypothesis but
connectivity.

None of that mathematics is new. What is new, as far as we can determine, is only that a machine has
now checked a 1980 theorem, and — much more modestly — the three corrections to its exposition
recorded above.

One thing remains, and it is of a different kind. *Section 5's full construction* — `n²` copies of
`K_{n,nⁿ}` beneath a complete bipartite graph, with the second parameter chosen by a counting
argument — is a substantial project of its own and has not been attempted. What is formalized is its
building block, which already exhibits the colourable-but-not-choosable separation.

Beyond the paper, the open question it left behind is still open: whether agreement of $`P_\ell` and
$`P` at one value of `n` forces agreement at `n + 1`. {ref "twoecc"}[The Theorem 2 chapter] says
what is known about the case $`\chi(G) = 2`.
