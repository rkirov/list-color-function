import VersoManual
import Book.Papers
import Cacti

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Beyond the Paper: Cacti" =>

%%%
tag := "cacti"
%%%

Source: the [`Cacti/`](https://github.com/rkirov/list-color-function/tree/main/Cacti) library —
`Defs.lean` for the definition, `Induction.lean` and `Three.lean` for the two invariants,
`BalancedCore.lean` for odd cycles, `RefTensor.lean` through `LargeBranch.lean` for even ones,
`GMFinal.lean` and `Statements.lean` for the assembly, and `Examples.lean` for the concrete
cacti below.

Everything up to here has been Kirov and Naimi's, or Rubin's. This chapter is not: it is a result
of the 2026 research collaboration on this repository, proved in the course of formalizing their
paper rather than found in it, and the only reason it belongs in a companion to their paper is that
it answers, for one infinite family, exactly the question they left open at `n = 2` and never asked
above it. The source of record for the mathematics is `FINAL_CACTI_ECC_HANDOFF.md` in the
repository's research notes; what follows is a guide to the formalized version, which differs from
the notes in three places recorded at the end of the chapter.

Their Theorem 2 settles which graphs are enumeratively chromatic-choosable at `2`
({ref "twoecc"}[the classification chapter]). Above `2` almost nothing is known in general. For
*cacti* — connected graphs in which any two cycles that share an edge are the same cycle — the
answer turns out to be complete and short to state: above `2` the property always holds, at `2` it
is a structural dichotomy, and there is nothing else to say.

The proof is longer than anything in the paper, and its difficulty is concentrated in one place
that no amount of bookkeeping removes. This chapter is a guide to it.

# What a cactus is

A cactus is connected, and any two of its cycles that share an edge coincide as edge sets. That is
the whole definition:

```lean
open SimpleGraph ListColoring in
example {V : Type} [DecidableEq V] (G : SimpleGraph V) :
    IsCactus G ↔ (G.Connected ∧
      ∀ ⦃u v : V⦄ (p : G.Walk u u) (q : G.Walk v v), p.IsCycle → q.IsCycle →
        ∀ e ∈ p.edges, e ∈ q.edges → p.edges.toFinset = q.edges.toFinset) := Iff.rfl
```

Equivalently: every edge lies in at most one cycle. Equivalently again, and this is the picture to
keep: every block is a single edge or a single cycle, and the blocks hang off one another at cut
vertices like beads. Trees are cacti; a single cycle is a cactus; two triangles glued at a vertex
is a cactus; $`K_4` is not, and neither is any theta graph.

The phrase to read carefully is *coincide as edge sets*. A cycle in Lean is a walk, and one cycle
has many walks — different basepoints, and both directions round. Had the definition asked for the
two walks to be equal it would have been false for every graph containing a cycle at all, cacti
would have collapsed to forests, and the classification below would have been a statement about
trees. Edge-set equality is how one says "the same cycle". Nothing is lost by passing to a finite
set, because a cycle's edge list is duplicate-free.

That reading is load-bearing enough that the development pins it down on three graphs rather than
arguing it. $`K_4` is refused, a triangle is accepted, and — the case that matters — the *bowtie*,
two triangles glued at a vertex, is accepted while failing to have at most one cycle:

```lean
open SimpleGraph ListColoring ListColoring.CactusExamples in
example : IsCactus bow ∧ ¬ HasAtMostOneCycle bow ∧ bow.ECCAt 3 :=
  ⟨bow_isCactus, bow_not_hasAtMostOneCycle, bow_eccAt_three⟩
```

The bowtie is the smallest graph that separates the two hypotheses in the theorem below, so its
being a cactus is what keeps that theorem from being a statement about unicyclic graphs. Its proof
is by deciding every closed walk of length at most five: a cycle's support is duplicate-free, so in
a five-vertex graph no cycle is longer, and each one that exists is one of the two triangles.

# The classification

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsCactus G) : G.ECC ↔ HasAtMostOneCycle G ∨ SimpleGraph.HasOddCycle G :=
  isCactus_ecc_iff G hG
```

`HasAtMostOneCycle` says any two cycles coincide — so, with connectivity, the graph is a tree or is
unicyclic. `SimpleGraph.HasOddCycle` is the same predicate Theorem 2 uses: a subgraph copy of
Mathlib's `cycleGraph n` for odd `n ≥ 3`.

The whole content of the iff sits at `2`, because above `2` the left side is unconditional:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 3 ≤ k) (hG : IsCactus G) : G.ECCAt k := isCactus_ecc_of_three_le G hk hG
```

and at `2` it is the dichotomy:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsCactus G) :
    G.ECCAt 2 ↔ HasAtMostOneCycle G ∨ SimpleGraph.HasOddCycle G := isCactus_ecc_two_iff G hG
```

The `2` case is the one that routes through the paper. An odd cycle makes a graph not
`2`-colourable, so both counts are zero and the property holds for a reason that has nothing to do
with counting.
In the other direction, a cactus with two even cycles and no odd one has none of the four cores
Theorem 2 allows: `K₂,₃` cannot sit inside a cactus at all, and a core that is a single vertex or a
single cycle forces at most one cycle. The `k = 2` half is therefore Theorem 2, with Rubin behind
it, plus an analysis of which cores a cactus can have; it was the first of the three cases to be
finished. Everything below is about `k ≥ 3`.

# Rooted profiles: what an induction can carry

The obstacle in all of this is that "the count is at least the uniform count" is too weak to induct
on. Cut a cactus at a cut vertex and you learn nothing about how the two halves interact, because
the halves interact through the *colour of the cut vertex*, not through their totals.

So the object that gets carried is finer. Fix a root `r`. The *rooted profile* of an assignment at
`r` is the function sending each colour `c` in the root's list to the number of colourings that
give `r` colour `c`. The count is its sum:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) (r : V) : G.col L = ∑ c ∈ L r, rootedCol G L r c :=
  col_eq_sum_rootedCol G L r
```

Write $`A` for the corresponding number in the *uniform* problem — the profile of the constant
assignment, which is the same for every colour. What has to be proved is `k·A ≤ ∑_c x_c` where
`x_c` is the profile of the arbitrary assignment. An induction that carried only that inequality
would be stuck immediately, because the sum is exactly what a cut vertex fails to respect. The
induction therefore carries a *pointwise* statement about the profile, strong enough to survive a
cut, and converts it to the sum only at the very end, at the root, by an inequality of the
arithmetic-geometric type.

There are two such statements, one for each side of the `k = 3` boundary, and the difference
between them is the mathematical content of the whole development.

# Above three: the pair bound

For `k ≥ 4` the invariant is that any *two distinct* entries of the profile have product at least
$`A^2`:

```lean
open SimpleGraph ListColoring in
example (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hG : IsCactus G) (L : ListAssignment V) (hL : IsNListAssignment L k)
    (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, ∀ c ∈ L v, ∀ d ∈ L v, c ≠ d → (W v) ^ 2 ≤ w v c * w v d)
    (r : V) {c d : ℕ} (hc : c ∈ L r) (hd : d ∈ L r) (hcd : c ≠ d) :
    (rootedCol G (constList V k) r 0 * ∏ v, W v) ^ 2
      ≤ rootedWcol G L w r c * rootedWcol G L w r d :=
  cactus_pair_bound (Fintype.card V) V G rfl hk hG L hL w W hdom r c hc d hd hcd
```

Ignore the weights `w` and `W` for a moment — set them to `1` — and the statement reads
$`A^2 \le x_c \cdot x_d` for every pair of distinct colours at the root. That is exactly the
hypothesis of an elementary lemma which delivers the sum:

```lean
open ListColoring in
example {k : ℕ} {A : ℝ} {x : Fin k → ℝ} (hk : 2 ≤ k) (hA : 0 ≤ A) (hx : ∀ c, 0 ≤ x c)
    (h : PairBound A x) : (k : ℝ) * A ≤ ∑ c, x c :=
  PairBound.card_mul_le_sum hk hA hx h
```

A pair bound is a strong thing to carry, and it survives everything the induction does to it: a
cut vertex, a leaf, a cycle block. The cycle block is the only step with real content, and it comes
from the transfer matrix — see below.

# Why the pair bound dies at three

At `k = 3` the pair bound is simply false, and it is worth seeing why, because the reason is not
an accident of the proof.

The induction does not work with the graph as given; it *peels*. When a block is removed, its
effect on the rest is absorbed into a weight `w v c` at the attachment vertex — the number of ways
the removed part can be completed given that `v` took colour `c`. The invariant then has to be
carried for weighted counts rather than plain ones, which is what the `w` and `W` above are, and
the peeling step has to pay for itself: absorbing a block costs a factor, and the bound has to have
enough slack to cover it.

At list size `k` that slack is $`k - 3`. At `k \ge 4` it is at least one and the peeling goes
through. At `k = 3` it is exactly zero. There is nothing to spend, and the pair bound — which is
strictly stronger than what is actually true at three — is the first casualty.

What survives is the geometric mean. Instead of every pair, the invariant constrains the *product
of the whole profile*:

```lean
open SimpleGraph ListColoring in
example (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsCactus G) (L : ListAssignment V) (hL : IsNListAssignment L 3)
    (w : V → ℕ → ℕ) (W : V → ℕ) (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) (r : V) :
    (rootedCol G (constList V 3) r 0 * ∏ v, W v) ^ 3 ≤ ∏ c ∈ L r, rootedWcol G L w r c :=
  cactus_gm_bound (Fintype.card V) V G rfl hG L hL w W hdom r
```

and the terminal step asks only for that product, not for the pairs:

```lean
open ListColoring in
example {k : ℕ} {A : ℝ} {x : Fin k → ℝ} (hk : 0 < k) (hA : 0 ≤ A) (hx : ∀ c, 0 ≤ x c)
    (h : A ^ k ≤ ∏ c, x c) : (k : ℝ) * A ≤ ∑ c, x c :=
  card_mul_le_sum_of_pow_le_prod hk hA hx h
```

The hypothesis on the weights changes in the same way: `(W v)² ≤ w v c · w v d` for every pair
becomes `(W v)³ ≤ ∏_c w v c` over the vertex's list. A weight system satisfying that is called
*GM-dominant*, and the whole `k = 3` route is the statement that GM dominance propagates.

This is the substance of the difference between the two halves. The `k ≥ 4` half is a real proof
with a comfortable margin; the `k = 3` half is the same architecture with every margin removed, and
the places where the margin was doing work have to be replaced by exact arguments.

# The pendant edge, and how tight three is

The smallest instance of the peeling makes the point. Take a vertex with a pendant neighbour whose
three colours carry weights `a`, `b`, `c`. Absorbing the pendant replaces them by the three
complementary sums `b+c`, `c+a`, `a+b`. GM dominance survives that step precisely because

$$`(a+b)(b+c)(c+a) \ge 8abc,`

and `8` is the cube of the pendant factor `k - 1 = 2`:

```lean
open ListColoring in
example {s : Finset ℕ} (hs : s.card = 3) (w : ℕ → ℕ) :
    8 * ∏ e ∈ s, w e ≤ ∏ e ∈ s, ∑ d ∈ s.erase e, w d := gm_bridge_prod hs w
```

Equality holds exactly when `a = b = c`. Every step of the `k = 3` argument is like this: true, with
equality at the uniform configuration, and with no room anywhere. It is worth recording the
numerical fact that makes this concrete. For a cycle, the unweighted form of the invariant —
$`A^3 \le \prod_c x_c` — has minimum ratio exactly `1.0000` over the cycles of length four through
seven, attained precisely at the constant assignment. The bound is not merely tight in the limit;
it is *achieved*. Nothing in the argument may throw anything away.

# The skeleton of the induction

With the invariant fixed, the induction itself is short to describe. A cactus with at least three
vertices either has a cut vertex or is a single cycle. The development produces exactly that
dichotomy, in the form the induction needs: either a splitting of the vertex set into two induced
cacti meeting at one vertex, each strictly smaller, or a cyclic indexing of the whole graph.

* *One vertex.* The invariant is the weight hypothesis at the root, and nothing happens.
* *Two vertices — a single edge.* The pendant computation above, in its base form.
* *A cut vertex.* Absorb one side into a weight at the cut vertex, apply the induction hypothesis
  to that side to check the absorbed weight is still dominant, then apply it to the other side. The
  two uses are what makes the recursion a strong induction on the number of vertices.
* *A cycle.* This is the only case with content.

Everything in the first three cases is bookkeeping that either side of the boundary handles the
same way, modulo the change of invariant. The classification is therefore, in the end, a theorem
about cycles carrying weights.

# Cycle blocks above three: the transfer matrix

For `k ≥ 4` a cycle is handled by the classical device. Colourings of a cycle with prescribed lists
are counted by a product of transfer matrices, one per edge, closed up by a permutation; the uniform
case has the closed form

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {m k : ℕ} (hk : 1 ≤ k) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1)) :
    rootedCol G (constList V k) (ix 0) 0 = uniformA k (m + 1) :=
  rootedCol_constList_cycle hk ix hadj
```

where `uniformA k n = (k-1) · beta k (n-1)` and `beta` is the usual two-term recursion behind the
chromatic polynomial of a cycle ({ref "cycles"}[the cycles chapter]). The pair bound on a cycle
then reduces to a finite case analysis on how the closing permutation acts on the two root colours
being compared — whether each is fixed, moved, or outside the domain — and each case is an
inequality between products of `alpha` and `beta`. This is UM-106 to UM-108 in the research notes,
and it is the comfortable half.

# Odd cycles at three: the balanced core

At `k = 3` the transfer-matrix route no longer closes, and the two parities of the cycle part
company. Odd cycles have a genuinely pretty argument.

The claim to prove is that the profile of a cycle has product at least $`A^3`. For an odd cycle one
can do better than estimate it: one can exhibit, inside the set of all colourings, a subfamily that
hits every vertex-colour pair exactly `A` times.

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {m : ℕ} (hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (hpar : Odd (m + 1)) (L : ListAssignment V) (hL : IsNListAssignment L 3) :
    ∃ S ⊆ G.colorings L, ∀ v, ∀ c ∈ L v,
      (S.filter (fun f => f v = c)).card = rootedCol G (constList V 3) (ix 0) 0 :=
  exists_balanced_core_odd hm ix hadj hpar L hL
```

Such an `S` is a *balanced core*. Given one, the profile of the true assignment dominates the
perfectly flat profile of `S` entry by entry, and the product bound is immediate. The construction
is a covering argument: colourings are built by choosing, for each vertex, which of the three
colours is skipped, and the odd length is exactly what lets the resulting alternating pattern close
up when it returns to the start. On an even cycle the same construction fails to close, and no
balanced core exists.

# Even cycles at three: where the work is

This is the case that took the longest and is the reason the library has the shape it has.

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {m : ℕ} (hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (hpar : Even (m + 1)) (L : ListAssignment V) (hL : IsNListAssignment L 3)
    (w : V → ℕ → ℕ) (W : V → ℕ) (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) :
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3
      ≤ ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c :=
  cycle_gm_bound_even hm ix hadj hpar L hL w W hdom
```

Three ingredients make it go.

*A word model.* A weighted colouring of the cycle is recoded as a word: the lists are enumerated,
so a colouring becomes a function from positions to $`\{0,1,2\}` and its weight becomes a product
along the word. The graph disappears and what is left is a sum over words with a constraint at each
step and one closing constraint where the cycle returns to its start.

*Holonomy.* Walking round the cycle carries the identification of the three colours with it, and
when the walk returns to the root the identification it comes back with need not be the one it left
with. The discrepancy is a permutation $`\sigma` of three elements — the *holonomy* — and it is the
only thing about the enumeration the argument depends on. There are three cases up to conjugacy:
the identity, a transposition, and a three-cycle. The residual tables in the development are the
book-keeping of these three, and one of the corrections below is that the four rows the source notes
tabulate are three instances of a single law.

*A reference tensor, compared by weighted AM–GM.* The bound is proved by comparing the true
weighted sum against an explicit reference distribution of integer masses over words, chosen to have
uniform one-coordinate marginals and prescribed pair marginals. The comparison is a weighted
arithmetic-geometric mean inequality with integral masses, stated and proved over $`\mathbb{N}` so
that no real analysis enters the development:

```lean
open ListColoring in
example {α : Type} (T : Finset α) (X U : α → ℕ) {P : ℕ} (hP : 0 < P)
    (hsum : ∑ a ∈ T, U a = P) (hU : ∀ a ∈ T, 0 < U a) :
    P ^ P * ∏ a ∈ T, X a ^ U a ≤ (∑ a ∈ T, X a) ^ P * ∏ a ∈ T, U a ^ U a :=
  weighted_amgm_masses T X U hP hsum hU
```

Reading that inequality in the direction it is used: the reference masses `U` contribute a
denominator $`\prod U^U`, an *entropy*; the path along the cycle contributes a *budget*; and the
case closes exactly when the budget exceeds the entropy. Everything else in these files is the
computation of those two numbers.

The even case splits into three, by the length of the cycle:

* *The four-cycle.* One terminal pair forces the holonomy to be the identity, so no tensor argument
  is needed at all; the four-cycle is a direct computation.
* *The six-cycle.* Here the tensor argument is unavoidable and the tables are explicit: five
  27-entry mass tables, one per non-identity holonomy, each of total mass `66`, with all nine
  one-coordinate marginals equal to `22` — which is the six-cycle's own uniform normalizer — and all
  three pair marginals equal to the base composed with the holonomy. The budget available is
  $`2^{50} \cdot 3^{30}` and the entropy denominators are $`2^{58} \cdot 3^{24}` at a transposition
  and $`2^{68} \cdot 3^{18}` at a three-cycle. The margins are `1.51` and `1.02` bits. Every one of
  these numbers is checked at build time rather than asserted.
* *Every longer cycle.* Beyond six, an entropy induction takes over: a scalar step shows the
  per-vertex cost of extending the cycle grows more slowly than the budget does, so once the margin
  is positive it stays positive, and the base case for the induction is the six-cycle.

The reason the tables cannot be avoided at six, and the reason a single uniform argument does not
cover the whole even range, is the same in both directions: the margin at six is around one bit.
The general argument is provably short there — its margin at six is negative — and above six it
carries the case on its own, so the tables are needed exactly once.

# What mechanization corrected

Three claims of the source notes did not survive formalization. None of them changes the theorem;
all three change what one should believe about the argument, which is the point of doing this at
all ({ref "findings"}[the findings chapter] records the same phenomenon for the paper itself).

*An alleged gap that was not one.* The notes report the budget going negative in the non-identity
case at the two smallest lengths, and treat this as a hole. Recomputing the margins shows the
negative values belong to lengths the argument explicitly excludes by name — the general chain is
stated for the longer cycles, and the short ones have their own treatment. The margins at the
lengths the chain does cover are positive and growing.

*A constant that is not what the notes say.* The six-cycle section quotes a strict factor of the
form $`2^{108}/(5^{10} \cdot 11^{22})`, and the machinery of the path cone does not deliver it. What
it delivers is $`(729/256)^5 = 3^{30}/2^{40}`, which is `1.12` bits weaker. The formalized six-cycle
argument therefore runs on the weaker constant, with the margins quoted above; the notes' own
arithmetic is a true statement about a factor the proof does not have. Two integer comparisons
recording the notes' version are kept in the development, marked as such, because a reader of the
notes will look for them.

*Four rows that are three.* The residual table for the closing edge lists four cases. They are three
instances of one law, uniform in the holonomy, and reading them as four suggests a case analysis
that is not there.

The first of these is the one worth pausing on. A reported hole in a proof is exactly the kind of
claim that is expensive to check by hand and cheap to check mechanically, and getting it wrong in
the pessimistic direction costs as much work as getting it wrong in the optimistic one.

# What is claimed

The development proves five statements about cacti; the challenge file claims three of them
({ref "readingchallenge"}[the reading chapter]). The `k = 3` and `k ≥ 4` halves are proved
separately, because as this chapter has laboured they are genuinely different arguments, but only
their union is claimed. A statement surface should state theorems, not case analyses.

Everything in this chapter depends on `propext`, `Classical.choice` and `Quot.sound`, and on nothing
else — the same standard as the rest of the development, and enforced the same way.
