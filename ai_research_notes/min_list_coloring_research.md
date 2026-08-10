# Minimum list-color counts: monotonicity, spectra, and class problems

Date: 2026-08-10

This note deliberately works in ordinary graph-theoretic language.  It separates elementary
arguments proved here, deductions from published theorems, and conjectural directions.  No claim is
made here to settle the general monotonicity problem: it is still presented as open in the recent
literature.

## 1. Terminology and the real question

For a finite graph `G`, write

\[
    m_G(k):=\min_L P(G,L), \qquad u_G(k):=P(G,k),
\]

where the minimum is over all assignments of lists of size `k`, and where `u_G(k)` is the number of
colorings from one common `k`-element palette.  Thus `m_G` is the usual list color function
`P_ell(G,k)`, while `u_G` is the chromatic polynomial evaluated at `k`.

Some terminology that avoids "monophilic":

* `G` is **uniform-minimal at `k`** if `m_G(k)=u_G(k)`.
* The **uniform-minimality spectrum** is
  \[
      A(G):=\{k\geq\chi(G):m_G(k)=u_G(k)\}.
  \]
* The **defect spectrum** is
  \[
      D(G):=\{k\geq\chi(G):m_G(k)<u_G(k)\}.
  \]

The restriction `k >= chi(G)` is essential.  Below the chromatic number both sides vanish, so
agreement is vacuous.  For example, a bipartite graph which is not uniform-minimal at `2` is still
vacuously uniform-minimal at `1`.

The literature uses

\[
\nu(G)=\min A(G),\qquad
\tau(G)=\min\{t\geq\chi(G):[t,\infty)\subseteq A(G)\}.
\]

I would call these the **first-agreement index** and **stabilization index** in prose.  Calling either
one a "list-coloring number" risks confusion with the choice number.

The proposed monotonicity theorem is

> **Uniform-minimality conjecture.**  If `k >= chi(G)` and `G` is uniform-minimal at `k`, then it is
> uniform-minimal at `k+1`.

This has several exactly equivalent forms:

1. `A(G)` is an upper set in the colorable range;
2. `D(G)` is an initial interval in the colorable range;
3. `nu(G)=tau(G)` for every finite graph.

The last formulation is the existing open question of Kirov--Naimi.  Both the 2025 enumerative
chromatic-choosability paper and the 2026 theta-graph paper still state it as open.

There is nevertheless a substantial positive result at the first nontrivial value: uniform
minimality at `2`, for a `2`-colorable graph, forces uniform minimality at every later value.  A proof
appears in Section 4.

## 2. The coarse shape of every spectrum

Three intervals are already understood.

* If `k < chi(G)`, then `m_G(k)=u_G(k)=0`; this is why these values are excluded from `A(G)`.
* If `chi(G) <= k < chi_ell(G)`, then `m_G(k)=0<u_G(k)`.
* Donner's eventual-agreement theorem makes `D(G)` finite.  The stronger bound of Dong--Zhang says,
  for a graph with `e` edges, that `m_G(k)=u_G(k)` for `k >= e-1` (with the small-edge cases harmless).

Consequently, all genuinely unknown behavior lies in the finite window

\[
       \chi_\ell(G)\leq k<\tau(G).
\]

The monotonicity conjecture says that this window cannot contain a pattern such as
"agreement, then disagreement, then eventual agreement."

## 3. Two exact reduction identities

These are useful both for proofs and for narrowing any counterexample search.

### Proposition 3.1: disjoint unions

For every `k`,

\[
  m_{G\sqcup H}(k)=m_G(k)m_H(k),\qquad
  u_{G\sqcup H}(k)=u_G(k)u_H(k).
\]

**Proof.**  A list assignment on a disjoint union is exactly a pair of list assignments, one on each
component.  A coloring is exactly a pair of colorings, so its count is the product of the two counts.
The two list assignments can be minimized independently.  The uniform formula is the same product
argument.  `square`

If `k >= max(chi(G),chi(H))`, both uniform factors are positive and each minimum is at most its
uniform value.  It follows that

\[
  G\sqcup H\text{ is uniform-minimal at }k
  \quad\Longleftrightarrow\quad
  G\text{ and }H\text{ are both uniform-minimal at }k.
\]

Hence, in the colorable range,

\[
  A(G\sqcup H)=A(G)\cap A(H),\qquad
  D(G\sqcup H)=D(G)\cup D(H),qquad
  \tau(G\sqcup H)=\max\{\tau(G),\tau(H)\}.
\]

In particular a counterexample to monotonicity has a connected counterexample among its components.
Notice that no equally simple formula for `nu` follows unless monotonicity is already known: the
first point in an intersection need not be the maximum of the first points.

### Proposition 3.2: adjoining a leaf

Let `G+z` be obtained by adjoining a new leaf `z` to a vertex of `G`.  For `k >= 1`,

\[
  m_{G+z}(k)=(k-1)m_G(k),\qquad
  u_{G+z}(k)=(k-1)u_G(k).
\]

**Proof.**  For the lower bound, restrict any `k`-assignment on `G+z` to `G`.  Every coloring of `G`
has at least `k-1` extensions to `z`, since the color on its neighbor forbids at most one member of
`L(z)`.  Thus every assignment has at least `(k-1)m_G(k)` colorings.

For the upper bound, take a minimizing assignment on `G` and give `z` the same list as its neighbor.
Every coloring then has exactly `k-1` extensions.  The uniform identity is the familiar leaf formula
for the chromatic polynomial.  `square`

For `k >= 2`, adjoining or deleting leaves preserves the entire agreement/defect spectrum.  Thus a
minimal connected counterexample can be assumed to have minimum degree at least two, after passing
to its `2`-core.

## 4. A complete result at two colors

The following gives both a genuine monotonicity theorem and a complete spectrum classification in a
natural graph class.

### Theorem 4.1: connected `2`-choosable graphs

Let `G` be a connected `2`-choosable graph.  Repeatedly delete leaves to obtain its core.  Then its
first-agreement and stabilization indices are as follows.

| Core/type | `nu(G)` | `tau(G)` |
|---|---:|---:|
| one isolated vertex | 1 | 1 |
| a nontrivial tree, an even cycle, or `K_{2,3}` | 2 | 2 |
| `Theta(2,2,2r)`, `r >= 2` | 3 | 3 |

Here the tree row includes graphs whose core is one vertex but which have at least one edge, and in
the other rows arbitrary trees may be attached to the displayed core.

**Proof from known theorems.**  Rubin's classification says that the core of a connected
`2`-choosable graph is a vertex, an even cycle, or `Theta(2,2,2r)`.  Leaf deletion does not change the
spectrum by Proposition 3.2.

Trees and cycles are uniform-minimal at every colorable list size.  The case `r=1` is `K_{2,3}`, also
uniform-minimal for every `k >= 2`.  If `r >= 2`, the list assignment in Kirov--Naimi gives exactly
one `2`-list-coloring while the common two-element palette gives two; hence agreement fails at `2`.
Allred--Mudrock prove that these same graphs are uniform-minimal for every `k >= 3`.  This proves the
table.  `square`

### Corollary 4.2: monotonicity starts correctly

If `G` is `2`-colorable and `m_G(2)=u_G(2)`, then

\[
             m_G(k)=u_G(k)\qquad\text{for every }k\geq2.
\]

**Proof.**  Since `u_G(2)>0`, equality implies `m_G(2)>0`, so `G` is `2`-choosable.  Apply Theorem
4.1 to every connected component.  The only `2`-choosable core whose spectrum starts at `3` is
`Theta(2,2,2r)` with `r >= 2`, and equality at `2` excludes it.  Every remaining component agrees at
all `k >= 2`; Proposition 3.1 recombines the components.  `square`

This proves considerably more than the single implication `2 -> 3`.  It also suggests that exact
spectra, rather than just equality at the chromatic number, are the right class-level target.

## 5. Random deletion and the exact missing inequality

There is a useful monotonicity theorem for a normalized quantity, but it does not by itself settle
uniform-minimality.

Let `n=|V(G)|`, let `s>k`, and start with an `s`-assignment `L`.  Independently choose a uniformly
random `k`-subset `L'(v)` of each `L(v)`.  Every fixed `L`-coloring survives with probability
`(k/s)^n`, so

\[
  \mathbb E\,P(G,L')=\left(\frac{k}{s}\right)^n P(G,L).
\]

Since every `L'` has at least `m_G(k)` colorings, minimizing over `L` gives

\[
       \frac{m_G(k)}{k^n}\leq\frac{m_G(s)}{s^n}.
\]

This is the recent "shameful inequality" for the list color function, and the proof above is
self-contained.

For adjacent sizes there is an exact sharpened formulation.  Given a `(k+1)`-assignment `L`, let
`partial L` be the multiset of all `k`-assignments obtained by deleting one color at every vertex.
There are `(k+1)^n` deletion choices.  Double-counting pairs consisting of a coloring and a deletion
choice gives

\[
       \sum_{M\in\partial L}P(G,M)=k^nP(G,L).                 \tag{5.1}
\]

Indeed, at each vertex one may delete any of the `k` colors other than the color used there.

Now assume `m_G(k)=u_G(k)`, and define the nonnegative shadow excess

\[
       e_k(M):=P(G,M)-u_G(k).
\]

Substituting this in (5.1) shows that `G` is uniform-minimal at `k+1` **if and only if**, for every
`(k+1)`-assignment `L`,

\[
  \boxed{
  \sum_{M\in\partial L}e_k(M)
     \;\geq\;
  k^n u_G(k+1)-(k+1)^n u_G(k).}                              \tag{5.2}
\]

Thus the main conjecture is exactly a quantitative stability statement at level `k`: the aggregate
excess of all one-deletion shadows must pay for the increase in the normalized chromatic polynomial.
Random deletion only proves that the left side is nonnegative; the right side is usually positive.
This identifies the precise gap in the tempting one-line probabilistic proof.

Three immediate consequences are worth recording.

1. If `G` is uniform-minimal at `k`, then necessarily
   \[
       \frac{u_G(k+1)}{(k+1)^n}\geq\frac{u_G(k)}{k^n}.
   \]
   If equality holds here, the squeeze already proves uniform-minimality at `k+1`.  Hence a genuine
   counterexample requires a strict increase of the normalized chromatic polynomial at that step.

2. Equality in normalized list-count monotonicity,
   \[
       m_G(k+1)/(k+1)^n=m_G(k)/k^n,
   \]
   occurs exactly when a minimizing `(k+1)`-assignment has every member of its one-deletion shadow
   minimizing at `k`.  This "cube of minimizers" is a concrete computational signature to search
   for.

3. Under uniform-minimality at `k`, the possible next-step defect is bounded by
   \[
     0\leq u_G(k+1)-m_G(k+1)
       \leq u_G(k+1)-\left(\frac{k+1}{k}\right)^n u_G(k).
   \]

A plausible route to the full theorem is therefore not another averaging argument, but a stability
theorem saying that nonconstant shadows have enough total excess.  The amount that must be proved is
already written explicitly in (5.2).

## 6. What a smallest counterexample would have to look like

Suppose `G` agrees at `k` but fails at `k+1`, with `k >= chi(G)`.  The preceding results allow the
following reductions.

* `k >= 3`, by Corollary 4.2.
* `G` may be taken connected, by Proposition 3.1.
* `G` may be taken with minimum degree at least two, by Proposition 3.2.
* `k >= chi_ell(G)`, because agreement in the colorable range implies `k`-choosability.
* If `e=|E(G)|`, the Dong--Zhang eventual bound forces `k+1<e-1`, hence `e >= k+3`.
* The normalized chromatic polynomial must strictly increase from `k` to `k+1`.
* A minimizing bad `(k+1)`-assignment must violate the shadow-excess inequality (5.2).

These restrictions are useful for a finite search, but there is no obvious reduction across cut
vertices.  That is a real mathematical issue rather than a technical nuisance.

## 7. Cut vertices and rooted profiles

Suppose two rooted graphs are glued at their roots.  For a fixed list assignment and root color `c`,
let `a_c` and `b_c` be the numbers of colorings of the two pieces extending `c`.  The glued count is

\[
                         \sum_c a_c b_c.                    \tag{7.1}
\]

For common uniform lists, color symmetry makes both profiles constant and (7.1) is

\[
                    \frac{u_{G_1}(k)u_{G_2}(k)}{k}.
\]

For arbitrary lists, however, the two profiles can be skew and their color labels can be oppositely
aligned.  Knowing only lower bounds on `sum a_c` and `sum b_c` cannot control their dot product.  This
is why disjoint-union factorization does not extend automatically to block decompositions.

A direct pointwise bound on the root fibers is already false for a single cycle.  For `C_4`, `k=3`,
root `v_0`, palette `{0,1,2,3}`, and cyclic lists

\[
  012,\quad012,\quad013,\quad023,
\]

the numbers of extensions of root colors `0,1,2` are `(8,12,5)`.  The uniform profile is `(6,6,6)`.
Thus one cannot prove a cactus theorem by showing that every root color separately has at least the
uniform number of extensions.

A more promising target is a multiplicative, permutation-insensitive inequality:

> **Root-product inequality.**  For a rooted block `B` and every `k`-assignment,
> \[
>    \left(\prod_{c\in L(r)} a_c\right)^{1/k}
>       \geq \frac{u_B(k)}{k}.
> \]

It survives the example above: `(8*12*5)^(1/3)>6`.  More importantly, if several blocks are glued at
one root and each satisfies the root-product inequality, AM--GM gives

\[
  \sum_c\prod_i a_{i,c}
     \geq k\left(\prod_c\prod_i a_{i,c}\right)^{1/k}
     \geq k\prod_i\frac{u_{B_i}(k)}k,
\]

which is exactly the uniform count of the bouquet.  Proving the root-product inequality for cycles
at `k >= 3` would therefore settle all bouquets of cycles.  A matrix-valued strengthening, stable
when blocks are attached at different cut vertices, is a plausible route to all cactus graphs.

## 8. Concrete class problems

### 8.1 Theta graphs

For a nondegenerate theta graph `Theta(l_1,l_2,l_3)`, the 2026 classification says that it is
enumeratively chromatic-choosable unless all three path lengths have the same parity and the graph is
not `Theta(2,2,2)=K_{2,3}`.  This determines whether `tau=chi`, but not the exact threshold in the
exceptional bipartite cases.

The clean next conjecture is:

> **Theta threshold conjecture.**  Every theta graph has `tau <= 3`.  Equivalently, a mixed-parity
> theta has `tau=3`, `K_{2,3}` has `tau=2`, and every other same-parity theta has `tau=3`.

The mixed-parity and `K_{2,3}` assertions are known.  The family `Theta(2,2,2r)`, `r >= 2`, is also
known to agree at every `k >= 3` by Allred--Mudrock.  The new content is the remaining same-parity
family.

There is a useful proof architecture through correspondence coloring.  Fix the two branch vertices.
For a path of length `l` and a common `k`-palette, put `q=k-1`.  The numbers of extensions for equal
and unequal endpoint colors are

\[
 S_l=\frac{q^l+q(-1)^l}{k},\qquad
 D_l=\frac{q^l-(-1)^l}{k},\qquad S_l-D_l=(-1)^l.
\]

In a full DP-cover, each path has the same base matrix plus a `0/1` permutation matrix (or its
complement, according to parity).  Independent permutations on the three paths create a holonomy
around the theta and can lower the count.  A genuine list assignment is much more rigid: all
conflict matchings come from equality of global color names and are only partial identity matchings.

Completing those partial matchings to permutations can only remove colorings and produces a DP
cover.  The required list-color proof should compare two quantities:

1. the deficit of that completed DP-cover below the uniform theta count; and
2. the colorings restored when the artificial matching edges are deleted.

Call this **holonomy-defect compensation**.  It is close in spirit to the missing-edge correction in
the 2026 theta proof, and it attacks exactly the extra structure distinguishing list covers from DP
covers.

The target amount is explicit.  The known minimum DP count for three paths of the same parity is

\[
 \frac1k\left(q^{l_1+l_2+l_3}-q^{l_1}-q^{l_2}-q^{l_3}
                 +2(-1)^{l_1+l_2+l_3}\right).
\]

Subtracting it from the uniform theta count gives

\[
\begin{array}{ll}
\text{all }l_i\text{ even}:&
  q^{l_1}+q^{l_2}+q^{l_3}+k-3,\\[2mm]
\text{all }l_i\text{ odd}:&
  q^{l_1}+q^{l_2}+q^{l_3}-k+3.
\end{array}                                                     \tag{8.1}
\]

So a list-cover completion argument does not need a qualitative estimate: it must recover precisely
the gap in (8.1).

As weak evidence only, exhaustive enumeration of all `3`-assignments drawn from a four-color palette
found the uniform assignment minimizing for

| graph | uniform/minimum count in that search |
|---|---:|
| `Theta(3,3,3)` | 186 |
| `Theta(2,2,4)` | 102 |
| `Theta(2,4,4)` | 366 |
| `Theta(2,2,6)` | 390 |

This does not cover assignments using larger palette unions, so it is evidence, not a proof.

### 8.2 Cactus graphs

A natural, still conjectural spectrum classification is:

* a forest or a cactus with a single cycle has `tau=chi`;
* a bipartite cactus with at least two cycles has `nu=tau=3`;
* a nonbipartite cactus has `tau=3`.

The first bullet follows from the leaf identity and the known theorem for cycles.  In the second
bullet, failure at `2` follows from the connected `2`-choosable classification; the unproved part is
agreement from `3` onward.  The rooted-profile issue in Section 7 is the main obstacle.  The
root-product lemma for cycles is the first sharply stated subproblem.

An exhaustive four-color-palette check for two copies of `C_4` sharing one vertex found the uniform
minimum `18*18/3=108` at `k=3`, again only as finite evidence.

### 8.3 Complete bipartite graphs and bounded parallelism

One should not conjecture a constant threshold for all series-parallel or treewidth-two graphs:
`K_{2,r}` is series-parallel and `tau(K_{2,r})-chi_ell(K_{2,r})` is unbounded.  Thus theta graphs are
interesting partly because they have exactly three parallel paths; allowing arbitrarily many paths
changes the phenomenon.

For `K_{2,r}` there is an exact set-system formulation.  If the two degree-`r` vertices receive
colors `a,b`, then the `i`th other vertex has

\[
              k-|\{a,b\}\cap L_i|
\]

choices.  Therefore

\[
 P(K_{2,r},L)=
 \sum_{a\in L(x)}\sum_{b\in L(y)}
       \prod_{i=1}^r\bigl(k-|\{a,b\}\cap L_i|\bigr).          \tag{8.2}
\]

For uniform lists this becomes

\[
        u_{K_{2,r}}(k)=k(k-1)^r+k(k-1)(k-2)^r.                \tag{8.3}
\]

Classifying the extremizers of (8.2), even for ranges of `r` relative to `k`, looks like a tractable
way to obtain exact thresholds rather than only upper and lower bounds.  It is also a good testbed for
the shadow-excess inequality (5.2).

## 9. Suggested order of attack

1. Prove the root-product inequality for a rooted cycle at `k=3`; then try general `k`.
2. Use it to prove uniform-minimality for bouquets of cycles, where AM--GM closes the argument
   immediately.
3. Find a two-terminal/matrix strengthening that composes along the block-cut tree; this is the
   plausible cactus theorem.
4. In parallel, prove holonomy-defect compensation for same-parity theta graphs, first at `k=3`.
5. Treat (5.2) as the global monotonicity target: classify equality and near-equality cases of the
   random-deletion inequality rather than trying to average once more.
6. For computational work, canonicalize list assignments by color-renaming and search directly for a
   bad `(k+1)`-assignment whose deletion shadow has too little total excess.  This quotient is much
   smaller than searching raw palettes.

The first two items are narrow enough to produce a publishable class theorem even if the global
monotonicity conjecture remains open.

## References used in this note

* R. Kirov and M. Naimi, [List coloring and n-monophilic graphs](https://arxiv.org/abs/1004.5183).
* H. Kaul et al., [On the List Color Function Threshold](https://arxiv.org/abs/2202.03431).
* F. Dong and M. Zhang, [An improved lower bound of `P(G,L)-P(G,k)` for `k`-assignments
  `L`](https://arxiv.org/abs/2206.14536).
* J. Allred and J. Mudrock, [Enumerative Chromatic
  Choosability](https://arxiv.org/abs/2505.05662).
* J. Mudrock et al., [Enumeratively Chromatic-Choosable Theta
  Graphs](https://arxiv.org/abs/2605.10861).
* H. Kaul et al., [Shameful Inequalities for List and DP
  Coloring](https://arxiv.org/abs/2412.16790).
* A. Halberg et al., [The DP Color Function of Theta Graphs](https://arxiv.org/abs/2012.12897).

