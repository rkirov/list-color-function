# Rooted uniform bounds and closure theorems

Date: 2026-08-10

The scalar property `m_G(k)=P(G,k)` does not retain enough information at a cut vertex.  The useful
objects are the numbers of extensions of each root color.  This note records two rooted strengthenings
and proves closure theorems from them.  Together with the rooted-cycle theorem, they give another
completely classified family beyond the `2`-choosable graphs.

Fix a graph `G`, a root `r`, a `k`-assignment `L`, and write

\[
 N_{G,L,r}(c)=\#\{L\text{-colorings }f:f(r)=c\},\qquad c\in L(r),
\]

and

\[
                        F_{G,r}(k):=\frac{P(G,k)}k.
\]

The quotient is an integer: under common lists, color symmetry makes all `k` root fibers equal.

## 1. Two rooted properties

Say that `(G,r)` is **pointwise uniform-root dominant** at `k`, abbreviated `PUR_k`, if every
`k`-assignment satisfies

\[
                         N_{G,L,r}(c)\geq F_{G,r}(k)              \tag{1.1}
\]

for every `c in L(r)`.

Say that `(G,r)` is **geometric uniform-root dominant** at `k`, abbreviated `GUR_k`, if every
`k`-assignment satisfies

\[
       \prod_{c\in L(r)}N_{G,L,r}(c)\geq F_{G,r}(k)^k.           \tag{1.2}
\]

The implications are

\[
             PUR_k\quad\Longrightarrow\quad GUR_k
             \quad\Longrightarrow\quad m_G(k)=P(G,k).          \tag{1.3}
\]

The second implication is AM--GM:

\[
 P(G,L)=\sum_cN(c)
   \geq k\left(\prod_cN(c)\right)^{1/k}
   \geq kF_{G,r}(k)=P(G,k).
\]

Odd cycles satisfy `PUR_k` for `k >= 3`.  Even cycles do not satisfy `PUR_3` in general, but every
cycle satisfies `GUR_k` for `k >= 3`; this is Theorem 1.1 of
`rooted_cycle_product_proof.md`.

## 2. Chordal graphs satisfy the pointwise property

### Lemma 2.1: a prescribed last vertex

If `G` is connected and chordal, then for every vertex `r` there is a perfect elimination ordering

\[
                              v_1,\ldots,v_n=r.                  \tag{2.1}
\]

**Proof.**  Induct on the number of vertices.  If `G` is complete, every ordering works.  Otherwise a
chordal graph has two nonadjacent simplicial vertices, so at least one of them is not `r`.  Delete
that vertex, apply induction to the remaining chordal graph, and place the deleted vertex first.  ∎

### Theorem 2.2: rooted chordal dominance

Let `G` be chordal and `k >= chi(G)`.  Then `(G,r)` satisfies `PUR_k` for every root `r`.

**Proof.**  First suppose `G` is connected, and use (2.1).  Let `d_i` be the number of neighbors of
`v_i` later in the ordering.  Those neighbors form a clique.  Fix any color `c in L(r)` at the root
and color the other vertices in reverse elimination order.  When `v_i` is reached, its `d_i` later
neighbors already have distinct colors, so at most `d_i` members of its list are forbidden.  There
are at least `k-d_i` choices.  Hence

\[
                  N_{G,L,r}(c)\geq\prod_{i<n}(k-d_i).            \tag{2.2}
\]

With one common palette, every inequality in this greedy count is equality and

\[
                  P(G,k)=k\prod_{i<n}(k-d_i).
\]

Thus the right side of (2.2) is exactly `F_{G,r}(k)`.  Disconnected graphs follow by multiplying by
the corresponding bounds on the other components.  ∎

This is stronger than ordinary enumerative chromatic choosability of chordal graphs: it controls
every prescribed root color, not just the sum of the fibers.

## 3. Attaching a pointwise-dominant graph

### Theorem 3.1: profile-preserving attachment

Let graphs `A` and `B` meet in exactly one vertex `x`.  Suppose `(B,x)` satisfies `PUR_k`.  For any
root `r` in `A`, attaching `B` at `x` has the following effects.

1. If `(A,r)` satisfies `PUR_k`, then `(A union_x B,r)` satisfies `PUR_k`.
2. If `(A,r)` satisfies `GUR_k`, then `(A union_x B,r)` satisfies `GUR_k`.

**Proof.**  Fix a list assignment and a root color at `r`.  Each coloring of `A` uses some color `d`
at `x`, and it has at least `P(B,k)/k` extensions across `B`, by pointwise dominance.  Thus every
fiber at `r` is multiplied by at least `P(B,k)/k`.  On common lists the root fiber is multiplied by
exactly that factor, since

\[
                    P(A\cup_xB,k)=\frac{P(A,k)P(B,k)}k.
\]

The pointwise and product conclusions follow.  ∎

### Corollary 3.2: chordal/odd-cycle block theorem

Suppose every block of `G` is either chordal or an odd cycle.  Then, for every `k >= chi(G)` and every
root `r`, `(G,r)` satisfies `PUR_k`.  In particular `G` is uniform-minimal throughout its colorable
range, so `nu(G)=tau(G)=chi(G)`.

**Proof.**  Chordal blocks have the pointwise property by Theorem 2.2; odd cycles have it by the odd
case of the rooted-cycle theorem.  Start with the block containing `r` and traverse the block-cut tree
outwards, applying Theorem 3.1 whenever a new block is attached.  ∎

This includes all cacti whose cycles are odd, but also permits arbitrary chordal blocks between the
odd cycles.

## 4. Geometric dominance at a common cut vertex

### Theorem 4.1: rooted one-sums

If `(A,x)` and `(B,x)` both satisfy `GUR_k`, then their one-vertex sum also satisfies `GUR_k` at `x`.

**Proof.**  If the two rooted profiles are `(a_c)` and `(b_c)`, the profile after gluing is
`(a_cb_c)`.  Therefore

\[
 \prod_c a_cb_c
   =\left(\prod_ca_c\right)\left(\prod_cb_c\right)
   \geq\left(\frac{P(A,k)}k\frac{P(B,k)}k\right)^k.
\]

The product inside the last parentheses is precisely the uniform root fiber of the one-sum.  ∎

This is the conceptual form of the AM--GM proof for bouquets of cycles.

## 5. Transporting a geometric bound across a bridge

### Lemma 5.1: complementary-sum product inequality

For nonnegative numbers `h_1,...,h_k`, with `S=sum h_i`,

\[
                       \prod_{i=1}^k(S-h_i)
                          \geq (k-1)^k\prod_{i=1}^kh_i.          \tag{5.1}
\]

**Proof.**  For each `i`, AM--GM gives

\[
 S-h_i=\sum_{j\ne i}h_j
   \geq(k-1)\left(\prod_{j\ne i}h_j\right)^{1/(k-1)}.
\]

Multiply these `k` inequalities.  Every `h_j` occurs in exactly `k-1` of the products under the
root, so its total exponent is one.  ∎

### Theorem 5.2: bridge transport

Suppose `(H,v)` satisfies `GUR_k`.  Add a new vertex `r` adjacent only to `v`, and regard `r` as the
new root.  Then the enlarged rooted graph satisfies `GUR_k`.

**Proof.**  For a fixed assignment, write `h_d` for the old profile on `L(v)` and `S=sum_d h_d`.
For a new-root color `c`, the new profile value is

\[
 a_c=\begin{cases}S-h_c,&c\in L(v),\\S,&c\notin L(v).\end{cases}
\]

Choose a bijection from `L(r)` to `L(v)` which fixes their intersection.  Replacing any factor `S`
by the smaller factor `S-h_d` and then using (5.1) gives

\[
              \prod_{c\in L(r)}a_c
                 \geq(k-1)^k\prod_{d\in L(v)}h_d.
\]

Taking geometric means, the rooted bound is multiplied by at least `k-1`.  The common-list root
fiber is also multiplied by exactly `k-1`, since adjoining a leaf multiplies the chromatic polynomial
by `k-1`.  ∎

Iterating Theorem 5.2 transports `GUR_k` along an arbitrary path.

## 6. A completely classified cactus family

Call a graph a **tree of cycle bouquets** if it can be constructed as follows:

1. start with a tree `T`;
2. at any vertex of `T`, glue any number of cycles by identifying one chosen vertex of each cycle
   with that tree vertex;
3. attach arbitrary additional trees at arbitrary vertices.

Equivalently, no cycle is used as a corridor between two other cyclic parts; all communication
between the bouquet roots runs through bridge edges.

### Theorem 6.1

Every tree of cycle bouquets is uniform-minimal for every `k >= 3`.  More strongly, if the graph is
rooted at a vertex of the underlying tree, it satisfies `GUR_k`.

**Proof.**  Each cycle satisfies `GUR_k`; combine all cycles based at one tree vertex using Theorem
4.1.  Root the underlying tree.  Working from its leaves inward, transport each child profile across
its incident tree edge using Theorem 5.2 and combine the resulting profiles at the parent using
Theorem 4.1.  Pendant trees are handled by the same bridge operation, or by Theorem 3.1 since trees
are chordal and pointwise dominant.  The final rooted graph satisfies `GUR_k`, hence is
uniform-minimal by (1.3).  ∎

### Corollary 6.2: exact spectrum

For a connected tree of cycle bouquets:

* a single vertex has `nu=tau=1`;
* a nontrivial tree, or a graph with exactly one cycle and that cycle even, has `nu=tau=2`;
* if all cycles are even and there are at least two, then `nu=tau=3`;
* if any cycle is odd, then `nu=tau=3`.

In the third case, failure at `2` follows from Rubin's connected `2`-choosable classification; the
core of such a cactus is neither a single even cycle nor `K_{2,3}`.  Agreement from `3` onward is
Theorem 6.1.  In particular, this completely classifies every cactus with at most two cycles.

## 7. Joining a dominating clique

### Theorem 7.1: clique-join shift

If `G` is uniform-minimal at `k`, then `K_t join G` is uniform-minimal at `k+t` for every `t >= 0`.

**Proof.**  Give the join arbitrary lists of size `k+t`.  Greedily coloring the `t`-clique gives at
least

\[
                         (k+t)(k+t-1)\cdots(k+1)                  \tag{7.1}
\]

proper clique colorings.  Fix one of them, using a set `S` of `t` distinct colors.  Delete `S` from
every list on `G`; at least `k` colors remain at every vertex.  Choose a `k`-subset at each vertex.
Uniform minimality of `G` at `k` supplies at least `P(G,k)` colorings from those sublists, all avoiding
the clique colors.  Thus the join has at least (7.1) times `P(G,k)` list colorings.  This product is
exactly `P(K_t join G,k+t)`.  ∎

Consequently

\[
     \nu(K_t\mathbin{\mathrm{join}}G)\leq\nu(G)+t,
     \qquad
     \tau(K_t\mathbin{\mathrm{join}}G)\leq\tau(G)+t.            \tag{7.2}
\]

In particular, joining a clique to an enumeratively chromatic-choosable graph preserves that
property.

For `t=1` there is a useful rooted strengthening: the cone `K_1 join G` is `PUR_{k+1}` at its apex
whenever `G` is uniform-minimal at `k`.  Indeed, after fixing the apex color, deleting it from every
list on `G` leaves at least `k` colors per vertex and hence at least `P(G,k)` extensions, exactly the
uniform apex fiber.

## 8. What remains for arbitrary cacti

Theorems 4.1 and 5.2 solve all compositions at a common cut vertex and across bridges.  The first
unresolved cactus configuration has an even cycle used as a corridor: already-attached rooted
subgraphs place nonconstant weights at one cycle vertex, and the desired root lies at another cycle
vertex.

The exact missing statement is a **two-terminal cycle-capacity inequality**.  If `M_{x,y}` is the
matrix whose `(c,d)` entry counts list colorings of a cycle with colors `c,d` fixed at terminals
`x,y`, the desired inequality is

\[
 \left(\prod_d\sum_c h_cM_{x,y}(c,d)\right)^{1/k}
   \geq \frac{P(C,k)}k\left(\prod_ch_c\right)^{1/k}             \tag{8.1}
\]

for every nonnegative vector `h`.  In matrix-scaling language, this says that the capacity of
`M_{x,y}` is at least the uniform root fiber.  It would transport `GUR_k` through a cycle, and hence
prove the full cactus threshold conjecture by induction on the block-cut tree.

Random tests for `k=3` on cycles of lengths `4,5,6`, using lists from a five-color palette and highly
skew weight vectors, found no violation of (8.1).  This is evidence only; (8.1) is not yet logged as
proved.

