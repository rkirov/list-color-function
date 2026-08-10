# Balanced coloring cores of odd cycles

Date: 2026-08-10

The two-terminal odd-cycle capacity theorem has a stronger and simpler explanation.  Every odd-cycle
list assignment contains a subcollection of exactly the uniform number of colorings which is
perfectly balanced at **every** vertex.  Weighted inequalities at any number of terminals then follow
from one AM--GM application.

Throughout, `C_ell` is an odd cycle, `k >= 3`, and

\[
             F=\frac{P(C_\ell,k)}k
               =\frac{(k-1)^\ell-(k-1)}k.                       \tag{0.1}
\]

## 1. Balanced coloring core

### Theorem 1.1

For every `k`-assignment `L` on an odd cycle, there is a set `B` of `L`-colorings such that

\[
                              |B|=P(C_\ell,k)                    \tag{1.1}
\]

and, for every vertex `v` and every color `c in L(v)`,

\[
                     |\{f\in B:f(v)=c\}|=F.                    \tag{1.2}
\]

Thus `B` has exactly the same one-vertex marginals as the common-list coloring set, even though the
original lists may be unrelated.

### Proof

On every cycle edge, equality of global color names gives a partial matching between the two endpoint
lists.  Complete each partial matching to a perfect matching.  This adds forbidden pairs, so every
coloring of the completed correspondence cover is an `L`-coloring.

Relabel the `k` color copies successively around a spanning path of the cycle.  All path-edge
matchings become the identity.  The remaining closing matching is represented by a permutation
`sigma` of the `k` labels: a last-vertex label `d` conflicts with root label `sigma(d)`.

Let `M` be the set of labels moved by `sigma`, and put `m=|M|`.  Fixing a label `c` at the root, the
number of completed-cover colorings is

\[
 \begin{cases}
 F,&\sigma(c)=c,\\
 F+1,&\sigma(c)\ne c.
 \end{cases}                                                     \tag{1.3}
\]

To see this, delete the closing edge.  There are `(k-1)^(ell-1)` colorings of the resulting path
extending `c`.  Since `ell-1` is even, the number ending in the closing-forbidden label is

\[
 \frac{(k-1)^{\ell-1}+(k-1)}k
 \quad\text{if }c\text{ is fixed},
\]

and

\[
 \frac{(k-1)^{\ell-1}-1}k
 \quad\text{if }c\text{ is moved}.
\]

Subtracting gives (1.3).  The same count holds at every vertex: rerooting replaces `sigma` by a
conjugate or its inverse, which has the same fixed labels after transporting the local indexing.

There are therefore `kF+m` completed-cover colorings.  We now identify `m` of them explicitly.  For
each moved label `c`, take the alternating coloring

\[
 f_c(v_i)=
 \begin{cases}
 c,&i\text{ even},\\
 \sigma(c),&i\text{ odd},
 \end{cases}                                                     \tag{1.4}
\]

where the root is `v_0`.  Consecutive labels differ because `c` is moved.  Since `ell-1` is even,
the last label is again `c`; the closing pair is allowed because `c != sigma(c)`.  Hence every `f_c`
is a completed-cover coloring.

At each even-indexed vertex, the colorings `(f_c)_{c in M}` use every moved label once.  At each
odd-indexed vertex, they use `(sigma(c))_{c in M}`, again every moved label once because `sigma`
permutes `M`.  Delete these `m` alternating colorings from the completed-cover coloring set.  By
(1.3), exactly `F` occurrences of every label remain at every vertex.  The remaining set has size
`kF=P(C_ell,k)` and is contained in the original `L`-coloring set.  This is the required `B`.  ∎

## 2. Multi-terminal weighted inequality

### Theorem 2.1

At every vertex `v` of an odd cycle, assign arbitrary nonnegative weights `w_v(c)` to the colors in
`L(v)`.  Then

\[
 \sum_{f\in\operatorname{Colorings}(C,L)}\prod_v w_v(f(v))
 \geq
 P(C,k)\prod_v\left(\prod_{c\in L(v)}w_v(c)\right)^{1/k}.       \tag{2.1}
\]

Weights equal to one may of course be omitted, so this includes any chosen set of terminals.

**Proof.**  Restrict the sum to the balanced core `B` from Theorem 1.1 and apply AM--GM to its
`|B|=kF` summands.  By balance,

\[
 \prod_{f\in B}\prod_vw_v(f(v))
   =\prod_v\prod_{c\in L(v)}w_v(c)^F.
\]

Taking the `(kF)`th root gives the product of geometric means on the right of (2.1).  ∎

### Corollary 2.2

Attach geometrically uniform-root dominant graphs at any number of vertices of an odd cycle.  The
resulting graph is geometrically uniform-root dominant at any remaining chosen root, after including
that root as one more terminal.

This is the multi-terminal propagation statement needed in a cactus block tree.

## 3. A larger cactus classification

Let `T_G` be the block-cut tree of a connected cactus.  Mark the block-nodes corresponding to even
cycles, and let `S_G` be the minimal subtree containing all marked nodes.  Say that the even cycles
are **peripheral** if every marked even-cycle node has degree at most one in `S_G`.  Equivalently, no
even cycle block lies on the block-cut-tree path between two other even cycle blocks.

### Theorem 3.1

If the even cycles of a cactus are peripheral, then the cactus is uniform-minimal for every
`k >= 3`.

**Proof.**  Components and pendant trees are harmless, so consider a connected component and its
block-cut tree.

Each peripheral even cycle is a leaf of the subtree connecting all even cycles.  Root it at its
unique cut vertex toward the rest of that subtree.  Any components attached on its other side contain
no even cycle; their blocks are edges or odd cycles and are pointwise uniform-root dominant.  Such
attachments preserve the even cycle's geometric rooted bound.  The rooted-cycle product theorem
therefore supplies one geometrically dominant message from every even-cycle leaf.

Prune the block-cut subtree inward.  At a cut vertex, incoming messages multiply coordinatewise and
remain geometrically dominant.  Across a bridge, use the complementary-sum bridge inequality.  At an
odd-cycle block, any number of incoming messages at different cut vertices and the outgoing message
are controlled simultaneously by Theorem 2.1.  All operations preserve the appropriate uniform
root fiber exactly.

Eventually the messages meet at one cut vertex or one odd-cycle block, where the same closure
argument yields a geometrically dominant rooted profile for the whole graph.  AM--GM makes the graph
uniform-minimal.  ∎

### Corollary 3.2: exact spectrum

For a connected cactus with peripheral even cycles:

* a single vertex has `nu=tau=1`;
* a nontrivial forest or an even-unicyclic graph has `nu=tau=2`;
* if it is bipartite with at least two cycles, then `nu=tau=3`;
* if it has an odd cycle, then `nu=tau=chi=3`.

The only new assertion below `3` is failure for a bipartite cactus with at least two cycles, which
follows from Rubin's connected `2`-choosable classification.  Agreement at every `k >= 3` is Theorem
3.1.

This includes arbitrarily many even cycles, provided none is used as a corridor between two others.
It strictly contains the class of cacti with at most two even cycles.

## 4. Remaining cactus obstruction

After Theorem 3.1, the first unresolved configuration is three even cycles in a chain: the middle
even cycle is an internal node of the subtree spanning the even blocks.  Thus the full cactus
conjecture has been reduced to one sharply isolated operation:

> transport geometric rooted dominance through an even cycle carrying independent weights at two
> or more vertices.

Equivalently, prove the even-cycle analogue of Theorem 2.1, with the balanced-core conclusion replaced
by a weaker capacity statement; a literally balanced core is impossible because an even-cycle root
fiber can be `F-1`.

