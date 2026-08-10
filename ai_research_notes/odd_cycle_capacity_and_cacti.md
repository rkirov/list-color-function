# Odd-cycle terminal capacity and cacti with two even cycles

Date: 2026-08-10

This note proves the two-terminal capacity inequality for **odd** cycles.  Combined with the rooted
product theorem for even cycles, it extends the proved cactus class from "at most one even cycle" to
"at most two even cycles," with arbitrarily many odd cycles and bridges between them.

Throughout, `k >= 3`, `q=k-1`, and all lists have size `k`.

## 1. Fixed-terminal matrices

Let `C` be a cycle with distinct terminals `x,y`.  For a list assignment `L`, define the `k by k`
matrix

\[
 M_{x,y}(c,d)=\#\{L\text{-colorings of }C:f(x)=c,\ f(y)=d\},   \tag{1.1}
\]

with rows indexed by `L(x)` and columns by `L(y)`.

For a nonnegative row vector `h`, the vector `hM` is the coloring profile at `y` obtained after a
rooted graph with profile `h` is attached at `x`.  Thus geometric rooted dominance transports from
`x` to `y` if

\[
 \left(\prod_d(hM)_d\right)^{1/k}
   \geq \frac{P(C,k)}k\left(\prod_ch_c\right)^{1/k}.            \tag{1.2}
\]

## 2. Completed path matrices

The terminals split `C` into paths of lengths `a` and `b`, with `a+b=ell`.  On an edge, equality of
global color names gives a partial matching between the two endpoint lists.  Complete every such
partial matching to a perfect matching.  This adds forbidden pairs, so it can only decrease every
fixed-endpoint path count.

After relabeling the color copies along a completed path of length `s`, its transfer matrix has the
form

\[
                         T_s(R)=D_sJ+(-1)^sR,                    \tag{2.1}
\]

where `R` is a permutation matrix and

\[
 S_s=\frac{q^s+q(-1)^s}{k},\qquad
 D_s=\frac{q^s-(-1)^s}{k}.                                    \tag{2.2}
\]

Indeed the entries on the matching `R` are `S_s`, all other entries are `D_s`, and
`S_s-D_s=(-1)^s`.

Since the two paths have disjoint internal vertices, their fixed-terminal counts multiply
entrywise.  Consequently the genuine list matrix in (1.1) dominates

\[
                         T_a(R_1)\circ T_b(R_2),                 \tag{2.3}
\]

where the circle is the Hadamard product.

## 3. The odd-cycle capacity theorem

### Theorem 3.1

If `C` is an odd cycle, then (1.2) holds for every choice of terminals, every `k`-assignment, and
every nonnegative vector `h`.

**Proof.**  Since `a+b` is odd, one path length is even and the other is odd.  Relabel the terminal
columns so that the permutation belonging to the even path is the identity.  Write `R` for the
relative permutation belonging to the odd path, and let

\[
                         B=T_a(I)\circ T_b(R)                    \tag{3.1}
\]

after interchanging `a,b` if necessary.

Put

\[
                              F=\frac{P(C,k)}k.                  \tag{3.2}
\]

If `R` fixes row index `i`, the two distinguished path entries coincide and row `i` of `B` has sum
`F`.  If `R(i) != i`, the distinguished entries are in different columns.  Expanding (2.1) shows
that row has sum `F+1`: the correction is

\[
                       (-1)^a(-1)^b=-1.
\]

The same statement holds for column sums.  Thus rows and columns indexed by fixed points of `R`
have sum `F`, while all other rows and columns have sum `F+1`.

For every nonfixed index `i`, subtract one from the `(i,i)` entry.  This entry is the product of the
even path's matched count and the odd path's unmatched count,

\[
                              S_aD_b\geq1,                       \tag{3.3}
\]

so the subtraction leaves a nonnegative matrix.  Call the resulting matrix `B_0`.  The nonfixed
indices form the same set on the row and column sides, so every row and every column of `B_0` now
has sum exactly `F`.

Hence `B_0/F` is doubly stochastic.  Weighted AM--GM, first in each column and then multiplied over
the columns, gives

\[
 \prod_d(hB_0)_d
   \geq F^k\prod_ch_c.                                         \tag{3.4}
\]

Explicitly,

\[
 \frac{(hB_0)_d}{F}=\sum_c\frac{B_0(c,d)}Fh_c
   \geq\prod_ch_c^{B_0(c,d)/F},
\]

and the exponent of each `h_c` becomes one after multiplying over `d`, because the corresponding
row sum is `F`.

Finally the genuine list matrix satisfies `M >= B >= B_0` entrywise by (2.3).  Replacing `B_0` by
`M` can only increase every coordinate of `hM`, so (3.4) proves (1.2).  ∎

### Corollary 3.2: transport through a decorated odd cycle

Attach any collection of pointwise uniform-root dominant graphs to vertices of an odd cycle, away
from or at the terminals.  The decorated cycle still transports geometric uniform-root dominance
between the two terminals.

**Proof.**  For every fixed coloring of the cycle, each attached graph has at least its uniform root
fiber many extensions.  Thus the decorated terminal matrix dominates the bare terminal matrix times
the product of those uniform fibers.  Its uniform terminal target is scaled by exactly the same
product.  Apply Theorem 3.1.  ∎

## 4. Cacti with at most two even cycles

### Theorem 4.1

Every cactus graph containing at most two even cycle blocks is uniform-minimal for every
`k >= chi(G)`.  More precisely, it is uniform-minimal for all `k >= 3`, and the value at `2` is
determined by the usual connected `2`-choosable classification.

**Proof.**  Work componentwise.

If the connected cactus has no even cycle, every block is an edge or an odd cycle.  The
chordal/odd-cycle block theorem gives the stronger pointwise rooted property.  The one-even-cycle
case was proved in `rooted_cycle_product_proof.md`.

Now suppose there are exactly two even cycle blocks `E_1,E_2`.  In the block-cut tree there is a
unique path between them.  Every component hanging off this path contains no even cycle, so all of
its blocks are edges or odd cycles.  It is pointwise uniform-root dominant at its attachment vertex;
attach these side components without weakening any geometric rooted bound on the main path.

Root `E_1` at the cut vertex leading toward `E_2`.  The rooted-cycle product theorem makes it
geometrically uniform-root dominant.  Traverse the block-cut path toward `E_2`:

* across a bridge, use the complementary-sum bridge-transport theorem;
* across an odd cycle, use Corollary 3.2;
* at a cut vertex, attach any side component using pointwise profile preservation.

This transports geometric rooted dominance to the attachment vertex of `E_2`.  The second even
cycle is geometrically dominant at that same root, so the rooted one-sum theorem combines the two
profiles.  The resulting graph is geometrically dominant and therefore uniform-minimal.  ∎

### Corollary 4.2: exact spectrum

For a connected cactus with at most two even cycles:

* a single vertex has `nu=tau=1`;
* a nontrivial forest or an even-unicyclic graph has `nu=tau=2`;
* if there are exactly two even cycles and no odd cycle, then `nu=tau=3`;
* if there is any odd cycle, then `nu=tau=chi=3`.

In the third case the graph is bipartite but not `2`-choosable: its core is not a vertex, a single
even cycle, or `K_{2,3}`.  Thus it fails at `2`, while Theorem 4.1 gives agreement from `3` onward.

## 5. Remaining cactus obstruction

For three or more even cycle blocks, the block-cut subtree spanning them can branch inside another
cycle block.  Bridge branching is harmless because geometric profiles combine at a common cut
vertex.  An odd cycle with three or more independently weighted terminal vertices requires a
multi-terminal version of Theorem 3.1, while an even cycle used as a two-terminal corridor still
requires the even version of (1.2).

Thus two precise next targets are:

1. prove the two-terminal capacity inequality for even cycles using the missing-matching compensation
   from the rooted product proof;
2. prove a multi-terminal capacity inequality for odd cycles.

Either would enlarge the cactus class; both together would prove the full cactus threshold
conjecture.

