# A rooted-cycle product theorem and two class consequences

Date: 2026-08-10

This note supersedes the conjectural treatment of the root-product inequality in
`min_list_coloring_research.md`.  The inequality is in fact provable for cycles, using the equality
case of the path-minimization lemma in Kirov--Naimi.  It gives a complete uniform-minimality spectrum
for bouquets of cycles and for cacti with at most one even cycle.

Throughout, `k >= 3`.  For a cycle of length `ell`, put

\[
 F_\ell(k):=\frac{P(C_\ell,k)}k
   =\frac{(k-1)^\ell+(-1)^\ell(k-1)}k.
\]

This is the number of uniform-palette cycle colorings extending any one prescribed color at a
specified root.

## 1. Rooted-cycle product theorem

### Theorem 1.1

Let `C_ell` be rooted at `r`, let `L` be any `k`-assignment, and, for each `c in L(r)`, let

\[
 a_c:=\#\{\text{proper }L\text{-colorings }f:f(r)=c\}.
\]

Then

\[
                    \prod_{c\in L(r)}a_c\ \geq\ F_\ell(k)^k.       \tag{1.1}
\]

If `ell` is odd, the stronger pointwise inequality

\[
                         a_c\geq F_\ell(k)                           \tag{1.2}
\]

holds for every root color `c`.

The common-list assignment attains equality in (1.1), so the bound is sharp.

### Input from path minimization

Fix a root color `c` and delete the root.  What remains is a path of length `ell-2`.  At each of its
two endpoints, delete `c` if it occurs in that endpoint list.  The endpoint lists now have size `k`
or `k-1`, while all internal lists have size `k`.  If an endpoint still has size `k`, shrink it
arbitrarily to size `k-1`; this can only decrease the number of colorings.

The path-minimization lemma for `(k,k-1)`-assignments says that the minimum is attained by a shaped
assignment: all internal lists are one common `k`-set `S`, and the endpoint lists are
`S minus {x}` and `S minus {y}`.  For `k >= 3`, its equality case says that a minimizing assignment
has `x=y` when the path length is odd and `x != y` when it is even.  Substitution in the two path
recurrences gives

\[
 a_c\geq
 \begin{cases}
 F_\ell(k),&\ell\text{ odd},\\
 F_\ell(k)-1,&\ell\text{ even}.
 \end{cases}                                                     \tag{1.3}
\]

The odd-cycle assertion (1.2), and hence (1.1) for odd cycles, follows immediately.  The rest of the
proof deals with even cycles.

### Equality structure for an even cycle

Assume `ell` is even and some root color `c` is deficient, meaning

\[
                         a_c=F_\ell(k)-1.                           \tag{1.4}
\]

First, `c` must occur in both lists neighboring the root.  If, say, the first effective endpoint list
still had size `k`, remove one of its colors.  The smaller assignment has at least `F_ell(k)-1`
colorings by (1.3).  Adding the removed color back creates at least one further coloring: fix that
color at the endpoint and greedily color along the path.  Every internal step has at least `k-1`
choices and the last endpoint has at least `k-2 >= 1`.  This contradicts (1.4).

Thus both effective endpoint lists have size `k-1`, and equality in (1.3) makes the remaining path a
minimizing assignment.  The equality classification supplies a `k`-set `S` and distinct `x,y in S`
such that the two neighbor lists in the original cycle are

\[
                 (S\setminus\{x\})\cup\{c\},\qquad
                 (S\setminus\{y\})\cup\{c\},                     \tag{1.5}
\]

all lists strictly between them are `S`, and `c` is not in `S`.  The last assertion follows because
`c` belongs to both original neighbor lists, while deleting it produces `S minus {x}` and
`S minus {y}` with `x != y`.

This already shows that at most one root color can be deficient.  Indeed, a deficient second color
would have to be the unique color outside `S` in either list in (1.5), and hence would equal `c`.

### The forced surplus

It remains to show that the other root colors compensate multiplicatively for the single possible
factor `F_ell(k)-1`.  Write

\[
 q=k-1,\qquad F=F_\ell(k),\qquad
 \beta=\frac{q^{\ell-4}-1}{k}\geq0.
\]

For a different root color `d`, count the path colorings using (1.5).  On the common palette `S`, the
transition matrix is `J-I`, and, since `ell-4` is even,

\[
                         (J-I)^{\ell-4}=\beta J+I.                 \tag{1.6}
\]

Multiplying the two endpoint incidence vectors through (1.6) gives the following exact increments:

\[
 a_d-F=
 \begin{cases}
 Z:=\beta(2q^2+1)+2q-2,
     &d\in S\setminus\{x,y\},\\[1mm]
 X:=\beta(q^3+2q^2+q+1)+q^2+q,
     &d=x\text{ or }d=y,\\[1mm]
 Y:=\beta(q+1)(2q^2+q+1)+2q^2+q,
     &d\notin S\cup\{c\}.
 \end{cases}                                                     \tag{1.7}
\]

For completeness, (1.7) is just the following two-vector calculation.  A vector of the form
`t*1 + 1_A` has coordinate sum `kt+|A|`, and

\[
 (t\mathbf1+\mathbf1_A)^T(\beta J+I)
 (s\mathbf1+\mathbf1_B)
 =\beta(kt+|A|)(ks+|B|)+kts+t|B|+s|A|+|A\cap B|.
\]

The endpoint vectors in the three cases of (1.7) are respectively

\[
\begin{array}{c|c|c}
&\text{left endpoint}&\text{right endpoint}\\ \hline
d\in S\setminus\{x,y\}
 &(q-1)\mathbf1+\mathbf1_{\{x,d\}}
 &(q-1)\mathbf1+\mathbf1_{\{y,d\}}\\
d=x
 &q\mathbf1+\mathbf1_{\{x\}}
 &(q-1)\mathbf1+\mathbf1_{\{x,y\}}\\
d\notin S\cup\{c\}
 &q\mathbf1+\mathbf1_{\{x\}}
 &q\mathbf1+\mathbf1_{\{y\}}.
\end{array}
\]

The case `d=y` is symmetric.

In particular, `Z >= 0`, `Y >= X`, and

\[
                            X\geq q^2+q\geq6.                     \tag{1.8}
\]

The root list contains `c` and `k-1` other colors, but `S minus {x,y}` contains only `k-2` colors.
Consequently at least one other root color lies in the second or third case of (1.7).  All remaining
root colors contribute at least `F`.  Since `F >= 6` for `k >= 3` and an even simple cycle, we obtain

\[
 \prod_{d\in L(r)}a_d
   \geq(F-1)(F+X)F^{k-2}
   \geq F^k,
\]

where the last inequality is equivalent to `F(X-1)-X >= 0`.  This proves Theorem 1.1.  ∎

## 2. Complete spectrum for bouquets of cycles

A **cycle bouquet** is obtained from vertex-disjoint cycles by identifying one chosen vertex from
each cycle into one common root.  Trees may subsequently be attached anywhere without affecting the
conclusions below.

### Theorem 2.1

Every cycle bouquet is uniform-minimal at every `k >= 3`.

**Proof.**  For cycle `i`, let `(a_{i,c})_c` be its rooted coloring profile and let
`F_i=P(C_i,k)/k`.  A coloring of the bouquet is a tuple of cycle colorings which use the same color at
the common root.  Hence its list-color count is

\[
                            \sum_c\prod_i a_{i,c}.
\]

Theorem 1.1 and AM--GM give

\[
 \sum_c\prod_i a_{i,c}
 \geq k\left(\prod_c\prod_i a_{i,c}\right)^{1/k}
 =k\prod_i\left(\prod_c a_{i,c}\right)^{1/k}
 \geq k\prod_i F_i.
\]

The last expression is exactly the uniform-palette count of the bouquet.  Attaching a leaf multiplies
both the minimum list count and the uniform count by `k-1`, so arbitrary attached trees cause no
change.  ∎

This gives the exact agreement spectrum for every connected graph whose core is a cycle bouquet.

* A single vertex has `nu=tau=1`; a nontrivial tree has `nu=tau=2`.
* If the bouquet consists of one even cycle, then `nu=tau=2`.
* If it consists of at least two even cycles and no odd cycle, then `chi=2` and `nu=tau=3`.
  Indeed it is not `2`-choosable by Rubin's classification, while Theorem 2.1 gives agreement from
  `3` onward.
* If at least one cycle is odd, then `chi=3` and `nu=tau=3` by Theorem 2.1.

Thus the monotonicity conjecture holds for this whole class, and the spectrum is completely
categorized.

## 3. A cactus theorem

The pointwise odd-cycle bound (1.2) composes more flexibly than the product bound.

### Lemma 3.1: adjoining an odd cycle

Suppose `A` is uniform-minimal at `k`, and glue an odd cycle `C` to `A` at one vertex.  The resulting
graph is uniform-minimal at `k`.

**Proof.**  For any list assignment, let `a_c` be the rooted profile of `A` and `b_c` that of `C`.
By (1.2), `b_c >= P(C,k)/k` for every `c`.  Therefore

\[
 \sum_c a_cb_c
   \geq \frac{P(C,k)}k\sum_c a_c
   \geq \frac{P(C,k)}kP(A,k),
\]

which is the uniform count of the one-vertex sum.  ∎

### Theorem 3.2

Every cactus graph with at most one even cycle is uniform-minimal at every `k >= chi(G)`.

**Proof.**  Work componentwise.  In a connected component, choose the unique even cycle as the
initial block if it exists; otherwise start with an odd cycle, or with a vertex if the graph is a
tree.  Cycles themselves are uniform-minimal.  Traverse the block-cut tree outwards.  Each new
nontrivial block is either an edge or an odd cycle.  Edges are handled by the leaf identity, and odd
cycles by Lemma 3.1.  ∎

In particular:

* a cactus with an odd cycle and at most one even cycle has `nu=tau=chi=3`;
* a bipartite cactus with at most one cycle is a forest or an even-unicyclic graph and has
  `nu=tau=chi` (apart from the conventional isolated-vertex value `1`).

## 4. The remaining cactus conjecture

The natural extension is now narrower:

> **Cactus threshold conjecture.**  Every cactus graph is uniform-minimal for every `k >= 3`.

Only arrangements with at least two even cycle blocks remain, and the bouquet case is already
Theorem 2.1.  If the conjecture holds, a connected bipartite cactus with at least two cycles has
`nu=tau=3`, while every nonbipartite cactus has `nu=tau=3`.

The unweighted root-product inequality is not by itself enough when even cycles occur at different
cut vertices.  Messages from already-attached subcacti weight the colors at several vertices of the
next cycle.  The appropriate next lemma is therefore a weighted or two-terminal version of Theorem
1.1: cycle transfer should preserve a geometric-mean lower bound under nonnegative vertex weights.
Such a statement would compose along the entire block-cut tree.

## 5. Computational checks

Before the proof above was found, the rooted-product inequality was exhaustively checked in the
following finite models:

* `k=3`, all lists chosen among the three-subsets of a five-color palette, for cycles of lengths
  `3` through `6`;
* `k=4`, all lists chosen among the four-subsets of a five-color palette, for cycles of lengths
  `3` through `7`.

In every case the minimum product was exactly the uniform product.  These checks are not used in the
proof, but they are useful guards against a sign or parity error.

## Reference

The path-minimization and equality statements used above are Lemma 3(b,c) of R. Kirov and M. Naimi,
[List coloring and n-monophilic graphs](https://arxiv.org/abs/1004.5183), already developed in this
repository in `Monophilic/PathMinimizing.lean`.

