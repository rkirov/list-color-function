# Formalization handoff log: uniform-minimal graph theorems

Last updated: 2026-08-10

This is the rolling handoff document for a future formalizing agent.  Stable IDs should be retained
when statements are refined.  A result marked **text proof complete** has a proof written in the
linked research note, but has not yet been checked in Lean.  A result marked **existing Lean base**
is already present wholly or substantially in the repository and should be reused rather than
reproved.

Notation:

\[
 m_G(k)=P_\ell(G,k),\qquad u_G(k)=P(G,k),
\]

and `G` is **uniform-minimal at `k`** when `m_G(k)=u_G(k)`.

For a rooted graph `(G,r)`, a `k`-assignment `L`, and `c in L(r)`, write

\[
 N_{G,L,r}(c)=\#\{L\text{-colorings }f:f(r)=c\},\qquad
 F_G(k)=u_G(k)/k.
\]

Two new rooted predicates are used below:

* `PUR_k(G,r)`: every root fiber satisfies `N(c) >= F_G(k)`;
* `GUR_k(G,r)`: every assignment satisfies `prod_c N(c) >= F_G(k)^k`.

They satisfy `PUR => GUR => uniform-minimal`.

## A. Existing Lean base or immediate packaging

### UM-001 — Disjoint-union multiplication

**Status:** existing Lean base; exact minimum-function packaging may remain.

**Statement:**

\[
 m_{G\sqcup H}(k)=m_G(k)m_H(k),\qquad
 u_{G\sqcup H}(k)=u_G(k)u_H(k).
\]

In the colorable range, uniform minimality of the union is equivalent to uniform minimality of both
components, and `tau(G disjoint_union H)=max(tau(G),tau(H))`.

**Reuse:** `Monophilic/Sum.lean`, especially `SimpleGraph.col_sum`,
`SimpleGraph.colConst_sum`, and `SimpleGraph.Monophilic.sum`.

**Text proof:** Section 3 of `min_list_coloring_research.md`.

### UM-002 — Pendant multiplication and spectrum invariance

**Status:** monophilicity equivalence is existing Lean base; exact `m_G` identity may remain.

**Statement:** if `G+z` adjoins a leaf, then for `k >= 1`

\[
 m_{G+z}(k)=(k-1)m_G(k),\qquad u_{G+z}(k)=(k-1)u_G(k).
\]

For `k >= 2`, the agreement spectrum is unchanged.

**Reuse:** `Monophilic/Core.lean`, notably `SimpleGraph.monophilic_addPendant_iff`; cone counting
lemmas in `Monophilic/Cone.lean`.

**Text proof:** Section 3 of `min_list_coloring_research.md`.

### UM-003 — Random-sublist inequality

**Status:** text proof complete; literature theorem, likely not yet formalized here.

**Statement:** for `s >= k`, with `n=|V(G)|`,

\[
                         \frac{m_G(k)}{k^n}\leq\frac{m_G(s)}{s^n}.
\]

**Proof dependency:** double-count survival of a coloring under independent random `k`-subsets of
an `s`-assignment.  A finite sum proof avoids probability in Lean.

**Text proof:** Section 5 of `min_list_coloring_research.md`.

### UM-004 — One-deletion shadow identity and monotonicity criterion

**Status:** text proof complete.

**Statement:** for a `(k+1)`-assignment `L` on an `n`-vertex graph, let `partial L` be the multiset
of `k`-assignments obtained by deleting one color at every vertex.  Then

\[
                    \sum_{M\in\partial L}P(G,M)=k^nP(G,L).       \tag{A.1}
\]

If `m_G(k)=u_G(k)` and `e_k(M)=P(G,M)-u_G(k)`, then uniform minimality at `k+1` is equivalent to

\[
 \sum_{M\in\partial L}e_k(M)
   \geq k^nu_G(k+1)-(k+1)^nu_G(k)                               \tag{A.2}
\]

for every `(k+1)`-assignment `L`.

**Text proof:** Section 5 of `min_list_coloring_research.md`.

**Formalization warning:** `partial L` is a multiset indexed by deletion choices, not a set; equal
subassignments must retain multiplicity.

## B. Exact low-color classifications

### UM-010 — Complete spectrum of connected `2`-choosable graphs

**Status:** text proof complete from published/formalized dependencies.

**Statement:** for a connected `2`-choosable graph, after deleting pendant trees:

* a nontrivial tree, even cycle, or `K_{2,3}` core has `nu=tau=2`;
* a `Theta(2,2,2r)` core with `r >= 2` has `nu=tau=3`;
* the isolated vertex has `nu=tau=1`.

**Dependencies:** Rubin classification; cycle and `K_{2,3}` uniform-minimality; the
Kirov--Naimi bad two-list assignment; Allred--Mudrock equality for `Theta(2,2,2r)` at every
`k >= 3`; UM-002.

**Text proof:** Theorem 4.1 of `min_list_coloring_research.md`.

### UM-011 — Full future agreement from agreement at two

**Status:** text proof complete from UM-001 and UM-010.

**Statement:** if `G` is `2`-colorable and `m_G(2)=u_G(2)`, then

\[
                           m_G(k)=u_G(k)\quad\text{for all }k\geq2.
\]

**Text proof:** Corollary 4.2 of `min_list_coloring_research.md`.

## C. Rooted cycle theorems

### UM-020 — Rooted cycle product inequality

**Status:** text proof complete; highest-priority new formalization target.

**Statement:** for `k >= 3`, a rooted cycle `(C_ell,r)`, and every `k`-assignment,

\[
 \prod_{c\in L(r)}N_{C_\ell,L,r}(c)
   \geq\left(\frac{P(C_\ell,k)}k\right)^k.                       \tag{C.1}
\]

If `ell` is odd, the stronger pointwise inequalities

\[
                         N_{C_\ell,L,r}(c)\geq P(C_\ell,k)/k
\]

hold for all root colors.

**Proof dependencies already in repo:** `(k,k-1)` path minimum and equality classification in
`Monophilic/PathMinimizing.lean`; path recurrences; root-fixed coloring counts.

**New proof ingredients:**

1. deleting/fixing the root reduces to the `(k,k-1)` path problem;
2. for an even cycle, every fiber is at least `F-1` and at most one fiber can equal `F-1`;
3. equality forces lists `(S-x)+c` and `(S-y)+c`, `x != y`, along the two root edges;
4. `(J-I)^(ell-4)=beta*J+I` gives exact surplus formulas for every other root color;
5. one other root color has surplus at least `k(k-1)`, making the product at least `F^k`.

**Full proof:** `rooted_cycle_product_proof.md`, Theorem 1.1.

**Sanity checks:** exhaustive palette checks recorded in Section 5 of that note.

### UM-021 — Cycle bouquet theorem and exact spectrum

**Status:** text proof complete from UM-020 and AM--GM.

**Statement:** a graph whose core is a bouquet of cycles is uniform-minimal for all `k >= 3`.
Its exact spectrum is:

* one even cycle: `nu=tau=2`;
* at least two even cycles and no odd cycle: `nu=tau=3`;
* any odd cycle: `nu=tau=3`.

Pendant trees do not change the spectrum.

**Full proof:** `rooted_cycle_product_proof.md`, Theorem 2.1.

### UM-022 — Cacti with at most one even cycle

**Status:** text proof complete.

**Statement:** every cactus with at most one even cycle is uniform-minimal throughout its colorable
range.  In particular, if it contains an odd cycle then `nu=tau=3`.

**Dependencies:** pointwise odd-cycle part of UM-020; UM-002; one-vertex chromatic-polynomial
factorization.

**Full proof:** `rooted_cycle_product_proof.md`, Lemma 3.1 and Theorem 3.2.

## D. Rooted closure calculus

### UM-030 — Rooted hierarchy

**Status:** text proof complete; definitions plus AM--GM.

**Statement:** `PUR_k(G,r) => GUR_k(G,r) => G is uniform-minimal at k`.

**Full proof:** Section 1 of `rooted_uniform_closure_theorems.md`.

### UM-031 — Pointwise rooted dominance for chordal graphs

**Status:** text proof complete; high-value target.

**Statement:** if `G` is chordal and `k >= chi(G)`, then `PUR_k(G,r)` holds for every root `r`.

**Proof:** choose a perfect elimination ordering ending at the prescribed root; fix the root color
and greedily color in reverse order.  The lower product is exactly the uniform root fiber.

**Dependencies:** existence of a PEO ending at any prescribed vertex; existing chordal/SEO APIs.

**Full proof:** Lemma 2.1 and Theorem 2.2 of `rooted_uniform_closure_theorems.md`.

### UM-032 — Attaching a pointwise-dominant block

**Status:** text proof complete.

**Statement:** let `A` and `B` meet only at `x`, with `PUR_k(B,x)`.  For any root `r` in `A`, the
attachment preserves `PUR_k(A,r)` and preserves `GUR_k(A,r)`.

**Proof idea:** every coloring of `A` has at least `P(B,k)/k` extensions, independently of its color
at `x`.

**Full proof:** Theorem 3.1 of `rooted_uniform_closure_theorems.md`.

### UM-033 — Chordal/odd-cycle block classification

**Status:** text proof complete from UM-020, UM-031, and UM-032.

**Statement:** if every block of `G` is chordal or an odd cycle, then `PUR_k(G,r)` holds for every
root and every `k >= chi(G)`.  Hence `nu=tau=chi`.

**Full proof:** Corollary 3.2 of `rooted_uniform_closure_theorems.md`.

### UM-034 — Geometric rooted one-sum closure

**Status:** text proof complete.

**Statement:** the one-vertex sum of two `GUR_k` rooted graphs is again `GUR_k` at the common root.

**Proof:** rooted profiles multiply coordinatewise, so their products multiply.

**Full proof:** Theorem 4.1 of `rooted_uniform_closure_theorems.md`.

### UM-035 — Complementary-sum product inequality

**Status:** text proof complete; standalone algebra lemma.

**Statement:** for nonnegative `h_1,...,h_k` and `S=sum h_i`,

\[
                         \prod_i(S-h_i)\geq(k-1)^k\prod_i h_i.
\]

**Proof:** apply AM--GM separately to every complementary sum and multiply.

**Full proof:** Lemma 5.1 of `rooted_uniform_closure_theorems.md`.

### UM-036 — Transporting `GUR` across a bridge

**Status:** text proof complete from UM-035.

**Statement:** if `(H,v)` is `GUR_k`, adjoining a new leaf `r` at `v` and using `r` as the new root
produces another `GUR_k` rooted graph.  Thus geometric dominance transports along arbitrary paths.

**Existing infrastructure:** `SimpleGraph.colFix`, `colAvoid`, and bridge decompositions in
`Monophilic/Bridge.lean`; pendant graph construction in `Monophilic/Path.lean`.

**Full proof:** Theorem 5.2 of `rooted_uniform_closure_theorems.md`.

### UM-037 — Trees of cycle bouquets: complete classification

**Status:** text proof complete from UM-020, UM-034, and UM-036.

**Graph class:** start with a tree; at its vertices glue arbitrary bouquets of cycles; then attach
arbitrary pendant trees.

**Statement:** every such graph is uniform-minimal for all `k >= 3`, and is `GUR_k` when rooted on
the underlying tree.  Exact spectrum:

* forest or a single even-unicyclic component: threshold equals chromatic number;
* at least two even cycles and no odd cycle: `nu=tau=3`;
* any odd cycle: `nu=tau=3`.

This includes every cactus with at most two cycles.

**Full proof:** Theorem 6.1 and Corollary 6.2 of `rooted_uniform_closure_theorems.md`.

## E. Clique operations

### UM-040 — Dominating-clique join shift

**Status:** text proof complete.

**Statement:** if `G` is uniform-minimal at `k`, then

\[
                         K_t\mathbin{\mathrm{join}}G
\]

is uniform-minimal at `k+t`.  Consequently

\[
 \nu(K_t\mathbin{\mathrm{join}}G)\leq\nu(G)+t,
 \qquad
 \tau(K_t\mathbin{\mathrm{join}}G)\leq\tau(G)+t.
\]

**Proof:** greedily color the clique in at least `(k+t)_t` ways; delete its `t` colors from the lists
on `G`, choose `k`-sublists, and invoke uniform minimality of `G`.

**Full proof:** Theorem 7.1 of `rooted_uniform_closure_theorems.md`.

### UM-041 — Rooted cone strengthening

**Status:** text proof complete; corollary of the UM-040 argument.

**Statement:** if `G` is uniform-minimal at `k`, then its cone `K_1 join G` satisfies
`PUR_{k+1}` at the universal apex.

**Full proof:** final paragraph of Section 7 in `rooted_uniform_closure_theorems.md`.

## F. Proven reductions on a hypothetical monotonicity counterexample

### UM-050 — Minimal counterexample restrictions

**Status:** text proof complete, using published eventual bounds.

If `G` is uniform-minimal at `k >= chi(G)` but not at `k+1`, a counterexample can be chosen with:

* `k >= 3`;
* `G` connected and of minimum degree at least two;
* `k >= chi_ell(G)`;
* `|E(G)| >= k+3`, by the Dong--Zhang bound;
* `u_G(k+1)/(k+1)^n > u_G(k)/k^n`;
* a minimizing `(k+1)`-assignment violating the shadow-excess inequality UM-004.

**Text proof:** Section 6 of `min_list_coloring_research.md`.

## G. Open statements — do not send as proved

### OPEN-001 — Global uniform-minimality monotonicity

If `k >= chi(G)` and `m_G(k)=u_G(k)`, prove `m_G(k+1)=u_G(k+1)`.  Equivalently `nu(G)=tau(G)`.

### OPEN-002 — Theta threshold conjecture

Every theta graph has `tau <= 3`.  Mixed-parity theta graphs and `Theta(2,2,2r)` are already covered
by known results; the remaining same-parity family is open in these notes.

### OPEN-003 — Full cactus threshold conjecture

Every cactus is uniform-minimal for all `k >= 3`.

### OPEN-004 — Two-terminal cycle-capacity inequality

For the fixed-terminal cycle matrix `M_{x,y}` and every nonnegative vector `h`, prove

\[
 \left(\prod_d\sum_ch_cM_{x,y}(c,d)\right)^{1/k}
 \geq\frac{P(C,k)}k\left(\prod_ch_c\right)^{1/k}.
\]

This would imply OPEN-003 by transporting `GUR_k` through internal cycle blocks.  Random finite tests
have found no counterexample, but there is not yet a proof.

### OPEN-005 — Rooted characterization

Determine whether every graph uniform-minimal at `k >= 3` is `GUR_k` at every root.  A positive
answer would make uniform-minimal graphs closed under one-vertex sums and would greatly simplify a
complete classification.  This has only computational support in the examples checked so far.

## H. Suggested formalization order

1. Define root profiles, `PUR_k`, and `GUR_k`; prove UM-030.
2. Formalize the elementary algebra/closure layer UM-032, UM-034, UM-035, UM-036.
3. Prove rooted chordal dominance UM-031 and block theorem UM-033.
4. Formalize the rooted cycle theorem UM-020, reusing `PathMinimizing.lean` aggressively.
5. Obtain UM-021, UM-022, and UM-037 as short compositional corollaries.
6. Formalize the clique-join shift UM-040/041.
7. Only then attack OPEN-004; it is the cleanest current gateway to the full cactus classification.

