# Formalization log addendum — balanced odd-cycle cores

Date: 2026-08-10

This addendum supersedes the odd-cycle proof route in the first addendum with a stronger theorem.
Merge these IDs into `FORMALIZATION_LOG.md` before handing work to a formalizing agent.

### UM-025 — Balanced coloring core of an odd cycle

**Status:** text proof complete; preferred formalization route for odd-cycle capacity.

**Statement:** for an odd cycle `C`, `k >= 3`, and every `k`-assignment `L`, there is a subset `B`
of the `L`-colorings with

\[
 |B|=P(C,k),\qquad
 |\{f\in B:f(v)=c\}|=P(C,k)/k
\]

for every vertex `v` and every `c in L(v)`.

**Explicit construction:** complete all equality partial matchings to a full DP-cover; normalize all
but the closing matching to the identity, leaving holonomy permutation `sigma`.  A fixed label has
`F` completed-cover colorings and a moved label has `F+1`.  For every moved label `c`, delete the
alternating coloring `c,sigma(c),c,sigma(c),...`.  The deleted colorings use every moved label once
at every vertex, leaving exactly `F=P(C,k)/k` occurrences of every label.

**Full proof:** Theorem 1.1 of `odd_cycle_balanced_core.md`.

### UM-026 — Multi-terminal weighted odd-cycle inequality

**Status:** text proof complete from UM-025 and AM--GM; subsumes UM-023.

**Statement:** for arbitrary nonnegative vertex/color weights,

\[
 \sum_{f\in\operatorname{Colorings}(C,L)}\prod_vw_v(f(v))
 \geq P(C,k)\prod_v\left(\prod_{c\in L(v)}w_v(c)\right)^{1/k}.
\]

**Rooted consequence:** attach `GUR_k` graphs at any number of vertices of an odd cycle.  The
resulting graph is `GUR_k` at any chosen remaining root.  To extract the root-product conclusion,
apply the displayed inequality with an arbitrary test-weight vector `t` at the output root and then
minimize

\[
                 \frac{\sum_ct_cb_c}{k(\prod_ct_c)^{1/k}}
                 =(\prod_cb_c)^{1/k}
\]

over positive `t`; the minimum is achieved at `t_c proportional_to 1/b_c`.

**Full proof:** Theorem 2.1 and Corollary 2.2 of `odd_cycle_balanced_core.md`.

### UM-027 — Cacti with peripheral even cycles

**Status:** text proof complete from UM-020, UM-026, UM-032, UM-034, and UM-036; subsumes UM-022,
UM-024, and the cactus part of UM-037.

**Definition:** in the block-cut tree, take the minimal subtree containing all even-cycle block
nodes.  The even cycles are peripheral when every such marked node has degree at most one in that
subtree—equivalently, no even cycle lies between two other even cycles.

**Statement:** every cactus with peripheral even cycles is uniform-minimal for all `k >= 3`.
Its exact spectrum is:

* forest or one even cycle and no odd cycle: threshold equals chromatic number;
* bipartite with at least two cycles: `nu=tau=3`;
* any odd cycle: `nu=tau=chi=3`.

**Proof:** messages from peripheral even cycles satisfy `GUR`; prune the connecting block-cut
subtree inward.  Combine at cut vertices, transport across bridges, and use UM-026 at odd-cycle
blocks with any number of incident messages.

**Full proof:** Theorem 3.1 and Corollary 3.2 of `odd_cycle_balanced_core.md`.

### Revised sole cactus gateway

After UM-027, the missing local operation is a multi-terminal geometric-capacity inequality for an
**even** cycle.  A balanced-core statement is impossible (some root fibers can be `F-1`), so the
formal target should be stated directly in terms of products/capacity.

