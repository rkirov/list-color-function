# Formalization log addendum — odd-cycle capacity

Date: 2026-08-10

This addendum extends `FORMALIZATION_LOG.md`.  It partially resolves `OPEN-004` there.  Retain the
stable IDs below when merging the files.

### UM-023 — Two-terminal capacity of an odd cycle

**Status:** text proof complete; new high-priority formalization target.

**Statement:** let `C` be an odd cycle with distinct terminals `x,y`, let `M(c,d)` count list
colorings with terminal colors fixed to `c,d`, and let `k >= 3`.  For every `k`-assignment and every
nonnegative vector `h`,

\[
 \prod_d\left(\sum_ch_cM(c,d)\right)
   \geq\left(\frac{P(C,k)}k\right)^k\prod_ch_c.                  \tag{A.1}
\]

Equivalently, the matrix-scaling capacity of `M` is at least the uniform root fiber.

**Proof skeleton:**

1. split the odd cycle into an even and an odd terminal path;
2. complete every equality partial matching along each path to a permutation matching;
3. the completed path matrix is `D_s J + (-1)^s R`;
4. their Hadamard product has row/column sums `F` on fixed points of the relative permutation and
   `F+1` elsewhere;
5. subtract a partial identity on the nonfixed indices, leaving a nonnegative matrix with every row
   and column sum exactly `F=P(C,k)/k`;
6. divide by `F` and apply weighted AM--GM to the resulting doubly stochastic matrix;
7. restore the deleted/artificial edges by entrywise monotonicity.

**Full proof:** Theorem 3.1 of `odd_cycle_capacity_and_cacti.md`.

**Formalization dependencies:** finite matrices indexed by endpoint lists; permutation completion of
partial matchings; the existing path recurrence formulas.  A direct Finset weighted-AM--GM proof may
be easier than importing matrix-scaling terminology.

### UM-024 — Cacti with at most two even cycles

**Status:** text proof complete from UM-020, UM-023, UM-032, UM-034, and UM-036.

**Statement:** every cactus with at most two even cycle blocks is uniform-minimal for all `k >= 3`.
Its exact colorable-range spectrum is:

* forest or one even cycle and no odd cycle: threshold equals chromatic number;
* exactly two even cycles and no odd cycle: `nu=tau=3`;
* any odd cycle: `nu=tau=chi=3`.

**Proof:** follow the unique block-cut-tree path between the two even cycles.  Off-path components
have only chordal/odd-cycle blocks and are pointwise dominant.  Transport a geometric profile from
the first even cycle across bridges and odd cycles, then combine it with the second rooted even-cycle
profile.

**Full proof:** Theorem 4.1 and Corollary 4.2 of `odd_cycle_capacity_and_cacti.md`.

### Revised open gateway

The broad odd-cycle case of `OPEN-004` is now UM-023.  The remaining cactus gateways are:

* **OPEN-004E:** the two-terminal capacity inequality for even cycles;
* **OPEN-004M:** a multi-terminal capacity inequality for an odd cycle with independently weighted
  attachments at three or more vertices.

Together they would prove uniform minimality of every cactus for all `k >= 3`.

