# List coloring and enumeratively chromatic-choosable graphs — a Lean 4 formalization

[![CI](https://github.com/rkirov/list-color-function/actions/workflows/ci.yml/badge.svg)](https://github.com/rkirov/list-color-function/actions/workflows/ci.yml)

📖 **[Read the companion book](https://rkirov.github.io/list-color-function/)**

A machine-checked development of Kirov & Naimi, *List coloring and n-monophilic graphs*,
Ars Combinatoria **124** (2016), 329–340 ([arXiv:1004.5183](https://arxiv.org/abs/1004.5183)).

Give each vertex of a graph its own list of `n` permitted colors and count the proper colorings
respecting those lists. A graph is **enumeratively chromatic-choosable at `n`** when that count is
minimized by giving every vertex the *same* list. Kostochka and Sidorenko raised the question in
1990; Kirov and Naimi prove that every cycle is enumeratively chromatic-choosable at `n` for every
`n`, characterize the graphs that are enumeratively chromatic-choosable at `2`, and construct, for
each `n`, a graph that is `n`-choosable but not enumeratively chromatic-choosable at `n`.

**A note on the name.** Kirov and Naimi call this property "`n`-monophilic". The name the literature
settled on is *enumeratively chromatic-choosable* (Kaul et al., Involve **16** (2023) 849–882;
Allred–Mudrock, [arXiv:2505.05662](https://arxiv.org/abs/2505.05662); Chi et al.,
[arXiv:2605.10861](https://arxiv.org/abs/2605.10861)), and that is the name used throughout this
development: `SimpleGraph.ECCAt G n` for the property at one `n`, and `SimpleGraph.ECC G` for
`∀ n, G.ECCAt n`. `provenance.md` §4 records the history, the relation to Ohba's
*chromatic-choosable*, and the invariants `ν(G)` and `τ(G)` the modern papers state things with.

As far as we can determine, **list coloring and choosability have not been formalized in any proof
assistant before**, and Mathlib at the revision targeted here has no chromatic polynomial, no
choosability, no DP-coloring, no chordality, and no Brooks or Vizing. Everything here is built from
`SimpleGraph` and `Finset`.

## Layout

| | |
|---|---|
| `ListColoring/` | the formalization |
| `Cacti/` | the cactus classification — beyond the paper, see below |
| `OpenProblems.lean` | Kirov–Naimi §6's two open questions, stated in Lean and asserted with `sorry` |
| `formalization.yaml` | machine-readable map: every numbered result of the paper → its Lean name, file, and status |
| `book/` | a Verso textbook companion (see `book/README.md`) |
| `plan.md` | milestones, design decisions, progress log, and findings |
| `references.md` | verified bibliography, with corrections to the literature |
| `provenance.md` | **credit ledger** — which theorem in which paper each result is, and what is not claimed |
| `survey.md` | the original scoping report that started the project |

## Building

Toolchain: `leanprover/lean4:v4.33.0`; Mathlib is pinned in `lake-manifest.json`.

```sh
lake exe cache get     # fetch Mathlib oleans (first time only)
lake build             # the formalization
```

For the companion book (Verso `v4.33.0`):

```sh
cd book
lake build                                                     # checks every example in the text
lake env lean --run Main.lean --output _out --depth 2 --without-tex
python3 -m http.server 8000 --directory _out/html-multi        # Verso needs a server, not file://
```

Two notes carried over from development, both recorded in `plan.md`:

* The book deliberately declares **no `lean_exe`** — linking a native binary that imports Mathlib
  forces compiling all of Mathlib to object code (~2700 jobs, several GB). Hence the interpreted
  `lake env lean --run` invocation above.
* On the machine this was developed on, `.lake/packages` was a symlink into a sibling Mathlib
  checkout to save disk. That is a purely local optimisation, is `.gitignore`d, and is not needed
  for a fresh clone.

## What is proved

| Paper result | |
|---|---|
| Lemma 1 (cone over a clique) | ✅ |
| Kostochka–Sidorenko — every graph with a simplicial elimination ordering | ✅ |
| Lemma 2 (list swap → nested lists) | ✅ |
| Lemma 3(a),(b),(c) — the `A_k`/`B_k` recurrences and minimizing assignments | ✅ |
| Lemma 4 (strict monotonicity on paths) | ✅ |
| **Theorem 1 — every cycle is enumeratively chromatic-choosable at `n`, every `n ≥ 2`** | ✅ |
| Lemma 5 (cores, as pendant towers) | ✅ |
| Lemma 6 (`K₂,₃` is enumeratively chromatic-choosable at `2`) | ✅ |
| **Theorem 2** — the characterization of the graphs enumeratively chromatic-choosable at `2`, unconditionally | ✅ |
| §5 building block — `K_{n,nⁿ}` is `n`-colourable but not `n`-choosable | ✅ |
| §5 Lemmas 7, 8, 9, 10 and the full `H_{n+1}` construction | ✅ |
| **§5's conclusion at every list size `k ≥ 2`** — a graph that is `k`-choosable but not enumeratively chromatic-choosable at `k` | ✅ |

**One erratum in the paper, at `n = 1`.** Lemmas 7 and 10 of §5 are stated "for all `n ≥ 1`", i.e.
down to list size `2`. Lemmas 7, 9 and 10 are all false there, and
`ListColoring/Section5.lean` therefore assumes `2 ≤ n` throughout. The reason is structural: `p` is
defined as the least integer with `nᵖ > x^{n²}`, which at `n = 1` reads `1 > x` with
`x = col(K_{1,1}, L_j) = 2` — no such `p` exists, so `H₂` is not defined. Take any `p` anyway and
`v₁` is joined to both ends of the single edge of `G_{1,1} = K_{1,1}`, so `H₂` contains a triangle;
then `col(H₂, 2) = 0 < 2 = col(H₂, L)`, which is Lemma 7's inequality reversed, and `H₂` is not
`2`-colourable, so it is not `2`-choosable either. All three failures are `#guard`s at the foot of
that file. The paper's conclusion is unaffected: list size `2` is witnessed instead by `θ_{2,2,4}`,
`2`-choosable by Rubin and not enumeratively chromatic-choosable at `2` by the paper's own Figure 2
— both already proved here, and combined in
`SimpleGraph.KN5.exists_choosable_not_ecc_of_two_le`. This is the only error found in Kirov–Naimi;
`provenance.md` §3 records it, along with the rather longer list of claims of *ours* that were
refuted.

One dependency is worth stating plainly. **Rubin's characterization of 2-choosable graphs** (A. L.
Rubin, in Erdős–Rubin–Taylor 1980, pp. 131–134) had not, as far as we can determine, been formalized
anywhere. It is proved here, in both directions — `ListColoring.rubinTheorem` — out of
`choosable_two_of_rubinFamily` (⟸), the generalized-theta classification
`choosable_two_gtheta_iff` (arbitrary arity), the dumbbell case `not_choosable_two_of_dumbbell`,
Rubin's steps 4–6 (`rubin_structure`) and the core extraction (`hasCore`). It is a theorem from
1980; none of the mathematics is ours.

Kirov–Naimi's Theorem 2 is stated in `ListColoring/Theorem2.lean` with `RubinTheorem` as its first
explicit argument and the core alternatives as **real definitions** rather than abstract
propositions; `ListColoring.ecc_two_iff` supplies that argument, so Theorem 2 now assumes
nothing beyond connectivity. (The two live in different files only because everything Rubin's
theorem is proved from imports `ListColoring/Theorem2.lean`.)

## Beyond the paper: the cactus classification

`Cacti/` proves a result that is not in Kirov–Naimi and, as far as we know, not in the literature:
**the complete enumerative-chromatic-choosability spectrum of a cactus.** A *cactus* is a connected
graph in which any two cycles sharing an edge are the same cycle.

> A cactus is enumeratively chromatic-choosable — at *every* list size — iff it has at most one
> cycle or contains an odd cycle. (`ListColoring.isCactus_ecc_iff`)

The content is in the three cases, all proved with no `sorry`:

| | |
|---|---|
| `k = 2` | `isCactus_ecc_two_iff` — the classification, through Theorem 2 and Rubin above |
| `k ≥ 4` | `isCactus_ecc_of_four_le` — a block induction on the pair invariant `A² ≤ x_c·x_d`, with the slack `k - 3 ≥ 1` paying for the weight peeling |
| `k = 3` | `isCactus_ecc_three` — the pair invariant is *false* here, so the induction carries GM dominance instead; the even-cycle block is a tensor capacity argument (`Cacti/RefTensor.lean` through `Cacti/LargeBranch.lean`) split into `C₄`, `C₆` and every longer cycle |

This is the result of a 2026-08 AI research collaboration on this repository, not of the paper;
the source of record is `ai_research_notes/FINAL_CACTI_ECC_HANDOFF.md`. Three things the notes
had wrong were caught by formalizing them: a reported gap in the non-identity budget was an
`m ≥ 4` argument misapplied at `m = 3`; the strict factor the path cone actually supplies is
`(729/256)ⁿ`, not the stronger constant the `C₆` note quotes, so that section's arithmetic is not
what the proof runs on; and the residual table's four rows are three instances of one law.
`Cacti/` imports `ListColoring/` and is never imported by it.

## Standard of proof

* No `sorry`, `admit`, or `native_decide` anywhere in `ListColoring/` or `Cacti/`, checked by CI.
  The three `sorry`s in the repository are all in `OpenProblems.lean`, which is a **separate
  `lean_lib`** for exactly that reason: it imports `ListColoring` and nothing imports it, so no
  theorem can rest on an unproved statement. A `sorry` there means *nobody knows* — those are
  §6's open questions, not gaps in the formalization of the paper.
* Every headline result depends on exactly the three standard Lean axioms — `propext`,
  `Classical.choice`, `Quot.sound` — enforced by the comparator's `permitted_axioms`.
* Statements were checked by brute-force evaluation *before* being proved, which repeatedly caught
  indexing and orientation errors that would not have surfaced as type errors. See the
  "Specs verified numerically" section of `plan.md`.
* CI runs the real [leanprover/comparator](https://github.com/leanprover/comparator) against
  `comparator/Challenge.lean`, which claims **thirteen keystone theorems** — ten from the paper
  and three of the cactus classification — and the definitions needed to state them — deliberately not the whole library, so that what is certified is legible.
  That checks three things an axiom audit cannot: that the statements really are the ones claimed,
  that only the permitted axioms are used, and that every proof replays through two independent
  kernels (Lean's, via `lean4export`, and `nanoda`). It is CI-only — it builds four external tools.
* Every displayed statement in the companion book is an `example` discharged against the real
  theorem, so the prose cannot drift from the proofs.

## Design decisions

The two that shaped everything else:

**Colorings are counted as a `Finset (V → ℕ)`, not via Mathlib's bundled `SimpleGraph.Coloring`.**
The bundled type has no `Fintype` instance at this revision, and it fixes a single color type for
the whole graph, which is exactly wrong when lists vary per vertex. `G.Coloring` survives only as a
bridge to `Colorable` / `chromaticNumber`.

**Kirov–Naimi does not need the chromatic polynomial.** The natural reading of the literature
suggests a dependency on deletion–contraction and Whitney's broken-cycle theorem, but the paper
needs the *number* of colorings, never the polynomial. Dropping that layer kept edge contraction —
absent from Mathlib — off the critical path. The polynomial is nevertheless built here, separately,
in `ListColoring/ChromaticPolynomial.lean` via the Whitney subset expansion, so that
`ecc_iff_listColorFunction_eq_eval` can say `P_ℓ(G,n) = P(G,n)` with a genuine polynomial on
the right. Likewise Kostochka–Sidorenko needs only a simplicial elimination ordering, so **Dirac's
theorem is not on its critical path** — though it is proved here anyway, as
`isChordal_iff_exists_cliqueTower`.

See `plan.md` for what mechanization turned up: hypotheses that proved load-bearing, hypotheses that
proved unnecessary, and the places where a naive formalization diverges from a correct informal
argument.
