# List coloring and *n*-monophilic graphs — a Lean 4 formalization

A machine-checked development of Kirov & Naimi, *List coloring and n-monophilic graphs*,
Ars Combinatoria **124** (2016), 329–340 ([arXiv:1004.5183](https://arxiv.org/abs/1004.5183)).

Give each vertex of a graph its own list of `n` permitted colors and count the proper colorings
respecting those lists. A graph is **`n`-monophilic** when that count is minimized by giving every
vertex the *same* list. Kostochka and Sidorenko raised the question in 1990; Kirov and Naimi prove
that every cycle is `n`-monophilic for every `n`, characterize the `2`-monophilic graphs, and
construct, for each `n`, a graph that is `n`-choosable but not `n`-monophilic.

As far as we can determine, **list coloring and choosability have not been formalized in any proof
assistant before**, and Mathlib at the revision targeted here has no chromatic polynomial, no
choosability, no DP-coloring, no chordality, and no Brooks or Vizing. Everything here is built from
`SimpleGraph` and `Finset`.

## Layout

| | |
|---|---|
| `Monophilic/` | the formalization |
| `book/` | a Verso textbook companion (see `book/README.md`) |
| `plan.md` | milestones, design decisions, progress log, and findings |
| `references.md` | verified bibliography, with corrections to the literature |
| `survey.md` | the original scoping report that started the project |

## Building

Toolchain: `leanprover/lean4:v4.32.2`; Mathlib is pinned in `lake-manifest.json`.

```sh
lake exe cache get     # fetch Mathlib oleans (first time only)
lake build             # the formalization
```

For the companion book (Verso `v4.32.0`):

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
| **Theorem 1 — every cycle is `n`-monophilic, every `n ≥ 2`** | ✅ |
| Lemma 5 (cores, as pendant towers) | ✅ |
| Lemma 6 (`K₂,₃` is 2-monophilic) | ✅ |
| **Theorem 2** — the 2-monophilic characterization, *relative to Rubin* | ✅ |
| §5 building block — `K_{n,nⁿ}` is `n`-colourable but not `n`-choosable | ✅ |
| §5 full `H_{n+1}` construction (Lemmas 7–10) | not attempted |

Two dependencies are worth stating plainly. **Rubin's characterization of 2-choosable graphs** is not
formalized here or, as far as we can determine, anywhere else; Theorem 2 is therefore stated with it
as an explicit hypothesis and the classes it names left as abstract propositions, so the borrowed
ingredient is visible in the signature rather than hidden. And **Dirac's theorem** is not needed at
all — Kostochka–Sidorenko is proved in its simplicial-elimination-ordering form, which is what the
argument actually uses.

## Standard of proof

* No `sorry`, `admit`, or `native_decide` anywhere.
* Every headline result depends on exactly the three standard Lean axioms — `propext`,
  `Classical.choice`, `Quot.sound` — verified by `#print axioms`.
* Statements were checked by brute-force evaluation *before* being proved, which repeatedly caught
  indexing and orientation errors that would not have surfaced as type errors. See the
  "Specs verified numerically" section of `plan.md`.
* Every displayed statement in the companion book is an `example` discharged against the real
  theorem, so the prose cannot drift from the proofs.

## Design decisions

The two that shaped everything else:

**Colorings are counted as a `Finset (V → ℕ)`, not via Mathlib's bundled `SimpleGraph.Coloring`.**
The bundled type has no `Fintype` instance at this revision, and it fixes a single color type for
the whole graph, which is exactly wrong when lists vary per vertex. `G.Coloring` survives only as a
bridge to `Colorable` / `chromaticNumber`.

**The chromatic polynomial is not needed.** The natural reading of the literature suggests a
dependency on deletion–contraction and Whitney's broken-cycle theorem. Kirov–Naimi needs the
*number* of colorings, never the polynomial. Dropping that layer removes edge contraction — absent
from Mathlib — from the critical path entirely. Likewise Kostochka–Sidorenko follows from Lemma 1 by
induction along a simplicial elimination ordering, so Dirac's theorem is not needed either.

See `plan.md` for what mechanization turned up: hypotheses that proved load-bearing, hypotheses that
proved unnecessary, and the places where a naive formalization diverges from a correct informal
argument.
