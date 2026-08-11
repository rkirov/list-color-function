# Provenance — who proved what

`references.md` is the bibliography. **This file is the credit ledger**: for every headline result in
the formalization, which theorem in which paper it is, or — where that is the honest answer — that it
is not in the literature at all.

The rule this project follows:

> **Every top-level theorem carries its attribution in its docstring.** A result that is *not* from
> the literature says so explicitly. Nothing is left for a reader to infer from context.

Formalizing a known theorem is not a mathematical contribution and is not presented as one. What is
new here is the mechanization, and — separately and much more modestly — a handful of findings listed
in §3 that only surfaced because a machine insisted on the details.

---

## 1. Theorems formalized from the literature

These are known results. The Lean proof is ours; the mathematics is not.

| Lean name | Result | Credit |
|---|---|---|
| `SimpleGraph.eval_chromaticPolynomial` | the Whitney subset expansion evaluates to the colouring count | **Whitney 1932**; Birkhoff 1912 for the polynomial itself |
| `SimpleGraph.ecc_iff_listColorFunction_eq_eval` | enumeratively chromatic-choosable at `n` (`n`-monophilic) ⟺ `P_ℓ(G,n) = P(G,n)` | definitional bridge; the notions are **Kostochka–Sidorenko 1990/92** and **Kirov–Naimi 2016** |
| `SimpleGraph.ERT.not_choosable`, `ERT.colorable` | `K_{n,nⁿ}` is `n`-colourable but not `n`-choosable | **Erdős–Rubin–Taylor 1980**; also Kirov–Naimi §5 |
| `SimpleGraph.ecc_of_isChordal`, `SimpleGraph.IsChordal.ecc` | chordal ⟹ enumeratively chromatic-choosable at every `n` | **Kostochka–Sidorenko 1990/92**; = Thm 2(i) of Chi et al. 2026 |
| `SimpleGraph.isChordal_iff_exists_cliqueTower` | chordal ⟺ has a simplicial elimination ordering | **Dirac 1961**; Fulkerson–Gross 1965 |
| `ListColoring.ecc_closePath_of_two_le`, `ListColoring.closePath_ecc` | **every cycle is enumeratively chromatic-choosable, every `n ≥ 2`** | **Kirov–Naimi 2016, Theorem 1**; = Thm 2(ii) of Chi et al. 2026 |
| `ListColoring.choosable_two_of_rubinFamily` | a vertex / even cycle / `θ_{2,2,2m}` is 2-choosable | **Rubin**, in Erdős–Rubin–Taylor 1980 — the *easy* direction |
| Theorem 2 (`ecc_two_iff…`) | connected `G` is enumeratively chromatic-choosable at `2` (the paper's "2-monophilic") ⟺ core is a vertex, a cycle, `K₂,₃`, or `G` has an odd cycle | **Kirov–Naimi 2016, Theorem 2**; = Thm 2(iv) of Chi et al. 2026, there attributed to [1, 6, 13, 16, 17] |
| `SimpleGraph.KN5.not_ecc`, `KN5.choosable`, `KN5.exists_choosable_not_ecc` | `H_{n+1}` is `(n+1)`-choosable but not enumeratively chromatic-choosable at `n+1`, for `n ≥ 2` | **Kirov–Naimi 2016, §5**, Lemmas 7 and 10 |
| `SimpleGraph.KN5.left_disjoint`, `KN5.left_card_eq`, `KN5.badColor_unique` | the two structural facts about `n`-lists on `K_{n,nⁿ}` with no colouring, and the uniqueness of a killing colour | **Kirov–Naimi 2016, §5**, Lemmas 8 and 9 |
| `SimpleGraph.KN5.exists_choosable_not_ecc_of_two_le` | for **every** list size `k ≥ 2`, a graph that is `k`-choosable but not enumeratively chromatic-choosable at `k` | **Kirov–Naimi 2016, §5**; the `k = 2` case is `θ_{2,2,4}`, not their `H₂` — see §3 |
| `SimpleGraph.exists_ecc_forall_ge` | `P_ℓ(G,m) = P(G,m)` for all large `m` | **Donner 1992**; threshold via **Wang–Qian–Yan 2017** |
| `SimpleGraph.ecc_of_two_pow_lt` | explicit threshold `2^{\|E(G)\|} < m` | weaker form of **Wang–Qian–Yan 2017**; superseded by **Dong–Zhang 2023** (`m ≥ \|E(G)\| − 1`) |
| Lemmas 1–6 | the supporting lemmas | **Kirov–Naimi 2016**, numbered as in the paper |

### Rubin's theorem

**Rubin's theorem** (A. L. Rubin, in **Erdős–Rubin–Taylor**, *Choosability in graphs*,
Congr. Numer. **26** (1980), 125–157): *a connected graph is 2-choosable iff its core is a single
vertex, an even cycle, or `θ_{2,2,2m}` for some `m ≥ 1`.* Kirov–Naimi cite it; it is **proved here**
(`ListColoring.rubinTheorem`), so Theorem 2 carries no hypothesis
(`ListColoring.ecc_two_iff`).

| piece | Result | Credit |
|---|---|---|
| ⟸ | the three families are 2-choosable (`choosable_two_of_rubinFamily`) | **Rubin** — **proved** |
| 5 | `Θ(k₁,…,k_n)` is 2-choosable ⟺ `n = 3` and shape `(2,2,even)`, **arity arbitrary** (`choosable_two_gtheta_iff`) | a component of **Rubin's theorem**; as a statement it is a corollary of it. Proved here directly from list assignments, so it can feed the proof of Rubin without circularity — **proved** |
| 1 | core reduction, `G` 2-choosable ⟺ its core is (`choosable_iff_of_coreIs`) | standard, part of **Rubin's** argument — **proved** |
| 2 | every connected finite graph has a core (`hasCore`) | standard, assumed without proof wherever "the core" is used — **proved** |
| 3 | a **dumbbell** — two cycles joined by a path — is not 2-choosable (`not_choosable_two_of_dumbbell`) | standard, part of **Rubin's** argument — **proved** |
| 4–6 | shortest cycle `C₁` plus a shortest edge-disjoint path `P₁` between two of its vertices: `C₁` is a 4-cycle, `P₁` is even, and no edge lies outside `C₁ ∪ P₁` (`rubin_structure`) | **Rubin**, pp. 131–134 (his steps 4, 5, 6) — **proved** |
| ⟹ | assembly: core, structure, and the two isomorphism constructions (`rubinTheorem`) | **Rubin** — **proved** |

The structural theorem for 2-connected non-cycles that an earlier plan routed through is **not**
established here, and is not needed: Rubin's own steps 4–6 replace it. The refutations that killed
that route are recorded in §3 below and in the module docstring of `ListColoring.Rubin`.

**None of this is novel.** It is a theorem from 1980 that appears not to have been machine-checked before.

## 2. Theorems in the literature that this project does *not* claim

Listed so no reader mistakes an absence for a claim.

* **Chi, Lee, Morrissette, Mudrock, Nguyen, Whatley (arXiv:2605.10861, 2026), Theorem 4** —
  `Θ(l₁,l₂,l₃)` with `l₂,l₃ ≥ 2` is *not* enumeratively chromatic-choosable iff `l₁,l₂,l₃` all have
  the same parity and `{l₁,l₂,l₃} ≠ {2}`. **Not formalized.** Note this is a *different* statement
  from the generalized-theta classification above: it is about `P_ℓ = P` at every `m` (a counting
  property) for three arms, whereas ours is about 2-choosability (an existence property) for
  arbitrary arity. Their proof uses DP-coloring, which is not formalized here either.
* **Chi et al., Theorem 2(iii)** — `Θ(l₁,l₂,l₃)` is enumeratively chromatic-choosable when `l₁` has
  a different parity from both `l₂` and `l₃` (Halberg–Kaul–Liu–Mudrock–Shin–Thomason 2024;
  Bui–Kaul–Maxfield–Mudrock–Shin–Thomason 2023). **Not formalized.**
* **Dong–Zhang 2023** — the sharp threshold `m ≥ |E(G)| − 1`. **Not formalized**; we prove a weaker
  exponential bound.
* **Kirov–Naimi's §3 remark** that for `n = 2` a minimizing list assignment on a path need not be of
  type A or type B ("examples are easy to construct"). **Not formalized.**
* **Kirov–Naimi §6, Question 1's negative answer at `n = 2`** — that `P₂ □ P₃` is not
  `2`-monophilic while every path is. A corollary of Theorem 2 rather than a separate argument.
  **Stated but not proved**, as `ListColoring.OpenProblem.not_ecc_two_boxProd_path_two_three`.
* **Kirov–Naimi §6, Questions 1 and 2** — both **open**, and stated as such in `OpenProblems.lean`.
  A `sorry` there means nobody knows, not that a proof is missing here; the file is a separate
  `lean_lib` precisely so that no theorem can rest on one. Question 2 is the modern `ν = τ`
  question recorded in §4 below.

## 3. Not from the literature

Nothing here is a mathematical advance. These are artifacts of mechanization, recorded because they
are the parts a reader could not get from the papers.

* **The formalization itself.** As far as we can determine, list coloring and choosability had not
  been formalized in any proof assistant before this project.
* **A Mathlib `TODO` discharged.** *A graph that is not 2-colourable contains an odd cycle* is listed
  as an open `TODO` in Mathlib's `Combinatorics/SimpleGraph/Bipartite.lean` at the pinned revision.
  Theorem 2's converse needs it, so it is proved here —
  `ListColoring.exists_odd_isCycle_of_odd_closed_walk` (strong induction on walk length: rotate to a
  repeated vertex, cut at its second visit, and one of the two shorter closed walks is odd) plus the
  bridge from Mathlib's `cycleGraph` to `closePath`. Classical mathematics, but a genuine and
  reusable gap in the library rather than a fact about this project. Worth upstreaming.
* **`ListColoring.const_block`, `armBlockLists_forced`, `alt_chain`** (`ThetaClass.lean`) — the
  induction along an arm of unbounded length. The informal proofs say "it is then easy to check";
  these lemmas are what that phrase expands to. Presentation, not mathematics.
* **Lemma 3(c) fails at `k = 0`.** Kirov–Naimi's hypothesis "path of length at least one" is
  load-bearing, not decorative — machine-checked witness in `plan.md`. This *confirms* the paper.
* **`ThetaAlternative` was false.** An auxiliary hypothesis invented *in this repository* to split
  Rubin's theorem into a structural half and a colouring half. `K₂,₄` refutes it. It has been
  deleted. This is a defect in our scaffolding and **not** an error in Kirov–Naimi, which cites
  Rubin's theorem rather than proving it. Recorded in `plan.md`.
* **Three further structural claims of ours, all refuted.** Recorded because the *shape* of the
  mistake repeated: **`contains` and `is` are not interchangeable here**, and neither is
  "a theta" and "a *bad* theta".
  * *connected, min degree `≥ 2`, not a cycle ⟹ **contains** a theta subgraph* — **false**: the
    **bowtie** (two triangles sharing a vertex) contains no theta at all. And useless even where it
    holds, since the theta produced may be a *good* one, and good thetas are 2-choosable.
  * *connected, min degree `≥ 2`, not a cycle ⟹ **is** a generalized theta, or contains two cycles
    meeting in ≤ 1 vertex* — **false**, refuted by `K₃,₃ − e` on six vertices; 4,162 of the 129,073
    bipartite 2-connected non-cycle graphs on `≤ 9` vertices satisfy neither branch. (Note the *is*:
    under a `contains` reading `K₃,₃ − e` refutes nothing, since it contains both `θ(1,3,3)` and
    `θ(2,2,2)` — which is precisely why containment is the wrong predicate.)
  * *two cycles meeting in at most one vertex are not 2-choosable* — **false** without a connecting
    path, since two **disjoint** even cycles are 2-choosable.

  All are defects in this repository's scaffolding; none appears in Kirov–Naimi. `plan.md` records
  a corrected three-branch alternative, which is **empirical and unproved**.
* **`ListColoring.not_choosable_two_of_dumbbell`** — two cycles joined by a path are not 2-choosable.
  A standard step of Rubin's argument, proved here. Mildly notable: it needs **no parity case
  split**, because the forcing chain kills a prescribed colour at a cycle's base point regardless
  of the cycle's parity.
* **One error found in Kirov–Naimi: §5's Lemmas 7, 9 and 10 fail at `n = 1`.** The paper states
  Lemmas 7 and 10 "for all `n ≥ 1`" — i.e. down to list size `2` — and §5's opening sentence claims
  the construction for each `n ≥ 2` in the `H_n` indexing. It does not reach the bottom case:
  * `p` is the least integer with `nᵖ > x^{n²}`, which at `n = 1` reads `1 > x` with
    `x = col(K_{1,1}, L_j) = 2`. **No such `p` exists**, so `H₂` is not defined.
  * For any `p` whatsoever, `v₁` is joined to both ends of the single edge of `G_{1,1} = K_{1,1}`,
    so `H₂` contains a **triangle**. Then `col(H₂, 2) = 0 < 2 = col(H₂, L)` — Lemma 7's inequality
    reversed — and `H₂` is vacuously enumeratively chromatic-choosable at `2` by the paper's own
    fact (2); not being `2`-colourable it is not `2`-choosable, so Lemma 10 fails as well.
  * Lemma 9 fails independently at `n = 1`: `K_{1,1}` with both lists `{0,1}` has **two** colours
    whose deletion destroys every colouring, not at most one.

  All three are machine-checked `#guard`s in `ListColoring/Section5.lean`, which assumes `2 ≤ n`
  throughout. **The paper's conclusion survives**: at list size `2` the witness is `θ_{2,2,4}`,
  which is `2`-choosable by Rubin's theorem and not enumeratively chromatic-choosable at `2` by
  Kirov–Naimi's own Figure 2 — both proved here, and `SimpleGraph.KN5.exists_choosable_not_ecc_of_two_le`
  assembles the two ranges into the statement for every `k ≥ 2`. The defect is in the stated range
  of three lemmas, not in the theorem they serve.

  This is the **only** error found in the paper. Every other refuted claim in this project has been
  one of ours — see the four above.

## 4. A note on the name

Kirov–Naimi's "`n`-monophilic" is the pointwise property `P_ℓ(G,n) = P(G,n)` at one `n`. The term
that has since taken hold is **enumeratively chromatic-choosable**, first formally defined in Kaul
et al., *Bounding the list color function threshold from above*, Involve **16** (2023) 849–882.

Allred and Mudrock, *Enumerative Chromatic Choosability* ([arXiv:2505.05662](https://arxiv.org/abs/2505.05662)),
give the precise vocabulary, built on two invariants:

* **`ν(G)`**, the *list color function number* — the smallest `t ≥ χ(G)` with `P_ℓ(G,t) = P(G,t)`.
* **`τ(G)`**, the *list color function threshold* — the smallest `k ≥ χ(G)` such that
  `P_ℓ(G,m) = P(G,m)` for **every** `m ≥ k`. Always `χ(G) ≤ χ_ℓ(G) ≤ ν(G) ≤ τ(G)`.

| term | definition | |
|---|---|---|
| **enumeratively chromatic-choosable** | `τ(G) = χ(G)` | agreement at every `m` |
| **weakly enumeratively chromatic-choosable** | `ν(G) = χ(G)` | agreement at the single value `m = χ(G)` |

**Why the name is built this way.** *Chromatic-choosable* is Ohba's 2002 notion `χ(G) = χ_ℓ(G)` —
lists cost nothing at the level of the *number*. `P_ℓ` is the enumerative analogue of the chromatic
polynomial, so *enumeratively* chromatic-choosable lifts the same property from a number to a
counting function. The implication runs the right way, which is what justifies the name: if
`P_ℓ(G,χ(G)) = P(G,χ(G))` then that common value is positive, so `G` is `χ(G)`-choosable and
`χ_ℓ(G) = χ(G)`. Allred–Mudrock note that examples separating the two notions are scarce.

**Where Kirov–Naimi sits.** For a graph with `χ(G) = 2`, "2-monophilic" is exactly *weakly
enumeratively chromatic-choosable*, i.e. `ν(G) = 2`. Allred–Mudrock's Theorem 10 obtains the same
classification — core `K₁`, `C_{2k+2}`, or `K₂,₃` — for the full notion, i.e. `τ(G) = 2`. So their
result strengthens Kirov–Naimi's Theorem 2 from `ν` to `τ`, settling the `χ = 2` case of the open
question below. For a general fixed `n` the literature gives the pointwise property **no name at
all**; `n`-monophilic remains the only one anyone has proposed.

**The open question.** Whether `ν(G) = τ(G)` for every graph — equivalently, whether
`P_ℓ(G,m) = P(G,m)` propagates from `m` to `m+1` — is **open**. It is Question 2 of Allred–Mudrock
and Question 1 of Chi et al. 2026, and both trace it to Kirov–Naimi.

**This repository's naming.** The pointwise predicate is the workhorse (Theorem 1 is "for every
`n`", Theorem 2 is at `n = 2`), so it is **`SimpleGraph.ECCAt G n`**, with
**`SimpleGraph.ECC G := ∀ n, G.ECCAt n`**, both expanded in the module docstring of
`ListColoring.Defs`, and `n`-monophilic recorded there as the historical name. Every declaration
that used to read `monophilic_…` now reads `ecc_…`; the module namespace and directory are
`ListColoring`, since the library is about list colourings and not only about this one predicate.
Prose throughout the development leads with the modern term and mentions `n`-monophilic in passing;
the one place the old wording is kept verbatim is where the docstrings of
`ListColoring.ecc_two_iff` and `ListColoring.ecc_two_iff_of_rubin` quote Theorem 2 as the paper
prints it.

Two caveats about the fit, both recorded above. First, `ECC` quantifies over every `n`, including
`n < χ(G)` where the property is vacuous (`SimpleGraph.ecc_of_not_colorable`), so it agrees with
`τ(G) = χ(G)`; `SimpleGraph.ecc_iff_forall_two_le` is the reformulation that drops the free cases.
Second, at `χ(G) = 2` the paper's Theorem 2 characterizes `ν(G) = 2`, the *weak* notion, so
`ListColoring.ecc_two_iff` is a statement about `ECCAt _ 2` and **not** about `ECC`; whether the two
coincide is the open question above.
