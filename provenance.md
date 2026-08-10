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
| `SimpleGraph.monophilic_iff_listColorFunction_eq_eval` | `n`-monophilic ⟺ `P_ℓ(G,n) = P(G,n)` | definitional bridge; the notions are **Kostochka–Sidorenko 1990/92** and **Kirov–Naimi 2016** |
| `SimpleGraph.ERT.not_choosable`, `ERT.colorable` | `K_{n,nⁿ}` is `n`-colourable but not `n`-choosable | **Erdős–Rubin–Taylor 1979**; also Kirov–Naimi §5 |
| `SimpleGraph.monophilic_of_isChordal` | chordal ⟹ `n`-monophilic for every `n` | **Kostochka–Sidorenko 1990/92**; = Thm 2(i) of Chi et al. 2026 |
| `SimpleGraph.isChordal_iff_exists_cliqueTower` | chordal ⟺ has a simplicial elimination ordering | **Dirac 1961**; Fulkerson–Gross 1965 |
| `Monophilic.monophilic_closePath_of_two_le` | **every cycle is `n`-monophilic, every `n ≥ 2`** | **Kirov–Naimi 2016, Theorem 1**; = Thm 2(ii) of Chi et al. 2026 |
| `Monophilic.choosable_two_of_rubinFamily` | a vertex / even cycle / `θ_{2,2,2m}` is 2-choosable | **Rubin**, in Erdős–Rubin–Taylor 1979 — the *easy* direction |
| Theorem 2 (`monophilic_two_iff…`) | connected `G` is 2-monophilic ⟺ core is a vertex, a cycle, `K₂,₃`, or `G` has an odd cycle | **Kirov–Naimi 2016, Theorem 2**; = Thm 2(iv) of Chi et al. 2026, there attributed to [1, 6, 13, 16, 17] |
| `SimpleGraph.exists_monophilic_forall_ge` | `P_ℓ(G,m) = P(G,m)` for all large `m` | **Donner 1992**; threshold via **Wang–Qian–Yan 2017** |
| `SimpleGraph.monophilic_of_two_pow_lt` | explicit threshold `2^{\|E(G)\|} < m` | weaker form of **Wang–Qian–Yan 2017**; superseded by **Dong–Zhang 2023** (`m ≥ \|E(G)\| − 1`) |
| Lemmas 1–6 | the supporting lemmas | **Kirov–Naimi 2016**, numbered as in the paper |

### In progress — Rubin's theorem

The target is **Rubin's theorem** (A. L. Rubin, in **Erdős–Rubin–Taylor**, *Choosability in graphs*,
Congr. Numer. **26** (1979), 125–157): *a connected graph is 2-choosable iff its core is a single
vertex, an even cycle, or `θ_{2,2,2m}` for some `m ≥ 1`.* Kirov–Naimi cite it; this development aims
to prove it, so that Theorem 2 carries no hypothesis.

| piece | Result | Credit |
|---|---|---|
| ⟸ | the three families are 2-choosable | **Rubin** — **proved** |
| 5 | `Θ(k₁,…,k_n)` is 2-choosable ⟺ `n = 3` and shape `(2,2,even)` | a component of **Rubin's theorem**; as a statement it is a corollary of it. Proved here directly from list assignments, so it can feed the proof of Rubin without circularity |
| 1, 3 | core reduction; two cycles meeting in ≤ 1 vertex are not 2-choosable | standard, part of **Rubin's** argument |
| 4 | 2-connected non-cycle ⟹ generalized theta, or two cycles meeting in ≤ 1 vertex | classical structural graph theory (ear decomposition) |

**None of this is novel.** It is a 1979 theorem that appears not to have been machine-checked before.

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
* **Kirov–Naimi §5, the full `H_{n+1}` construction (Lemmas 7–10)** — for each `n`, a graph that is
  `n`-choosable but not `n`-monophilic. **Not attempted**; only the building block `K_{n,nⁿ}` is done.

## 3. Not from the literature

Nothing here is a mathematical advance. These are artifacts of mechanization, recorded because they
are the parts a reader could not get from the papers.

* **The formalization itself.** As far as we can determine, list coloring and choosability had not
  been formalized in any proof assistant before this project.
* **`Monophilic.const_block`, `armBlockLists_forced`, `alt_chain`** (`ThetaClass.lean`) — the
  induction along an arm of unbounded length. The informal proofs say "it is then easy to check";
  these lemmas are what that phrase expands to. Presentation, not mathematics.
* **Lemma 3(c) fails at `k = 0`.** Kirov–Naimi's hypothesis "path of length at least one" is
  load-bearing, not decorative — machine-checked witness in `plan.md`. This *confirms* the paper.
* **`ThetaAlternative` was false.** An auxiliary hypothesis invented *in this repository* to split
  Rubin's theorem into a structural half and a colouring half. `K₂,₄` refutes it. It has been
  deleted. This is a defect in our scaffolding and **not** an error in Kirov–Naimi, which cites
  Rubin's theorem rather than proving it. Recorded in `plan.md`.
* **Zero errors found in Kirov–Naimi.** Stated positively because it is the more useful fact.

## 4. A note on the name

Kirov–Naimi's "`n`-monophilic" is the pointwise property `P_ℓ(G,n) = P(G,n)` at one `n`. The term
that has since taken hold is **enumeratively chromatic-choosable**, first formally defined in Kaul
et al., *Bounding the list color function threshold from above*, Involve **16** (2023) 849–882, for
the stronger "at *every* `m`" property. The literature gives the pointwise property no separate
name. The two are not known to coincide: whether `P_ℓ(G,m) = P(G,m)` propagates from `m` to `m+1` is
**open** — Question 1 of Chi et al. 2026, raised in Kirov–Naimi.
