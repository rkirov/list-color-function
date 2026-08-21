# Formalizing the List Color Function in Lean 4 / Mathlib: A State-of-the-Art Report and Starter Brief

**Bottom line:** As of 2026, Mathlib has a solid, well-developed *vertex proper-coloring* API (`SimpleGraph.Coloring`, `Colorable`, `chromaticNumber`) but has **no chromatic polynomial, no list coloring / choosability, no DP-coloring, and no Brooks' or Vizing's theorem** — and **no proof assistant anywhere (Lean, Isabelle/AFP, Coq/Rocq, Mizar) has formalized list coloring, choosability, or the list color function.** This means essentially the entire "list color function" theory must be built from first principles on top of Mathlib's counting and graph infrastructure. Because there is also **no existing survey dedicated to the list color function P_ℓ(G,m)**, both halves of the user's project (formalization + survey) address genuine, unfilled gaps.

## TL;DR
- **Mathlib coloring API is real but shallow for this project.** `SimpleGraph.Coloring`, `Colorable`, and `chromaticNumber` are proven and usable, together with cliques, subgraphs, walks/paths/cycles, box product, and complete-bipartite/multipartite graphs. But the file's own TODO still lists "Chromatic polynomials" and "partial colorings" as unstarted, and there is no list-coloring layer at all.
- **The enumerative-chromatic-choosability edifice is 0% formalized.** No `chromaticPolynomial`, no deletion-contraction, no `P_ℓ`, no `P_DP`, no choosability, no Vizing/Brooks/Galvin in Mathlib. The only closely related mechanized results are Gonthier's Four Color Theorem (Coq), Bauer–Nipkow's Five Colour Theorem (Isabelle), and Arohee Bhoja's brand-new **standalone** Lean 4 proof of Vizing's theorem (arXiv:2512.13999, Dec 2025) — which is *not* in Mathlib.
- **A survey would not duplicate existing work.** The paper repeatedly cited as "the survey" is really Thomassen's 6-page 2009 JCTB note; the standard book (Dong–Koh–Teo 2005) predates the topic and does not cover P_ℓ. The user should write the first dedicated expository treatment of the list color function.

---

## Key Findings

### 1. Mathlib graph-coloring API — current state

The vertex-coloring API lives in **`Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`**, re-exported by the thin wrapper `Mathlib/Combinatorics/SimpleGraph/Coloring.lean` (docs: `leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.html`; source under `leanprover-community/mathlib4/blob/.../Coloring/Vertex.lean`). Note the file was recently split: coloring now sits in a `Coloring/` subdirectory rather than a single `Coloring.lean`.

**Proven and usable:**
- `SimpleGraph.Coloring G α` — reducible abbreviation for `G →g completeGraph α` (a proper coloring = homomorphism into the complete graph on the color type). Coercion to `V → α`; `Coloring.mk` builds one from `color : V → α` plus a validity proof; `Coloring.valid` gives `G.Adj v w → C v ≠ C w`.
- `SimpleGraph.Colorable G n` — `∃` coloring with `≤ n` colors; monotonicity (`Colorable.mono`, `mono_left`), `colorable_of_fintype`, `colorable_iff_exists_bdd_nat_coloring`, per-connected-component reductions.
- `SimpleGraph.chromaticNumber : ℕ∞` (value in `ℕ∞`, `⊤` iff not finitely colorable) with a large lemma set: `chromaticNumber_eq_iInf`/`_biInf`, `Colorable.chromaticNumber_le`, `chromaticNumber_le_iff_colorable`, `chromaticNumber_le_card`, `chromaticNumber_bot`/`_top`, `chromaticNumber_eq_card_iff`, positivity/zero/one/two characterizations.
- **Color classes:** `Coloring.colorClass`, `colorClasses`, `colorClasses_isPartition`, `isIndepSet_colorClass`, `card_colorClasses_le`.
- **Clique lower bound (ω ≤ χ):** `IsClique.card_le_of_colorable`, `IsClique.card_le_chromaticNumber`, `cliqueNum_le_chromaticNumber`, `Colorable.cliqueFree`.
- **Specific families proven:** complete multipartite (`completeMultipartiteGraph.coloring/.colorable/.chromaticNumber`), complete bipartite (`CompleteBipartiteGraph.bicoloring`, `CompleteBipartiteGraph.chromaticNumber`). Disjoint-union coloring is in `Mathlib/Combinatorics/SimpleGraph/Sum.lean` (`⊕g`, `Colorable.sum_max`, `colorable_sum`).
- `Colorable.card_le_of_pairwise_adj`, `recolorOfEmbedding`/`recolorOfEquiv`/`recolorOfCardLE`, `coloringCongr`.

**Stated-only / absent (the TODO in `Coloring/Vertex.lean`):** the file explicitly lists "Trees", "Planar graphs", **"Chromatic polynomials"**, and "develop API for partial colorings, likely as colorings of subgraphs (`H.coe.Coloring α`)" as not done.

**Also absent from Mathlib:** Brooks' theorem, any greedy-coloring procedure, chordal graphs / perfect elimination orderings, and edge coloring / chromatic index. Brooks' theorem and Vizing's theorem appear on the community "open conjecture formalizations" difficulty list (github.com/SamuelSchlesinger/open-conjecture-formalizations) as reachable-but-not-done, and that same list states flatly: **"List coloring not in Mathlib."**

*Report verdict:* what is **proven** is the proper-coloring / chromatic-number core plus the ω ≤ χ bound and complete-(multi)partite values; everything a enumerative-chromatic-choosability project specifically needs (polynomial counting, greedy/PEO, list assignments) is **not even stated**.

### 2. Chromatic polynomial — does not exist in Mathlib

There is **no `chromaticPolynomial`** declaration in Mathlib, and no deletion-contraction lemma, no Whitney broken-cycle theorem, and **no Tutte polynomial**. A Lean Zulip thread "chromatic polynomial" exists in the graph-theory stream (20 messages, latest Aug 22 2024) but yielded no merged definition; it remains a TODO in the coloring file.

**Nearest reusable machinery for building it:**
- `Polynomial R` API (for defining P(G,m) as a genuine polynomial, e.g. via deletion-contraction induction on edges).
- `Finset.card` / `Fintype.card` and `Fintype.card (G.Coloring (Fin m))` — Mathlib already provides `SimpleGraph.instFintypeColoring`, so the *number* of m-colorings is expressible directly as a `Fintype.card`, which is the natural bridge to P(G,m).
- Inclusion–exclusion (`Finset.inclusion_exclusion` family) and the incidence-algebra / Möbius-inversion API (`Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean`) for broken-circuit / NBC-set expansions.
- For deletion-contraction you will need edge deletion (`G.deleteEdges`) and a contraction construction (contraction is **not** currently well-developed in Mathlib and will likely have to be built).

*Recommended first milestone:* define `P(G,m) := Fintype.card (G.Coloring (Fin m))`, prove it equals a polynomial in `m` via deletion-contraction, and prove the chordal-graph product formula `P(G,m) = ∏ (m − αᵢ)` over a perfect elimination ordering — this last is the exact bridge to the list color function (see below).

### 3. List coloring / choosability in proof assistants — nothing exists

**Confirmed: list coloring, choosability, the list chromatic number, DP/correspondence coloring, Galvin's theorem (Dinitz problem), Rubin's 2-choosable characterization, and Gutner's NP-hardness of 3-choosability are formalized in NO major proof assistant.** Consequently the list color function P_ℓ(G,m) has certainly never been formalized anywhere.

**What does exist (reusable adjacent results):**
- **Coq/Rocq:** Georges Gonthier's fully machine-checked **Four Color Theorem** (2005; "Formal Proof — The Four-Color Theorem," *Notices of the AMS* 55(11) (2008) 1382–1393; engineering paper: Gonthier, ASCM 2007, LNCS 5081). Ordinary planar 4-coloring only, built on a hypermap formalization.
- **Isabelle/HOL:** Bauer & Nipkow, **"The 5 Colour Theorem in Isabelle/Isar"** (TPHOLs 2002, LNCS 2410, 67–82) — inductive triangulations + planar graphs. The Archive of Formal Proofs (isa-afp.org) has **no** list-coloring/choosability entry; the closest coloring entries are Edmonds & Paulson, "Hypergraph Colouring Bounds" (AFP, Sep 2023; Property B / Lovász Local Lemma) and Edmonds, "Undirected Graph Theory" (AFP, Sep 2022) — neither touches list coloring.
- **Lean 4:** **Arohee Bhoja, "A verified implementation of the Misra and Gries edge coloring algorithm," arXiv:2512.13999 (Dec 16, 2025)**, code at **github.com/aroheebhoja/vizing** ("Lean4 formalization of Vizing's theorem using the Misra and Gries edge contraction algorithm"). Abstract: *"Vizing's theorem states that every simple undirected graph can be edge-colored using fewer than Δ+1 colors, where Δ is the graph's maximum degree… I used the Lean theorem prover to produce a verified implementation of the Misra and Gries edge-coloring algorithm."* **This is a standalone project, not in Mathlib.** In the Lean Zulip graph-theory topic "Formalization of Vizing's theorem" (Sep 11 – Oct 7 2025, 5 messages), Bhoja announced the constructive proof, received Mathlib-style code review (Vlad Tsyrklevich, Chris Wong suggesting `Sym2`), and stated an intent to upstream *auxiliary list/array lemmas* to Mathlib — but there was **no decision to merge the Vizing proof itself**, and none had been merged as of the archive's Feb 28 2026 snapshot.
- **Mathlib matchings / Hall's theorem:** `Mathlib/Combinatorics/SimpleGraph/Matching.lean` (`IsPerfectMatching`, `IsMatchingFree`, `IsCycles`, `IsAlternating`) and Hall's marriage theorem are available. Since Galvin's theorem (Dinitz) is proved via kernels/stable matchings in orientations, and list-coloring bounds often reduce to matchings/SDRs, this API is directly relevant.
- Kempe chains, the four color theorem, and the two-color/bipartite theory are otherwise only informally available.

### 4. Related combinatorics infrastructure in Mathlib

**Available and directly usable:**
- **Subgraphs / induced subgraphs:** `SimpleGraph.Subgraph`, `Subgraph.coe`, `Subgraph.induce`, `SimpleGraph.induce`, `IsNClique.of_induce`. Partial colorings would naturally be `H.coe.Coloring α`.
- **Walks/paths/cycles:** `Mathlib/Combinatorics/SimpleGraph/Path.lean` and `.../Connectivity/`: `Walk`, `Walk.IsTrail`/`IsPath`/`IsCycle`, `Path`, `Reachable`, `Preconnected`/`Connected`, `ConnectedComponent`, `IsBridge` with `isBridge_iff_mem_and_forall_cycle_not_mem`. `Walk.toSubgraph` and its lemmas. Girth is available (Zulip "Girth and Diameter Proof").
- **Cartesian (box) product:** `SimpleGraph.boxProd` (notation `□`) in `Mathlib/Combinatorics/SimpleGraph/Prod.lean`, with `boxProd_adj`, distributivity isos (`Iso.boxProdSumDistrib`), and connectivity lemmas. The file's own TODO is "Define all other graph products!" — so **tensor/strong/lexicographic products are not present**, and there are essentially **no coloring theorems about `boxProd`** yet (this is exactly the Kaul–Mudrock Cartesian-product territory, which would be new work). Note Zulip topics "graph products" (Jan 2026) and "Lemma about box products" (Mar 2025).
- **Named graphs:** `completeBipartiteGraph V W` and `completeMultipartiteGraph` (in Basic/Maps), `pathGraph`, `cycleGraph`, `circulantGraph` (Circulant.lean), `completeGraph`/`⊤`, `emptyGraph`/`⊥`, Hasse graphs.
- **Bipartite API:** `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` (`IsBipartiteWith`), double counting in `Mathlib/Combinatorics/Enumerative/DoubleCounting.lean`.
- **Counting:** `Fintype.card`, `SimpleGraph.instFintypeColoring`, `Finset` sum/product API.

**Missing (must be built):** chordality / `IsChordal` / perfect elimination orderings (only the *math* is standard: G chordal ⟺ has a PEO, and then P(G,m)=∏(m−αᵢ) — the exact identity Kaul–Mudrock use to show cycles and chordal graphs are "enumeratively chromatic-choosable," i.e. τ(G)=χ(G)); generalized theta graphs; the 2-core / iterated degree-1 deletion; edge contraction; and all counting glue relating `Fintype.card (G.Coloring (Fin m))` to a `Polynomial`.

### 5. Consolidated bibliography of the list color function area

Origins and comparison-with-chromatic-polynomial line:
- **A. V. Kostochka and A. Sidorenko**, "Problem Session of the Prachatice Conference on Graph Theory," *Fourth Czechoslovak Symposium on Combinatorics, Graphs and Complexity*, **Ann. Discrete Math. 51 (1992), 380** — introduces the list color function (problem posed 1990). (Note: a problem-session abstract, not a full paper.)
- **Q. Donner**, "On the number of list-colorings," **J. Graph Theory 16 (1992), 239–245.**
- **P. Erdős, A. L. Rubin, H. Taylor**, "Choosability in graphs," *Proc. West Coast Conf. on Combinatorics, Graph Theory and Computing (Arcata, 1979)*, **Congressus Numerantium 26 (1980), 125–157** (frequently cited as pp. 125–127, 1979).
- **V. G. Vizing**, "Coloring the vertices of a graph in prescribed colors," *Diskret. Analiz.* no. 29, Metody Diskret. Anal. v Teorii Kodov i Skhem **101 (1976), 3–10.**
- **C. Thomassen**, "The chromatic polynomial and list colorings," **J. Combin. Theory Ser. B 99(2) (2009), 474–479**, doi:10.1016/j.jctb.2008.09.005 — proves P_ℓ(G,m)=P(G,m) for m sufficiently large (the "m ≥ n^{10}"-type bound); the note most often loosely cited as "the survey."
- **W. Wang, J. Qian, Z. Yan**, "When does the list-coloring function of a graph equal its chromatic polynomial," **J. Combin. Theory Ser. B 122 (2017), 543–549** — sharpened bound: for a connected graph with m edges, P_ℓ(G,k)=P(G,k) whenever k > (m−1)/ln(1+√2).
- **F. Dong and M. Zhang**, "An improved lower bound of P(G,L)−P(G,k) for k-assignments L," **J. Combin. Theory Ser. B 161 (2023), 109–119.** (Companion line: F. Dong & Y. Yang, "DP color functions versus chromatic polynomials," *Adv. Appl. Math.* 134 (2022), 102301; M. Zhang & F. Dong, "…(II)," *J. Graph Theory* 103 (2023), 740–761.)
- **R. Kirov and R. Naimi**, "List coloring and n-monophilic graphs," **Ars Combin. 124 (2016), 329–340** (arXiv:1004.5183, 2010) — *the user's own paper.*

List color function threshold τ(G):
- **H. Kaul, A. Kumar, J. A. Mudrock, P. Rewers, P. Shin, K. To**, "On the List Color Function Threshold," **J. Graph Theory 105(3) (2024), 386–397** (arXiv:2202.03431) — answers Thomassen's question in the negative: ∃ C with τ(K_{2,ℓ}) − χ_ℓ(K_{2,ℓ}) ≥ C√ℓ for ℓ ≥ 16.
- **H. Kaul, A. Kumar, A. Liu, J. A. Mudrock, P. Rewers, P. Shin, M. S. Tanahara, K. To**, "Bounding the List Color Function Threshold from Above," **Involve 16(5) (2023), 849–882** (arXiv:2207.04831) — τ(K_{2,n}) ≤ ⌈(n+2.05)/1.24⌉; general bound τ(G) ≤ (|E(G)|−1)/ln(1+√2)+1.

DP color function P_DP(G,m) (Kaul–Mudrock 2019 and after):
- **H. Kaul and J. A. Mudrock**, "On the chromatic polynomial and counting DP-colorings of graphs," **Adv. Appl. Math. 123 (2021), 103121** (arXiv:1904.07697) — introduces the DP color function; proves chordal graphs satisfy P_DP(G,m)=P(G,m).
- **H. Kaul and J. A. Mudrock**, "Criticality, the list color function, and list coloring the Cartesian product of graphs," **J. Combinatorics 12(3) (2021), 479–514.**
- **M. V. Bui, H. Kaul, M. Maxfield, J. A. Mudrock, P. Shin, S. Thomason**, "Non-chromatic-adherence of the DP color function via generalized theta graphs," **Graphs Combin. 39 (2023), Paper 42** (arXiv:2110.04058), doi:10.1007/s00373-023-02633-z.
- **J. A. Mudrock and S. Thomason**, "Answers to two questions on the DP color function," **Electron. J. Combin. 28 (2021), P2.24** (arXiv:2009.08242).
- **J. A. Mudrock**, "A deletion-contraction relation for the DP color function," **Graphs Combin. 38 (2022), Paper 115** (doi:10.1007/s00373-022-02520-z).
- **C. Halberg, H. Kaul, A. Liu, J. A. Mudrock, P. Shin, S. Thomason**, "On polynomial representations of the DP color function: theta graphs and their generalizations," **J. Combin. 15(4) (2024), 451–468** (arXiv:2012.12897).
- **H. Kaul, J. A. Mudrock, G. Sharma, Q. Stratton**, "DP-coloring Cartesian products of graphs," **J. Graph Theory (2023)** (Wiley, doi:10.1002/jgt.22917).

Recent (2025–2026) and enumerative chromatic-choosability:
- **S. Allred and J. A. Mudrock**, "Enumerative Chromatic Choosability," arXiv:2505.05662 (2025).
- **[Allred & Mudrock]**, "Enumeratively Chromatic-Choosable Theta Graphs," arXiv:2605.10861 (2026).
- **H. Kaul, J. A. Mudrock, G. Sharma**, "Shameful Inequalities for List and DP Coloring of Graphs," **Graphs Combin. 42 (2026), Paper 46** (arXiv:2412.16790, doi:10.1007/s00373-026-03040-w).
- **H. Kaul and J. A. Mudrock**, "Counting List Colorings of Unlabeled Graphs," arXiv:2409.06063 (2024, rev. 2026).

Choosability landmark results (for the survey):
- **F. Galvin**, "The list chromatic index of a bipartite multigraph" (Dinitz conjecture), **J. Combin. Theory Ser. B 63 (1995), 153–158.**
- **A. L. Rubin** — 2-choosable-graph characterization (via the "cores," in Erdős–Rubin–Taylor 1980).
- **S. Gutner**, "The complexity of planar graph choosability," *Discrete Math.* 159 (1996), 119–130 — NP-hardness of 3-choosability.
- **Zs. Tuza**, "Graph colorings with local constraints — a survey," **Discuss. Math. Graph Theory 17 (1997), 161–228.**
- **Z. Dvořák and L. Postle**, "Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8," **J. Combin. Theory Ser. B 129 (2018), 38–54** — introduces DP/correspondence coloring.
- Background: **G. D. Birkhoff** (1912, *Ann. of Math.* 14, 42–46); **H. Whitney** (broken cycles, 1932); **F. Dong**, "Proof of a chromatic polynomial conjecture" (the Shameful Conjecture), *J. Combin. Theory Ser. B* 78 (2000), 35–44.

### 6. Prior surveys / expository treatments — the closest prior art

**There is no dedicated survey, book chapter, lecture-note set, or thesis whose primary subject is the list color function P_ℓ(G,m) or the DP color function P_DP(G,m).** Specifically:
- The reference repeatedly cited in Kaul–Mudrock papers as a "survey of known results and open questions on the list color function" is really **Thomassen (2009)**, a 6-page research note — not an expository survey.
- **F. M. Dong, K. M. Koh, K. L. Teo, "Chromatic Polynomials and Chromaticity of Graphs," World Scientific, 2005** (384 pp., ISBN 978-981-256-317-0, doi:10.1142/5814) — "the first book to comprehensively cover chromatic polynomials of graphs," but it covers **only the ordinary chromatic polynomial** and predates essentially all enumerative-chromatic-choosability work (which took off after Wang–Qian–Yan 2017 / Kaul–Mudrock 2019). A useful companion: F. M. Dong & K. M. Koh, "Foundations of the chromatic polynomial," in *Handbook on the Tutte Polynomial and Related Topics* (CRC, 2021), 232–266.
- **Mudrock's PhD thesis** ("On the list coloring problem and its equitable variants," Illinois Institute of Technology, 2018) is about list coloring / equitable list coloring generally, **not** the enumerative function P_ℓ. No student thesis of Kaul or Mudrock dedicated to P_ℓ/P_DP was found (checked jmudrock.weebly.com research/student-research pages).
- A **different**, broader 2026 survey exists — **N. K. Vasudevan, K. Somasundaram, N. Narayanan, "List-Coloring and Chromatic-Choosability — A Dynamic Survey," arXiv:2606.31702 (2026)** — but it surveys list-coloring/chromatic-choosability (graph classes where χ_ℓ=χ), **not** the enumerative list color function. The earlier general list-coloring survey it cites is D. R. Woodall (2001), on defective choosability.

*Verdict:* the user's proposed survey of the list color function would be the first of its kind and is not at risk of duplication.

---

## Recommendations

**Stage 0 — Scoping the Lean project (immediate).** Hand the agent the concrete Mathlib anchors above. The single most important design decision is the definition of the counting object. Recommended: define the chromatic polynomial operationally as `P(G, m) := Fintype.card (G.Coloring (Fin m))` (Mathlib already supplies `instFintypeColoring`), then separately prove it is polynomial in `m`. Define list assignments as `L : V → Finset α` and an `L`-coloring as `f : Π v, α` with `∀ v, f v ∈ L v` and properness; define `P_ℓ(G,m)` as the min over all m-uniform `L` of the number of proper L-colorings. This mirrors the Kaul–Mudrock definitions exactly.

**Stage 1 — Build the missing scaffolding, contribute upstream.** In dependency order: (a) edge deletion is present; build **edge contraction** and the **deletion-contraction** recurrence for P(G,m); (b) build **chordal graphs / perfect elimination orderings** and prove `P(G,m)=∏(m−αᵢ)` — this is the key lemma that yields "cycles and chordal graphs are enumeratively chromatic-choosable" (τ(G)=χ(G)); (c) build **partial colorings** as `H.coe.Coloring α` (already flagged as a Mathlib TODO). Each of these is independently valuable to Mathlib and should be PR'd; coordinate on the Lean Zulip **#graph theory** stream, where coloring, chromatic-polynomial, and Vizing discussions are active.

**Stage 2 — First real theorems.** Target, in increasing difficulty: (1) P(C_n,m)=(m−1)^n+(−1)^n(m−1) via deletion-contraction (a clean, self-contained showcase); (2) chordal/cycle enumerative chromatic-choosability, i.e. P_ℓ(G,m)=P(G,m) (Kostochka–Sidorenko / Donner); (3) the Wang–Qian–Yan threshold P_ℓ(G,k)=P(G,k) for k>(|E|−1)/ln(1+√2); (4) as reach goals, the τ(K_{2,ℓ}) lower bound (Kaul et al. 2024) and a formalized reproduction of a Kirov–Naimi n-monophilic result. Reuse Mathlib's Hall/matching API for any SDR-style arguments; if edge-coloring analogues arise, watch whether Bhoja's Vizing auxiliary lemmas land in Mathlib.

**Stage 3 — The survey.** Write the first dedicated expository survey of the list color function: history (Kostochka–Sidorenko 1990 → Donner 1992 → Thomassen 2009 → Wang–Qian–Yan 2017 → Dong–Zhang 2023), the τ(G) threshold program, the DP color function parallel (2019→2026), enumerative chromatic-choosability, and open problems — and uniquely, a section on **formalization status and challenges** (leveraging this report). Position it against, not overlapping with, the Vasudevan–Somasundaram–Narayanan (2026) chromatic-choosability dynamic survey and the Dong–Koh–Teo (2005) book.

**Benchmarks that would change the plan:** (i) if Bhoja's Vizing proof or its auxiliary lemmas are merged into Mathlib, reuse them and cite `Mathlib`; (ii) if a `chromaticPolynomial` PR appears on Zulip/GitHub, pivot to building `P_ℓ` on top of it rather than redefining P(G,m); (iii) if any AFP/Coq list-coloring entry appears, re-scope the survey's formalization section and consider cross-assistant comparison.

---

## Caveats
- Several conclusions are **inferences from absence** (no list coloring in Mathlib; no dedicated P_ℓ survey; nothing in AFP/Coq/Mizar). These are well-supported by the Mathlib docs, the coloring-file TODO, the community "open conjecture" list stating "List coloring not in Mathlib," the Zulip graph-theory topic index, Mudrock's own homepage, and AFP search — but a universal negative cannot be proven; a quick Loogle/`grep` of current Mathlib for `Choosable`/list-coloring and a fresh AFP search are advisable before publication.
- Mathlib evolves rapidly and the coloring files were recently reorganized (into `Coloring/Vertex.lean`); exact declaration names and the commit hash in doc URLs will drift — verify against the live `mathlib4_docs` before relying on any specific signature.
- Bhoja's Vizing paper (arXiv:2512.13999) is very recent (Dec 2025) and its Mathlib-upstreaming status is fluid; treat "not in Mathlib" as accurate as of early 2026.
- Two bibliographic details carry minor ambiguity in the literature: the Erdős–Rubin–Taylor venue is cited both as *Congr. Numer.* 26 (1979), 125–127 and (1980), 125–157; and the Kostochka–Sidorenko item is a problem-session abstract (Ann. Discrete Math. 51 (1992), 380), variously dated 1990/1992. Both should be cited with these variants noted.
