# References — List Color Function / n-Monophilic Graphs (Lean 4 formalization project)

Verified bibliography. Every entry below was checked against at least one authoritative
index (Crossref DOI metadata via content negotiation, zbMATH Open API, dblp API, arXiv,
publisher pages, or author CVs). Entries that could **not** be confirmed are marked
`[UNVERIFIED]` and explained in the final section. Corrections to `survey.md` are recorded
in "Verification notes".

Compiled 2026-08-08.

---

## Primary paper

- **R. Kirov and R. Naimi**, "List coloring and $n$-monophilic graphs," *Ars Combinatoria*
  **124** (2016), 329–340. arXiv:[1004.5183](https://arxiv.org/abs/1004.5183) (v1, 29 Apr 2010).
  Zbl 1413.05116; dblp `journals/arscom/KirovN16`. No DOI (Ars Combinatoria does not assign DOIs);
  the arXiv record carries no journal-ref.
  — *The user's own paper. Proves all cycles are $n$-monophilic for all $n$; characterizes
  2-monophilic graphs (parallel to the Erdős–Rubin–Taylor 2-choosable characterization); and
  constructs, for each $n$, a graph that is $n$-choosable but not $n$-monophilic.*

---

## Foundations of list coloring

- **P. Erdős, A. L. Rubin, and H. Taylor**, "Choosability in graphs," in *Proceedings of the
  West Coast Conference on Combinatorics, Graph Theory and Computing* (Arcata, California, 1979),
  Congressus Numerantium **XXVI** (26), Utilitas Math., Winnipeg, **1980**, pp. **125–157**.
  Zbl 0469.05032. No DOI.
  — *Co-origin of list coloring/choosability; contains Rubin's characterization of 2-choosable
  graphs, the template Kirov–Naimi mirror for 2-monophilic graphs.* See Verification notes §1.

- **V. G. Vizing**, "Coloring the vertices of a graph in prescribed colors" (Russian),
  *Diskret. Analiz.* No. **29**: *Metody Diskret. Anal. v Teorii Kodov i Skhem* (1976), 3–10, 101.
  MR0498216. No DOI.
  — *Independent co-origin of list coloring. Note: "101" is a trailing page number (the summary
  page), not a volume — see Verification notes §5.*

- **R. Diestel**, *Graph Theory*, Graduate Texts in Mathematics **173**, Springer, New York,
  **1997** (translated from the German; xiv+286 pp.). Zbl 0873.05001.
  Later editions: 2nd ed. 2000 (Zbl 0945.05002), 3rd ed. 2005 (Zbl 1074.05001).
  — *Kirov–Naimi reference [1]: the source of their notation and terminology. Cite the 1997
  edition to match their usage.*

---

## List color function $P_\ell(G,m)$

- **A. V. Kostochka and A. F. Sidorenko**, "Problem session of the Prachatice conference on
  graph theory," in *Fourth Czechoslovak(ian) Symposium on Combinatorics, Graphs and Complexity*
  (Prachatice, **1990**), eds. J. Nešetřil and M. Fiedler, Annals of Discrete Mathematics **51**,
  North-Holland/Elsevier, **1992**, p. **380**.
  — *Origin of the list color function: a one-page problem-session abstract, not a full paper.
  Problem posed at the 1990 meeting; proceedings volume published 1992.* See Verification notes §2.

- **Q. Donner**, "On the number of list-colorings," *Journal of Graph Theory* **16** (3) (1992),
  239–245. DOI [10.1002/jgt.3190160307](https://doi.org/10.1002/jgt.3190160307). Zbl 0754.05038.
  — *Kirov–Naimi reference [3]: $P_\ell(G,m) = P(G,m)$ for all sufficiently large $m$.*

- **C. Thomassen**, "The chromatic polynomial and list colorings," *Journal of Combinatorial
  Theory, Series B* **99** (2) (2009), 474–479.
  DOI [10.1016/j.jctb.2008.09.005](https://doi.org/10.1016/j.jctb.2008.09.005).
  — *Explicit polynomial bound on Donner's threshold; poses the $\tau(G)$ question. Frequently
  (and loosely) cited as "the survey" of the list color function — it is a 6-page research note.*

- **W. Wang, J. Qian, and Z. Yan**, "When does the list-coloring function of a graph equal its
  chromatic polynomial," *Journal of Combinatorial Theory, Series B* **122** (2017), 543–549.
  DOI [10.1016/j.jctb.2016.08.002](https://doi.org/10.1016/j.jctb.2016.08.002).
  — *Sharpened threshold: $P_\ell(G,k) = P(G,k)$ for $k > (|E(G)|-1)/\ln(1+\sqrt{2})$.*

- **F. Dong and M. Zhang**, "An improved lower bound of $P(G,L) - P(G,k)$ for $k$-assignments $L$,"
  *Journal of Combinatorial Theory, Series B* **161** (2023), 109–119.
  DOI [10.1016/j.jctb.2023.02.002](https://doi.org/10.1016/j.jctb.2023.02.002).
  — ***The best known threshold:*** $P_\ell(G,m) = P(G,m)$ for every $m \ge |E(G)| - 1$. This
  supersedes Wang–Qian–Yan above, and is far stronger than what this repository formalizes
  (`monophilic_of_two_pow_lt`, which needs $2^{|E(G)|} < m$).

- **H. Kaul, A. Kumar, J. A. Mudrock, P. Rewers, P. Shin, and K. To**, "On the list color function
  threshold," *Journal of Graph Theory* **105** (3) (2024), 386–397.
  DOI [10.1002/jgt.23045](https://doi.org/10.1002/jgt.23045). arXiv:[2202.03431](https://arxiv.org/abs/2202.03431).
  — *Answers Thomassen's question negatively: $\tau(K_{2,\ell}) - \chi_\ell(K_{2,\ell}) \ge C\sqrt{\ell}$.*

- **H. Kaul, A. Kumar, A. Liu, J. A. Mudrock, P. Rewers, P. Shin, M. S. Tanahara, and K. To**,
  "Bounding the list color function threshold from above," *Involve, a Journal of Mathematics*
  **16** (5) (2023), 849–882.
  DOI [10.2140/involve.2023.16.849](https://doi.org/10.2140/involve.2023.16.849).
  arXiv:[2207.04831](https://arxiv.org/abs/2207.04831).

- **H. Kaul, J. A. Mudrock, and G. Sharma**, "Shameful inequalities for list and DP coloring of
  graphs," *Graphs and Combinatorics* **42** (3) (2026), Paper No. **46**.
  DOI [10.1007/s00373-026-03040-w](https://doi.org/10.1007/s00373-026-03040-w) (online 13 Apr 2026).
  arXiv:[2412.16790](https://arxiv.org/abs/2412.16790) (v1 21 Dec 2024; v2 25 Sep 2025).
  — *List/DP analogues of Dong's shameful-conjecture inequality.*

- **S. Allred and J. A. Mudrock**, "Enumerative chromatic choosability,"
  arXiv:[2505.05662](https://arxiv.org/abs/2505.05662) (8 May 2025). **Preprint / submitted**;
  no journal-ref as of 2026-08-08.
  — *Introduces "enumeratively chromatic-choosable" ($P_\ell(G,m) = P(G,m)$ for all $m$);
  characterizes the $\chi = 2$ case. This is the property Kirov–Naimi call $n$-monophilic-for-all-$n$
  in the uniform-list setting.*

- **Y. Chi, S. Lee, F. Morrissette, J. A. Mudrock, G. Nguyen, and B. Whatley**, "Enumeratively
  chromatic-choosable theta graphs," *Enumerative Combinatorics and Applications* **6** (3) (2026),
  Article **S2R23**. arXiv:[2605.10861](https://arxiv.org/abs/2605.10861).
  — *Characterizes the enumeratively chromatic-choosable theta graphs via DP-coloring.*
  **NOTE:** survey.md misattributes this to "Allred & Mudrock" — see Verification notes §4.

- **H. Kaul and J. A. Mudrock**, "Counting list colorings of unlabeled graphs,"
  arXiv:[2409.06063](https://arxiv.org/abs/2409.06063) (v1 9 Sep 2024; v2 3 Feb 2026).
  **Preprint / submitted**; no journal-ref as of 2026-08-08.

- **H. Kaul and J. A. Mudrock**, "Criticality, the list color function, and list coloring the
  Cartesian product of graphs," *Journal of Combinatorics* **12** (3) (2021), 479–514.
  DOI [10.4310/joc.2021.v12.n3.a4](https://doi.org/10.4310/joc.2021.v12.n3.a4).

---

## DP color function $P_{DP}(G,m)$

- **Z. Dvořák and L. Postle**, "Correspondence coloring and its application to list-coloring planar
  graphs without cycles of lengths 4 to 8," *Journal of Combinatorial Theory, Series B* **129**
  (2018), 38–54. DOI [10.1016/j.jctb.2017.09.001](https://doi.org/10.1016/j.jctb.2017.09.001).
  — *Introduces DP/correspondence coloring.*

- **H. Kaul and J. A. Mudrock**, "On the chromatic polynomial and counting DP-colorings of graphs,"
  *Advances in Applied Mathematics* **123** (2021), Article **102131**.
  DOI [10.1016/j.aam.2020.102131](https://doi.org/10.1016/j.aam.2020.102131).
  arXiv:[1904.07697](https://arxiv.org/abs/1904.07697).
  — *Introduces the DP color function; proves $P_{DP}(G,m) = P(G,m)$ for chordal graphs.*
  **NOTE:** the article number is **102131**, not 103121 — see Verification notes §6.

- **J. A. Mudrock and S. Thomason**, "Answers to two questions on the DP color function,"
  *The Electronic Journal of Combinatorics* **28** (2) (2021), Paper **P2.24**.
  DOI [10.37236/9863](https://doi.org/10.37236/9863). arXiv:[2009.08242](https://arxiv.org/abs/2009.08242).

- **J. A. Mudrock**, "A deletion–contraction relation for the DP color function,"
  *Graphs and Combinatorics* **38** (4) (2022), Paper No. **115**.
  DOI [10.1007/s00373-022-02520-z](https://doi.org/10.1007/s00373-022-02520-z).
  arXiv:[2107.08154](https://arxiv.org/abs/2107.08154).
  — *Directly relevant to the Lean plan: the DP analogue of deletion–contraction.*

- **M. V. Bui, H. Kaul, M. Maxfield, J. A. Mudrock, P. Shin, and S. Thomason**,
  "Non-chromatic-adherence of the DP color function via generalized theta graphs,"
  *Graphs and Combinatorics* **39** (3) (2023), Paper No. **42**.
  DOI [10.1007/s00373-023-02633-z](https://doi.org/10.1007/s00373-023-02633-z).
  arXiv:[2110.04058](https://arxiv.org/abs/2110.04058).

- **C. Halberg, H. Kaul, A. Liu, J. A. Mudrock, P. Shin, and S. Thomason**, "On polynomial
  representations of the DP color function: theta graphs and their generalizations,"
  *Journal of Combinatorics* **15** (4) (2024), **451–478**.
  DOI [10.4310/joc.240906222651](https://doi.org/10.4310/joc.240906222651).
  arXiv:[2012.12897](https://arxiv.org/abs/2012.12897). Zbl 1562.05104.
  — **NOTE:** page range disputed (451–478 vs 451–468) — see Verification notes §7.

- **H. Kaul, J. A. Mudrock, G. Sharma, and Q. Stratton**, "DP-coloring Cartesian products of
  graphs," *Journal of Graph Theory* **103** (2) (2023), 285–306.
  DOI [10.1002/jgt.22917](https://doi.org/10.1002/jgt.22917).

- **F. Dong and Y. Yang**, "DP color functions versus chromatic polynomials," *Advances in Applied
  Mathematics* **134** (2022), Article **102301**.
  DOI [10.1016/j.aam.2021.102301](https://doi.org/10.1016/j.aam.2021.102301).

- **M. Zhang and F. Dong**, "DP color functions versus chromatic polynomials (II),"
  *Journal of Graph Theory* **103** (4) (2023), 740–761.
  DOI [10.1002/jgt.22944](https://doi.org/10.1002/jgt.22944).

---

## Choosability landmarks and chromatic-polynomial background

- **G. A. Dirac**, "On rigid circuit graphs," *Abhandlungen aus dem Mathematischen Seminar der
  Universität Hamburg* **25** (1961), 71–76.
  DOI [10.1007/BF02992776](https://doi.org/10.1007/BF02992776). Zbl 0098.14703.
  — *Kirov–Naimi reference [2]: chordal ⟺ perfect elimination ordering. The lemma behind
  "chordal graphs are $n$-monophilic for all $n$", and Stage-1 target (b) of the Lean plan.*

- **F. Galvin**, "The list chromatic index of a bipartite multigraph," *Journal of Combinatorial
  Theory, Series B* **63** (1) (1995), 153–158.
  DOI [10.1006/jctb.1995.1011](https://doi.org/10.1006/jctb.1995.1011). Zbl 0826.05026.
  — *Kirov–Naimi reference [5]: proof of the Dinitz conjecture via kernels/stable matchings.
  Mathlib's Hall/matching API is the natural substrate for formalizing this.*

- **S. Gutner**, "The complexity of planar graph choosability," *Discrete Mathematics* **159**
  (1–3) (1996), 119–130.
  DOI [10.1016/0012-365X(95)00104-5](https://doi.org/10.1016/0012-365X(95)00104-5). Zbl 0865.05066.
  — *Kirov–Naimi reference [6]: NP-hardness of 3-choosability.*

- **G. D. Birkhoff**, "A determinant formula for the number of ways of coloring a map,"
  *Annals of Mathematics* (2) **14** (1/4) (1912), 42–46.
  DOI [10.2307/1967597](https://doi.org/10.2307/1967597). Zbl 43.0574.02.
  — *Origin of the chromatic polynomial.*

- **H. Whitney**, "A logical expansion in mathematics," *Bulletin of the American Mathematical
  Society* **38** (8) (1932), 572–579.
  DOI [10.1090/S0002-9904-1932-05460-X](https://doi.org/10.1090/S0002-9904-1932-05460-X).
  — *The broken-circuit / NBC expansion. survey.md cites "Whitney (broken cycles, 1932)" without
  detail; this is the intended paper (not Whitney's "The coloring of graphs," Ann. of Math. 33
  (1932), 688–718).*

- **F. Dong**, "Proof of a chromatic polynomial conjecture," *Journal of Combinatorial Theory,
  Series B* **78** (1) (2000), 35–44.
  DOI [10.1006/jctb.1999.1925](https://doi.org/10.1006/jctb.1999.1925).
  — *The "shameful conjecture"; the target the 2026 Kaul–Mudrock–Sharma paper generalizes.*

---

## Surveys and books

- **Zs. Tuza**, "Graph colorings with local constraints — a survey," *Discussiones Mathematicae
  Graph Theory* **17** (2) (1997), 161–228.
  DOI [10.7151/dmgt.1049](https://doi.org/10.7151/dmgt.1049). Zbl 0923.05027.
  — *Kirov–Naimi reference [8]: the standard broad survey of list coloring circa 1997.*

- **D. R. Woodall**, "List colourings of graphs," in *Surveys in Combinatorics, 2001*, London Math.
  Soc. Lecture Note Series **288**, Cambridge University Press, 2001, pp. 269–301.
  DOI [10.1017/CBO9780511721328.012](https://doi.org/10.1017/CBO9780511721328.012).
  — *General list-colouring survey. survey.md describes this as being "on defective
  choosability", which is inaccurate — see Verification notes §8.*

- **F. M. Dong, K. M. Koh, and K. L. Teo**, *Chromatic Polynomials and Chromaticity of Graphs*,
  World Scientific, Singapore, 2005. DOI [10.1142/5814](https://doi.org/10.1142/5814).
  — *The standard book on the ordinary chromatic polynomial; predates the list-color-function
  literature and does not cover $P_\ell$.*
  `[UNVERIFIED]` page count (384 pp.) and ISBN 978-981-256-317-0 as claimed in survey.md — not checked.

- **F. M. Dong and K. M. Koh**, "Foundations of the chromatic polynomial," in *Handbook of the
  Tutte Polynomial and Related Topics* (eds. J. Ellis-Monaghan and I. Moffatt), CRC Press /
  Chapman & Hall, pp. **213–251**.
  DOI [10.1201/9780429161612-11](https://doi.org/10.1201/9780429161612-11) (Crossref date 2022-05-11).
  — **NOTE:** survey.md gives "*Handbook **on** the Tutte Polynomial*… (CRC, 2021), 232–266";
  title preposition, year, and page range all differ — see Verification notes §9.

- **N. K. Vasudevan, K. Somasundaram, and N. Narayanan**, "List-coloring and chromatic-choosability
  — a dynamic survey," arXiv:[2606.31702](https://arxiv.org/abs/2606.31702)
  (submitted Tue, 30 Jun 2026 14:10:19 UTC). Preprint; no journal-ref.
  — *Surveys chromatic-choosability ($\chi_\ell = \chi$), NOT the enumerative list color function.
  Confirms the survey.md claim of non-overlap with a $P_\ell$ survey.*

- **J. A. Mudrock**, *On the List Coloring Problem and Its Equitable Variants*, Ph.D. dissertation,
  Illinois Institute of Technology, 2018 (ProQuest 2070374930).
  — *About list coloring and equitable variants generally, not $P_\ell$.*

---

## Formalization

- **G. Gonthier**, "Formal proof — the four-color theorem," *Notices of the American Mathematical
  Society* **55** (11) (2008), 1382–1393. No DOI located.
  — *The Coq four-colour formalization. Ordinary planar 4-colouring only.*

- **G. Gonthier**, "The four colour theorem: engineering of a formal proof," in *Computer
  Mathematics (ASCM 2007)*, Lecture Notes in Computer Science **5081**, Springer, 2008, p. 333.
  DOI [10.1007/978-3-540-87827-8_28](https://doi.org/10.1007/978-3-540-87827-8_28).

- **G. Bauer and T. Nipkow**, "The 5 colour theorem in Isabelle/Isar," in *Theorem Proving in
  Higher Order Logics (TPHOLs 2002)*, Lecture Notes in Computer Science **2410**, Springer, 2002,
  pp. 67–82. DOI [10.1007/3-540-45685-6_6](https://doi.org/10.1007/3-540-45685-6_6).

- **A. Bhoja**, "A verified implementation of the Misra and Gries edge coloring algorithm,"
  arXiv:[2512.13999](https://arxiv.org/abs/2512.13999) (16 Dec 2025). Lean 4; code at
  `github.com/aroheebhoja/vizing`. **Standalone, not in Mathlib** as of 2026-08-08.

- **C. Edmonds and L. C. Paulson**, "Hypergraph colouring bounds," *Archive of Formal Proofs*,
  submitted 23 September 2023. `https://www.isa-afp.org/entries/Hypergraph_Colourings.html`
  — *Property B and the Lovász Local Lemma in Isabelle/HOL; the nearest AFP coloring entry.*

- **C. Edmonds**, "Undirected graph theory," *Archive of Formal Proofs*, submitted
  29 September 2022. `https://www.isa-afp.org/entries/Undirected_Graph_Theory.html`

- **Mathlib 4**, `Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean` (and the wrapper
  `Coloring.lean`) — `SimpleGraph.Coloring`, `Colorable`, `chromaticNumber`,
  `instFintypeColoring`. No list coloring, choosability, chromatic polynomial, or DP coloring.
  `[UNVERIFIED HERE]` — the Mathlib claims in survey.md were not re-checked in this pass;
  verify against live `mathlib4_docs` before relying on declaration names.

---

## Verification notes

### 1. Erdős–Rubin–Taylor, "Choosability in graphs" — RESOLVED in favour of **Congr. Numer. 26 (1980), 125–157**

**Evidence.** zbMATH Open (Zbl 0469.05032) records the source verbatim as:

> "Combinatorics, graph theory and computing, Proc. West Coast Conf., Arcata/Calif. **1979**, **125-157** (**1980**)."

with the publication year field set to **1980**. This is decisive on both disputed points:

- **Year.** *1979* is the **conference** year (West Coast Conference on Combinatorics, Graph Theory
  and Computing, Arcata, California, 1979); *1980* is the **publication** year of the proceedings
  volume, Congressus Numerantium XXVI. Both numbers are "correct" about different things; the
  citation year should be **1980**, with "(Arcata, 1979)" carried in the venue string.
- **Pages.** **125–157**, not 125–127. The paper is a 33-page monograph-length article; "125–127"
  is a propagated typo. Corroboration: the Kirov–Naimi reference list itself (page 10 of the PDF,
  ref [4]) reads *"Congr. Numer. **26** (1980), 125-157"*; and the 2026 paper arXiv:2605.10861,
  ref [11], reads *"(1980) … Congress Numerantium, Vol. XXVI, 125–157."*

**Where the "125–127 (1979)" variant comes from.** It circulates inside the Kaul–Mudrock group's
own bibliographies. The published *Shameful Inequalities* paper (arXiv:2412.16790) ref [11] reads
verbatim: *"P. Erdős, A. L. Rubin, and H. Taylor, Choosability in graphs, Congressus Numerantium 26
(1979), 125-127."* survey.md inherited this variant from that literature. **Use the 1980 / 125–157
form.**

### 2. Kostochka–Sidorenko — CONFIRMED as a problem-session abstract, Ann. Discrete Math. 51 (1992), 380

- **It is an abstract, not a paper.** Neither zbMATH nor Crossref indexes it as a document
  (searches on both returned nothing); the only Kostochka–Sidorenko joint item in zbMATH is
  Hamburger–Kostochka–Sidorenko, *J. Graph Theory* 30 (1999), 101–111. Kostochka's own publication
  list at `kostochk.web.illinois.edu/publ.html` contains **no** 1992 Annals of Discrete Mathematics
  entry and nothing mentioning Prachatice or a problem session — exactly what one expects of a
  one-page problem-session abstract that indexers do not treat as a publication.
- **The standard citation form is confirmed verbatim.** The published Kaul–Mudrock–Sharma paper
  (arXiv:2412.16790) ref [17] reads: *"A. V. Kostochka and A. Sidorenko, Problem Session of the
  Prachatice Conference on Graph Theory, Fourth Czechoslovak Symposium on Combinatorics, Graphs and
  Complexity, Ann. Discrete Math. 51 (1992), 380."* This matches survey.md exactly.
- **1990 vs 1992 resolved.** The Fourth Czechoslovak(ian) Symposium on Combinatorics, Graphs and
  Complexity was **held at Prachatice in 1990**; its proceedings were published as Annals of
  Discrete Mathematics **51** (eds. J. Nešetřil and M. Fiedler, North-Holland/Elsevier) in **1992**
  (Elsevier bookseries record). So "Kostochka and Sidorenko proposed this in 1990" (as Kirov–Naimi's
  abstract says) and "Ann. Discrete Math. 51 (1992), 380" are both correct: **pose 1990, publish 1992**.
- **Kirov–Naimi's own wording** (ref [7]) is: *"A. V. Kostochka, A. F. Sidorenko. Problem presented
  at the problem session. Fourth Czechoslovak Symposium on Cominatorics, Prachatice, 1990. Annals of
  Discrete Mathematics 51 (1992), 380."* (Note "Cominatorics" is a typo in the original PDF.)

### 3. Kirov–Naimi journal reference — CONFIRMED, no correction needed

survey.md's "Ars Combin. 124 (2016), 329–340" is **correct**, confirmed by three mutually
independent sources:

| Source | Record |
|---|---|
| dblp API | `journals/arscom/KirovN16` — "List Coloring And n-Monophilic Graphs", *Ars Comb.* **124**, 329-340, 2016 |
| zbMATH Open | Zbl 1413.05116 — "List coloring and $n$-monophilic graphs.", *Ars Comb.* **124**, 329-340 (2016) |
| Ramin Naimi's Occidental College CV (`sites.google.com/a/oxy.edu/rnaimi/cv`) | "List coloring and *n*-monophilic graphs (with Radoslav Kirov) … Ars Combinatoria **124** (2016), 329-340." |

The arXiv abstract page for 1004.5183 genuinely shows **no journal-ref** — the authors never
updated the arXiv metadata after publication. That absence is not evidence against the citation.
Ars Combinatoria assigns no DOIs, so there is no DOI for this paper. Caveat: the publisher-side
table of contents at `combinatoire.ca/ArsCombinatoria/Vol124.html` could not be fetched (TLS
certificate hostname mismatch), and the dblp *volume* page for Ars Combin. 124 did not surface the
entry in a page-summary fetch, but the dblp *API* record above is unambiguous.

### 4. CORRECTION — arXiv:2605.10861 is misattributed in survey.md

survey.md line: *"**[Allred & Mudrock]**, 'Enumeratively Chromatic-Choosable Theta Graphs',
arXiv:2605.10861 (2026)."* Both the authorship and the publication status are wrong.

- **Actual authors** (arXiv, zbMATH preprint record, and the ECA journal listing all agree):
  **Yanghong Chi, Seoju Lee, Fennec Morrissette, Jeffrey A. Mudrock, Gavin Nguyen, Benjamin Whatley.**
  Allred is not an author.
- **It is published**, not merely a preprint: *Enumerative Combinatorics and Applications* **6** (3)
  (2026), Article **S2R23** — confirmed on the ECA volumes page (`ecajournal.haifa.ac.il/Volumes.html`)
  and on Mudrock's own research page (`jmudrock.weebly.com/research.html`).
- The confusable neighbour is **Allred & Mudrock, "Enumerative chromatic choosability",
  arXiv:2505.05662** — a *different*, still-unpublished paper, which survey.md lists separately and
  correctly. Mudrock's own page lists it under "Submitted".
- (Aside: ECA article IDs restart per volume, so "ECA 5:3 Article S2R23" — a 2025 paper on pizza
  sharing — is a different article from "ECA 6:3 Article S2R23" and is not a contradiction.)

### 5. CORRECTION — the Vizing 1976 citation misparses a page number as a volume

survey.md gives: *"Diskret. Analiz. no. 29, Metody Diskret. Anal. v Teorii Kodov i Skhem **101**
(1976), 3–10."* The canonical MathSciNet form (MR0498216) is:

> Diskret. Analiz No. **29**: Metody Diskret. Anal. v Teorii Kodov i Shem (1976), **3–10, 101**.

**"101" is a trailing page number** (the Russian-journal summary page), not a volume. The issue
number is 29. The malformed variant also appears in the wild — arXiv:2605.10861 ref [25] renders it
as *"Diskretnyj Analiz, 101(29), 3–10"*, treating 101 as a volume. Cite it as "No. 29 … (1976),
3–10, 101" or simply "No. 29 (1976), 3–10".

### 6. CORRECTION — Kaul & Mudrock, Adv. Appl. Math. 123: article number is 102131, not 103121

survey.md gives "Adv. Appl. Math. 123 (2021), **103121**". The correct article number is **102131**
(digits transposed). Proof by DOI resolution:

- `https://doi.org/10.1016/j.aam.2020.102131` → resolves; CSL-JSON returns *"On the chromatic
  polynomial and counting DP-colorings of graphs", Advances in Applied Mathematics, vol 123,
  page 102131, article-number 102131*.
- `https://doi.org/10.1016/j.aam.2020.103121` → **HTTP 404**, does not exist.

This error is not survey.md's invention: it is propagated by the authors' own bibliographies
(arXiv:2605.10861 ref [15] also prints "123, 103121"). Use **102131**.

### 7. DISPUTED — Halberg et al., J. Combin. 15(4) (2024): 451–478 vs 451–468

Sources conflict, 2–2, and I could not obtain the printed article to settle it definitively:

| Says **451–478** | Says **451–468** |
|---|---|
| Publisher DOI metadata, `10.4310/joc.240906222651` (Int. Press, via DOI content negotiation) | Mudrock's research page, `jmudrock.weebly.com/research.html` |
| zbMATH Open, Zbl 1562.05104 | The paper's own citing bibliography in arXiv:2605.10861 ref [13] |

I have listed **451–478** because the two sources supporting it (the publisher's own registered DOI
metadata, and zbMATH's independent cataloguing of the printed issue) are bibliographically
authoritative, whereas author webpages and citing bibliographies routinely carry stale or copied
page ranges. Int. Press's article page (`intlpress.com`) returned HTTP 403 and could not be checked.
**Flag this one if it matters; do not treat 451–478 as certain.**

### 8. Minor — Woodall (2001) mischaracterized

survey.md says the earlier general list-coloring survey is "D. R. Woodall (2001), **on defective
choosability**." Woodall's 2001 item is "List colourings of graphs," *Surveys in Combinatorics 2001*,
LMS Lecture Note Ser. 288, CUP, pp. 269–301 (DOI 10.1017/CBO9780511721328.012) — a **general**
list-colouring survey. Defective choosability is a later Woodall topic, not this survey's subject.

### 9. Minor — Dong & Koh Handbook chapter: three discrepancies

survey.md: "*Handbook **on** the Tutte Polynomial and Related Topics* (CRC, **2021**), **232–266**."
Crossref (DOI 10.1201/9780429161612-11): title is "Handbook **of** the Tutte Polynomial and Related
Topics", chapter pages **213–251**, container date **2022-05-11**. The "2021" is plausibly the
copyright/first-electronic year and is a common citation; the page range 232–266 is not corroborated
by any source I checked.

### 10. Minor — sharpenings applied to survey.md entries that were otherwise correct

- Kaul, Mudrock, Sharma, Stratton, "DP-coloring Cartesian products of graphs": survey.md gives only
  "*J. Graph Theory* (2023)". Precise: **103** (2) (2023), 285–306.
- Kaul et al., "On the list color function threshold": DOI added (10.1002/jgt.23045).
- Birkhoff 1912: full DOI added (10.2307/1967597); Crossref lists start page 42, zbMATH confirms 42–46.
- The arXiv title of 1904.07697 is "On the Chromatic Polynomial and Counting DP-Colorings" (without
  "of graphs"); the published title adds "of graphs". Both are correct for their respective versions.

### 11. Everything in the Kirov–Naimi reference list (PDF p. 10) — ALL EIGHT VERIFIED

| # | Entry | Status |
|---|---|---|
| [1] | Diestel, *Graph Theory*, GTM 173 (1997) | ✅ zbMATH Zbl 0873.05001 (1997, GTM 173, translated from German) |
| [2] | Dirac, "On rigid circuit graphs," Abh. Math. Sem. Univ. Hamburg **25** (1961), 71–76 | ✅ DOI 10.1007/BF02992776; Zbl 0098.14703 |
| [3] | Donner, "On the number of list-colorings," JGT **16** (1992), 239–245 | ✅ DOI 10.1002/jgt.3190160307; Zbl 0754.05038; issue no. 3 |
| [4] | Erdős–Rubin–Taylor, Congr. Numer. **26** (1980), 125–157 | ✅ **Kirov–Naimi's form is the correct one** — see §1 |
| [5] | Galvin, JCTB **63** (1995), 153–158 | ✅ DOI 10.1006/jctb.1995.1011; Zbl 0826.05026; issue no. 1 |
| [6] | Gutner, Discrete Math. **159** (1996), 119–130 | ✅ DOI 10.1016/0012-365X(95)00104-5; Zbl 0865.05066; issue 1–3 |
| [7] | Kostochka–Sidorenko, Ann. Discrete Math. **51** (1992), 380 | ✅ Confirmed as problem-session abstract — see §2 |
| [8] | Tuza, Discuss. Math. Graph Theory **17**, No. 2 (1997), 161–228 | ✅ DOI 10.7151/dmgt.1049; Zbl 0923.05027 |

No errors were found in the Kirov–Naimi reference list. (Typo only: "Cominatorics" for
"Combinatorics" in ref [7], and "survery" for "survey" in ref [8], in the printed PDF.)

### 12. 2025–2026 arXiv entries — all four EXIST and were checked individually

The concern that these might be hallucinated is unfounded; all resolve, and the YYMM encoding is
consistent with today's date (2026-08-08).

| arXiv ID | Claimed by survey.md | Verified |
|---|---|---|
| 2505.05662 | Allred & Mudrock, "Enumerative Chromatic Choosability" (2025) | ✅ Correct. Submitted 8 May 2025. Still a preprint (Mudrock lists it as "Submitted"). |
| 2605.10861 | "[Allred & Mudrock]", "Enumeratively Chromatic-Choosable Theta Graphs" (2026) | ⚠️ Paper exists; **authors wrong**, and it is **published** in ECA 6(3), Art. S2R23 — see §4 |
| 2606.31702 | Vasudevan–Somasundaram–Narayanan, list-coloring/chromatic-choosability dynamic survey (2026) | ✅ Correct. Submitted 30 Jun 2026 14:10:19 UTC. Preprint, no journal-ref. |
| 2412.16790 | Kaul–Mudrock–Sharma, "Shameful Inequalities…", Graphs Combin. **42** (2026), Paper 46, doi:10.1007/s00373-026-03040-w | ✅ **Fully correct**, including the DOI. Journal metadata: vol 42, issue 3, article 46, online 13 Apr 2026. |
| 2409.06063 | Kaul & Mudrock, "Counting List Colorings of Unlabeled Graphs" (2024, rev. 2026) | ✅ Correct. v1 9 Sep 2024, v2 3 Feb 2026. Still submitted/unpublished. |
| 2512.13999 | Bhoja, Lean 4 Vizing / Misra–Gries (Dec 2025) | ✅ Correct. Submitted 16 Dec 2025. |

### 13. Items I could NOT verify

- **Ars Combinatoria vol. 124 publisher table of contents** — `combinatoire.ca` serves a TLS
  certificate for `*.cs.umanitoba.ca`, so the hostname does not match and the page could not be
  fetched. Immaterial: three independent sources confirm the citation (§3).
- **MathSciNet** — paywalled; not consulted directly. zbMATH Open was used as the substitute
  MathSciNet-adjacent authority throughout, plus Crossref DOI content negotiation.
- **Dong–Koh–Teo (2005) page count and ISBN** as stated in survey.md — not checked.
- **Gonthier, Notices of the AMS 55(11) (2008), 1382–1393** — volume/pages confirmed via multiple
  secondary citation databases, but no DOI exists in Crossref for that Notices issue and the AMS
  page was not fetched. Treat volume/pages as high-confidence, not primary-verified.
- **Halberg et al. page range** — genuinely unresolved, see §7.
- **All Mathlib / Lean Zulip / AFP-absence claims in survey.md §§1–4** — outside this pass's scope
  except for the two AFP entries listed above (both confirmed). survey.md's own caveat that these
  are "inferences from absence" still stands and should be re-checked against live Mathlib before
  publication.
