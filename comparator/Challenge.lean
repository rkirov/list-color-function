import Mathlib
/-!
# List coloring and enumerative chromatic-choosability — the challenge statements

The statement surface of the `graph_coloring` development, a formalization of

> Radoslav Kirov and Ramin Naimi, *List coloring and `n`-monophilic graphs*,
> Ars Combinatoria (arXiv:1004.5183).

Everything is stated exactly as in the library; proofs and two decidability instances are
`sorry`, so "declaration uses `sorry`" is expected.  The comparator checks these statements
against `Submission.lean`, which imports the library; `config.json` lists what is claimed.
-/

open Finset

universe u

namespace SimpleGraph

/-! ### 1. Colouring a graph

`col(G, L)` counts the proper colourings that draw each vertex's colour from its own finite list
`L v`; `col(G, n)` is the special case where every list is the palette `{0, …, n-1}`.  Every claim
below is a statement about these two counts.
-/

/-- A **list assignment** for a graph on `V` gives each vertex a finite set of allowed colors. -/
abbrev ListAssignment (V : Type u) : Type u := V → Finset ℕ

/-- The constant list assignment sending every vertex to `{0, 1, …, n-1}`; the paper's `[n]`. -/
def constList (V : Type u) (n : ℕ) : ListAssignment V := fun _ => range n

/-- `f` is a proper coloring of `G`: adjacent vertices get distinct colors. -/
def IsProperColoring {V : Type*} (G : SimpleGraph V) (f : V → ℕ) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → f v ≠ f w

/-- Unlisted: only so that `colorings` can be written as a `Finset.filter`. -/
instance instDecidableIsProperColoring {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [Fintype V] (f : V → ℕ) : Decidable (G.IsProperColoring f) := by
  unfold IsProperColoring; infer_instance

/-- The finset of proper colorings of `G` drawn from the lists `L`. -/
def colorings {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) : Finset (V → ℕ) :=
  (Fintype.piFinset L).filter G.IsProperColoring

/-- `col(G, L)`: the number of proper colorings of `G` from the list assignment `L`. -/
def col {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) : ℕ := (G.colorings L).card

/-- `col(G, n)`: the number of proper colorings of `G` from the constant list `{0, …, n-1}`. -/
def colConst {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : ℕ := G.col (constList V n)

/-! ### 2. The chromatic polynomial

Defined by the Whitney subset expansion `∑_{S ⊆ E(G)} (-1)^{|S|} X^{c(S)}`, where `c(S)` counts
the connected components of the spanning subgraph with edge set `S`; the claim is that evaluating
it at `n` returns `col(G, n)`. -/

/-- Adjacency in `fromEdgeSet S` is decidable when `S` comes from a `Finset` of edges. -/
instance decidableRelFromEdgeSetCoe {V : Type*} [DecidableEq V] (S : Finset (Sym2 V)) :
    DecidableRel (fromEdgeSet (S : Set (Sym2 V))).Adj := sorry

/-- `c(S)`: the number of connected components of the spanning subgraph of `V` whose edges are
exactly the non-loop elements of `S`. -/
def compCount {V : Type*} [Fintype V] [DecidableEq V] (S : Finset (Sym2 V)) : ℕ :=
  Fintype.card (fromEdgeSet (S : Set (Sym2 V))).ConnectedComponent

/-- The **chromatic polynomial** of `G`, defined by the Whitney subset expansion
`∑_{S ⊆ E(G)} (-1)^{|S|} X^{c(S)}`. -/
noncomputable def chromaticPolynomial {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Polynomial ℤ :=
  ∑ S ∈ G.edgeFinset.powerset, (-1) ^ #S * Polynomial.X ^ compCount S

/-- **Evaluation of the chromatic polynomial counts colorings.** -/
theorem eval_chromaticPolynomial {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) :
    (G.chromaticPolynomial).eval (n : ℤ) = (G.colConst n : ℤ) := sorry

/-! ### 3. Lists instead of a palette

`G` is **`n`-choosable** if every `n`-list assignment admits a colouring, and **enumeratively
chromatic-choosable at `n`** if the constant assignment *minimizes* the number of colourings — the
paper's subject, claimed below to be exactly the condition `P_ℓ(G, n) = P(G, n)`.  Two
separations are claimed after it: the regime `χ(G) ≤ n < χ_ℓ(G)` is nonempty (Erdős–Rubin–Taylor),
and above `χ_ℓ` the property still fails for some graph at every `k ≥ 2` (the paper's §5).
-/

/-- An **`n`-list assignment** gives every vertex a list of exactly `n` colors. -/
def IsNListAssignment {V : Type*} (L : ListAssignment V) (n : ℕ) : Prop := ∀ v, (L v).card = n

/-- `G` is **`n`-choosable** if it admits a coloring from every `n`-list assignment. -/
def Choosable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Prop :=
  ∀ L : ListAssignment V, IsNListAssignment L n → 0 < G.col L

/-- `G` is **enumeratively chromatic-choosable at `n`** when the number of list colorings is
minimized by the constant list assignment, among all assignments of lists of size `n`. -/
def ECCAt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Prop :=
  ∀ L : ListAssignment V, IsNListAssignment L n → G.colConst n ≤ G.col L

/-- `G` is **enumeratively chromatic-choosable** when it is enumeratively chromatic-choosable at
every `n`.  Below `χ(G)` the pointwise property is vacuous, so quantifying over all `n` rather
than over `n ≥ χ(G)` costs nothing. -/
def ECC {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ n, G.ECCAt n

/-- The set of coloring counts achievable by `n`-list assignments. -/
def colCounts {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Set ℕ := {c | ∃ L : ListAssignment V, IsNListAssignment L n ∧ G.col L = c}

/-- **The list color function** `P_ℓ(G, n)`: the least number of colorings achievable by any
`n`-list assignment. -/
noncomputable def listColorFunction {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) : ℕ := sInf (G.colCounts n)

/-- **`P_ℓ(G, n) = P(G, n)` with a genuine polynomial on the right.** -/
theorem ecc_iff_listColorFunction_eq_eval {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (n : ℕ) :
    G.ECCAt n ↔ (G.listColorFunction n : ℤ) = (G.chromaticPolynomial).eval (n : ℤ) := sorry

end SimpleGraph

namespace SimpleGraph.ERT

/-- Adjacency in a complete bipartite graph is decidable. -/
instance instDecidableRelCompleteBipartiteAdj (V W : Type*) :
    DecidableRel (completeBipartiteGraph V W).Adj := sorry

/-- `K_{n,nⁿ}`, the complete bipartite graph whose right side is indexed by the functions
`Fin n → Fin n`. -/
abbrev K (n : ℕ) : SimpleGraph (Fin n ⊕ (Fin n → Fin n)) :=
  completeBipartiteGraph (Fin n) (Fin n → Fin n)

/-- `K_{n,nⁿ}` is **not** `n`-choosable, witnessed by `L₀`. -/
theorem not_choosable (n : ℕ) : ¬ (K n).Choosable n := sorry

/-- `K_{n,nⁿ}` is `n`-colorable once `2 ≤ n`.  Together with `not_choosable` this is the
Erdős–Rubin–Taylor separation: `χ(K_{n,nⁿ}) ≤ n < χ_ℓ(K_{n,nⁿ})`. -/
theorem colorable (n : ℕ) (hn : 2 ≤ n) : (K n).Colorable n := sorry

end SimpleGraph.ERT

namespace SimpleGraph.KN5

/-- **Kirov–Naimi, §5.**  For every `k ≥ 2` there is a graph that is `k`-choosable but not
enumeratively chromatic-choosable at `k`. -/
theorem exists_choosable_not_ecc_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ (V : Type) (iF : Fintype V) (iD : DecidableEq V) (G : SimpleGraph V)
      (iA : DecidableRel G.Adj), @Choosable V iF iD G iA k ∧ ¬ @ECCAt V iF iD G iA k := sorry

end SimpleGraph.KN5

namespace SimpleGraph

/-! ### 4. Chordal graphs and Kostochka–Sidorenko

Coning over a clique preserves enumerative chromatic-choosability (Kirov–Naimi's Lemma 1), and a
finite graph is built from nothing by such attachments exactly when it is **chordal** — Dirac's
theorem, proved in the library — which is what lets Kostochka–Sidorenko be claimed in its own
terms.
-/

/-- **A chordal graph.** Every cycle of length at least `4` has a chord: an edge of the graph
joining two vertices of the cycle which is not itself an edge of the cycle.  Phrased through
Mathlib's `SimpleGraph.Walk.IsChordless`. -/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ {u : V} (c : G.Walk u u), c.IsCycle → 4 ≤ c.length → ¬ c.IsChordless

/-- **The Kostochka–Sidorenko theorem.** *Every chordal graph is enumeratively
chromatic-choosable at `n`, for every `n`.* -/
theorem ecc_of_isChordal {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsChordal) (n : ℕ) : G.ECCAt n := sorry

/-! ### 5. Theorem 1: every cycle is enumeratively chromatic-choosable at `n`

The paper's main theorem, claimed on Mathlib's `SimpleGraph.cycleGraph` so that the statement
involves no construction of this development.  The two pendant attachments below are §6's
vocabulary: iterated, they grow a core back into a graph, and `addPendantPair` over a cycle
builds the theta graph.
-/

/-- **Theorem 1 of Kirov–Naimi: every cycle is enumeratively chromatic-choosable at `n`, for
every `n ≥ 2`.**  `cycleGraph n` is Mathlib's cycle graph on `n` vertices. -/
theorem ecc_cycleGraph_of_three_le {n m : ℕ} (hn : 3 ≤ n) :
    (cycleGraph n).ECCAt (m + 2) := sorry

/-- Adjacency for `G` with a new vertex `none` joined to `v` alone. -/
def addPendantAdj {V : Type*} (G : SimpleGraph V) (v : V) : Option V → Option V → Prop
  | none, none => False
  | none, some b => b = v
  | some a, none => a = v
  | some a, some b => G.Adj a b

/-- `G` with one new pendant vertex `none`, attached to `v`. -/
def addPendant {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph (Option V) where
  Adj := G.addPendantAdj v
  symm := ⟨by rintro (_ | a) (_ | b) h <;> simp_all [addPendantAdj, G.adj_comm]⟩
  loopless := ⟨by rintro (_ | a) h <;> simp_all [addPendantAdj]⟩

/-- Adjacency for `G` with a new vertex `none` joined to both `u` and `v` (and nothing else). -/
def addPendantPairAdj {V : Type*} (G : SimpleGraph V) (u v : V) : Option V → Option V → Prop
  | none, none => False
  | none, some b => b = u ∨ b = v
  | some a, none => a = u ∨ a = v
  | some a, some b => G.Adj a b

/-- `G` with one new vertex `none`, joined to both `u` and `v`. -/
def addPendantPair {V : Type*} (G : SimpleGraph V) (u v : V) : SimpleGraph (Option V) where
  Adj := G.addPendantPairAdj u v
  symm := ⟨by rintro (_ | a) (_ | b) h <;> simp_all [addPendantPairAdj, G.adj_comm]⟩
  loopless := ⟨by rintro (_ | a) h <;> simp_all [addPendantPairAdj]⟩

instance instDecidableRelAddPendantPair {V : Type*} (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (u v : V) : DecidableRel (G.addPendantPair u v).Adj := fun a b =>
  match a, b with
  | none, none => inferInstanceAs (Decidable False)
  | none, some b => inferInstanceAs (Decidable (b = u ∨ b = v))
  | some a, none => inferInstanceAs (Decidable (a = u ∨ a = v))
  | some a, some b => inferInstanceAs (Decidable (G.Adj a b))

/-! ### 6. `2`-choosability: Rubin's theorem

Choosability is unchanged by attaching or removing pendant vertices, so a connected graph may be
replaced by its **core**: the graph of which it is a `pendantTower`.  `CoreIs` spells that out,
and `CoreIsVertex`, `CoreIsEvenCycle`, `CoreIsTheta` are the three cases Rubin's theorem names —
a single vertex is `⊥` on `Fin 1`, a cycle is Mathlib's `cycleGraph`, and `θ_{2,2,2m}` is
`thetaGraph m`, the cycle `C_{2m+2}` with one extra vertex attached to `0` and `2`.  Rubin's
theorem is proved in this development and claimed in full, both directions.
-/

/-- The vertex type of `G` after `k` successive pendant attachments: `V` with `k` extra points. -/
def TowerV (V : Type u) : ℕ → Type u
  | 0 => V
  | k + 1 => Option (TowerV V k)

/-- The data specifying a tower of `k` pendant attachments: for each step, the already-existing
vertex at which the new pendant vertex is attached. -/
def TowerData (V : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => TowerData V k × TowerV V k

/-- **A tower of pendant attachments.** `pendantTower G k d` is the graph obtained from `G` by
attaching `k` pendant vertices one after another, the `i`-th of them at the vertex recorded in `d`
(which may itself be one of the earlier new vertices). -/
def pendantTower {V : Type u} (G : SimpleGraph V) :
    (k : ℕ) → TowerData V k → SimpleGraph (TowerV V k)
  | 0, _ => G
  | k + 1, d => (pendantTower G k d.1).addPendant d.2

/-- **The core of `G` is `H`**: `G` is `H` with a finite tower of pendant vertices attached — the
reverse reading of "delete degree-one vertices until none remain".  Up to isomorphism, because the
tower lives on its own vertex type. -/
def CoreIs {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  ∃ (k : ℕ) (d : TowerData W k), Nonempty (G ≃g pendantTower H k d)

/-- `G` **contains** a copy of `K`: an injection of the vertices of `K` into those of `G` carrying
edges to edges. Only a *subgraph* is asked for, not an induced one, which is all that a
choosability argument ever needs. -/
def Contains {V W : Type*} (G : SimpleGraph V) (K : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ a b, K.Adj a b → G.Adj (f a) (f b)

/-- `θ_{2,2,2m}`, on Mathlib's cycle graph: the cycle `C_{2m+2}` together with one extra vertex
joined to `0` and `2`, which lie at distance two on the cycle.  The three arms between the branch
vertices `some 0` and `some 2` have lengths `2`, `2` and `2m`. -/
def thetaGraph (m : ℕ) : SimpleGraph (Option (Fin (2 * m + 2))) :=
  (cycleGraph (2 * m + 2)).addPendantPair 0 2

instance instDecidableRelThetaGraph (m : ℕ) : DecidableRel (thetaGraph m).Adj :=
  inferInstanceAs (DecidableRel ((cycleGraph (2 * m + 2)).addPendantPair 0 2).Adj)

/-- **The core of `G` is a single vertex**: Mathlib's `⊥` on `Fin 1`.  Equivalently, `G` is a
tree.  First alternative of Rubin's theorem, and of Theorem 2. -/
def CoreIsVertex {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := CoreIs G (⊥ : SimpleGraph (Fin 1))

/-- **The core of `G` is an even cycle.**  Second alternative of Rubin's theorem. -/
def CoreIsEvenCycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ n, Even n ∧ 4 ≤ n ∧ CoreIs G (cycleGraph n)

/-- **The core of `G` is `θ_{2,2,2m}` for some `m ≥ 1`.**  Third alternative of Rubin's
theorem. -/
def CoreIsTheta {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ m, 1 ≤ m ∧ CoreIs G (thetaGraph m)

/-- **Rubin's theorem.**

> A connected graph is `2`-choosable iff its core is a single vertex, an even cycle, or
> `θ_{2,2,2m}` for some `m ≥ 1`.

A. L. Rubin, in Erdős–Rubin–Taylor, *Choosability in graphs*, Congr. Numer. **26** (1980),
125–157.  The paper cites it; this development proves it. -/
theorem rubinTheorem {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) :
    G.Choosable 2 ↔ (CoreIsVertex G ∨ CoreIsEvenCycle G ∨ CoreIsTheta G) := sorry

/-! ### 7. Enumerative chromatic-choosability at `2`: Theorem 2

`K₂,₃ = θ_{2,2,2}` is enumeratively chromatic-choosable at `2` (Kirov–Naimi's Lemma 6) and
`θ_{2,2,2m}` with `m ≥ 2` is not; with §5's cycles, §4's chordal graphs and the core reduction
(Lemma 5), that turns §6's list into Theorem 2's.  Where Rubin says "even cycle", Theorem 2 says
"cycle": odd cycles qualify by not being `2`-colourable at all, which is the fourth alternative,
`HasOddCycle`.
-/

/-- **The core of `G` is a cycle**: Mathlib's `cycleGraph n`, a genuine cycle once `3 ≤ n`.
No parity restriction: Theorem 2 says "is a cycle", not "is an even cycle".  Second alternative
of Theorem 2. -/
def CoreIsCycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ n, 3 ≤ n ∧ CoreIs G (cycleGraph n)

/-- **The core of `G` is `K₂,₃`**, which is `thetaGraph 1 = θ_{2,2,2}`.  Third alternative of
Theorem 2. -/
def CoreIsK23 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := CoreIs G (thetaGraph 1)

/-- **`G` contains an odd cycle**: a subgraph copy of `cycleGraph n` for an odd `n ≥ 3`.  Fourth
alternative of Theorem 2. -/
def HasOddCycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ n, Odd n ∧ 3 ≤ n ∧ Contains G (cycleGraph n)

/-- **Theorem 2 of Kirov–Naimi, with no hypothesis beyond connectivity.**

> A connected graph is 2-monophilic iff its core is a single vertex, is a cycle, is `K₂,₃`, or
> contains an odd cycle.

The paper's wording; "2-monophilic" is `SimpleGraph.ECCAt G 2`.  Kirov–Naimi, Ars Combin. **124**
(2016), 329–340, Theorem 2.  Rubin's theorem, which the paper quotes, is claimed above. -/
theorem ecc_two_iff {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) :
    G.ECCAt 2 ↔ CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨ HasOddCycle G := sorry

/-! ### 8. Every graph, eventually

Donner's theorem.  The library proves more than is claimed: the explicit threshold
`n > 2^{|E(G)|}` suffices (`SimpleGraph.ecc_of_two_pow_lt`). -/

/-- **Donner's theorem (1992).** Every graph is enumeratively chromatic-choosable at `k` for all
sufficiently large `k`. -/
theorem exists_ecc_forall_ge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∃ N, ∀ k, N ≤ k → G.ECCAt k := sorry

end SimpleGraph

/-! ### 9. Cacti

Not from the paper.  The cactus classification is the result of the 2026-08 AI research
collaboration on this repository; source of record `ai_research_notes/FINAL_CACTI_ECC_HANDOFF.md`,
formalized in `Cacti/`.  A **cactus** is a connected graph in which any two cycles that share an
edge are the same cycle — equivalently, every block is an edge or a cycle.  Above `2` every cactus
is enumeratively chromatic-choosable; at `2` the property is an exact structural condition, and
that is the whole spectrum.
-/

namespace ListColoring

open SimpleGraph

/-- A **cactus**: a connected graph in which any two cycles sharing an edge coincide as edge
sets. -/
def IsCactus {V : Type} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  G.Connected ∧
    ∀ ⦃u v : V⦄ (p : G.Walk u u) (q : G.Walk v v), p.IsCycle → q.IsCycle →
      ∀ e ∈ p.edges, e ∈ q.edges → p.edges.toFinset = q.edges.toFinset

/-- **At most one cycle**: any two cycles coincide as edge sets.  With connectivity this covers
trees (no cycles at all) and unicyclic graphs. -/
def HasAtMostOneCycle {V : Type} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ ⦃u v : V⦄ (p : G.Walk u u) (q : G.Walk v v), p.IsCycle → q.IsCycle →
    p.edges.toFinset = q.edges.toFinset

/-- **Every cactus is `k`-ECC for `k ≥ 4`** (handoff §6, UM-108).  The block induction over the
cut-vertex decomposition, run on the pair invariant `A² ≤ x_c · x_d`; the transfer-matrix bound
supplies it on a cycle block, and the slack `k - 3 ≥ 1` pays for the weight peeling. -/
theorem isCactus_ecc_of_four_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hk : 4 ≤ k) (hG : IsCactus G) : G.ECCAt k := sorry

/-- **Every cactus is `3`-ECC** (handoff §5, UM-105).  At `k = 3` the pair invariant is false and
the induction carries GM dominance instead; its cycle blocks are the balanced core of an odd cycle
(UM-025) and the full tensor capacity of an even one (UM-104). -/
theorem isCactus_ecc_three {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCactus G) : G.ECCAt 3 := sorry

/-- **Every cactus is `k`-ECC for `k ≥ 3`**: the two cases above. -/
theorem isCactus_ecc_of_three_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k) (hG : IsCactus G) : G.ECCAt k := sorry

/-- **The `k = 2` cactus classification** (handoff §3): a cactus is `2`-ECC iff it has at most one
cycle or contains an odd cycle — `SimpleGraph.HasOddCycle`, the same predicate §7's Theorem 2 is
stated with.  Routes through Theorem 2 and Rubin's theorem above. -/
theorem isCactus_ecc_two_iff {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCactus G) :
    G.ECCAt 2 ↔ HasAtMostOneCycle G ∨ SimpleGraph.HasOddCycle G := sorry

/-- **The full cactus spectrum** (handoff Theorem A): a cactus is enumeratively
chromatic-choosable iff it has at most one cycle or contains an odd cycle.  Below `2` the property
is vacuous, at `2` it is the classification, and above it every cactus qualifies. -/
theorem isCactus_ecc_iff {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCactus G) :
    G.ECC ↔ HasAtMostOneCycle G ∨ SimpleGraph.HasOddCycle G := sorry

end ListColoring
