/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring

/-!
# Cacti: definitions

**Provenance.** This library formalizes the cactus ECC classification developed in
`ai_research_notes/` (2026-08-15) by the two AI research agents working on this repository.
It is **not** part of the Kirov–Naimi paper formalization in `ListColoring/`, which it imports
but must never be imported by. The mathematical source of record is
`ai_research_notes/FINAL_CACTI_ECC_HANDOFF.md`, reviewed in
`ai_research_notes/ADVERSARIAL_REVIEW_2026-08-15_HANDOFF.md`.

A **cactus** is a connected graph in which every edge lies in at most one cycle. We state
"at most one cycle through an edge" as: any two cycles (closed walks satisfying `Walk.IsCycle`)
that share an edge have equal edge sets. This is the form the block decomposition consumes, and
it avoids committing to a block-tree API before one is needed.
-/

namespace ListColoring

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- A **cactus**: a connected graph in which any two cycles sharing an edge coincide as edge
sets. Equivalently (not proved here yet), every block is an edge or a cycle. -/
def IsCactus : Prop :=
  G.Connected ∧
    ∀ ⦃u v : V⦄ (p : G.Walk u u) (q : G.Walk v v), p.IsCycle → q.IsCycle →
      ∀ e ∈ p.edges, e ∈ q.edges → p.edges.toFinset = q.edges.toFinset

/-- **At most one cycle**: any two cycles coincide as edge sets. Together with connectivity this
covers trees (no cycles at all) and unicyclic graphs. This is the structural side of the `k = 2`
cactus classification. -/
def HasAtMostOneCycle : Prop :=
  ∀ ⦃u v : V⦄ (p : G.Walk u u) (q : G.Walk v v), p.IsCycle → q.IsCycle →
    p.edges.toFinset = q.edges.toFinset

end ListColoring
