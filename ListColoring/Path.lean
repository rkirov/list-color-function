/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Delete

/-!
# Paths, built by repeatedly attaching a pendant vertex

Kirov–Naimi §3 works with paths and computes list-coloring counts by peeling off a terminal vertex.
We therefore build paths in exactly that shape: `pathG (k+1)` is `pathG k` with one new vertex
attached to its current endpoint, so that deleting the new vertex returns `pathG k` *definitionally*
and the deletion identity of `ListColoring.Delete` applies with no transport.

`pathG k` is the path of **length `k`**, i.e. with `k + 1` vertices and `k` edges. Its two terminal
vertices are `pathEnd k` (the most recently attached one, always `none`) and `pathStart k`.

## Main definitions

* `SimpleGraph.addPendant G v` : `G` with a new vertex `none` attached to `v`
* `ListColoring.PathV k`, `ListColoring.pathG k` : the vertex type and graph of a path of length `k`
* `ListColoring.pathEnd k`, `ListColoring.pathStart k` : its two terminal vertices

## Main results

* `ListColoring.col_pathG_succ` : peeling the endpoint off a path,
  `col(P_{k+1}, M) = ∑ c ∈ M (pathEnd), col(P_k, M_c)`
-/

open Finset

-- Several adjacency lemmas below do not use the ambient decidability instances.
set_option linter.unusedSectionVars false

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Adjacency for `G` with a new vertex `none` joined to `v` alone. -/
def addPendantAdj (v : V) : Option V → Option V → Prop
  | none, none => False
  | none, some b => b = v
  | some a, none => a = v
  | some a, some b => G.Adj a b

/-- `G` with one new pendant vertex `none`, attached to `v`. -/
def addPendant (v : V) : SimpleGraph (Option V) where
  Adj := G.addPendantAdj v
  symm := ⟨by rintro (_ | a) (_ | b) h <;> simp_all [addPendantAdj, G.adj_comm]⟩
  loopless := ⟨by rintro (_ | a) h <;> simp_all [addPendantAdj]⟩

instance (v : V) : DecidableRel (G.addPendant v).Adj := fun a b =>
  match a, b with
  | none, none => inferInstanceAs (Decidable False)
  | none, some b => inferInstanceAs (Decidable (b = v))
  | some a, none => inferInstanceAs (Decidable (a = v))
  | some a, some b => inferInstanceAs (Decidable (G.Adj a b))

@[simp] lemma addPendant_adj_some_some {v a b : V} :
    (G.addPendant v).Adj (some a) (some b) ↔ G.Adj a b := Iff.rfl

@[simp] lemma addPendant_adj_none_some {v b : V} :
    (G.addPendant v).Adj none (some b) ↔ b = v := Iff.rfl

/-- Deleting the pendant vertex recovers the original graph. -/
@[simp] lemma delNone_addPendant (v : V) : (G.addPendant v).delNone = G := rfl

end SimpleGraph

namespace ListColoring

open SimpleGraph

/-- The vertex type of a path of length `k` (so `k + 1` vertices). -/
def PathV : ℕ → Type
  | 0 => Unit
  | k + 1 => Option (PathV k)

instance instDecidableEqPathV : (k : ℕ) → DecidableEq (PathV k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 => letI := instDecidableEqPathV k; inferInstanceAs (DecidableEq (Option (PathV k)))

instance instFintypePathV : (k : ℕ) → Fintype (PathV k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => letI := instFintypePathV k; inferInstanceAs (Fintype (Option (PathV k)))

/-- The terminal vertex of `pathG k` that was attached last. -/
def pathEnd : (k : ℕ) → PathV k
  | 0 => ()
  | _ + 1 => none

/-- The path of length `k`: `k + 1` vertices in a row. -/
def pathG : (k : ℕ) → SimpleGraph (PathV k)
  | 0 => ⊥
  | k + 1 => (pathG k).addPendant (pathEnd k)

instance instDecidableRelPathG : (k : ℕ) → DecidableRel (pathG k).Adj
  | 0 => fun _ _ => inferInstanceAs (Decidable False)
  | k + 1 =>
      letI := instDecidableEqPathV k
      letI := instDecidableRelPathG k
      inferInstanceAs (DecidableRel ((pathG k).addPendant (pathEnd k)).Adj)

/-- The successor case of `instDecidableRelPathG`, which instance search cannot reach on its own.

Another face of the `PathV (k+1)` / `Option (PathV k)` gap that keeps `rw` from firing on
`pathG (k + 1)`; see the module docstring of `ListColoring.PathColorable`.

`DecidableRel` is a reducible abbreviation for a `Π`-type, so synthesis unfolds it and turns the
goal into `(a b : Option (PathV k)) → Decidable ((pathG (k + 1)).Adj a b)` — note that the *binder
types have been reduced* while the graph has not. Resolving `instDecidableRelPathG` against that
abstracts its index over the two binders and leaves `PathV (?k a b) ≟ Option (PathV k)`, which
means inverting `PathV` at an unknown index; the unifier will not do it, and synthesis fails with
the instance sitting right there in the candidate list.

Ascribing `α` and `β` is what fixes it: the instance's binder types are then syntactically the
`Option (PathV k)` the goal already has, so `?k` is determined first-order before `pathG` is ever
examined. This is possible only because `DecidableRel` became **heterogeneous** in Lean 4.33
(`{α : Sort u} {β : Sort v} → (α → β → Prop) → _`) — which is also why nothing of the sort was
needed before 4.33, when synthesis matched the goal's head ahead of the binders. -/
instance instDecidableRelPathGSucc (k : ℕ) :
    DecidableRel (α := Option (PathV k)) (β := Option (PathV k)) (pathG (k + 1)).Adj :=
  instDecidableRelPathG (k + 1)

/-- The other terminal vertex of `pathG k`. -/
def pathStart : (k : ℕ) → PathV k
  | 0 => ()
  | k + 1 => some (pathStart k)

@[simp] lemma pathG_zero : pathG 0 = ⊥ := rfl

@[simp] lemma pathG_succ (k : ℕ) : pathG (k + 1) = (pathG k).addPendant (pathEnd k) := rfl

@[simp] lemma pathEnd_succ (k : ℕ) : pathEnd (k + 1) = none := rfl

/-- Deleting the last vertex of a path of length `k+1` gives the path of length `k`. -/
@[simp] lemma delNone_pathG_succ (k : ℕ) : (pathG (k + 1)).delNone = pathG k := rfl

/-- The list induced on `P_k` by giving color `c` to the endpoint of `P_{k+1}`: the color `c`
becomes unavailable at the old endpoint, and nowhere else. -/
lemma inducedList_pathG_succ (k : ℕ) (M : ListAssignment (PathV (k + 1))) (c : ℕ) (w : PathV k) :
    (pathG (k + 1)).inducedList M c w =
      if w = pathEnd k then (M (some w)).erase c else M (some w) := rfl

/-- **Peeling the endpoint off a path.** This is the recursion behind the `A_k`, `B_k` recurrences
of Lemma 3. -/
theorem col_pathG_succ (k : ℕ) (M : ListAssignment (PathV (k + 1))) :
    (pathG (k + 1)).col M
      = ∑ c ∈ M (pathEnd (k + 1)), (pathG k).col ((pathG (k + 1)).inducedList M c) :=
  col_eq_sum_delNone _ M

end ListColoring
