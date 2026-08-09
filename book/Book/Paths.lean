import VersoManual
import Book.Papers
import Monophilic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Paths and the Two Recurrences" =>

%%%
tag := "paths"
%%%

Source: [Path.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Path.lean), [Recurrence.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Recurrence.lean), [PathCount.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/PathCount.lean).

Section 3 of the paper computes the number of colorings of a path from a very particular shape of
list assignment, and everything about cycles follows from that computation. This chapter is about
getting the shape right.

# Building paths so that deletion is free

Mathlib has a path graph, on `Fin n`. It is not what we want. The counting argument peels one
terminal vertex off a path and recurses, and with `Fin n` that means proving `pathGraph (n+1)` minus
a vertex is isomorphic to `pathGraph n` and transporting everything across the isomorphism, every
time.

Instead, define paths by the operation the proof actually performs. A path of length `k+1` is a path
of length `k` with one new vertex attached to its current endpoint:

```lean
open SimpleGraph Monophilic in
example (k : ℕ) : pathG (k + 1) = (pathG k).addPendant (pathEnd k) := rfl
```

The payoff is that deleting the new vertex returns the shorter path *definitionally* — not up to
isomorphism, not up to a transport, but by `rfl`:

```lean
open SimpleGraph Monophilic in
example (k : ℕ) : (pathG (k + 1)).delNone = pathG k := rfl
```

so the deletion identity from the previous chapter applies with nothing in the way:

```lean
open Finset SimpleGraph Monophilic in
example (k : ℕ) (M : ListAssignment (PathV (k + 1))) :
    (pathG (k + 1)).col M
      = ∑ c ∈ M (pathEnd (k + 1)), (pathG k).col ((pathG (k + 1)).inducedList M c) :=
  col_pathG_succ k M
```

This design has one cost, and it is worth flagging because it bites repeatedly. `PathV (k+1)` is
*definitionally* `Option (PathV k)` but not *syntactically* equal to it. Tactics that match
syntactically — `rw`, `simp` — will silently fail to see through it, reporting that the target is
not type-correct under `instances` transparency. Tactics that unify at default transparency —
`exact`, `refine` — work fine. The rule that emerges is: state inductive step lemmas for an
arbitrary graph over `Option V`, where rewriting works, and cross into `PathV (k+1)` only by
term-mode application.

# The two shapes

An `(n, n-1)`-list assignment on a path gives the interior vertices a common palette `S` of `n`
colors and each terminal vertex an `(n-1)`-element subset of `S`. Since a terminal list has exactly
one color missing from `S`, such an assignment is determined, up to renaming, by the pair of missing
colors. The paper calls it **type A** when the two coincide and **type B** when they differ, and
writes `A_k` and `B_k` for the resulting counts.

Pictured, with $`S` the common interior palette and the two ends each missing one colour:

```diagram (cssWidth := "86%")
open Illuminate Diagram in
let v (x y : Float) : Diagram _ := translate x y (circle 8)
let e (x1 y1 : Float) (x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
let row (y : Float) (lbl : String) (l r : String) : List (Diagram _) :=
  let xs : List Float := [0, 70, 140, 210, 280]
  let verts := xs.map (fun x => v x y)
  let edges := [e 0 y 70 y, e 70 y 140 y, e 140 y 210 y, e 210 y 280 y]
  let labs := [translate 0 (y + 26) (text l), translate 280 (y + 26) (text r),
               translate 140 (y + 26) (text "S"),
               translate (-96) y (text lbl)]
  edges ++ verts ++ labs
(row 70 "type A" "S minus x" "S minus x" ++ row (-70) "type B" "S minus x" "S minus y")
  |>.foldl atop emptyDiagram
```

In type A the two ends are missing the *same* colour; in type B, different ones. Writing
`n = m + 2` throughout keeps everything in `ℕ` with no truncated subtraction. The recurrences are
then a two-line mutual definition:

```lean
open SimpleGraph Monophilic in
example (m k : ℕ) :
    pathA m (k + 1) = (m + 1) * pathB m k ∧
    pathB m (k + 1) = pathA m k + m * pathB m k :=
  ⟨pathA_succ m k, pathB_succ m k⟩
```

with base cases `A_0 = n-1` and `B_0 = n-2`. The base cases deserve a word. At length `0` the path
is a single vertex which is *both* terminals, so in type A its list is `S` minus one color and in
type B it is `S` minus two. That asymmetry is not an artifact; it is what makes the recurrences
start correctly, and it is also — as the next chapter shows — exactly where part (c) of Lemma 3
stops being true.

# Where the recurrences come from

The whole content of the computation is one observation about what peeling does to the shape.
Color the endpoint `c` and delete it: the neighbor loses `c` from its list, so the shorter path
again carries an `(n,n-1)`-assignment, now missing `c` at its new endpoint and still missing `y` at
the far end.

```lean
open SimpleGraph Monophilic in
example (k n x y c : ℕ) :
    (pathG (k + 1)).inducedList (pathAssign (k + 1) n x y) c = pathAssign k n c y :=
  inducedList_pathAssign k n x y c
```

Now count. In type A the two missing colors agree, `x = y`, and `c` ranges over `S` minus `x` — so
`c` is never `y`, and every one of the `n-1` terms is type B. That is `A_k = (n-1) B_{k-1}`, the
paper's equation (2). In type B the missing colors differ, so exactly one choice of `c` hits `y` and
produces a type A term while the other `n-2` are type B. That is `B_k = A_{k-1} + (n-2) B_{k-1}`,
equation (3).

Both cases at once:

```lean
open SimpleGraph Monophilic in
example (m k x y : ℕ) (hx : x < m + 2) (hy : y < m + 2) :
    (pathG k).col (pathAssign k (m + 2) x y) = if x = y then pathA m k else pathB m k :=
  col_pathAssign m k x y hx hy
```

# The closed forms

Subtracting the recurrences gives `A_k - B_k = (-1)^k`, the paper's equation (5) — the two counts
are always adjacent integers, with the order flipping at each step:

```lean
open SimpleGraph Monophilic in
example (m k : ℕ) : ((pathA m k : ℤ) - (pathB m k : ℤ)) = (-1) ^ k :=
  pathA_sub_pathB m k
```

and unwinding gives the closed form, stated with the denominator cleared:

```lean
open SimpleGraph Monophilic in
example (m k : ℕ) : ((m + 2) * pathA m k : ℤ) = (m + 1) * ((m + 1) ^ (k + 1) + (-1) ^ k) :=
  pathA_closed_form m k
```

The consequence that gets used is the one about which of the two is smaller, and it depends only on
the parity of `k`:

```lean
open SimpleGraph Monophilic in
example (m k : ℕ) :
    min (pathA m k) (pathB m k) = if Even k then pathB m k else pathA m k :=
  min_pathA_pathB_eq m k
```

# A note on method

The recurrences and the path graph were developed independently in this project, and were checked
against each other numerically before either was used in a proof. At `n = 3` the path of length one
carries `2` type A colorings and `3` type B colorings; the path of length two carries `6` and `5`.
Those agree with `A_1, B_1, A_2, B_2`, and the uniform count `n(n-1)^k` confirms separately that
`pathG` really is a path.

This is worth doing every time. An off-by-one in the indexing of `A_k` would not have shown up as a
type error, and would have cost far more to discover inside an induction than it cost to rule out
with four evaluations.
