import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

-- Warnings are promoted to errors, so that anything Verso or Lean reports about a rendered
-- docstring breaks the build instead of passing quietly. Since that is wanted in every chapter,
-- `warningAsError` lives in the package's `leanOptions` (see `book/lakefile.lean`); it is repeated
-- here so that the reason travels with the file that most depends on it.
set_option warningAsError true
-- ... but not the cosmetic linters, which have nothing to do with dangling references. Library
-- docstrings are Markdown: they carry their own line widths, and they write bold as `**bold**`,
-- which Verso's markup linter objects to. The emphasis linter therefore has to be off here, and
-- only here — the book's own prose is kept clean of it and is linted normally.
set_option verso.code.warnLineLength 0
set_option linter.verso.markup.emph false

/-!
### The dangling-reference check

`{docstring}` guarantees that the declaration it names *exists* — an unknown constant is an error,
and so is a missing docstring, since `verso.docstring.allowMissing` defaults to `false`. It does
**not** guarantee that the names *inside* the rendered docstring exist. Verso elaborates every
backticked span of a docstring through `tryElabInlineCode`, whose failure path is `logWarningAt`;
but the last elaborator in its chain is `tryElabInlineCodeTerm (ignoreElabErrors := true)`, which
discards the message log and succeeds regardless. So an unresolvable name renders as ordinary
highlighted code, nothing is ever logged, and `warningAsError` has nothing to promote. Checked
empirically against Verso `v4.33.0`: a docstring referring to `Nonexistent.name` builds green.

The check below closes that hole directly. It walks every declaration docstring in the
`ListColoring` library, picks out the backticked spans that are shaped like qualified names in the
`ListColoring`, `SimpleGraph` or `Mathlib` namespaces, and reports any that name neither a constant
nor a module. Spans that are not name-shaped — `θ_{2,2,2m}`, `col(C,2) = 2`, `n ≥ 2` — are ignored,
so the check never fires on prose.
-/

section DanglingReferences

open Lean Elab Command

/-- The even-indexed gaps between backticks on a line: the backticked spans. -/
private def backtickSpans : List String → List String
  | _ :: b :: rest => b :: backtickSpans rest
  | _ => []

/-- A single component of a Lean identifier, conservatively. -/
private def isIdentPart (s : String) : Bool :=
  !s.isEmpty && (s.toList.head!.isAlpha) &&
    s.all fun c => c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'

/-- A backticked span shaped like a qualified name in a namespace this book cares about. Anything
else — mathematical notation, prose, file names — yields `none` and is not checked. -/
private def qualifiedName? (s : String) : Option Name :=
  match s.splitOn "." with
  | root :: second :: rest =>
      if (root :: second :: rest).all isIdentPart &&
          (root == "ListColoring" || root == "SimpleGraph" || root == "Mathlib") then
        some s.toName
      else none
  | _ => none

/--
Known-bad references, with the reason each is tolerated. An entry here is a defect in the library
that this book cannot fix — `ListColoring/` is not the book's to edit — and deleting the entry is
what closes it. The list is expected to shrink to nothing.

Currently empty: the one entry it held — `isArm_of_walk` claiming its indexing was by a
non-existent `ListColoring.getVert`, when the function is Mathlib's `SimpleGraph.Walk.getVert` —
was found by this very check and has been fixed in the library.
-/
private def toleratedRefs : List (Name × Name) := []

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let mut bad : Array (Name × Name) := #[]
  for i in [0:mods.size] do
    if (`ListColoring).isPrefixOf mods[i]! then
      for c in data[i]!.constNames do
        if let some doc ← liftCoreM (findDocString? env c) then
          for line in doc.splitOn "\n" do
            for span in backtickSpans (line.splitOn "`") do
              if let some n := qualifiedName? span then
                if !env.contains n && !mods.contains n &&
                    !toleratedRefs.contains (c, n) then
                  bad := bad.push (c, n)
  for (c, n) in bad do
    logError m!"dangling reference `{n}` in the docstring of `{c}`: \
      it names neither a constant nor a module. Fix the docstring, or add it to `toleratedRefs` \
      in Book/Reference.lean with a reason."

end DanglingReferences

#doc (Manual) "The Declarations" =>

%%%
tag := "reference"
%%%

Every displayed statement elsewhere in this book is an `example` whose proof is a theorem of the
development. That keeps the *statements* honest: if a theorem is renamed or its hypotheses change,
the book stops building.

It does not keep the *prose* honest. A sentence that names a declaration in backticks is just text,
and it survives the deletion of the thing it names. This chapter closes that gap by rendering the
declarations themselves, with their own documentation, straight out of the library. Every
`{docstring}` block below fails the build if the declaration it names has been renamed or deleted,
or if its documentation has been removed.

That still leaves the names *inside* those docstrings, which Verso renders without checking — its
elaborator for backticked spans falls back to one that ignores elaboration errors, so an
unresolvable name is highlighted and passed over in silence. The chapter's source therefore carries
a small command that walks every declaration docstring in the library, picks out the spans shaped
like qualified names, and errors on any that name neither a constant nor a module. It found one,
and it is listed there.

It is also, and mainly, a reference: the vocabulary and the headline results in one place, in the
words the library uses for them.

# Counting list colourings

The whole development rests on one number — the count of proper colourings drawing each vertex's
colour from its own list — and on the special case where all the lists agree.

{docstring SimpleGraph.ListAssignment}

{docstring SimpleGraph.constList}

{docstring SimpleGraph.IsProperColoring}

{docstring SimpleGraph.colorings}

{docstring SimpleGraph.col}

{docstring SimpleGraph.colConst}

{docstring SimpleGraph.IsNListAssignment}

# The two properties

Choosability asks for *some* colouring from every list assignment; enumerative
chromatic-choosability asks that the uniform assignment be the worst case for the *count*. The
second implies the first whenever the uniform count is positive, and is strictly stronger.

{docstring SimpleGraph.Choosable}

{docstring SimpleGraph.ECCAt}

{docstring SimpleGraph.ECC}

{docstring SimpleGraph.colCounts}

{docstring SimpleGraph.listColorFunction}

{docstring SimpleGraph.compCount}

{docstring SimpleGraph.chromaticPolynomial}

# Graph constructions

Almost every graph in the development is built by coning: attach a new vertex adjacent to a chosen
set of old ones. Over a clique that gives the chordal machinery, over a singleton it gives pendant
vertices and hence cores, and twice over the ends of a path it gives the theta graphs.

{docstring SimpleGraph.coneOn}

{docstring SimpleGraph.addPendant}

{docstring SimpleGraph.TowerData}

{docstring SimpleGraph.pendantTower}

{docstring SimpleGraph.IsChordal}

{docstring SimpleGraph.cliqueTower}

{docstring ListColoring.pathG}

{docstring ListColoring.closePath}

{docstring ListColoring.theta}

{docstring ListColoring.thetaGen}

{docstring ListColoring.gtheta}

{docstring ListColoring.gsize}

{docstring SimpleGraph.ERT.K}

# Cores, and the alternatives of the two classifications

The core of a graph is what remains after repeatedly deleting vertices of degree one. Read
backwards, that says the graph is its core with a tower of pendant vertices on top, which is the
form a formalization can use directly.

{docstring ListColoring.Contains}

{docstring ListColoring.CoreIs}

{docstring ListColoring.CoreIsVertex}

{docstring ListColoring.CoreIsCycle}

{docstring ListColoring.CoreIsEvenCycle}

{docstring ListColoring.CoreIsK23}

{docstring ListColoring.CoreIsTheta}

{docstring ListColoring.HasOddCycle}

{docstring ListColoring.RubinFamily}

{docstring ListColoring.ValidShape}

{docstring ListColoring.GoodShape}

{docstring ListColoring.ValidArms}

{docstring ListColoring.GoodArms}

{docstring ListColoring.HasCore}

# The ten claims

These are the theorems `comparator/Challenge.lean` states, in its own order;
{ref "readingchallenge"}[the guide to that file] explains why these ten.

{docstring SimpleGraph.eval_chromaticPolynomial}

{docstring SimpleGraph.ecc_iff_listColorFunction_eq_eval}

{docstring SimpleGraph.ERT.not_choosable}

{docstring SimpleGraph.ERT.colorable}

{docstring SimpleGraph.KN5.exists_choosable_not_ecc_of_two_le}

{docstring SimpleGraph.ecc_of_isChordal}

{docstring SimpleGraph.ecc_cycleGraph_of_three_le}

{docstring ListColoring.rubinTheorem}

{docstring ListColoring.ecc_two_iff}

{docstring SimpleGraph.exists_ecc_forall_ge}

# Transport along cores

Kirov and Naimi's Lemma 5 and its choosability counterpart are what make a classification of cores
a classification of graphs.

{docstring SimpleGraph.ecc_pendantTower_iff}

{docstring SimpleGraph.choosable_pendantTower_iff}

{docstring ListColoring.ecc_iff_of_coreIs}

{docstring ListColoring.choosable_iff_of_coreIs}

# Rubin's theorem

Rubin's characterization of the `2`-choosable graphs is a named proposition here as well as a
theorem, so that the statements which consume it are written against the statement rather than the
proof. It is not an axiom and it is not a hypothesis tailored to what Theorem 2 needs. The
theorem itself is {name ListColoring.rubinTheorem}`rubinTheorem`, above; what follows are its
pieces.

{docstring ListColoring.RubinTheorem}

{docstring ListColoring.choosable_two_of_rubinAlternatives}

{docstring ListColoring.choosable_two_of_rubinFamily}

## The theta graphs

The colouring half of the forward direction: which theta graphs are `2`-choosable. The three-arm
case is what Rubin's own case analysis consumes; the arity-`n` case is what $`K_{2,4}` forced.

{docstring ListColoring.ThetaClassification}

{docstring ListColoring.thetaClassification}

{docstring ListColoring.not_choosable_two_thetaGen}

{docstring ListColoring.choosable_two_thetaGen_iff}

{docstring ListColoring.choosable_two_gtheta_iff}

{docstring ListColoring.not_choosable_two_gtheta_of_four}

{docstring ListColoring.not_choosable_two_K24}

The inductions along an arm of unbounded length — the content of the phrase "it is then easy to
check" — are these:

{docstring ListColoring.alt_chain}

{docstring ListColoring.const_block}

{docstring ListColoring.armBlockLists_forced}

## The other obstructions

Two cycles that meet in at most one vertex, and the forcing mechanism behind them. The connecting
path is not optional: two *disjoint* even cycles are `2`-choosable.

{docstring ListColoring.forced_chain}

{docstring ListColoring.no_coloring_of_cycle_chain}

{docstring ListColoring.not_choosable_two_of_dumbbell}

{docstring ListColoring.not_choosable_two_of_figureEight}

{docstring ListColoring.not_choosable_two_of_cycles_meet_le_one}

{docstring ListColoring.not_choosable_of_contains}

{docstring ListColoring.not_choosable_two_of_contains_odd_cycle}

## The structural half

Rubin's steps 1 to 6, and the two recognition lemmas that turn their walk data into an isomorphism.
No ear decomposition, no Menger and no `2`-connectivity appears anywhere below.

{docstring ListColoring.exists_isCycle_of_two_le_degree}

{docstring ListColoring.exists_shortest_isCycle}

{docstring ListColoring.exists_connecting_path_of_cycle_of_choosable}

{docstring ListColoring.step4}

{docstring ListColoring.step56}

{docstring ListColoring.rubin_structure}

{docstring ListColoring.hasCore}

{docstring ListColoring.exists_iso_closePath_of_two_regular}

{docstring ListColoring.nonempty_iso_thetaGen_of_paths}

{docstring ListColoring.exists_iso_theta_of_thetaData}

{docstring ListColoring.degree_eq_two_of_cycle_edges}

# Theorem 2

{docstring ListColoring.ecc_two_of_alternatives}

{docstring ListColoring.hasOddCycle_of_not_colorable_two}

{docstring ListColoring.exists_odd_isCycle_of_odd_closed_walk}

{docstring ListColoring.alternatives_of_rubinAlternatives}

{docstring ListColoring.ecc_two_iff_of_rubin}

# The families, one by one

{docstring SimpleGraph.ecc_K23}

{docstring ListColoring.choosable_theta}

{docstring ListColoring.not_ecc_theta}

{docstring ListColoring.ecc_closePath_all}

{docstring SimpleGraph.ecc_of_two_pow_lt}
