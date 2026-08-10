import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

-- Every backticked span inside a rendered docstring is elaborated by Verso, and a span that
-- cannot be resolved is reported with `logWarningAt`. Warnings are promoted to errors here so
-- that a reference to a declaration which no longer exists breaks the build instead of quietly
-- rendering as plain code. That is the failure mode this chapter exists to catch.
set_option warningAsError true
-- ... but not the cosmetic linters, which have nothing to do with dangling references: docstrings
-- carry their own line widths and their own Markdown emphasis conventions.
set_option verso.code.warnLineLength 0
set_option linter.verso.markup.emph false

#doc (Manual) "The Declarations" =>

%%%
tag := "reference"
%%%

Every displayed statement elsewhere in this book is an `example` whose proof is a theorem of the
development. That keeps the *statements* honest: if a theorem is renamed or its hypotheses change,
the book stops building.

It does not keep the *prose* honest. A sentence that names a declaration in backticks is just text,
and it survives the deletion of the thing it names. This chapter closes that gap by rendering the
declarations themselves, with their own documentation, straight out of the library. Verso
elaborates every backticked span inside a rendered docstring, and this chapter is compiled with
warnings promoted to errors, so a docstring that refers to a declaration which no longer exists
fails the build.

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

# The ten claims

These are the theorems `comparator/Challenge.lean` states, in its own order;
{ref "readingchallenge"}[the guide to that file] explains why these ten.

{docstring SimpleGraph.eval_chromaticPolynomial}

{docstring SimpleGraph.ecc_iff_listColorFunction_eq_eval}

{docstring SimpleGraph.ERT.not_choosable}

{docstring SimpleGraph.ERT.colorable}

{docstring SimpleGraph.ecc_of_isChordal}

{docstring SimpleGraph.isChordal_iff_exists_cliqueTower}

{docstring ListColoring.ecc_closePath_of_two_le}

{docstring ListColoring.choosable_two_of_rubinFamily}

{docstring SimpleGraph.ecc_two_iff_of_rubin_hard}

{docstring SimpleGraph.exists_ecc_forall_ge}

# Transport along cores

Kirov and Naimi's Lemma 5 and its choosability counterpart are what make a classification of cores
a classification of graphs.

{docstring SimpleGraph.ecc_pendantTower_iff}

{docstring SimpleGraph.choosable_pendantTower_iff}

{docstring ListColoring.ecc_iff_of_coreIs}

{docstring ListColoring.choosable_iff_of_coreIs}

# Rubin's theorem

Rubin's characterization of the `2`-choosable graphs is a named proposition here, not an axiom and
not a hypothesis tailored to what Theorem 2 needs. Its ⟸ direction is proved, and so is its whole
content about theta graphs; what remains is the forward implication.

{docstring ListColoring.RubinTheorem}

{docstring ListColoring.choosable_two_of_rubinAlternatives}

{docstring ListColoring.ThetaClassification}

{docstring ListColoring.thetaClassification}

{docstring ListColoring.not_choosable_two_thetaGen}

{docstring ListColoring.choosable_two_thetaGen_iff}

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
